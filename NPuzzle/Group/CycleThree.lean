import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Alternating

namespace NPuzzle.Group

open Equiv Equiv.Perm
open scoped Pointwise

variable {α : Type*} [Fintype α] [DecidableEq α]

/-!
Group-theoretic tail for sliding-puzzle sufficiency arguments.

The puzzle-specific work should build two realizable permutations:

* a full cycle `g` on all nonblank tile positions;
* a 3-cycle `c = (a b d)` whose last point maps by `g` back to `a`.

This file proves the abstract block/primitivity step. Geometry-free lemmas here
are meant to be reused when moving from the 4×4 proof to rectangular grids.
-/

omit [Fintype α] [DecidableEq α] in
lemma block_apply_mem_of_maps_mem {G : Subgroup (Equiv.Perm α)} {B : Set α}
    (hB : MulAction.IsBlock G B) {g : G} {x z : α}
    (hx : x ∈ B) (hgx : (g : Equiv.Perm α) x ∈ B) (hz : z ∈ B) :
    (g : Equiv.Perm α) z ∈ B := by
  have hgx' : g • x ∈ B := by
    simpa [Equiv.Perm.smul_def] using hgx
  have hEq : g • B = B := hB.smul_eq_of_mem hx hgx'
  have hzimg : g • z ∈ g • B := Set.smul_mem_smul_set hz
  rw [hEq] at hzimg
  simpa [Equiv.Perm.smul_def] using hzimg

omit [Fintype α] [DecidableEq α] in
lemma block_pow_apply_mem_of_maps_mem {G : Subgroup (Equiv.Perm α)} {B : Set α}
    (hB : MulAction.IsBlock G B) {g : G} {x : α}
    (hx : x ∈ B) (hgx : (g : Equiv.Perm α) x ∈ B) (n : ℕ) :
    ((g : Equiv.Perm α) ^ n) x ∈ B := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      have hnext := block_apply_mem_of_maps_mem hB hx hgx ih
      simpa [pow_succ'] using hnext

lemma block_eq_univ_of_cycle_maps_mem {G : Subgroup (Equiv.Perm α)} {B : Set α}
    (hB : MulAction.IsBlock G B) {g : G} {x : α}
    (hcycle : IsCycle (g : Equiv.Perm α))
    (hsupp : (g : Equiv.Perm α).support = Finset.univ)
    (hx : x ∈ B) (hgx : (g : Equiv.Perm α) x ∈ B) : B = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  have hxSupp : (g : Equiv.Perm α) x ≠ x := by
    rw [← mem_support, hsupp]
    exact Finset.mem_univ x
  have hySupp : (g : Equiv.Perm α) y ≠ y := by
    rw [← mem_support, hsupp]
    exact Finset.mem_univ y
  obtain ⟨n, hn⟩ := hcycle.exists_pow_eq hxSupp hySupp
  have hmem := block_pow_apply_mem_of_maps_mem hB hx hgx n
  rwa [hn] at hmem

lemma isPretransitive_of_mem_full_cycle {G : Subgroup (Equiv.Perm α)} {g : Equiv.Perm α}
    (hg : g ∈ G) (hcycle : IsCycle g) (hsupp : g.support = Finset.univ) (a : α) :
    MulAction.IsPretransitive G α := by
  rw [MulAction.isPretransitive_iff_base a]
  intro y
  have hxSupp : g a ≠ a := by
    rw [← mem_support, hsupp]
    exact Finset.mem_univ a
  have hySupp : g y ≠ y := by
    rw [← mem_support, hsupp]
    exact Finset.mem_univ y
  obtain ⟨n, hn⟩ := hcycle.exists_pow_eq hxSupp hySupp
  exact ⟨⟨g ^ n, Subgroup.pow_mem G hg n⟩, hn⟩

lemma block_eq_univ_of_three_cycle_maps_mem {G : Subgroup (Equiv.Perm α)} {B : Set α}
    (hB : MulAction.IsBlock G B) {g c : Equiv.Perm α} {a b d x : α}
    (hg : g ∈ G) (hc : c ∈ G)
    (hcycle : IsCycle g) (hsupp : g.support = Finset.univ)
    (hca : c a = b) (hcb : c b = d) (hgd : g d = a)
    (ha : a ∈ B) (hx : x ∈ B) (hcx : c x ∈ B) : B = Set.univ := by
  have hcx' : ((⟨c, hc⟩ : G) : Equiv.Perm α) x ∈ B := by
    simpa using hcx
  have hb' := block_apply_mem_of_maps_mem hB hx hcx' ha
  have hb : b ∈ B := by
    simpa [hca] using hb'
  have hd' := block_apply_mem_of_maps_mem hB hx hcx' hb
  have hd : d ∈ B := by
    simpa [hcb] using hd'
  have hga : ((⟨g, hg⟩ : G) : Equiv.Perm α) d ∈ B := by
    simpa [hgd] using ha
  exact block_eq_univ_of_cycle_maps_mem hB (g := (⟨g, hg⟩ : G)) (x := d)
    (by simpa using hcycle) (by simpa using hsupp) hd hga

lemma isPreprimitive_of_mem_full_cycle_and_three_cycle
    {G : Subgroup (Equiv.Perm α)} {g c : Equiv.Perm α} {a b d : α}
    (hg : g ∈ G) (hc : c ∈ G)
    (hcycle : IsCycle g) (hsupp : g.support = Finset.univ)
    (hca : c a = b) (hcb : c b = d) (hcd : c d = a)
    (hfixed : ∀ x : α, x ≠ a → x ≠ b → x ≠ d → c x = x)
    (hgd : g d = a) :
    MulAction.IsPreprimitive G α := by
  haveI : MulAction.IsPretransitive G α :=
    isPretransitive_of_mem_full_cycle hg hcycle hsupp a
  apply MulAction.IsPreprimitive.of_isTrivialBlock_base a
  intro B ha hB
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  · right
    obtain ⟨x, hx, hxne⟩ : ∃ x ∈ B, x ≠ a := by
      by_contra hno
      apply hsub
      intro y hy z hz
      have hya : y = a := by
        by_contra hyne
        exact hno ⟨y, hy, hyne⟩
      have hza : z = a := by
        by_contra hzne
        exact hno ⟨z, hz, hzne⟩
      rw [hya, hza]
    by_cases hxb : x = b
    · have hbmem : b ∈ B := by
        simpa [hxb] using hx
      exact block_eq_univ_of_three_cycle_maps_mem hB hg hc hcycle hsupp hca hcb hgd
        ha ha (by simpa [hca] using hbmem)
    · by_cases hxd : x = d
      · exact block_eq_univ_of_three_cycle_maps_mem hB hg hc hcycle hsupp hca hcb hgd
          ha hx (by simpa [hxd, hcd] using ha)
      · exact block_eq_univ_of_three_cycle_maps_mem hB hg hc hcycle hsupp hca hcb hgd
          ha hx (by simpa [hfixed x hxne hxb hxd] using hx)

lemma alternatingGroup_le_of_mem_full_cycle_and_three_cycle
    {G : Subgroup (Equiv.Perm α)} {g c : Equiv.Perm α} {a b d : α}
    (hg : g ∈ G) (hc : c ∈ G)
    (hcycle : IsCycle g) (hsupp : g.support = Finset.univ)
    (hthree : IsThreeCycle c)
    (hca : c a = b) (hcb : c b = d) (hcd : c d = a)
    (hfixed : ∀ x : α, x ≠ a → x ≠ b → x ≠ d → c x = x)
    (hgd : g d = a) :
    alternatingGroup α ≤ G := by
  have hprim : MulAction.IsPreprimitive G α :=
    isPreprimitive_of_mem_full_cycle_and_three_cycle hg hc hcycle hsupp
      hca hcb hcd hfixed hgd
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim hthree hc

end NPuzzle.Group
