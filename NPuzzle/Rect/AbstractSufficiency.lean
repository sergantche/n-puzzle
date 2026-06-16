import NPuzzle.Group.CycleThree
import NPuzzle.Rect.Realizable
import NPuzzle.Rect.TileGlue
import NPuzzle.Rect.TileSign

namespace NPuzzle.Rect

open Equiv Equiv.Perm

/-!
Conditional rectangular sufficiency.

This file separates the group-theoretic/relabel tail from the board-specific
macro construction.  Once a board has a realizable full cycle and a compatible
realizable 3-cycle, every even tile permutation is realizable, hence every
bottom-right configuration with the target parity is reachable from `goal`.
-/

lemma invStat_even_of_parity_bottomRight {B : Board} (cfg : Config B)
    (hbr : blank cfg = bottomRight B) (hpar : parityClass cfg = targetParity B) :
    invStat cfg % 2 = 0 := by
  by_cases hodd : B.cols % 2 = 1
  · rw [parityClass_of_odd_width cfg hodd, targetParity_of_odd_width hodd] at hpar
    exact hpar
  · have heven : B.cols % 2 = 0 := by
      have hlt := Nat.mod_lt B.cols (by decide : 0 < 2)
      omega
    rw [parityClass_of_even_width cfg heven, targetParity_of_even_width heven] at hpar
    rw [hbr, blankRow_bottomRight] at hpar
    omega

lemma permRealizable_mem_alternating {B : Board}
    {σ : Equiv.Perm (Fin B.tileCount)}
    (hσ : PermRealizable (B := B) σ) :
    σ ∈ alternatingGroup (Fin B.tileCount) := by
  obtain ⟨cfg, hbr, hreach, hperm⟩ := hσ
  have hpar : parityClass cfg = targetParity B :=
    (parityClass_reachable hreach).symm.trans (parityClass_goal B)
  have hmem := (invStat_even_iff_perm_alternating cfg hbr).mp
    (invStat_even_of_parity_bottomRight cfg hbr hpar)
  rwa [hperm] at hmem

lemma not_permRealizable_of_not_mem_alternating {B : Board}
    {σ : Equiv.Perm (Fin B.tileCount)}
    (hnot : σ ∉ alternatingGroup (Fin B.tileCount)) :
    ¬ PermRealizable (B := B) σ :=
  fun hσ => hnot (permRealizable_mem_alternating hσ)

lemma permRealizable_of_mem_alternating_of_generators {B : Board}
    {g c : Equiv.Perm (Fin B.tileCount)} {a b d : Fin B.tileCount}
    (hgReal : PermRealizable (B := B) g) (hcReal : PermRealizable (B := B) c)
    (hcycle : IsCycle g) (hsupp : g.support = Finset.univ)
    (hthree : IsThreeCycle c)
    (hca : c a = b) (hcb : c b = d) (hcd : c d = a)
    (hfixed : ∀ x : Fin B.tileCount, x ≠ a → x ≠ b → x ≠ d → c x = x)
    (hgd : g d = a) {σ : Equiv.Perm (Fin B.tileCount)}
    (hσ : σ ∈ alternatingGroup (Fin B.tileCount)) :
    PermRealizable (B := B) σ := by
  let S : Set (Equiv.Perm (Fin B.tileCount)) := {g, c}
  have hgmem : g ∈ Subgroup.closure S := by
    apply Subgroup.subset_closure
    simp [S]
  have hcmem : c ∈ Subgroup.closure S := by
    apply Subgroup.subset_closure
    simp [S]
  have halt_le : alternatingGroup (Fin B.tileCount) ≤ Subgroup.closure S :=
    NPuzzle.Group.alternatingGroup_le_of_mem_full_cycle_and_three_cycle
      hgmem hcmem hcycle hsupp hthree hca hcb hcd hfixed hgd
  exact permRealizable_of_mem_closure (B := B) (S := S)
    (by
      intro τ hτ
      simp [S] at hτ
      rcases hτ with rfl | rfl
      · exact hgReal
      · exact hcReal)
    (halt_le hσ)

lemma reachable_goal_to_cfg_bottomRight_of_generators {B : Board}
    {g c : Equiv.Perm (Fin B.tileCount)} {a b d : Fin B.tileCount}
    (hgReal : PermRealizable (B := B) g) (hcReal : PermRealizable (B := B) c)
    (hcycle : IsCycle g) (hsupp : g.support = Finset.univ)
    (hthree : IsThreeCycle c)
    (hca : c a = b) (hcb : c b = d) (hcd : c d = a)
    (hfixed : ∀ x : Fin B.tileCount, x ≠ a → x ≠ b → x ≠ d → c x = x)
    (hgd : g d = a) (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (heven : invStat cfg % 2 = 0) :
    Reachable (goal B) cfg := by
  have hσ := (invStat_even_iff_perm_alternating cfg hbr).mp heven
  obtain ⟨cfg', hbr', hreach, hperm⟩ :=
    permRealizable_of_mem_alternating_of_generators
      hgReal hcReal hcycle hsupp hthree hca hcb hcd hfixed hgd hσ
  have hcfg : cfg = cfg' := by
    apply config_eq_of_tileList_and_blank cfg cfg'
    · rw [hbr, hbr']
    · exact tileList_eq_of_tileListPerm_eq _ _
        (tileListSpec_of_config cfg (bottomRight B) hbr)
        (tileListSpec_of_config cfg' (bottomRight B) hbr')
        (by simpa [permOfCfg] using hperm.symm)
  rw [hcfg]
  exact hreach

lemma reachable_goal_to_cfg_bottomRight_of_parity_generators {B : Board}
    {g c : Equiv.Perm (Fin B.tileCount)} {a b d : Fin B.tileCount}
    (hgReal : PermRealizable (B := B) g) (hcReal : PermRealizable (B := B) c)
    (hcycle : IsCycle g) (hsupp : g.support = Finset.univ)
    (hthree : IsThreeCycle c)
    (hca : c a = b) (hcb : c b = d) (hcd : c d = a)
    (hfixed : ∀ x : Fin B.tileCount, x ≠ a → x ≠ b → x ≠ d → c x = x)
    (hgd : g d = a) (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable (goal B) cfg :=
  reachable_goal_to_cfg_bottomRight_of_generators
    hgReal hcReal hcycle hsupp hthree hca hcb hcd hfixed hgd cfg hbr
    (invStat_even_of_parity_bottomRight cfg hbr hpar)

lemma tiles_to_goal_bottomRight_of_parity_generators {B : Board}
    {g c : Equiv.Perm (Fin B.tileCount)} {a b d : Fin B.tileCount}
    (hgReal : PermRealizable (B := B) g) (hcReal : PermRealizable (B := B) c)
    (hcycle : IsCycle g) (hsupp : g.support = Finset.univ)
    (hthree : IsThreeCycle c)
    (hca : c a = b) (hcb : c b = d) (hcd : c d = a)
    (hfixed : ∀ x : Fin B.tileCount, x ≠ a → x ≠ b → x ≠ d → c x = x)
    (hgd : g d = a) (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable cfg (goal B) :=
  reachable_symm
    (reachable_goal_to_cfg_bottomRight_of_parity_generators
      hgReal hcReal hcycle hsupp hthree hca hcb hcd hfixed hgd cfg hbr hpar)

end NPuzzle.Rect
