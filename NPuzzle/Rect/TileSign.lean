import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.SpecificGroups.Alternating
import NPuzzle.List.Inversion
import NPuzzle.Rect.TileSorted

set_option maxHeartbeats 1600000

namespace NPuzzle.Rect

open Equiv Equiv.Perm

/-!
Sign of the rectangular tile-list permutation.

This is the board-generic analogue of `NPuzzle.FourFour.TileSign`: the sign of
the permutation encoded by the bottom-right tile list is `(-1)^inversionCount`.
-/

/-- Adjacent transposition on list indices `p` and `p + 1`. -/
noncomputable def adjSwap {n : ℕ} (p : Fin (n - 1)) : Equiv.Perm (Fin n) :=
  Equiv.swap (⟨p.1, by omega⟩ : Fin n) (⟨p.1 + 1, by omega⟩ : Fin n)

lemma adjSwap_isSwap {n : ℕ} (p : Fin (n - 1)) : (adjSwap p).IsSwap := by
  refine ⟨_, _, ?_, rfl⟩
  simp

lemma sign_adjSwap {n : ℕ} (p : Fin (n - 1)) : sign (adjSwap p) = -1 := by
  exact (adjSwap_isSwap p).sign_eq

private lemma tileListSpec_bubbleRight {B : Board} (L : List ℕ)
    (hs : TileListSpec (bottomRight B) L) (p : ℕ) (hp : p + 1 < L.length) :
    TileListSpec (bottomRight B) (NPuzzle.List.bubbleRight L p hp) := by
  refine ⟨by simp [NPuzzle.List.bubbleRight, hs.length_eq], ?_, ?_⟩
  · exact NPuzzle.List.bubbleRight_nodup L p hp hs.nodup
  · intro x hx
    have hxL : x ∈ L := (NPuzzle.List.bubbleRight_perm L p hp).mem_iff.mp hx
    exact hs.mem_Icc x hxL

lemma inversionCount_bubbleRight_succ_of_gt (L : List ℕ) (p : ℕ)
    (hp : p + 1 < L.length)
    (hgt : L[p]'(Nat.lt_of_succ_lt hp) > L[p + 1]'hp) :
    NPuzzle.List.inversionCount (NPuzzle.List.bubbleRight L p hp) + 1 =
      NPuzzle.List.inversionCount L :=
  NPuzzle.List.inversionCount_bubbleRight_succ L p hp hgt

private lemma bubbleRight_get_adjSwap {B : Board} (L : List ℕ)
    (hs : TileListSpec (bottomRight B) L) (p : Fin (B.tileCount - 1))
    (hp : p.1 + 1 < L.length) (i : Fin B.tileCount) :
    (NPuzzle.List.bubbleRight L p.1 hp)[i.1]'(by
      simp [NPuzzle.List.bubbleRight, hs.length_eq, i.isLt]) =
    L[(adjSwap p i).1]'(by
      rw [hs.length_eq]
      exact (adjSwap p i).isLt) := by
  have hpL : p.1 < L.length := Nat.lt_of_succ_lt hp
  have hpB : p.1 < B.tileCount := by
    have := p.isLt
    omega
  have hp1B : p.1 + 1 < B.tileCount := by
    have := p.isLt
    omega
  by_cases hi0 : i.1 = p.1
  · have hi : i = (⟨p.1, hpB⟩ : Fin B.tileCount) := Fin.eq_of_val_eq hi0
    subst i
    simpa [adjSwap] using NPuzzle.List.bubbleRight_get_at L p.1 hp hpL
  · by_cases hi1 : i.1 = p.1 + 1
    · have hi : i = (⟨p.1 + 1, hp1B⟩ : Fin B.tileCount) := Fin.eq_of_val_eq hi1
      subst i
      simpa [adjSwap] using NPuzzle.List.bubbleRight_get L p.1 hp hpL
    · have hif0 : i ≠ (⟨p.1, hpB⟩ : Fin B.tileCount) := by
        intro h
        exact hi0 (congrArg Fin.val h)
      have hif1 : i ≠ (⟨p.1 + 1, hp1B⟩ : Fin B.tileCount) := by
        intro h
        exact hi1 (congrArg Fin.val h)
      have hp_ne_i : ¬ p.1 = i.1 := fun h => hi0 h.symm
      have hp1_ne_i : ¬ p.1 + 1 = i.1 := fun h => hi1 h.symm
      simp [NPuzzle.List.bubbleRight, adjSwap, Equiv.swap_apply_def,
        hif0, hif1, hp_ne_i, hp1_ne_i]

lemma tileListPerm_bubbleRight {B : Board} (L : List ℕ)
    (hs : TileListSpec (bottomRight B) L) (p : Fin (B.tileCount - 1))
    (hp : p.1 + 1 < L.length) :
    tileListPerm (NPuzzle.List.bubbleRight L p.1 hp)
        (tileListSpec_bubbleRight L hs p.1 hp) =
      tileListPerm L hs * adjSwap p := by
  ext i
  have hget := bubbleRight_get_adjSwap L hs p hp i
  simp [tileListPerm_apply, tileLabelAt, hget]

lemma sign_tileListPerm_eq_neg_one_pow {B : Board} (L : List ℕ)
    (hs : TileListSpec (bottomRight B) L) :
    sign (tileListPerm L hs) = (NPuzzle.List.inversionCount L : ℤ).negOnePow := by
  induction h : NPuzzle.List.inversionCount L generalizing L with
  | zero =>
    rw [tileListPerm_sorted_eq_one L hs ((NPuzzle.List.inversionCount_eq_zero_iff_sorted L).mp h)]
    simp [Equiv.Perm.sign_one, Int.negOnePow_zero]
  | succ n ih =>
    have hpos : 0 < NPuzzle.List.inversionCount L := by
      rw [h]
      exact Nat.succ_pos n
    obtain ⟨p, hp1, hgt⟩ := NPuzzle.List.exists_adjacent_gt_of_inversionCount_pos L hpos
    have hs' := tileListSpec_bubbleRight L hs p hp1
    have hcount := inversionCount_bubbleRight_succ_of_gt L p hp1 hgt
    have hn' : NPuzzle.List.inversionCount (NPuzzle.List.bubbleRight L p hp1) = n := by
      linarith [hcount, h]
    have ih' := ih (NPuzzle.List.bubbleRight L p hp1) hs' hn'
    have hlen : L.length = B.tileCount := hs.length_eq
    have hpB : p + 1 < B.tileCount := by
      rwa [hlen] at hp1
    let pfin : Fin (B.tileCount - 1) := ⟨p, by omega⟩
    have hperm := tileListPerm_bubbleRight L hs pfin hp1
    have hsign : sign (tileListPerm L hs) = -((↑n : ℤ)).negOnePow := by
      have hgoal := ih'
      rw [hperm, Equiv.Perm.sign_mul, sign_adjSwap] at hgoal
      simpa [mul_neg, mul_one] using congrArg Neg.neg hgoal
    have hsucc : ((↑(n + 1) : ℤ)).negOnePow = -((↑n : ℤ)).negOnePow := by
      simpa [Nat.cast_add] using Int.negOnePow_succ (↑n : ℤ)
    exact hsign.trans hsucc.symm

lemma invStat_even_iff_perm_alternating {B : Board} (cfg : Config B)
    (hbr : blank cfg = bottomRight B) :
    invStat cfg % 2 = 0 ↔ permOfCfg cfg hbr ∈ alternatingGroup (Fin B.tileCount) := by
  have hspec := tileListSpec_of_config cfg (bottomRight B) hbr
  unfold invStat
  simp [permOfCfg, mem_alternatingGroup,
    sign_tileListPerm_eq_neg_one_pow (tileList cfg) hspec,
    Int.negOnePow_eq_one_iff, Nat.even_iff]

lemma even_invStat_iff_perm_alternating {B : Board} (cfg : Config B)
    (hbr : blank cfg = bottomRight B) :
    Even (invStat cfg) ↔ permOfCfg cfg hbr ∈ alternatingGroup (Fin B.tileCount) := by
  rw [Nat.even_iff]
  exact invStat_even_iff_perm_alternating cfg hbr

end NPuzzle.Rect
