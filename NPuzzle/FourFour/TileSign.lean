import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Sign
import NPuzzle.FourFour
import NPuzzle.FourFour.Inversion
import NPuzzle.FourFour.TilePerm
import NPuzzle.FourFour.TileSorted

set_option maxHeartbeats 1600000

namespace NPuzzle.FourFour

open Inversion List Equiv Equiv.Perm

/-- Adjacent transposition on list indices `p` and `p + 1`. -/
noncomputable def adjSwap (p : Fin 14) : Equiv.Perm (Fin 15) :=
  Equiv.swap (⟨p.1, by omega⟩ : Fin 15) (⟨p.1 + 1, by omega⟩ : Fin 15)

lemma adjSwap_isSwap (p : Fin 14) : (adjSwap p).IsSwap := by
  refine ⟨_, _, ?_, rfl⟩
  simp

lemma sign_adjSwap (p : Fin 14) : sign (adjSwap p) = -1 := by
  exact (adjSwap_isSwap p).sign_eq

private lemma headInv_pos_iff {x : ℕ} {xs : List ℕ} :
    0 < headInv x xs ↔ ∃ y ∈ xs, x > y := by
  constructor
  · intro hpos
    by_contra hall
    push_neg at hall
    have hzero : headInv x xs = 0 := (headInv_eq_zero).mpr fun y hy => le_of_not_gt (hall y hy)
    omega
  · rintro ⟨y, hy, hxy⟩
    rw [← Nat.pos_iff_ne_zero]
    intro hzero
    exact Nat.not_lt.mpr ((headInv_eq_zero).mp hzero y hy) hxy

private lemma tileListSpec_bubbleRight (L : List ℕ) (hs : TileListSpec bottomRight L) (p : ℕ)
    (hp : p + 1 < L.length) :
    TileListSpec bottomRight (bubbleRight L p hp) := by
  refine ⟨by simp [bubbleRight, hs.length_eq], ?_, ?_⟩
  · exact bubbleRight_nodup L p hp hs.nodup
  · intro x hx
    rw [List.mem_set] at hx
    rcases hx with rfl | rfl
    · exact hs.mem_Icc _ (List.getElem_mem (by rw [hs.length_eq] at hp; omega))
    · exact hs.mem_Icc _ (List.getElem_mem (by rw [hs.length_eq] at hp; omega))

lemma exists_succ_getElem_gt_of_inversionCount_pos (L : List ℕ) (hpos : 0 < inversionCount L) :
    ∃ p, ∃ hp : p < L.length, ∃ hp1 : p + 1 < L.length, L[p] > L[p + 1] := by
  induction L with
  | nil => simp [inversionCount] at hpos
  | cons x xs ih =>
    rw [inversionCount_def_cons] at hpos
    by_cases hx : 0 < headInv x xs
    · obtain ⟨y, hy, hxy⟩ := headInv_pos_iff.mp hx
      obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hy
      refine ⟨0, by simp, by simp [List.length_cons]; omega, ?_⟩
      simp [List.getElem_cons_zero, List.getElem_cons_succ, heq, hxy]
    · have hxs : 0 < inversionCount xs := by
        rw [inversionCount_def_cons, headInv_eq_zero] at hpos
        omega
      obtain ⟨p', hp', hp1', hgt⟩ := ih hxs
      refine ⟨p' + 1, by simp [List.length_cons] at hp'; omega, ?_, ?_⟩
      simpa [List.getElem_cons_succ] using hgt

lemma inversionCount_bubbleRight_succ_of_gt (L : List ℕ) (p : ℕ) (hp : p + 1 < L.length)
    (hgt : L[p]'(Nat.lt_of_succ_lt hp) > L[p + 1]'hp) (_hnd : L.Nodup) :
    inversionCount (bubbleRight L p hp) + 1 = inversionCount L :=
  inversionCount_bubbleRight_succ L p hp hgt

lemma tileListPerm_bubbleRight (L : List ℕ) (hs : TileListSpec bottomRight L) (p : Fin 14)
    (hp : p.1 + 1 < L.length) :
    let L' := bubbleRight L p.1 (by omega)
    tileListPerm L' (tileListSpec_bubbleRight L hs p.1 (by omega)) =
      tileListPerm L hs * adjSwap p := by
  dsimp only
  ext i
  simp only [tileListPerm_apply, adjSwap, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hi : i.1 < L.length := by rw [hs.length_eq]; exact i.isLt
  have hp' : p.1 < L.length := by omega
  by_cases hip : i.1 = p.1
  · have hi_eq : i = ⟨p.1, by rw [hs.length_eq] at hi; omega⟩ := Fin.ext hip
    rw [hi_eq]
    simp [bubbleRight, List.getElem_set, if_pos (by omega : p.1 = p.1),
      if_neg (by omega : ¬p.1 + 1 = p.1)]
    congr 1
    exact bubbleRight_get L p.1 (by omega) (Nat.lt_of_succ_lt hp)
  · by_cases hip1 : i.1 = p.1 + 1
    · have hi_eq : i = ⟨p.1 + 1, by rw [hs.length_eq] at hi; omega⟩ := Fin.ext hip1
      rw [hi_eq]
      simp [bubbleRight, List.getElem_set, if_neg (by omega : ¬p.1 = p.1 + 1),
        if_pos (by omega : p.1 + 1 = p.1 + 1)]
      congr 1
      exact bubbleRight_get L p.1 (by omega) (Nat.lt_of_succ_lt hp)
    · simp [bubbleRight, List.getElem_set, if_neg hip, if_neg hip1]

lemma tileList_eq_goalTileList_of_sorted (L : List ℕ) (hs : TileListSpec bottomRight L)
    (hsorted : List.Pairwise (· ≤ ·) L) : L = (List.range 15).map (· + 1) :=
  eq_range15_map_succ_of_sorted L hs.length_eq hs.nodup hsorted hs.mem_Icc

lemma tileListPerm_sorted_eq_one (L : List ℕ) (hs : TileListSpec bottomRight L)
    (hsorted : List.Pairwise (· ≤ ·) L) :
    tileListPerm L hs = 1 := by
  ext i
  rw [tileListPerm_apply, tileLabelAt]
  have hi : i.1 < L.length := by rw [hs.length_eq]; exact i.isLt
  have heq := tileList_eq_goalTileList_of_sorted L hs hsorted
  have hi15 : i.1 < 15 := by rw [hs.length_eq] at hi; exact hi
  have hi' : i.1 < (List.range 15).length := by simp
  have hval : L[i]'hi = i.1 + 1 := by
    rw [← heq, List.getElem_map, List.getElem_range]
    simp [hi15]
  simp [hval]

lemma sign_tileListPerm_eq_neg_one_pow (L : List ℕ) (hs : TileListSpec bottomRight L) :
    sign (tileListPerm L hs) = (inversionCount L : ℤ).negOnePow := by
  induction h : inversionCount L generalizing L with
  | zero =>
    rw [tileListPerm_sorted_eq_one L hs ((inversionCount_eq_zero_iff_sorted L).mp h)]
    simp [Equiv.Perm.sign_one, Int.negOnePow_zero]
  | succ n ih =>
    have hpos : 0 < inversionCount L := by rw [h]; exact Nat.succ_pos n
    obtain ⟨p, hp, hp1, hgt⟩ := exists_succ_getElem_gt_of_inversionCount_pos L hpos
    let L' := bubbleRight L p hp1
    have hs' := tileListSpec_bubbleRight L hs p hp1
    have hcount := inversionCount_bubbleRight_succ_of_gt L p hp1 hgt hs.nodup
    have hn' : inversionCount L' = n := by rw [h] at hcount; omega
    have ih' := ih L' hs' hn'
    have hperm := tileListPerm_bubbleRight L hs ⟨p, by omega⟩ (by omega)
    have hz : (inversionCount L : ℤ) = ↑(n + 1) := by rw [h]; rfl
    rw [hperm, sign_mul, ih', sign_adjSwap, hz, Int.negOnePow_one, Int.negOnePow_succ,
      mul_neg, mul_one, neg_neg]

lemma even_invStat_iff_perm_alternating (cfg : Config) (hbr : blank cfg = bottomRight) :
    Even (invStat cfg) ↔ permOfCfg cfg hbr ∈ alternatingGroup (Fin 15) := by
  have hspec := tileListSpec_of_config cfg bottomRight hbr
  unfold invStat
  rw [mem_alternatingGroup, permOfCfg, sign_tileListPerm_eq_neg_one_pow (tileList cfg) hspec,
    Int.negOnePow_eq_one_iff, ← Even.natCast]

lemma invStat_even_iff_perm_alternating (cfg : Config) (hbr : blank cfg = bottomRight) :
    invStat cfg % 2 = 0 ↔ permOfCfg cfg hbr ∈ alternatingGroup (Fin 15) := by
  rw [← Nat.even_iff]
  exact even_invStat_iff_perm_alternating cfg hbr

end NPuzzle.FourFour
