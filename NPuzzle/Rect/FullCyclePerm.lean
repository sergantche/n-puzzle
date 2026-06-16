import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.SpecificGroups.Alternating
import NPuzzle.Rect.CornerPerm

namespace NPuzzle.Rect

open Equiv Equiv.Perm

/-!
A compatible abstract full cycle on rectangular tile indices.

The later geometry layer must realize this shape by slides.  The important
compatibility with the corner 3-cycle is `fullCyclePerm cornerUpIdx = cornerLeftIdx`.
-/

private lemma tileCount_ge_three {B : Board} (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    3 ≤ B.tileCount := by
  have hsize : 4 ≤ B.size := by
    unfold Board.size
    exact Nat.mul_le_mul hrows hcols
  rw [Board.tileCount]
  omega

/-- A full cycle list, rotated so `cornerUpIdx` maps to `cornerLeftIdx`. -/
def fullCycleList (B : Board) (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    List (Fin B.tileCount) :=
  cornerUpIdx B hrows :: cornerLeftIdx B hcols ::
    ((List.finRange B.tileCount).erase (cornerUpIdx B hrows)).erase (cornerLeftIdx B hcols)

lemma fullCycleList_nodup (B : Board) (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    (fullCycleList B hrows hcols).Nodup := by
  let a := cornerUpIdx B hrows
  let b := cornerLeftIdx B hcols
  have hnd : (List.finRange B.tileCount).Nodup := List.nodup_finRange B.tileCount
  have hne : a ≠ b := cornerUpIdx_ne_cornerLeftIdx hrows hcols
  unfold fullCycleList
  change (a :: b :: ((List.finRange B.tileCount).erase a).erase b).Nodup
  rw [List.nodup_cons]
  constructor
  · intro hmem
    rw [List.mem_cons] at hmem
    rcases hmem with hab | htail
    · exact hne hab
    · have hndErase : ((List.finRange B.tileCount).erase a).Nodup := hnd.erase a
      have haMemErase := ((hndErase.mem_erase_iff).mp htail).2
      exact ((hnd.mem_erase_iff).mp haMemErase).1 rfl
  · rw [List.nodup_cons]
    constructor
    · intro hmem
      have hndErase : ((List.finRange B.tileCount).erase a).Nodup := hnd.erase a
      exact ((hndErase.mem_erase_iff).mp hmem).1 rfl
    · exact (hnd.erase a).erase b

lemma fullCycleList_length (B : Board) (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    (fullCycleList B hrows hcols).length = B.tileCount := by
  let a := cornerUpIdx B hrows
  let b := cornerLeftIdx B hcols
  have hnd : (List.finRange B.tileCount).Nodup := List.nodup_finRange B.tileCount
  have hne : a ≠ b := cornerUpIdx_ne_cornerLeftIdx hrows hcols
  have ha : a ∈ List.finRange B.tileCount := List.mem_finRange a
  have hbErase : b ∈ (List.finRange B.tileCount).erase a := by
    rw [hnd.mem_erase_iff]
    exact ⟨fun hba => hne hba.symm, List.mem_finRange b⟩
  unfold fullCycleList
  change (a :: b :: ((List.finRange B.tileCount).erase a).erase b).length = B.tileCount
  simp only [List.length_cons]
  rw [List.length_erase_of_mem hbErase, List.length_erase_of_mem ha, List.length_finRange]
  have htc := tileCount_ge_three hrows hcols
  omega

lemma fullCycleList_toFinset (B : Board) (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    (fullCycleList B hrows hcols).toFinset = Finset.univ := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  let a := cornerUpIdx B hrows
  let b := cornerLeftIdx B hcols
  have hnd : (List.finRange B.tileCount).Nodup := List.nodup_finRange B.tileCount
  by_cases hxa : x = a
  · simp [fullCycleList, hxa, a]
  · by_cases hxb : x = b
    · simp [fullCycleList, hxb, b]
    · have hxEraseA : x ∈ (List.finRange B.tileCount).erase a := by
        rw [hnd.mem_erase_iff]
        exact ⟨hxa, List.mem_finRange x⟩
      have hxEraseB : x ∈ ((List.finRange B.tileCount).erase a).erase b := by
        rw [(hnd.erase a).mem_erase_iff]
        exact ⟨hxb, hxEraseA⟩
      simp [fullCycleList, hxa, hxb, hxEraseB, a, b]

/-- A full cycle on all nonblank tile indices, compatible with the corner cycle. -/
noncomputable def fullCyclePerm (B : Board) (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    Equiv.Perm (Fin B.tileCount) :=
  List.formPerm (fullCycleList B hrows hcols)

lemma fullCyclePerm_isCycle (B : Board) (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    IsCycle (fullCyclePerm B hrows hcols) := by
  rw [fullCyclePerm]
  apply List.isCycle_formPerm
  · exact fullCycleList_nodup B hrows hcols
  · rw [fullCycleList_length B hrows hcols]
    have htc := tileCount_ge_three hrows hcols
    omega

lemma fullCyclePerm_support_univ (B : Board)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    (fullCyclePerm B hrows hcols).support = Finset.univ := by
  rw [fullCyclePerm, List.support_formPerm_of_nodup]
  · exact fullCycleList_toFinset B hrows hcols
  · exact fullCycleList_nodup B hrows hcols
  · intro x hsingle
    have hlen := congrArg List.length hsingle
    rw [fullCycleList_length B hrows hcols] at hlen
    simp at hlen
    have htc := tileCount_ge_three hrows hcols
    omega

lemma fullCyclePerm_sign_of_even_tileCount (B : Board)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (heven : Even B.tileCount) :
    sign (fullCyclePerm B hrows hcols) = -1 := by
  rw [(fullCyclePerm_isCycle B hrows hcols).sign,
    fullCyclePerm_support_univ B hrows hcols, Finset.card_univ, Fintype.card_fin,
    Even.neg_one_pow heven]

lemma fullCyclePerm_not_mem_alternating_of_even_tileCount (B : Board)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (heven : Even B.tileCount) :
    fullCyclePerm B hrows hcols ∉ alternatingGroup (Fin B.tileCount) := by
  intro hmem
  have hsign := fullCyclePerm_sign_of_even_tileCount B hrows hcols heven
  have hsignAlt := Equiv.Perm.mem_alternatingGroup.mp hmem
  have hneg : (-1 : ℤˣ) = 1 := hsign.symm.trans hsignAlt
  exact (by decide : (-1 : ℤˣ) ≠ 1) hneg

lemma fullCyclePerm_not_mem_alternating_of_odd_rows_odd_cols (B : Board)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsOdd : B.rows % 2 = 1) (hcolsOdd : B.cols % 2 = 1) :
    fullCyclePerm B hrows hcols ∉ alternatingGroup (Fin B.tileCount) := by
  apply fullCyclePerm_not_mem_alternating_of_even_tileCount
  rw [Board.tileCount]
  have hsizeOdd : B.size % 2 = 1 := by
    rw [Board.size, Nat.mul_mod, hrowsOdd, hcolsOdd]
  have hsizePos := B.size_pos
  exact Nat.even_iff.mpr (by omega)

lemma fullCyclePerm_apply_cornerUpIdx (B : Board)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    fullCyclePerm B hrows hcols (cornerUpIdx B hrows) = cornerLeftIdx B hcols := by
  have h := List.formPerm_apply_getElem (fullCycleList B hrows hcols)
    (fullCycleList_nodup B hrows hcols) 0 (by simp [fullCycleList])
  simpa [fullCyclePerm, fullCycleList] using h

end NPuzzle.Rect
