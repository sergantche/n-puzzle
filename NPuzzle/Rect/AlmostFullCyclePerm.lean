import Mathlib.GroupTheory.SpecificGroups.Alternating
import NPuzzle.Rect.FullCyclePerm

namespace NPuzzle.Rect

open Equiv Equiv.Perm

/-!
An abstract odd-board-compatible near-full cycle.

For odd by odd boards, `B.tileCount` is even, so a full cycle on all tile
indices is an odd permutation.  The replacement shape is a cycle on all tile
indices except `cornerUpLeftIdx`; it is rotated so `cornerUpIdx` maps to
`cornerLeftIdx`, matching the bottom-right corner 3-cycle.
-/

private lemma tileCount_ge_three {B : Board} (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    3 ≤ B.tileCount := by
  have hsize : 4 ≤ B.size := by
    unfold Board.size
    exact Nat.mul_le_mul hrows hcols
  rw [Board.tileCount]
  omega

/-- A near-full cycle list, omitting `cornerUpLeftIdx`. -/
def almostFullCycleList (B : Board) (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    List (Fin B.tileCount) :=
  cornerUpIdx B hrows :: cornerLeftIdx B hcols ::
    (((List.finRange B.tileCount).erase (cornerUpIdx B hrows)).erase
      (cornerLeftIdx B hcols)).erase (cornerUpLeftIdx B hrows)

lemma almostFullCycleList_nodup (B : Board) (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    (almostFullCycleList B hrows hcols).Nodup := by
  let d := cornerUpIdx B hrows
  let a := cornerLeftIdx B hcols
  let b := cornerUpLeftIdx B hrows
  have hnd : (List.finRange B.tileCount).Nodup := List.nodup_finRange B.tileCount
  have hda : d ≠ a := cornerUpIdx_ne_cornerLeftIdx hrows hcols
  have hdb : d ≠ b := fun h => cornerUpLeftIdx_ne_cornerUpIdx hrows hcols h.symm
  have hab : a ≠ b := cornerLeftIdx_ne_cornerUpLeftIdx hrows hcols
  unfold almostFullCycleList
  change (d :: a :: (((List.finRange B.tileCount).erase d).erase a).erase b).Nodup
  rw [List.nodup_cons]
  constructor
  · intro hmem
    rw [List.mem_cons] at hmem
    rcases hmem with hda' | htail
    · exact hda hda'
    · have hndEraseA : ((List.finRange B.tileCount).erase d).erase a |>.Nodup :=
        (hnd.erase d).erase a
      have hdMemEraseA := ((hndEraseA.mem_erase_iff).mp htail).2
      have hdMemEraseD := (((hnd.erase d).mem_erase_iff).mp hdMemEraseA).2
      exact ((hnd.mem_erase_iff).mp hdMemEraseD).1 rfl
  · rw [List.nodup_cons]
    constructor
    · intro hmem
      have hndEraseA : ((List.finRange B.tileCount).erase d).erase a |>.Nodup :=
        (hnd.erase d).erase a
      have haMemEraseA := ((hndEraseA.mem_erase_iff).mp hmem).2
      exact (((hnd.erase d).mem_erase_iff).mp haMemEraseA).1 rfl
    · exact ((hnd.erase d).erase a).erase b

lemma almostFullCycleList_length (B : Board) (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    (almostFullCycleList B hrows hcols).length = B.tileCount - 1 := by
  let d := cornerUpIdx B hrows
  let a := cornerLeftIdx B hcols
  let b := cornerUpLeftIdx B hrows
  have hnd : (List.finRange B.tileCount).Nodup := List.nodup_finRange B.tileCount
  have hda : d ≠ a := cornerUpIdx_ne_cornerLeftIdx hrows hcols
  have hdb : d ≠ b := fun h => cornerUpLeftIdx_ne_cornerUpIdx hrows hcols h.symm
  have hab : a ≠ b := cornerLeftIdx_ne_cornerUpLeftIdx hrows hcols
  have hd : d ∈ List.finRange B.tileCount := List.mem_finRange d
  have haEraseD : a ∈ (List.finRange B.tileCount).erase d := by
    rw [hnd.mem_erase_iff]
    exact ⟨fun had => hda had.symm, List.mem_finRange a⟩
  have hbEraseDA : b ∈ ((List.finRange B.tileCount).erase d).erase a := by
    rw [(hnd.erase d).mem_erase_iff]
    constructor
    · exact fun hba => hab hba.symm
    · rw [hnd.mem_erase_iff]
      exact ⟨fun hbd => hdb hbd.symm, List.mem_finRange b⟩
  unfold almostFullCycleList
  change (d :: a :: (((List.finRange B.tileCount).erase d).erase a).erase b).length =
    B.tileCount - 1
  simp only [List.length_cons]
  rw [List.length_erase_of_mem hbEraseDA, List.length_erase_of_mem haEraseD,
    List.length_erase_of_mem hd, List.length_finRange]
  have htc := tileCount_ge_three hrows hcols
  omega

lemma almostFullCycleList_toFinset (B : Board) (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    (almostFullCycleList B hrows hcols).toFinset =
      Finset.univ.erase (cornerUpLeftIdx B hrows) := by
  let d := cornerUpIdx B hrows
  let a := cornerLeftIdx B hcols
  let b := cornerUpLeftIdx B hrows
  have hnd := almostFullCycleList_nodup B hrows hcols
  have hlen := almostFullCycleList_length B hrows hcols
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_erase]
    constructor
    · intro hxb
      have hxmem : x ∈ almostFullCycleList B hrows hcols := by
        simpa using hx
      subst hxb
      have hda : d ≠ a := cornerUpIdx_ne_cornerLeftIdx hrows hcols
      have hdb : d ≠ b := fun h => cornerUpLeftIdx_ne_cornerUpIdx hrows hcols h.symm
      have hab : a ≠ b := cornerLeftIdx_ne_cornerUpLeftIdx hrows hcols
      have hndDA : (((List.finRange B.tileCount).erase d).erase a).Nodup :=
        ((List.nodup_finRange B.tileCount).erase d).erase a
      have hnotTail : b ∉ (((List.finRange B.tileCount).erase d).erase a).erase b := by
        intro hb
        exact ((hndDA.mem_erase_iff).mp hb).1 rfl
      change b ∈ almostFullCycleList B hrows hcols at hxmem
      rw [almostFullCycleList] at hxmem
      change b ∈ d :: a :: (((List.finRange B.tileCount).erase d).erase a).erase b at hxmem
      rw [List.mem_cons, List.mem_cons] at hxmem
      rcases hxmem with hbd | hba | htail
      · exact hdb hbd.symm
      · exact hab hba.symm
      · exact hnotTail htail
    · exact Finset.mem_univ x
  · rw [List.toFinset_card_of_nodup hnd, hlen, Finset.card_erase_of_mem (Finset.mem_univ b),
      Finset.card_univ, Fintype.card_fin]

/-- The near-full cycle omits `cornerUpLeftIdx`. -/
noncomputable def almostFullCyclePerm (B : Board) (hrows : 2 ≤ B.rows)
    (hcols : 2 ≤ B.cols) : Equiv.Perm (Fin B.tileCount) :=
  List.formPerm (almostFullCycleList B hrows hcols)

lemma almostFullCyclePerm_isCycle (B : Board) (hrows : 2 ≤ B.rows)
    (hcols : 2 ≤ B.cols) :
    IsCycle (almostFullCyclePerm B hrows hcols) := by
  rw [almostFullCyclePerm]
  apply List.isCycle_formPerm
  · exact almostFullCycleList_nodup B hrows hcols
  · rw [almostFullCycleList_length B hrows hcols]
    have htc := tileCount_ge_three hrows hcols
    omega

lemma almostFullCyclePerm_support (B : Board)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    (almostFullCyclePerm B hrows hcols).support =
      Finset.univ.erase (cornerUpLeftIdx B hrows) := by
  rw [almostFullCyclePerm, List.support_formPerm_of_nodup]
  · exact almostFullCycleList_toFinset B hrows hcols
  · exact almostFullCycleList_nodup B hrows hcols
  · intro x hsingle
    have hlen := congrArg List.length hsingle
    rw [almostFullCycleList_length B hrows hcols] at hlen
    simp at hlen
    have htc := tileCount_ge_three hrows hcols
    omega

lemma almostFullCyclePerm_apply_cornerUpIdx (B : Board)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    almostFullCyclePerm B hrows hcols (cornerUpIdx B hrows) =
      cornerLeftIdx B hcols := by
  have h := List.formPerm_apply_getElem (almostFullCycleList B hrows hcols)
    (almostFullCycleList_nodup B hrows hcols) 0 (by simp [almostFullCycleList])
  simpa [almostFullCyclePerm, almostFullCycleList] using h

lemma almostFullCyclePerm_sign_of_even_tileCount (B : Board)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (heven : Even B.tileCount) :
    sign (almostFullCyclePerm B hrows hcols) = 1 := by
  have htc := tileCount_ge_three hrows hcols
  have hodd : Odd (B.tileCount - 1) :=
    Nat.Even.sub_odd (by omega : 1 ≤ B.tileCount) heven (by decide : Odd 1)
  rw [(almostFullCyclePerm_isCycle B hrows hcols).sign,
    almostFullCyclePerm_support B hrows hcols,
    Finset.card_erase_of_mem (Finset.mem_univ (cornerUpLeftIdx B hrows)),
    Finset.card_univ, Fintype.card_fin, hodd.neg_one_pow]
  simp

lemma almostFullCyclePerm_mem_alternating_of_even_tileCount (B : Board)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (heven : Even B.tileCount) :
    almostFullCyclePerm B hrows hcols ∈ alternatingGroup (Fin B.tileCount) :=
  Equiv.Perm.mem_alternatingGroup.mpr
    (almostFullCyclePerm_sign_of_even_tileCount B hrows hcols heven)

lemma almostFullCyclePerm_mem_alternating_of_odd_rows_odd_cols (B : Board)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsOdd : B.rows % 2 = 1) (hcolsOdd : B.cols % 2 = 1) :
    almostFullCyclePerm B hrows hcols ∈ alternatingGroup (Fin B.tileCount) := by
  apply almostFullCyclePerm_mem_alternating_of_even_tileCount
  rw [Board.tileCount]
  have hsizeOdd : B.size % 2 = 1 := by
    rw [Board.size, Nat.mul_mod, hrowsOdd, hcolsOdd]
  have hsizePos := B.size_pos
  exact Nat.even_iff.mpr (by omega)

end NPuzzle.Rect
