import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.List
import NPuzzle.Rect.Corner

namespace NPuzzle.Rect

open Equiv Equiv.Perm List

/-!
The tile permutation induced by the bottom-right 2x2 corner loop.
-/

/-- The three nonblank tile-list indices touched by the bottom-right corner loop. -/
def cornerPermList (B : Board) (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    List (Fin B.tileCount) :=
  [cornerLeftIdx B hcols, cornerUpLeftIdx B hrows, cornerUpIdx B hrows]

lemma cornerPermList_nodup (B : Board) (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    (cornerPermList B hrows hcols).Nodup := by
  simp [cornerPermList,
    cornerLeftIdx_ne_cornerUpLeftIdx hrows hcols,
    cornerLeftIdx_ne_cornerUpIdx hrows hcols,
    cornerUpLeftIdx_ne_cornerUpIdx hrows hcols]

/-- The abstract 3-cycle on tile-list indices induced by the bottom-right corner loop. -/
noncomputable def cornerPerm (B : Board) (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    Equiv.Perm (Fin B.tileCount) :=
  List.formPerm (cornerPermList B hrows hcols)

lemma cornerPerm_apply_cornerLeftIdx (B : Board) (hrows : 2 ≤ B.rows)
    (hcols : 2 ≤ B.cols) :
    cornerPerm B hrows hcols (cornerLeftIdx B hcols) = cornerUpLeftIdx B hrows := by
  have h := List.formPerm_apply_getElem (cornerPermList B hrows hcols)
    (cornerPermList_nodup B hrows hcols) 0 (by simp [cornerPermList])
  simpa [cornerPerm, cornerPermList] using h

lemma cornerPerm_apply_cornerUpLeftIdx (B : Board) (hrows : 2 ≤ B.rows)
    (hcols : 2 ≤ B.cols) :
    cornerPerm B hrows hcols (cornerUpLeftIdx B hrows) = cornerUpIdx B hrows := by
  have h := List.formPerm_apply_getElem (cornerPermList B hrows hcols)
    (cornerPermList_nodup B hrows hcols) 1 (by simp [cornerPermList])
  simpa [cornerPerm, cornerPermList] using h

lemma cornerPerm_apply_cornerUpIdx (B : Board) (hrows : 2 ≤ B.rows)
    (hcols : 2 ≤ B.cols) :
    cornerPerm B hrows hcols (cornerUpIdx B hrows) = cornerLeftIdx B hcols := by
  simp [cornerPerm, cornerPermList]

lemma cornerPerm_apply_of_not_corner {B : Board} (hrows : 2 ≤ B.rows)
    (hcols : 2 ≤ B.cols) {x : Fin B.tileCount}
    (hleft : x ≠ cornerLeftIdx B hcols)
    (hupleft : x ≠ cornerUpLeftIdx B hrows)
    (hup : x ≠ cornerUpIdx B hrows) :
    cornerPerm B hrows hcols x = x := by
  rw [cornerPerm]
  apply List.formPerm_apply_of_notMem
  simp [cornerPermList, hleft, hupleft, hup]

lemma cornerPerm_isThreeCycle (B : Board) (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    IsThreeCycle (cornerPerm B hrows hcols) := by
  rw [← card_support_eq_three_iff]
  rw [cornerPerm, List.support_formPerm_of_nodup]
  · have hnd := cornerPermList_nodup B hrows hcols
    calc
      (cornerPermList B hrows hcols).toFinset.card =
          (cornerPermList B hrows hcols).length := by
        rw [List.toFinset_card_of_nodup hnd]
      _ = 3 := by
        simp [cornerPermList]
  · exact cornerPermList_nodup B hrows hcols
  · intro x h
    simp [cornerPermList] at h

end NPuzzle.Rect
