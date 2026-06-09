import NPuzzle.Rect.CellPerm
import NPuzzle.Rect.PathEffect

namespace NPuzzle.Rect

/-!
Tile permutations induced by closed blank paths.

This module combines the cell-level path effect with the cell-to-tile-index
bridge.  It does not construct any particular geometric path; it says what tile
cycle a closed path will realize once its visited-cell list is known.
-/

lemma tilePermOfCellPerm_closed_list {B : Board} (xs : List (Cell B))
    (hxs : ∀ c ∈ xs, c ≠ bottomRight B) :
    tilePermOfCellPerm
        (cellPermAlongList (bottomRight B) (xs ++ [bottomRight B]))
        (cellPermAlongList_closed_fix_start (bottomRight B) xs
          (by intro h; exact hxs (bottomRight B) h rfl)) =
      List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B)) := by
  have hnot : bottomRight B ∉ xs := by
    intro h
    exact hxs (bottomRight B) h rfl
  have hclosed :
      cellPermAlongList (bottomRight B) (xs ++ [bottomRight B]) =
        List.formPerm xs :=
    cellPermAlongList_closed_eq_formPerm (bottomRight B) xs hnot
  have hsub :
      Equiv.Perm.ofSubtype (List.formPerm (nonblankSubtypeList xs hxs)) =
        List.formPerm xs :=
    ofSubtype_formPerm_nonblankSubtypeList xs hxs
  have hform : List.formPerm xs (bottomRight B) = bottomRight B :=
    List.formPerm_apply_of_notMem hnot
  have hsource :
      cellPermAlongList (bottomRight B) (xs ++ [bottomRight B])
        (bottomRight B) = bottomRight B :=
    cellPermAlongList_closed_fix_start (bottomRight B) xs hnot
  have hlift :
      Equiv.Perm.ofSubtype (List.formPerm (nonblankSubtypeList xs hxs))
        (bottomRight B) = bottomRight B :=
    ofSubtype_fix_bottomRight (List.formPerm (nonblankSubtypeList xs hxs))
  calc
    tilePermOfCellPerm
        (cellPermAlongList (bottomRight B) (xs ++ [bottomRight B]))
        (cellPermAlongList_closed_fix_start (bottomRight B) xs
          (by intro h; exact hxs (bottomRight B) h rfl))
        = tilePermOfCellPerm
            (cellPermAlongList (bottomRight B) (xs ++ [bottomRight B]))
            hsource := by
              exact tilePermOfCellPerm_irrel _ _ _
    _ = tilePermOfCellPerm (List.formPerm xs) hform := by
          exact tilePermOfCellPerm_congr_perm hclosed hsource hform
    _ = tilePermOfCellPerm
          (Equiv.Perm.ofSubtype (List.formPerm (nonblankSubtypeList xs hxs)))
          hlift := by
          exact (tilePermOfCellPerm_congr_perm hsub hlift hform).symm
    _ = List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B)) :=
          tilePermOfCellPerm_ofSubtype_formPerm (nonblankSubtypeList xs hxs)

end NPuzzle.Rect
