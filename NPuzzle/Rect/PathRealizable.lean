import NPuzzle.Rect.PathTilePerm
import NPuzzle.Rect.Realizable

namespace NPuzzle.Rect

/-!
Realizability from closed blank paths.

`PathTilePerm` identifies the tile permutation induced by a closed list of
blank moves.  This file connects that calculation to the `PermRealizable`
interface used by the rectangular sufficiency tail.
-/

lemma permOfCfg_eq_tilePermOfCellPerm_of_goal_cells {B : Board}
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (π : Equiv.Perm (Cell B)) (hπ : π (bottomRight B) = bottomRight B)
    (hcells : ∀ c, cfg.cells c = (goal B).cells (π c)) :
    permOfCfg cfg hbr = tilePermOfCellPerm π hπ := by
  apply Equiv.ext
  intro i
  rw [permOfCfg, tileListPerm_apply, tilePermOfCellPerm_apply]
  apply Fin.ext
  let csub := (nonblankCellEquivFin B).symm i
  let c : Cell B := csub.1
  have hcbr : c ≠ bottomRight B := csub.2
  have hcblank : c ≠ blank cfg := by
    rw [hbr]
    exact hcbr
  have hrank_br : rankExcept (bottomRight B) c = i.val := by
    have hiCells : i.val < (cellsRowMajorExcept (bottomRight B)).length := by
      rw [cellsRowMajorExcept_length]
      exact i.isLt
    simpa [csub, c, nonblankCellEquivFin] using
      rankExcept_cellsRowMajorExcept (bottomRight B) i.val hiCells
  have hrank_blank : rankExcept (blank cfg) c = i.val := by
    rw [hbr]
    exact hrank_br
  have hget :
      (tileList cfg)[i.val]'(by
        rw [tileList_length]
        exact i.isLt) = cfg.cells c := by
    have h := tileList_get_rankExcept cfg c hcblank
    simpa [hrank_blank] using h
  have hπcbr : π c ≠ bottomRight B := by
    intro hbad
    have hsame : π c = π (bottomRight B) := by
      rw [hbad, hπ]
    exact hcbr (π.injective hsame)
  have htarget :
      ((nonblankCellEquivFin B)
        (nonblankPermOfCellPerm π hπ csub)).val =
        rankExcept (bottomRight B) (π c) := by
    have hcoe :
        ((nonblankPermOfCellPerm π hπ csub).1 : Cell B) = π c :=
      nonblankPermOfCellPerm_apply_coe π hπ csub
    simp [nonblankCellEquivFin_apply_val, hcoe]
  change (tileList cfg)[i.val]'(by
      rw [tileList_length]
      exact i.isLt) - 1 =
    ((nonblankCellEquivFin B)
      (nonblankPermOfCellPerm π hπ csub)).val
  rw [hget, hcells c, htarget]
  simp [goal, goalCells, hπcbr]

lemma permOfCfg_followClosedPath_goal {B : Board} {xs : List (Cell B)}
    (path : BlankGridPath (bottomRight B) (bottomRight B))
    (hverts : BlankGridPath.vertices path = xs ++ [bottomRight B])
    (hxs : ∀ c ∈ xs, c ≠ bottomRight B) :
    permOfCfg
        (followBlankGridPathStart (bottomRight B) (goal B) (blank_goal B)
          (bottomRight B) path)
        (blank_followBlankGridPathStart (bottomRight B) (goal B) (blank_goal B)
          (bottomRight B) path) =
      List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B)) := by
  have hnot : bottomRight B ∉ xs := by
    intro h
    exact hxs (bottomRight B) h rfl
  have hfix :
      cellPermAlongList (bottomRight B) (xs ++ [bottomRight B])
        (bottomRight B) = bottomRight B :=
    cellPermAlongList_closed_fix_start (bottomRight B) xs hnot
  have hcells :
      ∀ c,
        (followBlankGridPathStart (bottomRight B) (goal B) (blank_goal B)
          (bottomRight B) path).cells c =
          (goal B).cells
            (cellPermAlongList (bottomRight B) (xs ++ [bottomRight B]) c) := by
    intro c
    rw [followBlankGridPathStart_cells]
    rw [swapAlongBlankPathStart_eq_swapAlongList]
    rw [hverts]
    exact swapAlongList_eq_cellPermAlongList (goal B).cells
      (bottomRight B) (xs ++ [bottomRight B]) c
  calc
    permOfCfg
        (followBlankGridPathStart (bottomRight B) (goal B) (blank_goal B)
          (bottomRight B) path)
        (blank_followBlankGridPathStart (bottomRight B) (goal B) (blank_goal B)
          (bottomRight B) path)
        = tilePermOfCellPerm
            (cellPermAlongList (bottomRight B) (xs ++ [bottomRight B])) hfix := by
          exact permOfCfg_eq_tilePermOfCellPerm_of_goal_cells _ _ _ hfix hcells
    _ = tilePermOfCellPerm
          (cellPermAlongList (bottomRight B) (xs ++ [bottomRight B]))
          (cellPermAlongList_closed_fix_start (bottomRight B) xs
            (by intro h; exact hxs (bottomRight B) h rfl)) := by
          exact tilePermOfCellPerm_irrel _ _ _
    _ = List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B)) :=
          tilePermOfCellPerm_closed_list xs hxs

lemma closedPathPermRealizable {B : Board} {xs : List (Cell B)}
    (path : BlankGridPath (bottomRight B) (bottomRight B))
    (hverts : BlankGridPath.vertices path = xs ++ [bottomRight B])
    (hxs : ∀ c ∈ xs, c ≠ bottomRight B) :
    PermRealizable (B := B)
      (List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))) := by
  refine ⟨followBlankGridPathStart (bottomRight B) (goal B) (blank_goal B)
      (bottomRight B) path,
    blank_followBlankGridPathStart (bottomRight B) (goal B) (blank_goal B)
      (bottomRight B) path,
    reachable_followBlankGridPathStart (bottomRight B) (goal B) (blank_goal B)
      (bottomRight B) path,
    permOfCfg_followClosedPath_goal path hverts hxs⟩

end NPuzzle.Rect
