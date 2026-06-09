import NPuzzle.Rect.GeneratorSufficiency
import NPuzzle.Rect.PathList
import NPuzzle.Rect.PathRealizable

namespace NPuzzle.Rect

open Equiv Equiv.Perm

/-!
Rectangular sufficiency from a closed full blank path.

This is the last geometry-facing wrapper before constructing actual rectangular
paths: a closed path whose induced tile permutation is a compatible full cycle
is enough for the bottom-right sufficiency tail.
-/

lemma reachable_goal_to_cfg_bottomRight_of_closedFullPath {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {xs : List (Cell B)}
    (path : BlankGridPath (bottomRight B) (bottomRight B))
    (hverts : BlankGridPath.vertices path = xs ++ [bottomRight B])
    (hxs : ∀ c ∈ xs, c ≠ bottomRight B)
    (hcycle :
      IsCycle (List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))))
    (hsupp :
      (List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))).support =
        Finset.univ)
    (hcompat :
      List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))
        (cornerUpIdx B hrows) = cornerLeftIdx B hcols)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable (goal B) cfg :=
  reachable_goal_to_cfg_bottomRight_of_compatibleFullCycle hrows hcols
    (closedPathPermRealizable path hverts hxs)
    hcycle hsupp hcompat cfg hbr hpar

lemma tiles_to_goal_bottomRight_of_closedFullPath {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {xs : List (Cell B)}
    (path : BlankGridPath (bottomRight B) (bottomRight B))
    (hverts : BlankGridPath.vertices path = xs ++ [bottomRight B])
    (hxs : ∀ c ∈ xs, c ≠ bottomRight B)
    (hcycle :
      IsCycle (List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))))
    (hsupp :
      (List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))).support =
        Finset.univ)
    (hcompat :
      List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))
        (cornerUpIdx B hrows) = cornerLeftIdx B hcols)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable cfg (goal B) :=
  reachable_symm
    (reachable_goal_to_cfg_bottomRight_of_closedFullPath hrows hcols
      path hverts hxs hcycle hsupp hcompat cfg hbr hpar)

lemma reachable_goal_to_cfg_bottomRight_of_leftClosedFullPath {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {xs : List (Cell B)}
    (path : BlankGridPath (bottomRight B) (bottomRight B))
    (hverts : BlankGridPath.vertices path = xs ++ [bottomRight B])
    (hxs : ∀ c ∈ xs, c ≠ bottomRight B)
    (hcycle :
      IsCycle (List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))))
    (hsupp :
      (List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))).support =
        Finset.univ)
    (hcompat :
      List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))
        (cornerLeftIdx B hcols) = cornerUpLeftIdx B hrows)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable (goal B) cfg :=
  reachable_goal_to_cfg_bottomRight_of_cornerLeftFullCycle hrows hcols
    (closedPathPermRealizable path hverts hxs)
    hcycle hsupp hcompat cfg hbr hpar

lemma tiles_to_goal_bottomRight_of_leftClosedFullPath {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {xs : List (Cell B)}
    (path : BlankGridPath (bottomRight B) (bottomRight B))
    (hverts : BlankGridPath.vertices path = xs ++ [bottomRight B])
    (hxs : ∀ c ∈ xs, c ≠ bottomRight B)
    (hcycle :
      IsCycle (List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))))
    (hsupp :
      (List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))).support =
        Finset.univ)
    (hcompat :
      List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))
        (cornerLeftIdx B hcols) = cornerUpLeftIdx B hrows)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable cfg (goal B) :=
  reachable_symm
    (reachable_goal_to_cfg_bottomRight_of_leftClosedFullPath hrows hcols
      path hverts hxs hcycle hsupp hcompat cfg hbr hpar)

lemma reachable_goal_to_cfg_bottomRight_of_leftClosedFullList {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {xs : List (Cell B)}
    (hchain : AdjacentChain (bottomRight B) (xs ++ [bottomRight B]))
    (hxs : ∀ c ∈ xs, c ≠ bottomRight B)
    (hcycle :
      IsCycle (List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))))
    (hsupp :
      (List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))).support =
        Finset.univ)
    (hcompat :
      List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))
        (cornerLeftIdx B hcols) = cornerUpLeftIdx B hrows)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable (goal B) cfg :=
  reachable_goal_to_cfg_bottomRight_of_leftClosedFullPath hrows hcols
    (closedBlankGridPathOfList (bottomRight B) xs hchain)
    (by simp)
    hxs hcycle hsupp hcompat cfg hbr hpar

lemma tiles_to_goal_bottomRight_of_leftClosedFullList {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {xs : List (Cell B)}
    (hchain : AdjacentChain (bottomRight B) (xs ++ [bottomRight B]))
    (hxs : ∀ c ∈ xs, c ≠ bottomRight B)
    (hcycle :
      IsCycle (List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))))
    (hsupp :
      (List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))).support =
        Finset.univ)
    (hcompat :
      List.formPerm ((nonblankSubtypeList xs hxs).map (nonblankCellEquivFin B))
        (cornerLeftIdx B hcols) = cornerUpLeftIdx B hrows)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable cfg (goal B) :=
  reachable_symm
    (reachable_goal_to_cfg_bottomRight_of_leftClosedFullList hrows hcols
      hchain hxs hcycle hsupp hcompat cfg hbr hpar)

end NPuzzle.Rect
