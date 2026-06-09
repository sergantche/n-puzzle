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

lemma closedFullList_left_compat_of_prefix {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {ys : List (Cell B)}
    (hxs : ∀ c ∈ cornerLeft B :: cornerUpLeft B :: ys, c ≠ bottomRight B)
    (hnd :
      ((nonblankSubtypeList (cornerLeft B :: cornerUpLeft B :: ys) hxs).map
        (nonblankCellEquivFin B)).Nodup) :
    List.formPerm
        ((nonblankSubtypeList (cornerLeft B :: cornerUpLeft B :: ys) hxs).map
          (nonblankCellEquivFin B))
        (cornerLeftIdx B hcols) =
      cornerUpLeftIdx B hrows := by
  let L :=
    (nonblankSubtypeList (cornerLeft B :: cornerUpLeft B :: ys) hxs).map
      (nonblankCellEquivFin B)
  have hL0 : 0 < L.length := by
    simp [L, nonblankSubtypeList]
  have hL1 : 1 < L.length := by
    simp [L, nonblankSubtypeList]
  have h0 : L[0]'hL0 = cornerLeftIdx B hcols := by
    apply Fin.ext
    simp [L, nonblankSubtypeList, cornerLeftIdx]
  have h1 : L[1]'hL1 = cornerUpLeftIdx B hrows := by
    apply Fin.ext
    simp [L, nonblankSubtypeList, cornerUpLeftIdx]
  have h := List.formPerm_apply_getElem L hnd 0 hL0
  simpa [L, h0, h1] using h

lemma formPerm_isCycle_of_nodup_toFinset_univ {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {L : List (Fin B.tileCount)}
    (hnd : L.Nodup) (huniv : L.toFinset = Finset.univ) :
    IsCycle (List.formPerm L) := by
  apply List.isCycle_formPerm
  · exact hnd
  · have hlen : L.length = B.tileCount := by
      rw [← List.toFinset_card_of_nodup hnd, huniv]
      simp
    rw [hlen]
    have htc := Board.tileCount_ge_three hrows hcols
    omega

lemma support_formPerm_of_nodup_toFinset_univ {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {L : List (Fin B.tileCount)}
    (hnd : L.Nodup) (huniv : L.toFinset = Finset.univ) :
    (List.formPerm L).support = Finset.univ := by
  rw [List.support_formPerm_of_nodup]
  · exact huniv
  · exact hnd
  · intro x hsingle
    have hcard : L.toFinset.card = 1 := by
      simp [hsingle]
    rw [huniv] at hcard
    simp at hcard
    have htc := Board.tileCount_ge_three hrows hcols
    omega

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

lemma reachable_goal_to_cfg_bottomRight_of_prefixedFullList {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {ys : List (Cell B)}
    (hchain :
      AdjacentChain (bottomRight B)
        ((cornerLeft B :: cornerUpLeft B :: ys) ++ [bottomRight B]))
    (hxs : ∀ c ∈ cornerLeft B :: cornerUpLeft B :: ys, c ≠ bottomRight B)
    (hnd :
      ((nonblankSubtypeList (cornerLeft B :: cornerUpLeft B :: ys) hxs).map
        (nonblankCellEquivFin B)).Nodup)
    (huniv :
      ((nonblankSubtypeList (cornerLeft B :: cornerUpLeft B :: ys) hxs).map
        (nonblankCellEquivFin B)).toFinset = Finset.univ)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable (goal B) cfg :=
  reachable_goal_to_cfg_bottomRight_of_leftClosedFullList hrows hcols
    hchain hxs
    (formPerm_isCycle_of_nodup_toFinset_univ hrows hcols hnd huniv)
    (support_formPerm_of_nodup_toFinset_univ hrows hcols hnd huniv)
    (closedFullList_left_compat_of_prefix hrows hcols hxs hnd)
    cfg hbr hpar

lemma tiles_to_goal_bottomRight_of_prefixedFullList {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {ys : List (Cell B)}
    (hchain :
      AdjacentChain (bottomRight B)
        ((cornerLeft B :: cornerUpLeft B :: ys) ++ [bottomRight B]))
    (hxs : ∀ c ∈ cornerLeft B :: cornerUpLeft B :: ys, c ≠ bottomRight B)
    (hnd :
      ((nonblankSubtypeList (cornerLeft B :: cornerUpLeft B :: ys) hxs).map
        (nonblankCellEquivFin B)).Nodup)
    (huniv :
      ((nonblankSubtypeList (cornerLeft B :: cornerUpLeft B :: ys) hxs).map
        (nonblankCellEquivFin B)).toFinset = Finset.univ)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable cfg (goal B) :=
  reachable_symm
    (reachable_goal_to_cfg_bottomRight_of_prefixedFullList hrows hcols
      hchain hxs hnd huniv cfg hbr hpar)

end NPuzzle.Rect
