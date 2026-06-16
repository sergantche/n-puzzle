import NPuzzle.Rect.AbstractSufficiency
import NPuzzle.Rect.AlmostFullCyclePerm
import NPuzzle.Rect.CornerRealizable
import NPuzzle.Rect.FullCyclePerm

namespace NPuzzle.Rect

open Equiv Equiv.Perm

/-!
Named rectangular sufficiency from the concrete corner generator and the
compatible full-cycle generator shape.

After `fullCyclePerm` is realized by slides, these lemmas instantiate the
abstract group-theoretic tail.
-/

lemma reachable_goal_to_cfg_bottomRight_of_compatibleFullCycle {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {g : Equiv.Perm (Fin B.tileCount)}
    (hfull : PermRealizable (B := B) g)
    (hcycle : IsCycle g) (hsupp : g.support = Finset.univ)
    (hcompat : g (cornerUpIdx B hrows) = cornerLeftIdx B hcols)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable (goal B) cfg :=
  reachable_goal_to_cfg_bottomRight_of_parity_generators
    hfull
    (cornerPerm_realizable B hrows hcols)
    hcycle
    hsupp
    (cornerPerm_isThreeCycle B hrows hcols)
    (cornerPerm_apply_cornerLeftIdx B hrows hcols)
    (cornerPerm_apply_cornerUpLeftIdx B hrows hcols)
    (cornerPerm_apply_cornerUpIdx B hrows hcols)
    (fun _ hxleft hxupleft hxup =>
      cornerPerm_apply_of_not_corner hrows hcols hxleft hxupleft hxup)
    hcompat
    cfg hbr hpar

lemma tiles_to_goal_bottomRight_of_compatibleFullCycle {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {g : Equiv.Perm (Fin B.tileCount)}
    (hfull : PermRealizable (B := B) g)
    (hcycle : IsCycle g) (hsupp : g.support = Finset.univ)
    (hcompat : g (cornerUpIdx B hrows) = cornerLeftIdx B hcols)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable cfg (goal B) :=
  reachable_symm
    (reachable_goal_to_cfg_bottomRight_of_compatibleFullCycle hrows hcols
      hfull hcycle hsupp hcompat cfg hbr hpar)

lemma reachable_goal_to_cfg_bottomRight_of_compatibleAlmostFullCycle {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {g : Equiv.Perm (Fin B.tileCount)}
    (hfull : PermRealizable (B := B) g)
    (hcycle : IsCycle g)
    (hsupp : g.support = Finset.univ.erase (cornerUpLeftIdx B hrows))
    (hcompat : g (cornerUpIdx B hrows) = cornerLeftIdx B hcols)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable (goal B) cfg :=
  reachable_goal_to_cfg_bottomRight_of_almost_parity_generators
    hfull
    (cornerPerm_realizable B hrows hcols)
    hcycle
    hsupp
    (cornerPerm_isThreeCycle B hrows hcols)
    (cornerPerm_apply_cornerLeftIdx B hrows hcols)
    (cornerPerm_apply_cornerUpLeftIdx B hrows hcols)
    (cornerPerm_apply_cornerUpIdx B hrows hcols)
    (fun _ hxleft hxupleft hxup =>
      cornerPerm_apply_of_not_corner hrows hcols hxleft hxupleft hxup)
    hcompat
    (cornerLeftIdx_ne_cornerUpLeftIdx hrows hcols)
    (fun h => cornerUpLeftIdx_ne_cornerUpIdx hrows hcols h.symm)
    cfg hbr hpar

lemma tiles_to_goal_bottomRight_of_compatibleAlmostFullCycle {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {g : Equiv.Perm (Fin B.tileCount)}
    (hfull : PermRealizable (B := B) g)
    (hcycle : IsCycle g)
    (hsupp : g.support = Finset.univ.erase (cornerUpLeftIdx B hrows))
    (hcompat : g (cornerUpIdx B hrows) = cornerLeftIdx B hcols)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable cfg (goal B) :=
  reachable_symm
    (reachable_goal_to_cfg_bottomRight_of_compatibleAlmostFullCycle hrows hcols
      hfull hcycle hsupp hcompat cfg hbr hpar)

lemma reachable_goal_to_cfg_bottomRight_of_cornerLeftFullCycle {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {g : Equiv.Perm (Fin B.tileCount)}
    (hfull : PermRealizable (B := B) g)
    (hcycle : IsCycle g) (hsupp : g.support = Finset.univ)
    (hcompat : g (cornerLeftIdx B hcols) = cornerUpLeftIdx B hrows)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable (goal B) cfg :=
  reachable_goal_to_cfg_bottomRight_of_parity_generators
    hfull
    (cornerPerm_realizable B hrows hcols)
    hcycle
    hsupp
    (cornerPerm_isThreeCycle B hrows hcols)
    (cornerPerm_apply_cornerUpLeftIdx B hrows hcols)
    (cornerPerm_apply_cornerUpIdx B hrows hcols)
    (cornerPerm_apply_cornerLeftIdx B hrows hcols)
    (fun _ hxupleft hxup hxleft =>
      cornerPerm_apply_of_not_corner hrows hcols hxleft hxupleft hxup)
    hcompat
    cfg hbr hpar

lemma tiles_to_goal_bottomRight_of_cornerLeftFullCycle {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    {g : Equiv.Perm (Fin B.tileCount)}
    (hfull : PermRealizable (B := B) g)
    (hcycle : IsCycle g) (hsupp : g.support = Finset.univ)
    (hcompat : g (cornerLeftIdx B hcols) = cornerUpLeftIdx B hrows)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable cfg (goal B) :=
  reachable_symm
    (reachable_goal_to_cfg_bottomRight_of_cornerLeftFullCycle hrows hcols
      hfull hcycle hsupp hcompat cfg hbr hpar)

lemma reachable_goal_to_cfg_bottomRight_of_fullCycle {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hfull : PermRealizable (B := B) (fullCyclePerm B hrows hcols))
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable (goal B) cfg :=
  reachable_goal_to_cfg_bottomRight_of_compatibleFullCycle hrows hcols hfull
    (fullCyclePerm_isCycle B hrows hcols)
    (fullCyclePerm_support_univ B hrows hcols)
    (fullCyclePerm_apply_cornerUpIdx B hrows hcols)
    cfg hbr hpar

lemma tiles_to_goal_bottomRight_of_fullCycle {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hfull : PermRealizable (B := B) (fullCyclePerm B hrows hcols))
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable cfg (goal B) :=
  reachable_symm
    (reachable_goal_to_cfg_bottomRight_of_fullCycle hrows hcols hfull cfg hbr hpar)

lemma reachable_goal_to_cfg_bottomRight_of_almostFullCycle {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hfull : PermRealizable (B := B) (almostFullCyclePerm B hrows hcols))
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable (goal B) cfg :=
  reachable_goal_to_cfg_bottomRight_of_compatibleAlmostFullCycle hrows hcols hfull
    (almostFullCyclePerm_isCycle B hrows hcols)
    (almostFullCyclePerm_support B hrows hcols)
    (almostFullCyclePerm_apply_cornerUpIdx B hrows hcols)
    cfg hbr hpar

lemma tiles_to_goal_bottomRight_of_almostFullCycle {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hfull : PermRealizable (B := B) (almostFullCyclePerm B hrows hcols))
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable cfg (goal B) :=
  reachable_symm
    (reachable_goal_to_cfg_bottomRight_of_almostFullCycle hrows hcols hfull cfg hbr hpar)

end NPuzzle.Rect
