import NPuzzle.Rect.AbstractSufficiency
import NPuzzle.Rect.CornerRealizable
import NPuzzle.Rect.FullCyclePerm

namespace NPuzzle.Rect

/-!
Named rectangular sufficiency from the concrete corner generator and the
compatible full-cycle generator shape.

After `fullCyclePerm` is realized by slides, these lemmas instantiate the
abstract group-theoretic tail.
-/

lemma reachable_goal_to_cfg_bottomRight_of_fullCycle {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hfull : PermRealizable (B := B) (fullCyclePerm B hrows hcols))
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable (goal B) cfg :=
  reachable_goal_to_cfg_bottomRight_of_parity_generators
    hfull
    (cornerPerm_realizable B hrows hcols)
    (fullCyclePerm_isCycle B hrows hcols)
    (fullCyclePerm_support_univ B hrows hcols)
    (cornerPerm_isThreeCycle B hrows hcols)
    (cornerPerm_apply_cornerLeftIdx B hrows hcols)
    (cornerPerm_apply_cornerUpLeftIdx B hrows hcols)
    (cornerPerm_apply_cornerUpIdx B hrows hcols)
    (fun _ hxleft hxupleft hxup =>
      cornerPerm_apply_of_not_corner hrows hcols hxleft hxupleft hxup)
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

end NPuzzle.Rect
