import NPuzzle.Rect.EvenRowRoute

namespace NPuzzle.Rect

/-!
Bottom-right sufficiency for rectangular boards with at least one even side.
-/

lemma reachable_goal_to_cfg_bottomRight_of_evenDimension {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hEven : B.rows % 2 = 0 ∨ B.cols % 2 = 0)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable (goal B) cfg := by
  rcases hEven with hrowsEven | hcolsEven
  · exact reachable_goal_to_cfg_bottomRight_of_evenRows
      hrows hcols hrowsEven cfg hbr hpar
  · exact reachable_goal_to_cfg_bottomRight_of_evenCols
      hrows hcols hcolsEven cfg hbr hpar

lemma tiles_to_goal_bottomRight_of_evenDimension {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hEven : B.rows % 2 = 0 ∨ B.cols % 2 = 0)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable cfg (goal B) :=
  reachable_symm
    (reachable_goal_to_cfg_bottomRight_of_evenDimension hrows hcols hEven cfg hbr hpar)

end NPuzzle.Rect
