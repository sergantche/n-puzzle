import NPuzzle.Rect.EvenRowRoute
import NPuzzle.Rect.OddOddRoute

namespace NPuzzle.Rect

/-!
Bottom-right sufficiency for rectangular boards with at least one even side.
-/

lemma Board.evenDimension_or_oddRows_oddCols (B : Board) :
    (B.rows % 2 = 0 ∨ B.cols % 2 = 0) ∨
      (B.rows % 2 = 1 ∧ B.cols % 2 = 1) := by
  have hrowsMod : B.rows % 2 < 2 := Nat.mod_lt B.rows (by decide)
  have hcolsMod : B.cols % 2 < 2 := Nat.mod_lt B.cols (by decide)
  omega

lemma Board.oddRows_oddCols_of_not_evenDimension {B : Board}
    (hnot : ¬ (B.rows % 2 = 0 ∨ B.cols % 2 = 0)) :
    B.rows % 2 = 1 ∧ B.cols % 2 = 1 := by
  rcases B.evenDimension_or_oddRows_oddCols with hEven | hOdd
  · exact (hnot hEven).elim
  · exact hOdd

lemma Board.not_evenDimension_iff_oddRows_oddCols (B : Board) :
    ¬ (B.rows % 2 = 0 ∨ B.cols % 2 = 0) ↔
      B.rows % 2 = 1 ∧ B.cols % 2 = 1 := by
  constructor
  · exact Board.oddRows_oddCols_of_not_evenDimension
  · intro hOdd hEven
    rcases hEven with hrowsEven | hcolsEven
    · omega
    · omega

lemma Board.size_mod_two_eq_zero_of_evenDimension {B : Board}
    (hEven : B.rows % 2 = 0 ∨ B.cols % 2 = 0) :
    B.size % 2 = 0 := by
  rw [Board.size, Nat.mul_mod]
  rcases hEven with hrowsEven | hcolsEven
  · rw [hrowsEven]
    simp
  · rw [hcolsEven]
    simp

lemma Board.evenDimension_iff_size_mod_two_eq_zero (B : Board) :
    (B.rows % 2 = 0 ∨ B.cols % 2 = 0) ↔ B.size % 2 = 0 := by
  constructor
  · exact Board.size_mod_two_eq_zero_of_evenDimension
  · intro hsize
    rcases B.evenDimension_or_oddRows_oddCols with hEven | hOdd
    · exact hEven
    · have hsizeOdd := B.size_mod_two_eq_one_of_odd_rows_odd_cols hOdd.1 hOdd.2
      omega

lemma Board.oddRows_oddCols_iff_size_mod_two_eq_one (B : Board) :
    (B.rows % 2 = 1 ∧ B.cols % 2 = 1) ↔ B.size % 2 = 1 := by
  constructor
  · intro hOdd
    exact B.size_mod_two_eq_one_of_odd_rows_odd_cols hOdd.1 hOdd.2
  · intro hsize
    rcases B.evenDimension_or_oddRows_oddCols with hEven | hOdd
    · have hsizeEven := Board.size_mod_two_eq_zero_of_evenDimension hEven
      omega
    · exact hOdd

lemma Board.not_evenDimension_iff_size_mod_two_eq_one (B : Board) :
    ¬ (B.rows % 2 = 0 ∨ B.cols % 2 = 0) ↔ B.size % 2 = 1 := by
  rw [B.not_evenDimension_iff_oddRows_oddCols,
    B.oddRows_oddCols_iff_size_mod_two_eq_one]

lemma no_closedFullList_of_not_evenDimension {B : Board}
    (hnot : ¬ (B.rows % 2 = 0 ∨ B.cols % 2 = 0)) :
    ¬ ∃ xs : List (Cell B),
      AdjacentChain (bottomRight B) (xs ++ [bottomRight B]) ∧
        xs.length = B.tileCount :=
  no_closedFullList_of_size_mod_two_eq_one
    ((B.not_evenDimension_iff_size_mod_two_eq_one).mp hnot)

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

lemma reachable_goal_to_cfg_bottomRight_of_dimension_split {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable (goal B) cfg := by
  rcases B.evenDimension_or_oddRows_oddCols with hEven | hOddDims
  · exact reachable_goal_to_cfg_bottomRight_of_evenDimension
      hrows hcols hEven cfg hbr hpar
  · exact reachable_goal_to_cfg_bottomRight_of_oddOdd
      hrows hcols hOddDims.1 hOddDims.2 cfg hbr hpar

lemma tiles_to_goal_bottomRight_of_dimension_split {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable cfg (goal B) := by
  rcases B.evenDimension_or_oddRows_oddCols with hEven | hOddDims
  · exact tiles_to_goal_bottomRight_of_evenDimension
      hrows hcols hEven cfg hbr hpar
  · exact tiles_to_goal_bottomRight_of_oddOdd
      hrows hcols hOddDims.1 hOddDims.2 cfg hbr hpar

lemma reachable_goal_to_cfg_of_dimension_split {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (cfg : Config B) (hpar : parityClass cfg = targetParity B) :
    Reachable (goal B) cfg := by
  rcases reachable_blank_any cfg (bottomRight B) with ⟨cfg', hreach, hbr⟩
  have hpar' : parityClass cfg' = targetParity B :=
    (parityClass_reachable hreach).symm.trans hpar
  exact Relation.ReflTransGen.trans
    (reachable_goal_to_cfg_bottomRight_of_dimension_split
      hrows hcols cfg' hbr hpar')
    (reachable_symm hreach)

lemma tiles_to_goal_of_dimension_split {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (cfg : Config B) (hpar : parityClass cfg = targetParity B) :
    Reachable cfg (goal B) :=
  reachable_symm
    (reachable_goal_to_cfg_of_dimension_split hrows hcols cfg hpar)

theorem solvability_targetParity_of_two_le {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) (cfg : Config B) :
    Reachable cfg (goal B) ↔ parityClass cfg = targetParity B := by
  constructor
  · intro hre
    exact (reachable_imp_parity cfg hre).trans (parityClass_goal B)
  · intro hpar
    exact tiles_to_goal_of_dimension_split hrows hcols cfg hpar

theorem solvability_of_two_le {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) (cfg : Config B) :
    Reachable cfg (goal B) ↔ parityClass cfg = parityClass (goal B) := by
  constructor
  · intro hre
    exact reachable_imp_parity cfg hre
  · intro hpar
    exact tiles_to_goal_of_dimension_split hrows hcols cfg
      (hpar.trans (parityClass_goal B))

end NPuzzle.Rect
