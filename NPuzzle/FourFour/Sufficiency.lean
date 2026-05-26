import NPuzzle.FourFour
import NPuzzle.FourFour.Invariant
import NPuzzle.FourFour.TileCycles

namespace NPuzzle.FourFour

/-- Solvability criterion for 4×4 (even width): closed modulo `tiles_to_goal_at_bottomRight`. -/
theorem solvability_four_four (cfg : Config) :
    Reachable cfg goal ↔ parityClass cfg = parityClass goal := by
  constructor
  · intro hre
    exact (reachable_imp_parity cfg hre).trans parityClass_goal.symm
  · intro hpar
    exact parity_imp_reachable cfg (hpar.trans parityClass_goal)

end NPuzzle.FourFour
