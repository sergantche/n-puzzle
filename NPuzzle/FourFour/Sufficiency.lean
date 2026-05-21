import NPuzzle.FourFour
import NPuzzle.FourFour.Invariant

namespace NPuzzle.FourFour

/--
**Step 9 (sufficiency).** Every configuration with `parityClass = 1` can reach `goal`.

This is the large connectivity block: show the configuration graph has at most two classes
and that `goal` lies in the parity-`1` class. Planned via blank-repositioning macros and
tile cycles (see README proof plan).
-/
lemma parity_imp_reachable (cfg : Config) (h : parityClass cfg = 1) :
    Reachable cfg goal := by
  sorry

/-- Solvability criterion for 4×4 (even width): closed modulo invariant + sufficiency sorries. -/
theorem solvability_four_four (cfg : Config) :
    Reachable cfg goal ↔ parityClass cfg = parityClass goal := by
  constructor
  · intro hre
    exact (reachable_imp_parity cfg hre).trans parityClass_goal.symm
  · intro hpar
    exact parity_imp_reachable cfg (hpar.trans parityClass_goal)

end NPuzzle.FourFour
