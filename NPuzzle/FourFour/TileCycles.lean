import NPuzzle.FourFour
import NPuzzle.FourFour.Invariant
import NPuzzle.FourFour.BlankReach
import NPuzzle.FourFour.TileGlue
import NPuzzle.FourFour.TileConnectivity

namespace NPuzzle.FourFour

/-!
Step **9b**: tile rearrangement with the blank (after 9a blank repositioning).
-/

/-- Blank can be slid to the goal blank cell. -/
lemma reachable_blank_bottomRight (cfg : Config) :
    ∃ cfg', Reachable cfg cfg' ∧ blank cfg' = bottomRight :=
  reachable_blank_any cfg bottomRight

/-- Step 9c: assemble 9a (blank reposition) + 9b (tile rearrangement at bottom-right). -/
lemma parity_imp_reachable (cfg : Config) (h : parityClass cfg = 1) : Reachable cfg goal := by
  obtain ⟨cfg', hreach, hbr⟩ := reachable_blank_bottomRight cfg
  have hpar' : parityClass cfg' = 1 :=
    (parityClass_reachable hreach).symm.trans h
  exact Relation.ReflTransGen.trans hreach (tiles_to_goal_at_bottomRight cfg' hbr hpar')

end NPuzzle.FourFour
