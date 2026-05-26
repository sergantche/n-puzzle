import NPuzzle.FourFour
import NPuzzle.FourFour.TileGlue
import NPuzzle.FourFour.TileInverse
import NPuzzle.FourFour.TileMacros

namespace NPuzzle.FourFour

/-!
Step **9b.3** — connectivity at `bottomRight`.

Generators: `reachable_cornerRot_from_goal` (corner 3-cycle). Open: reach every even-`invStat`
configuration from `goal`, hence `tiles_to_goal_at_bottomRight` (via `reachable_symm` once (1) holds).
-/

/-- Already solved (`invStat = 0`). -/
lemma reachable_goal_to_cfg_invStat_zero (cfg : Config) (hbr : blank cfg = bottomRight)
    (h0 : invStat cfg = 0) : Reachable goal cfg := by
  rw [cfg_eq_goal_of_invStat_zero cfg hbr h0]
  exact Relation.ReflTransGen.refl

/-- From `goal`, reach any even-parity configuration with blank at `bottomRight`. -/
lemma reachable_goal_to_cfg_bottomRight (cfg : Config) (hbr : blank cfg = bottomRight)
    (heven : invStat cfg % 2 = 0) : Reachable goal cfg := by
  by_cases h0 : invStat cfg = 0
  · exact reachable_goal_to_cfg_invStat_zero cfg hbr h0
  · sorry

/-- Solved board at bottom-right. -/
lemma tiles_to_goal_invStat_zero (cfg : Config) (hbr : blank cfg = bottomRight)
    (h0 : invStat cfg = 0) : Reachable cfg goal := by
  rw [cfg_eq_goal_of_invStat_zero cfg hbr h0]
  exact Relation.ReflTransGen.refl

/-- If `goal` can reach `cfg` with blank at bottom-right, then `cfg` can reach `goal`. -/
lemma tiles_to_goal_of_reachable_goal (cfg : Config) (hbr : blank cfg = bottomRight)
    (h : Reachable goal cfg) : Reachable cfg goal :=
  reachable_symm h

lemma tiles_to_goal_at_bottomRight (cfg : Config) (hbr : blank cfg = bottomRight)
    (hpar : parityClass cfg = 1) : Reachable cfg goal := by
  have _heven : invStat cfg % 2 = 0 := invStat_even_of_parity_bottomRight cfg hbr hpar
  by_cases h0 : invStat cfg = 0
  · exact tiles_to_goal_invStat_zero cfg hbr h0
  · sorry

end NPuzzle.FourFour
