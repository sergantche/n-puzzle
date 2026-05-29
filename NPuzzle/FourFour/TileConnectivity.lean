import NPuzzle.FourFour
import NPuzzle.FourFour.TileGlue
import NPuzzle.FourFour.TileInverse
import NPuzzle.FourFour.TileReach

namespace NPuzzle.FourFour

/-!
Step **9b.3** — connectivity at `bottomRight`.

Infrastructure: `TilePerm` (`tileListPerm`, `tileList_perm_slide_vertical`, `configOfTileList`).
Generator: `reachable_cornerRot_from_goal` (corner 3-cycle on cells `{10,11,14}`).

**Open (`TileReach.lean`):** `reachable_goal_to_cfg_bottomRight` — alternating-group realization.
-/

/-- Already solved (`invStat = 0`). -/
lemma reachable_goal_to_cfg_invStat_zero (cfg : Config) (hbr : blank cfg = bottomRight)
    (h0 : invStat cfg = 0) : Reachable goal cfg := by
  rw [cfg_eq_goal_of_invStat_zero cfg hbr h0]
  exact Relation.ReflTransGen.refl

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
  have heven : invStat cfg % 2 = 0 := invStat_even_of_parity_bottomRight cfg hbr hpar
  by_cases h0 : invStat cfg = 0
  · exact tiles_to_goal_invStat_zero cfg hbr h0
  · exact tiles_to_goal_of_reachable_goal cfg hbr
      (reachable_goal_to_cfg_bottomRight cfg hbr heven)

end NPuzzle.FourFour
