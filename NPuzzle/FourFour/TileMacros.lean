import NPuzzle.FourFour
import NPuzzle.FourFour.BlankReach

set_option maxHeartbeats 800000

namespace NPuzzle.FourFour

/-!
Explicit slide macros (step 9b generators).

Corner 3-cycle on tile positions `{10, 11, 14}` with blank returning to `bottomRight`,
starting from `goal`: slide blank into `14 → 10 → 11 → 15`.
-/

/-- Cell `14` = `(3,2)`. -/
def cell14 : Cell := ⟨14, by omega⟩

/-- Cell `10` = `(2,2)`. -/
def cell10 : Cell := ⟨10, by omega⟩

/-- Cell `11` = `(2,3)`. -/
def cell11 : Cell := ⟨11, by omega⟩

lemma adjacent_bottomRight_cell14 : adjacent bottomRight cell14 := by
  unfold adjacent bottomRight cell14
  simp [sameRow, sameCol]

lemma adjacent_cell14_cell10 : adjacent cell14 cell10 := by
  unfold adjacent cell14 cell10
  simp [sameRow, sameCol]

lemma adjacent_cell10_cell11 : adjacent cell10 cell11 := by
  unfold adjacent cell10 cell11
  simp [sameRow, sameCol]

lemma adjacent_cell11_bottomRight : adjacent cell11 bottomRight := by
  unfold adjacent cell11 bottomRight
  simp [sameRow, sameCol]

lemma adjacent_goal_blank_cell14 : adjacent (blank goal) cell14 := by
  rw [blank_goal]
  exact adjacent_bottomRight_cell14

/-- Configuration after the corner 3-cycle macro from `goal`. -/
noncomputable def cornerRotCfg : Config :=
  let c1 := slide goal cell14 adjacent_goal_blank_cell14
  let c2 := slide c1 cell10 (by rw [blank_slide goal cell14 adjacent_goal_blank_cell14]; exact adjacent_cell14_cell10)
  let c3 := slide c2 cell11 (by
    rw [blank_slide c1 cell10 (by rw [blank_slide goal cell14 adjacent_goal_blank_cell14]; exact adjacent_cell14_cell10)]
    exact adjacent_cell10_cell11)
  slide c3 bottomRight (by
    rw [blank_slide c2 cell11 (by
      rw [blank_slide c1 cell10 (by rw [blank_slide goal cell14 adjacent_goal_blank_cell14]; exact adjacent_cell14_cell10)]
      exact adjacent_cell10_cell11)]
    exact adjacent_cell11_bottomRight)

lemma blank_cornerRot : blank cornerRotCfg = bottomRight := by
  simp [cornerRotCfg, blank_slide]

/-- Corner macro is reachable from `goal` in four slides. -/
lemma reachable_cornerRot_from_goal : Reachable goal cornerRotCfg := by
  let c1 := slide goal cell14 adjacent_goal_blank_cell14
  let h1 : adjacent (blank goal) cell14 := adjacent_goal_blank_cell14
  let h2 : adjacent (blank c1) cell10 := by rw [blank_slide goal cell14 h1]; exact adjacent_cell14_cell10
  let c2 := slide c1 cell10 h2
  let h3 : adjacent (blank c2) cell11 := by rw [blank_slide c1 cell10 h2]; exact adjacent_cell10_cell11
  let c3 := slide c2 cell11 h3
  let h4 : adjacent (blank c3) bottomRight := by rw [blank_slide c2 cell11 h3]; exact adjacent_cell11_bottomRight
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step c3 bottomRight h4)
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step c2 cell11 h3)
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step c1 cell10 h2)
  exact reachable_one_step goal cell14 h1

end NPuzzle.FourFour
