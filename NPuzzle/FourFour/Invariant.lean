import NPuzzle.FourFour

namespace NPuzzle.FourFour

lemma blank_slide (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n) :
    blank (slide cfg n h) = n := by
  apply ExistsUnique.unique (swapAt_valid cfg.valid (blank cfg) n (blank_zero cfg) (adjacent.ne h)).2.1
    (blank_zero (slide cfg n h))
  dsimp [slide]
  exact swapAt_b (adjacent.ne h) (blank_zero cfg)

/-- Step 2: horizontal slide preserves `L`. -/
lemma tileList_slide_horizontal (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n)
    (hr : sameRow (blank cfg) n) :
    tileList (slide cfg n h) = tileList cfg := by
  sorry

/-- Steps 3–5: `(I + r_B) mod 2` is preserved on every legal move. -/
lemma parityClass_legalStep {cfg cfg' : Config} (h : legalStep cfg cfg') :
    parityClass cfg = parityClass cfg' := by
  sorry

lemma parityClass_reachable {cfg cfg' : Config} (h : Reachable cfg cfg') :
    parityClass cfg = parityClass cfg' := by
  induction h with
  | refl => rfl
  | tail hab hbc ih => exact ih.trans (parityClass_legalStep hbc)


lemma tileList_goal : tileList goal = (List.range 15).map (· + 1) := by
  sorry

lemma invStat_goal : invStat goal = 0 := by
  sorry

lemma blankRow_bottomRight : blankRowFromBottom bottomRight = 1 := by
  simp [blankRowFromBottom, bottomRight, row]
/-- Step 7: standard goal value for even `M = 4`. -/
lemma parityClass_goal : parityClass goal = 1 := by
  unfold parityClass
  rw [blank_goal, invStat_goal, blankRow_bottomRight]

/-- Step 8 (necessity): reachability ⇒ correct parity. -/
lemma reachable_imp_parity (cfg : Config) (h : Reachable cfg goal) :
    parityClass cfg = 1 := by
  rw [← parityClass_goal, parityClass_reachable h]

end NPuzzle.FourFour
