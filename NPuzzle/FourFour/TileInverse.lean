import NPuzzle.FourFour

namespace NPuzzle.FourFour

/-!
Sliding is an involution: undo a slide by sliding the blank back.
-/

lemma adjacent_slide_blank (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n) :
    adjacent (blank (slide cfg n h)) (blank cfg) := by
  rw [blank_slide cfg n h]
  exact adjacent.symm h

/-- Undo a double swap when `a` holds the blank (`0`). -/
lemma swapAt_swapAt_rev_zero {cells : Cell → ℕ} {a b : Cell} (hne : a ≠ b) (ha0 : cells a = 0) :
    swapAt (swapAt cells a b) b a = cells := by
  funext c
  simp only [swapAt]
  split_ifs <;> simp [*]

lemma slide_cells (cfg' : Config) (m : Cell) (hm : adjacent (blank cfg') m) :
    (slide cfg' m hm).cells = swapAt cfg'.cells (blank cfg') m := rfl

lemma slide_cells_undo (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n) :
    (slide (slide cfg n h) (blank cfg) (adjacent_slide_blank cfg n h)).cells =
      swapAt (swapAt cfg.cells (blank cfg) n) n (blank cfg) := by
  rw [slide_cells, slide_cells, blank_slide cfg n h]

/-- Undo one slide. -/
lemma slide_inv (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n) :
    slide (slide cfg n h) (blank cfg) (adjacent_slide_blank cfg n h) = cfg := by
  apply Config.ext
  intro c
  rw [slide_cells_undo, congrFun (swapAt_swapAt_rev_zero (hne := adjacent.ne h) (ha0 := blank_zero cfg)) c]

lemma legalStep_symm {cfg cfg' : Config} (h : legalStep cfg cfg') : legalStep cfg' cfg := by
  rcases h with ⟨n, h, rfl⟩
  exact ⟨blank cfg, adjacent_slide_blank cfg n h, (slide_inv cfg n h).symm⟩

lemma reachable_symm {cfg cfg' : Config} (h : Reachable cfg cfg') : Reachable cfg' cfg := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hrest hstep ih =>
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (legalStep_symm hstep)) ih

end NPuzzle.FourFour
