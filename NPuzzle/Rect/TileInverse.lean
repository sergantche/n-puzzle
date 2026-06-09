import NPuzzle.Rect.Config

namespace NPuzzle.Rect

/-!
Sliding is an involution on any rectangular board: undo a slide by sliding the
blank back.
-/

lemma adjacent_slide_blank {B : Board} (cfg : Config B) (n : Cell B)
    (h : adjacent (blank cfg) n) :
    adjacent (blank (slide cfg n h)) (blank cfg) := by
  rw [blank_slide cfg n h]
  exact adjacent_symm h

/-- Undo a double swap, even when the second swap is written in the reverse order. -/
lemma swapAt_swapAt_rev {B : Board} {cells : Cell B → ℕ} (a b : Cell B) :
    swapAt (swapAt cells a b) b a = cells := by
  funext c
  dsimp [swapAt]
  grind

lemma slide_cells {B : Board} (cfg' : Config B) (m : Cell B)
    (hm : adjacent (blank cfg') m) :
    (slide cfg' m hm).cells = swapAt cfg'.cells (blank cfg') m := rfl

lemma slide_cells_undo {B : Board} (cfg : Config B) (n : Cell B)
    (h : adjacent (blank cfg) n) :
    (slide (slide cfg n h) (blank cfg) (adjacent_slide_blank cfg n h)).cells =
      swapAt (swapAt cfg.cells (blank cfg) n) n (blank cfg) := by
  rw [slide_cells, slide_cells, blank_slide cfg n h]

/-- Undo one slide. -/
lemma slide_inv {B : Board} (cfg : Config B) (n : Cell B)
    (h : adjacent (blank cfg) n) :
    slide (slide cfg n h) (blank cfg) (adjacent_slide_blank cfg n h) = cfg := by
  apply Config.ext
  intro c
  rw [slide_cells_undo,
    congrFun (swapAt_swapAt_rev (blank cfg) n) c]

lemma legalStep_symm {B : Board} {cfg cfg' : Config B}
    (h : legalStep cfg cfg') : legalStep cfg' cfg := by
  rcases h with ⟨n, h, rfl⟩
  exact ⟨blank cfg, adjacent_slide_blank cfg n h, (slide_inv cfg n h).symm⟩

lemma reachable_symm {B : Board} {cfg cfg' : Config B}
    (h : Reachable cfg cfg') : Reachable cfg' cfg := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hrest hstep ih =>
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (legalStep_symm hstep)) ih

end NPuzzle.Rect
