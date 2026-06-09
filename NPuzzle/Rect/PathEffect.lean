import NPuzzle.Rect.Reach

namespace NPuzzle.Rect

/-!
Cell-level effect of running a blank path.

This is the generic replacement for hand-written `hamCells` computations:
following a blank path is the same as repeatedly swapping labels along the
path's edges.
-/

/-- Cell labels after swapping along a blank-grid path starting at `a`. -/
def swapAlongBlankPathStart {B : Board} (cells : Cell B → ℕ) (a : Cell B)
    (t : Cell B) : BlankGridPath a t → Cell B → ℕ
  | .nil _ => cells
  | .cons (b := b) _ rest => swapAlongBlankPathStart (swapAt cells a b) b t rest

@[simp]
lemma swapAlongBlankPathStart_nil {B : Board} (cells : Cell B → ℕ) (a : Cell B) :
    swapAlongBlankPathStart cells a a (.nil a) = cells := rfl

@[simp]
lemma swapAlongBlankPathStart_cons {B : Board} (cells : Cell B → ℕ)
    {a b t : Cell B} (hab : adjacent a b) (rest : BlankGridPath b t) :
    swapAlongBlankPathStart cells a t (.cons hab rest) =
      swapAlongBlankPathStart (swapAt cells a b) b t rest := rfl

lemma followBlankGridPathStart_cells {B : Board} (a : Cell B) (cfg : Config B)
    (ha : blank cfg = a) (t : Cell B) (path : BlankGridPath a t) :
    (followBlankGridPathStart a cfg ha t path).cells =
      swapAlongBlankPathStart cfg.cells a t path := by
  match path with
  | .nil _ => rfl
  | .cons (b := b) hab rest =>
      let h : adjacent (blank cfg) b := by
        rw [ha]
        exact hab
      change (followBlankGridPathStart b (slide cfg b h) (blank_slide cfg b h) t rest).cells =
        swapAlongBlankPathStart (swapAt cfg.cells a b) b t rest
      rw [followBlankGridPathStart_cells b (slide cfg b h) (blank_slide cfg b h) t rest]
      congr
      funext c
      change swapAt cfg.cells (blank cfg) b c = swapAt cfg.cells a b c
      rw [ha]

end NPuzzle.Rect
