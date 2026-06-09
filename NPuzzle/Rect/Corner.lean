import NPuzzle.Rect.Reach

namespace NPuzzle.Rect

/-!
Bottom-right 2x2 geometry on a rectangular board.
-/

/-- The cell immediately left of `bottomRight`; degenerate on a one-column board. -/
def cornerLeft (B : Board) : Cell B :=
  ((bottomRight B).1, ⟨(bottomRight B).2.val - 1, by
    have hlt := (bottomRight B).2.isLt
    omega⟩)

/-- The cell immediately above `bottomRight`; degenerate on a one-row board. -/
def cornerUp (B : Board) : Cell B :=
  (⟨(bottomRight B).1.val - 1, by
    have hlt := (bottomRight B).1.isLt
    omega⟩, (bottomRight B).2)

/-- The upper-left cell of the bottom-right 2x2 block; degenerate on thin boards. -/
def cornerUpLeft (B : Board) : Cell B :=
  (⟨(bottomRight B).1.val - 1, by
    have hlt := (bottomRight B).1.isLt
    omega⟩, ⟨(bottomRight B).2.val - 1, by
    have hlt := (bottomRight B).2.isLt
    omega⟩)

lemma adjacent_bottomRight_cornerLeft (B : Board) (hcols : 2 ≤ B.cols) :
    adjacent (bottomRight B) (cornerLeft B) := by
  left
  constructor
  · simp [sameRow, cornerLeft]
  · right
    change (bottomRight B).2.val - 1 + 1 = (bottomRight B).2.val
    simp [bottomRight]
    omega

lemma adjacent_cornerLeft_cornerUpLeft (B : Board) (hrows : 2 ≤ B.rows) :
    adjacent (cornerLeft B) (cornerUpLeft B) := by
  right
  constructor
  · simp [sameCol, cornerLeft, cornerUpLeft]
  · right
    change (bottomRight B).1.val - 1 + 1 = (bottomRight B).1.val
    simp [bottomRight]
    omega

lemma adjacent_cornerUpLeft_cornerUp (B : Board) (hcols : 2 ≤ B.cols) :
    adjacent (cornerUpLeft B) (cornerUp B) := by
  left
  constructor
  · simp [sameRow, cornerUpLeft, cornerUp]
  · left
    change (bottomRight B).2.val - 1 + 1 = (bottomRight B).2.val
    simp [bottomRight]
    omega

lemma adjacent_cornerUp_bottomRight (B : Board) (hrows : 2 ≤ B.rows) :
    adjacent (cornerUp B) (bottomRight B) := by
  right
  constructor
  · simp [sameCol, cornerUp]
  · left
    change (bottomRight B).1.val - 1 + 1 = (bottomRight B).1.val
    simp [bottomRight]
    omega

/-- The blank loop around the bottom-right 2x2 block. -/
def cornerCyclePath (B : Board) (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    BlankGridPath (bottomRight B) (bottomRight B) :=
  .cons (adjacent_bottomRight_cornerLeft B hcols)
    (.cons (adjacent_cornerLeft_cornerUpLeft B hrows)
      (.cons (adjacent_cornerUpLeft_cornerUp B hcols)
        (.cons (adjacent_cornerUp_bottomRight B hrows) (.nil _))))

/-- Run the bottom-right 2x2 blank loop from a configuration whose blank is at `bottomRight`. -/
lemma reachable_cornerCycle_blank {B : Board} (cfg : Config B)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hbr : blank cfg = bottomRight B) :
    ∃ cfg', Reachable cfg cfg' ∧ blank cfg' = bottomRight B :=
  reachable_blank_gridPath_start (bottomRight B) cfg hbr (bottomRight B)
    (cornerCyclePath B hrows hcols)

end NPuzzle.Rect
