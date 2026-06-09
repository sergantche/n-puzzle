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

/-- The concrete configuration obtained by running the bottom-right 2x2 blank loop. -/
noncomputable def cornerCycleCfg {B : Board} (cfg : Config B)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hbr : blank cfg = bottomRight B) : Config B :=
  let h1 : adjacent (blank cfg) (cornerLeft B) := by
    rw [hbr]
    exact adjacent_bottomRight_cornerLeft B hcols
  let c1 := slide cfg (cornerLeft B) h1
  let h2 : adjacent (blank c1) (cornerUpLeft B) := by
    rw [blank_slide cfg (cornerLeft B) h1]
    exact adjacent_cornerLeft_cornerUpLeft B hrows
  let c2 := slide c1 (cornerUpLeft B) h2
  let h3 : adjacent (blank c2) (cornerUp B) := by
    rw [blank_slide c1 (cornerUpLeft B) h2]
    exact adjacent_cornerUpLeft_cornerUp B hcols
  let c3 := slide c2 (cornerUp B) h3
  let h4 : adjacent (blank c3) (bottomRight B) := by
    rw [blank_slide c2 (cornerUp B) h3]
    exact adjacent_cornerUp_bottomRight B hrows
  slide c3 (bottomRight B) h4

lemma blank_cornerCycleCfg {B : Board} (cfg : Config B)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hbr : blank cfg = bottomRight B) :
    blank (cornerCycleCfg cfg hrows hcols hbr) = bottomRight B := by
  simp [cornerCycleCfg, blank_slide]

lemma reachable_cornerCycleCfg {B : Board} (cfg : Config B)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hbr : blank cfg = bottomRight B) :
    Reachable cfg (cornerCycleCfg cfg hrows hcols hbr) := by
  let h1 : adjacent (blank cfg) (cornerLeft B) := by
    rw [hbr]
    exact adjacent_bottomRight_cornerLeft B hcols
  let c1 := slide cfg (cornerLeft B) h1
  let h2 : adjacent (blank c1) (cornerUpLeft B) := by
    rw [blank_slide cfg (cornerLeft B) h1]
    exact adjacent_cornerLeft_cornerUpLeft B hrows
  let c2 := slide c1 (cornerUpLeft B) h2
  let h3 : adjacent (blank c2) (cornerUp B) := by
    rw [blank_slide c1 (cornerUpLeft B) h2]
    exact adjacent_cornerUpLeft_cornerUp B hcols
  let c3 := slide c2 (cornerUp B) h3
  let h4 : adjacent (blank c3) (bottomRight B) := by
    rw [blank_slide c2 (cornerUp B) h3]
    exact adjacent_cornerUp_bottomRight B hrows
  change Reachable cfg (slide c3 (bottomRight B) h4)
  exact Relation.ReflTransGen.trans (reachable_one_step cfg (cornerLeft B) h1)
    (Relation.ReflTransGen.trans (reachable_one_step c1 (cornerUpLeft B) h2)
      (Relation.ReflTransGen.trans (reachable_one_step c2 (cornerUp B) h3)
        (reachable_one_step c3 (bottomRight B) h4)))

/-- Run the bottom-right 2x2 blank loop from a configuration whose blank is at `bottomRight`. -/
lemma reachable_cornerCycle_blank {B : Board} (cfg : Config B)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hbr : blank cfg = bottomRight B) :
    ∃ cfg', Reachable cfg cfg' ∧ blank cfg' = bottomRight B :=
  ⟨cornerCycleCfg cfg hrows hcols hbr,
    reachable_cornerCycleCfg cfg hrows hcols hbr,
    blank_cornerCycleCfg cfg hrows hcols hbr⟩

end NPuzzle.Rect
