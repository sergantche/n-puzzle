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

@[simp]
lemma cornerLeft_ne_bottomRight {B : Board} (hcols : 2 ≤ B.cols) :
    cornerLeft B ≠ bottomRight B := by
  intro h
  have hv := congrArg (fun c : Cell B => c.2.val) h
  simp [cornerLeft, bottomRight] at hv
  omega

@[simp]
lemma bottomRight_ne_cornerLeft {B : Board} (hcols : 2 ≤ B.cols) :
    bottomRight B ≠ cornerLeft B :=
  (cornerLeft_ne_bottomRight hcols).symm

@[simp]
lemma cornerUp_ne_bottomRight {B : Board} (hrows : 2 ≤ B.rows) :
    cornerUp B ≠ bottomRight B := by
  intro h
  have hv := congrArg (fun c : Cell B => c.1.val) h
  simp [cornerUp, bottomRight] at hv
  omega

@[simp]
lemma bottomRight_ne_cornerUp {B : Board} (hrows : 2 ≤ B.rows) :
    bottomRight B ≠ cornerUp B :=
  (cornerUp_ne_bottomRight hrows).symm

@[simp]
lemma cornerUpLeft_ne_bottomRight {B : Board} (hrows : 2 ≤ B.rows) :
    cornerUpLeft B ≠ bottomRight B := by
  intro h
  have hv := congrArg (fun c : Cell B => c.1.val) h
  simp [cornerUpLeft, bottomRight] at hv
  omega

@[simp]
lemma bottomRight_ne_cornerUpLeft {B : Board} (hrows : 2 ≤ B.rows) :
    bottomRight B ≠ cornerUpLeft B :=
  (cornerUpLeft_ne_bottomRight hrows).symm

@[simp]
lemma cornerUpLeft_ne_cornerLeft {B : Board} (hrows : 2 ≤ B.rows) :
    cornerUpLeft B ≠ cornerLeft B := by
  intro h
  have hv := congrArg (fun c : Cell B => c.1.val) h
  simp [cornerUpLeft, cornerLeft, bottomRight] at hv
  omega

@[simp]
lemma cornerLeft_ne_cornerUpLeft {B : Board} (hrows : 2 ≤ B.rows) :
    cornerLeft B ≠ cornerUpLeft B :=
  (cornerUpLeft_ne_cornerLeft hrows).symm

@[simp]
lemma cornerUp_ne_cornerUpLeft {B : Board} (hcols : 2 ≤ B.cols) :
    cornerUp B ≠ cornerUpLeft B := by
  intro h
  have hv := congrArg (fun c : Cell B => c.2.val) h
  simp [cornerUp, cornerUpLeft, bottomRight] at hv
  omega

@[simp]
lemma cornerUpLeft_ne_cornerUp {B : Board} (hcols : 2 ≤ B.cols) :
    cornerUpLeft B ≠ cornerUp B :=
  (cornerUp_ne_cornerUpLeft hcols).symm

@[simp]
lemma cornerLeft_ne_cornerUp {B : Board} (hrows : 2 ≤ B.rows) :
    cornerLeft B ≠ cornerUp B := by
  intro h
  have hv := congrArg (fun c : Cell B => c.1.val) h
  simp [cornerLeft, cornerUp, bottomRight] at hv
  omega

@[simp]
lemma cornerUp_ne_cornerLeft {B : Board} (hrows : 2 ≤ B.rows) :
    cornerUp B ≠ cornerLeft B :=
  (cornerLeft_ne_cornerUp hrows).symm

/-- Tile-list index of `cornerLeft` when the blank is at `bottomRight`. -/
def cornerLeftIdx (B : Board) (hcols : 2 ≤ B.cols) : Fin B.tileCount :=
  ⟨rankExcept (bottomRight B) (cornerLeft B), by
    rw [← cellsRowMajorExcept_length]
    exact rankExcept_lt (cornerLeft_ne_bottomRight hcols)⟩

/-- Tile-list index of `cornerUpLeft` when the blank is at `bottomRight`. -/
def cornerUpLeftIdx (B : Board) (hrows : 2 ≤ B.rows) : Fin B.tileCount :=
  ⟨rankExcept (bottomRight B) (cornerUpLeft B), by
    rw [← cellsRowMajorExcept_length]
    exact rankExcept_lt (cornerUpLeft_ne_bottomRight hrows)⟩

/-- Tile-list index of `cornerUp` when the blank is at `bottomRight`. -/
def cornerUpIdx (B : Board) (hrows : 2 ≤ B.rows) : Fin B.tileCount :=
  ⟨rankExcept (bottomRight B) (cornerUp B), by
    rw [← cellsRowMajorExcept_length]
    exact rankExcept_lt (cornerUp_ne_bottomRight hrows)⟩

@[simp]
lemma cornerLeftIdx_ne_cornerUpLeftIdx {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    cornerLeftIdx B hcols ≠ cornerUpLeftIdx B hrows := by
  intro h
  have hrank := congrArg Fin.val h
  simp [cornerLeftIdx, cornerUpLeftIdx] at hrank
  exact cornerLeft_ne_cornerUpLeft hrows
    (rankExcept_injective
      (cornerLeft_ne_bottomRight hcols)
      (cornerUpLeft_ne_bottomRight hrows)
      hrank)

@[simp]
lemma cornerUpLeftIdx_ne_cornerLeftIdx {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    cornerUpLeftIdx B hrows ≠ cornerLeftIdx B hcols :=
  (cornerLeftIdx_ne_cornerUpLeftIdx hrows hcols).symm

@[simp]
lemma cornerUpLeftIdx_ne_cornerUpIdx {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    cornerUpLeftIdx B hrows ≠ cornerUpIdx B hrows := by
  intro h
  have hrank := congrArg Fin.val h
  simp [cornerUpLeftIdx, cornerUpIdx] at hrank
  exact cornerUpLeft_ne_cornerUp hcols
    (rankExcept_injective
      (cornerUpLeft_ne_bottomRight hrows)
      (cornerUp_ne_bottomRight hrows)
      hrank)

@[simp]
lemma cornerUpIdx_ne_cornerUpLeftIdx {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    cornerUpIdx B hrows ≠ cornerUpLeftIdx B hrows :=
  (cornerUpLeftIdx_ne_cornerUpIdx hrows hcols).symm

@[simp]
lemma cornerUpIdx_ne_cornerLeftIdx {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    cornerUpIdx B hrows ≠ cornerLeftIdx B hcols := by
  intro h
  have hrank := congrArg Fin.val h
  simp [cornerUpIdx, cornerLeftIdx] at hrank
  exact cornerUp_ne_cornerLeft hrows
    (rankExcept_injective
      (cornerUp_ne_bottomRight hrows)
      (cornerLeft_ne_bottomRight hcols)
      hrank)

@[simp]
lemma cornerLeftIdx_ne_cornerUpIdx {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    cornerLeftIdx B hcols ≠ cornerUpIdx B hrows :=
  (cornerUpIdx_ne_cornerLeftIdx hrows hcols).symm

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

/-- Cell-label function obtained by the bottom-right 2x2 loop. -/
def cornerCycleCells {B : Board} (cfg : Config B) : Cell B → ℕ :=
  swapAt
    (swapAt
      (swapAt
        (swapAt cfg.cells (bottomRight B) (cornerLeft B))
        (cornerLeft B) (cornerUpLeft B))
      (cornerUpLeft B) (cornerUp B))
    (cornerUp B) (bottomRight B)

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

lemma cornerCycleCfg_cells_eq {B : Board} (cfg : Config B)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hbr : blank cfg = bottomRight B) :
    (cornerCycleCfg cfg hrows hcols hbr).cells = cornerCycleCells cfg := by
  funext c
  simp [cornerCycleCfg, cornerCycleCells, slide_cells, hbr, blank_slide]

lemma cornerCycleCells_cornerLeft {B : Board} (cfg : Config B)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    cornerCycleCells cfg (cornerLeft B) = cfg.cells (cornerUpLeft B) := by
  simp [cornerCycleCells, swapAt, hrows, hcols]

lemma cornerCycleCells_cornerUpLeft {B : Board} (cfg : Config B)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    cornerCycleCells cfg (cornerUpLeft B) = cfg.cells (cornerUp B) := by
  simp [cornerCycleCells, swapAt, hrows, hcols]

lemma cornerCycleCells_cornerUp {B : Board} (cfg : Config B)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    cornerCycleCells cfg (cornerUp B) = cfg.cells (cornerLeft B) := by
  simp [cornerCycleCells, swapAt, hrows, hcols]

lemma cornerCycleCells_bottomRight {B : Board} (cfg : Config B)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hbr : blank cfg = bottomRight B) :
    cornerCycleCells cfg (bottomRight B) = 0 := by
  simp [cornerCycleCells, swapAt, hrows, hcols]
  simpa [hbr] using blank_zero cfg

lemma cornerCycleCfg_cells_cornerLeft {B : Board} (cfg : Config B)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hbr : blank cfg = bottomRight B) :
    (cornerCycleCfg cfg hrows hcols hbr).cells (cornerLeft B) =
      cfg.cells (cornerUpLeft B) := by
  rw [cornerCycleCfg_cells_eq cfg hrows hcols hbr]
  exact cornerCycleCells_cornerLeft cfg hrows hcols

lemma cornerCycleCfg_cells_cornerUpLeft {B : Board} (cfg : Config B)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hbr : blank cfg = bottomRight B) :
    (cornerCycleCfg cfg hrows hcols hbr).cells (cornerUpLeft B) =
      cfg.cells (cornerUp B) := by
  rw [cornerCycleCfg_cells_eq cfg hrows hcols hbr]
  exact cornerCycleCells_cornerUpLeft cfg hrows hcols

lemma cornerCycleCfg_cells_cornerUp {B : Board} (cfg : Config B)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hbr : blank cfg = bottomRight B) :
    (cornerCycleCfg cfg hrows hcols hbr).cells (cornerUp B) =
      cfg.cells (cornerLeft B) := by
  rw [cornerCycleCfg_cells_eq cfg hrows hcols hbr]
  exact cornerCycleCells_cornerUp cfg hrows hcols

lemma cornerCycleCfg_cells_bottomRight {B : Board} (cfg : Config B)
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hbr : blank cfg = bottomRight B) :
    (cornerCycleCfg cfg hrows hcols hbr).cells (bottomRight B) = 0 := by
  rw [cornerCycleCfg_cells_eq cfg hrows hcols hbr]
  exact cornerCycleCells_bottomRight cfg hrows hcols hbr

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
