import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Tactic

namespace NPuzzle.Rect

/-!
Basic rectangular-board geometry, independent of tile labels.

The 4x4 proof encodes cells as `Fin 16`.  For the general case we start with a
more direct row/column representation: cells are pairs `(row, col)`.
-/

/-- A rectangular board with positive dimensions. -/
structure Board where
  rows : ℕ
  cols : ℕ
  rows_pos : 0 < rows
  cols_pos : 0 < cols

namespace Board

/-- Number of cells. -/
def size (B : Board) : ℕ :=
  B.rows * B.cols

/-- Number of nonblank tiles. -/
def tileCount (B : Board) : ℕ :=
  B.size - 1

lemma size_pos (B : Board) : 0 < B.size := by
  unfold size
  exact Nat.mul_pos B.rows_pos B.cols_pos

lemma tileCount_add_one (B : Board) : B.tileCount + 1 = B.size := by
  unfold tileCount
  have hsize := B.size_pos
  omega

end Board

/-- A cell is a row/column pair. Rows and columns are zero-indexed. -/
abbrev Cell (B : Board) : Type :=
  Fin B.rows × Fin B.cols

/-- Row-major linear index. -/
def index {B : Board} (c : Cell B) : ℕ :=
  c.1.val * B.cols + c.2.val

lemma index_lt_size {B : Board} (c : Cell B) : index c < B.size := by
  unfold index Board.size
  have hcol : c.2.val < B.cols := c.2.isLt
  have hrow : c.1.val + 1 ≤ B.rows := Nat.succ_le_iff.mpr c.1.isLt
  calc
    c.1.val * B.cols + c.2.val < c.1.val * B.cols + B.cols :=
      Nat.add_lt_add_left hcol _
    _ = (c.1.val + 1) * B.cols := by
      rw [Nat.succ_mul]
    _ ≤ B.rows * B.cols :=
      Nat.mul_le_mul_right B.cols hrow

/-- Bottom-right cell, the standard goal blank position. -/
def bottomRight (B : Board) : Cell B :=
  (⟨B.rows - 1, by have h := B.rows_pos; omega⟩,
    ⟨B.cols - 1, by have h := B.cols_pos; omega⟩)

def sameRow {B : Board} (a b : Cell B) : Prop :=
  a.1 = b.1

def sameCol {B : Board} (a b : Cell B) : Prop :=
  a.2 = b.2

/-- Edge-adjacent cells. -/
def adjacent {B : Board} (a b : Cell B) : Prop :=
  (sameRow a b ∧ (a.2.val + 1 = b.2.val ∨ b.2.val + 1 = a.2.val)) ∨
  (sameCol a b ∧ (a.1.val + 1 = b.1.val ∨ b.1.val + 1 = a.1.val))

lemma adjacent_symm {B : Board} {a b : Cell B} (h : adjacent a b) : adjacent b a := by
  rcases h with (⟨hr, hstep⟩ | ⟨hc, hstep⟩)
  · exact Or.inl ⟨hr.symm, Or.symm hstep⟩
  · exact Or.inr ⟨hc.symm, Or.symm hstep⟩

lemma adjacent_ne {B : Board} {a b : Cell B} (h : adjacent a b) : a ≠ b := by
  rintro rfl
  rcases h with (⟨_, hstep⟩ | ⟨_, hstep⟩) <;>
    rcases hstep with hstep | hstep <;> omega

/-- All cells in row-major order. -/
def cellsRowMajor (B : Board) : List (Cell B) :=
  (List.finRange B.rows) ×ˢ (List.finRange B.cols)

lemma mem_cellsRowMajor {B : Board} (c : Cell B) : c ∈ cellsRowMajor B := by
  rcases c with ⟨r, c⟩
  rw [cellsRowMajor, List.mem_product]
  simp

lemma cellsRowMajor_length (B : Board) : (cellsRowMajor B).length = B.size := by
  rw [cellsRowMajor, List.length_product]
  simp [Board.size]

lemma cellsRowMajor_nodup (B : Board) : (cellsRowMajor B).Nodup := by
  exact (List.nodup_finRange B.rows).product (List.nodup_finRange B.cols)

/-- Row-major order, skipping one cell (usually the blank). -/
def cellsRowMajorExcept {B : Board} (skip : Cell B) : List (Cell B) :=
  (cellsRowMajor B).filter (· ≠ skip)

lemma mem_cellsRowMajorExcept {B : Board} {skip c : Cell B} :
    c ∈ cellsRowMajorExcept skip ↔ c ≠ skip := by
  simp [cellsRowMajorExcept, mem_cellsRowMajor]

lemma cellsRowMajorExcept_nodup {B : Board} (skip : Cell B) :
    (cellsRowMajorExcept skip).Nodup := by
  exact (cellsRowMajor_nodup B).filter _

end NPuzzle.Rect
