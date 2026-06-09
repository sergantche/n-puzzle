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

lemma adjacent_right {B : Board} (r : Fin B.rows) (c : Fin B.cols)
    (hc : c.val + 1 < B.cols) :
    adjacent (r, c) (r, ⟨c.val + 1, hc⟩) :=
  Or.inl ⟨rfl, Or.inl rfl⟩

lemma adjacent_left {B : Board} (r : Fin B.rows) (c : Fin B.cols)
    (hc : 0 < c.val) :
    adjacent (r, c) (r, ⟨c.val - 1, by omega⟩) := by
  refine Or.inl ⟨rfl, Or.inr ?_⟩
  change c.val - 1 + 1 = c.val
  omega

lemma adjacent_down {B : Board} (r : Fin B.rows) (c : Fin B.cols)
    (hr : r.val + 1 < B.rows) :
    adjacent (r, c) (⟨r.val + 1, hr⟩, c) :=
  Or.inr ⟨rfl, Or.inl rfl⟩

lemma adjacent_up {B : Board} (r : Fin B.rows) (c : Fin B.cols)
    (hr : 0 < r.val) :
    adjacent (r, c) (⟨r.val - 1, by omega⟩, c) := by
  refine Or.inr ⟨rfl, Or.inr ?_⟩
  change r.val - 1 + 1 = r.val
  omega

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

lemma idxOf_erase_of_idxOf_lt {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) {a b : α} (h : xs.idxOf b < xs.idxOf a) :
    (xs.erase a).idxOf b = xs.idxOf b := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hxa : x = a
      · subst x
        simp at h
      · by_cases hxb : x = b
        · subst x
          have hbeq_ba : (b == a) = false := by simp [hxa]
          simp [List.erase, hbeq_ba]
        · have hbeq_xa : (x == a) = false := by simp [hxa]
          have htail : xs.idxOf b < xs.idxOf a := by
            simp [hxa, hxb] at h
            exact h
          simp [List.erase, hbeq_xa, hxb, ih htail]

lemma idxOf_erase_of_idxOf_gt {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) {a b : α} (h : xs.idxOf a < xs.idxOf b) :
    (xs.erase a).idxOf b = xs.idxOf b - 1 := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hxa : x = a
      · subst x
        have hne : a ≠ b := by
          intro hab
          subst b
          simp at h
        have hbeq_ab : (a == b) = false := by simp [hne]
        simp [List.idxOf_cons, hbeq_ab]
      · by_cases hxb : x = b
        · subst x
          simp [hxa] at h
        · have hbeq_xa : (x == a) = false := by simp [hxa]
          have htail : xs.idxOf a < xs.idxOf b := by
            simp [hxa, hxb] at h
            exact h
          have hih := ih htail
          have hbpos : 0 < xs.idxOf b := by omega
          simp [List.erase, hbeq_xa, hxb, hih]
          omega

lemma idxOf_map_const_prod {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (a : α) (b : β) (xs : List β) :
    ((xs.map fun y => (a, y)).idxOf (a, b)) = xs.idxOf b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hxb : x = b
      · subst x
        simp
      · have hpair : (a, x) ≠ (a, b) := by
          intro h
          exact hxb (Prod.ext_iff.mp h).2
        simp [hxb, hpair, ih]

lemma idxOf_product {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (xs : List α) (ys : List β) {a : α} {b : β}
    (ha : a ∈ xs) (hb : b ∈ ys) :
    (xs ×ˢ ys).idxOf (a, b) = xs.idxOf a * ys.length + ys.idxOf b := by
  induction xs generalizing a b with
  | nil => simp at ha
  | cons x xs ih =>
      by_cases hxa : x = a
      · subst x
        rw [List.product_cons]
        have hmem : (a, b) ∈ (ys.map fun y => (a, y)) :=
          List.mem_map.mpr ⟨b, hb, rfl⟩
        rw [List.idxOf_append_of_mem hmem, idxOf_map_const_prod]
        simp
      · have hnot : (a, b) ∉ (ys.map fun y => (x, y)) := by
          intro hmem
          rcases List.mem_map.mp hmem with ⟨y, _, hy⟩
          exact hxa (Prod.ext_iff.mp hy).1
        have haxs : a ∈ xs := by
          have hxa' : a ≠ x := fun h => hxa h.symm
          simpa [hxa'] using ha
        rw [List.product_cons, List.idxOf_append_of_notMem hnot, ih haxs hb]
        simp [hxa]
        ring

lemma idxOf_cellsRowMajor {B : Board} (c : Cell B) :
    (cellsRowMajor B).idxOf c = index c := by
  rcases c with ⟨r, c⟩
  rw [cellsRowMajor, idxOf_product]
  · simp [index]
  · simp
  · simp

/-- Row-major order, skipping one cell (usually the blank). -/
def cellsRowMajorExcept {B : Board} (skip : Cell B) : List (Cell B) :=
  (cellsRowMajor B).erase skip

lemma mem_cellsRowMajorExcept {B : Board} {skip c : Cell B} :
    c ∈ cellsRowMajorExcept skip ↔ c ≠ skip := by
  rw [cellsRowMajorExcept, (cellsRowMajor_nodup B).mem_erase_iff]
  simp [mem_cellsRowMajor]

lemma cellsRowMajorExcept_ne {B : Board} {skip c : Cell B}
    (hc : c ∈ cellsRowMajorExcept skip) : c ≠ skip :=
  mem_cellsRowMajorExcept.mp hc

lemma cellsRowMajorExcept_nodup {B : Board} (skip : Cell B) :
    (cellsRowMajorExcept skip).Nodup := by
  exact (cellsRowMajor_nodup B).erase skip

lemma cellsRowMajorExcept_length {B : Board} (skip : Cell B) :
    (cellsRowMajorExcept skip).length = B.tileCount := by
  have hmem : skip ∈ cellsRowMajor B := mem_cellsRowMajor skip
  have hlen := List.length_erase_add_one (a := skip) (l := cellsRowMajor B) hmem
  rw [← cellsRowMajorExcept, cellsRowMajor_length] at hlen
  rw [Board.tileCount]
  omega

/-- Index of `c` in the row-major cell list that skips `skip`. -/
def rankExcept {B : Board} (skip c : Cell B) : ℕ :=
  (cellsRowMajorExcept skip).idxOf c

lemma rankExcept_of_index_lt {B : Board} {skip c : Cell B} (h : index c < index skip) :
    rankExcept skip c = index c := by
  unfold rankExcept cellsRowMajorExcept
  rw [idxOf_erase_of_idxOf_lt]
  · exact idxOf_cellsRowMajor c
  · rw [idxOf_cellsRowMajor, idxOf_cellsRowMajor]
    exact h

lemma rankExcept_of_index_gt {B : Board} {skip c : Cell B} (h : index skip < index c) :
    rankExcept skip c = index c - 1 := by
  unfold rankExcept cellsRowMajorExcept
  rw [idxOf_erase_of_idxOf_gt]
  · rw [idxOf_cellsRowMajor]
  · rw [idxOf_cellsRowMajor, idxOf_cellsRowMajor]
    exact h

lemma rankExcept_lt {B : Board} {skip c : Cell B} (hc : c ≠ skip) :
    rankExcept skip c < (cellsRowMajorExcept skip).length := by
  exact List.idxOf_lt_length_of_mem (mem_cellsRowMajorExcept.mpr hc)

lemma rankExcept_getElem {B : Board} {skip c : Cell B} (hc : c ≠ skip) :
    (cellsRowMajorExcept skip)[rankExcept skip c]'(rankExcept_lt hc) = c := by
  exact
    List.idxOf_get (a := c) (l := cellsRowMajorExcept skip) (rankExcept_lt hc)

lemma rankExcept_cellsRowMajorExcept {B : Board} (skip : Cell B) (j : ℕ)
    (hj : j < (cellsRowMajorExcept skip).length) :
    rankExcept skip ((cellsRowMajorExcept skip)[j]'hj) = j := by
  simpa [rankExcept] using (cellsRowMajorExcept_nodup skip).idxOf_getElem j hj

lemma rankExcept_injective {B : Board} {skip c c' : Cell B}
    (hc : c ≠ skip) (hc' : c' ≠ skip) (h : rankExcept skip c = rankExcept skip c') :
    c = c' := by
  exact (rankExcept_getElem hc).symm.trans (by simpa [h] using rankExcept_getElem hc')

end NPuzzle.Rect
