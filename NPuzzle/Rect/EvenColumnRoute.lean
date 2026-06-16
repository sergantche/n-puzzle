import NPuzzle.Rect.TwoRowRoute

namespace NPuzzle.Rect

/-!
Route skeleton for boards with an even number of columns.

The intended closed route starts at `bottomRight`, first walks left along the
bottom row, then snakes through the remaining rows column by column.  This file
only establishes the first reusable facts about the explicit list: it contains
only nonblank cells and has exactly `tileCount` entries.
-/

def evenColsBottomTail (B : Board) : List (Cell B) :=
  (List.finRange (B.cols - 1)).reverse.map fun c =>
    ((bottomRight B).1, colFromColsMinusOne (B := B) c)

def evenColsUpperColumn (B : Board) (c : Fin B.cols) : List (Cell B) :=
  let rows :=
    if c.val % 2 = 0 then
      (List.finRange (B.rows - 1)).reverse
    else
      List.finRange (B.rows - 1)
  rows.map fun r => (rowFromRowsMinusOne (B := B) r, c)

def evenColsUpperSnake (B : Board) : List (Cell B) :=
  (List.finRange B.cols).flatMap (evenColsUpperColumn B)

def evenColsRouteXs (B : Board) : List (Cell B) :=
  evenColsBottomTail B ++ evenColsUpperSnake B

lemma evenColsUpperColumn_length (B : Board) (c : Fin B.cols) :
    (evenColsUpperColumn B c).length = B.rows - 1 := by
  by_cases h : c.val % 2 = 0 <;>
    simp [evenColsUpperColumn, h]

lemma evenColsUpperSnake_length (B : Board) :
    (evenColsUpperSnake B).length = B.cols * (B.rows - 1) := by
  simp [evenColsUpperSnake, evenColsUpperColumn_length, List.length_flatMap]

lemma evenColsRoute_length {B : Board} :
    (evenColsRouteXs B).length = B.tileCount := by
  have hlen : (evenColsRouteXs B).length + 1 = B.size := by
    simp [evenColsRouteXs, evenColsBottomTail, evenColsUpperSnake_length,
      Board.size]
    calc
      B.cols - 1 + B.cols * (B.rows - 1) + 1
          = (B.cols - 1 + 1) + B.cols * (B.rows - 1) := by omega
      _ = B.cols + B.cols * (B.rows - 1) := by
        rw [Nat.sub_add_cancel (Nat.succ_le_iff.mpr B.cols_pos)]
      _ = B.cols * (B.rows - 1) + B.cols := by omega
      _ = B.cols * ((B.rows - 1) + 1) := by rw [Nat.mul_succ]
      _ = B.cols * B.rows := by
        rw [Nat.sub_add_cancel (Nat.succ_le_iff.mpr B.rows_pos)]
      _ = B.rows * B.cols := by rw [Nat.mul_comm]
  rw [Board.tileCount]
  have hsize := B.size_pos
  omega

lemma evenColsBottomTail_nonblank {B : Board} :
    ∀ c ∈ evenColsBottomTail B, c ≠ bottomRight B := by
  intro c hc
  simp [evenColsBottomTail] at hc
  rcases hc with ⟨x, rfl⟩
  intro h
  have hv := congrArg (fun c : Cell B => c.2.val) h
  have hx := x.isLt
  simp [bottomRight, colFromColsMinusOne] at hv
  omega

lemma evenColsUpperSnake_nonblank {B : Board} :
    ∀ c ∈ evenColsUpperSnake B, c ≠ bottomRight B := by
  intro c hc
  rw [evenColsUpperSnake] at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and] at hc
  rcases hc with ⟨col, hcol⟩
  rw [evenColsUpperColumn] at hcol
  by_cases hpar : col.val % 2 = 0
  · simp [hpar] at hcol
    rcases hcol with ⟨row, _hrow, rfl⟩
    intro h
    have hv := congrArg (fun c : Cell B => c.1.val) h
    have hrowLt := row.isLt
    simp [bottomRight, rowFromRowsMinusOne] at hv
    omega
  · simp [hpar] at hcol
    rcases hcol with ⟨row, rfl⟩
    intro h
    have hv := congrArg (fun c : Cell B => c.1.val) h
    have hrowLt := row.isLt
    simp [bottomRight, rowFromRowsMinusOne] at hv
    omega

lemma evenColsRoute_nonblank {B : Board} :
    ∀ c ∈ evenColsRouteXs B, c ≠ bottomRight B := by
  intro c hc
  simp [evenColsRouteXs] at hc
  rcases hc with hc | hc
  · exact evenColsBottomTail_nonblank c hc
  · exact evenColsUpperSnake_nonblank c hc

end NPuzzle.Rect
