import NPuzzle.Rect.EvenColumnRoute

namespace NPuzzle.Rect

/-!
Route skeleton for boards with an even number of rows.

The route uses the same first move as the even-column route: from `bottomRight`
to `cornerLeft`, then along the bottom row to the left edge.  It then snakes
through the upper rows and finally walks down the right edge to `cornerUp`.
-/

def evenRowsUpperRow (B : Board) (r : Fin B.rows) : List (Cell B) :=
  let cols :=
    if r.val % 2 = 0 then
      List.finRange (B.cols - 1)
    else
      (List.finRange (B.cols - 1)).reverse
  cols.map fun c => (r, colFromColsMinusOne (B := B) c)

def evenRowsUpperSnake (B : Board) : List (Cell B) :=
  (List.finRange (B.rows - 1)).reverse.flatMap fun r =>
    evenRowsUpperRow B (rowFromRowsMinusOne (B := B) r)

def evenRowsRightColumn (B : Board) : List (Cell B) :=
  (List.finRange (B.rows - 1)).map fun r =>
    (rowFromRowsMinusOne (B := B) r, (bottomRight B).2)

def evenRowsRouteXs (B : Board) : List (Cell B) :=
  evenColsBottomTail B ++ evenRowsUpperSnake B ++ evenRowsRightColumn B

lemma evenRowsUpperRow_length (B : Board) (r : Fin B.rows) :
    (evenRowsUpperRow B r).length = B.cols - 1 := by
  by_cases h : r.val % 2 = 0 <;>
    simp [evenRowsUpperRow, h]

lemma evenRowsUpperSnake_length (B : Board) :
    (evenRowsUpperSnake B).length = (B.rows - 1) * (B.cols - 1) := by
  simp [evenRowsUpperSnake, evenRowsUpperRow_length, List.length_flatMap]

lemma evenRowsRightColumn_length (B : Board) :
    (evenRowsRightColumn B).length = B.rows - 1 := by
  simp [evenRowsRightColumn]

lemma evenRowsRoute_length {B : Board} :
    (evenRowsRouteXs B).length = B.tileCount := by
  have hlen : (evenRowsRouteXs B).length + 1 = B.size := by
    simp [evenRowsRouteXs, evenColsBottomTail, evenRowsUpperSnake_length,
      evenRowsRightColumn_length, Board.size]
    have hc : B.cols - 1 + 1 = B.cols := by
      have hcolsPos := B.cols_pos
      omega
    have hr : B.rows - 1 + 1 = B.rows := by
      have hrowsPos := B.rows_pos
      omega
    nlinarith
  rw [Board.tileCount]
  have hsize := B.size_pos
  omega

lemma evenRowsUpperSnake_nonblank {B : Board} :
    ∀ c ∈ evenRowsUpperSnake B, c ≠ bottomRight B := by
  intro c hc
  rw [evenRowsUpperSnake] at hc
  simp only [List.mem_flatMap, List.mem_reverse, List.mem_finRange, true_and] at hc
  rcases hc with ⟨row, hrow⟩
  rw [evenRowsUpperRow] at hrow
  by_cases hpar : row.val % 2 = 0
  · simp only [rowFromRowsMinusOne_val, hpar, ↓reduceIte, List.mem_map,
      List.mem_finRange, true_and] at hrow
    rcases hrow with ⟨col, hEq⟩
    rw [← hEq]
    intro h
    have hv := congrArg (fun c : Cell B => c.1.val) h
    have hrowLt := row.isLt
    simp [bottomRight, rowFromRowsMinusOne] at hv
    omega
  · simp only [rowFromRowsMinusOne_val, hpar, ↓reduceIte, List.mem_map,
      List.mem_reverse, List.mem_finRange, true_and] at hrow
    rcases hrow with ⟨col, hEq⟩
    rw [← hEq]
    intro h
    have hv := congrArg (fun c : Cell B => c.1.val) h
    have hrowLt := row.isLt
    simp [bottomRight, rowFromRowsMinusOne] at hv
    omega

lemma evenRowsRightColumn_nonblank {B : Board} :
    ∀ c ∈ evenRowsRightColumn B, c ≠ bottomRight B := by
  intro c hc
  simp [evenRowsRightColumn] at hc
  rcases hc with ⟨row, rfl⟩
  intro h
  have hv := congrArg (fun c : Cell B => c.1.val) h
  have hrowLt := row.isLt
  simp [bottomRight, rowFromRowsMinusOne] at hv
  omega

lemma evenRowsRoute_nonblank {B : Board} :
    ∀ c ∈ evenRowsRouteXs B, c ≠ bottomRight B := by
  intro c hc
  simp [evenRowsRouteXs] at hc
  rcases hc with hc | hc | hc
  · exact evenColsBottomTail_nonblank c hc
  · exact evenRowsUpperSnake_nonblank c hc
  · exact evenRowsRightColumn_nonblank c hc

end NPuzzle.Rect
