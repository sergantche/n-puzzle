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

lemma evenRowsUpperRow_nodup (B : Board) (row : Fin B.rows) :
    (evenRowsUpperRow B row).Nodup := by
  by_cases hpar : row.val % 2 = 0
  · simpa [evenRowsUpperRow, hpar] using
      (List.Nodup.map
        (l := List.finRange (B.cols - 1))
        (f := fun c => (row, colFromColsMinusOne (B := B) c))
        (by
          intro a b h
          apply Fin.ext
          have hv := congrArg (fun c : Cell B => c.2.val) h
          simpa [colFromColsMinusOne] using hv)
        (List.nodup_finRange (B.cols - 1)))
  · simpa [evenRowsUpperRow, hpar] using
      (List.Nodup.map
        (l := (List.finRange (B.cols - 1)).reverse)
        (f := fun c => (row, colFromColsMinusOne (B := B) c))
        (by
          intro a b h
          apply Fin.ext
          have hv := congrArg (fun c : Cell B => c.2.val) h
          simpa [colFromColsMinusOne] using hv)
        (List.nodup_reverse.mpr (List.nodup_finRange (B.cols - 1))))

lemma evenRowsUpperRow_mem_row {B : Board} {row : Fin B.rows} {c : Cell B}
    (hc : c ∈ evenRowsUpperRow B row) :
    c.1 = row := by
  rw [evenRowsUpperRow] at hc
  by_cases hpar : row.val % 2 = 0
  · simp [hpar] at hc
    rcases hc with ⟨col, _hcol, rfl⟩
    rfl
  · simp [hpar] at hc
    rcases hc with ⟨col, hEq⟩
    rw [← hEq]

lemma evenRowsUpperRow_not_right_col {B : Board} {row : Fin B.rows} :
    ∀ c ∈ evenRowsUpperRow B row, c.2 ≠ (bottomRight B).2 := by
  intro c hc
  rw [evenRowsUpperRow] at hc
  by_cases hpar : row.val % 2 = 0
  · simp [hpar] at hc
    rcases hc with ⟨col, _hcol, rfl⟩
    intro h
    have hv := congrArg (fun c : Fin B.cols => c.val) h
    have hcolLt := col.isLt
    simp [bottomRight, colFromColsMinusOne] at hv
    omega
  · simp [hpar] at hc
    rcases hc with ⟨col, hEq⟩
    rw [← hEq]
    intro h
    have hv := congrArg (fun c : Fin B.cols => c.val) h
    have hcolLt := col.isLt
    simp [bottomRight, colFromColsMinusOne] at hv
    omega

lemma evenRowsUpperRow_disjoint {B : Board} {a b : Fin B.rows}
    (hne : a ≠ b) :
    List.Disjoint (evenRowsUpperRow B a) (evenRowsUpperRow B b) := by
  rw [List.disjoint_left]
  intro c hca hcb
  have ha := evenRowsUpperRow_mem_row hca
  have hb := evenRowsUpperRow_mem_row hcb
  exact hne (ha.symm.trans hb)

lemma evenRowsUpperSnake_nodup (B : Board) :
    (evenRowsUpperSnake B).Nodup := by
  rw [evenRowsUpperSnake, List.nodup_flatMap]
  constructor
  · intro row _hrow
    exact evenRowsUpperRow_nodup B (rowFromRowsMinusOne (B := B) row)
  · exact (List.nodup_reverse.mpr (List.nodup_finRange (B.rows - 1))).imp
      (by
        intro a b hne
        apply evenRowsUpperRow_disjoint
        intro h
        apply hne
        apply Fin.ext
        have hv := congrArg (fun r : Fin B.rows => r.val) h
        simpa [rowFromRowsMinusOne] using hv)

lemma evenRowsRightColumn_nodup (B : Board) :
    (evenRowsRightColumn B).Nodup := by
  rw [evenRowsRightColumn]
  exact (List.nodup_finRange (B.rows - 1)).map
    (by
      intro a b h
      apply Fin.ext
      have hv := congrArg (fun c : Cell B => c.1.val) h
      simpa [rowFromRowsMinusOne] using hv)

lemma evenRowsBottomTail_disjoint_upperSnake {B : Board} :
    List.Disjoint (evenColsBottomTail B) (evenRowsUpperSnake B) := by
  rw [List.disjoint_left]
  intro c hbottom hupper
  simp [evenColsBottomTail] at hbottom
  rcases hbottom with ⟨col, rfl⟩
  rw [evenRowsUpperSnake] at hupper
  simp only [List.mem_flatMap, List.mem_reverse, List.mem_finRange, true_and] at hupper
  rcases hupper with ⟨upperRow, hupperRow⟩
  have hrow := evenRowsUpperRow_mem_row hupperRow
  have hv := congrArg (fun r : Fin B.rows => r.val) hrow
  have hrowLt := upperRow.isLt
  simp [bottomRight, rowFromRowsMinusOne] at hv
  omega

lemma evenRowsBottomTail_disjoint_rightColumn {B : Board} :
    List.Disjoint (evenColsBottomTail B) (evenRowsRightColumn B) := by
  rw [List.disjoint_left]
  intro c hbottom hright
  simp [evenColsBottomTail] at hbottom
  rcases hbottom with ⟨col, rfl⟩
  rw [evenRowsRightColumn] at hright
  simp only [List.mem_map, List.mem_finRange, true_and] at hright
  rcases hright with ⟨row, hEq⟩
  have hv := congrArg (fun c : Cell B => c.2.val) hEq
  have hcolLt := col.isLt
  simp [bottomRight, colFromColsMinusOne] at hv
  omega

lemma evenRowsUpperSnake_disjoint_rightColumn {B : Board} :
    List.Disjoint (evenRowsUpperSnake B) (evenRowsRightColumn B) := by
  rw [List.disjoint_left]
  intro c hupper hright
  rw [evenRowsUpperSnake] at hupper
  simp only [List.mem_flatMap, List.mem_reverse, List.mem_finRange, true_and] at hupper
  rcases hupper with ⟨upperRow, hupperRow⟩
  simp [evenRowsRightColumn] at hright
  rcases hright with ⟨row, hEq⟩
  have hcol := evenRowsUpperRow_not_right_col (B := B) (c := c) hupperRow
  have hrightCol := congrArg (fun c : Cell B => c.2) hEq
  exact hcol hrightCol.symm

lemma evenRowsRoute_nodup_cells {B : Board} :
    (evenRowsRouteXs B).Nodup := by
  rw [evenRowsRouteXs, List.nodup_append]
  constructor
  · rw [List.nodup_append]
    constructor
    · exact evenColsBottomTail_nodup_cells
    · constructor
      · exact evenRowsUpperSnake_nodup B
      · intro a ha b hb hab
        have hb' : a ∈ evenRowsUpperSnake B := by
          simpa [hab] using hb
        exact evenRowsBottomTail_disjoint_upperSnake ha hb'
  · constructor
    · exact evenRowsRightColumn_nodup B
    · intro a ha b hb hab
      have ha' : a ∈ evenColsBottomTail B ∨ a ∈ evenRowsUpperSnake B := by
        simpa using ha
      have hb' : a ∈ evenRowsRightColumn B := by
        simpa [hab] using hb
      rcases ha' with haBottom | haUpper
      · exact evenRowsBottomTail_disjoint_rightColumn haBottom hb'
      · exact evenRowsUpperSnake_disjoint_rightColumn haUpper hb'

lemma evenRowsRoute_nodup {B : Board} :
    ((nonblankSubtypeList
        (evenRowsRouteXs B)
        evenRowsRoute_nonblank).map
      (nonblankCellEquivFin B)).Nodup := by
  have hsub :
      (nonblankSubtypeList
        (evenRowsRouteXs B)
        evenRowsRoute_nonblank).Nodup := by
    apply List.Nodup.of_map (f := fun c : {c : Cell B // c ≠ bottomRight B} => c.1)
    simpa [nonblankSubtypeList_map_val] using evenRowsRoute_nodup_cells
  exact hsub.map (nonblankCellEquivFin B).injective

lemma evenRowsRoute_covers {B : Board} :
    ((nonblankSubtypeList
        (evenRowsRouteXs B)
        evenRowsRoute_nonblank).map
      (nonblankCellEquivFin B)).toFinset = Finset.univ := by
  apply finList_toFinset_eq_univ_of_nodup_length
  · exact evenRowsRoute_nodup
  · simpa [nonblankSubtypeList] using evenRowsRoute_length

end NPuzzle.Rect
