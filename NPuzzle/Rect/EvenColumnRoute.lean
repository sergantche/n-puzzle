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

lemma evenColsBottomTail_nodup_cells {B : Board} :
    (evenColsBottomTail B).Nodup := by
  rw [evenColsBottomTail]
  exact List.Nodup.map
      (l := (List.finRange (B.cols - 1)).reverse)
      (f := fun c => ((bottomRight B).1, colFromColsMinusOne (B := B) c))
      (by
        intro a b h
        apply Fin.ext
        have hv := congrArg (fun c : Cell B => c.2.val) h
        simpa [colFromColsMinusOne] using hv)
      (List.nodup_reverse.mpr (List.nodup_finRange (B.cols - 1)))

lemma evenColsUpperColumn_nodup (B : Board) (col : Fin B.cols) :
    (evenColsUpperColumn B col).Nodup := by
  by_cases hpar : col.val % 2 = 0
  · simpa [evenColsUpperColumn, hpar] using
      (List.Nodup.map
        (l := (List.finRange (B.rows - 1)).reverse)
        (f := fun r => (rowFromRowsMinusOne (B := B) r, col))
        (by
          intro a b h
          apply Fin.ext
          have hv := congrArg (fun c : Cell B => c.1.val) h
          simpa [rowFromRowsMinusOne] using hv)
        (List.nodup_reverse.mpr (List.nodup_finRange (B.rows - 1))))
  · simpa [evenColsUpperColumn, hpar] using
      (List.Nodup.map
        (l := List.finRange (B.rows - 1))
        (f := fun r => (rowFromRowsMinusOne (B := B) r, col))
        (by
          intro a b h
          apply Fin.ext
          have hv := congrArg (fun c : Cell B => c.1.val) h
          simpa [rowFromRowsMinusOne] using hv)
        (List.nodup_finRange (B.rows - 1)))

lemma evenColsUpperColumn_mem_col {B : Board} {col : Fin B.cols} {c : Cell B}
    (hc : c ∈ evenColsUpperColumn B col) :
    c.2 = col := by
  rw [evenColsUpperColumn] at hc
  by_cases hpar : col.val % 2 = 0
  · simp [hpar] at hc
    rcases hc with ⟨row, _hrow, rfl⟩
    rfl
  · simp [hpar] at hc
    rcases hc with ⟨row, rfl⟩
    rfl

lemma evenColsUpperColumn_not_bottom_row {B : Board} {col : Fin B.cols} :
    ∀ c ∈ evenColsUpperColumn B col, c.1 ≠ (bottomRight B).1 := by
  intro c hc
  rw [evenColsUpperColumn] at hc
  by_cases hpar : col.val % 2 = 0
  · simp [hpar] at hc
    rcases hc with ⟨row, _hrow, rfl⟩
    intro h
    have hv := congrArg (fun r : Fin B.rows => r.val) h
    have hrowLt := row.isLt
    simp [bottomRight, rowFromRowsMinusOne] at hv
    omega
  · simp [hpar] at hc
    rcases hc with ⟨row, rfl⟩
    intro h
    have hv := congrArg (fun r : Fin B.rows => r.val) h
    have hrowLt := row.isLt
    simp [bottomRight, rowFromRowsMinusOne] at hv
    omega

lemma evenColsUpperColumn_disjoint {B : Board} {a b : Fin B.cols}
    (hne : a ≠ b) :
    List.Disjoint (evenColsUpperColumn B a) (evenColsUpperColumn B b) := by
  rw [List.disjoint_left]
  intro c hca hcb
  have ha := evenColsUpperColumn_mem_col hca
  have hb := evenColsUpperColumn_mem_col hcb
  exact hne (ha.symm.trans hb)

lemma evenColsUpperSnake_nodup (B : Board) :
    (evenColsUpperSnake B).Nodup := by
  rw [evenColsUpperSnake, List.nodup_flatMap]
  constructor
  · intro col _hcol
    exact evenColsUpperColumn_nodup B col
  · exact (List.nodup_finRange B.cols).imp
      (by
        intro a b hne
        exact evenColsUpperColumn_disjoint hne)

lemma evenColsBottomTail_disjoint_upperSnake {B : Board} :
    List.Disjoint (evenColsBottomTail B) (evenColsUpperSnake B) := by
  rw [List.disjoint_left]
  intro c hbottom hupper
  simp [evenColsBottomTail] at hbottom
  rcases hbottom with ⟨col, rfl⟩
  rw [evenColsUpperSnake] at hupper
  simp only [List.mem_flatMap, List.mem_finRange, true_and] at hupper
  rcases hupper with ⟨upperCol, hupperCol⟩
  exact (evenColsUpperColumn_not_bottom_row
    (c := ((bottomRight B).1, colFromColsMinusOne (B := B) col))
    hupperCol) rfl

lemma evenColsRoute_nodup_cells {B : Board} :
    (evenColsRouteXs B).Nodup := by
  rw [evenColsRouteXs, List.nodup_append]
  constructor
  · exact evenColsBottomTail_nodup_cells
  · constructor
    · exact evenColsUpperSnake_nodup B
    · intro a ha b hb hab
      have hb' : a ∈ evenColsUpperSnake B := by
        simpa [hab] using hb
      exact evenColsBottomTail_disjoint_upperSnake ha hb'

lemma evenColsRoute_nodup {B : Board} :
    ((nonblankSubtypeList
        (evenColsRouteXs B)
        evenColsRoute_nonblank).map
      (nonblankCellEquivFin B)).Nodup := by
  have hsub :
      (nonblankSubtypeList
        (evenColsRouteXs B)
        evenColsRoute_nonblank).Nodup := by
    apply List.Nodup.of_map (f := fun c : {c : Cell B // c ≠ bottomRight B} => c.1)
    simpa [nonblankSubtypeList_map_val] using evenColsRoute_nodup_cells
  exact hsub.map (nonblankCellEquivFin B).injective

lemma evenColsRoute_covers {B : Board} :
    ((nonblankSubtypeList
        (evenColsRouteXs B)
        evenColsRoute_nonblank).map
      (nonblankCellEquivFin B)).toFinset = Finset.univ := by
  apply finList_toFinset_eq_univ_of_nodup_length
  · exact evenColsRoute_nodup
  · simpa [nonblankSubtypeList] using evenColsRoute_length

end NPuzzle.Rect
