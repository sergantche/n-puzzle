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

lemma evenRowsUpperRow_ne_nil {B : Board}
    (hcols : 2 ≤ B.cols) (row : Fin B.rows) :
    evenRowsUpperRow B row ≠ [] := by
  by_cases hpar : row.val % 2 = 0 <;>
    simp [evenRowsUpperRow, hpar] <;> omega

lemma isChain_evenRowsUpperRow {B : Board} (row : Fin B.rows) :
    List.IsChain adjacent (evenRowsUpperRow B row) := by
  by_cases hpar : row.val % 2 = 0
  · rw [evenRowsUpperRow]
    simp only [hpar, ↓reduceIte]
    rw [List.isChain_map]
    exact (isChain_finRange_val_succ (B.cols - 1)).imp
      (by
        intro a b h
        refine Or.inl ⟨rfl, Or.inl ?_⟩
        simpa [colFromColsMinusOne] using h)
  · rw [evenRowsUpperRow]
    simp only [hpar, ↓reduceIte]
    rw [List.isChain_map]
    exact (isChain_finRange_reverse_val_pred (B.cols - 1)).imp
      (by
        intro a b h
        refine Or.inl ⟨rfl, Or.inr ?_⟩
        simpa [colFromColsMinusOne] using h)

lemma adjacent_evenRowsUpperRow_next {B : Board}
    {a b : Fin (B.rows - 1)} (hnext : b.val + 1 = a.val) :
    ∀ x ∈ (evenRowsUpperRow B (rowFromRowsMinusOne (B := B) a)).getLast?,
      ∀ y ∈ (evenRowsUpperRow B (rowFromRowsMinusOne (B := B) b)).head?,
        adjacent x y := by
  intro x hx y hy
  by_cases hpar : a.val % 2 = 0
  · have hbpar : ¬ b.val % 2 = 0 := by omega
    simp [evenRowsUpperRow, rowFromRowsMinusOne, hpar, hbpar] at hx hy
    rcases hx with ⟨cx, hxlast, rfl⟩
    rcases hy with ⟨cy, hylast, rfl⟩
    have hcx := finRange_getLast_val_add_one hxlast
    have hcy := finRange_getLast_val_add_one hylast
    refine Or.inr ⟨?_, Or.inr ?_⟩
    · apply Fin.ext
      simp [colFromColsMinusOne]
      omega
    · simpa [rowFromRowsMinusOne] using hnext
  · have hbpar : b.val % 2 = 0 := by omega
    simp [evenRowsUpperRow, rowFromRowsMinusOne, hpar, hbpar] at hx hy
    rcases hx with ⟨cx, hxhead, rfl⟩
    rcases hy with ⟨cy, hyhead, rfl⟩
    have hcx := finRange_head_val_eq_zero hxhead
    have hcy := finRange_head_val_eq_zero hyhead
    refine Or.inr ⟨?_, Or.inr ?_⟩
    · apply Fin.ext
      simp [colFromColsMinusOne]
      omega
    · simpa [rowFromRowsMinusOne] using hnext

lemma isChain_evenRowsUpperSnake {B : Board}
    (hcols : 2 ≤ B.cols) :
    List.IsChain adjacent (evenRowsUpperSnake B) := by
  have hne :
      [] ∉ ((List.finRange (B.rows - 1)).reverse.map fun row =>
        evenRowsUpperRow B (rowFromRowsMinusOne (B := B) row)) := by
    intro h
    simp only [List.mem_map, List.mem_reverse, List.mem_finRange, true_and] at h
    rcases h with ⟨row, hnil⟩
    exact evenRowsUpperRow_ne_nil hcols (rowFromRowsMinusOne (B := B) row) hnil
  rw [evenRowsUpperSnake, List.flatMap, List.isChain_flatten hne]
  constructor
  · intro l hl
    simp only [List.mem_map, List.mem_reverse, List.mem_finRange, true_and] at hl
    rcases hl with ⟨row, rfl⟩
    exact isChain_evenRowsUpperRow (rowFromRowsMinusOne (B := B) row)
  · rw [List.isChain_map]
    exact (isChain_finRange_reverse_val_pred (B.rows - 1)).imp
      (by
        intro a b hnext
        exact adjacent_evenRowsUpperRow_next hnext)

lemma evenRowsUpperSnake_ne_nil {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    evenRowsUpperSnake B ≠ [] := by
  intro hnil
  have hlen := evenRowsUpperSnake_length B
  rw [hnil] at hlen
  simp at hlen
  have hprod : 0 < (B.rows - 1) * (B.cols - 1) :=
    Nat.mul_pos (by omega) (by omega)
  omega

lemma evenRowsRightColumn_ne_nil {B : Board}
    (hrows : 2 ≤ B.rows) :
    evenRowsRightColumn B ≠ [] := by
  intro hnil
  have hlen := evenRowsRightColumn_length B
  rw [hnil] at hlen
  simp at hlen
  omega

lemma isChain_evenRowsRightColumn {B : Board} :
    List.IsChain adjacent (evenRowsRightColumn B) := by
  rw [evenRowsRightColumn, List.isChain_map]
  exact (isChain_finRange_val_succ (B.rows - 1)).imp
    (by
      intro a b h
      refine Or.inr ⟨rfl, Or.inl ?_⟩
      simpa [rowFromRowsMinusOne] using h)

lemma adjacent_evenRowsBottomTail_upperSnake_head {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsEven : B.rows % 2 = 0) :
    ∀ x ∈ (evenColsBottomTail B).getLast?,
      ∀ y ∈ (evenRowsUpperSnake B).head?,
        adjacent x y := by
  intro x hx y hy
  simp [evenColsBottomTail] at hx
  rcases hx with ⟨c, hhead, rfl⟩
  have hmemBottom : c ∈ (List.finRange (B.cols - 1)).head? := by
    rw [hhead]
    simp
  have hcval := finRange_head_val_eq_zero hmemBottom
  let lastUpperRow : Fin (B.rows - 1) := ⟨B.rows - 2, by omega⟩
  have hlastUpperRowMem :
      lastUpperRow ∈ (List.finRange (B.rows - 1)).reverse.head? := by
    rw [List.head?_reverse]
    rw [finRange_getLast?_eq_last (by omega : 0 < B.rows - 1)]
    simp [lastUpperRow]
    omega
  have hrowsCons :
      (List.finRange (B.rows - 1)).reverse =
        lastUpperRow :: (List.finRange (B.rows - 1)).reverse.tail :=
    List.eq_cons_of_mem_head? hlastUpperRowMem
  rw [evenRowsUpperSnake, hrowsCons] at hy
  simp only [List.flatMap_cons] at hy
  rw [List.head?_append_of_ne_nil
    (evenRowsUpperRow B (rowFromRowsMinusOne (B := B) lastUpperRow))
    (evenRowsUpperRow_ne_nil hcols (rowFromRowsMinusOne (B := B) lastUpperRow))] at hy
  have hrowEven :
      lastUpperRow.val % 2 = 0 := by
    simp [lastUpperRow]
    omega
  simp [evenRowsUpperRow, rowFromRowsMinusOne, hrowEven] at hy
  rcases hy with ⟨d, dhead, rfl⟩
  have hdval := finRange_head_val_eq_zero dhead
  refine Or.inr ⟨?_, Or.inr ?_⟩
  · apply Fin.ext
    simp [colFromColsMinusOne]
    omega
  · simp [bottomRight, lastUpperRow]
    omega

lemma evenRowsUpperSnake_getLast?_eq_topRow {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    (evenRowsUpperSnake B).getLast? =
      (evenRowsUpperRow B
        (rowFromRowsMinusOne (B := B) (⟨0, by omega⟩ : Fin (B.rows - 1)))).getLast? := by
  let row0 : Fin (B.rows - 1) := ⟨0, by omega⟩
  let rows :=
    ((List.finRange (B.rows - 1)).reverse.map fun row =>
      evenRowsUpperRow B (rowFromRowsMinusOne (B := B) row))
  have hrowsLast? :
      rows.getLast? =
        some (evenRowsUpperRow B (rowFromRowsMinusOne (B := B) row0)) := by
    dsimp [rows]
    rw [List.getLast?_map, List.getLast?_reverse,
      finRange_head?_eq_zero (by omega : 0 < B.rows - 1)]
    simp [row0]
  have hmemRowsLast :
      evenRowsUpperRow B (rowFromRowsMinusOne (B := B) row0) ∈ rows.getLast? := by
    rw [hrowsLast?]
    simp
  have hrows_ne : rows ≠ [] := by
    exact List.ne_nil_of_mem (List.mem_of_mem_getLast? hmemRowsLast)
  have hrows_last :
      rows.getLast hrows_ne =
        evenRowsUpperRow B (rowFromRowsMinusOne (B := B) row0) :=
    List.getLast_of_mem_getLast? hmemRowsLast
  have hrows_last_ne : rows.getLast hrows_ne ≠ [] := by
    rw [hrows_last]
    exact evenRowsUpperRow_ne_nil hcols (rowFromRowsMinusOne (B := B) row0)
  have hflat_ne : rows.flatten ≠ [] := by
    exact List.flatten_ne_nil_iff.mpr
      ⟨rows.getLast hrows_ne, List.getLast_mem hrows_ne, hrows_last_ne⟩
  have hinner_ne :
      evenRowsUpperRow B (rowFromRowsMinusOne (B := B) row0) ≠ [] :=
    evenRowsUpperRow_ne_nil hcols (rowFromRowsMinusOne (B := B) row0)
  rw [evenRowsUpperSnake, List.flatMap]
  change rows.flatten.getLast? =
    (evenRowsUpperRow B (rowFromRowsMinusOne (B := B) row0)).getLast?
  rw [List.getLast?_eq_getLast_of_ne_nil hflat_ne,
    List.getLast?_eq_getLast_of_ne_nil hinner_ne]
  rw [List.getLast_flatten_eq_getLast_getLast (l := rows) hflat_ne hrows_last_ne]
  congr

lemma adjacent_evenRowsUpperSnake_rightColumn_head {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    ∀ x ∈ (evenRowsUpperSnake B).getLast?,
      ∀ y ∈ (evenRowsRightColumn B).head?,
        adjacent x y := by
  intro x hx y hy
  rw [evenRowsUpperSnake_getLast?_eq_topRow hrows hcols] at hx
  simp [evenRowsUpperRow, evenRowsRightColumn] at hx hy
  rcases hx with ⟨cx, hxlast, rfl⟩
  rcases hy with ⟨ry, hyhead, rfl⟩
  have hcx := finRange_getLast_val_add_one hxlast
  have hry := finRange_head_val_eq_zero hyhead
  refine Or.inl ⟨?_, Or.inl ?_⟩
  · apply Fin.ext
    simp [rowFromRowsMinusOne]
    omega
  · simp [bottomRight, colFromColsMinusOne]
    omega

lemma adjacent_evenRowsRightColumn_bottomRight {B : Board} :
    ∀ x ∈ (evenRowsRightColumn B).getLast?,
      ∀ y ∈ [bottomRight B].head?,
        adjacent x y := by
  intro x hx y hy
  simp [evenRowsRightColumn] at hx hy
  rcases hx with ⟨row, hlast, rfl⟩
  subst y
  have hrow := finRange_getLast_val_add_one hlast
  refine Or.inr ⟨rfl, Or.inl ?_⟩
  simp [bottomRight, rowFromRowsMinusOne]
  omega

lemma adjacent_evenRowsRoute_bottomRight {B : Board}
    (hrows : 2 ≤ B.rows) :
    ∀ x ∈ (evenRowsRouteXs B).getLast?,
      ∀ y ∈ [bottomRight B].head?,
        adjacent x y := by
  intro x hx y hy
  rw [evenRowsRouteXs,
    List.getLast?_append_of_ne_nil
      (evenColsBottomTail B ++ evenRowsUpperSnake B)
      (evenRowsRightColumn_ne_nil hrows)] at hx
  exact adjacent_evenRowsRightColumn_bottomRight x hx y hy

lemma evenRowsRoute_chain_open {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsEven : B.rows % 2 = 0) :
    AdjacentChain (bottomRight B) (evenRowsRouteXs B) := by
  rw [adjacentChain_iff_isChain]
  rw [evenRowsRouteXs, List.append_assoc]
  apply List.IsChain.cons
  · apply List.IsChain.append
    · exact isChain_evenColsBottomTail B
    · apply List.IsChain.append
      · exact isChain_evenRowsUpperSnake hcols
      · exact isChain_evenRowsRightColumn
      · exact adjacent_evenRowsUpperSnake_rightColumn_head hrows hcols
    · intro x hx y hy
      rw [List.head?_append_of_ne_nil
        (evenRowsUpperSnake B)
        (evenRowsUpperSnake_ne_nil hrows hcols)] at hy
      exact adjacent_evenRowsBottomTail_upperSnake_head hrows hcols hrowsEven x hx y hy
  · intro y hy
    have hbottom_ne : evenColsBottomTail B ≠ [] := by
      simp [evenColsBottomTail]
      omega
    rw [List.head?_append_of_ne_nil (evenColsBottomTail B) hbottom_ne] at hy
    exact adjacent_bottomRight_evenColsBottomTail_head y hy

lemma evenRowsRoute_chain {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsEven : B.rows % 2 = 0) :
    AdjacentChain (bottomRight B) (evenRowsRouteXs B ++ [bottomRight B]) := by
  rw [adjacentChain_iff_isChain]
  change List.IsChain adjacent ((bottomRight B :: evenRowsRouteXs B) ++ [bottomRight B])
  apply List.IsChain.append
  · exact (adjacentChain_iff_isChain (bottomRight B) (evenRowsRouteXs B)).mp
      (evenRowsRoute_chain_open hrows hcols hrowsEven)
  · simp
  · intro x hx y hy
    simp at hy
    subst y
    have hroute_ne : evenRowsRouteXs B ≠ [] := by
      simp [evenRowsRouteXs, evenColsBottomTail]
      omega
    have hxRoute : x ∈ (evenRowsRouteXs B).getLast? := by
      cases hroute : evenRowsRouteXs B with
      | nil =>
          exact (hroute_ne hroute).elim
      | cons z zs =>
          rw [hroute] at hx
          simpa using hx
    exact adjacent_evenRowsRoute_bottomRight hrows x hxRoute (bottomRight B) (by simp)

end NPuzzle.Rect
