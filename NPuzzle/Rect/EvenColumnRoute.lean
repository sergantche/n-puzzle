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

lemma evenColsUpperColumn_ne_nil {B : Board}
    (hrows : 2 ≤ B.rows) (col : Fin B.cols) :
    evenColsUpperColumn B col ≠ [] := by
  by_cases hpar : col.val % 2 = 0 <;>
    simp [evenColsUpperColumn, hpar] <;> omega

lemma isChain_evenColsBottomTail (B : Board) :
    List.IsChain adjacent (evenColsBottomTail B) := by
  rw [evenColsBottomTail, List.isChain_map]
  exact (isChain_finRange_reverse_val_pred (B.cols - 1)).imp
    (by
      intro a b h
      refine Or.inl ⟨rfl, Or.inr ?_⟩
      simpa [colFromColsMinusOne] using h)

lemma isChain_evenColsUpperColumn {B : Board} (col : Fin B.cols) :
    List.IsChain adjacent (evenColsUpperColumn B col) := by
  by_cases hpar : col.val % 2 = 0
  · rw [evenColsUpperColumn]
    simp only [hpar, ↓reduceIte]
    rw [List.isChain_map]
    exact (isChain_finRange_reverse_val_pred (B.rows - 1)).imp
      (by
        intro a b h
        refine Or.inr ⟨rfl, Or.inr ?_⟩
        simpa [rowFromRowsMinusOne] using h)
  · rw [evenColsUpperColumn]
    simp only [hpar, ↓reduceIte]
    rw [List.isChain_map]
    exact (isChain_finRange_val_succ (B.rows - 1)).imp
      (by
        intro a b h
        refine Or.inr ⟨rfl, Or.inl ?_⟩
        simpa [rowFromRowsMinusOne] using h)

lemma adjacent_evenColsUpperColumn_next {B : Board}
    {a b : Fin B.cols} (hnext : a.val + 1 = b.val) :
    ∀ x ∈ (evenColsUpperColumn B a).getLast?,
      ∀ y ∈ (evenColsUpperColumn B b).head?,
        adjacent x y := by
  intro x hx y hy
  by_cases hpar : a.val % 2 = 0
  · have hbpar : ¬ b.val % 2 = 0 := by omega
    simp [evenColsUpperColumn, hpar, hbpar] at hx hy
    rcases hx with ⟨rx, hxhead, rfl⟩
    rcases hy with ⟨ry, hyhead, rfl⟩
    have hrx := finRange_head_val_eq_zero hxhead
    have hry := finRange_head_val_eq_zero hyhead
    refine Or.inl ⟨?_, Or.inl ?_⟩
    · apply Fin.ext
      simp [rowFromRowsMinusOne]
      omega
    · exact hnext
  · have hbpar : b.val % 2 = 0 := by omega
    simp [evenColsUpperColumn, hpar, hbpar] at hx hy
    rcases hx with ⟨rx, hxlast, rfl⟩
    rcases hy with ⟨ry, hylast, rfl⟩
    have hrx := finRange_getLast_val_add_one hxlast
    have hry := finRange_getLast_val_add_one hylast
    refine Or.inl ⟨?_, Or.inl ?_⟩
    · apply Fin.ext
      simp [rowFromRowsMinusOne]
      omega
    · exact hnext

lemma isChain_evenColsUpperSnake {B : Board}
    (hrows : 2 ≤ B.rows) :
    List.IsChain adjacent (evenColsUpperSnake B) := by
  have hne :
      [] ∉ (List.finRange B.cols).map (evenColsUpperColumn B) := by
    intro h
    simp only [List.mem_map, List.mem_finRange, true_and] at h
    rcases h with ⟨col, hnil⟩
    exact evenColsUpperColumn_ne_nil hrows col hnil
  rw [evenColsUpperSnake, List.flatMap, List.isChain_flatten hne]
  constructor
  · intro l hl
    simp only [List.mem_map, List.mem_finRange, true_and] at hl
    rcases hl with ⟨col, rfl⟩
    exact isChain_evenColsUpperColumn col
  · rw [List.isChain_map]
    exact (isChain_finRange_val_succ B.cols).imp
      (by
        intro a b hnext
        exact adjacent_evenColsUpperColumn_next hnext)

lemma adjacent_bottomRight_evenColsBottomTail_head {B : Board} :
    ∀ y ∈ (evenColsBottomTail B).head?, adjacent (bottomRight B) y := by
  intro y hy
  simp [evenColsBottomTail] at hy
  rcases hy with ⟨c, hlast, rfl⟩
  have hmem : c ∈ (List.finRange (B.cols - 1)).getLast? := by
    rw [hlast]
    simp
  have hval := finRange_getLast_val_add_one hmem
  refine Or.inl ⟨rfl, Or.inr ?_⟩
  simp [bottomRight, colFromColsMinusOne]
  omega

lemma adjacent_evenColsBottomTail_upperSnake_head {B : Board}
    (hrows : 2 ≤ B.rows) :
    ∀ x ∈ (evenColsBottomTail B).getLast?,
      ∀ y ∈ (evenColsUpperSnake B).head?,
        adjacent x y := by
  intro x hx y hy
  simp [evenColsBottomTail] at hx
  rcases hx with ⟨c, hhead, rfl⟩
  have hmemBottom : c ∈ (List.finRange (B.cols - 1)).head? := by
    rw [hhead]
    simp
  have hcval := finRange_head_val_eq_zero hmemBottom
  have hzeroMem : (colZero B) ∈ (List.finRange B.cols).head? := by
    rw [finRange_head?_eq_zero B.cols_pos]
    simp [colZero]
  have hcolsCons : List.finRange B.cols = colZero B :: (List.finRange B.cols).tail :=
    List.eq_cons_of_mem_head? hzeroMem
  rw [evenColsUpperSnake, hcolsCons] at hy
  simp only [List.flatMap_cons] at hy
  rw [List.head?_append_of_ne_nil
    (evenColsUpperColumn B (colZero B))
    (evenColsUpperColumn_ne_nil hrows (colZero B))] at hy
  simp [evenColsUpperColumn, colZero] at hy
  rcases hy with ⟨r, hlast, rfl⟩
  have hrval := finRange_getLast_val_add_one hlast
  refine Or.inr ⟨?_, Or.inr ?_⟩
  · apply Fin.ext
    simp [colFromColsMinusOne]
    omega
  · simp [bottomRight, rowFromRowsMinusOne]
    omega

lemma evenColsUpperSnake_ne_nil {B : Board}
    (hrows : 2 ≤ B.rows) :
    evenColsUpperSnake B ≠ [] := by
  rw [evenColsUpperSnake, List.flatMap]
  apply List.flatten_ne_nil_iff.mpr
  refine ⟨evenColsUpperColumn B (colZero B), ?_, evenColsUpperColumn_ne_nil hrows (colZero B)⟩
  exact List.mem_map_of_mem (f := evenColsUpperColumn B) (List.mem_finRange (colZero B))

lemma evenColsUpperSnake_getLast?_eq_lastColumn {B : Board}
    (hrows : 2 ≤ B.rows) :
    (evenColsUpperSnake B).getLast? =
      (evenColsUpperColumn B (bottomRight B).2).getLast? := by
  let cols := (List.finRange B.cols).map (evenColsUpperColumn B)
  have hcols_ne : cols ≠ [] := by
    simp [cols, List.finRange_eq_nil_iff, B.cols_pos.ne']
  have hcols_last :
      cols.getLast hcols_ne = evenColsUpperColumn B (bottomRight B).2 := by
    apply List.getLast_of_mem_getLast?
    rw [List.getLast?_eq_getLast_of_ne_nil hcols_ne]
    simp [cols, List.getLast_eq_getElem, bottomRight]
  have hcols_last_ne : cols.getLast hcols_ne ≠ [] := by
    rw [hcols_last]
    exact evenColsUpperColumn_ne_nil hrows (bottomRight B).2
  have hflat_ne : cols.flatten ≠ [] := by
    exact List.flatten_ne_nil_iff.mpr
      ⟨cols.getLast hcols_ne, List.getLast_mem hcols_ne, hcols_last_ne⟩
  have hinner_ne : evenColsUpperColumn B (bottomRight B).2 ≠ [] :=
    evenColsUpperColumn_ne_nil hrows (bottomRight B).2
  rw [evenColsUpperSnake, List.flatMap]
  change cols.flatten.getLast? =
    (evenColsUpperColumn B (bottomRight B).2).getLast?
  rw [List.getLast?_eq_getLast_of_ne_nil hflat_ne,
    List.getLast?_eq_getLast_of_ne_nil hinner_ne]
  rw [List.getLast_flatten_eq_getLast_getLast (l := cols) hflat_ne hcols_last_ne]
  congr

lemma adjacent_evenColsUpperColumn_last_bottomRight {B : Board}
    {col : Fin B.cols}
    (hcolLast : col.val + 1 = B.cols)
    (hodd : ¬ col.val % 2 = 0) :
    ∀ x ∈ (evenColsUpperColumn B col).getLast?,
      adjacent x (bottomRight B) := by
  intro x hx
  simp [evenColsUpperColumn, hodd] at hx
  rcases hx with ⟨row, hlast, rfl⟩
  have hrow := finRange_getLast_val_add_one hlast
  refine Or.inr ⟨?_, Or.inl ?_⟩
  · apply Fin.ext
    simp [bottomRight]
    omega
  · simp [bottomRight, rowFromRowsMinusOne]
    omega

lemma adjacent_evenColsUpperSnake_bottomRight {B : Board}
    (hrows : 2 ≤ B.rows) (hcolsEven : B.cols % 2 = 0) :
    ∀ x ∈ (evenColsUpperSnake B).getLast?,
      ∀ y ∈ [bottomRight B].head?,
        adjacent x y := by
  intro x hx y hy
  simp at hy
  subst y
  rw [evenColsUpperSnake_getLast?_eq_lastColumn hrows] at hx
  exact adjacent_evenColsUpperColumn_last_bottomRight
    (col := (bottomRight B).2)
    (by
      change B.cols - 1 + 1 = B.cols
      have hcolsPos := B.cols_pos
      omega)
    (by
      change ¬ (B.cols - 1) % 2 = 0
      have hcolsPos := B.cols_pos
      omega)
    x hx

lemma adjacent_evenColsRoute_bottomRight {B : Board}
    (hrows : 2 ≤ B.rows) (hcolsEven : B.cols % 2 = 0) :
    ∀ x ∈ (evenColsRouteXs B).getLast?,
      ∀ y ∈ [bottomRight B].head?,
        adjacent x y := by
  intro x hx y hy
  rw [evenColsRouteXs,
    List.getLast?_append_of_ne_nil (evenColsBottomTail B) (evenColsUpperSnake_ne_nil hrows)] at hx
  exact adjacent_evenColsUpperSnake_bottomRight hrows hcolsEven x hx y hy

lemma evenColsRoute_chain_open {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    AdjacentChain (bottomRight B) (evenColsRouteXs B) := by
  rw [adjacentChain_iff_isChain]
  rw [evenColsRouteXs]
  apply List.IsChain.cons
  · apply List.IsChain.append
    · exact isChain_evenColsBottomTail B
    · exact isChain_evenColsUpperSnake hrows
    · exact adjacent_evenColsBottomTail_upperSnake_head hrows
  · intro y hy
    have hbottom_ne : evenColsBottomTail B ≠ [] := by
      simp [evenColsBottomTail]
      omega
    rw [List.head?_append_of_ne_nil (evenColsBottomTail B) hbottom_ne] at hy
    exact adjacent_bottomRight_evenColsBottomTail_head y hy

lemma evenColsRoute_chain {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hcolsEven : B.cols % 2 = 0) :
    AdjacentChain (bottomRight B) (evenColsRouteXs B ++ [bottomRight B]) := by
  rw [adjacentChain_iff_isChain]
  change List.IsChain adjacent ((bottomRight B :: evenColsRouteXs B) ++ [bottomRight B])
  apply List.IsChain.append
  · exact (adjacentChain_iff_isChain (bottomRight B) (evenColsRouteXs B)).mp
      (evenColsRoute_chain_open hrows hcols)
  · simp
  · intro x hx y hy
    simp at hy
    subst y
    have hroute_ne : evenColsRouteXs B ≠ [] := by
      simp [evenColsRouteXs, evenColsBottomTail]
      omega
    have hxRoute : x ∈ (evenColsRouteXs B).getLast? := by
      cases hroute : evenColsRouteXs B with
      | nil =>
          exact (hroute_ne hroute).elim
      | cons z zs =>
          rw [hroute] at hx
          simpa using hx
    exact adjacent_evenColsRoute_bottomRight hrows hcolsEven x hxRoute (bottomRight B) (by simp)

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
