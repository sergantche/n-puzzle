import NPuzzle.Rect.EvenColumnRoute

namespace NPuzzle.Rect

/-!
Explicit near-full route candidate for odd-by-odd boards.

The route starts with the usual bottom tail, snakes through all nonblank cells
except `cornerUpLeft`, and ends at `cornerUp`.  Closing it through
`bottomRight` gives the near-full cycle shape needed by the odd-by-odd
sufficiency tail.
-/

def oddOddColBeforeRight (B : Board) : Fin B.cols :=
  ⟨B.cols - 2, by
    have hpos := B.cols_pos
    omega⟩

def oddOddColOne {B : Board} (hcols : 2 ≤ B.cols) : Fin B.cols :=
  ⟨1, by omega⟩

def oddOddMiddleCol {B : Board} (c : Fin (B.cols - 3)) : Fin B.cols :=
  ⟨c.val + 1, by
    have hc := c.isLt
    omega⟩

@[simp]
lemma oddOddColBeforeRight_val {B : Board} :
    (oddOddColBeforeRight B).val = B.cols - 2 :=
  rfl

@[simp]
lemma oddOddColOne_val {B : Board} (hcols : 2 ≤ B.cols) :
    (oddOddColOne hcols).val = 1 :=
  rfl

@[simp]
lemma oddOddMiddleCol_val {B : Board} (c : Fin (B.cols - 3)) :
    (oddOddMiddleCol (B := B) c).val = c.val + 1 :=
  rfl

def oddOddLeftColumn (B : Board) : List (Cell B) :=
  (List.finRange (B.rows - 1)).reverse.map fun r =>
    (rowFromRowsMinusOne (B := B) r, colZero B)

def oddOddMiddleColumn (B : Board) (c : Fin (B.cols - 3)) : List (Cell B) :=
  let rows :=
    if (c.val + 1) % 2 = 1 then
      List.finRange (B.rows - 1)
    else
      (List.finRange (B.rows - 1)).reverse
  rows.map fun r =>
    (rowFromRowsMinusOne (B := B) r, oddOddMiddleCol (B := B) c)

def oddOddMiddleSnake (B : Board) : List (Cell B) :=
  (List.finRange (B.cols - 3)).flatMap (oddOddMiddleColumn B)

def oddOddCapRow (B : Board) (r : Fin (B.rows - 2)) : List (Cell B) :=
  let row := rowFromRowsMinusTwo (B := B) r
  if r.val % 2 = 0 then
    [(row, oddOddColBeforeRight B), (row, (bottomRight B).2)]
  else
    [(row, (bottomRight B).2), (row, oddOddColBeforeRight B)]

def oddOddCapRows (B : Board) : List (Cell B) :=
  (List.finRange (B.rows - 2)).flatMap (oddOddCapRow B)

def oddOddCap (B : Board) : List (Cell B) :=
  oddOddCapRows B ++ [cornerUp B]

def oddOddRouteXs (B : Board) : List (Cell B) :=
  evenColsBottomTail B ++ oddOddLeftColumn B ++ oddOddMiddleSnake B ++ oddOddCap B

lemma oddOddLeftColumn_length (B : Board) :
    (oddOddLeftColumn B).length = B.rows - 1 := by
  simp [oddOddLeftColumn]

lemma oddOddMiddleColumn_length (B : Board) (c : Fin (B.cols - 3)) :
    (oddOddMiddleColumn B c).length = B.rows - 1 := by
  by_cases hpar : (c.val + 1) % 2 = 1 <;>
    simp [oddOddMiddleColumn, hpar]

lemma oddOddMiddleSnake_length (B : Board) :
    (oddOddMiddleSnake B).length = (B.cols - 3) * (B.rows - 1) := by
  simp [oddOddMiddleSnake, oddOddMiddleColumn_length, List.length_flatMap]

lemma oddOddCapRow_length (B : Board) (r : Fin (B.rows - 2)) :
    (oddOddCapRow B r).length = 2 := by
  by_cases hpar : r.val % 2 = 0 <;>
    simp [oddOddCapRow, hpar]

lemma oddOddCap_length (B : Board) :
    (oddOddCap B).length = 2 * (B.rows - 2) + 1 := by
  simp [oddOddCap, oddOddCapRows, oddOddCapRow_length, List.length_flatMap, Nat.mul_comm]

lemma isChain_oddOddLeftColumn (B : Board) :
    List.IsChain adjacent (oddOddLeftColumn B) := by
  rw [oddOddLeftColumn, List.isChain_map]
  exact (isChain_finRange_reverse_val_pred (B.rows - 1)).imp
    (by
      intro a b h
      refine Or.inr ⟨rfl, Or.inr ?_⟩
      simpa [rowFromRowsMinusOne] using h)

lemma isChain_oddOddMiddleColumn {B : Board} (c : Fin (B.cols - 3)) :
    List.IsChain adjacent (oddOddMiddleColumn B c) := by
  by_cases hpar : (c.val + 1) % 2 = 1
  · rw [oddOddMiddleColumn]
    simp only [hpar, ↓reduceIte]
    rw [List.isChain_map]
    exact (isChain_finRange_val_succ (B.rows - 1)).imp
      (by
        intro a b h
        refine Or.inr ⟨rfl, Or.inl ?_⟩
        simpa [rowFromRowsMinusOne] using h)
  · rw [oddOddMiddleColumn]
    simp only [hpar, ↓reduceIte]
    rw [List.isChain_map]
    exact (isChain_finRange_reverse_val_pred (B.rows - 1)).imp
      (by
        intro a b h
        refine Or.inr ⟨rfl, Or.inr ?_⟩
        simpa [rowFromRowsMinusOne] using h)

lemma oddOddMiddleColumn_ne_nil {B : Board}
    (hrows : 2 ≤ B.rows) (c : Fin (B.cols - 3)) :
    oddOddMiddleColumn B c ≠ [] := by
  by_cases hpar : (c.val + 1) % 2 = 1 <;>
    simp [oddOddMiddleColumn, hpar] <;> omega

lemma adjacent_oddOddMiddleColumn_next {B : Board}
    {a b : Fin (B.cols - 3)} (hnext : a.val + 1 = b.val) :
    ∀ x ∈ (oddOddMiddleColumn B a).getLast?,
      ∀ y ∈ (oddOddMiddleColumn B b).head?,
        adjacent x y := by
  intro x hx y hy
  by_cases hpar : (a.val + 1) % 2 = 1
  · have hbpar : ¬ (b.val + 1) % 2 = 1 := by omega
    simp [oddOddMiddleColumn, hpar, hbpar] at hx hy
    rcases hx with ⟨rx, hxlast, rfl⟩
    rcases hy with ⟨ry, hylast, rfl⟩
    have hrx := finRange_getLast_val_add_one hxlast
    have hry := finRange_getLast_val_add_one hylast
    refine Or.inl ⟨?_, Or.inl ?_⟩
    · apply Fin.ext
      simp [rowFromRowsMinusOne]
      omega
    · simp [oddOddMiddleCol]
      omega
  · have hbpar : (b.val + 1) % 2 = 1 := by omega
    simp [oddOddMiddleColumn, hpar, hbpar] at hx hy
    rcases hx with ⟨rx, hxhead, rfl⟩
    rcases hy with ⟨ry, hyhead, rfl⟩
    have hrx := finRange_head_val_eq_zero hxhead
    have hry := finRange_head_val_eq_zero hyhead
    refine Or.inl ⟨?_, Or.inl ?_⟩
    · apply Fin.ext
      simp [rowFromRowsMinusOne]
      omega
    · simp [oddOddMiddleCol]
      omega

lemma isChain_oddOddMiddleSnake {B : Board}
    (hrows : 2 ≤ B.rows) :
    List.IsChain adjacent (oddOddMiddleSnake B) := by
  have hne :
      [] ∉ (List.finRange (B.cols - 3)).map (oddOddMiddleColumn B) := by
    intro h
    simp only [List.mem_map, List.mem_finRange, true_and] at h
    rcases h with ⟨col, hnil⟩
    exact oddOddMiddleColumn_ne_nil hrows col hnil
  rw [oddOddMiddleSnake, List.flatMap, List.isChain_flatten hne]
  constructor
  · intro l hl
    simp only [List.mem_map, List.mem_finRange, true_and] at hl
    rcases hl with ⟨col, rfl⟩
    exact isChain_oddOddMiddleColumn col
  · rw [List.isChain_map]
    exact (isChain_finRange_val_succ (B.cols - 3)).imp
      (by
        intro a b hnext
        exact adjacent_oddOddMiddleColumn_next hnext)

lemma isChain_oddOddCapRow {B : Board}
    (hcols : 2 ≤ B.cols) (r : Fin (B.rows - 2)) :
    List.IsChain adjacent (oddOddCapRow B r) := by
  by_cases hpar : r.val % 2 = 0
  · simp [oddOddCapRow, hpar]
    refine Or.inl ⟨rfl, Or.inl ?_⟩
    change B.cols - 2 + 1 = B.cols - 1
    omega
  · simp [oddOddCapRow, hpar]
    refine Or.inl ⟨rfl, Or.inr ?_⟩
    change B.cols - 2 + 1 = B.cols - 1
    omega

lemma oddOddCapRow_ne_nil {B : Board} (r : Fin (B.rows - 2)) :
    oddOddCapRow B r ≠ [] := by
  by_cases hpar : r.val % 2 = 0 <;>
    simp [oddOddCapRow, hpar]

lemma adjacent_oddOddCapRow_next {B : Board}
    {a b : Fin (B.rows - 2)} (hnext : a.val + 1 = b.val) :
    ∀ x ∈ (oddOddCapRow B a).getLast?,
      ∀ y ∈ (oddOddCapRow B b).head?,
        adjacent x y := by
  intro x hx y hy
  by_cases hpar : a.val % 2 = 0
  · have hbpar : ¬ b.val % 2 = 0 := by omega
    simp [oddOddCapRow, hpar, hbpar] at hx hy
    subst x
    subst y
    refine Or.inr ⟨rfl, Or.inl ?_⟩
    simp [rowFromRowsMinusTwo]
    omega
  · have hbpar : b.val % 2 = 0 := by omega
    simp [oddOddCapRow, hpar, hbpar] at hx hy
    subst x
    subst y
    refine Or.inr ⟨rfl, Or.inl ?_⟩
    simp [rowFromRowsMinusTwo]
    omega

lemma isChain_oddOddCapRows {B : Board}
    (hcols : 2 ≤ B.cols) :
    List.IsChain adjacent (oddOddCapRows B) := by
  have hne :
      [] ∉ (List.finRange (B.rows - 2)).map (oddOddCapRow B) := by
    intro h
    simp only [List.mem_map, List.mem_finRange, true_and] at h
    rcases h with ⟨row, hnil⟩
    exact oddOddCapRow_ne_nil row hnil
  rw [oddOddCapRows, List.flatMap, List.isChain_flatten hne]
  constructor
  · intro l hl
    simp only [List.mem_map, List.mem_finRange, true_and] at hl
    rcases hl with ⟨row, rfl⟩
    exact isChain_oddOddCapRow hcols row
  · rw [List.isChain_map]
    exact (isChain_finRange_val_succ (B.rows - 2)).imp
      (by
        intro a b hnext
        exact adjacent_oddOddCapRow_next hnext)

lemma oddOddLeftColumn_ne_nil {B : Board}
    (hrows : 2 ≤ B.rows) :
    oddOddLeftColumn B ≠ [] := by
  simp [oddOddLeftColumn]
  omega

lemma oddOddLeftColumn_head {B : Board}
    (hrows : 2 ≤ B.rows) :
    (oddOddLeftColumn B).head? = some ((cornerUp B).1, colZero B) := by
  simp [oddOddLeftColumn, List.head?_reverse,
    finRange_getLast?_eq_last (by omega : 0 < B.rows - 1),
    cornerUp, bottomRight, rowFromRowsMinusOne, colZero]

lemma oddOddLeftColumn_getLast {B : Board}
    (hrows : 2 ≤ B.rows) :
    (oddOddLeftColumn B).getLast? = some (rowZero B, colZero B) := by
  simp [oddOddLeftColumn, List.getLast?_reverse,
    finRange_head?_eq_zero (by omega : 0 < B.rows - 1),
    rowZero, colZero, rowFromRowsMinusOne]

lemma oddOddMiddleSnake_ne_nil {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 4 ≤ B.cols) :
    oddOddMiddleSnake B ≠ [] := by
  rw [oddOddMiddleSnake, List.flatMap]
  apply List.flatten_ne_nil_iff.mpr
  let col0 : Fin (B.cols - 3) := ⟨0, by omega⟩
  refine ⟨oddOddMiddleColumn B col0, ?_, oddOddMiddleColumn_ne_nil hrows col0⟩
  exact List.mem_map_of_mem (f := oddOddMiddleColumn B) (List.mem_finRange col0)

lemma oddOddMiddleSnake_head {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 4 ≤ B.cols) :
    (oddOddMiddleSnake B).head? =
      some
        (rowFromRowsMinusOne (B := B) (⟨0, by omega⟩ : Fin (B.rows - 1)),
          oddOddMiddleCol (B := B) (⟨0, by omega⟩ : Fin (B.cols - 3))) := by
  let col0 : Fin (B.cols - 3) := ⟨0, by omega⟩
  have hcol0Mem : col0 ∈ (List.finRange (B.cols - 3)).head? := by
    rw [finRange_head?_eq_zero (by omega : 0 < B.cols - 3)]
    simp [col0]
  have hcolsCons :
      List.finRange (B.cols - 3) = col0 :: (List.finRange (B.cols - 3)).tail :=
    List.eq_cons_of_mem_head? hcol0Mem
  rw [oddOddMiddleSnake, hcolsCons]
  simp only [List.flatMap_cons]
  rw [List.head?_append_of_ne_nil
    (oddOddMiddleColumn B col0)
    (oddOddMiddleColumn_ne_nil hrows col0)]
  simp [oddOddMiddleColumn, col0, oddOddMiddleCol,
    finRange_head?_eq_zero (by omega : 0 < B.rows - 1)]

lemma oddOddCapRows_ne_nil {B : Board}
    (hrows : 3 ≤ B.rows) :
    oddOddCapRows B ≠ [] := by
  rw [oddOddCapRows, List.flatMap]
  apply List.flatten_ne_nil_iff.mpr
  let row0 : Fin (B.rows - 2) := ⟨0, by omega⟩
  refine ⟨oddOddCapRow B row0, ?_, oddOddCapRow_ne_nil row0⟩
  exact List.mem_map_of_mem (f := oddOddCapRow B) (List.mem_finRange row0)

lemma oddOddCap_head {B : Board}
    (hrows : 3 ≤ B.rows) :
    (oddOddCap B).head? = some (rowZero B, oddOddColBeforeRight B) := by
  rw [oddOddCap,
    List.head?_append_of_ne_nil (oddOddCapRows B) (oddOddCapRows_ne_nil hrows)]
  let row0 : Fin (B.rows - 2) := ⟨0, by omega⟩
  have hrow0Mem : row0 ∈ (List.finRange (B.rows - 2)).head? := by
    rw [finRange_head?_eq_zero (by omega : 0 < B.rows - 2)]
    simp [row0]
  have hrowsCons :
      List.finRange (B.rows - 2) = row0 :: (List.finRange (B.rows - 2)).tail :=
    List.eq_cons_of_mem_head? hrow0Mem
  rw [oddOddCapRows, hrowsCons]
  simp [oddOddCapRow, row0, rowZero, rowFromRowsMinusTwo]

lemma oddOddMiddleSnake_getLast?_eq_lastColumn {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 4 ≤ B.cols) :
    (oddOddMiddleSnake B).getLast? =
      (oddOddMiddleColumn B
        (⟨B.cols - 4, by omega⟩ : Fin (B.cols - 3))).getLast? := by
  let colLast : Fin (B.cols - 3) := ⟨B.cols - 4, by omega⟩
  let cols := (List.finRange (B.cols - 3)).map (oddOddMiddleColumn B)
  have hcols_ne : cols ≠ [] := by
    simp [cols, List.finRange_eq_nil_iff]
    omega
  have hcols_last? :
      cols.getLast? = some (oddOddMiddleColumn B colLast) := by
    dsimp [cols]
    rw [List.getLast?_map, finRange_getLast?_eq_last (by omega : 0 < B.cols - 3)]
    congr
  have hcols_last :
      cols.getLast hcols_ne = oddOddMiddleColumn B colLast := by
    exact List.getLast_of_mem_getLast? (by rw [hcols_last?]; simp)
  have hcols_last_ne : cols.getLast hcols_ne ≠ [] := by
    rw [hcols_last]
    exact oddOddMiddleColumn_ne_nil hrows colLast
  have hflat_ne : cols.flatten ≠ [] := by
    exact List.flatten_ne_nil_iff.mpr
      ⟨cols.getLast hcols_ne, List.getLast_mem hcols_ne, hcols_last_ne⟩
  have hinner_ne : oddOddMiddleColumn B colLast ≠ [] :=
    oddOddMiddleColumn_ne_nil hrows colLast
  rw [oddOddMiddleSnake, List.flatMap]
  change cols.flatten.getLast? = (oddOddMiddleColumn B colLast).getLast?
  rw [List.getLast?_eq_getLast_of_ne_nil hflat_ne,
    List.getLast?_eq_getLast_of_ne_nil hinner_ne]
  rw [List.getLast_flatten_eq_getLast_getLast (l := cols) hflat_ne hcols_last_ne]
  congr

lemma oddOddCapRows_getLast?_eq_lastRow {B : Board}
    (hrows : 3 ≤ B.rows) :
    (oddOddCapRows B).getLast? =
      (oddOddCapRow B (⟨B.rows - 3, by omega⟩ : Fin (B.rows - 2))).getLast? := by
  let rowLast : Fin (B.rows - 2) := ⟨B.rows - 3, by omega⟩
  let rows := (List.finRange (B.rows - 2)).map (oddOddCapRow B)
  have hrows_ne : rows ≠ [] := by
    simp [rows, List.finRange_eq_nil_iff]
    omega
  have hrows_last? :
      rows.getLast? = some (oddOddCapRow B rowLast) := by
    dsimp [rows]
    rw [List.getLast?_map, finRange_getLast?_eq_last (by omega : 0 < B.rows - 2)]
    congr
  have hrows_last :
      rows.getLast hrows_ne = oddOddCapRow B rowLast := by
    exact List.getLast_of_mem_getLast? (by rw [hrows_last?]; simp)
  have hrows_last_ne : rows.getLast hrows_ne ≠ [] := by
    rw [hrows_last]
    exact oddOddCapRow_ne_nil rowLast
  have hflat_ne : rows.flatten ≠ [] := by
    exact List.flatten_ne_nil_iff.mpr
      ⟨rows.getLast hrows_ne, List.getLast_mem hrows_ne, hrows_last_ne⟩
  have hinner_ne : oddOddCapRow B rowLast ≠ [] :=
    oddOddCapRow_ne_nil rowLast
  rw [oddOddCapRows, List.flatMap]
  change rows.flatten.getLast? = (oddOddCapRow B rowLast).getLast?
  rw [List.getLast?_eq_getLast_of_ne_nil hflat_ne,
    List.getLast?_eq_getLast_of_ne_nil hinner_ne]
  rw [List.getLast_flatten_eq_getLast_getLast (l := rows) hflat_ne hrows_last_ne]
  congr

lemma adjacent_oddOddCapRows_cornerUp {B : Board}
    (hrows : 3 ≤ B.rows) (hrowsOdd : B.rows % 2 = 1) :
    ∀ x ∈ (oddOddCapRows B).getLast?,
      ∀ y ∈ [cornerUp B].head?,
        adjacent x y := by
  intro x hx y hy
  let rowLast : Fin (B.rows - 2) := ⟨B.rows - 3, by omega⟩
  have hrowLastEven : rowLast.val % 2 = 0 := by
    simp [rowLast]
    omega
  rw [oddOddCapRows_getLast?_eq_lastRow hrows] at hx
  simp [oddOddCapRow, rowLast, hrowLastEven] at hx hy
  subst x
  subst y
  refine Or.inr ⟨rfl, Or.inl ?_⟩
  simp [cornerUp, bottomRight, rowFromRowsMinusTwo]
  omega

lemma isChain_oddOddCap {B : Board}
    (hrows : 3 ≤ B.rows) (hcols : 2 ≤ B.cols) (hrowsOdd : B.rows % 2 = 1) :
    List.IsChain adjacent (oddOddCap B) := by
  rw [oddOddCap]
  apply List.IsChain.append
  · exact isChain_oddOddCapRows hcols
  · simp
  · exact adjacent_oddOddCapRows_cornerUp hrows hrowsOdd

lemma adjacent_evenColsBottomTail_oddOddLeftColumn_head {B : Board}
    (hrows : 2 ≤ B.rows) :
    ∀ x ∈ (evenColsBottomTail B).getLast?,
      ∀ y ∈ (oddOddLeftColumn B).head?,
        adjacent x y := by
  intro x hx y hy
  simp [evenColsBottomTail] at hx
  rcases hx with ⟨c, hhead, rfl⟩
  have hmemBottom : c ∈ (List.finRange (B.cols - 1)).head? := by
    rw [hhead]
    simp
  have hcval := finRange_head_val_eq_zero hmemBottom
  rw [oddOddLeftColumn_head hrows] at hy
  simp at hy
  subst y
  refine Or.inr ⟨?_, Or.inr ?_⟩
  · apply Fin.ext
    simp [colFromColsMinusOne, colZero]
    omega
  · simp [cornerUp, bottomRight]
    omega

lemma adjacent_oddOddLeftColumn_after_head {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsOdd : B.rows % 2 = 1) (hcolsOdd : B.cols % 2 = 1) :
    ∀ x ∈ (oddOddLeftColumn B).getLast?,
      ∀ y ∈ (oddOddMiddleSnake B ++ oddOddCap B).head?,
        adjacent x y := by
  intro x hx y hy
  rw [oddOddLeftColumn_getLast hrows] at hx
  simp at hx
  subst x
  have hrows_three : 3 ≤ B.rows := by omega
  have hcols_three : 3 ≤ B.cols := by omega
  by_cases hmid : 4 ≤ B.cols
  · rw [List.head?_append_of_ne_nil
      (oddOddMiddleSnake B)
      (oddOddMiddleSnake_ne_nil hrows hmid)] at hy
    rw [oddOddMiddleSnake_head hrows hmid] at hy
    simp at hy
    subst y
    refine Or.inl ⟨?_, Or.inl ?_⟩
    · apply Fin.ext
      simp [rowZero, rowFromRowsMinusOne]
    · simp [colZero, oddOddMiddleCol]
  · have hcols_eq : B.cols = 3 := by omega
    have hmiddle_empty : oddOddMiddleSnake B = [] := by
      rw [oddOddMiddleSnake]
      have hsub : B.cols - 3 = 0 := by omega
      have hrange : List.finRange (B.cols - 3) = [] := by
        rw [hsub]
        rfl
      rw [hrange]
      rfl
    have hy' : y = (rowZero B, oddOddColBeforeRight B) := by
      have hy'' : (rowZero B, oddOddColBeforeRight B) = y := by
        simpa [hmiddle_empty, oddOddCap_head hrows_three] using hy
      exact hy''.symm
    subst y
    refine Or.inl ⟨rfl, Or.inl ?_⟩
    simp [colZero, oddOddColBeforeRight, hcols_eq]

lemma adjacent_oddOddMiddleSnake_cap_head {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsOdd : B.rows % 2 = 1) (hcolsOdd : B.cols % 2 = 1) :
    ∀ x ∈ (oddOddMiddleSnake B).getLast?,
      ∀ y ∈ (oddOddCap B).head?,
        adjacent x y := by
  intro x hx y hy
  have hrows_three : 3 ≤ B.rows := by omega
  have hcols_three : 3 ≤ B.cols := by omega
  by_cases hmid : 4 ≤ B.cols
  · let colLast : Fin (B.cols - 3) := ⟨B.cols - 4, by omega⟩
    have hlastEven : ¬ (colLast.val + 1) % 2 = 1 := by
      simp [colLast]
      omega
    rw [oddOddMiddleSnake_getLast?_eq_lastColumn hrows hmid] at hx
    simp [oddOddMiddleColumn, colLast, hlastEven] at hx
    rcases hx with ⟨rx, hxhead, rfl⟩
    have hrx := finRange_head_val_eq_zero hxhead
    rw [oddOddCap_head hrows_three] at hy
    simp at hy
    subst y
    refine Or.inl ⟨?_, Or.inl ?_⟩
    · apply Fin.ext
      simp [rowZero, rowFromRowsMinusOne]
      omega
    · simp [oddOddMiddleCol, oddOddColBeforeRight]
      omega
  · have hcols_eq : B.cols = 3 := by omega
    have hmiddle_empty : oddOddMiddleSnake B = [] := by
      rw [oddOddMiddleSnake]
      have hsub : B.cols - 3 = 0 := by omega
      have hrange : List.finRange (B.cols - 3) = [] := by
        rw [hsub]
        rfl
      rw [hrange]
      rfl
    rw [hmiddle_empty] at hx
    simp at hx

lemma oddOddRoute_chain_open {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsOdd : B.rows % 2 = 1) (hcolsOdd : B.cols % 2 = 1) :
    AdjacentChain (bottomRight B) (oddOddRouteXs B) := by
  have hrows_three : 3 ≤ B.rows := by omega
  rw [adjacentChain_iff_isChain]
  rw [oddOddRouteXs, List.append_assoc]
  apply List.IsChain.cons
  · apply List.IsChain.append
    · apply List.IsChain.append
      · exact isChain_evenColsBottomTail B
      · exact isChain_oddOddLeftColumn B
      · exact adjacent_evenColsBottomTail_oddOddLeftColumn_head hrows
    · apply List.IsChain.append
      · exact isChain_oddOddMiddleSnake hrows
      · exact isChain_oddOddCap hrows_three hcols hrowsOdd
      · exact adjacent_oddOddMiddleSnake_cap_head hrows hcols hrowsOdd hcolsOdd
    · intro x hx y hy
      rw [List.getLast?_append_of_ne_nil
        (evenColsBottomTail B)
        (oddOddLeftColumn_ne_nil hrows)] at hx
      exact adjacent_oddOddLeftColumn_after_head hrows hcols hrowsOdd hcolsOdd x hx y hy
  · intro y hy
    have hbottom_ne : evenColsBottomTail B ≠ [] := by
      simp [evenColsBottomTail]
      omega
    have hprefix_ne : evenColsBottomTail B ++ oddOddLeftColumn B ≠ [] := by
      simp [hbottom_ne]
    rw [
      List.head?_append_of_ne_nil
        (evenColsBottomTail B ++ oddOddLeftColumn B) hprefix_ne,
      List.head?_append_of_ne_nil (evenColsBottomTail B) hbottom_ne] at hy
    exact adjacent_bottomRight_evenColsBottomTail_head y hy

lemma oddOddRoute_length {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsOdd : B.rows % 2 = 1) (hcolsOdd : B.cols % 2 = 1) :
    (oddOddRouteXs B).length = B.tileCount - 1 := by
  have hrows_three : 3 ≤ B.rows := by
    omega
  have hcols_three : 3 ≤ B.cols := by
    omega
  have hlen : (oddOddRouteXs B).length + 2 = B.size := by
    simp [oddOddRouteXs, evenColsBottomTail, oddOddLeftColumn_length,
      oddOddMiddleSnake_length, oddOddCap_length, Board.size]
    let r := B.rows
    let c := B.cols
    let cm3 := c - 3
    let cm1 := c - 1
    let rm2 := r - 2
    let rm1 := r - 1
    have hcm3 : cm3 + 3 = c := by omega
    have hcm1 : cm1 + 1 = c := by omega
    have hrm2 : rm2 + 2 = r := by omega
    have hrm1 : rm1 + 1 = r := by omega
    change cm1 + (rm1 + (cm3 * rm1 + (2 * rm2 + 1))) + 2 = r * c
    nlinarith
  rw [Board.tileCount]
  have hsize := B.size_pos
  omega

lemma oddOddCap_ne_nil (B : Board) :
    oddOddCap B ≠ [] := by
  simp [oddOddCap]

lemma oddOddRoute_head {B : Board}
    (hcols : 2 ≤ B.cols) :
    (oddOddRouteXs B).head? = some (cornerLeft B) := by
  have hbottom_ne : evenColsBottomTail B ≠ [] := by
    simp [evenColsBottomTail]
    omega
  have hprefix_ne : evenColsBottomTail B ++ oddOddLeftColumn B ≠ [] := by
    simp [hbottom_ne]
  have hprefix2_ne :
      evenColsBottomTail B ++ oddOddLeftColumn B ++ oddOddMiddleSnake B ≠ [] := by
    simp [hbottom_ne]
  rw [oddOddRouteXs,
    List.head?_append_of_ne_nil
      (evenColsBottomTail B ++ oddOddLeftColumn B ++ oddOddMiddleSnake B) hprefix2_ne,
    List.head?_append_of_ne_nil
      (evenColsBottomTail B ++ oddOddLeftColumn B) hprefix_ne,
    List.head?_append_of_ne_nil (evenColsBottomTail B) hbottom_ne]
  simp [evenColsBottomTail, finRange_getLast?_eq_last (by omega : 0 < B.cols - 1),
    cornerLeft, bottomRight, colFromColsMinusOne]

lemma oddOddRoute_getLast {B : Board} :
    (oddOddRouteXs B).getLast? = some (cornerUp B) := by
  rw [oddOddRouteXs,
    List.getLast?_append_of_ne_nil
      (evenColsBottomTail B ++ oddOddLeftColumn B ++ oddOddMiddleSnake B)
      (oddOddCap_ne_nil B)]
  simp [oddOddCap]

lemma adjacent_oddOddRoute_bottomRight {B : Board}
    (hrows : 2 ≤ B.rows) :
    ∀ x ∈ (oddOddRouteXs B).getLast?,
      ∀ y ∈ [bottomRight B].head?,
        adjacent x y := by
  intro x hx y hy
  rw [oddOddRoute_getLast] at hx
  simp at hx hy
  subst x
  subst y
  refine Or.inr ⟨rfl, Or.inl ?_⟩
  simp [cornerUp, bottomRight]
  omega

lemma oddOddRoute_chain {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsOdd : B.rows % 2 = 1) (hcolsOdd : B.cols % 2 = 1) :
    AdjacentChain (bottomRight B) (oddOddRouteXs B ++ [bottomRight B]) := by
  rw [adjacentChain_iff_isChain]
  change List.IsChain adjacent ((bottomRight B :: oddOddRouteXs B) ++ [bottomRight B])
  apply List.IsChain.append
  · exact (adjacentChain_iff_isChain (bottomRight B) (oddOddRouteXs B)).mp
      (oddOddRoute_chain_open hrows hcols hrowsOdd hcolsOdd)
  · simp
  · intro x hx y hy
    simp at hy
    subst y
    have hroute_ne : oddOddRouteXs B ≠ [] := by
      simp [oddOddRouteXs, evenColsBottomTail]
      omega
    have hxRoute : x ∈ (oddOddRouteXs B).getLast? := by
      cases hroute : oddOddRouteXs B with
      | nil =>
          exact (hroute_ne hroute).elim
      | cons z zs =>
          rw [hroute] at hx
          simpa using hx
    exact adjacent_oddOddRoute_bottomRight hrows x hxRoute (bottomRight B) (by simp)

lemma oddOddLeftColumn_nonblank {B : Board} :
    ∀ c ∈ oddOddLeftColumn B, c ≠ bottomRight B := by
  intro c hc
  simp [oddOddLeftColumn] at hc
  rcases hc with ⟨row, _hrow, rfl⟩
  intro h
  have hv := congrArg (fun c : Cell B => c.1.val) h
  have hrowLt := row.isLt
  simp [bottomRight, rowFromRowsMinusOne] at hv
  omega

lemma oddOddMiddleColumn_nonblank {B : Board} (col : Fin (B.cols - 3)) :
    ∀ c ∈ oddOddMiddleColumn B col, c ≠ bottomRight B := by
  intro c hc
  rw [oddOddMiddleColumn] at hc
  by_cases hpar : (col.val + 1) % 2 = 1
  · simp [hpar] at hc
    rcases hc with ⟨row, _hrow, rfl⟩
    intro h
    have hv := congrArg (fun c : Cell B => c.1.val) h
    have hrowLt := row.isLt
    simp [bottomRight, rowFromRowsMinusOne] at hv
    omega
  · simp [hpar] at hc
    rcases hc with ⟨row, _hrow, rfl⟩
    intro h
    have hv := congrArg (fun c : Cell B => c.1.val) h
    have hrowLt := row.isLt
    simp [bottomRight, rowFromRowsMinusOne] at hv
    omega

lemma oddOddMiddleSnake_nonblank {B : Board} :
    ∀ c ∈ oddOddMiddleSnake B, c ≠ bottomRight B := by
  intro c hc
  rw [oddOddMiddleSnake] at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and] at hc
  rcases hc with ⟨col, hcol⟩
  exact oddOddMiddleColumn_nonblank col c hcol

lemma oddOddCapRow_nonblank {B : Board} (row : Fin (B.rows - 2)) :
    ∀ c ∈ oddOddCapRow B row, c ≠ bottomRight B := by
  intro c hc
  by_cases hpar : row.val % 2 = 0
  · simp [oddOddCapRow, hpar] at hc
    rcases hc with h | h <;> rw [h] <;>
      intro heq <;>
      have hv := congrArg (fun c : Cell B => c.1.val) heq <;>
      have hrowLt := row.isLt <;>
      simp [bottomRight, rowFromRowsMinusTwo] at hv <;>
      omega
  · simp [oddOddCapRow, hpar] at hc
    rcases hc with h | h <;> rw [h] <;>
      intro heq <;>
      have hv := congrArg (fun c : Cell B => c.1.val) heq <;>
      have hrowLt := row.isLt <;>
      simp [bottomRight, rowFromRowsMinusTwo] at hv <;>
      omega

lemma oddOddCapRows_nonblank {B : Board} :
    ∀ c ∈ oddOddCapRows B, c ≠ bottomRight B := by
  intro c hc
  rw [oddOddCapRows] at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and] at hc
  rcases hc with ⟨row, hrow⟩
  exact oddOddCapRow_nonblank row c hrow

lemma oddOddCap_nonblank {B : Board}
    (hrows : 2 ≤ B.rows) :
    ∀ c ∈ oddOddCap B, c ≠ bottomRight B := by
  intro c hc
  simp [oddOddCap] at hc
  rcases hc with hrowsPart | hcorner
  · exact oddOddCapRows_nonblank c hrowsPart
  · rw [hcorner]
    exact cornerUp_ne_bottomRight hrows

lemma oddOddRoute_nonblank {B : Board}
    (hrows : 2 ≤ B.rows) :
    ∀ c ∈ oddOddRouteXs B, c ≠ bottomRight B := by
  intro c hc
  simp [oddOddRouteXs] at hc
  rcases hc with hc | hc | hc | hc
  · exact evenColsBottomTail_nonblank c hc
  · exact oddOddLeftColumn_nonblank c hc
  · exact oddOddMiddleSnake_nonblank c hc
  · exact oddOddCap_nonblank hrows c hc

lemma oddOddLeftColumn_nodup (B : Board) :
    (oddOddLeftColumn B).Nodup := by
  rw [oddOddLeftColumn]
  exact (List.nodup_reverse.mpr (List.nodup_finRange (B.rows - 1))).map
    (by
      intro a b h
      apply Fin.ext
      have hv := congrArg (fun c : Cell B => c.1.val) h
      simpa [rowFromRowsMinusOne] using hv)

lemma oddOddLeftColumn_mem_col {B : Board} {c : Cell B}
    (hc : c ∈ oddOddLeftColumn B) :
    c.2 = colZero B := by
  simp [oddOddLeftColumn] at hc
  rcases hc with ⟨row, _hrow, rfl⟩
  rfl

lemma oddOddLeftColumn_not_bottom_row {B : Board} :
    ∀ c ∈ oddOddLeftColumn B, c.1 ≠ (bottomRight B).1 := by
  intro c hc h
  simp [oddOddLeftColumn] at hc
  rcases hc with ⟨row, _hrow, rfl⟩
  have hv := congrArg (fun r : Fin B.rows => r.val) h
  have hrowLt := row.isLt
  simp [bottomRight, rowFromRowsMinusOne] at hv
  omega

lemma oddOddMiddleColumn_nodup (B : Board) (col : Fin (B.cols - 3)) :
    (oddOddMiddleColumn B col).Nodup := by
  by_cases hpar : (col.val + 1) % 2 = 1
  · simpa [oddOddMiddleColumn, hpar] using
      (List.Nodup.map
        (l := List.finRange (B.rows - 1))
        (f := fun r =>
          (rowFromRowsMinusOne (B := B) r, oddOddMiddleCol (B := B) col))
        (by
          intro a b h
          apply Fin.ext
          have hv := congrArg (fun c : Cell B => c.1.val) h
          simpa [rowFromRowsMinusOne] using hv)
        (List.nodup_finRange (B.rows - 1)))
  · simpa [oddOddMiddleColumn, hpar] using
      (List.Nodup.map
        (l := (List.finRange (B.rows - 1)).reverse)
        (f := fun r =>
          (rowFromRowsMinusOne (B := B) r, oddOddMiddleCol (B := B) col))
        (by
          intro a b h
          apply Fin.ext
          have hv := congrArg (fun c : Cell B => c.1.val) h
          simpa [rowFromRowsMinusOne] using hv)
        (List.nodup_reverse.mpr (List.nodup_finRange (B.rows - 1))))

lemma oddOddMiddleColumn_mem_col {B : Board} {col : Fin (B.cols - 3)} {c : Cell B}
    (hc : c ∈ oddOddMiddleColumn B col) :
    c.2 = oddOddMiddleCol (B := B) col := by
  rw [oddOddMiddleColumn] at hc
  by_cases hpar : (col.val + 1) % 2 = 1
  · simp [hpar] at hc
    rcases hc with ⟨row, _hrow, rfl⟩
    rfl
  · simp [hpar] at hc
    rcases hc with ⟨row, _hrow, rfl⟩
    rfl

lemma oddOddMiddleColumn_not_bottom_row {B : Board} {col : Fin (B.cols - 3)} :
    ∀ c ∈ oddOddMiddleColumn B col, c.1 ≠ (bottomRight B).1 := by
  intro c hc h
  rw [oddOddMiddleColumn] at hc
  by_cases hpar : (col.val + 1) % 2 = 1
  · simp [hpar] at hc
    rcases hc with ⟨row, _hrow, rfl⟩
    have hv := congrArg (fun r : Fin B.rows => r.val) h
    have hrowLt := row.isLt
    simp [bottomRight, rowFromRowsMinusOne] at hv
    omega
  · simp [hpar] at hc
    rcases hc with ⟨row, _hrow, rfl⟩
    have hv := congrArg (fun r : Fin B.rows => r.val) h
    have hrowLt := row.isLt
    simp [bottomRight, rowFromRowsMinusOne] at hv
    omega

lemma oddOddMiddleColumn_col_lt_beforeRight {B : Board}
    {col : Fin (B.cols - 3)} {c : Cell B}
    (hc : c ∈ oddOddMiddleColumn B col) :
    c.2.val < B.cols - 2 := by
  have hcol := oddOddMiddleColumn_mem_col hc
  have hlt := col.isLt
  rw [hcol]
  simp [oddOddMiddleCol]
  omega

lemma oddOddMiddleColumn_not_colZero {B : Board}
    {col : Fin (B.cols - 3)} {c : Cell B}
    (hc : c ∈ oddOddMiddleColumn B col) :
    c.2 ≠ colZero B := by
  intro h
  have hcol := oddOddMiddleColumn_mem_col hc
  have hv := congrArg (fun c : Fin B.cols => c.val) (hcol.symm.trans h)
  simp [oddOddMiddleCol, colZero] at hv

lemma oddOddMiddleColumn_disjoint {B : Board} {a b : Fin (B.cols - 3)}
    (hne : a ≠ b) :
    List.Disjoint (oddOddMiddleColumn B a) (oddOddMiddleColumn B b) := by
  rw [List.disjoint_left]
  intro c hca hcb
  have ha := oddOddMiddleColumn_mem_col hca
  have hb := oddOddMiddleColumn_mem_col hcb
  apply hne
  apply Fin.ext
  have hv := congrArg (fun c : Fin B.cols => c.val) (ha.symm.trans hb)
  simpa [oddOddMiddleCol] using hv

lemma oddOddMiddleSnake_nodup (B : Board) :
    (oddOddMiddleSnake B).Nodup := by
  rw [oddOddMiddleSnake, List.nodup_flatMap]
  constructor
  · intro col _hcol
    exact oddOddMiddleColumn_nodup B col
  · exact (List.nodup_finRange (B.cols - 3)).imp
      (by
        intro a b hne
        exact oddOddMiddleColumn_disjoint hne)

lemma oddOddMiddleSnake_not_bottom_row {B : Board} :
    ∀ c ∈ oddOddMiddleSnake B, c.1 ≠ (bottomRight B).1 := by
  intro c hc
  rw [oddOddMiddleSnake] at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and] at hc
  rcases hc with ⟨col, hcol⟩
  exact oddOddMiddleColumn_not_bottom_row c hcol

lemma oddOddMiddleSnake_col_lt_beforeRight {B : Board} {c : Cell B}
    (hc : c ∈ oddOddMiddleSnake B) :
    c.2.val < B.cols - 2 := by
  rw [oddOddMiddleSnake] at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and] at hc
  rcases hc with ⟨col, hcol⟩
  exact oddOddMiddleColumn_col_lt_beforeRight hcol

lemma oddOddMiddleSnake_not_colZero {B : Board} {c : Cell B}
    (hc : c ∈ oddOddMiddleSnake B) :
    c.2 ≠ colZero B := by
  rw [oddOddMiddleSnake] at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and] at hc
  rcases hc with ⟨col, hcol⟩
  exact oddOddMiddleColumn_not_colZero hcol

lemma oddOddCapRow_nodup {B : Board}
    (hcols : 2 ≤ B.cols) (row : Fin (B.rows - 2)) :
    (oddOddCapRow B row).Nodup := by
  have hne :
      (rowFromRowsMinusTwo (B := B) row, oddOddColBeforeRight B) ≠
        (rowFromRowsMinusTwo (B := B) row, (bottomRight B).2) := by
    intro h
    have hv := congrArg (fun c : Cell B => c.2.val) h
    simp [oddOddColBeforeRight, bottomRight] at hv
    omega
  by_cases hpar : row.val % 2 = 0
  · simpa [oddOddCapRow, hpar] using hne
  · simpa [oddOddCapRow, hpar] using hne.symm

lemma oddOddCapRow_mem_row {B : Board} {row : Fin (B.rows - 2)} {c : Cell B}
    (hc : c ∈ oddOddCapRow B row) :
    c.1 = rowFromRowsMinusTwo (B := B) row := by
  by_cases hpar : row.val % 2 = 0
  · simp [oddOddCapRow, hpar] at hc
    rcases hc with h | h <;> rw [h]
  · simp [oddOddCapRow, hpar] at hc
    rcases hc with h | h <;> rw [h]

lemma oddOddCapRow_col_ge_beforeRight {B : Board} {row : Fin (B.rows - 2)}
    {c : Cell B} (hc : c ∈ oddOddCapRow B row) :
    B.cols - 2 ≤ c.2.val := by
  by_cases hpar : row.val % 2 = 0
  · simp [oddOddCapRow, hpar] at hc
    rcases hc with h | h
    · rw [h]
      simp [oddOddColBeforeRight]
    · rw [h]
      simp [bottomRight]
      omega
  · simp [oddOddCapRow, hpar] at hc
    rcases hc with h | h
    · rw [h]
      simp [bottomRight]
      omega
    · rw [h]
      simp [oddOddColBeforeRight]

lemma oddOddCapRow_not_bottom_row {B : Board} {row : Fin (B.rows - 2)} :
    ∀ c ∈ oddOddCapRow B row, c.1 ≠ (bottomRight B).1 := by
  intro c hc h
  have hrow := oddOddCapRow_mem_row hc
  have hv := congrArg (fun r : Fin B.rows => r.val) (hrow.symm.trans h)
  have hlt := row.isLt
  simp [bottomRight, rowFromRowsMinusTwo] at hv
  omega

lemma oddOddCapRow_disjoint {B : Board} {a b : Fin (B.rows - 2)}
    (hne : a ≠ b) :
    List.Disjoint (oddOddCapRow B a) (oddOddCapRow B b) := by
  rw [List.disjoint_left]
  intro c hca hcb
  have ha := oddOddCapRow_mem_row hca
  have hb := oddOddCapRow_mem_row hcb
  apply hne
  apply Fin.ext
  have hv := congrArg (fun r : Fin B.rows => r.val) (ha.symm.trans hb)
  simpa [rowFromRowsMinusTwo] using hv

lemma oddOddCapRows_nodup {B : Board}
    (hcols : 2 ≤ B.cols) :
    (oddOddCapRows B).Nodup := by
  rw [oddOddCapRows, List.nodup_flatMap]
  constructor
  · intro row _hrow
    exact oddOddCapRow_nodup hcols row
  · exact (List.nodup_finRange (B.rows - 2)).imp
      (by
        intro a b hne
        exact oddOddCapRow_disjoint hne)

lemma oddOddCapRows_not_bottom_row {B : Board} :
    ∀ c ∈ oddOddCapRows B, c.1 ≠ (bottomRight B).1 := by
  intro c hc
  rw [oddOddCapRows] at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and] at hc
  rcases hc with ⟨row, hrow⟩
  exact oddOddCapRow_not_bottom_row c hrow

lemma oddOddCapRows_col_ge_beforeRight {B : Board} {c : Cell B}
    (hc : c ∈ oddOddCapRows B) :
    B.cols - 2 ≤ c.2.val := by
  rw [oddOddCapRows] at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and] at hc
  rcases hc with ⟨row, hrow⟩
  exact oddOddCapRow_col_ge_beforeRight hrow

lemma oddOddCapRows_disjoint_cornerUp {B : Board}
    (hrows : 3 ≤ B.rows) :
    List.Disjoint (oddOddCapRows B) [cornerUp B] := by
  rw [List.disjoint_left]
  intro c hc hcorner
  simp at hcorner
  rw [hcorner] at hc
  rw [oddOddCapRows] at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and] at hc
  rcases hc with ⟨row, hrow⟩
  have hrowEq := oddOddCapRow_mem_row hrow
  have hv := congrArg (fun r : Fin B.rows => r.val) hrowEq
  have hlt := row.isLt
  simp [cornerUp, bottomRight, rowFromRowsMinusTwo] at hv
  omega

lemma oddOddCap_nodup {B : Board}
    (hrows : 3 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    (oddOddCap B).Nodup := by
  rw [oddOddCap, List.nodup_append]
  constructor
  · exact oddOddCapRows_nodup hcols
  · constructor
    · simp
    · intro a ha b hb hab
      have haCorner : a ∈ [cornerUp B] := by
        simpa [hab] using hb
      exact oddOddCapRows_disjoint_cornerUp hrows ha haCorner

lemma oddOddCap_not_bottom_row {B : Board}
    (hrows : 2 ≤ B.rows) :
    ∀ c ∈ oddOddCap B, c.1 ≠ (bottomRight B).1 := by
  intro c hc
  simp [oddOddCap] at hc
  rcases hc with hrowsPart | hcorner
  · exact oddOddCapRows_not_bottom_row c hrowsPart
  · rw [hcorner]
    intro h
    have hv := congrArg (fun r : Fin B.rows => r.val) h
    simp [cornerUp, bottomRight] at hv
    omega

lemma oddOddCap_col_ge_beforeRight {B : Board}
    (hcols : 2 ≤ B.cols) {c : Cell B}
    (hc : c ∈ oddOddCap B) :
    B.cols - 2 ≤ c.2.val := by
  simp [oddOddCap] at hc
  rcases hc with hrowsPart | hcorner
  · exact oddOddCapRows_col_ge_beforeRight hrowsPart
  · rw [hcorner]
    simp [cornerUp, bottomRight]
    omega

lemma evenColsBottomTail_disjoint_oddOddLeftColumn {B : Board} :
    List.Disjoint (evenColsBottomTail B) (oddOddLeftColumn B) := by
  rw [List.disjoint_left]
  intro c hbottom hleft
  simp [evenColsBottomTail] at hbottom
  rcases hbottom with ⟨col, rfl⟩
  exact oddOddLeftColumn_not_bottom_row
    ((bottomRight B).1, colFromColsMinusOne (B := B) col) hleft rfl

lemma evenColsBottomTail_disjoint_oddOddMiddleSnake {B : Board} :
    List.Disjoint (evenColsBottomTail B) (oddOddMiddleSnake B) := by
  rw [List.disjoint_left]
  intro c hbottom hmiddle
  simp [evenColsBottomTail] at hbottom
  rcases hbottom with ⟨col, rfl⟩
  exact oddOddMiddleSnake_not_bottom_row
    ((bottomRight B).1, colFromColsMinusOne (B := B) col) hmiddle rfl

lemma evenColsBottomTail_disjoint_oddOddCap {B : Board}
    (hrows : 2 ≤ B.rows) :
    List.Disjoint (evenColsBottomTail B) (oddOddCap B) := by
  rw [List.disjoint_left]
  intro c hbottom hcap
  simp [evenColsBottomTail] at hbottom
  rcases hbottom with ⟨col, rfl⟩
  exact oddOddCap_not_bottom_row hrows
    ((bottomRight B).1, colFromColsMinusOne (B := B) col) hcap rfl

lemma oddOddLeftColumn_disjoint_middleSnake {B : Board} :
    List.Disjoint (oddOddLeftColumn B) (oddOddMiddleSnake B) := by
  rw [List.disjoint_left]
  intro c hleft hmiddle
  exact oddOddMiddleSnake_not_colZero hmiddle (oddOddLeftColumn_mem_col hleft)

lemma oddOddLeftColumn_disjoint_cap {B : Board}
    (hcols : 3 ≤ B.cols) :
    List.Disjoint (oddOddLeftColumn B) (oddOddCap B) := by
  rw [List.disjoint_left]
  intro c hleft hcap
  have hleftCol := oddOddLeftColumn_mem_col hleft
  have hge := oddOddCap_col_ge_beforeRight (by omega : 2 ≤ B.cols) hcap
  have hv := congrArg (fun c : Fin B.cols => c.val) hleftCol
  simp [colZero] at hv
  omega

lemma oddOddMiddleSnake_disjoint_cap {B : Board}
    (hcols : 2 ≤ B.cols) :
    List.Disjoint (oddOddMiddleSnake B) (oddOddCap B) := by
  rw [List.disjoint_left]
  intro c hmiddle hcap
  have hlt := oddOddMiddleSnake_col_lt_beforeRight hmiddle
  have hge := oddOddCap_col_ge_beforeRight hcols hcap
  omega

lemma oddOddRoute_nodup_cells {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsOdd : B.rows % 2 = 1) (hcolsOdd : B.cols % 2 = 1) :
    (oddOddRouteXs B).Nodup := by
  have hrows_three : 3 ≤ B.rows := by omega
  have hcols_three : 3 ≤ B.cols := by omega
  rw [oddOddRouteXs, List.nodup_append]
  constructor
  · rw [List.nodup_append]
    constructor
    · rw [List.nodup_append]
      constructor
      · exact evenColsBottomTail_nodup_cells
      · constructor
        · exact oddOddLeftColumn_nodup B
        · intro a ha b hb hab
          have hb' : a ∈ oddOddLeftColumn B := by
            simpa [hab] using hb
          exact evenColsBottomTail_disjoint_oddOddLeftColumn ha hb'
    · constructor
      · exact oddOddMiddleSnake_nodup B
      · intro a ha b hb hab
        have hb' : a ∈ oddOddMiddleSnake B := by
          simpa [hab] using hb
        have ha' : a ∈ evenColsBottomTail B ∨ a ∈ oddOddLeftColumn B := by
          simpa using ha
        rcases ha' with hbottom | hleft
        · exact evenColsBottomTail_disjoint_oddOddMiddleSnake hbottom hb'
        · exact oddOddLeftColumn_disjoint_middleSnake hleft hb'
  · constructor
    · exact oddOddCap_nodup hrows_three hcols
    · intro a ha b hb hab
      have hb' : a ∈ oddOddCap B := by
        simpa [hab] using hb
      have ha' :
          a ∈ evenColsBottomTail B ∨
            a ∈ oddOddLeftColumn B ∨
              a ∈ oddOddMiddleSnake B := by
        simpa using ha
      rcases ha' with hbottom | hleftOrMiddle
      · exact evenColsBottomTail_disjoint_oddOddCap hrows hbottom hb'
      · rcases hleftOrMiddle with hleft | hmiddle
        · exact oddOddLeftColumn_disjoint_cap hcols_three hleft hb'
        · exact oddOddMiddleSnake_disjoint_cap hcols hmiddle hb'

lemma oddOddRoute_nodup {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsOdd : B.rows % 2 = 1) (hcolsOdd : B.cols % 2 = 1) :
    ((nonblankSubtypeList
        (oddOddRouteXs B)
        (oddOddRoute_nonblank hrows)).map
      (nonblankCellEquivFin B)).Nodup := by
  have hsub :
      (nonblankSubtypeList
        (oddOddRouteXs B)
        (oddOddRoute_nonblank hrows)).Nodup := by
    apply List.Nodup.of_map (f := fun c : {c : Cell B // c ≠ bottomRight B} => c.1)
    simpa [nonblankSubtypeList_map_val] using
      oddOddRoute_nodup_cells hrows hcols hrowsOdd hcolsOdd
  exact hsub.map (nonblankCellEquivFin B).injective

lemma oddOddRoute_avoids_cornerUpLeft {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsOdd : B.rows % 2 = 1) (hcolsOdd : B.cols % 2 = 1) :
    cornerUpLeft B ∉ oddOddRouteXs B := by
  intro hmem
  have hrows_three : 3 ≤ B.rows := by omega
  have hcols_three : 3 ≤ B.cols := by omega
  simp [oddOddRouteXs] at hmem
  rcases hmem with hbottom | hleft | hmiddle | hcap
  · simp [evenColsBottomTail] at hbottom
    rcases hbottom with ⟨col, hEq⟩
    have hv := congrArg (fun c : Cell B => c.1.val) hEq
    simp [cornerUpLeft, bottomRight] at hv
    omega
  · have hcol := oddOddLeftColumn_mem_col hleft
    have hv := congrArg (fun c : Fin B.cols => c.val) hcol
    simp [cornerUpLeft, bottomRight, colZero] at hv
    omega
  · have hlt := oddOddMiddleSnake_col_lt_beforeRight hmiddle
    simp [cornerUpLeft, bottomRight] at hlt
    omega
  · simp [oddOddCap] at hcap
    rcases hcap with hrowsPart | hcorner
    · rw [oddOddCapRows] at hrowsPart
      simp only [List.mem_flatMap, List.mem_finRange, true_and] at hrowsPart
      rcases hrowsPart with ⟨row, hrow⟩
      have hrowEq := oddOddCapRow_mem_row hrow
      have hv := congrArg (fun r : Fin B.rows => r.val) hrowEq
      have hlt := row.isLt
      simp [cornerUpLeft, bottomRight, rowFromRowsMinusTwo] at hv
      omega
    · exact cornerUpLeft_ne_cornerUp hcols hcorner

lemma cornerUpLeftIdx_eq_nonblankCellEquivFin {B : Board}
    (hrows : 2 ≤ B.rows) :
    nonblankCellEquivFin B
        ⟨cornerUpLeft B, cornerUpLeft_ne_bottomRight hrows⟩ =
      cornerUpLeftIdx B hrows := by
  apply Fin.ext
  rfl

lemma oddOddRoute_index_avoids_cornerUpLeft {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsOdd : B.rows % 2 = 1) (hcolsOdd : B.cols % 2 = 1) :
    cornerUpLeftIdx B hrows ∉
      ((nonblankSubtypeList
        (oddOddRouteXs B)
        (oddOddRoute_nonblank hrows)).map
      (nonblankCellEquivFin B)) := by
  intro hmem
  rcases List.mem_map.mp hmem with ⟨c, hc, hEq⟩
  let missing : {c : Cell B // c ≠ bottomRight B} :=
    ⟨cornerUpLeft B, cornerUpLeft_ne_bottomRight hrows⟩
  have hmissing :
      nonblankCellEquivFin B missing = cornerUpLeftIdx B hrows := by
    exact cornerUpLeftIdx_eq_nonblankCellEquivFin hrows
  have hcMissing : c = missing :=
    (nonblankCellEquivFin B).injective (hEq.trans hmissing.symm)
  have hcCell : c.1 ∈ oddOddRouteXs B := by
    have hmap :
        c.1 ∈
          (nonblankSubtypeList
            (oddOddRouteXs B)
            (oddOddRoute_nonblank hrows)).map (fun c => c.1) :=
      List.mem_map_of_mem
        (f := fun c : {c : Cell B // c ≠ bottomRight B} => c.1) hc
    simpa [nonblankSubtypeList_map_val] using hmap
  have hcellEq : c.1 = cornerUpLeft B := by
    exact congrArg Subtype.val hcMissing
  exact oddOddRoute_avoids_cornerUpLeft hrows hcols hrowsOdd hcolsOdd
    (by simpa [hcellEq] using hcCell)

lemma oddOddRoute_covers {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsOdd : B.rows % 2 = 1) (hcolsOdd : B.cols % 2 = 1) :
    ((nonblankSubtypeList
        (oddOddRouteXs B)
        (oddOddRoute_nonblank hrows)).map
      (nonblankCellEquivFin B)).toFinset =
        Finset.univ.erase (cornerUpLeftIdx B hrows) := by
  let L :=
    (nonblankSubtypeList
      (oddOddRouteXs B)
      (oddOddRoute_nonblank hrows)).map
      (nonblankCellEquivFin B)
  have hnd : L.Nodup := by
    simpa [L] using oddOddRoute_nodup hrows hcols hrowsOdd hcolsOdd
  have hlen : L.length = B.tileCount - 1 := by
    simpa [L, nonblankSubtypeList] using
      oddOddRoute_length hrows hcols hrowsOdd hcolsOdd
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_erase]
    constructor
    · intro hxMissing
      have hxmem : x ∈ L := by
        simpa [L] using hx
      subst hxMissing
      exact oddOddRoute_index_avoids_cornerUpLeft
        hrows hcols hrowsOdd hcolsOdd hxmem
    · exact Finset.mem_univ x
  · rw [List.toFinset_card_of_nodup hnd, hlen,
      Finset.card_erase_of_mem (Finset.mem_univ (cornerUpLeftIdx B hrows)),
      Finset.card_univ, Fintype.card_fin]

lemma oddOddRoute_index_head {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    (((nonblankSubtypeList
      (oddOddRouteXs B)
      (oddOddRoute_nonblank hrows)).map
      (nonblankCellEquivFin B)).head?) =
        some (cornerLeftIdx B hcols) := by
  simp [nonblankSubtypeList, oddOddRoute_head hcols, cornerLeftIdx]
  apply Fin.ext
  rfl

lemma oddOddRoute_index_getLast {B : Board}
    (hrows : 2 ≤ B.rows) :
    (((nonblankSubtypeList
      (oddOddRouteXs B)
      (oddOddRoute_nonblank hrows)).map
      (nonblankCellEquivFin B)).getLast?) =
        some (cornerUpIdx B hrows) := by
  simp [nonblankSubtypeList, oddOddRoute_getLast, cornerUpIdx]
  apply Fin.ext
  rfl

lemma oddOddRoute_compat {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols) :
    List.formPerm
        ((nonblankSubtypeList
          (oddOddRouteXs B)
          (oddOddRoute_nonblank hrows)).map
          (nonblankCellEquivFin B))
        (cornerUpIdx B hrows) =
      cornerLeftIdx B hcols := by
  let L :=
    (nonblankSubtypeList
      (oddOddRouteXs B)
      (oddOddRoute_nonblank hrows)).map
      (nonblankCellEquivFin B)
  change List.formPerm L (cornerUpIdx B hrows) = cornerLeftIdx B hcols
  have hhead : L.head? = some (cornerLeftIdx B hcols) := by
    simpa [L] using oddOddRoute_index_head hrows hcols
  have hlast : L.getLast? = some (cornerUpIdx B hrows) := by
    simpa [L] using oddOddRoute_index_getLast hrows
  have hmemHead : cornerLeftIdx B hcols ∈ L.head? := by
    rw [hhead]
    simp
  have hLcons : L = cornerLeftIdx B hcols :: L.tail :=
    List.eq_cons_of_mem_head? hmemHead
  have hmemLast :
      cornerUpIdx B hrows ∈ (cornerLeftIdx B hcols :: L.tail).getLast? := by
    rw [← hLcons, hlast]
    simp
  have hgetLast :
      (cornerLeftIdx B hcols :: L.tail).getLast (List.cons_ne_nil _ _) =
        cornerUpIdx B hrows :=
    List.getLast_of_mem_getLast? hmemLast
  rw [hLcons]
  rw [← hgetLast]
  simp

lemma reachable_goal_to_cfg_bottomRight_of_oddOdd {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsOdd : B.rows % 2 = 1) (hcolsOdd : B.cols % 2 = 1)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable (goal B) cfg :=
  reachable_goal_to_cfg_bottomRight_of_closedAlmostFullList hrows hcols
    (oddOddRoute_chain hrows hcols hrowsOdd hcolsOdd)
    (oddOddRoute_nonblank hrows)
    (formPerm_isCycle_of_nodup_toFinset_erase hrows hcols
      (oddOddRoute_nodup hrows hcols hrowsOdd hcolsOdd)
      (oddOddRoute_covers hrows hcols hrowsOdd hcolsOdd))
    (support_formPerm_of_nodup_toFinset_erase hrows hcols
      (oddOddRoute_nodup hrows hcols hrowsOdd hcolsOdd)
      (oddOddRoute_covers hrows hcols hrowsOdd hcolsOdd))
    (oddOddRoute_compat hrows hcols)
    cfg hbr hpar

lemma tiles_to_goal_bottomRight_of_oddOdd {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : 2 ≤ B.cols)
    (hrowsOdd : B.rows % 2 = 1) (hcolsOdd : B.cols % 2 = 1)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable cfg (goal B) :=
  reachable_symm
    (reachable_goal_to_cfg_bottomRight_of_oddOdd
      hrows hcols hrowsOdd hcolsOdd cfg hbr hpar)

end NPuzzle.Rect
