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

def oddOddMiddleCol {B : Board} (c : Fin (B.cols - 3)) : Fin B.cols :=
  ⟨c.val + 1, by
    have hc := c.isLt
    omega⟩

@[simp]
lemma oddOddColBeforeRight_val {B : Board} :
    (oddOddColBeforeRight B).val = B.cols - 2 :=
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

end NPuzzle.Rect
