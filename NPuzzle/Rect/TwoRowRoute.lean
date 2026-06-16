import NPuzzle.Rect.TwoColumnRoute

namespace NPuzzle.Rect

/-!
Explicit full-route candidate for two-row boards.

The route starts at `bottomRight`, walks left along the bottom row, crosses to
the top-left corner, then walks right along the top row back to the cell above
`bottomRight`.
-/

def rowZero (B : Board) : Fin B.rows :=
  ⟨0, B.rows_pos⟩

def rowOneOfTwo {B : Board} (hrows : B.rows = 2) : Fin B.rows :=
  ⟨1, by omega⟩

@[simp]
lemma rowZero_val {B : Board} :
    (rowZero B).val = 0 :=
  rfl

@[simp]
lemma rowOneOfTwo_val {B : Board} (hrows : B.rows = 2) :
    (rowOneOfTwo hrows).val = 1 :=
  rfl

def colFromColsMinusOne {B : Board} (c : Fin (B.cols - 1)) : Fin B.cols :=
  ⟨c.val, by
    have hc := c.isLt
    omega⟩

@[simp]
lemma colFromColsMinusOne_val {B : Board} (c : Fin (B.cols - 1)) :
    (colFromColsMinusOne (B := B) c).val = c.val :=
  rfl

def twoRowBottomTail (B : Board) (hrows : B.rows = 2) : List (Cell B) :=
  (List.finRange (B.cols - 1)).reverse.map fun c =>
    (rowOneOfTwo hrows, colFromColsMinusOne (B := B) c)

def twoRowTopRow (B : Board) : List (Cell B) :=
  (List.finRange B.cols).map fun c =>
    (rowZero B, c)

def twoRowRouteXs (B : Board) (hrows : B.rows = 2) : List (Cell B) :=
  twoRowBottomTail B hrows ++ twoRowTopRow B

lemma isChain_twoRow_bottomTail {B : Board} (hrows : B.rows = 2) :
    List.IsChain adjacent (twoRowBottomTail B hrows) := by
  rw [twoRowBottomTail, List.isChain_map]
  exact (isChain_finRange_reverse_val_pred (B.cols - 1)).imp
    (by
      intro a b h
      refine Or.inl ⟨rfl, Or.inr ?_⟩
      simpa [colFromColsMinusOne] using h)

lemma isChain_twoRow_topRow (B : Board) :
    List.IsChain adjacent (twoRowTopRow B) := by
  rw [twoRowTopRow, List.isChain_map]
  exact (isChain_finRange_val_succ B.cols).imp
    (by
      intro a b h
      refine Or.inl ⟨rfl, Or.inl ?_⟩
      simpa using h)

lemma adjacent_bottomRight_twoRowBottomTail_head {B : Board}
    (hrows : B.rows = 2) :
    ∀ y ∈ (twoRowBottomTail B hrows).head?, adjacent (bottomRight B) y := by
  intro y hy
  simp [twoRowBottomTail] at hy
  rcases hy with ⟨c, hlast, rfl⟩
  have hmem : c ∈ (List.finRange (B.cols - 1)).getLast? := by
    rw [hlast]
    simp
  have hval := finRange_getLast_val_add_one hmem
  refine Or.inl ⟨?_, Or.inr ?_⟩
  · apply Fin.ext
    simp [bottomRight, rowOneOfTwo, hrows]
  · simp [bottomRight, colFromColsMinusOne]
    omega

lemma adjacent_twoRowBottomTail_topRow_head {B : Board}
    (hrows : B.rows = 2) :
    ∀ x ∈ (twoRowBottomTail B hrows).getLast?,
      ∀ y ∈ (twoRowTopRow B).head?,
        adjacent x y := by
  intro x hx y hy
  simp [twoRowBottomTail, twoRowTopRow] at hx hy
  rcases hx with ⟨c, hhead, rfl⟩
  rcases hy with ⟨d, dhead, rfl⟩
  have hmemBottom : c ∈ (List.finRange (B.cols - 1)).head? := by
    rw [hhead]
    simp
  have hmemTop : d ∈ (List.finRange B.cols).head? := by
    rw [dhead]
    simp
  have hcval := finRange_head_val_eq_zero hmemBottom
  have hdval := finRange_head_val_eq_zero hmemTop
  refine Or.inr ⟨?_, Or.inr ?_⟩
  · apply Fin.ext
    simp [colFromColsMinusOne]
    omega
  · simp [rowOneOfTwo, rowZero]

lemma adjacent_twoRowTopRow_bottomRight {B : Board}
    (hrows : B.rows = 2) :
    ∀ x ∈ (twoRowTopRow B).getLast?,
      ∀ y ∈ [bottomRight B].head?,
        adjacent x y := by
  intro x hx y hy
  simp [twoRowTopRow] at hx hy
  rcases hx with ⟨c, hlast, rfl⟩
  subst y
  have hmem : c ∈ (List.finRange B.cols).getLast? := by
    rw [hlast]
    simp
  have hval := finRange_getLast_val_add_one hmem
  refine Or.inr ⟨?_, Or.inl ?_⟩
  · apply Fin.ext
    simp [bottomRight]
    omega
  · simp [bottomRight, rowZero, hrows]

lemma twoRowRoute_chain {B : Board}
    (hrows : B.rows = 2) (hcols : 2 ≤ B.cols) :
    AdjacentChain (bottomRight B) (twoRowRouteXs B hrows ++ [bottomRight B]) := by
  rw [adjacentChain_iff_isChain]
  rw [twoRowRouteXs, List.append_assoc]
  apply List.IsChain.cons
  · apply List.IsChain.append
    · exact isChain_twoRow_bottomTail hrows
    · apply List.IsChain.append
      · exact isChain_twoRow_topRow B
      · simp
      · exact adjacent_twoRowTopRow_bottomRight hrows
    · intro x hx y hy
      have htop_ne : twoRowTopRow B ≠ [] := by
        simp [twoRowTopRow]
        exact B.cols_pos.ne'
      rw [List.head?_append_of_ne_nil (twoRowTopRow B) htop_ne] at hy
      exact adjacent_twoRowBottomTail_topRow_head hrows x hx y hy
  · intro y hy
    have hbottom_ne : twoRowBottomTail B hrows ≠ [] := by
      simp [twoRowBottomTail]
      omega
    rw [List.head?_append_of_ne_nil (twoRowBottomTail B hrows) hbottom_ne] at hy
    exact adjacent_bottomRight_twoRowBottomTail_head hrows y hy

lemma twoRowRoute_nonblank {B : Board}
    (hrows : B.rows = 2) :
    ∀ c ∈ twoRowRouteXs B hrows, c ≠ bottomRight B := by
  intro c hc
  simp [twoRowRouteXs, twoRowBottomTail, twoRowTopRow] at hc
  rcases hc with hc | hc
  · rcases hc with ⟨x, rfl⟩
    intro h
    have hv := congrArg (fun c : Cell B => c.2.val) h
    have hx := x.isLt
    simp [bottomRight, colFromColsMinusOne] at hv
    omega
  · rcases hc with ⟨x, rfl⟩
    intro h
    have hv := congrArg (fun c : Cell B => c.1.val) h
    simp [bottomRight, rowZero, hrows] at hv

lemma twoRowRoute_length {B : Board}
    (hrows : B.rows = 2) :
    (twoRowRouteXs B hrows).length = B.tileCount := by
  simp [twoRowRouteXs, twoRowBottomTail, twoRowTopRow,
    Board.tileCount, Board.size, hrows]
  omega

lemma twoRowRoute_nodup_cells {B : Board}
    (hrows : B.rows = 2) :
    (twoRowRouteXs B hrows).Nodup := by
  simp [twoRowRouteXs, twoRowBottomTail, twoRowTopRow, List.nodup_append]
  constructor
  · exact (List.nodup_finRange (B.cols - 1)).map
      (by
        intro a b h
        apply Fin.ext
        have hv := congrArg (fun c : Cell B => c.2.val) h
        simpa [colFromColsMinusOne] using hv)
  · constructor
    · exact (List.nodup_finRange B.cols).map
        (by
          intro a b h
          exact congrArg Prod.snd h)
    · intro _a hrow
      have hv := congrArg (fun r : Fin B.rows => r.val) hrow
      simp [rowOneOfTwo, rowZero] at hv

lemma twoRowRoute_nodup {B : Board}
    (hrows : B.rows = 2) :
    ((nonblankSubtypeList
        (twoRowRouteXs B hrows)
        (twoRowRoute_nonblank hrows)).map
      (nonblankCellEquivFin B)).Nodup := by
  have hsub :
      (nonblankSubtypeList
        (twoRowRouteXs B hrows)
        (twoRowRoute_nonblank hrows)).Nodup := by
    apply List.Nodup.of_map (f := fun c : {c : Cell B // c ≠ bottomRight B} => c.1)
    simpa [nonblankSubtypeList_map_val] using twoRowRoute_nodup_cells hrows
  exact hsub.map (nonblankCellEquivFin B).injective

lemma twoRowRoute_covers {B : Board}
    (hrows : B.rows = 2) :
    ((nonblankSubtypeList
        (twoRowRouteXs B hrows)
        (twoRowRoute_nonblank hrows)).map
      (nonblankCellEquivFin B)).toFinset = Finset.univ := by
  apply finList_toFinset_eq_univ_of_nodup_length
  · exact twoRowRoute_nodup hrows
  · simpa [nonblankSubtypeList] using twoRowRoute_length hrows

end NPuzzle.Rect
