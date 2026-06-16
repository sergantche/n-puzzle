import NPuzzle.Rect.PathParity

namespace NPuzzle.Rect

/-!
Explicit full-route candidate for two-column boards.

The route goes up the left column, crosses along the top edge, then returns down
the right column to the cell above `bottomRight`.
-/

def colZero (B : Board) : Fin B.cols :=
  ⟨0, B.cols_pos⟩

def colOneOfTwo {B : Board} (hcols : B.cols = 2) : Fin B.cols :=
  ⟨1, by omega⟩

@[simp]
lemma colZero_val {B : Board} :
    (colZero B).val = 0 :=
  rfl

@[simp]
lemma colOneOfTwo_val {B : Board} (hcols : B.cols = 2) :
    (colOneOfTwo hcols).val = 1 :=
  rfl

def rowFromRowsMinusTwo {B : Board} (r : Fin (B.rows - 2)) : Fin B.rows :=
  ⟨r.val, by
    have hr := r.isLt
    omega⟩

@[simp]
lemma rowFromRowsMinusTwo_val {B : Board} (r : Fin (B.rows - 2)) :
    (rowFromRowsMinusTwo (B := B) r).val = r.val :=
  rfl

def rowFromRowsMinusOne {B : Board} (r : Fin (B.rows - 1)) : Fin B.rows :=
  ⟨r.val, by
    have hr := r.isLt
    omega⟩

@[simp]
lemma rowFromRowsMinusOne_val {B : Board} (r : Fin (B.rows - 1)) :
    (rowFromRowsMinusOne (B := B) r).val = r.val :=
  rfl

lemma finList_toFinset_eq_univ_of_nodup_length {n : ℕ} {L : List (Fin n)}
    (hnd : L.Nodup) (hlen : L.length = n) :
    L.toFinset = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le
  · intro x _hx
    simp
  · rw [List.toFinset_card_of_nodup hnd, hlen]
    simp

lemma isChain_finRange_val_succ (n : ℕ) :
    List.IsChain (fun a b : Fin n => a.val + 1 = b.val) (List.finRange n) := by
  rw [List.isChain_iff_getElem]
  intro i
  simp

lemma isChain_finRange_reverse_val_pred (n : ℕ) :
    List.IsChain (fun a b : Fin n => b.val + 1 = a.val) (List.finRange n).reverse := by
  rw [List.isChain_reverse]
  exact isChain_finRange_val_succ n

lemma isChain_twoColumn_leftTail (B : Board) :
    List.IsChain adjacent
      ((List.finRange (B.rows - 2)).reverse.map fun r =>
        (rowFromRowsMinusTwo (B := B) r, colZero B)) := by
  rw [List.isChain_map]
  exact (isChain_finRange_reverse_val_pred (B.rows - 2)).imp
    (by
      intro a b h
      refine Or.inr ⟨rfl, Or.inr ?_⟩
      simpa [rowFromRowsMinusTwo] using h)

lemma isChain_twoColumn_rightColumn {B : Board} (hcols : B.cols = 2) :
    List.IsChain adjacent
      ((List.finRange (B.rows - 1)).map fun r =>
        (rowFromRowsMinusOne (B := B) r, colOneOfTwo hcols)) := by
  rw [List.isChain_map]
  exact (isChain_finRange_val_succ (B.rows - 1)).imp
    (by
      intro a b h
      refine Or.inr ⟨rfl, Or.inl ?_⟩
      simpa [rowFromRowsMinusOne] using h)

lemma bottomRight_eq_twoColumn {B : Board} (hcols : B.cols = 2) :
    bottomRight B = ((bottomRight B).1, colOneOfTwo hcols) := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    simp [bottomRight, colOneOfTwo, hcols]

lemma cornerLeft_eq_twoColumn {B : Board} (hcols : B.cols = 2) :
    cornerLeft B = ((bottomRight B).1, colZero B) := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    simp [cornerLeft, bottomRight, colZero, hcols]

lemma cornerUpLeft_eq_twoColumn {B : Board} (hcols : B.cols = 2) :
    cornerUpLeft B = ((cornerUp B).1, colZero B) := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    simp [cornerUpLeft, bottomRight, colZero, hcols]

lemma cornerUp_eq_twoColumn {B : Board} (hcols : B.cols = 2) :
    cornerUp B = ((cornerUp B).1, colOneOfTwo hcols) := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    simp [cornerUp, bottomRight, colOneOfTwo, hcols]

def twoColumnRouteYs (B : Board) (hcols : B.cols = 2) : List (Cell B) :=
  ((List.finRange (B.rows - 2)).reverse.map fun r =>
      (rowFromRowsMinusTwo (B := B) r, colZero B)) ++
    ((List.finRange (B.rows - 1)).map fun r =>
      (rowFromRowsMinusOne (B := B) r, colOneOfTwo hcols))

lemma twoColumnRoute_nonblank {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : B.cols = 2) :
    ∀ c ∈ cornerLeft B :: cornerUpLeft B :: twoColumnRouteYs B hcols,
      c ≠ bottomRight B := by
  intro c hc
  have hcolsLe : 2 ≤ B.cols := by omega
  simp [twoColumnRouteYs] at hc
  rcases hc with hleft | hupleft | htail
  · rw [hleft]
    exact cornerLeft_ne_bottomRight hcolsLe
  · rw [hupleft]
    exact cornerUpLeft_ne_bottomRight hrows
  · rcases htail with htail | htail
    · rcases htail with ⟨r, rfl⟩
      intro h
      have hv := congrArg (fun c : Cell B => c.2.val) h
      simp [bottomRight, colZero, hcols] at hv
    · rcases htail with ⟨r, rfl⟩
      intro h
      have hv := congrArg (fun c : Cell B => c.1.val) h
      have hr := r.isLt
      simp [bottomRight, rowFromRowsMinusOne] at hv
      omega

lemma twoColumnRoute_length {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : B.cols = 2) :
    (cornerLeft B :: cornerUpLeft B :: twoColumnRouteYs B hcols).length =
      B.tileCount := by
  simp [twoColumnRouteYs, Board.tileCount, Board.size, hcols]
  omega

lemma twoColumnRoute_nodup_cells {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : B.cols = 2) :
    (cornerLeft B :: cornerUpLeft B :: twoColumnRouteYs B hcols).Nodup := by
  rw [cornerLeft_eq_twoColumn hcols, cornerUpLeft_eq_twoColumn hcols]
  simp [twoColumnRouteYs, List.nodup_append]
  constructor
  · constructor
    · intro h
      have hv := congrArg (fun r : Fin B.rows => r.val) h
      simp [cornerUp, bottomRight] at hv
      omega
    · constructor
      · intro x h
        have hv := congrArg (fun r : Fin B.rows => r.val) h
        have hx := x.isLt
        simp [rowFromRowsMinusTwo, bottomRight] at hv
        omega
      · intro x hrow _hcol
        have hv := congrArg (fun r : Fin B.rows => r.val) hrow
        have hx := x.isLt
        simp [rowFromRowsMinusOne, bottomRight] at hv
        omega
  · constructor
    · constructor
      · intro x h
        have hv := congrArg (fun r : Fin B.rows => r.val) h
        have hx := x.isLt
        simp [rowFromRowsMinusTwo, cornerUp, bottomRight] at hv
        omega
      · intro _x _hrow hcol
        have hv := congrArg (fun c : Fin B.cols => c.val) hcol
        simp [colZero, colOneOfTwo] at hv
    · constructor
      · exact (List.nodup_finRange (B.rows - 2)).map
          (by
            intro a b h
            apply Fin.ext
            have hv := congrArg (fun c : Cell B => c.1.val) h
            simpa [rowFromRowsMinusTwo] using hv)
      · constructor
        · exact (List.nodup_finRange (B.rows - 1)).map
            (by
              intro a b h
              apply Fin.ext
              have hv := congrArg (fun c : Cell B => c.1.val) h
              simpa [rowFromRowsMinusOne] using hv)
        · intro _a _b _hrow hcol
          have hv := congrArg (fun c : Fin B.cols => c.val) hcol
          simp [colZero, colOneOfTwo] at hv

lemma twoColumnRoute_nodup {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : B.cols = 2) :
    ((nonblankSubtypeList
        (cornerLeft B :: cornerUpLeft B :: twoColumnRouteYs B hcols)
        (twoColumnRoute_nonblank hrows hcols)).map
      (nonblankCellEquivFin B)).Nodup := by
  have hsub :
      (nonblankSubtypeList
        (cornerLeft B :: cornerUpLeft B :: twoColumnRouteYs B hcols)
        (twoColumnRoute_nonblank hrows hcols)).Nodup := by
    apply List.Nodup.of_map (f := fun c : {c : Cell B // c ≠ bottomRight B} => c.1)
    simpa [nonblankSubtypeList_map_val] using twoColumnRoute_nodup_cells hrows hcols
  exact hsub.map (nonblankCellEquivFin B).injective

lemma twoColumnRoute_covers {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : B.cols = 2) :
    ((nonblankSubtypeList
        (cornerLeft B :: cornerUpLeft B :: twoColumnRouteYs B hcols)
        (twoColumnRoute_nonblank hrows hcols)).map
      (nonblankCellEquivFin B)).toFinset = Finset.univ := by
  apply finList_toFinset_eq_univ_of_nodup_length
  · exact twoColumnRoute_nodup hrows hcols
  · simpa [nonblankSubtypeList] using twoColumnRoute_length hrows hcols

end NPuzzle.Rect
