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

lemma finRange_head_val_eq_zero {n : ℕ} {a : Fin n}
    (ha : a ∈ (List.finRange n).head?) :
    a.val = 0 := by
  have hne : List.finRange n ≠ [] :=
    List.ne_nil_of_mem (List.mem_of_mem_head? ha)
  have hhead :
      (List.finRange n).head hne = a :=
    List.head_of_mem_head? ha
  have hval := congrArg Fin.val hhead
  simpa [List.head_eq_getElem_zero] using hval.symm

lemma finRange_getLast_val_add_one {n : ℕ} {a : Fin n}
    (ha : a ∈ (List.finRange n).getLast?) :
    a.val + 1 = n := by
  have hne : List.finRange n ≠ [] :=
    List.ne_nil_of_mem (List.mem_of_mem_getLast? ha)
  have hget :
      (List.finRange n).getLast hne = a :=
    List.getLast_of_mem_getLast? ha
  have hval := congrArg Fin.val hget
  simp [List.getLast_eq_getElem] at hval
  omega

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

def twoColumnLeftTail (B : Board) : List (Cell B) :=
  (List.finRange (B.rows - 2)).reverse.map fun r =>
    (rowFromRowsMinusTwo (B := B) r, colZero B)

def twoColumnRightColumn (B : Board) (hcols : B.cols = 2) : List (Cell B) :=
  (List.finRange (B.rows - 1)).map fun r =>
    (rowFromRowsMinusOne (B := B) r, colOneOfTwo hcols)

def twoColumnRouteYs (B : Board) (hcols : B.cols = 2) : List (Cell B) :=
  twoColumnLeftTail B ++ twoColumnRightColumn B hcols

lemma adjacent_cornerUpLeft_twoColumnLeftTail_head {B : Board}
    (hcols : B.cols = 2) :
    ∀ y ∈ (twoColumnLeftTail B).head?, adjacent (cornerUpLeft B) y := by
  intro y hy
  simp [twoColumnLeftTail] at hy
  rcases hy with ⟨a, hlast, rfl⟩
  have hmem : a ∈ (List.finRange (B.rows - 2)).getLast? := by
    rw [hlast]
    simp
  have hval := finRange_getLast_val_add_one hmem
  rw [cornerUpLeft_eq_twoColumn hcols]
  refine Or.inr ⟨rfl, Or.inr ?_⟩
  simp [cornerUp, bottomRight, rowFromRowsMinusTwo]
  omega

lemma isChain_twoColumn_leftSegment {B : Board}
    (hcols : B.cols = 2) :
    List.IsChain adjacent (cornerUpLeft B :: twoColumnLeftTail B) := by
  apply List.IsChain.cons
  · simpa [twoColumnLeftTail] using isChain_twoColumn_leftTail B
  · exact adjacent_cornerUpLeft_twoColumnLeftTail_head hcols

lemma adjacent_twoColumn_leftSegment_rightColumn_head {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : B.cols = 2) :
    ∀ x ∈ (cornerUpLeft B :: twoColumnLeftTail B).getLast?,
      ∀ y ∈ (twoColumnRightColumn B hcols).head?,
        adjacent x y := by
  intro x hx y hy
  simp [twoColumnLeftTail, twoColumnRightColumn] at hx hy
  rcases hy with ⟨a, hhead, rfl⟩
  have hmemHead : a ∈ (List.finRange (B.rows - 1)).head? := by
    rw [hhead]
    simp
  have hvalHead := finRange_head_val_eq_zero hmemHead
  rw [List.getLast?_cons] at hx
  cases htailLast :
      ((List.map (fun r => (rowFromRowsMinusTwo (B := B) r, colZero B))
        (List.finRange (B.rows - 2))).reverse).getLast? with
  | none =>
      simp [htailLast] at hx
      subst x
      have htailNil :
          (List.map (fun r => (rowFromRowsMinusTwo (B := B) r, colZero B))
            (List.finRange (B.rows - 2))).reverse = [] := by
        cases htail :
            (List.map (fun r => (rowFromRowsMinusTwo (B := B) r, colZero B))
              (List.finRange (B.rows - 2))).reverse with
        | nil => rfl
        | cons z zs =>
            simp [htail] at htailLast
      have hrowsSub : B.rows - 2 = 0 := by
        have hlen := congrArg List.length htailNil
        simpa using hlen
      refine Or.inl ⟨?_, Or.inl ?_⟩
      · apply Fin.ext
        simp [cornerUpLeft, bottomRight, rowFromRowsMinusOne]
        omega
      · simp [cornerUpLeft, bottomRight, colOneOfTwo, hcols]
  | some z =>
      simp [htailLast] at hx
      subst x
      rw [List.getLast?_reverse] at htailLast
      simp at htailLast
      rcases htailLast with ⟨b, hbhead, rfl⟩
      have hmemTailHead : b ∈ (List.finRange (B.rows - 2)).head? := by
        rw [hbhead]
        simp
      have hbvalHead := finRange_head_val_eq_zero hmemTailHead
      refine Or.inl ⟨?_, Or.inl ?_⟩
      · apply Fin.ext
        simp [rowFromRowsMinusTwo, rowFromRowsMinusOne]
        omega
      · simp [colZero, colOneOfTwo]

lemma adjacent_twoColumn_rightColumn_bottomRight {B : Board}
    (hcols : B.cols = 2) :
    ∀ x ∈ (twoColumnRightColumn B hcols).getLast?,
      ∀ y ∈ [bottomRight B].head?,
        adjacent x y := by
  intro x hx y hy
  simp [twoColumnRightColumn] at hx hy
  rcases hx with ⟨a, hlast, rfl⟩
  subst y
  have hmem : a ∈ (List.finRange (B.rows - 1)).getLast? := by
    rw [hlast]
    simp
  have hval := finRange_getLast_val_add_one hmem
  refine Or.inr ⟨?_, Or.inl ?_⟩
  · apply Fin.ext
    simp [bottomRight, colOneOfTwo, hcols]
  · simp [bottomRight, rowFromRowsMinusOne]
    omega

lemma twoColumnRoute_chain {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : B.cols = 2) :
    AdjacentChain (bottomRight B)
      ((cornerLeft B :: cornerUpLeft B :: twoColumnRouteYs B hcols) ++
        [bottomRight B]) := by
  rw [adjacentChain_iff_isChain]
  simp only [List.cons_append]
  rw [List.isChain_cons_cons]
  constructor
  · exact adjacent_bottomRight_cornerLeft B (by omega)
  rw [List.isChain_cons_cons]
  constructor
  · exact adjacent_cornerLeft_cornerUpLeft B hrows
  · rw [twoColumnRouteYs, List.append_assoc]
    change List.IsChain adjacent
      ((cornerUpLeft B :: twoColumnLeftTail B) ++
        (twoColumnRightColumn B hcols ++ [bottomRight B]))
    apply List.IsChain.append
    · exact isChain_twoColumn_leftSegment hcols
    · apply List.IsChain.append
      · simpa [twoColumnRightColumn] using isChain_twoColumn_rightColumn hcols
      · simp
      · exact adjacent_twoColumn_rightColumn_bottomRight hcols
    · intro x hx y hy
      have hright_ne : twoColumnRightColumn B hcols ≠ [] := by
        simp [twoColumnRightColumn]
        omega
      rw [List.head?_append_of_ne_nil (twoColumnRightColumn B hcols) hright_ne] at hy
      exact adjacent_twoColumn_leftSegment_rightColumn_head hrows hcols x hx y hy

lemma twoColumnRoute_nonblank {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : B.cols = 2) :
    ∀ c ∈ cornerLeft B :: cornerUpLeft B :: twoColumnRouteYs B hcols,
      c ≠ bottomRight B := by
  intro c hc
  have hcolsLe : 2 ≤ B.cols := by omega
  simp [twoColumnRouteYs, twoColumnLeftTail, twoColumnRightColumn] at hc
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
  simp [twoColumnRouteYs, twoColumnLeftTail, twoColumnRightColumn,
    Board.tileCount, Board.size, hcols]
  omega

lemma twoColumnRoute_nodup_cells {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : B.cols = 2) :
    (cornerLeft B :: cornerUpLeft B :: twoColumnRouteYs B hcols).Nodup := by
  rw [cornerLeft_eq_twoColumn hcols, cornerUpLeft_eq_twoColumn hcols]
  simp [twoColumnRouteYs, twoColumnLeftTail, twoColumnRightColumn, List.nodup_append]
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

def twoColumnPrefixedFullRoute {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : B.cols = 2) :
    PrefixedFullRoute B hrows (by omega) where
  ys := twoColumnRouteYs B hcols
  chain := twoColumnRoute_chain hrows hcols
  nonblank := twoColumnRoute_nonblank hrows hcols
  nodup := twoColumnRoute_nodup hrows hcols
  covers := twoColumnRoute_covers hrows hcols

lemma reachable_goal_to_cfg_bottomRight_of_twoColumn {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : B.cols = 2)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable (goal B) cfg :=
  reachable_goal_to_cfg_bottomRight_of_prefixedFullRoute
    (twoColumnPrefixedFullRoute hrows hcols) cfg hbr hpar

lemma tiles_to_goal_bottomRight_of_twoColumn {B : Board}
    (hrows : 2 ≤ B.rows) (hcols : B.cols = 2)
    (cfg : Config B) (hbr : blank cfg = bottomRight B)
    (hpar : parityClass cfg = targetParity B) :
    Reachable cfg (goal B) :=
  tiles_to_goal_bottomRight_of_prefixedFullRoute
    (twoColumnPrefixedFullRoute hrows hcols) cfg hbr hpar

end NPuzzle.Rect
