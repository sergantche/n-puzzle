import NPuzzle.FourFour

set_option maxHeartbeats 800000

namespace NPuzzle.FourFour

lemma adjacent_component {a b : Cell} (h : adjacent a b) :
    sameRow a b ∨ sameCol a b := by
  rcases h with (⟨hr, _⟩ | ⟨hc, _⟩)
  · exact Or.inl hr
  · exact Or.inr hc

lemma row_eq_of_sameRow {a b : Cell} (h : sameRow a b) : row a = row b := by
  ext
  simpa [sameRow] using h

lemma blankRowFromBottom_eq_sameRow {a b : Cell} (h : sameRow a b) :
    blankRowFromBottom a = blankRowFromBottom b := by
  simp [blankRowFromBottom, row_eq_of_sameRow h]

lemma sameRow.symm {a b : Cell} (h : sameRow a b) : sameRow b a := by
  simpa [sameRow, eq_comm] using h

/-- Step 2 (core): horizontal neighbor swap leaves row-major `L` unchanged. -/
lemma tileList_swap_horizontal (cells : Cell → ℕ) (b n : Cell)
    (hab : adjacent b n) (hr : sameRow b n) :
    (cellsRowMajorExcept n).map (swapAt cells b n) = (cellsRowMajorExcept b).map cells := by
  fin_cases b <;> fin_cases n <;>
    simp only [adjacent, sameRow, sameCol] at hab hr <;>
    first | contradiction |
      simp [cellsRowMajorExcept, swapAt, List.finRange, List.filter, List.map]

lemma tileList_slide_horizontal (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n)
    (hr : sameRow (blank cfg) n) :
    tileList (slide cfg n h) = tileList cfg := by
  unfold tileList slide
  rw [blank_slide cfg n h]
  exact tileList_swap_horizontal cfg.cells (blank cfg) n h hr

lemma invStat_slide_horizontal (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n)
    (hr : sameRow (blank cfg) n) :
    invStat (slide cfg n h) = invStat cfg := by
  unfold invStat
  rw [tileList_slide_horizontal cfg n h hr]

lemma blankRow_slide_horizontal (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n)
    (hr : sameRow (blank cfg) n) :
    blankRowFromBottom n = blankRowFromBottom (blank cfg) :=
  blankRowFromBottom_eq_sameRow hr.symm

lemma parityClass_slide_horizontal (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n)
    (hr : sameRow (blank cfg) n) :
    parityClass (slide cfg n h) = parityClass cfg := by
  unfold parityClass
  rw [blank_slide cfg n h, invStat_slide_horizontal cfg n h hr,
    blankRow_slide_horizontal cfg n h hr]

/-- Vertical slide flips `I(L) mod 2` (step 3; width `M = 4`). Still open. -/
lemma invStat_slide_vertical_mod (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n)
    (hc : sameCol (blank cfg) n) :
    invStat (slide cfg n h) % 2 = (invStat cfg + 1) % 2 := by
  sorry

lemma blankRow_adjacent_vertical {a b : Cell} (h : adjacent a b) (hc : sameCol a b) :
    blankRowFromBottom b % 2 = (blankRowFromBottom a + 1) % 2 := by
  rw [blankRowFromBottom_val, blankRowFromBottom_val]
  rcases adjacent_vertical_only h hc with hup | hdown
  · have : b.val = a.val + 4 := by omega
    rw [this]
    omega
  · have : a.val = b.val + 4 := by omega
    rw [this]
    omega

lemma blankRow_slide_vertical_mod (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n)
    (hc : sameCol (blank cfg) n) :
    blankRowFromBottom n % 2 = (blankRowFromBottom (blank cfg) + 1) % 2 :=
  blankRow_adjacent_vertical h hc

lemma parityClass_slide_vertical (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n)
    (hc : sameCol (blank cfg) n) :
    parityClass (slide cfg n h) = parityClass cfg := by
  unfold parityClass
  rw [blank_slide cfg n h]
  have hi := invStat_slide_vertical_mod cfg n h hc
  have hr := blankRow_slide_vertical_mod cfg n h hc
  omega

lemma parityClass_legalStep {cfg cfg' : Config} (h : legalStep cfg cfg') :
    parityClass cfg = parityClass cfg' := by
  rcases h with ⟨n, h, rfl⟩
  rcases adjacent_component h with hr | hc
  · exact (parityClass_slide_horizontal cfg n h hr).symm
  · exact (parityClass_slide_vertical cfg n h hc).symm

lemma parityClass_reachable {cfg cfg' : Config} (h : Reachable cfg cfg') :
    parityClass cfg = parityClass cfg' := by
  induction h with
  | refl => rfl
  | tail hab hbc ih => exact ih.trans (parityClass_legalStep hbc)

lemma tileList_goal : tileList goal = (List.range 15).map (· + 1) := by
  simp only [tileList]
  rw [blank_goal]
  simp only [goal]
  native_decide

lemma invStat_goal : invStat goal = 0 := by
  unfold invStat
  rw [tileList_goal]
  native_decide

lemma blankRow_bottomRight : blankRowFromBottom bottomRight = 1 := by
  simp [blankRowFromBottom, bottomRight, row]

/-- Step 7: standard goal value for even `M = 4`. -/
lemma parityClass_goal : parityClass goal = 1 := by
  unfold parityClass
  rw [blank_goal, invStat_goal, blankRow_bottomRight]

/-- Step 8 (necessity): reachability ⇒ correct parity. -/
lemma reachable_imp_parity (cfg : Config) (h : Reachable cfg goal) :
    parityClass cfg = 1 := by
  rw [← parityClass_goal, parityClass_reachable h]

end NPuzzle.FourFour
