import NPuzzle.FourFour
import NPuzzle.FourFour.TileListVertical

namespace NPuzzle.FourFour

/-- With blank at bottom-right, list rank equals cell index. -/
lemma rankExcept_bottomRight (c : Cell) (hc : c ≠ bottomRight) :
    rankExcept bottomRight c = c.val := by
  fin_cases c <;> simp [rankExcept_val, bottomRight] at hc ⊢

@[simp] lemma rankExcept_bottomRight_ten : rankExcept bottomRight ⟨10, by omega⟩ = 10 := by
  native_decide

@[simp] lemma rankExcept_bottomRight_eleven : rankExcept bottomRight ⟨11, by omega⟩ = 11 := by
  native_decide

@[simp] lemma rankExcept_bottomRight_fourteen : rankExcept bottomRight ⟨14, by omega⟩ = 14 := by
  native_decide

end NPuzzle.FourFour
