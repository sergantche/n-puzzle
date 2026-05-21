import Mathlib.Data.List.InsertIdx
import NPuzzle.FourFour

namespace NPuzzle.FourFour

namespace Inversion

open List

/-!
Moving one list entry flips `inversionCount mod 2` iff the index shift is odd.

Proof idea (the lecture proof): decompose `eraseIdx` + `insertIdx` into `|p - q|` adjacent
swaps; each adjacent transposition toggles parity when values are distinct (`Nodup`).
-/

/-- Adjacent swap at indices `i`, `i+1` toggles inversion parity when the values differ. -/
lemma inversionCount_swapAdjacent (L : List ℕ) (i : ℕ) (hi : i + 1 < L.length)
    (hne : L[i] ≠ L[i + 1]) :
    inversionCount (L.set i L[i + 1] |>.set (i + 1) L[i]) % 2 = (inversionCount L + 1) % 2 := by
  sorry

/-- One-element move (`erase` at `p`, `insert` at `q`) changes `I(L) mod 2` by `(p - q) mod 2`. -/
lemma inversionCount_erase_insert_mod (L : List ℕ) (p q : ℕ) (hp : p < L.length) (hq : q ≤ L.length)
    (hne : p ≠ q) (hnd : L.Nodup) :
    inversionCount (L.eraseIdx p |>.insertIdx q (L[p]'(by omega))) % 2 =
      (inversionCount L + (p - q)) % 2 := by
  sorry

/-- Corollary for an odd index shift (vertical slide on 4×4 has `|p - q| ≡ 1`). -/
lemma inversionCount_erase_insert_odd (L : List ℕ) (p q : ℕ) (hp : p < L.length) (hq : q ≤ L.length)
    (hne : p ≠ q) (hnd : L.Nodup) (hodd : (p - q) % 2 = 1) :
    inversionCount (L.eraseIdx p |>.insertIdx q (L[p]'(by omega))) % 2 = (inversionCount L + 1) % 2 := by
  rw [inversionCount_erase_insert_mod L p q hp hq hne hnd, Nat.add_mod, hodd, one_mod]

end Inversion

lemma tileList_nodup (cfg : Config) : (tileList cfg).Nodup := by
  sorry

lemma invStat_slide_vertical_mod (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n)
    (hc : sameCol (blank cfg) n) :
    invStat (slide cfg n h) % 2 = (invStat cfg + 1) % 2 := by
  unfold invStat
  rw [tileList_slide_vertical cfg n h hc]
  set L := tileList cfg with hL
  set b := blank cfg with hb
  set p := rankExcept b n with hp
  set q := rankExcept n b with hq
  have hne : p ≠ q := by
    intro heq
    have := rankExcept_vertical_mod b n h hc
    rw [heq] at this
    omega
  have hodd : (p - q) % 2 = 1 := by
    have := rankExcept_vertical_mod b n h hc
    omega
  have hnd : L.Nodup := tileList_nodup cfg
  have hne' : b ≠ n := adjacent.ne h
  have hidx := rankExcept_vertical_lt b n h hc
  have hp' : p < L.length := by
    rw [hL, hb, hp, tileList, cellsRowMajorExcept_length]
    exact hidx.1
  have hq' : q ≤ L.length := by
    rw [hL, hb, hq, tileList, cellsRowMajorExcept_length]
    exact Nat.le_of_lt hidx.2
  simpa [hL] using
    Inversion.inversionCount_erase_insert_odd L p q hp' hq' hne hnd hodd

end NPuzzle.FourFour
