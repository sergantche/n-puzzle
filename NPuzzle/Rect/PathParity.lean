import NPuzzle.Rect.PathSufficiency

namespace NPuzzle.Rect

/-!
Checkerboard parity for rectangular blank paths.

This separates a real geometric constraint from the sufficiency wrapper:
a simple closed route through every cell can exist only on an even-size board.
-/

/-- Checkerboard color, valued in `ZMod 2`. -/
def cellParity {B : Board} (c : Cell B) : ZMod 2 :=
  (c.1.val + c.2.val : ℕ)

lemma cellParity_adjacent {B : Board} {a b : Cell B}
    (h : adjacent a b) :
    cellParity b = cellParity a + 1 := by
  rcases h with (⟨hr, hstep⟩ | ⟨hc, hstep⟩)
  · rcases hstep with hstep | hstep
    · unfold cellParity
      unfold sameRow at hr
      rw [← hr, ← hstep]
      simp [Nat.cast_add, add_assoc]
    · unfold cellParity
      unfold sameRow at hr
      rw [← hr, ← hstep]
      simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
        (show (1 : ZMod 2) + 1 = 0 by decide)
  · rcases hstep with hstep | hstep
    · unfold cellParity
      unfold sameCol at hc
      rw [← hc, ← hstep]
      simp [Nat.cast_add, add_assoc, add_comm, add_left_comm]
    · unfold cellParity
      unfold sameCol at hc
      rw [← hc, ← hstep]
      simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
        (show (1 : ZMod 2) + 1 = 0 by decide)

lemma AdjacentChain.cellParity_endpoint {B : Board} {a : Cell B} :
    ∀ {xs : List (Cell B)}, AdjacentChain a xs →
      cellParity (listEndpoint a xs) = cellParity a + (xs.length : ZMod 2)
  | [], _ => by simp [listEndpoint]
  | b :: xs, hchain => by
      have ih := AdjacentChain.cellParity_endpoint (a := b) hchain.2
      rw [listEndpoint_cons, ih, cellParity_adjacent hchain.1]
      simp [Nat.cast_add, add_assoc, add_comm]

lemma AdjacentChain.length_even_of_endpoint {B : Board} {a : Cell B}
    {xs : List (Cell B)}
    (hchain : AdjacentChain a xs)
    (hend : listEndpoint a xs = a) :
    Even xs.length := by
  have hpar := AdjacentChain.cellParity_endpoint (a := a) hchain
  rw [hend] at hpar
  have hzero : (xs.length : ZMod 2) = 0 := by
    have hpar' : cellParity a + (xs.length : ZMod 2) = cellParity a + 0 := by
      simpa using hpar.symm
    exact add_left_cancel hpar'
  exact ZMod.natCast_eq_zero_iff_even.mp hzero

lemma PrefixedFullRoute.length_eq_tileCount {B : Board}
    {hrows : 2 ≤ B.rows} {hcols : 2 ≤ B.cols}
    (route : PrefixedFullRoute B hrows hcols) :
    (cornerLeft B :: cornerUpLeft B :: route.ys).length = B.tileCount := by
  have hlen :
      ((nonblankSubtypeList (cornerLeft B :: cornerUpLeft B :: route.ys)
        route.nonblank).map (nonblankCellEquivFin B)).length = B.tileCount := by
    rw [← List.toFinset_card_of_nodup route.nodup, route.covers]
    simp
  simpa [nonblankSubtypeList] using hlen

lemma PrefixedFullRoute.size_even {B : Board}
    {hrows : 2 ≤ B.rows} {hcols : 2 ≤ B.cols}
    (route : PrefixedFullRoute B hrows hcols) :
    Even B.size := by
  let xs := cornerLeft B :: cornerUpLeft B :: route.ys
  have hpathEven :
      Even (xs ++ [bottomRight B]).length :=
    AdjacentChain.length_even_of_endpoint
      (a := bottomRight B) route.chain
      (by simp [xs, listEndpoint_append_singleton])
  have hrouteLen : xs.length = B.tileCount := by
    simpa [xs] using route.length_eq_tileCount
  rw [List.length_append, List.length_singleton, hrouteLen] at hpathEven
  have hsize : B.tileCount + 1 = B.size := Board.tileCount_add_one B
  rwa [hsize] at hpathEven

lemma PrefixedFullRoute.size_mod_two_eq_zero {B : Board}
    {hrows : 2 ≤ B.rows} {hcols : 2 ≤ B.cols}
    (route : PrefixedFullRoute B hrows hcols) :
    B.size % 2 = 0 :=
  Nat.even_iff.mp route.size_even

end NPuzzle.Rect
