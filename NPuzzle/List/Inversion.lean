import Mathlib.Data.Nat.Basic

namespace NPuzzle.List

/-!
Basic inversion count for lists of natural-number labels.

The heavier parity lemmas still live in `NPuzzle.FourFour.Inversion` for now;
this file starts the geometry-free extraction with the shared definition.
-/

/-- Pair-inversion count for a list of natural numbers. -/
def inversionCount : List ℕ → ℕ
  | [] => 0
  | x :: xs =>
      xs.foldl (fun acc y => acc + if x > y then 1 else 0) 0 + inversionCount xs

end NPuzzle.List
