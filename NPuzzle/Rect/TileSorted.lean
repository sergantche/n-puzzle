import Mathlib.Data.List.Sort
import NPuzzle.Rect.TilePerm

namespace NPuzzle.Rect

/-!
Sorted rectangular tile lists.

This is the board-generic analogue of `NPuzzle.FourFour.TileSorted`, extended
with the immediate consequence for `tileListPerm`.
-/

/-- A sorted nodup list of length `n` inside `1…n` is `[1, …, n]`. -/
lemma eq_range_map_succ_of_sorted (L : List ℕ) {n : ℕ} (hlen : L.length = n)
    (hnd : L.Nodup) (hs : List.Pairwise (· ≤ ·) L)
    (hmem : ∀ x ∈ L, 1 ≤ x ∧ x ≤ n) :
    L = (List.range n).map (· + 1) := by
  let G := (List.range n).map (· + 1)
  have hLlt : L.SortedLT := by
    rw [List.sortedLT_iff_getElem_lt_getElem_of_lt]
    intro i j hi hj hij
    have hle := List.Pairwise.rel_get_of_le hs (a := ⟨i, hi⟩) (b := ⟨j, hj⟩)
      (Nat.le_of_lt hij)
    have hne : L[i] ≠ L[j] := by
      intro heq
      have := hnd.getElem_inj_iff.mp heq
      omega
    exact Nat.lt_of_le_of_ne hle hne
  have hGlt : G.SortedLT := by
    change (List.range n).map (fun m => m + 1) |>.SortedLT
    exact
      (StrictMono.sortedLT_listMap (f := fun m => m + 1) fun _ _ hab =>
        Nat.add_lt_add_right hab 1).mpr (List.sortedLT_range n)
  have hiff : ∀ a, a ∈ L ↔ a ∈ G := by
    intro a
    simp only [G, List.mem_map, List.mem_range]
    constructor
    · intro ha
      have ⟨ha1, ha2⟩ := hmem a ha
      exact ⟨a - 1, by omega, by omega⟩
    · rintro ⟨_, _, rfl⟩
      exact mem_Icc_of_nodup_len L hlen hnd hmem _ (by omega) (by omega)
  exact List.SortedLT.eq_of_mem_iff hLlt hGlt hiff

lemma tileList_eq_goalTileList_of_sorted {B : Board} (L : List ℕ)
    (hs : TileListSpec (bottomRight B) L) (hsorted : List.Pairwise (· ≤ ·) L) :
    L = (List.range B.tileCount).map (· + 1) :=
  eq_range_map_succ_of_sorted L hs.length_eq hs.nodup hsorted hs.mem_Icc

lemma tileListPerm_sorted_eq_one {B : Board} (L : List ℕ)
    (hs : TileListSpec (bottomRight B) L) (hsorted : List.Pairwise (· ≤ ·) L) :
    tileListPerm L hs = 1 := by
  ext i
  rw [tileListPerm_apply]
  have hi : i.1 < L.length := by
    rw [hs.length_eq]
    exact i.isLt
  have hiB : i.1 < B.tileCount := by
    rw [hs.length_eq] at hi
    exact hi
  have heq := tileList_eq_goalTileList_of_sorted L hs hsorted
  have hi' : i.1 < ((List.range B.tileCount).map (fun m => m + 1)).length := by
    simp [List.length_map, List.length_range, hiB]
  have hmap : ((List.range B.tileCount).map (fun m => m + 1))[i.1]'hi' = i.1 + 1 := by
    simp [List.getElem_map, List.getElem_range]
  have hval : L[i.1]'hi = i.1 + 1 := by
    simp [heq, hmap]
  simp [tileLabelAt, hval]

end NPuzzle.Rect
