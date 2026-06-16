import Mathlib.Data.Finset.Interval
import Mathlib.Data.List.Sort
import NPuzzle.FourFour
import NPuzzle.FourFour.Inversion

namespace NPuzzle.FourFour

open List

/-- Every value in `1…15` appears in a length-`15` nodup list bounded in `1…15`. -/
lemma mem_Icc_one_fifteen_of_nodup_len (L : List ℕ) (hlen : L.length = 15)
    (hnd : L.Nodup) (hmem : ∀ x ∈ L, 1 ≤ x ∧ x ≤ 15) :
    ∀ a, 1 ≤ a → a ≤ 15 → a ∈ L := by
  intro a ha hb
  rw [← List.mem_toFinset]
  have hcard : L.toFinset.card = 15 := by rw [List.toFinset_card_of_nodup hnd, hlen]
  have hsub : L.toFinset ⊆ Finset.Icc 1 15 := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact Finset.mem_Icc.mpr ⟨(hmem x hx).1, (hmem x hx).2⟩
  have hIcc : (Finset.Icc 1 15).card = 15 := by
    native_decide
  have heq : L.toFinset = Finset.Icc 1 15 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hIcc, hcard])
  exact heq.symm.subset (Finset.mem_Icc.mpr ⟨ha, hb⟩)

/-- A sorted nodup list of length `15` inside `1…15` is `[1,…,15]`. -/
lemma eq_range15_map_succ_of_sorted (L : List ℕ) (hlen : L.length = 15) (hnd : L.Nodup)
    (hs : List.Pairwise (· ≤ ·) L) (hmem : ∀ x ∈ L, 1 ≤ x ∧ x ≤ 15) :
    L = (List.range 15).map (· + 1) := by
  let G := (List.range 15).map (· + 1)
  have hLlt : L.SortedLT := by
    rw [sortedLT_iff_getElem_lt_getElem_of_lt]
    intro i j hi hj hij
    have hle := Pairwise.rel_get_of_le hs (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) (Nat.le_of_lt hij)
    have hne : L[i] ≠ L[j] := by
      intro heq
      have := (Nodup.getElem_inj_iff hnd).mp heq
      omega
    exact Nat.lt_of_le_of_ne hle hne
  have hGlt : G.SortedLT := by
    change (List.range 15).map (fun n => n + 1) |>.SortedLT
    exact
      (StrictMono.sortedLT_listMap (f := fun n => n + 1) fun _ _ hab =>
        Nat.add_lt_add_right hab 1).mpr (sortedLT_range 15)
  have hiff : ∀ a, a ∈ L ↔ a ∈ G := by
    intro a
    simp only [G, List.mem_map, List.mem_range]
    constructor
    · intro ha
      have ⟨ha1, ha2⟩ := hmem a ha
      exact ⟨a - 1, by omega, by omega⟩
    · intro
      exact mem_Icc_one_fifteen_of_nodup_len L hlen hnd hmem a (by omega) (by omega)
  exact SortedLT.eq_of_mem_iff hLlt hGlt hiff

end NPuzzle.FourFour
