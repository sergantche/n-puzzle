import Mathlib.Data.Finset.Interval
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.Perm.Basic
import NPuzzle.Rect.TileGlue

namespace NPuzzle.Rect

open List

/-!
Rectangular bridge from `tileList` data back to configurations.

This is the board-generic analogue of the first half of
`NPuzzle.FourFour.TilePerm`: a valid row-major tile list at a fixed blank cell
can be packaged as a `Config`, and this packaging recovers the same `tileList`.
-/

/-- A row-major tile list with blank at `b`. -/
structure TileListSpec {B : Board} (b : Cell B) (L : List ℕ) : Prop where
  length_eq : L.length = B.tileCount
  nodup : L.Nodup
  mem_Icc : ∀ x ∈ L, 1 ≤ x ∧ x ≤ B.tileCount

/-- Every value in `1…n` appears in a length-`n` nodup list bounded in `1…n`. -/
lemma mem_Icc_of_nodup_len (L : List ℕ) {n : ℕ} (hlen : L.length = n)
    (hnd : L.Nodup) (hmem : ∀ x ∈ L, 1 ≤ x ∧ x ≤ n) :
    ∀ a, 1 ≤ a → a ≤ n → a ∈ L := by
  intro a ha hb
  rw [← List.mem_toFinset]
  have hcard : L.toFinset.card = n := by
    rw [List.toFinset_card_of_nodup hnd, hlen]
  have hsub : L.toFinset ⊆ Finset.Icc 1 n := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact Finset.mem_Icc.mpr ⟨(hmem x hx).1, (hmem x hx).2⟩
  have hIcc : (Finset.Icc 1 n).card = n := by
    simp
  have heq : L.toFinset = Finset.Icc 1 n :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hIcc, hcard])
  exact heq.symm.subset (Finset.mem_Icc.mpr ⟨ha, hb⟩)

lemma tileListSpec_goal (B : Board) : TileListSpec (bottomRight B) (tileList (goal B)) where
  length_eq := tileList_length (goal B)
  nodup := tileList_nodup (goal B)
  mem_Icc := fun _ hx => tileList_mem_Icc (goal B) hx

lemma tileListSpec_of_config {B : Board} (cfg : Config B) (b : Cell B) (_hb : blank cfg = b) :
    TileListSpec b (tileList cfg) where
  length_eq := tileList_length cfg
  nodup := tileList_nodup cfg
  mem_Icc := fun _ hx => tileList_mem_Icc cfg hx

private lemma ne_of_not_eq {α : Type*} {a b : α} (h : ¬ a = b) : a ≠ b := by
  rintro rfl
  exact h rfl

lemma rankExcept_lt_tileList {B : Board} (b : Cell B) (L : List ℕ)
    (hlen : L.length = B.tileCount) (c : Cell B) (hc : c ≠ b) :
    rankExcept b c < L.length := by
  simpa [hlen, cellsRowMajorExcept_length] using rankExcept_lt hc

/-- Cell labels from a tile list with blank at `b`. -/
def cellsOfTileList {B : Board} (b : Cell B) (L : List ℕ)
    (hlen : L.length = B.tileCount) : Cell B → ℕ :=
  fun c =>
    if h : c = b then 0
    else L[rankExcept b c]'(rankExcept_lt_tileList b L hlen c (ne_of_not_eq h))

lemma cellsOfTileList_eq {B : Board} (b : Cell B) (L : List ℕ)
    (hlen : L.length = B.tileCount) (c : Cell B) (hc : c ≠ b) :
    cellsOfTileList b L hlen c =
      L[rankExcept b c]'(rankExcept_lt_tileList b L hlen c hc) := by
  simp [cellsOfTileList, hc]

lemma cellsOfTileList_le {B : Board} (b : Cell B) (L : List ℕ)
    (hs : TileListSpec b L) (c : Cell B) :
    cellsOfTileList b L hs.length_eq c ≤ B.tileCount := by
  simp only [cellsOfTileList]
  split_ifs with hcb
  · omega
  · exact (hs.mem_Icc _ (List.getElem_mem
        (rankExcept_lt_tileList b L hs.length_eq c (ne_of_not_eq hcb)))).2

lemma cellsOfTileList_blank {B : Board} (b : Cell B) (L : List ℕ)
    (hlen : L.length = B.tileCount) :
    cellsOfTileList b L hlen b = 0 := by
  simp [cellsOfTileList]

lemma existsUnique_cell_of_list_val {B : Board} (b : Cell B) (L : List ℕ)
    (hs : TileListSpec b L) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ B.tileCount) :
    ∃! c : Cell B, cellsOfTileList b L hs.length_eq c = k := by
  have hkmem : k ∈ L :=
    mem_Icc_of_nodup_len L hs.length_eq hs.nodup (fun x hx => hs.mem_Icc x hx)
      k hk.1 hk.2
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hkmem
  have hj' : j < B.tileCount := by
    rw [hs.length_eq] at hj
    exact hj
  let c := (cellsRowMajorExcept b)[j]'(by rw [cellsRowMajorExcept_length]; exact hj')
  refine ⟨c, ?_, ?_⟩
  · have hjcells : j < (cellsRowMajorExcept b).length := by
      rw [cellsRowMajorExcept_length]
      exact hj'
    have hc : c ≠ b := cellsRowMajorExcept_ne (List.getElem_mem hjcells)
    calc cellsOfTileList b L hs.length_eq c
        _ = L[rankExcept b c]'(rankExcept_lt_tileList b L hs.length_eq c hc) :=
          cellsOfTileList_eq b L hs.length_eq c hc
        _ = L[j]'hj := by
          congr
          exact rankExcept_cellsRowMajorExcept b j hjcells
        _ = k := heq
  · intro c' h'
    have hc' : c' ≠ b := by
      intro hcb
      rw [hcb, cellsOfTileList_blank] at h'
      omega
    have hjcells : j < (cellsRowMajorExcept b).length := by
      rw [cellsRowMajorExcept_length]
      exact hj'
    have hrank : rankExcept b c' = j := by
      have hidx := rankExcept_lt_tileList b L hs.length_eq c' hc'
      have heqL : L[rankExcept b c']'hidx = L[j]'hj := by
        rw [← cellsOfTileList_eq b L hs.length_eq c' hc', h', heq]
      exact (hs.nodup.getElem_inj_iff (hi := hidx) (hj := hj)).mp heqL
    have hc : c ≠ b := cellsRowMajorExcept_ne (List.getElem_mem hjcells)
    exact rankExcept_injective hc' hc (hrank.trans (rankExcept_cellsRowMajorExcept b j hjcells).symm)

lemma cellsOfTileList_eq_zero_iff {B : Board} (b : Cell B) (L : List ℕ)
    (hs : TileListSpec b L) (c : Cell B) :
    cellsOfTileList b L hs.length_eq c = 0 ↔ c = b := by
  constructor
  · intro h0
    simp only [cellsOfTileList] at h0
    split_ifs at h0 with hcb
    · exact hcb
    · have hpos := (hs.mem_Icc _ (List.getElem_mem
          (rankExcept_lt_tileList b L hs.length_eq c (ne_of_not_eq hcb)))).1
      omega
  · intro hcb
    simp [cellsOfTileList, hcb]

/-- Package a tile list and blank cell into a `Config`. -/
noncomputable def configOfTileList {B : Board} (b : Cell B) (L : List ℕ)
    (hs : TileListSpec b L) : Config B :=
  ⟨cellsOfTileList b L hs.length_eq,
    ⟨cellsOfTileList_le b L hs,
      ExistsUnique.intro b (cellsOfTileList_blank b L hs.length_eq) fun c h0 =>
        (cellsOfTileList_eq_zero_iff b L hs c).mp h0,
      fun k hk => existsUnique_cell_of_list_val b L hs k hk⟩⟩

lemma blank_configOfTileList {B : Board} (b : Cell B) (L : List ℕ)
    (hs : TileListSpec b L) :
    blank (configOfTileList b L hs) = b := by
  exact (ExistsUnique.unique (configOfTileList b L hs).valid.2.1
    (cellsOfTileList_blank b L hs.length_eq) (blank_zero (configOfTileList b L hs))).symm

lemma map_cellsOfTileList_eq {B : Board} (b : Cell B) (L : List ℕ)
    (hs : TileListSpec b L) :
    (cellsRowMajorExcept b).map (cellsOfTileList b L hs.length_eq) = L := by
  apply List.ext_getElem
  · rw [List.length_map, cellsRowMajorExcept_length, hs.length_eq]
  · intro i hi hiL
    have hi' : i < (cellsRowMajorExcept b).length := by
      simpa [List.length_map] using hi
    let c := (cellsRowMajorExcept b)[i]'hi'
    have hc : c ≠ b := cellsRowMajorExcept_ne (List.getElem_mem hi')
    rw [List.getElem_map]
    simpa [c, rankExcept_cellsRowMajorExcept b i hi'] using
      cellsOfTileList_eq b L hs.length_eq c hc

lemma tileList_configOfTileList {B : Board} (b : Cell B) (L : List ℕ)
    (hs : TileListSpec b L) :
    tileList (configOfTileList b L hs) = L := by
  dsimp [tileList]
  rw [congrArg cellsRowMajorExcept (blank_configOfTileList b L hs)]
  exact map_cellsOfTileList_eq b L hs

lemma config_eq_configOfTileList {B : Board} (cfg : Config B) (b : Cell B) (L : List ℕ)
    (hb : blank cfg = b) (ht : tileList cfg = L) (hs : TileListSpec b L) :
    cfg = configOfTileList b L hs := by
  apply config_eq_of_tileList_and_blank cfg (configOfTileList b L hs)
  · rw [blank_configOfTileList b L hs, hb]
  · rw [tileList_configOfTileList b L hs, ht]

/-!
### `Equiv.Perm (Fin B.tileCount)` from a tile list at `bottomRight`
-/

/-- Goal label at list index `i` (1-based tile value minus 1). -/
noncomputable def tileLabelAt {B : Board} (L : List ℕ) (i : Fin B.tileCount)
    (hs : TileListSpec (bottomRight B) L) : Fin B.tileCount :=
  have hi : i.1 < L.length := by
    rw [hs.length_eq]
    exact i.isLt
  let x := L[i]'hi
  have hmem : 1 ≤ x ∧ x ≤ B.tileCount := hs.mem_Icc x (List.getElem_mem hi)
  ⟨x - 1, by
    rcases hmem with ⟨hlo, hhi⟩
    omega⟩

lemma tileLabelAt_goal {B : Board} (i : Fin B.tileCount) :
    tileLabelAt (tileList (goal B)) i (tileListSpec_goal B) = i := by
  ext
  simp [tileLabelAt, tileList_goal]

lemma tileLabelAt_injective {B : Board} (L : List ℕ)
    (hs : TileListSpec (bottomRight B) L) :
    Function.Injective (fun i => tileLabelAt L i hs) := by
  intro i j hij
  have hval := congrArg Fin.val hij
  simp only [tileLabelAt] at hval
  have hi : i.1 < L.length := by
    rw [hs.length_eq]
    exact i.isLt
  have hj : j.1 < L.length := by
    rw [hs.length_eq]
    exact j.isLt
  have hlo_i := (hs.mem_Icc _ (List.getElem_mem hi)).1
  have hlo_j := (hs.mem_Icc _ (List.getElem_mem hj)).1
  have hL := Nat.pred_inj hlo_i hlo_j hval
  exact Fin.eq_of_val_eq ((hs.nodup.getElem_inj_iff (hi := hi) (hj := hj)).mp hL)

lemma tileLabelAt_surjective {B : Board} (L : List ℕ)
    (hs : TileListSpec (bottomRight B) L) :
    Function.Surjective (fun i => tileLabelAt L i hs) := by
  intro k
  have hk : k.1 + 1 ∈ L := by
    exact mem_Icc_of_nodup_len L hs.length_eq hs.nodup (fun x hx => hs.mem_Icc x hx)
      (k.1 + 1) (by omega) (by omega)
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hk
  refine ⟨⟨j, by rw [hs.length_eq] at hj; exact hj⟩, ?_⟩
  ext
  simp [tileLabelAt, heq]

/-- Bijection `Fin B.tileCount ≃ Fin B.tileCount` encoded by tile values in `L`. -/
noncomputable def tileListPerm {B : Board} (L : List ℕ)
    (hs : TileListSpec (bottomRight B) L) : Equiv.Perm (Fin B.tileCount) :=
  Equiv.ofBijective (fun i => tileLabelAt L i hs)
    ⟨tileLabelAt_injective L hs, tileLabelAt_surjective L hs⟩

lemma tileListPerm_goal (B : Board) :
    tileListPerm (tileList (goal B)) (tileListSpec_goal B) = 1 := by
  ext i
  simp [tileListPerm, tileLabelAt_goal]

lemma tileListPerm_apply {B : Board} (L : List ℕ)
    (hs : TileListSpec (bottomRight B) L) (j : Fin B.tileCount) :
    tileListPerm L hs j = tileLabelAt L j hs := by
  simp [tileListPerm, Equiv.ofBijective_apply]

lemma tileList_eq_of_tileListPerm_eq {B : Board} (L L' : List ℕ)
    (hs : TileListSpec (bottomRight B) L)
    (hs' : TileListSpec (bottomRight B) L')
    (h : tileListPerm L hs = tileListPerm L' hs') : L = L' := by
  apply List.ext_getElem
  · rw [hs.length_eq, hs'.length_eq]
  · intro i hi hi'
    have hiB : i < B.tileCount := by
      rw [hs.length_eq] at hi
      exact hi
    let j : Fin B.tileCount := ⟨i, hiB⟩
    have hlab : tileLabelAt L j hs = tileLabelAt L' j hs' := by
      rw [← tileListPerm_apply, h, tileListPerm_apply]
    have heq := congrArg Fin.val hlab
    simp only [tileLabelAt] at heq
    have hlo := (hs.mem_Icc _ (List.getElem_mem hi)).1
    have hlo' := (hs'.mem_Icc _ (List.getElem_mem hi')).1
    exact Nat.pred_inj hlo hlo' heq

/-- The permutation encoded by a configuration whose blank is at `bottomRight`. -/
noncomputable def permOfCfg {B : Board} (cfg : Config B)
    (hbr : blank cfg = bottomRight B) : Equiv.Perm (Fin B.tileCount) :=
  tileListPerm (tileList cfg) (tileListSpec_of_config cfg (bottomRight B) hbr)

lemma permOfCfg_goal (B : Board) :
    permOfCfg (goal B) (blank_goal B) = 1 := by
  simp [permOfCfg, tileListPerm_goal]

lemma tileList_eq_of_permOfCfg_eq {B : Board} (cfg cfg' : Config B)
    (hbr : blank cfg = bottomRight B) (hbr' : blank cfg' = bottomRight B)
    (h : permOfCfg cfg hbr = permOfCfg cfg' hbr') :
    tileList cfg = tileList cfg' := by
  exact tileList_eq_of_tileListPerm_eq (tileList cfg) (tileList cfg')
    (tileListSpec_of_config cfg (bottomRight B) hbr)
    (tileListSpec_of_config cfg' (bottomRight B) hbr') h

end NPuzzle.Rect
