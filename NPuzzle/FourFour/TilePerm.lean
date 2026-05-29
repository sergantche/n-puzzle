import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Perm.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import NPuzzle.FourFour
import NPuzzle.FourFour.Inversion
import NPuzzle.FourFour.TileGlue
import NPuzzle.FourFour.TileListVertical
import NPuzzle.FourFour.TileMacros
import NPuzzle.FourFour.TileRank
import NPuzzle.FourFour.TileSorted

namespace NPuzzle.FourFour

open Inversion List

/-!
Step **9b.3**: bridge `tileList` (at a fixed blank) to `Equiv.Perm (Fin 15)`.
-/

/-- A row-major tile list with blank at `b`. -/
structure TileListSpec (b : Cell) (L : List ℕ) : Prop where
  length_eq : L.length = 15
  nodup : L.Nodup
  mem_Icc : ∀ x ∈ L, 1 ≤ x ∧ x ≤ 15

lemma tileListSpec_goal : TileListSpec bottomRight (tileList goal) where
  length_eq := by simp [tileList, cellsRowMajorExcept_length]
  nodup := tileList_nodup goal
  mem_Icc := fun _ hx => tileList_mem_Icc goal hx

lemma tileListSpec_of_config (cfg : Config) (b : Cell) (_hb : blank cfg = b) :
    TileListSpec b (tileList cfg) where
  length_eq := by simp [tileList, cellsRowMajorExcept_length]
  nodup := tileList_nodup cfg
  mem_Icc := fun _ hx => tileList_mem_Icc cfg hx

private lemma ne_of_not_eq {α : Type*} {a b : α} (h : ¬ a = b) : a ≠ b := by
  rintro rfl
  exact h rfl

private lemma nat_sub_one_lt_fifteen {n : ℕ} (hlo : 1 ≤ n) (hhi : n ≤ 15) : n - 1 < 15 := by
  interval_cases n <;> simp_all

lemma rankExcept_lt_tileList (b : Cell) (L : List ℕ) (hlen : L.length = 15) (c : Cell) (hc : c ≠ b) :
    rankExcept b c < L.length := by
  simpa [hlen, cellsRowMajorExcept_length] using rankExcept_lt hc

/-- Cell labels from a tile list with blank at `b`. -/
def cellsOfTileList (b : Cell) (L : List ℕ) (hlen : L.length = 15) : Cell → ℕ :=
  fun c =>
    if h : c = b then 0
    else L[rankExcept b c]'(rankExcept_lt_tileList b L hlen c (ne_of_not_eq h))

lemma cellsOfTileList_eq (b : Cell) (L : List ℕ) (hlen : L.length = 15) (c : Cell) (hc : c ≠ b) :
    cellsOfTileList b L hlen c = L[rankExcept b c]'(rankExcept_lt_tileList b L hlen c hc) := by
  simp [cellsOfTileList, hc]

lemma cellsOfTileList_le (b : Cell) (L : List ℕ) (hs : TileListSpec b L) (c : Cell) :
    cellsOfTileList b L hs.length_eq c ≤ 15 := by
  simp only [cellsOfTileList]
  split_ifs with hcb
  · omega
  · exact (hs.mem_Icc _ (List.getElem_mem
        (rankExcept_lt_tileList b L hs.length_eq c (ne_of_not_eq hcb)))).2

lemma cellsOfTileList_blank (b : Cell) (L : List ℕ) (hlen : L.length = 15) :
    cellsOfTileList b L hlen b = 0 := by
  simp [cellsOfTileList]

lemma rankExcept_cellsRowMajorExcept (b : Cell) (j : ℕ) (hj : j < (cellsRowMajorExcept b).length) :
    rankExcept b ((cellsRowMajorExcept b)[j]'hj) = j := by
  set c := (cellsRowMajorExcept b)[j]'hj
  have hc := cellsRowMajorExcept_ne b c (List.getElem_mem hj)
  have hlt := rankExcept_lt hc
  exact (Nodup.getElem_inj_iff (cellsRowMajorExcept_nodup b) (hi := hlt) (hj := hj)).mp
    (rankExcept_getElem hc)

lemma existsUnique_cell_of_list_val (b : Cell) (L : List ℕ) (hs : TileListSpec b L)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 15) : ∃! c : Cell, cellsOfTileList b L hs.length_eq c = k := by
  have hkmem : k ∈ L :=
    mem_Icc_one_fifteen_of_nodup_len L hs.length_eq hs.nodup (fun x hx => hs.mem_Icc x hx) k hk.1 hk.2
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hkmem
  have hj' : j < 15 := by rw [hs.length_eq] at hj; omega
  let c := (cellsRowMajorExcept b)[j]'(by rw [cellsRowMajorExcept_length]; exact hj')
  refine ⟨c, ?_, ?_⟩
  · have hc := cellsRowMajorExcept_ne b c (List.getElem_mem (by rw [cellsRowMajorExcept_length]; omega))
    have hjcells : j < (cellsRowMajorExcept b).length := by rw [cellsRowMajorExcept_length]; omega
    calc cellsOfTileList b L hs.length_eq c
        _ = L[rankExcept b c]'(rankExcept_lt_tileList b L hs.length_eq c hc) :=
          cellsOfTileList_eq b L hs.length_eq c hc
        _ = L[j]'(by rw [hs.length_eq] at hj; omega) := by
          congr
          exact rankExcept_cellsRowMajorExcept b j hjcells
        _ = k := heq
  · intro c' h'
    have hc' : c' ≠ b := by
      intro hcb
      rw [hcb, cellsOfTileList_blank] at h'
      omega
    have hjcells : j < (cellsRowMajorExcept b).length := by rw [cellsRowMajorExcept_length]; omega
    have hrank : rankExcept b c' = j := by
      have hidx := rankExcept_lt_tileList b L hs.length_eq c' hc'
      have hjL : j < L.length := by rw [hs.length_eq] at hj; omega
      have heqL : L[rankExcept b c']'hidx = L[j]'hjL := by
        rw [← cellsOfTileList_eq b L hs.length_eq c' hc', h', heq]
      exact (Nodup.getElem_inj_iff hs.nodup (hi := hidx) (hj := hjL)).mp heqL
    have hcCell := cellsRowMajorExcept_ne b c (List.getElem_mem (by rw [cellsRowMajorExcept_length]; omega))
    exact rankExcept_injective hc' hcCell (hrank.trans (rankExcept_cellsRowMajorExcept b j hjcells).symm)

lemma cellsOfTileList_eq_zero_iff (b : Cell) (L : List ℕ) (hs : TileListSpec b L) (c : Cell) :
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
noncomputable def configOfTileList (b : Cell) (L : List ℕ) (hs : TileListSpec b L) : Config :=
  ⟨cellsOfTileList b L hs.length_eq,
    ⟨cellsOfTileList_le b L hs,
      ExistsUnique.intro b (cellsOfTileList_blank b L hs.length_eq) fun c h0 =>
        (cellsOfTileList_eq_zero_iff b L hs c).mp h0,
      fun k hk => existsUnique_cell_of_list_val b L hs k hk⟩⟩

lemma blank_configOfTileList (b : Cell) (L : List ℕ) (hs : TileListSpec b L) :
    blank (configOfTileList b L hs) = b := by
  exact (ExistsUnique.unique (configOfTileList b L hs).valid.2.1
    (cellsOfTileList_blank b L hs.length_eq) (blank_zero (configOfTileList b L hs))).symm

lemma map_cellsOfTileList_eq (b : Cell) (L : List ℕ) (hs : TileListSpec b L) :
    (cellsRowMajorExcept b).map (cellsOfTileList b L hs.length_eq) = L := by
  apply List.ext_get (by simp [cellsRowMajorExcept_length, hs.length_eq])
  intro i hi _hiL
  have hi' : i < (cellsRowMajorExcept b).length := by
    simpa [List.length_map, cellsRowMajorExcept_length] using hi
  let c := (cellsRowMajorExcept b)[i]'hi'
  have hc := cellsRowMajorExcept_ne b c (List.getElem_mem hi')
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]
  dsimp [cellsOfTileList]
  split_ifs with hcb
  · exact absurd hcb hc
  · congr 1
    exact rankExcept_cellsRowMajorExcept b i hi'

lemma tileList_configOfTileList (b : Cell) (L : List ℕ) (hs : TileListSpec b L) :
    tileList (configOfTileList b L hs) = L := by
  dsimp [tileList]
  rw [congrArg cellsRowMajorExcept (blank_configOfTileList b L hs)]
  exact map_cellsOfTileList_eq b L hs

lemma config_eq_configOfTileList (cfg : Config) (b : Cell) (L : List ℕ) (hb : blank cfg = b)
    (ht : tileList cfg = L) (hs : TileListSpec b L) :
    cfg = configOfTileList b L hs := by
  apply config_eq_of_tileList_and_blank cfg (configOfTileList b L hs)
  · rw [blank_configOfTileList b L hs, hb]
  · rw [tileList_configOfTileList b L hs, ht]

/-!
### `Equiv.Perm (Fin 15)` from a tile list at `bottomRight`
-/

/-- Goal label at list index `i` (1-based tile value minus 1). -/
noncomputable def tileLabelAt (L : List ℕ) (i : Fin 15) (hs : TileListSpec bottomRight L) : Fin 15 :=
  have hi : i.1 < L.length := by rw [hs.length_eq]; exact i.isLt
  have hmem := hs.mem_Icc _ (List.getElem_mem hi)
  ⟨(L[i]'hi) - 1, by
    rcases hmem with ⟨hlo, hhi⟩
    exact nat_sub_one_lt_fifteen hlo hhi⟩

lemma tileLabelAt_goal (i : Fin 15) : tileLabelAt (tileList goal) i tileListSpec_goal = i := by
  ext
  simp only [tileLabelAt, tileList, List.getElem_map, cellsRowMajorExcept_length,
    goalCells, bottomRight, blank_goal, tileListSpec_goal]
  fin_cases i <;>
    simp [rankExcept_bottomRight, goalCells, cellsRowMajorExcept, List.finRange, List.filter,
      List.findIdx, List.findIdx.go] <;> decide

lemma tileLabelAt_injective (L : List ℕ) (hs : TileListSpec bottomRight L) :
    Function.Injective (tileLabelAt L · hs) := by
  intro i j hij
  have hval := congrArg Fin.val hij
  simp only [tileLabelAt, Fin.mk.injEq] at hval
  have hi : i.1 < L.length := by rw [hs.length_eq]; exact i.isLt
  have hj : j.1 < L.length := by rw [hs.length_eq]; exact j.isLt
  have hlo_i := (hs.mem_Icc _ (List.getElem_mem hi)).1
  have hlo_j := (hs.mem_Icc _ (List.getElem_mem hj)).1
  have hL := Nat.pred_inj hlo_i hlo_j hval
  exact Fin.eq_of_val_eq ((hs.nodup.getElem_inj_iff (hi := hi) (hj := hj)).mp hL)

lemma tileLabelAt_surjective (L : List ℕ) (hs : TileListSpec bottomRight L) :
    Function.Surjective (tileLabelAt L · hs) := by
  intro k
  have hk : k.1 + 1 ∈ L := by
    simpa using
      mem_Icc_one_fifteen_of_nodup_len L hs.length_eq hs.nodup (fun x hx => hs.mem_Icc x hx)
        (k.1 + 1) (by omega) (by omega)
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hk
  refine ⟨⟨j, by rw [hs.length_eq] at hj; omega⟩, ?_⟩
  ext
  simp [tileLabelAt, heq, Fin.mk.injEq]

/-- Bijection `Fin 15 ≃ Fin 15` encoded by tile values in `L` (blank at `bottomRight`). -/
noncomputable def tileListPerm (L : List ℕ) (hs : TileListSpec bottomRight L) : Equiv.Perm (Fin 15) :=
  Equiv.ofBijective (tileLabelAt L · hs)
    ⟨tileLabelAt_injective L hs, tileLabelAt_surjective L hs⟩

lemma tileListPerm_goal : tileListPerm (tileList goal) tileListSpec_goal = 1 := by
  ext i
  simp [tileListPerm, tileLabelAt_goal]

lemma tileListPerm_apply (L : List ℕ) (hs : TileListSpec bottomRight L) (j : Fin 15) :
    tileListPerm L hs j = tileLabelAt L j hs := by
  simp [tileListPerm, Equiv.ofBijective_apply]

lemma tileList_eq_of_tileListPerm_eq (L L' : List ℕ) (hs : TileListSpec bottomRight L)
    (hs' : TileListSpec bottomRight L') (h : tileListPerm L hs = tileListPerm L' hs') : L = L' := by
  apply List.ext_get (by rw [hs.length_eq, hs'.length_eq])
  intro i hi _
  have hi15 : i < 15 := by rw [hs.length_eq] at hi; exact hi
  let j : Fin 15 := ⟨i, hi15⟩
  have hiL : i < L.length := by rwa [hs.length_eq]
  have hiL' : i < L'.length := by rwa [hs'.length_eq]
  have hlab : tileLabelAt L j hs = tileLabelAt L' j hs' := by
    rw [← tileListPerm_apply, h, tileListPerm_apply]
  have heq := congrArg Fin.val hlab
  simp only [tileLabelAt] at heq
  have hlo := (hs.mem_Icc _ (List.getElem_mem hiL)).1
  have hlo' := (hs'.mem_Icc _ (List.getElem_mem hiL')).1
  have hget : L[i]'hiL = L'[i]'hiL' := by
    have h1 := Nat.pred_inj hlo hlo' heq
    omega
  exact hget

/-- Vertical slide induces `List.Perm` on `tileList` (same `eraseIdx`/`insertIdx` model). -/
noncomputable def permOfCfg (cfg : Config) (hbr : blank cfg = bottomRight) : Equiv.Perm (Fin 15) :=
  tileListPerm (tileList cfg) (tileListSpec_of_config cfg bottomRight hbr)

lemma permOfCfg_goal : permOfCfg goal blank_goal = 1 := by
  simp [permOfCfg, tileListPerm_goal]

lemma tileList_perm_slide_vertical (cfg : Config) (n : Cell) (h : adjacent (blank cfg) n)
    (hc : sameCol (blank cfg) n) :
    (tileList (slide cfg n h)).Perm (tileList cfg) := by
  have hlt := rankExcept_vertical_lt (blank cfg) n h hc
  have hne : rankExcept (blank cfg) n ≠ rankExcept n (blank cfg) := by
    intro hpeq
    have hmod := rankExcept_vertical_mod (blank cfg) n h hc
    rw [hpeq] at hmod
    omega
  have hval := (tileList_get_rankExcept cfg n (adjacent.ne h.symm)).symm
  rw [tileList_slide_vertical cfg n h hc, hval]
  exact list_perm_erase_insert (tileList cfg) (rankExcept (blank cfg) n) (rankExcept n (blank cfg))
    (by simp [tileList, cellsRowMajorExcept_length]; exact hlt.1)
    (by simp [tileList, cellsRowMajorExcept_length]; exact hlt.2) hne

end NPuzzle.FourFour
