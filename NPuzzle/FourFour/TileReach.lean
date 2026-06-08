import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.List
import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.GroupTheory.SpecificGroups.Alternating
import NPuzzle.FourFour
import NPuzzle.FourFour.Invariant
import NPuzzle.FourFour.TileGlue
import NPuzzle.FourFour.BlankReach
import NPuzzle.FourFour.TileInverse
import NPuzzle.FourFour.TileMacros
import NPuzzle.FourFour.TilePerm
import NPuzzle.FourFour.TileRelabel
import NPuzzle.FourFour.TileSign

set_option maxHeartbeats 1600000

namespace NPuzzle.FourFour

open Equiv Equiv.Perm Inversion List
open scoped Pointwise

/-- Sorted tile list with blank at `bottomRight`. -/
def goalTileList : List ℕ := (List.range 15).map (· + 1)

lemma goalTileList_eq : tileList goal = goalTileList :=
  tileList_goal

/-- List after the corner macro (`11↦12↦15↦11` on values at cells `10,11,14`). -/
def cornerTileList : List ℕ :=
  goalTileList.map fun x =>
    if x = 11 then 12 else if x = 12 then 15 else if x = 15 then 11 else x

lemma cornerTileList_length : cornerTileList.length = 15 := by
  simp [cornerTileList, goalTileList]

lemma cornerTileList_nodup : cornerTileList.Nodup := by
  native_decide

lemma cornerTileList_mem_Icc : ∀ x ∈ cornerTileList, 1 ≤ x ∧ x ≤ 15 := by
  intro x hx
  simp only [cornerTileList, goalTileList, List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  split_ifs <;> omega

lemma tileListSpec_corner : TileListSpec bottomRight cornerTileList where
  length_eq := cornerTileList_length
  nodup := cornerTileList_nodup
  mem_Icc := cornerTileList_mem_Icc

noncomputable def cornerCycleC1 : Config := slide goal cell14 adjacent_goal_blank_cell14

lemma blank_cornerCycleC1 : blank cornerCycleC1 = cell14 := by
  simp [cornerCycleC1, blank_slide]

noncomputable def cornerCycleC2 : Config :=
  slide cornerCycleC1 cell10 (by rw [blank_cornerCycleC1]; exact adjacent_cell14_cell10)

lemma blank_cornerCycleC2 : blank cornerCycleC2 = cell10 := by
  simp [cornerCycleC2, blank_slide]

noncomputable def cornerCycleC3 : Config :=
  slide cornerCycleC2 cell11 (by rw [blank_cornerCycleC2]; exact adjacent_cell10_cell11)

lemma blank_cornerCycleC3 : blank cornerCycleC3 = cell11 := by
  simp [cornerCycleC3, blank_slide]

/-- The bottom-right 2×2 macro from `goal`, returning the blank to `bottomRight`. -/
noncomputable def cornerCycleCfg : Config :=
  slide cornerCycleC3 bottomRight (by
    rw [blank_cornerCycleC3]
    exact adjacent_cell11_bottomRight)

lemma blank_cornerCycleCfg : blank cornerCycleCfg = bottomRight := by
  simp [cornerCycleCfg, blank_slide]

lemma cornerCycleCfg_cells : cornerCycleCfg.cells = cornerRotCells := by
  funext i
  rw [cornerCycleCfg, slide_cells, blank_cornerCycleC3]
  rw [cornerCycleC3, slide_cells, blank_cornerCycleC2]
  rw [cornerCycleC2, slide_cells, blank_cornerCycleC1]
  rw [cornerCycleC1, slide_cells, blank_goal]
  fin_cases i <;>
    simp [cornerRotCells, swapAt, goal, goalCells, cell10, cell11, cell14, bottomRight]

lemma tileList_cornerCycleCfg : tileList cornerCycleCfg = cornerTileList := by
  unfold tileList
  rw [blank_cornerCycleCfg, cornerCycleCfg_cells]
  native_decide

def finTile10 : Fin 15 := ⟨10, by omega⟩

def finTile11 : Fin 15 := ⟨11, by omega⟩

def finTile14 : Fin 15 := ⟨14, by omega⟩

/-- The 3-cycle induced by the bottom-right 2×2 macro. -/
noncomputable def cornerPerm : Equiv.Perm (Fin 15) :=
  List.formPerm [finTile10, finTile11, finTile14]

lemma tileListPerm_cornerTileList :
    tileListPerm cornerTileList tileListSpec_corner = cornerPerm := by
  apply Equiv.ext
  intro i
  rw [tileListPerm_apply]
  apply Fin.ext
  fin_cases i <;>
    simp [tileLabelAt, cornerTileList, goalTileList, cornerPerm, finTile10, finTile11, finTile14,
      List.formPerm, Equiv.swap_apply_def]

lemma permOfCfg_cornerCycleCfg :
    permOfCfg cornerCycleCfg blank_cornerCycleCfg = cornerPerm := by
  unfold permOfCfg
  exact (tileListPerm_congr tileList_cornerCycleCfg
    (tileListSpec_of_config cornerCycleCfg bottomRight blank_cornerCycleCfg)
    tileListSpec_corner).trans tileListPerm_cornerTileList

lemma reachable_cornerCycleCfg_from_goal : Reachable goal cornerCycleCfg := by
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step cornerCycleC3 bottomRight (by
    rw [blank_cornerCycleC3]
    exact adjacent_cell11_bottomRight))
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step cornerCycleC2 cell11 (by
    rw [blank_cornerCycleC2]
    exact adjacent_cell10_cell11))
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step cornerCycleC1 cell10 (by
    rw [blank_cornerCycleC1]
    exact adjacent_cell14_cell10))
  exact reachable_one_step goal cell14 adjacent_goal_blank_cell14

def cell0 : Cell := ⟨0, by omega⟩

def cell1 : Cell := ⟨1, by omega⟩

def cell2 : Cell := ⟨2, by omega⟩

def cell3 : Cell := ⟨3, by omega⟩

def cell4 : Cell := ⟨4, by omega⟩

def cell5 : Cell := ⟨5, by omega⟩

def cell6 : Cell := ⟨6, by omega⟩

def cell7 : Cell := ⟨7, by omega⟩

def cell8 : Cell := ⟨8, by omega⟩

def cell9 : Cell := ⟨9, by omega⟩

def cell12 : Cell := ⟨12, by omega⟩

def cell13 : Cell := ⟨13, by omega⟩

lemma adjacent_cell10_cell6 : adjacent cell10 cell6 := by
  unfold adjacent cell10 cell6 sameRow sameCol
  simp

lemma adjacent_cell6_cell5 : adjacent cell6 cell5 := by
  unfold adjacent cell6 cell5 sameRow sameCol
  simp

lemma adjacent_cell5_cell9 : adjacent cell5 cell9 := by
  unfold adjacent cell5 cell9 sameRow sameCol
  simp

lemma adjacent_cell9_cell13 : adjacent cell9 cell13 := by
  unfold adjacent cell9 cell13 sameRow sameCol
  simp

lemma adjacent_cell13_cell12 : adjacent cell13 cell12 := by
  unfold adjacent cell13 cell12 sameRow sameCol
  simp

lemma adjacent_cell12_cell8 : adjacent cell12 cell8 := by
  unfold adjacent cell12 cell8 sameRow sameCol
  simp

lemma adjacent_cell8_cell4 : adjacent cell8 cell4 := by
  unfold adjacent cell8 cell4 sameRow sameCol
  simp

lemma adjacent_cell4_cell0 : adjacent cell4 cell0 := by
  unfold adjacent cell4 cell0 sameRow sameCol
  simp

lemma adjacent_cell0_cell1 : adjacent cell0 cell1 := by
  unfold adjacent cell0 cell1 sameRow sameCol
  simp

lemma adjacent_cell1_cell2 : adjacent cell1 cell2 := by
  unfold adjacent cell1 cell2 sameRow sameCol
  simp

lemma adjacent_cell2_cell3 : adjacent cell2 cell3 := by
  unfold adjacent cell2 cell3 sameRow sameCol
  simp

lemma adjacent_cell3_cell7 : adjacent cell3 cell7 := by
  unfold adjacent cell3 cell7 sameRow sameCol
  simp

lemma adjacent_cell7_cell11 : adjacent cell7 cell11 := by
  unfold adjacent cell7 cell11 sameRow sameCol
  simp

noncomputable def hamC1 : Config := slide goal cell14 adjacent_goal_blank_cell14

lemma blank_hamC1 : blank hamC1 = cell14 := by
  simp [hamC1, blank_slide]

noncomputable def hamC2 : Config :=
  slide hamC1 cell10 (by rw [blank_hamC1]; exact adjacent_cell14_cell10)

lemma blank_hamC2 : blank hamC2 = cell10 := by
  simp [hamC2, blank_slide]

noncomputable def hamC3 : Config :=
  slide hamC2 cell6 (by rw [blank_hamC2]; exact adjacent_cell10_cell6)

lemma blank_hamC3 : blank hamC3 = cell6 := by
  simp [hamC3, blank_slide]

noncomputable def hamC4 : Config :=
  slide hamC3 cell5 (by rw [blank_hamC3]; exact adjacent_cell6_cell5)

lemma blank_hamC4 : blank hamC4 = cell5 := by
  simp [hamC4, blank_slide]

noncomputable def hamC5 : Config :=
  slide hamC4 cell9 (by rw [blank_hamC4]; exact adjacent_cell5_cell9)

lemma blank_hamC5 : blank hamC5 = cell9 := by
  simp [hamC5, blank_slide]

noncomputable def hamC6 : Config :=
  slide hamC5 cell13 (by rw [blank_hamC5]; exact adjacent_cell9_cell13)

lemma blank_hamC6 : blank hamC6 = cell13 := by
  simp [hamC6, blank_slide]

noncomputable def hamC7 : Config :=
  slide hamC6 cell12 (by rw [blank_hamC6]; exact adjacent_cell13_cell12)

lemma blank_hamC7 : blank hamC7 = cell12 := by
  simp [hamC7, blank_slide]

noncomputable def hamC8 : Config :=
  slide hamC7 cell8 (by rw [blank_hamC7]; exact adjacent_cell12_cell8)

lemma blank_hamC8 : blank hamC8 = cell8 := by
  simp [hamC8, blank_slide]

noncomputable def hamC9 : Config :=
  slide hamC8 cell4 (by rw [blank_hamC8]; exact adjacent_cell8_cell4)

lemma blank_hamC9 : blank hamC9 = cell4 := by
  simp [hamC9, blank_slide]

noncomputable def hamC10 : Config :=
  slide hamC9 cell0 (by rw [blank_hamC9]; exact adjacent_cell4_cell0)

lemma blank_hamC10 : blank hamC10 = cell0 := by
  simp [hamC10, blank_slide]

noncomputable def hamC11 : Config :=
  slide hamC10 cell1 (by rw [blank_hamC10]; exact adjacent_cell0_cell1)

lemma blank_hamC11 : blank hamC11 = cell1 := by
  simp [hamC11, blank_slide]

noncomputable def hamC12 : Config :=
  slide hamC11 cell2 (by rw [blank_hamC11]; exact adjacent_cell1_cell2)

lemma blank_hamC12 : blank hamC12 = cell2 := by
  simp [hamC12, blank_slide]

noncomputable def hamC13 : Config :=
  slide hamC12 cell3 (by rw [blank_hamC12]; exact adjacent_cell2_cell3)

lemma blank_hamC13 : blank hamC13 = cell3 := by
  simp [hamC13, blank_slide]

noncomputable def hamC14 : Config :=
  slide hamC13 cell7 (by rw [blank_hamC13]; exact adjacent_cell3_cell7)

lemma blank_hamC14 : blank hamC14 = cell7 := by
  simp [hamC14, blank_slide]

noncomputable def hamC15 : Config :=
  slide hamC14 cell11 (by rw [blank_hamC14]; exact adjacent_cell7_cell11)

lemma blank_hamC15 : blank hamC15 = cell11 := by
  simp [hamC15, blank_slide]

/-- A Hamiltonian blank circuit, returning to `bottomRight`. -/
noncomputable def hamCfg : Config :=
  slide hamC15 bottomRight (by rw [blank_hamC15]; exact adjacent_cell11_bottomRight)

lemma blank_hamCfg : blank hamCfg = bottomRight := by
  simp [hamCfg, blank_slide]

def hamCells (i : Cell) : ℕ :=
  if i = cell0 then 2
  else if i = cell1 then 3
  else if i = cell2 then 4
  else if i = cell3 then 8
  else if i = cell4 then 1
  else if i = cell5 then 10
  else if i = cell6 then 6
  else if i = cell7 then 12
  else if i = cell8 then 5
  else if i = cell9 then 14
  else if i = cell10 then 7
  else if i = cell11 then 15
  else if i = cell12 then 9
  else if i = cell13 then 13
  else if i = cell14 then 11
  else if i = bottomRight then 0
  else goalCells i

lemma hamCfg_cells : hamCfg.cells = hamCells := by
  funext i
  rw [hamCfg, slide_cells, blank_hamC15]
  rw [hamC15, slide_cells, blank_hamC14]
  rw [hamC14, slide_cells, blank_hamC13]
  rw [hamC13, slide_cells, blank_hamC12]
  rw [hamC12, slide_cells, blank_hamC11]
  rw [hamC11, slide_cells, blank_hamC10]
  rw [hamC10, slide_cells, blank_hamC9]
  rw [hamC9, slide_cells, blank_hamC8]
  rw [hamC8, slide_cells, blank_hamC7]
  rw [hamC7, slide_cells, blank_hamC6]
  rw [hamC6, slide_cells, blank_hamC5]
  rw [hamC5, slide_cells, blank_hamC4]
  rw [hamC4, slide_cells, blank_hamC3]
  rw [hamC3, slide_cells, blank_hamC2]
  rw [hamC2, slide_cells, blank_hamC1]
  rw [hamC1, slide_cells, blank_goal]
  fin_cases i <;>
    simp [hamCells, swapAt, goal, goalCells, cell0, cell1, cell2, cell3, cell4, cell5, cell6,
      cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, bottomRight]

def hamTileList : List ℕ := [2, 3, 4, 8, 1, 10, 6, 12, 5, 14, 7, 15, 9, 13, 11]

lemma hamTileList_length : hamTileList.length = 15 := by
  native_decide

lemma hamTileList_nodup : hamTileList.Nodup := by
  native_decide

lemma hamTileList_mem_Icc : ∀ x ∈ hamTileList, 1 ≤ x ∧ x ≤ 15 := by
  native_decide

lemma tileListSpec_ham : TileListSpec bottomRight hamTileList where
  length_eq := hamTileList_length
  nodup := hamTileList_nodup
  mem_Icc := hamTileList_mem_Icc

lemma tileList_hamCfg : tileList hamCfg = hamTileList := by
  unfold tileList
  rw [blank_hamCfg, hamCfg_cells]
  native_decide

def finTile0 : Fin 15 := ⟨0, by omega⟩

def finTile1 : Fin 15 := ⟨1, by omega⟩

def finTile2 : Fin 15 := ⟨2, by omega⟩

def finTile3 : Fin 15 := ⟨3, by omega⟩

def finTile4 : Fin 15 := ⟨4, by omega⟩

def finTile5 : Fin 15 := ⟨5, by omega⟩

def finTile6 : Fin 15 := ⟨6, by omega⟩

def finTile7 : Fin 15 := ⟨7, by omega⟩

def finTile8 : Fin 15 := ⟨8, by omega⟩

def finTile9 : Fin 15 := ⟨9, by omega⟩

def finTile12 : Fin 15 := ⟨12, by omega⟩

def finTile13 : Fin 15 := ⟨13, by omega⟩

/-- The tile permutation induced by the Hamiltonian blank circuit. -/
noncomputable def hamPerm : Equiv.Perm (Fin 15) :=
  List.formPerm [finTile0, finTile1, finTile2, finTile3, finTile7, finTile11, finTile14,
    finTile10, finTile6, finTile5, finTile9, finTile13, finTile12, finTile8, finTile4]

lemma tileListPerm_hamTileList : tileListPerm hamTileList tileListSpec_ham = hamPerm := by
  apply Equiv.ext
  intro i
  rw [tileListPerm_apply]
  apply Fin.ext
  fin_cases i <;>
    simp [tileLabelAt, hamTileList, hamPerm, finTile0, finTile1, finTile2, finTile3, finTile4,
      finTile5, finTile6, finTile7, finTile8, finTile9, finTile10, finTile11, finTile12,
      finTile13, finTile14, List.formPerm, Equiv.swap_apply_def]

lemma permOfCfg_hamCfg : permOfCfg hamCfg blank_hamCfg = hamPerm := by
  unfold permOfCfg
  exact (tileListPerm_congr tileList_hamCfg
    (tileListSpec_of_config hamCfg bottomRight blank_hamCfg)
    tileListSpec_ham).trans tileListPerm_hamTileList

lemma reachable_hamCfg_from_goal : Reachable goal hamCfg := by
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step hamC15 bottomRight (by
    rw [blank_hamC15]
    exact adjacent_cell11_bottomRight))
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step hamC14 cell11 (by
    rw [blank_hamC14]
    exact adjacent_cell7_cell11))
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step hamC13 cell7 (by
    rw [blank_hamC13]
    exact adjacent_cell3_cell7))
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step hamC12 cell3 (by
    rw [blank_hamC12]
    exact adjacent_cell2_cell3))
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step hamC11 cell2 (by
    rw [blank_hamC11]
    exact adjacent_cell1_cell2))
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step hamC10 cell1 (by
    rw [blank_hamC10]
    exact adjacent_cell0_cell1))
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step hamC9 cell0 (by
    rw [blank_hamC9]
    exact adjacent_cell4_cell0))
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step hamC8 cell4 (by
    rw [blank_hamC8]
    exact adjacent_cell8_cell4))
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step hamC7 cell8 (by
    rw [blank_hamC7]
    exact adjacent_cell12_cell8))
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step hamC6 cell12 (by
    rw [blank_hamC6]
    exact adjacent_cell13_cell12))
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step hamC5 cell13 (by
    rw [blank_hamC5]
    exact adjacent_cell9_cell13))
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step hamC4 cell9 (by
    rw [blank_hamC4]
    exact adjacent_cell5_cell9))
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step hamC3 cell5 (by
    rw [blank_hamC3]
    exact adjacent_cell6_cell5))
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step hamC2 cell6 (by
    rw [blank_hamC2]
    exact adjacent_cell10_cell6))
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step hamC1 cell10 (by
    rw [blank_hamC1]
    exact adjacent_cell14_cell10))
  exact reachable_one_step goal cell14 adjacent_goal_blank_cell14

lemma cornerPerm_isThreeCycle : IsThreeCycle cornerPerm := by
  rw [← card_support_eq_three_iff]
  rw [cornerPerm, List.support_formPerm_of_nodup]
  · native_decide
  · simp [finTile10, finTile11, finTile14]
  · intro x h
    simp at h

lemma hamPerm_isCycle : IsCycle hamPerm := by
  rw [hamPerm]
  apply List.isCycle_formPerm
  · simp [finTile0, finTile1, finTile2, finTile3, finTile4, finTile5, finTile6, finTile7,
      finTile8, finTile9, finTile10, finTile11, finTile12, finTile13, finTile14]
  · simp

lemma hamPerm_support_univ : hamPerm.support = Finset.univ := by
  rw [hamPerm, List.support_formPerm_of_nodup]
  · ext i
    fin_cases i <;>
      simp [finTile0, finTile1, finTile2, finTile3, finTile4, finTile5, finTile6, finTile7,
        finTile8, finTile9, finTile10, finTile11, finTile12, finTile13, finTile14]
  · simp [finTile0, finTile1, finTile2, finTile3, finTile4, finTile5, finTile6, finTile7,
      finTile8, finTile9, finTile10, finTile11, finTile12, finTile13, finTile14]
  · intro x h
    simp at h

def hamCycle : List (Fin 15) :=
  [finTile0, finTile1, finTile2, finTile3, finTile7, finTile11, finTile14,
    finTile10, finTile6, finTile5, finTile9, finTile13, finTile12, finTile8, finTile4]

lemma hamCycle_nodup : hamCycle.Nodup := by
  native_decide

lemma hamCycle_length : hamCycle.length = 15 := by
  native_decide

lemma hamPerm_pow_apply_hamCycle (n i : ℕ) (hi : i < hamCycle.length) :
    (hamPerm ^ n) hamCycle[i] =
      hamCycle[(i + n) % hamCycle.length]'(Nat.mod_lt _ (by
        rw [hamCycle_length]
        norm_num)) := by
  simpa [hamPerm, hamCycle] using
    List.formPerm_pow_apply_getElem hamCycle hamCycle_nodup n i hi

lemma hamPerm_apply_finTile14 : hamPerm finTile14 = finTile10 := by
  have h := hamPerm_pow_apply_hamCycle 1 6 (by native_decide)
  simpa [hamCycle] using h

lemma cornerPerm_apply_finTile10 : cornerPerm finTile10 = finTile11 := by
  simp [cornerPerm, finTile10, finTile11, finTile14, List.formPerm]
  decide

lemma cornerPerm_apply_finTile11 : cornerPerm finTile11 = finTile14 := by
  simp [cornerPerm, finTile10, finTile11, finTile14, List.formPerm]
  decide

lemma cornerPerm_apply_finTile14 : cornerPerm finTile14 = finTile10 := by
  simp [cornerPerm, finTile10, finTile11, finTile14, List.formPerm]

/-- Corner macro from any configuration with blank at `bottomRight`. -/
noncomputable def cornerRotAt (cfg : Config) (hbr : blank cfg = bottomRight) : Config :=
  let h14 : adjacent (blank cfg) cell14 := by rw [hbr]; exact adjacent_bottomRight_cell14
  let c1 := slide cfg cell14 h14
  let h10 : adjacent (blank c1) cell10 := by
    rw [blank_slide cfg cell14 h14]
    exact adjacent_cell14_cell10
  let c2 := slide c1 cell10 h10
  let h11 : adjacent (blank c2) cell11 := by
    rw [blank_slide c1 cell10 h10]
    exact adjacent_cell10_cell11
  let c3 := slide c2 cell11 h11
  let h15 : adjacent (blank c3) bottomRight := by
    rw [blank_slide c2 cell11 h11]
    exact adjacent_cell11_bottomRight
  slide c3 bottomRight h15

lemma blank_cornerRotAt (cfg : Config) (hbr : blank cfg = bottomRight) :
    blank (cornerRotAt cfg hbr) = bottomRight := by
  simp [cornerRotAt, blank_slide]

lemma reachable_cornerRotAt (cfg : Config) (hbr : blank cfg = bottomRight) :
    Reachable cfg (cornerRotAt cfg hbr) := by
  let h14 : adjacent (blank cfg) cell14 := by rw [hbr]; exact adjacent_bottomRight_cell14
  let c1 := slide cfg cell14 h14
  let h10 : adjacent (blank c1) cell10 := by
    rw [blank_slide cfg cell14 h14]
    exact adjacent_cell14_cell10
  let c2 := slide c1 cell10 h10
  let h11 : adjacent (blank c2) cell11 := by
    rw [blank_slide c1 cell10 h10]
    exact adjacent_cell10_cell11
  let c3 := slide c2 cell11 h11
  let h15 : adjacent (blank c3) bottomRight := by
    rw [blank_slide c2 cell11 h11]
    exact adjacent_cell11_bottomRight
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step c3 bottomRight h15)
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step c2 cell11 h11)
  refine Relation.ReflTransGen.trans ?_ (reachable_one_step c1 cell10 h10)
  exact reachable_one_step cfg cell14 h14

/-- A permutation of tiles is realized by a reachable configuration (blank at `bottomRight`). -/
def PermRealizable (σ : Equiv.Perm (Fin 15)) : Prop :=
  ∃ (cfg : Config) (hbr : blank cfg = bottomRight), Reachable goal cfg ∧ permOfCfg cfg hbr = σ

lemma permRealizable_one : PermRealizable 1 :=
  ⟨goal, blank_goal, Relation.ReflTransGen.refl, permOfCfg_goal⟩

lemma cornerPerm_realizable : PermRealizable cornerPerm :=
  ⟨cornerCycleCfg, blank_cornerCycleCfg, reachable_cornerCycleCfg_from_goal,
    permOfCfg_cornerCycleCfg⟩

lemma hamPerm_realizable : PermRealizable hamPerm :=
  ⟨hamCfg, blank_hamCfg, reachable_hamCfg_from_goal, permOfCfg_hamCfg⟩

lemma relabelConfig_goal_eq_of_perm {σ : Equiv.Perm (Fin 15)} {cfg : Config}
    (hbr : blank cfg = bottomRight) (hperm : permOfCfg cfg hbr = σ) :
    relabelConfig σ goal = cfg := by
  apply config_eq_of_tileList_and_blank
  · rw [blank_relabelConfig, blank_goal, hbr]
  · apply tileList_eq_of_tileListPerm_eq
      (tileList (relabelConfig σ goal)) (tileList cfg)
      (tileListSpec_of_config (relabelConfig σ goal) bottomRight (by
        rw [blank_relabelConfig σ goal]
        exact blank_goal))
      (tileListSpec_of_config cfg bottomRight hbr)
    have hbrGoalRelabel : blank (relabelConfig σ goal) = bottomRight := by
      rw [blank_relabelConfig σ goal]
      exact blank_goal
    have hgoalperm : permOfCfg (relabelConfig σ goal) hbrGoalRelabel = σ := by
      have h := permOfCfg_relabel σ goal blank_goal
      simpa [hbrGoalRelabel, permOfCfg_goal] using h
    have hsame : permOfCfg (relabelConfig σ goal) hbrGoalRelabel = permOfCfg cfg hbr := by
      rw [hgoalperm, hperm]
    simpa [permOfCfg] using hsame

lemma relabelConfig_perm_eq_goal {σ : Equiv.Perm (Fin 15)} {cfg : Config}
    (hbr : blank cfg = bottomRight) (hperm : permOfCfg cfg hbr = σ) :
    relabelConfig σ⁻¹ cfg = goal := by
  apply config_eq_of_tileList_and_blank
  · rw [blank_relabelConfig, hbr, blank_goal]
  · apply tileList_eq_of_tileListPerm_eq
      (tileList (relabelConfig σ⁻¹ cfg)) (tileList goal)
      (tileListSpec_of_config (relabelConfig σ⁻¹ cfg) bottomRight (by
        rw [blank_relabelConfig σ⁻¹ cfg]
        exact hbr))
      (tileListSpec_of_config goal bottomRight blank_goal)
    have hbrRelabel : blank (relabelConfig σ⁻¹ cfg) = bottomRight := by
      rw [blank_relabelConfig σ⁻¹ cfg]
      exact hbr
    have hrel : permOfCfg (relabelConfig σ⁻¹ cfg) hbrRelabel = 1 := by
      have h := permOfCfg_relabel σ⁻¹ cfg hbr
      simpa [hbrRelabel, hperm] using h
    have hsame : permOfCfg (relabelConfig σ⁻¹ cfg) hbrRelabel = permOfCfg goal blank_goal := by
      rw [hrel, permOfCfg_goal]
    simpa [permOfCfg] using hsame

lemma permRealizable_mul {σ τ : Equiv.Perm (Fin 15)}
    (hσ : PermRealizable σ) (hτ : PermRealizable τ) : PermRealizable (σ * τ) := by
  obtain ⟨cfgσ, hbrσ, hreachσ, hpermσ⟩ := hσ
  obtain ⟨cfgτ, hbrτ, hreachτ, hpermτ⟩ := hτ
  refine ⟨relabelConfig σ cfgτ, by rw [blank_relabelConfig σ cfgτ]; exact hbrτ, ?_, ?_⟩
  · have hstart : relabelConfig σ goal = cfgσ :=
      relabelConfig_goal_eq_of_perm hbrσ hpermσ
    have hreach_start : Reachable goal (relabelConfig σ goal) := by
      rwa [hstart]
    exact Relation.ReflTransGen.trans hreach_start (reachable_relabel σ hreachτ)
  · have h := permOfCfg_relabel σ cfgτ hbrτ
    simpa [hpermτ] using h

lemma permRealizable_inv {σ : Equiv.Perm (Fin 15)}
    (hσ : PermRealizable σ) : PermRealizable σ⁻¹ := by
  obtain ⟨cfg, hbr, hreach, hperm⟩ := hσ
  refine ⟨relabelConfig σ⁻¹ goal, by
    rw [blank_relabelConfig σ⁻¹ goal]
    exact blank_goal, ?_, ?_⟩
  · have hgoal : relabelConfig σ⁻¹ cfg = goal := relabelConfig_perm_eq_goal hbr hperm
    have hrelReach : Reachable (relabelConfig σ⁻¹ goal) (relabelConfig σ⁻¹ cfg) :=
      reachable_relabel σ⁻¹ hreach
    rw [hgoal] at hrelReach
    exact reachable_symm hrelReach
  · have h := permOfCfg_relabel σ⁻¹ goal blank_goal
    simpa [permOfCfg_goal] using h

def permRealizableSubgroup : Subgroup (Equiv.Perm (Fin 15)) where
  carrier := {σ | PermRealizable σ}
  one_mem' := permRealizable_one
  mul_mem' := by
    intro σ τ hσ hτ
    exact permRealizable_mul hσ hτ
  inv_mem' := by
    intro σ hσ
    exact permRealizable_inv hσ

lemma closure_corner_ham_le_realizable :
    Subgroup.closure ({cornerPerm, hamPerm} : Set (Equiv.Perm (Fin 15))) ≤
      permRealizableSubgroup := by
  rw [Subgroup.closure_le]
  intro σ hσ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
  rcases hσ with rfl | rfl
  · exact cornerPerm_realizable
  · exact hamPerm_realizable

lemma permRealizable_of_mem_corner_ham_closure {σ : Equiv.Perm (Fin 15)}
    (hσ : σ ∈ Subgroup.closure ({cornerPerm, hamPerm} : Set (Equiv.Perm (Fin 15)))) :
    PermRealizable σ :=
  closure_corner_ham_le_realizable hσ

def generatorSubgroup : Subgroup (Equiv.Perm (Fin 15)) :=
  Subgroup.closure ({cornerPerm, hamPerm} : Set (Equiv.Perm (Fin 15)))

lemma cornerPerm_mem_generatorSubgroup : cornerPerm ∈ generatorSubgroup := by
  apply Subgroup.subset_closure
  simp

lemma hamPerm_mem_generatorSubgroup : hamPerm ∈ generatorSubgroup := by
  apply Subgroup.subset_closure
  simp

noncomputable def genHamPow (k : ℕ) : generatorSubgroup :=
  ⟨hamPerm ^ k, Subgroup.pow_mem generatorSubgroup hamPerm_mem_generatorSubgroup k⟩

noncomputable def genCorner : generatorSubgroup :=
  ⟨cornerPerm, cornerPerm_mem_generatorSubgroup⟩

lemma block_apply_mem_of_maps_mem {B : Set (Fin 15)}
    (hB : MulAction.IsBlock generatorSubgroup B) {g : generatorSubgroup} {x z : Fin 15}
    (hx : x ∈ B) (hgx : (g : Equiv.Perm (Fin 15)) x ∈ B) (hz : z ∈ B) :
    (g : Equiv.Perm (Fin 15)) z ∈ B := by
  have hgx' : g • x ∈ B := by
    simpa [Equiv.Perm.smul_def] using hgx
  have hEq : g • B = B := hB.smul_eq_of_mem hx hgx'
  have hzimg : g • z ∈ g • B := Set.smul_mem_smul_set hz
  rw [hEq] at hzimg
  simpa [Equiv.Perm.smul_def] using hzimg

lemma block_pow_apply_mem_of_maps_mem {B : Set (Fin 15)}
    (hB : MulAction.IsBlock generatorSubgroup B) {g : generatorSubgroup} {x : Fin 15}
    (hx : x ∈ B) (hgx : (g : Equiv.Perm (Fin 15)) x ∈ B) (n : ℕ) :
    ((g : Equiv.Perm (Fin 15)) ^ n) x ∈ B := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      have hnext := block_apply_mem_of_maps_mem hB hx hgx ih
      simpa [pow_succ'] using hnext

lemma block_eq_univ_of_cycle_maps_mem {B : Set (Fin 15)}
    (hB : MulAction.IsBlock generatorSubgroup B) {g : generatorSubgroup} {x : Fin 15}
    (hcycle : IsCycle (g : Equiv.Perm (Fin 15)))
    (hsupp : (g : Equiv.Perm (Fin 15)).support = Finset.univ)
    (hx : x ∈ B) (hgx : (g : Equiv.Perm (Fin 15)) x ∈ B) : B = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  have hxSupp : (g : Equiv.Perm (Fin 15)) x ≠ x := by
    rw [← mem_support, hsupp]
    exact Finset.mem_univ x
  have hySupp : (g : Equiv.Perm (Fin 15)) y ≠ y := by
    rw [← mem_support, hsupp]
    exact Finset.mem_univ y
  obtain ⟨n, hn⟩ := hcycle.exists_pow_eq hxSupp hySupp
  have hmem := block_pow_apply_mem_of_maps_mem hB hx hgx n
  rwa [hn] at hmem

lemma block_eq_univ_of_corner_maps_mem {B : Set (Fin 15)}
    (hB : MulAction.IsBlock generatorSubgroup B) (h10 : finTile10 ∈ B) {x : Fin 15}
    (hx : x ∈ B) (hcx : cornerPerm x ∈ B) : B = Set.univ := by
  have hcx' : (genCorner : Equiv.Perm (Fin 15)) x ∈ B := by
    simpa [genCorner] using hcx
  have h11' := block_apply_mem_of_maps_mem hB hx hcx' h10
  have h11 : finTile11 ∈ B := by
    simpa [genCorner, cornerPerm_apply_finTile10] using h11'
  have h14' := block_apply_mem_of_maps_mem hB hx hcx' h11
  have h14 : finTile14 ∈ B := by
    simpa [genCorner, cornerPerm_apply_finTile11] using h14'
  have hham : (genHamPow 1 : Equiv.Perm (Fin 15)) finTile14 ∈ B := by
    simpa [genHamPow, hamPerm_apply_finTile14] using h10
  exact block_eq_univ_of_cycle_maps_mem hB (g := genHamPow 1) (x := finTile14)
    (by simpa [genHamPow] using hamPerm_isCycle)
    (by simpa [genHamPow] using hamPerm_support_univ)
    h14 hham

lemma generatorSubgroup_isPretransitive :
    MulAction.IsPretransitive generatorSubgroup (Fin 15) := by
  rw [MulAction.isPretransitive_iff_base finTile10]
  intro y
  have hxSupp : hamPerm finTile10 ≠ finTile10 := by
    rw [← mem_support, hamPerm_support_univ]
    exact Finset.mem_univ finTile10
  have hySupp : hamPerm y ≠ y := by
    rw [← mem_support, hamPerm_support_univ]
    exact Finset.mem_univ y
  obtain ⟨n, hn⟩ := hamPerm_isCycle.exists_pow_eq hxSupp hySupp
  exact ⟨⟨hamPerm ^ n, Subgroup.pow_mem generatorSubgroup hamPerm_mem_generatorSubgroup n⟩, hn⟩

lemma generatorSubgroup_isPreprimitive :
    MulAction.IsPreprimitive generatorSubgroup (Fin 15) := by
  haveI : MulAction.IsPretransitive generatorSubgroup (Fin 15) :=
    generatorSubgroup_isPretransitive
  apply MulAction.IsPreprimitive.of_isTrivialBlock_base finTile10
  intro B h10 hB
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  · right
    obtain ⟨x, hx, hxne⟩ : ∃ x ∈ B, x ≠ finTile10 := by
      by_contra hno
      apply hsub
      intro y hy z hz
      have hy10 : y = finTile10 := by
        by_contra hyne
        exact hno ⟨y, hy, hyne⟩
      have hz10 : z = finTile10 := by
        by_contra hzne
        exact hno ⟨z, hz, hzne⟩
      rw [hy10, hz10]
    fin_cases x
    · exact block_eq_univ_of_corner_maps_mem hB h10 hx (by
        simpa [cornerPerm, finTile0, finTile10, finTile11, finTile14, List.formPerm] using hx)
    · exact block_eq_univ_of_corner_maps_mem hB h10 hx (by
        simpa [cornerPerm, finTile1, finTile10, finTile11, finTile14, List.formPerm] using hx)
    · exact block_eq_univ_of_corner_maps_mem hB h10 hx (by
        simpa [cornerPerm, finTile2, finTile10, finTile11, finTile14, List.formPerm] using hx)
    · exact block_eq_univ_of_corner_maps_mem hB h10 hx (by
        simpa [cornerPerm, finTile3, finTile10, finTile11, finTile14, List.formPerm] using hx)
    · exact block_eq_univ_of_corner_maps_mem hB h10 hx (by
        simpa [cornerPerm, finTile4, finTile10, finTile11, finTile14, List.formPerm] using hx)
    · exact block_eq_univ_of_corner_maps_mem hB h10 hx (by
        simpa [cornerPerm, finTile5, finTile10, finTile11, finTile14, List.formPerm] using hx)
    · exact block_eq_univ_of_corner_maps_mem hB h10 hx (by
        simpa [cornerPerm, finTile6, finTile10, finTile11, finTile14, List.formPerm] using hx)
    · exact block_eq_univ_of_corner_maps_mem hB h10 hx (by
        simpa [cornerPerm, finTile7, finTile10, finTile11, finTile14, List.formPerm] using hx)
    · exact block_eq_univ_of_corner_maps_mem hB h10 hx (by
        simpa [cornerPerm, finTile8, finTile10, finTile11, finTile14, List.formPerm] using hx)
    · exact block_eq_univ_of_corner_maps_mem hB h10 hx (by
        simpa [cornerPerm, finTile9, finTile10, finTile11, finTile14, List.formPerm] using hx)
    · exact (hxne rfl).elim
    · exact block_eq_univ_of_corner_maps_mem hB h10 h10 (by
        simpa [cornerPerm_apply_finTile10] using hx)
    · exact block_eq_univ_of_corner_maps_mem hB h10 hx (by
        simpa [cornerPerm, finTile12, finTile10, finTile11, finTile14, List.formPerm] using hx)
    · exact block_eq_univ_of_corner_maps_mem hB h10 hx (by
        simpa [cornerPerm, finTile13, finTile10, finTile11, finTile14, List.formPerm] using hx)
    · exact block_eq_univ_of_corner_maps_mem hB h10 hx (by
        simpa [cornerPerm_apply_finTile14] using h10)

lemma alternatingGroup_le_generatorSubgroup_of_isPreprimitive
    (hprim : MulAction.IsPreprimitive generatorSubgroup (Fin 15)) :
    alternatingGroup (Fin 15) ≤ generatorSubgroup := by
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim
    cornerPerm_isThreeCycle cornerPerm_mem_generatorSubgroup

lemma alternatingGroup_le_generatorSubgroup :
    alternatingGroup (Fin 15) ≤ generatorSubgroup :=
  alternatingGroup_le_generatorSubgroup_of_isPreprimitive generatorSubgroup_isPreprimitive

/-- Every even permutation is realized from `goal` (classical 15-puzzle group). -/
lemma permRealizable_of_mem_alternating {σ : Equiv.Perm (Fin 15)}
    (hσ : σ ∈ alternatingGroup (Fin 15)) : PermRealizable σ := by
  exact permRealizable_of_mem_corner_ham_closure (alternatingGroup_le_generatorSubgroup hσ)

/-- From `goal`, reach any even-parity configuration with blank at `bottomRight`. -/
lemma reachable_goal_to_cfg_bottomRight (cfg : Config) (hbr : blank cfg = bottomRight)
    (heven : invStat cfg % 2 = 0) : Reachable goal cfg := by
  by_cases h0 : invStat cfg = 0
  · rw [cfg_eq_goal_of_invStat_zero cfg hbr h0]
    exact Relation.ReflTransGen.refl
  · have hσ := (invStat_even_iff_perm_alternating cfg hbr).mp heven
    obtain ⟨cfg', hbr', hreach, hperm⟩ := permRealizable_of_mem_alternating hσ
    have hcfg : cfg = cfg' := by
      apply config_eq_of_tileList_and_blank cfg cfg'
      · rw [hbr, hbr']
      · exact tileList_eq_of_tileListPerm_eq _ _
          (tileListSpec_of_config cfg bottomRight hbr)
          (tileListSpec_of_config cfg' bottomRight hbr')
          (by simpa [permOfCfg] using hperm.symm)
    rw [hcfg]
    exact hreach

end NPuzzle.FourFour
