import NPuzzle.FourFour.TilePerm

set_option maxHeartbeats 1600000

namespace NPuzzle.FourFour

open Equiv Equiv.Perm

/-!
Relabel tile values by a permutation of `Fin 15`, keeping `0` as the blank.

This is a structural piece of the sufficiency proof: a legal slide sequence depends
only on blank positions, so uniformly relabeling all nonblank tiles transports
reachable paths and composes the induced `tileListPerm`.
-/

noncomputable def relabelVal (σ : Equiv.Perm (Fin 15)) (k : ℕ) : ℕ :=
  if h : 1 ≤ k ∧ k ≤ 15 then (σ ⟨k - 1, by omega⟩).val + 1 else 0

@[simp] lemma relabelVal_zero (σ : Equiv.Perm (Fin 15)) : relabelVal σ 0 = 0 := by
  simp [relabelVal]

lemma relabelVal_of_fin (σ : Equiv.Perm (Fin 15)) (i : Fin 15) :
    relabelVal σ (i.val + 1) = (σ i).val + 1 := by
  simp [relabelVal]

lemma relabelVal_le {σ : Equiv.Perm (Fin 15)} {k : ℕ} (hk : k ≤ 15) :
    relabelVal σ k ≤ 15 := by
  by_cases hpos : 1 ≤ k <;> simp [relabelVal, hpos, hk]

lemma relabelVal_eq_zero_iff {σ : Equiv.Perm (Fin 15)} {k : ℕ} (hk : k ≤ 15) :
    relabelVal σ k = 0 ↔ k = 0 := by
  constructor
  · intro h0
    by_cases hkpos : 1 ≤ k
    · have hpos : 1 ≤ relabelVal σ k := by
        simp [relabelVal, hkpos, hk]
      omega
    · omega
  · rintro rfl
    simp

lemma relabelVal_eq_iff_fin {σ : Equiv.Perm (Fin 15)} {a k : ℕ}
    (ha : 1 ≤ a ∧ a ≤ 15) (hk : 1 ≤ k ∧ k ≤ 15) :
    relabelVal σ a = k ↔ σ ⟨a - 1, by omega⟩ = (⟨k - 1, by omega⟩ : Fin 15) := by
  constructor
  · intro h
    apply Fin.ext
    change (σ ⟨a - 1, by omega⟩).val = k - 1
    have hsucc : (σ ⟨a - 1, by omega⟩).val + 1 = k := by
      simpa [relabelVal, ha] using h
    omega
  · intro h
    have hval : (σ ⟨a - 1, by omega⟩).val = k - 1 := congrArg Fin.val h
    simp [relabelVal, ha]
    omega

noncomputable def relabelCells (σ : Equiv.Perm (Fin 15)) (cells : Cell → ℕ) : Cell → ℕ :=
  fun c => relabelVal σ (cells c)

lemma relabel_valid (σ : Equiv.Perm (Fin 15)) {cells : Cell → ℕ} (hv : IsValid cells) :
    IsValid (relabelCells σ cells) := by
  rcases hv with ⟨hle, hblank, htiles⟩
  constructor
  · intro c
    exact relabelVal_le (σ := σ) (hle c)
  constructor
  · obtain ⟨b, hb, hbuniq⟩ := hblank
    refine ExistsUnique.intro b (by simp [relabelCells, hb]) ?_
    intro c hc
    apply hbuniq
    exact (relabelVal_eq_zero_iff (σ := σ) (hle c)).mp hc
  · intro k hk
    let target : Fin 15 := ⟨k - 1, by omega⟩
    let old : Fin 15 := σ.symm target
    have hold_bounds : 1 ≤ old.val + 1 ∧ old.val + 1 ≤ 15 := by omega
    obtain ⟨c, hc, hcuniq⟩ := htiles (old.val + 1) hold_bounds
    refine ExistsUnique.intro c ?_ ?_
    · have hso : σ old = target := by simp [old, target]
      have hval : (σ old).val + 1 = k := by
        rw [hso]
        simp [target]
        omega
      simpa [relabelCells, hc, relabelVal_of_fin] using hval
    · intro c2 hc2
      apply hcuniq
      have hc2_nonzero : cells c2 ≠ 0 := by
        intro h0
        rw [relabelCells, h0] at hc2
        simp at hc2
        omega
      have hc2_bounds : 1 ≤ cells c2 ∧ cells c2 ≤ 15 :=
        ⟨Nat.pos_of_ne_zero hc2_nonzero, hle c2⟩
      have hfin := (relabelVal_eq_iff_fin (σ := σ) hc2_bounds hk).mp hc2
      have hfin2 : ⟨cells c2 - 1, by omega⟩ = old := by
        apply_fun σ.symm at hfin
        simpa [old, target] using hfin
      have hval := congrArg Fin.val hfin2
      change cells c2 - 1 = old.val at hval
      omega

noncomputable def relabelConfig (σ : Equiv.Perm (Fin 15)) (cfg : Config) : Config :=
  ⟨relabelCells σ cfg.cells, relabel_valid σ cfg.valid⟩

lemma blank_relabelConfig (σ : Equiv.Perm (Fin 15)) (cfg : Config) :
    blank (relabelConfig σ cfg) = blank cfg := by
  apply ExistsUnique.unique (relabelConfig σ cfg).valid.2.1
  · exact blank_zero (relabelConfig σ cfg)
  · simp [relabelConfig, relabelCells, blank_zero cfg]

lemma relabelCells_swapAt (σ : Equiv.Perm (Fin 15)) (cells : Cell → ℕ) (a b : Cell) :
    relabelCells σ (swapAt cells a b) = swapAt (relabelCells σ cells) a b := by
  funext c
  simp only [relabelCells, swapAt]
  split_ifs <;> rfl

lemma relabel_slide (σ : Equiv.Perm (Fin 15)) (cfg : Config) (n : Cell)
    (h : adjacent (blank cfg) n) :
    relabelConfig σ (slide cfg n h) =
      slide (relabelConfig σ cfg) n (by rw [blank_relabelConfig σ cfg]; exact h) := by
  apply Config.ext
  intro c
  change relabelCells σ (swapAt cfg.cells (blank cfg) n) c =
    swapAt (relabelCells σ cfg.cells) (blank (relabelConfig σ cfg)) n c
  rw [blank_relabelConfig σ cfg]
  exact congrFun (relabelCells_swapAt σ cfg.cells (blank cfg) n) c

lemma legalStep_relabel (σ : Equiv.Perm (Fin 15)) {cfg cfg' : Config}
    (h : legalStep cfg cfg') : legalStep (relabelConfig σ cfg) (relabelConfig σ cfg') := by
  rcases h with ⟨n, h, rfl⟩
  refine ⟨n, by rw [blank_relabelConfig σ cfg]; exact h, ?_⟩
  exact relabel_slide σ cfg n h

lemma reachable_relabel (σ : Equiv.Perm (Fin 15)) {cfg cfg' : Config}
    (h : Reachable cfg cfg') : Reachable (relabelConfig σ cfg) (relabelConfig σ cfg') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single (legalStep_relabel σ hstep))

lemma tileList_relabel (σ : Equiv.Perm (Fin 15)) (cfg : Config) :
    tileList (relabelConfig σ cfg) = (tileList cfg).map (relabelVal σ) := by
  unfold tileList
  rw [blank_relabelConfig]
  simp [relabelConfig, relabelCells, List.map_map]

lemma tileLabelAt_relabel (σ : Equiv.Perm (Fin 15)) (L : List ℕ)
    (hs : TileListSpec bottomRight L) (hs' : TileListSpec bottomRight (L.map (relabelVal σ)))
    (i : Fin 15) :
    tileLabelAt (L.map (relabelVal σ)) i hs' = σ (tileLabelAt L i hs) := by
  apply Fin.ext
  have hi : i.1 < L.length := by rw [hs.length_eq]; exact i.isLt
  have himap : i.1 < (L.map (relabelVal σ)).length := by
    simpa [List.length_map] using hi
  have htile : (tileLabelAt L i hs).val = L[i.1]'hi - 1 := by
    rw [tileLabelAt]
    rfl
  have hbounds := hs.mem_Icc L[i.1] (List.getElem_mem hi)
  have hL : L[i.1]'hi = (tileLabelAt L i hs).val + 1 := by
    omega
  have hmap : (L.map (relabelVal σ))[i.1]'himap = relabelVal σ (L[i.1]'hi) := by
    simp [List.getElem_map]
  change (L.map (relabelVal σ))[i.1]'himap - 1 = (σ (tileLabelAt L i hs)).val
  rw [hmap, hL, relabelVal_of_fin]
  omega

lemma tileListPerm_relabel (σ : Equiv.Perm (Fin 15)) (L : List ℕ)
    (hs : TileListSpec bottomRight L) (hs' : TileListSpec bottomRight (L.map (relabelVal σ))) :
    tileListPerm (L.map (relabelVal σ)) hs' = σ * tileListPerm L hs := by
  apply Equiv.ext
  intro i
  rw [tileListPerm_apply]
  change tileLabelAt (L.map (relabelVal σ)) i hs' = σ (tileListPerm L hs i)
  rw [tileListPerm_apply]
  exact tileLabelAt_relabel σ L hs hs' i

private lemma tileListSpec_map_relabel (σ : Equiv.Perm (Fin 15)) (L : List ℕ)
    (hs : TileListSpec bottomRight L) : TileListSpec bottomRight (L.map (relabelVal σ)) where
  length_eq := by simp [hs.length_eq]
  nodup := by
    apply hs.nodup.map_on
    intro a ha b hb hab
    have habounds := hs.mem_Icc a ha
    have hbbounds := hs.mem_Icc b hb
    have haeq : relabelVal σ a = (σ (⟨a - 1, by omega⟩ : Fin 15)).val + 1 := by
      simp [relabelVal, habounds]
    have hbeq : relabelVal σ b = (σ (⟨b - 1, by omega⟩ : Fin 15)).val + 1 := by
      simp [relabelVal, hbbounds]
    rw [haeq, hbeq] at hab
    have hfin : σ (⟨a - 1, by omega⟩ : Fin 15) = σ (⟨b - 1, by omega⟩ : Fin 15) := by
      apply Fin.ext
      omega
    have holdfin := σ.injective hfin
    have hval := congrArg Fin.val holdfin
    change a - 1 = b - 1 at hval
    omega
  mem_Icc := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have habounds := hs.mem_Icc a ha
    constructor
    · by_cases hpos : 1 ≤ a
      · simp [relabelVal, hpos, habounds.2]
      · omega
    · exact relabelVal_le (σ := σ) habounds.2

lemma tileListPerm_congr {L L' : List ℕ} (h : L = L')
    (hs : TileListSpec bottomRight L) (hs' : TileListSpec bottomRight L') :
    tileListPerm L hs = tileListPerm L' hs' := by
  subst h
  congr

lemma permOfCfg_relabel (σ : Equiv.Perm (Fin 15)) (cfg : Config)
    (hbr : blank cfg = bottomRight) :
    permOfCfg (relabelConfig σ cfg) (by rw [blank_relabelConfig σ cfg, hbr]) =
      σ * permOfCfg cfg hbr := by
  unfold permOfCfg
  have ht := tileList_relabel σ cfg
  exact (tileListPerm_congr ht
    (tileListSpec_of_config (relabelConfig σ cfg) bottomRight
      (by rw [blank_relabelConfig σ cfg, hbr]))
    (tileListSpec_map_relabel σ (tileList cfg)
      (tileListSpec_of_config cfg bottomRight hbr))).trans
    (tileListPerm_relabel σ (tileList cfg)
      (tileListSpec_of_config cfg bottomRight hbr)
      (tileListSpec_map_relabel σ (tileList cfg)
        (tileListSpec_of_config cfg bottomRight hbr)))

end NPuzzle.FourFour
