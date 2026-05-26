import NPuzzle.FourFour
import NPuzzle.FourFour.Invariant
import NPuzzle.FourFour.Inversion
import NPuzzle.FourFour.TileSorted

namespace NPuzzle.FourFour

open Inversion

private lemma getElem_list_eq {α} {xs ys : List α} (h : xs = ys) {i : Nat} (hi : i < xs.length) :
    xs[i]'hi = ys[i]'(h ▸ hi) := by subst h; rfl

private lemma getElem_same_list {α} {xs : List α} {i j : Nat} (hij : i = j)
    (hi : i < xs.length) (hj : j < xs.length) :
    xs[i]'hi = xs[j]'hj := by subst hij; rfl

/-- Equal `tileList` and equal blank position determine all cell labels. -/
lemma cells_eq_of_tileList {cfg cfg' : Config}
    (hb : blank cfg = blank cfg') (ht : tileList cfg = tileList cfg') :
    ∀ c, cfg.cells c = cfg'.cells c := by
  intro c
  by_cases hc : c = blank cfg
  · subst hc
    rw [blank_zero cfg, hb, blank_zero cfg']
  · have hi := tileList_get_rankExcept cfg c hc
    have hj := tileList_get_rankExcept cfg' c (hb ▸ hc)
    have hrank : rankExcept (blank cfg) c = rankExcept (blank cfg') c := by simp [hb]
    have hidx : rankExcept (blank cfg) c < (tileList cfg).length := by
      unfold tileList; rw [List.length_map]; exact rankExcept_lt hc
    have hidx' : rankExcept (blank cfg) c < (tileList cfg').length := by rwa [← ht]
    have hlink :=
      getElem_same_list hrank hidx' (by
        unfold tileList; rw [List.length_map]; exact rankExcept_lt (hb ▸ hc))
    exact hi.symm.trans ((getElem_list_eq ht hidx).trans (hlink.trans hj))

/-- Matching `tileList` and blank cell implies configuration equality. -/
lemma config_eq_of_tileList_and_blank (cfg cfg' : Config)
    (hb : blank cfg = blank cfg') (ht : tileList cfg = tileList cfg') : cfg = cfg' :=
  Config.ext (cells_eq_of_tileList hb ht)

/-- Once `tileList` matches `goal` and blank stays at `bottomRight`, the board is solved. -/
lemma reachable_goal_of_tileList (cfg : Config) (hbr : blank cfg = bottomRight)
    (ht : tileList cfg = tileList goal) : Reachable cfg goal := by
  have heq : cfg = goal := by
    apply config_eq_of_tileList_and_blank cfg goal
    · rw [hbr, blank_goal]
    · exact ht
  rw [heq]
  exact Relation.ReflTransGen.refl

lemma parityClass_blank_bottomRight (cfg : Config) (hbr : blank cfg = bottomRight) :
    parityClass cfg = (invStat cfg + 1) % 2 := by
  unfold parityClass
  rw [hbr, blankRow_bottomRight]

/-- With blank at bottom-right, `parityClass cfg = 1` means `invStat cfg` is even. -/
lemma invStat_even_of_parity_bottomRight (cfg : Config) (hbr : blank cfg = bottomRight)
    (hpar : parityClass cfg = 1) : invStat cfg % 2 = 0 := by
  rw [parityClass_blank_bottomRight cfg hbr] at hpar
  omega

/-- Labels in `tileList` lie in `1…15`. -/
lemma tileList_mem_Icc (cfg : Config) {x : ℕ} (hx : x ∈ tileList cfg) :
    1 ≤ x ∧ x ≤ 15 := by
  rw [tileList] at hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  have hne := cellsRowMajorExcept_ne (blank cfg) c hc
  have hpos : cfg.cells c ≠ 0 := by
    intro h0
    have : c = blank cfg :=
      (ExistsUnique.unique cfg.valid.2.1 (blank_zero cfg) h0).symm
    exact hne this
  have hlo : 1 ≤ cfg.cells c := by omega
  exact ⟨hlo, cfg.valid.1 c⟩

/-- `invStat = 0` implies the canonical sorted `tileList`. -/
lemma tileList_eq_goal_of_invStat_zero (cfg : Config) (h0 : invStat cfg = 0) :
    tileList cfg = tileList goal := by
  rw [tileList_goal]
  have hs := (inversionCount_eq_zero_iff_sorted (tileList cfg)).mp (by
    unfold invStat at h0
    simpa using h0)
  exact eq_range15_map_succ_of_sorted (tileList cfg)
    (by simp [tileList, cellsRowMajorExcept_length])
    (tileList_nodup cfg) hs fun x hx => tileList_mem_Icc cfg hx

/-- Already solved board (`invStat = 0`, blank at bottom-right). -/
lemma cfg_eq_goal_of_invStat_zero (cfg : Config) (hbr : blank cfg = bottomRight)
    (h0 : invStat cfg = 0) : cfg = goal := by
  apply config_eq_of_tileList_and_blank cfg goal
  · rw [hbr, blank_goal]
  · exact tileList_eq_goal_of_invStat_zero cfg h0

end NPuzzle.FourFour
