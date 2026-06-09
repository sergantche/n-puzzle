import Mathlib.Data.Nat.Dist
import NPuzzle.Rect.Parity

namespace NPuzzle.Rect

/-!
Arithmetic shell for rectangular parity invariance.

The hard remaining work is list-level: horizontal slides preserve inversion
parity, and vertical slides change it by `B.cols + 1` modulo `2`.  This file
proves that those two facts are exactly enough to make the README parity
statistic invariant under legal moves.
-/

lemma add_mod_two_congr {a b c d : ℕ} (hab : a % 2 = b % 2) (hcd : c % 2 = d % 2) :
    (a + c) % 2 = (b + d) % 2 := by
  omega

lemma adjacent_component {B : Board} {a b : Cell B} (h : adjacent a b) :
    sameRow a b ∨ sameCol a b := by
  rcases h with (⟨hr, _⟩ | ⟨hc, _⟩)
  · exact Or.inl hr
  · exact Or.inr hc

lemma sameRow_symm {B : Board} {a b : Cell B} (h : sameRow a b) : sameRow b a :=
  h.symm

lemma sameCol_symm {B : Board} {a b : Cell B} (h : sameCol a b) : sameCol b a :=
  h.symm

lemma blankRowFromBottom_eq_sameRow {B : Board} {a b : Cell B} (h : sameRow a b) :
    blankRowFromBottom a = blankRowFromBottom b := by
  unfold sameRow at h
  unfold blankRowFromBottom
  rw [h]

lemma blankRow_adjacent_vertical_mod {B : Board} {a b : Cell B}
    (h : adjacent a b) (hc : sameCol a b) :
    blankRowFromBottom b % 2 = (blankRowFromBottom a + 1) % 2 := by
  rcases h with (⟨hr, hstep⟩ | ⟨_, hstep⟩)
  · have hrow : a.1.val = b.1.val := congrArg Fin.val hr
    have hcol : a.2.val = b.2.val := congrArg Fin.val hc
    rcases hstep with hstep | hstep <;> omega
  · unfold blankRowFromBottom
    rcases hstep with hstep | hstep <;> omega

lemma list_set_getElem_eq_self {α : Type} (L : List α) (p : ℕ) (hp : p < L.length) :
    L.set p (L[p]'hp) = L := by
  apply List.ext_getElem
  · simp
  · intro i hi hset
    rw [List.getElem_set]
    split_ifs with hpi
    · subst hpi
      rfl
    · rfl

lemma tileList_slide_eq_erase_insert {B : Board}
    (cfg : Config B) (n : Cell B) (h : adjacent (blank cfg) n) :
    tileList (slide cfg n h) =
      let L := tileList cfg
      let p := rankExcept (blank cfg) n
      let q := rankExcept n (blank cfg)
      (L.eraseIdx p).insertIdx q (cfg.cells n) := by
  unfold tileList
  rw [blank_slide cfg n h]
  dsimp [slide]
  unfold cellsRowMajorExcept rankExcept
  change ((cellsRowMajor B).erase n).map (swapAt cfg.cells (blank cfg) n) =
    ((((cellsRowMajor B).erase (blank cfg)).map cfg.cells).eraseIdx
        (((cellsRowMajor B).erase (blank cfg)).idxOf n)).insertIdx
      (((cellsRowMajor B).erase n).idxOf (blank cfg)) (cfg.cells n)
  simpa [swapAt, NPuzzle.List.swapValues] using
    NPuzzle.List.map_erase_swap_eq_move cfg.cells (cellsRowMajor B)
      (a := blank cfg) (b := n)
      (cellsRowMajor_nodup B)
      (mem_cellsRowMajor (blank cfg))
      (mem_cellsRowMajor n)
      (adjacent_ne h)

lemma rankExcept_adjacent_horizontal_eq {B : Board} {a b : Cell B}
    (h : adjacent a b) (hr : sameRow a b) :
    rankExcept a b = rankExcept b a := by
  rcases h with (⟨_, hstep⟩ | ⟨hc, hstep⟩)
  · have hrow : a.1.val = b.1.val := congrArg Fin.val hr
    rcases hstep with hstep | hstep
    · have hidx : index a < index b := by
        unfold index
        rw [hrow]
        omega
      rw [rankExcept_of_index_gt hidx, rankExcept_of_index_lt hidx]
      unfold index
      rw [hrow]
      omega
    · have hidx : index b < index a := by
        unfold index
        rw [hrow]
        omega
      rw [rankExcept_of_index_lt hidx, rankExcept_of_index_gt hidx]
      unfold index
      rw [hrow]
      omega
  · have hrow : a.1.val = b.1.val := congrArg Fin.val hr
    rcases hstep with hstep | hstep <;> omega

lemma rankExcept_adjacent_vertical_dist {B : Board} {a b : Cell B}
    (h : adjacent a b) (hc : sameCol a b) :
    Nat.dist (rankExcept a b) (rankExcept b a) = B.cols - 1 := by
  rcases h with (⟨hr, hstep⟩ | ⟨_, hstep⟩)
  · have hrow : a.1.val = b.1.val := congrArg Fin.val hr
    have hcol : a.2.val = b.2.val := congrArg Fin.val hc
    rcases hstep with hstep | hstep <;> omega
  · have hcol : a.2.val = b.2.val := congrArg Fin.val hc
    rcases hstep with hstep | hstep
    · have hidx : index a < index b := by
        unfold index
        rw [hcol]
        nlinarith [B.cols_pos]
      have hindex : index b = index a + B.cols := by
        unfold index
        rw [hcol]
        nlinarith
      have hle : index a ≤ index b - 1 := by
        omega
      rw [rankExcept_of_index_gt hidx, rankExcept_of_index_lt hidx]
      rw [Nat.dist_eq_sub_of_le_right hle]
      omega
    · have hidx : index b < index a := by
        unfold index
        rw [hcol]
        nlinarith [B.cols_pos]
      have hindex : index a = index b + B.cols := by
        unfold index
        rw [hcol]
        nlinarith
      have hle : index b ≤ index a - 1 := by
        omega
      rw [rankExcept_of_index_lt hidx, rankExcept_of_index_gt hidx]
      rw [Nat.dist_eq_sub_of_le hle]
      omega

lemma invStat_slide_horizontal_mod {B : Board}
    (cfg : Config B) (n : Cell B) (h : adjacent (blank cfg) n)
    (hr : sameRow (blank cfg) n) :
    invStat (slide cfg n h) % 2 = invStat cfg % 2 := by
  unfold invStat
  rw [tileList_slide_eq_erase_insert cfg n h]
  let L := tileList cfg
  let p := rankExcept (blank cfg) n
  have hp : p < L.length := by
    dsimp [L, p]
    rw [tileList_length]
    simpa [cellsRowMajorExcept_length] using rankExcept_lt (adjacent_ne h).symm
  have hget : L[p]'hp = cfg.cells n := by
    dsimp [L, p] at hp ⊢
    exact tileList_get_rankExcept cfg n (adjacent_ne h).symm
  have hpne : p ≠ L.length := by omega
  have hpq : rankExcept n (blank cfg) = p := by
    dsimp [p]
    exact (rankExcept_adjacent_horizontal_eq h hr).symm
  change NPuzzle.List.inversionCount
      ((L.eraseIdx p).insertIdx (rankExcept n (blank cfg)) (cfg.cells n)) % 2 =
    NPuzzle.List.inversionCount L % 2
  rw [hpq]
  have hlist : (L.eraseIdx p).insertIdx p (cfg.cells n) = L := by
    rw [← hget]
    rw [List.insertIdx_eraseIdx_self hpne]
    exact list_set_getElem_eq_self L p hp
  rw [hlist]

lemma invStat_slide_vertical_mod {B : Board}
    (cfg : Config B) (n : Cell B) (h : adjacent (blank cfg) n)
    (hc : sameCol (blank cfg) n) :
    invStat (slide cfg n h) % 2 = (invStat cfg + B.cols + 1) % 2 := by
  unfold invStat
  rw [tileList_slide_eq_erase_insert cfg n h]
  let L := tileList cfg
  let p := rankExcept (blank cfg) n
  let q := rankExcept n (blank cfg)
  have hp : p < L.length := by
    dsimp [L, p]
    rw [tileList_length]
    simpa [cellsRowMajorExcept_length] using rankExcept_lt (adjacent_ne h).symm
  have hq : q < L.length := by
    dsimp [L, q]
    rw [tileList_length]
    simpa [cellsRowMajorExcept_length] using rankExcept_lt (adjacent_ne h)
  have hget : L[p]'hp = cfg.cells n := by
    dsimp [L, p] at hp ⊢
    exact tileList_get_rankExcept cfg n (adjacent_ne h).symm
  have hdist : Nat.dist p q = B.cols - 1 := by
    dsimp [p, q]
    exact rankExcept_adjacent_vertical_dist h hc
  have hnd : L.Nodup := by
    dsimp [L]
    exact tileList_nodup cfg
  change NPuzzle.List.inversionCount ((L.eraseIdx p).insertIdx q (cfg.cells n)) % 2 =
    (NPuzzle.List.inversionCount L + B.cols + 1) % 2
  by_cases hpq : p = q
  · have hcols : B.cols = 1 := by
      have hdist0 : Nat.dist p q = 0 := by simp [hpq]
      rw [hdist0] at hdist
      have hpos : 0 < B.cols := B.cols_pos
      omega
    rw [← hpq]
    have hpne : p ≠ L.length := Nat.ne_of_lt hp
    have hlist : (L.eraseIdx p).insertIdx p (cfg.cells n) = L := by
      rw [← hget]
      rw [List.insertIdx_eraseIdx_self hpne]
      exact list_set_getElem_eq_self L p hp
    rw [hlist]
    omega
  · have hmod := NPuzzle.List.inversionCount_erase_insert_mod L p q hp hq hpq hnd
    have hval :
        (L.eraseIdx p).insertIdx q (cfg.cells n) =
          (L.eraseIdx p).insertIdx q (L[p]'hp) := by
      rw [hget]
    rw [hval]
    have hdist_mod : Nat.dist p q % 2 = (B.cols + 1) % 2 := by
      have hplus : B.cols + 1 = (B.cols - 1) + 2 := by
        have hpos : 0 < B.cols := B.cols_pos
        omega
      rw [hdist, hplus, Nat.add_mod]
      omega
    exact hmod.trans (by
      simpa [Nat.add_assoc] using
        add_mod_two_congr (a := NPuzzle.List.inversionCount L)
          (b := NPuzzle.List.inversionCount L)
          (c := Nat.dist p q) (d := B.cols + 1) rfl hdist_mod)

lemma parityClass_slide_horizontal_of_invStat_mod {B : Board}
    (cfg : Config B) (n : Cell B) (h : adjacent (blank cfg) n)
    (hr : sameRow (blank cfg) n)
    (hinv : invStat (slide cfg n h) % 2 = invStat cfg % 2) :
    parityClass (slide cfg n h) = parityClass cfg := by
  unfold parityClass
  rw [blank_slide cfg n h]
  have hrow : blankRowFromBottom n = blankRowFromBottom (blank cfg) :=
    (blankRowFromBottom_eq_sameRow hr).symm
  by_cases hodd : B.cols % 2 = 1
  · simp [hodd, hinv]
  · simp [hodd, hrow]
    exact add_mod_two_congr hinv rfl

lemma parityClass_slide_vertical_of_invStat_mod {B : Board}
    (cfg : Config B) (n : Cell B) (h : adjacent (blank cfg) n)
    (hc : sameCol (blank cfg) n)
    (hinv : invStat (slide cfg n h) % 2 = (invStat cfg + B.cols + 1) % 2) :
    parityClass (slide cfg n h) = parityClass cfg := by
  unfold parityClass
  rw [blank_slide cfg n h]
  have hrow :
      blankRowFromBottom n % 2 =
        (blankRowFromBottom (blank cfg) + 1) % 2 :=
    blankRow_adjacent_vertical_mod h hc
  by_cases hodd : B.cols % 2 = 1
  · have hinv' : invStat (slide cfg n h) % 2 = invStat cfg % 2 := by
      omega
    simp [hodd, hinv']
  · have hcols_lt : B.cols % 2 < 2 := Nat.mod_lt _ (by decide)
    have heven : B.cols % 2 = 0 := by omega
    have hinv' : invStat (slide cfg n h) % 2 = (invStat cfg + 1) % 2 := by
      omega
    simp [hodd]
    have hsum := add_mod_two_congr hinv' hrow
    omega

lemma parityClass_legalStep_of_invStat_mod {B : Board}
    (hhoriz :
      ∀ (cfg : Config B) (n : Cell B) (h : adjacent (blank cfg) n),
        sameRow (blank cfg) n →
          invStat (slide cfg n h) % 2 = invStat cfg % 2)
    (hvert :
      ∀ (cfg : Config B) (n : Cell B) (h : adjacent (blank cfg) n),
        sameCol (blank cfg) n →
          invStat (slide cfg n h) % 2 = (invStat cfg + B.cols + 1) % 2)
    {cfg cfg' : Config B} (hstep : legalStep cfg cfg') :
    parityClass cfg = parityClass cfg' := by
  rcases hstep with ⟨n, h, rfl⟩
  rcases adjacent_component h with hr | hc
  · exact (parityClass_slide_horizontal_of_invStat_mod cfg n h hr (hhoriz cfg n h hr)).symm
  · exact (parityClass_slide_vertical_of_invStat_mod cfg n h hc (hvert cfg n h hc)).symm

lemma parityClass_reachable_of_invStat_mod {B : Board}
    (hhoriz :
      ∀ (cfg : Config B) (n : Cell B) (h : adjacent (blank cfg) n),
        sameRow (blank cfg) n →
          invStat (slide cfg n h) % 2 = invStat cfg % 2)
    (hvert :
      ∀ (cfg : Config B) (n : Cell B) (h : adjacent (blank cfg) n),
        sameCol (blank cfg) n →
          invStat (slide cfg n h) % 2 = (invStat cfg + B.cols + 1) % 2)
    {cfg cfg' : Config B} (hreach : Reachable cfg cfg') :
    parityClass cfg = parityClass cfg' := by
  induction hreach with
  | refl => rfl
  | tail _ hbc ih =>
      exact ih.trans (parityClass_legalStep_of_invStat_mod hhoriz hvert hbc)

lemma parityClass_legalStep {B : Board} {cfg cfg' : Config B}
    (hstep : legalStep cfg cfg') :
    parityClass cfg = parityClass cfg' :=
  parityClass_legalStep_of_invStat_mod
    (fun cfg n h hr => invStat_slide_horizontal_mod cfg n h hr)
    (fun cfg n h hc => invStat_slide_vertical_mod cfg n h hc)
    hstep

lemma parityClass_reachable {B : Board} {cfg cfg' : Config B}
    (hreach : Reachable cfg cfg') :
    parityClass cfg = parityClass cfg' :=
  parityClass_reachable_of_invStat_mod
    (fun cfg n h hr => invStat_slide_horizontal_mod cfg n h hr)
    (fun cfg n h hc => invStat_slide_vertical_mod cfg n h hc)
    hreach

lemma reachable_imp_parity {B : Board} (cfg : Config B)
    (hreach : Reachable cfg (goal B)) :
    parityClass cfg = parityClass (goal B) :=
  parityClass_reachable hreach

end NPuzzle.Rect
