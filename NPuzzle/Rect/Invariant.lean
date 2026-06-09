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

end NPuzzle.Rect
