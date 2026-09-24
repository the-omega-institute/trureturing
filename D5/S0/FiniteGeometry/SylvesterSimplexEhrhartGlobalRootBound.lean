/- GID: D5/S0/FiniteGeometry/SylvesterSimplexEhrhartGlobalRootBound
   generality: G
   mirror-B: D5/B/S0/FiniteGeometry/SylvesterSimplexEhrhartGlobalRootBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Global norm bound for all nontrivial source roots in dimensions at least eight. -/

import D5.S0.FiniteGeometry.SylvesterSimplexEhrhartFixedSupportBound

noncomputable section

namespace D5.S0.FiniteGeometry.SylvesterSimplexEhrhartGlobalRootBound

open scoped BigOperators

open D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity
open D5.S0.FiniteGeometry.SylvesterSimplexEhrhartFixedSupportBound
open D5.S0.FiniteGeometry.SylvesterSimplexEhrhartRootContributionBound

open private sylvester_pos two_le_sylvester from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

open private sourceLocalRootContributionPolynomial from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartCoefficient

open private q period roots supportRoots supportPeriod from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartFixedSupportBound

private def squareWeight (i : ℕ) : ℝ := (sylvester (i + 1) : ℝ) ^ 2

private def prefixSquareSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, squareWeight i

private def elementarySquareSum (n r : ℕ) : ℝ :=
  ∑ R ∈ (Finset.range n).powersetCard r, ∏ i ∈ R, squareWeight i

private lemma seven_le_sylvester (j : ℕ) (hj : 3 ≤ j) :
    7 ≤ sylvester j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num [sylvester]
  | succ j hj ih =>
      have hrec :
          sylvester (j + 1) = sylvester j * (sylvester j - 1) + 1 := by
        cases j with
        | zero => omega
        | succ k => rfl
      rw [hrec]
      have hminus : 6 ≤ sylvester j - 1 := by omega
      have hmul : 7 * 6 ≤ sylvester j * (sylvester j - 1) :=
        Nat.mul_le_mul ih hminus
      omega

private lemma squareWeight_growth (j : ℕ) (hj : 3 ≤ j) :
    36 * squareWeight (j - 1) < squareWeight j := by
  have hs := seven_le_sylvester j hj
  have hrec :
      sylvester (j + 1) = sylvester j * (sylvester j - 1) + 1 := by
    cases j with
    | zero => omega
    | succ k => rfl
  have hnat : 6 * sylvester j < sylvester (j + 1) := by
    rw [hrec]
    have hminus : 6 ≤ sylvester j - 1 := by omega
    have hmul : sylvester j * 6 ≤ sylvester j * (sylvester j - 1) :=
      Nat.mul_le_mul_left _ hminus
    omega
  have hreal : 6 * (sylvester j : ℝ) < sylvester (j + 1) := by
    exact_mod_cast hnat
  have hpos : 0 < (sylvester j : ℝ) := by positivity
  simp only [squareWeight]
  rw [show j - 1 + 1 = j by omega]
  nlinarith [sq_nonneg ((sylvester (j + 1) : ℝ) - 6 * sylvester j)]

private lemma prefixSquareSum_lt (j : ℕ) (hj : 4 ≤ j) :
    20 * prefixSquareSum j < 21 * squareWeight (j - 1) := by
  induction j, hj using Nat.le_induction with
  | base => norm_num [prefixSquareSum, squareWeight, sylvester, Finset.sum_range_succ]
  | succ j hj ih =>
      have hsucc :
          prefixSquareSum (j + 1) = prefixSquareSum j + squareWeight j := by
        simp [prefixSquareSum, Finset.sum_range_succ]
      rw [hsucc]
      have hg := squareWeight_growth j (by omega)
      rw [show j + 1 - 1 = j by omega]
      have hw : 0 ≤ squareWeight (j - 1) := by
        exact sq_nonneg _
      nlinarith

private def maxErase (R : Finset ℕ) : ℕ × Finset ℕ :=
  if hR : R.Nonempty then (R.max' hR, R.erase (R.max' hR)) else (0, ∅)

private lemma maxErase_injOn_nonempty :
    Set.InjOn maxErase {R : Finset ℕ | R.Nonempty} := by
  intro A hA B hB hAB
  have hmaxA : maxErase A = (A.max' hA, A.erase (A.max' hA)) := by
    rw [maxErase]
    split
    · congr
    · contradiction
  have hmaxB : maxErase B = (B.max' hB, B.erase (B.max' hB)) := by
    rw [maxErase]
    split
    · congr
    · contradiction
  have hp : (A.max' hA, A.erase (A.max' hA)) =
      (B.max' hB, B.erase (B.max' hB)) := by
    rw [← hmaxA, ← hmaxB]
    exact hAB
  have hm : A.max' hA = B.max' hB := congrArg Prod.fst hp
  have he : A.erase (A.max' hA) = B.erase (B.max' hB) := congrArg Prod.snd hp
  have he' : A.erase (B.max' hB) = B.erase (B.max' hB) := by
    simpa [hm] using he
  calc
    A = insert (A.max' hA) (A.erase (A.max' hA)) :=
      (Finset.insert_erase (A.max'_mem hA)).symm
    _ = insert (B.max' hB) (B.erase (B.max' hB)) := by rw [hm, he']
    _ = B := Finset.insert_erase (B.max'_mem hB)

private lemma maxErase_maps_powerset (n r : ℕ) :
    Set.MapsTo maxErase
      ((Finset.range n).powersetCard (r + 1) : Set (Finset ℕ))
      ((Finset.range n ×ˢ (Finset.range (n - 1)).powersetCard r) :
        Set (ℕ × Finset ℕ)) := by
  intro R hR
  have hdata := Finset.mem_powersetCard.mp hR
  have hne : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun hzero => by
    rw [hzero] at hdata
    simp at hdata
  have hmaxmem : R.max' hne ∈ R := R.max'_mem hne
  have hmaxrange : R.max' hne ∈ Finset.range n := hdata.1 hmaxmem
  have heraseSub : R.erase (R.max' hne) ⊆ Finset.range (n - 1) := by
    intro i hi
    have hilow : i < R.max' hne := R.lt_max'_of_mem_erase_max' hne hi
    have himax : R.max' hne < n := Finset.mem_range.mp hmaxrange
    exact Finset.mem_range.mpr (by omega)
  have heraseCard : (R.erase (R.max' hne)).card = r := by
    rw [Finset.card_erase_of_mem hmaxmem, hdata.2]
    omega
  rw [maxErase, dif_pos hne]
  exact Set.mem_prod.mpr
    ⟨hmaxrange, Finset.mem_powersetCard.mpr ⟨heraseSub, heraseCard⟩⟩

private lemma elementarySquareSum_succ_le (n r : ℕ) :
    elementarySquareSum n (r + 1) ≤
      prefixSquareSum n * elementarySquareSum (n - 1) r := by
  let source := (Finset.range n).powersetCard (r + 1)
  let target := Finset.range n ×ˢ (Finset.range (n - 1)).powersetCard r
  let pairWeight : ℕ × Finset ℕ → ℝ := fun p =>
    squareWeight p.1 * ∏ i ∈ p.2, squareWeight i
  have hmaps : Set.MapsTo maxErase (source : Set (Finset ℕ))
      (target : Set (ℕ × Finset ℕ)) := by
    simpa [source, target] using maxErase_maps_powerset n r
  have hinj : Set.InjOn maxErase (source : Set (Finset ℕ)) := by
    apply maxErase_injOn_nonempty.mono
    intro R hR
    have hcard := (Finset.mem_powersetCard.mp hR).2
    exact Finset.nonempty_iff_ne_empty.mpr fun hzero => by
      rw [hzero] at hcard
      simp at hcard
  calc
    elementarySquareSum n (r + 1) =
        ∑ R ∈ source, pairWeight (maxErase R) := by
      apply Finset.sum_congr rfl
      intro R hR
      have hcard := (Finset.mem_powersetCard.mp hR).2
      have hne : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun hzero => by
        rw [hzero] at hcard
        simp at hcard
      rw [maxErase, dif_pos hne]
      dsimp only [pairWeight]
      exact (Finset.mul_prod_erase R squareWeight (R.max'_mem hne)).symm
    _ = ∑ p ∈ source.image maxErase, pairWeight p := by
      rw [Finset.sum_image]
      intro A hA B hB hAB
      exact hinj hA hB hAB
    _ ≤ ∑ p ∈ target, pairWeight p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.image_subset_iff.mpr hmaps
      · intro p _ _
        dsimp only [pairWeight]
        apply mul_nonneg (sq_nonneg _)
        exact Finset.prod_nonneg fun _ _ => sq_nonneg _
    _ = prefixSquareSum n * elementarySquareSum (n - 1) r := by
      dsimp only [target, pairWeight]
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      rfl

private lemma elementarySquareSum_one_ratio (n : ℕ) (hn : 4 ≤ n) :
    elementarySquareSum n 1 <
      (21 / 20 : ℝ) * squareWeight (n - 1) := by
  have hrec := elementarySquareSum_succ_le n 0
  rw [show elementarySquareSum (n - 1) 0 = 1 by simp [elementarySquareSum], mul_one] at hrec
  have hp := prefixSquareSum_lt n hn
  linarith

private lemma elementarySquareSum_two_ratio (n : ℕ) (hn : 5 ≤ n) :
    elementarySquareSum n 2 <
      (21 / 20 : ℝ) ^ 2 * squareWeight (n - 1) * squareWeight (n - 2) := by
  have hrec := elementarySquareSum_succ_le n 1
  norm_num at hrec
  have he := elementarySquareSum_one_ratio (n - 1) (by omega)
  have hp := prefixSquareSum_lt n (by omega)
  have hweight_pos (i : ℕ) : 0 < squareWeight i := by
    have hsi : 0 < (sylvester (i + 1) : ℝ) := by
      exact_mod_cast sylvester_pos (i + 1)
    exact sq_pos_of_pos hsi
  have hs : 0 < prefixSquareSum n := by
    rw [show n = (n - 1) + 1 by omega, prefixSquareSum, Finset.sum_range_succ]
    have hsum : 0 ≤ ∑ i ∈ Finset.range (n - 1), squareWeight i := by
      exact Finset.sum_nonneg fun i _ => (hweight_pos i).le
    linarith [hweight_pos (n - 1)]
  have hw : 0 < (21 / 20 : ℝ) * squareWeight (n - 2) :=
    mul_pos (by norm_num) (hweight_pos _)
  calc
    elementarySquareSum n 2 ≤
        prefixSquareSum n * elementarySquareSum (n - 1) 1 := hrec
    _ < prefixSquareSum n * ((21 / 20 : ℝ) * squareWeight (n - 2)) :=
      mul_lt_mul_of_pos_left he hs
    _ < ((21 / 20 : ℝ) * squareWeight (n - 1)) *
        ((21 / 20 : ℝ) * squareWeight (n - 2)) :=
      mul_lt_mul_of_pos_right (by nlinarith [hp]) hw
    _ = _ := by ring

private lemma elementarySquareSum_three_ratio (n : ℕ) (hn : 6 ≤ n) :
    elementarySquareSum n 3 <
      (21 / 20 : ℝ) ^ 3 * squareWeight (n - 1) * squareWeight (n - 2) *
        squareWeight (n - 3) := by
  have hrec := elementarySquareSum_succ_le n 2
  norm_num at hrec
  have he := elementarySquareSum_two_ratio (n - 1) (by omega)
  have hp := prefixSquareSum_lt n (by omega)
  have hweight_pos (i : ℕ) : 0 < squareWeight i := by
    have hsi : 0 < (sylvester (i + 1) : ℝ) := by
      exact_mod_cast sylvester_pos (i + 1)
    exact sq_pos_of_pos hsi
  have hs : 0 < prefixSquareSum n := by
    rw [show n = (n - 1) + 1 by omega, prefixSquareSum, Finset.sum_range_succ]
    have hsum : 0 ≤ ∑ i ∈ Finset.range (n - 1), squareWeight i := by
      exact Finset.sum_nonneg fun i _ => (hweight_pos i).le
    linarith [hweight_pos (n - 1)]
  have hw : 0 < (21 / 20 : ℝ) ^ 2 * squareWeight (n - 2) *
      squareWeight (n - 3) :=
    mul_pos (mul_pos (pow_pos (by norm_num) _) (hweight_pos _))
      (hweight_pos _)
  calc
    elementarySquareSum n 3 ≤
        prefixSquareSum n * elementarySquareSum (n - 1) 2 := hrec
    _ < prefixSquareSum n * ((21 / 20 : ℝ) ^ 2 * squareWeight (n - 2) *
        squareWeight (n - 3)) := mul_lt_mul_of_pos_left he hs
    _ < ((21 / 20 : ℝ) * squareWeight (n - 1)) *
        ((21 / 20 : ℝ) ^ 2 * squareWeight (n - 2) *
          squareWeight (n - 3)) :=
      mul_lt_mul_of_pos_right (by nlinarith [hp]) hw
    _ = _ := by ring

private lemma elementarySquareSum_four_ratio (n : ℕ) (hn : 7 ≤ n) :
    elementarySquareSum n 4 <
      (21 / 20 : ℝ) ^ 4 * squareWeight (n - 1) * squareWeight (n - 2) *
        squareWeight (n - 3) * squareWeight (n - 4) := by
  have hrec := elementarySquareSum_succ_le n 3
  norm_num at hrec
  have he := elementarySquareSum_three_ratio (n - 1) (by omega)
  have hp := prefixSquareSum_lt n (by omega)
  have hweight_pos (i : ℕ) : 0 < squareWeight i := by
    have hsi : 0 < (sylvester (i + 1) : ℝ) := by
      exact_mod_cast sylvester_pos (i + 1)
    exact sq_pos_of_pos hsi
  have hs : 0 < prefixSquareSum n := by
    rw [show n = (n - 1) + 1 by omega, prefixSquareSum, Finset.sum_range_succ]
    have hsum : 0 ≤ ∑ i ∈ Finset.range (n - 1), squareWeight i := by
      exact Finset.sum_nonneg fun i _ => (hweight_pos i).le
    linarith [hweight_pos (n - 1)]
  have hw : 0 < (21 / 20 : ℝ) ^ 3 * squareWeight (n - 2) *
      squareWeight (n - 3) * squareWeight (n - 4) :=
    mul_pos
      (mul_pos (mul_pos (pow_pos (by norm_num) _) (hweight_pos _))
        (hweight_pos _)) (hweight_pos _)
  calc
    elementarySquareSum n 4 ≤
        prefixSquareSum n * elementarySquareSum (n - 1) 3 := hrec
    _ < prefixSquareSum n * ((21 / 20 : ℝ) ^ 3 * squareWeight (n - 2) *
        squareWeight (n - 3) * squareWeight (n - 4)) :=
      mul_lt_mul_of_pos_left he hs
    _ < ((21 / 20 : ℝ) * squareWeight (n - 1)) *
        ((21 / 20 : ℝ) ^ 3 * squareWeight (n - 2) *
          squareWeight (n - 3) * squareWeight (n - 4)) :=
      mul_lt_mul_of_pos_right (by nlinarith [hp]) hw
    _ = _ := by ring

private def supportAllowance (n : ℕ) (R : Finset (Fin n)) (F : ℝ) : ℝ :=
  (if R.card = 1 then (supportPeriod n R : ℝ) ^ 2 / (Real.sqrt 12 * F) else 0) +
  (if R.card = 2 then (supportPeriod n R : ℝ) ^ 2 / (12 * F) else 0) +
  (if R.card = 3 then
      (supportPeriod n R : ℝ) ^ 2 / ((Real.sqrt 12) ^ 3 * F) else 0) +
  (if R.card = 4 then (supportPeriod n R : ℝ) ^ 2 / (2304 * F) else 0)

private lemma sylvester_mono_of_le (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    sylvester a ≤ sylvester b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
      apply ih.trans
      have hrec :
          sylvester (b + 1) = sylvester b * (sylvester b - 1) + 1 := by
        cases b with
        | zero => omega
        | succ k => rfl
      rw [hrec]
      have hs := two_le_sylvester b (by omega)
      have hm : sylvester b ≤ sylvester b * (sylvester b - 1) := by
        have := Nat.mul_le_mul_left (sylvester b) (show 1 ≤ sylvester b - 1 by omega)
        simpa using this
      omega

private lemma fixed_prefix_bounds (n : ℕ) (hn : 7 ≤ n) :
    42 ≤ sylvester (n - 3) - 1 ∧
    1806 ≤ sylvester (n - 2) - 1 ∧
    3000000 < sylvester (n - 1) - 1 ∧
    9000000000000 < sylvester n - 1 := by
  have h4 := sylvester_mono_of_le 4 (n - 3) (by omega) (by omega)
  have h5 := sylvester_mono_of_le 5 (n - 2) (by omega) (by omega)
  have h6 := sylvester_mono_of_le 6 (n - 1) (by omega) (by omega)
  have h7 := sylvester_mono_of_le 7 n (by omega) (by omega)
  norm_num [sylvester] at h4 h5 h6 h7 ⊢
  omega

private lemma supportAllowance_sum_lt (n : ℕ) (hn : 7 ≤ n) :
    (∑ R ∈ (Finset.univ : Finset (Fin n)).powerset,
      supportAllowance n R (n + 1 - 6).factorial) <
      ((sylvester (n + 1) - 1 : ℕ) : ℝ) ^ 2 /
        (1900000 * (n + 1 - 6).factorial) := by
  let F : ℝ := (n + 1 - 6).factorial
  let M : ℝ := (sylvester (n + 1) - 1 : ℕ)
  let p1 : ℝ := (sylvester n - 1 : ℕ)
  let p2 : ℝ := (sylvester (n - 1) - 1 : ℕ)
  let p3 : ℝ := (sylvester (n - 2) - 1 : ℕ)
  let p4 : ℝ := (sylvester (n - 3) - 1 : ℕ)
  have hF : 0 < F := by dsimp only [F]; positivity
  have hM : 0 < M := by
    dsimp only [M]
    exact_mod_cast Nat.sub_pos_of_lt
      (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester (n + 1) (by omega)))
  have hweight_pos (i : ℕ) : 0 < squareWeight i := by
    have hsi : 0 < (sylvester (i + 1) : ℝ) := by
      exact_mod_cast sylvester_pos (i + 1)
    exact sq_pos_of_pos hsi
  have hstep (j : ℕ) (hj : 1 ≤ j) :
      ((sylvester (j + 1) - 1 : ℕ) : ℝ) ^ 2 =
        ((sylvester j - 1 : ℕ) : ℝ) ^ 2 * squareWeight (j - 1) := by
    have hrec :
        sylvester (j + 1) = sylvester j * (sylvester j - 1) + 1 := by
      cases j with
      | zero => omega
      | succ k => rfl
    have hnat : sylvester (j + 1) - 1 = sylvester j * (sylvester j - 1) := by
      omega
    rw [hnat]
    push_cast
    simp only [squareWeight, show j - 1 + 1 = j by omega]
    ring
  have hstep1 := hstep n (by omega)
  have hstep2 := hstep (n - 1) (by omega)
  have hstep3 := hstep (n - 2) (by omega)
  have hstep4 := hstep (n - 3) (by omega)
  simp only [show n - 1 + 1 = n by omega,
    show n - 2 + 1 = n - 1 by omega,
    show n - 3 + 1 = n - 2 by omega,
    show n - 1 - 1 = n - 2 by omega,
    show n - 2 - 1 = n - 3 by omega,
    show n - 3 - 1 = n - 4 by omega] at hstep2 hstep3 hstep4
  have hs1 : M ^ 2 = p1 ^ 2 * squareWeight (n - 1) := by
    dsimp only [M, p1]
    exact hstep1
  have hs2 : M ^ 2 = p2 ^ 2 * squareWeight (n - 1) * squareWeight (n - 2) := by
    dsimp only [M, p2]
    rw [hstep1, hstep2]
    ring
  have hs3 : M ^ 2 = p3 ^ 2 * squareWeight (n - 1) * squareWeight (n - 2) *
      squareWeight (n - 3) := by
    dsimp only [M, p3]
    rw [hstep1, hstep2, hstep3]
    ring
  have hs4 : M ^ 2 = p4 ^ 2 * squareWeight (n - 1) * squareWeight (n - 2) *
      squareWeight (n - 3) * squareWeight (n - 4) := by
    dsimp only [M, p4]
    rw [hstep1, hstep2, hstep3, hstep4]
    ring
  have hp : 42 ≤ sylvester (n - 3) - 1 ∧
      1806 ≤ sylvester (n - 2) - 1 ∧
      3000000 < sylvester (n - 1) - 1 ∧
      9000000000000 < sylvester n - 1 := fixed_prefix_bounds n hn
  have hp1 : (9000000000000 : ℝ) < p1 := by
    dsimp only [p1]
    exact_mod_cast hp.2.2.2
  have hp2 : (3000000 : ℝ) < p2 := by
    dsimp only [p2]
    exact_mod_cast hp.2.2.1
  have hp3 : (1806 : ℝ) ≤ p3 := by
    dsimp only [p3]
    exact_mod_cast hp.2.1
  have hp4 : (42 : ℝ) ≤ p4 := by
    dsimp only [p4]
    exact_mod_cast hp.1
  have hp1pos : 0 < p1 := by linarith
  have hp2pos : 0 < p2 := by linarith
  have hp3pos : 0 < p3 := by linarith
  have hp4pos : 0 < p4 := by linarith
  have hsqrt : 3 < Real.sqrt 12 := by
    have hs0 := Real.sqrt_nonneg 12
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)
    nlinarith
  have hsqrt3 : 27 < (Real.sqrt 12) ^ 3 := by
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)
    nlinarith
  have hr1 := elementarySquareSum_one_ratio n (by omega)
  have hr2 := elementarySquareSum_two_ratio n (by omega)
  have hr3 := elementarySquareSum_three_ratio n (by omega)
  have hr4 := elementarySquareSum_four_ratio n hn
  have he1 : elementarySquareSum n 1 < 2 * squareWeight (n - 1) := by
    exact hr1.trans (mul_lt_mul_of_pos_right (by norm_num) (hweight_pos _))
  have he2 : elementarySquareSum n 2 <
      2 * squareWeight (n - 1) * squareWeight (n - 2) := by
    calc
      _ < (21 / 20 : ℝ) ^ 2 *
          (squareWeight (n - 1) * squareWeight (n - 2)) := by
        simpa only [mul_assoc] using hr2
      _ < 2 * (squareWeight (n - 1) * squareWeight (n - 2)) :=
        mul_lt_mul_of_pos_right (by norm_num)
          (mul_pos (hweight_pos _) (hweight_pos _))
      _ = _ := by ring
  have he3 : elementarySquareSum n 3 <
      2 * squareWeight (n - 1) * squareWeight (n - 2) * squareWeight (n - 3) := by
    calc
      _ < (21 / 20 : ℝ) ^ 3 *
          (squareWeight (n - 1) * squareWeight (n - 2) * squareWeight (n - 3)) := by
        simpa only [mul_assoc] using hr3
      _ < 2 * (squareWeight (n - 1) * squareWeight (n - 2) * squareWeight (n - 3)) :=
        mul_lt_mul_of_pos_right (by norm_num)
          (mul_pos (mul_pos (hweight_pos _) (hweight_pos _)) (hweight_pos _))
      _ = _ := by ring
  have he4 : elementarySquareSum n 4 <
      2 * squareWeight (n - 1) * squareWeight (n - 2) * squareWeight (n - 3) *
        squareWeight (n - 4) := by
    calc
      _ < (21 / 20 : ℝ) ^ 4 * (squareWeight (n - 1) * squareWeight (n - 2) *
          squareWeight (n - 3) * squareWeight (n - 4)) := by
        simpa only [mul_assoc] using hr4
      _ < 2 * (squareWeight (n - 1) * squareWeight (n - 2) * squareWeight (n - 3) *
          squareWeight (n - 4)) :=
        mul_lt_mul_of_pos_right (by norm_num)
          (mul_pos (mul_pos (mul_pos (hweight_pos _) (hweight_pos _)) (hweight_pos _))
            (hweight_pos _))
      _ = _ := by ring
  have hperiod_sum (r : ℕ) (a : ℝ) :
      (∑ R ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        (supportPeriod n R : ℝ) ^ 2 / a) = elementarySquareSum n r / a := by
    have hmap : (Finset.univ : Finset (Fin n)).map Fin.valEmbedding =
        Finset.range n := by
      ext i
      simp
    have hsum :
        (∑ R ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
          (supportPeriod n R : ℝ) ^ 2) = elementarySquareSum n r := by
      rw [elementarySquareSum, ← hmap, Finset.powersetCard_map, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro R _
      simp only [supportPeriod, q, squareWeight]
      push_cast
      rw [Finset.prod_pow]
      congr 1
      change (∏ i ∈ R, (sylvester (i.1 + 1) : ℝ)) =
        ∏ x ∈ R.map Fin.valEmbedding, (sylvester (x + 1) : ℝ)
      rw [Finset.prod_map]
      rfl
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, hsum]
  have hcancel (p w k : ℝ) (hp : p ≠ 0) (hk : k ≠ 0) :
      (2 * w) / (k * F) = (p ^ 2 * w) / F * (2 / (k * p ^ 2)) := by
    field_simp [hF.ne', hp, hk]
  have ht1 :
      (∑ R ∈ (Finset.univ : Finset (Fin n)).powersetCard 1,
        (supportPeriod n R : ℝ) ^ 2 / (Real.sqrt 12 * F)) <
        M ^ 2 / F * (2 / (3 * p1 ^ 2)) := by
    rw [hperiod_sum]
    calc
      elementarySquareSum n 1 / (Real.sqrt 12 * F) <
          (2 * squareWeight (n - 1)) / (Real.sqrt 12 * F) := by gcongr
      _ < (2 * squareWeight (n - 1)) / (3 * F) := by
        gcongr
        exact mul_pos (by norm_num) (hweight_pos _)
      _ = M ^ 2 / F * (2 / (3 * p1 ^ 2)) := by
        rw [hs1]
        exact hcancel p1 (squareWeight (n - 1)) 3 hp1pos.ne' (by norm_num)
  have ht2 :
      (∑ R ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
        (supportPeriod n R : ℝ) ^ 2 / (12 * F)) <
        M ^ 2 / F * (2 / (12 * p2 ^ 2)) := by
    rw [hperiod_sum]
    calc
      elementarySquareSum n 2 / (12 * F) <
          (2 * squareWeight (n - 1) * squareWeight (n - 2)) / (12 * F) := by gcongr
      _ = M ^ 2 / F * (2 / (12 * p2 ^ 2)) := by
        rw [hs2]
        simpa only [mul_assoc] using hcancel p2
          (squareWeight (n - 1) * squareWeight (n - 2)) 12 hp2pos.ne' (by norm_num)
  have ht3 :
      (∑ R ∈ (Finset.univ : Finset (Fin n)).powersetCard 3,
        (supportPeriod n R : ℝ) ^ 2 / ((Real.sqrt 12) ^ 3 * F)) <
        M ^ 2 / F * (2 / (27 * p3 ^ 2)) := by
    rw [hperiod_sum]
    calc
      elementarySquareSum n 3 / ((Real.sqrt 12) ^ 3 * F) <
          (2 * squareWeight (n - 1) * squareWeight (n - 2) *
            squareWeight (n - 3)) / ((Real.sqrt 12) ^ 3 * F) := by gcongr
      _ < (2 * squareWeight (n - 1) * squareWeight (n - 2) *
            squareWeight (n - 3)) / (27 * F) := by
        gcongr
        exact mul_pos
          (mul_pos (mul_pos (by norm_num) (hweight_pos _)) (hweight_pos _))
          (hweight_pos _)
      _ = M ^ 2 / F * (2 / (27 * p3 ^ 2)) := by
        rw [hs3]
        simpa only [mul_assoc] using hcancel p3
          (squareWeight (n - 1) * squareWeight (n - 2) * squareWeight (n - 3)) 27
          hp3pos.ne' (by norm_num)
  have ht4 :
      (∑ R ∈ (Finset.univ : Finset (Fin n)).powersetCard 4,
        (supportPeriod n R : ℝ) ^ 2 / (2304 * F)) <
        M ^ 2 / F * (2 / (2304 * p4 ^ 2)) := by
    rw [hperiod_sum]
    calc
      elementarySquareSum n 4 / (2304 * F) <
          (2 * squareWeight (n - 1) * squareWeight (n - 2) *
            squareWeight (n - 3) * squareWeight (n - 4)) / (2304 * F) := by gcongr
      _ = M ^ 2 / F * (2 / (2304 * p4 ^ 2)) := by
        rw [hs4]
        simpa only [mul_assoc] using hcancel p4
          (squareWeight (n - 1) * squareWeight (n - 2) * squareWeight (n - 3) *
            squareWeight (n - 4)) 2304 hp4pos.ne' (by norm_num)
  have hratio_lt (k a p : ℝ) (hk : 0 < k) (ha : 0 < a) (hap : a < p) :
      2 / (k * p ^ 2) < 2 / (k * a ^ 2) := by
    have hp : 0 < p := ha.trans hap
    have hsq : a ^ 2 < p ^ 2 := pow_lt_pow_left₀ hap ha.le (by norm_num)
    rw [div_lt_div_iff₀ (mul_pos hk (sq_pos_of_pos hp))
      (mul_pos hk (sq_pos_of_pos ha))]
    exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hsq hk) (by norm_num)
  have hratio_le (k a p : ℝ) (hk : 0 < k) (ha : 0 < a) (hap : a ≤ p) :
      2 / (k * p ^ 2) ≤ 2 / (k * a ^ 2) := by
    have hp : 0 < p := lt_of_lt_of_le ha hap
    have hsq : a ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ ha.le hap 2
    rw [div_le_div_iff₀ (mul_pos hk (sq_pos_of_pos hp))
      (mul_pos hk (sq_pos_of_pos ha))]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hk.le) (by norm_num)
  have hi1 : 2 / (3 * p1 ^ 2) < 2 / (3 * (9000000000000 : ℝ) ^ 2) :=
    hratio_lt 3 9000000000000 p1 (by norm_num) (by norm_num) hp1
  have hi2 : 2 / (12 * p2 ^ 2) < 2 / (12 * (3000000 : ℝ) ^ 2) :=
    hratio_lt 12 3000000 p2 (by norm_num) (by norm_num) hp2
  have hi3 : 2 / (27 * p3 ^ 2) ≤ 2 / (27 * (1806 : ℝ) ^ 2) :=
    hratio_le 27 1806 p3 (by norm_num) (by norm_num) hp3
  have hi4 : 2 / (2304 * p4 ^ 2) ≤ 2 / (2304 * (42 : ℝ) ^ 2) :=
    hratio_le 2304 42 p4 (by norm_num) (by norm_num) hp4
  have herr : 2 / (3 * p1 ^ 2) + 2 / (12 * p2 ^ 2) + 2 / (27 * p3 ^ 2) +
      2 / (2304 * p4 ^ 2) < (1 / 1900000 : ℝ) := by
    calc
      _ < 2 / (3 * (9000000000000 : ℝ) ^ 2) +
          2 / (12 * (3000000 : ℝ) ^ 2) + 2 / (27 * (1806 : ℝ) ^ 2) +
          2 / (2304 * (42 : ℝ) ^ 2) := by
        linarith only [hi1, hi2, hi3, hi4]
      _ < (1 / 1900000 : ℝ) := by norm_num
  have hpart (r : ℕ) (f : Finset (Fin n) → ℝ) :
      (∑ R ∈ (Finset.univ : Finset (Fin n)).powerset,
        if R.card = r then f R else 0) =
        ∑ R ∈ (Finset.univ : Finset (Fin n)).powersetCard r, f R := by
    rw [← Finset.sum_filter, ← Finset.powersetCard_eq_filter]
  simp only [supportAllowance, Finset.sum_add_distrib]
  rw [hpart, hpart, hpart, hpart]
  calc
    _ < M ^ 2 / F * (2 / (3 * p1 ^ 2)) +
        M ^ 2 / F * (2 / (12 * p2 ^ 2)) +
        M ^ 2 / F * (2 / (27 * p3 ^ 2)) +
        M ^ 2 / F * (2 / (2304 * p4 ^ 2)) := by nlinarith
    _ = M ^ 2 / F * (2 / (3 * p1 ^ 2) + 2 / (12 * p2 ^ 2) +
        2 / (27 * p3 ^ 2) + 2 / (2304 * p4 ^ 2)) := by ring
    _ < M ^ 2 / F * (1 / 1900000) :=
      mul_lt_mul_of_pos_left herr (div_pos (sq_pos_of_pos hM) hF)
    _ = ((sylvester (n + 1) - 1 : ℕ) : ℝ) ^ 2 /
        (1900000 * (n + 1 - 6).factorial) := by
      dsimp only [M, F]
      ring

/-- For dimensions at least eight and the two source shifts, the complete
nontrivial-root contribution is strictly below the required global budget. -/
theorem sourceNontrivialRootContribution_norm_sum_lt
    (d : ℕ) (hd : 8 ≤ d) (c : ℤ) (hc : c = 0 ∨ c = -1) :
    (∑ z ∈ (Polynomial.nthRootsFinset (sylvester d - 1) (1 : ℂ)).erase 1,
      ‖(sourceLocalRootContributionPolynomial d z c).coeff (d - 6)‖) <
      (sylvester d - 1 : ℝ) ^ 2 / (1900000 * (d - 6).factorial) := by
  let n := d - 1
  have hn : 7 ≤ n := by omega
  let support : ℂ → Finset (Fin n) := fun z =>
    Finset.univ.filter fun i : Fin n => z ^ (period n / q i) ≠ 1
  have hmaps : ∀ z ∈ (roots (period n)).erase 1,
      support z ∈ (Finset.univ : Finset (Fin n)).powerset := by
    intro z _
    exact Finset.mem_powerset.mpr (Finset.subset_univ _)
  have hsum :
      (∑ z ∈ (roots (period n)).erase 1,
        ‖(sourceLocalRootContributionPolynomial (n + 1) z c).coeff
          (n + 1 - 6)‖) ≤
        ∑ R ∈ (Finset.univ : Finset (Fin n)).powerset,
          supportAllowance n R (n + 1 - 6).factorial := by
    calc
      (∑ z ∈ (roots (period n)).erase 1,
          ‖(sourceLocalRootContributionPolynomial (n + 1) z c).coeff
            (n + 1 - 6)‖) =
          ∑ R ∈ (Finset.univ : Finset (Fin n)).powerset,
            ∑ z ∈ (roots (period n)).erase 1 with support z = R,
              ‖(sourceLocalRootContributionPolynomial (n + 1) z c).coeff
                (n + 1 - 6)‖ := by
        symm
        exact Finset.sum_fiberwise_of_maps_to hmaps _
      _ ≤ ∑ R ∈ (Finset.univ : Finset (Fin n)).powerset,
          supportAllowance n R (n + 1 - 6).factorial := by
        apply Finset.sum_le_sum
        intro R _
        have hfin : ((roots (period n)).erase 1).filter (fun z =>
            Finset.univ.filter (fun i : Fin n => z ^ (period n / q i) ≠ 1) = R) =
            (roots (period n)).filter (fun z => z ≠ 1 ∧
              Finset.univ.filter (fun i : Fin n => z ^ (period n / q i) ≠ 1) = R) := by
          ext z
          simp [and_left_comm, and_assoc]
        change (∑ z ∈ ((roots (period n)).erase 1).filter (fun z =>
            Finset.univ.filter (fun i : Fin n => z ^ (period n / q i) ≠ 1) = R),
          ‖(sourceLocalRootContributionPolynomial (n + 1) z c).coeff
            (n + 1 - 6)‖) ≤ _
        rw [hfin, ← Finset.sum_attach]
        change (∑ z : supportRoots n R,
          ‖(sourceLocalRootContributionPolynomial (n + 1) z.1 c).coeff
            (n + 1 - 6)‖) ≤ supportAllowance n R (n + 1 - 6).factorial
        by_cases hR : R.Nonempty
        · rcases lt_trichotomy R.card 4 with hlt | heq | hgt
          · have hcard : R.card ≤ 3 := by omega
            have hb := (sourceFixedSupportNormSum_bounds n hn R hR c).1 hcard hc
            have hcases : R.card = 1 ∨ R.card = 2 ∨ R.card = 3 := by
              have := Finset.card_pos.mpr hR
              omega
            rcases hcases with h1 | h2 | h3
            · simpa [supportAllowance, h1, show n + 1 - 6 = n - 5 by omega] using hb
            · simpa [supportAllowance, h2, show n + 1 - 6 = n - 5 by omega,
                show (Real.sqrt 12) ^ 2 = 12 by
                rw [sq, Real.mul_self_sqrt (by norm_num)]]
                using hb
            · simpa [supportAllowance, h3, show n + 1 - 6 = n - 5 by omega] using hb
          · have hb := (sourceFixedSupportNormSum_bounds n hn R hR c).2 heq
            simpa [supportAllowance, heq, show n + 1 - 6 = n - 5 by omega] using hb
          · have hzero (z : supportRoots n R) :
                (sourceLocalRootContributionPolynomial (n + 1) z.1 c).coeff
                  (n + 1 - 6) = 0 := by
              exact (sourceNontrivialRootContribution_support_cutoff n hn z.1
                (Finset.mem_filter.mp z.2).1 (Finset.mem_filter.mp z.2).2.1 c).2.2.2.2
                  (by simpa [(Finset.mem_filter.mp z.2).2.2] using hgt)
            have hind : n + 1 - 6 = n - 5 := by omega
            simp only [hind] at hzero ⊢
            simp [hzero, supportAllowance, show R.card ≠ 1 by omega,
              show R.card ≠ 2 by omega, show R.card ≠ 3 by omega,
              show R.card ≠ 4 by omega]
        · have hcard : R.card = 0 := Finset.not_nonempty_iff_eq_empty.mp hR ▸ rfl
          have hempty : IsEmpty (supportRoots n R) :=
            ⟨fun z => hR (by
              rw [← (Finset.mem_filter.mp z.2).2.2]
              by_contra hsupp
              rw [Finset.not_nonempty_iff_eq_empty] at hsupp
              let zRoot : {w // w ∈ roots (period n)} :=
                ⟨z.1, (Finset.mem_filter.mp z.2).1⟩
              let oneRoot : {w // w ∈ roots (period n)} :=
                ⟨1, by
                  rw [roots, Polynomial.mem_nthRootsFinset]
                  · simp
                  · exact Nat.sub_pos_of_lt
                      (lt_of_lt_of_le Nat.one_lt_two
                        (two_le_sylvester (n + 1) (by omega)))⟩
              have hcoords : sylvesterRootEquiv n (by omega) zRoot =
                  sylvesterRootEquiv n (by omega) oneRoot := by
                funext i
                apply Subtype.ext
                change z.1 ^ (period n / q i) = 1 ^ (period n / q i)
                rw [one_pow]
                by_contra hne
                have hi : i ∈ support z.1 :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
                change i ∈ Finset.univ.filter (fun j : Fin n =>
                  z.1 ^ (period n / q j) ≠ 1) at hi
                rw [hsupp] at hi
                simpa using hi
              have heq : zRoot = oneRoot :=
                (sylvesterRootEquiv n (by omega)).injective hcoords
              exact (Finset.mem_filter.mp z.2).2.1 (congrArg Subtype.val heq))⟩
          letI : IsEmpty (supportRoots n R) := hempty
          simp [supportAllowance, hcard]
  have hbudget := supportAllowance_sum_lt n hn
  have h := lt_of_le_of_lt hsum hbudget
  have hnd : n + 1 = d := by dsimp only [n]; omega
  have hsd : 1 ≤ sylvester d := le_trans (by norm_num) (two_le_sylvester d (by omega))
  simpa only [roots, period, hnd, Nat.cast_sub hsd, Nat.cast_one] using h

end D5.S0.FiniteGeometry.SylvesterSimplexEhrhartGlobalRootBound
