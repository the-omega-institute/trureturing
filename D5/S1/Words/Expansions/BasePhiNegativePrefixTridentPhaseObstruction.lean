/- GID: D5/S1/Words/Expansions/BasePhiNegativePrefixTridentPhaseObstruction
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The frozen phase selector disagrees with the canonical core for the prefix 010. -/

import D5.S1.Words.Expansions.BasePhiNegativePrefixTridentEdge

namespace D5.X_Frontier.BasePhiNegativePrefixTrident

open D5.S0.Carrier
open D5.S1.Words.Expansions.BasePhiCanonicalExpansion
open D5.S1.Words.Expansions.BasePhiNegative
open D5.S1.Words.Expansions.BasePhiTailBounds

noncomputable section

private theorem positive_phiUnit_local (K : Nat) :
    (((phiUnit ^ (K : Int) : GoldenIntˣ) : GoldenInt)) = phi ^ K := by
  rw [zpow_natCast]
  exact Units.val_pow_eq_pow_val phiUnit K

private theorem negative_phiUnit_local (K : Nat) :
    (((phiUnit ^ (-(K : Int)) : GoldenIntˣ) : GoldenInt)) =
      (-conj phi) ^ K := by
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  rfl

private theorem negative_phiUnit_even_local {K : Nat} (hK : Even K) :
    (((phiUnit ^ (-(K : Int)) : GoldenIntˣ) : GoldenInt)) =
      conj (phi ^ K) := by
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  change (phi - 1) ^ K = conj (phi ^ K)
  have hphi : phi - 1 = -conj phi := by
    rw [conj_phi]
    abel
  rw [hphi, neg_pow, Even.neg_one_pow hK, one_mul]
  exact (conjEquiv.map_pow phi K).symm

@[simp] private theorem phiUnit_zpow_neg_six :
    (((phiUnit ^ (-6 : Int) : GoldenIntˣ) : GoldenInt)) = ⟨13, -8⟩ := by
  rw [show (-6 : Int) = -((6 : Nat) : Int) by norm_num,
    negative_phiUnit_local]
  apply GoldenInt.ext <;> norm_num [conj, phi, pow_succ]

@[simp] private theorem phiUnit_zpow_neg_four :
    (((phiUnit ^ (-4 : Int) : GoldenIntˣ) : GoldenInt)) = ⟨5, -3⟩ := by
  rw [show (-4 : Int) = -((4 : Nat) : Int) by norm_num,
    negative_phiUnit_local]
  apply GoldenInt.ext <;> norm_num [conj, phi, pow_succ]

@[simp] private theorem phiUnit_zpow_neg_three :
    (((phiUnit ^ (-3 : Int) : GoldenIntˣ) : GoldenInt)) = ⟨-3, 2⟩ := by
  rw [show (-3 : Int) = -((3 : Nat) : Int) by norm_num,
    negative_phiUnit_local]
  apply GoldenInt.ext <;> norm_num [conj, phi, pow_succ]

@[simp] private theorem phiUnit_zpow_neg_two :
    (((phiUnit ^ (-2 : Int) : GoldenIntˣ) : GoldenInt)) = ⟨2, -1⟩ := by
  rw [show (-2 : Int) = -((2 : Nat) : Int) by norm_num,
    negative_phiUnit_local]
  apply GoldenInt.ext <;> norm_num [conj, phi, pow_succ]

@[simp] private theorem phiUnit_zpow_neg_one :
    (((phiUnit ^ (-1 : Int) : GoldenIntˣ) : GoldenInt)) = ⟨-1, 1⟩ := by
  rw [show (-1 : Int) = -((1 : Nat) : Int) by norm_num,
    negative_phiUnit_local]
  apply GoldenInt.ext <;> norm_num [conj, phi]

@[simp] private theorem phiUnit_inv_one :
    (((phiUnit ^ (1 : Nat))⁻¹ : GoldenIntˣ) : GoldenInt) = ⟨-1, 1⟩ := by
  have h := phiUnit_zpow_neg_one
  rw [show (-1 : Int) = -((1 : Nat) : Int) by norm_num,
    zpow_neg, zpow_natCast] at h
  exact h

@[simp] private theorem phiUnit_pow_two_inv :
    (((phiUnit ^ (2 : Nat))⁻¹ : GoldenIntˣ) : GoldenInt) = ⟨2, -1⟩ := by
  have h := phiUnit_zpow_neg_two
  rw [show (-2 : Int) = -((2 : Nat) : Int) by norm_num,
    zpow_neg, zpow_natCast] at h
  exact h

@[simp] private theorem phiUnit_pow_three_inv :
    (((phiUnit ^ (3 : Nat))⁻¹ : GoldenIntˣ) : GoldenInt) = ⟨-3, 2⟩ := by
  have h := phiUnit_zpow_neg_three
  rw [show (-3 : Int) = -((3 : Nat) : Int) by norm_num,
    zpow_neg, zpow_natCast] at h
  exact h

@[simp] private theorem phiUnit_pow_four_inv :
    (((phiUnit ^ (4 : Nat))⁻¹ : GoldenIntˣ) : GoldenInt) = ⟨5, -3⟩ := by
  have h := phiUnit_zpow_neg_four
  rw [show (-4 : Int) = -((4 : Nat) : Int) by norm_num,
    zpow_neg, zpow_natCast] at h
  exact h

@[simp] private theorem phiUnit_pow_six_inv :
    (((phiUnit ^ (6 : Nat))⁻¹ : GoldenIntˣ) : GoldenInt) = ⟨13, -8⟩ := by
  have h := phiUnit_zpow_neg_six
  rw [show (-6 : Int) = -((6 : Nat) : Int) by norm_num,
    zpow_neg, zpow_natCast] at h
  exact h

@[simp] private theorem phiUnit_zpow_zero :
    (((phiUnit ^ (0 : Int) : GoldenIntˣ) : GoldenInt)) = ⟨1, 0⟩ := by
  apply GoldenInt.ext <;> rfl

@[simp] private theorem phiUnit_zpow_one :
    (((phiUnit ^ (1 : Int) : GoldenIntˣ) : GoldenInt)) = ⟨0, 1⟩ := by
  simp [phi]

@[simp] private theorem phiUnit_zpow_two :
    (((phiUnit ^ (2 : Int) : GoldenIntˣ) : GoldenInt)) = ⟨1, 1⟩ := by
  rw [show (2 : Int) = ((2 : Nat) : Int) by rfl, zpow_natCast]
  rw [Units.val_pow_eq_pow_val]
  apply GoldenInt.ext <;> norm_num [phi, pow_succ]

@[simp] private theorem phiUnit_zpow_three :
    (((phiUnit ^ (3 : Int) : GoldenIntˣ) : GoldenInt)) = ⟨1, 2⟩ := by
  rw [show (3 : Int) = ((3 : Nat) : Int) by rfl, zpow_natCast]
  rw [Units.val_pow_eq_pow_val]
  apply GoldenInt.ext <;> norm_num [phi, pow_succ]

@[simp] private theorem phiUnit_zpow_four :
    (((phiUnit ^ (4 : Int) : GoldenIntˣ) : GoldenInt)) = ⟨2, 3⟩ := by
  rw [show (4 : Int) = ((4 : Nat) : Int) by rfl, zpow_natCast]
  rw [Units.val_pow_eq_pow_val]
  apply GoldenInt.ext <;> norm_num [phi, pow_succ]

@[simp] private theorem phiUnit_zpow_five :
    (((phiUnit ^ (5 : Int) : GoldenIntˣ) : GoldenInt)) = ⟨3, 5⟩ := by
  rw [show (5 : Int) = ((5 : Nat) : Int) by rfl, zpow_natCast]
  rw [Units.val_pow_eq_pow_val]
  apply GoldenInt.ext <;> norm_num [phi, pow_succ]

@[simp] private theorem phiUnit_zpow_six :
    (((phiUnit ^ (6 : Int) : GoldenIntˣ) : GoldenInt)) = ⟨5, 8⟩ := by
  rw [show (6 : Int) = ((6 : Nat) : Int) by rfl, zpow_natCast]
  rw [Units.val_pow_eq_pow_val]
  apply GoldenInt.ext <;> norm_num [phi, pow_succ]

private noncomputable def ones (positions : Finset Int) : Int →₀ Nat :=
  Finsupp.onFinset positions
    (fun i => if i ∈ positions then 1 else 0) (by simp)

@[simp] private theorem ones_apply (positions : Finset Int) (i : Int) :
    ones positions i = if i ∈ positions then 1 else 0 := by
  rfl

@[simp] private theorem ones_support (positions : Finset Int) :
    (ones positions).support = positions := by
  rw [ones, Finsupp.support_onFinset]
  ext i
  simp

private theorem basePhiValue_ones (positions : Finset Int) :
    basePhiValue (ones positions) =
      Finset.sum positions fun i =>
        (((phiUnit ^ i : GoldenIntˣ) : GoldenInt)) := by
  rw [basePhiValue, ones_support]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ones_apply, if_pos hi]
  simp

private noncomputable def smallDigits : Nat → Int →₀ Nat
  | 0 => ones ∅
  | 1 => ones {0}
  | 2 => ones {1, -2}
  | 3 => ones {2, -2}
  | 4 => ones {2, 0, -2}
  | 5 => ones {3, -1, -4}
  | 6 => ones {3, 1, -4}
  | 7 => ones {4, -4}
  | 8 => ones {4, 0, -4}
  | 9 => ones {4, 1, -2, -4}
  | 10 => ones {4, 2, -2, -4}
  | 11 => ones {4, 2, 0, -2, -4}
  | 12 => ones {5, -1, -3, -6}
  | 13 => ones {5, 1, -3, -6}
  | 14 => ones {5, 2, -3, -6}
  | 15 => ones {5, 2, 0, -3, -6}
  | 16 => ones {5, 3, -1, -6}
  | 17 => ones {5, 3, 1, -6}
  | 18 => ones {6, -6}
  | 19 => ones {6, 0, -6}
  | 20 => ones {6, 1, -2, -6}
  | 21 => ones {6, 2, -2, -6}
  | 22 => ones {6, 2, 0, -2, -6}
  | _ => 0

private theorem smallDigits_binary {N : Nat} (hN : N ≤ 22) (i : Int) :
    smallDigits N i ≤ 1 := by
  interval_cases N <;>
    simp [smallDigits] <;> (try split) <;> omega

private theorem smallDigits_canonical {N : Nat} (hN : N ≤ 22) (i : Int)
    (hi : smallDigits N i = 1) : smallDigits N (i + 1) = 0 := by
  interval_cases N <;>
    simp [smallDigits] at hi ⊢ <;> omega

private theorem smallDigits_value {N : Nat} (hN : N ≤ 22) :
    basePhiValue (smallDigits N) = (N : GoldenInt) := by
  interval_cases N <;>
    simp only [smallDigits, basePhiValue_ones] <;>
    decide

private theorem canonicalDigits_eq_small {N : Nat} (hN : N ≤ 22) :
    canonicalDigits N = smallDigits N := by
  apply bilateral_basePhi_injective
    (canonicalDigits_spec N).1 (canonicalDigits_spec N).2.1
    (smallDigits_binary hN) (smallDigits_canonical hN)
  rw [(canonicalDigits_spec N).2.2, smallDigits_value hN]

private theorem canonicalExpansion_digit_eq_small {N : Nat} (hN : N ≤ 22) :
    canonicalExpansion.digit N = smallDigits N := by
  exact canonicalDigits_eq_small hN

private theorem prefix010_occurs_nine :
    NegativePrefixOccurs canonicalExpansion [false, true, false] 9 := by
  rw [NegativePrefixOccurs]
  constructor
  · refine ⟨by norm_num, -4, ?_, by norm_num⟩
    rw [canonicalExpansion_digit_eq_small (by norm_num)]
    simp [smallDigits]
  · intro i
    rw [negativeDigit, canonicalExpansion_digit_eq_small (by norm_num)]
    fin_cases i <;> norm_num [smallDigits, ones]

private theorem prefix010_occurs_twenty :
    NegativePrefixOccurs canonicalExpansion [false, true, false] 20 := by
  rw [NegativePrefixOccurs]
  constructor
  · refine ⟨by norm_num, -6, ?_, by norm_num⟩
    rw [canonicalExpansion_digit_eq_small (by norm_num)]
    simp [smallDigits]
  · intro i
    rw [negativeDigit, canonicalExpansion_digit_eq_small (by norm_num)]
    fin_cases i <;> norm_num [smallDigits, ones]

private theorem sameNegativeTail_eleven_nine : SameNegativeTail 11 9 := by
  intro i
  rw [negativeDigit, negativeDigit,
    canonicalExpansion_digit_eq_small (N := 11) (by norm_num),
    canonicalExpansion_digit_eq_small (N := 9) (by norm_num)]
  simp only [smallDigits, ones_apply, Finset.mem_insert,
    Finset.mem_singleton]
  have h4 : -(((i + 1 : Nat) : Int)) ≠ 4 := by omega
  have h2 : -(((i + 1 : Nat) : Int)) ≠ 2 := by omega
  have h0 : -(((i + 1 : Nat) : Int)) ≠ 0 := by omega
  have h1 : -(((i + 1 : Nat) : Int)) ≠ 1 := by omega
  simp only [h4, h2, h0, h1, false_or]

private theorem sameNegativeTail_ten_nine : SameNegativeTail 10 9 := by
  intro i
  rw [negativeDigit, negativeDigit,
    canonicalExpansion_digit_eq_small (N := 10) (by norm_num),
    canonicalExpansion_digit_eq_small (N := 9) (by norm_num)]
  simp only [smallDigits, ones_apply, Finset.mem_insert,
    Finset.mem_singleton]
  have h4 : -(((i + 1 : Nat) : Int)) ≠ 4 := by omega
  have h2 : -(((i + 1 : Nat) : Int)) ≠ 2 := by omega
  have h1 : -(((i + 1 : Nat) : Int)) ≠ 1 := by omega
  simp only [h4, h2, h1, false_or]

private theorem sameNegativeTail_symm {M N : Nat} (h : SameNegativeTail M N) :
    SameNegativeTail N M := fun i => (h i).symm

private theorem sameNegativeTail_twenty_two_twenty : SameNegativeTail 22 20 := by
  intro i
  rw [negativeDigit, negativeDigit,
    canonicalExpansion_digit_eq_small (N := 22) (by norm_num),
    canonicalExpansion_digit_eq_small (N := 20) (by norm_num)]
  simp only [smallDigits, ones_apply, Finset.mem_insert,
    Finset.mem_singleton]
  have h6 : -(((i + 1 : Nat) : Int)) ≠ 6 := by omega
  have h2 : -(((i + 1 : Nat) : Int)) ≠ 2 := by omega
  have h0 : -(((i + 1 : Nat) : Int)) ≠ 0 := by omega
  have h1 : -(((i + 1 : Nat) : Int)) ≠ 1 := by omega
  simp only [h6, h2, h0, h1, false_or]

private theorem fiberStart_of_prefix010_and_plus_two {q : Nat}
    (hpositive : 0 < q)
    (hprefix : NegativePrefixOccurs canonicalExpansion [false, true, false] q)
    (htail : SameNegativeTail (q + 2) q) : fiberStart q := by
  have hadmissible :
      AdmissibleNegativePrefix canonicalExpansion [false, true, false] :=
    ⟨q, hpositive, hprefix⟩
  have hfibers := negative_tail_fiber_shape_proved
    (w := [false, true, false]) (by simp) hadmissible
  have hoccurrence :
      q ∈ occurrenceSet canonicalExpansion [false, true, false] :=
    ⟨hpositive, hprefix⟩
  have hhead : negativeDigit canonicalExpansion q 0 = false := by
    simpa using hprefix.2 ⟨0, by norm_num⟩
  obtain ⟨start, hstart, _hunique⟩ :=
    (hfibers q hoccurrence).2 hhead
  have hplusTwo : q + 2 ∈ negativeTailFiber q := by
    exact ⟨by omega, htail⟩
  rw [hstart.2.2] at hplusTwo
  have hstartEq : start = q := by
    rcases hplusTwo with h | h | h <;> omega
  constructor
  · exact ⟨hpositive, fun _ => rfl⟩
  · intro M hM
    rw [hstart.2.2, hstartEq] at hM
    rcases hM with h | h | h <;> omega

private theorem nine_mem_core010 : 9 ∈ Core [false, true, false] := by
  refine ⟨?_, prefix010_occurs_nine⟩
  apply fiberStart_of_prefix010_and_plus_two (by norm_num)
    prefix010_occurs_nine
  simpa using sameNegativeTail_eleven_nine

private theorem twenty_mem_core010 : 20 ∈ Core [false, true, false] := by
  refine ⟨?_, prefix010_occurs_twenty⟩
  apply fiberStart_of_prefix010_and_plus_two (by norm_num)
    prefix010_occurs_twenty
  simpa using sameNegativeTail_twenty_two_twenty

private theorem no_prefix010_below_nine {N : Nat} (hN : N < 9) :
    ¬ NegativePrefixOccurs canonicalExpansion [false, true, false] N := by
  intro hprefix
  interval_cases N
  · simp [NegativePrefixOccurs, reachesNegativeDepth,
      canonicalExpansion_digit_eq_small (N := 0) (by norm_num), smallDigits,
      ones] at hprefix
  · simp [NegativePrefixOccurs, reachesNegativeDepth,
      canonicalExpansion_digit_eq_small (N := 1) (by norm_num), smallDigits,
      ones] at hprefix
  · rcases hprefix.1.2 with ⟨i, hi, hle⟩
    norm_num at hle
    rw [canonicalExpansion_digit_eq_small (N := 2) (by norm_num)] at hi
    simp [smallDigits] at hi
    rcases hi with hi | hi <;> omega
  · rcases hprefix.1.2 with ⟨i, hi, hle⟩
    norm_num at hle
    rw [canonicalExpansion_digit_eq_small (N := 3) (by norm_num)] at hi
    simp [smallDigits] at hi
    rcases hi with hi | hi <;> omega
  · rcases hprefix.1.2 with ⟨i, hi, hle⟩
    norm_num at hle
    rw [canonicalExpansion_digit_eq_small (N := 4) (by norm_num)] at hi
    simp [smallDigits] at hi
    rcases hi with hi | hi | hi <;> omega
  · have hbit := hprefix.2 ⟨0, by norm_num⟩
    rw [negativeDigit,
      canonicalExpansion_digit_eq_small (N := 5) (by norm_num)] at hbit
    norm_num [smallDigits, ones] at hbit
  · have hbit := hprefix.2 ⟨1, by norm_num⟩
    rw [negativeDigit,
      canonicalExpansion_digit_eq_small (N := 6) (by norm_num)] at hbit
    norm_num [smallDigits, ones] at hbit
  · have hbit := hprefix.2 ⟨1, by norm_num⟩
    rw [negativeDigit,
      canonicalExpansion_digit_eq_small (N := 7) (by norm_num)] at hbit
    norm_num [smallDigits, ones] at hbit
  · have hbit := hprefix.2 ⟨1, by norm_num⟩
    rw [negativeDigit,
      canonicalExpansion_digit_eq_small (N := 8) (by norm_num)] at hbit
    norm_num [smallDigits, ones] at hbit

private theorem no_prefix010_twelve_through_nineteen {N : Nat}
    (hNLower : 12 ≤ N) (hNUpper : N ≤ 19) :
    ¬ NegativePrefixOccurs canonicalExpansion [false, true, false] N := by
  intro hprefix
  interval_cases N
  · have hbit := hprefix.2 ⟨0, by norm_num⟩
    rw [negativeDigit,
      canonicalExpansion_digit_eq_small (N := 12) (by norm_num)] at hbit
    norm_num [smallDigits, ones] at hbit
  · have hbit := hprefix.2 ⟨1, by norm_num⟩
    rw [negativeDigit,
      canonicalExpansion_digit_eq_small (N := 13) (by norm_num)] at hbit
    norm_num [smallDigits, ones] at hbit
  · have hbit := hprefix.2 ⟨1, by norm_num⟩
    rw [negativeDigit,
      canonicalExpansion_digit_eq_small (N := 14) (by norm_num)] at hbit
    norm_num [smallDigits, ones] at hbit
  · have hbit := hprefix.2 ⟨1, by norm_num⟩
    rw [negativeDigit,
      canonicalExpansion_digit_eq_small (N := 15) (by norm_num)] at hbit
    norm_num [smallDigits, ones] at hbit
  · have hbit := hprefix.2 ⟨0, by norm_num⟩
    rw [negativeDigit,
      canonicalExpansion_digit_eq_small (N := 16) (by norm_num)] at hbit
    norm_num [smallDigits, ones] at hbit
  · have hbit := hprefix.2 ⟨1, by norm_num⟩
    rw [negativeDigit,
      canonicalExpansion_digit_eq_small (N := 17) (by norm_num)] at hbit
    norm_num [smallDigits, ones] at hbit
  · have hbit := hprefix.2 ⟨1, by norm_num⟩
    rw [negativeDigit,
      canonicalExpansion_digit_eq_small (N := 18) (by norm_num)] at hbit
    norm_num [smallDigits, ones] at hbit
  · have hbit := hprefix.2 ⟨1, by norm_num⟩
    rw [negativeDigit,
      canonicalExpansion_digit_eq_small (N := 19) (by norm_num)] at hbit
    norm_num [smallDigits, ones] at hbit

private theorem core010_lower_bound {q : Nat}
    (hq : q ∈ Core [false, true, false]) : 9 ≤ q := by
  by_contra hq9
  exact no_prefix010_below_nine (by omega) hq.2

private theorem no_core010_strictly_between_nine_twenty {q : Nat}
    (hqLower : 9 < q) (hqUpper : q < 20) :
    q ∉ Core [false, true, false] := by
  intro hq
  by_cases hqTen : q = 10
  · subst q
    have hnine : 9 ∈ negativeTailFiber 10 :=
      ⟨by norm_num, sameNegativeTail_symm sameNegativeTail_ten_nine⟩
    have := hq.1.2 9 hnine
    omega
  · by_cases hqEleven : q = 11
    · subst q
      have hnine : 9 ∈ negativeTailFiber 11 :=
        ⟨by norm_num, sameNegativeTail_symm sameNegativeTail_eleven_nine⟩
      have := hq.1.2 9 hnine
      omega
    · exact no_prefix010_twelve_through_nineteen (by omega) (by omega) hq.2

private theorem frontier_enum_zero_eq_nine {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor [false, true, false] certificate) :
    certificate.enumerate 0 = 9 := by
  have hmono : StrictMono certificate.enumerate :=
    strictMono_nat_of_lt_succ hcertificate.successor_strict
  have hzeroCore : certificate.enumerate 0 ∈ Core [false, true, false] := by
    rw [← hcertificate.range_eq]
    exact ⟨0, rfl⟩
  have hzeroLower := core010_lower_bound hzeroCore
  have hnineRange : 9 ∈ Set.range certificate.enumerate := by
    rw [hcertificate.range_eq]
    exact nine_mem_core010
  obtain ⟨n, hn⟩ := hnineRange
  have hzeroUpper : certificate.enumerate 0 ≤ 9 := by
    rw [← hn]
    exact hmono.monotone (Nat.zero_le n)
  omega

private theorem frontier_enum_one_eq_twenty {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor [false, true, false] certificate) :
    certificate.enumerate 1 = 20 := by
  have hmono : StrictMono certificate.enumerate :=
    strictMono_nat_of_lt_succ hcertificate.successor_strict
  have hzero := frontier_enum_zero_eq_nine hcertificate
  have honeCore : certificate.enumerate 1 ∈ Core [false, true, false] := by
    rw [← hcertificate.range_eq]
    exact ⟨1, rfl⟩
  have honeLower : 20 ≤ certificate.enumerate 1 := by
    by_contra hlt
    exact no_core010_strictly_between_nine_twenty
      (by simpa [hzero] using hcertificate.successor_strict 0)
      (by omega) honeCore
  have htwentyRange : 20 ∈ Set.range certificate.enumerate := by
    rw [hcertificate.range_eq]
    exact twenty_mem_core010
  obtain ⟨n, hn⟩ := htwentyRange
  have hnPositive : 0 < n := by
    by_contra hnZero
    have : n = 0 := by omega
    subst n
    omega
  have honeUpper : certificate.enumerate 1 ≤ 20 := by
    rw [← hn]
    exact hmono.monotone hnPositive
  omega

private def obstructionStartCertificate : Bool → FrontierPhaseCertificate
  | false => ⟨.F0o, 4, 3⟩
  | true => ⟨.F1o, 7, 4⟩

private def obstructionNextCertificate : FrontierPhaseCertificate → Bool →
    FrontierPhaseCertificate
  | ⟨.F0o, a, b⟩, false => ⟨.F0e, a + b, a⟩
  | ⟨.F0o, a, b⟩, true => ⟨.G1e, 2 * a + b, a + b⟩
  | ⟨.F1o, a, b⟩, false => ⟨.F0e, a, b⟩
  | ⟨.F1o, a, b⟩, true => ⟨.F1o, a, b⟩
  | ⟨.F0e, a, b⟩, false => ⟨.F0o, a + b, a⟩
  | ⟨.F0e, a, b⟩, true => ⟨.F1o, 2 * a + b, a + b⟩
  | ⟨.G1e, a, b⟩, false => ⟨.G0o, a, b⟩
  | ⟨.G1e, a, b⟩, true => ⟨.G1e, a, b⟩
  | ⟨.G0o, a, b⟩, false => ⟨.H0e, a + b, a⟩
  | ⟨.G0o, a, b⟩, true => ⟨.G1e, 2 * a + b, a + b⟩
  | ⟨.H0e, a, b⟩, false => ⟨.G0o, a + b, a⟩
  | ⟨.H0e, a, b⟩, true => ⟨.F1o, 2 * a + b, a + b⟩

private def obstructionPhaseCertificate? :
    List Bool → Option FrontierPhaseCertificate
  | [] => none
  | bit :: tail =>
      some (tail.foldl obstructionNextCertificate
        (obstructionStartCertificate bit))

private theorem obstruction_transition_evaluates
    {before after : FrontierPhaseCertificate} {bit : Bool}
    (h : FrontierPhaseTransition before bit after) :
    obstructionNextCertificate before bit = after := by
  cases h <;> rfl

private theorem obstruction_phase_machine_nonempty {w : List Bool}
    {c : FrontierPhaseCertificate} (h : PrefixPhaseMachineFor w c) : w ≠ [] := by
  induction h <;> simp_all

private theorem obstruction_phase_append_singleton {w : List Bool}
    (hw : w ≠ []) (bit : Bool) :
    obstructionPhaseCertificate? (w ++ [bit]) =
      (obstructionPhaseCertificate? w).map fun c =>
        obstructionNextCertificate c bit := by
  cases w with
  | nil => contradiction
  | cons head tail =>
      simp [obstructionPhaseCertificate?, List.foldl_append]

private theorem obstruction_phase_machine_evaluates {w : List Bool}
    {c : FrontierPhaseCertificate} (h : PrefixPhaseMachineFor w c) :
    obstructionPhaseCertificate? w = some c := by
  induction h with
  | zero => rfl
  | one => rfl
  | step hprefix transition ih =>
      rw [obstruction_phase_append_singleton
        (obstruction_phase_machine_nonempty hprefix)]
      rw [ih]
      simp [obstruction_transition_evaluates transition]

private theorem phase_machine_010_eq {c : FrontierPhaseCertificate}
    (h : PrefixPhaseMachineFor [false, true, false] c) :
    c = ⟨.G0o, 11, 7⟩ := by
  have heval := obstruction_phase_machine_evaluates h
  have : some (⟨.G0o, 11, 7⟩ : FrontierPhaseCertificate) = some c := by
    simpa [obstructionPhaseCertificate?, obstructionStartCertificate,
      obstructionNextCertificate] using heval
  exact (Option.some.inj this).symm

/-- The current phase/family-letter selector is false for the first `010`
frontier step: the canonical core moves from `9` to `20`, while phase `G0o`
selects the smaller Lucas parameter `7` at input zero. -/
theorem frontierGapPhase_not_of_prefix010 {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor [false, true, false] certificate) :
    ¬ FrontierGapPhase certificate := by
  intro hgap
  have hphaseCertificate := phase_machine_010_eq hcertificate.phase_machine
  have hzero := frontier_enum_zero_eq_nine hcertificate
  have hone := frontier_enum_one_eq_twenty hcertificate
  have hfirstGap := hgap 0
  simp [FrontierReturnWord.gap, FrontierReturnWord.phase,
    FrontierReturnWord.b, hphaseCertificate,
    hzero, hone, frontierFamily, familyLetter] at hfirstGap

/-- Consequently the frozen phase-enriched edge trace also cannot exist for
the valid `010` core enumeration. -/
theorem phaseEnrichedCoreTrace_not_of_prefix010
    {certificate : FrontierReturnWord}
    (hcertificate : FrontierReturnWordFor [false, true, false] certificate) :
    ¬ PhaseEnrichedCoreTrace [false, true, false] certificate := by
  intro htrace
  exact frontierGapPhase_not_of_prefix010 hcertificate
    (phase_enriched_core_trace_gap_phase hcertificate htrace)

end

end D5.X_Frontier.BasePhiNegativePrefixTrident
