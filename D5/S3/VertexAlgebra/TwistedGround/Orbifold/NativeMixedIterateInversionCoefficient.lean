/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedIterateInversionCoefficient
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedIterateInversionCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite detector coefficient inversion for the native mixed Leech iterate. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairSkew
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairOrdinaryWard
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeDetectorTranslation

/-! Inversion at a single lattice energy for the native mixed Leech iterate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedIterateInversionCoefficient

open ActualLeechHyperbolic (leechData leech_spec)
open Complex (I)
open LatticeGeneratingFieldLocality (Carrier)
open LatticePositiveEnergy (grade)
open LatticeHalfFockGradedTrace (actualGrade)
open LatticeSugawaraCurrents (sugawaraMode gramComplex)
open NativeOddTwistedIntertwiner (Twisted leechUnit OddCarrier oddTranslation)
open NativeOddUpperRightSkew (lowering mixedPairing_lowering_tail)
open NativeMixedPairField (mu mu_coeff_of_grade mu_coeff_even_zero)
open NativeMixedPairState (mixedPairState_grade mixedPairWeight mixedPairState_truncation)
open NativeMixedPairSkew (mu_skew_of_grade swapInput)
open OriginalSkewAdjoints (actual_corrected_adjoint_of_grade)
open NativeDetectorTranslation (detector detector_apply detector_divided_translation)
open NativeMixedPairOrdinaryWard (mu_coeff_L1_ordinary)
open private actualGrade_eigen lowering_pow_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private lowering_eigen from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

local notation "ℒ" => leechData
local notation "V" => sugawaraMode ℒ (gramComplex ℒ)⁻¹ 1
local notation "T" => lowering ℒ leechUnit
local notation "D₋" => oddTranslation ℒ
local notation "B" => detector ℒ leechUnit
private abbrev State (s : Bool) := Twisted ℒ leechUnit s
private abbrev Odd := OddCarrier ℒ

private abbrev weight (M : ℕ) : ℤ := 3 + (M : ℤ)
private abbrev pairExp (mP mQ N : ℤ) : ℤ := 2 * N - mP - mQ
private abbrev detectorExp (mR mS N : ℤ) : ℤ := mS - mR - 2 * N
private abbrev invFact (n : ℕ) : ℂ := (n.factorial : ℂ)⁻¹
private abbrev sign (n : ℕ) : ℂ := (-1 : ℂ) ^ n

/-- The actual A coefficient at lattice energy N, evaluated at its selected signed mode. -/
def aCoeff (s t : Bool) (mP mQ mR mS : ℤ) (N : ℕ)
    (P : State s) (Q : State (!s)) (R : State t) (S : State (!t)) : ℂ :=
  B (detectorExp mR mS (N : ℤ)) R.val S.val
    ((mu s P).coeff (pairExp mP mQ (N : ℤ)) Q).val

private theorem swapped_val {s : Bool} (P : State s) : (swapInput P).val = P.val := by
  cases s <;> rfl

private theorem swapped_grade {s : Bool} {M : ℕ} {P : State s}
    (hP : P.val ∈ actualGrade ℒ leechUnit M) :
    (swapInput P).val ∈ actualGrade ℒ leechUnit M := by
  cases s <;> exact hP

private theorem swapped_twice (s : Bool) (e : ℤ) (P : State s) (Q : State (!s)) :
    (mu (!(!s)) (swapInput P)).coeff e (swapInput Q) = (mu s P).coeff e Q := by
  cases s <;> rfl

private theorem descend_grade {s : Bool} {M n : ℕ} {P : State s}
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hn : 2 * n ≤ M) :
    ((T s ^ n) P).val ∈ actualGrade ℒ leechUnit (M - 2 * n) := by
  rw [lowering_pow_val, actualGrade_eigen]
  have he := (actualGrade_eigen ℒ leechUnit M P.val).mp hP
  have hc : (((M - 2 * n : ℕ) : ℂ)) =
      (((M : ℤ) - 2 * (n : ℤ) : ℤ) : ℂ) := by
    exact_mod_cast (show ((M - 2 * n : ℕ) : ℤ) = (M : ℤ) - 2 * (n : ℤ) by omega)
  rw [hc]
  exact lowering_eigen ℒ leechUnit (M : ℤ) P.val
    (by simpa only [Int.cast_natCast] using he) n

private theorem pair_grade (s : Bool) (M K : ℕ) (d : ℤ) (P : State s) (Q : State (!s))
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K) :
    ((mu s P).coeff (pairExp (weight M) (weight K) d) Q).val ∈ grade ℒ d := by
  let e := pairExp (weight M) (weight K) d
  change ((mu s P).coeff e Q).val ∈ grade ℒ d
  by_cases he : Even e
  · rw [mu_coeff_even_zero s e P Q he]
    exact (grade ℒ d).zero_mem
  · obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp he
    let m : ℤ := -k - 2
    have hs : e = -2 * m - 3 := by dsimp [m]; omega
    have hd : mixedPairWeight M K m = d := by
      dsimp [e, pairExp, weight] at hs
      unfold mixedPairWeight
      omega
    rw [hs, mu_coeff_of_grade s M K m P Q hP hQ, ← hd]
    exact mixedPairState_grade s M K m P Q

private theorem pair_nonpositive_zero (s : Bool) (M K : ℕ) (d : ℤ)
    (P : State s) (Q : State (!s)) (hP : P.val ∈ actualGrade ℒ leechUnit M)
    (hQ : Q.val ∈ actualGrade ℒ leechUnit K) (hd : d ≤ 0) :
    (mu s P).coeff (pairExp (weight M) (weight K) d) Q = 0 := by
  let e := pairExp (weight M) (weight K) d
  change (mu s P).coeff e Q = 0
  by_cases he : Even e
  · exact mu_coeff_even_zero s e P Q he
  · obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp he
    let m : ℤ := -k - 2
    have hs : e = -2 * m - 3 := by dsimp [m]; omega
    rw [hs, mu_coeff_of_grade s M K m P Q hP hQ]
    apply mixedPairState_truncation
    dsimp [e, pairExp, weight] at hs
    omega

private theorem phase_step (e : ℤ) (h : ℕ) :
    I ^ (e + 2 * (h : ℤ)) = I ^ e * sign h := by
  rw [zpow_add₀ Complex.I_ne_zero, zpow_mul, zpow_natCast,
    show I ^ (2 : ℤ) = -1 by exact (zpow_natCast I 2).trans Complex.I_sq]

private theorem sign_square (h : ℕ) : sign h * sign h = 1 := by
  rw [← mul_pow]
  norm_num

private theorem negative_phase_step (e : ℤ) (h : ℕ) :
    I ^ (e - 2 * (h : ℤ)) = I ^ e * sign h := by
  have h' := phase_step (e - 2 * (h : ℤ)) h
  rw [sub_add_cancel] at h'
  rw [h', mul_assoc, sign_square, mul_one]

private theorem lower_skew_on_grade (s : Bool) (M K n : ℕ) (P : State s) (Q : State (!s))
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K) :
    I ^ pairExp (weight M) (weight K) (n : ℤ) •
      (mu s P).coeff (pairExp (weight M) (weight K) (n : ℤ)) Q =
      sign (3 + K) • ∑ h ∈ Finset.range (n + 1), (sign h * invFact h) •
        (D₋ ^ h) ((mu (!s) Q).coeff (pairExp (weight K) (weight M) ((n : ℤ) - h))
          (swapInput P)) := by
  let e := pairExp (weight M) (weight K) (n : ℤ)
  let term (h : ℕ) : Odd := (I ^ (-(e - 2 * (h : ℤ))) * invFact h) •
    (D₋ ^ h) ((mu (!s) Q).coeff (e - 2 * (h : ℤ)) (swapInput P))
  have rangeSupport : Function.support term ⊆ (Finset.range (n + 1) : Set ℕ) := by
    intro h hh
    apply Finset.mem_range.mpr
    by_contra! hout
    apply hh
    have he : e - 2 * (h : ℤ) = pairExp (weight K) (weight M) ((n : ℤ) - h) := by
      dsimp [e, pairExp]
      ring
    dsimp only [term]
    rw [he, pair_nonpositive_zero (!s) K M _ Q (swapInput P) hQ
      (swapped_grade hP) (by omega), map_zero, smul_zero]
  have skew := mu_skew_of_grade false s M K e P Q hP hQ
  change (mu s P).coeff e Q = sign (3 + K) • ∑ᶠ h, term h at skew
  change I ^ e • (mu s P).coeff e Q = _
  rw [skew, finsum_eq_sum_of_support_subset term rangeSupport, smul_comm (I ^ e),
    Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  have he : e - 2 * (h : ℤ) = pairExp (weight K) (weight M) ((n : ℤ) - h) := by
    dsimp [e, pairExp]
    ring
  have hphase : I ^ e * I ^ (-(e - 2 * (h : ℤ))) = sign h := by
    rw [← zpow_add₀ Complex.I_ne_zero,
      show e + -(e - 2 * (h : ℤ)) = 0 + 2 * (h : ℤ) by omega, phase_step,
      zpow_zero, one_mul]
  dsimp only [term]
  rw [smul_smul, ← mul_assoc, hphase, he]

private theorem alternating_factorials (r : ℕ) :
    (∑ k ∈ Finset.range (r + 1), invFact k * (sign (r - k) * invFact (r - k))) =
      (0 : ℂ) ^ r := by
  calc
    _ = (∑ k ∈ Finset.range (r + 1), (1 : ℂ) ^ k * (-1 : ℂ) ^ (r - k) *
        (r.choose k : ℂ)) / (r.factorial : ℂ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Nat.cast_choose ℂ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
      have hf (a : ℕ) : (a.factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero a
      simp only [one_pow, one_mul]
      field_simp [hf]
    _ = _ := by
      rw [← add_pow, show (1 : ℂ) + -1 = 0 by norm_num]
      cases r <;> simp

private theorem triangular_cancel (n : ℕ) (f : ℕ → Odd) :
    (∑ k ∈ Finset.range (n + 1), ∑ h ∈ Finset.range (n - k + 1),
      (invFact k * (sign h * invFact h)) • f (k + h)) = f 0 := by
  let term (k h : ℕ) := (invFact k * (sign h * invFact h)) • f (k + h)
  calc
    _ = ∑ k ∈ Finset.range (n + 1), ∑ h ∈ Finset.range (n + 1 - k), term k h := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn := Finset.mem_range.mp hk
      rw [show n - k + 1 = n + 1 - k by omega]
    _ = ∑ r ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (r + 1), term k (r - k) :=
      (Finset.sum_range_diag_flip (n + 1) term).symm
    _ = ∑ r ∈ Finset.range (n + 1), (0 : ℂ) ^ r • f r := by
      apply Finset.sum_congr rfl
      intro r _
      rw [← alternating_factorials, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [term]
      rw [Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
    _ = f 0 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro r _ hr
        simp [zero_pow hr]
      · simp

/-- Lower skew in first-input phase convention, obtained by expanding the
swapped lower branch and moving its finite translation to the other side. -/
private theorem lower_skew_first_phase (s : Bool) (M K n : ℕ)
    (P : State s) (Q : State (!s))
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K) :
    (mu s P).coeff (pairExp (weight M) (weight K) (n : ℤ)) Q =
      ∑ h ∈ Finset.range (n + 1),
        (sign (3 + M) * I ^ pairExp (weight M) (weight K) (n : ℤ) *
          (sign h * invFact h)) •
        (D₋ ^ h) ((mu (!s) Q).coeff (pairExp (weight K) (weight M) ((n : ℤ) - h))
          (swapInput P)) := by
  let e := pairExp (weight M) (weight K) (n : ℤ)
  let a (h : ℕ) := (mu s P).coeff (e - 2 * (h : ℤ)) Q
  let b (h : ℕ) := (mu (!s) Q).coeff (e - 2 * (h : ℤ)) (swapInput P)
  have swapped (k : ℕ) (hk : k ≤ n) :
      I ^ (e - 2 * (k : ℤ)) • b k =
        sign (3 + M) • ∑ h ∈ Finset.range (n - k + 1),
          (sign h * invFact h) • (D₋ ^ h) (a (k + h)) := by
    have law := lower_skew_on_grade (!s) K M (n - k) Q (swapInput P) hQ (swapped_grade hP)
    simp only [swapped_twice s] at law
    have he : pairExp (weight K) (weight M) ((n - k : ℕ) : ℤ) =
        e - 2 * (k : ℤ) := by dsimp [e, pairExp]; omega
    rw [he] at law
    refine law.trans (congrArg (fun x : Odd => sign (3 + M) • x) ?_)
    apply Finset.sum_congr rfl
    intro h _
    have heh : pairExp (weight M) (weight K) (((n - k : ℕ) : ℤ) - h) =
        e - 2 * ((k + h : ℕ) : ℤ) := by dsimp [e, pairExp]; omega
    rw [heh]
  have combine :
      (∑ k ∈ Finset.range (n + 1),
        invFact k • (D₋ ^ k) (sign (3 + M) • (I ^ (e - 2 * (k : ℤ)) • b k))) = a 0 := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1), ∑ h ∈ Finset.range (n - k + 1),
          (invFact k * (sign h * invFact h)) • (D₋ ^ (k + h)) (a (k + h)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [swapped k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), smul_smul,
          sign_square, one_smul, map_sum, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro h _
        rw [map_smul, smul_smul, pow_add, Module.End.mul_apply]
      _ = a 0 := by
        simpa only [pow_zero, Module.End.one_apply] using
          triangular_cancel n (fun h => (D₋ ^ h) (a h))
  calc
    _ = a 0 := by simp [a, e]
    _ = _ := combine.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      have he : e - 2 * (h : ℤ) = pairExp (weight K) (weight M) ((n : ℤ) - h) := by
        dsimp [e, pairExp]
        ring
      simp only [map_smul, smul_smul, b]
      rw [negative_phase_step, he]
      congr 1
      ac_rfl

private theorem odd_translation_pow_val (h : ℕ) (a : Odd) :
    ((D₋ ^ h) a).val = (LatticeSugawaraConformal.translation ℒ ^ h) a.val := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [pow_succ' D₋, Module.End.mul_apply]
    change LatticeSugawaraConformal.translation ℒ ((D₋ ^ h) a).val = _
    rw [ih, pow_succ' (LatticeSugawaraConformal.translation ℒ), Module.End.mul_apply]

private theorem lower_detector (s t : Bool) (M K n : ℕ) (q : ℤ)
    (P : State s) (Q : State (!s)) (R : State t) (S : State (!t))
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K) :
    B q S.val R.val ((mu s P).coeff (pairExp (weight M) (weight K) (n : ℤ)) Q).val =
      (sign (3 + M) * I ^ pairExp (weight M) (weight K) (n : ℤ)) *
        ∑ h ∈ Finset.range (n + 1), sign h * Ring.choose ((q : ℂ) / 2 + (h : ℂ)) h *
          B (q + 2 * (h : ℤ)) S.val R.val
            ((mu (!s) Q).coeff (pairExp (weight K) (weight M) ((n : ℤ) - h))
              (swapInput P)).val := by
  have law := congrArg (fun a : Odd => B q S.val R.val a.val)
    (lower_skew_first_phase s M K n P Q hP hQ)
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, smul_eq_mul,
    odd_translation_pow_val] at law
  rw [law, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  let a := ((mu (!s) Q).coeff
    (pairExp (weight K) (weight M) ((n : ℤ) - h)) (swapInput P)).val
  have ht := detector_divided_translation ℒ leechUnit (q + 2 * (h : ℤ)) S.val R.val a h
  rw [show q + 2 * (h : ℤ) - 2 * (h : ℤ) = q by omega] at ht
  have hx : (((q + 2 * (h : ℤ) : ℤ) : ℂ) / 2) = (q : ℂ) / 2 + (h : ℂ) := by
    push_cast
    ring
  rw [hx] at ht
  change
    (sign (3 + M) * I ^ pairExp (weight M) (weight K) (n : ℤ) *
      (sign h * invFact h)) *
      B q S.val R.val ((LatticeSugawaraConformal.translation ℒ ^ h) a) =
    (sign (3 + M) * I ^ pairExp (weight M) (weight K) (n : ℤ)) *
      (sign h * Ring.choose ((q : ℂ) / 2 + (h : ℂ)) h *
        B (q + 2 * (h : ℤ)) S.val R.val a)
  calc
    _ = (sign (3 + M) * I ^ pairExp (weight M) (weight K) (n : ℤ)) * sign h *
        (invFact h * B q S.val R.val ((LatticeSugawaraConformal.translation ℒ ^ h) a)) :=
      by ring
    _ = _ := by rw [ht]; ring

private theorem ward_bpz (s t : Bool) (M K N : ℕ) (mR mS : ℤ)
    (P : State s) (Q : State (!s)) (R : State t) (S : State (!t))
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K) :
    aCoeff s t (weight M) (weight K) mR mS N P Q R S =
      sign N * ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (N - j + 1),
        ∑ l ∈ Finset.range (N - j - i + 1),
          (Ring.choose ((N : ℂ) + (((weight M : ℤ) : ℂ) - ((weight K : ℤ) : ℂ)) / 2 -
            (i : ℂ) - 1) l / ((i.factorial : ℂ) * (j.factorial : ℂ))) *
          B (detectorExp mS mR ((N - j - i - l : ℕ) : ℤ)) S.val R.val
            ((mu s ((T s ^ i) P)).coeff
              (pairExp (weight M) (weight K) (N : ℤ) - 2 * (l : ℤ)) ((T (!s) ^ j) Q)).val := by
  let e := pairExp (weight M) (weight K) (N : ℤ)
  let q := detectorExp mR mS (N : ℤ)
  let a := ((mu s P).coeff e Q).val
  have ha : a ∈ grade ℒ (N : ℤ) := pair_grade s M K (N : ℤ) P Q hP hQ
  have bpz := actual_corrected_adjoint_of_grade ℒ leechUnit leech_spec.2.2.1
    (N : ℤ) q a ha R.val S.val
  simp only [Int.toNat_natCast, zpow_natCast] at bpz
  let G (j i l : ℕ) := (Ring.choose
      ((N : ℂ) + (((weight M : ℤ) : ℂ) - ((weight K : ℤ) : ℂ)) / 2 - (i : ℂ) - 1) l /
        ((i.factorial : ℂ) * (j.factorial : ℂ))) *
      B (detectorExp mS mR ((N - j - i - l : ℕ) : ℤ)) S.val R.val
        ((mu s ((T s ^ i) P)).coeff (e - 2 * (l : ℤ)) ((T (!s) ^ j) Q)).val
  change B q R.val S.val a =
    sign N * ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (N - j + 1),
      ∑ l ∈ Finset.range (N - j - i + 1), G j i l
  calc
    _ = sign N * ∑ n ∈ Finset.range (N + 1),
        B (detectorExp mS mR ((N - n : ℕ) : ℤ)) S.val R.val
          (invFact n • (V ^ n) a) := by
      simp only [map_smul, smul_eq_mul, detector_apply]
      rw [bpz]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have hq : -q - 4 * (N : ℤ) + 2 * (n : ℤ) =
          detectorExp mS mR ((N - n : ℕ) : ℤ) := by dsimp [q, detectorExp]; omega
      rw [hq, (ActualPairingSymmetry.actualForm_symmetric ℒ leechUnit).eq R.val]
    _ = sign N * ∑ n ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (n + 1),
        ∑ i ∈ Finset.range (n - j + 1), G j i (n - j - i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [show invFact n • (V ^ n) a = _ from mu_coeff_L1_ordinary s M n e P Q hP]
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hN : N - j - i - (n - j - i) = N - n := by omega
      have hx : 3 + (M : ℂ) + (e : ℂ) / 2 - (i : ℂ) - 1 =
          (N : ℂ) + (((weight M : ℤ) : ℂ) - ((weight K : ℤ) : ℂ)) / 2 - (i : ℂ) - 1 := by
        dsimp [e, pairExp, weight]
        push_cast
        ring
      simp only [G, hN, hx]
    _ = _ := by
      congr 1
      rw [Finset.sum_range_diag_flip (N + 1)
        (fun j p => ∑ i ∈ Finset.range (p + 1), G j i (p - i))]
      apply Finset.sum_congr rfl
      intro j hj
      have hjN := Finset.mem_range.mp hj
      rw [show N + 1 - j = N - j + 1 by omega,
        Finset.sum_range_diag_flip (N - j + 1) (G j)]
      apply Finset.sum_congr rfl
      intro i hi
      have hiN := Finset.mem_range.mp hi
      rw [show N - j + 1 - i = N - j - i + 1 by omega]

private theorem original_phase (M K N l : ℕ) :
    sign N * (sign (3 + M) *
      I ^ (pairExp (weight M) (weight K) (N : ℤ) - 2 * (l : ℤ))) =
        I ^ (weight M - weight K) * sign l := by
  have sign_as_I (n : ℕ) : sign n = I ^ (2 * (n : ℤ)) := by
    simpa only [zero_add, zpow_zero, one_mul] using (phase_step 0 n).symm
  have h4 : I ^ (4 : ℤ) = 1 := (zpow_natCast I 4).trans Complex.I_pow_four
  rw [negative_phase_step, ← mul_assoc, ← mul_assoc, sign_as_I N, sign_as_I (3 + M),
    ← zpow_add₀ Complex.I_ne_zero, ← zpow_add₀ Complex.I_ne_zero]
  have hex :
      2 * (N : ℤ) + 2 * ((3 + M : ℕ) : ℤ) + pairExp (weight M) (weight K) (N : ℤ) =
        (weight M - weight K) + 4 * (N : ℤ) := by dsimp [pairExp, weight]; omega
  rw [hex, zpow_add₀ Complex.I_ne_zero, zpow_mul I 4 (N : ℤ), h4, one_zpow, mul_one]

private theorem descend_sign (M i : ℕ) (hi : 2 * i ≤ M) :
    sign (3 + (M - 2 * i)) = sign (3 + M) := by
  have he : 3 + M = 3 + (M - 2 * i) + 2 * i := by omega
  conv_rhs => rw [he]
  simp only [pow_add, pow_mul]
  norm_num

private theorem reflect_choose (x : ℂ) (k : ℕ) :
    sign k * Ring.choose x k = Ring.choose (-x + (k : ℂ) - 1) k := by
  have h := Ring.choose_neg (-x) k
  rw [neg_neg] at h
  rw [h]
  simp only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]
  rw [← mul_assoc, ← mul_pow]
  norm_num

private theorem triangular_vandermonde (n : ℕ) (α β : ℂ) (f : ℕ → ℂ) :
    (∑ l ∈ Finset.range (n + 1), ∑ h ∈ Finset.range (n - l + 1),
      sign (l + h) * Ring.choose α l * Ring.choose (β - ((n - l - h : ℕ) : ℂ)) h *
        f (l + h)) =
      ∑ L ∈ Finset.range (n + 1), Ring.choose ((n : ℂ) - α - β - 1) L * f L := by
  let term (l h : ℕ) := sign (l + h) * Ring.choose α l *
    Ring.choose (β - ((n - l - h : ℕ) : ℂ)) h * f (l + h)
  calc
    _ = ∑ l ∈ Finset.range (n + 1), ∑ h ∈ Finset.range (n + 1 - l), term l h := by
      apply Finset.sum_congr rfl
      intro l hl
      have hln := Finset.mem_range.mp hl
      rw [show n - l + 1 = n + 1 - l by omega]
    _ = ∑ L ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (L + 1), term l (L - l) :=
      (Finset.sum_range_diag_flip (n + 1) term).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro L hL
      have hLn : L ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hL)
      let βL := β - ((n - L : ℕ) : ℂ)
      have vand := Ring.add_choose_eq (R := ℂ) (r := α) (s := βL) L (Commute.all _ _)
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at vand
      have hx : -(α + βL) + (L : ℂ) - 1 = (n : ℂ) - α - β - 1 := by
        dsimp [βL]
        rw [Nat.cast_sub hLn]
        ring
      rw [← hx, ← reflect_choose, vand, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      have hlL : l ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      dsimp only [term, βL]
      rw [Nat.add_sub_of_le hlL, show n - l - (L - l) = n - L by omega]
      ring

private theorem swap_zero {s : Bool} : swapInput (0 : State s) = 0 := by
  cases s <;> rfl

/-- Finite native detector inversion at the original lattice energy N.
The signed doubled weights of the exchanged inputs descend by 2j and 2i.
The three nested ranges enumerate exactly i + j + L ≤ N. -/
theorem aCoeff_inversion (s t : Bool) (M K H J N : ℕ)
    (P : State s) (Q : State (!s)) (R : State t) (S : State (!t))
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (_hR : R.val ∈ actualGrade ℒ leechUnit H) (_hS : S.val ∈ actualGrade ℒ leechUnit J) :
    aCoeff s t (weight M) (weight K) (weight H) (weight J) N P Q R S =
      I ^ (weight M - weight K) *
        ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (N - j + 1),
          ∑ L ∈ Finset.range (N - j - i + 1),
            (Ring.choose ((((weight J : ℤ) : ℂ) - ((weight H : ℤ) : ℂ) -
              ((weight M : ℤ) : ℂ) + ((weight K : ℤ) : ℂ)) / 2 - (j : ℂ)) L /
              ((i.factorial : ℂ) * (j.factorial : ℂ))) *
              aCoeff (!s) (!t) (weight K - 2 * (j : ℤ)) (weight M - 2 * (i : ℤ))
                (weight J) (weight H) (N - j - i - L)
                ((T (!s) ^ j) Q) (swapInput ((T s ^ i) P)) S (swapInput R) := by
  let mP := weight M
  let mQ := weight K
  let mR := weight H
  let mS := weight J
  let e := pairExp mP mQ (N : ℤ)
  let phase := I ^ (mP - mQ)
  let γ : ℂ := ((mS : ℂ) - (mR : ℂ)) / 2
  let δ : ℂ := ((mP : ℂ) - (mQ : ℂ)) / 2
  let α (i : ℕ) := (N : ℂ) + δ - (i : ℂ) - 1
  let f (j i L : ℕ) := aCoeff (!s) (!t) (mQ - 2 * (j : ℤ)) (mP - 2 * (i : ℤ)) mS mR
    (N - j - i - L) ((T (!s) ^ j) Q) (swapInput ((T s ^ i) P)) S (swapInput R)
  let g (j i l : ℕ) := B (detectorExp mS mR ((N - j - i - l : ℕ) : ℤ)) S.val R.val
    ((mu s ((T s ^ i) P)).coeff (e - 2 * (l : ℤ)) ((T (!s) ^ j) Q)).val
  let target (j : ℕ) := ((mS : ℂ) - (mR : ℂ) - (mP : ℂ) + (mQ : ℂ)) / 2 - (j : ℂ)
  change aCoeff s t mP mQ mR mS N P Q R S =
    phase * ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (N - j + 1),
      ∑ L ∈ Finset.range (N - j - i + 1),
        (Ring.choose (target j) L / ((i.factorial : ℂ) * (j.factorial : ℂ))) * f j i L
  calc
    _ = sign N * ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (N - j + 1),
        ∑ l ∈ Finset.range (N - j - i + 1),
          (Ring.choose (α i) l / ((i.factorial : ℂ) * (j.factorial : ℂ))) * g j i l :=
      ward_bpz s t M K N mR mS P Q R S hP hQ
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      apply Finset.sum_congr rfl
      intro i hi
      have hiN : i ≤ N - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      let n := N - j - i
      let Pᵢ := (T s ^ i) P
      let Qⱼ := (T (!s) ^ j) Q
      by_cases hiM : 2 * i ≤ M
      swap
      · have hz : (T s ^ i) P = 0 := mixedPairing_lowering_tail s M P hP i (by omega)
        have hg (l : ℕ) : g j i l = 0 := by simp [g, hz]
        have hf (L : ℕ) : f j i L = 0 := by simp [f, aCoeff, hz, swap_zero]
        simp only [hg, hf, mul_zero, Finset.sum_const_zero]
      by_cases hjK : 2 * j ≤ K
      swap
      · have hz : (T (!s) ^ j) Q = 0 := mixedPairing_lowering_tail (!s) K Q hQ j (by omega)
        have hg (l : ℕ) : g j i l = 0 := by simp [g, hz]
        have hf (L : ℕ) : f j i L = 0 := by simp [f, aCoeff, hz]
        simp only [hg, hf, mul_zero, Finset.sum_const_zero]
      have hPᵢ := descend_grade hP hiM
      have hQⱼ := descend_grade hQ hjK
      let d := (i.factorial : ℂ) * (j.factorial : ℂ)
      let term (l h : ℕ) := sign (l + h) * Ring.choose (α i) l *
        Ring.choose (-γ - ((n - l - h : ℕ) : ℂ)) h * f j i (l + h)
      change (∑ l ∈ Finset.range (n + 1),
          sign N * ((Ring.choose (α i) l / d) * g j i l)) =
        ∑ L ∈ Finset.range (n + 1), phase * ((Ring.choose (target j) L / d) * f j i L)
      calc
        _ = (phase / d) * ∑ l ∈ Finset.range (n + 1),
            ∑ h ∈ Finset.range (n - l + 1), term l h := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          have hln : l ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
          let q := detectorExp mS mR ((n - l : ℕ) : ℤ)
          let el := pairExp (weight (M - 2 * i)) (weight (K - 2 * j)) ((n - l : ℕ) : ℤ)
          have hel : el = e - 2 * (l : ℤ) := by
            dsimp [el, e, n, mP, mQ, pairExp, weight]
            omega
          have sk := lower_detector s t (M - 2 * i) (K - 2 * j) (n - l) q
            Pᵢ Qⱼ R S hPᵢ hQⱼ
          change B q S.val R.val ((mu s Pᵢ).coeff el Qⱼ).val = _ at sk
          have hg : g j i l = B q S.val R.val ((mu s Pᵢ).coeff el Qⱼ).val := by
            rw [hel]
          rw [hg, sk]
          have ex :
              (∑ h ∈ Finset.range (n - l + 1),
                sign h * Ring.choose ((q : ℂ) / 2 + (h : ℂ)) h *
                  B (q + 2 * (h : ℤ)) S.val R.val ((mu (!s) Qⱼ).coeff
                    (pairExp (weight (K - 2 * j)) (weight (M - 2 * i)) (((n - l : ℕ) : ℤ) - h))
                    (swapInput Pᵢ)).val) =
              ∑ h ∈ Finset.range (n - l + 1),
                sign h * Ring.choose (-γ - ((n - l - h : ℕ) : ℂ)) h * f j i (l + h) := by
            apply Finset.sum_congr rfl
            intro h hh
            have hhN : h ≤ n - l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
            have hq : q + 2 * (h : ℤ) = detectorExp mS mR ((n - l - h : ℕ) : ℤ) := by
              dsimp [q, detectorExp]
              omega
            have hx : (q : ℂ) / 2 + (h : ℂ) = -γ - ((n - l - h : ℕ) : ℂ) := by
              dsimp [q, detectorExp, γ]
              rw [Nat.cast_sub hhN]
              push_cast
              ring
            have heRev : pairExp (weight (K - 2 * j)) (weight (M - 2 * i))
                (((n - l : ℕ) : ℤ) - h) =
                pairExp (mQ - 2 * (j : ℤ)) (mP - 2 * (i : ℤ)) ((n - l - h : ℕ) : ℤ) := by
              dsimp [mQ, mP, pairExp, weight]
              omega
            have hF : N - j - i - (l + h) = n - l - h := by dsimp [n]; omega
            rw [hq, hx, heRev]
            simp only [f, aCoeff, hF, swapped_val, Pᵢ, Qⱼ]
          change sign N * (Ring.choose (α i) l / d *
              ((sign (3 + (M - 2 * i)) * I ^ el) * _)) =
            (phase / d) * ∑ h ∈ Finset.range (n - l + 1), term l h
          rw [ex]
          have hp :
              sign N * (sign (3 + (M - 2 * i)) * I ^ el) = phase * sign l := by
            rw [descend_sign M i hiM, hel]
            exact original_phase M K N l
          calc
            _ = (sign N * (sign (3 + (M - 2 * i)) * I ^ el)) *
                (Ring.choose (α i) l / d) *
                (∑ h ∈ Finset.range (n - l + 1),
                  sign h * Ring.choose (-γ - ((n - l - h : ℕ) : ℂ)) h * f j i (l + h)) :=
              by ring
            _ = _ := by
              rw [hp]
              simp only [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro h _
              simp only [term, sign, pow_add, div_eq_mul_inv]
              ring
        _ = _ := by
          dsimp only [term]
          rw [triangular_vandermonde n (α i) (-γ) (f j i)]
          have hx : (n : ℂ) - α i - -γ - 1 = target j := by
            dsimp [n, α, γ, δ, target]
            rw [Nat.cast_sub hiN, Nat.cast_sub hjN]
            ring
          rw [hx, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro L _
          simp only [div_eq_mul_inv]
          ring

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedIterateInversionCoefficient
