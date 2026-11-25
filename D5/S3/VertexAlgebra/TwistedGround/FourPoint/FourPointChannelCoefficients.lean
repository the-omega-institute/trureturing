/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Laurent residue extraction and actual signed four-point coset numerators. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChargeGerm
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.Order

/-! Finite Laurent coefficient extraction for the original four-point channels. -/

open Filter Set
open scoped BigOperators Topology

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.FourPointChannelCoefficients

/-- Taylor coefficient of an analytic numerator at zero. -/
def coeff (U : ℂ → ℂ) (i : ℕ) : ℂ :=
  iteratedDeriv i U 0 / (i.factorial : ℂ)

/-- The scalar coefficients of a supplied analytic power series are normalized derivatives. -/
theorem coeff_eq_of_hasFPowerSeriesAt {U : ℂ → ℂ} {c : ℕ → ℂ}
    (h : HasFPowerSeriesAt U (FormalMultilinearSeries.ofScalars ℂ c) 0) (i : ℕ) :
    coeff U i = c i := by
  have heq := h.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries h
  simpa only [coeff, FormalMultilinearSeries.coeff_ofScalars] using
    congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p.coeff i) heq

/-- The Laurent germ determined by a numerator and the sum of the two input weights. -/
def laurent (M : ℤ) (U : ℂ → ℂ) (t : ℂ) : ℂ :=
  t ^ (-M) * U t

/-- The coefficient of the Laurent monomial of exponent `-k-1`. -/
def diagonal (M : ℤ) (U : ℂ → ℂ) (k : ℤ) : ℂ :=
  if k < M then coeff U (M - k - 1).toNat else 0

/-- The coefficient at exponent `-1` for `t^(q-M) V(t)`. -/
def residue (M q : ℤ) (V : ℂ → ℂ) : ℂ :=
  diagonal M V q

/-- The sign in the binomial factor. -/
def sign (minus : Bool) : ℂ := if minus then -1 else 1

def binomial (minus : Bool) (r : ℤ) (t : ℂ) : ℂ :=
  (1 + sign minus * t) ^ r

theorem coeff_mul {V U : ℂ → ℂ} (hV : AnalyticAt ℂ V 0) (hU : AnalyticAt ℂ U 0)
    (i : ℕ) :
    coeff (fun t ↦ V t * U t) i =
      ∑ j ∈ Finset.range (i + 1), coeff V j * coeff U (i - j) := by
  unfold coeff
  rw [iteratedDeriv_fun_mul hV.contDiffAt hU.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hfact : (i.choose j : ℂ) * (j.factorial : ℂ) * ((i - j).factorial : ℂ) =
      (i.factorial : ℂ) := by exact_mod_cast h
  have hj0 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hij0 : ((i - j).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i - j)
  rw [← hfact]
  have hc : (i.choose j : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).ne'
  field_simp

private theorem plus_series (r : ℤ) : HasFPowerSeriesAt (binomial false r)
    (binomialSeries ℂ (r : ℂ)) 0 := by
  change HasFPowerSeriesAt (fun t : ℂ ↦ (1 + 1 * t) ^ r) (binomialSeries ℂ (r : ℂ)) 0
  simpa only [one_mul, Complex.cpow_intCast] using
    (Complex.one_add_cpow_hasFPowerSeriesAt_zero (a := (r : ℂ)))

private theorem analyticAt_reflect {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) :
    AnalyticAt ℂ (fun t ↦ U (-t)) 0 :=
  hU.fun_comp_of_eq (by fun_prop) (by simp)

theorem analyticAt_binomial (minus : Bool) (r : ℤ) :
    AnalyticAt ℂ (binomial minus r) 0 := by
  cases minus
  · exact (plus_series r).analyticAt
  · change AnalyticAt ℂ (fun t : ℂ ↦ (1 + (-1) * t) ^ r) 0
    simpa [binomial, sign] using analyticAt_reflect (plus_series r).analyticAt

theorem coeff_reflect (U : ℂ → ℂ) (i : ℕ) :
    coeff (fun t ↦ U (-t)) i = (-1 : ℂ) ^ i * coeff U i := by
  simp [coeff, iteratedDeriv_comp_neg, mul_div_assoc]

theorem coeff_binomial (minus : Bool) (r : ℤ) (j : ℕ) :
    coeff (binomial minus r) j = Ring.choose (r : ℂ) j * sign minus ^ j := by
  have hplus : coeff (binomial false r) j = Ring.choose (r : ℂ) j :=
    coeff_eq_of_hasFPowerSeriesAt (plus_series r) j
  cases minus
  · simpa [sign] using hplus
  · have heq : binomial true r = fun t ↦ binomial false r (-t) := by
      funext t
      simp [binomial, sign]
    rw [heq, coeff_reflect, hplus, mul_comm]
    rfl

/-- The exact cutoff is the positive part of `M-q`, even when either mode is negative. -/
theorem residue_binomial {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (M q r : ℤ)
    (minus : Bool) :
    residue M q (fun t ↦ binomial minus r t * U t) =
      ∑ j ∈ Finset.range (M - q).toNat,
        Ring.choose (r : ℂ) j * sign minus ^ j * diagonal M U (q + (j : ℤ)) := by
  by_cases hq : q < M
  · have hcut : (M - q).toNat = (M - q - 1).toNat + 1 := by omega
    rw [residue, diagonal, ite_eq_left hq, coeff_mul (analyticAt_binomial minus r) hU, hcut]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hmode : q + (j : ℤ) < M := by omega
    have hindex : (M - q - 1).toNat - j = (M - (q + (j : ℤ)) - 1).toNat := by omega
    rw [coeff_binomial, diagonal, ite_eq_left hmode, hindex]
  · have hcut : (M - q).toNat = 0 := by omega
    simp [residue, diagonal, hq, hcut]

/-- Principal part indexed from the simple pole. This is the convention of the
three-puncture residue theorem at the puncture zero. -/
def principalPart (N : ℕ) (c : ℕ → ℂ) (t : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N, c j * t⁻¹ ^ (j + 1)

def simpleCoeff (N : ℕ) (c : ℕ → ℂ) : ℂ :=
  if 0 < N then c 0 else 0

/-- A finite principal part and an analytic remainder on a punctured neighborhood. -/
def HasPrincipalPart (N : ℕ) (f : ℂ → ℂ) (s : ℂ) : Prop :=
  ∃ c : ℕ → ℂ, ∃ W : ℂ → ℂ, AnalyticAt ℂ W 0 ∧ simpleCoeff N c = s ∧
    f =ᶠ[𝓝[≠] 0] fun t ↦ principalPart N c t + W t

theorem hasPrincipalPart {V : ℂ → ℂ} (hV : AnalyticAt ℂ V 0) (M q : ℤ) :
    HasPrincipalPart (M - q).toNat (fun t ↦ t ^ (q - M) * V t) (residue M q V) := by
  by_cases hq : q < M
  · let N := (M - q).toNat
    have hN : 0 < N := by dsimp [N]; omega
    have hNM : (N : ℤ) = M - q := by dsimp [N]; omega
    obtain ⟨W, hW, hTaylor⟩ := hV.exists_eventuallyEq_sum_add_pow_mul N
    refine ⟨fun j ↦ coeff V (N - 1 - j), W, hW, ?_, ?_⟩
    · change simpleCoeff N (fun j ↦ coeff V (N - 1 - j)) = residue M q V
      simp only [simpleCoeff, ite_eq_left hN, Nat.sub_zero, residue, diagonal, ite_eq_left hq]
      congr 1
      omega
    · have hpTaylor := hTaylor.filter_mono
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)
      filter_upwards [hpTaylor, self_mem_nhdsWithin] with t ht htt
      have ht0 : t ≠ 0 := htt
      have hqM : q - M = -(N : ℤ) := by omega
      rw [ht, mul_add, Finset.mul_sum, smul_eq_mul, ← mul_assoc, ← zpow_natCast,
        ← zpow_add₀ ht0, hqM, neg_add_cancel, zpow_zero, one_mul, add_left_inj]
      unfold principalPart
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hexp : -(N : ℤ) + ((N - 1 - j : ℕ) : ℤ) = -((j + 1 : ℕ) : ℤ) := by omega
      have hp : t ^ (-(N : ℤ)) * t ^ (N - 1 - j : ℕ) = t⁻¹ ^ (j + 1) := by
        rw [← zpow_natCast t (N - 1 - j), ← zpow_add₀ ht0, hexp, zpow_neg, zpow_natCast, inv_pow]
      simp only [smul_eq_mul, coeff]
      rw [← hp]
      ring
  · have hcut : (M - q).toNat = 0 := by omega
    have hcast : (((q - M).toNat : ℕ) : ℤ) = q - M := by omega
    refine ⟨0, (fun t ↦ t ^ (q - M).toNat * V t), ?_, ?_, ?_⟩
    · exact analyticAt_id.pow _ |>.mul hV
    · simp [simpleCoeff, hcut, residue, diagonal, hq]
    · simp [principalPart, hcut, ← zpow_natCast, hcast]

/-- Finite Laurent extraction for both choices of sign, including the analytic case. -/
theorem hasPrincipalPart_binomial {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0)
    (M q r : ℤ) (minus : Bool) :
    HasPrincipalPart (M - q).toNat (fun t ↦ t ^ q * binomial minus r t * laurent M U t)
      (∑ j ∈ Finset.range (M - q).toNat,
        Ring.choose (r : ℂ) j * sign minus ^ j * diagonal M U (q + (j : ℤ))) := by
  rw [← residue_binomial hU]
  obtain ⟨c, W, hW, hc, hex⟩ :=
    hasPrincipalPart ((analyticAt_binomial minus r).mul hU) M q
  refine ⟨c, W, hW, hc, ?_⟩
  filter_upwards [hex, self_mem_nhdsWithin] with t ht htt
  have ht0 : t ≠ 0 := htt
  rw [← ht]
  dsimp [laurent]
  rw [sub_eq_add_neg, zpow_add₀ ht0]
  ac_rfl

private theorem coeff_const_mul (a : ℂ) (U : ℂ → ℂ) (i : ℕ) :
    coeff (fun t ↦ a * U t) i = a * coeff U i := by
  simp only [coeff, iteratedDeriv_const_mul_field, mul_div_assoc]

private theorem coeff_sum {ι : Type*} (s : Finset ι) {V : ι → ℂ → ℂ}
    (hV : ∀ j ∈ s, AnalyticAt ℂ (V j) 0) (i : ℕ) :
    coeff (fun t ↦ ∑ j ∈ s, V j t) i = ∑ j ∈ s, coeff (V j) i := by
  unfold coeff
  rw [iteratedDeriv_fun_sum (fun j hj ↦ (hV j hj).contDiffAt), Finset.sum_div]

private theorem neg_one_zpow_add_even (e k : ℤ) :
    (-1 : ℂ) ^ (e + 2 * k) = (-1 : ℂ) ^ e := by
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    (even_two_mul k).neg_one_zpow, mul_one]

private theorem neg_one_zpow_neg (e : ℤ) : (-1 : ℂ) ^ (-e) = (-1 : ℂ) ^ e := by
  rw [show -e = e + 2 * (-e) by omega, neg_one_zpow_add_even]

/-- Reflection includes the phase of the Laurent monomial. -/
def reflected (M : ℤ) (U : ℂ → ℂ) (t : ℂ) : ℂ :=
  (-1 : ℂ) ^ M * U (-t)

theorem laurent_reflected (M : ℤ) (U : ℂ → ℂ) (t : ℂ) :
    laurent M U (-t) = laurent M (reflected M U) t := by
  change (-t) ^ (-M) * U (-t) = t ^ (-M) * ((-1 : ℂ) ^ M * U (-t))
  rw [show -t = -1 * t by simp, mul_zpow, neg_one_zpow_neg]
  ring

theorem diagonal_reflected (M k : ℤ) (U : ℂ → ℂ) :
    diagonal M (reflected M U) k = (-1 : ℂ) ^ (-k - 1) * diagonal M U k := by
  by_cases hk : k < M
  · have he : M + ((M - k - 1).toNat : ℤ) = -k - 1 + 2 * M := by omega
    simp only [diagonal, ite_eq_left hk]
    change coeff (fun t ↦ (-1 : ℂ) ^ M * U (-t)) _ = _
    rw [coeff_const_mul, coeff_reflect, ← mul_assoc, ← zpow_natCast (-1 : ℂ), ← zpow_add₀ (by norm_num), he,
      neg_one_zpow_add_even]
  · simp [diagonal, hk]

/-- The two transported channels use the same reflected Laurent family, with the
original lowering phase and factorial. -/
def loweringWeight (d : ℤ) (ell : ℕ) : ℂ :=
  (-1 : ℂ) ^ (d + (ell : ℤ) + 2) * (ell.factorial : ℂ)⁻¹

def loweredLaurent (M d : ℤ) (N : ℕ) (U : ℕ → ℂ → ℂ) (t : ℂ) : ℂ :=
  ∑ ell ∈ Finset.range N, loweringWeight d ell * laurent M (U ell) (-t)

private def transportedNumerator (reverse : Bool) (M d r : ℤ) (N : ℕ) (U : ℕ → ℂ → ℂ)
    (t : ℂ) : ℂ :=
  ∑ ell ∈ Finset.range N,
    ((-1 : ℂ) ^ (if reverse then r else 0) * loweringWeight d ell) * reflected M (U ell) t

private theorem analyticAt_transportedNumerator (reverse : Bool) (M d r : ℤ) (N : ℕ)
    {U : ℕ → ℂ → ℂ} (hU : ∀ ell < N, AnalyticAt ℂ (U ell) 0) :
    AnalyticAt ℂ (transportedNumerator reverse M d r N U) 0 := by
  apply Finset.analyticAt_fun_sum
  intro ell hell
  exact analyticAt_const.mul (analyticAt_const.mul (analyticAt_reflect (hU ell (Finset.mem_range.mp hell))))

private theorem diagonal_transportedNumerator (reverse : Bool) (M d r k : ℤ) (N : ℕ)
    {U : ℕ → ℂ → ℂ} (hU : ∀ ell < N, AnalyticAt ℂ (U ell) 0) :
    diagonal M (transportedNumerator reverse M d r N U) k =
      ∑ ell ∈ Finset.range N,
        ((-1 : ℂ) ^ (if reverse then r else 0) * loweringWeight d ell) *
          ((-1 : ℂ) ^ (-k - 1) * diagonal M (U ell) k) := by
  by_cases hk : k < M
  · have hV : ∀ ell ∈ Finset.range N, AnalyticAt ℂ (fun t ↦
        ((-1 : ℂ) ^ (if reverse then r else 0) * loweringWeight d ell) *
          reflected M (U ell) t) 0 := by
      intro ell hell
      exact analyticAt_const.mul (analyticAt_const.mul (analyticAt_reflect (hU ell (Finset.mem_range.mp hell))))
    rw [diagonal, ite_eq_left hk]
    change coeff (fun t ↦ ∑ ell ∈ Finset.range N,
      ((-1 : ℂ) ^ (if reverse then r else 0) * loweringWeight d ell) *
        reflected M (U ell) t) _ = _
    rw [coeff_sum _ hV]
    apply Finset.sum_congr rfl
    intro ell _
    have hd : diagonal M (reflected M (U ell)) k = coeff (reflected M (U ell)) (M-k-1).toNat := by
      simp only [diagonal, ite_eq_left hk]
    rw [coeff_const_mul, ← hd, diagonal_reflected]
  · simp [diagonal, hk]

private theorem transported_sign (reverse : Bool) (d q r : ℤ) (j ell : ℕ) :
    sign true ^ j *
        ((-1 : ℂ) ^ (if reverse then r else 0) * (-1 : ℂ) ^ (d + (ell : ℤ) + 2)) *
        (-1 : ℂ) ^ (-(q + (j : ℤ)) - 1) =
      (-1 : ℂ) ^ (d - q + (if reverse then r else 0) + (ell : ℤ) + 1) := by
  have hn : (-1 : ℂ) ≠ 0 := by norm_num
  let e : ℤ := if reverse then r else 0
  change (-1 : ℂ) ^ j * ((-1 : ℂ) ^ e * (-1 : ℂ) ^ (d + (ell : ℤ) + 2)) *
    (-1 : ℂ) ^ (-(q + (j : ℤ)) - 1) = (-1 : ℂ) ^ (d - q + e + (ell : ℤ) + 1)
  have he : (j : ℤ) + (e + (d + (ell : ℤ) + 2)) + (-(q + (j : ℤ)) - 1) =
      d - q + e + (ell : ℤ) + 1 := by omega
  rw [← zpow_natCast (-1 : ℂ), ← zpow_add₀ hn, ← zpow_add₀ hn, ← zpow_add₀ hn, he]

/-- Finite lowering in the two transported channels. With `reverse = false` the
binomial factor is `(1-t)^r`; with `reverse = true` it is `(t-1)^r`. -/
theorem hasPrincipalPart_lowered (reverse : Bool) (M q r d : ℤ) (N : ℕ)
    {U : ℕ → ℂ → ℂ} (hU : ∀ ell < N, AnalyticAt ℂ (U ell) 0) :
    HasPrincipalPart (M - q).toNat
      (fun t ↦ t ^ q * (if reverse then t - 1 else 1 - t) ^ r * loweredLaurent M d N U t)
      (∑ j ∈ Finset.range (M - q).toNat, ∑ ell ∈ Finset.range N,
        Ring.choose (r : ℂ) j *
          (-1 : ℂ) ^ (d - q + (if reverse then r else 0) + (ell : ℤ) + 1) *
          (ell.factorial : ℂ)⁻¹ * diagonal M (U ell) (q + (j : ℤ))) := by
  have hsum :
    (∑ j ∈ Finset.range (M - q).toNat, Ring.choose (r : ℂ) j * sign true ^ j *
      diagonal M (transportedNumerator reverse M d r N U) (q + (j : ℤ))) =
      ∑ j ∈ Finset.range (M - q).toNat, ∑ ell ∈ Finset.range N,
        Ring.choose (r : ℂ) j *
          (-1 : ℂ) ^ (d - q + (if reverse then r else 0) + (ell : ℤ) + 1) *
          (ell.factorial : ℂ)⁻¹ * diagonal M (U ell) (q + (j : ℤ)) := by
    simp only [diagonal_transportedNumerator reverse M d r _ N hU, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro ell _
    dsimp only [loweringWeight]
    rw [← transported_sign reverse d q r j ell]
    ring
  have hf (t : ℂ) :
      (if reverse then t - 1 else 1 - t) ^ r =
        (-1 : ℂ) ^ (if reverse then r else 0) * binomial true r t := by
    cases reverse
    · simp [binomial, sign, sub_eq_add_neg]
    · simp only [ite_true, binomial, sign, neg_one_mul, ← mul_zpow]
      congr 1
      ring
  obtain ⟨c, W, hW, hc, hex⟩ :=
    hasPrincipalPart_binomial (analyticAt_transportedNumerator reverse M d r N hU) M q r true
  refine ⟨c, W, hW, hc.trans hsum, ?_⟩
  filter_upwards [hex] with t ht
  rw [← ht, hf]
  simp only [loweredLaurent, laurent_reflected]
  simp only [transportedNumerator, laurent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell _
  ring

section OriginalChannels

open D5.S3.VertexAlgebra
open D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization.SignQuotient
open LatticePositiveEnergy
open OriginalFourMChargeGerm
open OriginalFourMEnergyCoefficient (cosetSeries)
open private cosetKernel_energy_coefficient from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient

/-- An analytic numerator whose Taylor coefficients equal the original coset kernel
on the mode diagonal with summed index `s`. -/
def IsDiagonalNumerator (D : LatticeData) (hu : IsUnit D.G.det) (H K : ℕ)
    (s : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) (U : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ U 0 ∧ ∀ E : ℕ,
    coeff U E = cosetKernel D hu H K ((H : ℤ) + (K : ℤ) - (E : ℤ) - 1)
      ((E : ℤ) + (s - (H : ℤ) - (K : ℤ) + 1)) P Q R S a

/-- Convert the descended charge germ by supplying the energy coefficient identity
at the original two mode indices. -/
theorem isDiagonalNumerator_of_hasFPowerSeriesAt (D : LatticeData) (hu : IsUnit D.G.det)
    (H K : ℕ) (s : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D)
    {U : ℂ → ℂ} {c : ℕ → ℂ}
    (h : HasFPowerSeriesAt U (FormalMultilinearSeries.ofScalars ℂ c) 0)
    (hc : ∀ E : ℕ, cosetKernel D hu H K ((H : ℤ) + (K : ℤ) - (E : ℤ) - 1)
        ((E : ℤ) + (s - (H : ℤ) - (K : ℤ) + 1)) P Q R S a = c E) :
    IsDiagonalNumerator D hu H K s P Q R S a U :=
  ⟨h.analyticAt, fun E ↦ (coeff_eq_of_hasFPowerSeriesAt h E).trans (hc E).symm⟩

/-- The convergent Taylor sum of the original rescaled coset series on the
signed mode diagonal. -/
def actualDiagonalNumerator (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (H K : ℕ)
    (s : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) : ℂ → ℂ :=
  (FormalMultilinearSeries.ofScalars ℂ (fun E : ℕ ↦ PowerSeries.coeff E
    (PowerSeries.rescale (-1)
      (cosetSeries D hD H K ((E : ℤ) + (s - H - K + 1)) P Q R S a)))).sum

/-- The canonical numerator has the exact original kernel coefficients, and its
negative-square pullback recovers the even part of the actual sewn charge sum. -/
theorem actualDiagonalNumerator_spec (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (H K : ℕ)
    (s : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) :
    let U := actualDiagonalNumerator D hD H K s P Q R S a
    let f := diagonalSewn D H K (s - H - K + 1) P Q R S a
    IsDiagonalNumerator D hu H K s P Q R S a U ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), U (-(z ^ 2)) = (f z + f (-z)) / 2 := by
  dsimp only
  let t₀ : ℤ := s - H - K + 1
  let p := FormalMultilinearSeries.ofScalars ℂ (fun E : ℕ ↦ PowerSeries.coeff E
    (PowerSeries.rescale (-1) (cosetSeries D hD H K ((E : ℤ) + t₀) P Q R S a)))
  obtain ⟨G, hG, hpull⟩ := cosetSeries_negative_square_germ D hu hD H K t₀ P Q R S a
  change HasFPowerSeriesAt G p 0 at hG
  have hseries := (p.hasFPowerSeriesOnBall hG.radius_pos).hasFPowerSeriesAt
  refine ⟨isDiagonalNumerator_of_hasFPowerSeriesAt D hu H K s P Q R S a hseries
    (fun E ↦ cosetKernel_energy_coefficient D hu hD H K E _ P Q R S a), ?_⟩
  have heq : p.sum =ᶠ[𝓝 (0 : ℂ)] G := by
    obtain ⟨r, hr⟩ := hG
    filter_upwards [Metric.eball_mem_nhds (0 : ℂ) hr.r_pos] with w hw
    simpa only [zero_add] using (hr.sum hw).symm
  have hsquare : Tendsto (fun z : ℂ ↦ -(z ^ 2)) (𝓝 0) (𝓝 0) := by
    have h : Continuous (fun z : ℂ ↦ -(z ^ 2)) := (continuous_id.pow 2).neg
    simpa using (h.tendsto (0 : ℂ))
  exact (heq.comp_tendsto hsquare).trans hpull

theorem diagonal_eq_cosetKernel (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (H K : ℕ)
    (s : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) {U : ℂ → ℂ}
    (hU : IsDiagonalNumerator D hu H K s P Q R S a U) (k : ℤ) :
    diagonal ((H : ℤ) + (K : ℤ)) U k = cosetKernel D hu H K k (s - k) P Q R S a := by
  by_cases hk : k < (H : ℤ) + (K : ℤ)
  · have hE : ((((H : ℤ) + (K : ℤ) - k - 1).toNat : ℕ) : ℤ) =
        (H : ℤ) + (K : ℤ) - k - 1 := by omega
    rw [diagonal, ite_eq_left hk, hU.2, hE]
    congr 1 <;> omega
  · let : IsEmpty (EnergyFiber D ((H : ℤ) + (K : ℤ) - k - 1)) := ⟨fun b ↦ by
      have hq := chargeEnergy_nonneg D hD b.val.1
      have hb := b.property
      dsimp [LatticePositiveEnergy.energy] at hb
      omega⟩
    simp [diagonal, hk, cosetKernel, finsum_of_isEmpty]

/-- Local residue in the original iterate channel, with inputs `P Q R S`. -/
theorem hasPrincipalPart_channelA (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (H K : ℕ)
    (m n r : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) {U : ℂ → ℂ}
    (hU : IsDiagonalNumerator D hu H K (m + n + r) P Q R S a U) :
    HasPrincipalPart ((H : ℤ) + (K : ℤ) - r).toNat
      (fun t ↦ t ^ r * (1 + t) ^ m * laurent ((H : ℤ) + (K : ℤ)) U t)
      (channelA D hu H K m n r P Q R S a) := by
  have h := hasPrincipalPart_binomial hU.1 ((H : ℤ) + (K : ℤ)) r m false
  unfold channelA
  simp only [binomial, sign, Bool.false_eq_true, ite_false, one_mul, one_pow, mul_one,
    diagonal_eq_cosetKernel D hu hD H K (m + n + r) P Q R S a hU] at h
  have hmode (j : ℕ) : m + n + r - (r + (j : ℤ)) = m + n - (j : ℤ) := by omega
  simpa only [hmode] using h

/-- The common lowering cutoff, including a nonpositive output weight minus one. -/
def loweringCutoff (H K L : ℕ) (m n r : ℤ) : ℕ :=
  ((H : ℤ) + (K : ℤ) + (L : ℤ) - m - n - r - 3).toNat

/-- Local residue in the first transported channel, with inputs `Q R P` and
the original lowered detector in each summand. -/
theorem hasPrincipalPart_channelB (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (H K L : ℕ)
    (m n r : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) {U : ℕ → ℂ → ℂ}
    (hU : ∀ ell < loweringCutoff H K L m n r,
      IsDiagonalNumerator D hu K L (m + n + r + (ell : ℤ))
        Q R P ((oscillatorLower D ^ ell) S) a (U ell)) :
    HasPrincipalPart ((K : ℤ) + (L : ℤ) - n).toNat
      (fun t ↦ t ^ n * (1 - t) ^ r *
        loweredLaurent ((K : ℤ) + (L : ℤ)) (m + n + r) (loweringCutoff H K L m n r) U t)
      (channelB D hu H K L m n r P Q R S a) := by
  have h := hasPrincipalPart_lowered false ((K : ℤ) + (L : ℤ)) n r (m + n + r)
    (loweringCutoff H K L m n r) (fun ell hell ↦ (hU ell hell).1)
  simp only [Bool.false_eq_true, ite_false, add_zero] at h
  convert h using 1
  unfold channelB
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro ell hell
  rw [diagonal_eq_cosetKernel D hu hD K L _ Q R P _ a (hU ell (Finset.mem_range.mp hell))]
  have hmode : m + n + r + (ell : ℤ) - (n + (j : ℤ)) = m + r - (j : ℤ) + (ell : ℤ) := by omega
  have hsign : m + n + r - n + (ell : ℤ) + 1 = m + r + (ell : ℤ) + 1 := by omega
  rw [hmode, hsign]

/-- Local residue in the second transported channel, with inputs `P R Q` and
the original lowered detector in each summand. -/
theorem hasPrincipalPart_channelD (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (H K L : ℕ)
    (m n r : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D) {U : ℕ → ℂ → ℂ}
    (hU : ∀ ell < loweringCutoff H K L m n r,
      IsDiagonalNumerator D hu H L (m + n + r + (ell : ℤ))
        P R Q ((oscillatorLower D ^ ell) S) a (U ell)) :
    HasPrincipalPart ((H : ℤ) + (L : ℤ) - m).toNat
      (fun t ↦ t ^ m * (t - 1) ^ r *
        loweredLaurent ((H : ℤ) + (L : ℤ)) (m + n + r) (loweringCutoff H K L m n r) U t)
      (channelD D hu H K L m n r P Q R S a) := by
  have h := hasPrincipalPart_lowered true ((H : ℤ) + (L : ℤ)) m r (m + n + r)
    (loweringCutoff H K L m n r) (fun ell hell ↦ (hU ell hell).1)
  simp only [ite_true] at h
  convert h using 1
  unfold channelD
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro ell hell
  rw [diagonal_eq_cosetKernel D hu hD H L _ P R Q _ a (hU ell (Finset.mem_range.mp hell))]
  have hmode : m + n + r + (ell : ℤ) - (m + (j : ℤ)) = n + r - (j : ℤ) + (ell : ℤ) := by omega
  have hsign : m + n + r - m + r + (ell : ℤ) + 1 = n + (ell : ℤ) + 1 + 2 * r := by omega
  rw [hmode, hsign, neg_one_zpow_add_even]

end OriginalChannels

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.FourPointChannelCoefficients
