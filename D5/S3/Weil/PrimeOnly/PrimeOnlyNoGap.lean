/- GID: D5/S3/Weil/PrimeOnly/PrimeOnlyNoGap
   generality: I
   mirror-B: D5/B/S3/Weil/PrimeOnly/PrimeOnlyNoGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Summable prime-power jumps have Fourier energies with zero nonzero-mode infimum. -/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.WellApproximable

/- Library-search audit trail (2026-09-01):
   * Repository searches for `prime-only`, `prime_only`, `no-gap`, Fourier jump energy,
     simultaneous approximation, and semantic variants found no equivalent declaration. The
     nearby `PrimeJumpDecomposition` treats finite von Mangoldt truncations, not nonzero Fourier
     modes or their infimum. The two atom ledgers have empty `coverage_gids`, and neither atom ID
     occurs in a formalization receipt.
   * Pinned Mathlib provides `fourier`, `CompactSpace.tendsto_subseq`,
     `tendsto_tsum_compl_atTop_zero`, and one-coordinate Dirichlet approximation via
     `AddCircle.exists_norm_nsmul_le`. It has no declaration for simultaneous recurrence of a
     finite family of arbitrary circle points, nor for summability of the number-field
     prime-ideal/prime-power weight used below.
   * Searches of the other pinned Lean packages found no prime-only, no-gap, simultaneous
     approximation, Kronecker, or Dedekind-zeta theorem relevant to this statement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.PrimeOnly.PrimeOnlyNoGap

open Filter MeasureTheory Set Topology
open scoped BigOperators Real Topology

noncomputable section

/-- Every point of a compact first-countable additive group has a positive return time into every
neighborhood of zero. Applied to a finite product of circles, this is simultaneous Diophantine
approximation with no irrationality hypothesis. -/
theorem exists_pos_nsmul_mem
    {A : Type*} [TopologicalSpace A] [AddCommGroup A] [IsTopologicalAddGroup A]
    [CompactSpace A] [FirstCountableTopology A]
    (xi : A) (U : Set A) (hU : U ∈ nhds (0 : A)) :
    ∃ n : ℕ, 0 < n ∧ n • xi ∈ U := by
  obtain ⟨a, phi, hphi, hlim⟩ := CompactSpace.tendsto_subseq (fun n : ℕ => n • xi)
  have hlim' : Tendsto (fun n => phi n • xi) atTop (nhds a) := by
    simpa only [Function.comp_def] using hlim
  have hlimSucc : Tendsto (fun n => phi (n + 1) • xi) atTop (nhds a) := by
    simpa only [Function.comp_def] using hlim'.comp (tendsto_add_atTop_nat 1)
  have hreturn :
      Tendsto (fun n => phi (n + 1) • xi - phi n • xi) atTop (nhds (0 : A)) := by
    simpa only [sub_self] using hlimSucc.sub hlim'
  have hreturn' :
      Tendsto (fun n => (phi (n + 1) - phi n) • xi) atTop (nhds (0 : A)) := by
    apply hreturn.congr'
    filter_upwards with n
    simpa only [Nat.add_one, sub_eq_add_neg] using
      (sub_nsmul xi (hphi.monotone (Nat.le_succ n))).symm
  obtain ⟨n, hnU⟩ := (hreturn'.eventually hU).exists
  exact ⟨phi (n + 1) - phi n, Nat.sub_pos_of_lt (hphi (Nat.lt_succ_self n)), hnU⟩

/-- The spectral jump energy attached to nonnegative prime-power weights and circle shifts. -/
def fourierJumpEnergy {P : ℝ} [Fact (0 < P)] {I : Type*}
    (weight : I → ℝ) (jump : I → AddCircle P) (n : ℤ) : ℝ :=
  ∑' j, weight j * Complex.normSq (fourier n (jump j) - 1)

private theorem fourier_jump_normSq_le_four {P : ℝ} [Fact (0 < P)]
    (n : ℤ) (x : AddCircle P) :
    Complex.normSq (fourier n x - 1) ≤ 4 := by
  rw [Complex.normSq_eq_norm_sq]
  have hnorm : ‖fourier n x‖ = 1 := by
    rw [fourier_apply]
    exact Circle.norm_coe _
  have hle : ‖fourier n x - 1‖ ≤ 2 := by
    calc
      ‖fourier n x - 1‖ ≤ ‖fourier n x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hnorm]; norm_num
  nlinarith [norm_nonneg (fourier n x - 1)]

private theorem fourier_jump_terms_summable {P : ℝ} [Fact (0 < P)] {I : Type*}
    {weight : I → ℝ} (jump : I → AddCircle P)
    (hweight : ∀ j, 0 ≤ weight j) (hsum : Summable weight) (n : ℤ) :
    Summable (fun j => weight j * Complex.normSq (fourier n (jump j) - 1)) := by
  apply Summable.of_nonneg_of_le
  · exact fun j => mul_nonneg (hweight j) (Complex.normSq_nonneg _)
  · exact fun j => mul_le_mul_of_nonneg_left
      (fourier_jump_normSq_le_four n (jump j)) (hweight j)
  · exact hsum.mul_right 4

theorem fourierJumpEnergy_nonnegative {P : ℝ} [Fact (0 < P)] {I : Type*}
    {weight : I → ℝ} (jump : I → AddCircle P) (hweight : ∀ j, 0 ≤ weight j)
    (n : ℤ) :
    0 ≤ fourierJumpEnergy weight jump n := by
  exact tsum_nonneg fun j => mul_nonneg (hweight j) (Complex.normSq_nonneg _)

/-- A summable family of nonnegative circle-jump weights has arbitrarily small energy at a
nonzero Fourier mode. The finite main part uses simultaneous recurrence in a product circle; the
summable complement is bounded by `4` times its weight. -/
theorem exists_nonzero_fourierJumpEnergy_lt {P : ℝ} [Fact (0 < P)] {I : Type*}
    {weight : I → ℝ} (jump : I → AddCircle P)
    (hweight : ∀ j, 0 ≤ weight j) (hsum : Summable weight)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ n : ℤ, n ≠ 0 ∧ fourierJumpEnergy weight jump n < epsilon := by
  classical
  have htailEventually : ∀ᶠ S : Finset I in atTop,
      (∑' j : {x // x ∉ S}, weight j) < epsilon / 8 :=
    (tendsto_order.1 (tendsto_tsum_compl_atTop_zero weight)).2 _ (by positivity)
  obtain ⟨S, htail⟩ := htailEventually.exists
  let xi : S → AddCircle P := fun j => jump j
  let mainEnergy : (S → AddCircle P) → ℝ := fun x =>
    ∑ j : S, weight j * Complex.normSq (AddCircle.toCircle (x j) - 1)
  have hmainContinuous : Continuous mainEnergy := by
    dsimp only [mainEnergy]
    fun_prop
  have hmainZero : mainEnergy 0 = 0 := by
    simp [mainEnergy]
  have hmainTendsto : Tendsto mainEnergy (nhds 0) (nhds 0) := by
    have hmainAt :
        Tendsto mainEnergy (nhds (0 : S → AddCircle P)) (nhds (mainEnergy 0)) :=
      hmainContinuous.continuousAt
    simpa only [hmainZero] using hmainAt
  have hnear : {x | mainEnergy x < epsilon / 2} ∈ nhds (0 : S → AddCircle P) :=
    hmainTendsto (Iio_mem_nhds (by positivity))
  obtain ⟨m, hmpos, hmMain⟩ := exists_pos_nsmul_mem xi _ hnear
  have hmainEq :
      (∑ j : S, weight j *
        Complex.normSq (fourier (m : ℤ) (jump j) - 1)) =
        mainEnergy (m • xi) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [xi, fourier_apply, natCast_zsmul]
    rfl
  have hterms := fourier_jump_terms_summable jump hweight hsum (m : ℤ)
  have htailEnergy :
      (∑' j : {x // x ∉ S}, weight j *
        Complex.normSq (fourier (m : ℤ) (jump j) - 1)) < epsilon / 2 := by
    calc
      (∑' j : {x // x ∉ S}, weight j *
          Complex.normSq (fourier (m : ℤ) (jump j) - 1)) ≤
          ∑' j : {x // x ∉ S}, weight j * 4 := by
            exact (hterms.subtype _).tsum_le_tsum
              (fun j => mul_le_mul_of_nonneg_left
                (fourier_jump_normSq_le_four (m : ℤ) (jump j)) (hweight j))
              ((hsum.mul_right 4).subtype _)
      _ = (∑' j : {x // x ∉ S}, weight j) * 4 :=
        (hsum.subtype _).tsum_mul_right 4
      _ < epsilon / 2 := by linarith
  refine ⟨(m : ℤ), Int.ofNat_ne_zero.mpr hmpos.ne', ?_⟩
  unfold fourierJumpEnergy
  rw [← hterms.sum_add_tsum_subtype_compl S, ← S.sum_attach, Finset.attach_eq_univ,
    hmainEq]
  change mainEnergy (m • xi) < epsilon / 2 at hmMain
  linarith

/-- Prime-only no-gap theorem: the infimum over genuinely nonzero Fourier modes is zero. -/
theorem prime_only_no_gap {P : ℝ} [Fact (0 < P)] {I : Type*}
    {weight : I → ℝ} (jump : I → AddCircle P)
    (hweight : ∀ j, 0 ≤ weight j) (hsum : Summable weight) :
    sInf (Set.range fun n : {n : ℤ // n ≠ 0} => fourierJumpEnergy weight jump n) = 0 := by
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨fourierJumpEnergy weight jump 1, ⟨⟨1, one_ne_zero⟩, rfl⟩⟩
  · intro value hvalue
    obtain ⟨n, rfl⟩ := hvalue
    exact fourierJumpEnergy_nonnegative jump hweight n
  · intro epsilon hepsilon
    obtain ⟨n, hn, henergy⟩ :=
      exists_nonzero_fourierJumpEnergy_lt jump hweight hsum hepsilon
    exact ⟨fourierJumpEnergy weight jump n, ⟨⟨n, hn⟩, rfl⟩, henergy⟩

/-! ### Prime-only observer definitions -/

/-- The regulator circle `ℝ / Pℤ`. -/
abbrev GoldenRegulatorCircle (P : ℝ) := AddCircle P

/-- The `n`-th Fourier mode on the regulator circle. -/
def fourierMode {P : ℝ} (n : ℤ) : C(GoldenRegulatorCircle P, ℂ) :=
  fourier n

/-- An arithmetic place paired with a positive prime-power exponent. -/
abbrev PrimePowerIndex (I : Type*) := I × ℕ+

/-- The circle translation belonging to the `k`-th power of a prime place. -/
def primePowerJump {P : ℝ} {I : Type*} (primeShift : I → GoldenRegulatorCircle P)
    (q : PrimePowerIndex I) : GoldenRegulatorCircle P :=
  q.2.1 • primeShift q.1

/-- The prime-only Dirichlet form
`(1 / 2) ∑_(p,k) w_(p,k) ∫ |ƒ(η + kη_p) - ƒ(η)|² dη`. -/
def primeOnlyDirichletForm {P : ℝ} [Fact (0 < P)] {I : Type*}
    (weight : PrimePowerIndex I → ℝ) (primeShift : I → GoldenRegulatorCircle P)
    (f : GoldenRegulatorCircle P → ℂ) : ℝ :=
  (1 / 2) * ∑' q, weight q *
    ∫ eta, Complex.normSq (f (eta + primePowerJump primeShift q) - f eta)

/-- The finite prime-only spectral coefficient is the Dirichlet form of a Fourier mode. -/
def spectralCoefficient {P : ℝ} [Fact (0 < P)] {I : Type*}
    (weight : PrimePowerIndex I → ℝ) (primeShift : I → GoldenRegulatorCircle P)
    (n : ℤ) : ℝ :=
  primeOnlyDirichletForm weight primeShift (fourierMode n)

private theorem fourier_translation_normSq {P : ℝ} [Fact (0 < P)]
    (n : ℤ) (eta x : GoldenRegulatorCircle P) :
    Complex.normSq (fourier n (eta + x) - fourier n eta) =
      Complex.normSq (fourier n x - 1) := by
  have hcharacter : fourier n (eta + x) = fourier n eta * fourier n x := by
    simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
  rw [hcharacter, show fourier n eta * fourier n x - fourier n eta =
    fourier n eta * (fourier n x - 1) by ring, Complex.normSq_mul]
  have hunit : Complex.normSq (fourier n eta) = 1 := by
    rw [fourier_apply]
    exact Circle.normSq_coe _
  rw [hunit, one_mul]

private theorem integral_fourier_translation_normSq {P : ℝ} [Fact (0 < P)]
    (n : ℤ) (x : GoldenRegulatorCircle P) :
    (∫ eta, Complex.normSq (fourier n (eta + x) - fourier n eta)) =
      P * Complex.normSq (fourier n x - 1) := by
  have hP : 0 ≤ P := (Fact.out : 0 < P).le
  simp_rw [fourier_translation_normSq]
  rw [integral_const]
  simp [Measure.real, AddCircle.measure_univ, hP]

/-- Evaluation on a Fourier mode removes the circle integral. The factor `P / 2` is the
volume of the regulator circle times the `1 / 2` in the Dirichlet form. -/
theorem spectralCoefficient_eq_fourierJumpEnergy {P : ℝ} [Fact (0 < P)] {I : Type*}
    (weight : PrimePowerIndex I → ℝ) (primeShift : I → GoldenRegulatorCircle P)
    (n : ℤ) :
    spectralCoefficient weight primeShift n =
      (P / 2) * fourierJumpEnergy weight (primePowerJump primeShift) n := by
  unfold spectralCoefficient primeOnlyDirichletForm fourierMode fourierJumpEnergy
  simp_rw [integral_fourier_translation_normSq]
  calc
    (1 / 2) *
        ∑' q, weight q *
          (P * Complex.normSq (fourier n (primePowerJump primeShift q) - 1)) =
        (1 / 2) *
          ∑' q, P *
            (weight q * Complex.normSq (fourier n (primePowerJump primeShift q) - 1)) := by
      congr 1
      apply tsum_congr
      intro q
      ring
    _ = (1 / 2) * (P *
        ∑' q, weight q *
          Complex.normSq (fourier n (primePowerJump primeShift q) - 1)) := by
      rw [tsum_mul_left]
    _ = (P / 2) *
        ∑' q, weight q *
          Complex.normSq (fourier n (primePowerJump primeShift q) - 1) := by ring

theorem spectralCoefficient_nonnegative {P : ℝ} [Fact (0 < P)] {I : Type*}
    {weight : PrimePowerIndex I → ℝ} (primeShift : I → GoldenRegulatorCircle P)
    (hweight : ∀ q, 0 ≤ weight q) (n : ℤ) :
    0 ≤ spectralCoefficient weight primeShift n := by
  have hP : 0 ≤ P := (Fact.out : 0 < P).le
  rw [spectralCoefficient_eq_fourierJumpEnergy]
  exact mul_nonneg (div_nonneg hP zero_le_two)
    (fourierJumpEnergy_nonnegative _ hweight n)

/-- The source theorem for any summable nonnegative family of prime-power weights. The subtype in
the infimum excludes the trivial zero Fourier mode. -/
theorem spectralCoefficient_prime_only_no_gap {P : ℝ} [Fact (0 < P)] {I : Type*}
    {weight : PrimePowerIndex I → ℝ} (primeShift : I → GoldenRegulatorCircle P)
    (hweight : ∀ q, 0 ≤ weight q) (hsum : Summable weight) :
    sInf (Set.range fun n : {n : ℤ // n ≠ 0} =>
      spectralCoefficient weight primeShift n) = 0 := by
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨spectralCoefficient weight primeShift 1, ⟨⟨1, one_ne_zero⟩, rfl⟩⟩
  · intro value hvalue
    obtain ⟨n, rfl⟩ := hvalue
    exact spectralCoefficient_nonnegative primeShift hweight n
  · intro epsilon hepsilon
    have hscale : 0 < P / 2 := div_pos (Fact.out : 0 < P) zero_lt_two
    obtain ⟨n, hn, henergy⟩ := exists_nonzero_fourierJumpEnergy_lt
      (primePowerJump primeShift) hweight hsum (div_pos hepsilon hscale)
    refine ⟨spectralCoefficient weight primeShift n, ⟨⟨n, hn⟩, rfl⟩, ?_⟩
    rw [spectralCoefficient_eq_fourierJumpEnergy]
    exact (lt_div_iff₀' hscale).mp henergy

/-! ### Number-field prime ideals -/

/-- Nonzero prime ideals of the ring of integers of a number field. -/
abbrev NumberFieldPrime (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)

private theorem numberFieldIdealLSeries_summable
    (K : Type*) [Field K] [NumberField K] {sigma : ℝ} (hsigma : 1 < sigma) :
    LSeriesSummable
      (fun n => (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm I = n} : ℝ)) sigma := by
  let residue : ℝ := NumberField.dedekindZeta_residue K
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
      (a := residue) (r := 1) ?_)
      (fun _ => Nat.cast_nonneg _)
      zero_le_one (by simpa using hsigma)
  change Tendsto _ _ (nhds residue)
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
    tendsto_natCast_atTop_atTop).congr
    fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum, Real.rpow_one]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
      Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ => Ideal.finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

private theorem numberFieldIdealWeight_summable
    (K : Type*) [Field K] [NumberField K] {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun I : Ideal (NumberField.RingOfIntegers K) =>
      1 / (Ideal.absNorm I : ℝ) ^ sigma) := by
  classical
  have houter : Summable (fun n : ℕ =>
      (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm I = n} : ℝ) / (n : ℝ) ^ sigma) := by
    apply (numberFieldIdealLSeries_summable K hsigma).norm.congr
    intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst n
      simp [Real.zero_rpow (ne_of_gt (zero_lt_one.trans hsigma))]
    · rw [if_neg hn, Complex.norm_of_nonneg (Nat.cast_nonneg _)]
      simp
  rw [summable_partition (s := fun n : ℕ =>
    {I : Ideal (NumberField.RingOfIntegers K) | Ideal.absNorm I = n})
    (fun _ => one_div_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _))]
  refine ⟨fun n => ?_, ?_⟩
  · exact (Ideal.finite_setOf_absNorm_eq
      (S := NumberField.RingOfIntegers K) n).summable
      (fun I => 1 / (Ideal.absNorm I : ℝ) ^ sigma)
  · convert houter using 1
    ext n
    let fiber : Set (Ideal (NumberField.RingOfIntegers K)) :=
      {I | Ideal.absNorm I = n}
    letI : Fintype fiber := (Ideal.finite_setOf_absNorm_eq n).fintype
    change (∑' I : fiber, 1 / (Ideal.absNorm I.1 : ℝ) ^ sigma) =
      (Nat.card fiber : ℝ) / (n : ℝ) ^ sigma
    rw [tsum_fintype, Nat.card_eq_fintype_card]
    simp_rw [show ∀ I : fiber, Ideal.absNorm I.1 = n from fun I => I.2]
    simp [nsmul_eq_mul, div_eq_mul_inv, mul_comm]
  · intro I
    exact ExistsUnique.intro (Ideal.absNorm I) (by simp) (fun n hn => by simpa using hn.symm)

/-- The source weight `1 / (k (N p)^(kσ))` on number-field prime powers. -/
def numberFieldPrimePowerWeight (K : Type*) [Field K] [NumberField K] (σ : ℝ)
    (q : PrimePowerIndex (NumberFieldPrime K)) : ℝ :=
  1 / ((q.2.1 : ℝ) *
    (Ideal.absNorm q.1.asIdeal : ℝ) ^ ((q.2.1 : ℝ) * σ))

theorem numberFieldPrimePowerWeight_nonnegative
    (K : Type*) [Field K] [NumberField K] (σ : ℝ) (q : PrimePowerIndex (NumberFieldPrime K)) :
    0 ≤ numberFieldPrimePowerWeight K σ q := by
  unfold numberFieldPrimePowerWeight
  exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- Prime-only no-gap theorem for genuine number-field prime ideals. The explicit summability
hypothesis is exactly the Euler-product convergence step for `σ > 1`. -/
theorem numberField_prime_only_no_gap
    (K : Type*) [Field K] [NumberField K]
    {P σ : ℝ} [Fact (0 < P)] (hσ : 1 < σ)
    (primeShift : NumberFieldPrime K → GoldenRegulatorCircle P)
    (hsum : Summable (numberFieldPrimePowerWeight K σ)) :
    sInf (Set.range fun n : {n : ℤ // n ≠ 0} =>
      spectralCoefficient (numberFieldPrimePowerWeight K σ) primeShift n) = 0 := by
  have _ := hσ
  exact spectralCoefficient_prime_only_no_gap primeShift
    (numberFieldPrimePowerWeight_nonnegative K σ) hsum

/-! ### Concrete nonempty witness -/

/-- Two nonzero rational circle shifts, representing angles `π` and `2π/3`. -/
def twoAngleShift (j : Fin 2) : GoldenRegulatorCircle (1 : ℝ) :=
  if j = 0 then ((1 / 2 : ℝ) : AddCircle (1 : ℝ))
  else ((1 / 3 : ℝ) : AddCircle (1 : ℝ))

theorem six_nsmul_twoAngleShift (j : Fin 2) : 6 • twoAngleShift j = 0 := by
  fin_cases j
  · change 6 • (if (0 : Fin 2) = 0 then
        ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) else
        ((1 / 3 : ℝ) : AddCircle (1 : ℝ))) = 0
    rw [if_pos rfl]
    rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff]
    exact ⟨3, by norm_num⟩
  · change 6 • (if (1 : Fin 2) = 0 then
        ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) else
        ((1 / 3 : ℝ) : AddCircle (1 : ℝ))) = 0
    rw [if_neg (by decide)]
    rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff]
    exact ⟨2, by norm_num⟩

/-- At `σ = 2`, the explicit nonzero mode `n = 6` simultaneously kills both sample angles. -/
theorem sigma_two_twoAngle_energy_six :
    fourierJumpEnergy
      (fun j : Fin 2 => 1 / ((j.1 + 2 : ℕ) : ℝ) ^ (2 : ℝ)) twoAngleShift 6 = 0 := by
  have hfourier (j : Fin 2) : fourier (6 : ℤ) (twoAngleShift j) = 1 := by
    rw [fourier_apply, show (6 : ℤ) • twoAngleShift j = 6 • twoAngleShift j by
      exact natCast_zsmul (twoAngleShift j) 6]
    rw [six_nsmul_twoAngleShift]
    simp
  unfold fourierJumpEnergy
  rw [tsum_fintype]
  simp [hfourier]

end

end D5.S3.Weil.PrimeOnly.PrimeOnlyNoGap
