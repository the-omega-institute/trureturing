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

end

end D5.S3.Weil.PrimeOnly.PrimeOnlyNoGap
