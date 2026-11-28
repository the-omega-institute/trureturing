/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicTwiningCharacter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicTwiningCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute convergence and the theta-eta formula for the actual cubic twining character. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicOscillatorTrace
import D5.S3.VertexAlgebra.Lattice.LatticeSectorCharacterWeilCovariance

/-! The real P48q Gram controls the charge sum. The actual integer-grade trace
groups the product of this fixed-charge sum and the sixteen-colour occupation
sum at three times the modular parameter. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicTwiningCharacter

open Complex LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeThetaCharacter
open P48qTwistedChargeAction (lattice g)
open P48qGramPositivity (nebeGram_posDef)
open P48qCubicOscillatorTrace
open LatticeDiscriminantTheta (gramReal)
open LatticeSectorCharacterWeilCovariance (oscillator_norm oscillator_eta)
open D5.S3.Fourier.MatrixGaussian (quadratic summable_norm_theta)
open D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation (integerEnergy)

noncomputable section

private abbrev FixedCharge := {a : Charge lattice // g a = a}
private abbrev Occupation := (Fin 16 × ℕ) →₀ ℕ

private def gradePhase (τ : ℂ) (n : ℤ) : ℂ :=
  exp (2 * Real.pi * I * τ * ((n : ℂ) - lattice.rank / 24))

/-- The native cubic lift's finite full-grade trace with the rank-48 vacuum shift. -/
def traceTerm (τ : ℂ) (n : ℤ) : ℂ :=
  actualFullGradeStandardLiftTrace n * gradePhase τ n

/-- The normalized cubic twining character, formed from all integral grades. -/
def actualCubicTwiningCharacter (τ : ℂ) : ℂ :=
  ∑' n : ℤ, traceTerm τ n

private def chargeTerm (τ : ℂ) (a : Charge lattice) : ℂ :=
  exp (2 * Real.pi * I * τ * (chargeEnergy lattice a : ℂ))

/-- Theta series of the integrally fixed charges with the original lattice energy. -/
def fixedChargeTheta (τ : ℂ) : ℂ :=
  ∑' a : FixedCharge, chargeTerm τ a.1

private def occupationQ (τ : ℂ) : ℂ := exp (2 * Real.pi * I * (3 * τ))

private def occupationTerm (τ : ℂ) (d : Occupation) : ℂ :=
  occupationQ τ ^ integerEnergy (Fin 16) d

private def vacuum (τ : ℂ) : ℂ :=
  exp (-2 * Real.pi * I * τ * lattice.rank / 24)

private def totalEnergy (x : FixedCharge × Occupation) : ℤ :=
  chargeEnergy lattice x.1.1 + 3 * (integerEnergy (Fin 16) x.2 : ℤ)

private theorem gradePhase_totalEnergy (τ : ℂ) (x : FixedCharge × Occupation) :
    gradePhase τ (totalEnergy x) = vacuum τ * (chargeTerm τ x.1.1 * occupationTerm τ x.2) := by
  unfold gradePhase totalEnergy vacuum chargeTerm occupationTerm occupationQ
  rw [← exp_nat_mul, ← exp_add, ← exp_add]
  congr 1
  push_cast
  ring

private theorem chargeTerm_eq_gaussian (τ : ℂ) (a : Charge lattice) :
    chargeTerm τ a = exp (Real.pi * I * τ *
      (quadratic (gramReal lattice) (fun i => (a i : ℝ)) : ℂ)) := by
  have h : quadratic (gramReal lattice) (fun i => (a i : ℝ)) =
      2 * (chargeEnergy lattice a : ℝ) := by
    simpa [quadratic, gramReal, realQuadratic, dotProduct, Matrix.mulVec,
      Finset.mul_sum, mul_assoc] using realQuadratic_charge lattice a
  unfold chargeTerm
  rw [h]
  push_cast
  congr 1
  ring

private def fixedChargeCutoff (n : ℤ) : Finset (Charge lattice) :=
  (positiveChargeCutoff lattice nebeGram_posDef n).filter (fun a => g a = a)

private abbrev GradeFiber (n : ℤ) := {x : FixedCharge × Occupation // totalEnergy x = n}

private abbrev OccupationFiber (n : ℤ) (a : Charge lattice) :=
  {d : Occupation // 3 * (integerEnergy (Fin 16) d : ℤ) = n - chargeEnergy lattice a}

private def gradeFiberEquiv (n : ℤ) :
    GradeFiber n ≃ Σ a : fixedChargeCutoff n, OccupationFiber n a.1 where
  toFun x := by
    have he := x.2
    change chargeEnergy lattice x.1.1.1 + 3 * (integerEnergy (Fin 16) x.1.2 : ℤ) = n at he
    have ha := chargeEnergy_nonneg lattice nebeGram_posDef x.1.1.1
    have hc : x.1.1.1 ∈ fixedChargeCutoff n := by
      refine Finset.mem_filter.mpr ⟨?_, x.1.1.2⟩
      simp only [positiveChargeCutoff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      rw [Int.toNat_of_nonneg (show 0 ≤ n by omega)]
      omega
    refine ⟨⟨x.1.1.1, hc⟩, ⟨x.1.2, ?_⟩⟩
    change 3 * (integerEnergy (Fin 16) x.1.2 : ℤ) = n - chargeEnergy lattice x.1.1.1
    omega
  invFun x := by
    have hf := (Finset.mem_filter.mp x.1.2).2
    have he := x.2.2
    refine ⟨(⟨x.1.1, hf⟩, x.2.1), ?_⟩
    change chargeEnergy lattice x.1.1 + 3 * (integerEnergy (Fin 16) x.2.1 : ℤ) = n
    omega
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Sigma.ext (Subtype.ext rfl)
    apply heq_of_eq
    rfl

private theorem occupationFiber_finite (τ : ℂ)
    (ho : Summable (fun d : Occupation => ‖occupationTerm τ d‖)) (n : ℤ) (a : Charge lattice) :
    Finite (OccupationFiber n a) := by
  let m := (n - chargeEnergy lattice a).toNat / 3
  have hz : occupationQ τ ^ m ≠ 0 := pow_ne_zero _ (exp_ne_zero _)
  apply Finite.of_summable_const (norm_pos_iff.mpr hz)
  refine (ho.subtype {d | 3 * (integerEnergy (Fin 16) d : ℤ) =
    n - chargeEnergy lattice a}).congr ?_
  intro d
  have hd := d.2
  change 3 * (integerEnergy (Fin 16) d.1 : ℤ) = n - chargeEnergy lattice a at hd
  have he : integerEnergy (Fin 16) d.1 = m := by
    dsimp [m]
    omega
  change ‖occupationQ τ ^ integerEnergy (Fin 16) d.1‖ = ‖occupationQ τ ^ m‖
  rw [he]

private theorem traceTerm_eq_fiber (τ : ℂ)
    (ho : Summable (fun d : Occupation => ‖occupationTerm τ d‖)) (n : ℤ) :
    (∑' x : GradeFiber n, gradePhase τ (totalEnergy x.1)) = traceTerm τ n := by
  classical
  let (a : fixedChargeCutoff n) : Finite (OccupationFiber n a.1) :=
    occupationFiber_finite τ ho n a.1
  let (a : fixedChargeCutoff n) : Fintype (OccupationFiber n a.1) := Fintype.ofFinite _
  calc
    _ = ∑' _x : GradeFiber n, gradePhase τ n :=
      tsum_congr (fun x => congrArg (gradePhase τ) x.2)
    _ = ∑ _x : (Σ a : fixedChargeCutoff n, OccupationFiber n a.1), gradePhase τ n := by
      rw [← (gradeFiberEquiv n).symm.tsum_eq, tsum_fintype]
    _ = _ := by
      rw [traceTerm, actual_full_grade_trace_eq_fixed_occupation]
      change _ = (∑ a ∈ fixedChargeCutoff n, (Nat.card (OccupationFiber n a) : ℂ)) *
        gradePhase τ n
      rw [Finset.sum_mul, Fintype.sum_sigma]
      calc
        _ = ∑ a : fixedChargeCutoff n, (Nat.card (OccupationFiber n a.1) : ℂ) * gradePhase τ n := by
          apply Finset.sum_congr rfl
          intro a _
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
        _ = _ := Finset.sum_coe_sort (fixedChargeCutoff n)
          (fun a : Charge lattice => (Nat.card (OccupationFiber n a) : ℂ) * gradePhase τ n)

/-- In the upper half-plane the actual normalized cubic trace converges
absolutely and equals the fixed-charge theta series divided by eta(3τ) to
the sixteenth power. -/
theorem actual_cubic_twining_character_eq_theta_div_eta (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun n : ℤ => ‖traceTerm τ n‖) ∧
      actualCubicTwiningCharacter τ = fixedChargeTheta τ / ModularForm.eta (3 * τ) ^ 16 := by
  have hτ3 : 0 < (3 * τ).im := by
    simpa [Complex.mul_im] using mul_pos (by norm_num : (0 : ℝ) < 3) hτ
  have hq : ‖occupationQ τ‖ < 1 := by
    simpa [occupationQ, Function.Periodic.qParam] using
      Function.Periodic.norm_qParam_lt_one (by norm_num : (0 : ℝ) < 1) hτ3
  have hc_all : Summable (fun a : Charge lattice => ‖chargeTerm τ a‖) :=
    (summable_norm_theta (gramReal lattice) nebeGram_posDef τ hτ).congr
      (fun a => congrArg norm (chargeTerm_eq_gaussian τ a).symm)
  have hc : Summable (fun a : FixedCharge => ‖chargeTerm τ a.1‖) :=
    hc_all.subtype {a | g a = a}
  have ho : Summable (fun d : Occupation => ‖occupationTerm τ d‖) := oscillator_norm 16 hq
  let f : FixedCharge × Occupation → ℂ := fun x => gradePhase τ (totalEnergy x)
  have habs : Summable (fun x => ‖f x‖) := by
    simpa only [f, gradePhase_totalEnergy, norm_mul] using (hc.mul_norm ho).mul_left ‖vacuum τ‖
  have hnorm (n : ℤ) : ‖traceTerm τ n‖ ≤ ∑' x : GradeFiber n, ‖f x.1‖ := by
    rw [← traceTerm_eq_fiber τ ho n]
    exact norm_tsum_le_tsum_norm (habs.subtype _)
  have hgroup := habs.hasSum.tsum_fiberwise totalEnergy
  have hsum : HasSum (traceTerm τ) (∑' x, f x) :=
    (habs.of_norm.hasSum.tsum_fiberwise totalEnergy).congr_fun
      (fun n => (traceTerm_eq_fiber τ ho n).symm)
  refine ⟨hgroup.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm, ?_⟩
  rw [actualCubicTwiningCharacter, hsum.tsum_eq]
  simp_rw [f, gradePhase_totalEnergy]
  rw [tsum_mul_left, ← tsum_mul_tsum_of_summable_norm hc ho]
  change vacuum τ * (fixedChargeTheta τ * ∑' d : Occupation, occupationTerm τ d) = _
  have hshift : vacuum τ = exp (-2 * Real.pi * I * (3 * τ) * (16 : ℕ) / 24) := by
    change exp (-2 * Real.pi * I * τ * (48 : ℂ) / 24) = _
    congr 1
    push_cast
    ring
  rw [mul_left_comm, hshift]
  simp only [occupationTerm, occupationQ, oscillator_eta 16 (3 * τ) hτ3,
    div_eq_mul_inv (fixedChargeTheta τ)]

run_cmd do
  let name := ``actual_cubic_twining_character_eq_theta_div_eta
  let axioms ← Lean.collectAxioms name
  unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
    throwError "Unexpected axiom closure for {name}: {axioms}"
  Lean.logInfo m!"{name} depends on axioms: {axioms}"

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicTwiningCharacter
