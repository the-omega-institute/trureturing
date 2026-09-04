/- GID: D5/S3/Midline/Cayley/ZeroHilbertCayleyUnitarity
   generality: I
   mirror-B: D5/B/S3/Midline/Cayley/ZeroHilbertCayleyUnitarity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Realize the Cayley defect on the multiplicity-expanded zero Hilbert space. -/

import D5.S3.Midline.Cayley.CayleyUnitarityDefect
import D5.S3.Observer.Approximation.ReadoutUpdateCommutatorFactorization
import D5.S3.Weil.ZetaBridge.RhLocatesZeroData
import Mathlib.Algebra.Star.Unitary
import Mathlib.NumberTheory.LSeries.ZetaZeros

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Midline.Cayley.ZeroHilbertCayleyUnitarity

open D5.S3.Midline.Cayley.CayleyUnitarityDefect
open D5.S3.Observer.Approximation.ReadoutUpdateCommutatorFactorization
open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.RhLocatesZeroData
open scoped ComplexConjugate ENNReal InnerProduct lp

noncomputable section

/-- A zero coordinate records a distinct zero and one copy of its multiplicity. -/
abbrev ZeroCoordinate (Z : ZeroData) := Sigma fun n => Fin (Z.multiplicity n)

private theorem cayley_coefficients_memℓp_infty (Z : ZeroData) :
    Memℓp (fun v : ZeroCoordinate Z => cayleyCoefficient (Z.zero v.1)) ∞ := by
  have hzetaContinuous : ContinuousAt riemannZeta 0 :=
    (differentiableAt_riemannZeta (by norm_num)).continuousAt
  have hzetaZero : riemannZeta 0 ≠ 0 := by
    rw [riemannZeta_zero]
    norm_num
  have hEventually : ∀ᶠ z : Complex in nhds 0, riemannZeta z ≠ 0 :=
    hzetaContinuous.eventually_ne hzetaZero
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hEventually
  have hlower (v : ZeroCoordinate Z) : epsilon ≤ ‖Z.zero v.1‖ := by
    by_contra hnot
    have hnear : Z.zero v.1 ∈ Metric.ball (0 : Complex) epsilon := by
      simpa [Metric.mem_ball] using lt_of_not_ge hnot
    have hnonzero := hball hnear
    have hzero : riemannZeta (Z.zero v.1) = 0 := by
      simpa [classicalZeta] using (Z.zero_isNontrivial v.1).1
    exact hnonzero hzero
  rw [memℓp_infty_iff]
  refine ⟨1 + epsilon⁻¹, ?_⟩
  rintro _ ⟨v, rfl⟩
  have hnormPositive : 0 < ‖Z.zero v.1‖ := lt_of_lt_of_le hepsilon (hlower v)
  change ‖cayleyCoefficient (Z.zero v.1)‖ ≤ 1 + epsilon⁻¹
  rw [cayleyCoefficient, norm_div]
  calc
    ‖Z.zero v.1 - 1‖ / ‖Z.zero v.1‖ ≤
        (‖Z.zero v.1‖ + 1) / ‖Z.zero v.1‖ := by
      apply (div_le_div_iff_of_pos_right hnormPositive).2
      simpa using norm_sub_le (Z.zero v.1) 1
    _ = 1 + 1 / ‖Z.zero v.1‖ := by
      rw [add_div, div_self (ne_of_gt hnormPositive)]
    _ ≤ 1 + epsilon⁻¹ := by
      simpa only [one_div] using
        add_le_add_right (one_div_le_one_div_of_le hepsilon (hlower v)) 1

/-- The Cayley coefficient family as a bounded coordinate vector. -/
noncomputable def cayleyCoefficientVector (Z : ZeroData) :
    lp (fun _ : ZeroCoordinate Z => Complex) ∞ :=
  boundedReadoutCoefficient
    (fun v : ZeroCoordinate Z => cayleyCoefficient (Z.zero v.1))
    (Or.inr (cayley_coefficients_memℓp_infty Z))

/-- The bounded Cayley operator on the multiplicity-expanded zero Hilbert space. -/
noncomputable def zeroCayleyOperator (Z : ZeroData) :
    ObserverHilbertSpace (ZeroCoordinate Z) →L[Complex]
      ObserverHilbertSpace (ZeroCoordinate Z) :=
  diagonalOperator (cayleyCoefficientVector Z)

@[simp] theorem cayleyCoefficientVector_apply (Z : ZeroData) (v : ZeroCoordinate Z) :
    cayleyCoefficientVector Z v = cayleyCoefficient (Z.zero v.1) := rfl

@[simp] theorem zeroCayleyOperator_apply (Z : ZeroData)
    (psi : ObserverHilbertSpace (ZeroCoordinate Z)) (v : ZeroCoordinate Z) :
    zeroCayleyOperator Z psi v = cayleyCoefficient (Z.zero v.1) * psi v := by
  simp [zeroCayleyOperator]

private theorem zeroCayleyOperator_single (Z : ZeroData) (v : ZeroCoordinate Z) (a : Complex) :
    zeroCayleyOperator Z (lp.single 2 v a) =
      lp.single 2 v (cayleyCoefficient (Z.zero v.1) * a) := by
  apply lp.ext
  funext w
  by_cases hwv : w = v
  · subst w
    simp
  · simp [lp.single_apply, hwv]

private theorem star_zeroCayleyOperator_single (Z : ZeroData)
    (v : ZeroCoordinate Z) (a : Complex) :
    star (zeroCayleyOperator Z) (lp.single 2 v a) =
      lp.single 2 v (conj (cayleyCoefficient (Z.zero v.1)) * a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply ext_inner_left Complex
  intro psi
  rw [ContinuousLinearMap.adjoint_inner_right, lp.inner_single_right, lp.inner_single_right]
  rw [zeroCayleyOperator_apply]
  simp [mul_left_comm, mul_comm]

private theorem zeroCayleyOperator_norm (Z : ZeroData)
    (hcoeff : ∀ n, ‖cayleyCoefficient (Z.zero n)‖ = 1)
    (psi : ObserverHilbertSpace (ZeroCoordinate Z)) :
    ‖zeroCayleyOperator Z psi‖ = ‖psi‖ := by
  have hsq : ‖zeroCayleyOperator Z psi‖ ^ 2 = ‖psi‖ ^ 2 := by
    calc
      ‖zeroCayleyOperator Z psi‖ ^ 2 =
          ‖zeroCayleyOperator Z psi‖ ^ (2 : Real) :=
        (Real.rpow_two _).symm
      _ = ∑' v : ZeroCoordinate Z, ‖zeroCayleyOperator Z psi v‖ ^ (2 : Real) :=
        lp.norm_rpow_eq_tsum (by norm_num) _
      _ = ∑' v : ZeroCoordinate Z, ‖psi v‖ ^ (2 : Real) := by
        congr 1
        funext v
        rw [zeroCayleyOperator_apply, norm_mul, hcoeff v.1, one_mul]
      _ = ‖psi‖ ^ (2 : Real) :=
        (lp.norm_rpow_eq_tsum (by norm_num) _).symm
      _ = ‖psi‖ ^ 2 := Real.rpow_two _
  nlinarith [norm_nonneg (zeroCayleyOperator Z psi), norm_nonneg psi]

private theorem zeroCayleyOperator_isometry_iff (Z : ZeroData) :
    Isometry (zeroCayleyOperator Z) ↔
      ∀ n, ‖cayleyCoefficient (Z.zero n)‖ = 1 := by
  constructor
  · intro hisometry n
    let v : ZeroCoordinate Z := ⟨n, ⟨0, Z.multiplicity_pos n⟩⟩
    have hnorm := hisometry.norm_map_of_map_zero
      (zeroCayleyOperator Z).map_zero
      (lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 v 1)
    rw [zeroCayleyOperator_single] at hnorm
    simpa using hnorm
  · intro hcoeff
    exact AddMonoidHomClass.isometry_of_norm (zeroCayleyOperator Z)
      (zeroCayleyOperator_norm Z hcoeff)

private theorem coefficient_star_mul_self (Z : ZeroData)
    (hcoeff : ∀ n, ‖cayleyCoefficient (Z.zero n)‖ = 1)
    (v : ZeroCoordinate Z) :
    conj (cayleyCoefficient (Z.zero v.1)) *
        cayleyCoefficient (Z.zero v.1) = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hcoeff]
  norm_num

private theorem zeroCayleyOperator_isUnit (Z : ZeroData)
    (hcoeff : ∀ n, ‖cayleyCoefficient (Z.zero n)‖ = 1) :
    IsUnit (zeroCayleyOperator Z) := by
  let inverseCoefficients : lp (fun _ : ZeroCoordinate Z => Complex) ∞ :=
    star (cayleyCoefficientVector Z)
  let inverseOperator :
      ObserverHilbertSpace (ZeroCoordinate Z) →L[Complex]
        ObserverHilbertSpace (ZeroCoordinate Z) :=
    diagonalOperator inverseCoefficients
  refine ⟨⟨zeroCayleyOperator Z, inverseOperator, ?_, ?_⟩, rfl⟩
  · ext psi v
    change cayleyCoefficient (Z.zero v.1) *
        (conj (cayleyCoefficient (Z.zero v.1)) * psi v) = psi v
    rw [← mul_assoc, mul_comm (cayleyCoefficient (Z.zero v.1)),
      coefficient_star_mul_self Z hcoeff v, one_mul]
  · ext psi v
    change conj (cayleyCoefficient (Z.zero v.1)) *
        (cayleyCoefficient (Z.zero v.1) * psi v) = psi v
    rw [← mul_assoc, coefficient_star_mul_self Z hcoeff v, one_mul]

private theorem zeroCayleyOperator_gram_iff_unitary (Z : ZeroData) :
    star (zeroCayleyOperator Z) * zeroCayleyOperator Z = 1 ↔
      zeroCayleyOperator Z ∈
        unitary (ObserverHilbertSpace (ZeroCoordinate Z) →L[Complex]
          ObserverHilbertSpace (ZeroCoordinate Z)) := by
  constructor
  · intro hgram
    have hisometry : Isometry (zeroCayleyOperator Z) := by
      apply AddMonoidHomClass.isometry_of_norm (zeroCayleyOperator Z)
      intro psi
      have hAdjoint :
          ContinuousLinearMap.adjoint (zeroCayleyOperator Z)
              (zeroCayleyOperator Z psi) = psi := by
        have happly := congrArg (fun operator => operator psi) hgram
        simpa [ContinuousLinearMap.star_eq_adjoint] using happly
      have hsq : ‖zeroCayleyOperator Z psi‖ ^ 2 = ‖psi‖ ^ 2 := by
        rw [norm_sq_eq_re_inner (𝕜 := Complex) (zeroCayleyOperator Z psi),
          norm_sq_eq_re_inner (𝕜 := Complex) psi]
        rw [← ContinuousLinearMap.adjoint_inner_left, hAdjoint]
      nlinarith [norm_nonneg (zeroCayleyOperator Z psi), norm_nonneg psi]
    have hcoeff := (zeroCayleyOperator_isometry_iff Z).mp hisometry
    exact (zeroCayleyOperator_isUnit Z hcoeff).mem_unitary_of_star_mul_self hgram
  · exact fun hunit => Unitary.star_mul_self_of_mem hunit

private theorem zeroCayleyOperator_defect_on_basis (Z : ZeroData)
    (v : ZeroCoordinate Z) :
    let basis := fun w : ZeroCoordinate Z =>
      lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 w 1
    (star (zeroCayleyOperator Z) * zeroCayleyOperator Z - 1) (basis v) =
      (defectScalar Z v.1 : Complex) • basis v := by
  dsimp only
  change
    star (zeroCayleyOperator Z)
        (zeroCayleyOperator Z
          (lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 v 1)) -
      lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 v 1 = _
  rw [zeroCayleyOperator_single, star_zeroCayleyOperator_single]
  apply lp.ext
  funext w
  by_cases hwv : w = v
  · subst w
    simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_single, Pi.single_eq_same,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [← Complex.normSq_eq_conj_mul_self, defectScalar, Complex.sq_norm]
    norm_cast
  · simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_single,
      Pi.single_eq_of_ne hwv, sub_self, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, mul_zero]

private theorem riemannHypothesis_iff_cayley_norm
    (Z : ZeroData)
    (hExhaustive : ∀ rho : Complex,
      riemannZeta rho = 0 →
      (¬ ∃ n : Nat, rho = -2 * (n + 1)) →
      rho ≠ 1 →
      ∃ n, Z.zero n = rho) :
    RiemannHypothesis ↔
      ∀ v : ZeroCoordinate Z, ‖cayleyCoefficient (Z.zero v.1)‖ = 1 := by
  have hOld := cayley_unitarity_defect_formula Z
  constructor
  · intro hRH v
    apply hOld.2.1.mp
    intro n
    simpa [AllZerosOnMidline, criticalAbscissa] using
      zeroData_zero_on_critical_line_of_rh hRH Z n
  · intro hnorm rho hzero hnotTrivial hone
    obtain ⟨n, hn⟩ := hExhaustive rho hzero hnotTrivial hone
    have hAll : AllZerosOnMidline Z := by
      apply hOld.2.1.mpr
      intro m
      let v : ZeroCoordinate Z := ⟨m, ⟨0, Z.multiplicity_pos m⟩⟩
      exact hnorm v
    rw [← hn]
    exact hAll n

private theorem cayley_norm_iff_gram (Z : ZeroData) :
    (∀ v : ZeroCoordinate Z, ‖cayleyCoefficient (Z.zero v.1)‖ = 1) ↔
      star (zeroCayleyOperator Z) * zeroCayleyOperator Z = 1 := by
  have hMultiplicity :
      (∀ v : ZeroCoordinate Z, ‖cayleyCoefficient (Z.zero v.1)‖ = 1) ↔
        ∀ n, ‖cayleyCoefficient (Z.zero n)‖ = 1 := by
    constructor
    · intro h n
      exact h ⟨n, ⟨0, Z.multiplicity_pos n⟩⟩
    · exact fun h v => h v.1
  have hGramIsometry :
      Isometry (zeroCayleyOperator Z) ↔
        star (zeroCayleyOperator Z) * zeroCayleyOperator Z = 1 := by
    constructor
    · intro hisometry
      have hadjoint :=
        (zeroCayleyOperator Z).isometry_iff_adjoint_comp_self.mp hisometry
      apply ContinuousLinearMap.ext
      intro psi
      have happly := congrArg (fun operator => operator psi) hadjoint
      simpa [ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp] using happly
    · intro hgram
      apply (zeroCayleyOperator Z).isometry_iff_adjoint_comp_self.mpr
      apply ContinuousLinearMap.ext
      intro psi
      have happly := congrArg (fun operator => operator psi) hgram
      simpa [ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp] using happly
  exact hMultiplicity.trans ((zeroCayleyOperator_isometry_iff Z).symm.trans hGramIsometry)

/-- The Cayley defect formula on the multiplicity-expanded zero Hilbert space,
together with its pointwise and global unitarity characterizations. -/
theorem cayley_unitarity_defect_formula_on_zero_hilbert_space
    (Z : ZeroData)
    (hExhaustive : ∀ rho : Complex,
      riemannZeta rho = 0 →
      (¬ ∃ n : Nat, rho = -2 * (n + 1)) →
      rho ≠ 1 →
      ∃ n, Z.zero n = rho) :
    (∀ v : ZeroCoordinate Z,
      let delta : Real := ‖cayleyCoefficient (Z.zero v.1)‖ ^ 2 - 1
      zeroCayleyOperator Z
          (lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 v 1) =
        cayleyCoefficient (Z.zero v.1) •
          lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 v 1 ∧
      (star (zeroCayleyOperator Z) * zeroCayleyOperator Z - 1)
          (lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 v 1) =
        (delta : Complex) •
          lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 v 1 ∧
      delta =
        (1 - 2 * (Z.zero v.1).re) / Complex.normSq (Z.zero v.1) ∧
      (‖cayleyCoefficient (Z.zero v.1)‖ = 1 ↔
        (Z.zero v.1).re = 1 / 2) ∧
      ((Z.zero v.1).re = 1 / 2 ↔
        ‖zeroCayleyOperator Z
            (lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 v 1)‖ =
          ‖lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 v 1‖)) ∧
    (RiemannHypothesis ↔
      ∀ v : ZeroCoordinate Z, ‖cayleyCoefficient (Z.zero v.1)‖ = 1) ∧
    (RiemannHypothesis ↔
      star (zeroCayleyOperator Z) * zeroCayleyOperator Z = 1) ∧
    (RiemannHypothesis ↔
      zeroCayleyOperator Z ∈
        unitary (ObserverHilbertSpace (ZeroCoordinate Z) →L[Complex]
          ObserverHilbertSpace (ZeroCoordinate Z))) ∧
    ((∀ v : ZeroCoordinate Z,
      ‖zeroCayleyOperator Z
          (lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 v 1)‖ =
        ‖lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 v 1‖) ↔
      zeroCayleyOperator Z ∈
        unitary (ObserverHilbertSpace (ZeroCoordinate Z) →L[Complex]
          ObserverHilbertSpace (ZeroCoordinate Z))) := by
  have hOld := cayley_unitarity_defect_formula Z
  have hRhNorm := riemannHypothesis_iff_cayley_norm Z hExhaustive
  have hNormGram := cayley_norm_iff_gram Z
  have hGramUnitary := zeroCayleyOperator_gram_iff_unitary Z
  have hBasisNorm :
      (∀ v : ZeroCoordinate Z,
        ‖zeroCayleyOperator Z
            (lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 v 1)‖ =
          ‖lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 v 1‖) ↔
        ∀ v : ZeroCoordinate Z, ‖cayleyCoefficient (Z.zero v.1)‖ = 1 := by
    constructor
    · intro h v
      have hv := h v
      rw [zeroCayleyOperator_single] at hv
      simpa using hv
    · intro h v
      rw [zeroCayleyOperator_single]
      simp [h v]
  refine ⟨?_, hRhNorm, hRhNorm.trans hNormGram,
    (hRhNorm.trans hNormGram).trans hGramUnitary,
    hBasisNorm.trans (hNormGram.trans hGramUnitary)⟩
  intro v
  dsimp only
  have hDefect := hOld.1 v.1
  have hPointwise :
      ‖cayleyCoefficient (Z.zero v.1)‖ = 1 ↔
        (Z.zero v.1).re = 1 / 2 := by
    have hzero : Z.zero v.1 ≠ 0 := by
      intro hzero
      have hpositive := (Z.zero_isNontrivial v.1).2.1
      rw [hzero] at hpositive
      norm_num at hpositive
    have hnormSq : Complex.normSq (Z.zero v.1) ≠ 0 :=
      mt Complex.normSq_eq_zero.mp hzero
    constructor
    · intro hnorm
      have hzero : defectScalar Z v.1 = 0 := by
        simp [defectScalar, hnorm]
      rw [hzero] at hDefect
      have hnumerator : 1 - 2 * (Z.zero v.1).re = 0 :=
        (div_eq_zero_iff).mp hDefect.2.2.symm |>.resolve_right hnormSq
      linarith
    · intro hmidline
      have hzero : defectScalar Z v.1 = 0 := by
        rw [hDefect.2.2, hmidline]
        norm_num
      rw [defectScalar] at hzero
      nlinarith [norm_nonneg (cayleyCoefficient (Z.zero v.1))]
  refine ⟨?_, ?_, hDefect.2.1.symm.trans hDefect.2.2, hPointwise, ?_⟩
  · rw [zeroCayleyOperator_single]
    simpa using
      (lp.single_smul (E := fun _ : ZeroCoordinate Z => Complex) 2 v
        (cayleyCoefficient (Z.zero v.1)) 1)
  · simpa [hDefect.2.1] using zeroCayleyOperator_defect_on_basis Z v
  · rw [zeroCayleyOperator_single]
    simpa using hPointwise.symm

#print axioms cayley_unitarity_defect_formula_on_zero_hilbert_space

end

end D5.S3.Midline.Cayley.ZeroHilbertCayleyUnitarity
