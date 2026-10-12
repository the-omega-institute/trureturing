/- GID: D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/InteractionPictureAsymptotics
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.claim; result=D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.result; claim=D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.claim
   digest: Integrable past interactions need not yield polynomial-generator asymptotics. -/

/- Source: Madou–Remizov–Vafadar (eds.), "Open problems in one-parameter
   operator semigroups theory", arXiv:2410.00416v2, p.21, Problem 29
   (A.E. Teretenkov), at n = 1.
   The fixed norm is the entrywise supremum norm on complex 3×3 matrices.
   Matrix exponentials use the product topology and are norm independent.
   Bounded matrix generators give C₀-semigroups for every real coupling;
   exp(sD) is a group, so its inverse is exp(-sD). Commutation with P
   gives invariance of both summands. The projection has rank two.
   Hyp requires past Lebesgue integrability for every real endpoint,
   hence includes the source's nonnegative endpoints. Expansion allows
   all matrix coefficients, including operators not supported on PB.
   admission_basis: open-problem-resolution (#15805; Refuted)
   escape_witness: none
   Direct frozen dependencies: none (pinned Mathlib only).
   Reuse: Matrix.exp_diagonal, Matrix.exp_units_conj, Pi.coe_exp,
     Complex.exp_eq_exp_ℂ, Complex.ofReal_exp, Real.exp_add,
     integrableOn_exp_Iic, integral_exp_Iic, integrableOn_exp_mul_Iic,
     Integrable.smul_const, integral_smul_const, Real.add_one_le_exp,
     Matrix.norm_entry_le_entrywise_sup_norm, NormedSpace.exp_continuous,
     Metric.eventually_nhds_iff, norm_le_norm_sub_add.
   Definitions:
     M3: proof_shape definition; consumers=coupling, Hyp, Expansion, P, D, N, E, S, T
     matrixContinuousENorm: proof_shape definition; consumers=Hyp, inner_integral, hypotheses
     coupling: proof_shape definition; consumers=Hyp, coupling_formula, first_integrand, second_integrand
     Hyp: proof_shape definition; consumers=claim, hypotheses
     Expansion: proof_shape definition; consumers=claim, no_expansion
     claim: proof_shape definition; consumer=result
     P: proof_shape definition; consumers=projection_algebra, projected_entry, hypotheses, result
     D: proof_shape definition; consumers=conjugate, exp_D, projection_algebra, hypotheses, result
     N: proof_shape definition; consumers=conjugate, coupling_formula, second_integrand, result
     E: proof_shape definition; consumers=second_integrand, inner_integral, hypotheses
     S: proof_shape definition; consumers=ST, changeBasis, conjugate, exp_perturbed, projected_entry
     T: proof_shape definition; consumers=ST, changeBasis, conjugate, exp_perturbed, projected_entry
     changeBasis: proof_shape definition; consumer=exp_perturbed
     polynomial: proof_shape definition; consumers=polynomial_continuous, locally_bounded, no_expansion
   Per-declaration proof_shape and live consumers:
     ST: bind-only; consumer=changeBasis
     conjugate: bind-only; consumer=exp_perturbed
     exp_D: bind-only; consumers=exp_perturbed, projected_entry, coupling_formula
     exp_perturbed: bind-only; consumer=projected_entry
     projected_entry: bind-only; consumer=growth
     coupling_formula: bind-only; consumers=first_integrand, second_integrand
     projection_algebra: bind-only; consumers=first_integrand, hypotheses
     first_integrand: bind-only; consumer=hypotheses
     second_integrand: bind-only; consumers=inner_integral, hypotheses
     inner_integral: bind-only; consumer=hypotheses
     hypotheses: bind-only; consumer=result
     entry_norm_le: bind-only; consumer=growth
     growth: bind-only; consumer=no_expansion
     polynomial_continuous: bind-only; consumer=locally_bounded
     locally_bounded: bind-only; consumer=no_expansion
     no_expansion: bind-only; consumer=result
     result: bind-only; designated refutation conclusion
   The proofs instantiate pinned algebra, integration, continuity and
   inequality results and normalize their consequences. Admission uses
   the external open-problem resolution exception, not an escape witness.
   The (0,2) entry is λ²(exp(s)-1)²/2. At s = 1/λ² its norm is at least
   1/(2λ²), whereas every polynomial-generator approximant is bounded
   near zero. No order-four error can reconcile these bounds. -/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.Quantum.Semigroups.InteractionPictureAsymptotics
open Matrix MeasureTheory Set Filter
open scoped Matrix Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.seminormedAddCommGroup
  Matrix.normedSpace Matrix.isBoundedSMul

abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ

@[instance_reducible]
private def matrixContinuousENorm : ContinuousENorm M3 :=
  inferInstanceAs (ContinuousENorm (Fin 3 → Fin 3 → ℂ))
attribute [local instance] matrixContinuousENorm

/-- Interaction-picture coupling. -/
def coupling (D N : M3) (s : ℝ) : M3 :=
  NormedSpace.exp ((-s : ℂ) • D) * N * NormedSpace.exp ((s : ℂ) • D)

/-- The past-integrability hypotheses for order one in three dimensions. -/
def Hyp (P D N : M3) : Prop :=
  P * P = P ∧ D * P = P * D ∧ P * N * P = 0 ∧
  (∀ t : ℝ, IntegrableOn (fun s => P * coupling D N s * P) (Iic t)) ∧
  (∀ t : ℝ, (∀ s₁, IntegrableOn
    (fun s₂ => P * coupling D N s₁ * coupling D N s₂ * P) (Iic s₁)) ∧
    IntegrableOn (fun s₁ => ∫ s₂ in Iic s₁,
      P * coupling D N s₁ * coupling D N s₂ * P) (Iic t))

/-- Polynomial preparation and polynomial generator with order-four error. -/
def Expansion (P D N : M3) : Prop :=
  ∃ (m : ℕ) (R G : Fin m → M3), ∀ t : ℝ, 0 < t →
    ∃ C δ : ℝ, 0 < δ ∧ ∀ l : ℝ, 0 < l → l < δ →
    ‖P * NormedSpace.exp ((-(t / l ^ 2) : ℂ) • D) *
      NormedSpace.exp (((t / l ^ 2) : ℂ) • (D + (l : ℂ) • N)) * P -
      NormedSpace.exp ((t : ℂ) • ∑ j : Fin m, ((l : ℂ) ^ (j : ℕ)) • G j) *
        ∑ j : Fin m, ((l : ℂ) ^ (j : ℕ)) • R j‖ ≤ C * l ^ 4

def claim : Prop := ∀ P D N : M3, Hyp P D N → Expansion P D N

private def P : M3 := diagonal ![1, 0, 1]
private def D : M3 := diagonal ![-3, -2, -1]
private def N : M3 := !![0, 1, 0; 0, 0, 1; 0, 0, 0]
private def E : M3 := !![0, 0, 1; 0, 0, 0; 0, 0, 0]

/-- A polynomial change of basis diagonalizes the perturbed generator. -/
private def S (l : ℝ) : M3 := !![1, l, (l : ℂ)^2 / 2; 0, 1, l; 0, 0, 1]
private def T (l : ℝ) : M3 := !![1, -l, (l : ℂ)^2 / 2; 0, 1, -l; 0, 0, 1]

private lemma ST (l : ℝ) : S l * T l = 1 ∧ T l * S l = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [S, T, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, Fin.ext_iff, -Fin.val_eq_zero_iff] <;> ring

private def changeBasis (l : ℝ) : M3ˣ :=
  ⟨S l, T l, (ST l).1, (ST l).2⟩

private lemma conjugate (s l : ℝ) :
    (s : ℂ) • (D + (l : ℂ) • N) = S l * ((s : ℂ) • D) * T l := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [S, T, D, N, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal, Matrix.smul_apply, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Pi.smul_apply, Fin.ext_iff, -Fin.val_eq_zero_iff] <;> ring

private lemma exp_D (s : ℝ) : NormedSpace.exp ((s : ℂ) • D) =
    diagonal ![(Real.exp (-3*s) : ℂ), Real.exp (-2*s), Real.exp (-s)] := by
  rw [D, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp only [Pi.coe_exp, Pi.smul_apply, smul_eq_mul,
    ← Complex.exp_eq_exp_ℂ]
  all_goals
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring

private lemma exp_perturbed (s l : ℝ) :
    NormedSpace.exp ((s : ℂ) • (D + (l : ℂ) • N)) =
      S l * diagonal ![(Real.exp (-3*s) : ℂ), Real.exp (-2*s),
        Real.exp (-s)] * T l := by
  rw [conjugate]
  have h := Matrix.exp_units_conj (changeBasis l) ((s : ℂ) • D)
  change NormedSpace.exp (S l * ((s : ℂ) • D) * T l) =
    S l * NormedSpace.exp ((s : ℂ) • D) * T l at h
  rw [h, exp_D]

private lemma projected_entry (s l : ℝ) :
    (P * NormedSpace.exp ((-s : ℂ) • D) *
      NormedSpace.exp ((s : ℂ) • (D + (l : ℂ) • N)) * P) 0 2 =
      ((l^2 / 2 * (Real.exp s - 1)^2 : ℝ) : ℂ) := by
  rw [show (-s : ℂ) = ((-s : ℝ) : ℂ) by simp, exp_D, exp_perturbed]
  simp [P, S, T, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply,
    Fin.ext_iff, -Fin.val_eq_zero_iff, -Complex.ofReal_exp]
  have h0 : Real.exp (3*s) * Real.exp (-(3*s)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h1 : Real.exp (3*s) * Real.exp (-(2*s)) = Real.exp s := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (3*s) * Real.exp (-s) = (Real.exp s)^2 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hr : Real.exp (3*s) *
      (Real.exp (-(3*s)) * (l^2/2) +
        (-(l * Real.exp (-(2*s)) * l) + l^2/2 * Real.exp (-s))) =
        l^2/2 * (Real.exp s - 1)^2 := by
    calc
      _ = l^2/2 * (Real.exp (3*s) * Real.exp (-(3*s)) -
          2 * (Real.exp (3*s) * Real.exp (-(2*s))) +
          Real.exp (3*s) * Real.exp (-s)) := by ring
      _ = _ := by rw [h0, h1, h2]; ring
  convert congrArg (fun x : ℝ => (x : ℂ)) hr using 1 <;> push_cast <;> ring

private lemma coupling_formula (s : ℝ) : coupling D N s = Real.exp s • N := by
  unfold coupling
  rw [show (-s : ℂ) = ((-s : ℝ) : ℂ) by simp, exp_D, exp_D]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal,
      Matrix.smul_apply, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Fin.ext_iff, -Fin.val_eq_zero_iff, -Complex.ofReal_exp]
  all_goals
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring

private lemma projection_algebra :
    P * P = P ∧ D * P = P * D ∧ P * N * P = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [P, D, N, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.ext_iff, -Fin.val_eq_zero_iff]

private lemma first_integrand (s : ℝ) : P * coupling D N s * P = 0 := by
  rw [coupling_formula, Matrix.mul_smul, Matrix.smul_mul, projection_algebra.2.2,
    smul_zero]

private lemma second_integrand (s u : ℝ) :
    P * coupling D N s * coupling D N u * P =
      Real.exp u • (Real.exp s • E) := by
  rw [coupling_formula, coupling_formula]
  have ha : P * N * N * P = E := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, N, E, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal,
        Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.ext_iff, -Fin.val_eq_zero_iff]
  simp only [Matrix.mul_smul, Matrix.smul_mul, ha]

private lemma inner_integral (s : ℝ) :
    (∫ u in Iic s, P * coupling D N s * coupling D N u * P) =
      Real.exp (2*s) • E := by
  simp_rw [second_integrand]
  rw [integral_smul_const, integral_exp_Iic, smul_smul, ← Real.exp_add]
  congr 2
  ring

private lemma hypotheses : Hyp P D N := by
  refine ⟨projection_algebra.1, projection_algebra.2.1, projection_algebra.2.2,
    ?_, ?_⟩
  · intro t
    simp only [first_integrand]
    exact (integrableOn_zero (ε' := M3))
  · intro t
    constructor
    · intro s
      simp_rw [second_integrand]
      unfold IntegrableOn
      exact (integrableOn_exp_Iic s).smul_const (Real.exp s • E)
    · simp_rw [inner_integral]
      unfold IntegrableOn
      exact (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 2) t).smul_const E

private lemma entry_norm_le (A : M3) : ‖A 0 2‖ ≤ ‖A‖ :=
  Matrix.norm_entry_le_entrywise_sup_norm A

private lemma growth (l : ℝ) (hl : 0 < l) :
    1 ≤ 2 * l^2 * ‖P * NormedSpace.exp ((-(1 / l^2) : ℂ) • D) *
      NormedSpace.exp (((1 / l^2) : ℂ) • (D + (l : ℂ) • N)) * P‖ := by
  have hq : 0 < l^2 := sq_pos_of_pos hl
  have hx : 0 ≤ 1 / l^2 := (div_pos zero_lt_one hq).le
  have he : 1 / l^2 ≤ Real.exp (1 / l^2) - 1 := by
    linarith [Real.add_one_le_exp (1 / l^2)]
  have hs : (1 / l^2)^2 ≤ (Real.exp (1 / l^2) - 1)^2 :=
    pow_le_pow_left₀ hx he 2
  have hentry := entry_norm_le (P * NormedSpace.exp ((-(1 / l^2) : ℂ) • D) *
    NormedSpace.exp (((1 / l^2) : ℂ) • (D + (l : ℂ) • N)) * P)
  have hp := projected_entry (1 / l^2) l
  simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_one] at hp
  rw [hp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (div_nonneg hq.le (by norm_num)) (sq_nonneg _))] at hentry
  calc
    1 = 2 * l^2 * (l^2 / 2 * (1 / l^2)^2) := by
      field_simp
    _ ≤ 2 * l^2 * (l^2 / 2 * (Real.exp (1 / l^2) - 1)^2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hs (div_nonneg hq.le (by norm_num)))
        (mul_nonneg (by norm_num) hq.le)
    _ ≤ _ := mul_le_mul_of_nonneg_left hentry (mul_nonneg (by norm_num) hq.le)

private def polynomial {m : ℕ} (A : Fin m → M3) (l : ℝ) : M3 :=
  ∑ j : Fin m, ((l : ℂ) ^ (j : ℕ)) • A j

private lemma polynomial_continuous {m : ℕ} (A : Fin m → M3) :
    Continuous (polynomial A) := by
  unfold polynomial
  fun_prop

private lemma locally_bounded {m : ℕ} (R G : Fin m → M3) :
    ∃ B ε : ℝ, 0 < B ∧ 0 < ε ∧ ∀ l : ℝ, |l| < ε →
      ‖NormedSpace.exp (polynomial G l) * polynomial R l‖ ≤ B := by
  let f : ℝ → M3 := fun l => NormedSpace.exp (polynomial G l) * polynomial R l
  have hexp : Continuous (NormedSpace.exp : M3 → M3) := by
    open scoped Matrix.Norms.Operator in
      exact NormedSpace.exp_continuous
  have hf : Continuous f :=
    (hexp.comp (polynomial_continuous G)).mul (polynomial_continuous R)
  have hn : Continuous (fun l => ‖f l‖) := hf.norm
  have hb : ‖f 0‖ < ‖f 0‖ + 1 := by linarith
  have he : ∀ᶠ l in 𝓝 (0 : ℝ), ‖f l‖ < ‖f 0‖ + 1 :=
    hn.continuousAt.tendsto.eventually (gt_mem_nhds hb)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨‖f 0‖ + 1, ε, by positivity, hε, ?_⟩
  intro l hl
  exact (he (by simpa [Real.dist_eq] using hl)).le

private lemma no_expansion : ¬ Expansion P D N := by
  intro h
  obtain ⟨m, R, G, h⟩ := h
  obtain ⟨C, δ, hδ, h⟩ := h 1 zero_lt_one
  obtain ⟨B, ε, hB, hε, hb⟩ := locally_bounded R G
  let H : ℝ := |C| + B
  have hH : 0 < H := by dsimp [H]; positivity
  let a : ℝ := min δ (min ε (min 1 (1 / (2 * (H + 1)))))
  have ha : 0 < a := by dsimp [a]; positivity
  let l : ℝ := a / 2
  have hl : 0 < l := by dsimp [l]; positivity
  have hla : l < a := by dsimp [l]; linarith
  have hδl : l < δ := hla.trans_le (min_le_left _ _)
  have hεl : l < ε := hla.trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hl1 : l < 1 := hla.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hlr : l < 1 / (2 * (H + 1)) := hla.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let A : M3 := P * NormedSpace.exp ((-(1 / l^2) : ℂ) • D) *
    NormedSpace.exp (((1 / l^2) : ℂ) • (D + (l : ℂ) • N)) * P
  let F : M3 := NormedSpace.exp (polynomial G l) * polynomial R l
  have hF : ‖F‖ ≤ B := hb l (by simpa [abs_of_pos hl] using hεl)
  have herr : ‖A - F‖ ≤ C * l^4 := by
    simpa [A, F, polynomial] using h l hl hδl
  have hpow : l^4 ≤ 1 := pow_le_one₀ hl.le hl1.le
  have hC : C * l^4 ≤ |C| := by
    calc
      _ ≤ |C| * l^4 := mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hl.le _)
      _ ≤ |C| := mul_le_of_le_one_right (abs_nonneg C) hpow
  have hnorm : ‖A‖ ≤ H := by
    calc
      _ ≤ ‖A - F‖ + ‖F‖ := norm_le_norm_sub_add A F
      _ ≤ C * l^4 + B := add_le_add herr hF
      _ ≤ H := by dsimp [H]; linarith
  have hg : 1 ≤ 2 * l^2 * ‖A‖ := growth l hl
  have hu : 1 ≤ 2 * l^2 * H :=
    hg.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))
  have hr : l * (2 * (H + 1)) < 1 :=
    (lt_div_iff₀ (by positivity : 0 < 2 * (H + 1))).mp hlr
  have hs : l^2 ≤ l := by nlinarith
  have hsH := mul_le_mul_of_nonneg_right hs hH.le
  nlinarith

/-- Past-integrability alone does not imply polynomial-generator asymptotics. -/
theorem result : ¬ claim := by
  intro h
  exact no_expansion (h P D N hypotheses)

end D5.S3.Quantum.Semigroups.InteractionPictureAsymptotics
