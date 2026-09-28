/- GID: D5/S3/Quantum/Measurement/NonProjectiveDarkEffect
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/NonProjectiveDarkEffect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A permanent no-click effect need not be a projection. -/

import D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
import D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Measurement.NonProjectiveDarkEffect

open Matrix Filter Topology
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
open D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit

/-- **A permanent no-click effect need not be a projection.** For every `0 < a < 1`, the two
no-click Kraus operators `|0><0|` and `sqrt(a)|0><1|`, together with the click Kraus operator
`sqrt(1-a)|1><1|`, form a complete instrument. Its dual no-click map is explicit, its survival
effect stabilizes after one step, and the resulting permanent effect is not idempotent. The unit
vectors with permanent no-click probability one are exactly those with zero `|1>` component,
while the state `|1><1|` has permanent no-click probability `a` and zero weight on `|0><0|`. -/
theorem non_projective_dark_effect (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ (Q : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
      (L : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ)
      (F : Matrix (Fin 2) (Fin 2) ℂ),
      Q 0 = basisProjector (0 : Fin 2) ∧
      Q 1 = Matrix.single 0 1 (Real.sqrt a : ℂ) ∧
      L 0 = (Real.sqrt (1 - a) : ℂ) • basisProjector (1 : Fin 2) ∧
      (∑ i, (Q i)ᴴ * Q i) + ∑ i, (L i)ᴴ * L i = 1 ∧
      (∀ X, noClickDual Q X = X 0 0 • F) ∧
      (∀ N, 1 ≤ N → survival Q N = F) ∧
      Tendsto (survival Q) atTop (𝓝 F) ∧
      F = basisProjector (0 : Fin 2) + (a : ℂ) • basisProjector (1 : Fin 2) ∧
      F * F ≠ F ∧
      (∀ v : Fin 2 → ℂ, star v ⬝ᵥ v = 1 →
        (star v ⬝ᵥ (F *ᵥ v) = 1 ↔ v 1 = 0)) ∧
      (basisProjector (1 : Fin 2) * F).trace = (a : ℂ) ∧
      (basisProjector (1 : Fin 2) * ((L 0)ᴴ * L 0)).trace = ((1 - a : ℝ) : ℂ) ∧
      (basisProjector (1 : Fin 2) * basisProjector (0 : Fin 2)).trace = 0 := by
  classical
  let P0 : Matrix (Fin 2) (Fin 2) ℂ := basisProjector 0
  let P1 : Matrix (Fin 2) (Fin 2) ℂ := basisProjector 1
  let Q0 : Matrix (Fin 2) (Fin 2) ℂ := P0
  let Q1 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 0 1 (Real.sqrt a : ℂ)
  let L0 : Matrix (Fin 2) (Fin 2) ℂ := (Real.sqrt (1 - a) : ℂ) • P1
  let Q : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![Q0, Q1]
  let L : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ := fun _ => L0
  let F0 : Matrix (Fin 2) (Fin 2) ℂ := P0 + (a : ℂ) • P1
  have hsqrtA : (Real.sqrt a : ℂ) * (Real.sqrt a : ℂ) = (a : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt ha0.le
  have hsqrtOneSubA : (Real.sqrt (1 - a) : ℂ) * (Real.sqrt (1 - a) : ℂ) =
      ((1 - a : ℝ) : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (by linarith)
  have hcomp : (∑ i, (Q i)ᴴ * Q i) + ∑ i, (L i)ᴴ * L i = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q, Q0, Q1, L, L0, P0, P1, basisProjector, Fin.sum_univ_two,
        hsqrtA, hsqrtOneSubA]
  have hdual : ∀ X, noClickDual Q X = X 0 0 • F0 := by
    intro X
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [noClickDual, basisProjector, Fin.isValue, Fin.zero_eta, Fin.mk_one,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.conjTranspose_single, star_one,
        Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, RCLike.star_def, Complex.conj_ofReal, Matrix.add_apply,
        Matrix.single_apply_same, one_ne_zero, zero_ne_one, and_self, and_false, and_true,
        not_false_eq_true, Matrix.single_apply_of_ne, add_zero, zero_add, Matrix.smul_single,
        smul_eq_mul, Matrix.smul_apply, mul_zero, Q, Q0, Q1, F0, P0, P1]
    calc
      (Real.sqrt a : ℂ) * X 0 0 * (Real.sqrt a : ℂ) =
          X 0 0 * ((Real.sqrt a : ℂ) * (Real.sqrt a : ℂ)) := by ring
      _ = X 0 0 * (a : ℂ) := by rw [hsqrtA]
  have hfixed : noClickDual Q F0 = F0 := by
    rw [hdual]
    simp [F0, P0, P1, basisProjector]
  have hstable : ∀ N, 1 ≤ N → survival Q N = F0 := by
    intro N hN
    cases N with
    | zero => omega
    | succ n =>
        induction n with
        | zero =>
            rw [survival, hdual]
            simp [survival, F0, P0, P1, basisProjector]
        | succ n ih =>
            rw [survival, ih (by omega), hfixed]
  have hlimit0 : Tendsto (survival Q) atTop (𝓝 F0) := by
    exact tendsto_atTop_of_eventually_const (i₀ := 1) hstable
  obtain ⟨F, hlimit, _⟩ := survival_tendsto_maximal_fixed_effect Q L hcomp
  have hF : F = F0 := tendsto_nhds_unique hlimit hlimit0
  subst F
  have hnotIdempotent : F0 * F0 ≠ F0 := by
    intro h
    have hentry := congrArg Complex.re (congrFun (congrFun h (1 : Fin 2)) (1 : Fin 2))
    simp [F0, P0, P1, basisProjector, Matrix.mul_apply, Fin.sum_univ_two] at hentry
    nlinarith
  have hunitDirections : ∀ v : Fin 2 → ℂ, star v ⬝ᵥ v = 1 →
      (star v ⬝ᵥ (F0 *ᵥ v) = 1 ↔ v 1 = 0) := by
    intro v hunit
    have hunit' : star (v 0) * v 0 + star (v 1) * v 1 = 1 := by
      simpa only [Matrix.vec2_dotProduct, Pi.star_apply] using hunit
    constructor
    · intro hexpect
      have hexpect' : star (v 0) * v 0 + star (v 1) * ((a : ℂ) * v 1) = 1 := by
        simpa [F0, P0, P1, basisProjector, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two] using hexpect
      have hz : (((1 - a : ℝ) : ℂ) * (star (v 1) * v 1)) = 0 := by
        calc
          (((1 - a : ℝ) : ℂ) * (star (v 1) * v 1)) =
              (star (v 0) * v 0 + star (v 1) * v 1) -
                (star (v 0) * v 0 + star (v 1) * ((a : ℂ) * v 1)) := by
                  rw [Complex.ofReal_sub, Complex.ofReal_one]
                  ring
          _ = 1 - 1 := by rw [hunit', hexpect']
          _ = 0 := sub_self 1
      rcases mul_eq_zero.mp hz with hcoef | hprod
      · exact (Complex.ofReal_ne_zero.mpr (by linarith : 1 - a ≠ 0) hcoef).elim
      · rcases mul_eq_zero.mp hprod with hstar | hv
        · exact star_eq_zero.mp hstar
        · exact hv
    · intro hv
      simpa [F0, P0, P1, basisProjector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, hv] using hunit
  refine ⟨Q, L, F0, ?_, ?_, ?_, hcomp, hdual, hstable, hlimit0, rfl,
    hnotIdempotent, hunitDirections, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · simp [F0, P0, P1, basisProjector, Matrix.trace_single_mul]
  · simp [L, L0, P1, basisProjector, hsqrtOneSubA]
  · simp [basisProjector]

#print axioms non_projective_dark_effect

end D5.S3.Quantum.Measurement.NonProjectiveDarkEffect
