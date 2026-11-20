/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSMonicLevelGraphs
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSMonicLevelGraphs
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSRegularLevelGraphs]
   utility: none
   digest: A monic polynomial family has a countable cover by differentiable implicit graphs. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSRegularLevelGraphs
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Even at a multiple root, some preceding derivative has a regular zero.
Monicity guarantees a finite bound on the derivative required. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSMonicLevelGraphs

open Set Polynomial PeriodicMPSRegularLevelGraphs

universe u

variable {σ : Type u} [Fintype σ]

noncomputable section

abbrev Parameters (σ : Type*) := (σ → ℝ) × ℝ

/-- First evaluate the coefficients at the base, then evaluate the fiber polynomial. -/
def evalFamily (p : Polynomial (MvPolynomial σ ℝ)) (x : Parameters σ) : ℝ :=
  p.eval₂ (MvPolynomial.eval x.1) x.2

private lemma analyticAt_evalFamily (p : Polynomial (MvPolynomial σ ℝ)) (x : Parameters σ) :
    AnalyticAt ℝ (evalFamily p) x := by
  induction p using Polynomial.induction_on' with
  | monomial n c =>
    have hc : AnalyticAt ℝ (fun y : Parameters σ => MvPolynomial.eval y.1 c) x := by
      have h : AnalyticAt ℝ (fun z : σ → ℝ => MvPolynomial.aeval z c) x.1 :=
        AnalyticAt.aeval_mvPolynomial
          (fun i => (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ).analyticAt _) c
      exact h.comp ((ContinuousLinearMap.fst ℝ (σ → ℝ) ℝ).analyticAt x)
    have h₂ : AnalyticAt ℝ (fun y : Parameters σ => y.2) x :=
      (ContinuousLinearMap.snd ℝ (σ → ℝ) ℝ).analyticAt _
    have h : evalFamily (monomial n c) =
        fun y : Parameters σ => MvPolynomial.eval y.1 c * y.2 ^ n := by
      funext y
      exact eval₂_monomial _ _
    rw [h]
    exact hc.mul (h₂.pow n)
  | add p q hp hq =>
    have h : evalFamily (p + q) = evalFamily p + evalFamily q := by
      funext y
      exact eval₂_add _ _
    rw [h]
    exact hp.add hq

private lemma partial_derivative (p : Polynomial (MvPolynomial σ ℝ)) (x : Parameters σ) :
    (fderiv ℝ (evalFamily p) x ∘L ContinuousLinearMap.inr ℝ (σ → ℝ) ℝ) 1 =
      evalFamily p.derivative x := by
  let f := evalFamily p
  let i : ℝ → Parameters σ := fun t => (x.1, t)
  have hi : HasDerivAt i (0, 1) x.2 := (hasDerivAt_const x.2 x.1).prodMk
    (hasDerivAt_id _)
  have hf := (analyticAt_evalFamily p x).hasStrictFDerivAt.hasFDerivAt
  have h := hf.comp_hasDerivAt_of_eq _ hi (show x = i x.2 by rfl)
  have h' := ((p.map (MvPolynomial.eval x.1)).hasDerivAt x.2)
  have h'' : HasDerivAt (f ∘ i) (evalFamily p.derivative x) x.2 := by
    simpa [Function.comp_def, f, i, evalFamily, derivative_map, eval_map] using h'
  change fderiv ℝ f x (0, 1) = evalFamily p.derivative x
  exact h.deriv.symm.trans h''.deriv

private lemma invertible_of_ne (f : ℝ →L[ℝ] ℝ) (h : f 1 ≠ 0) : f.IsInvertible := by
  let u := Units.mk0 (f 1) h
  let e : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfUnit u).toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  apply ContinuousLinearMap.ext
  intro t
  have hf : f (t • (1 : ℝ)) = t • f 1 := map_smul f t 1
  change f 1 * t = f t
  simpa [smul_eq_mul, mul_comm] using hf.symm

private lemma top_derivative_ne {p : ℝ[X]} (hp : p.Monic) (x : ℝ) :
    ((derivative^[p.natDegree]) p).eval x ≠ 0 := by
  let d := p.natDegree
  let q := (derivative^[d]) p
  have hq : q.natDegree = 0 :=
    Nat.eq_zero_of_le_zero ((natDegree_iterate_derivative p d).trans_eq (Nat.sub_self _))
  change q.eval x ≠ 0
  rw [eq_C_of_natDegree_eq_zero hq, eval_C]
  change ((derivative^[d]) p).coeff 0 ≠ 0
  rw [coeff_iterate_derivative, zero_add, Nat.descFactorial_self]
  change d.factorial • p.leadingCoeff ≠ 0
  simp [hp, nsmul_eq_mul, Nat.factorial_ne_zero]

/-- The zero set of a monic polynomial family is contained in countably
many differentiable graphs over the base. -/
theorem countable_cover_monic_level {p : Polynomial (MvPolynomial σ ℝ)} (hp : p.Monic) :
    ∃ (ι : Type u) (_ : Countable ι) (D : ι → Set (σ → ℝ)) (g : ι → (σ → ℝ) → ℝ),
      (∀ i, DifferentiableOn ℝ (g i) (D i)) ∧
      {x | evalFamily p x = 0} ⊆ ⋃ i, (fun y => (y, g i y)) '' D i := by
  classical
  let f (n : ℕ) (x : Parameters σ) := evalFamily ((derivative^[n]) p) x
  let A (n : ℕ) : Set (Parameters σ) := {x | f n x = 0 ∧ f (n + 1) x ≠ 0}
  have hcut (x : Parameters σ) (hx : evalFamily p x = 0) : ∃ n, x ∈ A n := by
    have h : ∃ n, f n x ≠ 0 := by
      let q := p.map (MvPolynomial.eval x.1)
      refine ⟨q.natDegree, ?_⟩
      simpa [f, q, evalFamily, iterate_derivative_map, eval_map] using
        top_derivative_ne (hp.map (MvPolynomial.eval x.1)) x.2
    have hpos : Nat.find h ≠ 0 := by
      intro he
      exact Nat.find_spec h (by simpa [he, f] using hx)
    let n := Nat.find h - 1
    have hn : n + 1 = Nat.find h := by dsimp [n]; omega
    have hlt : n < Nat.find h := by omega
    exact ⟨n, (not_not.mp (Nat.find_min h hlt)), hn ▸ Nat.find_spec h⟩
  have cover (n : ℕ) :=
    countable_cover_regular_level (f n) (A n) 0
      (fun _ hx => hx.1)
      (fun x _ => (analyticAt_evalFamily _ x).contDiffAt)
      (fun x hx => invertible_of_ne _ (by
        rw [partial_derivative]
        simpa only [f, Function.iterate_succ_apply'] using hx.2))
  choose C D g hC hg hcov using cover
  have hcount (n : ℕ) : Countable (C n) := (hC n).to_subtype
  refine ⟨Σ n : ℕ, C n, inferInstance, fun i => D i.1 i.2, fun i => g i.1 i.2,
    fun i => hg i.1 i.2, ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := hcut x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov n hn)
  exact mem_iUnion.mpr ⟨⟨n, i⟩, hi⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSMonicLevelGraphs
