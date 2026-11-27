import Lean
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Analytic.Polynomial.DiagonalPadeWindow

open D5.S3.Analytic.Polynomial.DiagonalPadeWindow
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Reg.Support.DiagonalPadeWindow
noncomputable section

abbrev poissonSignature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def poissonActual : Realization poissonSignature :=
  realize poissonSignature (fun _ _ z => Complex.exp z) (fun e => nomatch e)

def poissonRejected : Realization poissonSignature :=
  realize poissonSignature (fun _ _ _ => 0) (fun e => nomatch e)

/- Preserve the complete Poisson statement and its scalar instances. -/
open Lean Elab Term in
elab "poissonLaw% " readout:term : term => do
  let readout ← elabTerm readout none
  let source ← getConstInfo `D5.S3.Analytic.Polynomial.DiagonalPadeWindow.gaussian_poisson
  return source.type.replace fun expression =>
    if expression.isConstOf ``Complex.exp then some readout else none

def poissonArena : Arena where
  signature := poissonSignature
  Law R := poissonLaw% (R.readout () ())

private theorem poisson_bridge : (type_of% (@gaussian_poisson)) ↔
    poissonArena.Law poissonActual := Iff.rfl

private theorem poisson_rejected : ¬ poissonArena.Law poissonRejected := by
  intro h
  have h0 := h (α := Real.pi) Real.pi_pos 0
  simp only [poissonRejected, realize, tsum_zero] at h0
  have hr := congrArg Complex.re h0
  simp only [Complex.zero_re, Complex.ofReal_re] at hr
  have hs : Summable (fun j : ℤ => Real.exp (-Real.pi * (j : ℝ) ^ 2)) := by
    simpa only [pow_zero, one_mul, mul_zero, zero_mul, sub_zero] using
      summable_pow_mul_jacobiTheta₂_term_bound 0 (by norm_num : (0 : ℝ) < 1) 0
  have hp := hs.tsum_pos (fun j => (Real.exp_pos _).le) 0 (Real.exp_pos _)
  simp only [div_self Real.pi_ne_zero, Real.sqrt_one, div_one, zero_div, sub_zero] at hr
  linarith

private theorem poisson_dependence :
    ObservationalDependence poissonSignature poissonActual := by
  intro i
  refine ⟨(), 0, -1, ?_⟩
  intro h
  change Complex.exp (0 : ℂ) = Complex.exp (-1 : ℂ) at h
  have hn := congrArg norm h
  simp only [Complex.norm_exp, Complex.zero_re, Complex.neg_re,
    Complex.one_re, Real.exp_zero] at hn
  have he := Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)
  linarith

def poissonRegistration : Registration poissonArena (type_of% (@gaussian_poisson)) where
  actual := poissonActual
  bridge := poisson_bridge
  variation := ⟨@gaussian_poisson, poissonRejected, poisson_rejected⟩
  sensitivity := ⟨fun i => ⟨poissonRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, poisson_rejected⟩, fun e => nomatch e⟩
  dependence := poisson_dependence

end
end Reg.Support.DiagonalPadeWindow
