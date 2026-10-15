import D5.S3.Geometry.ODE.UniformLocalGlobalPasting
import Reg.Support.DependentFamily
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.LinearIsometry

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter
open scoped Topology
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.ODE.UniformLocalGlobalPasting
universe u

/-- The producer packs the three selected coordinates as nested Sigma types. -/
def signature : Signature where
  Params := Σ E : Type u, Σ _f : E → E, ℝ
  State p := ℝ → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Observe the actual local curve endpoint, without a proof-status predicate. -/
def actual : Realization signature.{u} :=
  realize signature (fun _ _ C => C 0) (fun e => nomatch e)

/-- Relocate that endpoint outside the certified open local time interval. -/
def relocated : Realization signature.{u} :=
  realize signature (fun _ p C => C (2 * p.2.2)) (fun e => nomatch e)

/-- Every original type, dictionary, hypothesis, and conclusion remains here.
Only the raw local witness occurrence C 0 is replaced by the selected readout. -/
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) {T : ℝ} (_hT : 0 < T)
    (_hlocal : ∀ x : E, ∃ C : ℝ → E,
      R.readout () ⟨E, f, T⟩ C = x ∧
        ∀ s ∈ Ioo (-T) T, HasDerivAt C (f (C s)) s)
    (x0 : E),
    ∃ γ : ℝ → E, γ 0 = x0 ∧ ∀ t : ℝ, HasDerivAt γ (f (γ t)) t

def sourceStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) {T : ℝ} (_hT : 0 < T)
    (_hlocal : ∀ x : E, ∃ C : ℝ → E, C 0 = x ∧
      ∀ s ∈ Ioo (-T) T, HasDerivAt C (f (C s)) s)
    (x0 : E),
    ∃ γ : ℝ → E, γ 0 = x0 ∧ ∀ t : ℝ, HasDerivAt γ (f (γ t)) t

theorem bridge : sourceStatement.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h E instE instNS f T hT hlocal x0
    exact h f hT hlocal x0
  · intro h E instE instNS f T hT hlocal x0
    exact h f hT hlocal x0

theorem actual_positive : arena.{u}.Law actual := by
  intro E instE instNS f T hT hlocal x0
  exact _root_.D5.S3.Geometry.ODE.UniformLocalGlobalPasting.exists_global_solution_of_uniform_local
    f hT hlocal x0

/-- These helpers reuse the existing logarithm/exponential derivative suppliers. -/
def logCurve (s : ℝ) : ℝ := -Real.log (1 - s)

theorem logCurve_hasDerivAt (s : ℝ) (hs : s < 1) :
    HasDerivAt logCurve (Real.exp (logCurve s)) s := by
  have hpos : 0 < 1 - s := by linarith
  have hd : HasDerivAt logCurve ((1 - s)⁻¹) s := by
    have hd0 := ((Real.hasDerivAt_log hpos.ne').comp s
      ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s))).neg
    change HasDerivAt logCurve (-((1 - s)⁻¹ * (0 - 1))) s at hd0
    exact hd0.congr_deriv (by ring)
  have he : Real.exp (logCurve s) = (1 - s)⁻¹ := by
    rw [logCurve, Real.exp_neg, Real.exp_log hpos]
  rwa [← he] at hd

theorem no_global_exponential (γ : ℝ → ℝ)
    (hγ : ∀ t : ℝ, HasDerivAt γ (Real.exp (γ t)) t) : False := by
  let z : ℝ → ℝ := fun t => Real.exp (-γ t) + t
  have hz (t : ℝ) : HasDerivAt z 0 t := by
    have he := (hγ t).neg.exp
    change HasDerivAt (fun s => Real.exp (-γ s))
      (Real.exp (-γ t) * (-Real.exp (γ t))) t at he
    have hc : Real.exp (-γ t) * (-Real.exp (γ t)) = -1 := by
      calc
        Real.exp (-γ t) * (-Real.exp (γ t)) =
            -(Real.exp (-γ t) * Real.exp (γ t)) := by ring
        _ = -Real.exp (-γ t + γ t) := by rw [Real.exp_add]
        _ = -1 := by simp
    rw [hc] at he
    convert! he.add (hasDerivAt_id t) using 1 <;> simp [z]
  have hconst (t : ℝ) : z t = z 0 :=
    isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
      (fun s _ => (hz s).differentiableAt.differentiableWithinAt)
      (fun s _ => (hz s).deriv) (mem_univ t) (mem_univ 0)
  have hbad := hconst (Real.exp (-γ 0) + 1)
  have hpos := Real.exp_pos (-γ (Real.exp (-γ 0) + 1))
  dsimp [z] at hbad
  linarith

abbrev Sample := ULift.{u} ℝ

def downMap : Sample.{u} →L[ℝ] ℝ :=
  (ContinuousLinearEquiv.ulift : Sample.{u} ≃L[ℝ] ℝ).toContinuousLinearMap

def upMap : ℝ →L[ℝ] Sample.{u} :=
  (ContinuousLinearEquiv.ulift : Sample.{u} ≃L[ℝ] ℝ).symm.toContinuousLinearMap

def sampleField (x : Sample.{u}) : Sample.{u} := ⟨Real.exp x.down⟩

def remoteCurve (x : Sample.{u}) (s : ℝ) : Sample.{u} :=
  if s = 1 then x else ⟨logCurve s⟩

theorem remoteCurve_at_one (x : Sample.{u}) : remoteCurve x 1 = x := by
  simp [remoteCurve]

theorem remoteCurve_derivative (x : Sample.{u}) (s : ℝ)
    (hs : s ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    HasDerivAt (remoteCurve x) (sampleField (remoteCurve x s)) s := by
  have hs1 : s < 1 := by linarith [hs.2]
  have hd := upMap.hasFDerivAt.comp_hasDerivAt s (logCurve_hasDerivAt s hs1)
  change HasDerivAt (fun t => (⟨logCurve t⟩ : Sample.{u}))
    (⟨Real.exp (logCurve s)⟩ : Sample.{u}) s at hd
  have hnear : remoteCurve x =ᶠ[𝓝 s] (fun t => (⟨logCurve t⟩ : Sample.{u})) := by
    filter_upwards [Iio_mem_nhds hs1] with t ht
    exact if_neg (ne_of_lt ht)
  rw [hnear.eq_of_nhds]
  exact hd.congr_of_eventuallyEq hnear

theorem no_global_sample (γ : ℝ → Sample.{u})
    (hγ : ∀ t : ℝ, HasDerivAt γ (sampleField (γ t)) t) : False := by
  apply no_global_exponential (fun t => (γ t).down)
  intro t
  have hd := downMap.hasFDerivAt.comp_hasDerivAt t (hγ t)
  change HasDerivAt (fun t => (γ t).down) (Real.exp (γ t).down) t at hd
  exact hd

theorem relocated_rejected : ¬ arena.{u}.Law relocated := by
  intro h
  have hlocal : ∀ x : Sample.{u}, ∃ C : ℝ → Sample.{u},
      relocated.readout () ⟨Sample.{u}, sampleField, (1 / 2 : ℝ)⟩ C = x ∧
        ∀ s ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2), HasDerivAt C (sampleField (C s)) s := by
    intro x
    refine ⟨remoteCurve x, ?_, remoteCurve_derivative x⟩
    change remoteCurve x (2 * (1 / 2 : ℝ)) = x
    norm_num only [mul_one_div, div_self (show (2 : ℝ) ≠ 0 by norm_num)]
    exact remoteCurve_at_one x
  obtain ⟨γ, _, hγ⟩ := h sampleField (T := (1 / 2 : ℝ)) (by norm_num) hlocal
    (⟨0⟩ : Sample.{u})
  exact no_global_sample γ hγ

theorem variation : Variation arena.{u} actual :=
  ⟨actual_positive, relocated, relocated_rejected⟩

theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨relocated, ?_, rfl, relocated_rejected⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨Sample.{u}, (fun _ => (⟨0⟩ : Sample.{u})), (1 / 2 : ℝ)⟩,
    (fun _ => (⟨0⟩ : Sample.{u})), (fun _ => (⟨1⟩ : Sample.{u})), ?_⟩
  intro h
  have he := congrArg ULift.down h
  change (0 : ℝ) = 1 at he
  exact zero_ne_one he

def registration : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

/-- Select the local witness's initial endpoint from the theorem telescope. -/
def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S3.Geometry.ODE.UniformLocalGlobalPasting
  coordinates := #[0, 3, 4]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "domain",
      "body", "arg", "body", "fn", "arg", "fn", "arg"]
    stateBinder := 7 }] }

register_information_theorem
  _root_.D5.S3.Geometry.ODE.UniformLocalGlobalPasting.exists_global_solution_of_uniform_local in arena
  readout via (realize signature.{u} (fun _ _ C => C 0) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)


open Lean in
run_meta do
  let env ← getEnv
  let sourceName : Lean.Name :=
    `D5.S3.Geometry.ODE.UniformLocalGlobalPasting.exists_global_solution_of_uniform_local
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == sourceName &&
      row.occurrence.key.registrationModule == env.header.mainModule)
    | throwError "Uniform local solution registration evidence is missing"
  match row.result with
  | .declaredValidated certificate =>
      unless row.escape.fromObject.isSome &&
          row.escape.continuation.any (fun continuation => continuation.kind == "open") &&
          row.escape.bridgeKind == "source-equivalence" &&
          certificate.sourceBinding.isSome do
        throwError "Uniform local solution lacks validated source-bound four-slot evidence"
  | .declaredUnresolved diagnostic =>
      throwError "Uniform local solution registration is unresolved: {diagnostic}"
  | .undeclared =>
      throwError "Uniform local solution registration is undeclared"

#print axioms registration
#print axioms bridge
#print axioms actual_positive
#print axioms logCurve_hasDerivAt
#print axioms no_global_exponential
#print axioms remoteCurve_derivative
#print axioms no_global_sample
#print axioms relocated_rejected
#print axioms variation
#print axioms sensitivity
#print axioms dependence

end Reg.D5.S3.Geometry.ODE.UniformLocalGlobalPasting
