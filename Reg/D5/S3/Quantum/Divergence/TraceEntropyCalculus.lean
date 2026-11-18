import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Divergence.TraceEntropyCalculus

open LeanInformationAudit Matrix Filter
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.TraceEntropyCalculus
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Divergence.TraceEntropyCalculus

abbrev signature : Signature where
  Params := Σ i : Type u, Σ _ : Fintype i, DecidableEq i
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {i : Type u} [Fintype i] [DecidableEq i]
    (X : ℝ → Matrix i i ℂ) (V : Matrix i i ℂ) (t₀ : ℝ),
    HasDerivAt X V t₀ → (∀ᶠ t in 𝓝 t₀, (X t).IsHermitian) → (X t₀).PosDef →
    HasDerivAt (fun t => R.readout () ⟨i, inferInstance, inferInstance⟩
      ((X t * cfc Real.log (X t)).trace))
      (V * (cfc Real.log (X t₀) + 1)).trace.re t₀

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let X : ℝ → Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ :=
    fun t => Real.exp t • 1
  have hd : HasDerivAt X 1 0 := by
    simpa [X] using (Real.hasDerivAt_exp 0).smul_const
      (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)
  have hp (t : ℝ) : (X t).PosDef := Matrix.PosDef.one.smul (Real.exp_pos t)
  have hh : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 1 0 := by
    simpa [rejected, realize, X] using h X 1 0 hd
      (Eventually.of_forall fun t => (hp t).isHermitian) (hp 0)
  have he := (hasDerivAt_const (0 : ℝ) (0 : ℝ)).unique hh
  norm_num at he

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  exact ⟨⟨ULift.{u} Unit, inferInstance, inferInstance⟩, 0, 1,
    by norm_num [actual, realize]⟩

def family : Registration arena.{u} (type_of% (@hasDerivAt_trace_mul_log.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_trace_mul_log.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@hasDerivAt_trace_mul_log.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z.re) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.TraceEntropyCalculus.hasDerivAt_trace_mul_log.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.TraceEntropyCalculus.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.TraceEntropyCalculus
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Divergence.TraceEntropyCalculus
