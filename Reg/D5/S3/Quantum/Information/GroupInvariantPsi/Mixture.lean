import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.GroupInvariantPsi.Mixture
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Information.GroupInvariantPsi.Mixture

open _root_.D5.S3.Quantum.Information.GroupInvariantPsi
open _root_.D5.S3.Quantum.Information.GroupInvariantPsi.Mixture
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
universe u

abbrev traceSignature : Signature where
  Params := Σ ι : Type u, Fintype ι × DecidableEq ι × (ι → ℝ) × ℝ
  State k := k.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def traceActual : Realization traceSignature.{u} :=
  realize traceSignature (fun _ k p => by
    letI : Fintype k.1 := k.2.1
    letI : DecidableEq k.1 := k.2.2.1
    exact (Matrix.trace
      (_root_.D5.S3.Quantum.Matrix.SpectralPower.mpow
          (Matrix.diagonal fun i => (p i : ℂ)) k.2.2.2.2 *
        _root_.D5.S3.Quantum.Matrix.SpectralPower.mpow
          (Matrix.diagonal fun i => (k.2.2.2.1 i : ℂ)) (1 - k.2.2.2.2))).re)
    (fun e => nomatch e)

def traceRejected : Realization traceSignature.{u} :=
  realize traceSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev traceArena : Arena where
  signature := traceSignature.{u}
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (p q : ι → ℝ) (s : ℝ),
    R.readout () ⟨ι, inferInstance, inferInstance, q, s⟩ p =
      ∑ i, p i ^ s * q i ^ (1 - s)

private theorem traceRejectedLaw : ¬ traceArena.{u}.Law traceRejected := by
  intro h
  have he := h (ι := ULift.{u} Unit) (fun _ => 1) (fun _ => 1) 1
  norm_num [traceRejected, realize] at he

private theorem traceDependence : ObservationalDependence traceSignature.{u} traceActual := by
  intro i
  let k : traceSignature.{u}.Params :=
    ⟨ULift.{u} Unit, inferInstance, inferInstance, (fun _ => 1), 1⟩
  refine ⟨k, (fun _ => 0), (fun _ => 1), ?_⟩
  dsimp only [traceActual, realize, k]
  rw [trace_pow_diag, trace_pow_diag]
  norm_num

def traceEvidence : Registration traceArena.{u} (type_of% @trace_pow_diag.{u}) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨@trace_pow_diag, traceRejected, traceRejectedLaw⟩
  sensitivity := ⟨fun i => ⟨traceRejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, traceRejectedLaw⟩,
    fun e => nomatch e⟩
  dependence := traceDependence

def traceRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@trace_pow_diag.{u}) (Realization traceSignature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Information.GroupInvariantPsi.Mixture.trace_pow_diag.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Information.GroupInvariantPsi.Mixture.traceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨traceArena⟩
  objectArena := .source ⟨traceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source traceArena ⟨traceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature traceActual.readout traceActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.GroupInvariantPsi.Mixture
    definition := none
    coordinates := #[0, 1, 2, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


abbrev twirlSignature : Signature where
  Params := Σ d : ℕ, Σ G : Type u, Σ group : Group G,
    letI := group; Fintype G × (G →* Equiv.Perm (Fin d)) × ℕ
  State k := Fin k.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := Matrix (Fin k.2.2.2.2.2 → Fin k.1) (Fin k.2.2.2.2.2 → Fin k.1) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def twirlActual : Realization twirlSignature.{u} :=
  realize twirlSignature (fun _ k p => by
    letI : Group k.2.1 := k.2.2.1
    letI : Fintype k.2.1 := k.2.2.2.1
    exact Defs.twirlPower (permutationRepresentation k.2.2.2.2.1)
      (Matrix.diagonal fun i => (p i : ℂ)) k.2.2.2.2.2) (fun e => nomatch e)

def twirlRejected : Realization twirlSignature.{u} :=
  realize twirlSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev twirlArena : Arena where
  signature := twirlSignature.{u}
  Law R := ∀ {d : ℕ} {G : Type u} [Group G] [Fintype G]
    (σ : G →* Equiv.Perm (Fin d)) (p : Fin d → ℝ) (n : ℕ),
    R.readout () ⟨d, G, inferInstance, inferInstance, σ, n⟩ p =
      Matrix.diagonal fun w => (mixtureWeight σ p n w : ℂ)

private theorem twirlRejectedLaw : ¬ twirlArena.{u}.Law twirlRejected := by
  intro h
  let G := ULift.{u} (Equiv.Perm (Fin 1))
  let σ : G →* Equiv.Perm (Fin 1) := 1
  have he := congrArg (fun M => M (fun _ => 0) (fun _ => 0))
    (h σ (fun _ => 1) 1)
  norm_num [twirlRejected, realize, mixtureWeight, G] at he

private theorem twirlDependence : ObservationalDependence twirlSignature.{u} twirlActual := by
  intro i
  let G := ULift.{u} (Equiv.Perm (Fin 1))
  let σ : G →* Equiv.Perm (Fin 1) := 1
  let k : twirlSignature.{u}.Params := ⟨1, G, inferInstance, inferInstance, σ, 1⟩
  refine ⟨k, (fun _ => 0), (fun _ => 1), ?_⟩
  change Defs.twirlPower _ _ _ ≠ Defs.twirlPower _ _ _
  rw [twirlPower_diag, twirlPower_diag]
  intro he
  have he' := congrArg (fun M => M (fun _ => 0) (fun _ => 0)) he
  norm_num [mixtureWeight, G] at he'

def twirlEvidence : Registration twirlArena.{u} (type_of% @twirlPower_diag.{u}) where
  actual := twirlActual
  bridge := Iff.rfl
  variation := ⟨@twirlPower_diag, twirlRejected, twirlRejectedLaw⟩
  sensitivity := ⟨fun i => ⟨twirlRejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, twirlRejectedLaw⟩,
    fun e => nomatch e⟩
  dependence := twirlDependence

def twirlRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@twirlPower_diag.{u}) (Realization twirlSignature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Information.GroupInvariantPsi.Mixture.twirlPower_diag.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Information.GroupInvariantPsi.Mixture.twirlEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨twirlArena⟩
  objectArena := .source ⟨twirlArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source twirlArena ⟨twirlEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize twirlSignature twirlActual.readout twirlActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.GroupInvariantPsi.Mixture
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Information.GroupInvariantPsi.Mixture
