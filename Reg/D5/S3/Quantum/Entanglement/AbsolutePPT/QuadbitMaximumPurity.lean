import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity

open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature
    (fun _ _ (rho : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) =>
      (rho * rho).trace.re)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- The whole original closed claim is retained. Only the purity observation in
the universal upper bound is varied; the supremum and explicit attainment
clauses remain part of the law. -/
abbrev arena : Arena where
  signature := signature
  Law O :=
    (∀ rho : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) → APPT rho →
        O.readout () () rho ≤ (2 / 27 : ℝ)) ∧
    (sSup {p : ℝ | ∃ rho : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = p} = (2 / 27 : ℝ)) ∧
    ∃ rho : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ,
      rho = diagonal (fun ij : Fin 4 × Fin 4 =>
        if ij = (0, 0) then (1 / 6 : ℂ) else (1 / 18 : ℂ)) ∧
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = (2 / 27 : ℝ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨rho, _hdiag, hdensity, happt, _hpurity⟩ := result.2.2
  have hle := h.1 rho hdensity happt
  change (1 : ℝ) ≤ (2 / 27 : ℝ) at hle
  norm_num at hle

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ), 1, ?_⟩
  norm_num [actual, realize, Matrix.trace_one, Fintype.card_prod]

def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.result)
      (type_of% (realize.{0,0,0,0,0} signature
        (fun _ _ (rho : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) =>
          (rho * rho).trace.re)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.result.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ _ (rho : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) =>
      (rho * rho).trace.re)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity,
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity,
      name := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.claim,
      path := #[] },
    coordinates := #[],
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.Audit_norm
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
noncomputable section
abbrev signature : Signature where
  Params := Σ I : Type, Fintype I
  State p := p.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ p v => letI := p.2; ∑ i, ‖v i‖^2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {I : Type} [Fintype I] (v : I → ℂ),
    star v ⬝ᵥ v = 1 → O.readout () ⟨I,inferInstance⟩ v = 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun _ : Unit => (1 : ℂ)) (by simp [dotProduct])
  change (0 : ℝ) = 1 at hh
  norm_num at hh
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Unit,inferInstance⟩, 0, (fun _ => 1), ?_⟩
  change (∑ i : Unit, ‖(0 : ℂ)‖^2) ≠ ∑ i : Unit, ‖(1 : ℂ)‖^2
  norm_num
def registration : Registration arena (type_of% @norm_of_dot_eq_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨norm_of_dot_eq_one, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.norm_of_dot_eq_one) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.norm_of_dot_eq_one.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.Audit_norm.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p v => letI := p.2; ∑ i, ‖v i‖^2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity, definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.Audit_norm

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.Audit_separable
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Resource.CompositeCones
open _root_.D5.S3.Resource.EntanglementWitness
open _root_.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open Matrix
open scoped ComplexOrder
noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _m : ℕ, ℕ)
    (fun p => Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ)
    (fun p => Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ)
def actual : Realization signature :=
  realize signature (fun _ _ W => partialTranspose W) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -(1 : Matrix _ _ ℂ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {m n : ℕ} {W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ},
    separableCone W → (O.readout () ⟨m,n⟩ W).PosSemidef
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (m := 1) (n := 1) separableCone_zero
  have hd := hh.diag_nonneg (i := (0,0))
  change (0 : ℂ) ≤ -1 at hd
  norm_num at hd
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,1⟩, 0, 1, ?_⟩
  intro he
  have hd := congrArg (fun T : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ => T (0,0) (0,0)) he
  change (0 : ℂ) = 1 at hd
  exact zero_ne_one hd
def registration : Registration arena (type_of% @separableCone_partialTranspose_posSemidef) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@separableCone_partialTranspose_posSemidef, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.Audit_separable.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ W => partialTranspose W) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity, definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.Audit_separable
