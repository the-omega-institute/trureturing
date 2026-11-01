import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Contextuality.PureStateHTMBBound
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the pure-state HTMB bound. -/

namespace Reg.D5.S3.Quantum.Contextuality.PureStateHTMBBound

open _root_.D5.S3.Quantum.Contextuality.PureStateHTMBBound
open _root_.D5.S3.Quantum.QuantumChannels.EntanglementBreakingOverlapPurity (projector)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the HTMB value as the second measurement varies. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ d : ℕ, Σ _ψ : ZMod 3 × ZMod 3 → EuclideanSpace ℂ (Fin d),
      ZMod 3 → Matrix (Fin d) (Fin d) ℂ)
    (fun p => ZMod 3 → Matrix (Fin p.1) (Fin p.1) ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p n => htmbValue p.2.1 p.2.2 n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Preserve the normalization, both POVMs, and both parity equivalences. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (ψ : ZMod 3 × ZMod 3 → EuclideanSpace ℂ (Fin d))
    (m n : ZMod 3 → Matrix (Fin d) (Fin d) ℂ),
    (∀ x, ‖ψ x‖ = 1) →
    ((∀ b, (m b).PosSemidef) ∧ ∑ b, m b = 1) →
    ((∀ b, (n b).PosSemidef) ∧ ∑ b, n b = 1) →
    (∀ a ∈ ({1, 2} : Finset (ZMod 3)), ∀ k : ZMod 3,
      ∑ x ∈ Finset.univ.filter (fun x : ZMod 3 × ZMod 3 => x.1 + a * x.2 = k),
        projector (ψ x) =
      ∑ x ∈ Finset.univ.filter (fun x : ZMod 3 × ZMod 3 => x.1 + a * x.2 = 0),
        projector (ψ x)) →
    R.readout () ⟨d, ψ, m⟩ n ≤ 2 / 3

private def unitVector : EuclideanSpace ℂ (Fin 1) := WithLp.toLp 2 (fun _ => 1)

private def pointMeasurement : ZMod 3 → Matrix (Fin 1) (Fin 1) ℂ :=
  fun b => if b = 0 then 1 else 0

private theorem pointMeasurement_povm :
    (∀ b, (pointMeasurement b).PosSemidef) ∧ ∑ b, pointMeasurement b = 1 := by
  constructor
  · intro b
    unfold pointMeasurement
    split_ifs
    · exact PosSemidef.one
    · exact PosSemidef.zero
  · simp [pointMeasurement]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hu : ‖unitVector‖ = 1 := by
    simp [unitVector, EuclideanSpace.norm_eq]
  have hp : ∀ a ∈ ({1, 2} : Finset (ZMod 3)), ∀ k : ZMod 3,
      ∑ x ∈ Finset.univ.filter (fun x : ZMod 3 × ZMod 3 => x.1 + a * x.2 = k),
        projector unitVector =
      ∑ x ∈ Finset.univ.filter (fun x : ZMod 3 × ZMod 3 => x.1 + a * x.2 = 0),
        projector unitVector := by
    have hc (a k : ZMod 3) :
        (Finset.univ.filter (fun x : ZMod 3 × ZMod 3 => x.1 + a * x.2 = k)).card = 3 := by
      fin_cases a <;> fin_cases k <;> decide
    intro a _ k
    simp only [Finset.sum_const, hc]
  have hb := h 1 (fun _ => unitVector) pointMeasurement pointMeasurement (fun _ => hu)
    pointMeasurement_povm pointMeasurement_povm hp
  change (1 : ℝ) ≤ 2 / 3 at hb
  norm_num at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, (fun _ => unitVector), 0⟩, 0, (fun _ => 1), ?_⟩
  change htmbValue (fun _ => unitVector) 0 0 ≠
    htmbValue (fun _ => unitVector) 0 (fun _ => 1)
  norm_num [htmbValue, projector, unitVector, Matrix.trace, Matrix.vecMulVec_apply,
    Fintype.sum_prod_type, Fin.sum_univ_three]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Contextuality.PureStateHTMBBound.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Contextuality.PureStateHTMBBound.unit
  realizationName := `Reg.D5.S3.Quantum.Contextuality.PureStateHTMBBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p n => htmbValue p.2.1 p.2.2 n)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Contextuality.PureStateHTMBBound
    definition := some {
      owner := `D5.S3.Quantum.Contextuality.PureStateHTMBBound
      name := `D5.S3.Quantum.Contextuality.PureStateHTMBBound.claim
      path := #[] }
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.Quantum.Contextuality.PureStateHTMBBound.result
#print _root_.D5.S3.Quantum.Contextuality.PureStateHTMBBound.claim
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Contextuality.PureStateHTMBBound
