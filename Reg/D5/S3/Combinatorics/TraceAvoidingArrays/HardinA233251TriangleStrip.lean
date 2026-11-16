import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Readout registrations for the generating-function identity and its finite certificate. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

attribute [local irreducible] a classCount firstCount

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (1 - 8 * X) * (1 - 48 * X) *
      (PowerSeries.mk fun n => (R.readout () () n : ℤ)) = X * (3 - 64 * X)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change (1 - 8 * X) * (1 - 48 * X) *
      (PowerSeries.mk fun n => ((a n + 1 : ℕ) : ℤ)) = X * (3 - 64 * X) at h
  have h0 : a 0 = 0 := by unfold a; decide +kernel
  have hb := congrArg (PowerSeries.coeff 0) h
  simpa [PowerSeries.coeff_mul, h0] using hb

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    unfold a
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

namespace FiniteCertificate

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Bool) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ n => firstCount n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => firstCount n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ s p, Valid s p →
      classCount s p true = (if s.2 then 48 else 20) ∧
      classCount s p false = (if s.2 then 0 else 8)) ∧
    R.readout () () true = 1 ∧ R.readout () () false = 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2.1
  have ha := finite_certificate.2.1
  change firstCount true + 1 = 1 at hb
  linarith

def family : Registration arena (type_of% @finite_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), true, false, ?_⟩
    change firstCount true ≠ firstCount false
    rw [finite_certificate.2.1, finite_certificate.2.2]
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName :=
    `Reg.A233251FiniteCertificate.auditUnit
  realizationName :=
    ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => firstCount n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end FiniteCertificate
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.ColourBond

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
open _root_.D5.S3.Observer.Separation.BooleanRankThreeK4
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 6) (fun _ => Fin 3)

def actual : Realization signature := realize signature (fun _ _ x => beta x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ x y : Fin 6, (x ≠ y ∧ x.val + y.val ≠ 5) ↔
    R.readout () () x ≠ R.readout () () y

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 1
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% @colour_bond_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨colour_bond_iff, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro ⟨⟩
    exact ⟨(), 0, 1, by decide +kernel⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@colour_bond_iff) (Realization signature) Type Unit where
  unitName := `Reg.A233251ColourBond.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.ColourBond.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => beta x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.ColourBond

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.TransferBridge

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip (Seen good)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

structure Model where
  k : ℕ
  positive : NeZero k
  B : Type
  R : (Fin k → Fin 6) → Prop
  decR : DecidablePred R
  P : (Fin k → Fin 6) → B
  C : B → (Fin k → Fin 6) → Prop
  decC : DecidableRel C
  E : (Fin k → Fin 6) → (Fin k → Fin 6) → Prop
  decE : DecidableRel E
  edge : ∀ c d, E c d ↔ C (P c) d

private instance {k n : ℕ} (s : Seen) (f : Fin n → Fin k → Fin 6) :
    Decidable (widthNormal s f) :=
  inferInstanceAs (Decidable (∀ _ _, (_ → _) ∧ (_ → _)))

def literal (m : Model) (n : ℕ) : ℤ := by
  letI := m.positive
  letI := m.decR
  letI := m.decE
  exact ((Finset.univ.filter (fun A : Fin (n + 1) × Fin m.k → Fin 6 =>
    (∃ i : Fin (n + 1), i.val = 0 ∧ A (i, 0) = 0) ∧
    (∀ i, m.R (fun j => A (i, j))) ∧
    (∀ (i : Fin (n + 1)) (h : i.val + 1 < n + 1), m.E (fun j => A (i, j))
      (fun j => A (⟨i.val + 1, h⟩, j))) ∧
    widthNormal (false, false) (fun i j => A (i, j)))).card : ℤ)

abbrev signature : Signature where
  Params := Model
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ m n => literal m n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ m n => literal m n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ {k : ℕ} [positive : NeZero k] {B : Type}
    (R : (Fin k → Fin 6) → Prop) (P : (Fin k → Fin 6) → B)
    (C : B → (Fin k → Fin 6) → Prop) [dr : DecidablePred R] [dc : DecidableRel C]
    (E : (Fin k → Fin 6) → (Fin k → Fin 6) → Prop) [de : DecidableRel E]
    (edge : ∀ c d, E c d ↔ C (P c) d) (n : ℕ),
    F.readout () ⟨k, positive, B, R, dr, P, C, dc, E, de, edge⟩ n =
      widthTotal R P (widthV R P C n)

private def sample : Model where
  k := 1
  positive := inferInstance
  B := Unit
  R _ := True
  decR _ := isTrue trivial
  P _ := ()
  C _ _ := True
  decC _ _ := isTrue trivial
  E _ _ := True
  decE _ _ := isTrue trivial
  edge _ _ := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := @h sample.k sample.positive sample.B sample.R sample.P sample.C
    sample.decR sample.decC sample.E sample.decE sample.edge 0
  have ha := @width_counting_bridge sample.k sample.positive sample.B
    sample.R sample.P sample.C sample.decR sample.decC sample.E sample.decE sample.edge 0
  change literal sample 0 + 1 = _ at hb
  change literal sample 0 = _ at ha
  linarith

def family : Registration arena (type_of% @width_counting_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨width_counting_bridge, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro ⟨⟩
    exact ⟨sample, 0, 1, by decide +kernel⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 1, 0, 0, 0, 0, 0}
    (@width_counting_bridge) (Realization signature) Type Unit where
  unitName := `Reg.A233251TransferBridge.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.TransferBridge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m n => literal m n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.TransferBridge
