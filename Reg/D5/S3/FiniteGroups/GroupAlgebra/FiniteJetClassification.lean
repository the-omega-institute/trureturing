import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.FiniteJetAudit

/-! Source-faithful dependent-family audit evidence for finite original jets. -/

set_option autoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.GroupAlgebra
open FiniteJetCoefficients FiniteJetClassification FiniteJetOrbits OddPrimeJetDeformation
open Reg.Support.FiniteJetAudit
open scoped BigOperators
noncomputable section
universe u
namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification
namespace reference_subtraction
structure Scope extends OddData.{u} where
  B : Fin (n-1) → K
  c : K
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Scope.{u}
  (fun s => s.K) (fun s => s.K)
def actual : Realization signature.{u} := realize signature
  (fun _ s x => Q (p := s.p) s.n (fun i => s.c ^ (s.p ^ (i.val+1)) * s.B i) x)
  (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature
  (fun i s x => actual.readout i s x + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type u} [fk : Field K] [ft : Fintype K] [ak : Algebra (ZMod p) K]
    (n : ℕ) (B : Fin (n-1) → K) (c x : K),
    Q (p := p) n B (c*x) - x*Q (p := p) n B c =
      f.readout () ⟨⟨⟨p,K,n⟩⟩,B,c⟩ x
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := h (p := 3) (K := ULift.{u} (ZMod 3)) 1 0 0 0
  simpa [rejected, actual, realize, Q, coefficientMap_apply] using hb
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  obtain ⟨x, hx⟩ := coefficient_values_ne.{u}
  refine ⟨⟨nineOdd,(fun _ => (1 : Nine.{u})),(1 : Nine.{u})⟩, x, (0 : Nine.{u}), ?_⟩
  simp only [_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients.coefficientMap_apply] at hx
  simpa [actual, realize, nineOdd, nine, Q,
    _root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetCoefficients.coefficientMap_apply] using hx

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification.reference_subtraction.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification.reference_subtraction.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification.reference_subtraction.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification.reference_subtraction.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification.reference_subtraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification
    definition := none
    coordinates := #[0, 3, 7, 8, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end reference_subtraction
namespace fixed_automorphism_coefficients_iff
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature
  (Σ K : Type u, Field K) (fun s => s.1) (fun s => s.1)
def actual : Realization signature.{u} := realize signature (fun _ _ a => a) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature
  (fun _ s _ => letI := s.2; (0 : s.1)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type u} [fk : Field K] [ft : Fintype K] [ak : Algebra (ZMod p) K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Fintype.card K = p ^ n)
    (A B : Fin (n-1) → K) (φ : Multiplicative K ≃* Multiplicative K),
    Intertwines (Q (p := p) n A) (Q (p := p) n B) φ ↔
      ∃ (c : Kˣ) (σ : K ≃ₐ[ZMod p] K),
        (∀ a : K, Multiplicative.toAdd (φ (Multiplicative.ofAdd (f.readout () ⟨K,fk⟩ a))) =
          (c : K)*σ a) ∧
        ∀ i, B i = ((c⁻¹ : Kˣ) : K) ^ weight p n i * σ (A i)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := h (p := 3) (K := ULift.{u} (ZMod 3)) (n := 1) (by decide)
    (by simp) 0 0 (MulEquiv.refl _)
  have hi : Intertwines (Q (p := 3) 1 (0 : Fin (1-1) → ULift.{u} (ZMod 3)))
      (Q 1 0) (MulEquiv.refl _) :=
    ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩
  obtain ⟨c,σ,hc,_⟩ := hb.mp hi
  have hz := hc 1
  have he : (0 : ULift.{u} (ZMod 3)) = (c : ULift.{u} (ZMod 3)) := by
    simpa [rejected, realize] using hz
  exact c.ne_zero he.symm
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  exact ⟨⟨ULift.{u} (ZMod 3),inferInstance⟩,0,1,zero_ne_one⟩

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification.fixed_automorphism_coefficients_iff.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification.fixed_automorphism_coefficients_iff.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification.fixed_automorphism_coefficients_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification.fixed_automorphism_coefficients_iff.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification.fixed_automorphism_coefficients_iff.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "arg", "body", "fn", "arg", "body", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 15
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end fixed_automorphism_coefficients_iff
namespace original_equivalence_iff
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature OddData.{u}
  (fun s => Fin (s.n-1) → s.K) (fun s => Fin (s.n-1) → s.K)
def actual : Realization signature.{u} := realize signature (fun _ _ A => A) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law f := ∀ {p : ℕ} [pp : Fact p.Prime] [po : Fact (2 < p)]
    {K : Type u} [fk : Field K] [ft : Fintype K] [ak : Algebra (ZMod p) K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Fintype.card K = p ^ n) (A B : Fin (n-1) → K),
    (∃ φ : Multiplicative K ≃* Multiplicative K,
      Intertwines (Q (p := p) n A) (Q (p := p) n B) φ) ↔
      ∃ (c : Kˣ) (σ : K ≃ₐ[ZMod p] K),
        ∀ i, f.readout () ⟨⟨p,K,n⟩⟩ B i =
          ((c⁻¹ : Kˣ) : K) ^ weight p n i * σ (A i)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := h (p := 3) (K := Nine.{u}) (n := 2) (by decide) nine_card 0 1
  have hi := hb.mpr ⟨1, AlgEquiv.refl, by
    intro i
    change (0 : Nine.{u}) = _
    simp⟩
  obtain ⟨c,σ,hc⟩ := (FiniteJetClassification.original_equivalence_iff
    (p := 3) (K := Nine.{u}) (n := 2) (by decide) nine_card 0 1).mp hi
  have hz := hc 0
  simpa using hz
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  exact ⟨nineOdd,0,1,tuples_ne⟩

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification.original_equivalence_iff.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification.original_equivalence_iff.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification.original_equivalence_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification.original_equivalence_iff.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification.original_equivalence_iff.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification
    definition := none
    coordinates := #[0, 3, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "arg", "body", "body", "fn", "arg", "fn"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_equivalence_iff
end Reg.D5.S3.FiniteGroups.GroupAlgebra.FiniteJetClassification
