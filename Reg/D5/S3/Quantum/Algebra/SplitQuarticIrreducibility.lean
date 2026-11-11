import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Algebra.OriginalOcticSplitDeterminant
set_option autoImplicit false
set_option maxRecDepth 8192
/-! Exact source bridges for dependent readout audits. -/
noncomputable section
open Classical MvPolynomial Finset Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.SplitQuarticIrreducibility
open _root_.D5.S3.Quantum.Algebra.OriginalOcticSplitDeterminant
open LeanInformationAudit
namespace Reg.D5.S3.Quantum.Algebra.SplitQuarticIrreducibility
universe u v w
private abbrev single (P : Type u) (X : P → Type v) (Y : P → Type w) : Signature where
  Params := P
  State := X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := Y
  Anchor := Empty
  finiteAnchor := inferInstance

namespace Coordinates
abbrev signature : Signature := single Unit (fun _ => Finset (Fin 8))
  (fun _ => Fin 8 →₀ ℕ)
def actual : Realization signature := realize signature (fun _ _ => squareExponent)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (I : Finset (Fin 8)) (i : Fin 8),
    r.readout () () I i = if i ∈ I then 1 else 0
theorem source_bridge : (type_of% (@square_exponent_apply)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h {0} 0
  norm_num [rejected, realize] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), ∅, {0}, ?_⟩
  intro h
  have h0 := DFunLike.congr_fun h 0
  change squareExponent ∅ 0 = squareExponent {0} 0 at h0
  rw [square_exponent_apply, square_exponent_apply] at h0
  norm_num at h0
private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e
def familyRegistration : Registration arena (type_of% (@square_exponent_apply)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨square_exponent_apply, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

/-- Source reconstruction remains unspecified. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@square_exponent_apply)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Quantum.Algebra.SplitQuarticIrreducibility.square_exponent_apply.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.SplitQuarticIrreducibility.Coordinates.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Coordinates

namespace Degree
abbrev signature := Coordinates.signature
def actual : Realization signature := Coordinates.actual
def rejected : Realization signature := Coordinates.rejected
abbrev arena : Arena where
  signature := signature
  Law r := ∀ I : Finset (Fin 8), (r.readout () () I).degree = I.card
theorem source_bridge : (type_of% (@square_exponent_degree)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h {0}
  norm_num [rejected, Coordinates.rejected, realize] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), ∅, {0}, ?_⟩
  intro h
  have h0 := DFunLike.congr_fun h 0
  change squareExponent ∅ 0 = squareExponent {0} 0 at h0
  rw [square_exponent_apply, square_exponent_apply] at h0
  norm_num at h0
private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e
def familyRegistration : Registration arena (type_of% (@square_exponent_degree)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨square_exponent_degree, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

/-- Source reconstruction remains unspecified. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@square_exponent_degree)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Quantum.Algebra.SplitQuarticIrreducibility.square_exponent_degree.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.SplitQuarticIrreducibility.Degree.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Degree

namespace Obstruction
structure Parameters where
  k : Type u
  field : Field k
attribute [instance] Parameters.field
abbrev signature : Signature := single Parameters (fun p => MvPolynomial (Fin 8) p.k)
  (fun p => MvPolynomial (Fin 8) p.k)
def actual : Realization signature := realize signature (fun _ _ f => f) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {k : Type u} [Field k] (f : MvPolynomial (Fin 8) k),
    f.IsHomogeneous 4 → (∀ i, f.degreeOf i ≤ 1) →
    (((univ : Finset (Fin 8)).powersetCard 4).filter
      (fun I => f.coeff (squareExponent I) = 0)).card < 20 →
    Irreducible (r.readout () ⟨k, inferInstance⟩ f)
theorem source_bridge : (type_of% (@irreducible_of_fewer_than_twenty_zeros.{u})) ↔
    arena.{u}.Law actual.{u} := Iff.rfl
end Obstruction
end Reg.D5.S3.Quantum.Algebra.SplitQuarticIrreducibility
