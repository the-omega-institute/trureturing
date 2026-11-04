import Reg.D5.S3.VertexAlgebra.SignedFields.SignedFieldNormalProductLocality
import D5.S3.VertexAlgebra.SignedFields.SignedFieldResidueLocality

/-! Faithful residue-law families; source occurrence enrollment remains unresolved. -/
open scoped VertexOperator
open _root_.D5.S3.VertexAlgebra.FieldNormalProductLocality
open _root_.D5.S3.VertexAlgebra.SignedFieldNormalProductLocality
open _root_.D5.S3.VertexAlgebra.SignedFieldResidueLocality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.D5.S3.VertexAlgebra.SignedFieldNormalProductLocality
  (Context signature actual rejected)
open private dependence from Reg.D5.S3.VertexAlgebra.SignedFields.SignedFieldNormalProductLocality
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.SignedFieldResidueLocality
universe u

namespace Locality
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Context.{u}) (x y z : ℂ) (A B C : VertexOperator ℂ K.V),
    (∃ N : ℕ, delta^[N] (signedComm y A C) = 0) →
    (∃ N : ℕ, delta^[N] (signedComm z B C) = 0) →
    (∃ N : ℕ, delta^[N] (signedComm x A B) = 0) → ∀ r : ℤ,
      ∃ N : ℕ, R.readout () K (delta^[N]
        (signedComm (y * z) (residueField x r A B).operator C))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let K : Context.{u} := ⟨ULift.{u} ℂ, inferInstance, inferInstance⟩
  obtain ⟨N, hN⟩ := h K 0 0 0 0 0 0
    ⟨0, by ext; simp [signedComm]⟩ ⟨0, by ext; simp [signedComm]⟩
    ⟨0, by ext; simp [signedComm]⟩ 0
  exact hN

def family : Registration arena (type_of% @residue_locality.{u}) where
  actual := actual
  bridge := by
    constructor
    · intro h K
      exact h
    · intro h V hGroup hScalars
      exact h ⟨V, hGroup, hScalars⟩
  variation := ⟨(fun K => residue_locality), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@residue_locality.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.SignedFieldResidueLocality.Locality.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.SignedFieldResidueLocality.Locality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => d = 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Locality

namespace Translation
abbrev signature : Signature where
  Params := Context.{u}
  State C := Module.End ℂ C.V × Module.End ℂ C.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ p => p.1 = p.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Context.{u}) (s : ℂ) (r : ℤ) (A B : VertexOperator ℂ K.V)
    (T : Module.End ℂ K.V),
    (∀ m : ℤ, T * (A [[m]]) - (A [[m]]) * T = -(m : ℂ) • (A [[m - 1]])) →
    (∀ m : ℤ, T * (B [[m]]) - (B [[m]]) * T = -(m : ℂ) • (B [[m - 1]])) →
    ∀ n : ℤ, R.readout () K
      (T * ((residueField s r A B).operator [[n]]) -
        ((residueField s r A B).operator [[n]]) * T,
        -(n : ℂ) • ((residueField s r A B).operator [[n - 1]]))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let K : Context.{u} := ⟨ULift.{u} ℂ, inferInstance, inferInstance⟩
  exact h K 0 0 0 0 0 (by intro m; simp) (by intro m; simp) 0

def family : Registration arena (type_of% @residue_translation.{u}) where
  actual := actual
  bridge := by
    constructor
    · intro h K
      exact h
    · intro h V hGroup hScalars
      exact h ⟨V, hGroup, hScalars⟩
  variation := ⟨(fun K => residue_translation), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by
    intro role
    let K : Context.{u} := ⟨ULift.{u} ℂ, inferInstance, inferInstance⟩
    refine ⟨K, (0, 0), (0, 1), ?_⟩
    intro h
    exact zero_ne_one (Eq.mp h rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@residue_translation.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.SignedFieldResidueLocality.Translation.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.SignedFieldResidueLocality.Translation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p.1 = p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Translation

end Reg.D5.S3.VertexAlgebra.SignedFieldResidueLocality
