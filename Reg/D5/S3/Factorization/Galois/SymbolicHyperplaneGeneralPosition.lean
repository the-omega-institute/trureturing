import D5.S3.Factorization.Galois.SymbolicHyperplaneGeneralPosition
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.Factorization.Galois.SymbolicHyperplaneGeneralPosition
open D5.S3.Factorization.Galois.ActualWindowCommonKernel.HyperplaneRank
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
open scoped Classical

namespace Reg.D5.S3.Factorization.Galois.SymbolicHyperplaneGeneralPosition

universe u v w t

structure Coordinates where
  field : Type u
  fieldStructure : Field field
  index : Type v
  indexStructure : Fintype index

attribute [instance] Coordinates.fieldStructure Coordinates.indexStructure

namespace GeneralPosition

abbrev signature : Signature where
  Params := Coordinates.{u,v}
  State p := Submodule (SymbolicField p.field p.index) (p.index → SymbolicField p.field p.index)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Submodule (SymbolicField p.field p.index)
    (p.index → SymbolicField p.field p.index) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {F : Type u} {α : Type v} {ι : Type w} [Field F] [Fintype α] [CharZero F]
    (V : ι → Submodule F (α → F)) (s : Finset ι) (_hV : ∀ i ∈ s, V i ≠ ⊥),
    (∀ i ∈ s, ¬ extend (V i) ≤ LinearMap.ker symbolicNormal) ∧
    ∀ A ⊆ s, ∀ B ⊆ s, ∀ C ⊆ s,
      (cutSpan (fun i => extend (V i)) symbolicNormal A ⊔
          familySpan (fun i => extend (V i)) B) ⊓
        (cutSpan (fun i => extend (V i)) symbolicNormal A ⊔
          familySpan (fun i => extend (V i)) C) ≤ LinearMap.ker symbolicNormal →
      R.readout () ⟨F, inferInstance, α, inferInstance⟩
        ((cutSpan (fun i => extend (V i)) symbolicNormal A ⊔
            familySpan (fun i => extend (V i)) B) ⊓
          (cutSpan (fun i => extend (V i)) symbolicNormal A ⊔
            familySpan (fun i => extend (V i)) C))
        (cutSpan (fun i => extend (V i)) symbolicNormal A)

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  have hh := (h (F := ULift.{u} ℚ) (α := ULift.{v} Unit) (ι := ULift.{w} Unit)
    (fun _ => ⊥) ∅ (by simp)).2 ∅ (by simp) ∅ (by simp) ∅ (by simp)
      (by simp [cutSpan, familySpan])
  exact hh

def family : Registration arena.{u,v,w} (type_of% (@symbolic_general_position.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨symbolic_general_position, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    let p : Coordinates.{u,v} := ⟨ULift.{u} ℚ, inferInstance, ULift.{v} Unit, inferInstance⟩
    refine ⟨p, ⊥, ⊤, ?_⟩
    intro h
    have he : (⊤ : signature.State p) = ⊥ := Eq.mp (congrFun h ⊥) rfl
    have hz : (fun _ : p.index => (1 : SymbolicField p.field p.index)) = 0 :=
      (Submodule.mem_bot _).mp (he ▸ Submodule.mem_top)
    exact one_ne_zero (congrFun hz (ULift.up ()))

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@symbolic_general_position.{u,v,w}) (Realization signature.{u,v})
    (type_of% (@InGeneralPosition)) Unit where
  unitName := `Reg.D5.S3.Factorization.Galois.SymbolicHyperplaneGeneralPosition.GeneralPosition.unit
  realizationName :=
    `Reg.D5.S3.Factorization.Galois.SymbolicHyperplaneGeneralPosition.GeneralPosition.family
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
  escapeFrom := some (@InGeneralPosition)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end GeneralPosition

namespace PartitionRank

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {F : Type u} {ι : Type v} {β : Type w} {κ : β → Type t}
    [Field F] [Fintype β] [∀ i, Fintype (κ i)] [CharZero F]
    (b : ∀ i, ι → κ i → F) (k : β) (s : Finset ι) (_hk : ∀ σ ∈ s, b k σ ≠ 0),
    ∃ P : Finpartition s,
      R.readout () ()
        (Module.finrank (SymbolicField F (Σ i, κ i))
          (commonRowSpan (blockRows (liftRows b)) (coefficientNormal coordinate) k s))
        (∑ B ∈ P.parts,
          ((∑ i, Module.finrank (SymbolicField F (Σ i, κ i)) (blockSpan (liftRows b) B i)) - 1)) ∧
      ∀ Q : Finpartition s, Module.finrank (SymbolicField F (Σ i, κ i))
        (commonRowSpan (blockRows (liftRows b)) (coefficientNormal coordinate) k s) ≤
        ∑ B ∈ Q.parts,
          ((∑ i, Module.finrank (SymbolicField F (Σ i, κ i)) (blockSpan (liftRows b) B i)) - 1)

private theorem rejected_law : ¬ arena.{u,v,w,t}.Law rejected := by
  intro h
  obtain ⟨P, hp⟩ := h (F := ULift.{u} ℚ) (ι := ULift.{v} Unit)
    (β := ULift.{w} Unit) (κ := fun _ => ULift.{t} Unit)
    (fun _ _ _ => 0) (ULift.up ()) ∅ (by simp)
  exact hp.1

def family : Registration arena.{u,v,w,t}
    (type_of% (@symbolic_block_common_rows_partition_rank.{u,v,w,t})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨symbolic_block_common_rows_partition_rank, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    exact Nat.one_ne_zero (Eq.mp (congrFun h 0) rfl)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@symbolic_block_common_rows_partition_rank.{u,v,w,t}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Factorization.Galois.SymbolicHyperplaneGeneralPosition.PartitionRank.unit
  realizationName :=
    `Reg.D5.S3.Factorization.Galois.SymbolicHyperplaneGeneralPosition.PartitionRank.family
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end PartitionRank

end Reg.D5.S3.Factorization.Galois.SymbolicHyperplaneGeneralPosition
