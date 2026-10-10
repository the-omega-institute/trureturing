import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Resource.CompositeCones
open _root_.D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks
open scoped BigOperators ComplexOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks

namespace Phases

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ),
    (1 - Cᴴ * C).PosSemidef →
      ∃ (a : (Fin n ⊕ Fin n) → Fin n → ℂ) (c : (Fin n ⊕ Fin n) → ℂ),
        (∀ r, R.readout () () (c r) = 1) ∧
          (∑ r, vecMulVec (a r) (star (a r))) = 1 ∧
          (∑ r, c r • vecMulVec (a r) (star (a r))) = C

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, c, hc, _⟩ := h (n := 1) 0 (by
    simpa using (PosSemidef.one : (1 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef))
  have he := hc (Sum.inl 0)
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% @contraction_decomposition) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨contraction_decomposition, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@contraction_decomposition) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks.Phases.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks.Phases.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "fn", "arg", "body", "fn",
        "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Phases

namespace ScalarShift

abbrev signature : Signature where
  Params := Σ _m : ℕ, ℕ
  State p := Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1 × Fin p.2) (Fin p.1 × Fin p.2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ H => H) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ p _ => -((p.1 : ℂ) + 1) • 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m n : ℕ} (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
    H.IsHermitian →
      (∀ x : Fin m × Fin n → ℂ,
        ‖WithLp.toLp 2 (H *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖) →
          separableCone ((m : ℂ) • 1 + R.readout () ⟨m, n⟩ H)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs := h (m := 1) (n := 1) 0 (by simp) (by intro x; simp)
  have hd := (separable_isPosSemidef hs).diag_nonneg (i := (0, 0))
  change (0 : ℂ) ≤
    (((1 : ℕ) : ℂ) • (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) +
      (-(((1 : ℕ) : ℂ) + 1)) • 1) (0, 0) (0, 0) at hd
  norm_num [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Complex.le_def] at hd

def family : Registration arena (type_of% @separableCone_scalar_add_of_opNorm_le_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨separableCone_scalar_add_of_opNorm_le_one, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
    intro h
    have he := congrFun (congrFun h (0, 0)) (0, 0)
    change (0 : ℂ) = 1 at he
    exact zero_ne_one he

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@separableCone_scalar_add_of_opNorm_le_one) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks.ScalarShift.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks.ScalarShift.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end ScalarShift


namespace SeparableSum

universe u

abbrev signature : Signature where
  Params := Σ _m : ℕ, Σ _n : ℕ, Type u
  State p := p.2.2 → Matrix (Fin p.1 × Fin p.2.1) (Fin p.1 × Fin p.2.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.2 → Matrix (Fin p.1 × Fin p.2.1) (Fin p.1 × Fin p.2.1) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ _ f => f) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {m n : ℕ} {ι : Type u} [Fintype ι]
    (f : ι → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
    (∀ i, separableCone (f i)) → separableCone (∑ i, R.readout () ⟨m, n, ι⟩ f i)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hs := h (m := 1) (n := 1) (ι := ULift.{u} (Fin 1)) (fun _ => 0)
    (fun _ => _root_.D5.S3.Resource.EntanglementWitness.separableCone_zero)
  have hn : separableCone (-1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) := by
    simpa [rejected, realize] using hs
  have hd := (separable_isPosSemidef hn).diag_nonneg (i := (0, 0))
  norm_num [Matrix.neg_apply, Matrix.one_apply, Complex.le_def] at hd

def family : Registration arena.{u} (type_of% @separableCone_sum.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by simpa [arena, actual, realize] using @separableCone_sum.{u},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, 1, ULift.{u} (Fin 1)⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have he := congrFun (congrFun (congrFun h ⟨0⟩) (0, 0)) (0, 0)
    norm_num [actual, realize, Matrix.one_apply] at he

def registration : Contract.Registration.{u + 1, 0, 1, 0, 0, 0, u + 1, u, 0, u, 0, 0}
    (@separableCone_sum.{u}) (Realization signature.{u}) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks.SeparableSum.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks.SeparableSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end SeparableSum

end Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks
