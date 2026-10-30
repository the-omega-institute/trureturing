import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.SourceBPZ.OriginalWord

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator
namespace Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalWord
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeAllStateField LatticePositiveEnergy
open LatticeHalfFockFiniteCorrection (wordWeight)
open _root_.D5.S3.VertexAlgebra.SourceBPZ
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

private def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i; exact Fin.elim0 i
  even_diagonal := by intro i; exact Fin.elim0 i

namespace Charge
abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _ (fun _ _ p => p) (fun e => nomatch e)
def bad : Realization signature := realize _ (fun _ _ _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (α β : Charge D) (w : List (Index D))
    (n : ℤ) (v : Oscillator D), R.readout () ()
      (∃ p : Oscillator D,
        ((wordField D α w)[[n]]) (Finsupp.single β v) = Finsupp.single (α + β) p)

private theorem source_bridge : (type_of% (@word_choice_charge)) ↔ arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law bad := by
  intro h
  exact h zeroLattice 0 0 [] 0 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro h
  exact Eq.mp h True.intro

def family : Registration arena (type_of% (@word_choice_charge)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp word_choice_charge, bad, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@word_choice_charge)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.OriginalWord.word_choice_charge "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalWord.Charge.family
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
  escapeFrom := some Prop
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Charge

namespace Word
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D)) (α : Charge D)
    (hcurrent : ∀ i : Fin D.rank, ∀ k u v,
      B (neutralMode D i k u) v = -B u (neutralMode D i (-k) v))
    (hprimary : ∀ t u v, B (((actualField D α)[[t]]) u) v =
      paritySign (chargeEnergy D α) *
        B u (((actualField D α)[[2 * chargeEnergy D α - t - 2]]) v))
    (w : List (Index D)) (m : ℤ) (u v : Carrier D),
    R.readout () () (B (((wordField D α w)[[m]]) u) v)
      (paritySign (chargeEnergy D α) * (-1 : ℂ)^(wordWeight D w) *
        transposeReadout D B α w m u v)

private theorem source_bridge :
    (type_of% (@actual_word_transpose)) ↔ arena.Law complexEqual := Iff.rfl

private theorem rejected_law : ¬ arena.Law complexFalse := by
  intro h
  exact h zeroLattice 0 0 (by intros; simp) (by intros; simp) [] 0 0 0

def family : Registration arena (type_of% (@actual_word_transpose)) where
  actual := complexEqual
  bridge := source_bridge
  variation := ⟨source_bridge.mp actual_word_transpose, complexFalse, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    complexEqual complexFalse rejected_law
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_word_transpose)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.OriginalWord.actual_word_transpose "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalWord.Word.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.SourceBPZ.OriginalWord
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Word

namespace Homogeneous
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (hcurrent : ∀ i : Fin D.rank, ∀ k u v,
      B (neutralMode D i k u) v = -B u (neutralMode D i (-k) v))
    (hprimary : ∀ (α : Charge D) t u v, B (((actualField D α)[[t]]) u) v =
      paritySign (chargeEnergy D α) *
        B u (((actualField D α)[[2 * chargeEnergy D α - t - 2]]) v))
    (a : Carrier D) (d : ℤ) (ha : a ∈ grade D d)
    (m : ℤ) (u v : Carrier D),
    R.readout () () (B (((Y D a)[[m]]) u) v)
      (paritySign d * ∑ l ∈ Finset.range (sourceBound D a), (l.factorial : ℂ)⁻¹ *
        B u (((Y D ((sugawaraMode D (gramComplex D)⁻¹ 1 ^ l) a))[[2*d-l-m-2]]) v))

private theorem source_bridge :
    (type_of% (@actual_homogeneous_source_transpose)) ↔ arena.Law complexEqual := Iff.rfl

private theorem rejected_law : ¬ arena.Law complexFalse := by
  intro h
  exact h zeroLattice (by simp [zeroLattice]) 0 (by intros; simp) (by intros; simp)
    0 0 (Submodule.zero_mem _) 0 0 0

def family : Registration arena (type_of% (@actual_homogeneous_source_transpose)) where
  actual := complexEqual
  bridge := source_bridge
  variation := ⟨source_bridge.mp actual_homogeneous_source_transpose, complexFalse, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    complexEqual complexFalse rejected_law
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_homogeneous_source_transpose)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.OriginalWord.actual_homogeneous_source_transpose "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalWord.Homogeneous.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.SourceBPZ.OriginalWord
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Homogeneous

namespace Source
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (hcurrent : ∀ i : Fin D.rank, ∀ k u v,
      B (neutralMode D i k u) v = -B u (neutralMode D i (-k) v))
    (hprimary : ∀ (α : Charge D) t u v, B (((actualField D α)[[t]]) u) v =
      paritySign (chargeEnergy D α) *
        B u (((actualField D α)[[2 * chargeEnergy D α - t - 2]]) v))
    (a : Carrier D) (m : ℤ) (u v : Carrier D),
    R.readout () () (B (((Y D a)[[m]]) u) v)
      (∑ d ∈ stateEnergies D a, paritySign d *
        ∑ l ∈ Finset.range (sourceBound D a), (l.factorial : ℂ)⁻¹ *
          B u (((Y D ((sugawaraMode D (gramComplex D)⁻¹ 1 ^ l)
            (gradeProjection D d a)))[[2*d-l-m-2]]) v))

private theorem source_bridge :
    (type_of% (@actual_source_transpose)) ↔ arena.Law complexEqual := Iff.rfl

private theorem rejected_law : ¬ arena.Law complexFalse := by
  intro h
  exact h zeroLattice (by simp [zeroLattice]) 0 (by intros; simp) (by intros; simp)
    0 0 0 0

def family : Registration arena (type_of% (@actual_source_transpose)) where
  actual := complexEqual
  bridge := source_bridge
  variation := ⟨source_bridge.mp actual_source_transpose, complexFalse, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    complexEqual complexFalse rejected_law
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_source_transpose)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.OriginalWord.actual_source_transpose "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalWord.Source.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.SourceBPZ.OriginalWord
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Source

end Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalWord
