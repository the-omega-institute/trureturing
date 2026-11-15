import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular

open _root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation
open _root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting
open _root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix Module LinearMap Submodule
open scoped TensorProduct

abbrev natSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)
def natActual : Realization natSignature :=
  realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e)
def natRejected : Realization natSignature :=
  realize natSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem natDependence : ObservationalDependence natSignature natActual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  omega

private abbrev zeroPencil : Pencil ℂ where
  domain := ℂ
  codomain := ℂ
  first := 0
  second := 0

private theorem zero_chain_exists : ∃ r : ℕ, Nonempty (SplitData zeroPencil r) := by
  letI : Unique (Fin 1) := { default := 0, uniq := fun i => Fin.eq_zero i }
  have hb : boundary zeroPencil.first zeroPencil.second 1 (fun _ : Fin 1 => (1 : ℂ)) = 0 := by
    funext i
    change Fin.snoc (α := fun _ : Fin 2 => ℂ) (fun _ : Fin 1 => (0 : ℂ)) 0 i -
      Fin.cons (α := fun _ : Fin 2 => ℂ) (0 : ℂ) (fun _ : Fin 1 => 0) i = 0
    fin_cases i <;> simp
    change Fin.snoc (α := fun _ : Fin 2 => ℂ) (fun _ : Fin 1 => (0 : ℂ)) 0
      (Fin.last 1) = 0
    rw [Fin.snoc_last]
  refine ⟨0, ⟨{
    chain := fun _ => (1 : ℂ)
    boundary_zero := hb
    last_ne_zero := by change (1 : ℂ) ≠ 0; exact one_ne_zero
    domainProjection := LinearMap.id
    codomainProjection := 0
    domain_isProj := ?_
    codomain_isProj := ?_
    first_commute := by apply LinearMap.ext; intro x; rfl
    second_commute := by apply LinearMap.ext; intro x; rfl
    domain_independent := linearIndependent_unique_iff.mpr (by
      change (1 : ℂ) ≠ 0
      exact one_ne_zero)
    codomain_independent := linearIndependent_empty_type }⟩⟩
  · constructor
    · intro x
      change x ∈ span ℂ (Set.range (fun _ : Fin 1 => (1 : ℂ)))
      have hm : (1 : ℂ) ∈ span ℂ (Set.range (fun _ : Fin 1 => (1 : ℂ))) :=
        subset_span ⟨0, rfl⟩
      simpa using (span ℂ (Set.range (fun _ : Fin 1 => (1 : ℂ)))).smul_mem x hm
    · intro x _
      rfl
  · constructor
    · intro x
      exact zero_mem _
    · intro x hx
      have hx0 : x = 0 := by simpa using hx
      exact hx0.symm

namespace TensorSplit

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {p : Pencil ℂ} {r : ℕ} (s : SplitData p r) (q : Pencil ℂ),
    R.readout () ()
      (finrank ℂ (LinearMap.range
        (TensorProduct.map p.first q.first + TensorProduct.map p.second q.second)))
      (finrank ℂ (LinearMap.range
        (TensorProduct.map s.block.first q.first + TensorProduct.map s.block.second q.second)) +
       finrank ℂ (LinearMap.range
        (TensorProduct.map s.remainder.first q.first + TensorProduct.map s.remainder.second q.second)))

private theorem rejected_law : ¬ arena.Law natRejected := by
  intro h
  obtain ⟨r, ⟨s⟩⟩ := zero_chain_exists
  exact @h zeroPencil r s zeroPencil

def source_registration : Registration arena (type_of% @SplitData.tensor_split) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@SplitData.tensor_split, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@SplitData.tensor_split) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.SplitData.tensor_split.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular.TensorSplit.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end TensorSplit

namespace HorizontalSplit

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {p : Pencil ℂ} {r : ℕ} (s : SplitData p r),
    R.readout () ()
      (finrank ℂ ↥(LinearMap.range p.first ⊔ LinearMap.range p.second))
      (finrank ℂ ↥(LinearMap.range s.firstBlock ⊔ LinearMap.range s.secondBlock) +
       finrank ℂ ↥(LinearMap.range s.remainder.first ⊔ LinearMap.range s.remainder.second))

private theorem rejected_law : ¬ arena.Law natRejected := by
  intro h
  obtain ⟨r, ⟨s⟩⟩ := zero_chain_exists
  exact @h zeroPencil r s

def source_registration : Registration arena (type_of% @SplitData.horizontal_split) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@SplitData.horizontal_split, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@SplitData.horizontal_split) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.SplitData.horizontal_split.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular.HorizontalSplit.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end HorizontalSplit

namespace VerticalSplit

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {p : Pencil ℂ} {r : ℕ} (s : SplitData p r),
    R.readout () ()
      (finrank ℂ (LinearMap.range (p.first.prod p.second)))
      (finrank ℂ (LinearMap.range (s.firstBlock.prod s.secondBlock)) +
       finrank ℂ (LinearMap.range (s.remainder.first.prod s.remainder.second)))

private theorem rejected_law : ¬ arena.Law natRejected := by
  intro h
  obtain ⟨r, ⟨s⟩⟩ := zero_chain_exists
  exact @h zeroPencil r s

def source_registration : Registration arena (type_of% @SplitData.vertical_split) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@SplitData.vertical_split, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@SplitData.vertical_split) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.SplitData.vertical_split.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular.VerticalSplit.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end VerticalSplit

namespace HorizontalRank

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {p : Pencil ℂ} {r : ℕ} (s : SplitData p r),
    R.readout () () (finrank ℂ ↥(LinearMap.range s.firstBlock ⊔
      LinearMap.range s.secondBlock)) r

private theorem rejected_law : ¬ arena.Law natRejected := by
  intro h
  obtain ⟨r, ⟨s⟩⟩ := zero_chain_exists
  exact @h zeroPencil r s

def source_registration : Registration arena (type_of% @SplitData.horizontal_rank) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@SplitData.horizontal_rank, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@SplitData.horizontal_rank) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.SplitData.horizontal_rank.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular.HorizontalRank.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end HorizontalRank

namespace VerticalRank

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {p : Pencil ℂ} {r : ℕ} (s : SplitData p r),
    R.readout () () (finrank ℂ (LinearMap.range (s.firstBlock.prod s.secondBlock)))
      (if r = 0 then 0 else r + 1)

private theorem rejected_law : ¬ arena.Law natRejected := by
  intro h
  obtain ⟨r, ⟨s⟩⟩ := zero_chain_exists
  exact @h zeroPencil r s

def source_registration : Registration arena (type_of% @SplitData.vertical_rank) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@SplitData.vertical_rank, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@SplitData.vertical_rank) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.SplitData.vertical_rank.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular.VerticalRank.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end VerticalRank

namespace TensorRank

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {p q : Pencil ℂ} {r t : ℕ} (s : SplitData p r) (z : SplitData q t),
    R.readout () () (finrank ℂ (LinearMap.range
      (TensorProduct.map s.firstBlock z.firstBlock +
       TensorProduct.map s.secondBlock z.secondBlock))) (r * t)

private theorem rejected_law : ¬ arena.Law natRejected := by
  intro h
  obtain ⟨r, ⟨s⟩⟩ := zero_chain_exists
  exact @h zeroPencil zeroPencil r r s s

def source_registration : Registration arena (type_of% @SplitData.tensor_rank) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@SplitData.tensor_rank, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@SplitData.tensor_rank) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.SplitData.tensor_rank.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular.TensorRank.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end TensorRank

namespace PartialTransposeRank

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {p q : Pencil ℂ} {r t : ℕ} (s : SplitData p r) (z : SplitData q t),
    R.readout () () (finrank ℂ (LinearMap.range
      (TensorProduct.map s.firstBlock.dualMap z.firstBlock +
       TensorProduct.map s.secondBlock.dualMap z.secondBlock))) (r * t + min r t)

private theorem rejected_law : ¬ arena.Law natRejected := by
  intro h
  obtain ⟨r, ⟨s⟩⟩ := zero_chain_exists
  exact @h zeroPencil zeroPencil r r s s

def source_registration : Registration arena (type_of% @SplitData.partialTranspose_rank) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@SplitData.partialTranspose_rank, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@SplitData.partialTranspose_rank) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.SplitData.partialTranspose_rank.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular.PartialTransposeRank.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end PartialTransposeRank

namespace MixedTensorRank

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {p q : Pencil ℂ} {r t : ℕ} (s : SplitData p r) (z : SplitData q t),
    R.readout () () (finrank ℂ (LinearMap.range
      (TensorProduct.map s.firstBlock z.firstBlock.dualMap +
       TensorProduct.map s.secondBlock z.secondBlock.dualMap))) (r * t + min r t)

private theorem rejected_law : ¬ arena.Law natRejected := by
  intro h
  obtain ⟨r, ⟨s⟩⟩ := zero_chain_exists
  exact @h zeroPencil zeroPencil r r s s

def source_registration : Registration arena (type_of% @SplitData.mixed_tensor_rank) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@SplitData.mixed_tensor_rank, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@SplitData.mixed_tensor_rank) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair.SplitData.mixed_tensor_rank.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular.MixedTensorRank.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end MixedTensorRank

end Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular
