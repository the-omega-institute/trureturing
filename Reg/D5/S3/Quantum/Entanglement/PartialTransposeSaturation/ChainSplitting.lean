import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting
import Reg.Support.SingleDependentReadout
import Mathlib.Algebra.Field.ULift

set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u v w z

namespace Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting
open _root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LinearMap Submodule

abbrev signature : Signature where
  Params := Type z
  State T := T
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ T := T → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature.{z} actual := by
  intro role
  refine ⟨ULift.{z} ℚ, 0, 1, ?_⟩
  intro he
  have h : (1 : ULift.{z} ℚ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero h

namespace Common
abbrev arena : Arena where
  signature := signature.{max v w}
  Law R := ∀ {K : Type u} {U : Type v} {V : Type w}
    [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (f g : U →ₗ[K] V) (u : U) (hu : u ≠ 0) (hf : f u = 0) (hg : g u = 0),
    ∃ P : U →ₗ[K] U, IsProj (K ∙ u) P ∧
      R.readout () (U →ₗ[K] V) (f.comp P) 0 ∧ g.comp P = 0 ∧ IsCompl (K ∙ u) (ker P)
private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  let K := ULift.{u} ℚ
  let U := ULift.{v} ℚ
  let φ : K →+* U := ULift.ringEquiv.symm.toRingHom.comp ULift.ringEquiv.toRingHom
  letI : Algebra K U := φ.toAlgebra
  intro h
  obtain ⟨P, hP, hbad, _⟩ := @h K U PUnit.{w+1} inferInstance inferInstance inferInstance
    inferInstance inferInstance 0 0 1 one_ne_zero (by simp) (by simp)
  exact hbad

def source_registration : Registration arena.{u,v,w} (type_of% @split_common_kernel_line.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@split_common_kernel_line, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@split_common_kernel_line.{u,v,w}) (Realization signature.{max v w}) (Type (max v w + 1)) Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.Common.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.Common.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{max v w} (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Common

namespace Injective
abbrev arena : Arena where
  signature := signature.{v}
  Law R := ∀ {K : Type u} {U : Type v} {V : Type w}
    [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (f g : U →ₗ[K] V)
    (h : ∀ (r : ℕ) (u : Fin (r + 1) → U), boundary f g (r + 1) u = 0 → u (Fin.last r) = 0)
    (n : ℕ) (x y : Fin n → U), boundary f g n x = boundary f g n y →
      R.readout () (Fin n → U) x y
private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let K := ULift.{u} ℚ
  have hz : ∀ (r : ℕ) (u : Fin (r + 1) → PUnit.{v+1}),
      boundary (0 : PUnit.{v+1} →ₗ[K] PUnit.{w+1}) 0 (r + 1) u = 0 →
        u (Fin.last r) = 0 := by
    intro r u hu
    exact Subsingleton.elim _ _
  exact @h K PUnit.{v+1} PUnit.{w+1} inferInstance inferInstance inferInstance
    inferInstance inferInstance 0 0 hz 0 0 0 rfl

def source_registration : Registration arena.{u,v,w} (type_of% @boundary_injective_of_no_chain.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@boundary_injective_of_no_chain, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@boundary_injective_of_no_chain.{u,v,w}) (Realization signature.{v}) (Type (v + 1)) Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.Injective.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.Injective.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v} (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Injective

namespace Positive
abbrev arena : Arena where
  signature := signature.{max v w}
  Law R := ∀ {K : Type u} {U : Type v} {V : Type w}
    [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (f g : U →ₗ[K] V) {n : ℕ} (a : Fin (n + 2) → U)
    (ha : boundary f g (n + 2) a = 0) (hlast : a (Fin.last (n + 1)) ≠ 0)
    (hminimal : ∀ z : Fin (n + 1) → U, boundary f g (n + 1) z = 0 → z (Fin.last n) = 0),
    ∃ (P : U →ₗ[K] U) (Q : V →ₗ[K] V),
      IsProj (span K (Set.range a)) P ∧
      IsProj (span K (Set.range (fun j : Fin (n + 1) => g (a j.castSucc)))) Q ∧
      R.readout () (U →ₗ[K] V) (Q.comp f) (f.comp P) ∧ Q.comp g = g.comp P ∧
      LinearIndependent K a ∧
      LinearIndependent K (fun j : Fin (n + 1) => g (a j.castSucc)) ∧
      IsCompl (span K (Set.range a)) (ker P) ∧
      IsCompl (span K (Set.range (fun j : Fin (n + 1) => g (a j.castSucc)))) (ker Q)
private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  classical
  let K := ULift.{u} ℚ
  let M := ULift.{v} ℚ
  let V := ULift.{w} ℚ
  let φM : K →+* M := ULift.ringEquiv.symm.toRingHom.comp ULift.ringEquiv.toRingHom
  let φV : K →+* V := ULift.ringEquiv.symm.toRingHom.comp ULift.ringEquiv.toRingHom
  letI : Algebra K M := φM.toAlgebra
  letI : Algebra K V := φV.toAlgebra
  let f : (Fin 2 → M) →ₗ[K] V := {
    toFun := fun x => ⟨(x 1).down⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }
  let g : (Fin 2 → M) →ₗ[K] V := {
    toFun := fun x => ⟨(x 0).down⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }
  let a : Fin 2 → (Fin 2 → M) := fun i j => if i = j then 1 else 0
  have ha : boundary f g 2 a = 0 := by
    ext i
    fin_cases i
    · change (0 : ℚ) - 0 = 0
      norm_num
    · change (1 : ℚ) - 1 = 0
      norm_num
    · change (0 : ℚ) - 0 = 0
      norm_num
  have hlast : a (Fin.last 1) ≠ 0 := by
    intro hz
    have he : (1 : M) = 0 := by simpa [a] using congrFun hz 1
    exact one_ne_zero he
  have hmin : ∀ z : Fin 1 → (Fin 2 → M), boundary f g 1 z = 0 → z (Fin.last 0) = 0 := by
    intro z hz
    have hF : f (z 0) = 0 := by
      simpa [boundary, Fin.snoc_apply_zero] using congrFun hz 0
    have hG : g (z 0) = 0 := by
      have h := congrFun hz (Fin.last 1)
      change 0 - g (z 0) = 0 at h
      simpa only [zero_sub, neg_eq_zero] using h
    change z 0 = 0
    ext i
    fin_cases i
    · exact congrArg (fun t : V => t.down) hG
    · exact congrArg (fun t : V => t.down) hF
  intro h
  obtain ⟨P, Q, hP, hQ, hbad, _⟩ := @h K (Fin 2 → M) V inferInstance inferInstance
    inferInstance inferInstance inferInstance f g 0 a ha hlast hmin
  exact hbad

def source_registration : Registration arena.{u,v,w} (type_of% @split_shortest_chain.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@split_shortest_chain, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@split_shortest_chain.{u,v,w}) (Realization signature.{max v w}) (Type (max v w + 1)) Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.Positive.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.Positive.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{max v w} (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Positive

namespace TensorSplit
universe x y
open scoped TensorProduct
abbrev arena : Arena where
  signature := signature.{0}
  Law R := ∀ {K : Type u} {U : Type v} {V : Type w}
    [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {U' : Type x} {V' : Type y} [AddCommGroup U'] [Module K U']
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    (f₁ f₂ : U →ₗ[K] V) (g₁ g₂ : U' →ₗ[K] V')
    (P : Module.End K U) (Q : Module.End K V)
    (hQ : Q.comp Q = Q) (hf₁ : Q.comp f₁ = f₁.comp P) (hf₂ : Q.comp f₂ = f₂.comp P),
    let T := TensorProduct.map f₁ g₁ + TensorProduct.map f₂ g₂
    let Q' := TensorProduct.map Q (LinearMap.id : Module.End K V')
    R.readout () ℕ (Module.finrank K (LinearMap.range T))
      (Module.finrank K (LinearMap.range (Q'.comp T)) +
        Module.finrank K (LinearMap.range ((LinearMap.id - Q').comp T)))
private theorem rejected_law : ¬ arena.{u,v,w,x,y}.Law rejected := by
  let K := ULift.{u} ℚ
  intro h
  exact @h K PUnit.{v+1} PUnit.{w+1} inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance PUnit.{x+1} PUnit.{y+1}
    inferInstance inferInstance inferInstance inferInstance inferInstance
    0 0 0 0 0 0 (by simp) (by simp) (by simp)

def source_registration : Registration arena.{u,v,w,x,y}
    (type_of% @_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.finrank_tensorSum_split.{u,v,w,x,y}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.finrank_tensorSum_split, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.finrank_tensorSum_split.{u,v,w,x,y})
      (Realization signature.{0}) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.TensorSplit.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.TensorSplit.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,x,y}⟩
  objectArena := .source ⟨arena.{u,v,w,x,y}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,x,y} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{0} (fun _ _ a b => a = b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end TensorSplit

namespace RangeSplit
open scoped TensorProduct
abbrev arena : Arena where
  signature := signature.{0}
  Law R := ∀ {K : Type u} {U : Type v} {V : Type w}
    [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : U →ₗ[K] V) (P : Module.End K U) (Q : Module.End K V)
    (hQ : Q.comp Q = Q) (hT : Q.comp T = T.comp P),
    R.readout () ℕ (Module.finrank K (LinearMap.range T))
      (Module.finrank K (LinearMap.range (Q.comp T)) +
        Module.finrank K (LinearMap.range ((LinearMap.id - Q).comp T)))
private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  let K := ULift.{u} ℚ
  intro h
  exact @h K PUnit.{v+1} PUnit.{w+1} inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance 0 0 0 (by simp) (by simp)

def source_registration : Registration arena.{u,v,w}
    (type_of% @_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.finrank_range_split.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.finrank_range_split, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.finrank_range_split.{u,v,w})
      (Realization signature.{0}) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.RangeSplit.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.RangeSplit.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{0} (fun _ _ a b => a = b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end RangeSplit

end Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting
