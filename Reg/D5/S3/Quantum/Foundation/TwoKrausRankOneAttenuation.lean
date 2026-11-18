import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation

/-! Exact source-bound relation readouts for the CAR attenuation theorems. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open _root_.D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation

namespace MatrixRelation
abbrev signature.{v} : Signature where
  Params := Type v
  State p := Matrix p p ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p p ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def equality.{v} : Realization signature.{v} :=
  realize signature (fun _ _ X => Eq X) (fun e => nomatch e)
def order.{v} : Realization signature.{v} :=
  realize signature (fun _ _ X Y => X ≤ Y) (fun e => nomatch e)
def rejected.{v} : Realization signature.{v} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem eq_dependence.{v} : ObservationalDependence signature.{v} equality := by
  intro i
  refine ⟨ULift.{v} Unit, 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : Matrix (ULift.{v} Unit) (ULift.{v} Unit) ℂ) = 0) = (1 = 0) at he
  exact one_ne_zero (Eq.mp he rfl)

private theorem order_dependence.{v} : ObservationalDependence signature.{v} order := by
  intro i
  refine ⟨ULift.{v} Unit, 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : Matrix (ULift.{v} Unit) (ULift.{v} Unit) ℂ) ≤ 0) = (1 ≤ 0) at he
  have hh := (Matrix.le_iff.mp (Eq.mp he le_rfl)).trace_nonneg
  norm_num [Matrix.trace] at hh
end MatrixRelation

namespace RealOrder
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
  norm_num at he
end RealOrder

namespace Sandwich
abbrev arena.{v} : Arena where
  signature := MatrixRelation.signature.{v}
  Law O := ∀ {n : Type v} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℂ) (q : ℝ) (_hq : 0 ≤ q) (X : Matrix n n ℂ),
    O.readout () n (jumpMap J q X)
      (jumpFilter J q * X * (jumpFilter J q).conjTranspose +
        (q : ℂ) • (J * X * J.conjTranspose))
private theorem rejected_law.{v} : ¬ arena.{v}.Law MatrixRelation.rejected := by
  intro h
  exact @h (ULift.{v} Unit) inferInstance inferInstance 0 0 le_rfl 0

def family.{v} : Registration arena.{v} (type_of% (@jumpMap_apply.{v})) where
  actual := MatrixRelation.equality
  bridge := Iff.rfl
  variation := ⟨@jumpMap_apply.{v}, MatrixRelation.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨MatrixRelation.rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
        rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := MatrixRelation.eq_dependence
end Sandwich

namespace Positive
abbrev arena.{v} : Arena where
  signature := MatrixRelation.signature.{v}
  Law O := ∀ {n : Type v} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℂ) (q : ℝ) (_hq : 0 ≤ q)
    {X : Matrix n n ℂ} (_hX : 0 ≤ X), O.readout () n 0 (jumpMap J q X)
private theorem rejected_law.{v} : ¬ arena.{v}.Law MatrixRelation.rejected := by
  intro h
  exact @h (ULift.{v} Unit) inferInstance inferInstance 0 0 le_rfl 0 le_rfl

def family.{v} : Registration arena.{v} (type_of% (@jumpMap_positive.{v})) where
  actual := MatrixRelation.order
  bridge := Iff.rfl
  variation := ⟨@jumpMap_positive.{v}, MatrixRelation.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨MatrixRelation.rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
        rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := MatrixRelation.order_dependence
end Positive

namespace Contraction
abbrev arena.{v} : Arena where
  signature := RealOrder.signature
  Law O := ∀ {n : Type v} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℂ) (_hJ : J * J = 0)
    (_hCAR : J * J.conjTranspose + J.conjTranspose * J = 1)
    (q : ℝ) (_hq0 : 0 ≤ q) (_hq1 : q ≤ 1)
    (X : Matrix n n ℂ) (_hX : X.IsHermitian),
    O.readout () () ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (jumpMap J q X)‖
      ‖toEuclideanCLM (n := n) (𝕜 := ℂ) X‖
private theorem rejected_law.{v} : ¬ arena.{v}.Law RealOrder.rejected := by
  intro h
  exact @h (ULift.{v} Empty) inferInstance inferInstance 0 (by simp)
    (by ext i; exact i.down.elim) 0 le_rfl zero_le_one 0 isHermitian_zero

def family.{v} : Registration arena.{v} (type_of% (@jumpMap_norm_le.{v})) where
  actual := RealOrder.actual
  bridge := Iff.rfl
  variation := ⟨@jumpMap_norm_le.{v}, RealOrder.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨RealOrder.rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
        rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := RealOrder.dependence
end Contraction

namespace RankOne
abbrev arena.{v} : Arena where
  signature := RealOrder.signature
  Law O := ∀ {n : Type v} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℂ) (_hJ : J * J = 0)
    (_hCAR : J * J.conjTranspose + J.conjTranspose * J = 1)
    (q : ℝ) (_hq0 : 0 ≤ q) (_hq1 : q ≤ 1)
    (ψ : EuclideanSpace ℂ n) (_hψ : ‖ψ‖ = 1),
    let u := WithLp.ofLp ψ
    let p := (star u ⬝ᵥ ((J * J.conjTranspose) *ᵥ u)).re
    let c := star u ⬝ᵥ (J *ᵥ u)
    O.readout () () ‖toEuclideanCLM (n := n) (𝕜 := ℂ)
      (jumpMap J q (vecMulVec u (star u)))‖
      (1 - q * (1-q) * (p - Complex.normSq c))

private theorem rejected_law.{v} : ¬ arena.{v}.Law RealOrder.rejected := by
  intro h
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;0,0]
  have ha : A * A = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, Matrix.mul_apply, Fin.sum_univ_two]
  have hc : A * A.conjTranspose + A.conjTranspose * A = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two, Matrix.conjTranspose_apply]
  let e : ULift.{v} (Fin 2) ≃ Fin 2 := Equiv.ulift
  let K := A.submatrix e e
  have hk : K * K = 0 := by
    dsimp [K]
    rw [submatrix_mul_equiv, ha]
    rfl
  have hkc : K * K.conjTranspose + K.conjTranspose * K = 1 := by
    dsimp [K]
    simp only [conjTranspose_submatrix, submatrix_mul_equiv]
    change (A * A.conjTranspose + A.conjTranspose * A).submatrix e e = 1
    rw [hc, submatrix_one_equiv]
  exact @h (ULift.{v} (Fin 2)) inferInstance inferInstance K hk hkc 0 le_rfl
    zero_le_one (EuclideanSpace.single ⟨0⟩ 1) (by simp [EuclideanSpace.single])

def family.{v} : Registration arena.{v}
    (type_of% (@nilpotent_jump_rank_one_attenuation.{v})) where
  actual := RealOrder.actual
  bridge := Iff.rfl
  variation := ⟨@nilpotent_jump_rank_one_attenuation.{v}, RealOrder.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨RealOrder.rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
        rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := RealOrder.dependence
end RankOne


namespace Sandwich
def audit.{v} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@jumpMap_apply.{v}) (Realization MatrixRelation.signature.{v}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation.Sandwich.unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation.Sandwich.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize MatrixRelation.signature.{v} (fun _ _ X => Eq X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Sandwich

namespace Positive
def audit.{v} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@jumpMap_positive.{v}) (Realization MatrixRelation.signature.{v}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation.Positive.unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation.Positive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize MatrixRelation.signature.{v} (fun _ _ X Y => X ≤ Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Positive

namespace Contraction
def audit.{v} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@jumpMap_norm_le.{v}) (Realization RealOrder.signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation.Contraction.unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation.Contraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize RealOrder.signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Contraction
namespace RankOne
def audit.{v} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nilpotent_jump_rank_one_attenuation.{v}) (Realization RealOrder.signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation.RankOne.unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation.RankOne.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize RealOrder.signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end RankOne

end Reg.D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation
