import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.Mordell.FieldKummer
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

/-! Full dependent field, twist and covering observations. -/

namespace Reg.D5.S3.Factorization.Mordell.FieldKummer

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open WeierstrassCurve WeierstrassCurve.Affine
namespace F
export _root_.D5.S3.Factorization.Mordell.FieldKummer (Context Twist RepresentativeChange
  curve root descentRep coordinate kummer SquareClass CoveringRep Covering projectRep project
  unitClass changeRepresentatives curve_is_elliptic descentRep_add_square
  descentRep_product_square covering_fiber project_changeRepresentatives)
end F

universe u
noncomputable section

private instance liftCharZero : CharZero (ULift.{u} ℚ) where
  cast_injective := by
    intro m n h
    have hh : (m : ℚ) = (n : ℚ) := congrArg ULift.down h
    exact Nat.cast_injective hh

private theorem liftEq (a b : ULift.{u} ℚ) : a = b ↔ a.down = b.down := by
  constructor
  · exact congrArg ULift.down
  · intro h
    cases a
    cases b
    cases h
    rfl

private def rationalContext : F.Context.{u} :=
  ⟨ULift.{u} ℚ,inferInstance,inferInstance,inferInstance⟩

abbrev curveSignature : Signature where
  Params := F.Context.{u}
  State k := k.Carrier
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := WeierstrassCurve k.Carrier
  Anchor := Empty
  finiteAnchor := inferInstance

def curveActual : Realization curveSignature.{u} :=
  realize curveSignature (fun _ _ d => F.curve d) (fun e => nomatch e)
def curveRejected : Realization curveSignature.{u} :=
  realize curveSignature (fun _ _ _ => F.curve 0) (fun e => nomatch e)
abbrev curveArena : Arena where
  signature := curveSignature.{u}
  Law R := ∀ (C : F.Context.{u}) (d : C.Carrier),
    d ≠ 0 → (R.readout () C d).IsElliptic
private theorem curveNegative : ¬ curveArena.{u}.Law curveRejected := by
  intro h
  have hd := (h rationalContext 1 one_ne_zero).isUnit
  norm_num [curveRejected,realize,_root_.D5.S3.Factorization.Mordell.FieldKummer.curve,
    WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈] at hd

def curveRegistration : Registration curveArena.{u}
    (type_of% (@F.curve_is_elliptic.{u})) where
  actual := curveActual
  bridge := Iff.rfl
  variation := ⟨@F.curve_is_elliptic.{u},curveRejected,curveNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨curveRejected,?_,rfl,curveNegative⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨rationalContext,0,1,?_⟩
    intro h
    have hh := congrArg WeierstrassCurve.a₂ h
    norm_num [curveActual,realize,_root_.D5.S3.Factorization.Mordell.FieldKummer.curve] at hh

abbrev productSignature : Signature where
  Params := Σ C : F.Context.{u}, C.Carrier
  State p := (F.curve p.2).Point
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1.Carrier
  Anchor := Empty
  finiteAnchor := inferInstance

def productActual : Realization productSignature.{u} :=
  realize productSignature (fun _ p P => F.descentRep p.2 0 P * F.descentRep p.2 1 P * F.descentRep p.2 2 P) (fun e => nomatch e)
def productRejected : Realization productSignature.{u} :=
  realize productSignature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev productArena : Arena where
  signature := productSignature.{u}
  Law R := ∀ (C : F.Context.{u}) (d : C.Carrier), d ≠ 0 →
    ∀ P : (F.curve d).Point, IsSquare (R.readout () ⟨C,d⟩ P)
private theorem productNegative : ¬ productArena.{u}.Law productRejected := by
  intro h
  obtain ⟨r,hr⟩ := h rationalContext 1 one_ne_zero 0
  change (-1 : ULift.{u} ℚ) = r*r at hr
  have hh : (-1 : ℚ) = r.down*r.down := congrArg ULift.down hr
  nlinarith [sq_nonneg r.down]
private theorem ordinaryPoint : (F.curve (4 : ULift.{u} ℚ)).Nonsingular (-15) 75 := by
  norm_num [WeierstrassCurve.Affine.nonsingular_iff,
    WeierstrassCurve.Affine.equation_iff,_root_.D5.S3.Factorization.Mordell.FieldKummer.curve]

private theorem ordinaryProduct :
    F.descentRep (4 : ULift.{u} ℚ) 0 0 * F.descentRep 4 1 0 * F.descentRep 4 2 0 ≠
      F.descentRep 4 0 (Point.some (-15) 75 ordinaryPoint) *
        F.descentRep 4 1 (Point.some (-15) 75 ordinaryPoint) *
        F.descentRep 4 2 (Point.some (-15) 75 ordinaryPoint) := by
  norm_num [←Point.zero_def,
    _root_.D5.S3.Factorization.Mordell.FieldKummer.descentRep,
    _root_.D5.S3.Factorization.Mordell.FieldKummer.root,liftEq]

private theorem ordinaryAdd :
    F.descentRep (4 : ULift.{u} ℚ) 0 0 * F.descentRep 4 0 0 *
        F.descentRep 4 0 (0+0) ≠
      F.descentRep 4 0 0 * F.descentRep 4 0 (Point.some (-15) 75 ordinaryPoint) *
        F.descentRep 4 0 (0+Point.some (-15) 75 ordinaryPoint) := by
  rw [zero_add,zero_add]
  norm_num [←Point.zero_def,
    _root_.D5.S3.Factorization.Mordell.FieldKummer.descentRep,
    _root_.D5.S3.Factorization.Mordell.FieldKummer.root,liftEq]

def productRegistration : Registration productArena.{u}
    (type_of% (@F.descentRep_product_square.{u})) where
  actual := productActual
  bridge := Iff.rfl
  variation := ⟨@F.descentRep_product_square.{u},productRejected,productNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨productRejected,?_,rfl,productNegative⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨rationalContext,4⟩,0,Point.some (-15) 75 ordinaryPoint,?_⟩
    exact ordinaryProduct

abbrev addSignature : Signature where
  Params := Σ C : F.Context.{u}, Σ d : C.Carrier, Σ i : Fin 3, (F.curve d).Point
  State p := (F.curve p.2.1).Point
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1.Carrier
  Anchor := Empty
  finiteAnchor := inferInstance

def addActual : Realization addSignature.{u} :=
  realize addSignature (fun _ p Q => F.descentRep p.2.1 p.2.2.1 p.2.2.2 * F.descentRep p.2.1 p.2.2.1 Q * F.descentRep p.2.1 p.2.2.1 (p.2.2.2+Q)) (fun e => nomatch e)
def addRejected : Realization addSignature.{u} :=
  realize addSignature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev addArena : Arena where
  signature := addSignature.{u}
  Law R := ∀ (C : F.Context.{u}) (d : C.Carrier), d ≠ 0 →
    ∀ (i : Fin 3) (P Q : (F.curve d).Point), IsSquare (R.readout () ⟨C,d,i,P⟩ Q)
private theorem addNegative : ¬ addArena.{u}.Law addRejected := by
  intro h
  obtain ⟨r,hr⟩ := h rationalContext 1 one_ne_zero 0 0 0
  change (-1 : ULift.{u} ℚ) = r*r at hr
  have hh : (-1 : ℚ) = r.down*r.down := congrArg ULift.down hr
  nlinarith [sq_nonneg r.down]

def addRegistration : Registration addArena.{u}
    (type_of% (@F.descentRep_add_square.{u})) where
  actual := addActual
  bridge := Iff.rfl
  variation := ⟨@F.descentRep_add_square.{u},addRejected,addNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨addRejected,?_,rfl,addNegative⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨rationalContext,4,0,0⟩,0,Point.some (-15) 75 ordinaryPoint,?_⟩
    exact ordinaryAdd

abbrev fiberSignature : Signature where
  Params := Σ T : F.Twist.{u}, Σ b₁ : T.k.Carrierˣ, T.k.Carrierˣ
  State p := F.Covering p.1.d p.2.1 p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (F.curve p.1.d).Point
  Anchor := Empty
  finiteAnchor := inferInstance

def fiberActual : Realization fiberSignature.{u} :=
  realize fiberSignature (fun _ p c => F.project p.1.d p.1.hd p.2.1 p.2.2 c) (fun e => nomatch e)
def fiberRejected : Realization fiberSignature.{u} :=
  realize fiberSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev fiberArena : Arena where
  signature := fiberSignature.{u}
  Law R := ∀ (T : F.Twist.{u}) (b₁ b₂ : T.k.Carrierˣ) (P : (F.curve T.d).Point),
    (∃ c : F.Covering T.d b₁ b₂, R.readout () ⟨T,b₁,b₂⟩ c = P) ↔
      F.kummer T.d T.hd P = (F.unitClass b₁,F.unitClass b₂)
private def testTwist : F.Twist.{u} := ⟨rationalContext,-1/5,by norm_num⟩
private def finiteRep : F.CoveringRep (-1/5 : ULift.{u} ℚ) 1 1 where
  t := 1
  z₁ := 1
  z₂ := 0
  z₃ := 2
  nonzero := Or.inl one_ne_zero
  eq₁₂ := by norm_num
  eq₁₃ := by norm_num
private def infiniteRep : F.CoveringRep (-1/5 : ULift.{u} ℚ) 1 1 where
  t := 0
  z₁ := 1
  z₂ := 1
  z₃ := 1
  nonzero := Or.inr (Or.inl one_ne_zero)
  eq₁₂ := by norm_num
  eq₁₃ := by norm_num
private theorem finiteProject_ne_zero :
    F.project (-1/5 : ULift.{u} ℚ) (by norm_num) 1 1 (Quotient.mk _ finiteRep) ≠ 0 := by
  change F.projectRep (-1/5 : ULift.{u} ℚ) (by norm_num) 1 1 finiteRep ≠ 0
  simp [_root_.D5.S3.Factorization.Mordell.FieldKummer.projectRep,finiteRep]
private theorem fiberNegative : ¬ fiberArena.{u}.Law fiberRejected := by
  intro h
  let c : F.Covering testTwist.d 1 1 := Quotient.mk _ finiteRep
  let P := F.project testTwist.d testTwist.hd 1 1 c
  have hk := (F.covering_fiber testTwist 1 1 P).mp ⟨c,rfl⟩
  obtain ⟨c',hc'⟩ := (h testTwist 1 1 P).mpr hk
  exact finiteProject_ne_zero hc'.symm

def fiberRegistration : Registration fiberArena.{u}
    (type_of% (@F.covering_fiber.{u})) where
  actual := fiberActual
  bridge := Iff.rfl
  variation := ⟨@F.covering_fiber.{u},fiberRejected,fiberNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨fiberRejected,?_,rfl,fiberNegative⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨testTwist,1,1⟩,Quotient.mk _ infiniteRep,Quotient.mk _ finiteRep,?_⟩
    intro hh
    have hz : fiberActual.readout i ⟨testTwist,1,1⟩ (Quotient.mk _ infiniteRep) = 0 := by
      change F.projectRep (-1/5 : ULift.{u} ℚ) (by norm_num) 1 1 infiniteRep = 0
      simp [_root_.D5.S3.Factorization.Mordell.FieldKummer.projectRep,infiniteRep]
    rw [hz] at hh
    exact finiteProject_ne_zero hh.symm

abbrev changeSignature : Signature where
  Params := F.RepresentativeChange.{u}
  State p := F.Covering p.twist.d p.b₁ p.b₂
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (F.curve p.twist.d).Point
  Anchor := Empty
  finiteAnchor := inferInstance

def changeActual : Realization changeSignature.{u} :=
  realize changeSignature (fun _ p c => F.project p.twist.d p.twist.hd p.b₁' p.b₂'
    (F.changeRepresentatives p.twist.d p.b₁ p.b₂ p.b₁' p.b₂' p.u p.v p.h₁ p.h₂ c)) (fun e => nomatch e)
def changeRejected : Realization changeSignature.{u} :=
  realize changeSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev changeArena : Arena where
  signature := changeSignature.{u}
  Law R := ∀ (a : F.RepresentativeChange.{u}) (c : F.Covering a.twist.d a.b₁ a.b₂),
    R.readout () a c = F.project a.twist.d a.twist.hd a.b₁ a.b₂ c
private def testChange : F.RepresentativeChange.{u} :=
  ⟨testTwist,1,1,1,1,1,1,by norm_num,by norm_num⟩
private theorem changeNegative : ¬ changeArena.{u}.Law changeRejected := by
  intro h
  exact finiteProject_ne_zero (h testChange (Quotient.mk _ finiteRep)).symm
private theorem changeActual_eq (i : Unit) (p : F.RepresentativeChange.{u})
    (c : F.Covering p.twist.d p.b₁ p.b₂) :
    changeActual.readout i p c = F.project p.twist.d p.twist.hd p.b₁ p.b₂ c :=
  F.project_changeRepresentatives p c

def changeRegistration : Registration changeArena.{u}
    (type_of% (@F.project_changeRepresentatives.{u})) where
  actual := changeActual
  bridge := Iff.rfl
  variation := ⟨@F.project_changeRepresentatives.{u},changeRejected,changeNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨changeRejected,?_,rfl,changeNegative⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨testChange,Quotient.mk _ infiniteRep,Quotient.mk _ finiteRep,?_⟩
    have hz' : F.project (-1/5 : ULift.{u} ℚ) (by norm_num) 1 1
        (Quotient.mk _ infiniteRep) = 0 := by
      change F.projectRep (-1/5 : ULift.{u} ℚ) (by norm_num) 1 1 infiniteRep = 0
      simp [_root_.D5.S3.Factorization.Mordell.FieldKummer.projectRep,infiniteRep]
    have hz := (changeActual_eq i testChange (Quotient.mk _ infiniteRep)).trans hz'
    intro hh
    exact finiteProject_ne_zero ((changeActual_eq i testChange (Quotient.mk _ finiteRep)).symm.trans
      (hh.symm.trans hz))

noncomputable def curve_is_elliptic_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@F.curve_is_elliptic.{u})
      (type_of% (realize curveSignature.{u} (fun _ _ d => F.curve d) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.FieldKummer.curve_is_elliptic.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.FieldKummer.curveRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨curveArena.{u}⟩, objectArena := .source ⟨curveArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source curveArena.{u} ⟨curveRegistration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize curveSignature.{u} (fun _ _ d => F.curve d) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.FieldKummer, definition := none, coordinates := #[0], readouts := #[{ path := #["body","body","body","arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `relaxedAutoImplicit, value := .bool false }]
}
#print axioms curveRegistration
#print axioms curve_is_elliptic_registration

noncomputable def descentRep_product_square_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@F.descentRep_product_square.{u})
      (type_of% (realize productSignature.{u} (fun _ p P => F.descentRep p.2 0 P * F.descentRep p.2 1 P * F.descentRep p.2 2 P) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.FieldKummer.descentRep_product_square.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.FieldKummer.productRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨productArena.{u}⟩, objectArena := .source ⟨productArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source productArena.{u} ⟨productRegistration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize productSignature.{u} (fun _ p P => F.descentRep p.2 0 P * F.descentRep p.2 1 P * F.descentRep p.2 2 P) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.FieldKummer, definition := none, coordinates := #[0,1], readouts := #[{ path := #["body","body","body","body","arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `relaxedAutoImplicit, value := .bool false }]
}
#print axioms productRegistration
#print axioms descentRep_product_square_registration

noncomputable def descentRep_add_square_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@F.descentRep_add_square.{u})
      (type_of% (realize addSignature.{u} (fun _ p Q => F.descentRep p.2.1 p.2.2.1 p.2.2.2 * F.descentRep p.2.1 p.2.2.1 Q * F.descentRep p.2.1 p.2.2.1 (p.2.2.2+Q)) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.FieldKummer.descentRep_add_square.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.FieldKummer.addRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨addArena.{u}⟩, objectArena := .source ⟨addArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source addArena.{u} ⟨addRegistration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize addSignature.{u} (fun _ p Q => F.descentRep p.2.1 p.2.2.1 p.2.2.2 * F.descentRep p.2.1 p.2.2.1 Q * F.descentRep p.2.1 p.2.2.1 (p.2.2.2+Q)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.FieldKummer, definition := none, coordinates := #[0,1,3,4], readouts := #[{ path := #["body","body","body","body","body","body","arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `relaxedAutoImplicit, value := .bool false }]
}
#print axioms addRegistration
#print axioms descentRep_add_square_registration

noncomputable def covering_fiber_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@F.covering_fiber.{u})
      (type_of% (realize fiberSignature.{u} (fun _ p c => F.project p.1.d p.1.hd p.2.1 p.2.2 c) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.FieldKummer.covering_fiber.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.FieldKummer.fiberRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨fiberArena.{u}⟩, objectArena := .source ⟨fiberArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source fiberArena.{u} ⟨fiberRegistration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize fiberSignature.{u} (fun _ p c => F.project p.1.d p.1.hd p.2.1 p.2.2 c) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.FieldKummer, definition := none, coordinates := #[0,1,2], readouts := #[{ path := #["body","body","body","body","fn","arg","arg","body","fn","arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `relaxedAutoImplicit, value := .bool false }]
}
#print axioms fiberRegistration
#print axioms covering_fiber_registration

noncomputable def project_changeRepresentatives_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@F.project_changeRepresentatives.{u})
      (type_of% (realize changeSignature.{u} (fun _ p c => F.project p.twist.d p.twist.hd p.b₁' p.b₂' (F.changeRepresentatives p.twist.d p.b₁ p.b₂ p.b₁' p.b₂' p.u p.v p.h₁ p.h₂ c)) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.FieldKummer.project_changeRepresentatives.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.FieldKummer.changeRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨changeArena.{u}⟩, objectArena := .source ⟨changeArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source changeArena.{u} ⟨changeRegistration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize changeSignature.{u} (fun _ p c => F.project p.twist.d p.twist.hd p.b₁' p.b₂' (F.changeRepresentatives p.twist.d p.b₁ p.b₂ p.b₁' p.b₂' p.u p.v p.h₁ p.h₂ c)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.FieldKummer, definition := none, coordinates := #[0], readouts := #[{ path := #["body","body","fn","arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `relaxedAutoImplicit, value := .bool false }]
}
#print axioms changeRegistration
#print axioms project_changeRepresentatives_registration

end
end Reg.D5.S3.Factorization.Mordell.FieldKummer
