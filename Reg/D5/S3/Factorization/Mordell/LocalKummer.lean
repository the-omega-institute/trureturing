import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.Mordell.LocalKummer
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

/-! Rational-to-field naturality with the entire field and point telescope. -/

namespace Reg.D5.S3.Factorization.Mordell.LocalKummer

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open WeierstrassCurve WeierstrassCurve.Affine

namespace F
export _root_.D5.S3.Factorization.Mordell.FieldKummer (Context curve kummer SquareClass unitClass)
end F
namespace L
export _root_.D5.S3.Factorization.Mordell.LocalKummer (rationalBaseChange classMap rational_naturality)
end L
namespace R
export _root_.D5.S3.Factorization.Mordell.RationalKummer (curve kummer classOf SquareClass block_kummer_images)
end R

universe u
noncomputable section

private instance liftCharZero : CharZero (ULift.{u} ℚ) where
  cast_injective := by
    intro m n h
    have hh : (m : ℚ) = (n : ℚ) := congrArg ULift.down h
    exact Nat.cast_injective hh

private def rationalContext : F.Context.{u} :=
  ⟨ULift.{u} ℚ,inferInstance,inferInstance,inferInstance⟩

abbrev signature : Signature where
  Params := Σ C : F.Context.{u}, ℚˣ
  State p := (R.curve (p.2 : ℚ)).Point
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Additive (F.SquareClass p.1.Carrier) × Additive (F.SquareClass p.1.Carrier)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p P =>
    ((L.classMap (K := p.1.Carrier)).prodMap L.classMap) (R.kummer (p.2 : ℚ) p.2.ne_zero P))
    (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ =>
    (F.unitClass (Units.mk0 (-1 : p.1.Carrier) (neg_ne_zero.mpr one_ne_zero)),0))
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law A := ∀ (C : F.Context.{u}) (D : ℚˣ) (P : (R.curve (D : ℚ)).Point),
    F.kummer ((D : ℚ) : C.Carrier) (Rat.cast_ne_zero.mpr D.ne_zero) (L.rationalBaseChange (D : ℚ) P) =
      A.readout () ⟨C,D⟩ P

private theorem negativeUnitClass :
    F.unitClass (Units.mk0 (-1 : ULift.{u} ℚ) (neg_ne_zero.mpr one_ne_zero)) ≠ 0 := by
  intro h
  change ((Units.mk0 (-1 : ULift.{u} ℚ) _ : (ULift.{u} ℚ)ˣ) : F.SquareClass (ULift.{u} ℚ)) = 1 at h
  obtain ⟨w,hw⟩ := (QuotientGroup.eq_one_iff _).mp h
  have hh := congrArg (fun v : (ULift.{u} ℚ)ˣ => (v : ULift.{u} ℚ).down) hw
  change w.val.down^2 = -1 at hh
  nlinarith [sq_nonneg w.val.down]

private theorem mappedNegative (a : ℚ) (ha : a < 0) :
    L.classMap (K := ULift.{u} ℚ) (R.classOf a (ne_of_lt ha)) ≠ 0 := by
  intro h
  dsimp only [_root_.D5.S3.Factorization.Mordell.LocalKummer.classMap,
    _root_.D5.S3.Factorization.Mordell.RationalKummer.classOf] at h
  change ((Units.map (Rat.castHom (ULift.{u} ℚ)).toMonoidHom
    (Units.mk0 a (ne_of_lt ha)) : (ULift.{u} ℚ)ˣ) : F.SquareClass (ULift.{u} ℚ)) = 1 at h
  obtain ⟨w,hw⟩ := (QuotientGroup.eq_one_iff _).mp h
  have hh := congrArg (fun v : (ULift.{u} ℚ)ˣ => (ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ) v.val) hw
  have hh' : ((ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ) w.val)^2 = a := by simpa using hh
  nlinarith [sq_nonneg ((ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ) w.val)]

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := congrArg Prod.fst (h rationalContext 1 0)
  have hz : F.kummer (1 : ULift.{u} ℚ) (Rat.cast_ne_zero.mpr (one_ne_zero : (1 : ℚ) ≠ 0))
      (L.rationalBaseChange 1 0) = 0 := by rw [map_zero,map_zero]
  change (F.kummer (1 : ULift.{u} ℚ) _ (L.rationalBaseChange 1 0)).1 = _ at hh
  rw [hz] at hh
  exact negativeUnitClass hh.symm

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  have hR : (R.curve 4).Nonsingular 80 400 := by
    norm_num [WeierstrassCurve.Affine.nonsingular_iff,
      WeierstrassCurve.Affine.equation_iff,_root_.D5.S3.Factorization.Mordell.RationalKummer.curve]
  have hS : (R.curve 4).Nonsingular (-15) 75 := by
    norm_num [WeierstrassCurve.Affine.nonsingular_iff,
      WeierstrassCurve.Affine.equation_iff,_root_.D5.S3.Factorization.Mordell.RationalKummer.curve]
  have hR' : (R.curve 4).Nonsingular (5*4*(1^2+3)) (25*4^2*1*1*1) := by
    convert hR using 1 <;> norm_num
  have hS' : (R.curve 4).Nonsingular (-15/1^2) (75*1*1/1^3) := by
    convert hS using 1 <;> norm_num
  have hk : R.kummer (4 : ℚ) (by norm_num) (Point.some (-15) 75 hS) =
      (R.classOf (-15) (by norm_num),R.classOf 5 (by norm_num)) := by
    simpa only [one_pow,div_one,mul_one] using
      (R.block_kummer_images 4 1 1 1 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) hR' hS').2.1
  refine ⟨⟨rationalContext,Units.mk0 4 (by norm_num)⟩,
    0,Point.some (-15) 75 hS,?_⟩
  intro hh
  dsimp only [actual,realize] at hh
  change ((L.classMap (K := ULift.{u} ℚ)).prodMap L.classMap)
    (R.kummer (4 : ℚ) (by norm_num) 0) =
    ((L.classMap (K := ULift.{u} ℚ)).prodMap L.classMap)
      (R.kummer (4 : ℚ) (by norm_num) (Point.some (-15) 75 hS)) at hh
  rw [map_zero,map_zero,hk] at hh
  have hf := congrArg Prod.fst hh
  exact mappedNegative (-15) (by norm_num) hf.symm

def registration : Registration arena.{u}
    (type_of% (@L.rational_naturality.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@L.rational_naturality.{u},rejected,rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejectedLaw⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def rational_naturality_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@L.rational_naturality.{u})
      (type_of% (realize signature.{u} (fun _ p P =>
        ((L.classMap (K := p.1.Carrier)).prodMap L.classMap) (R.kummer (p.2 : ℚ) p.2.ne_zero P)) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Factorization.Mordell.LocalKummer.rational_naturality.__information_unit,
  realizationName := `Reg.D5.S3.Factorization.Mordell.LocalKummer.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨registration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ p P =>
    ((L.classMap (K := p.1.Carrier)).prodMap L.classMap) (R.kummer (p.2 : ℚ) p.2.ne_zero P)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Mordell.LocalKummer, definition := none, coordinates := #[0,1], readouts := #[{ path := #["body","body","body","arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `relaxedAutoImplicit, value := .bool false }]
}
#print axioms registration
#print axioms rational_naturality_registration

end
end Reg.D5.S3.Factorization.Mordell.LocalKummer
