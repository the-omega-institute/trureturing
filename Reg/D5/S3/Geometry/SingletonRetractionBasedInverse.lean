import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.SingletonRetractionBasedInverse

noncomputable section

open Set ContinuousMap
open scoped unitInterval
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.SingletonRetractionBasedInverse

namespace Reg.D5.S3.Geometry.SingletonRetractionBasedInverse

universe u v

structure Parameters where
  X : Type u
  Y : Type v
  topX : TopologicalSpace X
  topY : TopologicalSpace Y
  sepX : @T1Space X topX
  sepY : @T1Space Y topY
  x : X
  y : Y
  RX : @CylinderRetraction X topX x
  RY : @CylinderRetraction Y topY y
  f : @ContinuousMap X Y topX topY
  g : @ContinuousMap Y X topY topX
  Hgf : letI := topX; letI := topY
    (g.comp f).Homotopy (ContinuousMap.id X)
  Hfg : letI := topX; letI := topY
    (f.comp g).Homotopy (ContinuousMap.id Y)

attribute [instance] Parameters.topX Parameters.topY Parameters.sepX Parameters.sepY

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := Path (p.f p.x) p.y
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := C(I, p.Y)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ η => η.toContinuousMap) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ η => ContinuousMap.const _ (η ⟨1 / 2, by norm_num⟩)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ (p : Parameters.{u,v}) (η : Path (p.f p.x) p.y),
    ∃ E : BasedEquivalence p.x p.y, ∃ A : p.f.Homotopy E.forward,
      ∀ t, A (t, p.x) = R.readout () p η t

private theorem bridge :
    (type_of% (@based_inverse.{u,v})) ↔ arena.{u,v}.Law actual := by
  constructor
  · intro h p η
    exact h p.x p.y p.RX p.RY p.f p.g p.Hgf p.Hfg η
  · intro h X Y tx ty sx sy x y RX RY f g Hgf Hfg γ
    exact h ⟨X, Y, tx, ty, sx, sy, x, y, RX, RY, f, g, Hgf, Hfg⟩
      γ

private def zeroRetraction : CylinderRetraction (⟨(0 : I)⟩ : ULift.{u} I) where
  map := by
    refine ⟨fun z => ⟨(⟨⟨max ((z.1.down : ℝ) - (z.2 : ℝ)) 0,
      le_max_right _ _, max_le (by linarith [z.1.down.property.2, z.2.property.1]) zero_le_one⟩⟩,
      ⟨max ((z.2 : ℝ) - (z.1.down : ℝ)) 0, le_max_right _ _,
        max_le (by linarith [z.2.property.2, z.1.down.property.1]) zero_le_one⟩), ?_⟩, ?_⟩
    · by_cases h : (z.1.down : ℝ) ≤ (z.2 : ℝ)
      · right
        apply ULift.ext
        apply Subtype.ext
        exact max_eq_right (sub_nonpos.mpr h)
      · left
        apply Subtype.ext
        exact max_eq_right (by linarith)
    · fun_prop
  fixed := by
    intro z hz
    rcases hz with ht | hx
    · apply Prod.ext
      · apply ULift.ext
        apply Subtype.ext
        simp [ht, max_eq_left z.1.down.property.1]
      · apply Subtype.ext
        simp [ht, max_eq_right (neg_nonpos.mpr z.1.down.property.1)]
    · apply Prod.ext
      · apply ULift.ext
        apply Subtype.ext
        simp [hx, max_eq_right (neg_nonpos.mpr z.2.property.1)]
      · apply Subtype.ext
        simp [hx, max_eq_left z.2.property.1]

private def transport : C(ULift.{u} I, ULift.{v} I) :=
  ⟨fun z => ⟨z.down⟩, by fun_prop⟩

private def sample : Parameters.{u,v} where
  X := ULift.{u} I
  Y := ULift.{v} I
  topX := inferInstance
  topY := inferInstance
  sepX := inferInstance
  sepY := inferInstance
  x := ⟨0⟩
  y := ⟨0⟩
  RX := zeroRetraction
  RY := zeroRetraction
  f := transport
  g := transport
  Hgf := (Homotopy.refl (ContinuousMap.id _)).cast rfl rfl
  Hfg := (Homotopy.refl (ContinuousMap.id _)).cast rfl rfl

private def excursion : C(I, ULift.{v} I) :=
  ⟨fun t => ⟨⟨1 - |2 * (t : ℝ) - 1|,
    by
      have h : |2 * (t : ℝ) - 1| ≤ 1 :=
        abs_le.mpr ⟨by linarith [t.property.1], by linarith [t.property.2]⟩
      constructor <;> linarith [abs_nonneg (2 * (t : ℝ) - 1)]⟩⟩,
    by fun_prop⟩

private def excursionPath : signature.State sample.{u,v} where
  toContinuousMap := excursion
  source' := by apply ULift.ext; apply Subtype.ext; norm_num [excursion, sample, transport]
  target' := by apply ULift.ext; apply Subtype.ext; norm_num [excursion, sample]

private def zeroPath : signature.State sample.{u,v} where
  toContinuousMap := ContinuousMap.const _ ⟨0⟩
  source' := rfl
  target' := rfl

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨E, A, hA⟩ := h sample excursionPath
  have he := (A.apply_zero sample.x).symm.trans (hA 0)
  have hh := congrArg (fun z : ULift.{v} I => (z.down : ℝ)) he
  norm_num [rejected, realize, excursionPath, excursion, sample, transport] at hh

def family : Registration arena.{u,v} (type_of% (@based_inverse.{u,v})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@based_inverse.{u,v}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨sample, zeroPath, excursionPath, ?_⟩
    intro h
    have hh := congrArg (fun f : C(I, ULift.{v} I) =>
      ((f ⟨1 / 2, by norm_num⟩).down : ℝ)) h
    norm_num [actual, realize, zeroPath, excursionPath, excursion] at hh

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@based_inverse.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.SingletonRetractionBasedInverse.__information_unit
  realizationName := `Reg.D5.S3.Geometry.SingletonRetractionBasedInverse.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ η => η.toContinuousMap) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.SingletonRetractionBasedInverse
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "arg", "fn", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.Geometry.SingletonRetractionBasedInverse
