import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.SpinFactor.OriginalPureRigidity
import D5.S3.Quantum.SpinFactor.OriginalClassification

/-! Source-equivalence families for the pure theorems and original endpoint.

The closed registration constants use the original positive cross model only
to witness failure of the rejected readout. Their laws retain every original
relation and supplier premise, including the full P2/PB endpoint telescope.
The supplier and Euclidean adapters are unnamed proof terms; the mathematical
source declarations and their visibility are unchanged.
-/

noncomputable section

open _root_.D5.S3.Quantum.SpinFactor.OriginalDContract
open _root_.D5.S3.Quantum.SpinFactor.OriginalPureRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.SpinFactor.OriginalPureRigidity

local notation "auditModelLaws" =>
  ((_root_.D5.S3.Quantum.SpinFactor.OriginalClassification.complete_classification
    (crossD .plus)).mpr ⟨.plus, fun _ _ => rfl⟩)

local notation "auditSuppliers" =>
  (show PureSuppliers (crossD .plus) from by
    have laws := auditModelLaws
    refine {
      antisymmetric := p2_skew _ laws.1
      axis_zero := collinear_zero _ laws.1 laws.2
      difference := (pb_iff_finite_difference _).mp laws.2
      bound := ?_
      label_rotation := ?_ }
    · intro n hn a b
      let α : Evaluation := ⟨1, n, by simp [vnorm, hn]⟩
      have hnn : dotProduct n n = 1 := hn
      have he (u v : E) :
          evaluate α (jordan u v) = dot (lift n u) (lift n v) := by
        simp only [evaluate, α, jordan, lift, dot, one_mul,
          add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
          smul_eq_mul, hnn, dotProduct_comm u.2 n]
        ring
      have hcross (x y : Vec) :
          dot (crossProduct x y) (crossProduct x y) =
            dot x x * dot y y - dot x y ^ 2 := by
        simpa only [dot, pow_two, dotProduct_comm y x] using
          (cross_dot_cross x y x y)
      have hb := p2_determinant_bound (crossD .plus) laws.1 α a b
      rw [he a a, he b b, he a b] at hb
      simpa only [evaluate, α, one_mul, hcross] using hb
    · intro a b c s hcs
      simpa only [sub_eq_add_neg, neg_smul, add_comm] using
        (_root_.D5.S3.Quantum.SpinFactor.OriginalDContract.label_rotation
          (crossD .plus) laws.1 laws.2 c s hcs a b))

local notation "auditPerpendicular" =>
  (show CommonNonunitPerpendicular from by
    intro a b
    obtain ⟨n, hn, han, hbn⟩ :=
      _root_.D5.S3.Geometry.TwoAxisFiniteRotation.unit_perpendicular_pair
        (WithLp.toLp 2 a) (WithLp.toLp 2 b)
    let v : Vec := WithLp.ofLp n
    have hv : dot v v = 1 := by
      have hs := EuclideanSpace.real_norm_sq_eq n
      rw [hn] at hs
      simpa only [one_pow, dot, dotProduct, v, pow_two, one_mul] using hs.symm
    have hav : dot a v = 0 := by
      simpa [PiLp.inner_apply, RCLike.inner_apply, dot, dotProduct, v, mul_comm] using han
    have hbv : dot b v = 0 := by
      simpa [PiLp.inner_apply, RCLike.inner_apply, dot, dotProduct, v, mul_comm] using hbn
    have hvv : dotProduct v v = 1 := hv
    have hav' : dotProduct a v = 0 := hav
    have hbv' : dotProduct b v = 0 := hbv
    let z : Vec := (2 : ℝ) • v
    have hzz : dot z z = 4 := by
      norm_num [z, dot, smul_dotProduct, dotProduct_smul, smul_eq_mul, hvv]
    refine ⟨z, ?_, ?_, ?_, ?_⟩
    · intro hz
      rw [hz] at hzz
      norm_num [dot] at hzz
    · simp only [z, dot, dotProduct_smul, smul_eq_mul, hav', mul_zero]
    · simp only [z, dot, dotProduct_smul, smul_eq_mul, hbv', mul_zero]
    · rw [hzz]
      norm_num)

abbrev equalitySignature (α : Type) : Signature where
  Params := Unit
  State _ := α
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := α → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def equalityActual (α : Type) : Realization (equalitySignature α) :=
  realize (equalitySignature α) (fun _ _ x y => x = y) (fun e => nomatch e)

def equalityRejected (α : Type) : Realization (equalitySignature α) :=
  realize (equalitySignature α) (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem equalitySensitivity (α : Type)
    (law : Realization (equalitySignature α) → Prop)
    (hbad : ¬ law (equalityRejected α)) :
    Sensitivity ⟨equalitySignature α, law⟩ (equalityActual α) := by
  refine ⟨fun i => ⟨equalityRejected α, ?_, rfl, hbad⟩, fun e => nomatch e⟩
  intro j hji
  exact (hji (Subsingleton.elim j i)).elim

private theorem outputDependence :
    ObservationalDependence (equalitySignature E) (equalityActual E) := by
  intro i
  refine ⟨(), 0, unit, ?_⟩
  intro heq
  have h : unit = (0 : E) := Eq.mp (congrFun heq 0) rfl
  have hs := congrArg Prod.fst h
  norm_num [unit] at hs

private theorem signDependence :
    ObservationalDependence (equalitySignature ℝ) (equalityActual ℝ) := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro heq
  have h : (1 : ℝ) = 0 := Eq.mp (congrFun heq 0) rfl
  norm_num at h

private def x₀ : Vec := ![2, 0, 0]
private def y₀ : Vec := ![0, 1, 0]
private def z₀ : Vec := ![0, 1, 1]

private theorem x₀_ne : x₀ ≠ 0 := by
  intro h
  have hi := congrFun h 0
  norm_num [x₀] at hi

private theorem y₀_ne : y₀ ≠ 0 := by
  intro h
  have hi := congrFun h 1
  norm_num [y₀] at hi

private theorem xy₀_perp : dot x₀ y₀ = 0 := by
  norm_num [x₀, y₀, dot, dotProduct, Fin.sum_univ_succ]

namespace OrthogonalSaturation

abbrev arena : Arena where
  signature := equalitySignature E
  Law O := ∀ (D : E → E → E) (_ : PureSuppliers D) {x y : Vec},
    x ≠ 0 → y ≠ 0 → dot x y = 0 → ∃ k : ℝ, k ^ 2 = 1 ∧
      O.readout () () (D (pure x) (pure y)) (0, k • cross x y)

private theorem rejected_law (D₀ : E → E → E) (h₀ : PureSuppliers D₀) :
    ¬ arena.Law (equalityRejected E) := by
  intro h
  obtain ⟨k, hk, hf⟩ := h D₀ h₀ x₀_ne y₀_ne xy₀_perp
  exact hf

def family :
    Registration arena (type_of% (@orthogonal_saturation)) where
  actual := equalityActual E
  bridge := Iff.rfl
  variation := ⟨@orthogonal_saturation, equalityRejected E,
    rejected_law (crossD .plus) auditSuppliers⟩
  sensitivity := equalitySensitivity E arena.Law
    (rejected_law (crossD .plus) auditSuppliers)
  dependence := outputDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@orthogonal_saturation) (Realization (equalitySignature E)) Type Unit where
  unitName := `D5.S3.Quantum.SpinFactor.OriginalPureRigidity.orthogonal_saturation.audit
  realizationName := `Reg.D5.S3.Quantum.SpinFactor.OriginalPureRigidity.OrthogonalSaturation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (equalitySignature E)
    (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some E
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinFactor.OriginalPureRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end OrthogonalSaturation

namespace PairSaturation

abbrev arena : Arena where
  signature := equalitySignature E
  Law O := ∀ (D : E → E → E) (_ : PureSuppliers D) (x y : Vec),
    ∃ k : ℝ, k ^ 2 = 1 ∧
      O.readout () () (D (pure x) (pure y)) (0, k • cross x y)

private theorem rejected_law (D₀ : E → E → E) (h₀ : PureSuppliers D₀) :
    ¬ arena.Law (equalityRejected E) := by
  intro h
  obtain ⟨k, hk, hf⟩ := h D₀ h₀ 0 0
  exact hf

def family :
    Registration arena (type_of% (@pure_pair_saturation)) where
  actual := equalityActual E
  bridge := Iff.rfl
  variation := ⟨@pure_pair_saturation, equalityRejected E,
    rejected_law (crossD .plus) auditSuppliers⟩
  sensitivity := equalitySensitivity E arena.Law
    (rejected_law (crossD .plus) auditSuppliers)
  dependence := outputDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@pure_pair_saturation) (Realization (equalitySignature E)) Type Unit where
  unitName := `D5.S3.Quantum.SpinFactor.OriginalPureRigidity.pure_pair_saturation.audit
  realizationName := `Reg.D5.S3.Quantum.SpinFactor.OriginalPureRigidity.PairSaturation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (equalitySignature E)
    (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some E
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinFactor.OriginalPureRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PairSaturation

namespace TransverseSign

abbrev arena : Arena where
  signature := equalitySignature ℝ
  Law O := ∀ (D : E → E → E) (_ : PureSuppliers D) {x y z : Vec},
    dot x x ≠ 1 → dot x y = 0 → dot x z = 0 → dot y z ≠ 0 →
    dot x (cross y z) ≠ 0 → ∀ {k l : ℝ}, k ^ 2 = 1 → l ^ 2 = 1 →
    D (pure x) (pure y) = (0, k • cross x y) →
    D (pure x) (pure z) = (0, l • cross x z) → O.readout () () k l

private theorem rejected_law (D₀ : E → E → E) (h₀ : PureSuppliers D₀) :
    ¬ arena.Law (equalityRejected ℝ) := by
  intro h
  obtain ⟨k, hk, hky⟩ := pure_pair_saturation D₀ h₀ x₀ y₀
  obtain ⟨l, hl, hlz⟩ := pure_pair_saturation D₀ h₀ x₀ z₀
  apply h (D := D₀) h₀ (x := x₀) (y := y₀) (z := z₀)
      (k := k) (l := l) _ xy₀_perp _ _ _ hk hl hky hlz
  all_goals norm_num [x₀, y₀, z₀, dot, cross, dotProduct, Fin.sum_univ_succ]

def family :
    Registration arena (type_of% (@transverse_sign)) where
  actual := equalityActual ℝ
  bridge := Iff.rfl
  variation := ⟨@transverse_sign, equalityRejected ℝ,
    rejected_law (crossD .plus) auditSuppliers⟩
  sensitivity := equalitySensitivity ℝ arena.Law
    (rejected_law (crossD .plus) auditSuppliers)
  dependence := signDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@transverse_sign) (Realization (equalitySignature ℝ)) Type Unit where
  unitName := `D5.S3.Quantum.SpinFactor.OriginalPureRigidity.transverse_sign.audit
  realizationName := `Reg.D5.S3.Quantum.SpinFactor.OriginalPureRigidity.TransverseSign.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (equalitySignature ℝ)
    (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinFactor.OriginalPureRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TransverseSign

namespace NonunitRowSign

abbrev arena : Arena where
  signature := equalitySignature ℝ
  Law O := ∀ (D : E → E → E) (_ : PureSuppliers D) {x y z : Vec},
    x ≠ 0 → dot x x ≠ 1 → y ≠ 0 → z ≠ 0 → dot x y = 0 → dot x z = 0 →
    ∀ {k l : ℝ}, k ^ 2 = 1 → l ^ 2 = 1 →
    D (pure x) (pure y) = (0, k • cross x y) →
    D (pure x) (pure z) = (0, l • cross x z) → O.readout () () k l

private theorem rejected_law (D₀ : E → E → E) (h₀ : PureSuppliers D₀) :
    ¬ arena.Law (equalityRejected ℝ) := by
  intro h
  obtain ⟨k, hk, hky⟩ := pure_pair_saturation D₀ h₀ x₀ y₀
  apply h (D := D₀) h₀ (x := x₀) (y := y₀) (z := y₀)
      (k := k) (l := k) x₀_ne _ y₀_ne y₀_ne xy₀_perp xy₀_perp hk hk hky hky
  norm_num [x₀, dot, dotProduct, Fin.sum_univ_succ]

def family :
    Registration arena (type_of% (@nonunit_row_sign)) where
  actual := equalityActual ℝ
  bridge := Iff.rfl
  variation := ⟨@nonunit_row_sign, equalityRejected ℝ,
    rejected_law (crossD .plus) auditSuppliers⟩
  sensitivity := equalitySensitivity ℝ arena.Law
    (rejected_law (crossD .plus) auditSuppliers)
  dependence := signDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@nonunit_row_sign) (Realization (equalitySignature ℝ)) Type Unit where
  unitName := `D5.S3.Quantum.SpinFactor.OriginalPureRigidity.nonunit_row_sign.audit
  realizationName := `Reg.D5.S3.Quantum.SpinFactor.OriginalPureRigidity.NonunitRowSign.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (equalitySignature ℝ)
    (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinFactor.OriginalPureRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NonunitRowSign

namespace GlobalPure

abbrev arena : Arena where
  signature := equalitySignature E
  Law O := ∀ (D : E → E → E) (_ : PureSuppliers D) (_ : CommonNonunitPerpendicular),
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ ∀ x y : Vec,
      O.readout () () (D (pure x) (pure y)) (0, e • cross x y)

private theorem rejected_law (D₀ : E → E → E) (h₀ : PureSuppliers D₀)
    (hperp : CommonNonunitPerpendicular) : ¬ arena.Law (equalityRejected E) := by
  intro h
  obtain ⟨e, he, hf⟩ := h D₀ h₀ hperp
  exact hf 0 0

def family :
    Registration arena (type_of% (@global_pure_of_suppliers)) where
  actual := equalityActual E
  bridge := Iff.rfl
  variation := ⟨@global_pure_of_suppliers, equalityRejected E,
    rejected_law (crossD .plus) auditSuppliers auditPerpendicular⟩
  sensitivity := equalitySensitivity E arena.Law
    (rejected_law (crossD .plus) auditSuppliers auditPerpendicular)
  dependence := outputDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@global_pure_of_suppliers) (Realization (equalitySignature E)) Type Unit where
  unitName := `D5.S3.Quantum.SpinFactor.OriginalPureRigidity.global_pure_of_suppliers.audit
  realizationName := `Reg.D5.S3.Quantum.SpinFactor.OriginalPureRigidity.GlobalPure.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (equalitySignature E)
    (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some E
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinFactor.OriginalPureRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GlobalPure

namespace OriginalGlobalPure

abbrev arena : Arena where
  signature := equalitySignature E
  Law O := ∀ (D : E → E → E) (_ : P2 D) (_ : PB D),
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ ∀ x y : Vec,
      O.readout () () (D (pure x) (pure y)) (0, e • cross x y)

private theorem rejected_law (D₀ : E → E → E) (hP₀ : P2 D₀) (hPB₀ : PB D₀) :
    ¬ arena.Law (equalityRejected E) := by
  intro h
  obtain ⟨e, he, hf⟩ := h D₀ hP₀ hPB₀
  exact hf 0 0

def family :
    Registration arena (type_of% (@global_pure)) where
  actual := equalityActual E
  bridge := Iff.rfl
  variation := ⟨@global_pure, equalityRejected E,
    rejected_law (crossD .plus) auditModelLaws.1 auditModelLaws.2⟩
  sensitivity := equalitySensitivity E arena.Law
    (rejected_law (crossD .plus) auditModelLaws.1 auditModelLaws.2)
  dependence := outputDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@global_pure) (Realization (equalitySignature E)) Type Unit where
  unitName := `D5.S3.Quantum.SpinFactor.OriginalPureRigidity.global_pure.audit
  realizationName := `Reg.D5.S3.Quantum.SpinFactor.OriginalPureRigidity.OriginalGlobalPure.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (equalitySignature E)
    (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some E
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinFactor.OriginalPureRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end OriginalGlobalPure

end Reg.D5.S3.Quantum.SpinFactor.OriginalPureRigidity
