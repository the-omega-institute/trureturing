import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.HypereclecticNonShortening
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Module.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.SpinChains.HypereclecticNonShortening
open _root_.D5.S1.Words.ParityCode.OddTopWeight (ones)

attribute [local instance] LieRing.ofAssociativeRing

namespace Reg.D5.S3.Quantum.SpinChains.HypereclecticNonShortening

abbrev weightSignature : Signature where
  Params := ℕ
  State N := Fin N → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def weightActual : Realization weightSignature :=
  realize weightSignature (fun _ _ w => weight w) (fun e => nomatch e)
def weightShifted : Realization weightSignature :=
  realize weightSignature (fun _ _ w => weight w + 1) (fun e => nomatch e)
def weightZero : Realization weightSignature :=
  realize weightSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem weightDependence : ObservationalDependence weightSignature weightActual := by
  intro i
  refine ⟨2, (fun _ => false), (fun j => j == 0), ?_⟩
  norm_num [weightActual, realize, weight, Fin.sum_univ_two]

namespace weight_eq_level

abbrev arena : Arena where
  signature := weightSignature
  Law R := ∀ {N : ℕ} (w : Fin N → Bool),
    R.readout () N w = 2 * (level w : ℚ) - (ones w : ℚ) * ((N : ℚ) - ones w)

theorem rejected_law : ¬ arena.Law weightShifted := by
  intro law
  have eq := law (N := 0) (fun i => nomatch i)
  norm_num [weightShifted, realize, weight, level, ones] at eq

def family : Registration arena (type_of% @weight_eq_level) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨@weight_eq_level, weightShifted, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨weightShifted, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := weightDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@weight_eq_level) (Realization weightSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.HypereclecticNonShortening.weight_eq_level.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.HypereclecticNonShortening.weight_eq_level.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize weightSignature weightActual.readout weightActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.HypereclecticNonShortening
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end weight_eq_level

namespace binSl2Triple

abbrev arena : Arena where
  signature := weightSignature
  Law R := ∀ (N : ℕ) (_hN : 2 ≤ N),
    IsSl2Triple (LinearMap.mulLeft ℚ (fun w : Fin N → Bool => R.readout () N w))
      (Rbin N) (Hbin N)

theorem rejected_law : ¬ arena.Law weightZero := by
  intro law
  have triple := law 2 (by omega)
  exact triple.h_ne_zero (by ext v w; simp [weightZero, realize])

def family : Registration arena (type_of% @binSl2Triple) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨@binSl2Triple, weightZero, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨weightZero, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := weightDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@binSl2Triple) (Realization weightSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.HypereclecticNonShortening.binSl2Triple.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.HypereclecticNonShortening.binSl2Triple.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize weightSignature weightActual.readout weightActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.HypereclecticNonShortening
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg", "arg", "body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end binSl2Triple

namespace lowering_kernel_zero
universe u_3 u_4

abbrev signature : Signature where
  Params := Type u_4
  State p := p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_4} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature.{u_4} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u_4}
  Law R := ∀ {K : Type u_3} [Field K] [CharZero K]
    {V : Type u_4} [AddCommGroup V] [Module K V]
    {h e f : Module.End K V} (_t : IsSl2Triple h e f) (n : ℕ),
    ∀ (v : V) (q k : ℕ), h v = (q : K) • v → k ≤ q →
      (e ^ n) v = 0 → (f ^ k) v = 0 → R.readout () V v 0

theorem rejected_law : ¬ arena.{u_3, u_4}.Law rejected := by
  intro law
  let K := ULift.{u_3} ℚ
  let V := ULift.{u_4} (ℚ × ℚ)
  let : CharZero K := ⟨fun m n eq =>
    (Nat.cast_injective : Function.Injective (fun j : ℕ => (j : ℚ)))
      (congrArg ULift.down eq)⟩
  let h : Module.End K V := {
    toFun v := ⟨(v.down.1, -v.down.2)⟩
    map_add' x y := by
      apply ULift.ext
      change (x.down.1 + y.down.1, -(x.down.2 + y.down.2)) =
        (x.down.1 + y.down.1, -x.down.2 + -y.down.2)
      simp [add_comm]
    map_smul' c x := by
      apply ULift.ext
      change (c.down * x.down.1, -(c.down * x.down.2)) =
        (c.down * x.down.1, c.down * -x.down.2)
      simp }
  let e : Module.End K V := {
    toFun v := ⟨(v.down.2, 0)⟩
    map_add' x y := by
      apply ULift.ext
      change (x.down.2 + y.down.2, (0 : ℚ)) = (x.down.2 + y.down.2, 0 + 0)
      simp
    map_smul' c x := by
      apply ULift.ext
      change (c.down * x.down.2, (0 : ℚ)) = (c.down * x.down.2, c.down * 0)
      simp }
  let f : Module.End K V := {
    toFun v := ⟨(0, v.down.1)⟩
    map_add' x y := by
      apply ULift.ext
      change ((0 : ℚ), x.down.1 + y.down.1) = (0 + 0, x.down.1 + y.down.1)
      simp
    map_smul' c x := by
      apply ULift.ext
      change ((0 : ℚ), c.down * x.down.1) = (c.down * 0, c.down * x.down.1)
      simp }
  have triple : IsSl2Triple h e f := by
    constructor
    · intro hz
      have he := congrArg (fun a : Module.End K V => (a ⟨(1, 0)⟩).down.1) hz
      norm_num [h] at he
    · apply LinearMap.ext
      intro v
      apply ULift.ext
      change (v.down.1 - 0, 0 - v.down.2) = (v.down.1, -v.down.2)
      simp
    · apply LinearMap.ext
      intro v
      apply ULift.ext
      rw [two_smul]
      change (v.down.2 - -v.down.2, (0 : ℚ) - 0) = (v.down.2 + v.down.2, 0 + 0)
      simp
    · apply LinearMap.ext
      intro v
      apply ULift.ext
      rw [two_smul]
      change ((0 : ℚ) - 0, -v.down.1 - v.down.1) = (-(0 + 0), -(v.down.1 + v.down.1))
      simp [sub_eq_add_neg]
  exact law triple 0 0 0 0 (by simp) (by omega) (by simp) (by simp)

def family : Registration arena.{u_3, u_4} (type_of% @lowering_kernel_zero.{u_3, u_4}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lowering_kernel_zero, rejected, rejected_law⟩
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
    refine ⟨ULift.{u_4} Bool, ⟨false⟩, ⟨true⟩, ?_⟩
    intro he
    have hp := congrFun he (ULift.up false)
    change (ULift.up false = ULift.up false) = (ULift.up true = ULift.up false) at hp
    have impossible : (ULift.up true : ULift.{u_4} Bool) = ULift.up false := hp ▸ rfl
    cases impossible

def registration : Contract.Registration.{_, _, _, 0, 0, 0, u_4 + 1, u_4, 0, u_4, 0, 0}
    (@lowering_kernel_zero.{u_3, u_4}) (Realization signature.{u_4}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.HypereclecticNonShortening.lowering_kernel_zero.unit
  realizationName := .str
    `Reg.D5.S3.Quantum.SpinChains.HypereclecticNonShortening.lowering_kernel_zero
    "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_3, u_4}⟩
  objectArena := .source ⟨arena.{u_3, u_4}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u_3, u_4} ⟨family.{u_3, u_4}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature.{u_4} actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.HypereclecticNonShortening
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end lowering_kernel_zero

end Reg.D5.S3.Quantum.SpinChains.HypereclecticNonShortening
