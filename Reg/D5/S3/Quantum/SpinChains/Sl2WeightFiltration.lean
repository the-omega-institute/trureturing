import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.Sl2WeightFiltration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Module.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.SpinChains.Sl2WeightFiltration

namespace Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration
universe u v

abbrev testK := ULift.{u} ℚ
abbrev testV := ULift.{v} ℚ
instance testCharZero : CharZero testK.{u} := ⟨fun _m _n eq =>
  (Nat.cast_injective : Function.Injective (fun j : ℕ => (j : ℚ)))
    (congrArg ULift.down eq)⟩
instance testFinite : FiniteDimensional testK.{u} testV.{v} := by
  let L : testK.{u} →ₗ[testK.{u}] testV.{v} :=
    { toFun x := ⟨x.down⟩, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  exact Module.Finite.of_surjective L (fun x => ⟨⟨x.down⟩, rfl⟩)

theorem zeroRelations : Sl2Relations (0 : Module.End testK.{u} testV.{v}) 0 0 := by
  constructor <;> simp

theorem zeroIntegral : IntegralWeights (0 : Module.End testK.{u} testV.{v}) := by
  refine ⟨{0}, ?_⟩
  have E : weightSpace (0 : Module.End testK.{u} testV.{v}) 0 = ⊤ := by
    ext x
    simp [weightSpace]
  simpa using E

abbrev castSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def castActual : Realization castSignature :=
  realize castSignature (fun _ _ n => (n : ℤ)) (fun e => nomatch e)
def castSuccessor : Realization castSignature :=
  realize castSignature (fun _ _ n => (n : ℤ) + 1) (fun e => nomatch e)
def castNegative : Realization castSignature :=
  realize castSignature (fun _ _ _ => -1) (fun e => nomatch e)

theorem castDependence : ObservationalDependence castSignature castActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro eq
  change (0 : ℤ) = 1 at eq
  omega

abbrev exponentSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def exponentActual : Realization exponentSignature :=
  realize exponentSignature (fun _ _ n => n) (fun e => nomatch e)
def exponentRejected : Realization exponentSignature :=
  realize exponentSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem exponentDependence : ObservationalDependence exponentSignature exponentActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro eq
  change (0 : ℕ) = 1 at eq
  omega

abbrev natSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def natEq : Realization natSignature :=
  realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e)
def natLe : Realization natSignature :=
  realize natSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def natRejected : Realization natSignature :=
  realize natSignature (fun _ _ _ _ => False) (fun e => nomatch e)

theorem natEqDependence : ObservationalDependence natSignature natEq := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro eq
  have hp := congrFun eq 0
  change ((0 : ℕ) = 0) = ((1 : ℕ) = 0) at hp
  have impossible : (1 : ℕ) = 0 := hp ▸ rfl
  omega

theorem natLeDependence : ObservationalDependence natSignature natLe := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro eq
  have hp := congrFun eq 0
  change ((0 : ℕ) ≤ 0) = ((1 : ℕ) ≤ 0) at hp
  have impossible : (1 : ℕ) ≤ 0 := hp ▸ (Nat.le_refl 0)
  omega

namespace raising_pow_weight
abbrev arena : Arena where
  signature := castSignature
  Law R := ∀ {K : Type u} {V : Type v} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] {h e f : Module.End K V}
    (_a : Sl2Relations h e f) {s : ℤ} {v : V} (_hv : v ∈ weightSpace h s) (r : ℕ),
    (e ^ r) v ∈ weightSpace h (s + 2 * R.readout () () r)

theorem rejected_law : ¬ arena.{u, v}.Law castSuccessor := by
  intro law
  have z := law (K := testK.{u}) (V := testV.{v}) zeroRelations
    (s := 0) (v := 1) (by simp [weightSpace]) 0
  have eq := Module.End.mem_eigenspace_iff.mp z
  change (0 : testV.{v}) = (2 : testK.{u}) • (1 : testV.{v}) at eq
  have hz : (1 : testV.{v}) = 0 :=
    (smul_eq_zero.mp eq.symm).resolve_left (by norm_num)
  exact one_ne_zero hz

def family : Registration arena.{u, v} (type_of% @raising_pow_weight.{u, v}) where
  actual := castActual
  bridge := Iff.rfl
  variation := ⟨@raising_pow_weight.{u, v}, castSuccessor, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨castSuccessor, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := castDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@raising_pow_weight.{u, v}) (Realization castSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.raising_pow_weight.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.raising_pow_weight.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize castSignature castActual.readout castActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.Sl2WeightFiltration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "arg", "arg",
        "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end raising_pow_weight

namespace lowering_pow_weight
abbrev arena : Arena where
  signature := castSignature
  Law R := ∀ {K : Type u} {V : Type v} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] {h e f : Module.End K V}
    (_a : Sl2Relations h e f) {s : ℤ} {v : V} (_hv : v ∈ weightSpace h s) (r : ℕ),
    (f ^ r) v ∈ weightSpace h (s - 2 * R.readout () () r)

theorem rejected_law : ¬ arena.{u, v}.Law castSuccessor := by
  intro law
  have z := law (K := testK.{u}) (V := testV.{v}) zeroRelations
    (s := 0) (v := 1) (by simp [weightSpace]) 0
  have eq := Module.End.mem_eigenspace_iff.mp z
  change (0 : testV.{v}) = (-2 : testK.{u}) • (1 : testV.{v}) at eq
  have hz : (1 : testV.{v}) = 0 :=
    (smul_eq_zero.mp eq.symm).resolve_left (by norm_num)
  exact one_ne_zero hz

def family : Registration arena.{u, v} (type_of% @lowering_pow_weight.{u, v}) where
  actual := castActual
  bridge := Iff.rfl
  variation := ⟨@lowering_pow_weight.{u, v}, castSuccessor, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨castSuccessor, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := castDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@lowering_pow_weight.{u, v}) (Realization castSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.lowering_pow_weight.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.lowering_pow_weight.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize castSignature castActual.readout castActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.Sl2WeightFiltration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "arg", "arg",
        "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end lowering_pow_weight

namespace raising_locally_nilpotent
abbrev arena : Arena where
  signature := exponentSignature
  Law R := ∀ {K : Type u} {V : Type v} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {h e f : Module.End K V}
    (_a : Sl2Relations h e f) {s : ℤ} {v : V}
    (_hv : v ∈ weightSpace h s), ∃ n : ℕ, (e ^ R.readout () () n) v = 0

theorem rejected_law : ¬ arena.{u, v}.Law exponentRejected := by
  intro law
  obtain ⟨_n, hn⟩ := law (K := testK.{u}) (V := testV.{v}) zeroRelations
    (s := 0) (v := 1) (by simp [weightSpace])
  exact one_ne_zero hn

def family : Registration arena.{u, v} (type_of% @raising_locally_nilpotent.{u, v}) where
  actual := exponentActual
  bridge := Iff.rfl
  variation := ⟨@raising_locally_nilpotent.{u, v}, exponentRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨exponentRejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := exponentDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@raising_locally_nilpotent.{u, v}) (Realization exponentSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.raising_locally_nilpotent.unit
  realizationName :=
    `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.raising_locally_nilpotent.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize exponentSignature exponentActual.readout exponentActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.Sl2WeightFiltration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "fn", "arg",
        "fn", "arg", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end raising_locally_nilpotent

namespace lowering_locally_nilpotent
abbrev arena : Arena where
  signature := exponentSignature
  Law R := ∀ {K : Type u} {V : Type v} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {h e f : Module.End K V}
    (_a : Sl2Relations h e f) {s : ℤ} {v : V}
    (_hv : v ∈ weightSpace h s), ∃ n : ℕ, (f ^ R.readout () () n) v = 0

theorem rejected_law : ¬ arena.{u, v}.Law exponentRejected := by
  intro law
  obtain ⟨_n, hn⟩ := law (K := testK.{u}) (V := testV.{v}) zeroRelations
    (s := 0) (v := 1) (by simp [weightSpace])
  exact one_ne_zero hn

def family : Registration arena.{u, v} (type_of% @lowering_locally_nilpotent.{u, v}) where
  actual := exponentActual
  bridge := Iff.rfl
  variation := ⟨@lowering_locally_nilpotent.{u, v}, exponentRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨exponentRejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := exponentDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@lowering_locally_nilpotent.{u, v}) (Realization exponentSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.lowering_locally_nilpotent.unit
  realizationName :=
    `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.lowering_locally_nilpotent.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize exponentSignature exponentActual.readout exponentActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.Sl2WeightFiltration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "fn", "arg",
        "fn", "arg", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end lowering_locally_nilpotent

namespace lowering_pow_injective
abbrev arena : Arena where
  signature := castSignature
  Law R := ∀ {K : Type u} {V : Type v} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {h e f : Module.End K V}
    (_a : Sl2Relations h e f) (s : ℤ) (r : ℕ)
    (_hr : R.readout () () r ≤ s), Function.Injective (loweringMap _a s r)

theorem rejected_law : ¬ arena.{u, v}.Law castNegative := by
  intro law
  have inj := law (K := testK.{u}) (V := testV.{v}) zeroRelations 0 1
    (by norm_num [castNegative, realize])
  have z := @inj ⟨1, by simp [weightSpace]⟩ 0 (by
    apply Subtype.ext
    simp [loweringMap])
  have eq := congrArg (fun x : weightSpace (0 : Module.End testK.{u} testV.{v}) 0 =>
    (x : testV.{v})) z
  exact one_ne_zero eq

def family : Registration arena.{u, v} (type_of% @lowering_pow_injective.{u, v}) where
  actual := castActual
  bridge := Iff.rfl
  variation := ⟨@lowering_pow_injective.{u, v}, castNegative, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨castNegative, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := castDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@lowering_pow_injective.{u, v}) (Realization castSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.lowering_pow_injective.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.lowering_pow_injective.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize castSignature castActual.readout castActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.Sl2WeightFiltration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end lowering_pow_injective

namespace raising_pow_injective
abbrev arena : Arena where
  signature := castSignature
  Law R := ∀ {K : Type u} {V : Type v} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {h e f : Module.End K V}
    (_a : Sl2Relations h e f) (t : ℤ) (r : ℕ)
    (_hr : t ≤ -R.readout () () r), Function.Injective (raisingMap _a t r)

theorem rejected_law : ¬ arena.{u, v}.Law castNegative := by
  intro law
  have inj := law (K := testK.{u}) (V := testV.{v}) zeroRelations 0 1
    (by norm_num [castNegative, realize])
  have z := @inj ⟨1, by simp [weightSpace]⟩ 0 (by
    apply Subtype.ext
    simp [raisingMap])
  have eq := congrArg (fun x : weightSpace (0 : Module.End testK.{u} testV.{v}) 0 =>
    (x : testV.{v})) z
  exact one_ne_zero eq

def family : Registration arena.{u, v} (type_of% @raising_pow_injective.{u, v}) where
  actual := castActual
  bridge := Iff.rfl
  variation := ⟨@raising_pow_injective.{u, v}, castNegative, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨castNegative, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := castDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@raising_pow_injective.{u, v}) (Realization castSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.raising_pow_injective.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.raising_pow_injective.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize castSignature castActual.readout castActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.Sl2WeightFiltration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "body", "domain", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end raising_pow_injective

namespace weight_finrank_symm
abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {K : Type u} {V : Type v} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {h e f : Module.End K V}
    (_a : Sl2Relations h e f) (s : ℤ),
    R.readout () () (Module.finrank K (weightSpace h s)) (Module.finrank K (weightSpace h (-s)))

theorem rejected_law : ¬ arena.{u, v}.Law natRejected := by
  intro law
  exact law (K := testK.{u}) (V := testV.{v}) zeroRelations 0

def family : Registration arena.{u, v} (type_of% @weight_finrank_symm.{u, v}) where
  actual := natEq
  bridge := Iff.rfl
  variation := ⟨@weight_finrank_symm.{u, v}, natRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨natRejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := natEqDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weight_finrank_symm.{u, v}) (Realization natSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.weight_finrank_symm.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.weight_finrank_symm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize natSignature natEq.readout natEq.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.Sl2WeightFiltration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end weight_finrank_symm

namespace lowering_pow_surjective
abbrev arena : Arena where
  signature := castSignature
  Law R := ∀ {K : Type u} {V : Type v} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {h e f : Module.End K V}
    (_a : Sl2Relations h e f) (t : ℤ) (r : ℕ)
    (_ht : t ≤ -(r : ℤ)) (y : V) (_hy : y ∈ weightSpace h t),
    ∃ x ∈ weightSpace h (t + 2 * R.readout () () r), (f ^ r) x = y

theorem rejected_law : ¬ arena.{u, v}.Law castSuccessor := by
  intro law
  obtain ⟨x, hx, hz⟩ := law (K := testK.{u}) (V := testV.{v}) zeroRelations
    0 0 (by norm_num) 1 (by simp [weightSpace])
  have hxzero : x = 0 := by
    have eq := Module.End.mem_eigenspace_iff.mp hx
    change (0 : testV.{v}) = (2 : testK.{u}) • x at eq
    exact (smul_eq_zero.mp eq.symm).resolve_left (by norm_num)
  have hxone : x = 1 := hz
  exact zero_ne_one (hxzero.symm.trans hxone)

def family : Registration arena.{u, v} (type_of% @lowering_pow_surjective.{u, v}) where
  actual := castActual
  bridge := Iff.rfl
  variation := ⟨@lowering_pow_surjective.{u, v}, castSuccessor, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨castSuccessor, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := castDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@lowering_pow_surjective.{u, v}) (Realization castSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.lowering_pow_surjective.unit
  realizationName :=
    `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.lowering_pow_surjective.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize castSignature castActual.readout castActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.Sl2WeightFiltration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body",
        "fn", "arg", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end lowering_pow_surjective

namespace lowering_rank_formula
abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {K : Type u} {V : Type v} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {h e f : Module.End K V}
    (_a : Sl2Relations h e f) (_hw : IntegralWeights h) (r : ℕ),
    R.readout () () (Module.finrank K (LinearMap.range (f ^ r)))
      (Module.finrank K (weightGE h (r : ℤ)) +
        Module.finrank K (weightLE h (-(r : ℤ) - 1)))

theorem rejected_law : ¬ arena.{u, v}.Law natRejected := by
  intro law
  exact law (K := testK.{u}) (V := testV.{v}) zeroRelations zeroIntegral 0

def family : Registration arena.{u, v} (type_of% @lowering_rank_formula.{u, v}) where
  actual := natEq
  bridge := Iff.rfl
  variation := ⟨@lowering_rank_formula.{u, v}, natRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨natRejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := natEqDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@lowering_rank_formula.{u, v}) (Realization natSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.lowering_rank_formula.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.lowering_rank_formula.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize natSignature natEq.readout natEq.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.Sl2WeightFiltration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end lowering_rank_formula

namespace filtration_pow_map_le
abbrev arena : Arena where
  signature := castSignature
  Law R := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (F : ℤ → Submodule K V) (T : Module.End K V)
    (_hT : ∀ s : ℤ, (F s).map T ≤ F (s - 2)) (s : ℤ) (r : ℕ),
    (F s).map (T ^ r) ≤ F (s - 2 * R.readout () () r)

theorem rejected_law : ¬ arena.{u, v}.Law castSuccessor := by
  intro law
  let F : ℤ → Submodule testK.{u} testV.{v} := fun s => if 0 ≤ s then ⊤ else ⊥
  have ht : ∀ s : ℤ, (F s).map (0 : Module.End testK.{u} testV.{v}) ≤ F (s - 2) := by
    intro s
    simp
  have z := law F 0 ht 0 0
  simp [F, castSuccessor, realize, Module.End.one_eq_id] at z

def family : Registration arena.{u, v} (type_of% @filtration_pow_map_le.{u, v}) where
  actual := castActual
  bridge := Iff.rfl
  variation := ⟨@filtration_pow_map_le.{u, v}, castSuccessor, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨castSuccessor, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := castDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@filtration_pow_map_le.{u, v}) (Realization castSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.filtration_pow_map_le.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.filtration_pow_map_le.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize castSignature castActual.readout castActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.Sl2WeightFiltration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "arg",
        "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end filtration_pow_map_le

namespace rank_comparison
abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {K : Type u} {V : Type v} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {h e f : Module.End K V}
    (_a : Sl2Relations h e f) (_hw : IntegralWeights h)
    (T : Module.End K V) (_hT : ∀ s : ℤ, (weightLE h s).map T ≤ weightLE h (s - 2))
    (r : ℕ), R.readout () () (Module.finrank K (LinearMap.range (T ^ r)))
      (Module.finrank K (LinearMap.range (f ^ r)))

theorem rejected_law : ¬ arena.{u, v}.Law natRejected := by
  intro law
  exact law (K := testK.{u}) (V := testV.{v}) zeroRelations zeroIntegral 0
    (by intro s; simp) 0

def family : Registration arena.{u, v} (type_of% @rank_comparison.{u, v}) where
  actual := natLe
  bridge := Iff.rfl
  variation := ⟨@rank_comparison.{u, v}, natRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨natRejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := natLeDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rank_comparison.{u, v}) (Realization natSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.rank_comparison.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration.rank_comparison.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize natSignature natLe.readout natLe.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.Sl2WeightFiltration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end rank_comparison

end Reg.D5.S3.Quantum.SpinChains.Sl2WeightFiltration
