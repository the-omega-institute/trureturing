import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.GroupAlgebra.ProjectiveScalarExtension
import D5.S3.FiniteGroups.GroupAlgebra.PGroupProjectiveNormRing
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod

/-! The full scalar-extension equivalence with a source-coordinate dependent-family audit. -/

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups.GroupAlgebra.ProjectiveScalarExtension
open _root_.D5.S3.FiniteGroups.GroupAlgebra.PGroupProjectiveNormRing
open scoped MonoidAlgebra BigOperators

namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.ProjectiveScalarExtension
universe uk uR uG uV
noncomputable section

structure Scope where
  k : Type uk
  R : Type uR
  G : Type uG
  V : Type uV
  [fieldK : Field k]
  [ringR : CommRing R]
  [nontrivialR : Nontrivial R]
  [algebraKR : Algebra k R]
  [groupG : Group G]
  [addV : AddCommGroup V]
  [moduleV : Module k V]

attribute [instance] Scope.fieldK Scope.ringR Scope.nontrivialR Scope.algebraKR
  Scope.groupG Scope.addV Scope.moduleV

abbrev signature : Signature where
  Params := Scope.{uk,uR,uG,uV}
  State p := Representation p.k p.G p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{uk,uR,uG,uV} :=
  realize signature (fun _ p ρ => Module.Projective p.k[p.G] ρ.asModule)
    (fun e => nomatch e)

def rejected : Realization signature.{uk,uR,uG,uV} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

/-- The full original telescope is retained; only the left projectivity readout varies. -/
abbrev arena : Arena where
  signature := signature.{uk,uR,uG,uV}
  Law r := ∀ {k : Type uk} {R : Type uR} {G : Type uG} {V : Type uV}
    [Field k] [CommRing R] [Nontrivial R]
    [Algebra k R] [Group G] [AddCommGroup V] [Module k V] (ρ : Representation k G V),
    r.readout () ⟨k, R, G, V⟩ ρ ↔
      Module.Projective R[G] (scalarExtension R ρ).asModule

private abbrev testK := ULift.{uk} (ZMod 2)
private abbrev testR := ULift.{uR} (ZMod 2)
private abbrev testG := ULift.{uG} (Multiplicative (ZMod 2))
private abbrev testV := ULift.{uV} (ZMod 2 → ZMod 2)

private instance testAlgebra : Algebra testK.{uk} testR.{uR} :=
  (ULift.ringEquiv.trans ULift.ringEquiv.symm).toRingHom.toAlgebra

private def regular : Representation testK.{uk} testG.{uG} testV.{uV} where
  toFun g := {
    toFun := fun v => ULift.up (fun i => v.down (i + g.down.toAdd))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  map_one' := by
    apply LinearMap.ext
    intro v
    apply ULift.ext
    funext i
    change v.down (i + 0) = v.down i
    rw [add_zero]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply ULift.ext
    funext i
    change v.down (i + (g.down.toAdd + h.down.toAdd)) =
      v.down ((i + g.down.toAdd) + h.down.toAdd)
    rw [add_assoc]

private abbrev trivial : Representation testK.{uk} testG.{uG} testV.{uV} := 1

private theorem group_cases (g : testG.{uG}) :
    g = ULift.up (Multiplicative.ofAdd 0) ∨
      g = ULift.up (Multiplicative.ofAdd 1) := by
  rcases g with ⟨g⟩
  have h : ∀ a : Multiplicative (ZMod 2),
      a = Multiplicative.ofAdd 0 ∨ a = Multiplicative.ofAdd 1 := by decide
  rcases h g with rfl | rfl <;> simp

private theorem sum_group (f : testG.{uG} → testV.{uV}) :
    ∑ g, f g = f (ULift.up (Multiplicative.ofAdd 0)) +
      f (ULift.up (Multiplicative.ofAdd 1)) := by
  have hu : (Finset.univ : Finset testG.{uG}) =
      {ULift.up (Multiplicative.ofAdd 0), ULift.up (Multiplicative.ofAdd 1)} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact group_cases g
  rw [hu, Finset.sum_insert (by decide), Finset.sum_singleton]

private theorem norm_regular (v : testV.{uV}) (i : ZMod 2) :
    (regular.{uk,uG,uV}.norm v).down i = v.down i + v.down (i + 1) := by
  change (∑ g : testG.{uG}, regular.{uk,uG,uV} g v).down i = _
  rw [sum_group]
  simp [regular]

private theorem test_group : IsPGroup 2 testG.{uG} := by
  apply IsPGroup.of_card_dvd_pow (n := 1)
  norm_num [Nat.card_eq_fintype_card, testG, Fintype.card_ulift]

private theorem regular_projective :
    Module.Projective testK.{uk}[testG.{uG}] regular.{uk,uG,uV}.asModule := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply (projective_iff_projective_invariants_and_norm_surjective
    2 1 (by decide) (by decide) test_group regular).mpr
  refine ⟨inferInstance, ?_⟩
  intro w
  have hw := (Representation.mem_invariants regular.{uk,uG,uV} (w : testV.{uV})).mp w.property
    (ULift.up (Multiplicative.ofAdd 1))
  have hw01 : (w : testV.{uV}).down 1 = (w : testV.{uV}).down 0 := by
    exact congrArg (fun v : testV.{uV} => v.down 0) hw
  refine ⟨ULift.up (fun i => if i = 0 then (w : testV.{uV}).down 0 else 0), ?_⟩
  apply ULift.ext
  funext i
  rw [norm_regular]
  have h : ∀ (a : ZMod 2 → ZMod 2), a 1 = a 0 → ∀ j : ZMod 2,
      (if j = 0 then a 0 else 0) + (if j + 1 = 0 then a 0 else 0) = a j := by
    decide
  exact h (w : testV.{uV}).down hw01 i

private theorem trivial_not_projective :
    ¬ Module.Projective testK.{uk}[testG.{uG}] trivial.{uk,uG,uV}.asModule := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  intro h
  have hn := ((projective_iff_projective_invariants_and_norm_surjective
    2 1 (by decide) (by decide) test_group trivial).mp h).2
  let w : trivial.{uk,uG,uV}.invariants :=
    ⟨ULift.up (fun _ => 1), by
      apply (Representation.mem_invariants trivial _).mpr
      intro g
      rfl⟩
  obtain ⟨x, hx⟩ := hn w
  have hz : trivial.{uk,uG,uV}.norm x = 0 := by
    change (∑ g : testG.{uG}, trivial.{uk,uG,uV} g x) = 0
    rw [sum_group]
    apply ULift.ext
    funext i
    change x.down i + x.down i = 0
    exact CharTwo.add_self_eq_zero _
  have he := congrArg (fun v : testV.{uV} => v.down 0) (hz.symm.trans hx)
  exact (zero_ne_one : (0 : ZMod 2) ≠ 1) he

private theorem rejected_law : ¬ arena.{uk,uR,uG,uV}.Law rejected := by
  intro h
  have hR := (projective_iff_scalarExtension
    (R := testR.{uR}) regular.{uk,uG,uV}).mp regular_projective
  exact (h (R := testR.{uR}) regular).mpr hR

private theorem dependence : ObservationalDependence signature.{uk,uR,uG,uV} actual := by
  intro i
  refine ⟨⟨testK.{uk}, testR.{uR}, testG.{uG}, testV.{uV}⟩,
    regular, trivial, ?_⟩
  intro he
  exact trivial_not_projective (Eq.mp he regular_projective)

def family : Registration arena.{uk,uR,uG,uV}
    (type_of% (@projective_iff_scalarExtension.{uk,uR,uG,uV})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@projective_iff_scalarExtension.{uk,uR,uG,uV}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

/-- Native source binding remains subject to the compiler's source-coordinate audit. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@projective_iff_scalarExtension.{uk,uR,uG,uV})
    (Realization signature.{uk,uR,uG,uV}) Unit Unit where
  unitName :=
    `D5.S3.FiniteGroups.GroupAlgebra.ProjectiveScalarExtension.projective_iff_scalarExtension.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.ProjectiveScalarExtension.family
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.ProjectiveScalarExtension
    definition := none
    coordinates := #[0,1,2,3,4,5,6,7,8,9,10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.FiniteGroups.GroupAlgebra.ProjectiveScalarExtension
