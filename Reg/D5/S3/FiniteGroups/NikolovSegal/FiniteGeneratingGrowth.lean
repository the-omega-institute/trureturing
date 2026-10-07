import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.NikolovSegal.FiniteGeneratingGrowth
import Reg.Support.DependentFamily
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open NikolovSegal.SmallTwistedProduct

namespace Reg.D5.S3.FiniteGroups.NikolovSegal.FiniteGeneratingGrowth
universe u

structure GrowthData where
  G : Type u
  groupG : Group G
  equalG : DecidableEq G
  A : Finset G
  g : G

abbrev signature : Signature where
  Params := GrowthData.{u}
  State p := p.G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ p x => by
    letI := p.groupG
    letI := p.equalG
    exact x * p.g⁻¹ ∈ p.A) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ p : GrowthData.{u}, by
    letI := p.groupG
    letI := p.equalG
    exact (∀ x ∈ p.A, x * p.g ∈ p.A) → ∀ x ∈ p.A, r.readout () p x

abbrev statement : Prop :=
  ∀ (G : Type u) [Group G] [DecidableEq G] (A : Finset G) (g : G),
    (∀ x ∈ A, x * g ∈ A) → ∀ x ∈ A, x * g⁻¹ ∈ A

theorem bridge : statement.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p
    letI := p.groupG
    letI := p.equalG
    exact h p.G p.A p.g
  · intro h G gg dg A g
    exact h ⟨G,gg,dg,A,g⟩

def singletonData : GrowthData.{u} where
  G := ULift.{u} (Multiplicative (ZMod 2))
  groupG := inferInstance
  equalG := inferInstance
  A := {1}
  g := 1

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  letI := singletonData.{u}.groupG
  letI := singletonData.{u}.equalG
  have hh := h singletonData.{u}
  have hs : ∀ x ∈ singletonData.{u}.A, x * singletonData.{u}.g ∈ singletonData.{u}.A := by
    change ∀ x ∈ ({1} : Finset (ULift.{u} (Multiplicative (ZMod 2)))), x * 1 ∈ {1}
    simp only [mul_one]
    exact fun x hx => hx
  exact hh hs 1 (Finset.mem_singleton_self 1)

def distinguishingData : GrowthData.{u} where
  G := ULift.{u} (Multiplicative (ZMod 2))
  groupG := inferInstance
  equalG := inferInstance
  A := {1}
  g := 1

theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro ⟨⟩
  letI := distinguishingData.{u}.groupG
  letI := distinguishingData.{u}.equalG
  refine ⟨distinguishingData.{u},1,⟨Multiplicative.ofAdd 1⟩,?_⟩
  change (1 * (1 : ULift.{u} (Multiplicative (ZMod 2)))⁻¹ ∈ {1}) ≠
    ((⟨Multiplicative.ofAdd 1⟩ : ULift.{u} (Multiplicative (ZMod 2))) * 1⁻¹ ∈ {1})
  simp only [inv_one,mul_one,Finset.mem_singleton]
  intro h
  have he := Eq.mp h (Finset.mem_singleton_self 1)
  have hz := congrArg (fun x : ULift.{u} (Multiplicative (ZMod 2)) => Multiplicative.toAdd x.down) (Finset.mem_singleton.mp he)
  change (1 : ZMod 2) = 0 at hz
  exact one_ne_zero hz

def registration : Registration arena.{u} statement.{u} where
  actual := actual
  bridge := bridge.{u}
  variation := ⟨bridge.{u}.mp @finite_right_stable_inv,rejected.{u},rejected_law.{u}⟩
  sensitivity := by
    constructor
    · intro ⟨⟩
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := dependence.{u}

noncomputable def registration_1.{u} :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@NikolovSegal.SmallTwistedProduct.finite_right_stable_inv.{u})
      (type_of% (realize signature.{u} (fun _ p x => by
        letI := p.groupG
        letI := p.equalG
        exact x * p.g⁻¹ ∈ p.A) (fun e => nomatch e))) Unit Unit := {
  unitName := `NikolovSegal.SmallTwistedProduct.finite_right_stable_inv ++
    Lean.Name.str Lean.Name.anonymous
      "Reg.D5.S3.FiniteGroups.NikolovSegal.FiniteGeneratingGrowth/Reg.D5.S3.FiniteGroups.NikolovSegal.FiniteGeneratingGrowth.arena/[anonymous]" ++
    `__information_unit,
  realizationName := `Reg.D5.S3.FiniteGroups.NikolovSegal.FiniteGeneratingGrowth.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨registration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ p x => by
    letI := p.groupG
    letI := p.equalG
    exact x * p.g⁻¹ ∈ p.A) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.NikolovSegal.FiniteGeneratingGrowth,
    definition := none,
    coordinates := #[0,1,2,3,4],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body"],
      stateBinder := 6,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.FiniteGroups.NikolovSegal.FiniteGeneratingGrowth
