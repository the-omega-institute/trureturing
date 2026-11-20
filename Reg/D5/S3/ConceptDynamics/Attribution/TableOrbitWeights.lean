import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.TableOrbitWeights
import Reg.Support.DependentFamily
import Reg.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers

/-! The orbit constraints and optima read the prescribed event masses and kernel entries. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.TableOrbitWeights

open _root_.D5.S3.ConceptDynamics.Attribution.TableOrbitWeights
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

universe g t i x y s

noncomputable section

abbrev signature : Signature.{i + 1, i, 0, i, 0} where
  Params := Type i
  State I := I → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ I := I → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{i} :=
  realize signature (fun _ _ m => m) (fun e => nomatch e)

def rejected : Realization signature.{i} :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

local instance {G : Type g} {T : Type t} [Group G] [MulAction G T] [Fintype T] :
    Fintype (MulAction.orbitRel.Quotient G T) := Fintype.ofFinite _

abbrev arena : Arena where
  signature := signature.{i}
  Law R :=
    ∀ {G : Type g} {T : Type t} {I : Type i} [Group G] [MulAction G T] [Fintype T]
      (event : I → Finset T) (mass : I → ℝ),
      (∃ p : T → ℝ, (∀ t, 0 ≤ p t) ∧ (∑ t, p t) = 1 ∧
        (∀ (g : G) t, p (g • t) = p t) ∧ ∀ j, (∑ t ∈ event j, p t) = mass j) ↔
      (∃ z : MulAction.orbitRel.Quotient G T → ℝ, (∀ o, 0 ≤ z o) ∧ (∑ o, z o) = 1 ∧
        ∀ j, (∑ o, z o * orbitFrequency (event j) o) = R.readout () I mass j)

private theorem rejected_law : ¬ arena.{g,t,i}.Law rejected := by
  classical
  intro altered
  let G := PUnit.{g+1}
  let T := PUnit.{t+1}
  let I := PUnit.{i+1}
  let event (_ : I) : Finset T := univ
  let mass (_ : I) : ℝ := 1
  obtain ⟨z, _, total, prescribed⟩ := (altered (G := G) event mass).mp
    ⟨fun _ => 1, fun _ => zero_le_one, by simp, fun _ _ => rfl, fun _ => by simp [event, mass]⟩
  have full (o : MulAction.orbitRel.Quotient G T) :
      orbitFrequency (G := G) (univ : Finset T) o = 1 := by
    unfold orbitFrequency
    simp
    exact Subsingleton.elim _ _
  have zero := prescribed (PUnit.unit : I)
  change (∑ o, z o * orbitFrequency (G := G) (univ : Finset T) o) = 0 at zero
  simp only [full, mul_one, total] at zero
  exact one_ne_zero zero

def family : Registration arena.{g,t,i} (type_of% (@invariant_event_masses_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@invariant_event_masses_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨PUnit.{i+1}, fun _ => 0, fun _ => 1, ?_⟩
    intro equal
    exact zero_ne_one (congrFun equal PUnit.unit)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@invariant_event_masses_iff) (Realization signature.{i}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.TableOrbitWeights.eventMasses
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.TableOrbitWeights.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{g,t,i}⟩
  objectArena := .source ⟨arena.{g,t,i}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{g,t,i} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.TableOrbitWeights
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "arg", "arg", "body", "arg", "fn"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace EventMaximum

abbrev arena : Arena where
  signature := signature.{i}
  Law R :=
    ∀ {G : Type g} {T : Type t} {I : Type i} [Group G] [MulAction G T] [Fintype T]
      (event : I → Finset T) (mass : I → ℝ) (target : Finset T)
      (_feasible : ∃ p : T → ℝ, (∀ t, 0 ≤ p t) ∧ (∑ t, p t) = 1 ∧
        (∀ (g : G) t, p (g • t) = p t) ∧ ∀ j, (∑ t ∈ event j, p t) = mass j),
      ∃ z : MulAction.orbitRel.Quotient G T → ℝ,
        (∀ o, 0 ≤ z o) ∧ (∑ o, z o) = 1 ∧
        (∀ i, (∑ o, z o * orbitFrequency (event i) o) = R.readout () I mass i) ∧
        (∀ w : MulAction.orbitRel.Quotient G T → ℝ, (∀ o, 0 ≤ w o) → (∑ o, w o) = 1 →
          (∀ i, (∑ o, w o * orbitFrequency (event i) o) = mass i) →
          (∑ o, w o * orbitFrequency target o) ≤ ∑ o, z o * orbitFrequency target o) ∧
        (∀ a : ℝ,
          (∃ p : T → ℝ, (∀ t, 0 ≤ p t) ∧ (∑ t, p t) = 1 ∧
            (∀ (g : G) t, p (g • t) = p t) ∧ (∀ i, (∑ t ∈ event i, p t) = mass i) ∧
            (∑ t ∈ target, p t) = a) ↔
          (∃ w : MulAction.orbitRel.Quotient G T → ℝ, (∀ o, 0 ≤ w o) ∧ (∑ o, w o) = 1 ∧
            (∀ i, (∑ o, w o * orbitFrequency (event i) o) = mass i) ∧
            (∑ o, w o * orbitFrequency target o) = a))

private theorem rejected_law : ¬ arena.{g,t,i}.Law rejected := by
  classical
  intro altered
  let G := PUnit.{g+1}
  let T := PUnit.{t+1}
  let I := PUnit.{i+1}
  let event (_ : I) : Finset T := univ
  let mass (_ : I) : ℝ := 1
  obtain ⟨z, _, total, prescribed, _, _⟩ := altered (G := G) event mass univ
    ⟨fun _ => 1, fun _ => zero_le_one, by simp, fun _ _ => rfl, fun _ => by simp [event, mass]⟩
  have full (o : MulAction.orbitRel.Quotient G T) :
      orbitFrequency (G := G) (univ : Finset T) o = 1 := by
    unfold orbitFrequency
    simp
    exact Subsingleton.elim _ _
  have zero := prescribed (PUnit.unit : I)
  change (∑ o, z o * orbitFrequency (G := G) (univ : Finset T) o) = 0 at zero
  simp only [full, mul_one, total] at zero
  exact one_ne_zero zero

def family : Registration arena.{g,t,i} (type_of% (@maximal_invariant_event_mass)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@maximal_invariant_event_mass, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨PUnit.{i+1}, fun _ => 0, fun _ => 1, ?_⟩
    intro equal
    exact zero_ne_one (congrFun equal PUnit.unit)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@maximal_invariant_event_mass) (Realization signature.{i}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.TableOrbitWeights.EventMaximum.registration
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.TableOrbitWeights.EventMaximum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{g,t,i}⟩
  objectArena := .source ⟨arena.{g,t,i}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{g,t,i} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.TableOrbitWeights
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "body", "arg", "arg", "fn", "arg", "body", "arg", "fn"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EventMaximum

namespace TableMaximum

open _root_.D5.S3.ConceptDynamics.Attribution
open FixedKernelMass (seedFixedMass)
open Reg.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers renaming
  signature → kernelSignature, actual → kernelActual, rejected → kernelRejected

attribute [local instance 2000] NormalSubgroupFixedMass.tableSMul NormalSubgroupFixedMass.tableAction

local instance (priority := 2100) subgroupTableAction {G X Y : Type*} [Group G]
    [MulAction G X] [MulAction G Y] (H : Subgroup G) : MulAction H (X → Y) :=
  MulAction.compHom (X → Y) H.subtype

set_option linter.checkUnivs false in
open Classical in
abbrev arena : Arena where
  signature := kernelSignature.{x,y}
  Law R :=
    ∀ {G : Type g} [Group G] {X : Type x} {Y : Type y} [Fintype (X → Y)]
      [MulAction G X] [MulAction G Y] [Fintype X] [Fintype Y] [Nonempty X] [DecidableEq Y]
      (H : Subgroup G) (P : X → Y → ℝ) (_nn : ∀ x y, 0 ≤ P x y)
      (_normalized : ∀ x, ∑ y, P x y = 1)
      (_cov : ∀ (g : G) x y, P (g • x) (g • y) = P x y),
      let cell (xy : X × Y) := univ.filter (fun t : X → Y => t xy.1 = xy.2)
      let fixed := univ.filter (fun t : X → Y => ∀ h : H, h • t = t)
      ∃ z : MulAction.orbitRel.Quotient G (X → Y) → ℝ,
        (∀ o, 0 ≤ z o) ∧ (∑ o, z o) = 1 ∧
        (∀ x y, (∑ o, z o * orbitFrequency (cell (x, y)) o) = R.readout () ⟨X, Y⟩ P x y) ∧
        (∀ w : MulAction.orbitRel.Quotient G (X → Y) → ℝ,
          (∀ o, 0 ≤ w o) → (∑ o, w o) = 1 →
          (∀ x y, (∑ o, w o * orbitFrequency (cell (x, y)) o) = P x y) →
          (∑ o, w o * orbitFrequency fixed o) ≤ ∑ o, z o * orbitFrequency fixed o) ∧
        (∀ (U : Type s) [Fintype U] [MulAction G U]
          (w : U → ℝ) (f : X → U → Y),
          (∀ s, 0 ≤ w s) → (∑ s, w s = 1) → (∀ (g : G) s, w (g • s) = w s) →
          (∀ x y, (∑ s, if f x s = y then w s else 0) = P x y) →
          (∀ (g : G) x s, f (g • x) (g • s) = g • f x s) →
          seedFixedMass (G := H) w ≤ ∑ o, z o * orbitFrequency fixed o) ∧
        ∃ (U : Type (max x y)) (_ : Fintype U) (_ : MulAction G U)
          (q : U → ℝ) (f : X → U → Y),
          (∀ t, 0 < q t) ∧ (∑ t, q t) = 1 ∧ (∀ (g : G) t, q (g • t) = q t) ∧
          (∀ x y, (∑ t, if f x t = y then q t else 0) = P x y) ∧
          (∀ (g : G) x t, f (g • x) (g • t) = g • f x t) ∧
          seedFixedMass (G := H) q = ∑ o, z o * orbitFrequency fixed o

private theorem rejected_law : ¬ arena.{g,x,y,s}.Law kernelRejected := by
  classical
  intro altered
  let G := PUnit.{g+1}
  let X := PUnit.{x+1}
  let Y := PUnit.{y+1}
  let P : X → Y → ℝ := fun _ _ => 1
  obtain ⟨z, _, total, prescribed, _, _, _⟩ := altered (G := G) (⊤ : Subgroup G) P
    (by simp [P]) (by simp [P]) (by simp [P])
  have full (o : MulAction.orbitRel.Quotient G (X → Y)) :
      orbitFrequency (G := G) (univ.filter (fun t : X → Y => t PUnit.unit = PUnit.unit)) o = 1 := by
    have event : univ.filter (fun t : X → Y => t PUnit.unit = PUnit.unit) = univ := by
      simp only [filter_eq_self, mem_univ, forall_const]
      exact fun _ => Subsingleton.elim _ _
    rw [event]
    unfold orbitFrequency
    simp
    exact Subsingleton.elim _ _
  have zero := prescribed (PUnit.unit : X) (PUnit.unit : Y)
  change (∑ o, z o * orbitFrequency (G := G)
    (univ.filter (fun t : X → Y => t PUnit.unit = PUnit.unit)) o) = 0 at zero
  simp only [full, mul_one, total] at zero
  exact one_ne_zero zero

def family : Registration arena.{g,x,y,s} (type_of% (@maximal_table_fixed_mass)) where
  actual := kernelActual
  bridge := Iff.rfl
  variation := ⟨@maximal_table_fixed_mass, kernelRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨kernelRejected, ?_, rfl, rejected_law⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨⟨PUnit.{x+1}, PUnit.{y+1}⟩, fun _ _ => 0, fun _ _ => 1, ?_⟩
    intro equal
    exact zero_ne_one (congrFun (congrFun equal PUnit.unit) PUnit.unit)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@maximal_table_fixed_mass) (Realization kernelSignature.{x,y}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.TableOrbitWeights.TableMaximum.registration
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.TableOrbitWeights.TableMaximum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{g,x,y,s}⟩
  objectArena := .source ⟨arena.{g,x,y,s}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{g,x,y,s} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize kernelSignature (fun _ _ m => m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.TableOrbitWeights
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg",
        "fn", "arg", "body", "body", "arg", "fn", "fn"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TableMaximum

end
end Reg.D5.S3.ConceptDynamics.Attribution.TableOrbitWeights
