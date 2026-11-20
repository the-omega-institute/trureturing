import D5.S3.Combinatorics.Graph.LinearForests.AlternatingConnectorLaw
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! # Number of original cycles in the prescribed successor law -/

open LeanInformationAudit Equiv
open _root_.D5.S3.Combinatorics.Graph.LinearForests.AlternatingConnectorLaw
open _root_.D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open scoped ENNReal

namespace Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingConnectorLaw

noncomputable section
universe u

private abbrev signature : Signature where
  Params := Σ C : Type u, C → Bool
  State p := p.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => Nat.card (Compatible s p.2)) (fun e => nomatch e)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {C : Type u} [Finite C] (s d : C → Bool) (x y : C) (_hxy : y ≠ x)
    (μ : PMF (Compatible s d))
    (_hμ : ∀ σ, μ σ = (Nat.card (Compatible s d) : ℝ≥0∞)⁻¹),
    let B := {z : C // z ≠ x}
    let u := contractedSource s x y
    let v : B → Bool := fun z => d z.1
    let M := contractedInventoryCount u v
    μ.toOuterMeasure {σ | σ.1 x = y} =
      if s y = d x then (M : ℝ≥0∞) / R.readout () ⟨C, d⟩ s else 0

private abbrev Two := ULift.{u} Bool
private def left : Two.{u} := ULift.up false
private def right : Two.{u} := ULift.up true

private theorem endpoints_ne : right.{u} ≠ left.{u} := by decide

private def cycle : Compatible (fun _ : Two.{u} => false) (fun _ => false) := by
  classical
  let e := Equiv.swap left.{u} right.{u}
  refine ⟨e, ⟨left⟩, ⟨e.bijective.bijOn_univ, ?_⟩, fun _ => rfl⟩
  rintro ⟨a⟩ _ ⟨b⟩ _
  cases a <;> cases b
  · exact Perm.SameCycle.refl _ _
  · exact ⟨1, by simp [e, left, right]⟩
  · exact ⟨1, by simp [e, left, right]⟩
  · exact Perm.SameCycle.refl _ _

private theorem reducedCount :
    contractedInventoryCount (contractedSource (fun _ : Two.{u} => false) left right)
      (fun _ => false) = 1 := by
  have hs : contractedSource (fun _ : Two.{u} => false) left right = fun _ => false := by
    funext z
    simp [contractedSource]
  let B := {z : Two.{u} // z ≠ left}
  have hc : Nat.card B = 1 := by
    let e : B ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨right, endpoints_ne⟩
        left_inv := by
          rintro ⟨⟨b⟩, hb⟩
          cases b
          · exact (hb rfl).elim
          · rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans (by simp)
  have hm : inventory (fun _ : B => false) (fun _ => false) false true = 0 := by
    unfold inventory
    let : IsEmpty {z : B // false = false ∧ false = true} :=
      ⟨fun z => Bool.noConfusion z.2.2⟩
    exact Finite.card_eq_zero_iff.mpr inferInstance
  have hq : inventory (fun _ : B => false) (fun _ => false) true true = 0 := by
    unfold inventory
    let : IsEmpty {z : B // false = true ∧ false = true} :=
      ⟨fun z => Bool.noConfusion z.2.1⟩
    exact Finite.card_eq_zero_iff.mpr inferInstance
  rw [hs]
  change contractedInventoryCount (fun _ : B => false) (fun _ => false) = 1
  rw [contractedInventoryCount, hm, hq, hc]
  simp

private theorem negative : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let s : Two.{u} → Bool := fun _ => false
  let K := Compatible s s
  let : Fintype K := Fintype.ofFinite K
  let : Nonempty K := ⟨cycle⟩
  let μ := uniformPmf K
  have hweight (σ : K) : μ σ = (Nat.card K : ℝ≥0∞)⁻¹ := by
    simp only [μ, uniformPmf, PMF.ofFintype_apply, Nat.card_eq_fintype_card]
  have hm := h s s left right endpoints_ne μ hweight
  let S : Set K := {σ | σ.1 left = right}
  dsimp only at hm
  rw [ite_eq_left (show s right = s left from rfl)] at hm
  simp only [rejected, realize, Nat.cast_zero] at hm
  change μ.toOuterMeasure S = (contractedInventoryCount (contractedSource s left right)
    (fun _ => false) : ℝ≥0∞) / 0 at hm
  rw [reducedCount, Nat.cast_one, ENNReal.div_zero one_ne_zero] at hm
  have hle : μ.toOuterMeasure S ≤ μ.toOuterMeasure Set.univ :=
    μ.toOuterMeasure.mono (Set.subset_univ S)
  rw [hm, PMF.toOuterMeasure_apply, Set.indicator_univ, PMF.tsum_coe] at hle
  simp at hle

private theorem dependenceWitness :
    Nat.card (Compatible (fun _ : Two.{u} => false) (fun _ => false)) ≠
      Nat.card (Compatible (fun _ : Two.{u} => true) (fun _ => false)) := by
  let : IsEmpty (Compatible (fun _ : Two.{u} => true) (fun _ => false)) :=
    ⟨fun σ => Bool.noConfusion (σ.2.2.2 left)⟩
  have hz : Nat.card (Compatible (fun _ : Two.{u} => true) (fun _ => false)) = 0 :=
    Finite.card_eq_zero_iff.mpr inferInstance
  rw [hz]
  exact (Finite.card_pos_iff.mpr ⟨cycle⟩).ne'

def evidence : Registration arena.{u} (type_of% (@connector_mass.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@connector_mass.{u}, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, negative⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨⟨Two.{u}, fun _ => false⟩, fun _ => false, fun _ => true, dependenceWitness⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@connector_mass.{u}) (Realization signature.{u}) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingConnectorLaw.connector_mass
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingConnectorLaw.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s => Nat.card (Compatible s p.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.AlternatingConnectorLaw
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

namespace Balance

private abbrev signature : Signature where
  Params := Σ C : Type u, C → Bool
  State p := p.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ p d => inventory p.2 d false true) (fun e => nomatch e)

private def one : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [Finite A] (s d : A → Bool) (_ρ : Compatible s d),
    R.readout () ⟨A, s⟩ d = inventory s d true false

private theorem rejectsOne : ¬ arena.{u}.Law one := by
  intro h
  have hbad := h (fun _ : Two.{u} => false) (fun _ => false) cycle
  simp [one, realize, inventory, Nat.card_eq_fintype_card] at hbad

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  refine ⟨⟨Two.{u}, fun _ => false⟩, (fun _ => false), (fun _ => true), ?_⟩
  change inventory (fun _ : Two.{u} => false) (fun _ => false) false true ≠
    inventory (fun _ : Two.{u} => false) (fun _ => true) false true
  simp [inventory, Two, Nat.card_eq_fintype_card]

def evidence : Registration arena.{u} (type_of% (@balance_of_compatible.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@balance_of_compatible.{u}, one, rejectsOne⟩
  sensitivity := ⟨fun i => ⟨one, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejectsOne⟩, fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@balance_of_compatible.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingConnectorLaw.balance_of_compatible
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingConnectorLaw.Balance.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p d => inventory p.2 d false true)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.AlternatingConnectorLaw
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Balance

namespace ContractedBalance

private abbrev signature : Signature where
  Params := Σ C : Type u, Σ _ : C → Bool, Σ _ : C, C
  State p := {z : p.1 // z ≠ p.2.2.1} → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ p d =>
    inventory (contractedSource p.2.1 p.2.2.1 p.2.2.2) d false true)
    (fun e => nomatch e)

private def one : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {C : Type u} [Finite C] (s d : C → Bool) (x y : C)
    (_hxy : y ≠ x) (_hy : s y = d x) (_ρ : Compatible s d),
    R.readout () ⟨C, s, x, y⟩ (fun z => d z.1) =
      inventory (contractedSource s x y) (fun z => d z.1) true false

private theorem contractedConstant {C : Type u} (x y : C) :
    contractedSource (fun _ : C => false) x y = fun _ => false := by
  classical
  funext z
  simp [contractedSource]

private theorem rejectsOne : ¬ arena.{u}.Law one := by
  intro h
  have hbad := h (fun _ : Two.{u} => false) (fun _ => false) left right endpoints_ne rfl cycle
  simp [one, realize, contractedConstant, inventory, Nat.card_eq_fintype_card] at hbad

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  refine ⟨⟨Two.{u}, (fun _ => false), left, right⟩, (fun _ => false), (fun _ => true), ?_⟩
  let B := {z : Two.{u} // z ≠ left}
  let : Nonempty B := ⟨⟨right, endpoints_ne⟩⟩
  change inventory (contractedSource (fun _ : Two.{u} => false) left right)
      (fun _ => false) false true ≠
    inventory (contractedSource (fun _ : Two.{u} => false) left right) (fun _ => true) false true
  have hB : Nat.card B ≠ 0 := Nat.ne_of_gt Nat.card_pos
  simpa [contractedConstant, inventory] using hB.symm

def evidence : Registration arena.{u} (type_of% (@contracted_balance_at.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@contracted_balance_at.{u}, one, rejectsOne⟩
  sensitivity := ⟨fun i => ⟨one, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejectsOne⟩, fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@contracted_balance_at.{u}) (Realization signature.{u}) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingConnectorLaw.contracted_balance_at
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingConnectorLaw.ContractedBalance.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p d =>
    inventory (contractedSource p.2.1 p.2.2.1 p.2.2.2) d false true)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.AlternatingConnectorLaw
    definition := none
    coordinates := #[0, 2, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ContractedBalance

end
end Reg.D5.S3.Combinatorics.Graph.LinearForests.AlternatingConnectorLaw
