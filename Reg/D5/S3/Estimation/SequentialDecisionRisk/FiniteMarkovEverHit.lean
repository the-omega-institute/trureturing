import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.SequentialDecisionRisk.FiniteMarkovEverHit
import Reg.Support.DependentFamily

open scoped BigOperators Topology Classical
open Filter LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.SequentialDecisionRisk.FiniteMarkovEverHit

noncomputable section
namespace Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteMarkovEverHit
universe u
structure Parameters where
  S : Type u
  finite : Fintype S
  decEq : DecidableEq S
  W : S → S → ℝ
  d0 : S
  d1 : S

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.S
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => @everHit p.S p.finite p.decEq p.W p.d1 x)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {S : Type u} [Fintype S] [DecidableEq S]
    (W : S → S → ℝ) (d0 d1 : S) (hne : d0 ≠ d1)
    (hW0 : ∀ x y, 0 ≤ W x y) (hW1 : ∀ x, ∑ y, W x y = 1)
    (hfix0 : ∀ y, W d0 y = if y = d0 then 1 else 0)
    (hfix1 : ∀ y, W d1 y = if y = d1 then 1 else 0),
    let p : Parameters := ⟨S, inferInstance, inferInstance, W, d0, d1⟩
    (∀ x, 0 ≤ R.readout () p x ∧ R.readout () p x ≤ 1) ∧
    R.readout () p d0 = 0 ∧ R.readout () p d1 = 1 ∧
    (∀ x, Tendsto (fun n => hitWithin W d1 n x) atTop (𝓝 (R.readout () p x))) ∧
    (∀ x, ∑ y, W x y * R.readout () p y = R.readout () p x) ∧
    (∀ n x, hitWithin W d1 n x =
      ∑ p, futureMass W n x p * (if visits d1 n x p then (1 : ℝ) else 0)) ∧
    (∀ g : S → ℝ, (∀ x, 0 ≤ g x) → 1 ≤ g d1 →
      (∀ x, ∑ y, W x y * g y ≤ g x) → ∀ x, R.readout () p x ≤ g x)

def family : Registration arena.{u} (type_of% (@ever_hit_harmonic.{u})) := by
  have hbad : ¬ arena.Law rejected.{u} := by
    intro h
    let a : ULift.{u} Bool := ⟨false⟩
    let b : ULift.{u} Bool := ⟨true⟩
    have hh := h (fun x y : ULift.{u} Bool => if y = x then (1 : ℝ) else 0) a b
      (by decide)
      (by intro x y; split_ifs <;> norm_num)
      (by intro x; simp) (fun _ => rfl) (fun _ => rfl)
    have hb := hh.2.2.1
    norm_num [rejected, realize] at hb
  exact {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@ever_hit_harmonic, rejected, hbad⟩
    sensitivity := by
      constructor
      · intro i
        refine ⟨rejected, ?_, rfl, hbad⟩
        intro j h
        exact False.elim (h (Subsingleton.elim (α := Unit) j i))
      · intro e; exact nomatch e
    dependence := by
      intro _
      let a : ULift.{u} Bool := ⟨false⟩
      let b : ULift.{u} Bool := ⟨true⟩
      let W (x y : ULift.{u} Bool) : ℝ := if y = x then 1 else 0
      let p : Parameters.{u} := ⟨ULift.{u} Bool, inferInstance, inferInstance, W, a, b⟩
      refine ⟨p, a, b, ?_⟩
      change everHit W b a ≠ everHit W b b
      have ht := ever_hit_harmonic W a b (by decide)
        (by intro x y; dsimp [W]; split_ifs <;> norm_num)
        (by intro x; simp [W]) (fun _ => rfl) (fun _ => rfl)
      rw [ht.2.1, ht.2.2.1]
      exact zero_ne_one }

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ever_hit_harmonic.{u})
    (type_of% (realize signature.{u}
      (fun _ p x => @everHit p.S p.finite p.decEq p.W p.d1 x) (fun e => nomatch e)))
    Unit Unit where
  unitName := `D5.S3.Estimation.SequentialDecisionRisk.FiniteMarkovEverHit.ever_hit_harmonic.__information_unit
  realizationName := `Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteMarkovEverHit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p x => @everHit p.S p.finite p.decEq p.W p.d1 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Estimation.SequentialDecisionRisk.FiniteMarkovEverHit
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 11
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteMarkovEverHit
end
#print axioms Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteMarkovEverHit.family
#print axioms Reg.D5.S3.Estimation.SequentialDecisionRisk.FiniteMarkovEverHit.registration
