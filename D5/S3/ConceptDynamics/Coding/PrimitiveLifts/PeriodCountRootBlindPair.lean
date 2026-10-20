/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PeriodCountRootBlindPair
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/PeriodCountRootBlindPair
   mirror-E: none(waiver:symbolic-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PeriodCountRootBlindPair.claim; result=D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PeriodCountRootBlindPair.result; claim=D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PeriodCountRootBlindPair.claim
   digest: Two actual one-loop systems over the same group have equal periodic counts and different equivariant square-root existence. -/

import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.PrimitiveLiftRootCriterion
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.PeriodCountRootBlindPair

open EssentialWordRealization FiniteWindowTableCriterion FixedBlockRigidity
open OrderedGroupChainHistories PrimitiveLiftRootCriterion TwistedPeriodicHistories
open CountedGroupOverlap (GroupMat Path Edge)

universe u

/-- The actual numbered graph has one vertex and exactly one edge, labelled g. -/
def loop {H : Type u} [Group H] (g : H) : GroupMat H 1 1 :=
  fun _ _ => MonoidAlgebra.single g 1

section Loop
variable {H : Type u} [Group H] (g : H)
local instance : DecidableEq H := Classical.decEq H

private def loopEdge : Edge (loop g) :=
  ⟨0,0,g,⟨0,by simp [loop,MonoidAlgebra.coeff_single]⟩⟩

private theorem loop_edge_unique (e : Edge (loop g)) : e = loopEdge g := by
  have hl : e.label = g := by
    by_contra h
    have hn := e.number.isLt
    simp [loop,MonoidAlgebra.coeff_single,Ne.symm h] at hn
  rcases e with ⟨i,j,l,k⟩
  dsimp only at hl
  subst l
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i; subst j
  congr 1
  apply Fin.ext
  have hk : k.val < 1 := by simpa [loop,MonoidAlgebra.coeff_single] using k.isLt
  change k.val = 0
  omega

private def loopPath : Path (loop g) := ⟨fun _ => loopEdge g, fun _ => rfl⟩

private theorem loop_path_unique (p : Path (loop g)) : p = loopPath g := by
  apply Subtype.ext
  funext i
  exact loop_edge_unique g (p.val i)

private theorem loop_minimal :
    Function.minimalPeriod (CountedGroupOverlap.shift (loop g)) (loopPath g) = 1 :=
  Function.minimalPeriod_eq_one_iff_isFixedPt.2 (loop_path_unique g _)

private def allLifts : LiftOrbit (loop g) (loopPath g) 1 ≃ History (expandedGraph (loop g)) where
  toFun := Subtype.val
  invFun x := ⟨x,⟨0,loop_path_unique g (forgetHistory x)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def loopAtlas : ReturnAtlas H (History (expandedGraph (loop g))) :=
  let A := actualAtlas (loop g) (loopPath g) 1 (by decide) (loop_minimal g)
  let e := allLifts g
  { period := 1
    positive := by decide
    holonomy := A.holonomy
    point := fun t z => e (A.point t z)
    covers := fun x => by
      obtain ⟨t,z,h⟩ := A.covers (e.symm x)
      exact ⟨t,z,by rw [h,e.apply_symm_apply]⟩
    relation := fun t s z w => by
      rw [e.injective.eq_iff]
      exact A.relation t s z w
    time := fun x => e (A.time (e.symm x))
    time_point := fun t z => by
      simp only [e.symm_apply_apply]
      exact congrArg e (A.time_point t z)
    deck := fun a x => e (A.deck a (e.symm x))
    deck_point := fun a t z => by
      simp only [e.symm_apply_apply]
      exact congrArg e (A.deck_point a t z) }

private theorem loop_holonomy : (loopAtlas g).holonomy = g := by
  simp [loopAtlas,actualAtlas,orbitHolonomy,totalLabel,prefixLabel,historyWindow,loopPath,loopEdge]

/-- Root existence is tested on all actual bilateral histories. -/
def HasEquivariantRoot (k : ℕ) : Prop :=
  ∃ f : History (expandedGraph (loop g)) → History (expandedGraph (loop g)),
    (∀ a x, f (groupHistory (loop g) a x) = groupHistory (loop g) a (f x)) ∧
    f^[k] = shift (expandedGraph (loop g))

private theorem loop_root_iff (k : ℕ) : HasEquivariantRoot g k ↔ ∃ b : H, b^k = g := by
  have crit := (loopAtlas g).root_criterion k
  have ht : (loopAtlas g).time = shift (expandedGraph (loop g)) := rfl
  have hl : (loopAtlas g).deck = groupHistory (loop g) := rfl
  rw [ht] at crit
  change HasEquivariantRoot g k ↔ _ at crit
  rw [loop_holonomy] at crit
  change HasEquivariantRoot g k ↔ ∃ s : Fin 1, ∃ m : ℤ, ∃ b : H,
    Commute b g ∧ (k:ℤ)*(s.val:ℤ) = 1+(1:ℤ)*m ∧ b^k*g^m = 1 at crit
  simp only [one_mul] at crit
  rw [crit]
  constructor
  · rintro ⟨s,m,b,hb,hm,hz⟩
    have hs : s.val = 0 := Fin.val_eq_zero s
    have hm' : m = -1 := by simp only [hs,Int.natCast_zero,mul_zero,Int.natCast_one,one_mul] at hm; omega
    refine ⟨b, ?_⟩
    rw [hm',zpow_neg_one] at hz
    exact (mul_inv_eq_one.mp hz)
  · rintro ⟨b,hb⟩
    refine ⟨0,-1,b,?_,by simp,?_⟩
    · rw [← hb]
      exact Commute.self_pow b k
    · simp [hb]

private theorem loop_periodic (j : ℕ) (x : History (expandedGraph (loop g))) :
    Function.IsPeriodicPt (shift (expandedGraph (loop g))) j x ↔ g^j = 1 := by
  let A := loopAtlas g
  obtain ⟨t,z,rfl⟩ := A.covers x
  have ht : A.time = shift (expandedGraph (loop g)) := rfl
  have iter : ∀ j : ℕ, A.time^[j] (A.point t z) = A.point (t+(j:ℤ)) z := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply',ih,A.time_point]
      congr 1
      push_cast
      ring
  change (shift (expandedGraph (loop g)))^[j] (A.point t z) = A.point t z ↔ _
  rw [← ht,iter,A.relation]
  have hg : A.holonomy = g := loop_holonomy g
  have hd : A.period = 1 := rfl
  rw [hg,hd]
  constructor
  · rintro ⟨m,hm,hz⟩
    have hm' : m = (j:ℤ) := by omega
    rw [hm',zpow_natCast] at hz
    exact mul_left_cancel (show z*g^j = z*1 by simpa using hz)
  · intro h
    exact ⟨j,by simp,by simp [h]⟩

private theorem loop_minimal_period (x : History (expandedGraph (loop g))) :
    Function.minimalPeriod (shift (expandedGraph (loop g))) x = orderOf g := by
  change Function.minimalPeriod (shift (expandedGraph (loop g))) x =
    Function.minimalPeriod (g*·) (1:H)
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro j
  exact (loop_periodic g j x).trans (isPeriodicPt_mul_iff_pow_eq_one g).symm

private theorem loop_pow (j : ℕ) (i l : Fin 1) :
    ((loop g)^j) i l = MonoidAlgebra.single (g^j) 1 := by
  induction j generalizing i l with
  | zero => simp [Matrix.one_apply,Subsingleton.elim i l,MonoidAlgebra.one_def]
  | succ j ih =>
    rw [pow_succ,Matrix.mul_apply]
    simp [ih,loop,MonoidAlgebra.single_mul_single,pow_succ]

variable [Fintype H]

private theorem loop_count (j : ℕ) (hj : 0 < j) :
    Nat.card (TwistedPeriod (loop g) 1 j) =
      if g^j = 1 then Fintype.card H else 0 := by
  letI := twistedPeriodFintype (loop g) 1 hj
  rw [Nat.card_eq_fintype_card,twistedPeriod_card (loop g) 1 hj]
  by_cases h : g^j = 1 <;> simp [loop_pow,MonoidAlgebra.coeff_single,Finsupp.single_apply,h,eq_comm]

end Loop

/-- Both labels live in the same C4 times C2 deck group. -/
abbrev DeckGroup := Multiplicative (ZMod 4 × ZMod 2)

private def firstLabel : DeckGroup := Multiplicative.ofAdd (2,0)
private def secondLabel : DeckGroup := Multiplicative.ofAdd (0,1)

/-- The claim whose failure distinguishes group arithmetic from all ordinary periods. -/
def claim : Prop :=
  ∀ g h : DeckGroup,
    (∀ x : History (expandedGraph (loop g)),
      Function.minimalPeriod (shift (expandedGraph (loop g))) x = 2) →
    (∀ x : History (expandedGraph (loop h)),
      Function.minimalPeriod (shift (expandedGraph (loop h))) x = 2) →
    (∀ j : ℕ, 0 < j →
      Nat.card (TwistedPeriod (loop g) 1 j) = Nat.card (TwistedPeriod (loop h) 1 j)) →
    (HasEquivariantRoot g 2 ↔ HasEquivariantRoot h 2)

private theorem period_data (j : ℕ) (hj : 0 < j) :
    Nat.card (TwistedPeriod (loop firstLabel) 1 j) =
      Nat.card (TwistedPeriod (loop secondLabel) 1 j) := by
  have ho₁ : orderOf firstLabel = 2 := orderOf_eq_prime (p := 2) (by decide) (by decide)
  have ho₂ : orderOf secondLabel = 2 := orderOf_eq_prime (p := 2) (by decide) (by decide)
  have hc : Fintype.card DeckGroup = 8 := by decide
  have cfirst := loop_count firstLabel j hj
  have csecond := loop_count secondLabel j hj
  simp only [hc,← orderOf_dvd_iff_pow_eq_one,ho₁] at cfirst
  simp only [hc,← orderOf_dvd_iff_pow_eq_one,ho₂] at csecond
  exact cfirst.trans csecond.symm

/-- All positive ordinary periodic counts agree, while actual equivariant square roots differ. -/
theorem result : ¬ claim := by
  intro h
  have yes : HasEquivariantRoot firstLabel 2 :=
    (loop_root_iff firstLabel 2).2 ⟨Multiplicative.ofAdd (1,0),by decide⟩
  have no : ¬ HasEquivariantRoot secondLabel 2 := by
    rw [loop_root_iff]
    decide
  have hfirst : ∀ x : History (expandedGraph (loop firstLabel)),
      Function.minimalPeriod (shift (expandedGraph (loop firstLabel))) x = 2 := by
    intro x
    rw [loop_minimal_period]
    exact orderOf_eq_prime (p := 2) (by decide) (by decide)
  have hsecond : ∀ x : History (expandedGraph (loop secondLabel)),
      Function.minimalPeriod (shift (expandedGraph (loop secondLabel))) x = 2 := by
    intro x
    rw [loop_minimal_period]
    exact orderOf_eq_prime (p := 2) (by decide) (by decide)
  exact no ((h firstLabel secondLabel hfirst hsecond period_data).1 yes)

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.PeriodCountRootBlindPair
