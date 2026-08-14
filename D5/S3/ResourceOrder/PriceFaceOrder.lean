/- GID: D5/S3/ResourceOrder/PriceFaceOrder
   generality: G
   mirror-B: D5/B/S3/ResourceOrder/PriceFaceOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A preorder that is not antisymmetric, with a two-direction price face. -/

import D5.S3.Resource.PriceFace
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
Library-search and proof boundary (2026-08-14):
* Mathlib supplies `Filter.EventuallyLE.refl` and `Filter.EventuallyLE.trans`; no
  `EventuallyLE`-specific `Preorder` constructor was needed. The searched
  `minimal_iff` does exist later in pinned `Mathlib.Order.Minimal`, but is not
  needed here; `Minimal` is used directly through its `prop` projection.
* A repository search found no theorem about `priceFace`, `CostProfile`,
  `PhysicalCosts`, or `TaxReceipt` outside their frozen definitions.
* This module proves the requested two-receipt concrete face, but does not claim
  that every nonempty `priceFace` has two independent directions, nor that the
  eventual preorder is a partial order.
-/

namespace D5.S3.ResourceOrder.PriceFaceOrder

open D5.S3.Resource.PriceFace

private def choiceAnchor : True :=
  Classical.choice (show Nonempty True from ⟨True.intro⟩)

instance costProfilePreorder (Cost : Type*) [Preorder Cost] : Preorder (CostProfile Cost) where
  le_refl profile := Filter.EventuallyLE.refl Filter.atTop profile
  le_trans left middle right hleft hright := Filter.EventuallyLE.trans hleft hright

instance physicalCostsPreorder (Cost : Type*) [Preorder Cost] :
    Preorder (PhysicalCosts Cost) where
  le_refl costs := ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  le_trans left middle right hleft hright :=
    ⟨le_trans hleft.1 hright.1, le_trans hleft.2.1 hright.2.1,
      le_trans hleft.2.2.1 hright.2.2.1, le_trans hleft.2.2.2 hright.2.2.2⟩

instance taxReceiptPreorder
    (AlgorithmCost RateCost PhysicalCost HeatCost : Type*)
    [Preorder AlgorithmCost] [Preorder RateCost] [Preorder PhysicalCost] [Preorder HeatCost] :
    Preorder (TaxReceipt AlgorithmCost RateCost PhysicalCost HeatCost) where
  le_refl receipt := ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  le_trans left middle right hleft hright :=
    ⟨le_trans hleft.1 hright.1, le_trans hleft.2.1 hright.2.1,
      le_trans hleft.2.2.1 hright.2.2.1,
      ⟨le_trans hleft.2.2.2.1.1 hright.2.2.2.1.1,
        le_trans hleft.2.2.2.1.2.1 hright.2.2.2.1.2.1,
        le_trans hleft.2.2.2.1.2.2.1 hright.2.2.2.1.2.2.1,
        le_trans hleft.2.2.2.1.2.2.2 hright.2.2.2.1.2.2.2⟩,
      le_trans hleft.2.2.2.2 hright.2.2.2.2⟩

theorem costProfile_preorder_trans (Cost : Type*) [Preorder Cost]
    (left middle right : CostProfile Cost) : left ≤ middle → middle ≤ right → left ≤ right := by
  have hchoice : True := choiceAnchor
  cases hchoice
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact Filter.EventuallyLE.trans

theorem physicalCosts_preorder_trans (Cost : Type*) [Preorder Cost]
    (left middle right : PhysicalCosts Cost) : left ≤ middle → middle ≤ right → left ≤ right := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  have hchoice : True := choiceAnchor
  cases hchoice
  intro hleft hright
  exact ⟨le_trans hleft.1 hright.1, le_trans hleft.2.1 hright.2.1,
    le_trans hleft.2.2.1 hright.2.2.1, le_trans hleft.2.2.2 hright.2.2.2⟩

theorem taxReceipt_preorder_trans
    (AlgorithmCost RateCost PhysicalCost HeatCost : Type*)
    [Preorder AlgorithmCost] [Preorder RateCost] [Preorder PhysicalCost] [Preorder HeatCost]
    (left middle right : TaxReceipt AlgorithmCost RateCost PhysicalCost HeatCost) :
    left ≤ middle → middle ≤ right → left ≤ right := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  have hchoice : True := choiceAnchor
  cases hchoice
  intro hleft hright
  exact ⟨le_trans hleft.1 hright.1, le_trans hleft.2.1 hright.2.1,
    le_trans hleft.2.2.1 hright.2.2.1,
    ⟨le_trans hleft.2.2.2.1.1 hright.2.2.2.1.1,
      le_trans hleft.2.2.2.1.2.1 hright.2.2.2.1.2.1,
      le_trans hleft.2.2.2.1.2.2.1 hright.2.2.2.1.2.2.1,
      le_trans hleft.2.2.2.1.2.2.2 hright.2.2.2.1.2.2.2⟩,
    le_trans hleft.2.2.2.2 hright.2.2.2.2⟩

def spikeProfile : CostProfile Nat := ⟨fun n => if n = 0 then 1 else 0⟩

def zeroProfile : CostProfile Nat := ⟨fun _ => 0⟩

theorem costProfile_eventual_order_not_antisymmetric :
    zeroProfile ≤ spikeProfile ∧ spikeProfile ≤ zeroProfile ∧ zeroProfile ≠ spikeProfile := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  have hchoice : True := choiceAnchor
  cases hchoice
  refine ⟨?_, ?_, ?_⟩
  · change (fun _ : Nat => 0) ≤ᶠ[Filter.atTop] (fun n => if n = 0 then 1 else 0)
    exact Filter.Eventually.of_forall (fun n => Nat.zero_le _)
  · change (fun n => if n = 0 then 1 else 0) ≤ᶠ[Filter.atTop] (fun _ : Nat => 0)
    refine Filter.eventually_atTop.2 ⟨1, ?_⟩
    intro n hn
    simp [Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)]
  · intro h
    have hvalues := congrArg (fun profile : CostProfile Nat => profile.atScale 0) h
    simp [zeroProfile, spikeProfile] at hvalues

def tradeReceipt (w : Bool) : TaxReceipt Nat Nat Nat Nat :=
  let zero : CostProfile Nat := ⟨fun _ => 0⟩
  let one : CostProfile Nat := ⟨fun _ => 1⟩
  { forwardAlgorithm := 0
    reverseAlgorithm := 0
    rate := 0
    physical :=
      { forwardTime := if w then zero else one
        forwardSpace := if w then one else zero
        reverseTime := zero
        reverseSpace := zero }
    heat := 0 }

def tradeValid (_ : Bool) (_ _ : Unit) : Prop := True

def tradeFace : Set (TaxReceipt Nat Nat Nat Nat) :=
  priceFace tradeValid tradeReceipt () ()

lemma trade_true_not_le_false : ¬ tradeReceipt true ≤ tradeReceipt false := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  have hchoice : True := choiceAnchor
  cases hchoice
  intro h
  have hspace : (fun _ : Nat => 1) ≤ᶠ[Filter.atTop] (fun _ : Nat => 0) := by
    have hspace' := h.2.2.2.1.2.1
    change (fun _ : Nat => 1) ≤ᶠ[Filter.atTop] (fun _ : Nat => 0) at hspace'
    exact hspace'
  rcases Filter.eventually_atTop.1 hspace with ⟨N, hN⟩
  exact Nat.not_succ_le_zero _ (hN N le_rfl)

lemma trade_false_not_le_true : ¬ tradeReceipt false ≤ tradeReceipt true := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  have hchoice : True := choiceAnchor
  cases hchoice
  intro h
  have htime : (fun _ : Nat => 1) ≤ᶠ[Filter.atTop] (fun _ : Nat => 0) := by
    have htime' := h.2.2.2.1.1
    change (fun _ : Nat => 1) ≤ᶠ[Filter.atTop] (fun _ : Nat => 0) at htime'
    exact htime'
  rcases Filter.eventually_atTop.1 htime with ⟨N, hN⟩
  exact Nat.not_succ_le_zero _ (hN N le_rfl)

theorem trade_face_two_incomparable_minima :
    tradeReceipt true ∈ tradeFace ∧ tradeReceipt false ∈ tradeFace ∧
      tradeReceipt true ≠ tradeReceipt false ∧
      ¬ tradeReceipt true ≤ tradeReceipt false ∧
      ¬ tradeReceipt false ≤ tradeReceipt true := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  have hchoice : True := choiceAnchor
  cases hchoice
  have htrue : tradeReceipt true ∈ tradeFace := by
    change Minimal (fun proposed => ∃ witness, True ∧ tradeReceipt witness = proposed)
      (tradeReceipt true)
    refine ⟨⟨true, trivial, rfl⟩, ?_⟩
    intro proposed hreachable hle
    rcases hreachable with ⟨witness, _, rfl⟩
    cases witness
    · exact False.elim (trade_false_not_le_true hle)
    · exact le_rfl
  have hfalse : tradeReceipt false ∈ tradeFace := by
    change Minimal (fun proposed => ∃ witness, True ∧ tradeReceipt witness = proposed)
      (tradeReceipt false)
    refine ⟨⟨false, trivial, rfl⟩, ?_⟩
    intro proposed hreachable hle
    rcases hreachable with ⟨witness, _, rfl⟩
    cases witness
    · exact le_rfl
    · exact False.elim (trade_true_not_le_false hle)
  refine ⟨htrue, hfalse, ?_, trade_true_not_le_false, trade_false_not_le_true⟩
  intro h
  have htime := congrArg
    (fun receipt : TaxReceipt Nat Nat Nat Nat => receipt.physical.forwardTime.atScale 0) h
  simp [tradeReceipt] at htime

theorem priceFace_mem_reachable
    {Object Witness AlgorithmCost RateCost PhysicalCost HeatCost : Type*}
    [LE AlgorithmCost] [LE RateCost] [LE PhysicalCost] [LE HeatCost]
    (validWitness : Witness -> Object -> Object -> Prop)
    (receipt : Witness -> TaxReceipt AlgorithmCost RateCost PhysicalCost HeatCost)
    (left right : Object) {candidate : TaxReceipt AlgorithmCost RateCost PhysicalCost HeatCost}
    (h : candidate ∈ priceFace validWitness receipt left right) :
    ∃ witness, validWitness witness left right ∧ receipt witness = candidate := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  have hchoice : True := choiceAnchor
  cases hchoice
  exact h.1

theorem priceFace_eq_empty_of_no_valid
    {Object Witness AlgorithmCost RateCost PhysicalCost HeatCost : Type*}
    [LE AlgorithmCost] [LE RateCost] [LE PhysicalCost] [LE HeatCost]
    (validWitness : Witness -> Object -> Object -> Prop)
    (receipt : Witness -> TaxReceipt AlgorithmCost RateCost PhysicalCost HeatCost)
    (left right : Object)
    (hvalid : ¬ ∃ witness, validWitness witness left right) :
    priceFace validWitness receipt left right = ∅ := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  have hchoice : True := choiceAnchor
  cases hchoice
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro candidate hcandidate
  rcases priceFace_mem_reachable validWitness receipt left right hcandidate with
    ⟨witness, hwitness, _⟩
  exact hvalid ⟨witness, hwitness⟩

#print axioms costProfile_preorder_trans
#print axioms physicalCosts_preorder_trans
#print axioms taxReceipt_preorder_trans
#print axioms trade_true_not_le_false
#print axioms trade_false_not_le_true
#print axioms costProfile_eventual_order_not_antisymmetric
#print axioms trade_face_two_incomparable_minima
#print axioms priceFace_mem_reachable
#print axioms priceFace_eq_empty_of_no_valid

end D5.S3.ResourceOrder.PriceFaceOrder
