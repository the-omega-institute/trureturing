/- GID: D5/S0/Computability/PhysicalDivider/Framing
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Protected caller tapes and fixed finite code for the physical divider. -/

import D5.S0.Computability.PhysicalDivider.Footprint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S0.Computability.PhysicalDivider
open Turing Lax51Proofs.RamToTM

/-- Two additional sequential bit tapes, fixed before every operand and width. -/
abbrev CallerTape := Fin 2

/-- The complete machine has sixteen bit tapes. -/
abbrev FramedTape := Sum ActiveTape CallerTape

/-- Caller tapes are actual machine storage, not a numerical allowance. -/
structure FramedCfg where
  active : PhysicalCfg
  caller : CallerTape → Tape Bool

def framedTapes (c : FramedCfg) : FramedTape → Tape Bool :=
  Sum.elim c.active.tapes c.caller

/-- Each instruction still performs just one bit action, on its selected active tape. -/
def framedExecute (c : FramedCfg) (action : Instruction) : FramedCfg :=
  ⟨executeInstruction c.active.tapes action, c.caller⟩

def framedStep (c : FramedCfg) : Option FramedCfg :=
  (instruction c.active.control).map (framedExecute c)

/-- Paid reentry has the same counted read implementation on the complete tape family. -/
def framedAgain (c : FramedCfg) : Option FramedCfg :=
  match c.active.control with
  | .returned => some (framedExecute c (controlRead (.frame .seekA none)))
  | _ => none

/-- Every code field has a single fixed width. This deliberately loose width
is finite and independent of the width of a division problem. -/
noncomputable def codeFieldWidth : ℕ := Fintype.card Control + Fintype.card ActiveTape + 1

noncomputable def describeControl (c : Control) : List Bool :=
  fixedBits codeFieldWidth ((Fintype.equivFin Control) c).val

/-- Fixed-size rows encode the opcode, bit/direction, tape, and both read branches. -/
noncomputable def describeInstruction : Option Instruction → List Bool
  | none => List.replicate (3 + 3 * codeFieldWidth) false
  | some (.read k next) => [false, true, false] ++
      fixedBits codeFieldWidth ((Fintype.equivFin ActiveTape) k).val ++
      describeControl (next false) ++ describeControl (next true)
  | some (.write k b next) => [true, false, b] ++
      fixedBits codeFieldWidth ((Fintype.equivFin ActiveTape) k).val ++
      describeControl next ++ List.replicate codeFieldWidth false
  | some (.move k dir next) => [true, true, decide (dir = .right)] ++
      fixedBits codeFieldWidth ((Fintype.equivFin ActiveTape) k).val ++
      describeControl next ++ List.replicate codeFieldWidth false

/-- All rows of the actual finite transition table, followed by the reentry row. -/
noncomputable def codeDescription : List Bool :=
  (List.ofFn (fun i : Fin (Fintype.card Control) =>
    describeInstruction (instruction ((Fintype.equivFin Control).symm i)))).flatten ++
      describeInstruction (some (controlRead (.frame .seekA none)))

/-- Program bits and a complete current-control description. -/
noncomputable def fixedCodeCharge : ℕ := codeDescription.length + codeFieldWidth

/-- The protected frame includes its retained extents and signed head descriptions. -/
def callerFootprint (frame : CallerTape → Extent) : ℕ := ∑ k, extentCost (frame k)

noncomputable def framedFootprint (frame : CallerTape → Extent)
    (charged : ActiveTape → Extent) : ℕ :=
  callerFootprint frame + fixedCodeCharge + ∑ k, extentCost (charged k)

/-- A retained charge at a parked boundary; it may include cells from earlier calls. -/
def ChargeFits (w : ℕ) (charged : ActiveTape → Extent) : Prop :=
  ∀ k, -(callRadius w : ℤ) ≤ (charged k).low ∧
    (charged k).low ≤ 0 ∧ (charged k).head = 0 ∧
    2 * (w + 1 : ℤ) + 1 ≤ (charged k).high ∧ (charged k).high ≤ callRadius w

/-- Initial allocation includes both bits of every represented block, even zero bits. -/
def initialCharge (w : ℕ) : ActiveTape → Extent := fun _ => ⟨0, 0, 2 * (w + 1) + 1⟩

noncomputable def radiusSlope : ℕ := 405 + sourceStepBudget + 32 *
  @programPushBound DivStack DivLabel DivControl (fun _ => Bool) _ divMachine.m

/-- One absolute constant covers every active extent and the finite program/control. -/
noncomputable def framedSpaceConstant : ℕ :=
  fixedCodeCharge + Fintype.card ActiveTape * (3 * radiusSlope + 3) + 1

/-- An exact single-call certificate. Initial and historical cells remain charged;
the return and reentry equations describe actual machine execution. -/
def FramedCall (w a d : ℕ) (capacity oldQ oldR : List Bool)
    (caller : CallerTape → Tape Bool) (frame : CallerTape → Extent)
    (charged : ActiveTape → Extent) (n : ℕ) : Prop :=
  let entry := callEntry (fixedBits w a) (fixedBits w d) capacity oldQ oldR
  let returned := callReturned (fixedBits w a) (fixedBits w d) capacity
    (fixedBits w (a / d)) (fixedBits (w + 1) (a % d))
  n ≤ sourceStepBudget * (divPositiveRunTime w + 2) + 300 * (w + 1) ∧
  ((fun o : Option FramedCfg => o.bind framedStep)^[n]) (some ⟨entry, caller⟩) =
    some ⟨returned, caller⟩ ∧
  (∀ i ≤ n, ∃ c : LocatedCfg,
    ((fun o : Option LocatedCfg => o.bind locatedStep)^[i]) (some (entry, fun _ => 0)) = some c ∧
    ((fun o : Option FramedCfg => o.bind framedStep)^[i]) (some ⟨entry, caller⟩) =
      some ⟨c.1, caller⟩ ∧
    (∀ k, (prefixCharge (entry, fun _ => 0) charged i k).head = c.2 k ∧
      Within (c.1.tapes k) (prefixCharge (entry, fun _ => 0) charged i k)) ∧
    (∀ j ≤ i, Retains (prefixCharge (entry, fun _ => 0) charged j)
      (prefixCharge (entry, fun _ => 0) charged i)) ∧
    (∀ j ≤ i, ∃ past : LocatedCfg,
      ((fun o : Option LocatedCfg => o.bind locatedStep)^[j])
        (some (entry, fun _ => 0)) = some past ∧
      ∀ k, Within (past.1.tapes k) ⟨past.2 k,
        (prefixCharge (entry, fun _ => 0) charged i k).low,
        (prefixCharge (entry, fun _ => 0) charged i k).high⟩) ∧
    (∀ k p, 0 ≤ p → p ≤ 2 *
        (boundaryWords (fixedBits w a) (fixedBits w d) capacity oldQ oldR k).length + 1 →
      (prefixCharge (entry, fun _ => 0) charged i k).low ≤ p ∧
        p ≤ (prefixCharge (entry, fun _ => 0) charged i k).high) ∧
    (∀ k, extentCost (prefixCharge (entry, fun _ => 0) charged i k) =
      ((prefixCharge (entry, fun _ => 0) charged i k).high -
        (prefixCharge (entry, fun _ => 0) charged i k).low + 1).toNat +
          (signedHeadDescription (c.2 k)).length) ∧
    (∀ k, Within (caller k) (frame k)) ∧
    framedFootprint frame (prefixCharge (entry, fun _ => 0) charged i) ≤
      callerFootprint frame + framedSpaceConstant * (w + 1)) ∧
  ChargeFits w (prefixCharge (entry, fun _ => 0) charged n) ∧
  Retains charged (prefixCharge (entry, fun _ => 0) charged n) ∧
  framedAgain ⟨returned, caller⟩ = some
    ⟨callEntry (fixedBits w a) (fixedBits w d) capacity
      (fixedBits w (a / d)) (fixedBits (w + 1) (a % d)), caller⟩

/-- The complete caller frame is preserved through every physical action,
including return signalling. The fixed program/control and every tape/head
description fit one absolute linear allowance. No charge is reset at return. -/
theorem framed_positive_call (w a d : ℕ) (hw : 1 ≤ w)
    (ha : a < 2 ^ w) (hd0 : 0 < d) (hd : d < 2 ^ w)
    (capacity oldQ oldR : List Bool) (hcap : capacity.length = w)
    (hq : oldQ.length ≤ w) (hr : oldR.length ≤ w + 1)
    (caller : CallerTape → Tape Bool) (frame : CallerTape → Extent)
    (hframe : ∀ k, Within (caller k) (frame k))
    (charged : ActiveTape → Extent) (hcharged : ChargeFits w charged) :
    0 < framedSpaceConstant ∧
    Function.Injective describeControl ∧
    (∀ c, codeDescription.length + (describeControl c).length = fixedCodeCharge) ∧
    ∃ n, FramedCall w a d capacity oldQ oldR caller frame charged n := by
  classical
  let entry := callEntry (fixedBits w a) (fixedBits w d) capacity oldQ oldR
  let returned := callReturned (fixedBits w a) (fixedBits w d) capacity
    (fixedBits w (a / d)) (fixedBits (w + 1) (a % d))
  let initial : LocatedCfg := (entry, fun _ => 0)
  obtain ⟨n, hn, hrun, hb, hagain, hcost⟩ :=
    positive_call_execution w a d hw ha hd0 hd capacity oldQ oldR hcap hq hr
  have inject : Function.Injective describeControl := by
    intro c d heq
    apply (Fintype.equivFin Control).injective
    apply Fin.ext
    have hv := congrArg bitsValue heq
    have small (c : Control) : ((Fintype.equivFin Control) c).val < 2 ^ codeFieldWidth := by
      have h := ((Fintype.equivFin Control) c).isLt
      have hp := Nat.lt_two_pow_self (n := codeFieldWidth)
      dsimp [codeFieldWidth] at hp ⊢
      omega
    simpa only [describeControl, bitsValue_fixedBits, Nat.mod_eq_of_lt (small c),
      Nat.mod_eq_of_lt (small d)] using hv
  refine ⟨by unfold framedSpaceConstant; omega, inject, ?_, n, ?_⟩
  · intro c
    simp only [describeControl, fixedBits_length, fixedCodeCharge]
  have lift : Function.Semiconj
      (Option.map (fun c : PhysicalCfg => FramedCfg.mk c caller))
      (fun o : Option PhysicalCfg => o.bind physicalStep)
      (fun o : Option FramedCfg => o.bind framedStep) := by
    intro o
    cases o with
    | none => rfl
    | some c =>
        simp only [Option.bind_some, Option.map_some, physicalStep, framedStep,
          Option.map_map, Function.comp_def]
        rfl
  have proj : Function.Semiconj (Option.map Prod.fst)
      (fun o : Option LocatedCfg => o.bind locatedStep)
      (fun o : Option PhysicalCfg => o.bind physicalStep) := by
    intro o
    cases o with
    | none => rfl
    | some c => simp [locatedStep, physicalStep, Option.map_map, Function.comp_def]
  have runFrame (i : ℕ) (c : LocatedCfg)
      (hc : ((fun o : Option LocatedCfg => o.bind locatedStep)^[i]) (some initial) = some c) :
      ((fun o : Option FramedCfg => o.bind framedStep)^[i]) (some ⟨entry, caller⟩) =
        some ⟨c.1, caller⟩ := by
    have h := (proj.iterate_right i) (some initial)
    rw [hc] at h
    change some c.1 = ((fun o : Option PhysicalCfg => o.bind physicalStep)^[i])
      (some entry) at h
    have h' := (lift.iterate_right i) (some entry)
    rw [← h] at h'
    exact h'.symm
  have hhead : ∀ k, (charged k).head = initial.2 k := fun k => (hcharged k).2.2.1
  have hwithin : ∀ k, Within (entry.tapes k) (charged k) := by
    intro k
    let bs := boundaryWords (fixedBits w a) (fixedBits w d) capacity oldQ oldR k
    have hlen : bs.length ≤ w + 1 := by
      dsimp [bs]
      cases k <;> rename_i k <;> cases k <;>
        simp [boundaryWords, hcap] <;> omega
    have ht : entry.tapes k = stackAtOrigin bs := by
      cases k <;> rename_i k <;> cases k <;> rfl
    rcases hcharged k with ⟨_, hl, hh, hu, _⟩
    dsimp only [Within]
    rw [hh]
    refine ⟨hl, by omega, ?_⟩
    intro i hi
    rw [ht] at hi
    cases i with
    | ofNat j =>
      change (stackAtOrigin bs).nth (j : ℤ) = true at hi
      rw [stackAtOrigin, Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk] at hi
      have hc : j < ([false, true] ++ bs.reverse.flatMap (fun b => [true, b])).length := by
        by_contra hn
        rw [List.getI_eq_default _ (by omega)] at hi
        cases hi
      have he : ([false, true] ++ bs.reverse.flatMap (fun b => [true, b])).length =
          2 * bs.length + 2 := by simp [List.length_flatMap]; omega
      rw [he] at hc
      simp only [Int.zero_add, Int.ofNat_eq_natCast]
      constructor <;> omega
    | negSucc j =>
      change ([] : List Bool).getI j = true at hi
      simp at hi
  have chargeBounds : ∀ i ≤ n, ∀ k,
      -(callRadius w : ℤ) ≤ (prefixCharge initial charged i k).low ∧
      (prefixCharge initial charged i k).high ≤ callRadius w := by
    intro i hi
    induction i with
    | zero => exact fun k => ⟨(hcharged k).1, (hcharged k).2.2.2.2⟩
    | succ i ih =>
      obtain ⟨c, hc, _, he⟩ := hb (i+1) hi
      intro k
      have hp := ih (by omega) k
      have hk := he k
      dsimp only [Within] at hk
      simp only [prefixCharge, show
        ((fun o : Option LocatedCfg => o.bind locatedStep)^[i+1]) (some initial) = some c
          from hc, Option.getD_some]
      exact ⟨by omega, by omega⟩
  have linear : callRadius w ≤ radiusSlope * (w + 1) := by
    let p := @programPushBound DivStack DivLabel DivControl (fun _ => Bool) _ divMachine.m
    change 2 * ((w+1) + (6*(w+1)+10)*p) + sourceStepBudget + 400*(w+1)+3 ≤
      (405+sourceStepBudget+32*p)*(w+1)
    have hp : 20*p ≤ 20*p*(w+1) := Nat.le_mul_of_pos_right _ (by omega)
    have hs : sourceStepBudget ≤ sourceStepBudget*(w+1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  have bound (i : ℕ) (hi : i ≤ n) :
      framedFootprint frame (prefixCharge initial charged i) ≤
        callerFootprint frame + framedSpaceConstant * (w+1) := by
    have h := hcost charged hcharged (callerFootprint frame) fixedCodeCharge i hi
    change callerFootprint frame + fixedCodeCharge +
      ∑ k, extentCost (prefixCharge initial charged i k) ≤ _ at h
    have hc : fixedCodeCharge ≤ fixedCodeCharge*(w+1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have hr : 3*callRadius w+3 ≤ (3*radiusSlope+3)*(w+1) := by nlinarith
    have hm := Nat.mul_le_mul_left (Fintype.card ActiveTape) hr
    dsimp only [framedFootprint, framedSpaceConstant]
    nlinarith
  change FramedCall w a d capacity oldQ oldR caller frame charged n
  dsimp only [FramedCall]
  refine ⟨hn, runFrame n (returned, fun _ => 0) hrun, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨c, hc, _, _⟩ := hb i hi
    obtain ⟨hcells, hretains, hhistory, hdescribe⟩ :=
      persistent_prefix_footprint initial charged hhead hwithin i c hc
    refine ⟨c, hc, runFrame i c hc, hcells, hretains, hhistory, ?_,
      hdescribe, hframe, bound i hi⟩
    intro k p hp0 hplen
    have hlen : (boundaryWords (fixedBits w a) (fixedBits w d)
        capacity oldQ oldR k).length ≤ w + 1 := by
      cases k <;> rename_i k <;> cases k <;>
        simp [boundaryWords, hcap] <;> omega
    have hkeep := hretains 0 (Nat.zero_le i) k
    have hinit := hcharged k
    change (prefixCharge initial charged i k).low ≤ (charged k).low ∧
      (charged k).high ≤ (prefixCharge initial charged i k).high at hkeep
    change (prefixCharge initial charged i k).low ≤ p ∧
      p ≤ (prefixCharge initial charged i k).high
    constructor <;> omega
  · change ChargeFits w (prefixCharge initial charged n)
    intro k
    have h := persistent_prefix_footprint initial charged hhead hwithin n
      (returned, fun _ => 0) hrun
    have hkeep := h.2.1 0 (Nat.zero_le n) k
    have hh := (h.1 k).1
    have hl := chargeBounds n (le_refl n) k
    have hi := hcharged k
    change (prefixCharge initial charged n k).head = 0 at hh
    change (prefixCharge initial charged n k).low ≤ (charged k).low ∧
      (charged k).high ≤ (prefixCharge initial charged n k).high at hkeep
    exact ⟨hl.1, by omega, hh, by omega, hl.2⟩
  · exact (persistent_prefix_footprint initial charged hhead hwithin n
      (returned, fun _ => 0) hrun).2.1 0 (Nat.zero_le n)
  · change (callAgain returned).map (fun c => FramedCfg.mk c caller) = _
    rw [hagain]
    rfl

end D5.S0.Computability.PhysicalDivider
