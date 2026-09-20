/- GID: D5/S0/Computability/PhysicalDivider/Histories
   generality: G
   mirror-B: D5/B/S0/Computability/PhysicalDivider/Histories
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary finite same-capacity calls with paid operand production and reentry. -/

import D5.S0.Computability.PhysicalDivider.OperandProduction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S0.Computability.PhysicalDivider
open Turing Lax51Proofs.RamToTM

/-- A supplied operand is backed by an actual elementary-action trace.
Its production cost is separate; its high-water intervals are never reset. -/
def OperandSupply (divisor : Bool) (w : ℕ) (bits : List Bool)
    (before after : FramedCfg) (frame : CallerTape → Extent)
    (charged : ActiveTape → Extent) : Prop :=
  let actions := overwriteActions (operandCells bits)
  actions.length = 6 * w + 6 ∧
  actions.foldl (producerStep divisor) before = after ∧
  actions.foldl (observeProducer divisor) (before, charged) = (after, charged) ∧
  ∀ i ≤ actions.length,
    let s := (actions.take i).foldl (observeProducer divisor) (before, charged)
    s.1 = (actions.take i).foldl (producerStep divisor) before ∧
    s.1.caller = before.caller ∧ s.1.active.control = before.active.control ∧
    (∀ k, (s.2 k).low = (charged k).low ∧ (s.2 k).high = (charged k).high) ∧
    (∀ k, Within (s.1.active.tapes k) (s.2 k)) ∧
    framedFootprint frame s.2 ≤ callerFootprint frame + framedSpaceConstant * (w + 1)

/-- A read counts the current position without altering a retained extent. -/
def chargeRead (charged : ActiveTape → Extent) : ActiveTape → Extent := fun k =>
  ⟨(charged k).head, min (charged k).low (charged k).head,
    max (charged k).high (charged k).head⟩

/-- Each recursive boundary is the exact returned physical layout of its
predecessor. The very same charge passes through both producers and the paid
read before the next call. No count-dependent allocation or reset is present. -/
def RepeatedCalls (w : ℕ) (capacity : List Bool) (caller : CallerTape → Tape Bool)
    (frame : CallerTape → Extent) :
    List Bool → List Bool → List Bool → List Bool →
      (ActiveTape → Extent) → List (ℕ × ℕ) → Prop
  | _, _, _, _, _, [] => True
  | oldA, oldD, oldQ, oldR, charged, (a, d) :: calls =>
    let A := fixedBits w a
    let D := fixedBits w d
    let before : FramedCfg := ⟨callReturned oldA oldD capacity oldQ oldR, caller⟩
    let middle : FramedCfg := ⟨callReturned A oldD capacity oldQ oldR, caller⟩
    let ready : FramedCfg := ⟨callReturned A D capacity oldQ oldR, caller⟩
    let entry := callEntry A D capacity oldQ oldR
    OperandSupply false w A before middle frame charged ∧
    OperandSupply true w D middle ready frame charged ∧
    framedAgain ready = some ⟨entry, caller⟩ ∧
    chargeRead charged = charged ∧
    ∃ n, n + 1 ≤ sourceStepBudget * (divPositiveRunTime w + 2) + 301 * (w + 1) ∧
      FramedCall w a d capacity oldQ oldR caller frame charged n ∧
      RepeatedCalls w capacity caller frame A D (fixedBits w (a / d))
        (fixedBits (w + 1) (a % d)) (prefixCharge (entry, fun _ => 0) charged n) calls

/-- A fixed machine, a fixed sixteen-tape family and absolute positive constants
serve all widths and every finite sequence of positive-divisor calls. Production
of each new operand is separately charged; the paid reentry is part of the next
call's allowance. The physical frame and retained extents survive every boundary. -/
theorem framed_divider_histories :
    ∃ (Dphys reenter : FramedCfg → Option FramedCfg) (k Cstep Cframe K : ℕ),
      Dphys = framedStep ∧ reenter = framedAgain ∧ k = Fintype.card FramedTape ∧ k = 16 ∧
      Cstep = sourceStepBudget ∧ Cframe = 301 ∧ K = framedSpaceConstant ∧
      0 < Cstep ∧ 0 < Cframe ∧ 0 < K ∧
      ∀ (w a d : ℕ), 1 ≤ w → a < 2 ^ w → 0 < d → d < 2 ^ w →
      ∀ (capacity oldQ oldR : List Bool), capacity.length = w →
        oldQ.length ≤ w → oldR.length ≤ w + 1 →
      ∀ (caller : CallerTape → Tape Bool) (frame : CallerTape → Extent),
        (∀ j, Within (caller j) (frame j)) →
      ∃ n, Function.Injective signedHeadDescription ∧ Function.Injective describeControl ∧
        (∀ c, codeDescription.length + (describeControl c).length = fixedCodeCharge) ∧
        FramedCall w a d capacity oldQ oldR caller frame (initialCharge w) n ∧
        n ≤ Cstep * (divPositiveRunTime w + 2) + Cframe * (w + 1) ∧
        ∀ calls : List (ℕ × ℕ),
          (∀ p ∈ calls, p.1 < 2 ^ w ∧ 0 < p.2 ∧ p.2 < 2 ^ w) →
          RepeatedCalls w capacity caller frame (fixedBits w a) (fixedBits w d)
            (fixedBits w (a / d)) (fixedBits (w + 1) (a % d))
            (prefixCharge
              (callEntry (fixedBits w a) (fixedBits w d) capacity oldQ oldR, fun _ => 0)
              (initialCharge w) n) calls := by
  classical
  refine ⟨framedStep, framedAgain, 16, sourceStepBudget, 301, framedSpaceConstant,
    rfl, rfl, by decide, rfl, rfl, rfl, rfl, ?_, by decide, ?_, ?_⟩
  · unfold sourceStepBudget; omega
  · unfold framedSpaceConstant; omega
  intro w a d hw ha hd0 hd capacity oldQ oldR hcap hq hr caller frame hframe
  have headInject : Function.Injective signedHeadDescription := by
    intro x y heq
    have hb := List.cons.inj heq
    have hv := congrArg bitsValue hb.2
    simp only [bitsValue_fixedBits, Nat.mod_eq_of_lt (Nat.lt_size_self _)] at hv
    have habs : x.natAbs = y.natAbs := by omega
    by_cases hx : x < 0
    · have hy : y < 0 := by
        by_contra hy
        simp [hx, hy] at hb
      have hxa := Int.ofNat_natAbs_of_nonpos (show x ≤ 0 by omega)
      have hya := Int.ofNat_natAbs_of_nonpos (show y ≤ 0 by omega)
      omega
    · have hy : ¬y < 0 := by
        intro hy
        simp [hx, hy] at hb
      have hxa := Int.natAbs_of_nonneg (show 0 ≤ x by omega)
      have hya := Int.natAbs_of_nonneg (show 0 ≤ y by omega)
      omega
  have radius : 2 * (w + 1) + 1 ≤ callRadius w := by
    unfold callRadius arithmeticStackBound
    omega
  have linear : callRadius w ≤ radiusSlope * (w + 1) := by
    let p := @programPushBound DivStack DivLabel DivControl (fun _ => Bool) _ divMachine.m
    change 2 * ((w+1) + (6*(w+1)+10)*p) + sourceStepBudget + 400*(w+1)+3 ≤
      (405+sourceStepBudget+32*p)*(w+1)
    have hp : 20*p ≤ 20*p*(w+1) := Nat.le_mul_of_pos_right _ (by omega)
    have hs : sourceStepBudget ≤ sourceStepBudget*(w+1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  have cost (e : ActiveTape → Extent)
      (he : ∀ j, -(callRadius w : ℤ) ≤ (e j).low ∧ (e j).high ≤ callRadius w ∧
        -(callRadius w : ℤ) ≤ (e j).head ∧ (e j).head ≤ callRadius w) :
      framedFootprint frame e ≤ callerFootprint frame + framedSpaceConstant*(w+1) := by
    have each (j : ActiveTape) : extentCost (e j) ≤ 3 * callRadius w + 3 := by
      obtain ⟨hl, hh, hp, hq⟩ := he j
      have habs : (e j).head.natAbs ≤ callRadius w := by
        by_cases hn : 0 ≤ (e j).head
        · have h := Int.natAbs_of_nonneg hn; omega
        · have h := Int.ofNat_natAbs_of_nonpos (show (e j).head ≤ 0 by omega); omega
      have hs : ((e j).head.natAbs + 1).size ≤ (e j).head.natAbs + 1 :=
        Nat.size_le.mpr Nat.lt_two_pow_self
      have hspan : ((e j).high - (e j).low + 1).toNat ≤ 2 * callRadius w + 1 := by omega
      dsimp only [extentCost]; omega
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (f := fun j => extentCost (e j)) (g := fun _ : ActiveTape => 3*callRadius w+3)
      (fun j _ => each j)
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
    have hc : fixedCodeCharge ≤ fixedCodeCharge*(w+1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have hs : 3*callRadius w+3 ≤ (3*radiusSlope+3)*(w+1) := by nlinarith
    have hm := Nat.mul_le_mul_left (Fintype.card ActiveTape) hs
    dsimp only [framedFootprint, framedSpaceConstant]
    nlinarith
  have boundaryWithin (A D Q R : List Bool) (hA : A.length = w) (hD : D.length = w)
      (hQ : Q.length ≤ w) (hR : R.length ≤ w+1)
      (charged : ActiveTape → Extent) (hfits : ChargeFits w charged) :
      ∀ k, Within ((callReturned A D capacity Q R).tapes k) (charged k) := by
    intro k
    let bs := boundaryWords A D capacity Q R k
    have hlen : bs.length ≤ w+1 := by
      dsimp [bs]
      cases k <;> rename_i k <;> cases k <;>
        simp [boundaryWords, hA, hD, hcap] <;> omega
    have ht : (callReturned A D capacity Q R).tapes k = stackAtOrigin bs := by
      cases k <;> rename_i k <;> cases k <;> rfl
    have he := hfits k
    dsimp only [Within]
    rw [he.2.2.1]
    refine ⟨he.2.1, by have h := he.2.2.2.1; omega, ?_⟩
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
      have hl : ([false, true] ++ bs.reverse.flatMap (fun b => [true, b])).length =
          2 * bs.length + 2 := by simp [List.length_flatMap]; omega
      rw [hl] at hc
      simp only [Int.zero_add, Int.ofNat_eq_natCast]
      constructor <;> omega
    | negSucc j =>
      change ([] : List Bool).getI j = true at hi
      simp at hi
  have supply (divisor : Bool) (before : FramedCfg) (charged : ActiveTape → Extent)
      (hfits : ChargeFits w charged) (old bits : List Bool)
      (hold : old.length = w) (hbits : bits.length = w)
      (htape : before.active.tapes (operandTape divisor) = stackAtOrigin old)
      (hwithin : ∀ k, Within (before.active.tapes k) (charged k)) :
      OperandSupply divisor w bits before (replacedOperand divisor before bits) frame charged := by
    obtain ⟨hsize, hobs, hrun, hprefix, hsupport⟩ :=
      produce_operand_buffer divisor before charged old bits
      htape (by omega) (hfits _).2.2.1 (hfits _).2.1 (by
        have h := (hfits (operandTape divisor)).2.2.2.1
        rw [hbits]; omega)
    refine ⟨by simpa only [hbits] using hsize, hrun, hobs, ?_⟩
    intro i hi
    obtain ⟨hp, hf, hc, he, hother, hlo, hhi⟩ := hprefix i hi
    refine ⟨hp, hf, hc, he, hsupport i hwithin, cost _ ?_⟩
    intro j
    rw [(he j).1, (he j).2]
    have hj := hfits j
    refine ⟨hj.1, hj.2.2.2.2, ?_, ?_⟩
    all_goals
      by_cases hk : j = operandTape divisor
      · subst j
        rw [hbits] at hhi
        omega
      · rw [(hother j hk).2, hj.2.2.1]
        omega
  have repeated : ∀ calls : List (ℕ × ℕ),
      (∀ p ∈ calls, p.1 < 2 ^ w ∧ 0 < p.2 ∧ p.2 < 2 ^ w) →
      ∀ (A D Q R : List Bool), A.length = w → D.length = w → Q.length ≤ w → R.length ≤ w+1 →
      ∀ charged, ChargeFits w charged → RepeatedCalls w capacity caller frame A D Q R charged calls := by
    intro calls
    induction calls with
    | nil => intros; trivial
    | cons p calls ih =>
      intro hvalid A D Q R hA hD hQ hR charged hcharged
      rcases p with ⟨a', d'⟩
      have hp := hvalid (a',d') (by simp)
      have restValid : ∀ p ∈ calls, p.1 < 2^w ∧ 0 < p.2 ∧ p.2 < 2^w :=
        fun p hp => hvalid p (by simp [hp])
      obtain ⟨_, _, _, n, hcall⟩ := framed_positive_call w a' d' hw hp.1 hp.2.1 hp.2.2
        capacity Q R hcap hQ hR caller frame hframe charged hcharged
      have hcall' := hcall
      rcases hcall' with ⟨hn, _, _, hnext, _, _⟩
      let before : FramedCfg := ⟨callReturned A D capacity Q R, caller⟩
      let middle : FramedCfg := ⟨callReturned (fixedBits w a') D capacity Q R, caller⟩
      have hmid : replacedOperand false before (fixedBits w a') = middle := by
        dsimp [replacedOperand, before, middle, callReturned, operandTape]
        congr 2
        funext k
        cases k <;> rename_i k <;> cases k <;> simp [entryTapes, Function.update]
      have hready : replacedOperand true middle (fixedBits w d') =
          FramedCfg.mk (callReturned (fixedBits w a') (fixedBits w d') capacity Q R) caller := by
        dsimp [replacedOperand, middle, callReturned, operandTape]
        congr 2
        funext k
        cases k <;> rename_i k <;> cases k <;> simp [entryTapes, Function.update]
      dsimp only [RepeatedCalls]
      refine ⟨?_, ?_, rfl, ?_, n, by omega, hcall, ?_⟩
      · have h := supply false before charged hcharged A (fixedBits w a') hA
          (fixedBits_length _ _) rfl (boundaryWithin A D Q R hA hD hQ hR charged hcharged)
        rw [hmid] at h
        exact h
      · have h := supply true middle charged hcharged D (fixedBits w d') hD
          (fixedBits_length _ _) rfl (boundaryWithin (fixedBits w a') D Q R
            (fixedBits_length _ _) hD hQ hR charged hcharged)
        rw [hready] at h
        exact h
      · funext k
        have hk := hcharged k
        dsimp only [chargeRead]
        rw [min_eq_left (by rw [hk.2.2.1]; exact hk.2.1),
          max_eq_left (by rw [hk.2.2.1]; have h := hk.2.2.2.1; omega)]
      · exact ih restValid _ _ _ _ (fixedBits_length _ _) (fixedBits_length _ _)
          (by simp) (by simp) _ hnext
  have hinitial : ChargeFits w (initialCharge w) := by
    intro k
    dsimp only [initialCharge]
    refine ⟨by omega, le_rfl, rfl, by omega, ?_⟩
    exact_mod_cast radius
  obtain ⟨_, hcode, hcodeLength, n, hcall⟩ := framed_positive_call w a d hw ha hd0 hd
    capacity oldQ oldR hcap hq hr caller frame hframe (initialCharge w) hinitial
  have hcall' := hcall
  rcases hcall' with ⟨hn, _, _, hnext, _, _⟩
  refine ⟨n, headInject, hcode, hcodeLength, hcall, hn.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right (w + 1) (by decide : 300 ≤ 301)) _), ?_⟩
  intro calls hvalid
  exact repeated calls hvalid _ _ _ _ (fixedBits_length _ _) (fixedBits_length _ _)
    (by simp) (by simp) _ hnext

end D5.S0.Computability.PhysicalDivider
