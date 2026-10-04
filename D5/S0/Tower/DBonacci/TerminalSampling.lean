/- GID: D5/S0/Tower/DBonacci/TerminalSampling
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacci/TerminalSampling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite first-hit fair-bit executions return native legal words almost surely. -/

import D5.S0.Tower.DBonacci.Values
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section
namespace D5.S0.Tower.DBonacci.TerminalSampling

open D5.S0.Tower.DBonacci.Names D5.S0.Tower.DBonacci.Values
open MeasureTheory
open scoped BigOperators ENNReal

abbrev Tape := ℕ → Bool

/-- Actual completions of the native scanner, with `fuel` available consecutive ones. -/
def completionCount (maxTrue fuel h : ℕ) : ℕ :=
  Fintype.card (BoundedRunName maxTrue fuel h)

/-- The positional encoding is the pinned finite-function equivalence. -/
def blockEquiv (width : ℕ) : (Fin width → Bool) ≃ Fin (2 ^ width) :=
  (Equiv.piCongrRight (fun _ : Fin width => finTwoEquiv.symm)).trans finFunctionFinEquiv

/-- Read and decode the next finite block of literal source bits, low position first. -/
def readBlock (width cursor : ℕ) (tape : Tape) : Fin (2 ^ width) :=
  blockEquiv width (fun i : Fin width => tape (cursor + i.val))

/-- Retry number `t` is the first accepted block at this unchanged output state. -/
def AcceptedAt (width bound cursor : ℕ) (tape : Tape) (t : ℕ) : Prop :=
  (∀ i < t, bound ≤ (readBlock width (cursor + i * width) tape).val) ∧
    (readBlock width (cursor + t * width) tape).val < bound

/-- The literal first accepted block, or exceptional absence of any accepted block. -/
def draw (width bound cursor : ℕ) (tape : Tape) : Option (ℕ × Fin (2 ^ width)) :=
  by
  classical
  exact if h : ∃ t, (readBlock width (cursor + t * width) tape).val < bound then
    some (Nat.find h, readBlock width (cursor + Nat.find h * width) tape)
  else none

/-- Deterministic partial native-word sampler; each retry consumes a new block. -/
def sample (maxTrue : ℕ) (tape : Tape) :
    (fuel h cursor : ℕ) → Option ((Fin h → Bool) × ℕ)
  | _, 0, cursor => some ((fun i => Fin.elim0 i), cursor)
  | fuel, h + 1, cursor =>
      match draw (h + 1) (completionCount maxTrue fuel (h + 1)) cursor tape with
      | none => none
      | some (t, x) =>
          let bit := decide (completionCount maxTrue maxTrue h ≤ x.val)
          let nextFuel := if bit then fuel - 1 else maxTrue
          let nextCursor := cursor + (t + 1) * (h + 1)
          match sample maxTrue tape nextFuel h nextCursor with
          | none => none
          | some (tail, stop) => some (Fin.cons bit tail, stop)

/-- A successful finite execution records exactly the first accepted blocks it consumes. -/
inductive Run (maxTrue : ℕ) (tape : Tape) :
    (fuel h cursor : ℕ) → (Fin h → Bool) → ℕ → Prop
  | done (fuel cursor : ℕ) : Run maxTrue tape fuel 0 cursor (fun i => Fin.elim0 i) cursor
  | step {fuel h cursor stop : ℕ} {tail : Fin h → Bool}
      (t : ℕ)
      (accepted : AcceptedAt (h + 1) (completionCount maxTrue fuel (h + 1)) cursor tape t)
      (bit : Bool)
      (selected : bit = decide (completionCount maxTrue maxTrue h ≤
        (readBlock (h + 1) (cursor + t * (h + 1)) tape).val))
      (rest : Run maxTrue tape (if bit then fuel - 1 else maxTrue) h
        (cursor + (t + 1) * (h + 1)) tail stop) :
      Run maxTrue tape fuel (h + 1) cursor (Fin.cons bit tail) stop

/-- The fair law gives each actual Boolean coordinate equal mass. -/
abbrev fairBit : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

/-- One iid tape supplies all branch choices and all retries. -/
abbrev fairTape : Measure Tape := Measure.infinitePi (fun _ : ℕ => fairBit)

/-- The exact consumed source interval, allowing an arbitrary unused tape suffix. -/
def traceCylinder (cursor stop : ℕ) (tape : Tape) : Set Tape :=
  Set.pi (↑(Finset.Ico cursor stop) : Set ℕ) (fun i => {tape i})

/-- The partial evaluator and finite consumed-source execution agree. A returned native word
is legal, and replacing the unused tape suffix preserves the entire result and source cursor.
First-accepted native branch integers have the exact uniform law; infinite rejection has zero mass.
Returned-word events are measurable, illegal words have zero mass, and a native word is returned
almost surely. No uniform returned-word law is asserted here. -/
theorem terminal_sampling_execution_cylinders
    (maxTrue : ℕ) (tape : Tape) (fuel h cursor stop : ℕ) (word : Fin h → Bool) :
    (Run maxTrue tape fuel h cursor word stop ↔
      sample maxTrue tape fuel h cursor = some (word, stop)) ∧
    (sample maxTrue tape fuel h cursor = some (word, stop) →
      runAdmissible maxTrue fuel h word = true ∧ cursor ≤ stop ∧
        (∀ other : Tape, (∀ i, cursor ≤ i → i < stop → other i = tape i) →
          sample maxTrue other fuel h cursor = some (word, stop)) ∧
      fairTape (traceCylinder cursor stop tape ∩
        {other | sample maxTrue other fuel h cursor = some (word, stop)}) =
          (2 : ℝ≥0∞)⁻¹ ^ (stop - cursor)) ∧
    (∀ t (x : Fin (2 ^ h)), draw h (completionCount maxTrue fuel h) cursor tape = some (t, x) ↔
      AcceptedAt h (completionCount maxTrue fuel h) cursor tape t ∧
        readBlock h (cursor + t * h) tape = x) ∧
    (∀ t (x : Fin (2 ^ h)), x.val < completionCount maxTrue fuel h →
      MeasurableSet {source | draw h (completionCount maxTrue fuel h) cursor source = some (t, x)} ∧
        fairTape {source | draw h (completionCount maxTrue fuel h) cursor source = some (t, x)} =
          (((((2 ^ h - completionCount maxTrue fuel h : ℕ) : ℝ≥0∞) /
            (2 ^ h : ℝ≥0∞)) ^ t) / (2 ^ h : ℝ≥0∞))) ∧
    (∀ x : Fin (2 ^ h), x.val < completionCount maxTrue fuel h →
      MeasurableSet {source | ∃ t, draw h (completionCount maxTrue fuel h) cursor source = some (t, x)} ∧
        fairTape {source | ∃ t, draw h (completionCount maxTrue fuel h) cursor source = some (t, x)} =
          (completionCount maxTrue fuel h : ℝ≥0∞)⁻¹) ∧
    (MeasurableSet {source | draw h (completionCount maxTrue fuel h) cursor source = none} ∧
      fairTape {source | draw h (completionCount maxTrue fuel h) cursor source = none} = 0) ∧
    (∀ q, h = q + 1 →
      MeasurableSet {source | ∃ t, ∃ x : Fin (2 ^ h),
        draw h (completionCount maxTrue fuel h) cursor source = some (t, x) ∧
          x.val < completionCount maxTrue maxTrue q} ∧
      fairTape {source | ∃ t, ∃ x : Fin (2 ^ h),
        draw h (completionCount maxTrue fuel h) cursor source = some (t, x) ∧
          x.val < completionCount maxTrue maxTrue q} =
        (completionCount maxTrue maxTrue q : ℝ≥0∞) / completionCount maxTrue fuel h) ∧
    (MeasurableSet {source | sample maxTrue source fuel h cursor = some (word, stop)} ∧
      MeasurableSet {source | ∃ final, sample maxTrue source fuel h cursor = some (word, final)}) ∧
    @Measurable Tape (Option ((Fin h → Bool) × ℕ)) _ ⊤
      (fun source => sample maxTrue source fuel h cursor) ∧
    (runAdmissible maxTrue fuel h word = false →
      fairTape {source | ∃ final, sample maxTrue source fuel h cursor = some (word, final)} = 0) ∧
    (∀ᵐ source ∂fairTape, ∃ returned : Fin h → Bool, ∃ final : ℕ,
      sample maxTrue source fuel h cursor = some (returned, final) ∧
        runAdmissible maxTrue fuel h returned = true) := by
  classical
  have drawRun (width bound cursor t : ℕ) (x : Fin (2 ^ width)) : ∀ tape : Tape,
      draw width bound cursor tape = some (t, x) ↔
        AcceptedAt width bound cursor tape t ∧ readBlock width (cursor + t * width) tape = x := by
    intro tape
    constructor
    · intro he
      unfold draw at he
      split at he
      next hex =>
        have hp := Option.some.inj he
        have ht : Nat.find hex = t := congrArg Prod.fst hp
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro j hj
          exact Nat.le_of_not_gt (Nat.find_min hex (ht ▸ hj))
        · simpa [ht] using Nat.find_spec hex
        · simpa [ht] using congrArg Prod.snd hp
      next hn => simp at he
    · rintro ⟨accept, hx⟩
      have hex : ∃ j, (readBlock width (cursor + j * width) tape).val < bound :=
        ⟨t, accept.2⟩
      have hfind : Nat.find hex = t :=
        (Nat.find_eq_iff hex).mpr ⟨accept.2, fun j hj => Nat.not_lt.mpr (accept.1 j hj)⟩
      simp [draw, hex, hfind, hx]
  have firstHitLaw (width bound cursor t : ℕ) (bound_le : bound ≤ 2 ^ width)
      (x : Fin (2 ^ width)) (x_lt : x.val < bound) :
      MeasurableSet {tape | draw width bound cursor tape = some (t, x)} ∧
      fairTape {tape | draw width bound cursor tape = some (t, x)} =
        ((((2 ^ width - bound : ℕ) : ℝ≥0∞) / (2 ^ width : ℝ≥0∞)) ^ t) /
          (2 ^ width : ℝ≥0∞) := by
    classical
    have trialLaw (width cursor : ℕ) :
        fairTape.map (fun tape t => readBlock width (cursor + t * width) tape) =
          Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype (Fin (2 ^ width))).toMeasure) := by
      classical
      let index : ℕ × Fin width → ℕ := fun p => cursor + p.1 * width + p.2.val
      have index_inj : Function.Injective index := by
        rintro ⟨r, i⟩ ⟨s, j⟩ he
        change cursor + r * width + i.val = cursor + s * width + j.val at he
        have hrs : r = s := by
          rcases lt_trichotomy r s with hlt | heq | hgt
          · have hm := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hlt)
            rw [Nat.succ_mul] at hm
            have hi := i.isLt
            omega
          · exact heq
          · have hm := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hgt)
            rw [Nat.succ_mul] at hm
            have hj := j.isLt
            omega
        subst s
        have hij : i = j := Fin.ext (by omega)
        subst j
        rfl
      have decode_law :
          (Measure.infinitePi (fun _ : Fin width => fairBit)).map (blockEquiv width) =
            (PMF.uniformOfFintype (Fin (2 ^ width))).toMeasure := by
        apply Measure.ext_of_singleton
        intro x
        rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton x)]
        have pre : (blockEquiv width) ⁻¹' ({x} : Set (Fin (2 ^ width))) =
            {(blockEquiv width).symm x} := by
          ext f
          simp only [Set.mem_preimage, Set.mem_singleton_iff, (blockEquiv width).eq_symm_apply.symm]
        rw [pre, Measure.infinitePi_singleton_of_fintype]
        simp [fairBit, Nat.cast_pow, ← ENNReal.inv_pow]
      have bits_law : fairTape.map (fun tape p => tape (index p)) =
          Measure.infinitePi (fun _ : ℕ × Fin width => fairBit) :=
        Measure.map_infinitePi_infinitePi_of_inj index_inj
      have blocks_law : fairTape.map (fun (tape : Tape) (t : ℕ) (i : Fin width) => tape (cursor + t * width + i.val)) =
          Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : Fin width => fairBit)) := by
        rw [← Measure.infinitePi_map_curry (fun _ : ℕ => fun _ : Fin width => fairBit)]
        rw [← bits_law, Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      rw [show (fun tape t => readBlock width (cursor + t * width) tape) =
          (fun (blocks : ℕ → Fin width → Bool) (t : ℕ) => blockEquiv width (blocks t)) ∘
            (fun (tape : Tape) (t : ℕ) (i : Fin width) => tape (cursor + t * width + i.val)) by
          rfl]
      rw [← Measure.map_map (by fun_prop) (by fun_prop), blocks_law,
        Measure.infinitePi_map_pi _ (fun _ => measurable_of_finite _)]
      simp_rw [decode_law]
  
    let Q := 2 ^ width
    let ν : Measure (Fin Q) := (PMF.uniformOfFintype (Fin Q)).toMeasure
    let regions : ℕ → Set (Fin Q) := fun j =>
      if j < t then {y | bound ≤ y.val} else {x}
    have event : {tape | draw width bound cursor tape = some (t, x)} =
        (fun tape j => readBlock width (cursor + j * width) tape) ⁻¹'
          Set.pi (↑(Finset.range (t + 1)) : Set ℕ) regions := by
      ext tape
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Finset.mem_coe,
        Finset.mem_range]
      constructor
      · intro he j hj
        rcases (drawRun width bound cursor t x tape).mp he with ⟨accept, hx⟩
        by_cases hjt : j < t
        · simp only [regions, if_pos hjt]
          change bound ≤ (readBlock width (cursor + j * width) tape).val
          exact accept.1 j hjt
        · have hje : j = t := by omega
          subst j
          simpa only [regions, lt_self_iff_false, if_false, Set.mem_singleton_iff] using hx
      · intro he
        apply (drawRun width bound cursor t x tape).mpr
        have hx : readBlock width (cursor + t * width) tape = x := by
          simpa only [regions, lt_self_iff_false, if_false, Set.mem_singleton_iff] using
            he t (by omega)
        refine ⟨⟨?_, ?_⟩, hx⟩
        · intro j hj
          have hh := he j (by omega)
          simp only [regions, if_pos hj] at hh
          exact hh
        · simpa [hx] using x_lt
    have region_measurable : ∀ j, MeasurableSet (regions j) :=
      fun _ => (Set.toFinite _).measurableSet
    have family_measurable : Measurable (fun tape j => readBlock width (cursor + j * width) tape) := by
      apply measurable_pi_lambda
      intro j
      exact (measurable_of_finite (blockEquiv width)).comp
        (by fun_prop)
    have region_pi_measurable : MeasurableSet (Set.pi
        (↑(Finset.range (t + 1)) : Set ℕ) regions) :=
      MeasurableSet.pi (Finset.countable_toSet _) (fun j _ => region_measurable j)
    refine ⟨?_, ?_⟩
    · rw [event]
      exact family_measurable region_pi_measurable
    rw [event, ← Measure.map_apply family_measurable region_pi_measurable,
      trialLaw, Measure.infinitePi_pi _ (fun j _ => region_measurable j)]
    let acceptSet : Set (Fin Q) := {y | y.val < bound}
    let e : acceptSet ≃ Fin bound :=
      { toFun := fun y => ⟨y.1.val, y.2⟩
        invFun := fun y => ⟨⟨y.val, y.isLt.trans_le bound_le⟩, y.isLt⟩
        left_inv := fun y => by rfl
        right_inv := fun y => by rfl }
    have cardAccept : Fintype.card acceptSet = bound := by
      rw [Fintype.card_congr e, Fintype.card_fin]
    have cardReject : Fintype.card {y : Fin Q | bound ≤ y.val} = Q - bound := by
      have he : {y : Fin Q | bound ≤ y.val} = acceptSetᶜ := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, acceptSet]
        omega
      calc
        _ = Fintype.card (↥(acceptSetᶜ)) := Fintype.card_congr (Equiv.setCongr he)
        _ = _ := by rw [Fintype.card_compl_set, Fintype.card_fin, cardAccept]
    have rejection_mass : ν {y | bound ≤ y.val} = ((Q - bound : ℕ) : ℝ≥0∞) / Q := by
      unfold ν
      rw [PMF.toMeasure_uniformOfFintype_apply {y : Fin Q | bound ≤ y.val}
        ((Set.toFinite _).measurableSet),
        cardReject, Fintype.card_fin]
    have singleton_mass : ν {x} = (Q : ℝ≥0∞)⁻¹ := by
      simp [ν]
    have prior : ∏ j ∈ Finset.range t,
        (PMF.uniformOfFintype (Fin Q)).toMeasure (regions j) =
          (((Q - bound : ℕ) : ℝ≥0∞) / Q) ^ t := by
      calc
        _ = ∏ _j ∈ Finset.range t, (((Q - bound : ℕ) : ℝ≥0∞) / Q) := by
          apply Finset.prod_congr rfl
          intro j hj
          change ν (regions j) = _
          rw [show regions j = {y : Fin Q | bound ≤ y.val} by
            simp only [regions, if_pos (Finset.mem_range.mp hj)]]
          exact rejection_mass
        _ = _ := by simp
    rw [Finset.prod_range_succ, prior]
    have last : (PMF.uniformOfFintype (Fin Q)).toMeasure (regions t) =
        (Q : ℝ≥0∞)⁻¹ := by
      simp [regions]
    rw [last]
    simp only [Q, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]

  have valueLaw (width bound cursor : ℕ) (bound_le : bound ≤ 2 ^ width)
      (x : Fin (2 ^ width)) (x_lt : x.val < bound) :
      MeasurableSet {tape | ∃ t, draw width bound cursor tape = some (t, x)} ∧
        fairTape {tape | ∃ t, draw width bound cursor tape = some (t, x)} =
          (bound : ℝ≥0∞)⁻¹ := by
    classical
    let E : ℕ → Set Tape := fun t => {tape | draw width bound cursor tape = some (t, x)}
    have measurable_E : ∀ t, MeasurableSet (E t) :=
      fun t => (firstHitLaw width bound cursor t bound_le x x_lt).1
    have disjoint_E : Pairwise (fun i j => Disjoint (E i) (E j)) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro tape hi hj
      have hp := Option.some.inj (hi.symm.trans hj)
      exact hij (congrArg Prod.fst hp)
    have event : {tape | ∃ t, draw width bound cursor tape = some (t, x)} = ⋃ t, E t := by
      ext tape
      simp [E]
    rw [event]
    refine ⟨MeasurableSet.iUnion measurable_E, ?_⟩
    rw [measure_iUnion disjoint_E measurable_E]
    have masses : ∀ t, fairTape (E t) =
        ((((2 ^ width - bound : ℕ) : ℝ≥0∞) / (2 ^ width : ℝ≥0∞)) ^ t) *
          (2 ^ width : ℝ≥0∞)⁻¹ := by
      intro t
      simpa only [div_eq_mul_inv] using (firstHitLaw width bound cursor t bound_le x x_lt).2
    simp_rw [masses]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    let Q : ℝ≥0∞ := 2 ^ width
    have Qne : Q ≠ 0 := by simp [Q]
    have Qtop : Q ≠ ∞ := by simp [Q]
    have leQ : (bound : ℝ≥0∞) ≤ Q := by
      dsimp [Q]
      exact_mod_cast bound_le
    have ratio_le : (bound : ℝ≥0∞) / Q ≤ 1 := by
      rw [ENNReal.div_le_iff Qne Qtop, one_mul]
      exact leQ
    have ratio_reject : ((2 ^ width - bound : ℕ) : ℝ≥0∞) / Q =
        1 - (bound : ℝ≥0∞) / Q := by
      rw [ENNReal.natCast_sub, Nat.cast_pow, Nat.cast_ofNat]
      change (Q - (bound : ℝ≥0∞)) / Q = _
      rw [ENNReal.sub_div (fun _ _ => Qne), ENNReal.div_self Qne Qtop]
    change (1 - ((2 ^ width - bound : ℕ) : ℝ≥0∞) / Q)⁻¹ * Q⁻¹ = _
    rw [ratio_reject, ENNReal.sub_sub_cancel (by norm_num) ratio_le,
      ENNReal.inv_div (Or.inl Qtop) (Or.inl Qne), div_eq_mul_inv,
      mul_right_comm, ENNReal.mul_inv_cancel Qne Qtop, one_mul]
  have noneLaw (width bound cursor : ℕ) (positive : 0 < bound)
      (bound_le : bound ≤ 2 ^ width) :
      MeasurableSet {tape | draw width bound cursor tape = none} ∧
        fairTape {tape | draw width bound cursor tape = none} = 0 := by
    classical
    let embed : Fin bound → Fin (2 ^ width) := Fin.castLE bound_le
    let A : Fin bound → Set Tape := fun x =>
      {tape | ∃ t, draw width bound cursor tape = some (t, embed x)}
    have measurable_A : ∀ x, MeasurableSet (A x) :=
      fun x => (valueLaw width bound cursor bound_le (embed x) x.isLt).1
    have mass_A : ∀ x, fairTape (A x) = (bound : ℝ≥0∞)⁻¹ :=
      fun x => (valueLaw width bound cursor bound_le (embed x) x.isLt).2
    have disjoint_A : Pairwise (fun i j => Disjoint (A i) (A j)) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      rintro tape ⟨r, hr⟩ ⟨s, hs⟩
      have hx := congrArg Prod.snd (Option.some.inj (hr.symm.trans hs))
      exact hij (Fin.ext (congrArg (fun z : Fin (2 ^ width) => z.val) hx))
    have event : {tape | draw width bound cursor tape ≠ none} = ⋃ x, A x := by
      ext tape
      constructor
      · intro hn
        cases hd : draw width bound cursor tape with
        | none => exact (hn hd).elim
        | some result =>
            rcases result with ⟨t, x⟩
            have hx : x.val < bound := by
              unfold draw at hd
              split at hd
              next hex =>
                have hp := Option.some.inj hd
                have ht : Nat.find hex = t := congrArg Prod.fst hp
                have he : readBlock width (cursor + t * width) tape = x := by
                  simpa [ht] using congrArg Prod.snd hp
                simpa [he, ht] using Nat.find_spec hex
              next hn => simp at hd
            refine Set.mem_iUnion.mpr ⟨⟨x.val, hx⟩, ?_⟩
            refine ⟨t, ?_⟩
            have he : embed ⟨x.val, hx⟩ = x := Fin.ext rfl
            simpa [he] using hd
      · intro hu
        rcases Set.mem_iUnion.mp hu with ⟨x, t, ht⟩
        intro hn
        rw [ht] at hn
        contradiction
    have measurable_event : MeasurableSet {tape | draw width bound cursor tape ≠ none} := by
      rw [event]
      exact MeasurableSet.iUnion measurable_A
    have accepted_mass : fairTape {tape | draw width bound cursor tape ≠ none} = 1 := by
      rw [event, measure_iUnion disjoint_A measurable_A]
      simp_rw [mass_A]
      rw [tsum_fintype]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast positive.ne') (by simp)
    have complement : {tape | draw width bound cursor tape = none} =
        {tape | draw width bound cursor tape ≠ none}ᶜ := by
      ext tape
      simp
    rw [complement]
    refine ⟨measurable_event.compl, ?_⟩
    rw [measure_compl measurable_event (measure_ne_top _ _), accepted_mass, measure_univ]
    simp
  have thresholdLaw (width bound cursor numerator : ℕ)
      (bound_le : bound ≤ 2 ^ width) (numerator_le : numerator ≤ bound) :
      MeasurableSet {source | ∃ t, ∃ x : Fin (2 ^ width),
        draw width bound cursor source = some (t, x) ∧ x.val < numerator} ∧
      fairTape {source | ∃ t, ∃ x : Fin (2 ^ width),
        draw width bound cursor source = some (t, x) ∧ x.val < numerator} =
          (numerator : ℝ≥0∞) / bound := by
    classical
    let embed : Fin numerator → Fin (2 ^ width) := Fin.castLE (numerator_le.trans bound_le)
    let A : Fin numerator → Set Tape := fun x =>
      {source | ∃ t, draw width bound cursor source = some (t, embed x)}
    have measurable_A : ∀ x, MeasurableSet (A x) :=
      fun x => (valueLaw width bound cursor bound_le (embed x) (x.isLt.trans_le numerator_le)).1
    have mass_A : ∀ x, fairTape (A x) = (bound : ℝ≥0∞)⁻¹ :=
      fun x => (valueLaw width bound cursor bound_le (embed x) (x.isLt.trans_le numerator_le)).2
    have disjoint_A : Pairwise (fun i j => Disjoint (A i) (A j)) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      rintro source ⟨r, hr⟩ ⟨t, ht⟩
      have hx := congrArg Prod.snd (Option.some.inj (hr.symm.trans ht))
      exact hij (Fin.ext (congrArg (fun z : Fin (2 ^ width) => z.val) hx))
    have event : {source | ∃ t, ∃ x : Fin (2 ^ width),
        draw width bound cursor source = some (t, x) ∧ x.val < numerator} = ⋃ x, A x := by
      ext source
      constructor
      · rintro ⟨t, x, ht, hx⟩
        refine Set.mem_iUnion.mpr ⟨⟨x.val, hx⟩, t, ?_⟩
        have he : embed ⟨x.val, hx⟩ = x := Fin.ext rfl
        simpa [he] using ht
      · intro hu
        rcases Set.mem_iUnion.mp hu with ⟨x, t, ht⟩
        exact ⟨t, embed x, ht, x.isLt⟩
    rw [event]
    refine ⟨MeasurableSet.iUnion measurable_A, ?_⟩
    rw [measure_iUnion disjoint_A measurable_A]
    simp_rw [mass_A]
    rw [tsum_fintype]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rfl
  have allDraws : ∀ᵐ source ∂fairTape, ∀ (g f c : ℕ),
      draw g (completionCount maxTrue f g) c source ≠ none := by
    rw [ae_all_iff]
    intro g
    rw [ae_all_iff]
    intro f
    rw [ae_all_iff]
    intro c
    have positive : 0 < completionCount maxTrue f g := bounded_run_level_pos _ _ _
    have bounded : completionCount maxTrue f g ≤ 2 ^ g := by
      unfold completionCount
      simpa [BoundedRunName] using (Fintype.card_subtype_le
        (fun w : Fin g → Bool => runAdmissible maxTrue f g w = true))
    simpa only [ae_iff, not_not] using (noneLaw g (completionCount maxTrue f g) c positive bounded).2
  have forward
      (tape : Tape) {fuel h cursor stop : ℕ} {word : Fin h → Bool}
      (run : Run maxTrue tape fuel h cursor word stop) :
      runAdmissible maxTrue fuel h word = true ∧ cursor ≤ stop ∧
        sample maxTrue tape fuel h cursor = some (word, stop) ∧
        (∀ other : Tape, (∀ i, cursor ≤ i → i < stop → other i = tape i) →
          Run maxTrue other fuel h cursor word stop) := by
    classical
    induction run with
    | done fuel cursor =>
        refine ⟨by simp [runAdmissible], le_rfl, by simp [sample], ?_⟩
        intro other _
        exact Run.done fuel cursor
    | @step fuel h cursor stop tail t accepted bit selected rest ih =>
        rcases ih with ⟨legal, cursorBound, evaluated, transport⟩
        have acceptedValue := accepted.2
        have allowed : bit = true → 0 < fuel := by
          intro hb
          have hselected : completionCount maxTrue maxTrue h ≤
              (readBlock (h + 1) (cursor + t * (h + 1)) tape).val := by
            exact of_decide_eq_true (selected.symm.trans hb)
          by_contra hn
          have hf : fuel = 0 := by omega
          subst fuel
          have hc := bounded_run_name_card_zero maxTrue h
          change completionCount maxTrue 0 (h + 1) = completionCount maxTrue maxTrue h at hc
          omega
        have first : draw (h + 1) (completionCount maxTrue fuel (h + 1)) cursor tape =
            some (t, readBlock (h + 1) (cursor + t * (h + 1)) tape) := by
          have hex : ∃ j, (readBlock (h + 1) (cursor + j * (h + 1)) tape).val <
              completionCount maxTrue fuel (h + 1) := ⟨t, accepted.2⟩
          have hfind : Nat.find hex = t := by
            apply (Nat.find_eq_iff hex).mpr
            exact ⟨accepted.2, fun j hj => Nat.not_lt.mpr (accepted.1 j hj)⟩
          simp [draw, hex, hfind]
        refine ⟨?_, by omega, ?_, ?_⟩
        · cases bit with
          | false =>
              cases fuel <;> simpa [runAdmissible] using legal
          | true =>
              cases fuel with
              | zero => exact (Nat.lt_irrefl 0 (allowed rfl)).elim
              | succ fuel => simpa [runAdmissible] using legal
        · simp only [sample, first]
          rw [← selected]
          rw [evaluated]
        · intro other agree
          have blocks : ∀ j ≤ t,
              readBlock (h + 1) (cursor + j * (h + 1)) other =
                readBlock (h + 1) (cursor + j * (h + 1)) tape := by
            intro j hj
            unfold readBlock
            apply congrArg (blockEquiv (h + 1))
            funext i
            apply agree
            · omega
            · have hi := i.isLt
              have hmul := Nat.mul_le_mul_right (h + 1) hj
              have he : (t + 1) * (h + 1) = t * (h + 1) + (h + 1) := by ring
              rw [he] at cursorBound
              omega
          have newAccepted : AcceptedAt (h + 1) (completionCount maxTrue fuel (h + 1))
              cursor other t := by
            constructor
            · intro j hj
              rw [blocks j (by omega)]
              exact accepted.1 j hj
            · rw [blocks t le_rfl]
              exact accepted.2
          apply Run.step t newAccepted bit
          · rw [blocks t le_rfl]
            exact selected
          · apply transport other
            intro i hlow hhigh
            exact agree i (by omega) hhigh
  
  have backward (tape : Tape) : ∀ (h fuel cursor stop : ℕ) (word : Fin h → Bool),
      sample maxTrue tape fuel h cursor = some (word, stop) →
        Run maxTrue tape fuel h cursor word stop := by
    intro h
    induction h with
    | zero =>
        intro fuel cursor stop word he
        have hw : word = fun i => Fin.elim0 i := Subsingleton.elim _ _
        subst word
        have hs : cursor = stop := by simpa [sample] using he
        subst stop
        exact Run.done fuel cursor
    | succ h ih =>
        intro fuel cursor stop word he
        cases hd : draw (h + 1) (completionCount maxTrue fuel (h + 1)) cursor tape with
        | none => simp [sample, hd] at he
        | some result =>
            rcases result with ⟨t, x⟩
            have accepted : AcceptedAt (h + 1) (completionCount maxTrue fuel (h + 1))
                cursor tape t := by
              unfold draw at hd
              split at hd
              next hex =>
                have hp := Option.some.inj hd
                have ht : Nat.find hex = t := congrArg Prod.fst hp
                constructor
                · intro j hj
                  have hn := Nat.find_min hex (ht ▸ hj)
                  exact Nat.le_of_not_gt hn
                · simpa [ht] using Nat.find_spec hex
              next hn => simp at hd
            have hx : x = readBlock (h + 1) (cursor + t * (h + 1)) tape := by
              unfold draw at hd
              split at hd
              next hex =>
                have hp := Option.some.inj hd
                have ht : Nat.find hex = t := congrArg Prod.fst hp
                simpa [ht] using (congrArg Prod.snd hp).symm
              next hn => simp at hd
            simp only [sample, hd] at he
            let bit := decide (completionCount maxTrue maxTrue h ≤ x.val)
            change (match sample maxTrue tape (if bit then fuel - 1 else maxTrue) h
                (cursor + (t + 1) * (h + 1)) with
              | none => none
              | some (tail, final) => some (Fin.cons bit tail, final)) = some (word, stop) at he
            cases hr : sample maxTrue tape (if bit then fuel - 1 else maxTrue) h
                (cursor + (t + 1) * (h + 1)) with
            | none => simp [hr] at he
            | some result =>
                rcases result with ⟨tail, final⟩
                have hp : (Fin.cons bit tail, final) = (word, stop) := by
                  simpa only [hr, Option.some.injEq] using he
                have hw : Fin.cons bit tail = word := congrArg Prod.fst hp
                have hf : final = stop := congrArg Prod.snd hp
                subst word
                subst final
                exact Run.step t accepted bit (by simp [bit, hx])
                  (ih _ _ _ tail hr)
  have measurableReturn (word : Fin h → Bool) (stop : ℕ) :
      MeasurableSet {source | sample maxTrue source fuel h cursor = some (word, stop)} := by
    let representative (bits : Fin stop → Bool) : Tape := fun i =>
      if hi : i < stop then bits ⟨i, hi⟩ else false
    let A (bits : Fin stop → Bool) : Set Tape :=
      if sample maxTrue (representative bits) fuel h cursor = some (word, stop) then
        traceCylinder 0 stop (representative bits) else ∅
    have measurable_A : ∀ bits, MeasurableSet (A bits) := by
      intro bits
      dsimp [A]
      split
      · exact (measurableSet_pi (Finset.countable_toSet _)).mpr
          (Or.inl (fun _ _ => measurableSet_singleton _))
      · exact MeasurableSet.empty
    have event : {source | sample maxTrue source fuel h cursor = some (word, stop)} =
        ⋃ bits, A bits := by
      ext source
      constructor
      · intro he
        let bits : Fin stop → Bool := fun i => source i.val
        have agree : ∀ i, cursor ≤ i → i < stop → representative bits i = source i := by
          intro i _ hi
          simp [representative, bits, hi]
        have evaluated : sample maxTrue (representative bits) fuel h cursor = some (word, stop) :=
          (forward source (backward source h fuel cursor stop word he)).2.2.2 _ agree |>
            fun run => (forward _ run).2.2.1
        refine Set.mem_iUnion.mpr ⟨bits, ?_⟩
        simp only [A, evaluated, if_true]
        intro i hi
        have bound : i < stop := (Finset.mem_Ico.mp hi).2
        simp [representative, bits, bound]
      · intro hu
        rcases Set.mem_iUnion.mp hu with ⟨bits, ha⟩
        dsimp [A] at ha
        split at ha
        next he =>
          exact (forward source
            ((forward (representative bits)
              (backward _ h fuel cursor stop word he)).2.2.2 source
                (fun i _ hi => ha i (Finset.mem_Ico.mpr ⟨Nat.zero_le _, hi⟩)))).2.2.1
        next hn => exact ha.elim
    rw [event]
    exact MeasurableSet.iUnion measurable_A
  have boundCount : completionCount maxTrue fuel h ≤ 2 ^ h := by
    unfold completionCount
    simpa [BoundedRunName] using (Fintype.card_subtype_le
      (fun w : Fin h → Bool => runAdmissible maxTrue fuel h w = true))
  have positiveCount : 0 < completionCount maxTrue fuel h := bounded_run_level_pos _ _ _
  refine ⟨⟨fun run => (forward tape run).2.2.1, backward tape h fuel cursor stop word⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro he
    rcases forward tape (backward tape h fuel cursor stop word he) with
      ⟨legal, bound, _, transport⟩
    have causal : ∀ other : Tape,
        (∀ i, cursor ≤ i → i < stop → other i = tape i) →
          sample maxTrue other fuel h cursor = some (word, stop) := by
      intro other agree
      exact (forward other (transport other agree)).2.2.1
    refine ⟨legal, bound, causal, ?_⟩
    have event : traceCylinder cursor stop tape ∩
        {other | sample maxTrue other fuel h cursor = some (word, stop)} =
          traceCylinder cursor stop tape := by
      apply Set.inter_eq_left.mpr
      intro other hc
      apply causal other
      intro i hlo hhi
      exact hc i (Finset.mem_Ico.mpr ⟨hlo, hhi⟩)
    rw [event, traceCylinder, fairTape,
      Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
    simp [fairBit]

  · intro t x
    exact drawRun h (completionCount maxTrue fuel h) cursor t x tape
  · intro t x hx
    exact firstHitLaw h (completionCount maxTrue fuel h) cursor t boundCount x hx
  · intro x hx
    exact valueLaw h (completionCount maxTrue fuel h) cursor boundCount x hx
  · exact noneLaw h (completionCount maxTrue fuel h) cursor positiveCount boundCount
  · intro q hq
    subst h
    have numerator_le : completionCount maxTrue maxTrue q ≤
        completionCount maxTrue fuel (q + 1) := by
      unfold completionCount
      cases fuel with
      | zero => rw [bounded_run_name_card_zero]
      | succ f => rw [bounded_run_name_card_succ]; omega
    exact thresholdLaw (q + 1) (completionCount maxTrue fuel (q + 1)) cursor
      (completionCount maxTrue maxTrue q) boundCount numerator_le
  · refine ⟨measurableReturn word stop, ?_⟩
    have event : {source | ∃ final, sample maxTrue source fuel h cursor = some (word, final)} =
        ⋃ final, {source | sample maxTrue source fuel h cursor = some (word, final)} := by
      ext source
      simp
    rw [event]
    exact MeasurableSet.iUnion (measurableReturn word)
  · let : MeasurableSpace (Option ((Fin h → Bool) × ℕ)) := ⊤
    change Measurable (fun source => sample maxTrue source fuel h cursor)
    apply measurable_to_countable'
    intro result
    cases result with
    | none =>
        have event : {source | sample maxTrue source fuel h cursor = none} =
            (⋃ returned : Fin h → Bool, ⋃ final : ℕ,
              {source | sample maxTrue source fuel h cursor = some (returned, final)})ᶜ := by
          ext source
          simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
          cases he : sample maxTrue source fuel h cursor with
          | none => simp
          | some result =>
              rcases result with ⟨returned, final⟩
              simp
        change MeasurableSet {source | sample maxTrue source fuel h cursor = none}
        rw [event]
        exact (MeasurableSet.iUnion fun returned =>
          MeasurableSet.iUnion (measurableReturn returned)).compl
    | some result =>
        rcases result with ⟨returned, final⟩
        exact measurableReturn returned final
  · intro illegal
    have event : {source | ∃ final, sample maxTrue source fuel h cursor = some (word, final)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro source ⟨final, he⟩
      have legal := (forward source (backward source h fuel cursor final word he)).1
      rw [illegal] at legal
      contradiction
    rw [event, measure_empty]
  · filter_upwards [allDraws] with source available
    have returns : ∀ (g f c : ℕ), ∃ returned : Fin g → Bool, ∃ final : ℕ,
        sample maxTrue source f g c = some (returned, final) := by
      intro g
      induction g with
      | zero =>
          intro f c
          exact ⟨fun i => Fin.elim0 i, c, rfl⟩
      | succ g ih =>
          intro f c
          cases hd : draw (g + 1) (completionCount maxTrue f (g + 1)) c source with
          | none => exact (available (g + 1) f c hd).elim
          | some result =>
              rcases result with ⟨t, x⟩
              let bit := decide (completionCount maxTrue maxTrue g ≤ x.val)
              rcases ih (if bit then f - 1 else maxTrue) (c + (t + 1) * (g + 1)) with
                ⟨tail, final, ht⟩
              refine ⟨Fin.cons bit tail, final, ?_⟩
              simp only [sample, hd]
              change (match sample maxTrue source (if bit then f - 1 else maxTrue) g
                (c + (t + 1) * (g + 1)) with
                | none => none
                | some (tail, final) => some (Fin.cons (α := fun _ => Bool) bit tail, final)) = _
              rw [ht]
    rcases returns h fuel cursor with ⟨returned, final, he⟩
    refine ⟨returned, final, he, ?_⟩
    exact (forward source (backward source h fuel cursor final returned he)).1

end D5.S0.Tower.DBonacci.TerminalSampling

#print axioms D5.S0.Tower.DBonacci.TerminalSampling.terminal_sampling_execution_cylinders
#print axioms D5.S0.Tower.DBonacci.TerminalSampling.draw
#print axioms D5.S0.Tower.DBonacci.TerminalSampling.sample
