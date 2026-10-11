/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A bounded seven-fair-bit service has exact rejection and return laws. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFiniteMonitor
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.ProductMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFairBitService
open FourthSegmentStoppedLaw RarePriorFiniteMonitor
open scoped NNReal ENNReal Topology
open Filter

abbrev Packet := Letter × Letter × Letter × Letter × Letter × Letter × Letter

def packetEquiv : Packet ≃ Fin 128 :=
  let e₂ : (Letter × Letter) ≃ Fin 4 := finProdFinEquiv
  let e₃ := (Equiv.prodCongr (Equiv.refl Letter) e₂).trans finProdFinEquiv
  let e₄ := (Equiv.prodCongr (Equiv.refl Letter) e₃).trans finProdFinEquiv
  let e₅ := (Equiv.prodCongr (Equiv.refl Letter) e₄).trans finProdFinEquiv
  let e₆ := (Equiv.prodCongr (Equiv.refl Letter) e₅).trans finProdFinEquiv
  (Equiv.prodCongr (Equiv.refl Letter) e₆).trans finProdFinEquiv

def packetBits (p : Packet) : List Letter :=
  [p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2.1,p.2.2.2.2.2.2]

inductive Threshold where
  | ordinary | high | low
  deriving DecidableEq

instance : Fintype Threshold := ⟨{.ordinary,.high,.low}, by intro t; cases t <;> simp⟩

def threshold : Threshold → Fin 101
  | .ordinary => 40
  | .high => 90
  | .low => 1

def selectedThreshold (z : Runtime) : Threshold :=
  match queryMode z with | .g => .high | .gBeta => .low | _ => .ordinary

inductive PC where
  | reset | bit | compare | returned
  deriving DecidableEq

instance : Fintype PC := ⟨{.reset,.bit,.compare,.returned}, by intro p; cases p <;> simp⟩

@[ext] structure Service where
  thresholdTag : Threshold
  pc : PC
  bitPosition : Fin 7
  candidate : Fin 128
  output : Letter
  deriving DecidableEq, Fintype

def entry (t : Threshold) : Service := ⟨t,.reset,0,0,0⟩

/-- Only the bit instruction reads randomness. Reset and comparison are deterministic. -/
def microStep (s : Service) (b : Letter) : Service :=
  match s.pc with
  | .reset => { s with pc := .bit, bitPosition := 0, candidate := 0, output := 0 }
  | .bit =>
      let c : Fin 128 := ⟨(2*s.candidate.val+b.val)%128, Nat.mod_lt _ (by decide)⟩
      if h : s.bitPosition.val < 6 then
        { s with bitPosition := ⟨s.bitPosition.val+1, by omega⟩, candidate := c }
      else { s with pc := .compare, candidate := c }
  | .compare =>
      if s.candidate.val < 100 then
        { s with pc := .returned, output :=
            (if s.candidate.val < (threshold s.thresholdTag).val then 0 else 1) }
      else { s with pc := .reset, bitPosition := 0, candidate := 0, output := 0 }
  | .returned => s

def bitEntry (t : Threshold) : Service := microStep (entry t) 0

def collectPacket (t : Threshold) (p : Packet) : Service :=
  (packetBits p).foldl microStep (bitEntry t)

/-- Seven sequential bits form the explicit binary candidate; no rational-coin instruction exists. -/
theorem seven_bit_candidate (t : Threshold) (p : Packet) :
    collectPacket t p = ⟨t,.compare,6,packetEquiv p,0⟩ := by
  rcases p with ⟨a,b,c,d,e,f,g⟩
  apply Service.ext <;>
    simp [collectPacket, packetBits, bitEntry, entry, microStep, packetEquiv,
      finProdFinEquiv, Fin.ext_iff]
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
  have hd := d.isLt; have he := e.isLt; have hf := f.isLt; have hg := g.isLt
  omega

/-- Rejection clears both bounded registers; acceptance returns the prescribed threshold color. -/
theorem packet_transaction (t : Threshold) (p : Packet) :
    microStep (collectPacket t p) 0 =
      if (packetEquiv p).val < 100 then
        ⟨t,.returned,6,packetEquiv p,
          if (packetEquiv p).val < (threshold t).val then 0 else 1⟩
      else entry t := by
  rw [seven_bit_candidate]
  simp [microStep, entry]

/-- Transition weights use only zero, one half and one. -/
def microWeight (s q : Service) : ℚ :=
  if s.pc = .bit then
    (if microStep s 0 = q then 1/2 else 0) + (if microStep s 1 = q then 1/2 else 0)
  else if microStep s 0 = q then 1 else 0

theorem microstep_weights (s q : Service) :
    microWeight s q = 0 ∨ microWeight s q = 1/2 ∨ microWeight s q = 1 := by
  unfold microWeight
  split
  · by_cases h0 : microStep s 0 = q <;> by_cases h1 : microStep s 1 = q <;>
      simp [h0,h1] <;> norm_num
  · split <;> simp

noncomputable def fairParameter : unitInterval := ⟨1/2, by norm_num, by norm_num⟩

/-- The installed packet mass is the product of seven fresh fair-bit masses. -/
theorem fair_packet_mass (p : Packet) :
    wordMass fairParameter (packetBits p) = 1/128 := by
  rcases p with ⟨a,b,c,d,e,f,g⟩
  have h (x : Letter) :
      (ProbabilityTheory.bernoulliMeasure (0 : Letter) 1 fairParameter) {x} = 1/2 := by
    fin_cases x
    · rw [ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem fairParameter
        (measurableSet_singleton _) (by decide) (by decide)]
      change ((1/2 : ℝ≥0) : ℝ≥0∞) = 1/2
      simp [ENNReal.coe_div]
    · rw [ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem fairParameter
        (measurableSet_singleton _) (by decide) (by decide)]
      have hp : unitInterval.toNNReal (unitInterval.symm fairParameter) = (1/2:ℝ≥0) := by
        apply Subtype.ext
        change 1 - (1/2 : ℝ) = ((1/2 : ℝ≥0) : ℝ)
        norm_num
      rw [hp]
      simp [ENNReal.coe_div]
  simp only [wordMass, packetBits, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, h, mul_one, one_div]
  calc
    _ = (2⁻¹ : ℝ≥0∞)^7 := by ring
    _ = _ := by rw [← ENNReal.inv_pow]; norm_num

/-- The bijection counts every bit packet, including all rejected candidates. -/
noncomputable def packetRejectMass : ℝ :=
  ∑ p : Packet, if 100 ≤ (packetEquiv p).val then 1/128 else 0

noncomputable def packetAlphaMass (t : Threshold) : ℝ :=
  ∑ p : Packet, if (packetEquiv p).val < (threshold t).val then 1/128 else 0

private theorem rejection_count : packetRejectMass = 7/32 := by
  unfold packetRejectMass
  rw [Equiv.sum_comp packetEquiv (fun k : Fin 128 =>
    if 100 ≤ k.val then (1/128 : ℝ) else 0)]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun k : Fin 128 => 100 ≤ k.val) = Finset.Ici (100 : Fin 128) := by
    ext k; simp [Fin.le_def]
  rw [hf]
  norm_num [Fin.card_Ici]

private theorem acceptance_count (t : Threshold) :
    packetAlphaMass t = (threshold t).val/128 := by
  unfold packetAlphaMass
  rw [Equiv.sum_comp packetEquiv (fun k : Fin 128 =>
    if k.val < (threshold t).val then (1/128 : ℝ) else 0)]
  rw [← Finset.sum_filter]
  let k : Fin 128 := ⟨(threshold t).val, by have h := (threshold t).isLt; omega⟩
  have hf : Finset.univ.filter (fun j : Fin 128 => j.val < (threshold t).val) = Finset.Iio k := by
    ext j; simp [Fin.lt_def, k]
  rw [hf]
  simp [Fin.card_Iio, k]
  ring

/-- Finite survival and first-return masses are obtained by repeatedly executing the reset branch. -/
noncomputable def survivalMass : ℕ → ℝ
  | 0 => 1
  | m+1 => ∑ p : Packet,
      if 100 ≤ (packetEquiv p).val then (1/128)*survivalMass m else 0

noncomputable def firstAlphaMass (t : Threshold) (m : ℕ) : ℝ := survivalMass m * packetAlphaMass t

noncomputable def returnedAlphaMass (t : Threshold) : ℝ := ∑' m : ℕ, firstAlphaMass t m

/-- Every rejected round has probability 7/32, and no retry count occurs in Service. -/
theorem survival_geometric (m : ℕ) : survivalMass m = (7/32)^m := by
  induction m with
  | zero => simp [survivalMass]
  | succ m ih =>
      simp only [survivalMass]
      have he : (∑ p : Packet,
          if 100 ≤ (packetEquiv p).val then (1/128)*survivalMass m else 0) =
          packetRejectMass * survivalMass m := by
        rw [packetRejectMass, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _
        split <;> simp
      rw [he, rejection_count, ih, pow_succ]
      ring

/-- The total return masses and the zero limiting survival are consequences of the fair-bit graph. -/
theorem exact_service_law :
    returnedAlphaMass .ordinary = 2/5 ∧ returnedAlphaMass .high = 9/10 ∧
    returnedAlphaMass .low = 1/100 ∧
    Tendsto survivalMass atTop (𝓝 0) := by
  have hs : Summable (fun m : ℕ => (7/32 : ℝ)^m) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have ht : ∑' m : ℕ, (7/32 : ℝ)^m = (1-(7/32 : ℝ))⁻¹ :=
    tsum_geometric_of_abs_lt_one (by norm_num)
  have he (t : Threshold) : returnedAlphaMass t = (threshold t).val/100 := by
    simp only [returnedAlphaMass, firstAlphaMass, survival_geometric, acceptance_count]
    rw [tsum_mul_right, ht]
    ring
  refine ⟨?_,?_,?_,?_⟩
  · convert he .ordinary using 1 <;> norm_num [threshold]
  · convert he .high using 1 <;> norm_num [threshold]
  · simpa [threshold] using he .low
  · have hf : survivalMass = fun n => (7/32 : ℝ)^n := funext survival_geometric
    rw [hf]
    exact
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 7/32)
        (by norm_num : (7/32:ℝ) < 1))

open MeasureTheory ProbabilityTheory Set

noncomputable def packetLaw : Measure Packet :=
  let f := bernoulliMeasure (0 : Letter) 1 fairParameter
  f.prod (f.prod (f.prod (f.prod (f.prod (f.prod f)))))

instance : IsProbabilityMeasure packetLaw := by unfold packetLaw; infer_instance

theorem packet_law_singleton (p : Packet) : packetLaw {p} = (1/128 : ℝ≥0∞) := by
  rw [← fair_packet_mass p]
  rcases p with ⟨a,b,c,d,e,f,g⟩
  simp only [packetLaw, ← singleton_prod_singleton, Measure.prod_prod,
    wordMass, packetBits, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]

def rejectedPackets : Finset Packet := Finset.univ.filter (fun p => 100 ≤ (packetEquiv p).val)

private theorem packet_rejection_probability : packetLaw rejectedPackets = (7/32 : ℝ≥0∞) := by
  rw [← sum_measure_singleton]
  simp only [packet_law_singleton, Finset.sum_const]
  have hc : rejectedPackets.card = 28 := by
    unfold rejectedPackets
    have hm : (Finset.univ.filter (fun p : Packet => 100 ≤ (packetEquiv p).val)).map
        packetEquiv.toEmbedding = Finset.Ici (100 : Fin 128) := by
      ext k
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.toEmbedding_apply, Finset.mem_Ici, Fin.le_def]
      constructor
      · rintro ⟨p, hp, rfl⟩; exact hp
      · intro hk; exact ⟨packetEquiv.symm k, by simpa using hk, by simp⟩
    have hcard := congrArg Finset.card hm
    simpa [Finset.card_map, Fin.card_Ici] using hcard
  rw [hc]
  simp only [nsmul_eq_mul, one_div]
  change (28 : ℝ≥0∞) * 128⁻¹ = 7 / 32
  rw [← ENNReal.coe_ofNat 28, ← ENNReal.coe_ofNat 128, ← ENNReal.coe_ofNat 7,
    ← ENNReal.coe_ofNat 32, ← ENNReal.coe_inv, ← ENNReal.coe_mul, ← ENNReal.coe_div]
  all_goals norm_num

noncomputable def packetStreamLaw : Measure (ℕ → Packet) := Measure.infinitePi (fun _ => packetLaw)

instance : IsProbabilityMeasure packetStreamLaw := by unfold packetStreamLaw; infer_instance

def survives (m : ℕ) : Set (ℕ → Packet) :=
  Set.pi (Finset.range m) (fun _ => (rejectedPackets : Set Packet))

/-- These are actual stream-cylinder survival probabilities of repeated rejected fair packets. -/
theorem actual_survival_probability (m : ℕ) :
    packetStreamLaw (survives m) = (7/32 : ℝ≥0∞)^m := by
  rw [packetStreamLaw, survives, Measure.infinitePi_pi (fun _ => packetLaw)]
  · simp [packet_rejection_probability]
  · intro i hi; exact (rejectedPackets.finite_toSet.measurableSet)

/-- The infinite rejection event has zero mass, retaining the event in the output domain. -/
theorem almost_sure_service_return : packetStreamLaw (⋂ m : ℕ, survives m) = 0 := by
  have hm : Antitone survives := by
    intro i j hij ω hj k hk
    exact hj k (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hij))
  have hs (m : ℕ) : MeasurableSet (survives m) := by
    exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ =>
      rejectedPackets.finite_toSet.measurableSet)
  have he := tendsto_measure_iInter_atTop (fun m => (hs m).nullMeasurableSet) hm
    ⟨0, measure_ne_top packetStreamLaw _⟩
  have hz : Tendsto (fun m => packetStreamLaw (survives m)) atTop (𝓝 0) := by
    simp only [actual_survival_probability]
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by
      rw [← ENNReal.coe_ofNat 7, ← ENNReal.coe_ofNat 32, ← ENNReal.coe_div,
        ← ENNReal.coe_one, ENNReal.coe_lt_coe] <;> norm_num)
  exact tendsto_nhds_unique he hz

def alphaPackets (t : Threshold) : Finset Packet :=
  Finset.univ.filter (fun p => (packetEquiv p).val < (threshold t).val)

private theorem packet_alpha_probability (t : Threshold) :
    packetLaw (alphaPackets t) = ((threshold t).val : ℝ≥0∞)/128 := by
  rw [← sum_measure_singleton]
  simp only [packet_law_singleton, Finset.sum_const, nsmul_eq_mul]
  have hc : (alphaPackets t).card = (threshold t).val := by
    unfold alphaPackets
    let k : Fin 128 := ⟨(threshold t).val, by have h := (threshold t).isLt; omega⟩
    have hm : (Finset.univ.filter (fun p : Packet => (packetEquiv p).val < (threshold t).val)).map
        packetEquiv.toEmbedding = Finset.Iio k := by
      ext j
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.toEmbedding_apply, Finset.mem_Iio, Fin.lt_def]
      constructor
      · rintro ⟨p, hp, rfl⟩; exact hp
      · intro hj; exact ⟨packetEquiv.symm j, by simpa [k] using hj, by simp⟩
    have hcard := congrArg Finset.card hm
    simpa [Finset.card_map, Fin.card_Iio, k] using hcard
  rw [hc]
  simp [div_eq_mul_inv]

def alphaReturnEvent (t : Threshold) (m : ℕ) : Set (ℕ → Packet) :=
  Set.pi (Finset.range (m+1)) (fun i =>
    if i = m then (alphaPackets t : Set Packet) else (rejectedPackets : Set Packet))

private theorem alpha_return_cylinder (t : Threshold) (m : ℕ) :
    packetStreamLaw (alphaReturnEvent t m) =
      (7/32 : ℝ≥0∞)^m * ((threshold t).val : ℝ≥0∞)/128 := by
  rw [packetStreamLaw, alphaReturnEvent, Measure.infinitePi_pi (fun _ => packetLaw)]
  · rw [Finset.prod_range_succ]
    have he : (∏ i ∈ Finset.range m, packetLaw
        (if i = m then (alphaPackets t : Set Packet) else (rejectedPackets : Set Packet))) =
        (7/32 : ℝ≥0∞)^m := by
      calc
        _ = ∏ i ∈ Finset.range m, (7/32 : ℝ≥0∞) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hn : i ≠ m := by have := Finset.mem_range.mp hi; omega
          simp [hn, packet_rejection_probability]
        _ = _ := by simp
    rw [he]
    simp [packet_alpha_probability, mul_div_assoc]
  · intro i hi
    split
    · exact (alphaPackets t).finite_toSet.measurableSet
    · exact rejectedPackets.finite_toSet.measurableSet

private theorem alpha_events_disjoint (t : Threshold) :
    Pairwise (fun i j => Disjoint (alphaReturnEvent t i) (alphaReturnEvent t j)) := by
  have bad (i j : ℕ) (hlt : i < j) (ω : ℕ → Packet)
      (hi : ω ∈ alphaReturnEvent t i) (hj : ω ∈ alphaReturnEvent t j) : False := by
    have ha : (packetEquiv (ω i)).val < (threshold t).val := by
      have h := hi i (Finset.mem_range.mpr (by omega))
      simpa [alphaPackets] using h
    have hr : 100 ≤ (packetEquiv (ω i)).val := by
      have h := hj i (Finset.mem_range.mpr (by omega))
      simpa [ne_of_lt hlt, rejectedPackets] using h
    have ht := (threshold t).isLt
    omega
  intro i j hij
  rw [Set.disjoint_left]
  intro ω hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact bad i j h ω hi hj
  · exact bad j i h ω hj hi

/-- The measured output event is the disjoint union of actual first accepting packet cylinders. -/
theorem actual_service_output_law (t : Threshold) :
    packetStreamLaw (⋃ m : ℕ, alphaReturnEvent t m) =
      ENNReal.ofReal (returnedAlphaMass t) := by
  rw [measure_iUnion (alpha_events_disjoint t)]
  · simp only [alpha_return_cylinder]
    have he (m : ℕ) : (7/32 : ℝ≥0∞)^m * ((threshold t).val : ℝ≥0∞)/128 =
        ENNReal.ofReal (firstAlphaMass t m) := by
      rw [firstAlphaMass, survival_geometric, acceptance_count]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
      have hc : ENNReal.ofReal (((threshold t).val : ℝ)/128) =
          ((threshold t).val : ℝ≥0∞)/128 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        simp
      rw [hc]
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      simp [mul_div_assoc]
    simp only [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by
      rw [firstAlphaMass, survival_geometric, acceptance_count]; positivity)]
    · rfl
    · have hs : Summable (fun m : ℕ => (7/32 : ℝ)^m) :=
        summable_geometric_of_lt_one (by norm_num) (by norm_num)
      have hf : firstAlphaMass t = fun m => (7/32 : ℝ)^m * packetAlphaMass t :=
        funext (fun m => by rw [firstAlphaMass,survival_geometric])
      rw [hf]
      exact hs.mul_right _
  · intro m
    exact MeasurableSet.pi (Finset.countable_toSet _) (fun i hi => by
      split
      · exact (alphaPackets t).finite_toSet.measurableSet
      · exact rejectedPackets.finite_toSet.measurableSet)

/-- A paused bit instruction consumes precisely its remaining fresh bits.
    Reset consumes seven, comparison consumes none, and returned is absorbing. -/
def finishTrial (s : Service) (p : Packet) : Service :=
  match s.pc with
  | .reset => microStep (collectPacket s.thresholdTag p) 0
  | .bit => microStep ((packetBits p).take (7-s.bitPosition.val) |>.foldl microStep s) 0
  | .compare => microStep s 0
  | .returned => s

private theorem remaining_bit_progress (s : Service) (p : Packet) (hp : s.pc = .bit) :
    (((packetBits p).take (7-s.bitPosition.val)).foldl microStep s).pc = .compare ∧
    (((packetBits p).take (7-s.bitPosition.val)).foldl microStep s).thresholdTag = s.thresholdTag := by
  rcases s with ⟨t,pc,i,c,o⟩
  cases hp
  rcases p with ⟨a,b,d,e,f,g,h⟩
  fin_cases i <;> simp [packetBits, microStep]

private theorem compare_trial (s : Service) (hp : s.pc = .compare) :
    (microStep s 0).pc = .returned ∨ microStep s 0 = entry s.thresholdTag := by
  rcases s with ⟨t,pc,i,c,o⟩
  cases hp
  by_cases h : c.val < 100 <;> simp [microStep, h, entry]

private theorem finite_trial_dichotomy (s : Service) (p : Packet) :
    (finishTrial s p).pc = .returned ∨ ∃ t, finishTrial s p = entry t := by
  cases hp : s.pc with
  | reset =>
    simp only [finishTrial, hp]
    rw [packet_transaction]
    split <;> simp [entry]
  | bit =>
    simp only [finishTrial, hp]
    have hc := remaining_bit_progress s p hp
    rcases compare_trial _ hc.1 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨_,h⟩
  | compare =>
    simp only [finishTrial, hp]
    rcases compare_trial s hp with h | h
    · exact Or.inl h
    · exact Or.inr ⟨_,h⟩
  | returned => exact Or.inl (by simpa [finishTrial, hp] using hp)

/-- Iteration is an analysis of execution; its index is absent from Service. -/
def trialRun (s : Service) (ω : ℕ → Packet) : ℕ → Service
  | 0 => s
  | m+1 => finishTrial (trialRun s ω m) (ω m)

def neverReturns (s : Service) : Set (ℕ → Packet) :=
  {ω | ∀ m : ℕ, (trialRun s ω (m+1)).pc ≠ .returned}

def tailSurvives (m : ℕ) : Set (ℕ → Packet) :=
  Set.pi ((Finset.range m).image (fun i => i+1)) (fun _ => rejectedPackets)

private theorem tail_survival_probability (m : ℕ) :
    packetStreamLaw (tailSurvives m) = (7/32 : ℝ≥0∞)^m := by
  rw [packetStreamLaw, tailSurvives, Measure.infinitePi_pi (fun _ => packetLaw)]
  · simp only [packet_rejection_probability, Finset.prod_const]
    rw [Finset.card_image_of_injective _ (fun i j h => Nat.add_right_cancel h), Finset.card_range]
  · intro i hi; exact rejectedPackets.finite_toSet.measurableSet

private theorem tail_infinite_rejection_zero : packetStreamLaw (⋂ m : ℕ, tailSurvives m) = 0 := by
  have hm : Antitone tailSurvives := by
    intro i j hij ω hω k hk
    exact hω k ((Finset.image_mono (fun i : ℕ => i+1) (Finset.range_mono hij)) hk)
  have hs (m : ℕ) : MeasurableSet (tailSurvives m) :=
    MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ =>
      rejectedPackets.finite_toSet.measurableSet)
  have he := tendsto_measure_iInter_atTop (fun m => (hs m).nullMeasurableSet) hm
    ⟨0, measure_ne_top packetStreamLaw _⟩
  have hz : Tendsto (fun m => packetStreamLaw (tailSurvives m)) atTop (𝓝 0) := by
    simp only [tail_survival_probability]
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by
      rw [← ENNReal.coe_ofNat 7, ← ENNReal.coe_ofNat 32, ← ENNReal.coe_div,
        ← ENNReal.coe_one, ENNReal.coe_lt_coe] <;> norm_num)
  exact tendsto_nhds_unique he hz

/-- Every allowed paused microstate, including partial candidates, returns almost surely. -/
theorem every_microstate_returns (s : Service) : packetStreamLaw (neverReturns s) = 0 := by
  have hsub : neverReturns s ⊆ ⋂ m : ℕ, tailSurvives m := by
    intro ω hω
    apply Set.mem_iInter.mpr
    intro m i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    have hc : ∃ t, trialRun s ω (j+1) = entry t := by
      rcases finite_trial_dichotomy (trialRun s ω j) (ω j) with h | h
      · exact (hω j h).elim
      · exact h
    obtain ⟨t,ht⟩ := hc
    have hn := hω (j+1)
    rw [trialRun, ht] at hn
    simp only [finishTrial, entry] at hn
    rw [packet_transaction] at hn
    by_contra hbad
    have hp : (packetEquiv (ω (j+1))).val < 100 := by
      simpa [rejectedPackets] using hbad
    simp [hp] at hn
  apply le_antisymm _ bot_le
  calc
    _ ≤ packetStreamLaw (⋂ m : ℕ, tailSurvives m) := measure_mono hsub
    _ = 0 := tail_infinite_rejection_zero

/-- The fair-bit graph realizes the three rational thresholds and terminates from every microstate. -/
theorem rational_service_realization (t : Threshold) :
    packetStreamLaw (⋃ m : ℕ, alphaReturnEvent t m) =
      ENNReal.ofReal ((threshold t).val / (100 : ℝ)) ∧
    (∀ s q : Service, microWeight s q = 0 ∨ microWeight s q = 1/2 ∨ microWeight s q = 1) ∧
    (∀ s : Service, packetStreamLaw (neverReturns s) = 0) := by
  have he : returnedAlphaMass t = (threshold t).val / (100 : ℝ) := by
    cases t
    · norm_num [threshold]; exact exact_service_law.1
    · norm_num [threshold]; exact exact_service_law.2.1
    · norm_num [threshold]; exact exact_service_law.2.2.1
  exact ⟨(actual_service_output_law t).trans (congrArg ENNReal.ofReal he),
    microstep_weights, every_microstate_returns⟩

/-- The output event refers to the actual service trajectory, not to a coin primitive. -/
def alphaOutputEvent (t : Threshold) : Set (ℕ → Packet) :=
  {ω | ∃ m : ℕ, (trialRun (entry t) ω (m+1)).pc = .returned ∧
    (trialRun (entry t) ω (m+1)).output = 0}

private def acceptedService (t : Threshold) (p : Packet) : Service :=
  ⟨t,.returned,6,packetEquiv p,if (packetEquiv p).val < (threshold t).val then 0 else 1⟩

theorem prefix_reset (t : Threshold) (ω : ℕ → Packet) (m : ℕ)
    (h : ∀ j < m, 100 ≤ (packetEquiv (ω j)).val) :
    trialRun (entry t) ω m = entry t := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [trialRun, ih (fun j hj => h j (by omega))]
    simp only [finishTrial, entry]
    rw [packet_transaction, if_neg (by have := h m (by omega); omega)]
    rfl

private theorem canonical_trace (t : Threshold) (ω : ℕ → Packet) (m : ℕ) :
    (trialRun (entry t) ω m = entry t ∧
      ∀ j < m, 100 ≤ (packetEquiv (ω j)).val) ∨
    ∃ k < m, (∀ j < k, 100 ≤ (packetEquiv (ω j)).val) ∧
      (packetEquiv (ω k)).val < 100 ∧
      trialRun (entry t) ω m = acceptedService t (ω k) := by
  induction m with
  | zero => exact Or.inl ⟨rfl,by omega⟩
  | succ m ih =>
    rcases ih with ⟨hs,hp⟩ | ⟨k,hk,hp,ha,hs⟩
    · have ht : trialRun (entry t) ω (m+1) =
          if (packetEquiv (ω m)).val < 100 then acceptedService t (ω m) else entry t := by
        rw [trialRun, hs]
        simp only [finishTrial, entry]
        exact packet_transaction t (ω m)
      by_cases ha : (packetEquiv (ω m)).val < 100
      · exact Or.inr ⟨m,by omega,hp,ha,by simpa only [ha,if_true] using ht⟩
      · refine Or.inl ⟨by simpa only [ha,if_false] using ht,?_⟩
        intro j hj
        by_cases he : j = m
        · subst j; omega
        · exact hp j (by omega)
    · refine Or.inr ⟨k,by omega,hp,ha,?_⟩
      rw [trialRun, hs]
      rfl

private theorem alpha_cylinder_membership (t : Threshold) (ω : ℕ → Packet) (m : ℕ) :
    ω ∈ alphaReturnEvent t m ↔
      (∀ j < m, 100 ≤ (packetEquiv (ω j)).val) ∧
      (packetEquiv (ω m)).val < (threshold t).val := by
  constructor
  · intro h
    constructor
    · intro j hj
      have hc := h j (Finset.mem_range.mpr (by omega))
      simpa [alphaReturnEvent, rejectedPackets, show j ≠ m by omega] using hc
    · have hc := h m (Finset.mem_range.mpr (by omega))
      simpa [alphaReturnEvent, alphaPackets] using hc
  · rintro ⟨hp,ha⟩ j hj
    have hj' := Finset.mem_range.mp hj
    by_cases he : j = m
    · subst j; simpa [alphaReturnEvent, alphaPackets] using ha
    · simpa [alphaReturnEvent, rejectedPackets, he] using hp j (by omega)

private theorem operational_alpha_event (t : Threshold) :
    alphaOutputEvent t = ⋃ m : ℕ, alphaReturnEvent t m := by
  ext ω
  constructor
  · rintro ⟨m,hpc,ho⟩
    rcases canonical_trace t ω (m+1) with ⟨hs,_⟩ | ⟨k,_,hp,_,hs⟩
    · rw [hs] at hpc; cases hpc
    · have ha : (packetEquiv (ω k)).val < (threshold t).val := by
        rw [hs] at ho
        by_contra h
        simp [acceptedService,h] at ho
      exact Set.mem_iUnion.mpr ⟨k,(alpha_cylinder_membership t ω k).mpr ⟨hp,ha⟩⟩
  · intro h
    obtain ⟨m,hm⟩ := Set.mem_iUnion.mp h
    obtain ⟨hp,ha⟩ := (alpha_cylinder_membership t ω m).mp hm
    have hth : (threshold t).val ≤ 100 := by cases t <;> decide
    have hc : (packetEquiv (ω m)).val < 100 := by omega
    have hs : trialRun (entry t) ω (m+1) = acceptedService t (ω m) := by
      rw [trialRun, prefix_reset t ω m hp]
      simp only [finishTrial, entry]
      simpa only [hc,if_true,acceptedService] using packet_transaction t (ω m)
    exact ⟨m,by rw [hs]; rfl,by rw [hs]; simp [acceptedService,ha]⟩

/-- The actual sequential-bit trajectory has exactly the computed rational output law. -/
theorem operational_service_realization (t : Threshold) :
    alphaOutputEvent t = ⋃ m : ℕ, alphaReturnEvent t m ∧
    packetStreamLaw (alphaOutputEvent t) =
      ENNReal.ofReal ((threshold t).val / (100 : ℝ)) ∧
    (∀ s q : Service, microWeight s q = 0 ∨ microWeight s q = 1/2 ∨ microWeight s q = 1) ∧
    (∀ s : Service, packetStreamLaw (neverReturns s) = 0) ∧
    packetStreamLaw (⋂ m : ℕ, survives m) = 0 := by
  rw [operational_alpha_event]
  have hr := rational_service_realization t
  exact ⟨rfl,hr.1,hr.2.1,hr.2.2,almost_sure_service_return⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFairBitService
