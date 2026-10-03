/- GID: D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absorbing marker execution transports independent-seed alternating cylinders. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Process.HittingTime
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

/-- False selects the left arm, true the right arm. Histories are newest first. -/
abbrev Side := Bool
abbrev Path := ℕ → Bool
abbrev Source := Bool × (Path × Path)

structure Policy (Seed : Type*) [MeasurableSpace Seed] where
  choose : Seed → List Side → List Bool → Side
  measurable_section : ∀ actions replies, Measurable (fun u => choose u actions replies)

def sideCount (actions : List Side) (side : Side) : ℕ := actions.count side

def arm (source : Source) (side : Side) : Path :=
  if side then source.2.2 else source.2.1

def endpoint (source : Source) (side : Side) : ℕ → Bool
  | 0 => source.1
  | n + 1 => arm source side n

def markerResponse (source : Source) (side : Side) (count : ℕ) : Bool :=
  decide (endpoint source side count = false ∧ arm source side count = false)

def noAdjacentOnes (source : Source) : Prop :=
  ∀ side count, ¬(endpoint source side count = true ∧ arm source side count = true)

structure State where
  actions : List Side
  replies : List Bool
  stopped : Bool
  deriving DecidableEq

/-- Stopped states reject further queries without reading the policy or source. -/
def actualRun {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (seed : Seed) (source : Source) : ℕ → State
  | 0 => ⟨[], [], false⟩
  | n + 1 =>
      let state := actualRun policy seed source n
      if state.stopped then state else
        let side := policy.choose seed state.actions state.replies
        let response := markerResponse source side (sideCount state.actions side)
        ⟨side :: state.actions, response :: state.replies, response⟩

/-- Counterfactual action replay has no source or hidden-parameter argument. -/
def zeroReplay {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (seed : Seed) : ℕ → List Side
  | 0 => []
  | n + 1 =>
      let actions := zeroReplay policy seed n
      policy.choose seed actions (List.replicate n false) :: actions

def actualQueryCount {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (seed : Seed) (source : Source) (n : ℕ) : ℕ :=
  (actualRun policy seed source n).actions.length

/-- The first actual stopped state, with infinity if no marker is ever acquired. -/
def stoppingTime {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (seed : Seed) (source : Source) : WithTop ℕ :=
  by
    classical
    exact if h : ∃ n, (actualRun policy seed source n).stopped = true then
      (Nat.find h : WithTop ℕ) else ⊤

def prefixNoMarker (source : Source) (actions : List Side) : Prop :=
  ∀ side i, i < sideCount actions side → markerResponse source side i = false

def alternatingPrefixes (source : Source) (actions : List Side) : Prop :=
  ∀ side i, i < sideCount actions side →
    endpoint source side i ≠ arm source side i

/-- Causal replay identifies actual survival and the acquired trace; stopped cost is absorbing. -/
theorem stopped_execution_replay_bridge
    {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed) (seed : Seed)
    (source : Source) (n : ℕ) :
    ((n : WithTop ℕ) < stoppingTime policy seed source ↔
      prefixNoMarker source (zeroReplay policy seed n)) ∧
    ((actualRun policy seed source n).stopped = false ↔
      prefixNoMarker source (zeroReplay policy seed n)) ∧
    ((actualRun policy seed source n).stopped = false →
      (actualRun policy seed source n).actions = zeroReplay policy seed n ∧
      (actualRun policy seed source n).replies = List.replicate n false ∧
      actualQueryCount policy seed source n = n) ∧
    ((actualRun policy seed source n).stopped = true →
      ∀ k, actualRun policy seed source (n + k) = actualRun policy seed source n) ∧
    (noAdjacentOnes source →
      ((n : WithTop ℕ) < stoppingTime policy seed source ↔
        alternatingPrefixes source (zeroReplay policy seed n))) ∧
    ((actualQueryCount policy seed source n : WithTop ℕ) =
      min (n : WithTop ℕ) (stoppingTime policy seed source)) := by
  have hstep (actions : List Side) (side : Side) :
      prefixNoMarker source (side :: actions) ↔
        prefixNoMarker source actions ∧
          markerResponse source side (sideCount actions side) = false := by
    constructor
    · intro h
      refine ⟨fun s i hi => h s i ?_, h side (sideCount actions side) ?_⟩
      · dsimp [sideCount] at hi ⊢
        simp only [List.count_cons]
        split_ifs <;> omega
      · simp [sideCount]
    · rintro ⟨h, hs⟩ s i hi
      by_cases he : s = side
      · subst s
        by_cases hil : i < sideCount actions side
        · exact h side i hil
        · have : i = sideCount actions side := by
            dsimp [sideCount] at hi hil ⊢
            simp only [List.count_cons_self] at hi
            omega
          simpa [this] using hs
      · exact h s i (by simpa [sideCount, Ne.symm he] using hi)
  have habs (j : ℕ) (hj : (actualRun policy seed source j).stopped = true) :
      ∀ k, actualRun policy seed source (j + k) = actualRun policy seed source j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => simp [actualRun, ih, hj]
  have hcore : ∀ j,
      ((actualRun policy seed source j).stopped = false ↔
        prefixNoMarker source (zeroReplay policy seed j)) ∧
      ((actualRun policy seed source j).stopped = false →
        (actualRun policy seed source j).actions = zeroReplay policy seed j ∧
        (actualRun policy seed source j).replies = List.replicate j false ∧
        actualQueryCount policy seed source j = j) := by
    intro j
    induction j with
    | zero => simp [actualRun, zeroReplay, prefixNoMarker, sideCount, actualQueryCount]
    | succ j ih =>
      cases hp : (actualRun policy seed source j).stopped with
      | true =>
        have hg : ¬prefixNoMarker source (zeroReplay policy seed j) := by
          intro h
          have := ih.1.mpr h
          simp [hp] at this
        simp [actualRun, hp, zeroReplay, hstep, hg]
      | false =>
        obtain ⟨ha, hr, hc⟩ := ih.2 hp
        have hg := ih.1.mp hp
        simp only [actualRun, hp, Bool.false_eq_true, ↓reduceIte, zeroReplay]
        rw [ha, hr]
        constructor
        · rw [hstep]
          simp [hg]
        · intro h
          refine ⟨rfl, ?_, ?_⟩
          · simp [h, List.replicate_succ]
          · simpa only [actualQueryCount, actualRun, hp, Bool.false_eq_true,
                ↓reduceIte, List.length_cons] using congrArg Nat.succ hc
  classical
  have hfirst : (n : WithTop ℕ) < stoppingTime policy seed source ↔
      (actualRun policy seed source n).stopped = false := by
    unfold stoppingTime
    split_ifs with h
    · have hfind := Nat.find_spec h
      constructor
      · intro hn
        have hn' : n < Nat.find h := by exact_mod_cast hn
        have hnot := Nat.find_min h hn'
        cases hp : (actualRun policy seed source n).stopped <;> simp_all
      · intro hn
        have hn' : n < Nat.find h := by
          by_contra hn'
          have hle : Nat.find h ≤ n := by omega
          have he := habs (Nat.find h) hfind (n - Nat.find h)
          rw [Nat.add_sub_of_le hle] at he
          have : (actualRun policy seed source n).stopped = true := by rw [he]; exact hfind
          simp_all
        exact_mod_cast hn'
    · cases hp : (actualRun policy seed source n).stopped <;> simp_all
  refine ⟨hfirst.trans (hcore n).1, (hcore n).1, (hcore n).2, habs n, ?_, ?_⟩
  · intro hsource
    rw [hfirst, (hcore n).1]
    apply forall_congr'
    intro side
    apply forall_congr'
    intro i
    apply imp_congr_right
    intro _
    unfold markerResponse
    have hn := hsource side i
    cases hp : endpoint source side i <;> cases hb : arm source side i <;>
      simp_all
  · by_cases hn : (actualRun policy seed source n).stopped = false
    · rw [((hcore n).2 hn).2.2, min_eq_left_of_lt (hfirst.mpr hn)]
    · have hn' : (actualRun policy seed source n).stopped = true := by
        cases hb : (actualRun policy seed source n).stopped <;> simp_all
      have hex : ∃ j, (actualRun policy seed source j).stopped = true := ⟨n, hn'⟩
      have hstop := Nat.find_spec hex
      have hle : Nat.find hex ≤ n := Nat.find_min' hex hn'
      have hne : Nat.find hex ≠ 0 := by
        intro he
        rw [he] at hstop
        simp [actualRun] at hstop
      obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := Nat.exists_eq_succ_of_ne_zero hne
      have hprev : (actualRun policy seed source j).stopped = false := by
        have hnot := Nat.find_min hex (show j < Nat.find hex by omega)
        cases hb : (actualRun policy seed source j).stopped <;> simp_all
      have hcost : actualQueryCount policy seed source (Nat.find hex) = Nat.find hex := by
        rw [hj]
        simpa only [actualQueryCount, actualRun, hprev, Bool.false_eq_true,
          ↓reduceIte, List.length_cons] using congrArg Nat.succ (((hcore j).2 hprev).2.2)
      have he := habs (Nat.find hex) hstop (n - Nat.find hex)
      rw [Nat.add_sub_of_le hle] at he
      have ht : stoppingTime policy seed source = (Nat.find hex : WithTop ℕ) := by
        simp [stoppingTime, hex]
      rw [actualQueryCount, he]
      change (actualQueryCount policy seed source (Nat.find hex) : WithTop ℕ) = _
      rw [hcost, ht, min_eq_right (show (Nat.find hex : WithTop ℕ) ≤ n by exact_mod_cast hle)]


local instance : MeasurableSpace (List Bool) := ⊤

/-- One shared parameter is used at every outward transition on both arms. -/
def transition (q : unitInterval) : Kernel Bool Bool :=
  Kernel.boolKernel (bernoulliMeasure true false q) (Measure.dirac false)

instance (q : unitInterval) : IsMarkovKernel (transition q) := by
  unfold transition
  infer_instance

/-- Includes the root at time zero; each later index is one outward edge. -/
def armLaw (q : unitInterval) (root : Bool) : Measure Path :=
  Kernel.trajMeasure (Measure.dirac root)
    (fun n => (transition q).comap
      (fun u : ↥(Finset.Iic n) → Bool => u ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
      (measurable_pi_apply _))

instance (q : unitInterval) (root : Bool) : IsProbabilityMeasure (armLaw q root) := by
  unfold armLaw
  infer_instance

/-- Given root and parameter, the two outward trajectories are independent. -/
def conditionalSourceLaw (q : unitInterval) (root : Bool) : Measure Source :=
  ((armLaw q root).prod (armLaw q root)).map
    (fun p => (root, (fun i => p.1 (i + 1), fun i => p.2 (i + 1))))

instance (q : unitInterval) (root : Bool) :
    IsProbabilityMeasure (conditionalSourceLaw q root) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- Bernoulli root, followed by the two arms at the same fixed parameter. -/
def sourceLaw (alpha q : unitInterval) : Measure Source :=
  unitInterval.toNNReal alpha • conditionalSourceLaw q true +
    unitInterval.toNNReal (unitInterval.symm alpha) • conditionalSourceLaw q false

instance (alpha q : unitInterval) : IsProbabilityMeasure (sourceLaw alpha q) where
  measure_univ := by
    simp [sourceLaw]

/-- Product with the original arbitrary seed law, before any observations. -/
def jointLaw {Seed : Type*} [MeasurableSpace Seed]
    (seedLaw : Measure Seed) (alpha q : unitInterval) : Measure (Seed × Source) :=
  seedLaw.prod (sourceLaw alpha q)

instance {Seed : Type*} [MeasurableSpace Seed] (seedLaw : Measure Seed)
    [IsProbabilityMeasure seedLaw] (alpha q : unitInterval) :
    IsProbabilityMeasure (jointLaw seedLaw alpha q) := by
  unfold jointLaw
  infer_instance

def alternatingBit (root : Bool) (n : ℕ) : Bool :=
  if n % 2 = 0 then root else !root

def noMarkerCylinder (left right : ℕ) : Set Source :=
  {s | ∀ side i, i < (if side then right else left) → markerResponse s side i = false}

/-- Measured under the original seed law and defined without a source or q. -/
def lambda {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (seedLaw : Measure Seed) (m : ℕ) : ℝ :=
  seedLaw.real {u | sideCount (zeroReplay policy u (2 * m)) false % 2 = 1 ∧
    sideCount (zeroReplay policy u (2 * m)) true % 2 = 1}

set_option maxHeartbeats 800000 in
-- Trajectory support, both cylinder masses, and arbitrary-seed integration elaborate locally.
/-- Both exact tails use the original independent seed law; no posterior seed law occurs. -/
theorem adaptive_marker_stopping_tails
    {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw] (alpha q : unitInterval) :
    (∀ m : ℕ, (jointLaw seedLaw alpha q).real
      {p | ((2 * m + 1 : ℕ) : WithTop ℕ) < stoppingTime policy p.1 p.2} =
        ((alpha : ℝ) + (1 - (alpha : ℝ)) * (q : ℝ)) * (q : ℝ) ^ m) ∧
    (∀ m : ℕ, 1 ≤ m → (jointLaw seedLaw alpha q).real
      {p | ((2 * m : ℕ) : WithTop ℕ) < stoppingTime policy p.1 p.2} =
        (q : ℝ) ^ m + lambda policy seedLaw m *
          (((alpha : ℝ) + (1 - (alpha : ℝ)) * (q : ℝ) ^ 2) - (q : ℝ)) *
            (q : ℝ) ^ (m - 1)) ∧
    (∀ m : ℕ, 0 ≤ lambda policy seedLaw m ∧ lambda policy seedLaw m ≤ 1) := by
  classical
  have path_support (q : unitInterval) (root : Bool) :
      ∀ᵐ x ∂armLaw q root, x 0 = root ∧ ∀ i, ¬(x i = true ∧ x (i + 1) = true) := by
    have h0mass : armLaw q root {x | x 0 = root} = 1 := by
      have h := TrajectoryLaws.MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton
        (Measure.dirac root) (transition q) 0 (fun _ => root)
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at h
      have he : (fun (x : Path) (i : Fin 1) => x i.val) ⁻¹' {fun _ => root} =
          {x | x 0 = root} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, funext_iff]
        exact ⟨fun h => h 0, fun h i => by simpa using h⟩
      rw [he] at h
      simpa [armLaw] using h
    have h0 : ∀ᵐ x ∂armLaw q root, x 0 = root := by
      exact (ae_iff_measure_eq (by measurability)).mpr (by simpa using h0mass)
    have hstep (i : ℕ) : ∀ᵐ x ∂armLaw q root,
        ¬(x i = true ∧ x (i + 1) = true) := by
      let κ : (n : ℕ) → Kernel (↥(Finset.Iic n) → Bool) Bool :=
        fun n => (transition q).comap
          (fun u => u ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)
      have hpair : ∀ᵐ p ∂((armLaw q root).map (frestrictLe i) ⊗ₘ κ i),
          ¬(p.1 ⟨i, Finset.mem_Iic.mpr le_rfl⟩ = true ∧ p.2 = true) := by
        apply Measure.ae_compProd_of_ae_ae (by measurability)
        filter_upwards [] with u
        dsimp [κ]
        cases hb : u ⟨i, Finset.mem_Iic.mpr le_rfl⟩
        · exact Filter.Eventually.of_forall (by simp)
        · simp only [transition, Kernel.boolKernel_apply, ↓reduceIte]
          simp
      have he : (armLaw q root).map (frestrictLe i) ⊗ₘ κ i =
          (armLaw q root).map (fun x => (frestrictLe i x, x (i + 1))) :=
        Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      rw [he] at hpair
      simpa [frestrictLe] using ae_of_ae_map (by fun_prop) hpair
    filter_upwards [h0, ae_all_iff.mpr hstep] with x hx hxs
    exact ⟨hx, hxs⟩
  have arm_alternating_mass (q : unitInterval) (root : Bool) (n : ℕ) :
      armLaw q root {x | ∀ i ≤ n, x i = alternatingBit root i} =
        (unitInterval.toNNReal q : ℝ≥0∞) ^ (if root then n / 2 else (n + 1) / 2) := by
    have hs (root : Bool) (i : ℕ) :
        alternatingBit root (i + 1) = !(alternatingBit root i) := by
      rcases Nat.mod_two_eq_zero_or_one i with hi | hi
      · have hn : (i + 1) % 2 = 1 := by omega
        simp [alternatingBit, hi, hn]
      · have hn : (i + 1) % 2 = 0 := by omega
        simp [alternatingBit, hi, hn]
    have hw (root : Bool) (i : ℕ) :
        transition q (alternatingBit root i) {alternatingBit root (i + 1)} =
          if alternatingBit root i then 1 else (unitInterval.toNNReal q : ℝ≥0∞) := by
      rw [hs]
      cases hb : alternatingBit root i <;>
        simp [transition, Kernel.boolKernel_apply]
    have hp : ∀ n,
        (∏ i : Fin n, transition q (alternatingBit root i.val)
          {alternatingBit root (i.val + 1)}) =
          (unitInterval.toNNReal q : ℝ≥0∞) ^ (if root then n / 2 else (n + 1) / 2) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [ih, hw]
        rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;> cases root
        · have he : (j + 1 + 1) / 2 = (j + 1) / 2 + 1 := by omega
          simp [alternatingBit, hj, he, pow_succ]
        · have he : (j + 1) / 2 = j / 2 := by omega
          simp [alternatingBit, hj, he]
        · have he : (j + 1 + 1) / 2 = (j + 1) / 2 := by omega
          simp [alternatingBit, hj, he]
        · have he : (j + 1) / 2 = j / 2 + 1 := by omega
          simp [alternatingBit, hj, he, pow_succ]
    have h := TrajectoryLaws.MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton
      (Measure.dirac root) (transition q) n (fun i => alternatingBit root i.val)
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at h
    have he : (fun (x : Path) (i : Fin (n + 1)) => x i.val) ⁻¹'
        {fun i : Fin (n + 1) => alternatingBit root i.val} =
        {x | ∀ i ≤ n, x i = alternatingBit root i} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, funext_iff]
      exact ⟨fun h i hi => h ⟨i, by omega⟩, fun h i => h i.val (by omega)⟩
    rw [he] at h
    simp only [Fin.val_castSucc, Fin.val_succ] at h
    rw [hp] at h
    simpa [armLaw, alternatingBit] using h
  have source_cylinder_mass (alpha q : unitInterval) (left right : ℕ) :
      sourceLaw alpha q (noMarkerCylinder left right) =
        (unitInterval.toNNReal alpha : ℝ≥0∞) *
          (unitInterval.toNNReal q : ℝ≥0∞) ^ (left / 2 + right / 2) +
        (unitInterval.toNNReal (unitInterval.symm alpha) : ℝ≥0∞) *
          (unitInterval.toNNReal q : ℝ≥0∞) ^ ((left + 1) / 2 + (right + 1) / 2) := by
    classical
    have hmeas : MeasurableSet (noMarkerCylinder left right) := by
      unfold noMarkerCylinder markerResponse
      simp only [Set.ofPred_forall]
      refine MeasurableSet.iInter fun side => ?_
      refine MeasurableSet.iInter fun i => ?_
      cases i <;> cases side <;> simp only [endpoint, arm] <;> measurability
    have hs (root : Bool) (i : ℕ) :
        alternatingBit root (i + 1) = !(alternatingBit root i) := by
      rcases Nat.mod_two_eq_zero_or_one i with hi | hi
      · have hn : (i + 1) % 2 = 1 := by omega
        simp [alternatingBit, hi, hn]
      · have hn : (i + 1) % 2 = 0 := by omega
        simp [alternatingBit, hi, hn]
    have hchar (root : Bool) (x : Path) (hx0 : x 0 = root)
        (hx : ∀ i, ¬(x i = true ∧ x (i + 1) = true)) (n : ℕ) :
        (∀ i < n, ¬(x i = false ∧ x (i + 1) = false)) ↔
          ∀ i ≤ n, x i = alternatingBit root i := by
      constructor
      · intro h i hi
        induction i with
        | zero => simpa [alternatingBit] using hx0
        | succ i ih =>
          have hi' : i < n := by omega
          have hprev := ih (by omega)
          rw [hs, ← hprev]
          have hn := hx i
          have hm := h i hi'
          cases ha : x i <;> cases hb : x (i + 1) <;> simp_all
      · intro h i hi
        have hp := h i (by omega)
        have hn := h (i + 1) (by omega)
        rw [hp, hn, hs]
        cases alternatingBit root i <;> simp
    have hconditional (root : Bool) :
        conditionalSourceLaw q root (noMarkerCylinder left right) =
          (unitInterval.toNNReal q : ℝ≥0∞) ^
            ((if root then left / 2 else (left + 1) / 2) +
              (if root then right / 2 else (right + 1) / 2)) := by
      unfold conditionalSourceLaw
      rw [Measure.map_apply (by fun_prop) hmeas]
      let A (n : ℕ) : Set Path := {x | ∀ i ≤ n, x i = alternatingBit root i}
      have he : (fun p : Path × Path =>
          (root, (fun i => p.1 (i + 1), fun i => p.2 (i + 1)))) ⁻¹'
            noMarkerCylinder left right =ᵐ[(armLaw q root).prod (armLaw q root)]
            A left ×ˢ A right := by
        have hpaths : ∀ᵐ p ∂(armLaw q root).prod (armLaw q root),
            (p.1 0 = root ∧ ∀ i, ¬(p.1 i = true ∧ p.1 (i + 1) = true)) ∧
            (p.2 0 = root ∧ ∀ i, ¬(p.2 i = true ∧ p.2 (i + 1) = true)) := by
          apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
          filter_upwards [path_support q root] with x hx
          filter_upwards [path_support q root] with y hy
          exact ⟨hx, hy⟩
        filter_upwards [hpaths] with p hp
        have hL := hchar root p.1 hp.1.1 hp.1.2 left
        have hR := hchar root p.2 hp.2.1 hp.2.2 right
        have hend (side : Bool) (i : ℕ) :
            endpoint (root, (fun j => p.1 (j + 1), fun j => p.2 (j + 1))) side i =
              if side then p.2 i else p.1 i := by
          cases i <;> cases side <;> simp [endpoint, arm, hp.1.1, hp.2.1]
        apply propext
        change ((root, (fun i => p.1 (i + 1), fun i => p.2 (i + 1))) ∈
            noMarkerCylinder left right ↔ p.1 ∈ A left ∧ p.2 ∈ A right)
        simp only [noMarkerCylinder, Set.mem_ofPred_eq, markerResponse, hend, arm,
          Bool.forall_bool, Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not, A]
        exact and_congr hL hR
      rw [measure_congr he, Measure.prod_prod]
      dsimp [A]
      rw [arm_alternating_mass, arm_alternating_mass, pow_add]
    simp only [sourceLaw, Measure.add_apply, Measure.smul_apply]
    rw [hconditional true, hconditional false]
    rfl
  have hchoose : Measurable (fun p : Seed × (List Bool × List Bool) =>
      policy.choose p.1 p.2.1 p.2.2) :=
    measurable_from_prod_countable_left fun ar => policy.measurable_section ar.1 ar.2
  have hrep : ∀ n, Measurable (fun u => zeroReplay policy u n) := by
    intro n
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      exact (measurable_of_countable (fun p : Bool × List Bool => p.1 :: p.2)).comp
        ((hchoose.comp (measurable_id.prodMk (ih.prodMk measurable_const))).prodMk ih)
  have hlen (u : Seed) : ∀ n, (zeroReplay policy u n).length = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simpa [zeroReplay] using congrArg Nat.succ ih
  have hcounts (actions : List Bool) :
      sideCount actions false + sideCount actions true = actions.length := by
    induction actions with
    | nil => simp [sideCount]
    | cons side actions ih =>
        cases side <;>
          simpa [sideCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using congrArg Nat.succ ih
  have hdepth (u : Seed) (n : ℕ) :
      sideCount (zeroReplay policy u n) false +
        sideCount (zeroReplay policy u n) true = n := by rw [hcounts, hlen]
  have hmeasCylinder (left right : ℕ) : MeasurableSet (noMarkerCylinder left right) := by
    unfold noMarkerCylinder markerResponse
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun side => ?_
    refine MeasurableSet.iInter fun i => ?_
    cases i <;> cases side <;> simp only [endpoint, arm] <;> measurability
  have hroute (source : Source) (actions : List Bool) :
      prefixNoMarker source actions ↔ source ∈
        noMarkerCylinder (sideCount actions false) (sideCount actions true) := by
    simp [prefixNoMarker, noMarkerCylinder, Bool.forall_bool]
  have hjoint (n : ℕ) : jointLaw seedLaw alpha q
      {p | (n : WithTop ℕ) < stoppingTime policy p.1 p.2} =
        ∫⁻ u, sourceLaw alpha q
          (noMarkerCylinder (sideCount (zeroReplay policy u n) false)
            (sideCount (zeroReplay policy u n) true)) ∂seedLaw := by
    have he : {p : Seed × Source | (n : WithTop ℕ) < stoppingTime policy p.1 p.2} =
        {p | prefixNoMarker p.2 (zeroReplay policy p.1 n)} := by
      ext p
      exact (stopped_execution_replay_bridge policy p.1 p.2 n).1
    have hp : {p : Seed × Source | prefixNoMarker p.2 (zeroReplay policy p.1 n)} =
        ⋃ actions : List Bool, {u | zeroReplay policy u n = actions} ×ˢ
          {s | prefixNoMarker s actions} := by
      ext p
      simp
    have hmeas : MeasurableSet {p : Seed × Source |
        prefixNoMarker p.2 (zeroReplay policy p.1 n)} := by
      rw [hp]
      apply MeasurableSet.iUnion
      intro actions
      apply MeasurableSet.prod ((hrep n) (measurableSet_singleton actions))
      have he' : {s | prefixNoMarker s actions} =
          noMarkerCylinder (sideCount actions false) (sideCount actions true) := by
        ext s
        exact hroute s actions
      rw [he']
      exact hmeasCylinder _ _
    rw [he, jointLaw, Measure.prod_apply hmeas]
    apply lintegral_congr
    intro u
    congr 1
    ext s
    exact hroute s (zeroReplay policy u n)
  have hoddMeas (m : ℕ) : MeasurableSet
      {u | sideCount (zeroReplay policy u (2 * m)) false % 2 = 1 ∧
        sideCount (zeroReplay policy u (2 * m)) true % 2 = 1} := by
    apply MeasurableSet.inter
    · exact measurableSet_eq_fun
        ((measurable_of_countable (fun actions => sideCount actions false % 2)).comp
          (hrep (2 * m))) measurable_const
    · exact measurableSet_eq_fun
        ((measurable_of_countable (fun actions => sideCount actions true % 2)).comp
          (hrep (2 * m))) measurable_const
  refine ⟨?_, ?_, fun m => ⟨measureReal_nonneg, measureReal_le_one⟩⟩
  · intro m
    have hv (u : Seed) : sourceLaw alpha q
        (noMarkerCylinder (sideCount (zeroReplay policy u (2 * m + 1)) false)
          (sideCount (zeroReplay policy u (2 * m + 1)) true)) =
        ((unitInterval.toNNReal alpha : ℝ≥0∞) +
          (unitInterval.toNNReal (unitInterval.symm alpha) : ℝ≥0∞) *
            (unitInterval.toNNReal q : ℝ≥0∞)) * (unitInterval.toNNReal q : ℝ≥0∞) ^ m := by
      rw [source_cylinder_mass]
      have hd := hdepth u (2 * m + 1)
      rcases Nat.mod_two_eq_zero_or_one
        (sideCount (zeroReplay policy u (2 * m + 1)) false) with hl | hl <;>
      rcases Nat.mod_two_eq_zero_or_one
        (sideCount (zeroReplay policy u (2 * m + 1)) true) with hr | hr
      · omega
      · have hk : sideCount (zeroReplay policy u (2 * m + 1)) false / 2 +
            sideCount (zeroReplay policy u (2 * m + 1)) true / 2 = m := by omega
        have hc : (sideCount (zeroReplay policy u (2 * m + 1)) false + 1) / 2 +
            (sideCount (zeroReplay policy u (2 * m + 1)) true + 1) / 2 = m + 1 := by omega
        rw [hk, hc, pow_succ]
        ring
      · have hk : sideCount (zeroReplay policy u (2 * m + 1)) false / 2 +
            sideCount (zeroReplay policy u (2 * m + 1)) true / 2 = m := by omega
        have hc : (sideCount (zeroReplay policy u (2 * m + 1)) false + 1) / 2 +
            (sideCount (zeroReplay policy u (2 * m + 1)) true + 1) / 2 = m + 1 := by omega
        rw [hk, hc, pow_succ]
        ring
      · omega
    have h := hjoint (2 * m + 1)
    rw [lintegral_congr hv, lintegral_const, measure_univ, mul_one] at h
    have hreal := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)] at hreal
    simpa [measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_pow, unitInterval.coe_symm_eq] using hreal
  · intro m hm
    let E : Set Seed := {u | sideCount (zeroReplay policy u (2 * m)) false % 2 = 1 ∧
      sideCount (zeroReplay policy u (2 * m)) true % 2 = 1}
    have hE : MeasurableSet E := hoddMeas m
    let oddMass : ℝ≥0∞ := ((unitInterval.toNNReal alpha : ℝ≥0∞) +
      (unitInterval.toNNReal (unitInterval.symm alpha) : ℝ≥0∞) *
        (unitInterval.toNNReal q : ℝ≥0∞) ^ 2) * (unitInterval.toNNReal q : ℝ≥0∞) ^ (m - 1)
    have hv (u : Seed) : sourceLaw alpha q
        (noMarkerCylinder (sideCount (zeroReplay policy u (2 * m)) false)
          (sideCount (zeroReplay policy u (2 * m)) true)) =
        E.piecewise (fun _ => oddMass) (fun _ => (unitInterval.toNNReal q : ℝ≥0∞) ^ m) u := by
      rw [source_cylinder_mass]
      have hd := hdepth u (2 * m)
      by_cases hu : u ∈ E
      · have hl := hu.1
        have hr := hu.2
        have hk : sideCount (zeroReplay policy u (2 * m)) false / 2 +
            sideCount (zeroReplay policy u (2 * m)) true / 2 = m - 1 := by omega
        have hc : (sideCount (zeroReplay policy u (2 * m)) false + 1) / 2 +
            (sideCount (zeroReplay policy u (2 * m)) true + 1) / 2 = (m - 1) + 2 := by omega
        rw [Set.piecewise_eq_of_mem E _ _ hu, hk, hc, pow_add]
        dsimp [oddMass]
        ring
      · rw [Set.piecewise_eq_of_notMem E _ _ hu]
        have hnot : ¬(sideCount (zeroReplay policy u (2 * m)) false % 2 = 1 ∧
            sideCount (zeroReplay policy u (2 * m)) true % 2 = 1) := hu
        have hl := Nat.mod_two_eq_zero_or_one (sideCount (zeroReplay policy u (2 * m)) false)
        have hr := Nat.mod_two_eq_zero_or_one (sideCount (zeroReplay policy u (2 * m)) true)
        have hk : sideCount (zeroReplay policy u (2 * m)) false / 2 +
            sideCount (zeroReplay policy u (2 * m)) true / 2 = m := by omega
        have hc : (sideCount (zeroReplay policy u (2 * m)) false + 1) / 2 +
            (sideCount (zeroReplay policy u (2 * m)) true + 1) / 2 = m := by omega
        rw [hk, hc, ← add_mul]
        simp [← ENNReal.coe_add]
    have h := hjoint (2 * m)
    rw [lintegral_congr hv, lintegral_piecewise hE, setLIntegral_const,
      setLIntegral_const] at h
    have hreal := congrArg ENNReal.toReal h
    have hc : seedLaw.real Eᶜ = 1 - seedLaw.real E := by
      have hc := measureReal_add_measureReal_compl (μ := seedLaw) hE
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at hc
      change seedLaw.real E + seedLaw.real Eᶜ = 1 at hc
      linarith
    have hoddfinite : oddMass ≠ ⊤ := by dsimp [oddMass]; finiteness
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hreal
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow] at hreal
    have hoddreal : oddMass.toReal =
        ((alpha : ℝ) + (1 - (alpha : ℝ)) * (q : ℝ) ^ 2) * (q : ℝ) ^ (m - 1) := by
      dsimp [oddMass]
      rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp [ENNReal.toReal_mul, ENNReal.toReal_pow, unitInterval.coe_symm_eq]
    rw [hoddreal] at hreal
    change (jointLaw seedLaw alpha q).real
        {p | ((2 * m : ℕ) : WithTop ℕ) < stoppingTime policy p.1 p.2} =
        ((alpha : ℝ) + (1 - (alpha : ℝ)) * (q : ℝ) ^ 2) * (q : ℝ) ^ (m - 1) *
          seedLaw.real E + (q : ℝ) ^ m * seedLaw.real Eᶜ at hreal
    rw [hc] at hreal
    rw [hreal]
    change _ = (q : ℝ) ^ m + seedLaw.real E *
      (((alpha : ℝ) + (1 - (alpha : ℝ)) * (q : ℝ) ^ 2) - (q : ℝ)) * (q : ℝ) ^ (m - 1)
    have hpow : (q : ℝ) ^ m = (q : ℝ) * (q : ℝ) ^ (m - 1) := by
      calc
        (q : ℝ) ^ m = (q : ℝ) ^ ((m - 1) + 1) := by congr 1; omega
        _ = (q : ℝ) * (q : ℝ) ^ (m - 1) := by rw [pow_succ]; ring
    rw [hpow]
    ring


end D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails
