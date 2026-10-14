/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/LowerRateLimit
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/LowerRateLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual weight-fifty-eight choices and fixed-reset codebooks give the lower rate limit. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
import Mathlib.Topology.Order.LiminfLimsup

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral StrictSupply ResetCodebook ResetFactors ActualCountRateBridge InteriorRoot
    NestedPressureLimit MemoryGraph Operations SpectralBoundary
open Filter
open scoped Topology

/-- The two complete low words, in the original inside-to-outside execution order. -/
def lowReturns (choice : Bool) : List Return :=
  if choice then [⟨2, 1, by decide, by decide⟩, ⟨1, 1, by decide, by decide⟩]
  else [⟨1, 1, by decide, by decide⟩, ⟨2, 1, by decide, by decide⟩]

/-- An arbitrary finite choice of the two complete words. -/
def lowChoices {q : ℕ} (z : Fin q → Bool) : List Return :=
  (List.ofFn (fun i => lowReturns (z i))).flatten

private theorem low_word_geometry (choice : Bool) :
    executionWord (lowReturns choice) = lowBlock choice ∧
    listWeight (lowReturns choice) = 58 ∧
    (∀ a ∈ lowReturns choice, a.r = 1) := by
  cases choice <;> simp [lowReturns, lowBlock, executionWord, listWeight]

private theorem low_choice_geometry (q : ℕ) :
    Function.Injective (lowChoices (q := q)) ∧
    ∀ z : Fin q → Bool, listWeight (lowChoices z) = q * 58 ∧
      ∀ a ∈ lowChoices z, a.r = 1 := by
  have append (xs ys : List Return) :
      executionWord (xs ++ ys) = executionWord xs ++ executionWord ys := by
    induction xs with
    | nil => simp [executionWord]
    | cons a xs ih => simp [executionWord, ih, List.append_assoc]
  have flatten (ws : List (List Return)) :
      executionWord ws.flatten = (ws.map executionWord).flatten := by
    induction ws with
    | nil => rfl
    | cons w ws ih => simp only [List.flatten_cons, List.map_cons, append, ih]
  have weight (zs : List Bool) :
      wordWeight ((zs.map lowBlock).flatten) = zs.length * 58 := by
    induction zs with
    | nil => simp [wordWeight]
    | cons z zs ih =>
      have w : wordWeight (lowBlock z) = 58 := by
        rw [← (low_word_geometry z).1, complete_execution_word_parser.2.2.2.1]
        exact (low_word_geometry z).2.1
      simp only [List.map_cons, List.flatten_cons, word_weight_geometry.1, w, ih,
        List.length_cons]
      omega
  let block : Bool → {w : List CuLetter // wordWeight w = 58} := fun z =>
    ⟨lowBlock z, by cases z <;> rfl⟩
  have bi : Function.Injective block := by
    intro x y h
    have v := congrArg Subtype.val h
    cases x <;> cases y <;> simp [block, lowBlock] at v ⊢
  have letters (z : Fin q → Bool) :
      executionWord (lowChoices z) = ((List.ofFn z).map lowBlock).flatten := by
    simp only [lowChoices, flatten, List.map_ofFn, Function.comp_def,
      (low_word_geometry _).1]
  refine ⟨?_, ?_⟩
  · intro z z' h
    have he := congrArg executionWord h
    rw [letters, letters] at he
    have blocks : (((List.ofFn z).map block).map Subtype.val).flatten =
        (((List.ofFn z').map block).map Subtype.val).flatten := by
      simpa only [List.map_map, Function.comp_def, block] using he
    have recovered := equal_weight_concatenation_injective 58 (by decide) blocks
    have choices := List.map_injective_iff.mpr bi recovered
    exact List.ofFn_injective choices
  · intro z
    constructor
    · rw [← complete_execution_word_parser.2.2.2.1, letters, weight, List.length_ofFn]
    · intro a ha
      obtain ⟨w, hw, ha⟩ := List.mem_flatten.mp ha
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hw
      rw [← hi] at ha
      exact (low_word_geometry (z i)).2.2 a ha

private theorem low_trace (xs : List Return) (K : ℕ) (d D : ℝ) (strict : Bool)
    (hK : 2 ≤ K) (low : ∀ a ∈ xs, a.r = 1) :
    GuardTrace K d strict .high xs D := by
  induction xs generalizing D with
  | nil => trivial
  | cons a xs ih =>
    have r := low a (by simp)
    refine ⟨by omega, fun h => False.elim (by omega), ?_⟩
    exact ih _ (fun a ha => low a (by simp [ha]))

/-- Every finite binary choice is a strict actual complete list from either
original start, with original tails and no future errors. The weight-zero
choice is included in the actual strict and weak count bounds. -/
theorem actual_low_choice_count (model : Model) (o : Ownership) (b : ℝ)
    (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) (q : ℕ) :
    Function.Injective (lowChoices (q := q)) ∧
    Function.Injective (fun z : Fin q → Bool => history model (lowChoices z)) ∧
    (∀ z : Fin q → Bool,
      listWeight (lowChoices z) = q * 58 ∧
      ActualPairSupply model o b .strict (lowChoices z)) ∧
    (∀ strict : Bool, 2 ^ q ≤ actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict (q * 58))
        := by
  classical
  have geometry := low_choice_geometry q
  refine ⟨geometry.1, (complete_execution_word_parser.2.2.2.2 model).comp geometry.1, ?_, ?_⟩
  · intro z
    exact ⟨(geometry.2 z).1,
      (actual_strict_record_supply model o b (lowChoices z) K hK hqb hbp).1.mpr
        (low_trace _ K _ _ true hK (geometry.2 z).2)⟩
  · intro strict
    let f : (Fin q → Bool) → ActualDictionary model K ((lam - b) / g ^ 2 / chi ^ K) strict (q *
        58) :=
      fun z => ⟨lowChoices z, low_trace _ K _ _ strict hK (geometry.2 z).2, (geometry.2 z).1⟩
    let := (actual_dictionary_bound model K ((lam - b) / g ^ 2 / chi ^ K) strict (q * 58) (by
        omega)).1
    have injective : Function.Injective f := fun _ _ he =>
      geometry.1 (congrArg Subtype.val he)
    simpa only [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_bool,
      Fintype.card_fun, Fintype.card_fin, actualCount] using Nat.card_le_card_of_injective f
          injective

/-- Positivity is derived from actual strict word counts at the original
weight fifty-eight, for both starts and both guard flags. -/
theorem actual_rate_positive (model : Model) (o : Ownership) (b : ℝ)
    (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) (strict : Bool) :
    (1:ℝ) / 58 ≤ actualRate model K ((lam - b) / g ^ 2 / chi ^ K) strict := by
  have bounds := actual_log_rate_bounds model K ((lam - b) / g ^ 2 / chi ^ K) strict (by omega)
  apply le_limsup_of_frequently_le _ bounds.2
  apply frequently_atTop.mpr
  intro t
  let q := t + 1
  have qp : 0 < q := by dsimp [q]; omega
  refine ⟨q * 58, by dsimp [q]; omega, ?_⟩
  have count := (actual_low_choice_count model o b K hK hqb hbp q).2.2.2 strict
  have log := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (pow_pos (by norm_num : (0:ℝ)<2) q)
    (by exact_mod_cast count.trans (Nat.le_max_right 1 _) :
      (2:ℝ) ^ q ≤ ((max 1 (actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict (q * 58)) :
          ℕ) : ℝ))
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ)<2), mul_one] at log
  change (1:ℝ) / 58 ≤ Real.logb 2 ((max 1 (actualCount model K _ strict (q * 58)) : ℕ) : ℝ) /
    ((q * 58 : ℕ) : ℝ)
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

/-- The actual weak limsup has an unbounded positive-count sequence. Only a
finite prefix of the limsup selection is removed. -/
private theorem actual_positive_limsup_sequence (model : Model) (o : Ownership) (b : ℝ)
    (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    ∃ N : ℕ → ℕ, Tendsto N atTop atTop ∧
      (∀ j, 0 < N j ∧ 1 ≤ actualCount model K ((lam - b) / g ^ 2 / chi ^ K) false (N j)) ∧
      Tendsto (fun j => Real.logb 2 (actualCount model K ((lam - b) / g ^ 2 / chi ^ K) false (N
          j) : ℝ) /
        (N j : ℝ)) atTop (𝓝 (eta_b K b)) := by
  let d := (lam - b) / g ^ 2 / chi ^ K
  have bounds := actual_log_rate_bounds model K d false (by omega)
  have cobounded : IsCoboundedUnder (· ≤ ·) atTop (actualLogRate model K d false) :=
    (isBoundedUnder_of_eventually_ge
    (Eventually.of_forall bounds.1)).isCoboundedUnder_le
  obtain ⟨M, rate, unbounded⟩ := exists_seq_tendsto_limsup cobounded bounds.2
  have positive : 0 < actualRate model K d false :=
    lt_of_lt_of_le (by norm_num) (actual_rate_positive model o b K hK hqb hbp false)
  have eventuallyPositive : ∀ᶠ j in atTop, 0 < actualLogRate model K d false (M j) :=
    rate.eventually (eventually_gt_nhds positive)
  have eventuallyNonempty : ∀ᶠ j in atTop,
      0 < M j ∧ 1 ≤ actualCount model K d false (M j) := by
    filter_upwards [eventuallyPositive] with j hj
    constructor
    · by_contra h
      have zero : M j = 0 := by omega
      simp [actualLogRate, zero] at hj
    · by_contra h
      have zero : actualCount model K d false (M j) = 0 := by omega
      simp [actualLogRate, zero] at hj
  obtain ⟨j0, hj0⟩ := eventually_atTop.mp eventuallyNonempty
  let N := fun j => M (j + j0)
  have property (j : ℕ) : 0 < N j ∧ 1 ≤ actualCount model K d false (N j) :=
    hj0 _ (by omega)
  refine ⟨N, unbounded.comp (tendsto_add_atTop_nat j0), property, ?_⟩
  have shifted := rate.comp (tendsto_add_atTop_nat j0)
  have bridge := (original_actual_count_rate_bridge o b K hK hqb hbp).2.1 model false
  change actualRate model K d false = eta_b K b at bridge
  change limsup (actualLogRate model K d false) atTop = eta_b K b at bridge
  rw [bridge] at shifted
  apply shifted.congr'
  exact Eventually.of_forall (fun j => by
    simp only [Function.comp_def, N, actualLogRate, max_eq_right (property j).2]
    rfl)

/-- The full finite actual and bilateral auxiliary objects for one fixed
original weak dictionary. The same memory is used at every bilateral choice
and every finite power. -/
structure FixedCodebook (R : Return) (o : Ownership) (b : ℝ) (K : ℕ)
    (sourceModel : Model) (N : ℕ) : Prop where
  delta_pos : 0 < hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) - initial .high
      sourceModel
  gain_pos : 0 < (hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) - initial .high
      sourceModel) * g ^ N
  error_pos : 0 < min (b - actualAutomaticCost K)
    (g ^ 2 * chi ^ K * ((hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) - initial
        .high sourceModel) * g ^ N)) / 2
  finite : Finite (ActualDictionary sourceModel K ((lam - b) / g ^ 2 / chi ^ K) false N)
  actual : ∀ (targetModel : Model)
    (words : List (ActualDictionary sourceModel K ((lam - b) / g ^ 2 / chi ^ K) false N)),
    let d := (lam - b) / g ^ 2 / chi ^ K
    let gain := (hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) - initial .high
        sourceModel) * g ^ N
    let execution := resetConcatenation R (words.map Subtype.val)
    GuardTrace K (d + gain) false .high execution (initial .high targetModel) ∧
    ActualPairSupply targetModel o
      (b - min (b - actualAutomaticCost K) (g ^ 2 * chi ^ K * gain) / 2) .strict execution
  memory :
    let d := (lam - b) / g ^ 2 / chi ^ K
    let gain := (hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) - initial .high
        sourceModel) * g ^ N
    let V := ActualDictionary sourceModel K d false N
    let L := N + 20 + 6 * R.m
    ∃ n : ℕ, K ≤ n ∧ hSide .high * rho ^ n < chi ^ (K - 1) * gain ∧
      (∀ choices : ℤ → V,
        let W := fun j => executionWord (R::(choices j).val)
        ∃ ω : ℤ → CuLetter,
          ω ∈ AuxiliaryLanguage K (d + gain) ∧ ω ∈ LowerMemoryLanguage n K d ∧
          (∀ j (k : Fin (W j).length), ω (blockCut W j + (k : ℕ)) = (W j)[k]) ∧
          (∀ j, GuardTrace K (d + gain) false .high (R::(choices j).val)
            (pastState ω (blockCut W j)))) ∧
      (∀ q : ℕ,
        let f := fun z : Fin q → V => resetFactor R (List.ofFn (fun i => (z i).val))
        Function.Injective f ∧
        (∀ z, wordWeight (f z) = q * L ∧
          ∃ ω ∈ LowerMemoryLanguage n K d, Occurs ω (f z)) ∧
        (∃ family : Finset (List CuLetter), family.card = Nat.card V ^ q ∧
          (∀ w, w ∈ family ↔ ∃ z, f z = w) ∧
          (∀ w ∈ family, wordWeight w = q * L ∧
            ∃ ω ∈ LowerMemoryLanguage n K d, Occurs ω w)) ∧
        Nat.card V ^ q ≤ factorCount (LowerMemoryLanguage n K d) (q * L)) ∧
      Real.logb 2 ((max 1 (Nat.card V) : ℕ) : ℝ) / (L : ℝ) ≤
        weightedFactorRate (LowerMemoryLanguage n K d)

/-- A single reset, fixed before all original source weights, gives full
positive-count codebooks whose slopes approach the original actual rate. -/
theorem original_count_codebook_approximation (o : Ownership) (b : ℝ)
    (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    ∃ R : Return, R.r = 1 ∧
      max (max (xSide .high) (ySide .high)) ((lam - b) / g ^ 2 / chi ^ K) <
        hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) ∧
      ∀ model : Model, ∃ N : ℕ → ℕ, Tendsto N atTop atTop ∧
        (∀ j, 0 < N j ∧ 1 ≤ actualCount model K ((lam - b) / g ^ 2 / chi ^ K) false (N j)) ∧
        Tendsto (fun j => Real.logb 2 (actualCount model K ((lam - b) / g ^ 2 / chi ^ K) false
            (N j) : ℝ) /
          (N j : ℝ)) atTop (𝓝 (eta_b K b)) ∧
        Tendsto (fun j => (N j : ℝ) / ((N j + 20 + 6 * R.m : ℕ) : ℝ)) atTop (𝓝 1) ∧
        Tendsto (fun j => Real.logb 2 (actualCount model K ((lam - b) / g ^ 2 / chi ^ K) false
            (N j) : ℝ) /
          ((N j + 20 + 6 * R.m : ℕ) : ℝ)) atTop (𝓝 (eta_b K b)) ∧
        (∀ j, FixedCodebook R o b K model (N j)) := by
  obtain ⟨R, hr, floor, books⟩ := same_reset_factor_cardinality o b K hK hqb hbp
  refine ⟨R, hr, floor, ?_⟩
  intro model
  obtain ⟨N, unbounded, positive, rate⟩ := actual_positive_limsup_sequence model o b K hK hqb hbp
  have small : Tendsto (fun j => (20 + 6 * R.m : ℝ) / (N j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (20 + 6 * R.m : ℝ) |>.comp unbounded
  have ratio : Tendsto (fun j => (N j : ℝ) / ((N j + 20 + 6 * R.m : ℕ) : ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).div
      (tendsto_const_nhds.add small)
      (by norm_num : (1:ℝ) + 0 ≠ 0)
    simp only [add_zero, div_one] at h
    apply h.congr'
    exact Eventually.of_forall (fun j => by
      have nz : (N j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (positive j).1)
      dsimp only [Pi.div_apply]
      push_cast
      field_simp
      ring)
  refine ⟨N, unbounded, positive, rate, ratio, ?_, ?_⟩
  · have product := rate.mul ratio
    simp only [mul_one] at product
    apply product.congr'
    exact Eventually.of_forall (fun j => by
      have nz : (N j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (positive j).1)
      field_simp)
  · intro j
    obtain ⟨dp, gp, ep, finite, joint, memory⟩ := books model (N j) (positive j).1
    exact ⟨dp, gp, ep, finite, joint, memory⟩

/-- The original lower-memory rates increase and upper-memory rates decrease
to the same original actual rate. For each accuracy, one positive-count
dictionary is fixed before its memory is selected; its bound then holds at
every larger memory. The spectral roots use exactly the original real
threshold and the n-at-least-K convention on both memory sides. -/
theorem original_lower_rate_limit (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    (1:ℝ) / 58 ≤ eta_b K b ∧
    Monotone (fun n => weightedFactorRate
      (MemoryLanguage .lower n K ((lam - b) / g ^ 2 / chi ^ K))) ∧
    (∀ epsilon : ℝ, 0 < epsilon → ∃ n0 : ℕ, K ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → eta_b K b - epsilon < weightedFactorRate
        (MemoryLanguage .lower n K ((lam - b) / g ^ 2 / chi ^ K)) ∧
        weightedFactorRate (MemoryLanguage .lower n K ((lam - b) / g ^ 2 / chi ^ K)) ≤ eta_b K b) ∧
    Tendsto (fun n => weightedFactorRate
      (MemoryLanguage .lower n K ((lam - b) / g ^ 2 / chi ^ K))) atTop (𝓝 (eta_b K b)) ∧
    ∃ roots : MemorySide → ℕ → ℝ,
      (∀ side n, K ≤ n → 0 < roots side n ∧ roots side n < 1 ∧
        weightedRadius side n K ((lam - b) / g ^ 2 / chi ^ K) (roots side n) = 1 ∧
        weightedFactorRate (MemoryLanguage side n K ((lam - b) / g ^ 2 / chi ^ K)) =
          -Real.logb 2 (roots side n)) ∧
      (∀ n, K ≤ n →
        -Real.logb 2 (roots .lower n) ≤ eta_b K b ∧
        eta_b K b ≤ -Real.logb 2 (roots .upper n)) ∧
      MonotoneOn (fun n => -Real.logb 2 (roots .lower n)) (Set.Ici K) ∧
      AntitoneOn (fun n => -Real.logb 2 (roots .upper n)) (Set.Ici K) ∧
      Tendsto (fun n => -Real.logb 2 (roots .upper n)) atTop (𝓝 (eta_b K b)) ∧
      Tendsto (fun n => -Real.logb 2 (roots .lower (n + K))) atTop (𝓝 (eta_b K b)) ∧
      (∀ model strict,
        actualRate model K ((lam - b) / g ^ 2 / chi ^ K) strict = eta_b K b) := by
  let d := (lam - b) / g ^ 2 / chi ^ K
  let lower := fun n => weightedFactorRate (MemoryLanguage .lower n K d)
  obtain ⟨roots, properties, sandwich, lowerMono, upperMono, upperLimit, actualRates⟩ :=
    original_upper_root_limit o b K hK hqb hbp
  have bridge := (original_actual_count_rate_bridge o b K hK hqb hbp).1
  have etaPositive : (1:ℝ) / 58 ≤ eta_b K b := by
    rw [← (original_actual_count_rate_bridge o b K hK hqb hbp).2.1 .original false]
    exact actual_rate_positive .original o b K hK hqb hbp false
  have mono : Monotone lower := monotone_nat_of_le_succ
    (fun n => (original_memory_rate_nesting n K d).1)
  have upper (n : ℕ) : lower n ≤ eta_b K b := by
    have h := (mono (Nat.le_succ n)).trans (original_memory_rate_nesting n K d).2.1
    exact h.trans_eq bridge
  obtain ⟨R, hr, floor, approximations⟩ := original_count_codebook_approximation o b K hK hqb hbp
  obtain ⟨N, unbounded, positive, normalized, ratio, rate, books⟩ := approximations .original
  have approximate (a : ℝ) (ha : a < eta_b K b) :
      ∃ n0 : ℕ, K ≤ n0 ∧ ∀ n, n0 ≤ n → a < lower n := by
    obtain ⟨j, hj⟩ := (rate.eventually (eventually_gt_nhds ha)).exists
    obtain ⟨n, hn, small, bilateral, powers, slope⟩ := (books j).memory
    have codebook : Real.logb 2 (actualCount .original K d false (N j) : ℝ) /
        ((N j + 20 + 6 * R.m : ℕ) : ℝ) ≤ lower n := by
      change Real.logb 2 ((max 1 (actualCount .original K d false (N j)) : ℕ) : ℝ) /
        ((N j + 20 + 6 * R.m : ℕ) : ℝ) ≤ lower n at slope
      have cp : 1 ≤ actualCount .original K d false (N j) := (positive j).2
      rw [max_eq_right cp] at slope
      exact slope
    refine ⟨max K n, le_max_left _ _, ?_⟩
    intro m hm
    exact hj.trans_le (codebook.trans (mono ((le_max_right K n).trans hm)))
  have limit : Tendsto lower atTop (𝓝 (eta_b K b)) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      obtain ⟨n, hn, above⟩ := approximate a ha
      exact eventually_atTop.mpr ⟨n, above⟩
    · intro a ha
      exact Eventually.of_forall (fun n => (upper n).trans_lt ha)
  refine ⟨etaPositive, mono, ?_, limit, ?_⟩
  · intro epsilon he
    obtain ⟨n, hn, above⟩ := approximate (eta_b K b - epsilon) (by linarith)
    exact ⟨n, hn, fun m hm => ⟨above m hm, upper m⟩⟩
  · refine ⟨roots, properties, sandwich, lowerMono, upperMono, upperLimit, ?_, actualRates⟩
    have shifted := limit.comp (tendsto_add_atTop_nat K)
    apply shifted.congr'
    exact Eventually.of_forall (fun n => (properties .lower (n + K) (by omega)).2.2.2)

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit
