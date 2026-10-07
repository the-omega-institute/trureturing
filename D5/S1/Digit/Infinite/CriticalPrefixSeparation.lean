/- GID: D5/S1/Digit/Infinite/CriticalPrefixSeparation
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/CriticalPrefixSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp separation and critical recovery for actual finite-tail addresses. -/

import D5.S1.Digit.Infinite.ClosedObservationGraphRealization
import D5.S1.Digit.Infinite.OddColorThreeSource
import D5.S1.Digit.Infinite.LateLabelStateBound
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Instances.Discrete
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.CriticalPrefixSeparation

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S0.Carrier (GoldenInt)
open D5.S1.Scale (embedding)
open Filter Set
open scoped Topology

/-- The first h actual three-bit windows. -/
def windowPrefix (h : ℕ) (x : LegalDigits) : Fin h → Label := fun j => window x j

/-- The h + 1 real samples obtained by deleting three actual bits per step. -/
noncomputable def response (h : ℕ) (x : LegalDigits) : Fin (h + 1) → ℝ :=
  fun j => kappa (bitShift x (3 * j.val))

/-- The legal infinite repetition of the window five. -/
def fiveStream : LegalDigits := ⟨fun j => decide (j % 3 = 2), by
  intro j
  simp only [decide_eq_true_eq]
  omega⟩

/-- N windows five followed by an infinite empty tail. -/
def fiveRun (N : ℕ) : LegalDigits :=
  ⟨fun j => decide (j < 3 * N ∧ j % 3 = 2), by
    intro j
    simp only [decide_eq_true_eq]
    omega⟩

/-- The actual observation domain for the finite-tail closed-error contract. -/
def observations (h : ℕ) (ε : ℝ) : Set (Fin (h + 1) → ℝ) :=
  {r | ∃ x : LegalDigits, finiteTail x ∧ dist r (response h x) ≤ ε}

/-- Correctness requires every compatible source to have the returned windowPrefix. -/
def correct (h : ℕ) (ε : ℝ)
    (decode : observations h ε → (Fin h → Label)) : Prop :=
  ∀ (r : observations h ε) (x : LegalDigits), finiteTail x →
    dist r.val (response h x) ≤ ε → decode r = windowPrefix h x

theorem golden_facts : 0 < t ∧ t < 1 ∧ t ^ 2 + t = 1 ∧ 1 + g = 2 * t := by
  obtain ⟨hp, hl, hs, hg, _⟩ :=
    D5.S1.Digit.Infinite.OddColorThreeSource.golden_relations
  exact ⟨hp, hl, by linarith only [hs], by linarith only [hg]⟩

theorem residual (x : LegalDigits) (j : ℕ) :
    kappa (bitShift x (3 * j)) + g * kappa (bitShift x (3 * (j + 1))) =
      offset (window x j) := by
  have hr := (closed_observation_graph_realization.2.2.1 (bitShift x (3 * j))).1
  have hw : window (bitShift x (3 * j)) 0 = window x j := by
    simp only [window, Nat.mul_zero,
      D5.S1.Digit.Infinite.OddColorThreeSource.shift_add, Nat.add_zero]
  rw [hw] at hr
  simp only [originalT, D5.S1.Digit.Infinite.OddColorThreeSource.shift_add] at hr
  dsimp only [branch] at hr
  simp only [Nat.mul_add, Nat.mul_one]
  linarith

private theorem separation (h : ℕ) (x y : LegalDigits) (hne : windowPrefix h x ≠ windowPrefix h y) :
    t / 2 ≤ dist (response h x) (response h y) := by
  classical
  have hgap (l m : Label) (hne : l ≠ m) : t ^ 2 ≤ |offset l - offset m| := by
    have ht := golden_facts
    have hhalf : (1 : ℝ) / 2 < t :=
      D5.S1.Digit.Infinite.OddColorThreeSource.golden_relations.2.2.2.2
    have hln0 := l.property 0 (by decide)
    have hln1 := l.property 1 (by decide)
    have hmn0 := m.property 0 (by decide)
    have hmn1 := m.property 1 (by decide)
    have hext : (l.val 0 = m.val 0 ∧ l.val 1 = m.val 1 ∧ l.val 2 = m.val 2) → l = m := by
      rintro ⟨h0,h1,h2⟩
      apply Subtype.ext
      funext i
      fin_cases i <;> assumption
    simp only [Fin.reduceFinMk] at hln0 hln1 hmn0 hmn1
    cases hl0 : l.val 0 <;> cases hl1 : l.val 1 <;> cases hl2 : l.val 2 <;>
      cases hm0 : m.val 0 <;> cases hm1 : m.val 1 <;> cases hm2 : m.val 2 <;>
      simp_all only [Bool.false_eq_true, not_false_eq_true, and_self,
        and_false, false_and, and_true, true_and]
    all_goals try contradiction
    all_goals dsimp only [offset]
    all_goals simp only [hl0,hl1,hl2,hm0,hm1,hm2, Bool.false_eq_true, ↓reduceIte]
    all_goals first
      | exact (le_abs_self _).trans' (by nlinarith [ht.2.2.1])
      | exact (neg_le_abs _).trans' (by nlinarith [ht.2.2.1])
  obtain ⟨j, hj⟩ : ∃ j : Fin h, window x j ≠ window y j := by
    exact Function.ne_iff.mp hne
  let M := dist (response h x) (response h y)
  have h0 : |kappa (bitShift x (3 * j.val)) - kappa (bitShift y (3 * j.val))| ≤ M := by
    exact dist_le_pi_dist (response h x) (response h y) ⟨j.val, by omega⟩
  have h1 : |kappa (bitShift x (3 * (j.val + 1))) -
      kappa (bitShift y (3 * (j.val + 1)))| ≤ M := by
    exact dist_le_pi_dist (response h x) (response h y) ⟨j.val + 1, by omega⟩
  have hg : 0 ≤ g := (pow_pos golden_facts.1 3).le
  have hres : offset (window x j) - offset (window y j) =
      (kappa (bitShift x (3 * j.val)) - kappa (bitShift y (3 * j.val))) +
      g * (kappa (bitShift x (3 * (j.val + 1))) -
        kappa (bitShift y (3 * (j.val + 1)))) := by
    linarith [residual x j, residual y j]
  have hu : |offset (window x j) - offset (window y j)| ≤ (1 + g) * M := by
    rw [hres]
    calc
      _ ≤ |kappa (bitShift x (3 * j.val)) - kappa (bitShift y (3 * j.val))| +
          |g * (kappa (bitShift x (3 * (j.val + 1))) -
            kappa (bitShift y (3 * (j.val + 1))))| := abs_add_le _ _
      _ ≤ M + g * M := by rw [abs_mul, abs_of_nonneg hg]; gcongr
      _ = (1 + g) * M := by ring
  have hl := hgap _ _ hj
  rw [golden_facts.2.2.2] at hu
  have hp := golden_facts.1
  nlinarith

private theorem half_not_integral (z : GoldenInt) : embedding z ≠ t / 2 := by
  intro he
  have ht : t = Real.goldenRatio - 1 := by
    dsimp [t, D5.S1.Digit.Infinite.SignedSeriesRange.alpha]
    rw [Real.inv_goldenRatio, Real.goldenConj]
    dsimp [Real.goldenRatio]
    ring
  have hb : 2 * z.b - 1 ≠ 0 := by omega
  have hbr : ((2 * z.b - 1 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hφ : Real.goldenRatio = ((-2 * z.a - 1 : ℤ) : ℝ) /
      ((2 * z.b - 1 : ℤ) : ℝ) := by
    apply (eq_div_iff hbr).mpr
    rw [D5.S1.Scale.embedding_apply, ht] at he
    push_cast
    linarith
  exact Real.goldenRatio_irrational.ne_rational (-2 * z.a - 1) (2 * z.b - 1) hφ

private theorem strict_separation (h : ℕ) (x y : LegalDigits)
    (hx : finiteTail x) (hy : finiteTail y) (hne : windowPrefix h x ≠ windowPrefix h y) :
    t / 2 < dist (response h x) (response h y) := by
  classical
  have hl := separation h x y hne
  apply lt_of_le_of_ne hl
  intro he
  obtain ⟨j,hj⟩ := ((dist_pi_eq_iff (div_pos golden_facts.1 (by norm_num))).mp he.symm).1
  obtain ⟨a,ha⟩ := closed_observation_graph_realization.2.2.2.2.2.2.2.1
    (bitShift x (3 * j.val)) (D5.S1.Digit.Infinite.LateLabelStateBound.finite_shift x _ hx)
  obtain ⟨b,hb⟩ := closed_observation_graph_realization.2.2.2.2.2.2.2.1
    (bitShift y (3 * j.val)) (D5.S1.Digit.Infinite.LateLabelStateBound.finite_shift y _ hy)
  have hd : |embedding (a - b)| = t / 2 := by
    rw [map_sub]
    simpa only [response, Real.dist_eq, ha,hb] using hj
  rcases abs_cases (embedding (a - b)) with ⟨hp,hp'⟩ | ⟨hn,hn'⟩
  · exact half_not_integral (a - b) (hp.symm.trans hd)
  · exact half_not_integral (-(a - b)) (by rw [map_neg]; exact hn.symm.trans hd)

private theorem five_window (j : ℕ) : window fiveStream j = fiveLabel := by
  apply Subtype.ext
  funext i
  simp [window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift, fiveStream,
    fiveLabel, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

private theorem run_window (N j : ℕ) :
    window (fiveRun N) j = if j < N then fiveLabel else nullLabel := by
  apply Subtype.ext
  funext i
  by_cases hj : j < N
  · simp [hj, window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift, fiveRun,
      fiveLabel, show i.val + 3 * j < 3 * N by have := i.isLt; omega,
      Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  · simp [hj, window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift, fiveRun,
      nullLabel, show ¬i.val + 3 * j < 3 * N by omega]

private theorem run_finite (N : ℕ) : finiteTail (fiveRun N) := by
  refine ⟨3 * N, ?_⟩
  intro j hj
  simp [fiveRun, show ¬j < 3 * N by omega]

private theorem run_shift (N j : ℕ) :
    bitShift (fiveRun N) (3 * j) = fiveRun (N - j) := by
  apply Subtype.ext
  funext i
  simp only [bitShift, fiveRun]
  apply Bool.decide_congr
  omega

private theorem stream_shift (j : ℕ) : bitShift fiveStream (3 * j) = fiveStream := by
  apply Subtype.ext
  funext i
  simp [bitShift, fiveStream, Nat.add_mod]

private theorem zero_scalar : kappa (fiveRun 0) = 0 := by
  dsimp [kappa]
  simp [run_window, offset, nullLabel]

private theorem stream_scalar : kappa fiveStream = t / 2 := by
  have hr := residual fiveStream 0
  rw [stream_shift, stream_shift, five_window] at hr
  simp only [offset, fiveLabel, Fin.val_zero, Fin.val_one] at hr
  norm_num at hr
  have hg := golden_facts.2.2.2
  have ht := golden_facts.2.2.1
  nlinarith [golden_facts.1]

private theorem run_scalar (N : ℕ) :
    kappa (fiveRun N) = (t / 2) * (1 - (-g) ^ N) := by
  have hs : kappa (fiveRun N) = (∑ j ∈ Finset.range N, (-g) ^ j) * t ^ 2 := by
    calc
      _ = ∑ j ∈ Finset.range N, (-g) ^ j * offset (window (fiveRun N) j) := by
        apply tsum_eq_sum
        intro j hj
        rw [run_window]
        simp [show ¬j < N by simpa using hj, offset, nullLabel]
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        rw [run_window]
        simp [Finset.mem_range.mp hj, offset, fiveLabel]
  have ht := golden_facts
  have he := geom_sum_mul_neg (-g) N
  rw [hs]
  have hg : 1 - (-g) = 2 * t := by linarith [ht.2.2.2]
  rw [hg] at he
  nlinarith [ht.2.2.1]

private theorem zero_response (h : ℕ) : response h (fiveRun 0) = fun _ => 0 := by
  funext j
  simp only [response, run_shift, Nat.zero_sub, zero_scalar]

private theorem stream_response (h : ℕ) : response h fiveStream = fun _ => t / 2 := by
  funext j
  simp only [response, stream_shift, stream_scalar]

private theorem run_response (h N : ℕ) (j : Fin (h + 1)) :
    response h (fiveRun N) j = (t / 2) * (1 - (-g) ^ (N - j.val)) := by
  simp only [response, run_shift, run_scalar]

private theorem run_prefix (h N : ℕ) (hN : h ≤ N) :
    windowPrefix h (fiveRun N) = fun _ => fiveLabel := by
  funext j
  exact (run_window N j).trans (if_pos (by have := j.isLt; omega))

private theorem zero_prefix (h : ℕ) : windowPrefix h (fiveRun 0) = fun _ => nullLabel := by
  funext j
  simp only [windowPrefix, run_window, Nat.not_lt_zero, ↓reduceIte]

private theorem five_ne_null : fiveLabel ≠ nullLabel := by
  intro he
  have hh := congrArg (fun l : Label => l.val 2) he
  simp [fiveLabel,nullLabel] at hh

private theorem different_prefix (h N : ℕ) (hh : 1 ≤ h) (hN : h ≤ N) :
    windowPrefix h (fiveRun 0) ≠ windowPrefix h (fiveRun N) := by
  rw [zero_prefix, run_prefix h N hN]
  intro he
  have hx := congrFun he ⟨0, by omega⟩
  exact five_ne_null hx.symm

private theorem run_limit (h : ℕ) :
    Tendsto (fun N => response h (fiveRun N)) atTop (𝓝 (fun _ => t / 2)) := by
  have hg0 : 0 ≤ g := (pow_pos golden_facts.1 3).le
  have hg1 : g < 1 := pow_lt_one₀ golden_facts.1.le golden_facts.2.1 (by decide)
  have hp : Tendsto (fun N : ℕ => (-g) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_iff.mpr (by rwa [abs_neg, abs_of_nonneg hg0])
  apply tendsto_pi_nhds.mpr
  intro j
  simp only [run_response]
  have hl := (tendsto_const_nhds (x := t / 2)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub (hp.comp (tendsto_sub_atTop_nat j.val)))
  simpa only [sub_zero, mul_one, Function.comp_def] using hl

private theorem run_distance_limit (h : ℕ) :
    Tendsto (fun N => dist (response h (fiveRun 0)) (response h (fiveRun N)))
      atTop (𝓝 (t / 2)) := by
  have hl := (tendsto_const_nhds (x := response h (fiveRun 0))).dist (run_limit h)
  simpa only [zero_response, dist_pi_const, Real.dist_eq, zero_sub, abs_neg,
    abs_of_pos (div_pos golden_facts.1 (by norm_num : (0 : ℝ) < 2))] using hl

private theorem finite_infimum (h : ℕ) (hh : 1 ≤ h) :
    IsGLB {d : ℝ | ∃ x y : LegalDigits, finiteTail x ∧ finiteTail y ∧
      windowPrefix h x ≠ windowPrefix h y ∧ dist (response h x) (response h y) = d} (t / 2) := by
  constructor
  · rintro d ⟨x,y,hx,hy,hne,rfl⟩
    exact (strict_separation h x y hx hy hne).le
  · intro b hb
    apply ge_of_tendsto (run_distance_limit h)
    filter_upwards [eventually_ge_atTop h] with N hN
    exact hb ⟨fiveRun 0,fiveRun N,run_finite 0,run_finite N,
      different_prefix h N hh hN,rfl⟩

private theorem recovery (h : ℕ) (hh : 1 ≤ h) (ε : ℝ) (_hε : 0 ≤ ε) :
    (∃ decode : observations h ε → (Fin h → Label), correct h ε decode) ↔ ε ≤ t / 4 := by
  classical
  constructor
  · rintro ⟨decode,hd⟩
    by_contra he
    have he' : t / 2 < 2*ε := by linarith
    obtain ⟨N,hN,hdist⟩ : ∃ N : ℕ, h ≤ N ∧
        dist (response h (fiveRun 0)) (response h (fiveRun N)) < 2*ε := by
      obtain ⟨N,hN⟩ := ((run_distance_limit h).eventually (gt_mem_nhds he')).and
        (eventually_ge_atTop h) |>.exists
      exact ⟨N,hN.2,hN.1⟩
    let r := midpoint ℝ (response h (fiveRun 0)) (response h (fiveRun N))
    have hr0 : dist r (response h (fiveRun 0)) ≤ ε := by
      dsimp only [r]
      rw [dist_midpoint_left]
      norm_num
      linarith
    have hrN : dist r (response h (fiveRun N)) ≤ ε := by
      dsimp only [r]
      rw [dist_midpoint_right]
      norm_num
      linarith
    let R : observations h ε := ⟨r,fiveRun 0,run_finite 0,hr0⟩
    exact different_prefix h N hh hN
      ((hd R (fiveRun 0) (run_finite 0) hr0).symm.trans
        (hd R (fiveRun N) (run_finite N) hrN))
  · intro he
    let chosen (r : observations h ε) : LegalDigits := Classical.choose r.property
    have hc (r : observations h ε) : finiteTail (chosen r) ∧
        dist r.val (response h (chosen r)) ≤ ε := Classical.choose_spec r.property
    refine ⟨fun r => windowPrefix h (chosen r), ?_⟩
    intro r x hx hr
    by_contra hp
    have hs := strict_separation h (chosen r) x (hc r).1 hx hp
    have hu := dist_triangle (response h (chosen r)) r.val (response h x)
    rw [dist_comm (response h (chosen r)) r.val] at hu
    linarith [(hc r).2]

private theorem translated_distance (h : ℕ) (z : Fin (h + 1) → ℝ) (c : ℝ) (hc : 0 < c) :
    dist (fun j => z j - c) z = c := by
  change dist (z - fun _ => c) z = c
  rw [dist_self_sub_left, pi_norm_const, Real.norm_eq_abs, abs_of_pos hc]

private theorem critical_member (h : ℕ) :
    (fun _ : Fin (h + 1) => t / 4) ∈ observations h (t / 4) := by
  refine ⟨fiveRun 0,run_finite 0,?_⟩
  rw [zero_response, dist_pi_const, Real.dist_eq, sub_zero,
    abs_of_pos (div_pos golden_facts.1 (by norm_num))]

private theorem critical_discontinuity (h : ℕ) (hh : 1 ≤ h)
    (decode : observations h (t / 4) → (Fin h → Label)) (hd : correct h (t / 4) decode) :
    ¬ @ContinuousAt (observations h (t / 4)) (Fin h → Label) _ ⊥ decode
      ⟨fun _ => t / 4, critical_member h⟩ := by
  classical
  let : TopologicalSpace (Fin h → Label) := ⊥
  have : DiscreteTopology (Fin h → Label) := ⟨rfl⟩
  let rstar : observations h (t / 4) := ⟨fun _ => t / 4, critical_member h⟩
  let r (N : ℕ) : observations h (t / 4) :=
    ⟨fun j => response h (fiveRun (N + h)) j - t / 4, fiveRun (N + h), run_finite (N + h), by
      exact (translated_distance h _ (t / 4) (div_pos golden_facts.1 (by norm_num))).le⟩
  have hl : Tendsto r atTop (𝓝 rstar) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro j
    have hlim := (tendsto_pi_nhds.mp ((run_limit h).comp (tendsto_add_atTop_nat h)) j).sub
      (tendsto_const_nhds (x := t / 4))
    convert hlim using 1 <;> try rfl
    congr 1
    ring
  have hzero : decode rstar = windowPrefix h (fiveRun 0) := by
    apply hd rstar (fiveRun 0) (run_finite 0)
    rw [zero_response, dist_pi_const, Real.dist_eq, sub_zero,
      abs_of_pos (div_pos golden_facts.1 (by norm_num))]
  have hrun (N : ℕ) : decode (r N) = windowPrefix h (fiveRun (N + h)) :=
    hd (r N) (fiveRun (N + h)) (run_finite _)
      (translated_distance h _ (t / 4) (div_pos golden_facts.1 (by norm_num))).le
  intro hc
  have he : ∀ᶠ N in atTop, decode (r N) = decode rstar := by
    have he := hc.tendsto.comp hl
    rwa [nhds_discrete, tendsto_pure] at he
  obtain ⟨N,hN⟩ := he.exists
  exact different_prefix h (N + h) hh (by omega) (hzero.symm.trans (hN.symm.trans (hrun N)))

/-- The complete affine response with a prescribed legal terminal scalar. -/
noncomputable def affineResponse (h : ℕ) (x : LegalDigits) (a : ℝ) : Fin (h + 1) → ℝ :=
  fun j => (∑ k ∈ Finset.range (h - j.val), (-g) ^ k * offset (window x (j.val + k))) +
    (-g) ^ (h - j.val) * a

private theorem shifted_window (x : LegalDigits) (n j : ℕ) :
    window (bitShift x (3 * n)) j = window x (n + j) := by
  simp only [window, D5.S1.Digit.Infinite.OddColorThreeSource.shift_add, Nat.mul_add]

private theorem tail_guard (s : Bool) (x : LegalDigits) (n : ℕ) (hx : stateAddress s x) :
    stateAddress (actualGuard s x n) (bitShift x (3 * n)) := by
  cases n with
  | zero => simpa [actualGuard, bitShift] using hx
  | succ n =>
    have hs := (closed_observation_graph_realization.2.2.1 (bitShift x (3 * n))).2.1
    simpa [stateAddress, actualGuard, originalT, outgoing, window,
      D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift,
      show 3 * (n + 1) - 1 = 2 + 3 * n by omega,
      Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

private theorem guard_step (s : Bool) (x : LegalDigits) (n : ℕ) :
    actualGuard (outgoing (window x 0)) (originalT x) n = actualGuard s x (n + 1) := by
  cases n with
  | zero => simp [actualGuard, outgoing, window,
      D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift]
  | succ n =>
    simp only [actualGuard, Nat.succ_ne_zero, ↓reduceIte, originalT, bitShift]
    congr 1

private theorem realize_tail (h : ℕ) (s : Bool) (x z : LegalDigits)
    (hx : stateAddress s x) (hz : stateAddress (actualGuard s x h) z) :
    ∃ y : LegalDigits, stateAddress s y ∧ windowPrefix h y = windowPrefix h x ∧
      bitShift y (3 * h) = z := by
  induction h generalizing s x z with
  | zero =>
    refine ⟨z,hz,?_,?_⟩
    · ext j
      exact Fin.elim0 j
    · apply Subtype.ext
      funext i
      simp [bitShift]
  | succ h ih =>
    have hs := (closed_observation_graph_realization.2.2.1 x).2.1
    rw [← guard_step s x h] at hz
    obtain ⟨v,hv,hvp,hvt⟩ := ih (outgoing (window x 0)) (originalT x) z hs hz
    have hl : lawful s (window x 0) (outgoing (window x 0)) := by
      refine ⟨?_,rfl⟩
      intro hsg
      simpa [window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift] using hx hsg
    obtain ⟨y,⟨hy,hyw,hyt⟩,_⟩ := closed_observation_graph_realization.2.2.2.1
      s (window x 0) (outgoing (window x 0)) v hl hv
    refine ⟨y,hy,?_,?_⟩
    · funext j
      by_cases hj : j.val = 0
      · simpa [windowPrefix, hj] using hyw
      · have hk : j.val - 1 < h := by omega
        have hp := congrFun hvp ⟨j.val - 1,hk⟩
        change window v (j.val - 1) = window (originalT x) (j.val - 1) at hp
        rw [← hyt] at hp
        change window (bitShift y (3 * 1)) (j.val - 1) =
          window (bitShift x (3 * 1)) (j.val - 1) at hp
        rw [shifted_window y 1, shifted_window x 1] at hp
        simpa only [windowPrefix, show 1 + (j.val - 1) = j.val by omega] using hp
    · have he : bitShift y (3 * (h + 1)) = bitShift (originalT y) (3 * h) := by
        simp only [originalT, D5.S1.Digit.Infinite.OddColorThreeSource.shift_add]
        congr 1
        omega
      rw [he,hyt,hvt]

private theorem response_expansion (x : LegalDigits) (j n : ℕ) :
    kappa (bitShift x (3 * j)) =
      (∑ k ∈ Finset.range n, (-g) ^ k * offset (window x (j + k))) +
      (-g) ^ n * kappa (bitShift x (3 * (j + n))) := by
  let f (k : ℕ) : ℝ := (-g) ^ k * kappa (bitShift x (3 * (j + k)))
  have hterm (k : ℕ) : (-g) ^ k * offset (window x (j + k)) = f k - f (k + 1) := by
    dsimp only [f]
    rw [← residual x (j + k), pow_succ, Nat.add_assoc]
    ring
  have he : (∑ k ∈ Finset.range n, (-g) ^ k * offset (window x (j + k))) =
      f 0 - f n := by
    calc
      _ = ∑ k ∈ Finset.range n, (f k - f (k + 1)) :=
        Finset.sum_congr rfl (fun k _ => hterm k)
      _ = f 0 - f n := Finset.sum_range_sub' f n
  dsimp only [f] at he
  simp only [pow_zero, one_mul, Nat.add_zero] at he
  linarith only [he]

private theorem affine_actual (h : ℕ) (x y : LegalDigits)
    (hp : windowPrefix h y = windowPrefix h x) :
    response h y = affineResponse h x (kappa (bitShift y (3 * h))) := by
  funext j
  have hj : j.val ≤ h := by have := j.isLt; omega
  have he := response_expansion y j (h - j.val)
  rw [Nat.add_sub_of_le hj] at he
  dsimp only [response, affineResponse]
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkh : j.val + k < h := by have := Finset.mem_range.mp hk; omega
  exact congrArg (fun l : Label => (-g) ^ k * offset l) (congrFun hp ⟨j.val + k,hkh⟩)

private theorem last_guard (h : ℕ) (hh : 1 ≤ h) (x : LegalDigits) :
    actualGuard false x h = outgoing (window x (h - 1)) := by
  simp only [actualGuard, show h ≠ 0 by omega, ↓reduceIte, outgoing, window,
    D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift]
  change x.val (3 * h - 1) = x.val (2 + 3 * (h - 1))
  exact congrArg x.val (by omega : 3 * h - 1 = 2 + 3 * (h - 1))

private theorem response_segment (h : ℕ) (hh : 1 ≤ h) (x : LegalDigits) :
    response h '' {y : LegalDigits | windowPrefix h y = windowPrefix h x} =
      affineResponse h x '' stateInterval (actualGuard false x h) := by
  ext r
  constructor
  · rintro ⟨y,hp,rfl⟩
    have hg : actualGuard false y h = actualGuard false x h := by
      rw [last_guard h hh y,last_guard h hh x]
      exact congrArg outgoing (congrFun hp ⟨h - 1,by omega⟩)
    have hs := tail_guard false y h (by simp [stateAddress])
    rw [hg] at hs
    refine ⟨kappa (bitShift y (3 * h)),?_,(affine_actual h x y hp).symm⟩
    rw [← closed_observation_graph_realization.2.1]
    exact ⟨bitShift y (3 * h),hs,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    rw [← closed_observation_graph_realization.2.1] at ha
    obtain ⟨z,hz,hza⟩ := ha
    obtain ⟨y,_,hp,hyt⟩ := realize_tail h false x z (by simp [stateAddress]) hz
    refine ⟨y,hp,?_⟩
    rw [affine_actual h x y hp,hyt,hza]

/-- The complete response segments have sharp global separation t / 2, attained by
empty and periodic - five sources under either guard. Finite-tail sources have the
same unattained infimum, closed recovery exactly up to t / 4, and every correct
discrete-prefix decoder is discontinuous at the critical constant observation. -/
theorem result (h : ℕ) (hh : 1 ≤ h) :
    (∀ x : LegalDigits,
      response h '' {y : LegalDigits | windowPrefix h y = windowPrefix h x} =
        affineResponse h x '' stateInterval (actualGuard false x h)) ∧
    (∀ s : Bool, IsLeast {d : ℝ | ∃ x y : LegalDigits,
      stateAddress s x ∧ stateAddress s y ∧ windowPrefix h x ≠ windowPrefix h y ∧
      dist (response h x) (response h y) = d} (t / 2)) ∧
    (response h (fiveRun 0) = (fun _ => 0) ∧
      response h fiveStream = (fun _ => t / 2) ∧
      windowPrefix h (fiveRun 0) ≠ windowPrefix h fiveStream ∧
      ∀ s : Bool, stateAddress s (fiveRun 0) ∧ stateAddress s fiveStream) ∧
    (∀ x y : LegalDigits, finiteTail x → finiteTail y →
      windowPrefix h x ≠ windowPrefix h y → t / 2 < dist (response h x) (response h y)) ∧
    IsGLB {d : ℝ | ∃ x y : LegalDigits, finiteTail x ∧ finiteTail y ∧
      windowPrefix h x ≠ windowPrefix h y ∧ dist (response h x) (response h y) = d} (t / 2) ∧
    (∀ ε : ℝ, 0 ≤ ε →
      ((∃ decode : observations h ε → (Fin h → Label), correct h ε decode) ↔ ε ≤ t / 4)) ∧
    (∃ hr : (fun _ : Fin (h + 1) => t / 4) ∈ observations h (t / 4),
      ∀ decode : observations h (t / 4) → (Fin h → Label), correct h (t / 4) decode →
      ¬ @ContinuousAt (observations h (t / 4)) (Fin h → Label) _ ⊥ decode ⟨fun _ => t / 4,hr⟩) := by
  have hprefix : windowPrefix h (fiveRun 0) ≠ windowPrefix h fiveStream := by
    intro he
    have hx := congrFun he ⟨0,by omega⟩
    simp only [windowPrefix, run_window, Nat.not_lt_zero, ↓reduceIte, five_window] at hx
    exact five_ne_null hx.symm
  have hguard (s : Bool) : stateAddress s (fiveRun 0) ∧ stateAddress s fiveStream := by
    simp [stateAddress,fiveRun,fiveStream]
  have hdist : dist (response h (fiveRun 0)) (response h fiveStream) = t / 2 := by
    rw [zero_response, stream_response, dist_pi_const, Real.dist_eq, zero_sub, abs_neg,
      abs_of_pos (div_pos golden_facts.1 (by norm_num))]
  refine ⟨response_segment h hh,?_,⟨zero_response h,stream_response h,hprefix,hguard⟩,
    strict_separation h,finite_infimum h hh,recovery h hh,?_⟩
  · intro s
    refine ⟨⟨fiveRun 0,fiveStream,(hguard s).1,(hguard s).2,hprefix,hdist⟩,?_⟩
    rintro d ⟨x,y,_,_,hp,rfl⟩
    exact separation h x y hp
  · refine ⟨critical_member h,?_⟩
    intro decode hd
    exact critical_discontinuity h hh decode hd

end D5.S1.Digit.Infinite.CriticalPrefixSeparation
