/- GID: D5/S3/Combinatorics/Graph/Pressure/MeyerovitchYoungQ61CycleValue
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Pressure/MeyerovitchYoungQ61CycleValue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The subcritical free-endpoint maximin limit is the maximum reachable cycle mean. -/

import D5.S1.Dynamics.Symbolic.MeyerovitchYoungQ61Subcritical
import D5.S3.Combinatorics.Graph.LayeredCirculation.PositiveCircuitSupplier
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.List

/-!
The reachable score graph for Meyerovitch–Young Q6.1. Each edge retains
its Alice label and carries the exact increment of the original minimum
Bob payoff. The finite-horizon maximin has a bounded error from the
maximum cycle mean times the horizon.
-/

open Filter Set
open scoped Topology

set_option autoImplicit false

namespace MeyerovitchYoungQ61Subcritical

noncomputable section

open Maths Maths.AdditiveTransport Maths.MaxPlusPotential

abbrev State (c : ℝ) := {x : ℝ // x ∈ reachable c}
abbrev Edge (c : ℝ) := State c × Bool

abbrev reachableGraph (c : ℝ) : EdgeGraph (State c) (Edge c) :=
  ⟨Prod.fst, fun e => ⟨step c e.1.val e.2, reachable_step e.1.property e.2⟩⟩

def edgeWeight (c : ℝ) (e : Edge c) : ℝ := payoffIncrement c e.1.val e.2

abbrev initialState (c : ℝ) : State c := ⟨c, ⟨fun _ => false, 0, rfl⟩⟩

private abbrev wordState (c : ℝ) (w : ℕ → Bool) (n : ℕ) : State c :=
  ⟨trajectory c w n, ⟨w, n, rfl⟩⟩

private theorem wordState_succ (c : ℝ) (w : ℕ → Bool) (k n : ℕ) :
    (reachableGraph c).target (wordState c w (k + n), w (k + n)) =
      wordState c w (k + (n + 1)) := rfl

private def segment (c : ℝ) (w : ℕ → Bool) (k : ℕ) :
    (n : ℕ) → (reachableGraph c).Walk (wordState c w k) (wordState c w (k + n))
  | 0 => .nil
  | n + 1 =>
      ((segment c w k n).concat (wordState c w (k + n), w (k + n)) rfl).castFinish
        (wordState_succ c w k n)

private theorem segment_length (c : ℝ) (w : ℕ → Bool) (k n : ℕ) :
    (segment c w k n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [segment, EdgeGraph.Walk.length_castFinish,
      EdgeGraph.Walk.length_concat, ih]

private theorem segment_weight {c : ℝ} (hc : 0 ≤ c) (w : ℕ → Bool) (k n : ℕ) :
    walkWeight (edgeWeight c) (segment c w k n) =
      freeMinimum c (fun i : Fin (k + n) => w i.val) -
        freeMinimum c (fun i : Fin k => w i.val) := by
  induction n with
  | zero => simp [segment, walkWeight]
  | succ n ih =>
      rw [segment, walkWeight_castFinish, walkWeight_concat, ih, Nat.add_succ]
      have h := freeMinimum_succ_sub hc w (k + n)
      change _ + payoffIncrement c (trajectory c w (k + n)) (w (k + n)) = _
      linarith only [h]

private def wordWalk (c : ℝ) (w : ℕ → Bool) (n : ℕ) :
    (reachableGraph c).Walk (initialState c) (wordState c w n) :=
  ((segment c w 0 n).castStart (show wordState c w 0 = initialState c from rfl)).castFinish
    (congrArg (wordState c w) (Nat.zero_add n))

private theorem wordWalk_length (c : ℝ) (w : ℕ → Bool) (n : ℕ) :
    (wordWalk c w n).length = n := by
  simp [wordWalk, segment_length]

private theorem walkWeight_castStart {c : ℝ} {x x' y : State c}
    (p : (reachableGraph c).Walk x y) (h : x = x') :
    walkWeight (edgeWeight c) (p.castStart h) = walkWeight (edgeWeight c) p := by
  cases h
  rfl

private theorem wordWalk_weight {c : ℝ} (hc : 0 ≤ c) (w : ℕ → Bool) (n : ℕ) :
    walkWeight (edgeWeight c) (wordWalk c w n) =
      freeMinimum c (fun i : Fin n => w i.val) := by
  rw [wordWalk, walkWeight_castFinish, walkWeight_castStart, segment_weight hc, Nat.zero_add]
  have hzero : freeMinimum c (fun i : Fin 0 => w i.val) = 0 := by
    simp [freeMinimum_eq_minimumScore, minimumScore, scores]
  rw [hzero, sub_zero]

private theorem trajectory_prefix_congr (c : ℝ) {u v : ℕ → Bool} (n : ℕ)
    (h : ∀ i < n, u i = v i) : trajectory c u n = trajectory c v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [trajectory]
      rw [ih (fun i hi => h i (by omega)), h n (by omega)]

/-- Every walk from the initial state of the labelled graph is the
normalized score trajectory of an Alice word and has its physical payoff. -/
private theorem walk_realized {c : ℝ} (hc : 0 ≤ c) {x : State c}
    (path : (reachableGraph c).Walk (initialState c) x) :
    ∃ w : ℕ → Bool, wordState c w path.length = x ∧
      walkWeight (edgeWeight c) path =
        freeMinimum c (fun i : Fin path.length => w i.val) := by
  induction path with
  | nil =>
      refine ⟨fun _ => false, rfl, ?_⟩
      have h := freeMinimum_eq_minimumScore c (fun _ => false) 0
      simpa [walkWeight, minimumScore, scores] using h.symm
  | @concat x path e he ih =>
      obtain ⟨w, hw, hwWeight⟩ := ih
      let n := path.length
      let v (i : ℕ) := if i = n then e.2 else w i
      have hletters : ∀ i < n, v i = w i := by
        intro i hi
        simp [v, ne_of_lt hi]
      have htraj : trajectory c v n = trajectory c w n :=
        trajectory_prefix_congr c n hletters
      have hx : trajectory c v n = e.1.val := by
        rw [htraj]
        exact congrArg Subtype.val (hw.trans he.symm)
      have hword : (fun i : Fin n => v i.val) = fun i : Fin n => w i.val :=
        funext (fun i => hletters i.val i.isLt)
      have hlast : v n = e.2 := by simp [v]
      refine ⟨v, ?_, ?_⟩
      · apply Subtype.ext
        change step c (trajectory c v n) (v n) = step c e.1.val e.2
        rw [hx, hlast]
      · rw [walkWeight_concat, hwWeight, EdgeGraph.Walk.length_concat]
        change freeMinimum c (fun i : Fin n => w i.val) + edgeWeight c e =
          freeMinimum c (fun i : Fin (n + 1) => v i.val)
        have hstep := freeMinimum_succ_sub hc v n
        rw [hword, hx, hlast] at hstep
        unfold edgeWeight
        linarith only [hstep]

private theorem simpleCycle_exists (c : ℝ) [Finite (State c)] :
    ∃ x : State c, ∃ cycle : (reachableGraph c).Walk x x, IsSimpleCycle cycle := by
  let w : ℕ → Bool := fun _ => false
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (wordState c w)
  have closed_of_lt {a b : ℕ} (hab : a < b) (h : wordState c w a = wordState c w b) :
      ∃ x : State c, ∃ cycle : (reachableGraph c).Walk x x, 0 < cycle.length := by
    have he : a + (b - a) = b := by omega
    let cycle := (segment c w a (b - a)).castFinish
      ((congrArg (wordState c w) he).trans h.symm)
    exact ⟨_, cycle, by simpa [cycle, segment_length] using (show 0 < b - a by omega)⟩
  obtain ⟨x, cycle, hpos⟩ := (lt_or_gt_of_ne hij).elim
    (fun h => closed_of_lt h heq) (fun h => closed_of_lt h heq.symm)
  obtain ⟨y, simple, hs, _⟩ := exists_simpleCycle_cycleMeanDominates (edgeWeight c) cycle hpos
  exact ⟨y, simple, hs⟩

/-- The largest reachable simple cycle mean is attained. -/
private theorem maximumCycle_exists (c : ℝ) [Finite (State c)] :
    ∃ x : State c, ∃ cycle : (reachableGraph c).Walk x x, IsSimpleCycle cycle ∧
      ∀ y (p : (reachableGraph c).Walk y y), IsSimpleCycle p →
        walkWeight (edgeWeight c) p / (p.length : ℝ) ≤
          walkWeight (edgeWeight c) cycle / (cycle.length : ℝ) := by
  classical
  let : Fintype (State c) := Fintype.ofFinite _
  let means : Set ℝ := {m | ∃ x : State c, ∃ p : (reachableGraph c).Walk x x,
    IsSimpleCycle p ∧ walkWeight (edgeWeight c) p / (p.length : ℝ) = m}
  have hfinite : means.Finite := by
    have hlist : ({l : List (Edge c) | l.length ≤ Fintype.card (State c)} :
        Set (List (Edge c))).Finite := List.finite_length_le _ _
    apply (hlist.image (fun l : List (Edge c) =>
      (l.map (edgeWeight c)).sum / (l.length : ℝ))).subset
    rintro _ ⟨x, p, hp, rfl⟩
    exact ⟨p.edges, by simpa using hp.length_le_card, by simp [walkWeight]⟩
  have hnonempty : means.Nonempty := by
    obtain ⟨x, p, hp⟩ := simpleCycle_exists c
    exact ⟨_, x, p, hp, rfl⟩
  have hnonempty' : hfinite.toFinset.Nonempty := by
    obtain ⟨m, hm⟩ := hnonempty
    exact ⟨m, hfinite.mem_toFinset.mpr hm⟩
  obtain ⟨m, hm, hmax⟩ := hfinite.toFinset.exists_max_image id hnonempty'
  obtain ⟨x, cycle, hs, heq⟩ := hfinite.mem_toFinset.mp hm
  exact ⟨x, cycle, hs, fun y p hp => by
    have h := hmax _ (hfinite.mem_toFinset.mpr ⟨y, p, hp, rfl⟩)
    simpa only [id_eq, heq] using h⟩

private theorem walkWeight_append {c : ℝ} {x y z : State c}
    (p : (reachableGraph c).Walk x y) (q : (reachableGraph c).Walk y z) :
    walkWeight (edgeWeight c) (p.append q) =
      walkWeight (edgeWeight c) p + walkWeight (edgeWeight c) q := by
  simp [walkWeight]

private theorem walkWeight_le_of_potential {c : ℝ} {μ : ℝ} {φ : State c → ℝ}
    (hφ : ∀ e : Edge c, defect (reachableGraph c) (edgeWeight c) φ e ≤ μ)
    {x y : State c} (p : (reachableGraph c).Walk x y) :
    walkWeight (edgeWeight c) p ≤ (p.length : ℝ) * μ + φ y - φ x := by
  induction p with
  | nil => simp [walkWeight, EdgeGraph.Walk.edges]
  | @concat y p e hsrc ih =>
      have he := hφ e
      rw [defect, hsrc] at he
      rw [walkWeight_concat, EdgeGraph.Walk.length_concat, Nat.cast_add, Nat.cast_one]
      linarith only [he, ih]

private def repeatCycle {c : ℝ} {x : State c} (p : (reachableGraph c).Walk x x) :
    ℕ → (reachableGraph c).Walk x x
  | 0 => .nil
  | n + 1 => (repeatCycle p n).append p

private theorem repeatCycle_length {c : ℝ} {x : State c} (p : (reachableGraph c).Walk x x)
    (n : ℕ) : (repeatCycle p n).length = n * p.length := by
  induction n with
  | zero => simp [repeatCycle]
  | succ n ih => simp [repeatCycle, ih, Nat.succ_mul]

private theorem repeatCycle_weight {c : ℝ} {x : State c} (p : (reachableGraph c).Walk x x)
    (n : ℕ) : walkWeight (edgeWeight c) (repeatCycle p n) =
      (n : ℝ) * walkWeight (edgeWeight c) p := by
  induction n with
  | zero => simp [repeatCycle, walkWeight]
  | succ n ih => simp [repeatCycle, ih, Nat.cast_succ, add_mul]

private def padWalk (c : ℝ) (x : State c) : ℕ → Σ y, (reachableGraph c).Walk x y
  | 0 => ⟨x, .nil⟩
  | n + 1 =>
      let p := padWalk c x n
      ⟨_, p.2.concat (p.1, false) rfl⟩

private theorem padWalk_length (c : ℝ) (x : State c) (n : ℕ) :
    (padWalk c x n).2.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [padWalk, EdgeGraph.Walk.length_concat, ih]

private theorem padWalk_weight_lower {c B : ℝ} (hB : ∀ e : Edge c, -B ≤ edgeWeight c e)
    (x : State c) (n : ℕ) :
    -B * (n : ℝ) ≤ walkWeight (edgeWeight c) (padWalk c x n).2 := by
  induction n with
  | zero => simp [padWalk, walkWeight]
  | succ n ih =>
      rw [padWalk, walkWeight_concat, Nat.cast_succ]
      linarith only [ih, hB ((padWalk c x n).1, false)]

/-- The finite-horizon optimum is within bounded additive error of the
attained maximum cycle mean times the horizon. -/
theorem maximin_cycle_estimate_of_hit {c : ℝ} (hc : 0 ≤ c) (hW : 2 * c < circumference)
    {N : ℕ} (hHit : UniformForbiddenHit c N) :
    ∃ x : State c, ∃ cycle : (reachableGraph c).Walk x x, IsSimpleCycle cycle ∧
      let μ := walkWeight (edgeWeight c) cycle / (cycle.length : ℝ)
      (∀ y (p : (reachableGraph c).Walk y y),
        walkWeight (edgeWeight c) p ≤ (p.length : ℝ) * μ) ∧
      ∃ A B : ℝ, ∀ᶠ n : ℕ in atTop,
        (n : ℝ) * μ - A ≤ maximin c n ∧ maximin c n ≤ (n : ℝ) * μ + B := by
  classical
  obtain ⟨states, hstates, _⟩ := reachable_finset_of_hit hc hW hHit
  let : Finite (State c) := Finite.of_injective
    (fun x : State c => (⟨x.val, by
      change x.val ∈ (↑states : Set ℝ)
      rw [hstates]
      exact x.property⟩ : {z : ℝ // z ∈ states}))
    (fun _ _ h => Subtype.ext (congrArg (fun z : {z : ℝ // z ∈ states} => z.val) h))
  let : Fintype (State c) := Fintype.ofFinite _
  let : Nonempty (State c) := ⟨initialState c⟩
  obtain ⟨x, cycle, hs, hmax⟩ := maximumCycle_exists c
  let μ := walkWeight (edgeWeight c) cycle / (cycle.length : ℝ)
  have hpositive : (0 : ℝ) < cycle.length := by exact_mod_cast hs.1
  have hcycle : walkWeight (edgeWeight c) cycle = (cycle.length : ℝ) * μ := by
    dsimp only [μ]
    rw [mul_comm, div_mul_cancel₀ _ hpositive.ne']
  have hall := (forall_closedWalk_mean_le_iff_simpleCycle
    (G := reachableGraph c) (edgeWeight c) μ).mpr (by
      intro y p hp
      have hp' : (0 : ℝ) < p.length := by exact_mod_cast hp.1
      have h := (div_le_iff₀ hp').mp (hmax y p hp)
      simpa only [mul_comm] using h)
  obtain ⟨φ, hφ⟩ := (worstDirectedResidualAtMost_iff_closedWalk_le
    (reachableGraph c) (edgeWeight c) μ).mpr hall
  obtain ⟨xMax, _, hφMax⟩ := Finset.exists_max_image Finset.univ φ Finset.univ_nonempty
  let : Nonempty (Edge c) := ⟨(initialState c, false)⟩
  obtain ⟨eMin, _, heMin⟩ := Finset.exists_min_image Finset.univ (edgeWeight c) Finset.univ_nonempty
  let L := |edgeWeight c eMin|
  have hL : ∀ e : Edge c, -L ≤ edgeWeight c e := fun e =>
    (neg_abs_le _).trans (heMin e (Finset.mem_univ _))
  obtain ⟨w, k, hreach⟩ := x.property
  let connector := (wordWalk c w k).castFinish (Subtype.ext hreach)
  have hk : connector.length = k := by simp [connector, wordWalk_length]
  let A := (k : ℝ) * μ + (cycle.length : ℝ) * (|μ| + L) -
    walkWeight (edgeWeight c) connector
  refine ⟨x, cycle, hs, hall, A, φ xMax - φ (initialState c), ?_⟩
  filter_upwards [eventually_ge_atTop k] with n hn
  constructor
  · let t := (n - k) / cycle.length
    let r := (n - k) % cycle.length
    have hr : r < cycle.length := Nat.mod_lt _ hs.1
    have hlen : k + t * cycle.length + r = n := by
      have hmod := Nat.mod_add_div (n - k) cycle.length
      dsimp only [t, r]
      rw [Nat.mul_comm ((n - k) / cycle.length), add_assoc,
        Nat.add_comm (cycle.length * ((n - k) / cycle.length)), hmod, Nat.add_sub_of_le hn]
    let p := (connector.append (repeatCycle cycle t)).append (padWalk c x r).2
    have hp : p.length = n := by
      simpa only [p, EdgeGraph.Walk.length_append, hk, repeatCycle_length, padWalk_length]
        using hlen
    obtain ⟨v, _, hv⟩ := walk_realized hc p
    have hpay := (maximin_spec c p.length).2 (fun i => v i.val)
    rw [← hv, hp] at hpay
    change walkWeight (edgeWeight c)
      ((connector.append (repeatCycle cycle t)).append (padWalk c x r).2) ≤ maximin c n at hpay
    rw [walkWeight_append, walkWeight_append, repeatCycle_weight, hcycle] at hpay
    have htail := padWalk_weight_lower hL x r
    have hlenReal : (k : ℝ) + (t : ℝ) * (cycle.length : ℝ) + (r : ℝ) = (n : ℝ) := by
      exact_mod_cast hlen
    have hμ : μ + L ≤ |μ| + L := add_le_add_left (le_abs_self μ) _
    have hr' : (r : ℝ) ≤ cycle.length := by exact_mod_cast hr.le
    have herror := mul_le_mul hμ hr' (Nat.cast_nonneg r) (by positivity : 0 ≤ |μ| + L)
    have hscaled : ((k : ℝ) + (t : ℝ) * (cycle.length : ℝ) + (r : ℝ)) * μ =
        (n : ℝ) * μ := congrArg (fun a : ℝ => a * μ) hlenReal
    dsimp only [A]
    nlinarith only [hpay, htail, herror, hscaled]
  · obtain ⟨v, hv⟩ := (maximin_spec c n).1
    let u (i : ℕ) := if hi : i < n then v ⟨i, hi⟩ else false
    have hu : (fun i : Fin n => u i.val) = v := by
      funext i
      simp [u, i.isLt]
    have h := walkWeight_le_of_potential hφ (wordWalk c u n)
    rw [wordWalk_weight hc, wordWalk_length, hu, hv] at h
    linarith only [h, hφMax (wordState c u n) (Finset.mem_univ _)]

/-- The actual free-endpoint Q6.1 value is the mean of a reachable simple
cycle, which bounds the mean of every reachable positive-length closed walk. -/
theorem maximin_tendsto_cycleMean_of_hit {c : ℝ} (hc : 0 ≤ c)
    (hW : 2 * c < circumference) {N : ℕ} (hHit : UniformForbiddenHit c N) :
    ∃ x : State c, ∃ cycle : (reachableGraph c).Walk x x, IsSimpleCycle cycle ∧
      let μ := walkWeight (edgeWeight c) cycle / (cycle.length : ℝ)
      (∀ y (p : (reachableGraph c).Walk y y),
        walkWeight (edgeWeight c) p ≤ (p.length : ℝ) * μ) ∧
      Tendsto (fun n : ℕ => maximin c n / (n : ℝ)) atTop (𝓝 μ) := by
  obtain ⟨x, cycle, hs, hall, A, B, hbounds⟩ := maximin_cycle_estimate_of_hit hc hW hHit
  let μ := walkWeight (edgeWeight c) cycle / (cycle.length : ℝ)
  refine ⟨x, cycle, hs, hall, ?_⟩
  have hA : Tendsto (fun n : ℕ => μ - A / (n : ℝ)) atTop (𝓝 μ) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat A)
  have hB : Tendsto (fun n : ℕ => μ + B / (n : ℝ)) atTop (𝓝 μ) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat B)
  apply hA.squeeze' hB
  · filter_upwards [hbounds, eventually_ge_atTop (1 : ℕ)] with n h hn
    have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply (le_div_iff₀ hpos).mpr
    have hcancel := div_mul_cancel₀ A hpos.ne'
    rw [sub_mul, hcancel]
    simpa only [mul_comm] using h.1
  · filter_upwards [hbounds, eventually_ge_atTop (1 : ℕ)] with n h hn
    have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply (div_le_iff₀ hpos).mpr
    have hcancel := div_mul_cancel₀ B hpos.ne'
    rw [add_mul, hcancel]
    simpa only [mul_comm] using h.2

/-- The Pell hitting lemma supplies the hypothesis for every real
nonnegative strictly subcritical toll. -/
theorem maximin_tendsto_cycleMean_subcritical {c : ℝ} (hc : 0 ≤ c)
    (hW : 2 * c < circumference) :
    ∃ x : State c, ∃ cycle : (reachableGraph c).Walk x x, IsSimpleCycle cycle ∧
      let μ := walkWeight (edgeWeight c) cycle / (cycle.length : ℝ)
      (∀ y (p : (reachableGraph c).Walk y y),
        walkWeight (edgeWeight c) p ≤ (p.length : ℝ) * μ) ∧
      Tendsto (fun n : ℕ => maximin c n / (n : ℝ)) atTop (𝓝 μ) := by
  obtain ⟨N, hHit⟩ := uniformForbiddenHit_pell hW
  exact maximin_tendsto_cycleMean_of_hit hc hW hHit

/-!
The ordinary proof of the sharper hitting estimate uses the full
translated Pell mesh. For a convergent a/q of 1/R, establish that times
1 through q give all q grid residues modulo q and that each corresponding
rotation phase differs by at most R/q_next. The Pell determinant and
error formulas supply the arithmetic inputs. The first q > 4R/(R-2c)
then gives N ≤ 12R/(R-2c).

The refinement in `q61-irrational-renewal-cycle-exact.txt` needs the
reachable endpoint multigraph.
Its edges are first strictly positive overshoot segments from 0 or 2c,
with their original labels, lengths, and overshoots. The free start c is
used to compute reachable endpoints. Prove the exact decomposition and
concatenation, then minimize total overshoot divided by total length over
reachable self arcs and opposing arc pairs. This yields the 2N period
bound. Exact field operations and comparisons in ℚ(√2), termination of
the executable enumeration, and the local piecewise-affine formula are
separate formalization obligations. The critical branch and the quadratic
approach estimates are outside the strict subcritical value theorem.
-/

end

end MeyerovitchYoungQ61Subcritical
