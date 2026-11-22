/- GID: D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61Subcritical
   generality: I
   mirror-B: D5/B/S1/Dynamics/Symbolic/MeyerovitchYoungQ61Subcritical
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Free-endpoint payoffs and finite score states for a subcritical silver rotation. -/

import D5.S1.Dynamics.Symbolic.MeyerovitchYoungQ62
import D5.S1.Words.Mechanical.SilverSlopeAbelianPellArithmetic
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
Meyerovitch–Young, “Rationality and computability of the covering radius for
sofic shifts,” arXiv:2603.21449v1, Question 6.1 and equations (5)–(6).

https://arxiv.org/html/2603.21449v1#S6.Thmlemma1
https://arxiv.org/html/2603.21449v1#S4.Ex38

Alice has one vertex and two loops. Bob has two vertices and one directed
edge for each ordered pair. The running payoff uses the source mode. Both
Bob endpoints are free. The score coordinate is the plus-mode minimum
minus the minus-mode minimum, translated by the switch toll. The finite
state argument follows the ordinary proof in
`q61-irrational-switching-subcritical-exact.txt`.
-/

open scoped BigOperators
open Set

set_option autoImplicit false

namespace MeyerovitchYoungQ61Subcritical

noncomputable section

open PrimitivePayoffSwitching (Response sgn)

/-- The circumference for the rotation in the translated score coordinate. -/
def circumference : ℝ := 1 + Real.sqrt 2

def increment : Bool → ℝ
  | false => 1
  | true => -Real.sqrt 2

def edgePayoff (c : ℝ) (b s t : Bool) : ℝ :=
  sgn s * (increment b / 2) + if s = t then 0 else c

def walkCost (c : ℝ) {n : ℕ} (w : Fin n → Bool) (p : Response n) : ℝ :=
  ∑ i : Fin n, edgePayoff c (w i) (p i.castSucc) (p i.succ)

def update (c : ℝ) (b : Bool) (v : Bool → ℝ) (t : Bool) : ℝ :=
  min (v false + edgePayoff c b false t) (v true + edgePayoff c b true t)

def scores (c : ℝ) (w : ℕ → Bool) : ℕ → Bool → ℝ
  | 0 => fun _ => 0
  | n + 1 => update c (w n) (scores c w n)

private theorem walkCost_succ (c : ℝ) (w : ℕ → Bool) (n : ℕ)
    (p : Response (n + 1)) :
    walkCost c (fun i => w i.val) p =
      walkCost c (fun i => w i.val) (Fin.init p) +
        edgePayoff c (w n) (Fin.init p (Fin.last n)) (p (Fin.last (n + 1))) := by
  unfold walkCost
  rw [Fin.sum_univ_castSucc]
  rfl

private theorem exists_bool_minimizer (f : Bool → ℝ) :
    ∃ b, f b = min (f false) (f true) := by
  rcases le_total (f false) (f true) with h | h
  · exact ⟨false, (min_eq_left h).symm⟩
  · exact ⟨true, (min_eq_right h).symm⟩

theorem scores_spec (c : ℝ) (w : ℕ → Bool) (n : ℕ) (t : Bool) :
    (∃ p : Response n, p (Fin.last n) = t ∧
      walkCost c (fun i => w i.val) p = scores c w n t) ∧
    ∀ p : Response n, p (Fin.last n) = t →
      scores c w n t ≤ walkCost c (fun i => w i.val) p := by
  induction n generalizing t with
  | zero =>
      constructor
      · exact ⟨fun _ => t, rfl, by simp [walkCost, scores]⟩
      · intro p _
        simp [walkCost, scores]
  | succ n ih =>
      constructor
      · obtain ⟨s, hs⟩ := exists_bool_minimizer
          (fun s => scores c w n s + edgePayoff c (w n) s t)
        obtain ⟨p, hp, hcost⟩ := (ih s).1
        refine ⟨Fin.snoc p t, Fin.snoc_last _ _, ?_⟩
        rw [walkCost_succ, Fin.init_snoc, Fin.snoc_last, hp, hcost]
        exact hs
      · intro p hp
        rw [walkCost_succ, hp]
        let s := Fin.init p (Fin.last n)
        have hprefix := (ih s).2 (Fin.init p) rfl
        have hstep : scores c w (n + 1) t ≤
            scores c w n s + edgePayoff c (w n) s t := by
          cases s
          · exact min_le_left _ _
          · exact min_le_right _ _
        exact hstep.trans (add_le_add_left hprefix _)

private theorem exists_free_minimizer (c : ℝ) {n : ℕ} (w : Fin n → Bool) :
    ∃ p : Response n, ∀ q : Response n, walkCost c w p ≤ walkCost c w q := by
  classical
  obtain ⟨p, _, hp⟩ := (Finset.univ : Finset (Response n)).exists_min_image
    (walkCost c w) ⟨fun _ => false, Finset.mem_univ _⟩
  exact ⟨p, fun q => hp q (Finset.mem_univ _)⟩

/-- The actual Bob minimum, over whole compatible walks with two free endpoints. -/
def freeMinimum (c : ℝ) {n : ℕ} (w : Fin n → Bool) : ℝ :=
  walkCost c w (exists_free_minimizer c w).choose

theorem freeMinimum_spec (c : ℝ) {n : ℕ} (w : Fin n → Bool) :
    (∃ p : Response n, walkCost c w p = freeMinimum c w) ∧
    ∀ p : Response n, freeMinimum c w ≤ walkCost c w p :=
  ⟨⟨(exists_free_minimizer c w).choose, rfl⟩, (exists_free_minimizer c w).choose_spec⟩

/-- Explicit edge-word version for a positive horizon. The two endpoint
witnesses in the subtype are existentially quantified. -/
theorem freeMinimum_edge_spec (c : ℝ) {n : ℕ} (hn : 0 < n) (w : Fin n → Bool) :
    IsLeast
      (Set.range (fun e : {e : Fin n → MeyerovitchYoungQ62.GEdge //
          ∃ s t, MeyerovitchYoungQ62.WalkBetween Prod.fst Prod.snd hn s t e} =>
        ∑ i : Fin n, edgePayoff c (w i) (e.val i).1 (e.val i).2))
      (freeMinimum c w) := by
  let edgeCost (e : Fin n → MeyerovitchYoungQ62.GEdge) :=
    ∑ i : Fin n, edgePayoff c (w i) (e i).1 (e i).2
  have hcost {s t : Bool} (p : PrimitivePayoffSwitching.EndpointResponse n s t) :
      edgeCost ((MeyerovitchYoungQ62.endpointWalkEquiv hn s t) p).val =
        walkCost c w p.val := rfl
  constructor
  · obtain ⟨p, hp⟩ := (freeMinimum_spec c w).1
    let q : PrimitivePayoffSwitching.EndpointResponse n (p 0) (p (Fin.last n)) :=
      ⟨p, rfl, rfl⟩
    let e := MeyerovitchYoungQ62.endpointWalkEquiv hn _ _ q
    exact ⟨⟨e.val, _, _, e.property⟩, (hcost q).trans hp⟩
  · rintro _ ⟨⟨e, s, t, he⟩, rfl⟩
    let equiv := MeyerovitchYoungQ62.endpointWalkEquiv hn s t
    let q := equiv.symm ⟨e, he⟩
    have h := hcost q
    change edgeCost (equiv q).val = walkCost c w q.val at h
    rw [Equiv.apply_symm_apply] at h
    exact ((freeMinimum_spec c w).2 q.val).trans_eq h.symm

def minimumScore (v : Bool → ℝ) : ℝ := min (v false) (v true)

theorem freeMinimum_eq_minimumScore (c : ℝ) (w : ℕ → Bool) (n : ℕ) :
    freeMinimum c (fun i : Fin n => w i.val) = minimumScore (scores c w n) := by
  obtain ⟨s, hs⟩ := exists_bool_minimizer (scores c w n)
  obtain ⟨p, _, hp⟩ := (scores_spec c w n s).1
  obtain ⟨q, hq⟩ := (freeMinimum_spec c (fun i : Fin n => w i.val)).1
  apply le_antisymm
  · exact ((freeMinimum_spec c _).2 p).trans_eq (hp.trans hs)
  · rw [← hq]
    apply le_trans _ ((scores_spec c w n (q (Fin.last n))).2 q rfl)
    cases q (Fin.last n)
    · exact min_le_left _ _
    · exact min_le_right _ _

/-- The finite-horizon maximum of the actual free-endpoint minima. -/
def maximin (c : ℝ) (n : ℕ) : ℝ := by
  classical
  exact (Finset.univ.image (fun w : Fin n → Bool => freeMinimum c w)).max'
    (Finset.univ_nonempty.image _)

theorem maximin_spec (c : ℝ) (n : ℕ) :
    (∃ w : Fin n → Bool, freeMinimum c w = maximin c n) ∧
    ∀ w : Fin n → Bool, freeMinimum c w ≤ maximin c n := by
  classical
  unfold maximin
  constructor
  · obtain ⟨w, _, hw⟩ := Finset.mem_image.mp
      (Finset.max'_mem ((Finset.univ : Finset (Fin n → Bool)).image (freeMinimum c)) _)
    exact ⟨w, hw⟩
  · intro w
    exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))

def averageScore (v : Bool → ℝ) : ℝ := (v true + v false) / 2

def normalized (c : ℝ) (v : Bool → ℝ) : ℝ := v true - v false + c

def clip (W y : ℝ) : ℝ := min W (max 0 y)

def overshoot (W y : ℝ) : ℝ := max 0 (-y) + max 0 (y - W)

def step (c : ℝ) (x : ℝ) (b : Bool) : ℝ := clip (2 * c) (x + increment b)

theorem clip_mem {W : ℝ} (hW : 0 ≤ W) (y : ℝ) : clip W y ∈ Icc 0 W :=
  ⟨le_min hW (le_max_left _ _), min_le_left _ _⟩

theorem overshoot_nonneg (W y : ℝ) : 0 ≤ overshoot W y :=
  add_nonneg (le_max_left _ _) (le_max_left _ _)

theorem overshoot_eq_zero_iff (W y : ℝ) :
    overshoot W y = 0 ↔ y ∈ Icc 0 W := by
  constructor
  · intro h
    have h₁ : 0 ≤ max 0 (-y) := le_max_left _ _
    have h₂ : 0 ≤ max 0 (y - W) := le_max_left _ _
    have hl : -y ≤ max 0 (-y) := le_max_right _ _
    have hu : y - W ≤ max 0 (y - W) := le_max_right _ _
    unfold overshoot at h
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hl, hu⟩
    simp [overshoot, max_eq_left (neg_nonpos.mpr hl), max_eq_left (sub_nonpos.mpr hu)]

theorem update_normalized_average {c : ℝ} (hc : 0 ≤ c) (b : Bool) (v : Bool → ℝ) :
    normalized c (update c b v) = step c (normalized c v) b ∧
    averageScore (update c b v) =
      averageScore v - overshoot (2 * c) (normalized c v + increment b) / 2 := by
  let a := v true + increment b / 2
  let d := v false - increment b / 2
  let y := normalized c v + increment b
  have hy : y = a - d + c := by
    dsimp [y, a, d, normalized]
    ring
  have hmean : (a + d) / 2 = averageScore v := by
    dsimp [a, d, averageScore]
    ring
  have hplus : update c b v true = min a (d + c) := by
    simp only [update, edgePayoff, sgn, Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul,
      add_zero]
    rw [min_comm]
    congr 1
    dsimp [d]
    ring
  have hminus : update c b v false = min (a + c) d := by
    simp only [update, edgePayoff, sgn, Bool.true_eq_false, ↓reduceIte, one_mul, neg_mul,
      add_zero]
    rw [min_comm]
    congr 1
    dsimp [a]
    ring
  change update c b v true - update c b v false + c = clip (2 * c) y ∧
    (update c b v true + update c b v false) / 2 =
      averageScore v - overshoot (2 * c) y / 2
  rw [hplus, hminus, ← hmean]
  by_cases hl : y < 0
  · rw [min_eq_left (show a ≤ d + c by linarith), min_eq_left (show a + c ≤ d by linarith)]
    simp only [clip, overshoot, max_eq_left (le_of_lt hl),
      min_eq_right (show 0 ≤ 2 * c by linarith),
      max_eq_right (show 0 ≤ -y by linarith), max_eq_left (show y - 2 * c ≤ 0 by linarith)]
    constructor <;> linarith
  · have hl' : 0 ≤ y := le_of_not_gt hl
    by_cases hu : 2 * c < y
    · rw [min_eq_right (show d + c ≤ a by linarith), min_eq_right (show d ≤ a + c by linarith)]
      simp only [clip, overshoot, max_eq_right hl', min_eq_left hu.le,
        max_eq_left (neg_nonpos.mpr hl'), max_eq_right (sub_nonneg.mpr hu.le)]
      constructor <;> linarith
    · have hu' : y ≤ 2 * c := le_of_not_gt hu
      rw [min_eq_left (show a ≤ d + c by linarith), min_eq_right (show d ≤ a + c by linarith)]
      simp only [clip, overshoot, max_eq_right hl', min_eq_right hu',
        max_eq_left (neg_nonpos.mpr hl'), max_eq_left (sub_nonpos.mpr hu')]
      constructor <;> linarith

theorem minimumScore_eq_average (c : ℝ) (v : Bool → ℝ) :
    minimumScore v = averageScore v - |normalized c v - c| / 2 := by
  rcases le_total (v false) (v true) with h | h
  · have hd : 0 ≤ normalized c v - c := by unfold normalized; linarith
    rw [minimumScore, min_eq_left h, abs_of_nonneg hd]
    unfold averageScore normalized
    ring
  · have hd : normalized c v - c ≤ 0 := by unfold normalized; linarith
    rw [minimumScore, min_eq_right h, abs_of_nonpos hd]
    unfold averageScore normalized
    ring

def trajectory (c : ℝ) (w : ℕ → Bool) : ℕ → ℝ
  | 0 => c
  | n + 1 => step c (trajectory c w n) (w n)

theorem trajectory_mem {c : ℝ} (hc : 0 ≤ c) (w : ℕ → Bool) (n : ℕ) :
    trajectory c w n ∈ Icc 0 (2 * c) := by
  cases n with
  | zero => exact ⟨hc, by change c ≤ 2 * c; linarith⟩
  | succ n => exact clip_mem (by linarith) _

theorem normalized_scores_eq {c : ℝ} (hc : 0 ≤ c) (w : ℕ → Bool) (n : ℕ) :
    normalized c (scores c w n) = trajectory c w n := by
  induction n with
  | zero => simp [scores, trajectory, normalized]
  | succ n ih => rw [scores, trajectory, (update_normalized_average hc _ _).1, ih]

theorem freeMinimum_eq_overshoot {c : ℝ} (hc : 0 ≤ c) (w : ℕ → Bool) (n : ℕ) :
    freeMinimum c (fun i : Fin n => w i.val) =
      -(∑ j ∈ Finset.range n, overshoot (2 * c) (trajectory c w j + increment (w j))) / 2 -
        |trajectory c w n - c| / 2 := by
  have havg : averageScore (scores c w n) =
      -(∑ j ∈ Finset.range n, overshoot (2 * c) (trajectory c w j + increment (w j))) / 2 := by
    induction n with
    | zero => simp [scores, averageScore]
    | succ n ih =>
        rw [scores, (update_normalized_average hc _ _).2, normalized_scores_eq hc,
          ih, Finset.sum_range_succ]
        ring
  rw [freeMinimum_eq_minimumScore, minimumScore_eq_average c, normalized_scores_eq hc, havg]

def payoffIncrement (c x : ℝ) (b : Bool) : ℝ :=
  (|x - c| - |step c x b - c| - overshoot (2 * c) (x + increment b)) / 2

theorem freeMinimum_succ_sub {c : ℝ} (hc : 0 ≤ c) (w : ℕ → Bool) (n : ℕ) :
    freeMinimum c (fun i : Fin (n + 1) => w i.val) -
        freeMinimum c (fun i : Fin n => w i.val) =
      payoffIncrement c (trajectory c w n) (w n) := by
  rw [freeMinimum_eq_overshoot hc w (n + 1), freeMinimum_eq_overshoot hc w n,
    Finset.sum_range_succ, trajectory, payoffIncrement]
  ring

theorem circumference_pos : 0 < circumference := by
  unfold circumference
  positivity

private abbrev phase (x : ℝ) : AddCircle circumference := (x : AddCircle circumference)

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x + phase y := rfl

/-- Every allowed starting phase has a positive rotation time at most N
whose representative lies strictly within the forbidden arc. -/
def UniformForbiddenHit (c : ℝ) (N : ℕ) : Prop :=
  ∀ x ∈ Icc (0 : ℝ) (2 * c), ∃ j : ℕ, 0 < j ∧ j ≤ N ∧
    ∃ y ∈ Ioo (2 * c) circumference, phase (x + (j : ℝ)) = phase y

private theorem phase_add_increment (x : ℝ) (b : Bool) :
    phase (x + increment b) = phase (x + 1) := by
  cases b with
  | false => rfl
  | true =>
      have h : x + increment true + circumference = x + 1 := by
        unfold increment circumference
        ring
      rw [← h]
      exact (AddCircle.coe_add_period (p := circumference) (x + increment true)).symm

private theorem not_forbidden_of_allowed {c x y : ℝ} (hW : 2 * c < circumference)
    (hx : x ∈ Icc 0 (2 * c)) (hy : y ∈ Ioo (2 * c) circumference) :
    phase x ≠ phase y := by
  have : Fact (0 < circumference) := ⟨circumference_pos⟩
  have hx' : x ∈ Ico (0 : ℝ) (0 + circumference) := ⟨hx.1, by simpa using hx.2.trans_lt hW⟩
  have hy' : y ∈ Ico (0 : ℝ) (0 + circumference) := by
    refine ⟨hx.1.trans (hx.2.trans hy.1.le), ?_⟩
    simpa using hy.2
  intro h
  have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico hx' hy').mp h
  exact (ne_of_lt (hx.2.trans_lt hy.1)) heq

/-- A zero overshoot is an actual unclipped step, including equality at
either endpoint. In the strict subcritical range at most one label does this. -/
theorem unclipped_label_unique {c x : ℝ} (hW : 2 * c < circumference) {a b : Bool}
    (ha : overshoot (2 * c) (x + increment a) = 0)
    (hb : overshoot (2 * c) (x + increment b) = 0) : a = b := by
  have ha' := (overshoot_eq_zero_iff _ _).mp ha
  have hb' := (overshoot_eq_zero_iff _ _).mp hb
  have ha₀ := ha'.1
  have ha₁ := ha'.2
  have hb₀ := hb'.1
  have hb₁ := hb'.2
  cases a <;> cases b <;> simp_all only [increment, circumference] <;> linarith

/-- Every block of length N on a physical score trajectory contains a
strictly positive overshoot. -/
theorem exists_overshoot_in_block {c : ℝ} (hc : 0 ≤ c) (hW : 2 * c < circumference)
    {N : ℕ} (hHit : UniformForbiddenHit c N) (w : ℕ → Bool) (start : ℕ) :
    ∃ j < N, 0 < overshoot (2 * c) (trajectory c w (start + j) + increment (w (start + j))) := by
  by_contra! h
  obtain ⟨k, _, hkN, y, hy, hky⟩ := hHit _ (trajectory_mem hc w start)
  have horbit : ∀ j ≤ k, phase (trajectory c w (start + j)) =
      phase (trajectory c w start + (j : ℝ)) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
        intro hj
        let raw := trajectory c w (start + j) + increment (w (start + j))
        have hz : overshoot (2 * c) raw = 0 :=
          le_antisymm (h j (by omega)) (overshoot_nonneg _ _)
        have hraw := (overshoot_eq_zero_iff _ _).mp hz
        have hclip : clip (2 * c) raw = raw := by
          simp [clip, max_eq_right hraw.1, min_eq_right hraw.2]
        change phase (clip (2 * c) raw) = _
        rw [hclip]
        change phase (trajectory c w (start + j) + increment (w (start + j))) = _
        rw [phase_add_increment, phase_add, ih (by omega), ← phase_add]
        push_cast
        rw [add_assoc]
  exact not_forbidden_of_allowed hW (trajectory_mem hc w (start + k)) hy
    ((horbit k le_rfl).trans hky)

def reachable (c : ℝ) : Set ℝ :=
  {x | ∃ (w : ℕ → Bool) (n : ℕ), trajectory c w n = x}

theorem reachable_step {c x : ℝ} (hx : x ∈ reachable c) (b : Bool) :
    step c x b ∈ reachable c := by
  obtain ⟨w, n, rfl⟩ := hx
  let v (i : ℕ) := if i = n then b else w i
  have hagree : ∀ k ≤ n, trajectory c v k = trajectory c w k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
        intro hk
        simp only [trajectory]
        rw [ih (by omega)]
        simp [v, show k ≠ n by omega]
  exact ⟨v, n + 1, by rw [trajectory, hagree n le_rfl]; simp [v]⟩

private def seed (c : ℝ) (i : Fin 3) : ℝ :=
  if i = 0 then c else if i = 1 then 0 else 2 * c

private theorem seed_mem {c : ℝ} (hc : 0 ≤ c) (i : Fin 3) :
    seed c i ∈ Icc 0 (2 * c) := by
  unfold seed
  split
  · exact ⟨hc, by linarith⟩
  · split <;> exact ⟨by linarith, by linarith⟩

/-- The current phase is a rotation of one of the three seeds. All phases
since that seed have representatives in the allowed arc. -/
private theorem trajectory_phase_certificate {c : ℝ} (hc : 0 ≤ c) (w : ℕ → Bool) (n : ℕ) :
    ∃ (i : Fin 3) (age : ℕ),
      phase (trajectory c w n) = phase (seed c i + (age : ℝ)) ∧
      ∀ j ≤ age, ∃ y ∈ Icc 0 (2 * c), phase y = phase (seed c i + (j : ℝ)) := by
  have atSeed (i : Fin 3) : ∀ j : ℕ, j ≤ 0 →
      ∃ y ∈ Icc 0 (2 * c), phase y = phase (seed c i + (j : ℝ)) := by
    intro j hj
    have hj0 : j = 0 := by omega
    exact ⟨seed c i, seed_mem hc i, by simp [hj0]⟩
  induction n with
  | zero => exact ⟨0, 0, by simp [seed, trajectory], atSeed 0⟩
  | succ n ih =>
      let y := trajectory c w n + increment (w n)
      change ∃ (i : Fin 3) (age : ℕ), phase (clip (2 * c) y) =
        phase (seed c i + (age : ℝ)) ∧
        ∀ j ≤ age, ∃ z ∈ Icc 0 (2 * c), phase z = phase (seed c i + (j : ℝ))
      by_cases hl : y < 0
      · have h10 : (1 : Fin 3) ≠ 0 := by decide
        exact ⟨1, 0, by simp [clip, max_eq_left hl.le,
          min_eq_right (show 0 ≤ 2 * c by linarith), seed, h10], atSeed 1⟩
      by_cases hu : 2 * c < y
      · have hy₀ : 0 ≤ y := le_of_not_gt hl
        have h20 : (2 : Fin 3) ≠ 0 := by decide
        have h21 : (2 : Fin 3) ≠ 1 := by decide
        exact ⟨2, 0, by simp [clip, max_eq_right hy₀, min_eq_left hu.le, seed, h20, h21],
          atSeed 2⟩
      obtain ⟨i, age, hphase, htrace⟩ := ih
      have hy : y ∈ Icc 0 (2 * c) := ⟨le_of_not_gt hl, le_of_not_gt hu⟩
      have hy' : phase y = phase (seed c i + ((age + 1 : ℕ) : ℝ)) := by
        change phase (trajectory c w n + increment (w n)) = _
        rw [phase_add_increment, phase_add, hphase, ← phase_add]
        push_cast
        rw [add_assoc]
      have hclip : clip (2 * c) y = y := by
        simp [clip, max_eq_right hy.1, min_eq_right hy.2]
      refine ⟨i, age + 1, by rw [hclip]; exact hy', ?_⟩
      intro j hj
      by_cases hja : j ≤ age
      · exact htrace j hja
      · have hje : j = age + 1 := by omega
        exact ⟨y, hy, by rw [hje]; exact hy'⟩

/-- A finite set of actual reachable reals, with a uniform cardinality
bound. Only the intermediate list of candidate lifts uses the rotation. -/
theorem reachable_finset_of_hit {c : ℝ} (hc : 0 ≤ c) (hW : 2 * c < circumference)
    {N : ℕ} (hHit : UniformForbiddenHit c N) :
    ∃ states : Finset ℝ, (↑states : Set ℝ) = reachable c ∧ states.card ≤ 3 * N := by
  classical
  have : Fact (0 < circumference) := ⟨circumference_pos⟩
  let representative (p : Fin 3 × Fin N) : ℝ :=
    (AddCircle.equivIco circumference 0 (phase (seed c p.1 + (p.2.val : ℝ)))).val
  let candidates := Finset.univ.image representative
  have hcover : ∀ x ∈ reachable c, x ∈ candidates := by
    intro x hx
    obtain ⟨w, n, rfl⟩ := hx
    obtain ⟨i, age, hphase, htrace⟩ := trajectory_phase_certificate hc w n
    have hage : age < N := by
      by_contra! hle
      obtain ⟨j, _, hjN, y, hy, hj⟩ := hHit _ (seed_mem hc i)
      obtain ⟨z, hz, hzj⟩ := htrace j (hjN.trans hle)
      exact not_forbidden_of_allowed hW hz hy (hzj.trans hj)
    have hx := trajectory_mem hc w n
    have hx' : trajectory c w n ∈ Ico (0 : ℝ) (0 + circumference) :=
      ⟨hx.1, by simpa using hx.2.trans_lt hW⟩
    refine Finset.mem_image.mpr ⟨(i, ⟨age, hage⟩), Finset.mem_univ _, ?_⟩
    change (AddCircle.equivIco circumference 0 (phase (seed c i + (age : ℝ)))).val = _
    rw [← hphase]
    exact AddCircle.equivIco_coe_of_mem hx'
  refine ⟨candidates.filter (· ∈ reachable c), ?_, ?_⟩
  · ext x
    simp only [Finset.mem_coe, Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨hcover x hx, hx⟩⟩
  · calc
      _ ≤ candidates.card := Finset.card_filter_le _ _
      _ ≤ (Finset.univ : Finset (Fin 3 × Fin N)).card := Finset.card_image_le
      _ = 3 * N := by simp

open D5.S1.Words.Mechanical (silverSlope silverPell_error_formula)
open D5.S1.Recurrence.PellCompanionGcd (P pell_companion_step companion_odd)

theorem circumference_mul_silverSlope : circumference * silverSlope = 1 := by
  unfold circumference silverSlope
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- A positive Pell return of size R times a power of the silver slope. -/
theorem silverPell_return (k : ℕ) :
    (P (2 * k + 1) : ℝ) =
      (P (2 * k) : ℝ) * circumference + circumference * silverSlope ^ (2 * k + 1) := by
  have heven : Even (2 * k) := ⟨k, by omega⟩
  have h := silverPell_error_formula (2 * k)
  rw [heven.neg_one_pow, one_mul] at h
  calc
    (P (2 * k + 1) : ℝ) = circumference * ((P (2 * k + 1) : ℝ) * silverSlope) := by
      rw [← mul_assoc, mul_comm circumference (P (2 * k + 1) : ℝ), mul_assoc,
        circumference_mul_silverSlope, mul_one]
    _ = (P (2 * k) : ℝ) * circumference + circumference * silverSlope ^ (2 * k + 1) := by
      have h' := congrArg (fun t : ℝ => circumference * t) h
      change circumference * ((P (2 * k + 1) : ℝ) * silverSlope - P (2 * k)) =
        circumference * silverSlope ^ (2 * k + 1) at h'
      rw [mul_sub] at h'
      linarith [h']

private theorem silverSlope_bounds : 0 < silverSlope ∧ silverSlope < 1 := by
  unfold silverSlope
  have hl : (1 : ℝ) < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
  have hu : Real.sqrt (2 : ℝ) < 2 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  constructor <;> linarith

/-- A small positive Pell return, repeated enough times to cross the first
quarter of the forbidden arc. The bound is uniform over all allowed starts. -/
theorem uniformForbiddenHit_pell {c : ℝ} (hW : 2 * c < circumference) :
    ∃ N : ℕ, UniformForbiddenHit c N := by
  obtain ⟨hα₀, hα₁⟩ := silverSlope_bounds
  let gap := circumference - 2 * c
  have hgap : 0 < gap := sub_pos.mpr hW
  have hfour : 0 < 4 * circumference := mul_pos (by norm_num) circumference_pos
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hgap hfour) hα₁
  let q := P (2 * k + 1)
  let p := P (2 * k)
  let d := circumference * silverSlope ^ (2 * k + 1)
  have hd : 0 < d := mul_pos circumference_pos (pow_pos hα₀ _)
  have hq : 0 < q := by
    have hstep := (pell_companion_step (2 * k)).1
    obtain ⟨m, hm⟩ := companion_odd (2 * k)
    dsimp only [q]
    omega
  have hsmall : d < gap / 4 := by
    have hpow : silverSlope ^ (2 * k + 1) ≤ silverSlope ^ k := by
      rw [show 2 * k + 1 = k + (k + 1) by omega, pow_add]
      exact mul_le_of_le_one_right (pow_nonneg hα₀.le _) (pow_le_one₀ hα₀.le hα₁.le)
    have hprod := (lt_div_iff₀ hfour).mp hk
    have hprod' := mul_le_mul_of_nonneg_left hpow circumference_pos.le
    dsimp only [d]
    linarith only [hprod, hprod']
  let M := ⌈circumference / d⌉₊
  refine ⟨M * q, ?_⟩
  intro x hx
  let m := ⌈(2 * c + gap / 4 - x) / d⌉₊
  have hpositive : 0 < (2 * c + gap / 4 - x) / d :=
    div_pos (by linarith [hx.2]) hd
  have hm : 0 < m := Nat.ceil_pos.mpr hpositive
  have hmM : m ≤ M := by
    apply Nat.ceil_mono
    apply (div_le_div_iff_of_pos_right hd).mpr
    dsimp only [gap]
    linarith [hx.1]
  let y := x + (m : ℝ) * d
  have hy₁ : 2 * c + gap / 4 - x ≤ (m : ℝ) * d :=
    (div_le_iff₀ hd).mp (Nat.le_ceil ((2 * c + gap / 4 - x) / d))
  have hy₂ := (lt_div_iff₀ hd).mp
    (show (m : ℝ) - 1 < (2 * c + gap / 4 - x) / d from
      by linarith only [Nat.ceil_lt_add_one hpositive.le])
  have hyLower : 2 * c + gap / 4 ≤ y := by
    dsimp only [y]
    linarith only [hy₁]
  have hyUpper : y < 2 * c + gap / 2 := by
    dsimp only [y]
    linarith only [hy₂, hsmall]
  refine ⟨m * q, Nat.mul_pos hm hq, Nat.mul_le_mul_right q hmM, y, ⟨?_, ?_⟩, ?_⟩
  · linarith only [hyLower, hgap]
  · dsimp only [gap] at hyUpper
    linarith only [hyUpper, hW]
  have hreturn : (q : ℝ) = (p : ℝ) * circumference + d := silverPell_return k
  have hperiod : phase ((m * p : ℕ) • circumference) = 0 := by
    change (((m * p : ℕ) • circumference : ℝ) : AddCircle circumference) = 0
    rw [AddCircle.coe_nsmul, AddCircle.coe_period, nsmul_zero]
  have hsum : x + ((m * q : ℕ) : ℝ) = y + (m * p : ℕ) • circumference := by
    rw [nsmul_eq_mul, Nat.cast_mul, Nat.cast_mul, hreturn]
    dsimp only [y]
    ring
  rw [hsum, phase_add, hperiod, add_zero]

end

end MeyerovitchYoungQ61Subcritical
