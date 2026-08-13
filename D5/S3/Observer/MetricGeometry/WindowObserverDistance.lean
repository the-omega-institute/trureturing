/- GID: D5/S3/Observer/MetricGeometry/WindowObserverDistance
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Cyclic distances are exact; LP window costs have exact unbounded one-third growth. -/

import D5.S1.Depth.FiniteMetric
import D5.S3.Observer.ObserverMetric
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace D5.S3.Observer.MetricGeometry.WindowObserverDistance

open Set
open D5.S1.Depth
open D5.S3.Observer.ObserverMetric

def windowCycleDist (M : ℕ) [NeZero M] (a b : ZMod M) : ℕ :=
  phaseDist ⟨a.val, ZMod.val_lt a⟩ ⟨b.val, ZMod.val_lt b⟩

/-- The frozen observer-metric unit ball on the finite cyclic window. -/
def windowLipBall (M : ℕ) [NeZero M] : Set (ZMod M → Real) :=
  {f | perturbationSeminorm (Equiv.addRight (1 : ZMod M))
    (fun i => (f i : Complex)) ≤ 1}

/-- The all-pairs cyclic-Lipschitz ball. The bridge below identifies it with the
frozen update-defect ball `windowLipBall`. -/
def cyclicLipBall (M : ℕ) [NeZero M] : Set (ZMod M → Real) :=
  {f | ∀ a b, dist (f a) (f b) ≤ windowCycleDist M a b}

private theorem windowCycleDist_add_one_le (M : ℕ) [NeZero M] (a : ZMod M) :
    windowCycleDist M a (a + 1) ≤ 1 := by
  unfold windowCycleDist phaseDist
  change min (Nat.dist a.val (a + 1).val)
    (M - Nat.dist a.val (a + 1).val) ≤ 1
  by_cases hM : M = 1
  · subst M
    fin_cases a
    decide
  have hOne : (1 : ZMod M).val = 1 := ZMod.val_one'' hM
  by_cases h : a.val + 1 < M
  · have hvalRaw := ZMod.val_add_of_lt (a := a) (b := (1 : ZMod M))
        (by simpa only [hOne] using h)
    have hval : (a + 1).val = a.val + 1 := by simpa only [hOne] using hvalRaw
    rw [hval]
    simp only [Nat.dist]
    omega
  · have hvalRaw := ZMod.val_add_of_le (a := a) (b := (1 : ZMod M))
        (by simpa only [hOne] using (Nat.le_of_not_gt h))
    have hval : (a + 1).val = a.val + 1 - M := by simpa only [hOne] using hvalRaw
    have ha := ZMod.val_lt a
    rw [hval]
    simp only [Nat.dist]
    omega

private theorem windowLipBall_unit_update_defect {M : ℕ} [NeZero M]
    {f : ZMod M → Real} (hf : f ∈ windowLipBall M) (k : ZMod M) :
    dist (f (k + 1)) (f k) ≤ 1 := by
  have hk :
      ‖updateDefect (Equiv.addRight (1 : ZMod M))
        (fun i => (f i : Complex)) (k + 1)‖ ≤
        perturbationSeminorm (Equiv.addRight (1 : ZMod M))
          (fun i => (f i : Complex)) :=
    Finset.le_sup'
      (fun i => ‖updateDefect (Equiv.addRight (1 : ZMod M))
        (fun j => (f j : Complex)) i‖) (Finset.mem_univ (k + 1))
  refine (show dist (f (k + 1)) (f k) ≤
      perturbationSeminorm (Equiv.addRight (1 : ZMod M))
        (fun i => (f i : Complex)) from ?_).trans hf
  simpa [updateDefect, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, Real.dist_eq, abs_sub_comm] using hk

private theorem dist_le_natCast_of_add_nat {M : ℕ} [NeZero M] {f : ZMod M → Real}
    (hstep : ∀ k, dist (f (k + 1)) (f k) ≤ 1) (a : ZMod M) (d : ℕ) :
    dist (f a) (f (a + d)) ≤ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        dist (f a) (f (a + (d.succ : ZMod M))) ≤
            dist (f a) (f (a + d)) +
              dist (f (a + d)) (f (a + (d.succ : ZMod M))) := dist_triangle _ _ _
        _ ≤ (d : Real) + 1 := by
          gcongr
          simpa [Nat.cast_succ, dist_comm, add_assoc] using hstep (a + d)
        _ = (d.succ : Real) := by simp

private theorem windowLipBall_dist_le {M : ℕ} [NeZero M] {f : ZMod M → Real}
    (hf : f ∈ windowLipBall M) (a b : ZMod M) :
    dist (f a) (f b) ≤ windowCycleDist M a b := by
  let d := Nat.dist a.val b.val
  have hdM : d ≤ M := by
    have ha := ZMod.val_le a
    have hb := ZMod.val_le b
    dsimp [d]
    simp only [Nat.dist]
    omega
  have hforward : dist (f a) (f b) ≤ (d : Real) := by
    rcases le_total a.val b.val with hab | hba
    · have hab' : a + (d : ZMod M) = b := by
        rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, ← Nat.cast_add]
        congr 1
        simp only [d, Nat.dist]
        omega
      rw [← hab']
      exact dist_le_natCast_of_add_nat (windowLipBall_unit_update_defect hf) a d
    · have hba' : b + (d : ZMod M) = a := by
        rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, ← Nat.cast_add]
        congr 1
        simp only [d, Nat.dist]
        omega
      rw [dist_comm, ← hba']
      exact dist_le_natCast_of_add_nat (windowLipBall_unit_update_defect hf) b d
  have hbackward : dist (f a) (f b) ≤ ((M - d : ℕ) : Real) := by
    rcases le_total a.val b.val with hab | hba
    · have hab' : a + (d : ZMod M) = b := by
        rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, ← Nat.cast_add]
        congr 1
        simp only [d, Nat.dist]
        omega
      have hcycle : b + (M - d : ℕ) = a := by
        rw [← hab', add_assoc, ← Nat.cast_add, Nat.add_sub_of_le hdM,
          ZMod.natCast_self, add_zero]
      rw [dist_comm, ← hcycle]
      exact dist_le_natCast_of_add_nat (windowLipBall_unit_update_defect hf) b (M - d)
    · have hba' : b + (d : ZMod M) = a := by
        rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, ← Nat.cast_add]
        congr 1
        simp only [d, Nat.dist]
        omega
      have hcycle : a + (M - d : ℕ) = b := by
        rw [← hba', add_assoc, ← Nat.cast_add, Nat.add_sub_of_le hdM,
          ZMod.natCast_self, add_zero]
      rw [← hcycle]
      exact dist_le_natCast_of_add_nat (windowLipBall_unit_update_defect hf) a (M - d)
  change dist (f a) (f b) ≤ (min d (M - d) : ℕ)
  rw [Nat.cast_min]
  exact le_min hforward hbackward

/-- On a finite cyclic window, the frozen update-defect constraint is equivalent to
the all-pairs cyclic-Lipschitz constraint. -/
theorem windowLipBall_eq_cyclicLipBall (M : ℕ) [NeZero M] :
    windowLipBall M = cyclicLipBall M := by
  ext f
  constructor
  · intro hf a b
    exact windowLipBall_dist_le hf a b
  · intro hf
    change perturbationSeminorm (Equiv.addRight (1 : ZMod M))
      (fun i => (f i : Complex)) ≤ 1
    apply Finset.sup'_le
    intro k _
    have hgap := hf (k - 1) k
    have hcycle : windowCycleDist M (k - 1) k ≤ 1 := by
      simpa only [sub_add_cancel] using windowCycleDist_add_one_le M (k - 1)
    have hcycleReal : (windowCycleDist M (k - 1) k : Real) ≤ 1 := by
      exact_mod_cast hcycle
    have hdist : dist (f (k - 1)) (f k) ≤ 1 := hgap.trans hcycleReal
    simp only [updateDefect, Equiv.addRight_symm_apply]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [Real.dist_eq, sub_eq_add_neg] using hdist

def windowGapSet (M : ℕ) [NeZero M] (a b : ZMod M) : Set Real :=
  {r | ∃ f ∈ windowLipBall M, r = dist (f a) (f b)}

noncomputable def windowObserverDistance (M : ℕ) [NeZero M] (a b : ZMod M) : Real :=
  sSup (windowGapSet M a b)

private theorem windowGapSet_nonempty (M : ℕ) [NeZero M] (a b : ZMod M) :
    (windowGapSet M a b).Nonempty := by
  refine ⟨0, fun _ => 0, ?_, by simp⟩
  change perturbationSeminorm (Equiv.addRight (1 : ZMod M))
    (fun _ => (0 : Complex)) ≤ 1
  simp [perturbationSeminorm, updateDefect]

private theorem windowGapSet_le (M : ℕ) [NeZero M] (a b : ZMod M) {r : Real}
    (hr : r ∈ windowGapSet M a b) : r ≤ windowCycleDist M a b := by
  rcases hr with ⟨f, hf, rfl⟩
  rw [windowLipBall_eq_cyclicLipBall] at hf
  exact hf a b

def clippedWindowDistance (M : ℕ) [NeZero M] (a : ZMod M) : ZMod M → Real :=
  fun k => windowCycleDist M a k

private theorem clippedWindowDistance_mem (M : ℕ) [NeZero M] (a : ZMod M) :
    clippedWindowDistance M a ∈ windowLipBall M := by
  rw [windowLipBall_eq_cyclicLipBall]
  intro x y
  unfold clippedWindowDistance
  rw [Real.dist_eq]
  have hxy := phaseDist_triangle
    (⟨a.val, ZMod.val_lt a⟩) (⟨x.val, ZMod.val_lt x⟩) (⟨y.val, ZMod.val_lt y⟩)
  have hyx := phaseDist_triangle
    (⟨a.val, ZMod.val_lt a⟩) (⟨y.val, ZMod.val_lt y⟩) (⟨x.val, ZMod.val_lt x⟩)
  unfold windowCycleDist at hxy hyx ⊢
  have hcomm : phaseDist ⟨y.val, ZMod.val_lt y⟩ ⟨x.val, ZMod.val_lt x⟩ =
      phaseDist ⟨x.val, ZMod.val_lt x⟩ ⟨y.val, ZMod.val_lt y⟩ := phaseDist_comm _ _
  rw [abs_le]
  constructor
  · have hn : -(phaseDist ⟨x.val, ZMod.val_lt x⟩ ⟨y.val, ZMod.val_lt y⟩ : ℤ) ≤
        phaseDist ⟨a.val, ZMod.val_lt a⟩ ⟨x.val, ZMod.val_lt x⟩ -
          phaseDist ⟨a.val, ZMod.val_lt a⟩ ⟨y.val, ZMod.val_lt y⟩ := by omega
    exact_mod_cast hn
  · have hn :
      phaseDist ⟨a.val, ZMod.val_lt a⟩ ⟨x.val, ZMod.val_lt x⟩ -
          phaseDist ⟨a.val, ZMod.val_lt a⟩ ⟨y.val, ZMod.val_lt y⟩ ≤
        (phaseDist ⟨x.val, ZMod.val_lt x⟩ ⟨y.val, ZMod.val_lt y⟩ : ℤ) := by omega
    exact_mod_cast hn

private theorem clippedWindowDistance_attains (M : ℕ) [NeZero M] (a b : ZMod M) :
    dist (clippedWindowDistance M a a) (clippedWindowDistance M a b) =
      windowCycleDist M a b := by
  unfold clippedWindowDistance
  simp [windowCycleDist, Real.dist_eq, phaseDist]

private theorem windowGapSet_bddAbove (M : ℕ) [NeZero M] (a b : ZMod M) :
    BddAbove (windowGapSet M a b) :=
  ⟨(windowCycleDist M a b : Real), fun _ => windowGapSet_le M a b⟩

private theorem windowGapSet_attains (M : ℕ) [NeZero M] (a b : ZMod M) :
    (windowCycleDist M a b : Real) ∈ windowGapSet M a b := by
  refine ⟨clippedWindowDistance M a, clippedWindowDistance_mem M a, ?_⟩
  exact (clippedWindowDistance_attains M a b).symm

theorem window_observer_distance_eq_cycle_distance (M : ℕ) [NeZero M]
    (a b : ZMod M) : windowObserverDistance M a b = windowCycleDist M a b := by
  apply le_antisymm
  · exact csSup_le (windowGapSet_nonempty M a b) (fun _ hr => windowGapSet_le M a b hr)
  · exact le_csSup (windowGapSet_bddAbove M a b) (windowGapSet_attains M a b)

theorem window_twelve_antipode_witness :
    ∃ f ∈ windowLipBall 12, f 0 ≠ f 6 ∧ dist (f 0) (f 6) = 6 := by
  let f := clippedWindowDistance 12 (0 : ZMod 12)
  have hf : f ∈ windowLipBall 12 := clippedWindowDistance_mem 12 0
  have hgap : dist (f 0) (f 6) = 6 := by
    change dist ((windowCycleDist 12 (0 : ZMod 12) 0 : ℕ) : Real)
      ((windowCycleDist 12 (0 : ZMod 12) 6 : ℕ) : Real) = 6
    have h0 : windowCycleDist 12 (0 : ZMod 12) 0 = 0 := by
      norm_num [windowCycleDist, phaseDist]
    have h6 : windowCycleDist 12 (0 : ZMod 12) 6 = 6 := by
      change min (Nat.dist 0 6) (12 - Nat.dist 0 6) = 6
      norm_num [Nat.dist]
    rw [h0, h6]
    norm_num
  refine ⟨f, hf, ?_, hgap⟩
  intro h
  rw [h, dist_self] at hgap
  norm_num at hgap

theorem window_wrap_unit_check : windowCycleDist 12 (0 : ZMod 12) 11 = 1 := by
  change min (Nat.dist 0 11) (12 - Nat.dist 0 11) = 1
  norm_num [Nat.dist]

/-- The self-contained cost of the `n - 1` adjacent steps in a nonempty `n`-window.
No frozen `c_n` family exists in the observer metric modules, so this definition is not
an identification with the external LP data. -/
def lpWindowCost (n : ℕ) (x : ℝ) : ℝ :=
  (n - 1 : ℕ) * (-x)

private theorem lp_window_cost_double {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    lpWindowCost (n * 2) x = 2 * lpWindowCost n x - x := by
  unfold lpWindowCost
  rw [Nat.cast_sub hn, Nat.cast_sub (by omega : 1 ≤ n * 2), Nat.cast_mul]
  norm_num
  ring

theorem lp_window_cost_power_two_exact (m : ℕ) :
    lpWindowCost (2 ^ m) (-1 / 3 : ℝ) = ((2 : ℝ) ^ m - 1) / 3 := by
  induction m with
  | zero => norm_num [lpWindowCost]
  | succ m ih =>
      rw [pow_succ, lp_window_cost_double (Nat.one_le_two_pow), ih]
      ring

theorem lp_window_cost_power_two_unbounded (B : ℝ) :
    ∃ m : ℕ, B < ((2 : ℝ) ^ m - 1) / 3 := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (3 * B + 1) (by norm_num : (1 : ℝ) < 2)
  refine ⟨m, ?_⟩
  linarith

theorem lp_window_cost_four : lpWindowCost 4 (-1 / 3 : ℝ) = 1 := by
  norm_num [lpWindowCost]

end D5.S3.Observer.MetricGeometry.WindowObserverDistance
