/- GID: D5/S3/Combinatorics/Graph/RollingSpanOneLower
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A single full spine in a span-one retention graph has lanes with common endpoints. -/

import D5.S3.Combinatorics.Graph.RollingSpanOne
import D5.S3.Combinatorics.Graph.L1BalancedRadius
import Mathlib.Algebra.Order.Archimedean.Basic

compile_only_with_mathlib

/-! Omega original.

A single full spine in a span-one retention graph has lanes with common
endpoints. Gains defined by depth give all lanes the prescribed large
potential displacement, and the triangle bound holds on the full graph.
-/
namespace Omega.RollingCliques.SpanOne
open SimpleGraph
noncomputable section

variable {M n k : ℕ} {hM : 2 ≤ M}

private theorem depth_adj {u v : Vertex M n k hM} (h : (graph M n k hM).Adj u v) :
    u.1.stage.val ≤ v.1.stage.val + 1 ∧ v.1.stage.val ≤ u.1.stage.val + 1 := by
  rcases h.2 with he | ⟨hab, _⟩ | ⟨hba, _⟩
  · rw [he]
    omega
  · by_cases he : u.1 = v.1
    · rw [he]
      omega
    obtain ⟨hp, _, hz⟩ := edge_parent hab he h
    have hh : u.1.stage.val = v.1.stage.val - 1 := congrArg (fun b => b.stage.val) hp
    omega
  · by_cases he : v.1 = u.1
    · rw [he]
      omega
    obtain ⟨hp, _, hz⟩ := edge_parent hba he h.symm
    have hh : v.1.stage.val = u.1.stage.val - 1 := congrArg (fun b => b.stage.val) hp
    omega

private def spine (M n k : ℕ) (hM : 2 ≤ M) (i : ℕ) : Block M n k hM :=
  (fullSpine 1 n M k le_rfl (Nat.le_trans (by decide : 1 ≤ 2) hM)).prefix
    ⟨min i n, (min_le_right i n).trans_lt (Nat.lt_succ_self n)⟩ (min_le_right i n)

private theorem spine_depth (i : ℕ) (hi : i ≤ n) :
    (spine M n k hM i).stage.val = i :=
  min_eq_left hi

private theorem spine_adj (j : ℕ) (hj : j + 1 ≤ n)
    (a b : Label M) (ha : a.val < M ^ 2) :
    (graph M n k hM).Adj (spine M n k hM j, a) (spine M n k hM (j + 1), b) := by
  have h₀ := spine_depth (M := M) (k := k) (hM := hM) j (by omega : j ≤ n)
  have h₁ := spine_depth (M := M) (k := k) (hM := hM) (j + 1) hj
  have hlt : (spine M n k hM j).stage < (spine M n k hM (j + 1)).stage := by
    change (spine M n k hM j).stage.val < (spine M n k hM (j + 1)).stage.val
    omega
  refine ⟨fun h => hlt.ne (congrArg (fun v => v.1.stage) h), Or.inr (Or.inl ⟨?_, ?_⟩)⟩
  · refine ⟨hlt.le, fun i hi => ?_⟩
    change i ≤ (spine M n k hM j).stage at hi
    have hi' := hi.trans hlt.le
    change (if i ≤ (spine M n k hM j).stage then
        (fullSpine 1 n M k le_rfl (Nat.le_trans (by decide : 1 ≤ 2) hM)).step i else
        rootStep n (M ^ (1 + 2)) k) = (if i ≤ (spine M n k hM (j + 1)).stage then
        (fullSpine 1 n M k le_rfl (Nat.le_trans (by decide : 1 ≤ 2) hM)).step i else
        rootStep n (M ^ (1 + 2)) k)
    rw [ite_eq_left hi, ite_eq_left hi']
  · change a ∈ ((spine M n k hM (j + 1)).step
      (spine M n k hM (j + 1)).stage).1 (spine M n k hM j).stage
    rw [show ((spine M n k hM (j + 1)).step (spine M n k hM (j + 1)).stage) =
        (fullSpine 1 n M k le_rfl (Nat.le_trans (by decide : 1 ≤ 2) hM)).step (spine M n k hM (j + 1)).stage by
      simp [spine, History.prefix]]
    change a ∈ (Finset.univ : Finset (Fin (quota 1 M
      (spine M n k hM j).stage.val (spine M n k hM (j + 1)).stage.val))).map _
    refine Finset.mem_map.mpr ⟨⟨a.val, ?_⟩, Finset.mem_univ _, Fin.ext rfl⟩
    rw [h₀, h₁]
    simpa [quota] using ha

private def depthGain {V E : Type*} [AddCommGroup E] (d : V → ℕ) (x : V → E)
    (v w : V) : E :=
  if d v < d w then x v + x w else if d w < d v then -(x w + x v) else 0

private theorem depthGain_skew {V E : Type*} [AddCommGroup E] (d : V → ℕ) (x : V → E)
    (v w : V) : depthGain d x w v = -depthGain d x v w := by
  rcases lt_trichotomy (d v) (d w) with h | h | h
  · simp [depthGain, h, h.not_gt]
  · simp [depthGain, h]
  · simp [depthGain, h, h.not_gt]

private theorem depthGain_triangle {V E : Type*} [SeminormedAddCommGroup E]
    (d : V → ℕ) (x : V → E)
    (hd : ∀ a b, d a = d b → ‖x a - x b‖ ≤ 1) (a b c : V)
    (hab : d a ≤ d b + 1 ∧ d b ≤ d a + 1)
    (hbc : d b ≤ d c + 1 ∧ d c ≤ d b + 1)
    (hac : d a ≤ d c + 1 ∧ d c ≤ d a + 1) :
    ‖depthGain d x a b + depthGain d x b c - depthGain d x a c‖ ≤ 1 := by
  let g := depthGain d x
  have ordered (a b c : V) (hab : d a ≤ d b) (hbc : d b ≤ d c)
      (hac : d c ≤ d a + 1) :
      ‖g a b + g b c - g a c‖ ≤ 1 := by
    rcases eq_or_lt_of_le hab with h | h
    · rcases eq_or_lt_of_le hbc with he | he
      · simp [g, depthGain, h, he]
      · change ‖depthGain d x a b + depthGain d x b c - depthGain d x a c‖ ≤ 1
        simp only [depthGain, h, lt_irrefl, ite_false, he, ite_true, zero_add]
        rw [show x b + x c - (x a + x c) = x b - x a by abel]
        exact hd _ _ h.symm
    · have he : d b = d c := by omega
      change ‖depthGain d x a b + depthGain d x b c - depthGain d x a c‖ ≤ 1
      simp only [depthGain, ← he, lt_irrefl, ite_false, h, ite_true, add_zero]
      rw [show x a + x b - (x a + x c) = x b - x c by abel]
      exact hd _ _ he
  have swapFirst (u v w : V) :
      ‖g v u + g u w - g v w‖ = ‖g u v + g v w - g u w‖ := by
    rw [show g v u = -g u v from depthGain_skew d x u v,
      ← norm_neg (g u v + g v w - g u w)]
    congr 1
    abel
  have swapLast (u v w : V) :
      ‖g u w + g w v - g u v‖ = ‖g u v + g v w - g u w‖ := by
    rw [show g w v = -g v w from depthGain_skew d x v w,
      ← norm_neg (g u v + g v w - g u w)]
    congr 1
    abel
  change ‖g a b + g b c - g a c‖ ≤ 1
  rcases le_total (d a) (d b) with h₁ | h₁
  · rcases le_total (d b) (d c) with h₂ | h₂
    · exact ordered a b c h₁ h₂ hac.2
    · rcases le_total (d a) (d c) with h₃ | h₃
      · rw [← swapLast a b c]
        exact ordered a c b h₃ h₂ hab.2
      · rw [← swapLast a b c, ← swapFirst a c b]
        exact ordered c a b h₃ h₁ hbc.1
  · rcases le_total (d a) (d c) with h₃ | h₃
    · rw [swapFirst b a c]
      exact ordered b a c h₁ h₃ hbc.2
    · rcases le_total (d b) (d c) with h₂ | h₂
      · rw [swapFirst b a c, ← swapLast b a c]
        exact ordered b c a h₂ h₃ hab.1
      · rw [swapFirst b a c, ← swapLast b a c, ← swapFirst b c a]
        exact ordered c b a h₂ h₁ hac.1

/-- A normalized finite family of diameter at most one gives parallel gain
displacements on the full span-one graph. Every lane starts and ends at the
same two vertices. -/
theorem spine_radius_obstruction {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℕ) (hM : 2 ≤ M) (L : ℕ) (hL : 0 < L) (k : ℕ)
    {r : ℕ} (hr : 0 < r) (hrM : r ≤ M ^ 2) (x : Fin r → E)
    (hx : ∀ a b, ‖x a - x b‖ ≤ 1) :
    ∃ g : Vertex M (L + 1) k hM → Vertex M (L + 1) k hM → E,
      (∀ u v, g v u = -g u v) ∧
      (∀ u v w, (graph M (L + 1) k hM).Adj u v →
        (graph M (L + 1) k hM).Adj v w →
        (graph M (L + 1) k hM).Adj u w → ‖g u v + g v w - g u w‖ ≤ 1) ∧
      ∀ (p : Vertex M (L + 1) k hM → E) (C : ℝ),
        (∀ u v, (graph M (L + 1) k hM).Adj u v →
          ‖g u v - (p v - p u)‖ ≤ C) →
        ∃ y : E, ∀ a, ‖(2 : ℝ) • x a - y‖ ≤ ((L : ℝ) + 1) / L * C := by
  let V := Vertex M (L + 1) k hM
  let d (u : V) := u.1.stage.val
  have hcap : r ≤ M ^ (1 + 2) := hrM.trans (pow_le_pow_right' (by omega) (by omega))
  let includeLabel (a : Fin r) : Label M := Fin.castLE hcap a
  let proj (a : Label M) : Fin r := ⟨a.val % r, Nat.mod_lt _ hr⟩
  have proj_include (a : Fin r) : proj (includeLabel a) = a :=
    Fin.ext (Nat.mod_eq_of_lt a.isLt)
  let active (u : V) := if 0 < d u ∧ d u < L + 1 then x (proj u.2) else 0
  let g := depthGain d active
  have active_diam (u v : V) (h : d u = d v) : ‖active u - active v‖ ≤ 1 := by
    simp only [active, h]
    split
    · exact hx _ _
    · simp
  refine ⟨g, depthGain_skew d active, fun a b c hab hbc hac =>
    depthGain_triangle d active active_diam a b c (depth_adj hab) (depth_adj hbc) (depth_adj hac), ?_⟩
  intro p C hp
  let z : Fin r := ⟨0, hr⟩
  let waypoint (a : Fin r) (i : ℕ) : V :=
    (spine M (L + 1) k hM i, includeLabel (if 0 < i ∧ i < L + 1 then a else z))
  have wd (a : Fin r) (j : ℕ) (hj : j ≤ L + 1) : d (waypoint a j) = j :=
    spine_depth j hj
  have wa (a : Fin r) (j : ℕ) (hj : j ≤ L + 1) :
      active (waypoint a j) = if 0 < j ∧ j < L + 1 then x a else 0 := by
    simp only [active, wd a j hj]
    split
    · rename_i h
      simp [waypoint, h, proj_include]
    · rfl
  have edge (a : Fin r) (j : ℕ) (hj : j + 1 ≤ L + 1) :
      (graph M (L + 1) k hM).Adj (waypoint a j) (waypoint a (j + 1)) :=
    spine_adj j hj _ _ (((if 0 < j ∧ j < L + 1 then a else z) : Fin r).isLt.trans_le hrM)
  have forward (a : Fin r) (j : ℕ) (hj : j + 1 ≤ L + 1) :
      g (waypoint a j) (waypoint a (j + 1)) =
        active (waypoint a j) + active (waypoint a (j + 1)) := by
    simp [g, depthGain, wd a j (by omega : j ≤ L + 1), wd a (j + 1) hj]
  have along (a : Fin r) (j : ℕ) (hj : j ≤ L + 1) :
      ‖(2 * (min L (j - 1) : ℕ) : ℝ) • x a + active (waypoint a j) -
        (p (waypoint a j) - p (waypoint a 0))‖ ≤ (j : ℝ) * C := by
    induction j with
    | zero => simp [wa]
    | succ j ih =>
      have hj' : j ≤ L + 1 := by omega
      have h := hp _ _ (edge a j hj)
      rw [forward a j hj] at h
      have hid :
          (2 * (min L (j - 1) : ℕ) : ℝ) • x a + active (waypoint a j) +
              active (waypoint a j) =
            (2 * (min L (j + 1 - 1) : ℕ) : ℝ) • x a := by
        by_cases hzero : j = 0
        · subst j
          simp [wa]
        · have hjL : j ≤ L := by omega
          rw [wa a j hj', ite_eq_left (by omega), Nat.add_sub_cancel,
            min_eq_right (by omega : j - 1 ≤ L), min_eq_right hjL]
          rw [show (2 * (j : ℝ)) = 2 * ((j - 1 : ℕ) : ℝ) + 2 by
            rw [Nat.cast_sub (by omega : 1 ≤ j)]
            push_cast
            ring, add_smul, two_smul]
          abel
      rw [show (2 * (min L (j + 1 - 1) : ℕ) : ℝ) • x a +
            active (waypoint a (j + 1)) -
              (p (waypoint a (j + 1)) - p (waypoint a 0)) =
            ((2 * (min L (j - 1) : ℕ) : ℝ) • x a + active (waypoint a j) -
              (p (waypoint a j) - p (waypoint a 0))) +
            ((active (waypoint a j) + active (waypoint a (j + 1))) -
              (p (waypoint a (j + 1)) - p (waypoint a j))) by
          rw [← hid]
          abel]
      exact (norm_add_le _ _).trans ((add_le_add (ih hj') h).trans_eq (by push_cast; ring))
  let y := (L : ℝ)⁻¹ • (p (waypoint z (L + 1)) - p (waypoint z 0))
  refine ⟨y, fun a => ?_⟩
  have hend : waypoint a (L + 1) = waypoint z (L + 1) := by simp [waypoint]
  have hstart : waypoint a 0 = waypoint z 0 := by simp [waypoint]
  have ha := along a (L + 1) le_rfl
  rw [wa a (L + 1) le_rfl, ite_eq_right (by omega), add_zero, Nat.add_sub_cancel, min_self,
    hend, hstart] at ha
  have hLR : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have he : (2 : ℝ) • x a - y = (L : ℝ)⁻¹ • ((2 * (L : ℝ)) • x a -
      (p (waypoint z (L + 1)) - p (waypoint z 0))) := by
    rw [smul_sub, smul_smul, mul_comm (2 : ℝ) (L : ℝ), ← mul_assoc,
      inv_mul_cancel₀ hLR.ne', one_mul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (L : ℝ)⁻¹)]
  calc
    _ ≤ (L : ℝ)⁻¹ * (((L : ℝ) + 1) * C) := mul_le_mul_of_nonneg_left (by exact_mod_cast ha) (by positivity)
    _ = ((L : ℝ) + 1) / L * C := by ring

abbrev BalancedTarget (M : ℕ) :=
  PiLp 1 (fun _ : ChordalL1.BalancedCutCoordinate (M ^ 2 / 2) => ℝ)

/-- A common normalized reconstruction bound for all depths and copy counts
of the span-one rolling clique graph. -/
def IsUniformL1Bound (M : ℕ) (hM : 2 ≤ M) (C : ℝ) : Prop :=
  ∀ n k, ∀ g : Vertex M n k hM → Vertex M n k hM → BalancedTarget M,
    (∀ u v, g v u = -g u v) →
    (∀ u v w, (graph M n k hM).Adj u v → (graph M n k hM).Adj v w →
      (graph M n k hM).Adj u w → ‖g u v + g v w - g u w‖ ≤ 1) →
    ∃ p : Vertex M n k hM → BalancedTarget M, ∀ u v, (graph M n k hM).Adj u v →
      ‖g u v - (p v - p u)‖ ≤ C

/-- The parallel-lane obstruction converges to the span-one upper bound at
every even label parameter. -/
theorem uniform_l1_lower (M : ℕ) (hM : 2 ≤ M) (heven : Even M) (C : ℝ)
    (hC : IsUniformL1Bound M hM C) :
    2 - 2 / (M : ℝ)^2 ≤ C := by
  let m := M ^ 2 / 2
  have hs : 2 * m = M ^ 2 := by
    rcases heven with ⟨a, ha⟩
    have hsq : M ^ 2 = 2 * (a * M) := by
      calc
        M ^ 2 = M * M := by ring
        _ = 2 * (a * M) := by rw [ha]; ring
    dsimp [m]
    omega
  have hm : 0 < m := by
    have hpow : 0 < M ^ 2 := pow_pos (by omega) _
    omega
  have hsR : (2 * (m : ℝ)) = (M : ℝ)^2 := by exact_mod_cast hs
  let B : ℝ := 2 - 2 / (M : ℝ)^2
  obtain ⟨x, hx, hr⟩ := ChordalL1.exists_balanced_l1_family m hm
  by_contra! hbad
  change C < B at hbad
  obtain ⟨j, hj⟩ := exists_nat_gt (C / (B - C))
  let L := j + 1
  have hL : 0 < L := Nat.succ_pos j
  have hLR : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  have hj' : C / (B - C) < (L : ℝ) :=
    hj.trans_le (Nat.cast_le.mpr (Nat.le_succ j))
  obtain ⟨g, hrev, htri, hobs⟩ := spine_radius_obstruction
    M hM L hL 0 (show 0 < 2 * m by omega) hs.le x hx
  obtain ⟨p, hp⟩ := hC (L + 1) 0 g hrev htri
  obtain ⟨y, hy⟩ := hobs p C hp
  obtain ⟨a, ha⟩ := hr y
  rw [hsR] at ha
  have hle : B ≤ ((L : ℝ) + 1) / L * C := ha.trans (hy a)
  have hlt : ((L : ℝ) + 1) / L * C < B := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hLR]
    linarith [(div_lt_iff₀ (sub_pos.mpr hbad)).mp hj']
  exact hlt.not_ge hle

end
end Omega.RollingCliques.SpanOne
