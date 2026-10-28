/- GID: D5/S3/Topology/CompactMidpointInterval
   generality: G
   mirror-B: D5/B/S3/Topology/CompactMidpointInterval
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Compactness.Compact, mathlib/module/Mathlib.Topology.MetricSpace.Isometry]
   utility: none
   digest: Compact extended metric spaces with exact finite-distance midpoints admit endpoint-preserving isometric real intervals. -/

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Isometry


set_option autoImplicit false
open scoped ENNReal NNReal

namespace D5.S3.Topology.CompactMidpointInterval

universe u
variable {Y : Type u} [EMetricSpace Y]

private theorem refine_finite_chain
    (hmid : ∀ a b : Y, edist a b < ⊤ →
      ∃ z : Y, edist a z = edist a b / 2 ∧ edist z b = edist a b / 2)
    (p : ℕ → Y) (M : ℕ) (d : ℝ)
    (hp : ∀ k < M, edist (p k) (p (k + 1)) ≤ ENNReal.ofReal d) :
    ∃ q : ℕ → Y, q 0 = p 0 ∧ q (2 * M) = p M ∧
      ∀ k < 2 * M, edist (q k) (q (k + 1)) ≤ ENNReal.ofReal (d / 2) := by
  classical
  choose mid hmidL hmidR using fun k : Fin M =>
    hmid (p k.val) (p (k.val + 1))
      ((hp k.val k.isLt).trans_lt ENNReal.ofReal_lt_top)
  let middle (k : ℕ) : Y := if hk : k < M then mid ⟨k, hk⟩ else p 0
  have hdiv : ENNReal.ofReal (d / 2) = ENNReal.ofReal d / 2 := by
    simpa using (ENNReal.ofReal_div_of_pos (x := d) (y := 2) (by norm_num))
  have hleft (k : ℕ) (hk : k < M) :
      edist (p k) (middle k) ≤ ENNReal.ofReal (d / 2) := by
    dsimp only [middle]
    rw [dif_pos hk, hmidL ⟨k, hk⟩, hdiv]
    exact ENNReal.div_le_div_right (hp k hk) 2
  have hright (k : ℕ) (hk : k < M) :
      edist (middle k) (p (k + 1)) ≤ ENNReal.ofReal (d / 2) := by
    dsimp only [middle]
    rw [dif_pos hk, hmidR ⟨k, hk⟩, hdiv]
    exact ENNReal.div_le_div_right (hp k hk) 2
  let q (k : ℕ) : Y := if k % 2 = 0 then p (k / 2) else middle (k / 2)
  have heven (k : ℕ) : q (2 * k) = p k := by
    have hmod : (2 * k) % 2 = 0 := by omega
    have hquot : (2 * k) / 2 = k := by omega
    simp [q, hmod, hquot]
  have hodd (k : ℕ) : q (2 * k + 1) = middle k := by
    have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
    have hquot : (2 * k + 1) / 2 = k := by omega
    simp only [q, if_neg hmod, hquot]
  refine ⟨q, by simpa only [Nat.mul_zero] using heven 0, heven M, ?_⟩
  intro k hk
  let j := k / 2
  have hj : j < M := by dsimp only [j]; omega
  have hcases : k = 2 * j ∨ k = 2 * j + 1 := by dsimp only [j]; omega
  rcases hcases with h | h
  · rw [h, heven, hodd]
    exact hleft j hj
  · rw [h, hodd]
    have hnext : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
    rw [hnext, heven]
    exact hright j hj

private theorem exists_dyadic_chain
    (hmid : ∀ a b : Y, edist a b < ⊤ →
      ∃ z : Y, edist a z = edist a b / 2 ∧ edist z b = edist a b / 2)
    (a b : Y) (L : ℝ) (hL : edist a b = ENNReal.ofReal L) (n : ℕ) :
    ∃ p : ℕ → Y, p 0 = a ∧ p (2 ^ n) = b ∧
      ∀ k < 2 ^ n,
        edist (p k) (p (k + 1)) ≤ ENNReal.ofReal (L * (1 / 2 : ℝ) ^ n) := by
  induction n with
  | zero =>
      let p (k : ℕ) : Y := if k = 0 then a else b
      refine ⟨p, by simp [p], by simp [p], ?_⟩
      intro k hk
      have hk0 : k = 0 := by simpa only [pow_zero] using Nat.lt_one_iff.mp hk
      subst k
      simpa [p] using hL.le
  | succ n ih =>
      obtain ⟨p, hp0, hpN, hpedge⟩ := ih
      obtain ⟨q, hq0, hqN, hqedge⟩ :=
        refine_finite_chain hmid p (2 ^ n) (L * (1 / 2 : ℝ) ^ n) hpedge
      refine ⟨q, hq0.trans hp0, ?_, ?_⟩
      · simpa only [pow_succ, Nat.mul_comm] using hqN.trans hpN
      · intro k hk
        have hk' : k < 2 * 2 ^ n := by
          simpa only [pow_succ, Nat.mul_comm] using hk
        have hstep : L * (1 / 2 : ℝ) ^ n / 2 = L * (1 / 2 : ℝ) ^ (n + 1) := by
          rw [pow_succ]
          ring
        simpa only [hstep] using hqedge k hk'

end D5.S3.Topology.CompactMidpointInterval


set_option autoImplicit false
open Set
open scoped ENNReal NNReal

namespace D5.S3.Topology.CompactMidpointInterval

universe u
variable {Y : Type u} [EMetricSpace Y]

private theorem finite_chain_distance_bound
    (p : ℕ → Y) (M : ℕ) (d : ℝ)
    (hp : ∀ k < M, edist (p k) (p (k + 1)) ≤ ENNReal.ofReal d)
    (i j : ℕ) (hi : i ≤ M) (hj : j ≤ M) :
    edist (p i) (p j) ≤ ENNReal.ofReal (|(i : ℝ) - (j : ℝ)| * d) := by
  have forward (i j : ℕ) (hij : i ≤ j) (hj : j ≤ M) :
      edist (p i) (p j) ≤ ENNReal.ofReal (|(i : ℝ) - (j : ℝ)| * d) := by
    calc
      edist (p i) (p j) ≤ ∑ k ∈ Finset.Ico i j, ENNReal.ofReal d :=
        edist_le_Ico_sum_of_edist_le hij (fun _ hkj => hp _ (hkj.trans_le hj))
      _ = ENNReal.ofReal (((j - i : ℕ) : ℝ) * d) := by
        rw [Finset.sum_const, Nat.card_Ico, ← ENNReal.ofReal_nsmul, nsmul_eq_mul]
      _ = ENNReal.ofReal (|(i : ℝ) - (j : ℝ)| * d) := by
        rw [Nat.cast_sub hij, abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr hij))]
        congr 1
        ring
  rcases le_total i j with hij | hji
  · exact forward i j hij hj
  · rw [edist_comm, abs_sub_comm]
    exact forward j i hji hi

private theorem approximate_interval_map_of_finite_chain
    (a b : Y) (L d : ℝ) (hL : 0 ≤ L) (hd : 0 < d)
    (M : ℕ) (hscale : L = (M : ℝ) * d)
    (p : ℕ → Y) (hp0 : p 0 = a) (hpM : p M = b)
    (hp : ∀ k < M, edist (p k) (p (k + 1)) ≤ ENNReal.ofReal d) :
    ∃ f : Set.Icc (0 : ℝ) L → Y,
      f ⟨0, ⟨le_rfl, hL⟩⟩ = a ∧ f ⟨L, ⟨hL, le_rfl⟩⟩ = b ∧
      ∀ s t : Set.Icc (0 : ℝ) L,
        edist (f s) (f t) ≤ ENNReal.ofReal (|s.val - t.val| + 2 * d) := by
  let index (t : Set.Icc (0 : ℝ) L) : ℕ := ⌊t.val / d⌋₊
  let rounded (t : Set.Icc (0 : ℝ) L) : ℝ := (index t : ℝ) * d
  have hindex (t : Set.Icc (0 : ℝ) L) : index t ≤ M := by
    apply Nat.floor_le_of_le
    apply (div_le_iff₀ hd).mpr
    simpa only [← hscale] using t.property.2
  have hround_le (t : Set.Icc (0 : ℝ) L) : rounded t ≤ t.val := by
    exact (le_div_iff₀ hd).mp (Nat.floor_le (div_nonneg t.property.1 hd.le))
  have hround_lt (t : Set.Icc (0 : ℝ) L) : t.val < rounded t + d := by
    have h := (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one (t.val / d))
    dsimp only [rounded, index]
    nlinarith
  have herr (t : Set.Icc (0 : ℝ) L) : |rounded t - t.val| ≤ d := by
    rw [abs_of_nonpos (sub_nonpos.mpr (hround_le t))]
    linarith [hround_lt t]
  let f (t : Set.Icc (0 : ℝ) L) : Y := p (index t)
  refine ⟨f, ?_, ?_, ?_⟩
  · simpa only [f, index, zero_div, Nat.floor_zero] using hp0
  · have hr : L / d = (M : ℝ) := by
      rw [hscale]
      exact mul_div_cancel_right₀ _ hd.ne'
    simpa only [f, index, hr, Nat.floor_natCast] using hpM
  · intro s t
    have hgrid := finite_chain_distance_bound p M d hp
      (index s) (index t) (hindex s) (hindex t)
    have hidentity : |(index s : ℝ) - (index t : ℝ)| * d = |rounded s - rounded t| := by
      dsimp only [rounded]
      rw [← sub_mul, abs_mul, abs_of_nonneg hd.le]
    have herror : |rounded s - rounded t| ≤ |s.val - t.val| + 2 * d := by
      calc
        |rounded s - rounded t| =
            |(rounded s - s.val) + (s.val - t.val) + (t.val - rounded t)| := by
          congr 1
          ring
        _ ≤ |rounded s - s.val| + |s.val - t.val| + |t.val - rounded t| :=
          (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
        _ ≤ d + |s.val - t.val| + d := by
          exact add_le_add (add_le_add_right (herr s) _) (by simpa only [abs_sub_comm] using herr t)
        _ = |s.val - t.val| + 2 * d := by ring
    exact hgrid.trans (ENNReal.ofReal_le_ofReal (hidentity.le.trans herror))

end D5.S3.Topology.CompactMidpointInterval


set_option autoImplicit false
open Set Filter
open scoped ENNReal NNReal Topology

namespace D5.S3.Topology.CompactMidpointInterval

universe u v
variable {A : Type u} {Y : Type v} [EMetricSpace Y] [CompactSpace Y]

private theorem exact_map_of_uniform_approximations
    (a₀ a₁ : A) (a b : Y) (d : A → A → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (happrox : ∀ n : ℕ, ∃ f : A → Y,
      f a₀ = a ∧ f a₁ = b ∧
      ∀ s t : A, edist (f s) (f t) ≤ ENNReal.ofReal (d s t + C * (1 / 2 : ℝ) ^ n)) :
    ∃ f : A → Y, f a₀ = a ∧ f a₁ = b ∧
      ∀ s t : A, edist (f s) (f t) ≤ ENNReal.ofReal (d s t) := by
  let K (n : ℕ) : Set (A → Y) :=
    {f | f a₀ = a ∧ f a₁ = b ∧
      ∀ s t : A, edist (f s) (f t) ≤ ENNReal.ofReal (d s t + C * (1 / 2 : ℝ) ^ n)}
  have hclosed (n : ℕ) : IsClosed (K n) := by
    have hk : K n =
        {f : A → Y | f a₀ = a} ∩
        ({f : A → Y | f a₁ = b} ∩
          ⋂ s : A, ⋂ t : A,
            {f : A → Y | edist (f s) (f t) ≤ ENNReal.ofReal (d s t + C * (1 / 2 : ℝ) ^ n)}) := by
      ext f
      simp only [K, mem_setOf_eq, mem_inter_iff, mem_iInter]
    rw [hk]
    exact (isClosed_eq (continuous_apply a₀) continuous_const).inter
      ((isClosed_eq (continuous_apply a₁) continuous_const).inter
        (isClosed_iInter fun s => isClosed_iInter fun t =>
          isClosed_le ((continuous_apply s).edist (continuous_apply t)) continuous_const))
  have hnonempty (n : ℕ) : (K n).Nonempty := happrox n
  have hdecreasing (n : ℕ) : K (n + 1) ⊆ K n := by
    intro f hf
    refine ⟨hf.1, hf.2.1, ?_⟩
    intro s t
    have hpower : (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ n := by
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
    exact (hf.2.2 s t).trans
      (ENNReal.ofReal_le_ofReal (add_le_add_left (mul_le_mul_of_nonneg_left hpower hC) (d s t)))
  obtain ⟨f, hf⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      K hdecreasing hnonempty (hclosed 0).isCompact hclosed
  have hmem (n : ℕ) : f ∈ K n := mem_iInter.mp hf n
  refine ⟨f, (hmem 0).1, (hmem 0).2.1, ?_⟩
  intro s t
  have herr : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hbound : Tendsto
      (fun n : ℕ => ENNReal.ofReal (d s t + C * (1 / 2 : ℝ) ^ n))
      atTop (𝓝 (ENNReal.ofReal (d s t))) := by
    simpa only [mul_zero, add_zero] using
      (ENNReal.continuous_ofReal.tendsto (d s t + C * 0)).comp
        (tendsto_const_nhds.add (tendsto_const_nhds.mul herr))
  exact ge_of_tendsto' hbound (fun n => (hmem n).2.2 s t)

end D5.S3.Topology.CompactMidpointInterval


set_option autoImplicit false
open scoped ENNReal NNReal

namespace D5.S3.Topology.CompactMidpointInterval

universe u
variable {Y : Type u} [EMetricSpace Y]

private theorem isometry_of_endpoint_saturation
    (L : ℝ) (hL : 0 ≤ L) (f : Set.Icc (0 : ℝ) L → Y)
    (hend : edist (f ⟨0, ⟨le_rfl, hL⟩⟩) (f ⟨L, ⟨hL, le_rfl⟩⟩) = ENNReal.ofReal L)
    (hbound : ∀ s t : Set.Icc (0 : ℝ) L,
      edist (f s) (f t) ≤ ENNReal.ofReal |s.val - t.val|) : Isometry f := by
  let first : Set.Icc (0 : ℝ) L := ⟨0, ⟨le_rfl, hL⟩⟩
  let last : Set.Icc (0 : ℝ) L := ⟨L, ⟨hL, le_rfl⟩⟩
  have lower (s t : Set.Icc (0 : ℝ) L) (hst : s.val ≤ t.val) :
      ENNReal.ofReal (t.val - s.val) ≤ edist (f s) (f t) := by
    have hleft : edist (f first) (f s) ≤ ENNReal.ofReal s.val := by
      simpa [first, abs_of_nonneg s.property.1] using hbound first s
    have hright : edist (f t) (f last) ≤ ENNReal.ofReal (L - t.val) := by
      simpa only [last, abs_of_nonpos (sub_nonpos.mpr t.property.2), neg_sub] using hbound t last
    have hfinite : edist (f s) (f t) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound s t)
    have hsum : ENNReal.ofReal s.val + edist (f s) (f t) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hfinite⟩
    have htri : ENNReal.ofReal L ≤
        (ENNReal.ofReal s.val + edist (f s) (f t)) + ENNReal.ofReal (L - t.val) := by
      calc
        ENNReal.ofReal L = edist (f first) (f last) := hend.symm
        _ ≤ edist (f first) (f t) + edist (f t) (f last) := edist_triangle _ _ _
        _ ≤ (edist (f first) (f s) + edist (f s) (f t)) + edist (f t) (f last) :=
          add_le_add_right (edist_triangle _ _ _) _
        _ ≤ (ENNReal.ofReal s.val + edist (f s) (f t)) + ENNReal.ofReal (L - t.val) :=
          add_le_add (add_le_add_right hleft _) hright
    have hr := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hsum, ENNReal.ofReal_ne_top⟩) htri
    rw [ENNReal.toReal_add hsum ENNReal.ofReal_ne_top,
      ENNReal.toReal_add ENNReal.ofReal_ne_top hfinite,
      ENNReal.toReal_ofReal s.property.1,
      ENNReal.toReal_ofReal (sub_nonneg.mpr t.property.2),
      ENNReal.toReal_ofReal hL] at hr
    apply ENNReal.ofReal_le_of_le_toReal
    linarith
  intro s t
  change edist (f s) (f t) = edist s.val t.val
  rw [edist_dist, Real.dist_eq]
  apply le_antisymm (hbound s t)
  rcases le_total s.val t.val with hst | hts
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using lower s t hst
  · have h := lower t s hts
    rw [edist_comm] at h
    simpa only [abs_of_nonneg (sub_nonneg.mpr hts)] using h

end D5.S3.Topology.CompactMidpointInterval


set_option autoImplicit false
open scoped ENNReal NNReal

namespace D5.S3.Topology.CompactMidpointInterval

universe u
variable {Y : Type u} [EMetricSpace Y] [CompactSpace Y]

private theorem compact_midpoint_interval_aux
    (hmid : ∀ a b : Y, edist a b < ⊤ →
      ∃ z : Y, edist a z = edist a b / 2 ∧ edist z b = edist a b / 2)
    (a b : Y) (L : ℝ) (hL : 0 ≤ L) (hD : edist a b = ENNReal.ofReal L) :
    ∃ f : Set.Icc (0 : ℝ) L → Y, Isometry f ∧
      f ⟨0, ⟨le_rfl, hL⟩⟩ = a ∧ f ⟨L, ⟨hL, le_rfl⟩⟩ = b := by
  by_cases hzero : L = 0
  · have hab : a = b := edist_eq_zero.mp (by simpa only [hzero, ENNReal.ofReal_zero] using hD)
    subst b
    refine ⟨fun _ => a, ?_, rfl, rfl⟩
    intro s t
    have hst : s = t := by
      apply Subtype.ext
      have hs := s.property
      have ht := t.property
      rw [hzero] at hs ht
      linarith
    rw [hst]
    simp
  · have hLpos : 0 < L := lt_of_le_of_ne hL hzero.symm
    let first : Set.Icc (0 : ℝ) L := ⟨0, ⟨le_rfl, hL⟩⟩
    let last : Set.Icc (0 : ℝ) L := ⟨L, ⟨hL, le_rfl⟩⟩
    have happrox : ∀ n : ℕ, ∃ f : Set.Icc (0 : ℝ) L → Y,
        f first = a ∧ f last = b ∧
        ∀ s t : Set.Icc (0 : ℝ) L,
          edist (f s) (f t) ≤ ENNReal.ofReal (|s.val - t.val| + (2 * L) * (1 / 2 : ℝ) ^ n) := by
      intro n
      obtain ⟨p, hp0, hpN, hpedge⟩ := exists_dyadic_chain hmid a b L hD n
      have hd : 0 < L * (1 / 2 : ℝ) ^ n := mul_pos hLpos (pow_pos (by norm_num) n)
      have htwo : ((2 ^ n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n = 1 := by
        simp only [Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
        norm_num
      have hscale : L = ((2 ^ n : ℕ) : ℝ) * (L * (1 / 2 : ℝ) ^ n) := by
        calc
          L = L * 1 := by ring
          _ = L * (((2 ^ n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) := by rw [htwo]
          _ = ((2 ^ n : ℕ) : ℝ) * (L * (1 / 2 : ℝ) ^ n) := by ring
      obtain ⟨f, hf0, hfN, hfbound⟩ :=
        approximate_interval_map_of_finite_chain a b L (L * (1 / 2 : ℝ) ^ n)
          hL hd (2 ^ n) hscale p hp0 hpN hpedge
      refine ⟨f, hf0, hfN, ?_⟩
      intro s t
      have herr : 2 * (L * (1 / 2 : ℝ) ^ n) = (2 * L) * (1 / 2 : ℝ) ^ n := by ring
      simpa only [herr] using hfbound s t
    obtain ⟨f, hf0, hfN, hfbound⟩ := exact_map_of_uniform_approximations
      first last a b (fun s t : Set.Icc (0 : ℝ) L => |s.val - t.val|)
      (2 * L) (mul_nonneg (by norm_num) hL) happrox
    refine ⟨f, isometry_of_endpoint_saturation L hL f ?_ hfbound, hf0, hfN⟩
    simpa only [hf0, hfN] using hD

theorem compact_midpoints_isometric_interval
    (hmid : ∀ a b : Y, edist a b < ⊤ →
      ∃ z : Y, edist a z = edist a b / 2 ∧ edist z b = edist a b / 2)
    (a b : Y) (hfinite : edist a b < ⊤) :
    ∃ f : Set.Icc (0 : ℝ) (edist a b).toReal → Y, Isometry f ∧
      f ⟨0, ⟨le_rfl, ENNReal.toReal_nonneg⟩⟩ = a ∧
      f ⟨(edist a b).toReal, ⟨ENNReal.toReal_nonneg, le_rfl⟩⟩ = b := by
  exact compact_midpoint_interval_aux hmid a b (edist a b).toReal
    ENNReal.toReal_nonneg (ENNReal.ofReal_toReal hfinite.ne).symm

end D5.S3.Topology.CompactMidpointInterval
