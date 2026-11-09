/- GID: D5/S1/Dynamics/Shadowing/NorthSouthOrbitClock
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/NorthSouthOrbitClock
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Algebra.Monoid]
   utility: none
   digest: Locally finite integer orbit weights for pointwise north-south dynamics. -/

import D5.S1.Dynamics.Shadowing.PointwiseNorthSouth
import D5.S1.Dynamics.Shadowing.CompactPseudoOrbitSelector
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Compact

/-! The orbit clock is a finite weighted barycenter at each punctured point. -/

noncomputable section
open Set Function Filter Topology

namespace D5.S1.Dynamics.Shadowing.PointwiseNorthSouth

variable {M : Type*} [MetricSpace M] {f : M ≃ₜ M} {N S : M}

theorem zpow_fixed (hp : f N = N) (i : ℤ) : (f ^ i) N = N := by
  induction i using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [show (n : ℤ) + 1 = 1 + n by omega, zpow_add, zpow_one, Homeomorph.mul_apply, ih, hp]
  | pred n ih =>
    apply f.injective
    have he : f ((f ^ (-(n : ℤ) - 1)) N) = (f ^ (-(n : ℤ))) N := by
      have hh : f * f ^ (-(n : ℤ) - 1) = f ^ (-(n : ℤ)) := by
        calc
          f * f ^ (-(n : ℤ) - 1) = f ^ (1 : ℤ) * f ^ (-(n : ℤ) - 1) := by
            rw [zpow_one]
          _ = f ^ ((1 : ℤ) + (-(n : ℤ) - 1)) := (zpow_add _ _ _).symm
          _ = f ^ (-(n : ℤ)) := by congr 1; omega
      exact congrArg (fun g : M ≃ₜ M => g N) hh
    rw [he, ih, hp]

private theorem nonpole_zpow (h : Pointwise f N S) {p : M} (hp : p ≠ N ∧ p ≠ S)
    (i : ℤ) : (f ^ i) p ≠ N ∧ (f ^ i) p ≠ S := by
  constructor
  · intro hh
    exact hp.1 ((f ^ i).injective (hh.trans (zpow_fixed h.north_fixed i).symm))
  · intro hh
    exact hp.2 ((f ^ i).injective (hh.trans (zpow_fixed h.south_fixed i).symm))

private theorem orbit_add (i j : ℤ) (p : M) :
    (f ^ (i + j)) p = (f ^ i) ((f ^ j) p) := by rw [zpow_add, Homeomorph.mul_apply]

/-- A compactly supported bump with a positive value on each punctured orbit. -/
structure OrbitBump (f : M ≃ₜ M) (N S : M) where
  value : M → ℝ
  continuous_value : Continuous value
  nonneg : ∀ p, 0 ≤ value p
  radius : ℝ
  radius_pos : 0 < radius
  vanish_north : ∀ p, dist p N < radius → value p = 0
  vanish_south : ∀ p, dist p S < radius → value p = 0
  hits : ∀ p, p ≠ N → p ≠ S → ∃ i : ℤ, 0 < value ((f ^ i) p)

private theorem exists_bump [CompactSpace M] (h : Pointwise f N S) :
    Nonempty (OrbitBump f N S) := by
  classical
  let u : M → ℝ := fun p => dist p N - dist p S
  have hu : Continuous u := (continuous_id.dist continuous_const).sub
    (continuous_id.dist continuous_const)
  have huN : u N < 0 := by
    dsimp [u]
    simp only [dist_self, zero_sub]
    exact neg_neg_of_pos (dist_pos.mpr h.distinct)
  have huS : 0 < u S := by dsimp [u]; simpa using dist_pos.mpr h.distinct.symm
  let C : Set M := {p | u p ≤ 0 ∧ 0 ≤ u (f p)}
  have hC : IsCompact C :=
    ((isClosed_le hu continuous_const).inter (isClosed_le continuous_const (hu.comp f.continuous))).isCompact
  have hCN : N ∉ C := by
    intro hh
    have hh' : 0 ≤ u N := by simpa only [h.north_fixed] using hh.2
    linarith
  have hCS : S ∉ C := fun hh => (not_le_of_gt huS) hh.1
  have hitC (p : M) (hpN : p ≠ N) (hpS : p ≠ S) : ∃ i : ℤ, (f ^ i) p ∈ C := by
    obtain ⟨m, hm⟩ := ((hu.continuousAt.tendsto.comp (h.backward p hpN hpS)).eventually
      (Iio_mem_nhds huN)).exists
    let q := (f.symm ^ m) p
    change u q < 0 at hm
    have hq : q ≠ N ∧ q ≠ S := by
      have hh := nonpole_zpow h ⟨hpN, hpS⟩ (-(m : ℤ))
      have heq : f ^ (-(m : ℤ)) = f.symm ^ m := by
        rw [zpow_neg, zpow_natCast]
        exact (inv_pow f m).symm
      rw [heq] at hh
      exact hh
    have he : ∃ n : ℕ, 0 ≤ u ((f ^ n) q) := by
      obtain ⟨n, hn⟩ := ((hu.continuousAt.tendsto.comp (h.forward q hq.1 hq.2)).eventually
        (Ioi_mem_nhds huS)).exists
      exact ⟨n, hn.le⟩
    let n := Nat.find he
    have hn : 0 ≤ u ((f ^ n) q) := Nat.find_spec he
    have hnpos : 0 < n := by
      by_contra hh
      have hn0 : n = 0 := by omega
      have hneg : ¬ 0 ≤ u ((f ^ n) q) := by
        simpa only [hn0, pow_zero, Homeomorph.one_apply] using not_le_of_gt hm
      exact hneg hn
    have hbefore : u ((f ^ (n - 1)) q) < 0 :=
      lt_of_not_ge (Nat.find_min he (show n - 1 < n by omega))
    refine ⟨((n - 1 : ℕ) : ℤ) - m, ?_⟩
    have heq : (f ^ (((n - 1 : ℕ) : ℤ) - m)) p = (f ^ (n - 1)) q := by
      rw [sub_eq_add_neg, orbit_add, zpow_natCast, zpow_neg, zpow_natCast, ← inv_pow]
      rfl
    rw [heq]
    refine ⟨hbefore.le, ?_⟩
    have hfq : f ((f ^ (n - 1)) q) = (f ^ n) q := by
      rw [← Homeomorph.mul_apply, ← pow_succ', Nat.sub_add_cancel hnpos]
    rwa [hfq]
  let g : M → ℝ := fun p => min (dist p N) (dist p S)
  have hg : Continuous g := (continuous_id.dist continuous_const).min
    (continuous_id.dist continuous_const)
  obtain ⟨a, ha, hamin⟩ := hC.exists_forall_le' hg.continuousOn (a := (0 : ℝ)) (by
    intro p hp
    exact lt_min (dist_pos.mpr (fun hh => hCN (hh ▸ hp)))
      (dist_pos.mpr (fun hh => hCS (hh ▸ hp))))
  let b : M → ℝ := fun p => max 0 (2 * g p / a - 1)
  have hb0 (p : M) (hp : g p < a / 2) : b p = 0 := by
    dsimp [b]
    apply max_eq_left
    have hh : 2 * g p / a < 1 := (div_lt_one ha).mpr (by linarith)
    linarith
  refine ⟨{
    value := b
    continuous_value := continuous_const.max ((continuous_const.mul hg).div_const a |>.sub continuous_const)
    nonneg := fun _ => le_max_left _ _
    radius := a / 2
    radius_pos := half_pos ha
    vanish_north := fun p hp => hb0 p ((min_le_left _ _).trans_lt hp)
    vanish_south := fun p hp => hb0 p ((min_le_right _ _).trans_lt hp)
    hits := ?_ }⟩
  intro p hpN hpS
  obtain ⟨i, hi⟩ := hitC p hpN hpS
  refine ⟨i, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ?_⟩
  have hga := hamin _ hi
  apply le_trans _ (le_max_right _ _)
  have hh : 2 ≤ 2 * g ((f ^ i) p) / a := (le_div_iff₀ ha).mpr (by linarith)
  linarith

variable [CompactSpace M]

private theorem bump_finite_on_compact (h : Pointwise f N S) (b : OrbitBump f N S)
    {C : Set M} (hC : IsCompact C) (hCN : N ∉ C) (hCS : S ∉ C) :
    ∃ R : ℕ, ∀ p ∈ C, ∀ i : ℤ, R < i.natAbs → b.value ((f ^ i) p) = 0 := by
  obtain ⟨T, hT⟩ := (stability_and_compact_uniformity h).2.2.1 C hC hCN
    (Metric.ball S b.radius) (Metric.ball_mem_nhds S b.radius_pos)
  obtain ⟨U, hU⟩ := (stability_and_compact_uniformity h).2.2.2 C hC hCS
    (Metric.ball N b.radius) (Metric.ball_mem_nhds N b.radius_pos)
  refine ⟨max T U, fun p hp i hi => ?_⟩
  rcases Int.eq_nat_or_neg i with ⟨n, rfl | rfl⟩
  · rw [Int.natAbs_natCast] at hi
    rw [zpow_natCast]
    exact b.vanish_south _ (hT n (by omega) ⟨p, hp, rfl⟩)
  · rw [Int.natAbs_neg, Int.natAbs_natCast] at hi
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact b.vanish_north _ (hU n (by omega) ⟨p, hp, rfl⟩)

/-- The punctured carrier is only an auxiliary domain for the scalar clock. -/
abbrev Punctured (N S : M) := {p : M // p ≠ N ∧ p ≠ S}

private theorem bump_locallyFinite (h : Pointwise f N S) (b : OrbitBump f N S) :
    LocallyFinite (fun i : ℤ => support (fun p : Punctured N S => b.value ((f ^ i) p.1))) := by
  intro p
  let r := min (dist p.1 N) (dist p.1 S) / 2
  have hr : 0 < r := by
    dsimp [r]
    exact half_pos (lt_min (dist_pos.mpr p.2.1) (dist_pos.mpr p.2.2))
  let C := Metric.closedBall p.1 r
  have hCN : N ∉ C := by
    intro hh
    have hb : dist p.1 N ≤ r := by simpa only [C, Metric.mem_closedBall, dist_comm] using hh
    have := min_le_left (dist p.1 N) (dist p.1 S)
    dsimp [r] at hb
    linarith [dist_pos.mpr p.2.1]
  have hCS : S ∉ C := by
    intro hh
    have hb : dist p.1 S ≤ r := by simpa only [C, Metric.mem_closedBall, dist_comm] using hh
    have := min_le_right (dist p.1 N) (dist p.1 S)
    dsimp [r] at hb
    linarith [dist_pos.mpr p.2.2]
  obtain ⟨R, hR⟩ := bump_finite_on_compact h b Metric.isClosed_closedBall.isCompact hCN hCS
  refine ⟨Subtype.val ⁻¹' C,
    continuous_subtype_val.continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds p.1 hr), ?_⟩
  apply (Set.finite_Icc (-(R : ℤ)) (R : ℤ)).subset
  rintro i ⟨q, hqi, hqC⟩
  have habs : i.natAbs ≤ R := by
    by_contra hn
    exact hqi (hR q.1 hqC i (lt_of_not_ge hn))
  have hleft := Int.le_natAbs (a := -i)
  have hright := Int.le_natAbs (a := i)
  simp only [Int.natAbs_neg] at hleft
  constructor <;> omega

private def weight (b : OrbitBump f N S) (p : Punctured N S) (i : ℤ) : ℝ :=
  b.value ((f ^ i) p.1)

private def mass (b : OrbitBump f N S) (p : Punctured N S) : ℝ := ∑ᶠ i, weight b p i
private def moment (b : OrbitBump f N S) (p : Punctured N S) : ℝ :=
  ∑ᶠ i : ℤ, (i : ℝ) * weight b p i
private def clock (b : OrbitBump f N S) (p : Punctured N S) : ℝ := -moment b p / mass b p

private theorem finite_weight (h : Pointwise f N S) (b : OrbitBump f N S) (p : Punctured N S) :
    HasFiniteSupport (weight b p) := (bump_locallyFinite h b).point_finite p

private theorem mass_pos (h : Pointwise f N S) (b : OrbitBump f N S) (p : Punctured N S) :
    0 < mass b p :=
  finsum_pos (fun i => b.nonneg _) (b.hits p.1 p.2.1 p.2.2) (finite_weight h b p)

private theorem continuous_clock (h : Pointwise f N S) (b : OrbitBump f N S) :
    Continuous (clock b) := by
  have hw (i : ℤ) : Continuous (fun p : Punctured N S => weight b p i) :=
    b.continuous_value.comp ((f ^ i).continuous.comp continuous_subtype_val)
  have hB : Continuous (mass b) := continuous_finsum hw (bump_locallyFinite h b)
  have hA : Continuous (moment b) := continuous_finsum
    (fun i => continuous_const.mul (hw i)) ((bump_locallyFinite h b).subset
      (fun i p hp => (mul_ne_zero_iff.mp hp).2))
  exact hA.neg.div hB (fun p => ne_of_gt (mass_pos h b p))

private def next (h : Pointwise f N S) (p : Punctured N S) : Punctured N S :=
  ⟨f p.1, by simpa only [zpow_one] using nonpole_zpow h p.2 1⟩

private theorem weight_next (h : Pointwise f N S) (b : OrbitBump f N S)
    (p : Punctured N S) (i : ℤ) : weight b (next h p) i = weight b p (1 + i) := by
  dsimp [weight, next]
  rw [add_comm (1 : ℤ) i, orbit_add, zpow_one]

private theorem finite_moment (h : Pointwise f N S) (b : OrbitBump f N S) (p : Punctured N S) :
    HasFiniteSupport (fun i : ℤ => (i : ℝ) * weight b p i) :=
  (finite_weight h b p).subset (fun _ hi => (mul_ne_zero_iff.mp hi).2)

private theorem mass_next (h : Pointwise f N S) (b : OrbitBump f N S) (p : Punctured N S) :
    mass b (next h p) = mass b p := by
  unfold mass
  simp_rw [weight_next]
  exact finsum_comp (Equiv.addLeft (1 : ℤ)) (Equiv.addLeft (1 : ℤ)).bijective

private theorem moment_next (h : Pointwise f N S) (b : OrbitBump f N S) (p : Punctured N S) :
    moment b (next h p) = moment b p - mass b p := by
  calc
    moment b (next h p) = ∑ᶠ i : ℤ, (((1 + i : ℤ) : ℝ) - 1) * weight b p (1 + i) := by
      apply finsum_congr
      intro i
      rw [weight_next]
      push_cast
      ring
    _ = ∑ᶠ i : ℤ, ((i : ℝ) - 1) * weight b p i :=
      finsum_comp (g := fun i : ℤ => ((i : ℝ) - 1) * weight b p i)
        (Equiv.addLeft (1 : ℤ)) (Equiv.addLeft (1 : ℤ)).bijective
    _ = moment b p - mass b p := by
      simp_rw [sub_mul, one_mul]
      exact finsum_sub_distrib (finite_moment h b p) (finite_weight h b p)

private theorem clock_next (h : Pointwise f N S) (b : OrbitBump f N S) (p : Punctured N S) :
    clock b (next h p) = clock b p + 1 := by
  unfold clock
  rw [mass_next, moment_next]
  field_simp [ne_of_gt (mass_pos h b p)]
  ring

private theorem clock_ge (h : Pointwise f N S) (b : OrbitBump f N S) (p : Punctured N S)
    (R : ℝ) (hzero : ∀ i : ℤ, -R ≤ (i : ℝ) → weight b p i = 0) : R ≤ clock b p := by
  have hpoint (i : ℤ) : (i : ℝ) * weight b p i ≤ -R * weight b p i := by
    by_cases hi : -R ≤ (i : ℝ)
    · rw [hzero i hi]; simp
    · exact mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hi)) (b.nonneg _)
  have hfin : HasFiniteSupport (fun i : ℤ => -R * weight b p i) :=
    (finite_weight h b p).subset (fun i hi => (mul_ne_zero_iff.mp hi).2)
  have hsum := finsum_le_finsum (finite_moment h b p) hfin hpoint
  have he : (∑ᶠ i : ℤ, -R * weight b p i) = -R * mass b p :=
    (mul_finsum (weight b p) (-R)).symm
  rw [he] at hsum
  change moment b p ≤ -R * mass b p at hsum
  apply (le_div_iff₀ (mass_pos h b p)).mpr
  change R * mass b p ≤ -moment b p
  linarith

private theorem clock_le (h : Pointwise f N S) (b : OrbitBump f N S) (p : Punctured N S)
    (R : ℝ) (hzero : ∀ i : ℤ, (i : ℝ) ≤ R → weight b p i = 0) : clock b p ≤ -R := by
  have hpoint (i : ℤ) : R * weight b p i ≤ (i : ℝ) * weight b p i := by
    by_cases hi : (i : ℝ) ≤ R
    · rw [hzero i hi]; simp
    · exact mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hi)) (b.nonneg _)
  have hfin : HasFiniteSupport (fun i : ℤ => R * weight b p i) :=
    (finite_weight h b p).subset (fun i hi => (mul_ne_zero_iff.mp hi).2)
  have hsum := finsum_le_finsum hfin (finite_moment h b p) hpoint
  have he : (∑ᶠ i : ℤ, R * weight b p i) = R * mass b p :=
    (mul_finsum (weight b p) R).symm
  rw [he] at hsum
  change R * mass b p ≤ moment b p at hsum
  apply (div_le_iff₀ (mass_pos h b p)).mpr
  change -moment b p ≤ -R * mass b p
  linarith

private theorem inverse_nat_power (n : ℕ) : f.symm ^ n = f ^ (-(n : ℤ)) := by
  rw [zpow_neg, zpow_natCast]
  exact inv_pow f n

private theorem clock_tendsto_south (h : Pointwise f N S) (b : OrbitBump f N S) :
    Tendsto (clock b) (comap (Subtype.val : Punctured N S → M) (𝓝 S)) atTop := by
  apply tendsto_atTop.mpr
  intro R
  obtain ⟨n, hn⟩ := exists_nat_ge R
  obtain ⟨V, hV, hVO⟩ := (stability_and_compact_uniformity h).1
    (Metric.ball S b.radius) (Metric.ball_mem_nhds S b.radius_pos)
  have hfix : (f.symm ^ n) S = S := by
    rw [inverse_nat_power, zpow_fixed h.south_fixed]
  have hU : (f.symm ^ n) ⁻¹' V ∈ 𝓝 S :=
    (f.symm ^ n).continuous.continuousAt.preimage_mem_nhds (by rwa [hfix])
  filter_upwards [preimage_mem_comap hU] with p hp
  apply hn.trans
  apply clock_ge h b p (n : ℝ)
  intro i hi
  have hiz : -(n : ℤ) ≤ i := by exact_mod_cast hi
  let m := (i + (n : ℤ)).toNat
  have hm : (m : ℤ) = i + n := Int.toNat_of_nonneg (by omega)
  have he : (f ^ i) p.1 = (f ^ m) ((f.symm ^ n) p.1) := by
    rw [inverse_nat_power, ← zpow_natCast, ← orbit_add, hm]
    congr 2
    omega
  dsimp [weight]
  rw [he]
  exact b.vanish_south _ (hVO m ⟨(f.symm ^ n) p.1, hp, rfl⟩)

private theorem clock_tendsto_north (h : Pointwise f N S) (b : OrbitBump f N S) :
    Tendsto (clock b) (comap (Subtype.val : Punctured N S → M) (𝓝 N)) atBot := by
  apply tendsto_atBot.mpr
  intro R
  obtain ⟨n, hn⟩ := exists_nat_ge (-R)
  obtain ⟨V, hV, hVO⟩ := (stability_and_compact_uniformity h).2.1
    (Metric.ball N b.radius) (Metric.ball_mem_nhds N b.radius_pos)
  have hfix : (f ^ n) N = N := by
    rw [← zpow_natCast, zpow_fixed h.north_fixed]
  have hU : (f ^ n) ⁻¹' V ∈ 𝓝 N :=
    (f ^ n).continuous.continuousAt.preimage_mem_nhds (by rwa [hfix])
  filter_upwards [preimage_mem_comap hU] with p hp
  apply le_trans (clock_le h b p (n : ℝ) ?_) (by linarith)
  intro i hi
  have hiz : i ≤ (n : ℤ) := by exact_mod_cast hi
  let m := ((n : ℤ) - i).toNat
  have hm : (m : ℤ) = (n : ℤ) - i := Int.toNat_of_nonneg (by omega)
  have he : (f ^ i) p.1 = (f.symm ^ m) ((f ^ n) p.1) := by
    rw [inverse_nat_power, ← zpow_natCast, ← orbit_add, hm]
    congr 2
    omega
  dsimp [weight]
  rw [he]
  exact b.vanish_north _ (hVO m ⟨(f ^ n) p.1, hp, rfl⟩)

private def compress (r : ℝ) : ℝ := r / (1 + |r|)

private theorem continuous_compress : Continuous compress :=
  continuous_id.div (continuous_const.add continuous_abs) (fun r => by positivity)

private theorem compress_range (r : ℝ) : compress r ∈ Ioo (-1 : ℝ) 1 := by
  have hd : 0 < 1 + |r| := by positivity
  constructor
  · apply (lt_div_iff₀ hd).mpr
    have := neg_abs_le r
    linarith
  · apply (div_lt_iff₀ hd).mpr
    have := le_abs_self r
    linarith

private theorem strictMono_compress : StrictMono compress := by
  intro x y hxy
  have hx : 0 < 1 + |x| := by positivity
  have hy : 0 < 1 + |y| := by positivity
  apply (div_lt_div_iff₀ hx hy).mpr
  rcases le_or_gt 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0, abs_of_nonneg (hx0.trans hxy.le)]
    nlinarith
  · rcases le_or_gt 0 y with hy0 | hy0
    · rw [abs_of_neg hx0, abs_of_nonneg hy0]
      nlinarith
    · rw [abs_of_neg hx0, abs_of_neg hy0]
      nlinarith

private theorem compress_neg (r : ℝ) : compress (-r) = -compress r := by
  simp only [compress, abs_neg, neg_div]

private theorem compress_tendsto_top : Tendsto compress atTop (𝓝 (1 : ℝ)) := by
  have hh : Tendsto (fun r : ℝ => 1 - (1 + r)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_inv_atTop_zero.comp ((tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  dsimp [compress]
  rw [abs_of_nonneg hr]
  field_simp
  ring

private theorem compress_tendsto_bot : Tendsto compress atBot (𝓝 (-1 : ℝ)) := by
  have hh := (compress_tendsto_top.comp tendsto_neg_atBot_atTop).neg
  simpa only [Function.comp_def, compress_neg, neg_neg] using hh

/-- A strict scalar height is derived from pointwise dynamics, never assumed as NS data. -/
structure StrictHeight (f : M ≃ₜ M) (N S : M) where
  value : M → ℝ
  continuous_value : Continuous value
  north : value N = -1
  south : value S = 1
  range : ∀ p, -1 ≤ value p ∧ value p ≤ 1
  eq_north : ∀ p, value p = -1 ↔ p = N
  eq_south : ∀ p, value p = 1 ↔ p = S
  strict : ∀ p, p ≠ N → p ≠ S → value p < value (f p)

private def extendedHeight (h : Pointwise f N S) (b : OrbitBump f N S) (p : M) : ℝ := by
  classical
  exact if hn : p = N then -1 else if hs : p = S then 1 else compress (clock b ⟨p, hn, hs⟩)

private theorem extendedHeight_north (h : Pointwise f N S) (b : OrbitBump f N S) :
    extendedHeight h b N = -1 := by simp [extendedHeight]

private theorem extendedHeight_south (h : Pointwise f N S) (b : OrbitBump f N S) :
    extendedHeight h b S = 1 := by simp [extendedHeight, h.distinct.symm]

private theorem extendedHeight_punctured (h : Pointwise f N S) (b : OrbitBump f N S)
    (p : Punctured N S) : extendedHeight h b p.1 = compress (clock b p) := by
  simp only [extendedHeight, p.2.1, p.2.2, ↓reduceDIte]

private theorem continuousAt_height_north (h : Pointwise f N S) (b : OrbitBump f N S) :
    ContinuousAt (extendedHeight h b) N := by
  rw [ContinuousAt, extendedHeight_north]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht := compress_tendsto_bot.comp (clock_tendsto_north h b)
  obtain ⟨V, hV, hsub⟩ := mem_comap.mp (ht.eventually (Metric.ball_mem_nhds (-1) hε))
  have hNS : {p : M | p ≠ S} ∈ 𝓝 N :=
    isClosed_singleton.isOpen_compl.mem_nhds h.distinct
  filter_upwards [hV, hNS] with p hp hpS
  by_cases hpN : p = N
  · subst p
    simpa only [extendedHeight_north, dist_self] using hε
  · change dist (extendedHeight h b p) (-1) < ε
    rw [extendedHeight_punctured h b ⟨p, hpN, hpS⟩]
    exact hsub (show (⟨p, hpN, hpS⟩ : Punctured N S) ∈ Subtype.val ⁻¹' V from hp)

private theorem continuousAt_height_south (h : Pointwise f N S) (b : OrbitBump f N S) :
    ContinuousAt (extendedHeight h b) S := by
  rw [ContinuousAt, extendedHeight_south]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht := compress_tendsto_top.comp (clock_tendsto_south h b)
  obtain ⟨V, hV, hsub⟩ := mem_comap.mp (ht.eventually (Metric.ball_mem_nhds 1 hε))
  have hSN : {p : M | p ≠ N} ∈ 𝓝 S :=
    isClosed_singleton.isOpen_compl.mem_nhds h.distinct.symm
  filter_upwards [hV, hSN] with p hp hpN
  by_cases hpS : p = S
  · subst p
    simpa only [extendedHeight_south, dist_self] using hε
  · change dist (extendedHeight h b p) 1 < ε
    rw [extendedHeight_punctured h b ⟨p, hpN, hpS⟩]
    exact hsub (show (⟨p, hpN, hpS⟩ : Punctured N S) ∈ Subtype.val ⁻¹' V from hp)

private theorem continuous_extendedHeight (h : Pointwise f N S) (b : OrbitBump f N S) :
    Continuous (extendedHeight h b) := by
  have hc : Continuous (fun p : Punctured N S => extendedHeight h b p.1) := by
    apply (continuous_compress.comp (continuous_clock h b)).congr
    intro p
    exact (extendedHeight_punctured h b p).symm
  have hcOn : ContinuousOn (extendedHeight h b) {p | p ≠ N ∧ p ≠ S} :=
    continuousOn_iff_continuous_domRestrict.mpr hc
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hpN : p = N
  · subst p; exact continuousAt_height_north h b
  by_cases hpS : p = S
  · subst p; exact continuousAt_height_south h b
  exact (hcOn p ⟨hpN, hpS⟩).continuousAt
    (((isOpen_ne_fun continuous_id continuous_const).inter
      (isOpen_ne_fun continuous_id continuous_const)).mem_nhds ⟨hpN, hpS⟩)

/-- Every literal pointwise north-south homeomorphism has a continuous strict
height, obtained from locally finite orbit sums, including both endpoint limits. -/
theorem exists_strictHeight (h : Pointwise f N S) : Nonempty (StrictHeight f N S) := by
  obtain ⟨b⟩ := exists_bump h
  refine ⟨{
    value := extendedHeight h b
    continuous_value := continuous_extendedHeight h b
    north := extendedHeight_north h b
    south := extendedHeight_south h b
    range := ?_
    eq_north := ?_
    eq_south := ?_
    strict := ?_ }⟩
  · intro p
    by_cases hpN : p = N
    · subst p; rw [extendedHeight_north]; constructor <;> norm_num
    by_cases hpS : p = S
    · subst p; rw [extendedHeight_south]; constructor <;> norm_num
    rw [extendedHeight_punctured h b ⟨p, hpN, hpS⟩]
    exact ⟨(compress_range _).1.le, (compress_range _).2.le⟩
  · intro p
    constructor
    · intro he
      by_contra hpN
      by_cases hpS : p = S
      · subst p; rw [extendedHeight_south] at he; norm_num at he
      rw [extendedHeight_punctured h b ⟨p, hpN, hpS⟩] at he
      have hh := (compress_range (clock b ⟨p, hpN, hpS⟩)).1
      linarith
    · rintro rfl; exact extendedHeight_north h b
  · intro p
    constructor
    · intro he
      by_contra hpS
      by_cases hpN : p = N
      · subst p; rw [extendedHeight_north] at he; norm_num at he
      rw [extendedHeight_punctured h b ⟨p, hpN, hpS⟩] at he
      have hh := (compress_range (clock b ⟨p, hpN, hpS⟩)).2
      linarith
    · rintro rfl; exact extendedHeight_south h b
  · intro p hpN hpS
    have he := extendedHeight_punctured h b (next h ⟨p, hpN, hpS⟩)
    change extendedHeight h b (f p) = _ at he
    rw [extendedHeight_punctured h b ⟨p, hpN, hpS⟩, he]
    apply strictMono_compress
    rw [clock_next]
    linarith

#print axioms exists_strictHeight

end D5.S1.Dynamics.Shadowing.PointwiseNorthSouth
