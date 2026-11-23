/- GID: D5/S3/Fourier/ExactFourthRootGaps
   generality: G
   mirror-B: D5/B/S3/Fourier/ExactFourthRootGaps
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact fourth-root gaps give a finite step lower bound for phase deficit. -/

import D5.S3.Fourier.PhaseObstructionLengths
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The largest exact gap threshold on each support determines the weighted
omission function. Its integral is bounded by the weighted losses at each
common time and dominates the series formed from relation lengths alone. -/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace D5.S3.Fourier.ExactFourthRootGaps

open PhaseObstructionLengths (mass average deficit omissionFraction omissionFraction_isLeast
  summand aggregate_bounds shiftedScale shiftedScale_antitone shiftedScale_nonneg
  scaleDifference scaleDifference_hasSum)
open ShortPhaseRelations (fourth_root_gap_sq)
open WeightedIntegerRelations (chord_prod_zpow quarter quarter_chord_sq quarter_character
  orbit_character)

noncomputable section

variable {J : Type*} [DecidableEq J]

/-- The coordinate sine deficit at one common time. -/
def loss (g : J → ℝ) (t : ℝ) (j : J) : ℝ := 1 - Real.sin (g j * t)
/-- The coordinates with nonzero integer coefficients. -/
def relationSupport (s : Finset J) (k : J → ℤ) : Finset J := s.filter fun j => k j ≠ 0
/-- The integer relation's coefficient length. -/
def relationLength (s : Finset J) (k : J → ℤ) : ℕ := ∑ j ∈ s, (k j).natAbs
/-- The coefficient sum that determines the fourth-root target character. -/
def coefficientSum (s : Finset J) (k : J → ℤ) : ℤ := ∑ j ∈ s, k j
private def gap (z : ℤ) : ℝ := ‖(1 : ℂ) - Complex.I ^ z‖ ^ 2
/-- The squared character chord gap divided by twice the squared coefficient length. -/
def tau (s : Finset J) (k : J → ℤ) : ℝ :=
  gap (coefficientSum s k) / (2 * (relationLength s k : ℝ) ^ 2)
/-- A vanishing frequency relation whose quarter-phase character differs from one. -/
def IncompatibleRelation (s : Finset J) (g : J → ℝ) (k : J → ℤ) : Prop :=
  (∑ j ∈ s, (k j : ℝ) * g j) = 0 ∧ ¬ (4 : ℤ) ∣ coefficientSum s k

private lemma loss_nonneg (g : J → ℝ) (t : ℝ) (j : J) : 0 ≤ loss g t j :=
  sub_nonneg.mpr (Real.sin_le_one _)

private lemma loss_le_two (g : J → ℝ) (t : ℝ) (j : J) : loss g t j ≤ 2 := by
  unfold loss
  linarith only [Real.neg_one_le_sin (g j * t)]

private lemma mem_relationSupport {s : Finset J} {k : J → ℤ} {j : J} :
    j ∈ relationSupport s k ↔ j ∈ s ∧ k j ≠ 0 :=
  Finset.mem_filter

private lemma relationSupport_nonempty {s : Finset J} {g : J → ℝ} {k : J → ℤ} (hk : IncompatibleRelation s g k) :
    (relationSupport s k).Nonempty := by
  by_contra! h
  apply hk.2
  rw [coefficientSum, Finset.sum_eq_zero]
  · exact dvd_zero _
  · intro j hj
    by_contra hz
    have hmem := (mem_relationSupport (s := s)).mpr ⟨hj, hz⟩
    simp [h] at hmem

private lemma cast_relationLength (s : Finset J) (k : J → ℤ) :
    (relationLength s k : ℝ) = ∑ j ∈ s, |(k j : ℝ)| := by
  simp only [relationLength, Nat.cast_sum, ← Int.cast_abs, ← Nat.cast_natAbs]

private lemma relationLength_pos {s : Finset J} {g : J → ℝ} {k : J → ℤ} (hk : IncompatibleRelation s g k) :
    0 < relationLength s k := by
  obtain ⟨j, hj⟩ := relationSupport_nonempty hk
  obtain ⟨hjs, hjk⟩ := mem_relationSupport.mp hj
  exact (Int.natAbs_pos.mpr hjk).trans_le
    (Finset.single_le_sum (f := fun i => (k i).natAbs) (fun _ _ => Nat.zero_le _) hjs)

private lemma gap_le_four (z : ℤ) : gap z ≤ 4 := by
  have hn : ‖Complex.I ^ z‖ = 1 := by rw [Complex.norm_zpow, Complex.norm_I, one_zpow]
  have h : ‖(1 : ℂ) - Complex.I ^ z‖ ≤ 2 := by
    simpa only [norm_one, hn, one_add_one_eq_two] using norm_sub_le (1 : ℂ) (Complex.I ^ z)
  simpa only [gap, show (2 : ℝ) ^ 2 = 4 by norm_num] using
    pow_le_pow_left₀ (norm_nonneg _) h 2

private lemma relationLength_sq_ge_one {s : Finset J} {g : J → ℝ} {k : J → ℤ} (hk : IncompatibleRelation s g k) :
    1 ≤ (relationLength s k : ℝ) ^ 2 := by
  have h : (1 : ℝ) ≤ relationLength s k := by exact_mod_cast relationLength_pos hk
  simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h 2

private lemma tau_pos {s : Finset J} {g : J → ℝ} {k : J → ℤ} (hk : IncompatibleRelation s g k) :
    0 < tau s k := by
  have hl := relationLength_sq_ge_one hk
  apply div_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (fourth_root_gap_sq hk.2))
  linarith

private lemma tau_le_two {s : Finset J} {g : J → ℝ} {k : J → ℤ} (hk : IncompatibleRelation s g k) :
    tau s k ≤ 2 := by
  have hl := relationLength_sq_ge_one hk
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (relationLength s k : ℝ) ^ 2)).mpr
  linarith [gap_le_four (coefficientSum s k)]

private lemma invSq_le_tau {s : Finset J} {g : J → ℝ} {k : J → ℤ} (hk : IncompatibleRelation s g k)
    {h : ℕ} (hl : relationLength s k ≤ h) : 1 / (h : ℝ) ^ 2 ≤ tau s k := by
  have hp : 0 < (relationLength s k : ℝ) ^ 2 := lt_of_lt_of_le zero_lt_one (relationLength_sq_ge_one hk)
  have hr : (relationLength s k : ℝ) ≤ h := by exact_mod_cast hl
  calc
    _ ≤ 1 / (relationLength s k : ℝ) ^ 2 :=
      one_div_le_one_div_of_le hp (pow_le_pow_left₀ (by positivity) hr 2)
    _ = 2 / (2 * (relationLength s k : ℝ) ^ 2) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (fourth_root_gap_sq hk.2) (by positivity)

/-- An incompatible character forces a coordinate loss at least its exact threshold. -/
theorem coordinate_loss_same_time (s : Finset J) (g : J → ℝ) (k : J → ℤ)
    (hk : IncompatibleRelation s g k) (t : ℝ) :
    0 < relationLength s k ∧ tau s k ∈ Ioc (0 : ℝ) 2 ∧
      ∃ j ∈ relationSupport s k, tau s k ≤ loss g t j := by
  refine ⟨relationLength_pos hk, ⟨tau_pos hk, tau_le_two hk⟩, ?_⟩
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image (relationSupport s k) (loss g t) (relationSupport_nonempty hk)
  refine ⟨j, hj, ?_⟩
  let radius := ‖(Circle.exp (g j * t) : ℂ) - (quarter : ℂ)‖
  have hchord := chord_prod_zpow s (fun i => Circle.exp (g i * t)) (fun _ => quarter) k
  rw [orbit_character s g k hk.1 t, Circle.coe_one, quarter_character] at hchord
  have hbound :
      (∑ i ∈ s, |(k i : ℝ)| * ‖(Circle.exp (g i * t) : ℂ) - (quarter : ℂ)‖) ≤
        (relationLength s k : ℝ) * radius := by
    rw [cast_relationLength, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hz : k i = 0
    · simp [hz]
    · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      change ‖(Circle.exp (g i * t) : ℂ) - (quarter : ℂ)‖ ^ 2 ≤
        ‖(Circle.exp (g j * t) : ℂ) - (quarter : ℂ)‖ ^ 2
      rw [quarter_chord_sq, quarter_chord_sq]
      exact mul_le_mul_of_nonneg_left (hjmax i (mem_relationSupport.mpr ⟨hi, hz⟩)) (by norm_num)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) (hchord.trans hbound) 2
  have hl := relationLength_sq_ge_one hk
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (relationLength s k : ℝ) ^ 2)).mpr
  change gap _ ≤ _
  rw [mul_pow, show radius ^ 2 = 2 * loss g t j from quarter_chord_sq _] at hsq
  simpa only [gap, coefficientSum, mul_left_comm, mul_comm, mul_assoc] using hsq

private theorem best_mod_class (s : Finset J) (P : (J → ℤ) → Prop) (r : Fin 4)
    (hex : ∃ k, P k ∧ coefficientSum s k % 4 = r.val) :
    ∃ k, (P k ∧ coefficientSum s k % 4 = r.val) ∧
      ∀ k', (P k' ∧ coefficientSum s k' % 4 = r.val) → tau s k' ≤ tau s k := by
  classical
  let p (n : ℕ) := ∃ k, (P k ∧ coefficientSum s k % 4 = r.val) ∧ relationLength s k = n
  have hp : ∃ n, p n := by
    obtain ⟨k, hk⟩ := hex
    exact ⟨relationLength s k, k, hk, rfl⟩
  obtain ⟨k, hk, hlen⟩ := Nat.find_spec hp
  refine ⟨k, hk, fun k' hk' => ?_⟩
  have hle : relationLength s k ≤ relationLength s k' := hlen.trans_le (Nat.find_min' hp ⟨k', hk', rfl⟩)
  have hg : gap (coefficientSum s k') = gap (coefficientSum s k) := by
    unfold gap
    rw [Complex.I_zpow_eq_zpow_mod (coefficientSum s k'), Complex.I_zpow_eq_zpow_mod (coefficientSum s k),
      hk'.2, hk.2]
  by_cases hzero : relationLength s k = 0
  · have hz (l : J → ℤ) (h : relationLength s l = 0) : coefficientSum s l = 0 := by
      unfold coefficientSum
      apply Finset.sum_eq_zero
      intro j hj
      have hle := Finset.single_le_sum (f := fun i => (l i).natAbs) (fun _ _ => Nat.zero_le _) hj
      change (l j).natAbs ≤ relationLength s l at hle
      simpa [h] using hle
    have hg0 : gap (coefficientSum s k) = 0 := by simp [hz k hzero, gap]
    simp only [tau, hg, hg0, zero_div, le_refl]
  · unfold tau
    rw [hg]
    apply div_le_div_of_nonneg_left (sq_nonneg _)
    · have hpos : 0 < (relationLength s k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hzero
      positivity
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hle) 2) (by norm_num)

private theorem mod_index (z : ℤ) : ∃ r : Fin 4, z % 4 = r.val := by
  have h0 : 0 ≤ z % 4 := Int.emod_nonneg _ (by decide)
  have h4 : z % 4 < 4 := Int.emod_lt_of_pos _ (by decide)
  refine ⟨⟨(z % 4).toNat, by omega⟩, ?_⟩
  change z % 4 = ((z % 4).toNat : ℤ)
  omega

private theorem max_tau_on (s : Finset J) (P : (J → ℤ) → Prop) (hex : ∃ k, P k) :
    ∃ k, P k ∧ ∀ k', P k' → tau s k' ≤ tau s k := by
  classical
  let indices := Finset.univ.filter (fun r : Fin 4 =>
    ∃ k, P k ∧ coefficientSum s k % 4 = r.val)
  have hn : indices.Nonempty := by
    obtain ⟨k, hk⟩ := hex
    obtain ⟨r, hr⟩ := mod_index (coefficientSum s k)
    exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hk, hr⟩⟩
  have chooseBest (r : indices) : ∃ k, (P k ∧ coefficientSum s k % 4 = r.val.val) ∧
      ∀ k', (P k' ∧ coefficientSum s k' % 4 = r.val.val) → tau s k' ≤ tau s k :=
    best_mod_class s P r.val (Finset.mem_filter.mp r.property).2
  choose best hbest hbound using chooseBest
  letI : Nonempty indices := ⟨⟨hn.choose, hn.choose_spec⟩⟩
  obtain ⟨r, _, hr⟩ := Finset.exists_max_image (Finset.univ : Finset indices)
    (fun r => tau s (best r)) Finset.univ_nonempty
  refine ⟨best r, (hbest r).1, fun k hk => ?_⟩
  obtain ⟨r', hr'⟩ := mod_index (coefficientSum s k)
  let index : indices := ⟨r', Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hk, hr'⟩⟩
  exact (hbound index k ⟨hk, hr'⟩).trans (hr index (Finset.mem_univ _))

private theorem attained_support (s : Finset J) (g : J → ℝ) (v : Finset J)
    (hex : ∃ k, IncompatibleRelation s g k ∧ relationSupport s k = v) :
    ∃ k, IncompatibleRelation s g k ∧ relationSupport s k = v ∧
      ∀ k', IncompatibleRelation s g k' → relationSupport s k' = v → tau s k' ≤ tau s k := by
  obtain ⟨k, ⟨hk, hs⟩, hm⟩ := max_tau_on s (fun k => IncompatibleRelation s g k ∧ relationSupport s k = v) hex
  exact ⟨k, hk, hs, fun k' hk' hs' => hm k' ⟨hk', hs'⟩⟩

private def admissible (s : Finset J) (g : J → ℝ) (u : Finset J) (x : ℝ) : Prop :=
  ∀ k, IncompatibleRelation s g k → relationSupport s k ⊆ u → tau s k < x

private def cost (s : Finset J) (w : J → ℝ) (u : Finset J) : ℝ := mass (s \ u) w / mass s w

private def costs (s : Finset J) (g w : J → ℝ) (x : ℝ) : Set ℝ :=
  {c | ∃ u ⊆ s, admissible s g u x ∧ c = cost s w u}

/-- The minimum omitted weight fraction at an exact gap threshold. -/
def Q (s : Finset J) (g w : J → ℝ) (x : ℝ) : ℝ := sInf (costs s g w x)

/-- The largest threshold on an exact support, with zero for an empty family. -/
def supportMaximum (s : Finset J) (g : J → ℝ) (v : Finset J) : ℝ :=
  sSup (insert 0 {x | ∃ k, IncompatibleRelation s g k ∧ relationSupport s k = v ∧ x = tau s k})
private theorem admissible_iff_hits (s : Finset J) (g : J → ℝ) (u : Finset J) (x : ℝ) :
    admissible s g u x ↔ ∀ k, IncompatibleRelation s g k → x ≤ tau s k → ∃ j ∈ s \ u, k j ≠ 0 := by
  classical
  constructor
  · intro ha k hk hx
    by_contra! hn
    have hs : relationSupport s k ⊆ u := by
      intro j hj
      by_contra hu
      exact (mem_relationSupport.mp hj).2 (hn j (Finset.mem_sdiff.mpr ⟨(mem_relationSupport.mp hj).1, hu⟩))
    exact (not_lt_of_ge hx) (ha k hk hs)
  · intro h k hk hs
    by_contra! hx
    obtain ⟨j, hj, hkj⟩ := h k hk hx
    exact (Finset.mem_sdiff.mp hj).2 (hs (mem_relationSupport.mpr ⟨(Finset.mem_sdiff.mp hj).1, hkj⟩))

private lemma admissible_empty (s : Finset J) (g : J → ℝ) (x : ℝ) :
    admissible s g ∅ x := by
  intro k hk hs
  obtain ⟨j, hj⟩ := relationSupport_nonempty hk
  exact (Finset.notMem_empty j (hs hj)).elim

private theorem Q_isLeast (s : Finset J) (g w : J → ℝ) (x : ℝ) :
    IsLeast (costs s g w x) (Q s g w x) := by
  classical
  let choices := s.powerset.filter (fun u => admissible s g u x)
  have hn : choices.Nonempty := ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), admissible_empty s g x⟩⟩
  obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image choices (cost s w) hn
  have hleast : IsLeast (costs s g w x) (cost s w u) := by
    refine ⟨⟨u, Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1,
      (Finset.mem_filter.mp hu).2, rfl⟩, ?_⟩
    rintro _ ⟨v, hv, ha, rfl⟩
    exact hmin v (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hv, ha⟩)
  rwa [Q, hleast.csInf_eq]

/-- The threshold cost is attained by a set hitting every active support. -/
theorem least_hitting_weight (s : Finset J) (g w : J → ℝ) (x : ℝ) :
    IsLeast {p | ∃ u ⊆ s, (∀ k, IncompatibleRelation s g k → x ≤ tau s k → ∃ j ∈ s \ u, k j ≠ 0) ∧
      p = (∑ j ∈ s \ u, w j) / ∑ j ∈ s, w j} (Q s g w x) := by
  simpa only [costs, admissible_iff_hits, cost, mass] using Q_isLeast s g w x

private lemma Q_nonneg (s : Finset J) (g w : J → ℝ) (x : ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) : 0 ≤ Q s g w x := by
  obtain ⟨u, _, _, hu⟩ := (Q_isLeast s g w x).1
  rw [hu, cost]
  exact div_nonneg (Finset.sum_nonneg fun j hj => hw j (Finset.mem_sdiff.mp hj).1)
    (Finset.sum_nonneg hw)

private lemma Q_antitone (s : Finset J) (g w : J → ℝ) : Antitone (Q s g w) := by
  intro x y hxy
  obtain ⟨u, hu, ha, huQ⟩ := (Q_isLeast s g w x).1
  exact (Q_isLeast s g w y).2 ⟨u, hu, fun k hk hs => (ha k hk hs).trans_le hxy, huQ⟩

/-- Every nonempty support family attains its positive maximum. -/
theorem supportMaximum_zero_or_attained (s : Finset J) (g : J → ℝ) (v : Finset J) :
    (supportMaximum s g v = 0 ∧ ¬ ∃ k, IncompatibleRelation s g k ∧ relationSupport s k = v) ∨
      ∃ k, IncompatibleRelation s g k ∧ relationSupport s k = v ∧ supportMaximum s g v = tau s k := by
  by_cases h : ∃ k, IncompatibleRelation s g k ∧ relationSupport s k = v
  · obtain ⟨k, hk, hs, hmax⟩ := attained_support s g v h
    right
    refine ⟨k, hk, hs, ?_⟩
    have hg : IsGreatest (insert 0 {x | ∃ k, IncompatibleRelation s g k ∧ relationSupport s k = v ∧ x = tau s k})
        (tau s k) := by
      refine ⟨Or.inr ⟨k, hk, hs, rfl⟩, ?_⟩
      intro y hy
      rcases hy with h0 | ⟨k', hk', hs', rfl⟩
      · rw [h0]
        exact (tau_pos hk).le
      · exact hmax k' hk' hs'
    exact hg.csSup_eq
  · left
    refine ⟨?_, h⟩
    have he : {x | ∃ k, IncompatibleRelation s g k ∧ relationSupport s k = v ∧ x = tau s k} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨k, hk, hs, _⟩
      exact h ⟨k, hk, hs⟩
    simp [supportMaximum, he]

private lemma supportMaximum_bounds (s : Finset J) (g : J → ℝ) (v : Finset J) :
    supportMaximum s g v ∈ Icc (0 : ℝ) 2 := by
  rcases supportMaximum_zero_or_attained s g v with ⟨h, _⟩ | ⟨_, hk, _, h⟩
  · rw [h]
    norm_num
  · rw [h]
    exact ⟨(tau_pos hk).le, tau_le_two hk⟩

private theorem admissible_iff_support_maxima (s : Finset J) (g : J → ℝ) (u : Finset J) {x : ℝ}
    (hx : 0 < x) : admissible s g u x ↔ ∀ v ⊆ u, supportMaximum s g v < x := by
  constructor
  · intro h v hv
    rcases supportMaximum_zero_or_attained s g v with ⟨hz, _⟩ | ⟨k, hk, hs, he⟩
    · rwa [hz]
    · rw [he]
      exact h k hk (hs ▸ hv)
  · intro h k hk hs
    have hxv := h (relationSupport s k) hs
    rcases supportMaximum_zero_or_attained s g (relationSupport s k) with ⟨_, hnone⟩ | ⟨k', hk', hs', he⟩
    · exact (hnone ⟨k, hk, rfl⟩).elim
    · rw [he] at hxv
      have hb : BddAbove (insert 0 {x | ∃ k', IncompatibleRelation s g k' ∧
          relationSupport s k' = relationSupport s k ∧ x = tau s k'}) := by
        refine ⟨2, ?_⟩
        rintro _ (rfl | ⟨k', hk', _, rfl⟩)
        · norm_num
        · exact tau_le_two hk'
      exact (show tau s k ≤ supportMaximum s g (relationSupport s k) from
        le_csSup hb (Or.inr ⟨k, hk, rfl, rfl⟩)).trans_lt (he.symm ▸ hxv)

/-- The support maxima and the two endpoints of the integration interval. -/
def breakpoints (s : Finset J) (g : J → ℝ) : Finset ℝ :=
  insert 0 (insert 2 (s.powerset.image (supportMaximum s g)))

private lemma breakpoints_bounds (s : Finset J) (g : J → ℝ) {x : ℝ}
    (hx : x ∈ breakpoints s g) : x ∈ Icc (0 : ℝ) 2 := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · norm_num
  rcases Finset.mem_insert.mp hx with rfl | hx
  · norm_num
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  exact supportMaximum_bounds s g v

private theorem Q_constant_on_step (s : Finset J) (g w : J → ℝ) {a b x : ℝ}
    (ha : 0 ≤ a) (hax : a < x) (hxb : x ≤ b)
    (hclear : ∀ c ∈ breakpoints s g, ¬ (a < c ∧ c < b)) :
    Q s g w x = Q s g w b := by
  have he (u : Finset J) (hu : u ⊆ s) :
      admissible s g u x ↔ admissible s g u b := by
    rw [admissible_iff_support_maxima s g u (ha.trans_lt hax),
      admissible_iff_support_maxima s g u ((ha.trans_lt hax).trans_le hxb)]
    constructor
    · intro h v hv
      exact (h v hv).trans_le hxb
    · intro h v hv
      by_contra! hn
      have hc : supportMaximum s g v ∈ breakpoints s g := Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_powerset.mpr (hv.trans hu))))
      exact hclear _ hc ⟨hax.trans_le hn, h v hv⟩
  have heq : costs s g w x = costs s g w b := by
    ext c
    change (∃ u ⊆ s, admissible s g u x ∧ c = cost s w u) ↔
      (∃ u ⊆ s, admissible s g u b ∧ c = cost s w u)
    exact ⟨fun ⟨u, hu, h, hc⟩ => ⟨u, hu, (he u hu).mp h, hc⟩,
      fun ⟨u, hu, h, hc⟩ => ⟨u, hu, (he u hu).mpr h, hc⟩⟩
  simp only [Q, heq]

private def tail (s : Finset J) (g w : J → ℝ) (t x : ℝ) : ℝ :=
  (∑ j ∈ s.filter (fun j => x ≤ loss g t j), w j) / mass s w

private theorem Q_le_tail_same_time (s : Finset J) (g w : J → ℝ) (t x : ℝ) :
    Q s g w x ≤ tail s g w t x := by
  classical
  let u := s.filter fun j => loss g t j < x
  have ha : admissible s g u x := by
    intro k hk hs
    obtain ⟨j, hj, hl⟩ := (coordinate_loss_same_time s g k hk t).2.2
    exact hl.trans_lt (Finset.mem_filter.mp (hs hj)).2
  have h := (Q_isLeast s g w x).2 ⟨u, Finset.filter_subset _ _, ha, rfl⟩
  have he : s \ u = s.filter (fun j => x ≤ loss g t j) := by
    ext j
    by_cases hj : j ∈ s <;> simp [u, hj, not_lt]
  simpa only [tail, cost, mass, he] using h

private lemma indicator_integral {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 2) (c : ℝ) :
    (∫ x in (0 : ℝ)..2, (Iic a).indicator (fun _ => c) x) = a * c := by
  change (∫ x in (0 : ℝ)..2, {y | y ≤ a}.indicator (fun _ => c) x) = a * c
  rw [intervalIntegral.integral_indicator (f := fun _ => c) ha, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul]

private theorem antitone_indicator {a c : ℝ} (hc : 0 ≤ c) :
    Antitone ((Iic a).indicator (fun _ => c)) := by
  intro x y hxy
  by_cases hy : y ≤ a
  · have hx := hxy.trans hy
    rw [Set.indicator_of_mem (show y ∈ Iic a from hy),
      Set.indicator_of_mem (show x ∈ Iic a from hx)]
  · rw [Set.indicator_of_notMem (show y ∉ Iic a from hy)]
    exact Set.indicator_nonneg (fun _ _ => hc) _

private theorem tail_integral_same_time (s : Finset J) (g w : J → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (hW : 0 < mass s w) (t : ℝ) :
    (∫ x in (0 : ℝ)..2, tail s g w t x) = 1 - average s g w t := by
  classical
  have heq (x : ℝ) : tail s g w t x =
      ∑ j ∈ s, (Iic (loss g t j)).indicator (fun _ => w j / mass s w) x := by
    rw [tail, Finset.sum_filter, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : x ≤ loss g t j <;> simp [h, Set.indicator]
  simp_rw [heq]
  rw [intervalIntegral.integral_finsetSum (fun j hj =>
    (antitone_indicator (div_nonneg (hw j hj) hW.le)).intervalIntegrable)]
  simp_rw [indicator_integral ⟨loss_nonneg g t _, loss_le_two g t _⟩]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  have hsum : (∑ j ∈ s, loss g t j * w j) =
      mass s w - ∑ j ∈ s, w j * Real.sin (g j * t) := by
    rw [mass, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    unfold loss
    ring
  rw [hsum, sub_div, div_self hW.ne']
  rfl

/-- The integrated omission bound holds at each common time. -/
theorem integrated_Q_same_time (s : Finset J) (g w : J → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (t : ℝ) :
    (∫ x in (0 : ℝ)..2, Q s g w x) ≤ 1 - average s g w t := by
  rcases (Finset.sum_nonneg hw : 0 ≤ mass s w).eq_or_lt with hm | hW
  · have hQ (x : ℝ) : Q s g w x = 0 := by
      obtain ⟨u, _, _, hu⟩ := (Q_isLeast s g w x).1
      rw [hu, cost, ← hm, div_zero]
    simp [hQ, average, ← hm]
  rw [← tail_integral_same_time s g w hw hW t]
  have htail : Antitone (tail s g w t) := by
    intro x y hxy
    apply div_le_div_of_nonneg_right _ hW.le
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      obtain ⟨hjs, hjy⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hjs, hxy.trans hjy⟩
    · intro j hj _
      exact hw j (Finset.mem_filter.mp hj).1
  apply intervalIntegral.integral_mono_on (by norm_num)
    (Q_antitone s g w).intervalIntegrable htail.intervalIntegrable
  exact fun x _ => Q_le_tail_same_time s g w t x

/-- The integrated omission bound holds for every set of allowed times. -/
theorem integrated_Q_le_deficit (s : Finset J) (g w : J → ℝ) (T : Set ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) :
    (∫ x in (0 : ℝ)..2, Q s g w x) ≤ deficit s g w T := by
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simpa [deficit, average, Real.sSup_empty] using integrated_Q_same_time s g w hw 0
  rw [deficit, le_sub_comm]
  apply csSup_le (hT.image _)
  rintro _ ⟨t, _, rfl⟩
  exact le_sub_comm.mp (integrated_Q_same_time s g w hw t)

/-- The largest cut strictly below the given endpoint, with zero as default. -/
def predecessor (cuts : Finset ℝ) (b : ℝ) : ℝ :=
  if h : (cuts.filter (· < b)).Nonempty then (cuts.filter (· < b)).max' h else 0

private lemma predecessor_spec (cuts : Finset ℝ) (hzero : (0 : ℝ) ∈ cuts) {b : ℝ} (hb : 0 < b) :
    predecessor cuts b ∈ cuts ∧ predecessor cuts b < b ∧
      ∀ c ∈ cuts, c < b → c ≤ predecessor cuts b := by
  classical
  let lower := cuts.filter (· < b)
  have hn : lower.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨hzero, hb⟩⟩
  rw [predecessor, dite_eq_left hn]
  have hmax := Finset.mem_filter.mp (Finset.max'_mem lower hn)
  exact ⟨hmax.1, hmax.2, fun c hc hb' =>
    lower.le_max' c (Finset.mem_filter.mpr ⟨hc, hb'⟩)⟩

/-- The positive thresholds split into disjoint right-closed cells of constant cost. -/
theorem breakpoint_partition (s : Finset J) (g w : J → ℝ) :
    let cuts := breakpoints s g
    let rights := cuts.erase 0
    let cell := fun b => Ioc (predecessor cuts b) b
    ((rights : Set ℝ).PairwiseDisjoint cell) ∧
      (⋃ b ∈ rights, cell b) = Ioc 0 2 ∧
      ∀ b ∈ rights, ∀ x ∈ cell b, Q s g w x = Q s g w b := by
  dsimp only
  let cuts := breakpoints s g
  let rights := cuts.erase 0
  let cell := fun b => Ioc (predecessor cuts b) b
  change (rights : Set ℝ).PairwiseDisjoint cell ∧ (⋃ b ∈ rights, cell b) = Ioc 0 2 ∧
    ∀ b ∈ rights, ∀ x ∈ cell b, Q s g w x = Q s g w b
  have hzero : (0 : ℝ) ∈ cuts := Finset.mem_insert_self _ _
  have htwo : (2 : ℝ) ∈ cuts := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hright {b : ℝ} (hb : b ∈ rights) : b ∈ cuts ∧ 0 < b := by
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hb
    exact ⟨hmem, lt_of_le_of_ne (breakpoints_bounds s g hmem).1 hne.symm⟩
  constructor
  · intro b hb d hd hbd
    obtain ⟨hbm, hbp⟩ := hright hb
    obtain ⟨hdm, hdp⟩ := hright hd
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases lt_or_gt_of_ne hbd with hlt | hlt
    · exact (not_lt_of_ge (hx.2.trans
        ((predecessor_spec cuts hzero hdp).2.2 b hbm hlt))) hy.1
    · exact (not_lt_of_ge (hy.2.trans
        ((predecessor_spec cuts hzero hbp).2.2 d hdm hlt))) hx.1
  constructor
  · ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨b, hb, hx⟩
      obtain ⟨hm, hp⟩ := hright hb
      have hpre := predecessor_spec cuts hzero hp
      exact ⟨lt_of_le_of_lt (breakpoints_bounds s g hpre.1).1 hx.1,
        hx.2.trans (breakpoints_bounds s g hm).2⟩
    · intro hx
      let candidates := cuts.filter fun b => x ≤ b
      have hn : candidates.Nonempty := ⟨2, Finset.mem_filter.mpr ⟨htwo, hx.2⟩⟩
      obtain ⟨b, hb, hmin⟩ := Finset.exists_min_image candidates id hn
      obtain ⟨hm, hxle⟩ := Finset.mem_filter.mp hb
      have hp : 0 < b := hx.1.trans_le hxle
      have hpre := predecessor_spec cuts hzero hp
      refine ⟨b, Finset.mem_erase.mpr ⟨hp.ne', hm⟩, ?_, hxle⟩
      by_contra! hfail
      exact (not_le_of_gt hpre.2.1) (hmin _ (Finset.mem_filter.mpr ⟨hpre.1, hfail⟩))
  · intro b hb x hx
    have hpr := predecessor_spec cuts hzero (hright hb).2
    apply Q_constant_on_step s g w (breakpoints_bounds s g hpr.1).1 hx.1 hx.2
    rintro y hy ⟨hlo, hhi⟩
    exact (not_lt_of_ge (hpr.2.2 y hy hhi)) hlo

/-- The integrated threshold cost is a finite sum of rectangle areas. -/
theorem finite_step_integral (s : Finset J) (g w : J → ℝ) :
    let cuts := breakpoints s g
    (∫ x in (0 : ℝ)..2, Q s g w x) =
      ∑ b ∈ cuts.erase 0, (b - predecessor cuts b) * Q s g w b := by
  dsimp only
  let cuts := breakpoints s g
  let rights := cuts.erase 0
  let cell := fun b => Ioc (predecessor cuts b) b
  change (∫ x in (0 : ℝ)..2, Q s g w x) =
    ∑ b ∈ rights, (b - predecessor cuts b) * Q s g w b
  have hzero : (0 : ℝ) ∈ cuts := Finset.mem_insert_self _ _
  have hprev (b : ℝ) (hb : b ∈ rights) :
      predecessor cuts b ∈ cuts ∧ predecessor cuts b < b ∧
        ∀ c ∈ cuts, c < b → c ≤ predecessor cuts b := by
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hb
    exact predecessor_spec cuts hzero
      (lt_of_le_of_ne (breakpoints_bounds s g hm).1 hne.symm)
  obtain ⟨hdisjoint, hcover, hconstant⟩ := breakpoint_partition s g w
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2), ← hcover]
  rw [integral_biUnion_finset rights (s := cell) (fun _ _ => measurableSet_Ioc) hdisjoint]
  · apply Finset.sum_congr rfl
    intro b hb
    have hpr := hprev b hb
    calc
      (∫ x in cell b, Q s g w x) = ∫ _ in cell b, Q s g w b := by
        apply setIntegral_congr_fun measurableSet_Ioc
        exact hconstant b hb
      _ = _ := by
        rw [show cell b = Ioc (predecessor cuts b) b from rfl,
          ← intervalIntegral.integral_of_le hpr.2.1.le, intervalIntegral.integral_const, smul_eq_mul]
  · intro b _
    exact (Q_antitone s g w).intervalIntegrable.1

private theorem length_omission_le_Q (s : Finset J) (g w : J → ℝ)
    {h : ℕ} {x : ℝ} (hx : x ≤ 1 / (h : ℝ) ^ 2) :
    omissionFraction s g w h ≤ Q s g w x := by
  obtain ⟨u, hu, ha, heq⟩ := (Q_isLeast s g w x).1
  rw [heq]
  apply (omissionFraction_isLeast s g w h).2
  refine ⟨u, hu, ?_, rfl⟩
  intro k hzero hrel hlength
  by_contra hb
  have hk : IncompatibleRelation s g k := ⟨hrel, hb⟩
  have hle : relationLength s k ≤ h := by
    have hcast : (relationLength s k : ℤ) = ∑ j ∈ s, |k j| := by
      simp only [relationLength, Nat.cast_sum, Int.natCast_natAbs]
    exact_mod_cast (hcast.trans_le hlength)
  have hsupp : relationSupport s k ⊆ u := by
    intro j hj
    exact not_not.mp fun h => (mem_relationSupport.mp hj).2 (hzero j h)
  exact (not_lt_of_ge (hx.trans (invSq_le_tau hk hle))) (ha k hk hsupp)

private lemma shiftedScale_le_two (n : ℕ) : shiftedScale n ≤ 2 := by
  have h := shiftedScale_antitone (Nat.zero_le n)
  exact h.trans (by change (1 : ℝ) / (↑(0 + 1 : ℕ) : ℝ) ^ 2 ≤ 2; norm_num)

private lemma Q_integral_nonneg (s : Finset J) (g w : J → ℝ) (hw : ∀ j ∈ s, 0 ≤ w j)
    {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ ∫ u in x..y, Q s g w u := by
  apply intervalIntegral.integral_nonneg hxy
  intro u _
  exact Q_nonneg s g w u hw

/-- The threshold integral dominates each partial length sum. -/
theorem partial_length_le_integral (s : Finset J) (g w : J → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (N : ℕ) :
    (∑ n ∈ Finset.range N, summand s g w (n + 1)) ≤
      ∫ x in (0 : ℝ)..2, Q s g w x := by
  have hi (x y : ℝ) : IntervalIntegrable (Q s g w) volume x y :=
    (Q_antitone s g w).intervalIntegrable
  have hslice (n : ℕ) :
      summand s g w (n + 1) ≤ ∫ x in shiftedScale (n + 1)..shiftedScale n, Q s g w x := by
    have h := intervalIntegral.integral_mono_on (shiftedScale_antitone (Nat.le_succ n))
      (intervalIntegrable_const (c := omissionFraction s g w (n + 1)))
      (hi (shiftedScale (n + 1)) (shiftedScale n))
      (fun x hx => length_omission_le_Q s g w (show x ≤ shiftedScale n from hx.2))
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    exact h
  have hpartial (N : ℕ) :
      (∑ n ∈ Finset.range N, summand s g w (n + 1)) ≤
        ∫ x in shiftedScale N..2, Q s g w x := by
    induction N with
    | zero =>
      simpa only [Finset.sum_range_zero] using Q_integral_nonneg s g w hw (shiftedScale_le_two 0)
    | succ n ih =>
      rw [Finset.sum_range_succ, ← intervalIntegral.integral_add_adjacent_intervals
        (hi (shiftedScale (n + 1)) (shiftedScale n)) (hi (shiftedScale n) 2), add_comm]
      exact add_le_add (hslice n) ih
  calc
    _ ≤ ∫ x in shiftedScale N..2, Q s g w x := hpartial N
    _ ≤ (∫ x in (0 : ℝ)..shiftedScale N, Q s g w x) + ∫ x in shiftedScale N..2, Q s g w x :=
      le_add_of_nonneg_left (Q_integral_nonneg s g w hw (shiftedScale_nonneg N))
    _ = _ := intervalIntegral.integral_add_adjacent_intervals (hi 0 (shiftedScale N)) (hi (shiftedScale N) 2)

/-- The threshold integral dominates the coefficient-length series. -/
theorem length_series_le_integral (s : Finset J) (g w : J → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) :
    (∑' n, summand s g w (n + 1)) ≤ ∫ x in (0 : ℝ)..2, Q s g w x := by
  have hsum := (aggregate_bounds s g w Set.univ hw).2.1.summable
  exact hsum.tsum_le_of_sum_range_le (partial_length_le_integral s g w hw)

abbrev pairIndices : Finset (Fin 2) := Finset.univ
/-- The frequency pair with a shortest relation of length four and chord gap squared four. -/
def pairFrequency : Fin 2 → ℝ := ![1, 3]
private def pairRelation : Fin 2 → ℤ := ![3, -1]

private lemma pairRelation_incompatible : IncompatibleRelation pairIndices pairFrequency pairRelation := by
  norm_num [IncompatibleRelation, coefficientSum, Fin.sum_univ_two, pairFrequency, pairRelation]

private lemma pair_len (k : Fin 2 → ℤ) (hk : IncompatibleRelation pairIndices pairFrequency k) : 4 ≤ relationLength pairIndices k := by
  have hr : (k 0 : ℝ) + (k 1 : ℝ) * 3 = 0 := by
    simpa [Fin.sum_univ_two, pairFrequency] using hk.1
  have hz : k 0 + k 1 * 3 = 0 := by exact_mod_cast hr
  have h0 : k 0 = k 1 * (-3) := by omega
  have h1 : k 1 ≠ 0 := by
    intro hh
    apply hk.2
    simp [coefficientSum, Fin.sum_univ_two, h0, hh]
  simp only [relationLength, Fin.sum_univ_two, h0, Int.natAbs_mul]
  have hp := Int.natAbs_pos.mpr h1
  change 4 ≤ (k 1).natAbs * 3 + (k 1).natAbs
  omega

private lemma pair_support (k : Fin 2 → ℤ) (hk : IncompatibleRelation pairIndices pairFrequency k) : relationSupport pairIndices k = pairIndices := by
  have hr : (k 0 : ℝ) + (k 1 : ℝ) * 3 = 0 := by
    simpa [Fin.sum_univ_two, pairFrequency] using hk.1
  have hz : k 0 + k 1 * 3 = 0 := by exact_mod_cast hr
  have hsum : ¬ (4 : ℤ) ∣ k 0 + k 1 := by simpa [coefficientSum, Fin.sum_univ_two] using hk.2
  have h0 : k 0 ≠ 0 := by
    intro h
    have h' : k 1 = 0 := by omega
    simp [h, h'] at hsum
  have h1 : k 1 ≠ 0 := by omega
  apply Finset.eq_univ_of_forall
  intro j
  fin_cases j
  · exact mem_relationSupport.mpr ⟨Finset.mem_univ _, h0⟩
  · exact mem_relationSupport.mpr ⟨Finset.mem_univ _, h1⟩

private lemma pair_cost_single (w : ℝ) (hw : 0 < w) : cost pairIndices (fun _ => w) {0} = 1 / 2 := by
  have hsplit : mass (pairIndices \ {0}) (fun _ => w) + mass ({0} : Finset (Fin 2)) (fun _ => w) =
      mass pairIndices (fun _ => w) := Finset.sum_sdiff (Finset.subset_univ _)
  have hmass : mass pairIndices (fun _ => w) = w + w := by simp [mass, two_mul]
  have hs : mass ({0} : Finset (Fin 2)) (fun _ => w) = w := by simp [mass]
  have hd : mass (pairIndices \ {0}) (fun _ => w) = w := by linarith only [hsplit, hs, hmass]
  rw [cost, hd, hmass]
  field_simp
  ring

private lemma pair_cost_of_ne (w : ℝ) (hw : 0 < w) (u : Finset (Fin 2)) (hu : u ≠ pairIndices) :
    1 / 2 ≤ cost pairIndices (fun _ => w) u := by
  have hn : (pairIndices \ u).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hs
    exact hu (Finset.eq_univ_of_forall fun j => hs (Finset.mem_univ j))
  obtain ⟨j, hj⟩ := hn
  have hle : w ≤ mass (pairIndices \ u) (fun _ => w) :=
    Finset.single_le_sum (f := pairW w) (fun _ _ => hw.le) hj
  have hmass : mass pairIndices (fun _ => w) = w + w := by simp [mass, two_mul]
  rw [cost, hmass, le_div_iff₀ (by positivity : 0 < w + w)]
  linarith only [hle]

private lemma pairRelation_length : relationLength pairIndices pairRelation = 4 := by
  norm_num [relationLength, Fin.sum_univ_two, pairRelation]

private lemma pairRelation_tau : tau pairIndices pairRelation = 1 / 8 := by
  have hsum : coefficientSum pairIndices pairRelation = 2 := by norm_num [coefficientSum, Fin.sum_univ_two, pairRelation]
  have hg : gap 2 = 4 := by
    rw [gap, show (2 : ℤ) = (2 : ℕ) from rfl, zpow_natCast, Complex.I_sq, Complex.sq_norm,
      Complex.normSq_apply]
    norm_num [Complex.sub_re, Complex.sub_im]
  rw [tau, hsum, hg, pairRelation_length]
  norm_num

/-- The equal-weight pair has one positive threshold and a cost of one half below it. -/
theorem pair_exact_Q (w : ℝ) (hw : 0 < w) (x : ℝ) :
    Q pairIndices pairFrequency (fun _ => w) x = if x ≤ (1 : ℝ) / 8 then 1 / 2 else 0 := by
  split_ifs with hx
  · apply le_antisymm
    · rw [← pair_cost_single w hw]
      apply (Q_isLeast _ _ _ _).2
      refine ⟨{0}, Finset.subset_univ _, ?_, rfl⟩
      intro k hk hs
      rw [pair_support k hk] at hs
      have := hs (Finset.mem_univ (1 : Fin 2))
      norm_num at this
    · obtain ⟨u, _, ha, hc⟩ := (Q_isLeast pairIndices pairFrequency (fun _ => w) x).1
      rw [hc]
      apply pair_cost_of_ne w hw
      rintro rfl
      have hh := ha pairRelation pairRelation_incompatible (Finset.subset_univ _)
      rw [pairRelation_tau] at hh
      exact (not_lt_of_ge hx) hh
  · apply le_antisymm
    · have hc : cost pairIndices (fun _ => w) pairIndices = 0 := by simp [cost, mass]
      rw [← hc]
      apply (Q_isLeast _ _ _ _).2
      refine ⟨pairIndices, Subset.rfl, ?_, rfl⟩
      intro k hk _
      have hl : (4 : ℝ) ≤ relationLength pairIndices k := by exact_mod_cast pair_len k hk
      have hden : (32 : ℝ) ≤ 2 * (relationLength pairIndices k : ℝ) ^ 2 := by
        have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hl 2
        linarith only [hh]
      have ht : tau pairIndices k ≤ 1 / 8 := by
        unfold tau
        calc
          _ ≤ 4 / (2 * (relationLength pairIndices k : ℝ) ^ 2) :=
            div_le_div_of_nonneg_right (gap_le_four _) (by positivity)
          _ ≤ 4 / 32 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
          _ = _ := by norm_num
      exact ht.trans_lt (lt_of_not_ge hx)
    · exact Q_nonneg _ _ _ _ (fun _ _ => hw.le)

private theorem pair_exact_integral (w : ℝ) (hw : 0 < w) :
    (∫ x in (0 : ℝ)..2, Q pairIndices pairFrequency (fun _ => w) x) = 1 / 16 := by
  have heq (x : ℝ) : Q pairIndices pairFrequency (fun _ => w) x =
      (Iic ((1 : ℝ) / 8)).indicator (fun _ => (1 : ℝ) / 2) x := by
    rw [pair_exact_Q w hw]
    simp [Set.indicator]
  simp_rw [heq]
  rw [indicator_integral (a := (1 : ℝ) / 8) (by norm_num)]
  norm_num

private lemma pair_length_omission (w : ℝ) (hw : 0 < w) (h : ℕ) :
    omissionFraction pairIndices pairFrequency (fun _ => w) h = if 4 ≤ h then 1 / 2 else 0 := by
  have hleast := omissionFraction_isLeast pairIndices pairFrequency (fun _ => w) h
  split_ifs with hh
  · apply le_antisymm
    · rw [← pair_cost_single w hw]
      apply hleast.2
      refine ⟨{0}, Finset.subset_univ _, ?_, rfl⟩
      intro k hzero hr _
      by_contra hb
      have hs := pair_support k ⟨hr, hb⟩
      have hm : (1 : Fin 2) ∈ relationSupport pairIndices k := by rw [hs]; exact Finset.mem_univ _
      have hz : k 1 = 0 := hzero 1 (by decide)
      exact (mem_relationSupport.mp hm).2 hz
    · obtain ⟨u, _, hg, hcost⟩ := hleast.1
      refine (le_trans ?_ hcost.symm.le : (1 : ℝ) / 2 ≤ _)
      apply pair_cost_of_ne w hw
      rintro rfl
      apply pairRelation_incompatible.2
      have hlen : (∑ j ∈ pairIndices, |pairRelation j|) = 4 := by norm_num [Fin.sum_univ_two, pairRelation]
      apply hg pairRelation (fun j hj => (hj (Finset.mem_univ j)).elim) pairRelation_incompatible.1
      rw [hlen]
      exact_mod_cast hh
  · apply le_antisymm
    · have hc : cost pairIndices (fun _ => w) pairIndices = 0 := by simp [cost, mass]
      rw [← hc]
      apply hleast.2
      refine ⟨pairIndices, Subset.rfl, ?_, rfl⟩
      intro k _ hrel hlen
      by_contra hb
      have he : (relationLength pairIndices k : ℤ) = ∑ j ∈ pairIndices, |k j| := by
        simp only [relationLength, Nat.cast_sum, Int.natCast_natAbs]
      have hle : relationLength pairIndices k ≤ h := by exact_mod_cast he.trans_le hlen
      exact hh ((pair_len k ⟨hrel, hb⟩).trans hle)
    · obtain ⟨u, _, _, hcost⟩ := hleast.1
      refine (le_trans ?_ hcost.symm.le : (0 : ℝ) ≤ _)
      apply div_nonneg
      · exact Finset.sum_nonneg fun j _ => hw.le
      · exact Finset.sum_nonneg fun j _ => hw.le


private theorem pair_exact_length_series (w : ℝ) (hw : 0 < w) :
    (∑' n, summand pairIndices pairFrequency (fun _ => w) (n + 1)) = 1 / 32 := by
  let f (n : ℕ) := summand pairIndices pairFrequency (fun _ => w) (n + 1)
  have hterm (n : ℕ) : f n = scaleDifference n * (if 4 ≤ n + 1 then 1 / 2 else 0) := by
    change scaleDifference n * omissionFraction pairIndices pairFrequency (fun _ => w) (n + 1) = _
    rw [pair_length_omission w hw]
  have hprefix : ∑ n ∈ Finset.range 3, f n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn' := Finset.mem_range.mp hn
    rw [hterm, ite_eq_right (by omega), mul_zero]
  have htail : HasSum (fun n => f (n + 3)) (shiftedScale 3 * (1 / 2)) := by
    convert (scaleDifference_hasSum 3).mul_right ((1 : ℝ) / 2) using 1
    funext n
    rw [hterm, ite_eq_left (by omega)]
  have hsum := htail.sum_range_add
  rw [hprefix, zero_add] at hsum
  change (∑' n, f n) = _
  rw [hsum.tsum_eq]
  change (1 : ℝ) / ((↑(3 + 1 : ℕ) : ℝ) ^ 2) * (1 / 2) = _
  norm_num

/-- The exact threshold integral is twice the length series for the equal-weight pair. -/
theorem pair_strict (w : ℝ) (hw : 0 < w) :
    (∑' n, summand pairIndices pairFrequency (fun _ => w) (n + 1)) = 1 / 32 ∧
    (∫ x in (0 : ℝ)..2, Q pairIndices pairFrequency (fun _ => w) x) = 1 / 16 ∧
    (∑' n, summand pairIndices pairFrequency (fun _ => w) (n + 1)) <
      ∫ x in (0 : ℝ)..2, Q pairIndices pairFrequency (fun _ => w) x := by
  rw [pair_exact_length_series w hw, pair_exact_integral w hw]
  norm_num

end

end D5.S3.Fourier.ExactFourthRootGaps
