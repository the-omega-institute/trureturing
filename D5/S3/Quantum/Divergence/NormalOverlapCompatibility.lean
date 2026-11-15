/- GID: D5/S3/Quantum/Divergence/NormalOverlapCompatibility
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/NormalOverlapCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual normal overlaps and finite positive-secant posterior interpolation. -/

import D5.S3.Quantum.Divergence.GeneralConvexReverseTestAttainment
import Mathlib.Analysis.Convex.Slope

/-! Ordered functionals are tested on every positive algebra element. The
posterior family is the actual full continuous-moment family, and its outputs
are linked to the independently defined concrete coefficient predual. -/

noncomputable section
open Set MeasureTheory
open scoped ComplexOrder Topology
open D5.S3.Quantum.Analysis.NormalMomentFamily
open D5.S3.Quantum.Analysis.ConcreteCoefficientPredual
open D5.S3.Quantum.Analysis.ConcreteCoefficientSeries
open D5.S3.Quantum.Divergence.GeneralConvexReverseTestAttainment

namespace D5.S3.Quantum.Divergence.NormalOverlapCompatibility


variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Positivity in the actual continuous dual. -/
def Positive (φ : StrongDual ℂ A) : Prop := ∀ a, 0 ≤ a → 0 ≤ φ a

/-- Order in the actual continuous dual, not just order of masses. -/
def Below (φ ψ : StrongDual ℂ A) : Prop := ∀ a, 0 ≤ a → φ a ≤ ψ a

/-- The continuous overlap observation, including the two posterior endpoints. -/
def overlapFunction (t : ℝ) : C(Interval, ℂ) :=
  ⟨fun x => ((min x.val (t * (1 - x.val)) : ℝ) : ℂ), by fun_prop⟩

/-- The functional overlap of an actual posterior family. -/
def overlap {ρ σ : StrongDual ℂ A} (F : Family ρ σ) (t : ℝ) : StrongDual ℂ A :=
  linearMap F (overlapFunction t)

private theorem map_positive {ρ σ : StrongDual ℂ A} (F : Family ρ σ)
    (g : C(Interval, ℂ)) (hg : ∀ x, 0 ≤ g x) : Positive (linearMap F g) :=
  F.property.2.2.1 g hg

private theorem map_mono {ρ σ : StrongDual ℂ A} (F : Family ρ σ)
    {g h : C(Interval, ℂ)} (hgh : ∀ x, g x ≤ h x) :
    Below (linearMap F g) (linearMap F h) := by
  have hp := map_positive F (h - g) (fun x => sub_nonneg.mpr (hgh x))
  intro a ha
  simpa only [map_sub, sub_apply, sub_nonneg] using hp a ha

theorem overlap_feasible {ρ σ : StrongDual ℂ A} (F : Family ρ σ)
    (t : ℝ) (ht : 0 ≤ t) :
    Positive (overlap F t) ∧ Below (overlap F t) ρ ∧
      Below (overlap F t) (t • σ) := by
  refine ⟨map_positive F _ (fun x => ?_), ?_, ?_⟩
  · change (0 : ℂ) ≤ (min x.val (t * (1 - x.val)) : ℝ)
    exact_mod_cast le_min x.property.1 (mul_nonneg ht (sub_nonneg.mpr x.property.2))
  · have h := map_mono F (g := overlapFunction t) (h := posterior)
      (fun x => by
        change ((min x.val (t * (1 - x.val)) : ℝ) : ℂ) ≤ (x.val : ℂ)
        exact_mod_cast min_le_left x.val (t * (1 - x.val)))
    rwa [posterior_value] at h
  · have h := map_mono F (g := overlapFunction t)
      (h := (t : ℂ) • (1 - posterior)) (fun x => by
        change ((min x.val (t * (1 - x.val)) : ℝ) : ℂ) ≤ (t : ℂ) * (1 - (x.val : ℂ))
        exact_mod_cast min_le_right x.val (t * (1 - x.val)))
    rw [map_smul, map_sub, unit_value, posterior_value] at h
    have he : (ρ + σ) - ρ = σ := by abel
    simpa only [he, Complex.coe_smul, overlap] using h

private theorem continuous_overlap_mass (ρ σ : StrongDual ℂ A) (t : ℝ) :
    Continuous (fun F : Family ρ σ => (overlap F t 1).re) := by
  exact Complex.continuous_re.comp
    ((WeakDual.eval_continuous (1 : A)).comp
      ((continuous_apply (overlapFunction t)).comp continuous_subtype_val))

/-- Functional divided difference of the actual overlap path. -/
def overlapSecant {ρ σ : StrongDual ℂ A} (F : Family ρ σ) (s t : ℝ) : StrongDual ℂ A :=
  (t - s)⁻¹ • (overlap F t - overlap F s)

private def secantFunction (s t : ℝ) : C(Interval, ℂ) :=
  (((t - s)⁻¹ : ℝ) : ℂ) • (overlapFunction t - overlapFunction s)

private theorem secant_map {ρ σ : StrongDual ℂ A} (F : Family ρ σ) (s t : ℝ) :
    linearMap F (secantFunction s t) = overlapSecant F s t := by
  rw [secantFunction, map_smul, map_sub]
  simp only [Complex.coe_smul, overlapSecant, overlap]

private theorem overlap_secant_bounds {ρ σ : StrongDual ℂ A} (F : Family ρ σ)
    (s t : ℝ) (hst : s < t) :
    Positive (overlapSecant F s t) ∧ Below (overlapSecant F s t) σ := by
  have hpoint (x : Interval) :
      0 ≤ (min x.val (t * (1 - x.val)) - min x.val (s * (1 - x.val))) / (t - s) ∧
      (min x.val (t * (1 - x.val)) - min x.val (s * (1 - x.val))) / (t - s) ≤ 1 - x.val := by
    have hq : 0 ≤ 1 - x.val := sub_nonneg.mpr x.property.2
    have hmono := min_le_min_left x.val (mul_le_mul_of_nonneg_right hst.le hq)
    have ha := abs_min_sub_min_le_max x.val (t * (1 - x.val)) x.val (s * (1 - x.val))
    rw [sub_self, abs_zero, max_eq_right (abs_nonneg _), ← sub_mul,
      abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hst.le) hq)] at ha
    exact ⟨div_nonneg (sub_nonneg.mpr hmono) (sub_pos.mpr hst).le,
      (div_le_iff₀ (sub_pos.mpr hst)).mpr (by
        have hh := le_abs_self (min x.val (t * (1 - x.val)) - min x.val (s * (1 - x.val)))
        nlinarith)⟩
  have hg (x : Interval) : secantFunction s t x =
      (((min x.val (t * (1 - x.val)) - min x.val (s * (1 - x.val))) / (t - s) : ℝ) : ℂ) := by
    simp only [secantFunction, ContinuousMap.smul_apply, ContinuousMap.sub_apply,
      overlapFunction, ContinuousMap.coe_mk, smul_eq_mul, Complex.ofReal_div,
      Complex.ofReal_sub, Complex.ofReal_inv, div_eq_mul_inv]
    push_cast
    ring
  have hp := map_positive F (secantFunction s t) (fun x => by
    rw [hg]; exact_mod_cast (hpoint x).1)
  have hl := map_mono F (g := secantFunction s t) (h := 1 - posterior) (fun x => by
    rw [hg]
    change ((_ : ℝ) : ℂ) ≤ 1 - (x.val : ℂ)
    exact_mod_cast (hpoint x).2)
  rw [secant_map] at hp hl
  rw [map_sub, unit_value, posterior_value] at hl
  have he : (ρ + σ) - ρ = σ := by abel
  rw [he] at hl
  exact ⟨hp, hl⟩

private theorem overlap_secant_antitone {ρ σ : StrongDual ℂ A} (F : Family ρ σ)
    (r s t v : ℝ) (hrs : r < s) (hst : s ≤ t) (htv : t < v) :
    Below (overlapSecant F t v) (overlapSecant F r s) := by
  have hpoint (x : Interval) :
      (min x.val (v * (1 - x.val)) - min x.val (t * (1 - x.val))) / (v - t) ≤
      (min x.val (s * (1 - x.val)) - min x.val (r * (1 - x.val))) / (s - r) := by
    have hc : ConcaveOn ℝ Set.univ (fun z : ℝ => min x.val (z * (1 - x.val))) := by
      refine ⟨convex_univ, ?_⟩
      intro y _ z _ a b ha hb hab
      change a * min x.val (y * (1 - x.val)) + b * min x.val (z * (1 - x.val)) ≤
        min x.val ((a * y + b * z) * (1 - x.val))
      apply le_min
      · have h1 := mul_le_mul_of_nonneg_left (min_le_left x.val (y * (1 - x.val))) ha
        have h2 := mul_le_mul_of_nonneg_left (min_le_left x.val (z * (1 - x.val))) hb
        calc
          _ ≤ a * x.val + b * x.val := add_le_add h1 h2
          _ = x.val := by rw [← add_mul, hab, one_mul]
      · have h1 := mul_le_mul_of_nonneg_left (min_le_right x.val (y * (1 - x.val))) ha
        have h2 := mul_le_mul_of_nonneg_left (min_le_right x.val (z * (1 - x.val))) hb
        calc
          _ ≤ a * (y * (1 - x.val)) + b * (z * (1 - x.val)) := add_le_add h1 h2
          _ = _ := by ring
    rcases hst.eq_or_lt with he | hlt
    · subst t
      exact hc.slope_anti_adjacent (mem_univ _) (mem_univ _) hrs htv
    · exact (hc.slope_anti_adjacent (mem_univ _) (mem_univ _) hlt htv).trans
        (hc.slope_anti_adjacent (mem_univ _) (mem_univ _) hrs hlt)
  have h := map_mono F (g := secantFunction t v) (h := secantFunction r s) (fun x => by
    change (((v - t)⁻¹ : ℝ) : ℂ) *
      (((min x.val (v * (1 - x.val)) : ℝ) : ℂ) - ((min x.val (t * (1 - x.val)) : ℝ) : ℂ)) ≤
      (((s - r)⁻¹ : ℝ) : ℂ) *
      (((min x.val (s * (1 - x.val)) : ℝ) : ℂ) - ((min x.val (r * (1 - x.val)) : ℝ) : ℂ))
    have hh := hpoint x
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm _ (v - t)⁻¹, mul_comm _ (s - r)⁻¹] at hh
    exact_mod_cast hh)
  rwa [secant_map, secant_map] at h

private def endpoint (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : Interval := ⟨x, hx⟩

/-- Three positive blocks realize every feasible functional overlap exactly.
No state, normalization by a mass, or nonzero functional is chosen. -/
theorem feasible_overlap_realized {ρ σ η : StrongDual ℂ A} (t : ℝ) (ht : 0 < t)
    (hη : Positive η) (hηρ : Below η ρ) (hησ : Below η (t • σ)) :
    ∃ F : Family ρ σ, overlap F t = η := by
  let x : Interval := ⟨t / (1 + t),
    ⟨div_nonneg ht.le (by linarith), (div_le_one (by linarith)).mpr (by linarith)⟩⟩
  let B := (t⁻¹ : ℝ) • η
  let U := σ - B
  let V := ρ - η
  have hU : Positive U := by
    intro a ha
    have h := hησ a ha
    change η a ≤ t • σ a at h
    have h' := smul_le_smul_of_nonneg_left h (inv_nonneg.mpr ht.le)
    simpa only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul, U, B,
      sub_apply, smul_apply, sub_nonneg] using h'
  have hV : Positive V := fun a ha => sub_nonneg.mpr (hηρ a ha)
  have hB : Positive B := fun a ha => smul_nonneg (inv_nonneg.mpr ht.le) (hη a ha)
  let J : C(Interval, ℂ) →ₗ[ℂ] StrongDual ℂ A :=
    { toFun g := g (endpoint 0 (by simp)) • U +
        g (endpoint 1 (by simp)) • V + (((1 + t : ℝ) : ℂ) * g x) • B
      map_add' g h := by
        simp only [ContinuousMap.add_apply, mul_add, add_smul]; module
      map_smul' z g := by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply, id_eq, smul_eq_mul,
          smul_add, smul_smul]
        congr 1
        congr 1
        ring }
  have hunit : J 1 = ρ + σ := by
    change (1 : ℂ) • U + (1 : ℂ) • V + (((1 + t : ℝ) : ℂ) * 1) • B = _
    simp only [one_smul, mul_one, Complex.coe_smul, U, V, B, add_smul, one_smul,
      smul_smul]
    rw [add_mul, one_mul, mul_inv_cancel₀ ht.ne', add_smul]
    module
  have hpost : J posterior = ρ := by
    have hx : (((1 + t : ℝ) : ℂ) * posterior x) = (t : ℂ) := by
      change ((1 + t : ℝ) : ℂ) * ((t / (1 + t) : ℝ) : ℂ) = (t : ℂ)
      norm_cast
      field_simp
    change (0 : ℂ) • U + (1 : ℂ) • V + _ • B = _
    rw [hx, zero_smul, one_smul, zero_add]
    simp only [V, B, Complex.coe_smul, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    module
  let F := ofLinearMap J (by
    intro g hg a ha
    change 0 ≤ g _ * U a + g _ * V a + (((1 + t : ℝ) : ℂ) * g x) * B a
    exact add_nonneg (add_nonneg (mul_nonneg (hg _) (hU a ha))
      (mul_nonneg (hg _) (hV a ha)))
      (mul_nonneg (mul_nonneg (by exact_mod_cast (show 0 ≤ 1 + t by linarith)) (hg x))
        (hB a ha))) hunit hpost
  refine ⟨F, ?_⟩
  have hx : ((1 + t : ℝ) : ℂ) * overlapFunction t x = (t : ℂ) := by
    have he : t * (1 - t / (1 + t)) = t / (1 + t) := by field_simp; ring
    change ((1 + t : ℝ) : ℂ) * ((min (t / (1 + t))
      (t * (1 - t / (1 + t))) : ℝ) : ℂ) = (t : ℂ)
    rw [he, min_self]
    norm_cast
    field_simp
  change J (overlapFunction t) = η
  change ((min (0 : ℝ) (t * (1 - 0)) : ℝ) : ℂ) • U +
    ((min (1 : ℝ) (t * (1 - 1)) : ℝ) : ℂ) • V + _ • B = η
  rw [hx]
  simp only [sub_zero, mul_one, min_eq_left ht.le, sub_self, mul_zero,
    min_eq_right zero_le_one, Complex.ofReal_zero, zero_smul, zero_add,
    B, Complex.coe_smul, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]

private theorem sum_successor_sub {V : Type*} [AddCommGroup V]
    {m : ℕ} (F : Fin (m + 1) → V) :
    (∑ i : Fin m, (F i.succ - F i.castSucc)) = F (Fin.last m) - F 0 := by
  have hfront : (∑ i : Fin m, F i.castSucc) = (∑ i, F i) - F (Fin.last m) :=
    eq_sub_iff_add_eq.mpr (Fin.sum_univ_castSucc F).symm
  have htail : (∑ i : Fin m, F i.succ) = (∑ i, F i) - F 0 := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using (Fin.sum_univ_succ F).symm
  rw [Finset.sum_sub_distrib, hfront, htail]
  abel

private theorem summation_by_parts {m : ℕ}
    (w : Fin (m + 1) → ℝ) (d : Fin (m + 1) → StrongDual ℂ A) :
    (∑ i : Fin m, w i.succ • (d i.castSucc - d i.succ)) =
      (∑ i : Fin m, (w i.succ - w i.castSucc) • d i.castSucc) -
        (w (Fin.last m) • d (Fin.last m) - w 0 • d 0) := by
  have hterm (i : Fin m) :
      w i.succ • (d i.castSucc - d i.succ) =
        (w i.succ - w i.castSucc) • d i.castSucc -
          (w i.succ • d i.succ - w i.castSucc • d i.castSucc) := by module
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, sum_successor_sub (F := fun i => w i • d i)]

private theorem sum_clipped_differences {m : ℕ}
    (X : Fin (m + 1) → StrongDual ℂ A) (j : Fin (m + 1)) :
    (∑ i : Fin m, if i.castSucc < j then X i.succ - X i.castSucc else 0) =
      X j - X 0 := by
  have hterm (i : Fin m) :
      X (min i.succ j) - X (min i.castSucc j) =
        if i.castSucc < j then X i.succ - X i.castSucc else 0 := by
    by_cases hi : i.castSucc < j
    · have hs : i.succ ≤ j := by change i.val + 1 ≤ j.val; exact hi
      simp only [hi, ↓reduceIte, min_eq_left hi.le, min_eq_left hs]
    · have hp : j ≤ i.castSucc := le_of_not_gt hi
      have hs : j ≤ i.succ := hp.trans i.castSucc_le_succ
      simp only [hi, ↓reduceIte, min_eq_right hp, min_eq_right hs, sub_self]
  have h := sum_successor_sub (fun i => X (min i j))
  simp_rw [hterm] at h
  simpa only [min_eq_right (Fin.le_last j), min_eq_left (Fin.zero_le j)] using h

set_option maxHeartbeats 800000 in
/-- Every finite tuple with positive decreasing functional secants is realized
by one actual posterior family, with exact functional observations at all knots.
The blocks may vanish. This construction makes no choice of a normal state. -/
theorem finite_positive_secants_realized {ρ σ : StrongDual ℂ A}
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht0 : t 0 = 0) (ht : StrictMono t)
    (X d : Fin (m + 1) → StrongDual ℂ A) (hX0 : X 0 = 0)
    (hXρ : Below (X (Fin.last m)) ρ)
    (hdlast : d (Fin.last m) = 0)
    (hdanti : ∀ i j, i ≤ j → Below (d j) (d i)) (hdσ : Below (d 0) σ)
    (hstep : ∀ i : Fin m,
      (t i.succ - t i.castSucc) • d i.castSucc = X i.succ - X i.castSucc) :
    ∃ F : Family ρ σ, ∀ j, overlap F (t j) = X j := by
  classical
  let G : Fin m → StrongDual ℂ A := fun i => d i.castSucc - d i.succ
  have hG (i : Fin m) : Positive (G i) :=
    fun a ha => sub_nonneg.mpr (hdanti _ _ i.castSucc_le_succ a ha)
  have hGsum : ∑ i, G i = d 0 := by
    calc
      _ = -(∑ i : Fin m, (d i.succ - d i.castSucc)) := by
        rw [← Finset.sum_neg_distrib]; simp only [G, neg_sub]
      _ = d 0 := by rw [sum_successor_sub, hdlast, zero_sub, neg_neg]
  have hGmoment : ∑ i, t i.succ • G i = X (Fin.last m) := by
    rw [show (∑ i, t i.succ • G i) =
      (∑ i : Fin m, (t i.succ - t i.castSucc) • d i.castSucc) -
        (t (Fin.last m) • d (Fin.last m) - t 0 • d 0) from summation_by_parts t d]
    simp_rw [hstep]
    rw [hdlast, ht0, smul_zero, zero_smul, sub_self, sub_zero,
      sum_successor_sub, hX0, sub_zero]
  have hprofile (j : Fin (m + 1)) :
      (∑ i : Fin m, min (t j) (t i.succ) • G i) = X j := by
    have hnonneg : 0 ≤ t j := by simpa only [ht0] using ht.monotone (Fin.zero_le j)
    have hsum := summation_by_parts (fun i => min (t j) (t i)) d
    have hw0 : min (t j) (t 0) = 0 := by rw [ht0, min_eq_right hnonneg]
    have hterm (i : Fin m) :
        (min (t j) (t i.succ) - min (t j) (t i.castSucc)) • d i.castSucc =
          if i.castSucc < j then X i.succ - X i.castSucc else 0 := by
      by_cases hi : i.castSucc < j
      · have hs : i.succ ≤ j := by change i.val + 1 ≤ j.val; exact hi
        rw [min_eq_right (ht.monotone hs), min_eq_right (ht hi).le, hstep, if_pos hi]
      · have hp : j ≤ i.castSucc := le_of_not_gt hi
        have hs : j ≤ i.succ := hp.trans i.castSucc_le_succ
        rw [min_eq_left (ht.monotone hs), min_eq_left (ht.monotone hp),
          sub_self, zero_smul, if_neg hi]
    change (∑ i : Fin m, min (t j) (t i.succ) • (d i.castSucc - d i.succ)) = X j
    rw [hsum, hdlast, hw0, smul_zero, zero_smul, sub_self, sub_zero]
    simp_rw [hterm]
    rw [sum_clipped_differences, hX0, sub_zero]
  have hti (i : Fin m) : 0 < t i.succ := by
    have h := ht (show (0 : Fin (m + 1)) < i.succ by exact Fin.succ_pos i)
    rwa [ht0] at h
  let x (i : Fin m) : Interval := ⟨t i.succ / (1 + t i.succ),
    ⟨div_nonneg (hti i).le (by linarith [hti i]),
      (div_le_one (by linarith [hti i])).mpr (by linarith)⟩⟩
  let U := σ - d 0
  let V := ρ - X (Fin.last m)
  let J : C(Interval, ℂ) →ₗ[ℂ] StrongDual ℂ A :=
    { toFun g := g (endpoint 0 (by simp)) • U + g (endpoint 1 (by simp)) • V +
        ∑ i, (((1 + t i.succ : ℝ) : ℂ) * g (x i)) • G i
      map_add' g h := by
        simp only [ContinuousMap.add_apply, mul_add, add_smul, Finset.sum_add_distrib]; module
      map_smul' z g := by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply, id_eq, smul_eq_mul,
          smul_add, Finset.smul_sum, smul_smul]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        ring }
  have hunit : J 1 = ρ + σ := by
    change (1 : ℂ) • U + (1 : ℂ) • V +
      (∑ i, (((1 + t i.succ : ℝ) : ℂ) * 1) • G i) = _
    simp only [one_smul, mul_one, Complex.coe_smul, add_smul, one_smul,
      Finset.sum_add_distrib, hGsum, hGmoment, U, V]
    module
  have hpost : J posterior = ρ := by
    have hx (i : Fin m) : ((1 + t i.succ : ℝ) : ℂ) * posterior (x i) = (t i.succ : ℂ) := by
      change ((1 + t i.succ : ℝ) : ℂ) * ((t i.succ / (1 + t i.succ) : ℝ) : ℂ) = _
      norm_cast
      field_simp [(show 1 + t i.succ ≠ 0 by linarith [hti i])]
    change (0 : ℂ) • U + (1 : ℂ) • V + (∑ i, _ • G i) = _
    simp_rw [hx]
    simp only [zero_smul, one_smul, zero_add, Complex.coe_smul, hGmoment, V]
    module
  let F := ofLinearMap J (by
    intro g hg a ha
    change 0 ≤ g _ * U a + g _ * V a + (∑ i, _ • G i) a
    apply add_nonneg
    · exact add_nonneg (mul_nonneg (hg _) (sub_nonneg.mpr (hdσ a ha)))
        (mul_nonneg (hg _) (sub_nonneg.mpr (hXρ a ha)))
    · simp only [sum_apply, smul_apply, smul_eq_mul]
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (mul_nonneg (by exact_mod_cast (show 0 ≤ 1 + t i.succ by linarith [hti i]))
        (hg _)) (hG i a ha)) hunit hpost
  refine ⟨F, ?_⟩
  intro j
  have htj : 0 ≤ t j := by simpa only [ht0] using ht.monotone (Fin.zero_le j)
  have hx (i : Fin m) : ((1 + t i.succ : ℝ) : ℂ) * overlapFunction (t j) (x i) =
      ((min (t j) (t i.succ) : ℝ) : ℂ) := by
    have ha : 0 < 1 + t i.succ := by linarith [hti i]
    have he : t j * (1 - t i.succ / (1 + t i.succ)) = t j / (1 + t i.succ) := by
      field_simp; ring
    change ((1 + t i.succ : ℝ) : ℂ) * ((min (t i.succ / (1 + t i.succ))
      (t j * (1 - t i.succ / (1 + t i.succ))) : ℝ) : ℂ) = _
    rw [he, min_div_div_right ha.le]
    norm_cast
    rw [mul_div_cancel₀ _ ha.ne', min_comm]
  change J (overlapFunction (t j)) = X j
  change ((min (0 : ℝ) (t j * (1 - 0)) : ℝ) : ℂ) • U +
    ((min (1 : ℝ) (t j * (1 - 1)) : ℝ) : ℂ) • V + (∑ i, _ • G i) = X j
  simp_rw [hx]
  simpa only [sub_zero, mul_one, min_eq_left htj, sub_self, mul_zero,
    min_eq_right zero_le_one, Complex.ofReal_zero, zero_smul, zero_add, Complex.coe_smul]
    using hprofile j

section Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H)
    (ρ σ : StrongDual ℂ M.toStarSubalgebra)
    (hρ : Positive ρ) (hσ : Positive σ)
    (hρs : IsCoefficientSeries M ρ) (hσs : IsCoefficientSeries M σ)

include hρ hσ hρs hσs

/-- The mass maximum is over actual positive standard-predual overlaps, and
is achieved by an actual posterior family. This is not an optimizer premise. -/
theorem normal_overlap_maximum (t : ℝ) (ht : 0 < t) :
    ∃ F : Family ρ σ,
      IsCoefficientSeries M (overlap F t) ∧
      Positive (overlap F t) ∧ Below (overlap F t) ρ ∧
      Below (overlap F t) (t • σ) ∧
      ∀ η : StrongDual ℂ M.toStarSubalgebra,
        Positive η → Below η ρ → Below η (t • σ) →
        (η 1).re ≤ (overlap F t 1).re := by
  have hsum : ρ + σ ∈ coefficientSpace M :=
    (coefficientSpace M).add_mem (series_mem_coefficientSpace M hρs)
      (series_mem_coefficientSpace M hσs)
  obtain ⟨hc, hn, _, _, _⟩ := compact_normal_posterior_family M ρ σ hρ hσ
    (coefficientSpace_le_normalDual M hsum)
  letI : CompactSpace (Family ρ σ) := isCompact_iff_compactSpace.mp hc
  letI : Nonempty (Family ρ σ) := hn
  obtain ⟨F, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_overlap_mass ρ σ t).continuousOn
  obtain ⟨hp, hl, hr⟩ := overlap_feasible F t ht.le
  have hs : IsCoefficientSeries M (overlap F t) := by
    apply (mem_coefficientSpace_iff_series M _).mp
    exact coefficientSpace_hereditary M ρ (overlap F t)
      (series_mem_coefficientSpace M hρs) hρ (fun a ha => ⟨hp a ha, hl a ha⟩)
  refine ⟨F, hs, hp, hl, hr, ?_⟩
  intro η hp hl hr
  obtain ⟨G, hG⟩ := feasible_overlap_realized t ht hp hl hr
  have hh : (overlap G t 1).re ≤ (overlap F t 1).re := hmax (Set.mem_univ G)
  simpa only [hG] using hh

/-- Literal masses of standard-predual feasible overlaps. -/
def feasibleMasses (t : ℝ) : Set ℝ :=
  {z | ∃ η : StrongDual ℂ M.toStarSubalgebra,
    IsCoefficientSeries M η ∧ Positive η ∧ Below η ρ ∧ Below η (t • σ) ∧ (η 1).re = z}

/-- The actual normal-overlap supremum; attainment is a theorem. -/
def overlapValue (t : ℝ) : ℝ := sSup (feasibleMasses M ρ σ t)

private theorem overlap_series (F : Family ρ σ) (t : ℝ) (ht : 0 ≤ t) :
    IsCoefficientSeries M (overlap F t) := by
  obtain ⟨hp, hl, _⟩ := overlap_feasible F t ht
  apply (mem_coefficientSpace_iff_series M _).mp
  exact coefficientSpace_hereditary M ρ (overlap F t)
    (series_mem_coefficientSpace M hρs) hρ (fun a ha => ⟨hp a ha, hl a ha⟩)

theorem value_attained (t : ℝ) (ht : 0 < t) :
    ∃ F : Family ρ σ,
      (overlap F t 1).re = overlapValue M ρ σ t ∧
      ∀ η : StrongDual ℂ M.toStarSubalgebra,
        Positive η → Below η ρ → Below η (t • σ) → (η 1).re ≤ overlapValue M ρ σ t := by
  obtain ⟨F, hs, hp, hl, hr, hmax⟩ := normal_overlap_maximum M ρ σ hρ hσ hρs hσs t ht
  have hg : IsGreatest (feasibleMasses M ρ σ t) (overlap F t 1).re :=
    ⟨⟨overlap F t, hs, hp, hl, hr, rfl⟩, by
      rintro z ⟨η, _, hp, hl, hr, rfl⟩
      exact hmax η hp hl hr⟩
  have he : overlapValue M ρ σ t = (overlap F t 1).re := hg.csSup_eq
  exact ⟨F, he.symm, fun η hp hl hr => he ▸ hmax η hp hl hr⟩

/-- Actual optimal normal overlaps at every finite increasing tuple, with
positive antitone secants and the initial bound by sigma. Zero is only an
initial knot; the set K contains strictly positive thresholds. -/
def FiniteCompatibility (K : Set {t : ℝ // 0 < t}) : Prop :=
  ∀ (m : ℕ) (t : Fin (m + 1) → ℝ), t 0 = 0 → StrictMono t →
    (∀ i (hi : 0 < t i), (⟨t i, hi⟩ : {t : ℝ // 0 < t}) ∈ K) →
    ∃ X : Fin (m + 1) → StrongDual ℂ M.toStarSubalgebra,
      X 0 = 0 ∧
      (∀ j, IsCoefficientSeries M (X j) ∧ Positive (X j) ∧ Below (X j) ρ ∧
        Below (X j) (t j • σ)) ∧
      (∀ j, 0 < t j → (X j 1).re = overlapValue M ρ σ (t j)) ∧
      let D : Fin m → StrongDual ℂ M.toStarSubalgebra := fun i =>
        (t i.succ - t i.castSucc)⁻¹ • (X i.succ - X i.castSucc)
      (∀ i, Positive (D i) ∧ Below (D i) σ) ∧
      (∀ i j, i ≤ j → Below (D j) (D i))

private theorem simultaneous_implies_compatibility (K : Set {t : ℝ // 0 < t})
    (F : Family ρ σ)
    (hF : ∀ t ∈ K, (overlap F t 1).re = overlapValue M ρ σ t) :
    FiniteCompatibility M ρ σ K := by
  intro m t ht0 ht htK
  refine ⟨fun j => overlap F (t j), ?_, ?_, ?_, ?_, ?_⟩
  · have he : overlapFunction 0 = 0 := by
      ext x
      change ((min x.val (0 * (1 - x.val)) : ℝ) : ℂ) = 0
      simp only [zero_mul, min_eq_right x.property.1, Complex.ofReal_zero]
    change overlap F (t 0) = 0
    rw [ht0, overlap, he, map_zero]
  · intro j
    have hn : 0 ≤ t j := by simpa only [ht0] using ht.monotone (Fin.zero_le j)
    exact ⟨overlap_series M ρ σ hρ hσ hρs hσs F (t j) hn, overlap_feasible F (t j) hn⟩
  · intro j hj
    exact hF ⟨t j, hj⟩ (htK j hj)
  · intro i
    exact overlap_secant_bounds F _ _ (ht i.castSucc_lt_succ)
  · intro i j hij
    rcases hij.eq_or_lt with he | hlt
    · subst j
      exact fun _ _ => le_rfl
    · exact overlap_secant_antitone F _ _ _ _ (ht i.castSucc_lt_succ)
        (ht.monotone (show i.succ ≤ j.castSucc from hlt)) (ht j.castSucc_lt_succ)

private theorem compatible_knots_realized (K : Set {t : ℝ // 0 < t})
    (hK : FiniteCompatibility M ρ σ K)
    (m : ℕ) (t : Fin (m + 1) → ℝ) (ht0 : t 0 = 0) (ht : StrictMono t)
    (htK : ∀ i (hi : 0 < t i), (⟨t i, hi⟩ : {t : ℝ // 0 < t}) ∈ K) :
    ∃ F : Family ρ σ, ∀ j, 0 < t j → (overlap F (t j) 1).re = overlapValue M ρ σ (t j) := by
  classical
  obtain ⟨X, hX0, hX, hopt, hDb, hDa⟩ := hK m t ht0 ht htK
  let D : Fin m → StrongDual ℂ M.toStarSubalgebra := fun i =>
    (t i.succ - t i.castSucc)⁻¹ • (X i.succ - X i.castSucc)
  let d : Fin (m + 1) → StrongDual ℂ M.toStarSubalgebra := fun j =>
    if hj : j.val < m then D ⟨j.val, hj⟩ else 0
  have hdcast (i : Fin m) : d i.castSucc = D i := by simp only [d, Fin.val_castSucc, dif_pos i.isLt]
  have hdlast : d (Fin.last m) = 0 := by simp [d]
  have hdanti : ∀ i j, i ≤ j → Below (d j) (d i) := by
    intro i j hij a ha
    by_cases hj : j.val < m
    · have hi : i.val < m := lt_of_le_of_lt hij hj
      simp only [d, dif_pos hi, dif_pos hj]
      exact hDa _ _ hij a ha
    · rw [show d j = 0 by simp only [d, dif_neg hj]]
      by_cases hi : i.val < m
      · simpa [d, D, hi] using (hDb ⟨i.val, hi⟩).1 a ha
      · simp only [d, dif_neg hi, map_zero, le_refl]
  have hdσ : Below (d 0) σ := by
    by_cases hm : 0 < m
    · simpa [d, D, hm] using (hDb ⟨0, hm⟩).2
    · intro a ha
      simpa [d, hm] using hσ a ha
  have hstep (i : Fin m) :
      (t i.succ - t i.castSucc) • d i.castSucc = X i.succ - X i.castSucc := by
    rw [hdcast]
    dsimp only [D]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr (ht i.castSucc_lt_succ))), one_smul]
  obtain ⟨F, hF⟩ := finite_positive_secants_realized t ht0 ht X d hX0
    (hX (Fin.last m)).2.2.1 hdlast hdanti hdσ hstep
  exact ⟨F, fun j hj => by rw [hF]; exact hopt j hj⟩

private theorem compatible_finite_set_realized (K : Set {t : ℝ // 0 < t})
    (hK : FiniteCompatibility M ρ σ K) (S : Finset {t : ℝ // 0 < t})
    (hSK : ∀ t ∈ S, t ∈ K) :
    ∃ F : Family ρ σ, ∀ t ∈ S, (overlap F t 1).re = overlapValue M ρ σ t := by
  classical
  let P : Finset ℝ := S.image Subtype.val
  let T : Finset ℝ := insert 0 P
  have hzero : (0 : ℝ) ∉ P := by
    rintro hz
    obtain ⟨x, _, hx0⟩ : ∃ x : {t : ℝ // 0 < t}, x ∈ S ∧ (x : ℝ) = 0 :=
      Finset.mem_image.1 hz
    exact (ne_of_gt x.2) hx0
  have hcard : T.card = P.card + 1 := Finset.card_insert_of_notMem hzero
  let t : Fin (P.card + 1) ↪o ℝ := T.orderEmbOfFin hcard
  have htmem (i : Fin (P.card + 1)) : t i ∈ T := T.orderEmbOfFin_mem hcard i
  have htrange : Set.range t = (T : Set ℝ) := T.range_orderEmbOfFin hcard
  have hnonneg (i : Fin (P.card + 1)) : 0 ≤ t i := by
    have hiT : t i ∈ insert 0 (S.image Subtype.val) := by simpa [T, P] using htmem i
    rcases Finset.mem_insert.1 hiT with hi | hi
    · rw [hi]
    · obtain ⟨s, _, hsi⟩ : ∃ s : {t : ℝ // 0 < t}, s ∈ S ∧ (s : ℝ) = t i :=
        Finset.mem_image.1 hi
      exact hsi ▸ s.2.le
  have ht0 : t 0 = 0 := by
    have hz : (0 : ℝ) ∈ Set.range t := by rw [htrange]; exact Finset.mem_insert_self _ _
    obtain ⟨i, hi⟩ := hz
    exact le_antisymm (by simpa only [hi] using t.monotone (Fin.zero_le i)) (hnonneg 0)
  have htK (i : Fin (P.card + 1)) (hi : 0 < t i) :
      (⟨t i, hi⟩ : {t : ℝ // 0 < t}) ∈ K := by
    have hiT : t i ∈ insert 0 (S.image Subtype.val) := by simpa [T, P] using htmem i
    rcases Finset.mem_insert.1 hiT with hz | hp
    · exact False.elim ((ne_of_gt hi) hz)
    · obtain ⟨s, hs, hsi⟩ : ∃ s : {t : ℝ // 0 < t}, s ∈ S ∧ (s : ℝ) = t i :=
        Finset.mem_image.1 hp
      have he : (⟨t i, hi⟩ : {t : ℝ // 0 < t}) = s := Subtype.ext hsi.symm
      rw [he]
      exact hSK s hs
  obtain ⟨F, hF⟩ := compatible_knots_realized M ρ σ hρ hσ hρs hσs K hK
    P.card t ht0 t.strictMono htK
  refine ⟨F, ?_⟩
  intro s hs
  have hsrange : (s : ℝ) ∈ Set.range t := by
    rw [htrange]
    exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨s, hs, rfl⟩)
  obtain ⟨i, hi⟩ := hsrange
  simpa only [hi] using hF i (by rw [hi]; exact s.property)

/-- Finite positive-secant compatibility produces a single actual whole-L1
standard-predual test optimal at every threshold in an arbitrary set K.
There is no optimizer, compatible-family, countability or full-support premise.
This statement concerns overlap observations, and does not assert f-cost equality. -/
theorem finite_compatibility_simultaneous_realization
    (K : Set {t : ℝ // 0 < t}) (hK : FiniteCompatibility M ρ σ K) :
    ∃ F : Family ρ σ,
      (∀ t ∈ K, (overlap F t 1).re = overlapValue M ρ σ t) ∧
      ∃ Γ : (Interval →₁[scalarMeasure F] ℂ) →L[ℂ] StrongDual ℂ M.toStarSubalgebra,
        (∀ h, IsCoefficientSeries M (Γ h)) ∧
        (∀ h, (∀ᵐ x ∂scalarMeasure F, 0 ≤ h x) → Positive (Γ h)) ∧
        (∀ h, Γ h 1 = ∫ x, h x ∂scalarMeasure F) ∧
        Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ posterior) = ρ ∧
        Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ (1 - posterior)) = σ ∧
        (∀ t ∈ K, (Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ (overlapFunction t)) 1).re =
          overlapValue M ρ σ t) := by
  classical
  have hsum : ρ + σ ∈ coefficientSpace M :=
    (coefficientSpace M).add_mem (series_mem_coefficientSpace M hρs)
      (series_mem_coefficientSpace M hσs)
  obtain ⟨hc, _, _, _, _⟩ := compact_normal_posterior_family M ρ σ hρ hσ
    (coefficientSpace_le_normalDual M hsum)
  letI : CompactSpace (Family ρ σ) := isCompact_iff_compactSpace.mp hc
  let E (t : K) : Set (Family ρ σ) :=
    {F | (overlap F t.val 1).re = overlapValue M ρ σ t.val}
  have hclosed (t : K) : IsClosed (E t) :=
    isClosed_eq (continuous_overlap_mass ρ σ t.val) continuous_const
  have hfinite (T : Finset K) : (⋂ t ∈ T, E t).Nonempty := by
    let S : Finset {t : ℝ // 0 < t} := T.image Subtype.val
    have hSK : ∀ t ∈ S, t ∈ K := by
      intro t ht
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp ht
      exact s.property
    obtain ⟨F, hF⟩ := compatible_finite_set_realized M ρ σ hρ hσ hρs hσs K hK S hSK
    refine ⟨F, ?_⟩
    simp only [Set.mem_iInter]
    intro t ht
    exact hF t.val (Finset.mem_image.mpr ⟨t, ht, rfl⟩)
  obtain ⟨F, hF⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  have hopt : ∀ t ∈ K, (overlap F t 1).re = overlapValue M ρ σ t :=
    fun t ht => Set.mem_iInter.mp hF ⟨t, ht⟩
  obtain ⟨Γ, hagree, _, hp, hm, _, hl, hr, hΓE, _⟩ :=
    standard_posterior_realization M ρ σ hρ hσ hρs hσs F
  refine ⟨F, hopt, Γ, ?_, hp, hm, hl, hr, ?_⟩
  · intro h
    exact (mem_coefficientSpace_iff_series M _).mp (hΓE h)
  · intro t ht
    rw [hagree]
    exact hopt t ht

/-- Functional positive-secant finite compatibility is equivalent to a single
actual posterior family optimal on K. Optimizers and simultaneous realization
are derived, and the equivalence covers empty and uncountable K. -/
theorem finite_compatibility_iff_simultaneous (K : Set {t : ℝ // 0 < t}) :
    FiniteCompatibility M ρ σ K ↔
      ∃ F : Family ρ σ, ∀ t ∈ K, (overlap F t 1).re = overlapValue M ρ σ t := by
  constructor
  · intro hK
    obtain ⟨F, hF, _⟩ := finite_compatibility_simultaneous_realization M ρ σ hρ hσ hρs hσs K hK
    exact ⟨F, hF⟩
  · rintro ⟨F, hF⟩
    exact simultaneous_implies_compatibility M ρ σ hρ hσ hρs hσs K F hF

end Concrete

#print axioms feasible_overlap_realized
#print axioms finite_positive_secants_realized
#print axioms normal_overlap_maximum
#print axioms finite_compatibility_simultaneous_realization
#print axioms finite_compatibility_iff_simultaneous

end D5.S3.Quantum.Divergence.NormalOverlapCompatibility
