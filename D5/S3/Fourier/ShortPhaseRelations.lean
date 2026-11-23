/- GID: D5/S3/Fourier/ShortPhaseRelations
   generality: G
   mirror-B: D5/B/S3/Fourier/ShortPhaseRelations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Short incompatible relations control weighted deletion and common-time sine deficit. -/

import D5.S3.Fourier.WeightedIntegerRelations
import D5.S3.Fourier.WeightedPhaseRelationLattice

/-! A short incompatible relation forces a coordinate of large loss. Removing
all such coordinates leaves a compatible subset. -/

set_option autoImplicit false

open Set
open scoped BigOperators

namespace D5.S3.Fourier.ShortPhaseRelations

open D5.S3.Fourier.WeightedIntegerRelations (chord_prod_zpow)
open D5.S3.Fourier.WeightedPhaseRelationLattice (closure_real_phase_orbit)

noncomputable section

variable {J : Type*} [DecidableEq J]

/-- Every integer relation on the retained set has coefficient sum divisible by four. -/
def Compatible (s : Finset J) (g : J → ℝ) : Prop :=
  ∀ k : J → ℤ, (∑ j ∈ s, (k j : ℝ) * g j) = 0 → (4 : ℤ) ∣ ∑ j ∈ s, k j

/-- Each incompatible subset has an incompatible relation of length at most `H`. -/
def HasShortIncompatibleRelations (s : Finset J) (g : J → ℝ) (H : ℝ) : Prop :=
  ∀ u ⊆ s, ¬ Compatible u g →
    ∃ k : J → ℤ, (∑ j ∈ u, (k j : ℝ) * g j) = 0 ∧
      ¬ (4 : ℤ) ∣ (∑ j ∈ u, k j) ∧ (∑ j ∈ u, |(k j : ℝ)|) ≤ H

private def mass (s : Finset J) (w : J → ℝ) : ℝ := ∑ j ∈ s, w j

private def score (s : Finset J) (g w : J → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ s, w j * Real.sin (g j * t)

/-- One minus the normalized supremum of the common-time weighted sine score. -/
def weightedDeficit (s : Finset J) (g w : J → ℝ) (T : Set ℝ) : ℝ :=
  1 - sSup (score s g w '' T) / mass s w

/-- The least weight fraction removed to leave a compatible retained set. -/
def deletionFraction (s : Finset J) (g w : J → ℝ) : ℝ :=
  sInf {p | ∃ u ⊆ s, Compatible u g ∧ p = mass (s \ u) w / mass s w}

private def quarter : Circle := ⟨Complex.I, mem_sphere_zero_iff_norm.mpr Complex.norm_I⟩

omit [DecidableEq J] in
private theorem quarterChar (s : Finset J) (k : J → ℤ) :
    ((∏ j ∈ s, quarter ^ k j : Circle) : ℂ) = Complex.I ^ (∑ j ∈ s, k j) := by
  have h := congrArg Additive.toMul
    (map_sum (zmultiplesHom (Additive Circle) (Additive.ofMul quarter)) k s)
  rw [toMul_sum] at h
  change quarter ^ (∑ j ∈ s, k j) = ∏ j ∈ s, quarter ^ k j at h
  rw [← h, Circle.coe_zpow]
  rfl

private theorem fourth_root_gap_sq {k : ℤ} (h : ¬ (4 : ℤ) ∣ k) :
    2 ≤ ‖(1 : ℂ) - Complex.I ^ k‖ ^ 2 := by
  have hpos : 0 < k % 4 := by omega
  have hlt : k % 4 < 4 := by omega
  rw [Complex.I_zpow_eq_zpow_mod, Complex.sq_norm, Complex.normSq_apply]
  interval_cases (k % 4) <;>
    norm_num [Complex.sub_re, Complex.sub_im, show (2 : ℤ) = (2 : ℕ) from rfl,
      show (3 : ℤ) = (3 : ℕ) from rfl, zpow_natCast, Complex.I_sq, Complex.I_pow_three]

private theorem quarter_chord_sq (x : ℝ) :
    ‖(Circle.exp x : ℂ) - (quarter : ℂ)‖ ^ 2 = 2 * (1 - Real.sin x) := by
  have hn := Circle.normSq_coe (Circle.exp x)
  rw [Complex.normSq_apply] at hn
  change ‖(Circle.exp x : ℂ) - Complex.I‖ ^ 2 = _
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, sub_zero]
  have hi : (Circle.exp x : ℂ).im = Real.sin x := Complex.exp_ofReal_mul_I_im x
  rw [← hi]
  nlinarith only [hn]

omit [DecidableEq J] in
private theorem large_loss_of_short_relation (s : Finset J) (g : J → ℝ) (k : J → ℤ) (H t : ℝ)
    (hH : 1 ≤ H) (hr : ∑ j ∈ s, (k j : ℝ) * g j = 0)
    (hb : ¬ (4 : ℤ) ∣ ∑ j ∈ s, k j) (hk : ∑ j ∈ s, |(k j : ℝ)| ≤ H) :
    ∃ j ∈ s, k j ≠ 0 ∧ 1 / H ^ 2 ≤ 1 - Real.sin (g j * t) := by
  by_contra! h
  have hHp : 0 < H := by linarith
  have hsmall (j : J) (hj : j ∈ s) (hkj : k j ≠ 0) :
      ‖(Circle.exp (g j * t) : ℂ) - (quarter : ℂ)‖ < Real.sqrt 2 / H := by
    have hl := h j hj hkj
    have hh : 0 < H ^ 2 := by positivity
    have hmul := (lt_div_iff₀ hh).mp hl
    apply (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [quarter_chord_sq, div_pow, Real.sq_sqrt (by norm_num), lt_div_iff₀ hh]
    nlinarith only [hmul]
  have hex : ∃ j ∈ s, k j ≠ 0 := by
    by_contra! hz
    apply hb
    rw [Finset.sum_eq_zero hz]
    exact dvd_zero _
  have hs : (∑ j ∈ s, |(k j : ℝ)| *
      ‖(Circle.exp (g j * t) : ℂ) - (quarter : ℂ)‖) <
      ∑ j ∈ s, |(k j : ℝ)| * (Real.sqrt 2 / H) := by
    apply Finset.sum_lt_sum
    · intro j hj
      by_cases hz : k j = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hsmall j hj hz).le (abs_nonneg _)
    · obtain ⟨j, hj, hz⟩ := hex
      exact ⟨j, hj, mul_lt_mul_of_pos_left (hsmall j hj hz)
        (abs_pos.mpr (by exact_mod_cast hz))⟩
  have horbit : (∏ j ∈ s, Circle.exp (g j * t) ^ k j) = 1 := by
    simp_rw [← Circle.exp_intCast_mul, ← mul_assoc]
    have hsum : (∑ j ∈ s, (k j : ℝ) * g j * t) = 0 := by
      rw [← Finset.sum_mul, hr, zero_mul]
    have h := congrArg Additive.toMul
      (map_sum Circle.expHom (fun j => (k j : ℝ) * g j * t) s)
    rw [hsum, toMul_sum] at h
    exact h.symm.trans Circle.exp_zero
  have hc := chord_prod_zpow s (fun j => Circle.exp (g j * t)) (fun _ => quarter) k
  rw [horbit, Circle.coe_one, quarterChar] at hc
  rw [← Finset.sum_mul] at hs
  have hbound : (∑ j ∈ s, |(k j : ℝ)|) * (Real.sqrt 2 / H) ≤ Real.sqrt 2 := by
    calc
      _ ≤ H * (Real.sqrt 2 / H) := mul_le_mul_of_nonneg_right hk (by positivity)
      _ = _ := by field_simp
  have hlt := hc.trans_lt (hs.trans_le hbound)
  have hsq := (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hlt
  rw [Real.sq_sqrt (by norm_num)] at hsq
  exact (not_lt_of_ge (fourth_root_gap_sq hb)) hsq

omit [DecidableEq J] in
private theorem scoreBound (s : Finset J) (g w : J → ℝ) (t : ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) :
    -mass s w ≤ score s g w t ∧ score s g w t ≤ mass s w := by
  constructor
  · rw [mass, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [mul_neg, mul_one] using
      mul_le_mul_of_nonneg_left (Real.neg_one_le_sin (g j * t)) (hw j hj)
  · apply Finset.sum_le_sum
    intro j hj
    exact mul_le_of_le_one_right (hw j hj) (Real.sin_le_one _)

omit [DecidableEq J] in
private theorem scoreBdd (s : Finset J) (g w : J → ℝ) (T : Set ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) : BddAbove (score s g w '' T) :=
  ⟨mass s w, by rintro _ ⟨t, _, rfl⟩; exact (scoreBound s g w t hw).2⟩

omit [DecidableEq J] in
private theorem emptyCompatible (g : J → ℝ) : Compatible ∅ g := by
  intro k _
  simp

private theorem deleteNonempty (s : Finset J) (g w : J → ℝ) :
    {p | ∃ u ⊆ s, Compatible u g ∧ p = mass (s \ u) w / mass s w}.Nonempty :=
  ⟨_, ∅, Finset.empty_subset _, emptyCompatible g, rfl⟩

private theorem deleteBdd (s : Finset J) (g w : J → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) :
    BddBelow {p | ∃ u ⊆ s, Compatible u g ∧ p = mass (s \ u) w / mass s w} := by
  refine ⟨0, ?_⟩
  rintro _ ⟨u, _, _, rfl⟩
  exact div_nonneg (Finset.sum_nonneg fun j hj => hw j (Finset.mem_sdiff.mp hj).1)
    (Finset.sum_nonneg hw)

private theorem scoreSplit {s u : Finset J} (hu : u ⊆ s) (g w : J → ℝ) (t : ℝ) :
    score (s \ u) g w t + score u g w t = score s g w t :=
  Finset.sum_sdiff hu

private theorem massSplit {s u : Finset J} (hu : u ⊆ s) (w : J → ℝ) :
    mass (s \ u) w + mass u w = mass s w :=
  Finset.sum_sdiff hu

omit [DecidableEq J] in
private theorem compatibleQuarter {u : Finset J} {g : J → ℝ} (hc : Compatible u g)
    (a : ℝ) :
    (fun _ : u => quarter) ∈
      closure ((fun (t : ℝ) (j : u) => Circle.exp (g j * t)) '' Ici a) := by
  classical
  have horbit := closure_real_phase_orbit (fun j : u => g j)
  rw [(horbit.2 a).1, horbit.1]
  intro k hk
  let extend (j : J) : ℤ := if hj : j ∈ u then k ⟨j, hj⟩ else 0
  have hrel : ∑ j ∈ u, (extend j : ℝ) * g j = 0 := by
    rw [← Finset.sum_coe_sort]
    simpa only [extend, dite_eq_left (Subtype.property _)] using hk
  have hd := hc extend hrel
  rw [← Finset.sum_coe_sort] at hd
  have hsum : (4 : ℤ) ∣ ∑ j : u, k j := by
    simpa only [extend, dite_eq_left (Subtype.property _)] using hd
  apply Subtype.coe_injective
  change ((∏ j : u, quarter ^ k j : Circle) : ℂ) = ((1 : Circle) : ℂ)
  rw [Circle.coe_one, quarterChar, Complex.I_zpow_eq_zpow_mod,
    Int.emod_eq_zero_of_dvd hsum, zpow_zero]

private theorem compatibleScore_le {s u : Finset J} (hu : u ⊆ s) {g w : J → ℝ}
    (hc : Compatible u g) {T : Set ℝ} {a : ℝ} (htail : Ici a ⊆ T)
    (hw : ∀ j ∈ s, 0 ≤ w j) :
    mass u w ≤ sSup (score s g w '' T) + mass (s \ u) w := by
  let f (p : u → Circle) := ∑ j : u, w j * (p j : ℂ).im
  have hf : Continuous f := by
    exact continuous_finsetSum _ fun j _ => continuous_const.mul
      (Complex.continuous_im.comp (continuous_subtype_val.comp (continuous_apply j)))
  have hsub : (fun (t : ℝ) (j : u) => Circle.exp (g j * t)) '' Ici a ⊆
      {p | f p ≤ sSup (score s g w '' T) + mass (s \ u) w} := by
    rintro _ ⟨t, ht, rfl⟩
    have htot : score s g w t ≤ sSup (score s g w '' T) :=
      le_csSup (scoreBdd s g w T hw) ⟨t, htail ht, rfl⟩
    have hfscore : f (fun j => Circle.exp (g j * t)) = score u g w t := by
      simp only [f, Circle.coe_exp, Complex.exp_ofReal_mul_I_im, score]
      exact Finset.sum_coe_sort u (fun j => w j * Real.sin (g j * t))
    change f _ ≤ _
    rw [hfscore]
    have hrest := (scoreBound (s \ u) g w t fun j hj => hw j (Finset.mem_sdiff.mp hj).1).1
    linarith only [htot, hrest, scoreSplit hu g w t]
  have hval := closure_minimal hsub (isClosed_le hf continuous_const) (compatibleQuarter hc a)
  change f (fun _ => quarter) ≤ _ at hval
  simpa only [f, quarter, Complex.I_im, mul_one, Finset.sum_coe_sort, mass] using hval

/-- Weighted compatible deletion controls the common-time deficit over every upper ray. -/
theorem weighted_deletion_bounds (s : Finset J) (g w : J → ℝ) (H : ℝ) (T : Set ℝ)
    (hs : s.Nonempty) (hw : ∀ j ∈ s, 0 < w j) (hH : 1 ≤ H)
    (hshort : HasShortIncompatibleRelations s g H) (htail : ∃ a, Ici a ⊆ T) :
    let P := deletionFraction s g w
    let D := weightedDeficit s g w T
    P / (2 * H ^ 2) ≤ D ∧ D ≤ 2 * P ∧ P / H ^ 2 ≤ D := by
  dsimp only
  classical
  obtain ⟨a, htail⟩ := htail
  let W := mass s w
  let V := sSup (score s g w '' T)
  let c := H ^ 2
  have hW : 0 < W := Finset.sum_pos hw hs
  have hc : 0 < c := by dsimp [c]; positivity
  have hw₀ : ∀ j ∈ s, 0 ≤ w j := fun j hj => (hw j hj).le
  have hlower : deletionFraction s g w / c ≤ 1 - V / W := by
    have hpoint (t : ℝ) : deletionFraction s g w / c * W ≤ W - score s g w t := by
      let u := s.filter fun j => 1 - Real.sin (g j * t) < 1 / c
      have hu : u ⊆ s := Finset.filter_subset _ _
      have hcompat : Compatible u g := by
        by_contra hbad
        obtain ⟨k, hk, hb, hl⟩ := hshort u hu hbad
        obtain ⟨j, hj, _, hlarge⟩ := large_loss_of_short_relation u g k H t hH hk hb hl
        exact (not_lt_of_ge hlarge) (Finset.mem_filter.mp hj).2
      have hp : deletionFraction s g w ≤ mass (s \ u) w / W :=
        csInf_le (deleteBdd s g w hw₀) ⟨u, hu, hcompat, rfl⟩
      have hthreshold : mass (s \ u) w / c ≤ W - score s g w t := by
        rw [mass, Finset.sum_div, show W = ∑ j ∈ s, w j from rfl, score,
          ← Finset.sum_sub_distrib]
        refine (Finset.sum_le_sum (g := fun j => w j - w j * Real.sin (g j * t)) ?_).trans
          (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_)
        · intro j hj
          have hj' := Finset.mem_sdiff.mp hj
          have hsin : 1 / c ≤ 1 - Real.sin (g j * t) :=
            le_of_not_gt fun h => hj'.2 (Finset.mem_filter.mpr ⟨hj'.1, h⟩)
          have hh := mul_le_mul_of_nonneg_left hsin (hw₀ j hj'.1)
          simpa only [mul_one_div, mul_sub, mul_one] using hh
        · intro j hj _
          exact sub_nonneg.mpr (mul_le_of_le_one_right (hw₀ j hj) (Real.sin_le_one _))
      calc
        deletionFraction s g w / c * W ≤ mass (s \ u) w / W / c * W :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hp hc.le) hW.le
        _ = mass (s \ u) w / c := by field_simp
        _ ≤ _ := hthreshold
    have hV : V ≤ W - deletionFraction s g w / c * W := by
      refine csSup_le (image_nonempty.mpr ⟨a, htail (mem_Ici.mpr le_rfl)⟩) ?_
      rintro _ ⟨t, _, rfl⟩
      linarith only [hpoint t]
    rw [le_sub_comm, div_le_iff₀ hW, sub_mul, one_mul]
    exact hV
  have hupper : 1 - V / W ≤ 2 * deletionFraction s g w := by
    suffices (1 - V / W) / 2 ≤ deletionFraction s g w by linarith
    apply le_csInf (deleteNonempty s g w)
    rintro _ ⟨u, hu, hcompat, rfl⟩
    have hgood := compatibleScore_le hu hcompat htail hw₀
    change mass u w ≤ V + mass (s \ u) w at hgood
    have hpart := massSplit hu w
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    calc
      1 - V / W = (W - V) / W := by rw [sub_div, div_self hW.ne']
      _ ≤ (2 * mass (s \ u) w) / W :=
        div_le_div_of_nonneg_right (by linarith only [hgood, hpart]) hW.le
      _ = mass (s \ u) w / W * 2 := by ring
  have hP : 0 ≤ deletionFraction s g w := by
    apply le_csInf (deleteNonempty s g w)
    rintro _ ⟨u, _, _, rfl⟩
    exact div_nonneg (Finset.sum_nonneg fun j hj => hw₀ j (Finset.mem_sdiff.mp hj).1) hW.le
  refine ⟨(div_le_div_of_nonneg_left hP hc ?_).trans hlower, hupper, hlower⟩
  dsimp [c]
  nlinarith only [sq_nonneg H]

/-- The consecutive real frequencies `n` and `n + 1`. -/
def pairFreq (n : ℕ) : Fin 2 → ℝ := ![(n : ℝ), (n : ℝ) + 1]

private def pairRelation (n : ℕ) : Fin 2 → ℤ := ![(n : ℤ) + 1, -(n : ℤ)]

private theorem pairRelation_dot (n : ℕ) :
    ∑ j : Fin 2, (pairRelation n j : ℝ) * pairFreq n j = 0 := by
  simp [Fin.sum_univ_two, pairRelation, pairFreq]
  ring

private theorem pairRelation_sum (n : ℕ) : ∑ j : Fin 2, pairRelation n j = 1 := by
  simp [Fin.sum_univ_two, pairRelation]

private theorem pairRelation_length (n : ℕ) :
    ∑ j : Fin 2, |(pairRelation n j : ℝ)| = 2 * (n : ℝ) + 1 := by
  simp [Fin.sum_univ_two, pairRelation, abs_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity),
    abs_of_nonneg (show 0 ≤ (n : ℝ) by positivity)]
  ring

private theorem pairFullBad (n : ℕ) : ¬ Compatible Finset.univ (pairFreq n) := by
  intro hc
  have h := hc (pairRelation n) (pairRelation_dot n)
  rw [pairRelation_sum] at h
  norm_num at h

omit [DecidableEq J] in
private theorem singletonCompatible (j : J) {g : J → ℝ} (hg : g j ≠ 0) :
    Compatible {j} g := by
  intro k hk
  simp only [Finset.sum_singleton] at hk ⊢
  have hzero : (k j : ℝ) = 0 := (mul_eq_zero.mp hk).resolve_right hg
  have hk₀ : k j = 0 := by exact_mod_cast hzero
  simp [hk₀]

private theorem pairFreq_ne_zero (n : ℕ) (hn : 0 < n) (j : Fin 2) : pairFreq n j ≠ 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  fin_cases j
  · simpa [pairFreq] using hn'.ne'
  · change (n : ℝ) + 1 ≠ 0
    positivity

private theorem pairProperGood (n : ℕ) (hn : 0 < n) (u : Finset (Fin 2))
    (hu : u ≠ Finset.univ) : Compatible u (pairFreq n) := by
  by_cases h0 : (0 : Fin 2) ∈ u
  · have h1 : (1 : Fin 2) ∉ u := by
      intro h1
      apply hu
      ext j
      fin_cases j <;> simp_all
    have heq : u = {0} := by
      ext j
      fin_cases j <;> simp_all
    rw [heq]
    exact singletonCompatible 0 (pairFreq_ne_zero n hn 0)
  · by_cases h1 : (1 : Fin 2) ∈ u
    · have heq : u = {1} := by
        ext j
        fin_cases j <;> simp_all
      rw [heq]
      exact singletonCompatible 1 (pairFreq_ne_zero n hn 1)
    · have heq : u = ∅ := by
        ext j
        fin_cases j <;> simp_all
      rw [heq]
      exact emptyCompatible _

private theorem pairShort (n : ℕ) (hn : 0 < n) :
    HasShortIncompatibleRelations Finset.univ (pairFreq n) (2 * (n : ℝ) + 1) := by
  intro u _ hu
  have heq : u = Finset.univ := by
    by_contra h
    exact hu (pairProperGood n hn u h)
  subst u
  refine ⟨pairRelation n, pairRelation_dot n, ?_, (pairRelation_length n).le⟩
  rw [pairRelation_sum]
  norm_num

private theorem pairDeletion (n : ℕ) (hn : 0 < n) (w : ℝ) (hw : 0 < w) :
    deletionFraction Finset.univ (pairFreq n) (fun _ => w) = 1 / 2 := by
  classical
  have hu : ({0} : Finset (Fin 2)) ⊆ Finset.univ := Finset.subset_univ _
  have hm : mass (Finset.univ : Finset (Fin 2)) (fun _ => w) = 2 * w := by
    simp [mass, two_mul]
  apply le_antisymm
  · have hpart := massSplit hu (fun _ => w)
    rw [hm] at hpart
    have hsingle : mass ({0} : Finset (Fin 2)) (fun _ => w) = w := by simp [mass]
    have hdel : mass ((Finset.univ : Finset (Fin 2)) \ {0}) (fun _ => w) = w := by
      linarith only [hpart, hsingle]
    have hratio : mass ((Finset.univ : Finset (Fin 2)) \ {0}) (fun _ => w) /
        mass (Finset.univ : Finset (Fin 2)) (fun _ => w) = 1 / 2 := by
      rw [hm, hdel]
      field_simp
    rw [← hratio]
    exact csInf_le (deleteBdd _ _ _ (fun _ _ => hw.le))
      ⟨{0}, hu, singletonCompatible 0 (pairFreq_ne_zero n hn 0), rfl⟩
  · apply le_csInf (deleteNonempty _ _ _)
    rintro _ ⟨u, _, hcomp, rfl⟩
    have hnfull : u ≠ Finset.univ := by
      intro h
      exact pairFullBad n (h ▸ hcomp)
    have hnonempty : ((Finset.univ : Finset (Fin 2)) \ u).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro h
      exact hnfull (Finset.eq_univ_of_forall fun j => h (Finset.mem_univ j))
    obtain ⟨j, hj⟩ := hnonempty
    have hmass := Finset.single_le_sum (f := fun _ => w) (fun _ _ => hw.le) hj
    rw [hm, le_div_iff₀ (by positivity)]
    change w ≤ mass (Finset.univ \ u) (fun _ => w) at hmass
    linarith only [hmass]

private theorem pairUpper (n : ℕ) (w : ℝ) (hw : 0 < w) {T : Set ℝ}
    (htail : ∃ a, Ici a ⊆ T) :
    weightedDeficit Finset.univ (pairFreq n) (fun _ => w) T ≤
      (Real.pi ^ 2 / 8) / (2 * (n : ℝ) + 1) ^ 2 := by
  obtain ⟨a, htail⟩ := htail
  have hH : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  let t₀ := Real.pi / (2 * (n : ℝ) + 1)
  let x := t₀ / 2
  obtain ⟨m, hm⟩ := exists_nat_ge ((a - t₀) / (2 * Real.pi))
  let t := t₀ + (m : ℝ) * (2 * Real.pi)
  have ht : t ∈ T := htail (mem_Ici.mpr (by
    have h := (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hm
    dsimp [t]
    linarith only [h]))
  have hlo : (n : ℝ) * t₀ = Real.pi / 2 - x := by
    dsimp [t₀, x]
    field_simp
    ring
  have hhi : ((n : ℝ) + 1) * t₀ = Real.pi / 2 + x := by
    dsimp [t₀, x]
    field_simp
    ring
  have hperiod (k : ℕ) : Real.sin ((k : ℝ) * t) = Real.sin ((k : ℝ) * t₀) := by
    rw [show (k : ℝ) * t = (k : ℝ) * t₀ + ((k * m : ℕ) : ℝ) * (2 * Real.pi) by
      push_cast
      dsimp [t]
      ring, Real.sin_add_nat_mul_two_pi]
  have hscore : score Finset.univ (pairFreq n) (fun _ => w) t = 2 * w * Real.cos x := by
    have hperiod' : Real.sin (((n : ℝ) + 1) * t) =
        Real.sin (((n : ℝ) + 1) * t₀) := by simpa only [Nat.cast_succ] using hperiod (n + 1)
    simp [score, Fin.sum_univ_two, pairFreq, hperiod n, hperiod', hlo, hhi,
      Real.sin_pi_div_two_sub, add_comm (Real.pi / 2) x, Real.sin_add_pi_div_two]
    ring
  have hmass : mass (Finset.univ : Finset (Fin 2)) (fun _ => w) = 2 * w := by
    simp [mass, two_mul]
  have hsup := le_csSup (scoreBdd Finset.univ (pairFreq n) (fun _ => w) T (fun _ _ => hw.le))
    (mem_image_of_mem (score Finset.univ (pairFreq n) (fun _ => w)) ht)
  unfold weightedDeficit
  rw [hmass, hscore] at *
  calc
    _ ≤ 1 - Real.cos x := by
      have h := (le_div_iff₀ (by positivity : 0 < 2 * w)).mpr
        (show Real.cos x * (2 * w) ≤ _ by simpa only [mul_comm (Real.cos x)] using hsup)
      linarith only [h]
    _ ≤ x ^ 2 / 2 := by linarith only [Real.one_sub_sq_div_two_le_cos (x := x)]
    _ = _ := by dsimp [x, t₀]; field_simp; ring

/-- Consecutive positive integer frequencies exhibit quadratic separation. -/
theorem consecutive_pair_separation (n : ℕ) (w : ℝ) (hn : 0 < n) (hw : 0 < w)
    (T : Set ℝ) (htail : ∃ a, Ici a ⊆ T) :
    let H := 2 * (n : ℝ) + 1
    let g := pairFreq n
    let D := weightedDeficit Finset.univ g (fun _ => w) T
    deletionFraction Finset.univ g (fun _ => w) = 1 / 2 ∧
      HasShortIncompatibleRelations Finset.univ g H ∧
      1 / (4 * H ^ 2) ≤ D ∧ D ≤ (Real.pi ^ 2 / 8) / H ^ 2 ∧
      1 / (2 * H ^ 2) ≤ D := by
  dsimp only
  have hH : 1 ≤ 2 * (n : ℝ) + 1 := by linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hs := pairShort n hn
  have hp := pairDeletion n hn w hw
  have hd := weighted_deletion_bounds Finset.univ (pairFreq n) (fun _ => w)
    (2 * (n : ℝ) + 1) T Finset.univ_nonempty (fun _ _ => hw) hH hs htail
  rw [hp] at hd
  refine ⟨hp, hs, ?_, pairUpper n w hw htail, ?_⟩
  · convert hd.1 using 1
    rw [div_div]
    congr 1
    ring
  · simpa only [div_div] using hd.2.2

end

end D5.S3.Fourier.ShortPhaseRelations
