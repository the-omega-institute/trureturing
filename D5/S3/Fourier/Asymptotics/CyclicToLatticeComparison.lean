/- GID: D5/S3/Fourier/Asymptotics/CyclicToLatticeComparison
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicToLatticeComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative comparison of the two-mode cyclic and lattice squared-mass minima. -/

import D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
import D5.S3.Fourier.Concentration.AggregateCosineBalance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Order.Compact

/-! A lattice optimizer embeds in a sufficiently large cyclic group. A dual polynomial
using both cosine moments gives the reverse comparison up to an explicit finite-size error. -/

open Finset
open D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation

noncomputable section

namespace D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison

set_option autoImplicit false

/-- The full cosine moment of the weights on residues at integral frequency `r`. -/
def cosineMoment {q : ℕ} [NeZero q] (r : ℕ) (v : ZMod q → ℝ) : ℝ :=
  ∑ i : ZMod q, v i * D5.S3.Fourier.Concentration.AggregateCosineBalance.mode i (r : ℤ)

/-- Probability weights with both the first and second cosine moments at least `a`. -/
def feasible (q : ℕ) [NeZero q] (a : ℝ) : Set (ZMod q → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = 1 ∧ a ≤ cosineMoment 1 v ∧ a ≤ cosineMoment 2 v}

/-- Squared mass on the cyclic group. -/
def energy {q : ℕ} [NeZero q] (v : ZMod q → ℝ) : ℝ :=
  ∑ i, v i ^ 2

/-- The angle determined by the centered integer representative of a residue. -/
def centeredAngle {q : ℕ} (i : ZMod q) : ℝ :=
  2 * Real.pi * (i.valMinAbs : ℝ) / q

/-- Centering representatives preserves every integral cosine moment. -/
theorem cosineMoment_eq_centered {q : ℕ} [NeZero q] (r : ℕ) (v : ZMod q → ℝ) :
    let readout := Real.cos
    cosineMoment r v = ∑ i : ZMod q, v i * readout ((r : ℝ) * centeredAngle i) := by
  dsimp only
  unfold cosineMoment
  apply sum_congr rfl
  intro i _
  congr 1
  rw [D5.S3.Fourier.Concentration.AggregateCosineBalance.mode, Int.cast_natCast]
  rw [show 2 * Real.pi * (r : ℝ) * (i.val : ℝ) / q =
    (r : ℝ) * (2 * Real.pi * (i.val : ℝ) / q) by ring]
  have he := congrArg (fun y : ℤ => (y : ℝ)) (ZMod.val_eq_ite_valMinAbs i)
  split at he
  · push_cast at he
    rw [he]
    simp [centeredAngle]
  · push_cast at he
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
    rw [he, show (r : ℝ) * (2 * Real.pi * ((i.valMinAbs : ℝ) + q) / q) =
      (r : ℝ) * centeredAngle i + (r : ℝ) * (2 * Real.pi) by
        unfold centeredAngle
        field_simp, Real.cos_add_nat_mul_two_pi]

theorem abs_centeredAngle_le_pi {q : ℕ} [NeZero q] (i : ZMod q) :
    |centeredAngle i| ≤ Real.pi := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hl : -(q : ℝ) < (i.valMinAbs : ℝ) * 2 := by
    exact_mod_cast i.valMinAbs_mem_Ioc.1
  have hu : (i.valMinAbs : ℝ) * 2 ≤ q := by
    exact_mod_cast i.valMinAbs_mem_Ioc.2
  rw [abs_le, centeredAngle, le_div_iff₀ hq, div_le_iff₀ hq]
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left hl.le Real.pi_pos.le]
  · nlinarith only [mul_le_mul_of_nonneg_left hu Real.pi_pos.le]

private theorem sq_mul_cos_le_sin_sq {x : ℝ} (hx : |x| ≤ Real.pi) :
    x ^ 2 * Real.cos x ≤ Real.sin x ^ 2 := by
  have nonneg_case (y : ℝ) (hy : 0 ≤ y) (hyp : y ≤ Real.pi) :
      y ^ 2 * Real.cos y ≤ Real.sin y ^ 2 := by
    by_cases hc : Real.cos y ≤ 0
    · exact (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) hc).trans (sq_nonneg _)
    have hylt : y < Real.pi / 2 := by
      by_contra! h
      exact hc (Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith [Real.pi_pos]))
    have hhpos : 0 < Real.cos (y / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
    have htan := Real.le_tan (show 0 ≤ y / 2 by positivity)
      (show y / 2 < Real.pi / 2 by linarith [Real.pi_pos])
    rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hhpos] at htan
    have hsin : y * Real.cos (y / 2) ^ 2 ≤ Real.sin y := by
      calc
        _ = 2 * Real.cos (y / 2) * ((y / 2) * Real.cos (y / 2)) := by ring
        _ ≤ 2 * Real.cos (y / 2) * Real.sin (y / 2) :=
          mul_le_mul_of_nonneg_left htan (by positivity)
        _ = _ := by
          conv_rhs => rw [show y = 2 * (y / 2) by ring, Real.sin_two_mul]
          ring
    have hcos : Real.cos y ≤ (Real.cos (y / 2) ^ 2) ^ 2 := by
      conv_lhs => rw [show y = 2 * (y / 2) by ring, Real.cos_two_mul]
      nlinarith only [sq_nonneg (Real.cos (y / 2) ^ 2 - 1)]
    have hl : 0 ≤ y * Real.cos (y / 2) ^ 2 := by positivity
    calc
      _ ≤ y ^ 2 * (Real.cos (y / 2) ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hcos (sq_nonneg _)
      _ = (y * Real.cos (y / 2) ^ 2) ^ 2 := by ring
      _ ≤ _ := (sq_le_sq₀ hl (hl.trans hsin)).mpr hsin
  by_cases h : 0 ≤ x
  · exact nonneg_case x h ((abs_le.mp hx).2)
  · simpa [Real.cos_neg, Real.sin_neg] using
      nonneg_case (-x) (by linarith) (by linarith [(abs_le.mp hx).1])

private def dualPolynomial {q : ℕ} (t Z : ℝ) (i : ZMod q) : ℝ :=
  (t * Real.cos (centeredAngle i) -
    ((q : ℝ) / (2 * Real.pi) * Real.sin (centeredAngle i)) ^ 2) / Z

-- The sign case includes the half-turn when the modulus is even.
private theorem dual_positive_part_le {q : ℕ} [NeZero q] {m t Z : ℝ} {n : ℕ}
    {w : ℤ → ℝ} (A : Activation m n t Z w) (i : ZMod q) :
    max 0 (dualPolynomial t Z i) ≤ w i.valMinAbs := by
  let θ := centeredAngle i
  let s := (q : ℝ) / (2 * Real.pi)
  have ht : 0 ≤ t := (sq_nonneg _).trans A.radius_lower
  have hscaled : ((i.valMinAbs : ℝ) ^ 2) * Real.cos θ ≤ (s * Real.sin θ) ^ 2 := by
    have he : s * θ = (i.valMinAbs : ℝ) := by
      have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
      dsimp [s, θ, centeredAngle]
      field_simp [Real.pi_ne_zero]
    calc
      _ = s ^ 2 * (θ ^ 2 * Real.cos θ) := by rw [← he]; ring
      _ ≤ s ^ 2 * Real.sin θ ^ 2 :=
        mul_le_mul_of_nonneg_left (sq_mul_cos_le_sin_sq (abs_centeredAngle_le_pi i)) (sq_nonneg _)
      _ = _ := by ring
  apply max_le (A.nonneg _)
  rw [A.law, dualPolynomial]
  apply (div_le_div_iff_of_pos_right A.normalizer_pos).mpr
  change t * Real.cos θ - (s * Real.sin θ) ^ 2 ≤ max 0 (t - (i.valMinAbs : ℝ) ^ 2)
  by_cases hc : 0 ≤ Real.cos θ
  · calc
      _ ≤ (t - (i.valMinAbs : ℝ) ^ 2) * Real.cos θ := by linarith only [hscaled]
      _ ≤ max 0 (t - (i.valMinAbs : ℝ) ^ 2) * Real.cos θ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hc
      _ ≤ _ := mul_le_of_le_one_right (le_max_left _ _) (Real.cos_le_one _)
  · exact (sub_nonpos.mpr ((mul_nonpos_of_nonneg_of_nonpos ht (le_of_not_ge hc)).trans
      (sq_nonneg _))).trans (le_max_left _ _)

/-- The support radius drops by one at the lower activation threshold. -/
def latticeSupportRadius (n : ℕ) (m : ℝ) : ℕ :=
  if m = ((n : ℝ) ^ 2 - 1) / 5 then n - 1 else n

theorem activation_zero_outside {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (A : Activation m n t Z w) {k : ℤ}
    (hk : k ∉ Icc (-(latticeSupportRadius n m : ℤ)) (latticeSupportRadius n m : ℤ)) :
    w k = 0 := by
  by_contra h
  have hs : k ∈ Function.support w := h
  rw [A.support] at hs
  by_cases hm : m = ((n : ℝ) ^ 2 - 1) / 5
  · rw [ite_eq_left (A.lower_endpoint.mp hm)] at hs
    exact hk (by simpa [latticeSupportRadius, hm] using hs)
  · rw [ite_eq_right (fun ht => hm (A.lower_endpoint.mpr ht))] at hs
    exact hk (by simpa [latticeSupportRadius, hm] using hs)

theorem sum_centered_eq_tsum {q n : ℕ} [NeZero q] (hq : 2 * n < q) (f : ℤ → ℝ)
    (hf : ∀ k, k ∉ Icc (-(n : ℤ)) (n : ℤ) → f k = 0) :
    (∑ i : ZMod q, f i.valMinAbs) = ∑' k : ℤ, f k := by
  let reps := (univ : Finset (ZMod q)).map ⟨ZMod.valMinAbs, ZMod.injective_valMinAbs⟩
  have hzero (k : ℤ) (hk : k ∉ reps) : f k = 0 := by
    apply hf
    intro hin
    apply hk
    have hi := Finset.mem_Icc.mp hin
    have hq' : (2 : ℤ) * (n : ℤ) < q := by exact_mod_cast hq
    have hrep : (k : ZMod q).valMinAbs = k :=
      (ZMod.valMinAbs_spec _ _).mpr ⟨rfl, by constructor <;> omega⟩
    exact Finset.mem_map.mpr ⟨(k : ZMod q), mem_univ _, hrep⟩
  rw [(hasSum_sum_of_ne_finset_zero hzero).tsum_eq, show reps =
    univ.map (⟨ZMod.valMinAbs, ZMod.injective_valMinAbs⟩ : ZMod q ↪ ℤ) from rfl, sum_map]
  rfl

theorem lattice_energy_eq {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (A : Activation m n t Z w) : (∑' k : ℤ, w k ^ 2) = (t - m) / Z := by
  have hp (k : ℤ) : w k ^ 2 = (t * w k - (k : ℝ) ^ 2 * w k) / Z := by
    rw [A.law k]
    by_cases hk : 0 ≤ t - (k : ℝ) ^ 2
    · rw [max_eq_right hk]
      ring
    · simp [max_eq_left (le_of_not_ge hk)]
  simp_rw [hp]
  have hs := ((A.mass.mul_left t).sub A.second_moment).mul_right Z⁻¹
  simpa only [← div_eq_mul_inv, mul_one] using hs.tsum_eq

private theorem radius_le_normalizer {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (A : Activation m n t Z w) : t ≤ Z := by
  rw [A.normalizer_eq]
  have hterm (k : ℤ) (hk : k ∈ Icc (-(n : ℤ)) (n : ℤ)) : 0 ≤ t - (k : ℝ) ^ 2 := by
    have hk' := Finset.mem_Icc.mp hk
    have habs : |(k : ℝ)| ≤ n := abs_le.mpr ⟨by exact_mod_cast hk'.1, by exact_mod_cast hk'.2⟩
    have hsq := (sq_le_sq₀ (abs_nonneg (k : ℝ)) (Nat.cast_nonneg n)).mpr habs
    rw [sq_abs] at hsq
    exact sub_nonneg.mpr (hsq.trans A.radius_lower)
  simpa using single_le_sum hterm (show (0 : ℤ) ∈ Icc (-(n : ℤ)) (n : ℤ) by simp)

private theorem embedded_feasible {q n : ℕ} [NeZero q] {lam t Z : ℝ} {w : ℤ → ℝ}
    (hq : 2 * latticeSupportRadius n (lam / (8 * Real.pi ^ 2)) < q)
    (A : Activation (lam / (8 * Real.pi ^ 2)) n t Z w) :
    ∃ u ∈ feasible q (1 - lam / (q : ℝ) ^ 2), energy u = ∑' k : ℤ, w k ^ 2 := by
  let u : ZMod q → ℝ := fun i => w i.valMinAbs
  have hz := fun k hk => activation_zero_outside A (k := k) hk
  have hmass : (∑ i, u i) = 1 := (sum_centered_eq_tsum hq w hz).trans A.mass.tsum_eq
  have hmoment : (∑ i : ZMod q, (i.valMinAbs : ℝ) ^ 2 * u i) = lam / (8 * Real.pi ^ 2) :=
    (sum_centered_eq_tsum hq _ (fun k hk => by rw [hz k hk, mul_zero])).trans
      A.second_moment.tsum_eq
  have henergy : energy u = ∑' k : ℤ, w k ^ 2 :=
    sum_centered_eq_tsum hq (fun k => w k ^ 2)
      (fun k hk => by simp only [hz k hk, zero_pow two_ne_zero])
  have hdeficit (r : ℕ) (hr : r ≤ 2) : 1 - lam / (q : ℝ) ^ 2 ≤ cosineMoment r u := by
    have hr2 : (r : ℝ) ^ 2 ≤ (2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (Nat.cast_nonneg _) (by norm_num)).mpr (by exact_mod_cast hr)
    let C := 8 * Real.pi ^ 2 / (q : ℝ) ^ 2
    have hp (i : ZMod q) :
        1 - Real.cos ((r : ℝ) * centeredAngle i) ≤ C * (i.valMinAbs : ℝ) ^ 2 := by
      calc
        _ ≤ ((r : ℝ) * centeredAngle i) ^ 2 / 2 := by
          linarith only [Real.one_sub_sq_div_two_le_cos (x := (r : ℝ) * centeredAngle i)]
        _ = (r : ℝ) ^ 2 * (centeredAngle i ^ 2 / 2) := by ring
        _ ≤ (2 : ℝ) ^ 2 * (centeredAngle i ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right hr2 (by positivity)
        _ = _ := by unfold C centeredAngle; ring
    have hsum : (∑ i : ZMod q, u i * (1 - Real.cos ((r : ℝ) * centeredAngle i))) ≤
        ∑ i : ZMod q, C * ((i.valMinAbs : ℝ) ^ 2 * u i) := by
      apply sum_le_sum
      intro i _
      calc
        _ ≤ u i * (C * (i.valMinAbs : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (hp i) (A.nonneg _)
        _ = _ := by ring
    rw [← mul_sum, hmoment] at hsum
    have hC : C * (lam / (8 * Real.pi ^ 2)) = lam / (q : ℝ) ^ 2 := by
      dsimp [C]
      have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
      field_simp [Real.pi_ne_zero]
    simp_rw [mul_sub, mul_one] at hsum
    rw [sum_sub_distrib, hmass, ← cosineMoment_eq_centered, hC] at hsum
    linarith only [hsum]
  exact ⟨u, ⟨fun i => A.nonneg _, hmass, hdeficit 1 (by omega), hdeficit 2 le_rfl⟩, henergy⟩

private theorem universal_lower_bound {q n : ℕ} [NeZero q] {lam t Z : ℝ} {w : ℤ → ℝ}
    (hq : 2 * latticeSupportRadius n (lam / (8 * Real.pi ^ 2)) < q)
    (A : Activation (lam / (8 * Real.pi ^ 2)) n t Z w)
    {v : ZMod q → ℝ} (hv : ∀ i, 0 ≤ v i) (hmass : ∑ i, v i = 1) :
    let a := 1 - lam / (q : ℝ) ^ 2
    (∑ i : ZMod q, (v i - w i.valMinAbs) ^ 2) +
      (2 * t / Z) * (cosineMoment 1 v - a) +
      (((q : ℝ) / (2 * Real.pi)) ^ 2 / Z) * (cosineMoment 2 v - a) ≤
      energy v - (∑' k : ℤ, w k ^ 2) + (2 * t / Z) * (lam / (q : ℝ) ^ 2) := by
  let m := lam / (8 * Real.pi ^ 2)
  let δ := lam / (q : ℝ) ^ 2
  let C := ((q : ℝ) / (2 * Real.pi)) ^ 2 / 2
  let P := dualPolynomial (q := q) t Z
  have hCδ : C * δ = m := by
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
    dsimp [C, δ, m]
    field_simp [Real.pi_ne_zero]
    ring
  have hdot : (∑ i, v i * P i) =
      (t * cosineMoment 1 v - C * (1 - cosineMoment 2 v)) / Z := by
    have hp (i : ZMod q) : v i * P i =
        (t * (v i * Real.cos (centeredAngle i)) -
          C * (v i * (1 - Real.cos (2 * centeredAngle i)))) / Z := by
      dsimp [P, dualPolynomial, C]
      rw [Real.cos_two_mul_eq_one_sub]
      ring
    have hfirst : cosineMoment 1 v = ∑ i, v i * Real.cos (centeredAngle i) := by
      simpa only [Nat.cast_one, one_mul] using cosineMoment_eq_centered 1 v
    have hsecond : cosineMoment 2 v = ∑ i, v i * Real.cos (2 * centeredAngle i) := by
      simpa only [Nat.cast_ofNat] using cosineMoment_eq_centered 2 v
    have hdeficit : (∑ i, v i * (1 - Real.cos (2 * centeredAngle i))) =
        1 - cosineMoment 2 v := by
      simp_rw [mul_sub, mul_one]
      rw [sum_sub_distrib, hmass, ← hsecond]
    simp_rw [hp]
    rw [← sum_div, sum_sub_distrib, ← mul_sum, ← mul_sum, ← hfirst, hdeficit]
  have hdot_exact : 2 * (∑ i, v i * P i) =
      2 * ((t - m) / Z) - (2 * t / Z) * δ +
        (2 * t / Z) * (cosineMoment 1 v - (1 - δ)) +
        (2 * C / Z) * (cosineMoment 2 v - (1 - δ)) := by
    rw [hdot, ← hCδ]
    ring
  have hsq : (∑ i : ZMod q, w i.valMinAbs ^ 2) = ∑' k : ℤ, w k ^ 2 :=
    sum_centered_eq_tsum hq (fun k => w k ^ 2)
      (fun k hk => by simp only [activation_zero_outside A hk, zero_pow two_ne_zero])
  have hdot_weight : (∑ i, v i * P i) ≤ ∑ i : ZMod q, v i * w i.valMinAbs :=
    sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left ((le_max_right 0 _).trans (dual_positive_part_le A i)) (hv i)
  have hdist : (∑ i : ZMod q, (v i - w i.valMinAbs) ^ 2) =
      energy v - 2 * (∑ i : ZMod q, v i * w i.valMinAbs) + (∑' k : ℤ, w k ^ 2) := by
    simp_rw [sub_sq, mul_assoc]
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, hsq, energy]
  have hC : 2 * C / Z = ((q : ℝ) / (2 * Real.pi)) ^ 2 / Z := by dsimp [C]; ring
  dsimp only
  rw [hdist, lattice_energy_eq A, ← hC]
  change _ + (2 * t / Z) * (cosineMoment 1 v - (1 - δ)) +
      (2 * C / Z) * (cosineMoment 2 v - (1 - δ)) ≤ _
  linarith only [hdot_weight, hdot_exact]

private theorem exists_cyclic_minimum {q : ℕ} [NeZero q] {a : ℝ}
    (hne : (feasible q a).Nonempty) :
    ∃ v ∈ feasible q a, IsMinOn energy (feasible q a) v := by
  have hm (r : ℕ) : Continuous (cosineMoment (q := q) r) := by
    unfold cosineMoment
    fun_prop
  have hmass : Continuous (fun v : ZMod q → ℝ => ∑ i, v i) := by fun_prop
  have hclosed : IsClosed (feasible q a) := by
    have hnonneg : IsClosed {v : ZMod q → ℝ | ∀ i, 0 ≤ v i} := by
      simpa only [Set.ofPred_forall] using
        isClosed_iInter (fun i : ZMod q => isClosed_le continuous_const (continuous_apply i))
    exact hnonneg.inter ((isClosed_eq hmass continuous_const).inter
      ((isClosed_le continuous_const (hm 1)).inter (isClosed_le continuous_const (hm 2))))
  have hbounded : feasible q a ⊆ Set.Icc (0 : ZMod q → ℝ) 1 := by
    intro v hv
    refine ⟨hv.1, fun i => ?_⟩
    exact (single_le_sum (fun j _ => hv.1 j) (mem_univ i)).trans_eq hv.2.1
  have hcont : Continuous (energy (q := q)) := by
    unfold energy
    fun_prop
  exact (isCompact_Icc.of_isClosed_subset hclosed hbounded).exists_isMinOn hne hcont.continuousOn

/-- If the lattice support fits in the centered residues, the cyclic minimum
at threshold `1 - λ/q²` is attained. Its gap below the lattice minimum is at most
`(2t/Z) λ/q²`, hence at most `2λ/q²`. -/
theorem cyclic_to_lattice_comparison (q n : ℕ) (hn : 0 < n) (lam : ℝ)
    (hq : 2 * latticeSupportRadius n (lam / (8 * Real.pi ^ 2)) < q)
    (hmlo : ((n : ℝ) ^ 2 - 1) / 5 ≤ lam / (8 * Real.pi ^ 2))
    (hmhi : lam / (8 * Real.pi ^ 2) ≤ (n : ℝ) * (n + 2) / 5) :
    letI : NeZero q := ⟨by omega⟩
    let m := lam / (8 * Real.pi ^ 2)
    let a := 1 - lam / (q : ℝ) ^ 2
    let error := fun x : ℝ => 2 * x
    ∃ (t Z : ℝ) (w : ℤ → ℝ), Activation m n t Z w ∧
      (∀ (u : ZMod q → ℝ), (∀ i, 0 ≤ u i) → (∑ i, u i) = 1 →
        (∑ i : ZMod q, (u i - w i.valMinAbs) ^ 2) +
          (2 * t / Z) * (cosineMoment 1 u - a) +
          (((q : ℝ) / (2 * Real.pi)) ^ 2 / Z) * (cosineMoment 2 u - a) ≤
        energy u - (∑' k : ℤ, w k ^ 2) + (2 * t / Z) * (lam / (q : ℝ) ^ 2)) ∧
      ∃ v ∈ feasible q a, IsMinOn energy (feasible q a) v ∧
        0 ≤ (∑' k : ℤ, w k ^ 2) - energy v ∧
        (∑' k : ℤ, w k ^ 2) - energy v ≤ (2 * t / Z) * (lam / (q : ℝ) ^ 2) ∧
        (∑' k : ℤ, w k ^ 2) - energy v ≤ error (lam / (q : ℝ) ^ 2) := by
  let _ : NeZero q := ⟨by omega⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : 0 ≤ lam / (8 * Real.pi ^ 2) := by
    have h := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ n)).mpr hn'
    linarith
  have hlam : 0 ≤ lam := by
    rw [le_div_iff₀ (by positivity : 0 < 8 * Real.pi ^ 2), zero_mul] at hm
    exact hm
  obtain ⟨⟨t, Z, w⟩, A, _⟩ :=
    (exists_lattice_square_moment_minimizer_on_interval n hn _).mp ⟨hmlo, hmhi⟩
  obtain ⟨u, hu, huenergy⟩ := embedded_feasible hq A
  obtain ⟨v, hv, hvmin⟩ := exists_cyclic_minimum ⟨u, hu⟩
  have hdist := universal_lower_bound hq A hv.1 hv.2.1
  have hnonneg : 0 ≤ ∑ i : ZMod q, (v i - w i.valMinAbs) ^ 2 :=
    sum_nonneg fun i _ => sq_nonneg _
  have hgap : (∑' k : ℤ, w k ^ 2) - energy v ≤ (2 * t / Z) * (lam / (q : ℝ) ^ 2) := by
    have ht : 0 ≤ t := (sq_nonneg _).trans A.radius_lower
    have hs₁ := mul_nonneg (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht) A.normalizer_pos.le)
      (sub_nonneg.mpr hv.2.2.1)
    have hs₂ := mul_nonneg (div_nonneg (sq_nonneg ((q : ℝ) / (2 * Real.pi))) A.normalizer_pos.le)
      (sub_nonneg.mpr hv.2.2.2)
    dsimp only at hdist
    linarith only [hdist, hnonneg, hs₁, hs₂]
  refine ⟨t, Z, w, A, fun _ hu hmass => universal_lower_bound hq A hu hmass, v, hv, hvmin,
    sub_nonneg.mpr ((hvmin hu).trans_eq huenergy), hgap, ?_⟩
  have hratio : 2 * t / Z ≤ 2 := by
    rw [div_le_iff₀ A.normalizer_pos]
    exact mul_le_mul_of_nonneg_left (radius_le_normalizer A) (by norm_num)
  calc
    _ ≤ (2 * t / Z) * (lam / (q : ℝ) ^ 2) := hgap
    _ ≤ 2 * (lam / (q : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hratio (div_nonneg hlam (sq_nonneg _))

end D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
