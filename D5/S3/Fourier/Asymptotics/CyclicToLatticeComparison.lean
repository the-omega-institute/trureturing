/- GID: D5/S3/Fourier/Asymptotics/CyclicToLatticeComparison
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicToLatticeComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative comparison of the two-mode cyclic and lattice squared-mass minima. -/

import D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
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
  ∑ i : ZMod q, v i * Real.cos ((r : ℝ) * (2 * Real.pi * (i.val : ℝ) / q))

/-- Probability weights with both the first and second cosine moments at least `a`. -/
def feasible (q : ℕ) [NeZero q] (a : ℝ) : Set (ZMod q → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = 1 ∧ a ≤ cosineMoment 1 v ∧ a ≤ cosineMoment 2 v}

/-- Squared mass on the cyclic group. -/
def energy {q : ℕ} [NeZero q] (v : ZMod q → ℝ) : ℝ :=
  ∑ i, v i ^ 2

private def centeredAngle {q : ℕ} (i : ZMod q) : ℝ :=
  2 * Real.pi * (i.valMinAbs : ℝ) / q

private theorem cosineMoment_eq_centered {q : ℕ} [NeZero q] (r : ℕ) (v : ZMod q → ℝ) :
    cosineMoment r v = ∑ i : ZMod q, v i * Real.cos ((r : ℝ) * centeredAngle i) := by
  unfold cosineMoment
  apply sum_congr rfl
  intro i _
  congr 1
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

private theorem abs_centeredAngle_le_pi {q : ℕ} [NeZero q] (i : ZMod q) :
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

private theorem activation_zero_outside {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (A : Activation m n t Z w) {k : ℤ} (hk : k ∉ Icc (-(n : ℤ)) (n : ℤ)) : w k = 0 := by
  by_contra h
  have hs : k ∈ Function.support w := h
  rw [A.support] at hs
  split at hs
  · simp only [Finset.mem_coe, Finset.mem_Icc] at hs
    apply hk
    simp only [Finset.mem_Icc]
    have hpred : ((n - 1 : ℕ) : ℤ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    omega
  · exact hk hs

private theorem sum_centered_eq_tsum {q n : ℕ} [NeZero q] (hq : 2 * n < q) (f : ℤ → ℝ)
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

private theorem lattice_energy_eq {m t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
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
    (hq : 2 * n < q) (A : Activation (lam / (8 * Real.pi ^ 2)) n t Z w) :
    ∃ u ∈ feasible q (1 - lam / (q : ℝ) ^ 2), energy u = ∑' k : ℤ, w k ^ 2 := by
  let u : ZMod q → ℝ := fun i => w i.valMinAbs
  have hz (k : ℤ) (hk : k ∉ Icc (-(n : ℤ)) (n : ℤ)) : w k = 0 :=
    activation_zero_outside A hk
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

private theorem quadratic_dual_le {x p : ℝ} (hx : 0 ≤ x) :
    2 * (x * p) - (max 0 p) ^ 2 ≤ x ^ 2 := by
  by_cases hp : 0 ≤ p
  · rw [max_eq_right hp]
    nlinarith only [sq_nonneg (x - p)]
  · rw [max_eq_left (le_of_not_ge hp)]
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos hx (le_of_not_ge hp), sq_nonneg x]

private theorem universal_lower_bound {q n : ℕ} [NeZero q] {lam t Z : ℝ} {w : ℤ → ℝ}
    (hq : 2 * n < q) (A : Activation (lam / (8 * Real.pi ^ 2)) n t Z w)
    {v : ZMod q → ℝ} (hv : v ∈ feasible q (1 - lam / (q : ℝ) ^ 2)) :
    (∑' k : ℤ, w k ^ 2) - (2 * t / Z) * (lam / (q : ℝ) ^ 2) ≤ energy v := by
  let m := lam / (8 * Real.pi ^ 2)
  let δ := lam / (q : ℝ) ^ 2
  let C := ((q : ℝ) / (2 * Real.pi)) ^ 2 / 2
  let P := dualPolynomial (q := q) t Z
  have hCδ : C * δ = m := by
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
    dsimp [C, δ, m]
    field_simp [Real.pi_ne_zero]
    <;> ring
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
      rw [sum_sub_distrib, hv.2.1, ← hsecond]
    simp_rw [hp]
    rw [← sum_div, sum_sub_distrib, ← mul_sum, ← mul_sum, ← hfirst, hdeficit]
  have hdot_lower : (t - m) / Z - t * δ / Z ≤ ∑ i, v i * P i := by
    rw [hdot, ← sub_div]
    apply (div_le_div_iff_of_pos_right A.normalizer_pos).mpr
    have h₁ := mul_le_mul_of_nonneg_left hv.2.2.1 ((sq_nonneg _).trans A.radius_lower)
    have h₂ := mul_le_mul_of_nonneg_left (show 1 - cosineMoment 2 v ≤ δ by
      linarith only [hv.2.2.2]) (show 0 ≤ C by positivity)
    linarith only [h₁, h₂, hCδ]
  have hsq : (∑ i : ZMod q, w i.valMinAbs ^ 2) = ∑' k : ℤ, w k ^ 2 :=
    sum_centered_eq_tsum hq (fun k => w k ^ 2)
      (fun k hk => by simp only [activation_zero_outside A hk, zero_pow two_ne_zero])
  calc
    _ ≤ 2 * (∑ i, v i * P i) - ∑' k : ℤ, w k ^ 2 := by
      rw [lattice_energy_eq A]
      change (t - m) / Z - (2 * t / Z) * δ ≤ 2 * (∑ i, v i * P i) - (t - m) / Z
      linarith only [hdot_lower, show (2 * t / Z) * δ = 2 * (t * δ / Z) by ring]
    _ ≤ 2 * (∑ i, v i * P i) - ∑ i, (max 0 (P i)) ^ 2 := by
      rw [← hsq]
      exact sub_le_sub_left (sum_le_sum fun i _ =>
        (sq_le_sq₀ (le_max_left _ _) (A.nonneg _)).mpr (dual_positive_part_le A i)) _
    _ ≤ energy v := by
      rw [mul_sum, ← sum_sub_distrib, energy]
      exact sum_le_sum fun i _ => quadratic_dual_le (hv.1 i)

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

/-- For a positive activation index of `m = λ / (8π²)` and `q > 2n`, the cyclic minimum
at threshold `1 - λ/q²` is attained. Its gap below the lattice minimum is at most
`(2t/Z) λ/q²`, hence at most `2λ/q²`. -/
theorem cyclic_to_lattice_comparison (q n : ℕ) (hn : 0 < n) (hq : 2 * n < q)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hmlo : ((n : ℝ) ^ 2 - 1) / 5 ≤ lam / (8 * Real.pi ^ 2))
    (hmhi : lam / (8 * Real.pi ^ 2) ≤ (n : ℝ) * (n + 2) / 5) :
    letI : NeZero q := ⟨by omega⟩
    let m := lam / (8 * Real.pi ^ 2)
    let a := 1 - lam / (q : ℝ) ^ 2
    ∃ (t Z : ℝ) (w : ℤ → ℝ), Activation m n t Z w ∧
      ∃ v ∈ feasible q a, IsMinOn energy (feasible q a) v ∧
        0 ≤ (∑' k : ℤ, w k ^ 2) - energy v ∧
        (∑' k : ℤ, w k ^ 2) - energy v ≤ (2 * t / Z) * (lam / (q : ℝ) ^ 2) ∧
        (∑' k : ℤ, w k ^ 2) - energy v ≤ 2 * lam / (q : ℝ) ^ 2 := by
  let _ : NeZero q := ⟨by omega⟩
  obtain ⟨t, Z, w, A⟩ :=
    (exists_lattice_square_moment_minimizer_on_interval n hn _).mp ⟨hmlo, hmhi⟩
  obtain ⟨u, hu, huenergy⟩ := embedded_feasible hq A
  obtain ⟨v, hv, hvmin⟩ := exists_cyclic_minimum ⟨u, hu⟩
  have hgap := sub_le_comm.mp (universal_lower_bound hq A hv)
  refine ⟨t, Z, w, A, v, hv, hvmin, sub_nonneg.mpr ((hvmin hu).trans_eq huenergy), hgap, ?_⟩
  have hratio : 2 * t / Z ≤ 2 := by
    rw [div_le_iff₀ A.normalizer_pos]
    exact mul_le_mul_of_nonneg_left (radius_le_normalizer A) (by norm_num)
  calc
    _ ≤ (2 * t / Z) * (lam / (q : ℝ) ^ 2) := hgap
    _ ≤ 2 * (lam / (q : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hratio (div_nonneg hlam (sq_nonneg _))
    _ = _ := by ring

end D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
