/- GID: D5/S3/Constants/Moments/IntegerNegativeFamilyQuadratic
   generality: G
   mirror-B: D5/B/S3/Constants/Moments/IntegerNegativeFamilyQuadratic
   mirror-E: none(waiver:finite-dimensional-classical-analysis)
   anchors: []
   utility: none
   digest: Simultaneous integer approximation preserves a negative real subspace. -/

import D5.S3.Constants.Moments.CountableHankelNegativeWitness
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-! Uniform Gram perturbations and one denominator preserve an entire real span. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Filter
open scoped BigOperators Topology

namespace D5.S3.Constants.Moments.CountableHankelNegativeWitness

private def family_form {k d : ℕ} (M : Fin d → Fin d → ℝ)
    (A : Fin k → Fin d → ℝ) (t : Fin k → ℝ) : ℝ :=
  ∑ a, ∑ b, (∑ j, t j * A j a) * (∑ j, t j * A j b) * M a b

private def family_gram {k d : ℕ} (M : Fin d → Fin d → ℝ)
    (A : Fin k → Fin d → ℝ) (j l : Fin k) : ℝ :=
  ∑ a, ∑ b, A j a * A l b * M a b

private theorem family_form_gram {k d : ℕ} (M : Fin d → Fin d → ℝ)
    (A : Fin k → Fin d → ℝ) (t : Fin k → ℝ) :
    family_form M A t = ∑ j, ∑ l, t j * t l * family_gram M A j l := by
  classical
  calc
    _ = ∑ a, ∑ b, ∑ j, ∑ l, t j * t l * (A j a * A l b * M a b) := by
      dsimp only [family_form]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul_sum]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = ∑ j, ∑ a, ∑ b, ∑ l, t j * t l * (A j a * A l b * M a b) := by
      calc
        _ = ∑ a, ∑ j, ∑ b, ∑ l, t j * t l * (A j a * A l b * M a b) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]
    _ = ∑ j, ∑ l, ∑ a, ∑ b, t j * t l * (A j a * A l b * M a b) := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = ∑ a, ∑ l, ∑ b, t j * t l * (A j a * A l b * M a b) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]
    _ = _ := by simp only [family_gram, Finset.mul_sum]

private theorem family_form_homogeneous {k d : ℕ} (M : Fin d → Fin d → ℝ)
    (A : Fin k → Fin d → ℝ) (t : Fin k → ℝ) (r : ℝ) :
    family_form M A (r • t) = r ^ 2 * family_form M A t := by
  rw [family_form_gram, family_form_gram]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

private theorem family_form_scale_rows {k d : ℕ} (M : Fin d → Fin d → ℝ)
    (A : Fin k → Fin d → ℝ) (t : Fin k → ℝ) (r : ℝ) :
    family_form M (fun j a => r * A j a) t = r ^ 2 * family_form M A t := by
  have hlin (a : Fin d) : (∑ j, t j * (r * A j a)) = r * ∑ j, t j * A j a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  dsimp only [family_form]
  simp_rw [hlin]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem sum_sq_pos {k : ℕ} (t : Fin k → ℝ) (ht : t ≠ 0) :
    0 < ∑ j, (t j) ^ 2 := by
  have hnonneg : 0 ≤ ∑ j, (t j) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  refine lt_of_le_of_ne hnonneg ?_
  intro h
  apply ht
  funext j
  exact ((Finset.sum_sq_eq_zero_iff Finset.univ t).mp h.symm) j (Finset.mem_univ _)

/-- A uniform real quadratic gap survives simultaneous approximation of all
rows by one integer matrix. No symmetry of the finite real form is required. -/
theorem exists_integer_negative_family_quadratic_of_gap {k d : ℕ}
    (M : Fin d → Fin d → ℝ) (A : Fin k → Fin d → ℝ)
    (γ : ℝ) (hγ : 0 < γ)
    (hA : ∀ t : Fin k → ℝ,
      (∑ a, ∑ b, (∑ j, t j * A j a) * (∑ j, t j * A j b) * M a b) ≤
        -γ * ∑ j, (t j) ^ 2) :
    ∃ U : Fin k → Fin d → ℤ, ∀ t : Fin k → ℝ, t ≠ 0 →
      (∑ a, ∑ b, (∑ j, t j * (U j a : ℝ)) *
        (∑ j, t j * (U j b : ℝ)) * M a b) < 0 := by
  classical
  let η : ℝ := γ / (2 * ((k : ℝ) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  let V : Set (Fin k → Fin d → ℝ) :=
    {T | ∀ j l, |family_gram M T j l - family_gram M A j l| < η}
  have hV : IsOpen V := by
    have hVe : V = ⋂ j, ⋂ l,
        {T | |family_gram M T j l - family_gram M A j l| < η} := by
      ext T
      simp [V]
    rw [hVe]
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro l
    apply isOpen_lt _ continuous_const
    dsimp [family_gram]
    fun_prop
  have hAV : A ∈ V := by intro j l; simpa using hη
  have hd : DenseRange (fun R : Fin k → Fin d → ℚ => fun j a => (R j a : ℝ)) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => Rat.denseRange_cast))
  obtain ⟨R, hR⟩ := hd.exists_mem_open hV ⟨A, hAV⟩
  let T : Fin k → Fin d → ℝ := fun j a => (R j a : ℝ)
  have hnear (j l : Fin k) : |family_gram M T j l - family_gram M A j l| ≤ η :=
    (hR j l).le
  have hT (t : Fin k → ℝ) (ht : t ≠ 0) : family_form M T t < 0 := by
    have hdiff : family_form M T t - family_form M A t =
        ∑ j, ∑ l, t j * t l * (family_gram M T j l - family_gram M A j l) := by
      rw [family_form_gram, family_form_gram, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l _
      ring
    have herr : |family_form M T t - family_form M A t| ≤
        η * (∑ j, |t j|) ^ 2 := by
      rw [hdiff]
      calc
        _ ≤ ∑ j, |∑ l, t j * t l * (family_gram M T j l - family_gram M A j l)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, ∑ l, |t j * t l * (family_gram M T j l - family_gram M A j l)| := by
          apply Finset.sum_le_sum
          intro j _
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, ∑ l, |t j| * |t l| * η := by
          apply Finset.sum_le_sum
          intro j _
          apply Finset.sum_le_sum
          intro l _
          simp only [abs_mul]
          exact mul_le_mul_of_nonneg_left (hnear j l) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = _ := by
          simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro l _
          ring
    have hcs : (∑ j, |t j|) ^ 2 ≤ (∑ j, (t j) ^ 2) * (k : ℝ) := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => |t j|) (fun _ => (1 : ℝ))
    have hηk : η * (k : ℝ) ≤ γ / 2 := by
      have hηeq : η * (2 * ((k : ℝ) + 1)) = γ := by
        dsimp [η]
        exact div_mul_cancel₀ _ (by positivity)
      nlinarith
    have hS := sum_sq_pos t ht
    have herr' := herr.trans (mul_le_mul_of_nonneg_left hcs hη.le)
    have hηS := mul_le_mul_of_nonneg_right hηk hS.le
    have hup := (le_abs_self (family_form M T t - family_form M A t)).trans herr'
    have hgap : family_form M A t ≤ -γ * ∑ j, (t j) ^ 2 := hA t
    have hγS : 0 < γ * (∑ j, (t j) ^ 2) := mul_pos hγ hS
    nlinarith
  let B : Matrix (Fin k) (Fin d) ℚ := R
  have hD : (B.den : ℝ) ≠ 0 := by exact_mod_cast B.den_ne_zero
  have hscale (j : Fin k) (a : Fin d) :
      (B.num j a : ℝ) = (B.den : ℝ) * T j a := by
    have h := B.num_div_den j a
    have h' : (B.num j a : ℝ) / (B.den : ℝ) = (B j a : ℝ) := by exact_mod_cast h
    exact (div_eq_iff hD).mp h' |>.trans (mul_comm _ _)
  refine ⟨B.num, ?_⟩
  intro t ht
  change family_form M (fun j a => (B.num j a : ℝ)) t < 0
  simp_rw [hscale]
  rw [family_form_scale_rows]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hD) (hT t ht)

/-- Any real row matrix with strictly negative pullback on every nonzero real
vector admits one integer row matrix with that property, including k = 0. -/
theorem exists_integer_negative_family_quadratic {k d : ℕ}
    (M : Fin d → Fin d → ℝ) (A : Fin k → Fin d → ℝ)
    (hA : ∀ t : Fin k → ℝ, t ≠ 0 →
      (∑ a, ∑ b, (∑ j, t j * A j a) * (∑ j, t j * A j b) * M a b) < 0) :
    ∃ U : Fin k → Fin d → ℤ, ∀ t : Fin k → ℝ, t ≠ 0 →
      (∑ a, ∑ b, (∑ j, t j * (U j a : ℝ)) *
        (∑ j, t j * (U j b : ℝ)) * M a b) < 0 := by
  classical
  let S : (Fin k → ℝ) → ℝ := fun t => ∑ j, (t j) ^ 2
  let K := Metric.sphere (0 : Fin k → ℝ) 1
  have hK : IsCompact K := isCompact_sphere _ _
  have hne (t : Fin k → ℝ) (ht : t ∈ K) : t ≠ 0 := by
    intro h
    simp [K, h] at ht
  have hS (t : Fin k → ℝ) (ht : t ∈ K) : 0 < S t := sum_sq_pos t (hne t ht)
  have hc : ContinuousOn (fun t => -family_form M A t / S t) K := by
    apply ContinuousOn.div
    · exact (show Continuous (fun t => -family_form M A t) by
        dsimp [family_form]; fun_prop).continuousOn
    · exact (show Continuous S by dsimp [S]; fun_prop).continuousOn
    · intro t ht
      exact (hS t ht).ne'
  obtain ⟨γ, hγ, hγK⟩ := hK.exists_forall_le' hc (a := (0 : ℝ)) (by
    intro t ht
    exact div_pos (neg_pos.mpr (hA t (hne t ht))) (hS t ht))
  apply exists_integer_negative_family_quadratic_of_gap M A γ hγ
  intro t
  change family_form M A t ≤ -γ * S t
  by_cases ht : t = 0
  · subst t
    simp [family_form, S]
  let u := NormedSpace.normalize t
  have hu : u ∈ K := by
    simpa only [K, Metric.mem_sphere, dist_zero_right] using
      (NormedSpace.norm_normalize ht : ‖u‖ = 1)
  have hu_scale : ‖t‖ • u = t := NormedSpace.norm_smul_normalize t
  have hg : family_form M A u ≤ -γ * S u := by
    have h := (le_div_iff₀ (hS u hu)).mp (hγK u hu)
    linarith
  have hscaleQ : family_form M A t = ‖t‖ ^ 2 * family_form M A u := by
    calc
      _ = family_form M A (‖t‖ • u) := by rw [hu_scale]
      _ = _ := family_form_homogeneous M A u ‖t‖
  have hscaleS : S t = ‖t‖ ^ 2 * S u := by
    calc
      _ = S (‖t‖ • u) := by rw [hu_scale]
      _ = _ := by
        simp only [S, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  rw [hscaleQ, hscaleS]
  have h := mul_le_mul_of_nonneg_left hg (sq_nonneg ‖t‖)
  nlinarith

end D5.S3.Constants.Moments.CountableHankelNegativeWitness
