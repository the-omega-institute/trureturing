/- GID: D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/SparseProbeCoercivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A full-support complex probe controls the scalar defect of every complex matrix. -/

import D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity

noncomputable section
open Matrix Complex
open scoped ComplexConjugate BigOperators
namespace D5.S3.Quantum.QuantumChannels.SparseProbeCoercivity

variable {d : ℕ}

/-- Squared Hilbert--Schmidt norm in the fixed coordinate basis. -/
def hsSq (C : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (C i j)

/-- The off-diagonal squared Hilbert--Schmidt norm. -/
def offSq (C : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else Complex.normSq (C i j)

/-- The rank-one survival defect of one Kraus matrix. -/
def survivalLoss (C : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) : ℝ :=
  (∑ i, Complex.normSq (C.mulVec v i)) -
    Complex.normSq (∑ i, conj (v i) * C.mulVec v i)

/-- Loss in the coordinate probes and one additional unit probe. -/
def probeLoss (C : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) : ℝ :=
  offSq C + survivalLoss C v

private theorem sub_sq_le (x y : ℂ) :
    normSq (x-y) ≤ 2 * normSq x + 2 * normSq y := by
  simp only [normSq_apply, sub_re, sub_im]
  nlinarith [sq_nonneg (x.re+y.re), sq_nonneg (x.im+y.im)]

private theorem residual_identity (x v : Fin d → ℂ)
    (hv : ∑ i, normSq (v i) = 1) :
    let c := ∑ i, conj (v i) * x i
    ∑ i, normSq (x i - c * v i) = (∑ i, normSq (x i)) - normSq c := by
  dsimp
  simp only [normSq_sub, normSq_mul, map_mul, conj_conj,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hv, mul_one]
  have hh : (∑ i, (x i * (conj (∑ j, conj (v j) * x j) * conj (v i))).re) =
      normSq (∑ i, conj (v i) * x i) := by
    rw [← Complex.re_sum]
    have he : (∑ i, x i * (conj (∑ j, conj (v j) * x j) * conj (v i))) =
        (∑ i, conj (v i) * x i) * conj (∑ i, conj (v i) * x i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he, Complex.mul_conj, Complex.ofReal_re]
  rw [← Finset.mul_sum, hh]
  ring

private theorem mulVec_sq_le (B : Matrix (Fin d) (Fin d) ℂ)
    (v : Fin d → ℂ) (hv : ∑ i, normSq (v i) = 1) :
    ∑ i, normSq (B.mulVec v i) ≤ hsSq B := by
  apply Finset.sum_le_sum
  intro i _
  have hn : ‖B.mulVec v i‖ ≤ ∑ j, ‖B i j‖ * ‖v j‖ := by
    simpa only [Matrix.mulVec, dotProduct, norm_mul] using
      norm_sum_le Finset.univ (fun j => B i j * v j)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
    (fun j => ‖B i j‖) (fun j => ‖v j‖)
  have hv' : ∑ j, ‖v j‖^2 = 1 := by simpa only [normSq_eq_norm_sq] using hv
  rw [hv', mul_one] at hc
  exact (by simpa only [normSq_eq_norm_sq] using
    (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc)

private theorem diagonal_minimum (lam : Fin d → ℂ) (c : ℂ) (hd : 0 < d) :
    (∑ i, normSq (lam i)) - normSq (∑ i, lam i) / d ≤
      ∑ i, normSq (lam i-c) := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hsum : (∑ i, normSq (lam i-c)) =
      (∑ i, normSq (lam i)) + d * normSq c -
        2 * ((∑ i, lam i) * conj c).re := by
    simp only [normSq_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.sum_mul]
  have hc : 2 * ((∑ i, lam i) * conj c).re - d * normSq c ≤
      normSq (∑ i, lam i) / d := by
    apply (le_div_iff₀ hd').mpr
    apply sub_nonneg.mp
    have he : normSq (∑ i, lam i) -
        (2 * ((∑ i, lam i) * conj c).re - d * normSq c) * d =
        normSq ((∑ i, lam i) - (d:ℂ)*c) := by
      simp only [normSq_sub, normSq_mul, Complex.normSq_natCast, map_mul,
        Complex.conj_natCast, Complex.mul_re, Complex.mul_im,
        Complex.natCast_re, Complex.natCast_im]
      ring
    rw [he]
    exact normSq_nonneg _
  rw [hsum]
  linarith

theorem hs_split (C : Matrix (Fin d) (Fin d) ℂ) :
    hsSq C = offSq C + ∑ i, normSq (C i i) := by
  unfold hsSq offSq
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have he : (∑ j, normSq (C i j)) =
      ∑ j, ((if i=j then 0 else normSq (C i j)) +
        (if i=j then normSq (C i j) else 0)) := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [he, Finset.sum_add_distrib]
  simp

/-- Basis survival tests and one full-support probe quantitatively force scalar Kraus matrices.
The estimate holds for all complex matrices, without a self-adjointness or reality condition. -/
theorem sparse_probe_coercivity (C : Matrix (Fin d) (Fin d) ℂ)
    (v : Fin d → ℂ) (hd : 0 < d) (hv : ∑ i, normSq (v i) = 1)
    (μ : ℝ) (hμ : 0 < μ) (hfull : ∀ i, μ ≤ normSq (v i)) :
    μ / (2+μ) * (hsSq C - normSq (Matrix.trace C) / d) ≤ probeLoss C v := by
  let c : ℂ := ∑ i, conj (v i) * C.mulVec v i
  let B : Matrix (Fin d) (Fin d) ℂ := fun i j => if i=j then 0 else C i j
  have hb : hsSq B = offSq C := by
    simp only [hsSq, offSq, B, apply_ite normSq, normSq_zero]
  have hr : (∑ i, normSq (C.mulVec v i - c*v i)) = survivalLoss C v :=
    residual_identity (C.mulVec v) v hv
  have hsplit (i : Fin d) : (C i i-c)*v i =
      (C.mulVec v i-c*v i) - B.mulVec v i := by
    have hrow : C.mulVec v i = C i i * v i + B.mulVec v i := by
      have he : (∑ j, C i j * v j) = ∑ j,
          ((if i=j then C i j * v j else 0) +
            (if i=j then 0 else C i j * v j)) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
      simp only [Matrix.mulVec, dotProduct, B, ite_mul, zero_mul]
      rw [he, Finset.sum_add_distrib]
      simp
    rw [hrow]
    ring
  have hweighted : μ * (∑ i, normSq (C i i-c)) ≤
      2 * survivalLoss C v + 2 * offSq C := by
    calc
      _ ≤ ∑ i, normSq ((C i i-c)*v i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        rw [normSq_mul]
        exact (mul_le_mul_of_nonneg_right (hfull i) (normSq_nonneg _)).trans_eq
          (mul_comm _ _)
      _ ≤ ∑ i, (2 * normSq (C.mulVec v i-c*v i) + 2 * normSq (B.mulVec v i)) :=
        Finset.sum_le_sum fun i _ => by rw [hsplit]; exact sub_sq_le _ _
      _ ≤ _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hr]
        have hm := mulVec_sq_le B v hv
        rw [hb] at hm
        linarith
  have hmean := diagonal_minimum (fun i => C i i) c hd
  have hvar : μ * ((∑ i, normSq (C i i)) - normSq (Matrix.trace C)/d) ≤
      2*survivalLoss C v + 2*offSq C := by
    exact (mul_le_mul_of_nonneg_left hmean hμ.le).trans hweighted
  have hpos : 0 ≤ survivalLoss C v := by
    rw [← hr]
    exact Finset.sum_nonneg fun i _ => normSq_nonneg _
  rw [hs_split]
  unfold probeLoss
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by linarith : 0 < 2+μ)).mpr
  nlinarith

#print axioms sparse_probe_coercivity
end D5.S3.Quantum.QuantumChannels.SparseProbeCoercivity
