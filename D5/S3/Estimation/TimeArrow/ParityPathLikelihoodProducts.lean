/- GID: D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform-reference inner products of parity-kernel path products, both directions. -/

import D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts

open Finset
open D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates

/-- The forward path likelihood `∏_{t<s} 2^d P_a(x_t, x_{t+1})` of a path of `s` steps against the
uniform product reference. -/
noncomputable def forwardLikelihood {d : ℕ} (a : (Fin d → ℤˣ) → ℝ) (s : ℕ)
    (x : Fin (s + 1) → Fin d → ℤˣ) : ℝ :=
  ∏ t : Fin s, (2 ^ d * parityKernel a (x t.castSucc) (x t.succ))

/-- The backward path likelihood `∏_{t<s} 2^d P_a(x_{t+1}, x_t)`: the likelihood of the
time-reversed path law. -/
noncomputable def backwardLikelihood {d : ℕ} (a : (Fin d → ℤˣ) → ℝ) (s : ℕ)
    (x : Fin (s + 1) → Fin d → ℤˣ) : ℝ :=
  ∏ t : Fin s, (2 ^ d * parityKernel a (x t.succ) (x t.castSucc))

/-- Expectation under the uniform product law on paths of `s` steps. -/
noncomputable def uniformPathMean {d : ℕ} (s : ℕ) (F : (Fin (s + 1) → Fin d → ℤˣ) → ℝ) : ℝ :=
  (1 / 2 ^ d : ℝ) ^ (s + 1) * ∑ x, F x

/-- If every column of `M` sums to `λ`, the sum over all paths of `s` steps of the edge products
is `2^d λ^s`: sum out the first state and induct. -/
private theorem sum_path_prod_of_column {d : ℕ} (M : (Fin d → ℤˣ) → (Fin d → ℤˣ) → ℝ) (lam : ℝ)
    (hcol : ∀ y, ∑ x, M x y = lam) (s : ℕ) :
    ∑ x : Fin (s + 1) → Fin d → ℤˣ, ∏ t : Fin s, M (x t.castSucc) (x t.succ) =
      2 ^ d * lam ^ s := by
  induction s with
  | zero => simp [Fintype.card_units_int]
  | succ s ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (s + 2) => Fin d → ℤˣ)).sum_comp, Fintype.sum_prod_type]
    have hsplit : ∀ (x0 : Fin d → ℤˣ) (x' : Fin (s + 1) → Fin d → ℤˣ),
        ∏ t : Fin (s + 1), M ((Fin.consEquiv (fun _ : Fin (s + 2) => Fin d → ℤˣ)) (x0, x')
            t.castSucc) ((Fin.consEquiv (fun _ : Fin (s + 2) => Fin d → ℤˣ)) (x0, x') t.succ) =
          M x0 (x' 0) * ∏ t : Fin s, M (x' t.castSucc) (x' t.succ) := by
      intro x0 x'
      rw [Fin.prod_univ_succ]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one,
        Fin.cons_one, Fin.cons_succ, ← Fin.succ_castSucc]
    simp_rw [hsplit]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hcol]
    rw [← Finset.mul_sum, ih]
    ring

/-- If every row of `M` sums to `μ`, the sum over all paths of `s` steps of the edge products is
`2^d μ^s`: sum out the last state and induct. -/
private theorem sum_path_prod_of_row {d : ℕ} (M : (Fin d → ℤˣ) → (Fin d → ℤˣ) → ℝ) (mu : ℝ)
    (hrow : ∀ x, ∑ y, M x y = mu) (s : ℕ) :
    ∑ x : Fin (s + 1) → Fin d → ℤˣ, ∏ t : Fin s, M (x t.castSucc) (x t.succ) =
      2 ^ d * mu ^ s := by
  induction s with
  | zero => simp [Fintype.card_units_int]
  | succ s ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (s + 2) => Fin d → ℤˣ)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    have hsplit : ∀ (xl : Fin d → ℤˣ) (xi : Fin (s + 1) → Fin d → ℤˣ),
        ∏ t : Fin (s + 1), M ((Fin.snocEquiv (fun _ : Fin (s + 2) => Fin d → ℤˣ)) (xl, xi)
            t.castSucc) ((Fin.snocEquiv (fun _ : Fin (s + 2) => Fin d → ℤˣ)) (xl, xi) t.succ) =
          (∏ t : Fin s, M (xi t.castSucc) (xi t.succ)) * M (xi (Fin.last s)) xl := by
      intro xl xi
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_castSucc, Fin.snoc_last,
        Fin.succ_castSucc, Fin.succ_last]
    simp_rw [hsplit, ← Finset.mul_sum, hrow]
    rw [← Finset.sum_mul, ih]
    ring

/-- **Same-direction forward inner product.** If `∑ a = 0` and `∑ b = 0`, then under the uniform
product reference on paths of `s` steps the forward likelihoods of `P_a` and `P_{b}` have inner
product `(1 + E[a b])^s`. -/
theorem forward_inner_product {d : ℕ} (a b : (Fin d → ℤˣ) → ℝ) (ha : ∑ y, a y = 0)
    (hb : ∑ y, b y = 0) (s : ℕ) :
    uniformPathMean s (fun x => forwardLikelihood a s x * forwardLikelihood b s x) =
      (1 + (1 / 2 ^ d) * ∑ y, a y * b y) ^ s := by
  have card_cube : (Fintype.card (Fin d → ℤˣ) : ℝ) = 2 ^ d := by
    simp [Fintype.card_units_int]
  have parity_sq : ∀ y : Fin d → ℤˣ, parity y * parity y = 1 := by
    intro y
    unfold parity
    rcases Int.units_eq_one_or (∏ j, y j) with h | h <;> simp [h]
  have scale_mean : ∀ c : ℝ, (1 / 2 ^ d : ℝ) ^ (s + 1) * (2 ^ d * (2 ^ d * c) ^ s) = c ^ s := by
    intro c
    have hne : (2 : ℝ) ^ d ≠ 0 := by positivity
    have key : (1 / 2 ^ d : ℝ) ^ (s + 1) * (2 ^ d * (2 ^ d * c) ^ s) =
        ((1 / 2 ^ d) * 2 ^ d) ^ (s + 1) * c ^ s := by ring
    rw [key, one_div_mul_cancel hne, one_pow, one_mul]
  have hcol : ∀ y, ∑ x, (2 ^ d * parityKernel a x y) * (2 ^ d * parityKernel b x y) =
      2 ^ d * (1 + (1 / 2 ^ d) * ∑ y, a y * b y) := by
    intro y
    have hexp : ∀ x, (2 ^ d * parityKernel a x y) * (2 ^ d * parityKernel b x y) =
        1 + parity y * a x + parity y * b x + (parity y * parity y) * (a x * b x) := by
      intro x
      unfold parityKernel
      field_simp
      ring
    simp_rw [hexp, parity_sq, one_mul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ha, hb, Finset.sum_const, Finset.card_univ]
    simp only [nsmul_eq_mul, mul_one, mul_zero, add_zero]
    rw [card_cube]
    field_simp
  unfold uniformPathMean forwardLikelihood
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_path_prod_of_column _ _ hcol s]
  exact scale_mean _

/-- **Same-direction backward inner product.** Under the same hypotheses the backward likelihoods
have the same inner product `(1 + E[a b])^s`. -/
theorem backward_inner_product {d : ℕ} (a b : (Fin d → ℤˣ) → ℝ) (ha : ∑ y, a y = 0)
    (hb : ∑ y, b y = 0) (s : ℕ) :
    uniformPathMean s (fun x => backwardLikelihood a s x * backwardLikelihood b s x) =
      (1 + (1 / 2 ^ d) * ∑ y, a y * b y) ^ s := by
  have card_cube : (Fintype.card (Fin d → ℤˣ) : ℝ) = 2 ^ d := by
    simp [Fintype.card_units_int]
  have parity_sq : ∀ y : Fin d → ℤˣ, parity y * parity y = 1 := by
    intro y
    unfold parity
    rcases Int.units_eq_one_or (∏ j, y j) with h | h <;> simp [h]
  have scale_mean : ∀ c : ℝ, (1 / 2 ^ d : ℝ) ^ (s + 1) * (2 ^ d * (2 ^ d * c) ^ s) = c ^ s := by
    intro c
    have hne : (2 : ℝ) ^ d ≠ 0 := by positivity
    have key : (1 / 2 ^ d : ℝ) ^ (s + 1) * (2 ^ d * (2 ^ d * c) ^ s) =
        ((1 / 2 ^ d) * 2 ^ d) ^ (s + 1) * c ^ s := by ring
    rw [key, one_div_mul_cancel hne, one_pow, one_mul]
  have hrow : ∀ x, ∑ y, (2 ^ d * parityKernel a y x) * (2 ^ d * parityKernel b y x) =
      2 ^ d * (1 + (1 / 2 ^ d) * ∑ y, a y * b y) := by
    intro x
    have hexp : ∀ y, (2 ^ d * parityKernel a y x) * (2 ^ d * parityKernel b y x) =
        1 + parity x * a y + parity x * b y + (parity x * parity x) * (a y * b y) := by
      intro y
      unfold parityKernel
      field_simp
      ring
    simp_rw [hexp, parity_sq, one_mul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ha, hb, Finset.sum_const, Finset.card_univ]
    simp only [nsmul_eq_mul, mul_one, mul_zero, add_zero]
    rw [card_cube]
    field_simp
  unfold uniformPathMean backwardLikelihood
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_path_prod_of_row (fun x y => (2 ^ d * parityKernel a y x) * (2 ^ d * parityKernel b y x))
    _ hrow s]
  exact scale_mean _

/-- **Opposite directions are orthogonal after centering.** If `d ≥ 1`, `∑ b = 0` and
`∑ χ b = 0`, then for every profile `a` the forward likelihood of `P_a` and the backward
likelihood of `P_{b}` have inner product one. -/
theorem forward_backward_inner_product {d : ℕ} (hd : 1 ≤ d) (a b : (Fin d → ℤˣ) → ℝ)
    (hb : ∑ y, b y = 0) (hχb : ∑ y, parity y * b y = 0) (s : ℕ) :
    uniformPathMean s (fun x => forwardLikelihood a s x * backwardLikelihood b s x) = 1 := by
  -- the parity sums to zero: the record law of the empty coordinate set at `T = 1`, `a = 1`
  have hχ : ∑ y : Fin d → ℤˣ, parity y = 0 := by
      have hS : (∅ : Finset (Fin d)) ≠ Finset.univ := by
        intro h
        have : (⟨0, hd⟩ : Fin d) ∈ (∅ : Finset (Fin d)) := h ▸ Finset.mem_univ _
        simp at this
      have h := subcoordinateLaw_eq (fun _ => 1) ∅ hS 1 (fun _ _ => 1)
      unfold subcoordinateLaw at h
      simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, if_true,
        Finset.prod_const_one, mul_one, Finset.card_empty, pow_zero, div_one, one_pow,
        Fin.prod_univ_one, Fin.castSucc_zero, Fin.succ_zero_eq_one] at h
      rw [← (piFinTwoEquiv fun _ => Fin d → ℤˣ).symm.sum_comp, Fintype.sum_prod_type] at h
      simp only [piFinTwoEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, parityKernel, one_mul] at h
      have hn : (0 : ℝ) < 2 ^ d := by positivity
      have hcard : (Fintype.card (Fin d → ℤˣ) : ℝ) = 2 ^ d := by simp [Fintype.card_units_int]
      simp only [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, mul_one, hcard] at h
      field_simp at h
      have hcons : ∀ x x1 : Fin d → ℤˣ, (Fin.cons x (Fin.cons x1 finZeroElim) : Fin 2 → Fin d → ℤˣ) 1 = x1 :=
        fun _ _ => rfl
      simp only [hcons, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, add_eq_left] at h
      exact (mul_eq_zero.mp h).resolve_left hn.ne'
  have scale_mean : ∀ c : ℝ, (1 / 2 ^ d : ℝ) ^ (s + 1) * (2 ^ d * (2 ^ d * c) ^ s) = c ^ s := by
    intro c
    have hne : (2 : ℝ) ^ d ≠ 0 := by positivity
    have key : (1 / 2 ^ d : ℝ) ^ (s + 1) * (2 ^ d * (2 ^ d * c) ^ s) =
        ((1 / 2 ^ d) * 2 ^ d) ^ (s + 1) * c ^ s := by ring
    rw [key, one_div_mul_cancel hne, one_pow, one_mul]
  have hrow : ∀ x, ∑ y, (2 ^ d * parityKernel a x y) * (2 ^ d * parityKernel b y x) =
      2 ^ d * 1 := by
    intro x
    have hexp : ∀ y, (2 ^ d * parityKernel a x y) * (2 ^ d * parityKernel b y x) =
        1 + a x * parity y + parity x * b y + a x * parity x * (parity y * b y) := by
      intro y
      unfold parityKernel
      field_simp
      ring
    simp_rw [hexp]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, hχ, hb, hχb, Finset.sum_const, Finset.card_univ]
    simp [Fintype.card_units_int]
  unfold uniformPathMean forwardLikelihood backwardLikelihood
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_path_prod_of_row (fun x y => (2 ^ d * parityKernel a x y) * (2 ^ d * parityKernel b y x))
    _ hrow s]
  rw [scale_mean, one_pow]

#print axioms forward_inner_product
#print axioms backward_inner_product
#print axioms forward_backward_inner_product

end D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts
