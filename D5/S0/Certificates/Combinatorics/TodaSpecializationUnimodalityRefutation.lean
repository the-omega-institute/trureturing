/- GID: D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.claim; result=D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.result; claim=D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.claim
   digest: Labelle's Toda-eigenfunction numerator is not unimodal in type C₂ at α = 2α₁ + 2α₂. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#11627; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
set_option relaxedAutoImplicit true

namespace D5.S0.Certificates.Combinatorics.TodaSpecializationUnimodalityRefutation

open scoped BigOperators Polynomial

structure CartanDatum (r : ℕ) where
  cartan : Matrix (Fin r) (Fin r) ℤ
  gram : Matrix (Fin r) (Fin r) ℤ
  d : Fin r → ℕ
  cartan_diagonal : ∀ i, cartan i i = 2
  cartan_off_diagonal : ∀ i j, i ≠ j → cartan i j ≤ 0
  cartan_zero : ∀ i j, cartan i j = 0 ↔ cartan j i = 0
  gram_symmetric : ∀ i j, gram i j = gram j i
  d_positive : ∀ i, 0 < d i
  short_normalization : ∀ i, ∃ j,
    (SimpleGraph.fromRel (fun i j => cartan i j ≠ 0)).Reachable i j ∧ d j = 1
  finite_type : ∀ x : Fin r → ℚ, x ≠ 0 →
    0 < ∑ i, ∑ j, x i * (gram i j : ℚ) * x j
  normalized : ∀ i, gram i i = 2 * (d i : ℤ)
  symmetrizes : ∀ i j, gram i j = (d i : ℤ) * cartan i j
  gram_even : ∀ β : Fin r → ℤ, Even (∑ i, ∑ j, β i * gram i j * β j)

private def height {r : ℕ} (α : Fin r → ℕ) : ℕ := ∑ i, α i

noncomputable def qFactor {r : ℕ} (D : CartanDatum r) (α : Fin r → ℕ) : RatFunc ℚ :=
  ∏ i, ∏ j ∈ Finset.range (α i), (1 - RatFunc.X ^ (D.d i * (j + 1)))

/-- The integer half supplied by evenness of the integral Gram quadratic form. -/
noncomputable def quad {r : ℕ} (D : CartanDatum r) (α : Fin r → ℕ) : ℤ :=
  (∑ i, ∑ j, (α i : ℤ) * (α j : ℤ) * D.gram i j) / 2

/-- Definition 1.1, with the self-term moved to the left for nonzero α. -/
noncomputable def J {r : ℕ} (D : CartanDatum r) (α : Fin r → ℕ) : RatFunc ℚ :=
  by
    classical
    exact if α = 0 then 1 else
      (1 - RatFunc.X ^ quad D α)⁻¹ *
      ∑ β ∈ Fintype.piFinset (fun i => Finset.range (α i + 1)),
        if h : β ≤ α ∧ β ≠ α then
          RatFunc.X ^ quad D β / qFactor D (α - β) * J D β
        else 0
termination_by height α
decreasing_by
  unfold height
  apply Finset.sum_lt_sum
  · intro i _hi
    exact h.1 i
  · have hn : ∃ i, β i ≠ α i := by
      by_contra hn
      push Not at hn
      exact h.2 (funext hn)
    obtain ⟨i, hi⟩ := hn
    exact ⟨i, Finset.mem_univ i, lt_of_le_of_ne (h.1 i) hi⟩

def Unimodal (p : ℚ[X]) : Prop :=
  ∃ m : ℕ, m ≤ p.natDegree ∧
    (∀ i, i < m → p.coeff i ≤ p.coeff (i + 1)) ∧
    ∀ i, m ≤ i → i < p.natDegree → p.coeff (i + 1) ≤ p.coeff i

def claim : Prop := ∀ (r : ℕ) (D : CartanDatum r) (α : Fin r → ℕ), ∃ p : ℚ[X],
  algebraMap ℚ[X] (RatFunc ℚ) p = qFactor D α ^ 2 * J D α ∧ Unimodal p

def c2 : CartanDatum 2 where
  cartan := !![2, -2; -1, 2]
  gram := !![2, -2; -2, 4]
  d := ![1, 2]
  cartan_diagonal := by intro i; fin_cases i <;> norm_num
  cartan_off_diagonal := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  cartan_zero := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  gram_symmetric := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  d_positive := by intro i; fin_cases i <;> norm_num
  short_normalization := by
    intro i
    fin_cases i
    · exact ⟨0, SimpleGraph.Reachable.refl _, by rfl⟩
    · refine ⟨0, ?_, by rfl⟩
      apply SimpleGraph.Adj.reachable
      rw [SimpleGraph.fromRel_adj]
      constructor
      · norm_num
      · left
        norm_num
  finite_type := by
    intro x hx
    have h : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hx
      funext i
      fin_cases i <;> simp_all
    norm_num [Fin.sum_univ_two]
    rcases h with hx | hy
    · by_cases hy0 : x 1 = 0
      · have hxy : x 0 - x 1 ≠ 0 := by simpa [hy0] using hx
        nlinarith [sq_pos_of_ne_zero hxy, sq_nonneg (x 1)]
      · nlinarith [sq_nonneg (x 0 - x 1), sq_pos_of_ne_zero hy0]
    · nlinarith [sq_nonneg (x 0 - x 1), sq_pos_of_ne_zero hy]
  normalized := by
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  symmetrizes := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  gram_even := by
    intro β
    refine ⟨β 0 ^ 2 - 2 * β 0 * β 1 + 2 * β 1 ^ 2, ?_⟩
    norm_num [Fin.sum_univ_two]
    ring


theorem result : ¬ claim := by
  classical
  have quad_c2 : ∀ α : Fin 2 → ℕ,
      quad c2 α = (α 0 : ℤ) ^ 2 - 2 * (α 0 : ℤ) * (α 1 : ℤ) +
        2 * (α 1 : ℤ) ^ 2 := by
    intro α
    apply Int.ediv_eq_of_eq_mul_right (by norm_num : (2 : ℤ) ≠ 0)
    simp only [Fin.sum_univ_two]
    norm_num [c2]
    ring
  have box_sum : ∀ (α : Fin 2 → ℕ) (f : (Fin 2 → ℕ) → RatFunc ℚ),
      (∑ β ∈ Fintype.piFinset (fun i => Finset.range (α i + 1)), f β) =
      ∑ a ∈ Finset.range (α 0 + 1), ∑ b ∈ Finset.range (α 1 + 1), f ![a, b] := by
    intro α f
    trans ∑ ab ∈ (Finset.range (α 0 + 1)).product (Finset.range (α 1 + 1)),
      f ![ab.1, ab.2]
    swap
    · exact Finset.sum_product _ _ (fun ab : ℕ × ℕ => f ![ab.1, ab.2])
    apply Finset.sum_bij (fun β _ => (β 0, β 1))
    · intro β hβ
      apply Finset.mem_product.mpr
      exact ⟨Fintype.mem_piFinset.mp hβ 0, Fintype.mem_piFinset.mp hβ 1⟩
    · intro β hβ γ hγ he
      funext i
      fin_cases i
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
    · intro ab hab
      refine ⟨![ab.1, ab.2], ?_, ?_⟩
      · apply Fintype.mem_piFinset.mpr
        intro i
        fin_cases i
        · simpa using (Finset.mem_product.mp hab).1
        · simpa using (Finset.mem_product.mp hab).2
      · simp
    · intro β hβ
      congr 1
      funext i
      fin_cases i <;> simp
  have nz : ∀ k : ℕ, 0 < k → (1 - RatFunc.X ^ k : RatFunc ℚ) ≠ 0 := by
    intro k hk he
    have hp : (1 - Polynomial.X ^ k : ℚ[X]) = 0 := by
      apply RatFunc.algebraMap_injective ℚ
      simpa only [map_sub, map_one, map_pow, RatFunc.algebraMap_X, map_zero] using he
    have hx : (Polynomial.X : ℚ[X]) ^ k = 1 := (sub_eq_zero.mp hp).symm
    exact Polynomial.X_pow_sub_C_ne_zero hk (1 : ℚ)
      (by simp only [hx, Polynomial.C_1, sub_self])
  have nz1 : (1 - RatFunc.X : RatFunc ℚ) ≠ 0 := by
    simpa only [pow_one] using nz 1 (by decide)
  have factor_nz : ∀ α : Fin 2 → ℕ, qFactor c2 α ≠ 0 := by
    intro α
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply nz
    exact Nat.mul_pos (c2.d_positive i) (Nat.succ_pos j)
  have h00 : J c2 ![0, 0] = 1 / qFactor c2 ![0, 0] ^ 2 := by
    rw [J]
    have hz : (![0, 0] : Fin 2 → ℕ) = 0 := by ext i; fin_cases i <;> rfl
    norm_num [qFactor, Fin.prod_univ_two, hz]
  have h10 : J c2 ![1, 0] =
      (1) / qFactor c2 ![1, 0] ^ 2 := by
    rw [J]
    norm_num [box_sum, dite_eq_ite, Pi.le_def, Fin.forall_fin_two, Pi.sub_apply, Finset.sum_range_succ, h00]
    simp only [quad_c2]
    norm_num [Finset.prod_range_succ, c2, qFactor, Fin.prod_univ_two]
    field_simp [nz1, nz 2 (by decide), nz 4 (by decide),
      nz 5 (by decide), nz 8 (by decide)]
  have h01 : J c2 ![0, 1] =
      (1) / qFactor c2 ![0, 1] ^ 2 := by
    rw [J]
    norm_num [box_sum, dite_eq_ite, Pi.le_def, Fin.forall_fin_two, Pi.sub_apply, Finset.sum_range_succ, h00, h10]
    simp only [quad_c2]
    norm_num [Finset.prod_range_succ, c2, qFactor, Fin.prod_univ_two]
    field_simp [nz1, nz 2 (by decide), nz 4 (by decide),
      nz 5 (by decide), nz 8 (by decide)]
  have h20 : J c2 ![2, 0] =
      (1) / qFactor c2 ![2, 0] ^ 2 := by
    rw [J]
    norm_num [box_sum, dite_eq_ite, Pi.le_def, Fin.forall_fin_two, Pi.sub_apply, Finset.sum_range_succ, h00, h10, h01]
    simp only [quad_c2]
    norm_num [Finset.prod_range_succ, c2, qFactor, Fin.prod_univ_two]
    field_simp [nz1, nz 2 (by decide), nz 4 (by decide),
      nz 5 (by decide), nz 8 (by decide)]
    ring
  have h11 : J c2 ![1, 1] =
      (1 + RatFunc.X + RatFunc.X ^ 2) / qFactor c2 ![1, 1] ^ 2 := by
    rw [J]
    norm_num [box_sum, dite_eq_ite, Pi.le_def, Fin.forall_fin_two, Pi.sub_apply, Finset.sum_range_succ, h00, h10, h01, h20]
    simp only [quad_c2]
    norm_num [Finset.prod_range_succ, c2, qFactor, Fin.prod_univ_two]
    field_simp [nz1, nz 2 (by decide), nz 4 (by decide),
      nz 5 (by decide), nz 8 (by decide)]
    ring
  have h02 : J c2 ![0, 2] =
      (1) / qFactor c2 ![0, 2] ^ 2 := by
    rw [J]
    norm_num [box_sum, dite_eq_ite, Pi.le_def, Fin.forall_fin_two, Pi.sub_apply, Finset.sum_range_succ, h00, h10, h01, h20, h11]
    simp only [quad_c2]
    norm_num [Finset.prod_range_succ, c2, qFactor, Fin.prod_univ_two]
    field_simp [nz1, nz 2 (by decide), nz 4 (by decide),
      nz 5 (by decide), nz 8 (by decide)]
    ring
  have h21 : J c2 ![2, 1] =
      (1 + RatFunc.X + 3 * RatFunc.X ^ 2 + RatFunc.X ^ 3 + RatFunc.X ^ 4) / qFactor c2 ![2, 1] ^ 2 := by
    rw [J]
    norm_num [box_sum, dite_eq_ite, Pi.le_def, Fin.forall_fin_two, Pi.sub_apply, Finset.sum_range_succ,
      h00, h10, h01, h20, h11, h02]
    simp only [quad_c2]
    norm_num [Finset.prod_range_succ, c2, qFactor, Fin.prod_univ_two]
    field_simp [nz1, nz 2 (by decide), nz 4 (by decide),
      nz 5 (by decide), nz 8 (by decide)]
    ring
  have h12 : J c2 ![1, 2] =
      (1 + RatFunc.X + RatFunc.X ^ 2 + RatFunc.X ^ 3 + RatFunc.X ^ 4) / qFactor c2 ![1, 2] ^ 2 := by
    rw [J]
    norm_num [box_sum, dite_eq_ite, Pi.le_def, Fin.forall_fin_two, Pi.sub_apply, Finset.sum_range_succ,
      h00, h10, h01, h20, h11, h02, h21]
    simp only [quad_c2]
    norm_num [Finset.prod_range_succ, c2, qFactor, Fin.prod_univ_two]
    field_simp [nz1, nz 2 (by decide), nz 4 (by decide),
      nz 5 (by decide), nz 8 (by decide)]
    ring
  have h22 : J c2 ![2, 2] =
      (1 + RatFunc.X + 3 * RatFunc.X ^ 2 + 2 * RatFunc.X ^ 3 +
      5 * RatFunc.X ^ 4 + 2 * RatFunc.X ^ 5 + 3 * RatFunc.X ^ 6 +
      RatFunc.X ^ 7 + RatFunc.X ^ 8) / qFactor c2 ![2, 2] ^ 2 := by
    rw [J]
    norm_num [box_sum, dite_eq_ite, Pi.le_def, Fin.forall_fin_two, Pi.sub_apply, Finset.sum_range_succ,
      h00, h10, h01, h20, h11, h02, h21, h12]
    simp only [quad_c2]
    norm_num [Finset.prod_range_succ, c2, qFactor, Fin.prod_univ_two]
    field_simp [nz1, nz 2 (by decide), nz 4 (by decide),
      nz 5 (by decide), nz 8 (by decide)]
    ring
  let P : ℚ[X] :=
    1 + Polynomial.X + 3 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 +
      5 * Polynomial.X ^ 4 + 2 * Polynomial.X ^ 5 + 3 * Polynomial.X ^ 6 +
      Polynomial.X ^ 7 + Polynomial.X ^ 8
  have map_P : algebraMap ℚ[X] (RatFunc ℚ) P =
      1 + RatFunc.X + 3 * RatFunc.X ^ 2 + 2 * RatFunc.X ^ 3 +
      5 * RatFunc.X ^ 4 + 2 * RatFunc.X ^ 5 + 3 * RatFunc.X ^ 6 +
      RatFunc.X ^ 7 + RatFunc.X ^ 8 := by
    norm_num [P, RatFunc.algebraMap_X, map_ofNat]
  intro h
  obtain ⟨p, hp, m, hmdeg, hinc, hdec⟩ := h 2 c2 ![2, 2]
  have hp_eq : p = P := by
    apply RatFunc.algebraMap_injective ℚ
    rw [hp, h22, ← map_P]
    field_simp [factor_nz ![2, 2]]
  rw [hp_eq] at hinc hdec
  have hdegree : 4 ≤ P.natDegree := by
    apply Polynomial.le_natDegree_of_ne_zero
    norm_num [P, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
      Polynomial.coeff_X_pow]
  by_cases hm : m ≤ 2
  · have := hdec 3 (by omega) (by omega)
    norm_num [P, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
      Polynomial.coeff_X_pow] at this
  · have := hinc 2 (by omega)
    norm_num [P, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
      Polynomial.coeff_X_pow] at this

#print axioms result

end D5.S0.Certificates.Combinatorics.TodaSpecializationUnimodalityRefutation
