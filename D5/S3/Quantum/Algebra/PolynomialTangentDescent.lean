/- GID: D5/S3/Quantum/Algebra/PolynomialTangentDescent
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PolynomialTangentDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A polynomial has gradient parallel to a nonzero vector exactly when it depends on the associated linear form. -/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Algebra.PolynomialTangentDescent

open MvPolynomial

variable {K sigma : Type*} [Field K]

section Elimination

variable [CharZero K]

private theorem notMem_vars_of_pderiv_eq_zero
    (q : MvPolynomial sigma K) (i : sigma) (h : pderiv i q = 0) :
    i ∉ q.vars := by
  classical
  intro hi
  obtain ⟨a, ha, hai⟩ := (mem_vars_iff_mem_support i).mp hi
  have hai' : a i ≠ 0 := Finsupp.mem_support_iff.mp hai
  let d : sigma →₀ ℕ := a - Finsupp.single i 1
  -- A derivative coefficient has one possible preimage exponent.
  have hc := congrArg (coeff (a - Finsupp.single i 1)) h
  rw [coeff_pderiv, Finsupp.sub_add_single_one_cancel hai', coeff_zero] at hc
  have hn : (d i : K) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (d i)
  exact (mem_support_iff.mp ha) ((mul_eq_zero.mp hc).resolve_right hn)

private theorem exists_aeval_axis_of_pderiv_eq_zero
    (q : MvPolynomial sigma K) (j : sigma)
    (h : ∀ i, i ≠ j → pderiv i q = 0) :
    ∃ F : Polynomial K, q = Polynomial.aeval (X j : MvPolynomial sigma K) F := by
  classical
  refine ⟨MvPolynomial.aeval (fun i => if i = j then Polynomial.X else 0) q, ?_⟩
  have hv : (q.vars : Set sigma) ⊆ {j} := by
    intro i hi
    by_contra hij
    exact notMem_vars_of_pderiv_eq_zero q i (h i hij) hi
  have he :
      (Polynomial.aeval (X j : MvPolynomial sigma K)).comp
        (MvPolynomial.aeval (fun i => if i = j then (Polynomial.X : Polynomial K) else 0)) =
      MvPolynomial.aeval (fun i => if i ∈ ({j} : Set sigma) then
        (X i : MvPolynomial sigma K) else 0) := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i = j <;> simp [hi]
  exact (aeval_ite_mem_eq_self q hv).symm.trans (AlgHom.congr_fun he q).symm

end Elimination

section Pivot

variable [Fintype sigma]

private def linearForm (c : sigma → K) : MvPolynomial sigma K :=
  ∑ i, c i • X i

private def tailForm (c : sigma → K) (j : sigma) : MvPolynomial sigma K := by
  classical
  exact ∑ i ∈ Finset.univ.erase j, c i • X i

private def pivotSub (c : sigma → K) (j : sigma) :
    MvPolynomial sigma K →ₐ[K] MvPolynomial sigma K := by
  classical
  exact MvPolynomial.aeval (fun i =>
    if i = j then (c j)⁻¹ • (X j - tailForm c j) else X i)

private def pivotInv (c : sigma → K) (j : sigma) :
    MvPolynomial sigma K →ₐ[K] MvPolynomial sigma K := by
  classical
  exact MvPolynomial.aeval (fun i => if i = j then linearForm c else X i)

private theorem linearForm_eq (c : sigma → K) (j : sigma) :
    linearForm c = c j • X j + tailForm c j := by
  classical
  exact (Finset.add_sum_erase Finset.univ (fun i => c i • (X i : MvPolynomial sigma K))
    (Finset.mem_univ j)).symm

private theorem pivotInv_tail (c : sigma → K) (j : sigma) :
    pivotInv c j (tailForm c j) = tailForm c j := by
  classical
  simp only [tailForm, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  simp [pivotInv, (Finset.mem_erase.mp hi).1]

private theorem pderiv_linearForm (c : sigma → K) (i : sigma) :
    pderiv i (linearForm c) = C (c i) := by
  classical
  simp [linearForm, map_sum, pderiv_X, Pi.single_apply,
    smul_eq_C_mul]

private theorem pderiv_tailForm (c : sigma → K) (j i : sigma) (hij : i ≠ j) :
    pderiv i (tailForm c j) = C (c i) := by
  classical
  simp [tailForm, map_sum, pderiv_X, Pi.single_apply, hij,
    smul_eq_C_mul]

private theorem pivotInv_comp_pivotSub (c : sigma → K) (j : sigma) (hj : c j ≠ 0) :
    (pivotInv c j).comp (pivotSub c j) = AlgHom.id K (MvPolynomial sigma K) := by
  classical
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : i = j
  · subst i
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [show pivotSub c j (X j) = (c j)⁻¹ • (X j - tailForm c j) by
      simp [pivotSub]]
    rw [map_smul, map_sub, pivotInv_tail]
    have hx : pivotInv c j (X j) = linearForm c := by simp [pivotInv]
    rw [hx, linearForm_eq c j]
    simp [smul_smul, hj]
  · simp [pivotInv, pivotSub, hi]

private theorem pderiv_pivotSub_X
    (c : sigma → K) (j i : sigma) (hij : i ≠ j) (k : sigma) :
    pderiv i (pivotSub c j (X k)) =
      pivotSub c j (pderiv i (X k) - (c i / c j) • pderiv j (X k)) := by
  classical
  by_cases hk : k = j
  · subst k
    rw [show pivotSub c j (X j) = (c j)⁻¹ • (X j - tailForm c j) by
      simp [pivotSub]]
    rw [Derivation.map_smul, map_sub, pderiv_X_of_ne hij.symm,
      pderiv_tailForm c j i hij, pderiv_X_self]
    simp [smul_eq_C_mul, div_eq_mul_inv, mul_comm]
  · by_cases hki : k = i
    · subst k
      simp [pivotSub, hij, pderiv_X_of_ne hij]
    · simp [pivotSub, hk, pderiv_X_of_ne hki]

private theorem pderiv_pivotSub
    (c : sigma → K) (j i : sigma) (hij : i ≠ j) (p : MvPolynomial sigma K) :
    pderiv i (pivotSub c j p) =
      pivotSub c j (pderiv i p - (c i / c j) • pderiv j p) := by
  classical
  -- Both sides obey the product rule with factors transported through pivotSub.
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, map_sub, map_smul, smul_add]
    abel
  | mul_X p k hp =>
    rw [map_mul, pderiv_mul, hp, pderiv_pivotSub_X c j i hij k]
    simp only [pderiv_mul, map_sub, map_add, map_mul, smul_eq_C_mul]
    ring

end Pivot

variable [CharZero K] [Fintype sigma]

private theorem exists_aeval_of_pivot
    (c : sigma → K) (j : sigma) (hj : c j ≠ 0) (p : MvPolynomial sigma K)
    (hgrad : ∀ i, c j • pderiv i p = c i • pderiv j p) :
    ∃ F : Polynomial K, p = Polynomial.aeval (linearForm c) F := by
  have hz : ∀ i, i ≠ j → pderiv i (pivotSub c j p) = 0 := by
    intro i hij
    rw [pderiv_pivotSub c j i hij]
    have hd : pderiv i p = (c i / c j) • pderiv j p := by
      have he := congrArg (fun q : MvPolynomial sigma K => (c j)⁻¹ • q) (hgrad i)
      simpa [smul_smul, hj, div_eq_mul_inv, mul_comm] using he
    rw [hd, sub_self, map_zero]
  obtain ⟨F, hF⟩ := exists_aeval_axis_of_pderiv_eq_zero (pivotSub c j p) j hz
  refine ⟨F, ?_⟩
  calc
    p = pivotInv c j (pivotSub c j p) :=
      (AlgHom.congr_fun (pivotInv_comp_pivotSub c j hj) p).symm
    _ = pivotInv c j (Polynomial.aeval (X j) F) := congrArg (pivotInv c j) hF
    _ = Polynomial.aeval (linearForm c) F := by
      rw [← Polynomial.aeval_algHom_apply]
      simp [pivotInv]

/-- A polynomial has gradient parallel to a fixed nonzero coefficient vector exactly
when it is a univariate polynomial in the associated homogeneous linear form. -/
theorem tangent_descent
    (c : sigma → K) (hc : c ≠ 0) (p : MvPolynomial sigma K) :
    (∀ i j, c j • MvPolynomial.pderiv i p = c i • MvPolynomial.pderiv j p) ↔
    ∃ F : Polynomial K,
      p = Polynomial.aeval
        (∑ i, c i • (MvPolynomial.X i : MvPolynomial sigma K)) F := by
  constructor
  · intro hgrad
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
      by_contra h
      apply hc
      funext j
      simpa using (not_exists.mp h j)
    exact exists_aeval_of_pivot c j hj p (fun i => hgrad i j)
  · rintro ⟨F, rfl⟩ i j
    change c j • pderiv i (Polynomial.aeval (linearForm c) F) =
      c i • pderiv j (Polynomial.aeval (linearForm c) F)
    rw [Derivation.map_aeval, Derivation.map_aeval, pderiv_linearForm, pderiv_linearForm]
    simp only [smul_eq_mul, smul_eq_C_mul]
    ring

end D5.S3.Quantum.Algebra.PolynomialTangentDescent
