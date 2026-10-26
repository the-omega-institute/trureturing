/- GID: D5/S3/Observer/Linear/GainRayMixedGeometry
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayMixedGeometry
   mirror-E: none(waiver:distinct-clock-diagonal-rigidity)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Lagrange]
   utility: none
   digest: Diagonal preservation of bounded-degree evaluations forces a scalar diagonal beyond the coefficient dimension. -/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Real.Basic

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace D5.S3.Observer.Linear.GainRay

/-- Zero diagonal entries are included; the conclusion needs no invertibility of a. -/
theorem diagonal_evaluation_rigid (d n : ℕ) (hn : d+2 ≤ n)
    (t : Fin n → ℝ) (ht : Function.Injective t) (a : Fin n → ℝ)
    (h : ∀ p : Polynomial ℝ, p.natDegree ≤ d →
      ∃ q : Polynomial ℝ, q.natDegree ≤ d ∧ ∀ i, q.eval (t i) = a i * p.eval (t i)) :
    ∀ i j, a i = a j := by
  classical
  intro i j
  by_cases hij : i = j
  · exact congrArg a hij
  let U : Finset (Fin n) := (Finset.univ.erase i).erase j
  have hU : U.card = n-2 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem (by simp [Ne.symm hij]),
      Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
    omega
  obtain ⟨K, hKU, hK⟩ := Finset.exists_subset_card_eq
    (show d ≤ U.card by rw [hU]; omega)
  have hni : i ∉ K := fun hi => (by simpa [U] using hKU hi : False)
  have hnj : j ∉ K := fun hj => (by simpa [U] using hKU hj : False)
  let p : Polynomial ℝ := ∏ k ∈ K, (Polynomial.X - Polynomial.C (t k))
  have hp : p.natDegree ≤ d := by
    simp [p, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, hK]
  have hpzero (k : Fin n) (hk : k ∈ K) : p.eval (t k) = 0 := by
    simp only [p, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero hk (sub_self _)
  obtain ⟨q,hq,hqe⟩ := h p hp
  have he : q = a i • p := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq q (a i • p)
      (f := fun k : ↥(insert i K : Finset (Fin n)) => t k.1) (ht.comp Subtype.val_injective)
    · intro k
      rw [hqe, Polynomial.eval_smul]
      rcases Finset.mem_insert.mp k.2 with hk | hk
      · simp [hk]
      · simp [hpzero _ hk]
    · have hs : (a i • p).natDegree ≤ d := (Polynomial.natDegree_smul_le _ _).trans hp
      have hc : Fintype.card ↥(insert i K : Finset (Fin n)) = d+1 := by
        rw [Fintype.card_coe, Finset.card_insert_of_notMem hni, hK]
      rw [hc]
      omega
  have hpj : p.eval (t j) ≠ 0 := by
    simp only [p, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply sub_ne_zero.mpr
    intro he
    exact hnj (ht he ▸ hk)
  have heval := congrArg (fun f : Polynomial ℝ => f.eval (t j)) he
  rw [hqe, Polynomial.eval_smul] at heval
  exact (mul_right_cancel₀ hpj heval).symm

#print axioms diagonal_evaluation_rigid
end D5.S3.Observer.Linear.GainRay
