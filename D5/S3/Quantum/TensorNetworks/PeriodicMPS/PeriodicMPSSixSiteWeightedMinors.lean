/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteWeightedMinors
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteWeightedMinors
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.RingTheory.MvPolynomial.EulerIdentity]
   utility: none
   digest: Weighted degree ninety-three of the six-site residual Jacobian minors. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteLineMinors
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! Removing a trace column from the Jacobian gives weight 93. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteWeightedMinors

open MvPolynomial Matrix PeriodicMPSSixSiteCoordinates PeriodicMPSSixSiteLineMinors
open PeriodicMPSSixSiteMarginal (flatten)
open PeriodicMPSFiveSiteLineMinors (line)
open scoped BigOperators

noncomputable section

abbrev P := MvPolynomial (Fin 10) ℤ

/-- Trace variables have weight one. Determinants and mixed traces have weight two. -/
def weights : Fin 10 → ℕ := ![1, 1, 2, 2, 2, 1, 1, 2, 2, 2]

private abbrev H (p : P) (n : ℕ) := p.IsWeightedHomogeneous weights n

private lemma hNat (n : ℕ) : H n 0 := by
  simpa using (isWeightedHomogeneous_C weights (n : ℤ))

set_option maxHeartbeats 1200000 in
-- Verify the weights of the fourteen cubic coordinate polynomials.
private theorem coordinates_weight (T S U d e k : P)
    (hT : H T 2) (hS : H S 2) (hU : H U 2) (hd : H d 2) (he : H e 2) (hk : H k 2)
    (i : Fin 14) : H (coordinates T S U d e k i) 6 := by
  fin_cases i
  · exact ((((hT).pow 3).sub ((((hNat 6)).mul ((hT).pow 2)).mul (hd))).add ((((hNat 9)).mul
      (hT)).mul ((hd).pow 2))).sub (((hNat 2)).mul ((hd).pow 3))
  · exact (((((((hS).neg).mul (hT)).mul (hd)).add ((((hNat 2)).mul (hS)).mul ((hd).pow 2))).add
      (((hT).pow 2).mul (hk))).sub (((((hNat 3)).mul (hT)).mul (hd)).mul (hk))).add
      (((hd).pow 2).mul (hk))
  · exact ((((((((hS).mul (hT)).mul (hk)).sub (((((hNat 2)).mul (hS)).mul (hd)).mul (hk))).sub
      (((hT).pow 2).mul (he))).sub (((hT).mul (hU)).mul (hd))).add (((((hNat 4)).mul
      (hT)).mul (hd)).mul (he))).add ((hU).mul ((hd).pow 2))).sub ((((hNat 2)).mul ((hd).pow
      2)).mul (he))
  · exact (((((((hS).neg).mul (hd)).mul (hk)).sub (((hT).mul (hd)).mul (he))).add ((hT).mul
      ((hk).pow 2))).add ((((hNat 2)).mul ((hd).pow 2)).mul (he))).sub ((hd).mul ((hk).pow
      2))
  · exact (((((((((hS).neg).mul (hT)).mul (he)).sub (((hS).mul (hU)).mul (hd))).add (((((hNat
      4)).mul (hS)).mul (hd)).mul (he))).add (((hT).mul (hU)).mul (hk))).sub (((hT).mul
      (he)).mul (hk))).sub (((hU).mul (hd)).mul (hk))).add (((hd).mul (he)).mul (hk))
  · exact ((((((((hNat 2)).neg).mul (hS)).mul (hd)).mul (hk)).add ((hT).mul ((hk).pow 2))).add
      ((hU).mul ((hd).pow 2))).sub ((((hNat 2)).mul ((hd).pow 2)).mul (he))
  · exact ((((hS).mul ((hk).pow 2)).sub (((hT).mul (he)).mul (hk))).sub (((hU).mul (hd)).mul
      (hk))).add (((hd).mul (he)).mul (hk))
  · exact ((((hS).mul ((hk).pow 2)).sub (((hT).mul (he)).mul (hk))).sub (((hU).mul (hd)).mul
      (hk))).add (((hd).mul (he)).mul (hk))
  · exact ((((((((hS).mul (hU)).mul (hk)).sub (((((hNat 2)).mul (hS)).mul (he)).mul (hk))).sub
      (((hT).mul (hU)).mul (he))).add ((hT).mul ((he).pow 2))).sub (((hU).pow 2).mul
      (hd))).add (((((hNat 4)).mul (hU)).mul (hd)).mul (he))).sub ((((hNat 2)).mul (hd)).mul
      ((he).pow 2))
  · exact ((((((hNat 3)).neg).mul (hd)).mul (he)).mul (hk)).add ((hk).pow 3)
  · exact (((((((hS).neg).mul (he)).mul (hk)).sub (((hU).mul (hd)).mul (he))).add ((hU).mul
      ((hk).pow 2))).add ((((hNat 2)).mul (hd)).mul ((he).pow 2))).sub ((he).mul ((hk).pow
      2))
  · exact ((((((((hNat 2)).neg).mul (hS)).mul (he)).mul (hk)).add ((hT).mul ((he).pow 2))).add
      ((hU).mul ((hk).pow 2))).sub ((((hNat 2)).mul (hd)).mul ((he).pow 2))
  · exact (((((((hS).neg).mul (hU)).mul (he)).add ((((hNat 2)).mul (hS)).mul ((he).pow 2))).add
      (((hU).pow 2).mul (hk))).sub (((((hNat 3)).mul (hU)).mul (he)).mul (hk))).add
      (((he).pow 2).mul (hk))
  · exact ((((hU).pow 3).sub ((((hNat 6)).mul ((hU).pow 2)).mul (he))).add ((((hNat 9)).mul
      (hU)).mul ((he).pow 2))).sub (((hNat 2)).mul ((he).pow 3))

/-- Each entry of the complexified observation has weighted degree twelve. -/
theorem observation_weight (i : Fin 10) : H (observation (R := P) X i) 12 := by
  classical
  unfold observation
  apply IsWeightedHomogeneous.sum
  intro j _
  exact (hp₁ _).mul (hp₂ _)
where
  hp₁ : ∀ k, H (coordinates (X 0 ^ 2) (X 0 * X 1) (X 1 ^ 2) (X 2) (X 3) (X 4) k) 6 :=
    coordinates_weight _ _ _ _ _ _
      ((isWeightedHomogeneous_X ℤ weights 0).pow 2)
      ((isWeightedHomogeneous_X ℤ weights 0).mul (isWeightedHomogeneous_X ℤ weights 1))
      ((isWeightedHomogeneous_X ℤ weights 1).pow 2)
      (isWeightedHomogeneous_X ℤ weights 2) (isWeightedHomogeneous_X ℤ weights 3)
      (isWeightedHomogeneous_X ℤ weights 4)
  hp₂ : ∀ k, H (coordinates (X 5 ^ 2) (X 5 * X 6) (X 6 ^ 2) (X 7) (X 8) (X 9) k) 6 :=
    coordinates_weight _ _ _ _ _ _
      ((isWeightedHomogeneous_X ℤ weights 5).pow 2)
      ((isWeightedHomogeneous_X ℤ weights 5).mul (isWeightedHomogeneous_X ℤ weights 6))
      ((isWeightedHomogeneous_X ℤ weights 6).pow 2)
      (isWeightedHomogeneous_X ℤ weights 7) (isWeightedHomogeneous_X ℤ weights 8)
      (isWeightedHomogeneous_X ℤ weights 9)

private theorem weight_le_two (j : Fin 10) : weights j ≤ 2 := by
  fin_cases j <;> decide

/-- Every column of the observation derivative has a fixed weight. -/
theorem derivative_weight (i j : Fin 10) :
    H (pderiv j (observation (R := P) X i)) (12 - weights j) := by
  exact (observation_weight i).pderiv (Nat.sub_add_cancel ((weight_le_two j).trans (by decide)))

/-- The symbolic residual cofactor before restriction to a line. -/
def symbolicMinor (k : Fin 10) : P :=
  (Matrix.of fun i j : Fin 9 =>
    pderiv (k.succAbove j) (observation (R := P) X (k.succAbove i))).det

private lemma weight_sum (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    ∑ j : Fin 9, (12 - weights (k.succAbove j)) = 93 := by
  rcases hk with rfl | rfl <;> decide

/-- Deleting the column of either selected trace variable leaves weight 93. -/
theorem symbolicMinor_weight (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    H (symbolicMinor k) 93 := by
  classical
  rw [symbolicMinor, Matrix.det_apply, ← weight_sum k hk]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have h := IsWeightedHomogeneous.prod Finset.univ
    (fun j : Fin 9 => pderiv (k.succAbove j)
      (observation (R := P) X (k.succAbove (σ j))))
    (fun j => 12 - weights (k.succAbove j))
    (fun j _ => derivative_weight _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using h
  · simpa [hs, Units.neg_smul] using h.neg

private lemma natDegree_substitution {R : Type*} [CommRing R] (q : P) (n : ℕ)
    (h : H q n) (a : Fin 10 → Polynomial R)
    (ha : ∀ j, (a j).natDegree ≤ weights j) :
    (q.eval₂ (Int.castRingHom (Polynomial R)) a).natDegree ≤ n := by
  classical
  rw [MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  have hdw := h (MvPolynomial.mem_support_iff.mp hd)
  rw [Finsupp.weight_eq_sum] at hdw
  calc
    _ ≤ (∏ j, a j ^ d j).natDegree := by
      simpa using (Polynomial.natDegree_mul_le (p := Int.castRingHom (Polynomial R) (q.coeff d))
        (q := ∏ j, a j ^ d j))
    _ ≤ ∑ j : Fin 10, (a j ^ d j).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ j : Fin 10, d j * weights j := Finset.sum_le_sum fun j _ =>
      Polynomial.natDegree_pow_le_of_le _ (ha j)
    _ = n := hdw

private lemma degree_line {R : Type*} [CommRing R] (j : Fin 10) :
    (line (Polynomial.X : Polynomial R) j).natDegree ≤ weights j := by
  unfold line
  have h (a b : ℤ) :
      ((a : Polynomial R) + (b : Polynomial R) * Polynomial.X).natDegree ≤ 1 := by
    have hm : ((b : Polynomial R) * Polynomial.X).natDegree ≤ 1 := by
      exact (Polynomial.natDegree_mul_le.trans (by
        simpa using (Polynomial.natDegree_X_le (R := R))))
    simpa using Polynomial.natDegree_add_le_of_le
      (show (a : Polynomial R).natDegree ≤ 0 by simp) hm
  split
  · rename_i hj
    have hw : weights j = 1 := by
      rcases hj with rfl | rfl | rfl | rfl <;> rfl
    exact hw ▸ h _ _
  · rename_i hj
    have hw : weights j = 2 := by
      fin_cases j <;> simp_all [weights]
    rw [hw]
    exact Polynomial.natDegree_pow_le_of_le 2 (h _ _)

/-- Evaluating a symbolic minor on the prescribed line yields degree at most 93. -/
theorem line_degree_bound {R : Type*} [CommRing R] (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    ((symbolicMinor k).eval₂ (Int.castRingHom (Polynomial R))
      (line (Polynomial.X : Polynomial R))).natDegree ≤ 93 :=
  natDegree_substitution _ _ (symbolicMinor_weight k hk) _ degree_line

private lemma eval_dual_derivative {R : Type*} [CommRing R] (q : P)
    (a : Fin 10 → R) (j : Fin 10) :
    let b : Fin 10 → DualNumber R := fun k => ⟨a k, if k = j then 1 else 0⟩
    let v := q.eval₂ (Int.castRingHom (DualNumber R)) b
    v.fst = q.eval₂ (Int.castRingHom R) a ∧
      v.snd = (pderiv j q).eval₂ (Int.castRingHom R) a := by
  let b : Fin 10 → DualNumber R := fun k => ⟨a k, if k = j then 1 else 0⟩
  let F := MvPolynomial.eval₂Hom (Int.castRingHom (DualNumber R)) b
  let G := MvPolynomial.eval₂Hom (Int.castRingHom R) a
  change (F q).fst = G q ∧ (F q).snd = G (pderiv j q)
  induction q using MvPolynomial.induction_on with
  | C c =>
    simp [F, G, TrivSqZeroExt.fst_intCast, TrivSqZeroExt.snd_intCast]
  | add p q hp hq =>
    simp only [map_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, hp.1, hq.1,
      hp.2, hq.2, and_self]
  | mul_X p k hp =>
    have hF : F (X k) = b k := by simp [F]
    have hG : G (X k) = a k := by simp [G]
    constructor
    · simp only [map_mul, TrivSqZeroExt.fst_mul, hF, hG, hp.1]
      rfl
    · rw [map_mul, hF, pderiv_mul, map_add, map_mul, map_mul, hG, TrivSqZeroExt.snd_mul,
        hp.1, hp.2]
      change G p * (if k = j then 1 else 0) + G (pderiv j p) * a k =
        G (pderiv j p) * a k + G p * G (pderiv j (X k))
      by_cases h : k = j
      · subst k
        simp [b, pderiv_X, smul_eq_mul, mul_comm, add_comm]
      · simp [b, pderiv_X, h, smul_eq_mul, mul_comm, add_comm]

/-- The dual-number computation agrees with coefficientwise formal differentiation. -/
theorem evaluated_derivative {R : Type*} [CommRing R] (a : Fin 10 → R) (i j : Fin 10) :
    (pderiv j (observation (R := P) X i)).eval₂ (Int.castRingHom R) a = jacobian a i j := by
  let b : Fin 10 → DualNumber R := fun k => ⟨a k, if k = j then 1 else 0⟩
  let F := MvPolynomial.eval₂Hom (Int.castRingHom (DualNumber R)) b
  have h : F ∘ (X : Fin 10 → P) = b := by
    funext k
    exact MvPolynomial.eval₂Hom_X' _ _ _
  have he := map_observation F (X : Fin 10 → P) i
  rw [h] at he
  exact (eval_dual_derivative (observation (R := P) X i) a j).2.symm.trans
    (congrArg TrivSqZeroExt.snd he)

theorem evaluated_symbolicMinor {R : Type*} [CommRing R] (x : R) (k : Fin 10) :
    (symbolicMinor k).eval₂ (Int.castRingHom R) (line x) = residualMinor x k := by
  let F := MvPolynomial.eval₂Hom (Int.castRingHom R) (line x)
  change F (symbolicMinor k) = _
  rw [symbolicMinor, RingHom.map_det, residualMinor]
  congr 1
  ext i j
  exact evaluated_derivative _ _ _

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteWeightedMinors
