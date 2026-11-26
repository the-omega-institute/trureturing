/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteWeightedMinors
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteWeightedMinors
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.RingTheory.MvPolynomial.EulerIdentity]
   utility: none
   digest: Weighted degree seventy-five of the five-site residual Jacobian minors. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteLineMinors
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! Removing a trace column from the Jacobian gives weight 75. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteWeightedMinors

open MvPolynomial Matrix PeriodicMPSFiveSiteCoordinates PeriodicMPSFiveSiteLineMinors
open scoped BigOperators

noncomputable section

abbrev P := MvPolynomial (Fin 10) ℤ

/-- Trace variables have weight one. Determinants and mixed traces have weight two. -/
def weights : Fin 10 → ℕ := ![1, 1, 2, 2, 2, 1, 1, 2, 2, 2]

private abbrev H (p : P) (n : ℕ) := p.IsWeightedHomogeneous weights n

private lemma hNat (n : ℕ) : H n 0 := by
  simpa using (isWeightedHomogeneous_C weights (n : ℤ))

private theorem coordinates_weight (t s d e k : P)
    (ht : H t 1) (hs : H s 1) (hd : H d 2) (he : H e 2) (hk : H k 2)
    (i : Fin 8) : H (coordinates t s d e k i) 5 := by
  fin_cases i
  · exact ((ht.pow 5).sub (((hNat 5).mul hd).mul (ht.pow 3))).add
      (((hNat 5).mul (hd.pow 2)).mul ht)
  · exact (((ht.pow 3).sub (((hNat 2).mul hd).mul ht)).mul hk).add
      (((hd.pow 2).sub (hd.mul (ht.pow 2))).mul hs)
  · have h₁ := (hs.mul ((ht.pow 2).sub hd)).mul hk
    have h₂ := he.mul (ht.pow 3)
    have h₃ := (hd.mul (hs.pow 2)).mul ht
    have h₄ := (((hNat 3).mul hd).mul he).mul ht
    exact ((h₁.sub h₂).sub h₃).add h₄
  · exact ((ht.mul (hk.pow 2)).sub ((hd.mul hs).mul hk)).sub ((hd.mul he).mul ht)
  · have h₁ := (((hs.pow 2).sub he).mul hk).mul ht
    have h₂ := hd.mul (hs.pow 3)
    have h₃ := (hs.mul he).mul (ht.pow 2)
    have h₄ := (((hNat 3).mul hs).mul hd).mul he
    exact ((h₁.sub h₂).sub h₃).add h₄
  · exact ((hs.mul (hk.pow 2)).sub ((he.mul hk).mul ht)).sub ((hd.mul he).mul hs)
  · have h₁ := ((hs.pow 3).sub (((hNat 2).mul hs).mul he)).mul hk
    exact (h₁.add ((he.pow 2).mul ht)).sub (((hs.pow 2).mul he).mul ht)
  · exact ((hs.pow 5).sub (((hNat 5).mul he).mul (hs.pow 3))).add
      (((hNat 5).mul (he.pow 2)).mul hs)

private lemma flatten_weight (p : Fin 8 → P) (hp : ∀ i, H (p i) 5)
    (i : Fin 4) (j : Fin 8) : H (flatten p i j) 5 := by
  fin_cases i <;> fin_cases j <;> exact hp _

/-- The raw observed entries are weighted homogeneous of degree ten. -/
theorem observation_weight (i : Fin 10) : H (observation (R := P) X i) 10 := by
  classical
  unfold observation
  apply IsWeightedHomogeneous.sum
  intro j _
  exact (flatten_weight _ hp₁ _ _).mul (flatten_weight _ hp₂ _ _)
where
  hp₁ : ∀ k, H (coordinates (X 0) (X 1) (X 2) (X 3) (X 4) k) 5 :=
    coordinates_weight _ _ _ _ _
      (isWeightedHomogeneous_X ℤ weights 0) (isWeightedHomogeneous_X ℤ weights 1)
      (isWeightedHomogeneous_X ℤ weights 2) (isWeightedHomogeneous_X ℤ weights 3)
      (isWeightedHomogeneous_X ℤ weights 4)
  hp₂ : ∀ k, H (coordinates (X 5) (X 6) (X 7) (X 8) (X 9) k) 5 :=
    coordinates_weight _ _ _ _ _
      (isWeightedHomogeneous_X ℤ weights 5) (isWeightedHomogeneous_X ℤ weights 6)
      (isWeightedHomogeneous_X ℤ weights 7) (isWeightedHomogeneous_X ℤ weights 8)
      (isWeightedHomogeneous_X ℤ weights 9)

private theorem weight_le_two (j : Fin 10) : weights j ≤ 2 := by
  fin_cases j <;> decide

/-- Every column of the observation derivative has a fixed weight. -/
theorem derivative_weight (i j : Fin 10) :
    H (pderiv j (observation (R := P) X i)) (10 - weights j) := by
  exact (observation_weight i).pderiv (Nat.sub_add_cancel ((weight_le_two j).trans (by decide)))

/-- The symbolic residual cofactor before restriction to a line. -/
def symbolicMinor (k : Fin 10) : P :=
  (Matrix.of fun i j : Fin 9 =>
    pderiv (k.succAbove j) (observation (R := P) X (k.succAbove i))).det

private lemma weight_sum (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    ∑ j : Fin 9, (10 - weights (k.succAbove j)) = 75 := by
  rcases hk with rfl | rfl <;> decide

/-- Deleting the column of either selected trace variable leaves weight 75. -/
theorem symbolicMinor_weight (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    H (symbolicMinor k) 75 := by
  classical
  rw [symbolicMinor, Matrix.det_apply, ← weight_sum k hk]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have h := IsWeightedHomogeneous.prod Finset.univ
    (fun j : Fin 9 => pderiv (k.succAbove j)
      (observation (R := P) X (k.succAbove (σ j))))
    (fun j => 10 - weights (k.succAbove j))
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

/-- Evaluating a symbolic minor on the prescribed line yields degree at most 75. -/
theorem line_degree_bound {R : Type*} [CommRing R] (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    ((symbolicMinor k).eval₂ (Int.castRingHom (Polynomial R))
      (line (Polynomial.X : Polynomial R))).natDegree ≤ 75 :=
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

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteWeightedMinors
