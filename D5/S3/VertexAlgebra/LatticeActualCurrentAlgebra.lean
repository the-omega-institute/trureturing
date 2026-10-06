/- GID: D5/S3/VertexAlgebra/LatticeActualCurrentAlgebra
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeActualCurrentAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual neutral modes satisfy the Heisenberg commutator and uniform order-two locality. -/

import D5.S3.VertexAlgebra.LatticeAllStateField
import D5.S3.VertexAlgebra.LatticeActualGeneratorLocality
import D5.S3.VertexAlgebra.FieldNormalProductLocality

/- Actual neutral current algebra, without positivity or nondegeneracy.
   Direct polynomial derivation proof; no Fock carrier or transfer.
   Bakalov--Kac math/0402315v1, section 4.1, equations (4.4)--(4.5). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeActualCurrentAlgebra
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration MvPolynomial
open scoped BigOperators VertexOperator
noncomputable section

theorem partials_commute (D : LatticeData) (x y : Index D) (p : Oscillator D) :
    pderiv x (pderiv y p) = pderiv y (pderiv x p) := by
  classical
  ext e
  simp only [coeff_pderiv]
  rw [show e + Finsupp.single x 1 + Finsupp.single y 1 =
      e + Finsupp.single y 1 + Finsupp.single x 1 by abel]
  by_cases h : x = y
  · subst y; rfl
  · simp [Finsupp.single_apply, h, Ne.symm h]
    ring

def annihilate (D : LatticeData) (i : Fin D.rank) (k : ℕ) :
    Oscillator D →ₗ[ℂ] Oscillator D :=
  ∑ j : Fin D.rank, (D.G i j : ℂ) • (pderiv (j,k)).toLinearMap

theorem annihilate_commute (D : LatticeData) (i j : Fin D.rank) (k l : ℕ)
    (p : Oscillator D) :
    annihilate D i k (annihilate D j l p) =
      annihilate D j l (annihilate D i k p) := by
  classical
  simp only [annihilate, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [partials_commute, mul_comm]

theorem annihilate_mul (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (p q : Oscillator D) :
    annihilate D i k (p*q) = annihilate D i k p * q + p * annihilate D i k q := by
  classical
  simp only [annihilate, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe, pderiv_mul, smul_add, Finset.sum_add_distrib,
    smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum]

theorem annihilate_X (D : LatticeData) (i j : Fin D.rank) (k l : ℕ) :
    annihilate D i k (X (j,l)) =
      if k = l then (D.G i j : ℂ) • (1 : Oscillator D) else 0 := by
  classical
  by_cases h : k = l
  · subst l; simp [annihilate, pderiv_X, Pi.single_apply, Prod.mk.injEq]
  · simp [annihilate, pderiv_X, Pi.single_apply, Prod.mk.injEq, h, Ne.symm h]

theorem annihilate_create_commutator (D : LatticeData) (i j : Fin D.rank)
    (k l : ℕ) (p : Oscillator D) :
    annihilate D i k (X (j,l) * p) - X (j,l) * annihilate D i k p =
      if k = l then (D.G i j : ℂ) • p else 0 := by
  rw [annihilate_mul, annihilate_X, add_sub_cancel_right]
  split_ifs <;> simp [smul_mul_assoc]

@[simp] theorem neutral_single (D : LatticeData) (i : Fin D.rank) (m : ℤ)
    (δ : Charge D) (p : Oscillator D) :
    neutralMode D i m (Finsupp.single δ p) =
      Finsupp.single δ (neutralPolynomialMode D i δ m p) := by
  simp [neutralMode]

theorem positive_negative_sector (D : LatticeData) (i j : Fin D.rank)
    (δ : Charge D) (m n : ℤ) (hm : 0 < m) (hn : n < 0) (p : Oscillator D) :
    neutralPolynomialMode D i δ m (neutralPolynomialMode D j δ n p) -
      neutralPolynomialMode D j δ n (neutralPolynomialMode D i δ m p) =
      if m+n = 0 then ((m : ℂ) * (D.G i j : ℂ)) • p else 0 := by
  have hidx : (m-1).toNat = (-n-1).toNat ↔ m+n = 0 := by omega
  simp only [neutralPolynomialMode, not_lt.mpr hm.le, ne_of_gt hm, hn,
    if_false, if_true, LinearMap.smul_apply, LinearMap.mulLeft_apply]
  change (m : ℂ) • annihilate D i (m-1).toNat (X (j,(-n-1).toNat)*p) -
    X (j,(-n-1).toNat) * ((m : ℂ) • annihilate D i (m-1).toNat p) = _
  rw [mul_smul_comm, ← smul_sub, annihilate_create_commutator]
  simp only [hidx]
  split_ifs <;> simp [smul_smul]

theorem neutral_sector_heisenberg (D : LatticeData) (i j : Fin D.rank)
    (δ : Charge D) (m n : ℤ) (p : Oscillator D) :
    neutralPolynomialMode D i δ m (neutralPolynomialMode D j δ n p) -
      neutralPolynomialMode D j δ n (neutralPolynomialMode D i δ m p) =
      if m+n = 0 then ((m : ℂ) * (D.G i j : ℂ)) • p else 0 := by
  classical
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rcases lt_trichotomy n 0 with hn | hn | hn
    · simp [neutralPolynomialMode, hm, hn, show m+n ≠ 0 by omega,
        LinearMap.mulLeft_apply, mul_left_comm]
    · subst n
      simp [neutralPolynomialMode, hm, ne_of_lt hm, LinearMap.mulLeft_apply,
        mul_smul_comm]
    · have h := positive_negative_sector D j i δ n m hn hm p
      have hs : m+n = 0 ↔ n+m = 0 := by omega
      by_cases hz : m+n = 0
      · have hc : (n : ℂ) = -(m : ℂ) := by exact_mod_cast (show n = -m by omega)
        simp only [if_pos (hs.mp hz), hc, D.symmetric j i, neg_mul, neg_smul] at h
        rw [if_pos hz]
        linear_combination -h
      · simp only [if_neg (hs.not.mp hz)] at h
        rw [if_neg hz]
        exact (sub_eq_zero.mpr (sub_eq_zero.mp h).symm)
  · subst m
    simp [neutralPolynomialMode, map_smul, smul_comm]
  · rcases lt_trichotomy n 0 with hn | hn | hn
    · exact positive_negative_sector D i j δ m n hm hn p
    · subst n
      simp only [neutralPolynomialMode, not_lt.mpr hm.le, ne_of_gt hm,
        if_false, if_true, lt_self_iff_false, LinearMap.smul_apply,
        LinearMap.id_apply, map_smul, show m + 0 ≠ 0 by omega]
      rw [smul_comm (m : ℂ), sub_self]
    · simp only [neutralPolynomialMode, not_lt.mpr hm.le, not_lt.mpr hn.le,
        ne_of_gt hm, ne_of_gt hn, if_false, show m+n ≠ 0 by omega,
        LinearMap.smul_apply]
      change (m : ℂ) • annihilate D i (m-1).toNat
          ((n : ℂ) • annihilate D j (n-1).toNat p) -
        (n : ℂ) • annihilate D j (n-1).toNat
          ((m : ℂ) • annihilate D i (m-1).toNat p) = 0
      rw [map_smul, map_smul, annihilate_commute, smul_comm, sub_self]

/-- The actual Heisenberg commutator on all charge sectors and polynomials. -/
theorem neutral_heisenberg (D : LatticeData) (i j : Fin D.rank) (m n : ℤ) :
    neutralMode D i m * neutralMode D j n - neutralMode D j n * neutralMode D i m =
      if m+n = 0 then ((m : ℂ) * (D.G i j : ℂ)) • LinearMap.id else 0 := by
  classical
  apply Finsupp.lhom_ext
  intro δ p
  simp only [LinearMap.sub_apply, Module.End.mul_apply, neutral_single,
    ← Finsupp.single_sub, neutral_sector_heisenberg]
  split_ifs <;> simp

end
end D5.S3.VertexAlgebra.LatticeActualCurrentAlgebra

/- Actual neutral-neutral locality under the supplier's normalized mode delta.
   The finite difference cancellation adapts the currentLocal calculation in
   PolynomialFockStateField at the sealed a9f81b99 supplier; the input here is
   the independently proved actual all-sector matrix Heisenberg FieldNormalProductLocality.commutator. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeActualCurrentLocality
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeActualCurrentAlgebra LatticeActualGeneratorLocality
open FieldNormalProductLocality
open scoped VertexOperator

/-- Uniform actual neutral locality on every charge and polynomial, with order two. -/
theorem actual_neutral_neutral_locality (D : LatticeData) (i j : Fin D.rank) :
    delta^[2] (FieldNormalProductLocality.commutator (neutralField D i) (neutralField D j)) = 0 := by
  funext left right
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, delta,
    FieldNormalProductLocality.commutator, neutral_modes]
  simp_rw [neutral_heisenberg]
  rw [show left+1+1+right = left+right+2 by omega,
    show left+1+(right+1) = left+right+2 by omega,
    show left+(right+1+1) = left+right+2 by omega]
  by_cases h : left+right+2 = 0
  · simp only [if_pos h, Pi.zero_apply]
    push_cast
    module
  · simp [h]

end D5.S3.VertexAlgebra.LatticeActualCurrentLocality
