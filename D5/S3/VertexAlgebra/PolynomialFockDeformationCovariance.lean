/- GID: D5/S3/VertexAlgebra/PolynomialFockDeformationCovariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/PolynomialFockDeformationCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial generator substitution intertwines every actual Fock product coefficient. -/

/-
proof_shape: deformation_covariance: content
escape_witness: Independent coefficients of the bivariate generator substitution
  satisfy the finite count recurrence and positive-weight support. Count induction
  combines the actual Borcherds current law with negative-binomial convolution;
  summing the supported counts gives the unrestricted coefficient identity.
admission_basis: escape-witness
utility: none; a universal symbolic identity, not an enumeration, checker,
  numerical reduction or certified finite instance.
-/

import D5.S3.VertexAlgebra.PolynomialFockJacobi
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.Derivation.MapCoeffs

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace D5.S3.VertexAlgebra.PolynomialFockDeformationCovariance

open MvPolynomial PolynomialFockSugawaraSupport PolynomialFockStateField
open PolynomialFockJacobi (mu integerBinomial borcherds jacobiLeftTerm
  jacobiRightFirstTerm jacobiRightSecondTerm epsilon)
open scoped VertexOperator

/-- Independent polynomial generator substitution with arbitrary complex charge. -/
noncomputable def deformation (lambda : ℂ) : Fock →ₐ[ℂ] Polynomial Fock :=
  MvPolynomial.aeval fun j => Polynomial.C (X j) +
    Polynomial.monomial (j + 1) (MvPolynomial.C (((-1 : ℂ) ^ j) * lambda))

/-- The actual coefficient of the substituted polynomial. -/
noncomputable def deformationCoeff (lambda : ℂ) (k : ℕ) (p : Fock) : Fock :=
  (deformation lambda p).coeff k

/-- Every coefficient of the independent substitution intertwines the actual Fock products. -/
theorem deformation_covariance (lambda : ℂ) (u v : Fock) (r : ℤ) (k : ℕ) :
    deformationCoeff lambda k (mu u r v) =
      ∑ d ∈ Finset.range (k + 1), ∑ e ∈ Finset.range (k - d + 1),
        integerBinomial (-(d : ℤ)) (k - d - e) •
          mu (deformationCoeff lambda d u) (r + (k - d - e : ℕ))
            (deformationCoeff lambda e v) := by
  classical
  have currentLaw (u v : Fock) (r : ℤ) (m : ℕ) :
      (m + 1 : ℂ) • pderiv m (mu u r v) =
        mu u r ((m + 1 : ℂ) • pderiv m v) +
          ∑ d ∈ Finset.range (m + 1), ((m + 1).choose (d + 1) : ℂ) •
            mu ((d + 1 : ℂ) • pderiv d u) (r + (m - d : ℕ)) v := by
    have currentModes (i : ℤ) (x : Fock) : mu (X 0) i x = mode i x := by
      rw [mu, stateField_creation.2.1, current, VertexOperator.ncoeff_of_coeff]
      rw [show -(-i - 1) - 1 = i by omega]
    have natModes (i : ℕ) (x : Fock) : mu (X 0) i x =
        if i = 0 then 0 else (i : ℂ) • pderiv (i - 1) x := by
      rw [currentModes]
      cases i with
      | zero => simp [mode]
      | succ i => simp [mode, annihilate, Nat.cast_add]
    have binomNat (i : ℕ) : integerBinomial ((m : ℤ) + 1) i =
        ((m + 1).choose i : ℂ) := by
      unfold integerBinomial
      rw [show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by simp]
      rw [Ring.choose_natCast, Int.cast_natCast]
    have modeSucc (x : Fock) : mu (X 0) ((m : ℤ) + 1) x =
        (m + 1 : ℂ) • pderiv m x := by
      simpa using natModes (m + 1) x
    have h := (borcherds (X 0) u v (m + 1) r 0).2.2.2
    have lhs : (∑ᶠ i : ℕ, jacobiLeftTerm (m + 1) r 0 (X 0) u v i) =
        ∑ i ∈ Finset.range (m + 2), ((m + 1).choose i : ℂ) •
          mu (mu (X 0) i u) ((m : ℤ) + 1 + r - i) v := by
      simp only [jacobiLeftTerm, zero_add, binomNat]
      apply finsum_eq_sum_of_support_subset
      intro i hi
      by_contra hn
      have hge : m + 2 ≤ i := by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hn
      have hz : (m + 1).choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
      exact hi (by simp [hz])
    rw [lhs, finsum_eq_single _ 0] at h
    · simp only [pow_zero, integerBinomial, Ring.choose_zero_right, Int.cast_one, mul_one,
        Int.natCast_zero, add_zero, sub_zero, epsilon, zpow_zero, one_smul] at h
      rw [modeSucc, modeSucc] at h
      rw [show m + 2 = (m + 1) + 1 by omega, Finset.sum_range_succ'] at h
      simp only [natModes, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
        Nat.add_sub_cancel, if_pos rfl] at h
      have zeroMu (i : ℤ) : mu 0 i v = 0 := by simp [mu]
      simp only [ite_true, zeroMu, smul_zero, add_zero] at h
      have hs : (∑ d ∈ Finset.range (m + 1), ((m + 1).choose (d + 1) : ℂ) •
          mu (((d + 1 : ℕ) : ℂ) • pderiv d u) ((m : ℤ) + 1 + r - (d + 1 : ℕ)) v) =
          ∑ d ∈ Finset.range (m + 1), ((m + 1).choose (d + 1) : ℂ) •
            mu ((d + 1 : ℂ) • pderiv d u) (r + (m - d : ℕ)) v := by
        apply Finset.sum_congr rfl
        intro d hd
        have hd' : d ≤ m := by simpa using Finset.mem_range.mp hd
        rw [Nat.cast_add, Nat.cast_one]
        have index : (m : ℤ) + 1 + r - (d + 1 : ℕ) = r + (m - d : ℕ) := by
          push_cast [Int.natCast_sub hd']; omega
        rw [index]
      rw [hs] at h
      have hh := eq_sub_iff_add_eq.mp h
      exact hh.symm.trans (add_comm _ _)
    · intro i hi
      have hz : Ring.choose (0 : ℤ) i = 0 := Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)
      simp [integerBinomial, hz]
  have weightedBinomial (m d : ℕ) (hd : d ≤ m) :
      (m + 1 : ℂ) * integerBinomial (-(d + 1 : ℤ)) (m - d) * (-1 : ℂ) ^ d =
        (-1 : ℂ) ^ m * ((m + 1).choose (d + 1) : ℂ) * (d + 1 : ℂ) := by
    have hb : integerBinomial (-(d + 1 : ℤ)) (m - d) =
        (-1 : ℂ) ^ (m - d) * (m.choose d : ℂ) := by
      unfold integerBinomial
      rw [Ring.choose_neg]
      rw [show (d + 1 : ℤ) + (m - d : ℕ) - 1 = (m : ℤ) by
        push_cast [Int.natCast_sub hd]; omega]
      rw [Ring.choose_natCast, Nat.choose_symm hd]
      simp [Int.coe_negOnePow_natCast, Units.smul_def]
    have hc : (m + 1 : ℂ) * (m.choose d : ℂ) =
        ((m + 1).choose (d + 1) : ℂ) * (d + 1 : ℂ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq m d
    have hp : (-1 : ℂ) ^ (m - d) * (-1 : ℂ) ^ d = (-1 : ℂ) ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hd]
    rw [hb]
    calc
      _ = ((-1 : ℂ) ^ (m - d) * (-1 : ℂ) ^ d) *
        ((m + 1 : ℂ) * (m.choose d : ℂ)) := by ring
      _ = _ := by rw [hp, hc]; ring
  let S : Fock →ₐ[ℂ] Polynomial (Polynomial Fock) :=
    MvPolynomial.aeval fun j => Polynomial.C (Polynomial.C (X j)) +
      Polynomial.monomial 1 (Polynomial.monomial (j + 1) (C (((-1 : ℂ) ^ j) * lambda)))
  let Q (n k : ℕ) (p : Fock) : Fock := ((S p).coeff n).coeff k
  have zeroCount (k : ℕ) (p : Fock) : Q 0 k p = if k = 0 then p else 0 := by
    let ev : Polynomial (Polynomial Fock) →ₐ[ℂ] Polynomial Fock :=
      (Polynomial.aeval (0 : Polynomial Fock)).restrictScalars ℂ
    have hs : ev.comp S = (Polynomial.CAlgHom : Fock →ₐ[ℂ] Polynomial Fock) := by
      ext j
      simp [ev, S, Polynomial.eval_monomial]
    have hh := congrArg (fun f : Fock →ₐ[ℂ] Polynomial Fock => (f p).coeff k) hs
    change (Polynomial.eval 0 (S p)).coeff k = _ at hh
    rw [← Polynomial.coeff_zero_eq_eval_zero] at hh
    change ((S p).coeff 0).coeff k = (Polynomial.C p).coeff k at hh
    simpa only [Q, Polynomial.coeff_C] using hh
  have S_X (j : ℕ) : S (X j) = Polynomial.C (Polynomial.C (X j)) +
      Polynomial.monomial 1 (Polynomial.monomial (j + 1) (C (((-1 : ℂ) ^ j) * lambda))) := by
    simp [S]
  have support (p : Fock) (n k : ℕ) (hn : k < n) : Q n k p = 0 := by
    induction p using MvPolynomial.induction_on generalizing n k with
    | C c =>
      have hn0 : n ≠ 0 := by omega
      simp [Q, S, Polynomial.coeff_C, hn0]
    | add p t hp ht =>
      change ((S (p + t)).coeff n).coeff k = 0
      rw [map_add, Polynomial.coeff_add, Polynomial.coeff_add]
      change Q n k p + Q n k t = 0
      rw [hp n k hn, ht n k hn, add_zero]
    | mul_X p j hp =>
      cases n with
      | zero => omega
      | succ n =>
        simp only [Q, map_mul, S_X, mul_add, Polynomial.coeff_add, Polynomial.coeff_mul_C]
        rw [← Polynomial.C_mul_X_pow_eq_monomial, pow_one, ← mul_assoc,
          Polynomial.coeff_mul_X, Polynomial.coeff_mul_C]
        rw [show ((S p).coeff (n + 1)).coeff k = 0 from hp (n + 1) k hn, zero_mul, zero_add]
        rw [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc,
          Polynomial.coeff_mul_X_pow', Polynomial.coeff_mul_C]
        split_ifs with hj
        · rw [show ((S p).coeff n).coeff (k - (j + 1)) = 0 from hp n _ (by omega), zero_mul]
        · rfl
  let A (j : ℕ) : Polynomial (Polynomial Fock) :=
    Polynomial.C (Polynomial.monomial (j + 1) (C (((-1 : ℂ) ^ j) * lambda)))
  let modS : Module Fock (Polynomial (Polynomial Fock)) :=
    Module.compHom (Polynomial (Polynomial Fock)) S.toRingHom
  letI : Module Fock (Polynomial (Polynomial Fock)) := modS
  letI : SMul Fock (Polynomial (Polynomial Fock)) := modS.toSMul
  letI : IsScalarTower ℂ Fock (Polynomial (Polynomial Fock)) := {
    smul_assoc c p b := by
      change S (c • p) * b = c • (S p * b)
      rw [map_smul, smul_mul_assoc] }
  letI : IsScalarTower Fock (Polynomial (Polynomial Fock))
      (Polynomial (Polynomial Fock)) := {
    smul_assoc p a b := by
      change (S p * a) * b = S p * (a * b)
      exact mul_assoc _ _ _ }
  letI : SMulCommClass Fock (Polynomial (Polynomial Fock))
      (Polynomial (Polynomial Fock)) := {
    smul_comm p a b := by
      change S p * (a * b) = a * (S p * b)
      ring }
  letI : SMulCommClass (Polynomial (Polynomial Fock)) Fock
      (Polynomial (Polynomial Fock)) := {
    smul_comm a p b := by
      change a * (S p * b) = S p * (a * b)
      ring }
  letI : SMulCommClass ℂ (Polynomial (Polynomial Fock))
      (Polynomial (Polynomial Fock)) := {
    smul_comm c a b := by
      exact (mul_smul_comm c a b).symm }
  let SL : Fock →ₗ[Fock] Polynomial (Polynomial Fock) := {
    toFun := S
    map_add' := S.map_add
    map_smul' c p := by
      change S (c * p) = S c * S p
      exact S.map_mul c p }
  let D : Derivation ℂ Fock (Polynomial (Polynomial Fock)) := {
    toLinearMap := (Polynomial.derivative.restrictScalars ℂ).comp S.toLinearMap
    map_one_eq_zero' := by simp
    leibniz' p t := by
      change Polynomial.derivative (S (p * t)) =
        S p * Polynomial.derivative (S t) + S t * Polynomial.derivative (S p)
      rw [map_mul, Polynomial.derivative_mul]
      ring }
  have Dgen : D = MvPolynomial.mkDerivation ℂ A := by
    apply MvPolynomial.derivation_ext
    intro j
    rw [MvPolynomial.mkDerivation_X]
    change Polynomial.derivative (S (X j)) = A j
    rw [S_X]
    simp only [Polynomial.derivative_add, Polynomial.derivative_C,
      Polynomial.derivative_monomial, Nat.cast_one, mul_one,
      Nat.sub_self, Polynomial.monomial_zero_left, zero_add]
    rfl
  let PD (j : ℕ) : Derivation ℂ Fock (Polynomial (Polynomial Fock)) :=
    SL.compDer (pderiv j)
  have PD_apply (j : ℕ) (p : Fock) : PD j p = S (pderiv j p) := rfl
  have sumDer (s : Finset ℕ) (f : ℕ → Derivation ℂ Fock (Polynomial (Polynomial Fock)))
      (p : Fock) : (∑ j ∈ s, f j) p = ∑ j ∈ s, f j p := by
    have hh := congrFun (map_sum
      (Derivation.coeFnAddMonoidHom (R := ℂ) (A := Fock)
        (M := Polynomial (Polynomial Fock))) f s) p
    simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using hh
  have chain (p : Fock) : Polynomial.derivative (S p) =
      ∑ j ∈ p.vars, A j * S (pderiv j p) := by
    have hh : D p = (∑ j ∈ p.vars, A j • PD j) p := by
      apply MvPolynomial.derivation_eq_of_forall_mem_vars
      intro j hj
      rw [Dgen]
      rw [MvPolynomial.mkDerivation_X, sumDer]
      simp only [Derivation.smul_apply, PD_apply, pderiv_X, Pi.single_apply]
      simp [apply_ite, hj]
    rw [sumDer] at hh
    simp only [Derivation.smul_apply, PD_apply] at hh
    exact hh
  let E (j : ℕ) : Derivation ℂ (Polynomial Fock) (Polynomial Fock) :=
    PolynomialModule.equivPolynomialSelf.toLinearMap.compDer (pderiv j).mapCoeffs
  let E2 (j : ℕ) : Derivation ℂ (Polynomial (Polynomial Fock))
      (Polynomial (Polynomial Fock)) :=
    PolynomialModule.equivPolynomialSelf.toLinearMap.compDer (E j).mapCoeffs
  have E_coeff (j : ℕ) (p : Polynomial Fock) (k : ℕ) :
      (E j p).coeff k = pderiv j (p.coeff k) := by rfl
  have E2_coeff (j : ℕ) (p : Polynomial (Polynomial Fock)) (n k : ℕ) :
      ((E2 j p).coeff n).coeff k = pderiv j ((p.coeff n).coeff k) := by rfl
  have E2mon (j n k : ℕ) (x : Fock) :
      E2 j (Polynomial.monomial n (Polynomial.monomial k x)) =
        Polynomial.monomial n (Polynomial.monomial k (pderiv j x)) := by
    apply Polynomial.ext
    intro a
    apply Polynomial.ext
    intro b
    rw [E2_coeff]
    by_cases hn : n = a <;> by_cases hk : k = b
    all_goals simp [Polynomial.coeff_monomial, hn, hk, apply_ite]
  have commuteQ (j n k : ℕ) (p : Fock) :
      Q n k (pderiv j p) = pderiv j (Q n k p) := by
    let ED : Derivation ℂ Fock (Polynomial (Polynomial Fock)) := {
      toLinearMap := (E2 j).toLinearMap.comp S.toLinearMap
      map_one_eq_zero' := by simp
      leibniz' p t := by
        change E2 j (S (p * t)) = S p * E2 j (S t) + S t * E2 j (S p)
        rw [map_mul, (E2 j).leibniz]
        rfl }
    have hh : ED = PD j := by
      apply MvPolynomial.derivation_ext
      intro i
      change E2 j (S (X i)) = S (pderiv j (X i))
      rw [S_X]
      change E2 j (Polynomial.monomial 0 (Polynomial.monomial 0 (X i)) +
        Polynomial.monomial 1 (Polynomial.monomial (i + 1) (C (((-1 : ℂ)^i)*lambda)))) = _
      rw [map_add, E2mon, E2mon, pderiv_C]
      simp only [Polynomial.monomial_zero_right, add_zero, pderiv_X, Pi.single_apply,
        apply_ite, map_one, map_zero, Polynomial.monomial_zero_left]
      split_ifs <;> simp
    have ht := congrArg (fun f : Derivation ℂ Fock (Polynomial (Polynomial Fock)) =>
      ((f p).coeff n).coeff k) hh
    change ((E2 j (S p)).coeff n).coeff k = ((S (pderiv j p)).coeff n).coeff k at ht
    rw [E2_coeff] at ht
    exact ht.symm
  let Cc (m : ℕ) (p : Fock) : Fock := (((-1 : ℂ)^m)*lambda) • pderiv m p
  have recurrence (n k : ℕ) (p : Fock) :
      (n + 1 : ℂ) • Q (n + 1) k p =
        ∑ j ∈ Finset.range k, Cc j (Q n (k - (j + 1)) p) := by
    have hh := congrArg (fun b : Polynomial (Polynomial Fock) => (b.coeff n).coeff k) (chain p)
    have derivCoeff : ((Polynomial.derivative (S p)).coeff n).coeff k =
        (n + 1 : ℂ) • Q (n + 1) k p := by
      rw [Polynomial.coeff_derivative]
      rw [show (S p).coeff (n + 1) * (n + 1) = (n + 1) • (S p).coeff (n + 1) by
        simp [nsmul_eq_mul, mul_comm] ]
      rw [Polynomial.coeff_smul]
      change (n + 1) • Q (n + 1) k p = _
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Nat.cast_smul_eq_nsmul ℂ (n + 1) (Q (n + 1) k p)).symm
    rw [derivCoeff] at hh
    let f (j : ℕ) : Fock := if j + 1 ≤ k then
      (((-1 : ℂ)^j)*lambda) • Q n (k - (j + 1)) (pderiv j p) else 0
    have summand (j : ℕ) : ((A j * S (pderiv j p)).coeff n).coeff k = f j := by
      dsimp only [A]
      rw [Polynomial.coeff_C_mul]
      rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_mul']
      simp only [f, smul_eq_C_mul, apply_ite, map_zero, mul_zero]
      split_ifs <;> rfl
    simp only [Polynomial.finsetSum_coeff, summand] at hh
    have first : (∑ᶠ j, f j) = ∑ j ∈ p.vars, f j := by
      apply finsum_eq_sum_of_support_subset
      intro j hj
      by_contra hn
      have hz := pderiv_eq_zero_of_notMem_vars hn
      exact hj (by simp [f, hz, Q])
    have second : (∑ᶠ j, f j) = ∑ j ∈ Finset.range k, f j := by
      apply finsum_eq_sum_of_support_subset
      intro j hj
      by_contra hn
      have hk : ¬ j < k := by simpa only [Finset.mem_coe, Finset.mem_range] using hn
      exact hj (by simp only [f, if_neg (show ¬ j + 1 ≤ k by omega)])
    rw [← first, second] at hh
    rw [hh]
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j + 1 ≤ k := by have := Finset.mem_range.mp hj; omega
    dsimp only [f]
    rw [if_pos hjk, commuteQ]
  have leftReindex (k : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℕ → Fock) :
      (∑ h ∈ Finset.range k, ∑ d ∈ Finset.range (k - h),
        ∑ e ∈ Finset.range (k - h - d), ∑ l ∈ Finset.range (h + 1),
          f (l + 1) d e (h - l) (k - h - 1 - d - e)) =
      ∑ D ∈ Finset.range (k + 1), ∑ E ∈ Finset.range (k - D + 1),
        ∑ H ∈ Finset.range D, ∑ L ∈ Finset.range (k - D - E + 1),
          f (H + 1) (D - H - 1) E L (k - D - E - L) := by
    let s : Finset (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
      (Finset.range k).sigma fun h => (Finset.range (k - h)).sigma fun d =>
        (Finset.range (k - h - d)).sigma fun _ => Finset.range (h + 1)
    let t : Finset (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
      (Finset.range (k + 1)).sigma fun D => (Finset.range (k - D + 1)).sigma fun E =>
        (Finset.range D).sigma fun _ => Finset.range (k - D - E + 1)
    have hs (x : Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) : x ∈ s ↔
        x.1 < k ∧ x.2.1 < k - x.1 ∧ x.2.2.1 < k - x.1 - x.2.1 ∧
          x.2.2.2 < x.1 + 1 := by simp [s, Finset.mem_sigma]
    have ht (x : Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) : x ∈ t ↔
        x.1 < k + 1 ∧ x.2.1 < k - x.1 + 1 ∧ x.2.2.1 < x.1 ∧
          x.2.2.2 < k - x.1 - x.2.1 + 1 := by simp [t, Finset.mem_sigma]
    let i (x : Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) :
        Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ :=
      ⟨x.2.1 + x.2.2.2 + 1, ⟨x.2.2.1, ⟨x.2.2.2, x.1 - x.2.2.2⟩⟩⟩
    let j (x : Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) :
        Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ :=
      ⟨x.2.2.1 + x.2.2.2, ⟨x.1 - x.2.2.1 - 1, ⟨x.2.1, x.2.2.1⟩⟩⟩
    have mi (x) (hx : x ∈ s) : i x ∈ t := by
      rw [hs] at hx
      rw [ht]
      dsimp [i]
      omega
    have mj (x) (hx : x ∈ t) : j x ∈ s := by
      rw [ht] at hx
      rw [hs]
      dsimp [j]
      omega
    have li (x) (hx : x ∈ s) : j (i x) = x := by
      rw [hs] at hx
      rcases x with ⟨h,d,e,l⟩
      dsimp at hx
      dsimp [i, j]
      rw [show l + (h - l) = h by omega, show d + l + 1 - l - 1 = d by omega]
    have ri (x) (hx : x ∈ t) : i (j x) = x := by
      rw [ht] at hx
      rcases x with ⟨D,E,H,L⟩
      dsimp at hx
      dsimp [i, j]
      rw [show D - H - 1 + H + 1 = D by omega, show H + L - H = L by omega]
    have heq : (∑ x ∈ s, f (x.2.2.2 + 1) x.2.1 x.2.2.1 (x.1 - x.2.2.2)
        (k - x.1 - 1 - x.2.1 - x.2.2.1)) =
        ∑ x ∈ t, f (x.2.2.1 + 1) (x.1 - x.2.2.1 - 1) x.2.1 x.2.2.2
          (k - x.1 - x.2.1 - x.2.2.2) := by
      refine Finset.sum_bij' (fun x _ => i x) (fun x _ => j x) mi mj li ri ?_
      intro x hx
      rw [hs] at hx
      dsimp [i]
      congr 1 <;> omega
    simpa only [s, t, Finset.sum_sigma] using heq
  have rightReindex (k : ℕ) (f : ℕ → ℕ → ℕ → ℕ → Fock) :
      (∑ h ∈ Finset.range k, ∑ d ∈ Finset.range (k - h),
        ∑ e ∈ Finset.range (k - h - d), f (h + 1) d e (k - h - 1 - d - e)) =
      ∑ D ∈ Finset.range (k + 1), ∑ E ∈ Finset.range (k - D + 1),
        ∑ H ∈ Finset.range E, f (H + 1) D (E - H - 1) (k - D - E) := by
    let s : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
      (Finset.range k).sigma fun h => (Finset.range (k - h)).sigma fun d =>
        Finset.range (k - h - d)
    let t : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
      (Finset.range (k + 1)).sigma fun D => (Finset.range (k - D + 1)).sigma fun E =>
        Finset.range E
    have hs (x : Σ _ : ℕ, Σ _ : ℕ, ℕ) : x ∈ s ↔
        x.1 < k ∧ x.2.1 < k - x.1 ∧ x.2.2 < k - x.1 - x.2.1 := by
      simp [s, Finset.mem_sigma]
    have ht (x : Σ _ : ℕ, Σ _ : ℕ, ℕ) : x ∈ t ↔
        x.1 < k + 1 ∧ x.2.1 < k - x.1 + 1 ∧ x.2.2 < x.2.1 := by
      simp [t, Finset.mem_sigma]
    let i (x : Σ _ : ℕ, Σ _ : ℕ, ℕ) : Σ _ : ℕ, Σ _ : ℕ, ℕ :=
      ⟨x.2.1, ⟨x.2.2 + x.1 + 1, x.1⟩⟩
    let j (x : Σ _ : ℕ, Σ _ : ℕ, ℕ) : Σ _ : ℕ, Σ _ : ℕ, ℕ :=
      ⟨x.2.2, ⟨x.1, x.2.1 - x.2.2 - 1⟩⟩
    have mi (x) (hx : x ∈ s) : i x ∈ t := by
      rw [hs] at hx
      rw [ht]
      dsimp [i]
      omega
    have mj (x) (hx : x ∈ t) : j x ∈ s := by
      rw [ht] at hx
      rw [hs]
      dsimp [j]
      omega
    have li (x) (hx : x ∈ s) : j (i x) = x := by
      rw [hs] at hx
      rcases x with ⟨h,d,e⟩
      dsimp at hx
      dsimp [i, j]
      rw [show e + h + 1 - h - 1 = e by omega]
    have ri (x) (hx : x ∈ t) : i (j x) = x := by
      rw [ht] at hx
      rcases x with ⟨D,E,H⟩
      dsimp at hx
      dsimp [i, j]
      rw [show E - H - 1 + H + 1 = E by omega]
    have heq : (∑ x ∈ s, f (x.1 + 1) x.2.1 x.2.2 (k - x.1 - 1 - x.2.1 - x.2.2)) =
        ∑ x ∈ t, f (x.2.2 + 1) x.1 (x.2.1 - x.2.2 - 1) (k - x.1 - x.2.1) := by
      refine Finset.sum_bij' (fun x _ => i x) (fun x _ => j x) mi mj li ri ?_
      intro x hx
      rw [hs] at hx
      dsimp [i]
      congr 1 <;> omega
    simpa only [s, t, Finset.sum_sigma] using heq
  have muAddLeft (a b c : Fock) (r : ℤ) : mu (a+b) r c = mu a r c + mu b r c := by
    simp [mu]
  have muAddRight (a b c : Fock) (r : ℤ) : mu a r (b+c) = mu a r b + mu a r c := by
    simp [mu]
  have muSmulLeft (a : ℂ) (b c : Fock) (r : ℤ) : mu (a • b) r c = a • mu b r c := by
    simp [mu]
  have muSmulRight (a : ℂ) (b c : Fock) (r : ℤ) : mu b r (a • c) = a • mu b r c := by
    simp [mu]
  have infinitesimal (u v : Fock) (r : ℤ) (m : ℕ) :
      Cc m (mu u r v) = mu u r (Cc m v) +
        ∑ d ∈ Finset.range (m + 1), integerBinomial (-(d + 1 : ℤ)) (m - d) •
          mu (Cc d u) (r + (m - d : ℕ)) v := by
    apply smul_right_injective Fock (show (m + 1 : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero m)
    have h := congrArg (fun x : Fock => (((-1 : ℂ)^m)*lambda) • x) (currentLaw u v r m)
    simp only [smul_add, Finset.smul_sum, smul_smul] at h
    dsimp only [Cc]
    rw [smul_add, Finset.smul_sum]
    have first : (m + 1 : ℂ) • mu u r (((-1 : ℂ)^m*lambda) • pderiv m v) =
        (((-1 : ℂ)^m)*lambda) • mu u r ((m + 1 : ℂ) • pderiv m v) := by
      rw [muSmulRight, muSmulRight, smul_smul, smul_smul, mul_comm]
    rw [first]
    have term (d : ℕ) (hd : d ∈ Finset.range (m + 1)) :
        (m + 1 : ℂ) • (integerBinomial (-(d + 1 : ℤ)) (m - d) •
          mu (((-1 : ℂ)^d*lambda) • pderiv d u) (r + (m - d : ℕ)) v) =
        (((-1 : ℂ)^m)*lambda) • (((m + 1).choose (d + 1) : ℂ) •
          mu ((d + 1 : ℂ) • pderiv d u) (r + (m - d : ℕ)) v) := by
      simp only [muSmulLeft, smul_smul]
      congr 1
      have hw := weightedBinomial m d (by have := Finset.mem_range.mp hd; omega)
      linear_combination lambda * hw
    rw [Finset.sum_congr rfl term]
    simpa only [Cc, smul_smul, mul_comm] using h
  let CL (m : ℕ) : Module.End ℂ Fock := (((-1 : ℂ)^m)*lambda) • (pderiv m).toLinearMap
  have Cc_eq (m : ℕ) (p : Fock) : Cc m p = CL m p := rfl
  have muSumLeft (s : Finset ℕ) (f : ℕ → Fock) (r : ℤ) (x : Fock) :
      mu (∑ a ∈ s, f a) r x = ∑ a ∈ s, mu (f a) r x := by
    simp [mu]
  have muSumRight (s : Finset ℕ) (f : ℕ → Fock) (r : ℤ) (x : Fock) :
      mu x r (∑ a ∈ s, f a) = ∑ a ∈ s, mu x r (f a) := by
    simp [mu]
  have binomialConvolution (d h J : ℕ) :
      (∑ L ∈ Finset.range (J + 1),
        integerBinomial (-(h : ℤ)) L * integerBinomial (-(d : ℤ)) (J - L)) =
        integerBinomial (-(d + h : ℤ)) J := by
    have hv := congrArg (fun z : ℤ => (z : ℂ))
      (Ring.add_choose_eq (R := ℤ) (r := -(h : ℤ)) (s := -(d : ℤ)) J (Commute.all _ _))
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun x y => Ring.choose (-(h : ℤ)) x * Ring.choose (-(d : ℤ)) y) J] at hv
    simpa only [integerBinomial, Int.cast_sum, Int.cast_mul, neg_add_rev] using hv.symm
  let star (a b : ℕ → Fock) (r : ℤ) (k : ℕ) : Fock :=
    ∑ d ∈ Finset.range (k + 1), ∑ e ∈ Finset.range (k - d + 1),
      integerBinomial (-(d : ℤ)) (k - d - e) • mu (a d) (r + (k - d - e : ℕ)) (b e)
  have firstBranch (a b k : ℕ) (r : ℤ) (u v : Fock) :
      (∑ h ∈ Finset.range k, ∑ d ∈ Finset.range (k - h),
        ∑ e ∈ Finset.range (k - h - d), ∑ l ∈ Finset.range (h + 1),
          (integerBinomial (-(d : ℤ)) (k - h - 1 - d - e) *
            integerBinomial (-(l + 1 : ℤ)) (h - l)) •
            mu (Cc l (Q a d u))
              (r + (k - h - 1 - d - e : ℕ) + (h - l : ℕ)) (Q b e v)) =
        (a + 1 : ℂ) • star (fun d => Q (a + 1) d u) (fun e => Q b e v) r k := by
    have hr := leftReindex k (fun H d e L J =>
      (integerBinomial (-(d : ℤ)) J * integerBinomial (-(H : ℤ)) L) •
        mu (Cc (H - 1) (Q a d u)) (r + (J : ℤ) + L) (Q b e v))
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hr
    rw [hr]
    dsimp only [star]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro D hD
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro E hE
    have hDE : E ≤ k - D := by have := Finset.mem_range.mp hE; omega
    have hDk : D ≤ k := by have := Finset.mem_range.mp hD; omega
    have inner (H : ℕ) (hH : H ∈ Finset.range D) :
        (∑ L ∈ Finset.range (k - D - E + 1),
          (integerBinomial (-((D - H - 1 : ℕ) : ℤ)) (k - D - E - L) *
            integerBinomial (-(H + 1 : ℤ)) L) •
            mu (Cc H (Q a (D - H - 1) u))
              (r + (k - D - E - L : ℕ) + L) (Q b E v)) =
          integerBinomial (-(D : ℤ)) (k - D - E) •
            mu (Cc H (Q a (D - H - 1) u)) (r + (k - D - E : ℕ)) (Q b E v) := by
      have hHD : H < D := Finset.mem_range.mp hH
      have index (L : ℕ) (hL : L ∈ Finset.range (k - D - E + 1)) :
          r + (k - D - E - L : ℕ) + L = r + (k - D - E : ℕ) := by
        have hh := Finset.mem_range.mp hL
        push_cast [Int.natCast_sub (show L ≤ k - D - E by omega)]
        omega
      rw [Finset.sum_congr rfl (fun L hL => by rw [index L hL])]
      rw [← Finset.sum_smul]
      congr 1
      have hh := binomialConvolution (D - H - 1) (H + 1) (k - D - E)
      have hsum : ((D - H - 1 : ℕ) : ℤ) + (H + 1 : ℤ) = (D : ℤ) := by
        push_cast [Int.natCast_sub (show H + 1 ≤ D by omega)]
        omega
      simp only [Nat.cast_add, Nat.cast_one] at hh
      rw [hsum] at hh
      simpa only [mul_comm] using hh
    rw [Finset.sum_congr rfl inner, ← Finset.smul_sum, ← muSumLeft]
    have hre := recurrence a D u
    have hindices (H : ℕ) : D - (H + 1) = D - H - 1 := by omega
    simp only [hindices] at hre
    rw [← hre, muSmulLeft, smul_comm]
  have secondBranch (a b k : ℕ) (r : ℤ) (u v : Fock) :
      (∑ h ∈ Finset.range k, ∑ d ∈ Finset.range (k - h),
        ∑ e ∈ Finset.range (k - h - d),
          integerBinomial (-(d : ℤ)) (k - h - 1 - d - e) •
            mu (Q a d u) (r + (k - h - 1 - d - e : ℕ)) (Cc h (Q b e v))) =
        (b + 1 : ℂ) • star (fun d => Q a d u) (fun e => Q (b + 1) e v) r k := by
    have hr := rightReindex k (fun H d e J => integerBinomial (-(d : ℤ)) J •
      mu (Q a d u) (r + (J : ℤ)) (Cc (H - 1) (Q b e v)))
    simp only [Nat.add_sub_cancel] at hr
    rw [hr]
    dsimp only [star]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro D hD
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro E hE
    rw [← Finset.smul_sum, ← muSumRight]
    have hre := recurrence b E v
    have hindices (H : ℕ) : E - (H + 1) = E - H - 1 := by omega
    simp only [hindices] at hre
    rw [← hre, muSmulRight, smul_comm]
  have countShuffle (n : ℕ) (f : ℕ → ℕ → Fock) :
      (∑ a ∈ Finset.range (n + 1),
        ((a + 1 : ℂ) • f (a + 1) (n - a) + ((n - a + 1 : ℕ) : ℂ) • f a (n - a + 1))) =
        (n + 1 : ℂ) • ∑ a ∈ Finset.range (n + 2), f a (n + 1 - a) := by
    rw [Finset.sum_add_distrib]
    have left : (∑ a ∈ Finset.range (n + 1), (a + 1 : ℂ) • f (a + 1) (n - a)) =
        ∑ a ∈ Finset.range (n + 2), (a : ℂ) • f a (n + 1 - a) := by
      rw [Finset.sum_range_succ' (fun a => (a : ℂ) • f a (n + 1 - a)) (n + 1)]
      simp only [Nat.cast_zero, zero_smul, add_zero]
      apply Finset.sum_congr rfl
      intro a ha
      rw [show n + 1 - (a + 1) = n - a by omega, Nat.cast_add, Nat.cast_one]
    have right : (∑ a ∈ Finset.range (n + 1), ((n - a + 1 : ℕ) : ℂ) • f a (n - a + 1)) =
        ∑ a ∈ Finset.range (n + 2), (n + 1 - a : ℕ) • f a (n + 1 - a) := by
      rw [Finset.sum_range_succ (fun a => (n + 1 - a : ℕ) • f a (n + 1 - a)) (n + 1)]
      simp only [Nat.sub_self, zero_smul, add_zero]
      apply Finset.sum_congr rfl
      intro a ha
      have hna : a ≤ n := by have := Finset.mem_range.mp ha; omega
      rw [show n + 1 - a = n - a + 1 by omega]
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Nat.cast_smul_eq_nsmul ℂ (n - a + 1) (f a (n - a + 1)))
    rw [left, right, ← Finset.sum_add_distrib, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← add_smul]
    congr 1
    have ha' : a ≤ n + 1 := by have := Finset.mem_range.mp ha; omega
    exact_mod_cast Nat.add_sub_of_le ha'
  have Csum (m : ℕ) (s : Finset ℕ) (f : ℕ → Fock) :
      Cc m (∑ i ∈ s, f i) = ∑ i ∈ s, Cc m (f i) := by
    simpa only [Cc_eq] using map_sum (CL m) f s
  have Csmul (m : ℕ) (c : ℂ) (x : Fock) : Cc m (c • x) = c • Cc m x := by
    simpa only [Cc_eq] using (CL m).map_smul c x
  have countCovariance (n : ℕ) (u v : Fock) (r : ℤ) (k : ℕ) :
      Q n k (mu u r v) = ∑ a ∈ Finset.range (n + 1),
        star (fun d => Q a d u) (fun e => Q (n - a) e v) r k := by
    induction n generalizing u v r k with
    | zero =>
      by_cases hk : k = 0
      · subst k
        simp [star, zeroCount, integerBinomial]
      · have hz := Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hk)
        simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton,
          Nat.sub_zero, zeroCount, if_neg hk]
        dsimp only [star]
        symm
        apply Finset.sum_eq_zero
        intro d hd
        by_cases hd0 : d = 0
        · subst d
          simp [zeroCount, integerBinomial, hz, mu, apply_ite]
        · simp [zeroCount, hd0, mu]
    | succ n ih =>
      apply smul_right_injective Fock
        (show (n + 1 : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n)
      change (n + 1 : ℂ) • Q (n + 1) k (mu u r v) =
        (n + 1 : ℂ) • ∑ a ∈ Finset.range (n + 2),
          star (fun d => Q a d u) (fun e => Q (n + 1 - a) e v) r k
      rw [recurrence]
      have step (h : ℕ) (hh : h ∈ Finset.range k) :
          Cc h (Q n (k - (h + 1)) (mu u r v)) =
            ∑ a ∈ Finset.range (n + 1),
              ((∑ d ∈ Finset.range (k - h), ∑ e ∈ Finset.range (k - h - d),
                  ∑ l ∈ Finset.range (h + 1),
                    (integerBinomial (-(d : ℤ)) (k - h - 1 - d - e) *
                      integerBinomial (-(l + 1 : ℤ)) (h - l)) •
                      mu (Cc l (Q a d u))
                        (r + (k - h - 1 - d - e : ℕ) + (h - l : ℕ)) (Q (n - a) e v)) +
                (∑ d ∈ Finset.range (k - h), ∑ e ∈ Finset.range (k - h - d),
                  integerBinomial (-(d : ℤ)) (k - h - 1 - d - e) •
                    mu (Q a d u) (r + (k - h - 1 - d - e : ℕ)) (Cc h (Q (n - a) e v)))) := by
        rw [ih, Csum]
        apply Finset.sum_congr rfl
        intro a ha
        have hh' : h < k := Finset.mem_range.mp hh
        have ksub : k - (h + 1) = k - h - 1 := by omega
        have krange : k - h - 1 + 1 = k - h := by omega
        dsimp only [star]
        rw [ksub, krange, Csum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        have hd' : d < k - h := Finset.mem_range.mp hd
        have erange : k - h - 1 - d + 1 = k - h - d := by omega
        rw [erange, Csum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro e he
        rw [Csmul, infinitesimal, smul_add, Finset.smul_sum]
        simp only [smul_smul]
        exact add_comm _ _
      rw [Finset.sum_congr rfl step, Finset.sum_comm]
      have branches : (∑ a ∈ Finset.range (n + 1),
          ∑ h ∈ Finset.range k,
            ((∑ d ∈ Finset.range (k - h), ∑ e ∈ Finset.range (k - h - d),
                ∑ l ∈ Finset.range (h + 1),
                  (integerBinomial (-(d : ℤ)) (k - h - 1 - d - e) *
                    integerBinomial (-(l + 1 : ℤ)) (h - l)) •
                    mu (Cc l (Q a d u))
                      (r + (k - h - 1 - d - e : ℕ) + (h - l : ℕ)) (Q (n - a) e v)) +
              (∑ d ∈ Finset.range (k - h), ∑ e ∈ Finset.range (k - h - d),
                integerBinomial (-(d : ℤ)) (k - h - 1 - d - e) •
                  mu (Q a d u) (r + (k - h - 1 - d - e : ℕ)) (Cc h (Q (n - a) e v))))) =
          ∑ a ∈ Finset.range (n + 1),
            ((a + 1 : ℂ) • star (fun d => Q (a + 1) d u) (fun e => Q (n - a) e v) r k +
              ((n - a + 1 : ℕ) : ℂ) •
                star (fun d => Q a d u) (fun e => Q (n - a + 1) e v) r k) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_add_distrib, firstBranch, secondBranch]
        simp only [Nat.cast_add, Nat.cast_one]
      rw [branches]
      exact countShuffle n (fun a b => star (fun d => Q a d u) (fun e => Q b e v) r k)
  have evaluateCount (p : Fock) : Polynomial.eval (1 : Polynomial Fock) (S p) =
      deformation lambda p := by
    let ev : Polynomial (Polynomial Fock) →ₐ[ℂ] Polynomial Fock :=
      (Polynomial.aeval (1 : Polynomial Fock)).restrictScalars ℂ
    have hh : ev.comp S = deformation lambda := by
      ext j
      simp [ev, S, deformation, Polynomial.eval_monomial]
    exact congrArg (fun f : Fock →ₐ[ℂ] Polynomial Fock => f p) hh
  have sumCounts (k : ℕ) (p : Fock) : deformationCoeff lambda k p =
      ∑ n ∈ Finset.range (k + 1), Q n k p := by
    have first : (∑ᶠ n, Q n k p) = ∑ n ∈ (S p).support, Q n k p := by
      apply finsum_eq_sum_of_support_subset
      intro n hn
      by_contra hm
      have hz : (S p).coeff n = 0 := by
        simpa only [Finset.mem_coe, Polynomial.mem_support_iff, not_not] using hm
      exact hn (by simp [Q, hz])
    have second : (∑ᶠ n, Q n k p) = ∑ n ∈ Finset.range (k + 1), Q n k p := by
      apply finsum_eq_sum_of_support_subset
      intro n hn
      by_contra hm
      have hnk : k < n := by
        have hne : ¬ n < k + 1 := by simpa only [Finset.mem_coe, Finset.mem_range] using hm
        omega
      exact hn (support p n k hnk)
    rw [← second, first]
    rw [deformationCoeff, ← evaluateCount]
    simp [Polynomial.eval_eq_sum, Polynomial.sum, Q]
  have countTriangle (k : ℕ) (f : ℕ → ℕ → Fock) :
      (∑ n ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (n + 1), f a (n - a)) =
        ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k - a + 1), f a b := by
    let s : Finset (Σ _ : ℕ, ℕ) :=
      (Finset.range (k + 1)).sigma fun n => Finset.range (n + 1)
    let t : Finset (Σ _ : ℕ, ℕ) :=
      (Finset.range (k + 1)).sigma fun a => Finset.range (k - a + 1)
    have hs (x : Σ _ : ℕ, ℕ) : x ∈ s ↔ x.1 ≤ k ∧ x.2 ≤ x.1 := by
      simp [s, Finset.mem_sigma, Nat.lt_succ_iff]
    have ht (x : Σ _ : ℕ, ℕ) : x ∈ t ↔ x.1 ≤ k ∧ x.2 ≤ k - x.1 := by
      simp [t, Finset.mem_sigma, Nat.lt_succ_iff]
    let i (x : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ := ⟨x.2, x.1 - x.2⟩
    let j (x : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ := ⟨x.1 + x.2, x.1⟩
    have mi x (hx : x ∈ s) : i x ∈ t := by
      rw [hs] at hx
      rw [ht]
      dsimp [i]
      omega
    have mj x (hx : x ∈ t) : j x ∈ s := by
      rw [ht] at hx
      rw [hs]
      dsimp [j]
      omega
    have li x (hx : x ∈ s) : j (i x) = x := by
      rw [hs] at hx
      rcases x with ⟨n,a⟩
      dsimp at hx
      dsimp [i,j]
      rw [show a + (n - a) = n by omega]
    have ri x (hx : x ∈ t) : i (j x) = x := by
      rcases x with ⟨a,b⟩
      simp [i,j]
    have hsum : (∑ x ∈ s, f x.2 (x.1 - x.2)) = ∑ x ∈ t, f x.1 x.2 := by
      exact Finset.sum_bij' (fun x _ => i x) (fun x _ => j x) mi mj li ri (by intro x hx; rfl)
    simpa only [s,t,Finset.sum_sigma] using hsum
  rw [sumCounts]
  simp_rw [countCovariance]
  rw [countTriangle k (fun a b => star (fun d => Q a d u) (fun e => Q b e v) r k)]
  dsimp only [star]
  let term (a b d e : ℕ) : Fock :=
    integerBinomial (-(d : ℤ)) (k - d - e) •
      mu (Q a d u) (r + (k - d - e : ℕ)) (Q b e v)
  have exchangeCounts :
      (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k - a + 1),
        ∑ d ∈ Finset.range (k + 1), ∑ e ∈ Finset.range (k - d + 1), term a b d e) =
      ∑ d ∈ Finset.range (k + 1), ∑ e ∈ Finset.range (k - d + 1),
        ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k - a + 1), term a b d e := by
    calc
      _ = ∑ a ∈ Finset.range (k + 1), ∑ d ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.range (k - d + 1), ∑ b ∈ Finset.range (k - a + 1), term a b d e := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_comm]
  change (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k - a + 1),
    ∑ d ∈ Finset.range (k + 1), ∑ e ∈ Finset.range (k - d + 1), term a b d e) = _
  rw [exchangeCounts]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hdk : d ≤ k := by have := Finset.mem_range.mp hd; omega
  have hed : e ≤ k - d := by have := Finset.mem_range.mp he; omega
  have truncate : (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k - a + 1), term a b d e) =
      ∑ a ∈ Finset.range (d + 1), ∑ b ∈ Finset.range (e + 1), term a b d e := by
    calc
      _ = ∑ a ∈ Finset.range (d + 1), ∑ b ∈ Finset.range (k - a + 1), term a b d e := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro a ha hna
        have hda : d < a := by
          have hh : ¬ a < d + 1 := by simpa only [Finset.mem_range] using hna
          omega
        apply Finset.sum_eq_zero
        intro b hb
        simp [term, support u a d hda, mu]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        have had : a ≤ d := by have := Finset.mem_range.mp ha; omega
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro b hb hnb
        have heb : e < b := by
          have hh : ¬ b < e + 1 := by simpa only [Finset.mem_range] using hnb
          omega
        simp [term, support v b e heb, mu]
  rw [truncate]
  dsimp only [term]
  simp_rw [← Finset.smul_sum, ← muSumRight]
  rw [← muSumLeft, ← sumCounts d u, ← sumCounts e v]

end D5.S3.VertexAlgebra.PolynomialFockDeformationCovariance
