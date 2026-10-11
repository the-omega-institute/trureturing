/- GID: D5/S3/VertexAlgebra/PolynomialFockC2
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/PolynomialFockC2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual nonpositive Fock modes identify the C2 subspace with the higher-variable ideal. -/

/-
proof_shape: actual_c2_modes: content
escape_witness: A simultaneous induction over arbitrary normal-product words,
inputs and nonpositive modes uses raw statewise truncation before projection.
Actual singleton minus-two coefficients generate every higher-variable multiple.
admission_basis: escape-witness
Classical background: Arakawa, arXiv:1605.00138v2, Section 3.8; Li,
arXiv:math/0409140v1, Corollary 3.6 and Proposition 3.7; Matsuo--Nagatomo,
hep-th/9704060v1, Sections 2.1--2.3. No mathematical novelty is asserted.
-/

import D5.S3.VertexAlgebra.PolynomialFockJacobi
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.MvPolynomial.Equiv

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.PolynomialFockC2

open MvPolynomial
open D5.S3.VertexAlgebra.PolynomialFockSugawaraSupport
open D5.S3.VertexAlgebra.PolynomialFockStateField
open D5.S3.VertexAlgebra.FieldNormalProduct
open scoped VertexOperator

/-- Keep the first variable and set every higher variable to zero. -/
noncomputable def pi : Fock →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval (fun i : ℕ => if i = 0 then Polynomial.X else 0)

/-- The complex span of actual minus-two state-field coefficients. -/
noncomputable def C2 : Submodule ℂ Fock :=
  Submodule.span ℂ {w | ∃ u v : Fock, w = PolynomialFockJacobi.mu u (-2) v}

set_option backward.isDefEq.respectTransparency false in
/-- The actual C2 subspace and every nonpositive mode on arbitrary polynomial inputs. -/
theorem actual_c2_modes :
    C2 = (Ideal.span (MvPolynomial.X '' {i : ℕ | 1 ≤ i} : Set Fock)).restrictScalars ℂ ∧
    C2 = LinearMap.ker pi.toLinearMap ∧
    ∀ (u v : Fock) (n : ℤ), n ≤ 0 →
      pi (PolynomialFockJacobi.mu u n v) = if n = -1 then pi u * pi v else 0 := by
  classical
  have identityModes (n : ℤ) :
      ((identityField : VertexOperator ℂ Fock) [[n]]) =
        if n = -1 then LinearMap.id else 0 := by
    rw [identityField, VertexOperator.ncoeff_of_coeff]
    simp only [show -n - 1 = 0 ↔ n = -1 by omega]
  have currentModes (n : ℤ) : (current [[n]]) = mode n := by
    rw [current, VertexOperator.ncoeff_of_coeff]
    rw [show -(-n - 1) - 1 = n by omega]
  have derivativeModes (j : ℕ) (n : ℤ) :
      ((dividedDerivative j current) [[n]]) =
        ((Ring.choose (-n - 1 + j) j : ℤ) : ℂ) • mode (n - j) := by
    apply LinearMap.ext
    intro v
    change Ring.choose (-n - 1 + j) j •
      HVertexOperator.coeff current (-n - 1 + j) v = _
    rw [VertexOperator.coeff_eq_ncoeff, currentModes]
    rw [show -(-n - 1 + j) - 1 = n - j by omega]
    simp only [LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
  have negativeDerivative (j k : ℕ) (v : Fock) :
      ((dividedDerivative j current) [[-(k : ℤ) - 1]]) v =
        (((j + k).choose j : ℕ) : ℂ) • ((X (j + k) : Fock) * v) := by
    rw [derivativeModes, LinearMap.smul_apply]
    rw [show -(-(k : ℤ) - 1) - 1 + j = ((j + k : ℕ) : ℤ) by omega,
      Ring.choose_natCast]
    rw [show -(k : ℤ) - 1 - j = Int.negSucc (j + k) by omega]
    simp [mode, create]
  have derivativeAtZero (j : ℕ) (v : Fock) :
      ((dividedDerivative j current) [[0]]) v = 0 := by
    rw [derivativeModes, LinearMap.smul_apply]
    cases j with
    | zero => simp [mode]
    | succ j =>
      rw [show -(0 : ℤ) - 1 + (j + 1 : ℕ) = (j : ℤ) by omega,
        Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
      simp
  -- Both bounds refer to the original polynomial-valued summands.
  have leftFinite (left right : VertexOperator ℂ Fock) (n : ℤ) (v : Fock) :
      Function.HasFiniteSupport (fun k : ℕ =>
        (left [[-(k : ℤ) - 1]]) ((right [[n + k]]) v)) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (right v)).order - n).toNat, ?_⟩
    intro k hk
    contrapose! hk
    have hz : (right [[n + k]]) v = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    simp [hz]
  have rightFinite (left right : VertexOperator ℂ Fock) (n : ℤ) (v : Fock) :
      Function.HasFiniteSupport (fun k : ℕ =>
        (right [[n - k - 1]]) ((left [[k]]) v)) := by
    refine BddAbove.finite (bddAbove_def.mpr ?_)
    refine ⟨(-((HahnModule.of ℂ).symm (left v)).order - 1).toNat, ?_⟩
    intro k hk
    contrapose! hk
    have hz : (left [[(k : ℤ)]]) v = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    simp [hz]
  have wordModes : ∀ (w : List ℕ) (v : Fock) (n : ℤ), n ≤ 0 →
      pi (((wordField w) [[n]]) v) =
        if n = -1 then pi ((w.map (fun j => (X j : Fock))).prod) * pi v else 0 := by
    intro w
    induction w with
    | nil =>
      intro v n hn
      simp only [wordField, identityModes, List.map_nil, List.prod_nil, map_one]
      split_ifs <;> simp
    | cons j w ih =>
      intro v n hn
      rw [wordField, (normalMinusOne (dividedDerivative j current) (wordField w)).2,
        map_add, map_finsum pi (leftFinite _ _ n v),
        map_finsum pi (rightFinite _ _ n v)]
      have rightZero (k : ℕ) :
          pi (((wordField w) [[n - k - 1]])
            (((dividedDerivative j current) [[(k : ℤ)]]) v)) = 0 := by
        by_cases hk : k = 0
        · subst k
          simp only [Nat.cast_zero]
          rw [derivativeAtZero, map_zero, map_zero]
        · rw [ih _ _ (by omega), if_neg (by omega)]
      simp only [rightZero, finsum_zero, add_zero]
      have leftZero (k : ℕ) (hk : k ≠ 0) :
          pi (((dividedDerivative j current) [[-(k : ℤ) - 1]])
            (((wordField w) [[n + k]]) v)) = 0 := by
        rw [negativeDerivative, map_smul, map_mul]
        have hz : pi (X (j + k)) = 0 := by
          rw [pi, aeval_X, if_neg (by omega)]
        rw [hz, zero_mul, smul_zero]
      rw [finsum_eq_single _ 0 leftZero, negativeDerivative, Nat.add_zero,
        Nat.choose_self, Nat.cast_one, one_smul, map_mul, Nat.cast_zero, add_zero, ih v n hn]
      simp only [List.map_cons, List.prod_cons, map_mul]
      split_ifs <;> simp [mul_assoc]
  have allModes (u v : Fock) (n : ℤ) (hn : n ≤ 0) :
      pi (PolynomialFockJacobi.mu u n v) = if n = -1 then pi u * pi v else 0 := by
    induction u using MvPolynomial.induction_on' with
    | monomial m c =>
      have fieldEquality : Y (monomial m (1 : ℂ)) = wordField (occurrences m) :=
        (basisMonomials ℕ ℂ).constr_basis ℂ _ m
      have productEquality : pi (( (occurrences m).map (fun j => (X j : Fock))).prod) =
          pi (monomial m (1 : ℂ)) := by
        have h := wordModes (occurrences m) (1 : Fock) (-1) (by omega)
        rw [← fieldEquality, stateField_creation.2.2.1] at h
        simpa using h.symm
      have scaled : monomial m c = c • monomial m (1 : ℂ) := by
        rw [smul_monomial]
        simp
      rw [scaled]
      simp only [PolynomialFockJacobi.mu, map_smul, Pi.smul_apply, LinearMap.smul_apply,
        fieldEquality, wordModes _ _ _ hn, productEquality]
      split_ifs <;> simp [Algebra.smul_mul_assoc]
    | add p q hp hq =>
      simp only [PolynomialFockJacobi.mu, map_add, Pi.add_apply, LinearMap.add_apply] at *
      rw [hp, hq]
      split_ifs <;> simp [add_mul]
  have c2Kernel : C2 ≤ LinearMap.ker pi.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro z ⟨u, v, rfl⟩
    change pi (PolynomialFockJacobi.mu u (-2) v) = 0
    simpa using allModes u v (-2) (by omega)
  have singletonMinusTwo (j : ℕ) (v : Fock) :
      PolynomialFockJacobi.mu (X j) (-2) v =
        (j + 1 : ℂ) • ((X (j + 1) : Fock) * v) := by
    have oneWord : occurrences (Finsupp.single j 1) = [j] := by
      simp [occurrences, Finsupp.toMultiset_single]
    have fieldEquality : Y (X j) = wordField [j] := by
      simpa only [Y, X, coe_basisMonomials, oneWord] using
        (basisMonomials ℕ ℂ).constr_basis ℂ
          (fun m => wordField (occurrences m)) (Finsupp.single j 1)
    rw [PolynomialFockJacobi.mu, fieldEquality, wordField, wordField,
      (normalMinusOne (dividedDerivative j current) identityField).2]
    have secondZero (k : ℕ) :
        ((identityField : VertexOperator ℂ Fock) [[-2 - k - 1]])
          (((dividedDerivative j current) [[(k : ℤ)]]) v) = 0 := by
      simp [identityModes, show (-2 : ℤ) - k - 1 ≠ -1 by omega]
    simp only [secondZero, finsum_zero, add_zero]
    rw [finsum_eq_single _ 1]
    · simp only [show (-2 : ℤ) + (1 : ℕ) = -1 by omega, identityModes]
      rw [negativeDerivative]
      simp [Nat.choose_succ_self_right]
    · intro k hk
      simp [identityModes, show (-2 : ℤ) + k ≠ -1 by omega]
  have higherMultiple (i : ℕ) (hi : 1 ≤ i) (v : Fock) : (X i : Fock) * v ∈ C2 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    have hc : (j + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have hm : PolynomialFockJacobi.mu (X j) (-2) v ∈ C2 :=
      Submodule.subset_span ⟨X j, v, rfl⟩
    have hs := C2.smul_mem (j + 1 : ℂ)⁻¹ hm
    rw [singletonMinusTwo, smul_smul, inv_mul_cancel₀ hc, one_smul] at hs
    exact hs
  let I : Ideal Fock := Ideal.span (MvPolynomial.X '' {i : ℕ | 1 ≤ i})
  have idealC2 : I.restrictScalars ℂ ≤ C2 := by
    intro p hp
    have supportCondition := (MvPolynomial.mem_ideal_span_X_image).mp hp
    rw [p.as_sum]
    apply Submodule.sum_mem
    intro m hm
    obtain ⟨i, hi, hmi⟩ := supportCondition m hm
    have factor : monomial m (AddMonoidAlgebra.coeff p m) =
        (X i : Fock) * monomial (m - Finsupp.single i 1) (AddMonoidAlgebra.coeff p m) := by
      rw [X, monomial_mul, one_mul]
      have hle : Finsupp.single i 1 ≤ m :=
        Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hmi)
      rw [add_tsub_cancel_of_le hle]
    rw [factor]
    exact higherMultiple i hi _
  let f : Unit → ℕ := fun _ => 0
  have hf : Function.Injective f := fun _ _ _ => Subsingleton.elim _ _
  let kill : Fock →ₐ[ℂ] MvPolynomial Unit ℂ := MvPolynomial.killCompl hf
  let e : MvPolynomial Unit ℂ ≃ₐ[ℂ] Polynomial ℂ := MvPolynomial.uniqueAlgEquiv ℂ Unit
  have factorPi : e.toAlgHom.comp kill = pi := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i = 0
    · subst i
      simp [kill, MvPolynomial.killCompl, f, e, pi, MvPolynomial.uniqueAlgEquiv]
    · simp [kill, MvPolynomial.killCompl, f, e, pi, hi]
  have kernelIdeal : LinearMap.ker pi.toLinearMap ≤ I.restrictScalars ℂ := by
    intro p hp
    change pi p = 0 at hp
    have hkill : kill p = 0 := by
      apply e.injective
      rw [map_zero]
      change (e.toAlgHom.comp kill) p = 0
      rw [factorPi, hp]
    apply MvPolynomial.mem_ideal_span_X_image.mpr
    intro m hm
    by_contra hnone
    have hvanish : ∀ i : ℕ, 1 ≤ i → m i = 0 := by
      intro i hi
      by_contra hmi
      exact hnone ⟨i, hi, hmi⟩
    have hmSingle : m = Finsupp.single 0 (m 0) := by
      ext i
      by_cases hi : i = 0
      · subst i; simp
      · simp [hi, hvanish i (by omega)]
    have hcoeff := congrArg ((fun p => AddMonoidAlgebra.coeff p (Finsupp.single () (m 0)))) hkill
    rw [show kill p = MvPolynomial.killCompl hf p from rfl,
      MvPolynomial.coeff_killCompl] at hcoeff
    simp only [MvPolynomial.coeff_zero, Finsupp.mapDomain_single, f] at hcoeff
    exact (MvPolynomial.mem_support_iff.mp hm) (by simpa [← hmSingle] using hcoeff)
  have c2Ideal : C2 = I.restrictScalars ℂ :=
    le_antisymm (c2Kernel.trans kernelIdeal) idealC2
  have c2EqualsKernel : C2 = LinearMap.ker pi.toLinearMap :=
    le_antisymm c2Kernel (kernelIdeal.trans idealC2)
  exact ⟨c2Ideal, c2EqualsKernel, allModes⟩

end D5.S3.VertexAlgebra.PolynomialFockC2
