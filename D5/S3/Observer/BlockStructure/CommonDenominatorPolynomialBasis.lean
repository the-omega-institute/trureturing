/- GID: D5/S3/Observer/BlockStructure/CommonDenominatorPolynomialBasis
   generality: G
   mirror-B: D5/B/S3/Observer/BlockStructure/CommonDenominatorPolynomialBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct finite Cayley scales give a common-denominator polynomial basis. -/

import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic

/- Library-search audit trail (2026-08-29):
   * D5 searches for common-denominator polynomial bases, confluent
     partial-fraction bases, and the displayed rational features found no exact
     owner.
   * Pinned Mathlib supplies `degreeLT.basis`, the Bernstein derivative
     identities, and uniqueness of partial fractions with pairwise-coprime
     powered denominators. It has no exported complex Bernstein basis theorem
     and no theorem assembling the source family, so both bridges are proved
     locally below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Module Polynomial Submodule
open scoped BigOperators

namespace D5.S3.Observer.BlockStructure.CommonDenominatorPolynomialBasis

private theorem bernstein_linearIndependent_aux (n k : Nat) (h : k <= n + 1) :
    LinearIndependent Complex fun nu : Fin k =>
      bernsteinPolynomial Complex n nu := by
  induction k with
  | zero => exact linearIndependent_empty_type
  | succ k ih =>
    apply linearIndependent_finSucc'.mpr
    constructor
    · exact ih (le_of_lt h)
    · simp only [add_le_add_iff_right] at h
      simp only [Fin.val_last, Fin.init_def]
      dsimp
      apply notMem_span_of_apply_notMem_span_image
        (@Polynomial.derivative Complex _ ^ (n - k))
      simp only [not_exists, not_and, Submodule.mem_map, Submodule.span_image _]
      intro p m
      apply_fun Polynomial.eval (1 : Complex)
      simp only [Module.End.pow_apply]
      suffices (Polynomial.derivative^[n - k] p).eval 1 = 0 by
        rw [this]
        exact
          (bernsteinPolynomial.iterate_derivative_at_1_ne_zero
            Complex n k h).symm
      refine span_induction ?_ ?_ ?_ ?_ m
      · simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
        rintro ⟨a, w⟩
        simp only
        rw [bernsteinPolynomial.iterate_derivative_at_1_eq_zero_of_lt
          Complex n ((tsub_lt_tsub_iff_left_of_le h).mpr w)]
      · simp
      · intro x y _ _ hx hy
        simp [hx, hy]
      · intro a x _ hx
        simp [hx]

private theorem bernstein_linearIndependent_complex (n : Nat) :
    LinearIndependent Complex fun nu : Fin (n + 1) =>
      bernsteinPolynomial Complex n nu :=
  bernstein_linearIndependent_aux n (n + 1) le_rfl

private theorem affine_block_linearIndependent
    (n : Nat) (r : Complex) (hr : r ≠ 0) (hrSquare : r ^ 2 ≠ 1) :
    LinearIndependent Complex fun j : Fin (n + 1) =>
      (Polynomial.X + Polynomial.C r) ^ (j : Nat) *
        (Polynomial.X + Polynomial.C r⁻¹) ^ (n - (j : Nat)) := by
  let a : Complex := r / (r ^ 2 - 1)
  let t : Polynomial Complex := Polynomial.C a * (Polynomial.X + Polynomial.C r)
  let substitute : Polynomial Complex →ₗ[Complex] Polynomial Complex :=
    { toFun := fun p => p.comp t
      map_add' := by
        intro p q
        exact Polynomial.add_comp
      map_smul' := by
        intro c p
        simp [smul_eq_C_mul, Polynomial.mul_comp, Polynomial.C_comp] }
  have ha : a ≠ 0 := div_ne_zero hr (sub_ne_zero.mpr hrSquare)
  have tNotConstant : t ≠ Polynomial.C (t.coeff 0) := by
    intro ht
    have coefficientEquality := congrArg (fun p : Polynomial Complex => p.coeff 1) ht
    simp [t, ha] at coefficientEquality
  have substituteInjective : Function.Injective substitute := by
    intro p q hpq
    apply sub_eq_zero.mp
    have composedZero : (p - q).comp t = 0 := by
      change substitute (p - q) = 0
      rw [map_sub, hpq, sub_self]
    rcases Polynomial.comp_eq_zero_iff.mp composedZero with differenceZero | constantCase
    · exact differenceZero
    · exact (tNotConstant constantCase.2).elim
  have mappedIndependent :
      LinearIndependent Complex fun j : Fin (n + 1) =>
        (bernsteinPolynomial Complex n j).comp t := by
    exact (bernstein_linearIndependent_complex n).map'
      substitute (LinearMap.ker_eq_bot.mpr substituteInjective)
  let scale : Fin (n + 1) -> Complex := fun j =>
    (n.choose (j : Nat) : Complex) * a ^ (j : Nat) *
      (-a) ^ (n - (j : Nat))
  have scaleNonzero (j : Fin (n + 1)) : scale j ≠ 0 := by
    have choosePositive : 0 < n.choose (j : Nat) := Nat.choose_pos (by omega)
    exact mul_ne_zero
      (mul_ne_zero (Nat.cast_ne_zero.mpr choosePositive.ne')
        (pow_ne_zero _ ha))
      (pow_ne_zero _ (neg_ne_zero.mpr ha))
  let scaleUnit : Fin (n + 1) -> Complexˣ := fun j =>
    Units.mk0 (scale j) (scaleNonzero j)
  have scaledIndependent :
      LinearIndependent Complex
        (scaleUnit • fun j : Fin (n + 1) =>
          (Polynomial.X + Polynomial.C r) ^ (j : Nat) *
            (Polynomial.X + Polynomial.C r⁻¹) ^ (n - (j : Nat))) := by
    convert mappedIndependent using 1
    funext j
    simp only [Pi.smul_apply']
    dsimp only [scaleUnit]
    change scale j •
      ((Polynomial.X + Polynomial.C r) ^ (j : Nat) *
        (Polynomial.X + Polynomial.C r⁻¹) ^ (n - (j : Nat))) =
      (bernsteinPolynomial Complex n j).comp t
    rw [smul_eq_C_mul]
    change Polynomial.C (scale j) *
        ((Polynomial.X + Polynomial.C r) ^ (j : Nat) *
          (Polynomial.X + Polynomial.C r⁻¹) ^ (n - (j : Nat))) =
      (bernsteinPolynomial Complex n j).comp t
    symm
    have scalarComplement : 1 - a * r = -a * r⁻¹ := by
      dsimp only [a]
      field_simp [hr, sub_ne_zero.mpr hrSquare]
      ring
    have complementIdentity :
        1 - t = Polynomial.C (-a) *
          (Polynomial.X + Polynomial.C r⁻¹) := by
      calc
        1 - t = Polynomial.C (1 - a * r) +
            Polynomial.C (-a) * Polynomial.X := by
          dsimp only [t]
          rw [mul_add, ← Polynomial.C_mul]
          simp only [map_sub, map_one, map_mul, map_neg]
          ring
        _ = Polynomial.C (-a * r⁻¹) +
            Polynomial.C (-a) * Polynomial.X := by rw [scalarComplement]
        _ = Polynomial.C (-a) *
            (Polynomial.X + Polynomial.C r⁻¹) := by
          rw [mul_add, ← Polynomial.C_mul]
          ring
    simp only [bernsteinPolynomial, Polynomial.mul_comp, Polynomial.pow_comp,
      Polynomial.natCast_comp, Polynomial.X_comp, Polynomial.sub_comp,
      Polynomial.one_comp]
    rw [complementIdentity]
    simp only [mul_pow]
    dsimp only [t, scale]
    simp only [mul_pow, Polynomial.C_pow, Polynomial.C_mul]
    have chooseCast :
        (n.choose (j : Nat) : Polynomial Complex) =
          Polynomial.C (n.choose (j : Nat) : Complex) :=
      (Polynomial.C_eq_natCast _).symm
    rw [chooseCast]
    ring
  exact (LinearIndependent.units_smul_iff _ scaleUnit).mp scaledIndependent

/-- The numerator polynomials obtained from finitely many distinct Cayley
parameters and a common denominator form a basis of the full bounded-degree
polynomial space. -/
theorem common_denominator_polynomial_basis
    (m : Nat) (r : Fin m -> Complex) (depth : Fin m -> Nat)
    (referenceDepth : Nat)
    (rNonzero : forall i, r i ≠ 0)
    (rInjective : Function.Injective r)
    (rInDisk : forall i, ‖r i‖ < 1) :
    let multiplicity : Fin m -> Nat := fun i => depth i + 1
    let q : Nat := ∑ i, multiplicity i
    let factor : Fin m -> Polynomial Complex := fun i =>
      1 + Polynomial.C (r i) * Polynomial.X
    let denominator : Polynomial Complex :=
      ∏ i, factor i ^ multiplicity i
    let index := Sum (Sigma fun i => Fin (multiplicity i)) (Fin (referenceDepth + 1))
    let family : index -> Polynomial Complex := fun index =>
      match index with
      | Sum.inl ij =>
          (Polynomial.X + Polynomial.C (r ij.1)) ^ (ij.2 : Nat) *
            factor ij.1 ^ (depth ij.1 - (ij.2 : Nat)) *
              ∏ k ∈ Finset.univ.erase ij.1, factor k ^ multiplicity k
      | Sum.inr j => denominator * Polynomial.X ^ (j : Nat)
    LinearIndependent Complex family /\
      span Complex (Set.range family) =
        Polynomial.degreeLT Complex (q + referenceDepth + 1) := by
  dsimp only
  let multiplicity : Fin m -> Nat := fun i => depth i + 1
  let q : Nat := ∑ i, multiplicity i
  let factor : Fin m -> Polynomial Complex := fun i =>
    1 + Polynomial.C (r i) * Polynomial.X
  let denominator : Polynomial Complex := ∏ i, factor i ^ multiplicity i
  let index := Sum (Sigma fun i => Fin (multiplicity i)) (Fin (referenceDepth + 1))
  let family : index -> Polynomial Complex := fun index =>
    match index with
    | Sum.inl ij =>
        (Polynomial.X + Polynomial.C (r ij.1)) ^ (ij.2 : Nat) *
          factor ij.1 ^ (depth ij.1 - (ij.2 : Nat)) *
            ∏ k ∈ Finset.univ.erase ij.1, factor k ^ multiplicity k
    | Sum.inr j => denominator * Polynomial.X ^ (j : Nat)
  change LinearIndependent Complex family /\
    span Complex (Set.range family) =
      Polynomial.degreeLT Complex (q + referenceDepth + 1)
  let root : Fin m -> Complex := fun i => -(r i)⁻¹
  let monicFactor : Fin m -> Polynomial Complex := fun i =>
    Polynomial.X - Polynomial.C (root i)
  let monicDenominator : Polynomial Complex :=
    ∏ i, monicFactor i ^ multiplicity i
  let normalizedFamily : index -> Polynomial Complex := fun index =>
    match index with
    | Sum.inl ij =>
        (Polynomial.X + Polynomial.C (r ij.1)) ^ (ij.2 : Nat) *
          monicFactor ij.1 ^ (depth ij.1 - (ij.2 : Nat)) *
            ∏ k ∈ Finset.univ.erase ij.1,
              monicFactor k ^ multiplicity k
    | Sum.inr j => monicDenominator * Polynomial.X ^ (j : Nat)
  have rootInjective : Function.Injective root := by
    intro i j hij
    apply rInjective
    dsimp only [root] at hij
    exact inv_injective (neg_injective hij)
  have monicFactors (i : Fin m) : (monicFactor i).Monic := by
    exact Polynomial.monic_X_sub_C _
  have pairwiseCoprime :
      Set.Pairwise (Finset.univ : Finset (Fin m)) fun i j =>
        IsCoprime (monicFactor i) (monicFactor j) := by
    intro i _ j _ hij
    exact Polynomial.pairwise_coprime_X_sub_C rootInjective hij
  have squareSeparated (i : Fin m) : r i ^ 2 ≠ 1 := by
    intro hsquare
    have normSquare := congrArg norm hsquare
    rw [norm_pow, norm_one] at normSquare
    nlinarith [norm_nonneg (r i), rInDisk i]
  have localIndependent (i : Fin m) :
      LinearIndependent Complex fun j : Fin (multiplicity i) =>
        (Polynomial.X + Polynomial.C (r i)) ^ (j : Nat) *
          monicFactor i ^ (depth i - (j : Nat)) := by
    simpa only [multiplicity, monicFactor, root, Polynomial.C_neg,
      sub_neg_eq_add] using
      affine_block_linearIndependent (depth i) (r i)
        (rNonzero i) (squareSeparated i)
  have monomialIndependent :
      LinearIndependent Complex fun j : Fin (referenceDepth + 1) =>
        (Polynomial.X : Polynomial Complex) ^ (j : Nat) := by
    have basisIndependent :=
      (Polynomial.degreeLT.basis Complex (referenceDepth + 1)).linearIndependent.map'
        (Polynomial.degreeLT Complex (referenceDepth + 1)).subtype
        (Submodule.ker_subtype _)
    have familyEquality :
        (fun j : Fin (referenceDepth + 1) =>
          (Polynomial.X : Polynomial Complex) ^ (j : Nat)) =
          (Polynomial.degreeLT Complex (referenceDepth + 1)).subtype ∘
            Polynomial.degreeLT.basis Complex (referenceDepth + 1) := by
      funext j
      exact (Polynomial.degreeLT.basis_val (R := Complex) j).symm
    rw [familyEquality]
    exact basisIndependent
  have normalizedIndependent :
      LinearIndependent Complex normalizedFamily := by
    rw [Fintype.linearIndependent_iff]
    intro coefficient combinationZero indexValue
    let localRemainder : Fin m -> Polynomial Complex := fun i =>
      ∑ j : Fin (multiplicity i), coefficient (Sum.inl ⟨i, j⟩) •
        ((Polynomial.X + Polynomial.C (r i)) ^ (j : Nat) *
          monicFactor i ^ (depth i - (j : Nat)))
    let quotient : Polynomial Complex :=
      ∑ j : Fin (referenceDepth + 1),
        coefficient (Sum.inr j) • Polynomial.X ^ (j : Nat)
    have remainderDegree (i : Fin m) :
        (localRemainder i).degree < (monicFactor i ^ multiplicity i).degree := by
      have localMembership :
          localRemainder i ∈ Polynomial.degreeLT Complex (multiplicity i) := by
        dsimp only [localRemainder]
        apply Submodule.sum_mem
        intro j _
        apply Submodule.smul_mem
        rw [Polynomial.mem_degreeLT]
        have localMonic :
            ((Polynomial.X + Polynomial.C (r i)) ^ (j : Nat) *
              monicFactor i ^ (depth i - (j : Nat))).Monic :=
          ((Polynomial.monic_X_add_C _).pow _).mul ((monicFactors i).pow _)
        rw [Polynomial.degree_eq_natDegree localMonic.ne_zero]
        norm_cast
        rw [((Polynomial.monic_X_add_C _).pow _).natDegree_mul
          ((monicFactors i).pow _),
          (Polynomial.monic_X_add_C _).natDegree_pow,
          (monicFactors i).natDegree_pow, Polynomial.natDegree_X_add_C]
        simp only [monicFactor, root, Polynomial.natDegree_X_sub_C, mul_one]
        simp only [multiplicity]
        omega
      have localDegree := Polynomial.mem_degreeLT.mp localMembership
      rw [Polynomial.degree_pow, show (monicFactor i).degree = 1 by
        simp only [monicFactor, root, Polynomial.degree_X_sub_C]]
      simpa only [multiplicity, Nat.cast_add, Nat.cast_one, nsmul_eq_mul,
        mul_one] using localDegree
    have combinationSplit :
        (∑ ij : Sigma fun i => Fin (multiplicity i),
            coefficient (Sum.inl ij) • normalizedFamily (Sum.inl ij)) +
          ∑ j : Fin (referenceDepth + 1),
            coefficient (Sum.inr j) • normalizedFamily (Sum.inr j) = 0 := by
      simpa only [index, Fintype.sum_sum_type] using combinationZero
    have decompositionEquality :
        quotient * monicDenominator +
            ∑ i, localRemainder i *
              ∏ k ∈ Finset.univ.erase i,
                monicFactor k ^ multiplicity k =
          0 * monicDenominator +
            ∑ i, (0 : Polynomial Complex) *
              ∏ k ∈ Finset.univ.erase i,
                monicFactor k ^ multiplicity k := by
      simp only [zero_mul, Finset.sum_const_zero, add_zero]
      calc
        quotient * monicDenominator +
              ∑ i, localRemainder i *
                ∏ k ∈ Finset.univ.erase i,
                  monicFactor k ^ multiplicity k =
            (∑ j : Fin (referenceDepth + 1),
                coefficient (Sum.inr j) • normalizedFamily (Sum.inr j)) +
              ∑ i, ∑ j : Fin (multiplicity i),
                coefficient (Sum.inl ⟨i, j⟩) •
                  normalizedFamily (Sum.inl ⟨i, j⟩) := by
            apply congrArg₂ (· + ·)
            · dsimp only [quotient, normalizedFamily]
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j _
              simp only [smul_eq_C_mul]
              ring
            · apply Finset.sum_congr rfl
              intro i _
              dsimp only [localRemainder, normalizedFamily]
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j _
              simp only [smul_eq_C_mul]
              ring
        _ = (∑ ij : Sigma fun i => Fin (multiplicity i),
              coefficient (Sum.inl ij) • normalizedFamily (Sum.inl ij)) +
            ∑ j : Fin (referenceDepth + 1),
              coefficient (Sum.inr j) • normalizedFamily (Sum.inr j) := by
            rw [Fintype.sum_sigma]
            exact add_comm _ _
        _ = 0 := combinationSplit
    have uniqueDecomposition :=
      Polynomial.quo_mul_prod_add_sum_rem_mul_prod_unique
        (s := (Finset.univ : Finset (Fin m)))
        (g := fun i => monicFactor i ^ multiplicity i)
        (fun i _ => (monicFactors i).pow _)
        (pairwiseCoprime.imp fun _ _ hij => hij.pow)
        (q₁ := quotient) (q₂ := 0)
        (r₁ := localRemainder) (r₂ := fun _ => 0)
        (fun i _ => remainderDegree i)
        (fun i _ => by
          rw [Polynomial.degree_pow]
          simp [multiplicity, monicFactor, root])
        decompositionEquality
    cases indexValue with
    | inl ij =>
        have localZero :
            ∑ j : Fin (multiplicity ij.1),
              coefficient (Sum.inl ⟨ij.1, j⟩) •
                ((Polynomial.X + Polynomial.C (r ij.1)) ^ (j : Nat) *
                  monicFactor ij.1 ^ (depth ij.1 - (j : Nat))) = 0 := by
          simpa only [localRemainder] using
            uniqueDecomposition.2 ij.1 (Finset.mem_univ ij.1)
        exact (Fintype.linearIndependent_iff.mp (localIndependent ij.1)
          (fun j => coefficient (Sum.inl ⟨ij.1, j⟩))
          localZero ij.2)
    | inr j =>
        exact (Fintype.linearIndependent_iff.mp monomialIndependent
          (fun j => coefficient (Sum.inr j))
          (by simpa only [quotient] using uniqueDecomposition.1) j)
  have factorIdentity (i : Fin m) :
      factor i = Polynomial.C (r i) * monicFactor i := by
    dsimp only [factor, monicFactor, root]
    simp only [Polynomial.C_neg, sub_neg_eq_add, mul_add, ← Polynomial.C_mul]
    simp [rNonzero i]
    ring
  let scale : index -> Complex := fun index =>
    match index with
    | Sum.inl ij =>
        r ij.1 ^ (depth ij.1 - (ij.2 : Nat)) *
          ∏ k ∈ Finset.univ.erase ij.1, r k ^ multiplicity k
    | Sum.inr _ => ∏ k, r k ^ multiplicity k
  have scaleNonzero (indexValue : index) : scale indexValue ≠ 0 := by
    cases indexValue with
    | inl ij =>
        exact mul_ne_zero (pow_ne_zero _ (rNonzero ij.1))
          (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (rNonzero k))
    | inr j =>
        exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (rNonzero k)
  let scaleUnit : index -> Complexˣ := fun indexValue =>
    Units.mk0 (scale indexValue) (scaleNonzero indexValue)
  have scaleConstantInl (ij : Sigma fun i => Fin (multiplicity i)) :
      Polynomial.C (scale (Sum.inl ij)) =
        Polynomial.C (r ij.1) ^ (depth ij.1 - (ij.2 : Nat)) *
          ∏ k ∈ Finset.univ.erase ij.1,
            Polynomial.C (r k) ^ multiplicity k := by
    dsimp only [scale]
    rw [map_mul, map_pow, map_prod Polynomial.C]
    simp only [map_pow]
  have scaleConstantInr (j : Fin (referenceDepth + 1)) :
      Polynomial.C (scale (Sum.inr j)) =
        ∏ k, Polynomial.C (r k) ^ multiplicity k := by
    dsimp only [scale]
    rw [map_prod Polynomial.C]
    simp only [map_pow]
  have familyAsScaled : family = scaleUnit • normalizedFamily := by
    funext indexValue
    simp only [Pi.smul_apply']
    cases indexValue with
    | inl ij =>
        dsimp only [scaleUnit]
        change family (Sum.inl ij) = scale (Sum.inl ij) •
          normalizedFamily (Sum.inl ij)
        rw [smul_eq_C_mul]
        change (Polynomial.X + Polynomial.C (r ij.1)) ^ (ij.2 : Nat) *
            factor ij.1 ^ (depth ij.1 - (ij.2 : Nat)) *
              ∏ k ∈ Finset.univ.erase ij.1, factor k ^ multiplicity k =
          Polynomial.C (scale (Sum.inl ij)) *
            ((Polynomial.X + Polynomial.C (r ij.1)) ^ (ij.2 : Nat) *
              monicFactor ij.1 ^ (depth ij.1 - (ij.2 : Nat)) *
                ∏ k ∈ Finset.univ.erase ij.1,
                  monicFactor k ^ multiplicity k)
        simp_rw [factorIdentity, mul_pow]
        rw [scaleConstantInl ij]
        simp only [Finset.prod_mul_distrib]
        ring
    | inr j =>
        dsimp only [scaleUnit]
        change family (Sum.inr j) = scale (Sum.inr j) •
          normalizedFamily (Sum.inr j)
        rw [smul_eq_C_mul]
        change denominator * Polynomial.X ^ (j : Nat) =
          Polynomial.C (scale (Sum.inr j)) *
            (monicDenominator * Polynomial.X ^ (j : Nat))
        dsimp only [denominator, monicDenominator]
        simp_rw [factorIdentity, mul_pow]
        rw [scaleConstantInr j]
        simp only [Finset.prod_mul_distrib]
        ring
  have familyIndependent : LinearIndependent Complex family := by
    rw [familyAsScaled]
    exact normalizedIndependent.units_smul scaleUnit
  refine ⟨familyIndependent, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    intro polynomial polynomialInRange
    rcases polynomialInRange with ⟨indexValue, rfl⟩
    rw [familyAsScaled]
    change (scaleUnit indexValue : Complex) • normalizedFamily indexValue ∈
      Polynomial.degreeLT Complex (q + referenceDepth + 1)
    apply Submodule.smul_mem
    rw [Polynomial.mem_degreeLT]
    cases indexValue with
    | inl ij =>
        have normalizedMonic :
            (normalizedFamily (Sum.inl ij)).Monic := by
          exact (((Polynomial.monic_X_add_C _).pow _).mul
            ((monicFactors ij.1).pow _)).mul
              (Polynomial.monic_prod_of_monic _ _ fun k _ =>
                (monicFactors k).pow _)
        rw [Polynomial.degree_eq_natDegree normalizedMonic.ne_zero]
        norm_cast
        dsimp only [normalizedFamily]
        rw [(((Polynomial.monic_X_add_C _).pow _).mul
            ((monicFactors ij.1).pow _)).natDegree_mul
              (Polynomial.monic_prod_of_monic _ _ fun k _ =>
                (monicFactors k).pow _),
          ((Polynomial.monic_X_add_C _).pow _).natDegree_mul
            ((monicFactors ij.1).pow _),
          (Polynomial.monic_X_add_C _).natDegree_pow,
          (monicFactors ij.1).natDegree_pow,
          Polynomial.natDegree_X_add_C,
          Polynomial.natDegree_prod_of_monic]
        · simp [multiplicity, q, monicFactor, root]
          have eraseIdentity :
              (∑ k ∈ (Finset.univ.erase ij.1), (depth k + 1)) +
                  (depth ij.1 + 1) = ∑ k : Fin m, (depth k + 1) :=
            Finset.sum_erase_add _ _ (Finset.mem_univ ij.1)
          omega
        · intro k hk
          exact (monicFactors k).pow _
    | inr j =>
        have denominatorMonic : monicDenominator.Monic :=
          Polynomial.monic_prod_of_monic _ _ fun i _ => (monicFactors i).pow _
        have normalizedMonic :
            (normalizedFamily (Sum.inr j)).Monic :=
          denominatorMonic.mul (Polynomial.monic_X_pow _)
        rw [Polynomial.degree_eq_natDegree normalizedMonic.ne_zero]
        norm_cast
        dsimp only [normalizedFamily]
        rw [denominatorMonic.natDegree_mul (Polynomial.monic_X_pow _),
          Polynomial.natDegree_prod_of_monic,
          Polynomial.natDegree_X_pow]
        · simp_rw [(monicFactors _).natDegree_pow]
          simp only [monicFactor, root, Polynomial.natDegree_X_sub_C, mul_one,
            multiplicity, q]
          omega
        · intro i hi
          exact (monicFactors i).pow _
  · rw [finrank_span_eq_card familyIndependent]
    rw [Module.finrank_eq_card_basis
      (Polynomial.degreeLT.basis Complex (q + referenceDepth + 1))]
    simp only [index, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin,
      q, multiplicity]
    omega

#print axioms common_denominator_polynomial_basis

end D5.S3.Observer.BlockStructure.CommonDenominatorPolynomialBasis
