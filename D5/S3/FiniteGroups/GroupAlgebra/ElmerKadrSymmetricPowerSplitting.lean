/- GID: D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrSymmetricPowerSplitting
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/ElmerKadrSymmetricPowerSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.TensorPower.Symmetric, mathlib/module/Mathlib.Data.Nat.Choose.Lucas]
   utility: none
   digest: Actual splitting of the ordered coefficient-sum copy in symmetric powers of V_(p+1). -/

import D5.S3.FiniteGroups.GroupAlgebra.SymmetricPowerBlockSplitting
import D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrResidueCriterion
import D5.S3.FiniteGroups.GroupAlgebra.EmbeddedOriginalClassification
import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.LinearAlgebra.Basis.SMul

/-!
The target is the actual direct-summand question after Lemma 3.9 of
Elmer--Kadr, arXiv:2510.07939v1, Section 3.2,
DOI 10.1007/s13366-026-00855-9. Relative stable isomorphism is not used.

Binary bounded polarization is iterated before any scalar is inverted.
Multiplication composed with this ordered block map is k! times the
identity in characteristic p. Only k! is inverted for k < p. The raw dual
of multiplication has exactly the ordered coefficient sums as its image;
the quotient retraction is obtained by averaging the dual block map.

The exact Fin-index Mathlib quotient requires K : Type. The original W
and the elementary abelian group retain independent universes. The proof
does not require K finite or any comparison between polynomial degree
and group order; the splitting retains 1 <= k < p. Thus it includes the
paper's finite elementary abelian range q >= p^2.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrSymmetricPowerSplitting

open Module Polynomial ElmerKadrTensorCounterexample ElmerKadrPositiveCriterion
open PolynomialKernelPolarization EmbeddedOriginalClassification
open SymmetricPowerBlockSplitting
open ElmerKadrTensorCounterexample.SymmetricPowerTranslation
open scoped TensorProduct

universe uE uW

variable {K : Type} [Field K]

/-- Recursive notation keeps all intermediate bounded tensor domains literally
equal. The public endpoint is converted to p*k by blockLength_eq. -/
abbrev blockLength (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => p + blockLength p n

theorem blockLength_eq (p n : ℕ) : blockLength p n = p * n := by
  induction n with
  | zero => simp [blockLength]
  | succ n ih => simp only [blockLength, ih, Nat.mul_succ]; omega

def blockDegree (p n : ℕ) (t : Fin n → Fin (p + 1)) : Fin (blockLength p n + 1) :=
  ⟨∑ j, (t j).val, by
    have h : (∑ j, (t j).val) ≤ ∑ _ : Fin n, p :=
      Finset.sum_le_sum (fun j _ => Nat.le_of_lt_succ (t j).isLt)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rw [blockLength_eq]
    exact Nat.lt_succ_of_le (by simpa [Nat.mul_comm] using h)⟩

def blockTensorBasis (p n : ℕ) :
    Basis (Fin n → Fin (p + 1)) K (Tensor (K := K) n (Primal K (p + 1))) :=
  Basis.piTensorProduct (fun _ => Polynomial.degreeLT.basis K (p + 1))

/-- Ordinary product of all bounded polynomial factors. -/
def blockMultiplication (p n : ℕ) :
    Tensor (K := K) n (Primal K (p + 1)) →ₗ[K] Primal K (blockLength p n + 1) :=
  (blockTensorBasis (K := K) p n).constr K
    (fun t => Polynomial.degreeLT.basis K (blockLength p n + 1) (blockDegree p n t))

@[simp] theorem blockMultiplication_basis (p n : ℕ) (t : Fin n → Fin (p + 1)) :
    blockMultiplication (K := K) p n
      (PiTensorProduct.tprod K (fun j => Polynomial.degreeLT.basis K (p + 1) (t j))) =
      Polynomial.degreeLT.basis K (blockLength p n + 1) (blockDegree p n t) := by
  simpa only [blockMultiplication, blockTensorBasis, Basis.piTensorProduct_apply] using
    (blockTensorBasis (K := K) p n).constr_basis K
      (fun t => Polynomial.degreeLT.basis K (blockLength p n + 1) (blockDegree p n t)) t

theorem blockMultiplication_coe_tprod (p n : ℕ) (v : Fin n → Primal K (p + 1)) :
    (blockMultiplication p n (PiTensorProduct.tprod K v) : K[X]) = ∏ j, (v j : K[X]) := by
  have h : (Polynomial.degreeLT K (blockLength p n + 1)).subtype.comp
        (blockMultiplication p n) =
      PiTensorProduct.lift
        ((MultilinearMap.mkPiAlgebra K (Fin n) K[X]).compLinearMap
          (fun _ => (Polynomial.degreeLT K (p + 1)).subtype)) := by
    apply (blockTensorBasis (K := K) p n).ext
    intro t
    simp only [blockTensorBasis, Basis.piTensorProduct_apply, LinearMap.comp_apply,
      blockMultiplication_basis, Submodule.subtype_apply, Polynomial.degreeLT.basis_val,
      PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, blockDegree]
    exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun j => (t j).val) (X : K[X])).symm
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply] using
    LinearMap.congr_fun h (PiTensorProduct.tprod K v)

def blockMultiplicationIntertwiner (p n : ℕ) :
    (SymmetricPowerBlockSplitting.tensorAction (primalAction K (p + 1)) n).IntertwiningMap
      (primalAction K (blockLength p n + 1)) where
  toLinearMap := blockMultiplication p n
  isIntertwining' g := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, tensorAction_tprod]
    apply Subtype.ext
    change (blockMultiplication p n
      (PiTensorProduct.tprod K (fun j => primalAction K (p + 1) g (v j))) : K[X]) =
      Polynomial.taylor (Multiplicative.toAdd g)
        (blockMultiplication p n (PiTensorProduct.tprod K v) : K[X])
    rw [blockMultiplication_coe_tprod, blockMultiplication_coe_tprod]
    exact (map_prod (Polynomial.taylorAlgHom (Multiplicative.toAdd g))
      (fun j : Fin n => (v j : K[X])) Finset.univ).symm

theorem blockMultiplication_permutation (p n : ℕ) (e : Equiv.Perm (Fin n)) :
    (blockMultiplication (K := K) p n).comp (permutation n e) = blockMultiplication p n := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  apply Subtype.ext
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    permutation_tprod, blockMultiplication_coe_tprod]
  exact Equiv.prod_comp e (fun j => (v j : K[X]))

private theorem multiplication_coe_tmul (n m : ℕ)
    (a : Primal K (n + 1)) (b : Primal K (m + 1)) :
    (multiplication n m (a ⊗ₜ[K] b) : K[X]) = (a : K[X]) * (b : K[X]) := by
  have h : (Polynomial.degreeLT K (n + m + 1)).subtype.comp (multiplication n m) =
      (LinearMap.mul' K K[X]).comp
        (TensorProduct.map (Polynomial.degreeLT K (n + 1)).subtype
          (Polynomial.degreeLT K (m + 1)).subtype) := by
    apply (tensorBasis (R := K) n m).ext
    rintro ⟨i, j⟩
    simp only [tensorBasis, Basis.tensorProduct_apply, LinearMap.comp_apply,
      multiplication_basis, TensorProduct.map_tmul, LinearMap.mul'_apply,
      Submodule.subtype_apply, Polynomial.degreeLT.basis_val, pow_add]
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, TensorProduct.map_tmul,
    LinearMap.mul'_apply] using LinearMap.congr_fun h (a ⊗ₜ[K] b)

private theorem multiplication_cons (p n : ℕ) :
    (blockMultiplication (K := K) p (n + 1)).comp (consTensor n) =
      (multiplication p (blockLength p n)).comp
        (TensorProduct.map LinearMap.id (blockMultiplication p n)) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  apply Subtype.ext
  change (blockMultiplication p (n + 1)
      (consTensor n (a ⊗ₜ[K] PiTensorProduct.tprod K v)) : K[X]) =
    (multiplication p (blockLength p n)
      (a ⊗ₜ[K] blockMultiplication p n (PiTensorProduct.tprod K v)) : K[X])
  rw [consTensor_tmul_tprod, blockMultiplication_coe_tprod,
    multiplication_coe_tmul, blockMultiplication_coe_tprod, Fin.prod_univ_succ]
  rfl

private def boundedPolarizationIntertwiner (n m : ℕ) :
    (primalAction K (n + m + 1)).IntertwiningMap
      ((primalAction K (n + 1)).tprod (primalAction K (m + 1))) where
  toLinearMap := boundedPolarization n m
  isIntertwining' g := (boundedPolarization_translate (Multiplicative.toAdd g) n m).symm

private def singletonSection (p : ℕ) :
    (primalAction K (blockLength p 1 + 1)).IntertwiningMap
      (SymmetricPowerBlockSplitting.tensorAction (primalAction K (p + 1)) 1) where
  toLinearMap := (PiTensorProduct.subsingletonEquiv (R := K)
    (s := fun _ : Fin 1 => Primal K (p + 1)) 0).symm.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      PiTensorProduct.subsingletonEquiv_symm_apply', tensorAction_tprod]
    rfl

section Characteristic

variable {p : ℕ} [Fact p.Prime] [CharP K p]

private theorem step_choose (n : ℕ) :
    ((p + blockLength p n).choose p : K) = (n + 1 : ℕ) := by
  have h := ElmerKadrResidueCriterion.choose_low_digits (K := K) (p := p)
    1 n 0 0 (Fact.out : p.Prime).pos
  simpa only [blockLength_eq, Nat.mul_one, Nat.add_zero, Nat.choose_zero_right,
    Nat.cast_one, one_mul, Nat.choose_one_right, Nat.add_comm 1 n] using h

/-- The ordered tensor block map is denominator-free. Its multiplication
scalar is k! in characteristic p, for every positive k, including k >= p. -/
theorem exists_block_polarization (k : ℕ) :
    1 ≤ k → ∃ δ : (primalAction K (blockLength p k + 1)).IntertwiningMap
        (SymmetricPowerBlockSplitting.tensorAction (primalAction K (p + 1)) k),
      (blockMultiplicationIntertwiner p k).comp δ =
        (k.factorial : K) • .id (primalAction K (blockLength p k + 1)) := by
  induction k with
  | zero => intro hk; omega
  | succ n ih =>
    intro hk
    by_cases hn : n = 0
    · subst n
      refine ⟨singletonSection p, ?_⟩
      apply Representation.IntertwiningMap.ext
      apply (Polynomial.degreeLT.basis K (blockLength p 1 + 1)).ext
      intro j
      change blockMultiplication p 1
          ((PiTensorProduct.subsingletonEquiv (R := K)
            (s := fun _ : Fin 1 => Primal K (p + 1)) 0).symm
              (Polynomial.degreeLT.basis K (p + 1) j)) = _
      rw [PiTensorProduct.subsingletonEquiv_symm_apply', blockMultiplication_basis]
      have hj : blockDegree p 1 (fun _ => j) = j := by
        apply Fin.ext
        simp [blockDegree]
      simp only [hj, Representation.IntertwiningMap.toLinearMap_apply,
        Nat.zero_add, Nat.factorial_one, Nat.cast_one, one_smul,
        Representation.IntertwiningMap.id_apply]
    · obtain ⟨δ, hδ⟩ := ih (by omega)
      let B := boundedPolarizationIntertwiner (K := K) p (blockLength p n)
      let δ' := (consIntertwiner (primalAction K (p + 1)) n).comp
        ((δ.lTensor (primalAction K (p + 1))).comp B)
      refine ⟨δ', ?_⟩
      have hmaps : (TensorProduct.map
          (LinearMap.id : Module.End K (Primal K (p + 1)))
          (blockMultiplication (K := K) p n)).comp
          (TensorProduct.map LinearMap.id δ.toLinearMap) =
            (n.factorial : K) • LinearMap.id := by
        apply TensorProduct.ext'
        intro a y
        have hy := congrArg (fun q => q y) hδ
        change blockMultiplication p n (δ y) = (n.factorial : K) • y at hy
        change a ⊗ₜ[K] blockMultiplication p n (δ y) = (n.factorial : K) • (a ⊗ₜ[K] y)
        rw [hy, TensorProduct.tmul_smul]
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      change blockMultiplication p (n + 1)
          (consTensor n (TensorProduct.map LinearMap.id δ.toLinearMap (B x))) =
        ((n + 1).factorial : K) • x
      change ((blockMultiplication p (n + 1)).comp (consTensor n))
          (TensorProduct.map LinearMap.id δ.toLinearMap (B x)) = _
      rw [multiplication_cons]
      change multiplication p (blockLength p n)
        (((TensorProduct.map LinearMap.id (blockMultiplication p n)).comp
          (TensorProduct.map LinearMap.id δ.toLinearMap)) (B x)) = _
      rw [hmaps]
      simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul]
      have hB := LinearMap.congr_fun
        (multiplication_boundedPolarization (R := K) p (blockLength p n)) x
      change multiplication p (blockLength p n) (B x) =
        ((p + blockLength p n).choose p : K) • x at hB
      rw [hB, step_choose, smul_smul, Nat.factorial_succ, Nat.cast_mul]
      congr 1
      ring

def polynomialInclusion (k : ℕ) :
    (dualAction K (blockLength p k + 1)).IntertwiningMap
      (action (dualAction K (p + 1)) k) :=
  coefficientInclusion (primalAction K (p + 1)) (primalAction K (blockLength p k + 1))
    k (Polynomial.degreeLT.basis K (p + 1)) (blockMultiplicationIntertwiner p k)

/-- Actual equivariant retraction in the polynomial coordinates, with no
finite-field or group-cardinality assumption. -/
theorem exists_polynomial_retraction (k : ℕ) (hk : 1 ≤ k) (hkp : k < p) :
    ∃ r : (action (dualAction K (p + 1)) k).IntertwiningMap
        (dualAction K (blockLength p k + 1)),
      r.comp (polynomialInclusion (K := K) (p := p) k) =
        .id (dualAction K (blockLength p k + 1)) := by
  have hfac : (k.factorial : K) ≠ 0 := isUnit_iff_ne_zero.mp
    ((IsUnit.natCast_factorial_iff_of_charP (A := K) p).mpr hkp)
  obtain ⟨δ, hδ⟩ := exists_block_polarization (K := K) (p := p) k hk
  let s := (k.factorial : K)⁻¹ • δ
  have hs : (blockMultiplicationIntertwiner p k).comp s =
      .id (primalAction K (blockLength p k + 1)) := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun q => q x) hδ
    change blockMultiplication p k (δ x) = (k.factorial : K) • x at hx
    change blockMultiplication p k ((k.factorial : K)⁻¹ • δ x) = x
    rw [map_smul, hx, smul_smul, inv_mul_cancel₀ hfac, one_smul]
  exact exists_coefficient_retraction (primalAction K (p + 1))
    (primalAction K (blockLength p k + 1)) k (Polynomial.degreeLT.basis K (p + 1))
    (blockMultiplicationIntertwiner p k) s hs (blockMultiplication_permutation p k) hfac

end Characteristic

section CoefficientSums

variable {A : Type uW} [AddCommGroup A] [Module K A]

/-- All ordered k-tuples are retained, including their multiplicities. -/
def coefficientSum (p k : ℕ) (x : Fin (p + 1) → A) (i : ℕ) :
    SymmetricPower K (Fin k) A :=
  ∑ t : Fin k → Fin (p + 1), if (∑ j, (t j).val) = i then
    SymmetricPower.tprod K (fun j => x (t j)) else 0

/-- The paper's optional sign changes each generator by an invertible scalar. -/
def signedCoefficientSum (p k : ℕ) (x : Fin (p + 1) → A) (i : ℕ) :
    SymmetricPower K (Fin k) A := (-1 : K) ^ i • coefficientSum p k x i

end CoefficientSums

section OriginalAction

variable {p : ℕ} [Fact p.Prime] [CharP K p]
variable {E : Type uE} [AddCommGroup E] [Nontrivial E]
variable {W : Type uW} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Actual splitting of the author's coefficient-sum copy, for every 1 <= k < p.
W is the original faithful two-dimensional elementary abelian action. Both
symmetric powers are the genuine additive-congruence quotients. The basis,
additive embedding and all maps are conclusions, never model premises. -/
theorem coefficient_sum_is_actual_summand
    (hE : ∀ e : E, p • e = 0) (hdim : finrank K W = 2)
    (ρ : Representation K (Multiplicative E) W) (hρ : Function.Injective ρ)
    (k : ℕ) (hk : 1 ≤ k) (hkp : k < p) :
    ∃ (b : Basis (Fin 2) K W) (α : E →+ K), Function.Injective α ∧
      ∃ (h0 : ∀ e : E, ρ (Multiplicative.ofAdd e) (b 0) = b 0)
        (h1 : ∀ e : E, ρ (Multiplicative.ofAdd e) (b 1) = α e • b 0 + b 1)
        (ι : (action ρ (p * k)).dual.IntertwiningMap (action (action ρ p).dual k))
        (r : (action (action ρ p).dual k).IntertwiningMap (action ρ (p * k)).dual),
        Function.Injective ι ∧ r.comp ι = .id (action ρ (p * k)).dual ∧
        (∀ j : Fin (p * k + 1),
          ι ((-1 : K) ^ j.val • (contragredientEquiv ρ b α h0 h1 (p * k)).symm
            (dualBasis K (p * k + 1) j)) =
          signedCoefficientSum p k
            (fun t => (contragredientEquiv ρ b α h0 h1 p).symm (dualBasis K (p + 1) t)) j.val) ∧
        LinearMap.range ι.toLinearMap = Submodule.span K (Set.range
          (fun j : Fin (p * k + 1) => signedCoefficientSum p k
            (fun t => (contragredientEquiv ρ b α h0 h1 p).symm
              (dualBasis K (p + 1) t)) j.val)) := by
  classical
  rw [← blockLength_eq p k]
  obtain ⟨b, α, hα, h0, h1⟩ :=
    TwoDimensionalUnipotentNormalForm.exists_faithful_unipotent_basis hE hdim ρ hρ
  let eA := contragredientEquiv ρ b α h0 h1 p
  let eU := contragredientEquiv ρ b α h0 h1 (blockLength p k)
  let eS := symmetricActionEquiv k eA
  let iP := restrictIntertwiner α.toMultiplicative
    (polynomialInclusion (K := K) (p := p) k)
  obtain ⟨rK, hri⟩ := exists_polynomial_retraction (K := K) (p := p) k hk hkp
  let rP := restrictIntertwiner α.toMultiplicative rK
  let ι := eS.symm.toIntertwiningMap.comp (iP.comp eU.toIntertwiningMap)
  let r := eU.symm.toIntertwiningMap.comp (rP.comp eS.toIntertwiningMap)
  have hleft (x) : r (ι x) = x := by
    change eU.symm (rP (eS (eS.symm (iP (eU x))))) = x
    rw [eS.apply_symm_apply]
    have hx := congrArg (fun q => q (eU x)) hri
    change rP (iP (eU x)) = eU x at hx
    rw [hx, eU.symm_apply_apply]
  have hsplit : r.comp ι = .id (action ρ (blockLength p k)).dual := by
    apply Representation.IntertwiningMap.ext
    exact LinearMap.ext hleft
  have hpoly (j : Fin (blockLength p k + 1)) :
      iP (dualBasis K (blockLength p k + 1) j) =
        coefficientSum p k (dualBasis K (p + 1)) j.val := by
    change coefficientInclusion (primalAction K (p + 1))
      (primalAction K (blockLength p k + 1)) k
      (Polynomial.degreeLT.basis K (p + 1))
      (blockMultiplicationIntertwiner p k) (dualBasis K (blockLength p k + 1) j) = _
    have h := coefficientInclusion_basis (primalAction K (p + 1))
      (primalAction K (blockLength p k + 1)) k
      (Polynomial.degreeLT.basis K (p + 1))
      (Polynomial.degreeLT.basis K (blockLength p k + 1))
      (blockMultiplicationIntertwiner p k) (blockDegree p k)
      (blockMultiplication_basis p k) j
    simpa only [iP, polynomialInclusion, restrictIntertwiner, coefficientSum,
      dualBasis, Fin.ext_iff, blockDegree, Basis.coe_dualBasis,
      Representation.IntertwiningMap.coe_toLinearMap] using h
  have hunsigned (j : Fin (blockLength p k + 1)) :
      ι (eU.symm (dualBasis K (blockLength p k + 1) j)) =
        coefficientSum p k (fun t => eA.symm (dualBasis K (p + 1) t)) j.val := by
    change eS.symm (iP (eU (eU.symm (dualBasis K (blockLength p k + 1) j)))) = _
    rw [eU.apply_symm_apply, hpoly]
    change symmetricMap k eA.symm.toLinearMap
      (coefficientSum p k (dualBasis K (p + 1)) j.val) = _
    simp only [coefficientSum, map_sum]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> simp only [symmetricMap_tprod, map_zero,
      Representation.IntertwiningMap.coe_toLinearMap,
      Representation.Equiv.coe_toIntertwiningMap]
  have hsigned (j : Fin (blockLength p k + 1)) :
      ι ((-1 : K) ^ j.val • eU.symm (dualBasis K (blockLength p k + 1) j)) =
        signedCoefficientSum p k (fun t => eA.symm (dualBasis K (p + 1) t)) j.val := by
    rw [map_smul, hunsigned]
    rfl
  refine ⟨b, α, hα, h0, h1, ι, r, Function.LeftInverse.injective hleft,
    hsplit, hsigned, ?_⟩
  let c := ((dualBasis K (blockLength p k + 1)).map eU.symm.toLinearEquiv).unitsSMul
    (fun j => (-1 : Kˣ) ^ j.val)
  have hc (j : Fin (blockLength p k + 1)) :
      ι (c j) = signedCoefficientSum p k
        (fun t => eA.symm (dualBasis K (p + 1) t)) j.val := by
    simpa only [c, Basis.unitsSMul_apply, Basis.map_apply, Units.smul_def,
      Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
      Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.coe_toIntertwiningMap]
      using hsigned j
  calc
    LinearMap.range ι.toLinearMap =
        Submodule.map ι.toLinearMap (Submodule.span K (Set.range c)) := by
      rw [c.span_eq, Submodule.map_top]
    _ = Submodule.span K (Set.range (fun j : Fin (blockLength p k + 1) =>
        signedCoefficientSum p k (fun t => eA.symm (dualBasis K (p + 1) t)) j.val)) := by
      rw [Submodule.map_span, ← Set.range_comp']
      apply congrArg (Submodule.span K)
      apply congrArg Set.range
      funext j
      exact hc j

end OriginalAction

end D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrSymmetricPowerSplitting
