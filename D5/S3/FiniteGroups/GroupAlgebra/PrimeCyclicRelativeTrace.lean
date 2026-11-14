/- GID: D5/S3/FiniteGroups/GroupAlgebra/PrimeCyclicRelativeTrace
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/PrimeCyclicRelativeTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.FieldTheory.Finite.Basic, mathlib/module/Mathlib.Algebra.Polynomial.RingDivision]
   utility: none
   digest: Prime cyclic conjugation norms on polynomial translation modules and relative-factor traces. -/

import D5.S3.FiniteGroups.GroupAlgebra.BoundedTensorPolarization
import D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# Prime cyclic norms for the original relative polynomial module

For every prime p and field of characteristic p, monic remainder modulo
`(X^p-X)^r` supplies an explicit conjugation-norm witness on the original
polynomial module of dimension p*r. Transpose and direct sum give the witness
on the original contragredient relative module with arbitrary summand count.
The norm statements include p = 2, r = 0 and the empty direct sum.

Only the target is traced in the relative-factor argument: the existential
modules X and P in the original `RelativeFactors` have no finiteness restriction.
The remainder and retract arguments extend the corresponding proofs in
`ElmerKadrTensorCounterexample`, using its public modules and actions unchanged.
Source: Elmer--Kadr, DOI 10.1007/s13366-026-00855-9, Section 2.2 and Lemma 2.1.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.PrimeCyclicRelativeTrace

open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
open scoped TensorProduct DirectSum
open Finset Polynomial

universe uK uG uC uV uX uM

section PrimeField

variable {K : Type uK} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

/-- The prime-field embedding, with no finiteness assumption on K. -/
abbrev primeCast : ZMod p →+* K := ZMod.castHom (dvd_refl p) K

/-- The actual order-p additive subgroup of the translation group. -/
def primeSubgroup : Multiplicative (ZMod p) →* Multiplicative K where
  toFun c := Multiplicative.ofAdd (primeCast (Multiplicative.toAdd c))
  map_one' := by simp
  map_mul' c d := by simp

private theorem primeSubgroup_card_zero :
    (Fintype.card (Multiplicative (ZMod p)) : K) = 0 := by
  rw [Fintype.card_multiplicative, ZMod.card]
  exact CharP.cast_eq_zero K p

private theorem primeCast_pow (a : ZMod p) :
    primeCast (K := K) a ^ p = primeCast a := by
  simpa only [map_pow] using
    congrArg (primeCast (K := K) (p := p)) (ZMod.pow_card a)

-- In particular this includes exponent zero: the sum is p = 0 in K.
private theorem primeField_power_sum_lt (n : ℕ) (hn : n < p - 1) :
    (∑ a : ZMod p, primeCast (K := K) a ^ n) = 0 := by
  have h : (∑ a : ZMod p, a ^ n) = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (ZMod p) n
      (by simpa only [ZMod.card] using hn)
  simpa only [map_sum, map_pow, map_zero] using
    congrArg (primeCast (K := K) (p := p)) h

private theorem primeField_top_power_sum :
    (∑ a : ZMod p, a ^ (p - 1)) = -1 := by
  classical
  have hn : p - 1 ≠ 0 := by
    have := (Fact.out : p.Prime).two_le
    omega
  let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x => x, Units.val_injective⟩
  have hφ : univ.map φ = univ \ {(0 : ZMod p)} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and,
      mem_sdiff, mem_singleton, φ] using! isUnit_iff_ne_zero
  calc
    (∑ a : ZMod p, a ^ (p - 1)) =
        ∑ a ∈ univ \ {(0 : ZMod p)}, a ^ (p - 1) := by
      rw [← sum_sdiff ({0} : Finset (ZMod p)).subset_univ, sum_singleton,
        zero_pow hn, add_zero]
    _ = ∑ a : (ZMod p)ˣ, (a ^ (p - 1) : ZMod p) := by
      simp [φ, ← hφ, univ.sum_map φ]
    _ = -1 := by
      rw [FiniteField.sum_pow_units (ZMod p) (p - 1), ZMod.card,
        if_pos (dvd_refl (p - 1))]

private theorem primeField_power_sum_top :
    (∑ a : ZMod p, primeCast (K := K) a ^ (p - 1)) = -1 := by
  simpa only [map_sum, map_pow, map_neg, map_one] using
    congrArg (primeCast (K := K) (p := p)) (primeField_top_power_sum (p := p))

/-- The polynomial identity supplying the norm witness, including p = 2. -/
private theorem primeField_translate_sum :
    -(∑ a : ZMod p, ((X : K[X]) + C (primeCast a)) ^ (p - 1)) = 1 := by
  classical
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_neg, ← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_X_add_C_pow]
  rw [← Finset.sum_mul]
  by_cases hk : k = 0
  · subst k
    rw [Nat.sub_zero, primeField_power_sum_top]
    simp
  · rw [Polynomial.coeff_one, if_neg hk]
    by_cases hkp : k ≤ p - 1
    · have hn : p - 1 - k < p - 1 := by omega
      rw [primeField_power_sum_lt (p - 1 - k) hn, zero_mul, neg_zero]
    · rw [Nat.choose_eq_zero_of_lt (by omega : p - 1 < k),
        Nat.cast_zero, mul_zero, neg_zero]

private theorem primeField_taylor_sum :
    (∑ a : ZMod p, Polynomial.taylor (primeCast (K := K) a)
      (-((X : K[X]) ^ (p - 1)))) = 1 := by
  simpa only [map_neg, Polynomial.taylor_X_pow, Finset.sum_neg_distrib] using
    (primeField_translate_sum (K := K) (p := p))

end PrimeField

section Remainder

variable {K : Type uK} [Field K]

/-- Translation commutes with remainder when the monic modulus is fixed. -/
private theorem taylor_modByMonic (q : K[X]) (hq : q.Monic) (a : K)
    (ha : Polynomial.taylor a q = q) (f : K[X]) :
    Polynomial.taylor a (f %ₘ q) = Polynomial.taylor a f %ₘ q := by
  have hdvd : q ∣ Polynomial.taylor a (f %ₘ q) - Polynomial.taylor a f := by
    have h := map_dvd (Polynomial.taylorAlgHom a) (Polynomial.dvd_modByMonic_sub f q)
    change Polynomial.taylor a q ∣ Polynomial.taylor a (f %ₘ q - f) at h
    simpa only [map_sub, ha] using h
  calc
    Polynomial.taylor a (f %ₘ q) = (Polynomial.taylor a (f %ₘ q)) %ₘ q := by
      symm
      apply (Polynomial.modByMonic_eq_self_iff hq).mpr
      simpa only [Polynomial.degree_taylor] using Polynomial.degree_modByMonic_lt f hq
    _ = _ := Polynomial.modByMonic_eq_of_dvd_sub hq hdvd

/-- Actual conjugation of the remainder operator by polynomial translation. -/
private theorem remainderMul_conjugate {m : ℕ} (q : K[X]) (hq : q.Monic)
    (hd : q.degree = m) (b : K[X]) (a : K)
    (ha : Polynomial.taylor a q = q) (f : Primal K m) :
    ((primalAction K m (Multiplicative.ofAdd a))
      (ElmerKadrTensorCounterexample.remainderMul q hq hd b
        (primalAction K m (Multiplicative.ofAdd (-a)) f)) : K[X]) =
      (Polynomial.taylor a b * (f : K[X])) %ₘ q := by
  change Polynomial.taylor a
    ((b * Polynomial.taylor (-a) (f : K[X])) %ₘ q) = _
  rw [taylor_modByMonic q hq a ha, Polynomial.taylor_mul,
    Polynomial.taylor_taylor, add_neg_cancel, Polynomial.taylor_zero]

end Remainder

section PrimeNorm

variable {K : Type uK} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

/-- Q_r = (X^p - X)^r; no positivity assumption on r. -/
def invariantModulus (r : ℕ) : K[X] := (X ^ p - X) ^ r

private theorem invariantModulus_monic (r : ℕ) :
    (invariantModulus (K := K) (p := p) r).Monic := by
  apply Polynomial.Monic.pow
  apply Polynomial.monic_X_pow_sub
  simp only [Polynomial.degree_X]
  exact_mod_cast (Fact.out : p.Prime).one_lt

private theorem invariantModulus_degree (r : ℕ) :
    (invariantModulus (K := K) (p := p) r).degree = ((p * r : ℕ) : WithBot ℕ) := by
  have hb : ((X : K[X]) ^ p - X).degree = (p : WithBot ℕ) := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt]
    · exact Polynomial.degree_X_pow p
    · simp only [Polynomial.degree_X, Polynomial.degree_X_pow]
      exact_mod_cast (Fact.out : p.Prime).one_lt
  simp [invariantModulus, Polynomial.degree_pow, hb, nsmul_eq_mul, mul_comm]

private theorem invariantModulus_translate (r : ℕ) (a : K) (ha : a ^ p = a) :
    Polynomial.taylor a (invariantModulus (K := K) (p := p) r) =
      invariantModulus (p := p) r := by
  have hb : Polynomial.taylor a ((X : K[X]) ^ p - X) = X ^ p - X := by
    rw [map_sub, Polynomial.taylor_X_pow, Polynomial.taylor_X,
      add_pow_char _ _ p, ← Polynomial.C_pow, ha]
    ring
  simpa only [invariantModulus, Polynomial.taylor_pow, hb]

private theorem invariantModulus_prime_translate (r : ℕ) (a : ZMod p) :
    Polynomial.taylor (primeCast (K := K) a) (invariantModulus (p := p) r) =
      invariantModulus (p := p) r :=
  invariantModulus_translate r _ (primeCast_pow a)

/-- t_r(f) = (-X^(p-1) f) mod Q_r on the actual primal module. -/
def primalNormWitness (r : ℕ) : Module.End K (Primal K (p * r)) :=
  ElmerKadrTensorCounterexample.remainderMul (m := p * r)
    (invariantModulus (p := p) r) (invariantModulus_monic r)
    (invariantModulus_degree r) (-X ^ (p - 1))

private theorem primalNormWitness_conjugate (r : ℕ) (c : Multiplicative (ZMod p))
    (f : Primal K (p * r)) :
    ((primalAction K (p * r) (primeSubgroup c))
      (primalNormWitness r (primalAction K (p * r) (primeSubgroup c⁻¹) f)) : K[X]) =
      (Polynomial.taylor (primeCast (Multiplicative.toAdd c)) (-X ^ (p - 1)) *
        (f : K[X])) %ₘ invariantModulus (p := p) r := by
  change ((primalAction K (p * r)
    (Multiplicative.ofAdd (primeCast (Multiplicative.toAdd c))))
      (ElmerKadrTensorCounterexample.remainderMul (m := p * r) (invariantModulus (p := p) r)
        (invariantModulus_monic r) (invariantModulus_degree r) (-X ^ (p - 1))
        (primalAction K (p * r)
          (Multiplicative.ofAdd (primeCast (Multiplicative.toAdd c⁻¹))) f)) : K[X]) = _
  rw [toAdd_inv, map_neg]
  exact (remainderMul_conjugate (m := p * r)
      (invariantModulus (K := K) (p := p) r)
      (invariantModulus_monic r) (invariantModulus_degree r) (-X ^ (p - 1))
      (primeCast (Multiplicative.toAdd c))
      (invariantModulus_prime_translate r (Multiplicative.toAdd c)) f)

/-- The actual prime-subgroup conjugation norm of t_r is the identity. -/
theorem primal_norm (r : ℕ) :
    (∑ c : Multiplicative (ZMod p),
      (primalAction K (p * r) (primeSubgroup c)).comp
        ((primalNormWitness r).comp (primalAction K (p * r) (primeSubgroup c⁻¹)))) =
      LinearMap.id := by
  classical
  have hs : (∑ c : Multiplicative (ZMod p),
      Polynomial.taylor (primeCast (K := K) (Multiplicative.toAdd c))
        (-((X : K[X]) ^ (p - 1)))) = 1 := by
    calc
      _ = ∑ a : ZMod p,
          Polynomial.taylor (primeCast (K := K) a) (-((X : K[X]) ^ (p - 1))) :=
        (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).sum_comp _
      _ = 1 := primeField_taylor_sum
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply,
    Submodule.coe_sum, primalNormWitness_conjugate]
  calc
    (∑ c : Multiplicative (ZMod p),
        (Polynomial.taylor (primeCast (Multiplicative.toAdd c)) (-X ^ (p - 1)) *
          (f : K[X])) %ₘ invariantModulus (p := p) r) =
      ((∑ c : Multiplicative (ZMod p),
        Polynomial.taylor (primeCast (Multiplicative.toAdd c)) (-X ^ (p - 1)) *
          (f : K[X])) %ₘ invariantModulus (p := p) r) := by
        exact (map_sum (Polynomial.modByMonicHom (invariantModulus (p := p) r)) _ _).symm
    _ = (f : K[X]) %ₘ invariantModulus (p := p) r := by rw [← sum_mul, hs, one_mul]
    _ = (f : K[X]) := (Polynomial.modByMonic_eq_self_iff
      (invariantModulus_monic r)).mpr
        (invariantModulus_degree (K := K) (p := p) r ▸
          Polynomial.mem_degreeLT.mp f.property)

end PrimeNorm

section InverseReindexing

variable {K : Type uK} [Field K]
  {G : Type uG} [Group G] {C : Type uC} [Group C] [Fintype C]
  {V : Type uV} [AddCommGroup V] [Module K V]

/-- The inverse indexing is a genuine finite-group permutation. -/
private theorem inverse_conjugation_sum (ι : C →* G) (ρ : Representation K G V)
    (t : Module.End K V) :
    (∑ c : C, (ρ (ι c⁻¹)).comp (t.comp (ρ (ι c)))) =
      ∑ c : C, (ρ (ι c)).comp (t.comp (ρ (ι c⁻¹))) := by
  classical
  refine Fintype.sum_bijective (fun c : C => c⁻¹) inv_involutive.bijective _ _ ?_
  intro c
  rw [inv_inv]

end InverseReindexing

section DualAndDirectSum

variable {K : Type uK} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

/-- Transpose on the actual contragredient, without any coordinate equivalence. -/
def dualNormWitness (r : ℕ) : Module.End K (DualPower K (p * r)) :=
  Module.Dual.transpose (primalNormWitness r)

/-- Contragredient inversion and finite inverse reindexing are both explicit. -/
theorem dual_norm (r : ℕ) :
    (∑ c : Multiplicative (ZMod p),
      (dualAction K (p * r) (primeSubgroup c)).comp
        ((dualNormWitness r).comp (dualAction K (p * r) (primeSubgroup c⁻¹)))) =
      LinearMap.id := by
  classical
  have hpInv : (∑ c : Multiplicative (ZMod p),
      (primalAction K (p * r) (primeSubgroup c⁻¹)).comp
        ((primalNormWitness r).comp (primalAction K (p * r) (primeSubgroup c)))) =
        LinearMap.id :=
    (inverse_conjugation_sum (primeSubgroup (K := K) (p := p))
      (primalAction K (p * r))
      (primalNormWitness (p := p) r)).trans (primal_norm (p := p) r)
  have hdInv : (∑ c : Multiplicative (ZMod p),
      (dualAction K (p * r) (primeSubgroup c⁻¹)).comp
        ((dualNormWitness r).comp (dualAction K (p * r) (primeSubgroup c)))) =
        LinearMap.id := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro q
    have hq := congrArg f (LinearMap.congr_fun hpInv q)
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply,
      map_sum] at hq
    simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply,
      dualAction, Representation.dual_apply, dualNormWitness,
      Module.Dual.transpose_apply, map_inv, inv_inv] using hq
  exact (inverse_conjugation_sum (primeSubgroup (K := K) (p := p))
    (dualAction K (p * r)) (dualNormWitness (p := p) r)).symm.trans hdInv

/-- The original finite relative module, with arbitrary number of summands. -/
abbrev RelativeSpace (K : Type uK) [Field K] (p s : ℕ) :=
  ⨁ i : Fin s, DualPower K (p * (i.val + 1))

/-- The ACTUAL direct sum of the original contragredient actions. -/
def relativeAction (s : ℕ) :
    Representation K (Multiplicative K) (RelativeSpace K p s) :=
  Representation.directSum (fun i : Fin s => dualAction K (p * (i.val + 1)))

/-- An explicit endomorphism, pointwise transpose of monic remainder operators. -/
def relativeNormWitness (s : ℕ) : Module.End K (RelativeSpace K p s) :=
  DirectSum.lmap (fun i : Fin s => dualNormWitness (i.val + 1))

theorem relative_norm (s : ℕ) :
    (∑ c : Multiplicative (ZMod p),
      (relativeAction (K := K) (p := p) s (primeSubgroup c)).comp
        ((relativeNormWitness s).comp
          (relativeAction (K := K) (p := p) s (primeSubgroup c⁻¹)))) =
      LinearMap.id := by
  apply LinearMap.ext
  intro m
  apply DFinsupp.ext
  intro i
  simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply,
    relativeAction, Representation.directSum_apply, relativeNormWitness,
    DirectSum.lmap_apply, DirectSum.sum_apply]
    using LinearMap.congr_fun (dual_norm (K := K) (p := p) (i.val + 1)) (m i)

end DualAndDirectSum

section ActualRelativeModule

variable {K : Type uK} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  {U : Type uK} [AddCommGroup U] [Module K U]

/-- Every original-relative-factor endomorphism has zero ordinary target trace,
for the explicit M_(p,s) with its actual translation-contragredient action. -/
theorem trace_relativeFactors (s : ℕ)
    (ρ : Representation K (Multiplicative K) U) (h : ρ.IntertwiningMap ρ)
    (hh : RelativeFactors (relativeAction (K := K) (p := p) s) h) :
    LinearMap.trace K U h.toLinearMap = 0 :=
  ElmerKadrTensorCounterexample.trace_relative_factor (primeSubgroup (K := K) (p := p))
    (relativeAction (K := K) (p := p) s)
    (relativeNormWitness (K := K) (p := p) s) (relative_norm (p := p) s)
    (primeSubgroup_card_zero (K := K) (p := p)) ρ h hh

end ActualRelativeModule

end D5.S3.FiniteGroups.GroupAlgebra.PrimeCyclicRelativeTrace

namespace D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrPositiveCriterion

open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
open D5.S3.FiniteGroups.GroupAlgebra.PolynomialKernelPolarization
open Polynomial
open scoped TensorProduct DirectSum

universe uK uG

section ZeroAndUnits

variable {K : Type uK} [Field K] {G : Type uG} [Group G]
  {M U Z : Type uK} [AddCommGroup M] [Module K M]
  [AddCommGroup U] [Module K U] [AddCommGroup Z] [Module K Z]

/-- A literal zero representation is a retract of K tensor M by zero maps.
Thus the zero error has an explicit witness for the ORIGINAL RelativeFactors. -/
theorem relativeFactors_zero (τ : Representation K G M)
    (ρ : Representation K G U) (σ : Representation K G Z) :
    RelativeFactors τ (0 : ρ.IntertwiningMap σ) := by
  let ζ : Representation K G (Fin 0 → K) :=
    Representation.trivial K G (Fin 0 → K)
  refine ⟨Rep.of ζ, ?_, 0, 0, ?_⟩
  · refine ⟨Rep.of (Representation.trivial K G K), 0, 0, ?_⟩
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    funext j
    exact Fin.elim0 j
  · apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    rfl

end ZeroAndUnits

section PolynomialUnits

variable {K : Type uK} [Field K]

theorem primal_one_action (c : Multiplicative K) :
    primalAction K 1 c = LinearMap.id := by
  apply (Polynomial.degreeLT.basis K 1).ext
  intro i
  apply Subtype.ext
  have hi : (i : ℕ) = 0 := by have := i.is_lt; omega
  change Polynomial.taylor (Multiplicative.toAdd c)
      (Polynomial.degreeLT.basis K 1 i : K[X]) =
    (Polynomial.degreeLT.basis K 1 i : K[X])
  simp only [Polynomial.degreeLT.basis_val, hi, pow_zero,
    Polynomial.taylor_one, Polynomial.C_1]

theorem dual_one_action (c : Multiplicative K) :
    dualAction K 1 c = LinearMap.id := by
  change (primalAction K 1 c⁻¹).dualMap = LinearMap.id
  rw [primal_one_action, LinearMap.dualMap_id]

/-- V_1 is actually the tensor unit: its original translation action is trivial. -/
def dualOneEquiv :
    (dualAction K 1).Equiv (Representation.trivial K (Multiplicative K) K) :=
  Representation.Equiv.mk
    ((dualBasis K 1).equivFun.trans (LinearEquiv.funUnique (Fin 1) K K)) fun c => by
      rw [dual_one_action]
      apply LinearMap.ext
      intro v
      rfl

variable {U : Type uK} [AddCommGroup U] [Module K U]

/-- The actual left tensor-unit equivalence, including its equivariance. -/
def tensorUnitLeft (ρ : Representation K (Multiplicative K) U) :
    ((dualAction K 1).tprod ρ).Equiv ρ := by
  let e : ((dualAction K 1).tprod ρ).Equiv
      ((Representation.trivial K (Multiplicative K) K).tprod ρ) :=
    Representation.Equiv.mk
      (TensorProduct.congr (dualOneEquiv (K := K)).toLinearEquiv
        (LinearEquiv.refl K U)) fun c => by
        apply TensorProduct.ext'
        intro x y
        change dualOneEquiv (dualAction K 1 c x) ⊗ₜ[K] ρ c y =
          dualOneEquiv x ⊗ₜ[K] ρ c y
        rw [dual_one_action]
        rfl
  exact e.trans (Representation.TensorProduct.lid K ρ)

/-- The actual right tensor-unit equivalence, using the equivariant tensor flip. -/
def tensorUnitRight (ρ : Representation K (Multiplicative K) U) :
    (ρ.tprod (dualAction K 1)).Equiv ρ :=
  (Representation.TensorProduct.comm ρ (dualAction K 1)).trans (tensorUnitLeft ρ)

end PolynomialUnits

section RelativeSummand

variable {K : Type uK} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

local notation "MAction" => PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)

/-- Literal inclusion of one of the specified V_(p*(i+1)) summands of M. -/
def relativeInclusion {s : ℕ} (i : Fin s) :
    (dualAction K (p * (i.val + 1))).IntertwiningMap (MAction s) where
  toLinearMap := DirectSum.lof K (Fin s)
    (fun j : Fin s => DualPower K (p * (j.val + 1))) i
  isIntertwining' c := by
    apply LinearMap.ext
    intro v
    exact (DirectSum.lmap_lof
      (fun j : Fin s => dualAction K (p * (j.val + 1)) c) i v).symm

/-- Literal projection from the same direct sum. -/
def relativeProjection {s : ℕ} (i : Fin s) :
    (MAction s).IntertwiningMap (dualAction K (p * (i.val + 1))) where
  toLinearMap := DirectSum.component K (Fin s)
    (fun j : Fin s => DualPower K (p * (j.val + 1))) i
  isIntertwining' c := by
    apply LinearMap.ext
    intro v
    rfl

theorem relativeProjection_inclusion {s : ℕ} (i : Fin s) :
    (relativeProjection (K := K) (p := p) i).comp (relativeInclusion i) =
      .id (dualAction K (p * (i.val + 1))) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  exact DirectSum.component.lof_self (R := K) (ι := Fin s)
    (M := fun j : Fin s => DualPower K (p * (j.val + 1))) i v

/-- The actual complement is M-relative-projective: identify its dual tensor,
flip it, and tensor the literal direct-sum inclusion/projection by V_m.
The witness X is V_m; the original existential P/X quantifiers are retained. -/
theorem dualTensor_relativeProjective (s : ℕ) (i : Fin s) (m : ℕ) :
    RelativeProjective (MAction s)
      (Rep.of (((primalAction K (p * (i.val + 1))).tprod
        (primalAction K m)).dual)) := by
  let ρ := dualAction K (p * (i.val + 1))
  let τ := dualAction K m
  let : Module.Finite K (Primal K (p * (i.val + 1))) :=
    Module.Finite.of_basis (Polynomial.degreeLT.basis K (p * (i.val + 1)))
  let : Module.Projective K (Primal K (p * (i.val + 1))) :=
    Module.Projective.of_basis (Polynomial.degreeLT.basis K (p * (i.val + 1)))
  let : Module.Finite K (Primal K m) :=
    Module.Finite.of_basis (Polynomial.degreeLT.basis K m)
  let : Module.Projective K (Primal K m) :=
    Module.Projective.of_basis (Polynomial.degreeLT.basis K m)
  let e := (dualTensorEquiv (primalAction K (p * (i.val + 1)))
    (primalAction K m)).symm.trans (Representation.TensorProduct.comm ρ τ)
  let I := (relativeInclusion (K := K) (p := p) i).lTensor τ
  let R := (relativeProjection (K := K) (p := p) i).lTensor τ
  have hRI : R.comp I = .id (τ.tprod ρ) := by
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    change x ⊗ₜ[K] relativeProjection i (relativeInclusion i y) = x ⊗ₜ[K] y
    have hy := congrArg (fun k => k y)
      (relativeProjection_inclusion (K := K) (p := p) i)
    change relativeProjection i (relativeInclusion i y) = y at hy
    rw [hy]
  refine ⟨Rep.of τ, I.comp e.toIntertwiningMap, e.symm.toIntertwiningMap.comp R, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  change e.symm (R (I (e v))) = v
  have hv := congrArg (fun k => k (e v)) hRI
  change R (I (e v)) = e v at hv
  rw [hv, e.symm_apply_apply]

end RelativeSummand

end D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrPositiveCriterion
