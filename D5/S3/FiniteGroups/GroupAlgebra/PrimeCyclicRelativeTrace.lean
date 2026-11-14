/-
SOURCE ONLY: this file has not been elaborated or kernel checked.
Intended path: D5/S3/FiniteGroups/GroupAlgebra/PrimeCyclicRelativeTrace.lean.
The first import is the pending public ElmerKadrTensorCounterexample source,
head 6cbd3539694ccfe551315617e259e0213d7222bf, frozen source SHA256
 a9450ce20a3b226cc832301e664dde3dee29d21f50a0dc0408c4d92aea0211ca.

Source conventions: Elmer--Kadr, DOI 10.1007/s13366-026-00855-9,
Section 2.2 and Lemma 2.1. Primal, DualPower, both actions, and
RelativeFactors below are the ORIGINAL public definitions at that import.
The remainder and trace/retract arguments generalize the private proofs in
that frozen source; they are repeated here because private declarations
cannot be imported. This is preparation for the same corrected criterion,
not a proof of that criterion or a claim of mathematical novelty.
-/

import D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.TypeTags.Finite

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

theorem primeSubgroup_injective :
    Function.Injective (primeSubgroup (K := K) (p := p)) := by
  intro c d h
  exact (ZMod.castHom_injective K) h

theorem primeSubgroup_card_zero :
    (Fintype.card (Multiplicative (ZMod p)) : K) = 0 := by
  rw [Fintype.card_multiplicative, ZMod.card]
  exact CharP.cast_eq_zero K p

theorem primeCast_pow (a : ZMod p) :
    primeCast (K := K) a ^ p = primeCast a := by
  simpa only [map_pow] using
    congrArg (primeCast (K := K) (p := p)) (ZMod.pow_card a)

-- In particular this includes exponent zero: the sum is p = 0 in K.
theorem primeField_power_sum_lt (n : ℕ) (hn : n < p - 1) :
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

theorem primeField_power_sum_top :
    (∑ a : ZMod p, primeCast (K := K) a ^ (p - 1)) = -1 := by
  simpa only [map_sum, map_pow, map_neg, map_one] using
    congrArg (primeCast (K := K) (p := p)) (primeField_top_power_sum (p := p))

/-- The polynomial identity supplying the norm witness, including p = 2. -/
theorem primeField_translate_sum :
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

theorem primeField_taylor_sum :
    (∑ a : ZMod p, Polynomial.taylor (primeCast (K := K) a)
      (-((X : K[X]) ^ (p - 1)))) = 1 := by
  simpa only [map_neg, Polynomial.taylor_X_pow, Finset.sum_neg_distrib] using
    (primeField_translate_sum (K := K) (p := p))

end PrimeField

section Remainder

variable {K : Type uK} [Field K]

/-- Multiplication followed by monic remainder on the ORIGINAL degreeLT space. -/
def remainderMul {m : ℕ} (q : K[X]) (hq : q.Monic)
    (hd : q.degree = m) (b : K[X]) : Module.End K (Primal K m) where
  toFun f := ⟨(b * (f : K[X])) %ₘ q, Polynomial.mem_degreeLT.mpr
    (hd ▸ Polynomial.degree_modByMonic_lt _ hq)⟩
  map_add' f g := by
    apply Subtype.ext
    simp only [Submodule.coe_add, mul_add, Polynomial.add_modByMonic]
  map_smul' c f := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply, mul_smul_comm,
      Polynomial.smul_modByMonic]

/-- Translation commutes with remainder when the monic modulus is fixed. -/
theorem taylor_modByMonic (q : K[X]) (hq : q.Monic) (a : K)
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
theorem remainderMul_conjugate {m : ℕ} (q : K[X]) (hq : q.Monic)
    (hd : q.degree = m) (b : K[X]) (a : K)
    (ha : Polynomial.taylor a q = q) (f : Primal K m) :
    ((primalAction K m (Multiplicative.ofAdd a))
      (remainderMul q hq hd b
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

theorem invariantModulus_monic (r : ℕ) :
    (invariantModulus (K := K) (p := p) r).Monic := by
  apply Polynomial.Monic.pow
  apply Polynomial.monic_X_pow_sub
  simp only [Polynomial.degree_X]
  exact_mod_cast (Fact.out : p.Prime).one_lt

theorem invariantModulus_degree (r : ℕ) :
    (invariantModulus (K := K) (p := p) r).degree = p * r := by
  have hb : ((X : K[X]) ^ p - X).degree = p := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt]
    · exact Polynomial.degree_X_pow p
    · simp only [Polynomial.degree_X, Polynomial.degree_X_pow]
      exact_mod_cast (Fact.out : p.Prime).one_lt
  simp [invariantModulus, Polynomial.degree_pow, hb, nsmul_eq_mul, mul_comm]

theorem invariantModulus_translate (r : ℕ) (a : K) (ha : a ^ p = a) :
    Polynomial.taylor a (invariantModulus (K := K) (p := p) r) =
      invariantModulus r := by
  have hb : Polynomial.taylor a ((X : K[X]) ^ p - X) = X ^ p - X := by
    rw [map_sub, Polynomial.taylor_X_pow, Polynomial.taylor_X,
      add_pow_char _ _ p, ← Polynomial.C_pow, ha]
    ring
  simpa only [invariantModulus, Polynomial.taylor_pow, hb]

theorem invariantModulus_prime_translate (r : ℕ) (a : ZMod p) :
    Polynomial.taylor (primeCast (K := K) a) (invariantModulus (p := p) r) =
      invariantModulus r :=
  invariantModulus_translate r _ (primeCast_pow a)

/-- t_r(f) = (-X^(p-1) f) mod Q_r on the actual primal module. -/
def primalNormWitness (r : ℕ) : Module.End K (Primal K (p * r)) :=
  remainderMul (invariantModulus r) (invariantModulus_monic r)
    (invariantModulus_degree r) (-X ^ (p - 1))

theorem primalNormWitness_apply (r : ℕ) (f : Primal K (p * r)) :
    (primalNormWitness (p := p) r f : K[X]) =
      (-X ^ (p - 1) * (f : K[X])) %ₘ invariantModulus r := rfl

theorem primalNormWitness_conjugate (r : ℕ) (c : Multiplicative (ZMod p))
    (f : Primal K (p * r)) :
    ((primalAction K (p * r) (primeSubgroup c))
      (primalNormWitness r (primalAction K (p * r) (primeSubgroup c⁻¹) f)) : K[X]) =
      (Polynomial.taylor (primeCast (Multiplicative.toAdd c)) (-X ^ (p - 1)) *
        (f : K[X])) %ₘ invariantModulus r := by
  simpa only [primeSubgroup, primalNormWitness, toAdd_inv, map_neg] using
    (remainderMul_conjugate (invariantModulus (K := K) (p := p) r)
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
          (f : K[X])) %ₘ invariantModulus r) =
      ((∑ c : Multiplicative (ZMod p),
        Polynomial.taylor (primeCast (Multiplicative.toAdd c)) (-X ^ (p - 1)) *
          (f : K[X])) %ₘ invariantModulus r) := by
        exact (map_sum (Polynomial.modByMonicHom (invariantModulus r)) _ _).symm
    _ = (f : K[X]) %ₘ invariantModulus r := by rw [← sum_mul, hs, one_mul]
    _ = (f : K[X]) := (Polynomial.modByMonic_eq_self_iff
      (invariantModulus_monic r)).mpr
        (invariantModulus_degree (K := K) (p := p) r ▸
          Polynomial.mem_degreeLT.mp f.property)

/-- The zero truncation really is the zero module. -/
theorem primal_zero (f : Primal K 0) : f = 0 := by
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  change (f : K[X]).coeff n = 0
  exact (Polynomial.degree_lt_iff_coeff_zero (f : K[X]) 0).mp
    (Polynomial.mem_degreeLT.mp f.property) n (Nat.zero_le n)

/-- r = 0 really gives modulus 1, not an excluded degenerate case. -/
theorem invariantModulus_zero :
    invariantModulus (K := K) (p := p) 0 = 1 := pow_zero _

theorem primalNormWitness_zero :
    primalNormWitness (K := K) (p := p) 0 = 0 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  simp [primalNormWitness, remainderMul, invariantModulus]

end PrimeNorm

section InverseReindexing

variable {K : Type uK} [Field K]
  {G : Type uG} [Group G] {C : Type uC} [Group C] [Fintype C]
  {V : Type uV} [AddCommGroup V] [Module K V]

/-- The inverse indexing is a genuine finite-group permutation. -/
theorem inverse_conjugation_sum (ι : C →* G) (ρ : Representation K G V)
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
    (inverse_conjugation_sum primeSubgroup (primalAction K (p * r))
      (primalNormWitness r)).trans (primal_norm r)
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
  exact (inverse_conjugation_sum primeSubgroup (dualAction K (p * r))
    (dualNormWitness r)).symm.trans hdInv

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

section OriginalRelativeTrace

variable {K : Type uK} [Field K]
  {G : Type uG} [Group G] {C : Type uC} [Group C] [Fintype C]
  {V : Type uV} [AddCommGroup V] [Module K V]
  {X : Type uX} [AddCommGroup X] [Module K X]
  {M : Type uM} [AddCommGroup M] [Module K M]

-- The following two arguments reproduce the frozen private RelativeTrace
-- mathematics. No dimension, basis, projectivity or trace is required on X/M.
theorem trace_conjugate (ρ : Representation K G V)
    (t : Module.End K V) (g : G) :
    LinearMap.trace K V ((ρ g).comp (t.comp (ρ g⁻¹))) =
      LinearMap.trace K V t := by
  change LinearMap.trace K V (ρ g * (t * ρ g⁻¹)) = _
  rw [LinearMap.trace_mul_cycle']
  rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

/-- Only V is traced; X and M are arbitrary modules in independent universes. -/
theorem trace_tensor_factorization
    (ι : C →* G) (ρ : Representation K G V)
    (σ : Representation K G X) (τ : Representation K G M)
    (t : Module.End K M)
    (ht : (∑ c : C, (τ (ι c)).comp (t.comp (τ (ι c⁻¹)))) = LinearMap.id)
    (hcard : (Fintype.card C : K) = 0)
    (f : ρ.IntertwiningMap (σ.tprod τ))
    (g : (σ.tprod τ).IntertwiningMap ρ) :
    LinearMap.trace K V (g.toLinearMap.comp f.toLinearMap) = 0 := by
  classical
  let T : Module.End K (X ⊗[K] M) := TensorProduct.map LinearMap.id t
  have hT : (∑ c : C,
      ((σ.tprod τ) (ι c)).comp (T.comp ((σ.tprod τ) (ι c⁻¹)))) =
        LinearMap.id := by
    apply TensorProduct.ext'
    intro x m
    simp only [LinearMap.sum_apply, LinearMap.comp_apply,
      Representation.tprod_apply, TensorProduct.map_tmul, T, LinearMap.id_apply]
    have hc (c : C) : σ (ι c) (σ (ι c⁻¹) x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel,
        map_one, map_one, Module.End.one_apply]
    simp_rw [hc]
    rw [← TensorProduct.tmul_sum]
    congr 1
    simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
      using LinearMap.congr_fun ht m
  have he : g.toLinearMap.comp f.toLinearMap =
      ∑ c : C, (ρ (ι c)).comp
        ((g.toLinearMap.comp (T.comp f.toLinearMap)).comp (ρ (ι c⁻¹))) := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sum_apply, LinearMap.comp_apply,
      Representation.IntertwiningMap.toLinearMap_apply]
    have hv := congrArg g (LinearMap.congr_fun hT (f v))
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply,
      map_sum] at hv
    simpa only [LinearMap.sum_apply, LinearMap.comp_apply,
      ← f.isIntertwining, g.isIntertwining] using hv.symm
  rw [he, map_sum]
  simp only [map_inv, trace_conjugate, sum_const, card_univ, nsmul_eq_mul,
    hcard, zero_mul]

variable {U : Type uK} [AddCommGroup U] [Module K U]

/-- The ORIGINAL retract-based RelativeFactors, with all P/X quantifiers kept.
No finiteness hypothesis on P, X or M and no trace on those factors occurs.
LinearMap.trace is defined for arbitrary U; in particular this gives the usual
trace statement for every finite-dimensional target U. -/
theorem trace_original_relative_factor
    (ι : C →* G) (τ : Representation K G M) (t : Module.End K M)
    (ht : (∑ c : C, (τ (ι c)).comp (t.comp (τ (ι c⁻¹)))) = LinearMap.id)
    (hcard : (Fintype.card C : K) = 0)
    (ρ : Representation K G U) (h : ρ.IntertwiningMap ρ)
    (hh : RelativeFactors τ h) :
    LinearMap.trace K U h.toLinearMap = 0 := by
  obtain ⟨P, ⟨X, i, r, hri⟩, a, b, hab⟩ := hh
  have hz := trace_tensor_factorization ι ρ X.ρ τ t ht hcard (i.comp a) (b.comp r)
  have he : (b.comp r).toLinearMap.comp (i.comp a).toLinearMap = h.toLinearMap := by
    apply LinearMap.ext
    intro v
    change b (r (i (a v))) = h v
    have hs := congrArg (fun q : P.ρ.IntertwiningMap P.ρ => q (a v)) hri
    change r (i (a v)) = a v at hs
    rw [hs]
    exact congrArg (fun q : ρ.IntertwiningMap ρ => q v) hab
  rwa [he] at hz

end OriginalRelativeTrace

section ActualRelativeModule

variable {K : Type uK} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
  {U : Type uK} [AddCommGroup U] [Module K U]

/-- Every original-relative-factor endomorphism has zero ordinary target trace,
for the explicit M_(p,s) with its actual translation-contragredient action. -/
theorem trace_relativeFactors (s : ℕ)
    (ρ : Representation K (Multiplicative K) U) (h : ρ.IntertwiningMap ρ)
    (hh : RelativeFactors (relativeAction (K := K) (p := p) s) h) :
    LinearMap.trace K U h.toLinearMap = 0 :=
  trace_original_relative_factor primeSubgroup (relativeAction s)
    (relativeNormWitness s) (relative_norm s) primeSubgroup_card_zero ρ h hh

end ActualRelativeModule

end D5.S3.FiniteGroups.GroupAlgebra.PrimeCyclicRelativeTrace
