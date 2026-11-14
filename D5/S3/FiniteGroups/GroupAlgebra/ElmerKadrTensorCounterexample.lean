/- GID: D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorCounterexample
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Basic, mathlib/module/Mathlib.RingTheory.Polynomial.DegreeLT, mathlib/module/Mathlib.LinearAlgebra.Trace]
   utility: none
   digest: Polynomial translation duals and the relative trace obstruction for the Elmer--Kadr tensor instance. -/

import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Trace
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic

/-!
The source conventions are Elmer--Kadr, DOI 10.1007/s13366-026-00855-9,
Section 2.2, Lemma 2.1 and formulas (11)--(12). Polynomial translation on
degree < m is the dehomogenized symmetric power, with z^i corresponding
to X^i Y^(m-1-i); V_m is its actual contragredient dual.

The relative trace argument uses a genuine finite subgroup action. It does
not regard a coefficient operator as primitive on arbitrary tensor factors.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample

open scoped TensorProduct
open Finset Polynomial

universe uK uG uC uV uX uM

section RelativeTrace

variable {K : Type uK} [Field K]
  {G : Type uG} [Group G] {C : Type uC} [Group C] [Fintype C]
  {V : Type uV} [AddCommGroup V] [Module K V]
  {X : Type uX} [AddCommGroup X] [Module K X]
  {M : Type uM} [AddCommGroup M] [Module K M]

private theorem trace_conjugate (ρ : Representation K G V)
    (t : Module.End K V) (g : G) :
    LinearMap.trace K V ((ρ g).comp (t.comp (ρ g⁻¹))) =
      LinearMap.trace K V t := by
  change LinearMap.trace K V (ρ g * (t * ρ g⁻¹)) = _
  rw [LinearMap.trace_mul_cycle']
  rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

-- Only V has a trace. X and M can be arbitrarily generated, in independent
-- universes; no invalid cyclicity across an infinite-dimensional factor is used.
private theorem trace_tensor_factorization
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

end RelativeTrace

section PolynomialModel

variable (K : Type uK) [Field K]

/-- The primal model of S^(m-1)(W): z^i corresponds to X^i Y^(m-1-i). -/
abbrev Primal (m : ℕ) := Polynomial.degreeLT K m

/-- The original dual module, rather than a separately postulated matrix action. -/
abbrev DualPower (m : ℕ) := Module.Dual K (Primal K m)

/-- Actual polynomial translations by the additive group of the field. -/
def primalAction (m : ℕ) : Representation K (Multiplicative K) (Primal K m) where
  toFun a := (Polynomial.taylorLinearEquiv (Multiplicative.toAdd a) m).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    exact Polynomial.taylor_zero _
  map_mul' a b := by
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    exact (Polynomial.taylor_taylor _ _ _).symm

/-- The contragredient of the actual translation symmetric power. -/
def dualAction (m : ℕ) : Representation K (Multiplicative K) (DualPower K m) :=
  (primalAction K m).dual

/-- The dual monomial basis used in formula (12). -/
def dualBasis (m : ℕ) : Module.Basis (Fin m) K (DualPower K m) :=
  (Polynomial.degreeLT.basis K m).dualBasis

-- This is formula (12) evaluated on the primal monomial a_j. In particular
-- the sign comes from inversion in the contragredient, not a basis rescaling.
private theorem dual_action_basis_value (m : ℕ) (a : K) (i j : Fin m) :
    dualAction K m (Multiplicative.ofAdd a) (dualBasis K m i)
      (Polynomial.degreeLT.basis K m j) =
        (j.val.choose i.val : K) * (-a) ^ (j.val - i.val) := by
  change (Polynomial.degreeLT.basis K m).dualBasis i
    ((Polynomial.taylorLinearEquiv (-a) m)
      (Polynomial.degreeLT.basis K m j)) = _
  rw [Module.Basis.dualBasis_apply, Polynomial.degreeLT.basis_repr]
  change (Polynomial.taylor (-a)
    (Polynomial.degreeLT.basis K m j : K[X])).coeff i = _
  rw [Polynomial.degreeLT.basis_val, Polynomial.taylor_coeff,
    ← Polynomial.monomial_one_right_eq_X_pow, Polynomial.hasseDeriv_monomial]
  simp

private theorem dual_action_matrix (m : ℕ) (a : K) (i j : Fin m) :
    (dualBasis K m).repr
      (dualAction K m (Multiplicative.ofAdd a) (dualBasis K m i)) j =
        (j.val.choose i.val : K) * (-a) ^ (j.val - i.val) := by
  simpa only [dualBasis, Module.Basis.dualBasis_repr]
    using dual_action_basis_value K m a i j

private def coefficient (m k : ℕ) : Module.End K (DualPower K m) :=
  Matrix.toLin (dualBasis K m) (dualBasis K m)
    (Matrix.of fun j i =>
      if j.val = i.val + k then (-1 : K) ^ k * j.val.choose i.val else 0)

private theorem coefficient_matrix (m k : ℕ) (i j : Fin m) :
    (dualBasis K m).repr (coefficient K m k (dualBasis K m i)) j =
      if j.val = i.val + k then (-1 : K) ^ k * j.val.choose i.val else 0 := by
  classical
  rw [← LinearMap.toMatrix_apply, coefficient, LinearMap.toMatrix_toLin]
  rfl

private theorem coefficient_basis_value (m k : ℕ) (i j : Fin m) :
    coefficient K m k (dualBasis K m i) (Polynomial.degreeLT.basis K m j) =
      if j.val = i.val + k then (-1 : K) ^ k * j.val.choose i.val else 0 := by
  simpa only [dualBasis, Module.Basis.dualBasis_repr]
    using coefficient_matrix K m k i j

private theorem dual_action_expansion (m n : ℕ) (hmn : m ≤ n) (a : K) :
    dualAction K m (Multiplicative.ofAdd a) =
      ∑ k : Fin n, a ^ k.val • coefficient K m k.val := by
  classical
  apply (dualBasis K m).ext
  intro i
  apply (Polynomial.degreeLT.basis K m).ext
  intro j
  simp only [LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul,
    smul_eq_mul]
  rw [dual_action_basis_value]
  simp_rw [coefficient_basis_value]
  by_cases hij : i.val ≤ j.val
  · let k : Fin n := ⟨j.val - i.val, by have := j.isLt; omega⟩
    rw [Finset.sum_eq_single k]
    · dsimp only [k]
      rw [if_pos (by omega : j.val = i.val + (j.val - i.val))]
      rw [neg_pow]
      ring
    · intro l _ hl
      have hne : j.val ≠ i.val + l.val := by
        intro he
        apply hl
        apply Fin.ext
        dsimp [k]
        omega
      simp [hne]
    · simp
  · have hchoose : j.val.choose i.val = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hchoose, Nat.cast_zero, zero_mul]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro k _
    have hne : j.val ≠ i.val + k.val := by omega
    simp [hne]

private theorem coefficient_basis_of_lt (m k : ℕ) (i : Fin m) (hi : i.val + k < m) :
    coefficient K m k (dualBasis K m i) =
      ((-1 : K) ^ k * (i.val + k).choose i.val) •
        dualBasis K m ⟨i.val + k, hi⟩ := by
  classical
  apply (Polynomial.degreeLT.basis K m).ext
  intro j
  rw [coefficient_basis_value]
  simp only [LinearMap.smul_apply, smul_eq_mul, dualBasis,
    Module.Basis.dualBasis_apply_self, Fin.ext_iff]
  split_ifs with h
  · rw [h, mul_one]
  · rw [mul_zero]

private theorem coefficient_basis_of_ge (m k : ℕ) (i : Fin m) (hi : m ≤ i.val + k) :
    coefficient K m k (dualBasis K m i) = 0 := by
  apply (Polynomial.degreeLT.basis K m).ext
  intro j
  rw [coefficient_basis_value, LinearMap.zero_apply]
  rw [if_neg (by have := j.isLt; omega)]

end PolynomialModel

section Interpolation

variable {K : Type uK} [Field K] [Fintype K]

private theorem power_sum (n : ℕ) (hn : n ≠ 0) :
    (∑ a : K, a ^ n) = if Fintype.card K - 1 ∣ n then -1 else 0 := by
  classical
  let φ : Kˣ ↪ K := ⟨fun x => x, Units.val_injective⟩
  have hφ : univ.map φ = univ \ {(0 : K)} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and,
      mem_sdiff, mem_singleton, φ] using! isUnit_iff_ne_zero
  calc
    (∑ a : K, a ^ n) = ∑ a ∈ univ \ {(0 : K)}, a ^ n := by
      rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton,
        zero_pow hn, add_zero]
    _ = ∑ a : Kˣ, (a ^ n : K) := by simp [φ, ← hφ, univ.sum_map φ]
    _ = _ := FiniteField.sum_pow_units K n

private theorem coefficient_pairing (hK : Fintype.card K = 27) (k t : Fin 13) :
    -(∑ a : K, a ^ (26 - k.val) * a ^ t.val) = if t = k then 1 else 0 := by
  simp_rw [← pow_add]
  rw [power_sum _ (by have := k.isLt; omega), hK]
  have hd : 27 - 1 ∣ 26 - k.val + t.val ↔ t = k := by
    have hk := k.isLt
    have ht := t.isLt
    rw [show 27 - 1 = 26 from rfl]
    constructor
    · rintro ⟨d, hd⟩
      have : d = 1 := by omega
      apply Fin.ext
      omega
    · intro h
      subst t
      exact ⟨1, by omega⟩
  simp only [hd]
  split_ifs <;> simp

private theorem recover_coefficients
    {E : Type*} [AddCommGroup E] [Module K E]
    (hK : Fintype.card K = 27) (A : Fin 13 → E) (k : Fin 13) :
    -(∑ a : K, a ^ (26 - k.val) • (∑ t : Fin 13, a ^ t.val • A t)) = A k := by
  classical
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  simp_rw [← Finset.sum_smul, ← neg_smul, coefficient_pairing hK k]
  simp

private theorem recover_family
    {E I : Type*} [AddCommGroup E] [Module K E] [Fintype I]
    (hK : Fintype.card K = 27) (d : I → Fin 13) (A : I → E) (k : Fin 13) :
    -(∑ a : K, a ^ (26 - k.val) • (∑ i : I, a ^ (d i).val • A i)) =
      ∑ i : I, if d i = k then A i else 0 := by
  classical
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  simp_rw [← Finset.sum_smul, ← neg_smul, coefficient_pairing hK k]
  apply sum_congr rfl
  intro i _
  split_ifs <;> simp

private theorem extract_dual_coefficient (hK : Fintype.card K = 27) (k : Fin 13) :
    coefficient K 13 k.val =
      -(∑ a : K, a ^ (26 - k.val) • dualAction K 13 (Multiplicative.ofAdd a)) := by
  simp_rw [dual_action_expansion K 13 13 (le_refl 13)]
  exact (recover_coefficients hK (fun t => coefficient K 13 t.val) k).symm

end Interpolation

section TensorCoefficients

variable (K : Type uK) [Field K]

/-- The actual tensor product of the two original seven-dimensional duals. -/
abbrev TensorSpace := DualPower K 7 ⊗[K] DualPower K 7

def tensorAction : Representation K (Multiplicative K) (TensorSpace K) :=
  (dualAction K 7).tprod (dualAction K 7)

private def tensorDegree (i : Fin 7 × Fin 7) : Fin 13 :=
  ⟨i.1.val + i.2.val, by have := i.1.isLt; have := i.2.isLt; omega⟩

private def tensorCoefficient (k : Fin 13) : Module.End K (TensorSpace K) :=
  ∑ i : Fin 7 × Fin 7, if tensorDegree i = k then
    TensorProduct.map (coefficient K 7 i.1.val) (coefficient K 7 i.2.val) else 0

private theorem tensor_action_expansion (a : K) :
    tensorAction K (Multiplicative.ofAdd a) =
      ∑ i : Fin 7 × Fin 7, a ^ (tensorDegree i).val •
        TensorProduct.map (coefficient K 7 i.1.val) (coefficient K 7 i.2.val) := by
  apply TensorProduct.ext'
  intro x y
  simp only [tensorAction, Representation.tprod_apply, TensorProduct.map_tmul,
    dual_action_expansion K 7 7 (le_refl 7), LinearMap.sum_apply,
    LinearMap.smul_apply, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul, Finset.smul_sum, smul_smul,
    ← pow_add, Fintype.sum_prod_type, tensorDegree]
  rw [sum_comm]
  simp only [Nat.add_comm]

set_option maxRecDepth 2048 in
private theorem extract_tensor_coefficient [Fintype K]
    (hK : Fintype.card K = 27) (k : Fin 13) :
    tensorCoefficient K k =
      -(∑ a : K, a ^ (26 - k.val) • tensorAction K (Multiplicative.ofAdd a)) := by
  simp_rw [tensor_action_expansion]
  exact (recover_family hK tensorDegree
    (fun i => TensorProduct.map (coefficient K 7 i.1.val)
      (coefficient K 7 i.2.val)) k).symm

private theorem extracted_intertwines [Fintype K]
    {U Z : Type*} [AddCommGroup U] [Module K U] [AddCommGroup Z] [Module K Z]
    (ρ : Representation K (Multiplicative K) U)
    (σ : Representation K (Multiplicative K) Z)
    (f : ρ.IntertwiningMap σ) (k : Fin 13) :
    f.toLinearMap.comp (-(∑ a : K, a ^ (26 - k.val) • ρ (Multiplicative.ofAdd a))) =
      (-(∑ a : K, a ^ (26 - k.val) • σ (Multiplicative.ofAdd a))).comp f.toLinearMap := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_neg, map_sum, map_smul,
    Representation.IntertwiningMap.toLinearMap_apply, f.isIntertwining]

end TensorCoefficients

section CyclicNormWitness

variable {K : Type uK} [Field K] [CharP K 3]

private def remainderMul {m : ℕ} (q : K[X]) (hq : q.Monic)
    (hd : q.degree = m) (b : K[X]) : Module.End K (Primal K m) where
  toFun p := ⟨(b * (p : K[X])) %ₘ q, Polynomial.mem_degreeLT.mpr
    (hd ▸ Polynomial.degree_modByMonic_lt _ hq)⟩
  map_add' p r := by
    apply Subtype.ext
    simp only [Submodule.coe_add, mul_add, Polynomial.add_modByMonic]
  map_smul' c p := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply, mul_smul_comm,
      Polynomial.smul_modByMonic]

private theorem taylor_modByMonic (q : K[X]) (hq : q.Monic) (a : K)
    (ha : Polynomial.taylor a q = q) (p : K[X]) :
    Polynomial.taylor a (p %ₘ q) = Polynomial.taylor a p %ₘ q := by
  have hdvd : q ∣ Polynomial.taylor a (p %ₘ q) - Polynomial.taylor a p := by
    have h := map_dvd (Polynomial.taylorAlgHom a) (Polynomial.dvd_modByMonic_sub p q)
    change Polynomial.taylor a q ∣
      Polynomial.taylor a (p %ₘ q - p) at h
    simpa only [map_sub, ha] using h
  calc
    Polynomial.taylor a (p %ₘ q) = (Polynomial.taylor a (p %ₘ q)) %ₘ q := by
      symm
      apply (Polynomial.modByMonic_eq_self_iff hq).mpr
      simpa only [Polynomial.degree_taylor] using Polynomial.degree_modByMonic_lt p hq
    _ = _ := Polynomial.modByMonic_eq_of_dvd_sub hq hdvd

private theorem remainderMul_conjugate {m : ℕ} (q : K[X]) (hq : q.Monic)
    (hd : q.degree = m) (b : K[X]) (a : K)
    (ha : Polynomial.taylor a q = q) (p : Primal K m) :
    ((primalAction K m (Multiplicative.ofAdd a))
      (remainderMul q hq hd b
        (primalAction K m (Multiplicative.ofAdd (-a)) p)) : K[X]) =
      (Polynomial.taylor a b * (p : K[X])) %ₘ q := by
  change Polynomial.taylor a
    ((b * Polynomial.taylor (-a) (p : K[X])) %ₘ q) = _
  rw [taylor_modByMonic q hq a ha, Polynomial.taylor_mul,
    Polynomial.taylor_taylor, add_neg_cancel, Polynomial.taylor_zero]

private theorem quadratic_norm :
    (-((X : K[X]) ^ 2)) + Polynomial.taylor (1 : K) (-X ^ 2) +
      Polynomial.taylor (-1 : K) (-X ^ 2) = 1 := by
  simp only [map_neg, Polynomial.taylor_X_pow, Polynomial.C_1, Polynomial.C_neg]
  have hp : (3 : K[X]) = 0 := CharP.cast_eq_zero _ 3
  linear_combination -(X ^ 2 + 1) * hp

private theorem remainderMul_norm {m : ℕ} (q : K[X]) (hq : q.Monic)
    (hd : q.degree = m)
    (hplus : Polynomial.taylor (1 : K) q = q)
    (hminus : Polynomial.taylor (-1 : K) q = q) :
    let t := remainderMul q hq hd (-X ^ 2)
    t + (primalAction K m (Multiplicative.ofAdd (1 : K))).comp
        (t.comp (primalAction K m (Multiplicative.ofAdd (-1 : K)))) +
      (primalAction K m (Multiplicative.ofAdd (-1 : K))).comp
        (t.comp (primalAction K m (Multiplicative.ofAdd (1 : K)))) = LinearMap.id := by
  dsimp only
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    Submodule.coe_add]
  rw [remainderMul_conjugate q hq hd (-X ^ 2) 1 hplus]
  have hneg := remainderMul_conjugate q hq hd (-X ^ 2) (-1) hminus p
  simp only [neg_neg] at hneg
  rw [hneg]
  change (-X ^ 2 * (p : K[X])) %ₘ q +
    (Polynomial.taylor (1 : K) (-X ^ 2) * (p : K[X])) %ₘ q +
      (Polynomial.taylor (-1 : K) (-X ^ 2) * (p : K[X])) %ₘ q = _
  rw [← Polynomial.add_modByMonic, ← Polynomial.add_modByMonic,
    ← add_mul, ← add_mul, quadratic_norm, one_mul]
  exact (Polynomial.modByMonic_eq_self_iff hq).mpr
    (hd ▸ Polynomial.mem_degreeLT.mp p.property)

private def invariantModulus (r : ℕ) : K[X] := (X ^ 3 - X) ^ r

private theorem invariantModulus_monic (r : ℕ) :
    (invariantModulus (K := K) r).Monic := by
  apply Polynomial.Monic.pow
  apply Polynomial.monic_X_pow_sub
  simp only [Polynomial.degree_X]
  norm_num

private theorem invariantModulus_degree (r : ℕ) :
    (invariantModulus (K := K) r).degree = 3 * r := by
  have hb : ((X : K[X]) ^ 3 - X).degree = 3 := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt]
    · exact Polynomial.degree_X_pow 3
    · simp only [Polynomial.degree_X, Polynomial.degree_X_pow]
      norm_num
  simp [invariantModulus, Polynomial.degree_pow, hb, nsmul_eq_mul, mul_comm]

private theorem invariantModulus_translate (r : ℕ) (a : K) (ha : a ^ 3 = a) :
    Polynomial.taylor a (invariantModulus (K := K) r) = invariantModulus r := by
  have hb : Polynomial.taylor a ((X : K[X]) ^ 3 - X) = X ^ 3 - X := by
    rw [map_sub, Polynomial.taylor_X_pow, Polynomial.taylor_X,
      add_pow_char _ _ 3, ← Polynomial.C_pow, ha]
    ring
  simpa only [invariantModulus, Polynomial.taylor_pow, hb]

private def primalNormWitness (r : ℕ) : Module.End K (Primal K (3 * r)) :=
  remainderMul (invariantModulus r) (invariantModulus_monic r)
    (invariantModulus_degree r) (-X ^ 2)

private def dualNormWitness (r : ℕ) : Module.End K (DualPower K (3 * r)) :=
  Module.Dual.transpose (primalNormWitness r)

private theorem dual_norm_three (r : ℕ) :
    let t := dualNormWitness (K := K) r
    t + (dualAction K (3 * r) (Multiplicative.ofAdd (1 : K))).comp
        (t.comp (dualAction K (3 * r) (Multiplicative.ofAdd (-1 : K)))) +
      (dualAction K (3 * r) (Multiplicative.ofAdd (-1 : K))).comp
        (t.comp (dualAction K (3 * r) (Multiplicative.ofAdd (1 : K)))) = LinearMap.id := by
  have ht := remainderMul_norm (invariantModulus (K := K) r)
    (invariantModulus_monic r) (invariantModulus_degree r)
    (invariantModulus_translate r 1 (by simp))
    (invariantModulus_translate r (-1) (by norm_num))
  dsimp only at ht ⊢
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro p
  have hp := congrArg f (LinearMap.congr_fun ht p)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    map_add] at hp
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    dualAction, Representation.dual_apply, dualNormWitness,
    Module.Dual.transpose_apply, ofAdd_neg, inv_inv]
  change f (primalNormWitness r p) +
    f (primalAction K (3 * r) (Multiplicative.ofAdd (1 : K))
      (primalNormWitness r
        (primalAction K (3 * r) (Multiplicative.ofAdd (-1 : K)) p))) +
    f (primalAction K (3 * r) (Multiplicative.ofAdd (-1 : K))
      (primalNormWitness r
        (primalAction K (3 * r) (Multiplicative.ofAdd (1 : K)) p))) = f p
  exact hp

private def primeSubgroup : Multiplicative (ZMod 3) →* Multiplicative K where
  toFun c := Multiplicative.ofAdd
    (ZMod.castHom (dvd_refl 3) K (Multiplicative.toAdd c))
  map_one' := by simp
  map_mul' c d := by simp

private theorem sum_c3 {E : Type*} [AddCommMonoid E]
    (f : Multiplicative (ZMod 3) → E) :
    (∑ c, f c) = f (Multiplicative.ofAdd 0) + f (Multiplicative.ofAdd 1) +
      f (Multiplicative.ofAdd (-1)) := by
  change (∑ c : Fin 3, f (Multiplicative.ofAdd c)) = _
  exact Fin.sum_univ_three _

private theorem dual_norm (r : ℕ) :
    (∑ c : Multiplicative (ZMod 3),
      (dualAction K (3 * r) (primeSubgroup c)).comp
        ((dualNormWitness r).comp (dualAction K (3 * r) (primeSubgroup c⁻¹)))) =
      LinearMap.id := by
  rw [sum_c3]
  simpa [primeSubgroup, ← Module.End.mul_eq_comp] using dual_norm_three (K := K) r

/-- The original relative module M = V_3 ⊕ V_6 ⊕ ... ⊕ V_27. -/
abbrev RelativeSpace (K : Type uK) [Field K] :=
  ⨁ i : Fin 9, DualPower K (3 * (i.val + 1))

def relativeAction : Representation K (Multiplicative K) (RelativeSpace K) :=
  Representation.directSum (fun i : Fin 9 => dualAction K (3 * (i.val + 1)))

private def relativeNormWitness : Module.End K (RelativeSpace K) :=
  DirectSum.lmap (fun i : Fin 9 => dualNormWitness (i.val + 1))

private theorem relative_norm :
    (∑ c : Multiplicative (ZMod 3),
      (relativeAction (K := K) (primeSubgroup c)).comp
        (relativeNormWitness.comp (relativeAction (K := K) (primeSubgroup c⁻¹)))) =
      LinearMap.id := by
  apply LinearMap.ext
  intro m
  apply DFinsupp.ext
  intro i
  simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply,
    relativeAction, Representation.directSum_apply, relativeNormWitness,
    DirectSum.lmap_apply, DirectSum.sum_apply]
    using LinearMap.congr_fun (dual_norm (K := K) (i.val + 1)) (m i)

end CyclicNormWitness

end D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
