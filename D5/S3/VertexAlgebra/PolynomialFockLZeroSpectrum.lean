/- GID: D5/S3/VertexAlgebra/PolynomialFockLZeroSpectrum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/PolynomialFockLZeroSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The concrete Sugawara L0 has finite-dimensional weighted-monomial eigenspaces. -/

/-
proof_shape: energyFiber_finite: content; lZero_spectrum: content
escape_witness: Positive weight bounds both every occupied index and its exponent, giving
  finite fibers despite infinitely many variables. The frozen Sugawara commutator and
  vacuum calculation determine the action of L 0 on every monomial; coefficientwise
  comparison then excludes all other weights from its kernel.
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S3/VertexAlgebra/PolynomialFockSugawaraCommutators.L_mode_commutator
  (sha256:70348f27aba9962d3e7e1069a03392b19973770fa93026cf488d6119d17860b5).
-/

import D5.S3.VertexAlgebra.PolynomialFockSugawaraCommutators
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.PolynomialFockLZeroSpectrum

open MvPolynomial
open D5.S3.VertexAlgebra.PolynomialFockSugawaraSupport
open D5.S3.VertexAlgebra.PolynomialFockSugawaraCommutators

/-- Weighted degree, with the variable `X i` contributing `i + 1`. -/
def energy (d : ℕ →₀ ℕ) : ℕ := d.sum fun i e => (i + 1) * e

/-- Exponent vectors of a fixed nonnegative energy. -/
abbrev EnergyFiber (N : ℕ) := {d : ℕ →₀ ℕ // energy d = N}

/-- The eigenspace of the actual pointwise-finite Sugawara operator. -/
noncomputable def lZeroEigenspace (N : ℕ) : Submodule ℂ Fock :=
  LinearMap.ker (L 0 - (N : ℂ) • (LinearMap.id : Module.End ℂ Fock))

/-- Positive variable weights bound occupied indices and exponents, even for infinitely
many available variables. -/
theorem energyFiber_finite (N : ℕ) : Finite (EnergyFiber N) := by
  classical
  have hweight (d : ℕ →₀ ℕ) :
      energy d = Finsupp.weight (fun i : ℕ => i + 1) d := by
    simp only [energy, Finsupp.weight_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_comm]
  have hindex (d : EnergyFiber N) (i : ℕ) (hi : N ≤ i) : d.1 i = 0 := by
    by_contra hne
    have h := Finsupp.le_weight_of_ne_zero' (fun j : ℕ => j + 1) hne
    rw [← hweight, d.2] at h
    omega
  have hexponent (d : EnergyFiber N) (i : ℕ) : d.1 i ≤ N := by
    have h := Finsupp.le_weight (fun j : ℕ => j + 1) (s := i) (by omega) d.1
    rw [← hweight, d.2] at h
    exact h
  let encode (d : EnergyFiber N) (i : Fin N) : Fin (N + 1) :=
    ⟨d.1 i, Nat.lt_succ_of_le (hexponent d i)⟩
  have hinj : Function.Injective encode := by
    intro d e h
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    by_cases hi : i < N
    · have heq := congrFun h ⟨i, hi⟩
      exact congrArg Fin.val heq
    · rw [hindex d i (Nat.le_of_not_lt hi), hindex e i (Nat.le_of_not_lt hi)]
  exact Finite.of_injective encode hinj

/-- The full eigenspace and its dimension are determined by the energy fiber. -/
theorem lZero_spectrum (N : ℕ) :
    lZeroEigenspace N =
      Submodule.span ℂ (Set.range (fun d : EnergyFiber N => monomial d.1 (1 : ℂ))) ∧
    Module.finrank ℂ (lZeroEigenspace N) = Nat.card (EnergyFiber N) := by
  classical
  haveI : Finite (EnergyFiber N) := energyFiber_finite N
  letI : Fintype (EnergyFiber N) := Fintype.ofFinite (EnergyFiber N)
  let b := basisMonomials ℕ ℂ
  have hweight (d : ℕ →₀ ℕ) :
      energy d = Finsupp.weight (fun i : ℕ => i + 1) d := by
    simp only [energy, Finsupp.weight_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_comm]
  have hvacuum : L 0 (1 : Fock) = 0 := by
    have hterm (k : ℤ) : normalPair (-k) k (1 : Fock) = 0 := by
      cases k with
      | ofNat n =>
          cases n with
          | zero => simp [normalPair, mode]
          | succ n =>
              have hneg : -(Int.ofNat (n + 1)) = Int.negSucc n := by
                simp [Int.negSucc_eq, Nat.cast_add]
              rw [hneg]
              simp only [normalPair]
              split_ifs with h
              · simp only [Int.negSucc_eq] at h
                omega
              · simp [mode, annihilate]
      | negSucc n =>
          have hneg : -(Int.negSucc n) = Int.ofNat (n + 1) := by
            simp [Int.negSucc_eq, Nat.cast_add]
          rw [hneg]
          simp only [normalPair]
          split_ifs with h
          · simp [mode, annihilate]
          · simp only [Int.negSucc_eq] at h
            omega
    change (2 : ℂ)⁻¹ • (∑ᶠ k : ℤ, normalPair (0 - k) k (1 : Fock)) = 0
    simp [hterm]
  have hraise (k : ℕ) (p : Fock) :
      L 0 ((X k : Fock) * p) =
        (X k : Fock) * L 0 p + (k + 1 : ℂ) • ((X k : Fock) * p) := by
    have h := congrArg (fun T : Module.End ℂ Fock => T p)
      (L_mode_commutator 0 (Int.negSucc k))
    change L 0 ((X k : Fock) * p) - (X k : Fock) * L 0 p =
      (-(Int.negSucc k : ℂ)) • ((X k : Fock) * p) at h
    have hc : -(Int.negSucc k : ℂ) = (k + 1 : ℂ) := by
      simp [Int.negSucc_eq]
    rw [hc] at h
    linear_combination h
  have hpower (k e : ℕ) (p : Fock) (E : ℂ)
      (hp : L 0 p = E • p) :
      L 0 ((X k : Fock) ^ e * p) =
        (E + (e : ℂ) * (k + 1 : ℂ)) • ((X k : Fock) ^ e * p) := by
    induction e with
    | zero => simpa using hp
    | succ e ih =>
        have hmul : (X k : Fock) ^ (e + 1) * p =
            (X k : Fock) * ((X k : Fock) ^ e * p) := by
          rw [pow_succ']
          ring
        rw [hmul, hraise, ih, mul_smul_comm, ← add_smul]
        congr 1
        push_cast
        ring
  have hmonomial (d : ℕ →₀ ℕ) :
      L 0 (monomial d (1 : ℂ)) = (energy d : ℂ) • monomial d (1 : ℂ) := by
    induction d using Finsupp.induction with
    | zero =>
        simpa [energy] using hvacuum
    | single_add k e d _ _ ih =>
        have he : energy (Finsupp.single k e + d) = (k + 1) * e + energy d := by
          rw [hweight, map_add, Finsupp.weight_single, ← hweight]
          simp [mul_comm]
        have hm : monomial (Finsupp.single k e + d) (1 : ℂ) =
            (X k : Fock) ^ e * monomial d (1 : ℂ) := by
          rw [X_pow_eq_monomial, monomial_mul]
          simp
        rw [hm, he]
        have hc : (((k + 1) * e + energy d : ℕ) : ℂ) =
            (energy d : ℂ) + (e : ℂ) * (k + 1 : ℂ) := by
          push_cast
          ring
        rw [hc]
        exact hpower k e (monomial d 1) (energy d : ℂ) ih
  have hcoeff (p : Fock) (d : ℕ →₀ ℕ) :
      coeff d (L 0 p) = (energy d : ℂ) * coeff d p := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum, coeff_sum]
    have hterm (e : ℕ →₀ ℕ) :
        L 0 (monomial e (coeff e p)) =
          (energy e : ℂ) • monomial e (coeff e p) := by
      have hm : monomial e (coeff e p) = (coeff e p) • monomial e (1 : ℂ) := by
        simp only [smul_monomial, smul_eq_mul, mul_one]
      rw [hm, map_smul, hmonomial, smul_comm]
    simp_rw [hterm, coeff_smul]
    by_cases hd : d ∈ p.support
    · simp [coeff_monomial, hd, Finset.sum_ite_eq', mul_comm]
    · have hz : coeff d p = 0 := Finsupp.notMem_support_iff.mp hd
      simp [coeff_monomial, hd, hz]
  have hspan : lZeroEigenspace N =
      Submodule.span ℂ (Set.range (fun d : EnergyFiber N => monomial d.1 (1 : ℂ))) := by
    apply le_antisymm
    · intro p hp
      simp only [lZeroEigenspace, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hp
      have hs : ↑(b.repr p).support ⊆ {d : ℕ →₀ ℕ | energy d = N} := by
        intro d hd
        have hnonzero : coeff d p ≠ 0 := by
          have hd' : (b.repr p) d ≠ 0 := Finsupp.mem_support_iff.mp hd
          change coeff d p ≠ 0 at hd'
          exact hd'
        have heq := congrArg (coeff d) hp
        rw [hcoeff, coeff_smul] at heq
        have hcast : (energy d : ℂ) = (N : ℂ) :=
          (mul_right_cancel₀ hnonzero) (by simpa [smul_eq_mul] using heq)
        exact_mod_cast hcast
      have hm : p ∈ Submodule.span ℂ
          (b '' {d : ℕ →₀ ℕ | energy d = N}) :=
        (b.mem_span_image).2 hs
      have hset : Set.range (fun d : EnergyFiber N => monomial d.1 (1 : ℂ)) =
          b '' {d : ℕ →₀ ℕ | energy d = N} := by
        ext x
        constructor
        · rintro ⟨d, rfl⟩
          exact ⟨d.1, d.2, rfl⟩
        · rintro ⟨d, hd, rfl⟩
          exact ⟨⟨d, hd⟩, rfl⟩
      rw [hset]
      exact hm
    · apply Submodule.span_le.mpr
      rintro x ⟨d, rfl⟩
      change (L 0 - (N : ℂ) • (LinearMap.id : Module.End ℂ Fock))
        (monomial d.1 (1 : ℂ)) = 0
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero]
      rw [hmonomial, d.2]
  refine ⟨hspan, ?_⟩
  rw [hspan]
  have hli : LinearIndependent ℂ
      (fun d : EnergyFiber N => monomial d.1 (1 : ℂ)) := by
    simpa only [Function.comp_def, coe_basisMonomials] using
      (basisMonomials ℕ ℂ).linearIndependent.comp
      (fun d : EnergyFiber N => d.1) (fun _ _ h => Subtype.ext h)
  simpa only [Nat.card_eq_fintype_card] using finrank_span_eq_card hli

end D5.S3.VertexAlgebra.PolynomialFockLZeroSpectrum
