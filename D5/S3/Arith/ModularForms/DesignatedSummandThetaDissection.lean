/- GID: D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/DesignatedSummandThetaDissection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: The full signed Jacobi sum splits through a degree-preserving parity bijection. -/

/-
admission_basis: escape-witness through U_dissection and the parity lattice reindexing
U_product proof_shape: content
  escape_witness: the finite weighted-sum factor identification before the full limit
phi_product proof_shape: content
  escape_witness: the sign-twisted Laurent cone specialization on the full product
psi_product proof_shape: content
  escape_witness: the constant-unit Jacobi product and triangular pairing
U_dissection proof_shape: content
  escape_witness: the signed parity bijection and finite degree fibers
prod_split_two proof_shape: bind-only
  Consumers: finiteE_split, U_product, finEta_split
Escape registration: unfinished. See https://github.com/the-omega-institute/trureturing/issues/33480.

Direct frozen dependencies:
  D5.S3.Arith.ModularForms.CubicThetaJacobi
  D5.S3.Arith.ModularForms.CubicThetaJacobiCube
  D5.S3.Arith.ModularForms.CubicThetaProductTwist
  D5.S3.Arith.ModularForms.CubicThetaTwistedColumns
  D5.S3.Arith.ModularForms.WeightedJacobiSpecialization
  D5.S3.Combinatorics.PowerSeries.LaurentSpecialization
-/

import D5.S3.Combinatorics.Partitions.DesignatedSummands
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import D5.S3.Arith.ModularForms.WeightedJacobiSpecialization
import D5.S3.Arith.ModularForms.CubicThetaTwistedColumns

/-! The weighted, sign-twisted and constant-unit Jacobi specializations give the three theta products. The parity split reindexes the entire bilateral product and preserves coefficientwise summability. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace D5.S3.Combinatorics.PowerSeries.DilatedEulerProduct

open Finset

theorem prod_split_two {M : Type*} [CommMonoid M] (g : ℕ → M) (N : ℕ) :
    (∏ j ∈ range (2 * N), g j) =
    (∏ j ∈ range N, g (2 * j)) * (∏ j ∈ range N, g (2 * j + 1)) := by
  let e : Fin N × Fin 2 ≃ Fin (2 * N) := finProdFinEquiv.trans (finCongr (Nat.mul_comm N 2))
  calc
    _ = ∏ i : Fin (2 * N), g i := (Fin.prod_univ_eq_prod_range g _).symm
    _ = ∏ pair : Fin N × Fin 2, g (e pair) :=
      (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [← univ_product_univ, prod_product]
      simp only [Fin.prod_univ_two, e, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
        finProdFinEquiv_apply_val, Fin.val_zero, Fin.val_one, zero_add, add_comm 1,
        prod_mul_distrib]
      rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => g (2 * j)) N,
        Fin.prod_univ_eq_prod_range (fun j : ℕ => g (2 * j + 1)) N]

end D5.S3.Combinatorics.PowerSeries.DilatedEulerProduct

namespace D5.S3.Arith.ModularForms.DesignatedSummandThetaDissection

open Filter Finset _root_.PowerSeries
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology
open D5.S3.Arith.ModularForms
open D5.S3.Arith.ModularForms.CubicThetaJacobi
open D5.S3.Arith.ModularForms.CubicThetaJacobiCube
open D5.S3.Arith.ModularForms.CubicThetaTwistedColumns (twist twist_single)
open D5.S3.Arith.ModularForms.CubicThetaProductTwist
open D5.S3.Combinatorics.PowerSeries.LaurentSpecialization
open D5.S3.Combinatorics.PowerSeries.DilatedEulerProduct

section JacobiProducts

private local instance : UniformSpace ℚ := ⊥
private local instance : DiscreteUniformity ℚ := ⟨rfl⟩
private local instance : UniformSpace (LaurentPolynomial ℚ) := ⊥
private local instance : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩

local notation "Q" => PowerSeries ℚ
local notation "x" => (PowerSeries.X : PowerSeries ℚ)
local notation "f[" d "]" => (euler d (by decide) : Q)

noncomputable def U : Q := WeightedJacobiSpecialization.J 2 1

private theorem hasSum_U :
    HasSum (fun k : ℤ => C ((-1 : ℚ) ^ k.natAbs) *
      x ^ WeightedJacobiSpecialization.weightedExponent 2 1 k) U :=
  WeightedJacobiSpecialization.hasSum_J 2 1

private noncomputable def minusUnit : ℚˣ := -1

private theorem minusUnit_phase (k : ℤ) :
    (↑(minusUnit ^ k) : ℚ) = (-1 : ℚ) ^ k.natAbs := by
  cases k with
  | ofNat k => simp [minusUnit]
  | negSucc k => simp [minusUnit, zpow_negSucc, ← inv_pow]

private theorem phase_sq (k : ℤ) :
    ((-1 : ℚ) ^ k.natAbs) * ((-1 : ℚ) ^ k.natAbs) = 1 := by
  rw [← mul_pow]
  norm_num

noncomputable def phi : Q :=
  specialize 0 1 (PowerSeries.map (twist (RingHom.id ℚ) minusUnit) jacobiSeries)

private theorem hasSum_phi : HasSum (fun k : ℤ => x ^ k.natAbs ^ 2) phi := by
  let t := PowerSeries.map (twist (RingHom.id ℚ) minusUnit)
  have hmap := hasSum_map_jacobi (twist (RingHom.id ℚ) minusUnit)
  have h := hmap.map (specializeAdd 0 1) (continuous_specialize 0 1)
  change HasSum (fun k => specialize 0 1 (t (jacobiTerm k))) phi at h
  convert h using 1
  funext k
  have ht : t (jacobiTerm k) =
      C (LaurentPolynomial.C 1 * LaurentPolynomial.T k) * PowerSeries.X ^ triangularExponent k := by
    rw [jacobiTerm]
    simp only [t, map_mul, PowerSeries.map_C, map_pow, PowerSeries.map_X, twist_single,
      RingHom.id_apply, minusUnit_phase, phase_sq]
    rw [LaurentPolynomial.single_eq_C_mul_T, map_mul]
  rw [ht, specialize_monomial 0 1 _ _ _
    (WeightedJacobiSpecialization.triangular_add_index_nonnegative k), map_one, one_mul]
  congr 1
  have he := WeightedJacobiSpecialization.twice_weightedExponent 0 1 k
  have ht : (↑(k.natAbs ^ 2) : ℤ) = k ^ 2 := by
    rw [Nat.cast_pow, Int.natAbs_sq]
  apply Int.ofNat.inj
  change (↑(k.natAbs ^ 2) : ℤ) = (WeightedJacobiSpecialization.weightedExponent 0 1 k : ℤ)
  rw [ht]
  push_cast at he
  nlinarith

noncomputable def psi : Q :=
  C (1 / 2 : ℚ) * jacobiEvaluation (RingHom.id ℚ) minusUnit

private theorem hasSum_psi :
    HasSum (fun n : ℕ => x ^ triangularExponent (-(n : ℤ))) psi := by
  have h := hasSum_map_jacobi (LaurentPolynomial.eval₂ (RingHom.id ℚ) minusUnit)
  change HasSum (fun k => PowerSeries.map _ (jacobiTerm k))
    (jacobiEvaluation (RingHom.id ℚ) minusUnit) at h
  have heval (k : ℤ) : LaurentPolynomial.eval₂ (RingHom.id ℚ) minusUnit
      (AddMonoidAlgebra.single k ((-1 : ℚ) ^ k.natAbs)) = 1 := by
    rw [LaurentPolynomial.single_eq_C_mul_T, map_mul, LaurentPolynomial.eval₂_C,
      LaurentPolynomial.eval₂_T, RingHom.id_apply, minusUnit_phase, phase_sq]
  simp only [jacobiTerm, map_mul, PowerSeries.map_C, map_pow, PowerSeries.map_X,
    heval, map_one, one_mul] at h
  have hneg := (Equiv.neg ℤ).hasSum_iff.mpr h
  have hpair := hneg.nat_add_neg_add_one
  have hp := hpair.mul_left (C (1 / 2 : ℚ))
  change HasSum (fun n : ℕ => C (1 / 2 : ℚ) *
    (x ^ triangularExponent (-(n : ℤ)) + x ^ triangularExponent (-(-((n : ℤ) + 1))))) psi at hp
  convert hp using 1
  funext n
  have hd : triangularExponent (-(-((n : ℤ) + 1))) = triangularExponent (-(n : ℤ)) := by
    apply Int.ofNat.inj
    have h₁ := twice_triangular (-(-((n : ℤ) + 1)))
    have h₂ := twice_triangular (-(n : ℤ))
    change (triangularExponent (-(-((n : ℤ) + 1))) : ℤ) = (triangularExponent (-(n : ℤ)) : ℤ)
    nlinarith only [h₁,h₂]
  rw [hd, ← two_mul, ← mul_assoc, ← map_ofNat (C : ℚ →+* Q) 2, ← map_mul]
  norm_num

private noncomputable def finiteE (d N : ℕ) : Q :=
  ∏ i ∈ range N, (1 - x ^ (d * (i + 1)))

private noncomputable def oddFactors (d N : ℕ) (sign : ℚ) : Q :=
  ∏ i ∈ range N, (1 - C sign * x ^ (d * (2*i+1)))

private theorem finiteE_split (d N : ℕ) :
    finiteE d (2*N) = finiteE (2*d) N * oddFactors d N 1 := by
  rw [finiteE, prod_split_two, finiteE, oddFactors]
  simp only [map_one, one_mul]
  rw [mul_comm]
  congr 1
  apply prod_congr rfl
  intro j _
  congr 2
  ring

private theorem oddFactors_pair (d N : ℕ) :
    oddFactors d N (-1) * oddFactors d N 1 = oddFactors (2*d) N 1 := by
  simp only [oddFactors, map_neg, map_one, one_mul, neg_one_mul, sub_neg_eq_add,
    ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  rw [show (2*d) * (2*i+1) = d*(2*i+1)*2 by ring, pow_mul]
  ring

theorem U_product : U * f[2] = f[4] * f[1] := by
  have hU := WeightedJacobiSpecialization.tendsto_finiteProduct 2 1
  have h2 := (euler_tendsto (R := ℚ) 2 (by decide)).comp (tendsto_atTop_mono (fun n : ℕ => Nat.le_mul_of_pos_left n (by decide : 0 < 2)) tendsto_id)
  have h4 := euler_tendsto (R := ℚ) 4 (by decide)
  have h1 := (euler_tendsto (R := ℚ) 1 (by decide)).comp (tendsto_atTop_mono (fun n : ℕ => Nat.le_mul_of_pos_left n (by decide : 0 < 4)) tendsto_id)
  change Tendsto (fun N => finiteE 2 (2*N)) atTop (nhds (f[2])) at h2
  change Tendsto (finiteE 4) atTop (nhds (f[4])) at h4
  change Tendsto (fun N => finiteE 1 (4*N)) atTop (nhds (f[1])) at h1
  apply tendsto_nhds_unique (hU.mul h2)
  convert h4.mul h1 using 1
  funext N
  rw [show 4*N = 2*(2*N) by ring, finiteE_split 1 (2*N)]
  have ho : oddFactors 1 (2*N) 1 =
      (∏ i ∈ range N, (1 - x ^ (4*i+1))) * (∏ i ∈ range N, (1 - x ^ (4*i+3))) := by
    rw [oddFactors, prod_split_two]
    simp only [map_one, one_mul, one_mul]
    congr 1 <;> (apply prod_congr rfl; intro i _; congr 2; omega)
  rw [ho]
  simp only [WeightedJacobiSpecialization.finiteProduct, finiteE, Nat.reduceAdd]
  ring

private theorem twist_T (k : ℤ) : twist (RingHom.id ℚ) minusUnit (LaurentPolynomial.T k) =
    LaurentPolynomial.C ((-1 : ℚ) ^ k.natAbs) * LaurentPolynomial.T k := by
  have h := twist_single (RingHom.id ℚ) minusUnit k 1
  simpa only [LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul, minusUnit_phase] using h

private theorem phi_factor (n : ℕ) (k : ℤ) (hk : 0 ≤ (n : ℤ) + k)
    (hs : k = 1 ∨ k = -1) :
    specialize 0 1
      (PowerSeries.map (twist (RingHom.id ℚ) minusUnit)
        (1 - C (LaurentPolynomial.T k) * PowerSeries.X ^ n)) =
      1 + x ^ (n + ((n : ℤ) + k).toNat) := by
  have hp : ((-1 : ℚ) ^ k.natAbs) = -1 := by rcases hs with rfl | rfl <;> norm_num
  simp only [map_sub, map_one, map_mul, PowerSeries.map_C, twist_T, hp, map_pow,
    PowerSeries.map_X]
  have h := (specializeAdd 0 1).map_sub 1
    (C (LaurentPolynomial.C (-1) * LaurentPolynomial.T k) * PowerSeries.X ^ n)
  change specialize 0 1 _ = _ at h
  rw [← map_mul (C : LaurentPolynomial ℚ →+* PowerSeries (LaurentPolynomial ℚ))]
  rw [h]
  change specialize 0 1 1 - specialize 0 1 _ = _
  rw [specialize_one, specialize_monomial 0 1 _ _ _ hk]
  simp

private theorem phi_admissible (n : ℕ) (k : ℤ) (hk : 0 ≤ (n : ℤ) + k) :
    Admissible (PowerSeries.map (twist (RingHom.id ℚ) minusUnit)
      (1 - C (LaurentPolynomial.T k) * PowerSeries.X ^ n)) := by
  let c : ℚ := (-1 : ℚ) ^ k.natAbs
  let p : PowerSeries (LaurentPolynomial ℚ) :=
    C (LaurentPolynomial.C c * LaurentPolynomial.T k) * PowerSeries.X ^ n
  have h : PowerSeries.map (twist (RingHom.id ℚ) minusUnit)
      (1 - C (LaurentPolynomial.T k) * PowerSeries.X ^ n) = 1 - p := by
    simp only [map_sub, map_one, map_mul, PowerSeries.map_C, twist_T, map_pow,
      PowerSeries.map_X, c, p]
  exact h.symm ▸ admissible_sub (p := 1) (q := p) admissible_one
    (admissible_monomial n k c hk)

private theorem phi_finite (N : ℕ) :
    specialize 0 1 (PowerSeries.map (twist (RingHom.id ℚ) minusUnit)
      ((∏ i ∈ range N, (1 - (PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)) ^ (i + 1))) *
        finiteEulerEvaluation N 0 (LaurentPolynomial.T 1) *
        finiteEulerEvaluation N 1 (LaurentPolynomial.T (-1)))) =
      finiteE 2 N * oddFactors 1 N (-1) ^ 2 := by
  rw [finiteEulerEvaluation_eq_prod, finiteEulerEvaluation_eq_prod]
  simp only [map_mul, map_prod, Nat.add_zero]
  have h0 : ∀ i ∈ range N,
      Admissible (PowerSeries.map (twist (RingHom.id ℚ) minusUnit)
        (1 - (PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)) ^ (i+1))) := by
    intro i _
    simpa only [LaurentPolynomial.T_zero, map_one, one_mul] using
      phi_admissible (i+1) 0 (by omega)
  have hp : ∀ i ∈ range N,
      Admissible (PowerSeries.map (twist (RingHom.id ℚ) minusUnit)
        (1 - C (LaurentPolynomial.T 1) * PowerSeries.X ^ i)) :=
    fun i _ => phi_admissible i 1 (by omega)
  have hn : ∀ i ∈ range N,
      Admissible (PowerSeries.map (twist (RingHom.id ℚ) minusUnit)
        (1 - C (LaurentPolynomial.T (-1)) * PowerSeries.X ^ (i+1))) :=
    fun i _ => phi_admissible (i+1) (-1) (by omega)
  rw [specialize_mul 0 1 (admissible_mul (admissible_prod _ _ h0)
      (admissible_prod _ _ hp)) (admissible_prod _ _ hn),
    specialize_mul 0 1 (admissible_prod _ _ h0) (admissible_prod _ _ hp),
    specialize_prod 0 1 _ _ h0, specialize_prod 0 1 _ _ hp, specialize_prod 0 1 _ _ hn]
  have h0' (i : ℕ) :
      specialize 0 1 (PowerSeries.map (twist (RingHom.id ℚ) minusUnit)
        (1 - (PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)) ^ (i+1))) =
      1 - x ^ (2 * (i+1)) := by
    simp only [map_sub, map_one, map_pow, PowerSeries.map_X]
    have h := specialize_factor 0 1 (i+1) 0 (by omega)
    have hi : (((i + 1 : ℕ) : ℤ) + 0).toNat = i+1 := by omega
    simpa only [LaurentPolynomial.T_zero, map_one, one_mul, hi, Nat.zero_add, ← two_mul] using h
  have hp' (i : ℕ) :
      specialize 0 1 (PowerSeries.map (twist (RingHom.id ℚ) minusUnit)
        (1 - C (LaurentPolynomial.T 1) * PowerSeries.X ^ i)) = 1 + x ^ (2*i+1) := by
    rw [phi_factor i 1 (by omega) (Or.inl rfl)]
    congr 2
    omega
  have hn' (i : ℕ) :
      specialize 0 1 (PowerSeries.map (twist (RingHom.id ℚ) minusUnit)
        (1 - C (LaurentPolynomial.T (-1)) * PowerSeries.X ^ (i+1))) =
      1 + x ^ (2*i+1) := by
    rw [phi_factor (i+1) (-1) (by omega) (Or.inr rfl)]
    congr 2
    omega
  simp only [h0', hp', hn', finiteE, oddFactors, one_mul, map_neg, map_one,
    neg_one_mul, sub_neg_eq_add]
  ring

theorem phi_product : phi * (f[1] ^ 2 * f[4] ^ 2) = f[2] ^ 5 := by
  have ht : Continuous (fun p : PowerSeries (LaurentPolynomial ℚ) =>
      PowerSeries.map (twist (RingHom.id ℚ) minusUnit) p) := by
    rw [continuous_iff_continuousAt]
    intro p
    apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).2
    intro n
    simp only [coeff_map]
    exact (continuous_of_discreteTopology (f := (twist (RingHom.id ℚ) minusUnit))).continuousAt.tendsto.comp
      (PowerSeries.WithPiTopology.continuous_coeff (LaurentPolynomial ℚ) n).continuousAt
  have hm := ht.continuousAt.tendsto.comp tendsto_finite_jacobi
  have hh := (continuous_specialize 0 1).continuousAt.tendsto.comp hm
  change Tendsto (fun N =>
    specialize 0 1 (PowerSeries.map (twist (RingHom.id ℚ) minusUnit)
      ((∏ i ∈ range N, (1 - (PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)) ^ (i + 1))) *
        finiteEulerEvaluation N 0 (LaurentPolynomial.T 1) *
        finiteEulerEvaluation N 1 (LaurentPolynomial.T (-1)))))
    atTop (nhds phi) at hh
  simp only [phi_finite] at hh
  change Tendsto (fun N => finiteE 2 N * oddFactors 1 N (-1)^2) atTop (nhds phi) at hh
  have h1 := (euler_tendsto (R := ℚ) 1 (by decide)).comp (tendsto_atTop_mono (fun n : ℕ => Nat.le_mul_of_pos_left n (by decide : 0 < 2)) tendsto_id)
  have h2 := euler_tendsto (R := ℚ) 2 (by decide)
  have h2' := h2.comp (tendsto_atTop_mono (fun n : ℕ => Nat.le_mul_of_pos_left n (by decide : 0 < 2)) tendsto_id)
  have h4 := euler_tendsto (R := ℚ) 4 (by decide)
  have hl := hh.mul ((h1.pow 2).mul (h4.pow 2))
  have hr := (h2.pow 3).mul (h2'.pow 2)
  have h := tendsto_nhds_unique hl (by
    convert hr using 1
    funext N
    change (finiteE 2 N * oddFactors 1 N (-1)^2) *
        (finiteE 1 (2*N)^2 * finiteE 4 N^2) = finiteE 2 N^3 * finiteE 2 (2*N)^2
    rw [finiteE_split 1, finiteE_split 2]
    change _ = finiteE 2 N^3 * (finiteE 4 N * oddFactors 2 N 1)^2
    rw [← show oddFactors 1 N (-1) * oddFactors 1 N 1 = oddFactors 2 N 1 from oddFactors_pair 1 N]
    ring)
  calc
    _ = _ := h
    _ = _ := by ring

private theorem psi_finite (N : ℕ) :
    (C (1/2 : ℚ) * finiteJacobi (RingHom.id ℚ) minusUnit N) * finiteE 1 N =
      finiteE 2 N ^ 2 := by
  rw [finite_jacobi_eq, finiteFactor, prod_range_succ', finiteFactor, finiteEuler]
  have hp : ((minusUnit : ℚˣ) : ℚ) = -1 := rfl
  have hn : ((minusUnit⁻¹ : ℚˣ) : ℚ) = -1 := by simp [minusUnit]
  simp only [hp, hn, Nat.add_zero, pow_zero, mul_one, map_neg, map_one, sub_neg_eq_add,
    neg_one_mul, one_mul, Nat.add_comm 1]
  have hpair : finiteE 1 N * (∏ i ∈ range N, (1 + x ^ (i+1))) = finiteE 2 N := by
    rw [finiteE, finiteE, ← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    rw [show 2*(i+1) = (i+1)*2 by ring, pow_mul]
    ring
  have hc : (C (1/2 : ℚ) : Q) * (1+1) = 1 := by
    simpa only [map_mul, map_add, map_one] using congrArg (C : ℚ →+* Q)
      (show (1/2 : ℚ) * (1+1) = 1 by norm_num)
  simp only [finiteE, one_mul] at hpair ⊢
  rw [← hpair]
  calc
    _ = (C (1/2 : ℚ) * (1+1)) *
      ((∏ i ∈ range N, (1 - x ^ (i+1))) * (∏ i ∈ range N, (1 + x ^ (i+1))))^2 := by ring
    _ = _ := by rw [hc, one_mul]

theorem psi_product : psi * f[1] = f[2] ^ 2 := by
  have hJ := tendsto_finite_jacobi_evaluation (RingHom.id ℚ) minusUnit
  have h1 := euler_tendsto (R := ℚ) 1 (by decide)
  have h2 := euler_tendsto (R := ℚ) 2 (by decide)
  have hl := (hJ.const_mul (C (1/2 : ℚ))).mul h1
  change Tendsto (fun N => (C (1/2 : ℚ) * finiteJacobi (RingHom.id ℚ) minusUnit N) *
    finiteE 1 N) atTop (nhds (psi * f[1])) at hl
  simp only [psi_finite] at hl
  exact tendsto_nhds_unique hl (h2.pow 2)

end JacobiProducts

section ParityLattice

private def latticeIndex (p : ℤ × ℤ) : (ℕ × ℤ) ⊕ (ℤ × ℕ) :=
  let u := (p.1 + 3*p.2) / 2
  let v := (p.1 - p.2) / 2
  if (p.1+p.2)%2 = 0 then
    .inl ((if 1 ≤ u then u-1 else -u).toNat, v)
  else
    .inr (u, (if 0 ≤ v then v else -v-1).toNat)

private def latticeInverse : (ℕ × ℤ) ⊕ (ℤ × ℕ) → ℤ × ℤ
  | .inl (m,v) =>
    let u := if ((m : ℤ)+1)%2 = v%2 then (m : ℤ)+1 else -(m : ℤ)
    ((u+3*v)/2, (u-v)/2)
  | .inr (u,m) =>
    let v := if (m : ℤ)%2 = u%2 then (m : ℤ) else -(m : ℤ)-1
    ((u+3*v+2)/2, (u-v)/2)

private def latticeEquiv : (ℤ × ℤ) ≃ (ℕ × ℤ) ⊕ (ℤ × ℕ) where
  toFun := latticeIndex
  invFun := latticeInverse
  left_inv := by
    rintro ⟨a,b⟩
    unfold latticeIndex
    dsimp only
    split <;> split <;> simp only [latticeInverse, Prod.mk.injEq] <;>
      split <;> constructor <;> omega
  right_inv := by
    rintro (⟨m,v⟩ | ⟨u,m⟩) <;>
      unfold latticeInverse <;> dsimp only <;> split <;> unfold latticeIndex <;>
      dsimp only <;> split
    all_goals
      first
      | simp only [reduceCtorEq]; omega
      | split <;> simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq] <;>
          constructor <;> omega

open D5.S3.Arith.ModularForms.WeightedJacobiSpecialization (weightedExponent twice_weightedExponent)
open D5.S3.Arith.ModularForms.CubicThetaJacobiCube (triangularExponent twice_triangular)

private def latticeDegree : (ℕ × ℤ) ⊕ (ℤ × ℕ) → ℕ
  | .inl (m,v) => 4 * triangularExponent (-(m : ℤ)) + 6 * v.natAbs ^ 2
  | .inr (u,m) => 1 + 2 * u.natAbs ^ 2 + 12 * triangularExponent (-(m : ℤ))

private theorem lattice_degree (a b : ℤ) :
    weightedExponent 2 1 a + 3 * weightedExponent 2 1 b =
      latticeDegree (latticeEquiv (a,b)) := by
  let u := (a+3*b)/2
  let v := (a-b)/2
  have ha := twice_weightedExponent 2 1 a
  have hb := twice_weightedExponent 2 1 b
  norm_num at ha hb
  change weightedExponent 2 1 a + 3 * weightedExponent 2 1 b =
    latticeDegree (if (a+b)%2 = 0 then
      .inl ((if 1 ≤ u then u-1 else -u).toNat,v)
    else .inr (u,(if 0 ≤ v then v else -v-1).toNat))
  apply Int.ofNat.inj
  change ((weightedExponent 2 1 a + 3 * weightedExponent 2 1 b : ℕ) : ℤ) = _
  push_cast
  split
  · rename_i he
    have hA : 2*a = u+3*v := by dsimp [u,v]; omega
    have hB : 2*b = u-v := by dsimp [u,v]; omega
    have hd : (weightedExponent 2 1 a : ℤ) + 3*(weightedExponent 2 1 b : ℤ) =
        2*u*(u-1)+6*v^2 := by
      have hAsq : (2*a)^2 = (u+3*v)^2 := by rw [hA]
      have hBsq : (2*b)^2 = (u-v)^2 := by rw [hB]
      nlinarith only [ha,hb,hA,hB,hAsq,hBsq]
    rw [hd]
    change _ = ((_ : ℕ) : ℤ)
    simp only [latticeDegree, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Int.natAbs_sq]
    split
    · rename_i hu
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ u-1)]
      have h := twice_triangular (-(u-1))
      nlinarith only [h]
    · rename_i hu
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -u)]
      have h := twice_triangular (-(-u))
      nlinarith only [h]
  · rename_i he
    have hA : 2*a = u+3*v+2 := by dsimp [u,v]; omega
    have hB : 2*b = u-v := by dsimp [u,v]; omega
    have hd : (weightedExponent 2 1 a : ℤ) + 3*(weightedExponent 2 1 b : ℤ) =
        1+2*u^2+6*v*(v+1) := by
      have hAsq : (2*a)^2 = (u+3*v+2)^2 := by rw [hA]
      have hBsq : (2*b)^2 = (u-v)^2 := by rw [hB]
      nlinarith only [ha,hb,hA,hB,hAsq,hBsq]
    rw [hd]
    change _ = ((_ : ℕ) : ℤ)
    simp only [latticeDegree, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
      Nat.cast_one, Int.natAbs_sq]
    split
    · rename_i hv
      rw [Int.toNat_of_nonneg hv]
      have h := twice_triangular (-v)
      nlinarith only [h]
    · rename_i hv
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -v-1)]
      have h := twice_triangular (-(-v-1))
      nlinarith only [h]

private theorem lattice_sign (a b : ℤ) :
    ((-1 : ℚ) ^ a.natAbs) * ((-1 : ℚ) ^ b.natAbs) =
      match latticeEquiv (a,b) with
      | .inl _ => 1
      | .inr _ => -1 := by
  rw [← Int.coe_negOnePow, ← Int.coe_negOnePow, ← Int.cast_mul, ← Units.val_mul, ← Int.negOnePow_add]
  rw [show latticeEquiv (a,b) = latticeIndex (a,b) from rfl]
  unfold latticeIndex
  dsimp only
  by_cases he : (a+b)%2 = 0
  · simp only [he, ite_true]
    have h : Even (a+b) := ⟨(a+b)/2, by omega⟩
    rw [Int.negOnePow_even _ h]
    rfl
  · simp only [he, ite_false]
    have h : Odd (a+b) := ⟨(a+b)/2, by omega⟩
    rw [Int.negOnePow_odd _ h]
    rfl

end ParityLattice

section ThetaDissection

private local instance : UniformSpace ℚ := ⊥
private local instance : DiscreteUniformity ℚ := ⟨rfl⟩

local notation "Q" => PowerSeries ℚ
local notation "x" => (PowerSeries.X : Q)

private theorem c_mul_term (a b : ℚ) (i j : ℕ) :
    (C a * x^i) * (C b * x^j) = C (a*b) * x^(i+j) := by
  rw [map_mul, pow_add]
  ac_rfl

private theorem summable_pair {ι κ : Type*} (s : ι → ℕ) (t : κ → ℕ)
    (hs : ∀ n, {i | s i ≤ n}.Finite) (ht : ∀ n, {j | t j ≤ n}.Finite)
    (a : ι → ℚ) (b : κ → ℚ) :
    Summable (fun p : ι × κ => (C (a p.1)*x^(s p.1))*(C (b p.2)*x^(t p.2))) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro n
  apply summable_of_hasFiniteSupport
  apply ((hs n).prod (ht n)).subset
  intro p hp
  change coeff n ((C (a p.1)*x^(s p.1))*(C (b p.2)*x^(t p.2))) ≠ 0 at hp
  have he : s p.1 + t p.2 = n := by
    by_contra h
    rw [c_mul_term, coeff_C_mul, coeff_X_pow, ite_eq_right (Ne.symm h), mul_zero] at hp
    exact hp rfl
  change s p.1 ≤ n ∧ t p.2 ≤ n
  exact ⟨by omega, by omega⟩

private theorem hasSum_dilate {ι : Type*} {s : ι → ℕ} {a : ι → ℚ} {p : Q}
    (h : HasSum (fun i => C (a i)*x^(s i)) p) (d : ℕ) (hd : d ≠ 0) :
    HasSum (fun i => C (a i)*x^(d*s i)) (expand d hd p) := by
  have hh := h.map (expand d hd (R := ℚ)).toAddMonoidHom (tendsto_expand_discrete d hd)
  change HasSum (fun i => expand d hd (C (a i)*x^(s i))) (expand d hd p) at hh
  simpa only [map_mul, map_pow, expand_C, expand_X, ← pow_mul] using hh

private theorem finite_weighted (n : ℕ) : {k | WeightedJacobiSpecialization.weightedExponent 2 1 k ≤ n}.Finite := by
  apply (Finset.Icc (-(2*(n : ℤ)+2)) (2*(n : ℤ)+2)).finite_toSet.subset
  intro k hk
  apply triangular_bound
  unfold WeightedJacobiSpecialization.weightedExponent at hk
  change (2+1)*triangularExponent k + 1*((triangularExponent k : ℤ)+k).toNat ≤ n at hk
  omega

private theorem finite_triangular (n : ℕ) :
    {k : ℕ | triangularExponent (-(k : ℤ)) ≤ n}.Finite := by
  apply (Finset.range (2*n+3)).finite_toSet.subset
  intro k hk
  have h := triangular_bound (-(k : ℤ)) n hk
  simp only [Finset.mem_Icc] at h
  exact Finset.mem_range.mpr (by omega)

private theorem finite_square (n : ℕ) : {k : ℤ | k.natAbs^2 ≤ n}.Finite := by
  apply (Finset.Icc (-(n : ℤ)) (n : ℤ)).finite_toSet.subset
  intro k hk
  change k.natAbs^2 ≤ n at hk
  have hh : k.natAbs ≤ n := (Nat.le_self_pow (by decide : 2 ≠ 0) _).trans hk
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

private theorem finite_mul_degree {ι : Type*} {s : ι → ℕ}
    (hs : ∀ n, {i | s i ≤ n}.Finite) (c : ℕ) (hc : 0 < c) (n : ℕ) :
    {i | c * s i ≤ n}.Finite := by
  apply (hs n).subset
  intro i hi
  change c*s i ≤ n at hi
  exact (by simpa only [one_mul] using Nat.mul_le_mul_right (s i) (show 1 ≤ c by omega) : s i ≤ c*s i).trans hi

private noncomputable def uterm (k : ℤ) : Q :=
  C ((-1 : ℚ)^k.natAbs) * x^WeightedJacobiSpecialization.weightedExponent 2 1 k

private noncomputable def vterm (k : ℤ) : Q :=
  C ((-1 : ℚ)^k.natAbs) * x^(3*WeightedJacobiSpecialization.weightedExponent 2 1 k)

private def paritySign : (ℕ×ℤ) ⊕ (ℤ×ℕ) → ℚ
  | .inl _ => 1
  | .inr _ => -1

private noncomputable def parityTerm (p : (ℕ×ℤ) ⊕ (ℤ×ℕ)) : Q :=
  C (paritySign p) * x^latticeDegree p

private theorem parityTerm_agrees (a b : ℤ) :
    uterm a * vterm b = parityTerm (latticeEquiv (a,b)) := by
  rw [uterm, vterm, parityTerm, c_mul_term, lattice_degree a b, lattice_sign a b]
  cases latticeEquiv (a,b) <;> rfl

private theorem reindexed_sum : HasSum parityTerm (U * expand 3 (by decide) U) := by
  have hu : HasSum uterm U := hasSum_U
  have hv : HasSum vterm (expand 3 (by decide) U) := hasSum_dilate hasSum_U 3 (by decide)
  have hsum' : Summable (fun p : ℤ × ℤ => uterm p.1 * vterm p.2) :=
    summable_pair (WeightedJacobiSpecialization.weightedExponent 2 1) (fun k => 3*WeightedJacobiSpecialization.weightedExponent 2 1 k)
      finite_weighted (finite_mul_degree finite_weighted 3 (by decide))
      (fun k => (-1 : ℚ)^k.natAbs) (fun k => (-1 : ℚ)^k.natAbs)
  have hh := hu.mul hv hsum'
  apply latticeEquiv.hasSum_iff.mp
  have he : (fun p : ℤ × ℤ => uterm p.1 * vterm p.2) = parityTerm ∘ latticeEquiv := by
    funext p
    exact parityTerm_agrees p.1 p.2
  exact he ▸ hh

private theorem hasSum_dilate_psi (d : ℕ) (hd : d ≠ 0) :
    HasSum (fun m : ℕ => C (1 : ℚ) * x^(d*triangularExponent (-(m : ℤ)))) (expand d hd psi) := by
  apply hasSum_dilate
  simpa only [map_one, one_mul] using hasSum_psi

private theorem hasSum_dilate_phi (d : ℕ) (hd : d ≠ 0) :
    HasSum (fun v : ℤ => C (1 : ℚ) * x^(d*v.natAbs^2)) (expand d hd phi) := by
  apply hasSum_dilate
  simpa only [map_one, one_mul] using hasSum_phi

private theorem parityTerm_even : HasSum (parityTerm ∘ Sum.inl)
    (expand 4 (by decide) psi * expand 6 (by decide) phi) := by
  have hh := (hasSum_dilate_psi 4 (by decide)).mul (hasSum_dilate_phi 6 (by decide))
    (summable_pair (fun m : ℕ => 4*triangularExponent (-(m : ℤ))) (fun v : ℤ => 6*v.natAbs^2)
      (finite_mul_degree finite_triangular 4 (by decide))
      (finite_mul_degree finite_square 6 (by decide)) (fun _ => 1) (fun _ => 1))
  simpa only [Function.comp_def, parityTerm, paritySign, latticeDegree, c_mul_term, mul_one] using hh

private theorem parityTerm_odd : HasSum (parityTerm ∘ Sum.inr)
    (-(x * (expand 2 (by decide) phi * expand 12 (by decide) psi))) := by
  have hh := (hasSum_dilate_phi 2 (by decide)).mul (hasSum_dilate_psi 12 (by decide))
    (summable_pair (fun v : ℤ => 2*v.natAbs^2) (fun m : ℕ => 12*triangularExponent (-(m : ℤ)))
      (finite_mul_degree finite_square 2 (by decide))
      (finite_mul_degree finite_triangular 12 (by decide)) (fun _ => 1) (fun _ => 1))
  convert hh.mul_left (-x) using 1
  · funext p
    simp only [Function.comp_def, parityTerm, paritySign, latticeDegree, c_mul_term,
      map_neg, map_one, mul_one, neg_one_mul, neg_mul]
    simp only [one_mul, add_assoc, pow_add, pow_one]
  · rw [neg_mul]

theorem U_dissection :
    U * expand 3 (by decide) U =
      expand 4 (by decide) psi * expand 6 (by decide) phi -
        x * (expand 2 (by decide) phi * expand 12 (by decide) psi) := by
  exact reindexed_sum.unique (by simpa only [sub_eq_add_neg] using parityTerm_even.sum parityTerm_odd)

end ThetaDissection

end D5.S3.Arith.ModularForms.DesignatedSummandThetaDissection
