/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qRetainedDiagonalComparison
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compare retained Wick coefficients with the regular charged diagonal product. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qRetainedNormalRecurrence
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qDiagonalCreationDerivative
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qDiagonalAnnihilationDerivative
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalWickScalar

/-! The retained diagonal coefficient of the native charged fields at a fixed cutoff. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators LaurentSeries VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge bilinear epsilon)
open P48qTwistedChargeAction (lattice g Momentum)
open P48qIntegratedNormalMode (integratedNormalMode integratedNormalMode_zero)
open P48qRetainedNormalRecurrence
open P48qNativeChargedWickFactorization (retainedJetCoeff nativeRetainedSeries)
open PowerSeries (coeff constantCoeff derivative)
open private creationPolynomial from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldTranslation
open private mapScalarToFock from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedCollision
open private inverseCover oscillatorCoeff_laurent from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedOrderedProduct
open private coeff_powerSeries_mul_inverseCover constantCoeff_coeff_mul_inverseCover from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalAnnihilation
open private normalOrderedCoeff_nil from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qJetNormalOrdering
open private derivative_mapScalarToFock from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qDiagonalAnnihilationDerivative

attribute [local instance 2000] HahnSeries.instAlgebra

local notation "R" => PowerSeries Fock
local notation "Cₜ" => (PowerSeries.C : Fock →+* R)
local notation "H" => HahnSeries.ofPowerSeries ℤ R
local notation "shift" => ThirdTwistedChargeAction.shift lattice g
local notation "E" => nativeDiagonalCreationExponential fixedDualBases
local notation "A" => nativeDiagonalAnnihilationPolynomial fixedDualBases
private def zeroEigenvalue (a : Charge lattice) (p : Momentum) : ℂ :=
  (bilinear lattice a p.1 : ℂ) / 3

private def readout (S : PowerSeries R) (Q : Polynomial R) (k : ℤ) : R :=
  (H S * inverseCover ℂ Q).coeff k

private def momentumFactor (a : Charge lattice) (p : Momentum) : R :=
  mapScalarToFock ((PowerSeries.exp ℂ).subst
    (PowerSeries.C (zeroEigenvalue a p) * PowerSeries.log ℂ))

private def diagonalRetained (a b : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock) : R :=
  Cₜ (algebraMap ℂ Fock (chargePhase (a + b) p)) * momentumFactor a p *
    readout (E a b) (A a b P) (h - momentumExponent (a + b) p)

private theorem momentumFactor_constant (a : Charge lattice) (p : Momentum) :
    constantCoeff (momentumFactor a p) = 1 := by
  have hc : constantCoeff (PowerSeries.C (zeroEigenvalue a p) * PowerSeries.log ℂ) = 0 := by simp
  rw [momentumFactor, mapScalarToFock, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.constantCoeff_eq, PowerSeries.constantCoeff_subst_of_constantCoeff_zero hc,
    PowerSeries.constantCoeff_exp, map_one, map_one]

private theorem momentumFactor_derivative (a : Charge lattice) (p : Momentum) :
    derivative (momentumFactor a p) =
      mapScalarToFock (PowerSeries.C (zeroEigenvalue a p) * derivative (integratedNormalMode 0)) *
        momentumFactor a p := by
  have hc : constantCoeff (PowerSeries.C (zeroEigenvalue a p) * PowerSeries.log ℂ) = 0 := by simp
  rw [momentumFactor, derivative_mapScalarToFock,
    PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hc),
    PowerSeries.derivative_exp, Derivation.leibniz, PowerSeries.derivative_C,
    smul_eq_mul, smul_eq_mul, mul_zero, add_zero, map_mul, integratedNormalMode_zero, mul_comm]

private theorem coeff_hahn_tDerivative (S : PowerSeries R) (k : ℤ) :
    derivative ((H S).coeff k) = (H (diagonalCreationTDerivative S)).coeff k := by
  simp only [PowerSeries.coeff_coe]
  split_ifs <;> simp

private theorem readout_derivative (S : PowerSeries R) (Q : Polynomial R) (k : ℤ) :
    derivative (readout S Q k) =
      readout (diagonalCreationTDerivative S) Q k +
      readout S (diagonalPolynomialTDerivative Q) k := by
  classical
  unfold readout
  rw [coeff_powerSeries_mul_inverseCover, map_sum, coeff_powerSeries_mul_inverseCover,
    coeff_powerSeries_mul_inverseCover]
  have hsupport : (diagonalPolynomialTDerivative Q).support ⊆ Q.support := by
    intro d hd
    rw [Polynomial.mem_support_iff] at hd ⊢
    intro hz
    exact hd (by rw [coeff_diagonalPolynomialTDerivative, hz, map_zero])
  have hs : (∑ d ∈ (diagonalPolynomialTDerivative Q).support,
      (H S).coeff (k + (d : ℤ)) * (diagonalPolynomialTDerivative Q).coeff d) =
      ∑ d ∈ Q.support, (H S).coeff (k + (d : ℤ)) * (diagonalPolynomialTDerivative Q).coeff d :=
    Finset.sum_subset hsupport (fun d _ hd => by
      rw [Polynomial.notMem_support_iff.mp hd, mul_zero])
  rw [hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, coeff_hahn_tDerivative,
    coeff_diagonalPolynomialTDerivative]
  ring

private theorem readout_mul_creation (S T : PowerSeries R) (Q : Polynomial R) (k : ℤ) :
    readout (S * T) Q k =
      ∑ᶠ m : ℤ, (H S).coeff (-m) * readout T Q (k + m) := by
  classical
  let L := H T * inverseCover ℂ Q
  have h : readout (S * T) Q k = (H S * L).coeff k := by
    simp only [readout, L, map_mul, mul_assoc]
  rw [h, HahnSeries.coeff_mul]
  let F := Finset.antidiagonal (H S).isPWO_support L.isPWO_support k
  let f : ℤ × ℤ → ℤ := fun ij => -ij.1
  have hm (ij : ℤ × ℤ) (hij : ij ∈ F) :
      ij.1 ∈ (H S).support ∧ ij.2 ∈ L.support ∧ ij.1 + ij.2 = k :=
    Finset.mem_antidiagonal.mp hij
  have hs : Function.support (fun m : ℤ => (H S).coeff (-m) * readout T Q (k + m)) ⊆
      (F.image f : Set ℤ) := by
    intro m hm'
    change m ∈ F.image f
    change (H S).coeff (-m) * L.coeff (k + m) ≠ 0 at hm'
    refine Finset.mem_image.mpr ⟨(-m, k + m), ?_, by simp [f]⟩
    apply Finset.mem_antidiagonal.mpr
    exact ⟨left_ne_zero_of_mul hm', right_ne_zero_of_mul hm', by omega⟩
  rw [finsum_eq_finsetSum_of_support_subset _ hs, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro ij hij
    have he := (hm ij hij).2.2
    change (H S).coeff ij.1 * L.coeff ij.2 = (H S).coeff (- -ij.1) * L.coeff (k + -ij.1)
    rw [neg_neg, show k + -ij.1 = ij.2 by omega]
  · intro i hi j hj hij
    have hi' := (hm i hi).2.2
    have hj' := (hm j hj).2.2
    change -i.1 = -j.1 at hij
    exact Prod.ext (by omega) (by omega)

private theorem readout_mul_annihilation (S : PowerSeries R) (Q : Polynomial R)
    (k : ℤ) (w : R) (s : ℕ) :
    readout S (Polynomial.C w * Polynomial.X ^ s * Q) k =
      w * readout S Q (k + (s : ℤ)) := by
  have hC : inverseCover ℂ (Polynomial.C w) = HahnSeries.single 0 w := by
    simp only [inverseCover, Polynomial.aevalTower_C, AlgHom.coe_mk, HahnSeries.C_apply]
  have hX : inverseCover ℂ (Polynomial.X : Polynomial R) = HahnSeries.single (-1) 1 := by
    simp only [inverseCover, Polynomial.aevalTower_X]
  have hp : (HahnSeries.single (-1 : ℤ) (1 : R)) ^ s = HahnSeries.single (-(s : ℤ)) 1 := by
    rw [HahnSeries.single_pow, one_pow]
    congr 1
    simp
  rw [readout, map_mul, map_mul, map_pow, hC, hX, hp, HahnSeries.single_mul_single,
    zero_add, mul_one, ← mul_assoc, mul_comm (H S), mul_assoc, HahnSeries.coeff_single_mul,
    sub_neg_eq_add, readout]

private theorem readout_sum_annihilation {ι : Type*} (S : PowerSeries R) (F : Finset ι)
    (Q : ι → Polynomial R) (k : ℤ) :
    readout S (∑ i ∈ F, Q i) k = ∑ i ∈ F, readout S (Q i) k := by
  simp only [readout, map_sum, Finset.mul_sum, HahnSeries.coeff_sum]

private theorem diagonalRetained_initial (D : ℕ) (a b : Charge lattice) (h : ℤ)
    (p : Momentum) (P : Fock) :
    retainedCoefficient D 0 a b h p P = coeff 0 (diagonalRetained a b h p P) := by
  rw [retainedCoefficient, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    P48qFiniteWickSum.retainedSeries, P48qFiniteWickSum.constantCoeff_wordSeries,
    diagonalRetained, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [List.nil_append, map_mul, PowerSeries.constantCoeff_C, momentumFactor_constant, mul_one]
  rw [readout, constantCoeff_coeff_mul_inverseCover, nativeDiagonalCreationExponential_eval]
  have hA : (A a b P).map (PowerSeries.constantCoeff : PowerSeries Fock →+* Fock) =
      translatedPolynomial fixedDualBases (a + b) P :=
    translatedPolynomial_diagonal _ _ _ _
  rw [hA, oscillatorCoeff_laurent, retainedJetCoeff]
  simp only [P48qAllJetWickField.totalLevel, Nat.cast_zero, mul_zero, sub_zero,
    normalOrderedCoeff_nil]
  change (fieldCoeff fixedDualBases (a + b) h (Finsupp.single p P)) (shift (a + b) p) = _
  rw [fieldCoeff_single, Finsupp.single_eq_same, Algebra.smul_def]

#print axioms diagonalRetained_initial
#print axioms readout_derivative
#print axioms readout_mul_creation
#print axioms readout_mul_annihilation

private theorem readout_eq_zero_of_lt (S : PowerSeries R) (Q : Polynomial R) (k : ℤ)
    (hk : k < -(Q.natDegree : ℤ)) : readout S Q k = 0 := by
  rw [readout, coeff_powerSeries_mul_inverseCover]
  apply Finset.sum_eq_zero
  intro d hd
  have hdeg := Polynomial.le_natDegree_of_mem_supp d hd
  have hneg : k + (d : ℤ) < 0 := by omega
  rw [PowerSeries.coeff_coe, ite_eq_left hneg, zero_mul]

private theorem annihilator_eq_zero_of_bound (a : Charge lattice) (P : Fock) (s : ℕ)
    (hs : occupationBound P < s) : positiveAnnihilator fixedDualBases a (s - 1) P = 0 := by
  apply positiveAnnihilator_eq_zero_of_not_mem
  intro hm
  obtain ⟨j, hj, hjs⟩ := Finset.mem_image.mp hm
  obtain ⟨d, hd, hjd⟩ := (MvPolynomial.mem_vars_iff_mem_support j).mp hj
  have hpos : 1 ≤ d j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hjd)
  have hb : frequency j ≤ occupationBound P := by
    rw [occupationBound_eq]
    calc
      frequency j ≤ d j * frequency j := by
        simpa only [one_mul] using Nat.mul_le_mul_right (frequency j) hpos
      _ ≤ ∑ i ∈ d.support, d i * frequency i :=
        Finset.single_le_sum (fun i _ => Nat.zero_le (d i * frequency i)) hjd
      _ ≤ _ := Finset.le_sup (f := fun e => ∑ i ∈ e.support, e i * frequency i) hd
  unfold frequency at hb
  omega

private theorem diagonalRetained_zero (a b : Charge lattice) (h : ℤ) (p : Momentum) :
    diagonalRetained a b h p 0 = 0 := by
  simp [diagonalRetained, readout]

private def diagonalRetainedMode (a b : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock)
    (m : ℤ) : R :=
  match m with
  | .negSucc s => Cₜ (creationPolynomial fixedDualBases a s) *
      diagonalRetained a b (h + m) p P
  | .ofNat 0 => Cₜ (algebraMap ℂ Fock (zeroEigenvalue a p)) * diagonalRetained a b h p P
  | .ofNat (s + 1) => diagonalRetained a b (h + m) p (positiveAnnihilator fixedDualBases a s P)

private theorem diagonalRetainedMode_finite (a b : Charge lattice) (h : ℤ) (p : Momentum)
    (P : Fock) : Function.HasFiniteSupport (diagonalRetainedMode a b h p P) := by
  let k := h - momentumExponent (a + b) p
  let Q := A a b P
  let F := Finset.Icc (min 0 (-k - (Q.natDegree : ℤ))) (occupationBound P : ℤ)
  refine F.finite_toSet.subset ?_
  intro m hm
  change m ∈ F
  rw [Finset.mem_Icc]
  cases m with
  | negSucc s =>
    refine ⟨le_of_not_gt fun hlo => hm ?_, by omega⟩
    change Cₜ (creationPolynomial fixedDualBases a s) * diagonalRetained a b
      (h + Int.negSucc s) p P = 0
    have hlt : h + Int.negSucc s - momentumExponent (a + b) p < -(Q.natDegree : ℤ) := by
      dsimp [k] at hlo
      omega
    unfold diagonalRetained
    rw [readout_eq_zero_of_lt _ Q _ hlt, mul_zero, mul_zero]
  | ofNat n =>
    refine ⟨min_le_of_left_le (Int.natCast_nonneg n), le_of_not_gt fun hhi => hm ?_⟩
    change (occupationBound P : ℤ) < (n : ℤ) at hhi
    cases n with
    | zero => omega
    | succ s =>
      have hz := annihilator_eq_zero_of_bound a P (s + 1) (by exact_mod_cast hhi)
      change diagonalRetained a b (h + Int.ofNat (s + 1)) p
        (positiveAnnihilator fixedDualBases a s P) = 0
      rw [Nat.add_sub_cancel] at hz
      rw [hz, diagonalRetained_zero]

set_option maxHeartbeats 1400000 in
-- Assemble the three finite signed-mode sums with their dependent support proofs.
private theorem diagonalRetained_derivative (a b : Charge lattice) (h : ℤ) (p : Momentum)
    (P : Fock) : derivative (diagonalRetained a b h p P) =
      ∑ᶠ m : ℤ, mapScalarToFock (derivative (integratedNormalMode m)) *
        diagonalRetainedMode a b h p P m := by
  classical
  let k := h - momentumExponent (a + b) p
  let Q := A a b P
  let L := Cₜ (algebraMap ℂ Fock (chargePhase (a + b) p)) * momentumFactor a p
  let w (m : ℤ) := mapScalarToFock (derivative (integratedNormalMode m))
  let S := diagonalCreationTDerivative (diagonalNegativeCreationSeries fixedDualBases a)
  let neg (m : ℤ) := (H S).coeff (-m) * readout (E a b) Q (k + m)
  let pos (m : ℤ) := if 0 < m then w m * diagonalRetained a b (h + m) p
      (positiveAnnihilator fixedDualBases a (m.toNat - 1) P) else 0
  let zer (m : ℤ) := if m = 0 then w 0 * Cₜ (algebraMap ℂ Fock (zeroEigenvalue a p)) *
    diagonalRetained a b h p P else 0
  have hnegFinite : Function.HasFiniteSupport neg := by
    let F := Finset.Icc (min 0 (-k - (Q.natDegree : ℤ))) (0 : ℤ)
    refine F.finite_toSet.subset ?_
    intro m hm
    change m ∈ F
    rw [Finset.mem_Icc]
    refine ⟨le_of_not_gt fun hlo => hm ?_, le_of_not_gt fun hhi => hm ?_⟩
    · have hlt : k + m < -(Q.natDegree : ℤ) := by omega
      simp [neg, readout_eq_zero_of_lt _ Q _ hlt]
    · have hlt : -m < 0 := by omega
      change (H S).coeff (-m) * readout (E a b) Q (k + m) = 0
      rw [PowerSeries.coeff_coe, ite_eq_left hlt, zero_mul]
  have hnegLFinite : Function.HasFiniteSupport (fun m => L * neg m) := by
    refine hnegFinite.subset ?_
    intro m hm hz
    exact hm (by simp [hz])
  let Fpos := (Finset.Icc 1 (occupationBound P)).image (fun s : ℕ => (s : ℤ))
  have hposSupport : Function.support pos ⊆ (Fpos : Set ℤ) := by
    intro m hm
    have hmpos : 0 < m := by
      by_contra hn
      exact hm (by simp [pos, hn])
    have hbound : m.toNat ≤ occupationBound P := by
      by_contra hn
      have hzero := annihilator_eq_zero_of_bound a P m.toNat (by omega)
      exact hm (by simp [pos, hmpos, hzero, diagonalRetained_zero])
    change m ∈ Fpos
    exact Finset.mem_image.mpr ⟨m.toNat, Finset.mem_Icc.mpr ⟨by omega, hbound⟩, by omega⟩
  have hposFinite : Function.HasFiniteSupport pos := Fpos.finite_toSet.subset hposSupport
  have hzerFinite : Function.HasFiniteSupport zer := by
    refine ({0} : Finset ℤ).finite_toSet.subset ?_
    intro m hm
    by_contra hn
    have hne : m ≠ 0 := by simpa using hn
    exact hm (by simp [zer, hne])
  have hderL : derivative L = w 0 * Cₜ (algebraMap ℂ Fock (zeroEigenvalue a p)) * L := by
    simp only [L, w, Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_C,
      mul_zero, add_zero, momentumFactor_derivative, map_mul]
    have hC : mapScalarToFock (PowerSeries.C (zeroEigenvalue a p)) =
        Cₜ (algebraMap ℂ Fock (zeroEigenvalue a p)) := PowerSeries.map_C _ _
    rw [hC]
    ring
  have hneg : L * readout (diagonalCreationTDerivative (E a b)) Q k =
      ∑ᶠ m : ℤ, L * neg m := by
    rw [nativeDiagonalCreationExponential_derivative, readout_mul_creation]
    change L * (∑ᶠ m : ℤ, neg m) = ∑ᶠ m : ℤ, L * neg m
    exact mul_finsum' neg L hnegFinite
  have hpos : L * readout (E a b) (diagonalPolynomialTDerivative Q) k = ∑ᶠ m : ℤ, pos m := by
    rw [show Q = A a b P from rfl, nativeDiagonalAnnihilationPolynomial_derivative,
      readout_sum_annihilation, Finset.mul_sum, finsum_eq_finsetSum_of_support_subset _ hposSupport]
    change _ = ∑ m ∈ (Finset.Icc 1 (occupationBound P)).image (fun s : ℕ => (s : ℤ)), pos m
    rw [Finset.sum_image (fun i _ j _ hij => by exact_mod_cast hij)]
    apply Finset.sum_congr rfl
    intro s hs
    have hs1 := (Finset.mem_Icc.mp hs).1
    have hspos : (0 : ℤ) < (s : ℤ) := by omega
    rw [readout_mul_annihilation]
    simp only [pos, ite_eq_left hspos, Int.toNat_natCast, diagonalRetained]
    rw [show h + (s : ℤ) - momentumExponent (a + b) p = k + (s : ℤ) by dsimp [k]; ring]
    change L * (w (s : ℤ) * _) = w (s : ℤ) * (L * _)
    ring
  have hzer : derivative L * readout (E a b) Q k = ∑ᶠ m : ℤ, zer m := by
    rw [hderL, finsum_eq_single zer 0 (fun m hm => by simp [zer, hm])]
    simp only [zer, ite_eq_left rfl, diagonalRetained]
    change _ * _ = w 0 * Cₜ (algebraMap ℂ Fock (zeroEigenvalue a p)) *
      (L * readout (E a b) Q k)
    ring
  have hsplit : (fun m : ℤ => w m * diagonalRetainedMode a b h p P m) =
      fun m => (L * neg m + pos m) + zer m := by
    funext m
    cases m with
    | negSucc s =>
      have hm : Int.negSucc s < 0 := Int.negSucc_lt_zero s
      have hn : ¬ 0 < Int.negSucc s := by omega
      have hne : Int.negSucc s ≠ 0 := by omega
      simp only [pos, zer, ite_eq_right hn, ite_eq_right hne, add_zero, neg, diagonalRetainedMode,
        show -Int.negSucc s = ((s + 1 : ℕ) : ℤ) by omega,
        HahnSeries.ofPowerSeries_apply_coeff, S,
        coeff_diagonalNegativeCreationSeries_derivative _ _ _ (Nat.succ_pos s)]
      rw [show -((↑(s + 1 : ℕ) : ℤ)) = Int.negSucc s by omega]
      simp only [diagonalRetained]
      rw [show h + Int.negSucc s - momentumExponent (a + b) p = k + Int.negSucc s by
        dsimp [k]; ring]
      change w (Int.negSucc s) * (Cₜ (creationPolynomial fixedDualBases a s) *
        (L * readout (E a b) Q (k + Int.negSucc s))) =
        L * (w (Int.negSucc s) * Cₜ (creationPolynomial fixedDualBases a s) * _)
      ring
    | ofNat n =>
      cases n with
      | zero =>
        have hz : (H S).coeff (0 : ℤ) = 0 := by
          rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, HahnSeries.ofPowerSeries_apply_coeff,
            PowerSeries.coeff_zero_eq_constantCoeff_apply]
          exact constantCoeff_diagonalNegativeCreationSeries_derivative _ _
        simp [diagonalRetainedMode, neg, pos, zer, hz, mul_assoc]
      | succ s =>
        have hs : (0 : ℤ) < Int.ofNat (s + 1) := Int.natCast_pos.mpr (Nat.succ_pos s)
        have hn : -Int.ofNat (s + 1) < 0 := neg_lt_zero.mpr hs
        have hne : Int.ofNat (s + 1) ≠ 0 := ne_of_gt hs
        simp only [diagonalRetainedMode, pos, zer, ite_eq_left hs, ite_eq_right hne, neg,
          PowerSeries.coeff_coe, ite_eq_left hn, zero_mul, mul_zero, zero_add, add_zero,
          show (Int.ofNat (s + 1)).toNat - 1 = s by rfl]
  change derivative (L * readout (E a b) Q k) =
    ∑ᶠ m : ℤ, w m * diagonalRetainedMode a b h p P m
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, readout_derivative, mul_add,
    hneg, hpos, mul_comm (readout (E a b) Q k), hzer, hsplit]
  change (∑ᶠ m : ℤ, L * neg m) + (∑ᶠ m : ℤ, pos m) + (∑ᶠ m : ℤ, zer m) =
    ∑ᶠ m : ℤ, (((fun i => L * neg i) + pos) + zer) m
  exact ((finsum_add_distrib (hnegLFinite.add hposFinite) hzerFinite).trans
    (congrArg (fun v : R => v + ∑ᶠ m : ℤ, zer m)
      (finsum_add_distrib hnegLFinite hposFinite))).symm

private theorem diagonalRetainedMode_coeff (a b : Charge lattice) (h : ℤ) (p : Momentum)
    (P : Fock) (n : ℕ) (m : ℤ) :
    coeff n (diagonalRetainedMode a b h p P m) =
      (match m with
      | .negSucc s => creationPolynomial fixedDualBases a s *
          coeff n (diagonalRetained a b (h + m) p P)
      | .ofNat 0 => (zeroEigenvalue a p) • coeff n (diagonalRetained a b h p P)
      | .ofNat (s + 1) => coeff n (diagonalRetained a b (h + m) p
          (positiveAnnihilator fixedDualBases a s P))) := by
  cases m with
  | negSucc s => simp only [diagonalRetainedMode, PowerSeries.coeff_C_mul]
  | ofNat t =>
    cases t with
    | zero => simp only [diagonalRetainedMode, PowerSeries.coeff_C_mul, Algebra.smul_def]
    | succ s => rfl

set_option maxHeartbeats 1000000 in
-- Distribute the inner coefficient through the common finite support and antidiagonal.
private theorem diagonalRetained_recurrence (n : ℕ) (a b : Charge lattice) (h : ℤ)
    (p : Momentum) (P : Fock) :
    ((n + 1 : ℕ) : ℂ) • coeff (n + 1) (diagonalRetained a b h p P) =
      ∑ r : Fin (n + 1), ∑ᶠ m : ℤ,
        ((((r.1 + 1 : ℕ) : ℂ) * coeff (r.1 + 1) (integratedNormalMode m)) •
          coeff (n - r.1) (diagonalRetainedMode a b h p P m)) := by
  classical
  let w (m : ℤ) := mapScalarToFock (derivative (integratedNormalMode m))
  let V := diagonalRetainedMode a b h p P
  have hs := diagonalRetainedMode_finite a b h p P
  let F := hs.toFinset
  have hsupport (m : ℤ) (hm : m ∉ F) : V m = 0 := by
    by_contra hn
    exact hm (hs.mem_toFinset.mpr hn)
  have hs' : Function.support (fun m => w m * V m) ⊆ (F : Set ℤ) := by
    intro m hm
    by_contra hn
    apply hm
    change w m * V m = 0
    rw [hsupport m hn, mul_zero]
  have hrs (r : Fin (n + 1)) : Function.support (fun m : ℤ =>
      ((((r.1 + 1 : ℕ) : ℂ) * coeff (r.1 + 1) (integratedNormalMode m)) •
        coeff (n - r.1) (V m))) ⊆ (F : Set ℤ) := by
    intro m hm
    by_contra hn
    apply hm
    change _ • coeff (n - r.1) (V m) = 0
    rw [hsupport m hn, map_zero, smul_zero]
  have heq := congrArg (coeff n) (diagonalRetained_derivative a b h p P)
  change coeff n (derivative (diagonalRetained a b h p P)) = coeff n (∑ᶠ m, w m * V m) at heq
  rw [finsum_eq_finsetSum_of_support_subset _ hs', map_sum, PowerSeries.coeff_derivative] at heq
  have hcoeff (m : ℤ) : coeff n (w m * V m) =
      ∑ r : Fin (n + 1), ((((r.1 + 1 : ℕ) : ℂ) * coeff (r.1 + 1) (integratedNormalMode m)) •
          coeff (n - r.1) (V m)) := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      ← Fin.sum_univ_eq_sum_range]
    simp only [w, mapScalarToFock, PowerSeries.coeff_map, PowerSeries.coeff_derivative,
      Algebra.smul_def, map_mul, Nat.cast_succ, mul_comm]
  simp_rw [hcoeff] at heq
  rw [Finset.sum_comm] at heq
  change _ = ∑ r : Fin (n + 1), ∑ᶠ m : ℤ,
    ((((r.1 + 1 : ℕ) : ℂ) * coeff (r.1 + 1) (integratedNormalMode m)) •
      coeff (n - r.1) (V m))
  calc
    _ = ∑ r : Fin (n + 1), ∑ m ∈ F,
        ((((r.1 + 1 : ℕ) : ℂ) * coeff (r.1 + 1) (integratedNormalMode m)) •
          coeff (n - r.1) (V m)) := by
      simpa only [Algebra.smul_def, map_natCast, Nat.cast_succ, map_add, map_one,
        mul_comm] using heq
    _ = _ := Finset.sum_congr rfl fun r _ =>
      (finsum_eq_finsetSum_of_support_subset _ (hrs r)).symm

/-- The actual retained sum at cutoff `D` matches the diagonal creation and
annihilation factors through every degree at most `D`. -/
theorem retainedCoefficient_eq_nativeDiagonal (D d : ℕ) (hd : d ≤ D)
    (a b : Charge lattice) (h : ℤ) (p : Momentum) (P : Fock) :
    retainedCoefficient D d a b h p P = coeff d
      (Cₜ (algebraMap ℂ Fock (chargePhase (a + b) p)) *
        mapScalarToFock ((PowerSeries.exp ℂ).subst (PowerSeries.C
          ((bilinear lattice a p.1 : ℂ) / 3) * PowerSeries.log ℂ)) *
        ((H (E a b)) * inverseCover ℂ (A a b P)).coeff (h - momentumExponent (a + b) p)) := by
  change retainedCoefficient D d a b h p P = coeff d (diagonalRetained a b h p P)
  induction d using Nat.strong_induction_on generalizing h P with
  | h d ih =>
    cases d with
    | zero => exact diagonalRetained_initial D a b h p P
    | succ n =>
      have hn : n < D := by omega
      apply smul_right_injective Fock
        (show ((n + 1 : ℕ) : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n)
      change ((n + 1 : ℕ) : ℂ) • retainedCoefficient D (n + 1) a b h p P =
        ((n + 1 : ℕ) : ℂ) • coeff (n + 1) (diagonalRetained a b h p P)
      rw [retainedCoefficient_recurrence D n hn, diagonalRetained_recurrence]
      apply Finset.sum_congr rfl
      intro r _
      apply finsum_congr
      intro m
      congr 1
      have hlt : n - r.val < n + 1 := by omega
      have hle : n - r.val ≤ D := by omega
      rw [diagonalRetainedMode_coeff]
      cases m with
      | negSucc s =>
        change creationPolynomial fixedDualBases a s * retainedCoefficient D (n - r.val)
          a b (h + Int.negSucc s) p P = _
        rw [ih _ hlt hle]
      | ofNat t =>
        cases t with
        | zero =>
          change ((bilinear lattice a p.1 : ℂ) / 3) •
            retainedCoefficient D (n - r.val) a b h p P =
            zeroEigenvalue a p • coeff (n - r.val) (diagonalRetained a b h p P)
          rw [zeroEigenvalue, ih _ hlt hle]
        | succ s =>
          change retainedCoefficient D (n - r.val) a b (h + Int.ofNat (s + 1)) p
            (positiveAnnihilator fixedDualBases a s P) = _
          rw [ih _ hlt hle]

#print axioms diagonalRetained_recurrence
#print axioms retainedCoefficient_eq_nativeDiagonal

open private formalExp formalExp_add map_exp_subst from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedExponentialReordering

private theorem readout_C_mul (z : R) (S : PowerSeries R) (Q : Polynomial R) (k : ℤ) :
    readout (PowerSeries.C z * S) Q k = z * readout S Q k := by
  rw [readout, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, mul_assoc,
    HahnSeries.coeff_single_zero_mul, readout]

/-- After the collision power and total momentum monomial are removed, every
native diagonal coefficient agrees with the Wick-expanded iterate with its cocycle. -/
theorem chargedDiagonalRegular_coeff_eq_nativeIterate (a b : Charge lattice) (h : ℤ)
    (p : Momentum) (P : Fock) (d : ℕ) :
    coeff d ((chargedDiagonalRegular fixedDualBases a b p P).coeff
      (h - momentumExponent (a + b) p)) =
      epsilon lattice a b •
        (HVertexOperator.coeff (P48qAllJetWickField.nativePolynomialField (a + b)
          (coeff d (LatticeGeneratingFieldLocality.creationExponential lattice a)))
          (h - 3 * (d : ℤ)) (Finsupp.single p P)) (shift (a + b) p) := by
  let K := integratedJetMean a (a + b) + (1 / 2 : ℂ) • integratedJetPair a
  let W := (PowerSeries.exp Fock).subst (mapScalarToFock K)
  let Z := PowerSeries.C (zeroEigenvalue a p) * PowerSeries.log ℂ
  have hZ : constantCoeff Z = 0 := by simp [Z]
  have hK : constantCoeff K = 0 := by
    simp [K, integratedJetMean, integratedJetPair]
  have hlog : chargedIterateLog a b p = Z + K := by
    rw [chargedIterateLog_eq_jetKernels]
    simp only [Z, K, zeroEigenvalue, PowerSeries.smul_eq_C_mul, add_assoc]
  have hexp : mapScalarToFock (groundDiagonalScalar a b p) =
      Cₜ (algebraMap ℂ Fock (epsilon lattice a b * chargePhase (a + b) p)) *
        momentumFactor a p * W := by
    have ha : (PowerSeries.exp ℂ).subst (Z + K) =
        (PowerSeries.exp ℂ).subst Z * (PowerSeries.exp ℂ).subst K := formalExp_add hZ hK
    rw [groundDiagonalScalar_eq_exp, hlog, ha, map_mul mapScalarToFock,
      map_mul mapScalarToFock]
    have hc (c : ℂ) : mapScalarToFock (PowerSeries.C c) = Cₜ (algebraMap ℂ Fock c) :=
      PowerSeries.map_C _ _
    rw [hc, ← mul_assoc]
    change _ = _ * mapScalarToFock ((PowerSeries.exp ℂ).subst Z) * W
    rw [show mapScalarToFock ((PowerSeries.exp ℂ).subst K) = W from
      map_exp_subst (algebraMap ℂ Fock) K hK]
  have hdiag : (chargedDiagonalRegular fixedDualBases a b p P).coeff
      (h - momentumExponent (a + b) p) =
        Cₜ (algebraMap ℂ Fock (epsilon lattice a b)) * (W * diagonalRetained a b h p P) := by
    change readout (groundDiagonalRegular fixedDualBases a b p) (A a b P)
      (h - momentumExponent (a + b) p) = _
    rw [show groundDiagonalRegular fixedDualBases a b p =
      PowerSeries.C (mapScalarToFock (groundDiagonalScalar a b p)) * E a b by
        simp only [groundDiagonalRegular, nativeDiagonalCreationExponential, mul_assoc],
      readout_C_mul, hexp, map_mul, map_mul, diagonalRetained]
    ring
  rw [hdiag, PowerSeries.coeff_C_mul, ← Algebra.smul_def,
    P48qNativeChargedWickFactorization.nativePolynomialField_coeff_eq_integrated_wick_factorization]
  congr 1
  have hcoeff (n : ℕ) (hn : n ≤ d) : coeff n (nativeRetainedSeries a b h p P d) =
      coeff n (diagonalRetained a b h p P) := retainedCoefficient_eq_nativeDiagonal d n hn a b h p P
  change coeff d (W * diagonalRetained a b h p P) = coeff d (W * nativeRetainedSeries a b h p P d)
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [hcoeff ij.2 (by have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hij; omega)]

#print axioms chargedDiagonalRegular_coeff_eq_nativeIterate

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
