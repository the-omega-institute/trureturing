/- GID: D5/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod
   generality: G
   mirror-B: D5/B/S1/Recurrence/Periodic/AutonomousDerivationTotientSquarePeriod
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Autonomous integral derivations yield prescribed totient-square tail periods. -/
/-
admission_basis: escape-witness
escape_witness: BalaTruncated.integer_matrix_totient_square
Escape audit unfinished:
https://github.com/the-omega-institute/trureturing/issues/21972
Declaration names below are relative to this module.
BalaCharP.iterate_leibniz: proof_shape: content; consumer: BalaCharP.iterate_prime_leibniz
BalaCharP.iterate_prime_leibniz: proof_shape: content; consumer: BalaCharP.primeIterate
BalaCharP.primeIterate: proof_shape: bind-only; consumer: BalaCharP.primeIterate_apply
BalaCharP.primeIterate_apply: proof_shape: bind-only; consumer: BalaCharP.restricted_power_scalar
BalaCharP.restricted_power_scalar: proof_shape: content; consumer: BalaLocalPrime.jet_restricted_power
BalaJets.root_pow_zero: proof_shape: bind-only; consumer: BalaJets.jet_unit_of_constant_one
BalaJets.jet_derivation_stable: proof_shape: bind-only; consumer: BalaJets.existsJetDerivation
BalaJets.existsJetDerivation: proof_shape: bind-only; consumer: BalaJets.jetDerivation
BalaJets.jetDerivation: proof_shape: bind-only; consumer: BalaJets.jetDerivation_mk
BalaJets.jetDerivation_mk: proof_shape: bind-only; consumer: BalaJets.jetDerivation_root
BalaJets.jetDerivation_root: proof_shape: bind-only; consumer: BalaLocalPrime.jet_restricted_power
BalaJets.jet_derivation_ext: proof_shape: bind-only; consumer: BalaLocalPrime.jet_restricted_power
BalaJets.jet_unit_of_constant_one: proof_shape: bind-only; consumer: BalaLocalPrime.jet_restricted_power
BalaJets.polynomial_constant_of_derivative_zero: proof_shape: bind-only; consumer: BalaJets.jet_derivative_kernel
BalaJets.jet_derivative_kernel: proof_shape: bind-only; consumer: BalaLocalPrime.jet_restricted_power
BalaScalarAnnihilator.power_progression: proof_shape: bind-only; consumer: BalaScalarAnnihilator.local_annihilator
BalaScalarAnnihilator.local_annihilator: proof_shape: bind-only; consumer: BalaLocalPrime.jet_annihilator
BalaLocalPrime.jetNontrivial: proof_shape: bind-only; consumer: BalaLocalPrime.jetCharP
BalaLocalPrime.jetCharP: proof_shape: bind-only; consumer: BalaLocalPrime.jet_annihilator
BalaLocalPrime.jet_restricted_power: proof_shape: content; consumer: BalaLocalPrime.jet_annihilator
BalaLocalPrime.jet_annihilator: proof_shape: content; consumer: BalaLocalPrime.jet_annihilator_apply
BalaLocalPrime.jet_annihilator_apply: proof_shape: content; consumer: BalaLocalPrime.polynomial_annihilator_divisible
BalaLocalPrime.jet_iterate_mk: proof_shape: bind-only; consumer: BalaLocalPrime.polynomial_annihilator_divisible
BalaLocalPrime.polynomial_annihilator_divisible: proof_shape: content; consumer: BalaFiltration.filtration_annihilator
BalaFiltration.polynomialEndCharP: proof_shape: bind-only; consumer: BalaFiltration.prime_power_filtration_divisible
BalaFiltration.Q: proof_shape: bind-only; consumer: BalaFiltration.Q_apply
BalaFiltration.Q_apply: proof_shape: bind-only; consumer: BalaFiltration.Q_mul_of_derivation_zero
BalaFiltration.iterate_mul_of_derivation_zero: proof_shape: bind-only; consumer: BalaFiltration.Q_mul_of_derivation_zero
BalaFiltration.Q_mul_of_derivation_zero: proof_shape: bind-only; consumer: BalaFiltration.filtration_annihilator
BalaFiltration.derivation_X_multiple: proof_shape: bind-only; consumer: BalaFiltration.filtration_annihilator
BalaFiltration.filtration_annihilator: proof_shape: content; consumer: BalaFiltration.prime_power_filtration_divisible
BalaFiltration.characteristic_power_expansion: proof_shape: bind-only; consumer: BalaFiltration.prime_power_filtration_divisible
BalaFiltration.prime_power_filtration_divisible: proof_shape: content; consumer: BalaTruncated.jet_prime_power_annihilator
BalaOperator.commuting_prime_lift_step: proof_shape: bind-only; consumer: BalaOperator.commuting_prime_power_lift
BalaOperator.commuting_prime_power_lift: proof_shape: bind-only; consumer: BalaOperator.operator_lift
BalaOperator.operator_lift: proof_shape: bind-only; consumer: BalaMatrix.specified_shift_lift
BalaMatrix.scalar_dvd_iff: proof_shape: bind-only; consumer: BalaMatrix.scalar_dvd_of_mod_zero
BalaMatrix.scalar_dvd_of_mod_zero: proof_shape: bind-only; consumer: BalaMatrix.specified_shift_lift
BalaMatrix.specified_shift_lift: proof_shape: bind-only; consumer: BalaSecondOrderMatrix.integral_annihilator
BalaTruncated.encode_map: proof_shape: bind-only; consumer: BalaSecondOrderMatrix.secondOrderMatrix_natural
BalaTruncated.encode_decode_quotient: proof_shape: bind-only; consumer: BalaTruncated.jet_annihilator_of_matrix
BalaTruncated.intoJet: proof_shape: bind-only; consumer: BalaTruncated.intoJet_injective
BalaTruncated.intoJet_injective: proof_shape: bind-only; consumer: BalaTruncated.operator_prime_power_annihilator
BalaTruncated.truncation: proof_shape: bind-only; consumer: BalaLinearTruncation.decode_semiconj
BalaTruncated.operator_natural: proof_shape: bind-only; consumer: BalaTruncated.matrix_natural
BalaTruncated.matrix: proof_shape: bind-only; consumer: BalaSecondOrderMatrix.integral_annihilator
BalaTruncated.matrix_natural: proof_shape: bind-only; consumer: BalaTruncated.integer_matrix_totient_square
BalaTruncated.operator_semiconj: proof_shape: bind-only; consumer: BalaTruncated.jet_annihilator_of_matrix
BalaTruncated.jet_prime_power_annihilator: proof_shape: content; consumer: BalaTruncated.operator_prime_power_annihilator
BalaTruncated.operator_prime_power_annihilator: proof_shape: content; consumer: BalaTruncated.matrix_prime_power_annihilator
BalaTruncated.matrix_prime_power_annihilator: proof_shape: content; consumer: BalaSecondOrderMatrix.integral_annihilator
BalaTruncated.integer_matrix_totient_square: proof_shape: content; consumer: BalaTruncated.prime_power_derivative_congruence
BalaTruncated.derivation_map: proof_shape: bind-only; consumer: BalaTruncated.prime_power_derivative_congruence
BalaTruncated.jet_annihilator_of_matrix: proof_shape: bind-only; consumer: BalaTruncated.coeff_zero_annihilator_of_matrix
BalaTruncated.coeff_zero_annihilator_of_matrix: proof_shape: bind-only; consumer: BalaTruncated.prime_power_derivative_congruence
BalaTruncated.prime_power_derivative_congruence: proof_shape: content; consumer: BalaTruncated.prime_power_derivative_period
BalaTruncated.prime_power_derivative_period: proof_shape: content; consumer: BalaA281180TotientSquarePeriod.prime_power_period
BalaOddPrimeRoot.unipotent_power: proof_shape: bind-only; consumer: BalaOddPrimeRoot.square_root_in_finite_jet
BalaOddPrimeRoot.square_root_in_finite_jet: proof_shape: bind-only; consumer: BalaA281181TotientSquarePeriod.BalaOddBranch.exists_odd_branch
BalaLinearTruncation.decode_zero_iff: proof_shape: bind-only; consumer: BalaLinearTruncation.decode_semiconj
BalaLinearTruncation.decode_semiconj: proof_shape: bind-only; consumer: BalaA281181TotientSquarePeriod.BalaLinearTruncation.coeff_zero_annihilator
BalaLinearTruncation.secondOrder: proof_shape: bind-only; consumer: BalaLinearTruncation.secondOrder_apply
BalaLinearTruncation.secondOrder_apply: proof_shape: bind-only; consumer: BalaLinearTruncation.secondOrder_mod_two
BalaLinearTruncation.derivative_stable: proof_shape: bind-only; consumer: BalaLinearTruncation.secondOrder_stable
BalaLinearTruncation.secondOrder_stable: proof_shape: bind-only; consumer: BalaA281181TotientSquarePeriod.BalaSecondOrderMatrix.two_power_annihilator_congruence
BalaLinearTruncation.secondOrder_mod_two: proof_shape: bind-only; consumer: BalaSecondOrderMatrix.matrix_mod_two
BalaSecondOrderMatrix.secondOrderMatrix: proof_shape: bind-only; consumer: BalaSecondOrderMatrix.integral_annihilator
BalaSecondOrderMatrix.secondOrderMatrix_natural: proof_shape: bind-only; consumer: BalaSecondOrderMatrix.integral_annihilator
BalaSecondOrderMatrix.matrix_mod_two: proof_shape: bind-only; consumer: BalaSecondOrderMatrix.integral_annihilator
BalaSecondOrderMatrix.integral_annihilator: proof_shape: content; consumer: BalaA281181TotientSquarePeriod.BalaSecondOrderMatrix.two_power_annihilator_congruence
-/

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.NormNum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Tactic.Linarith
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.NumberTheory.Basic

namespace D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod
open scoped Classical

open Finset
namespace BalaCharP
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
theorem iterate_leibniz [Module R A] (d : Derivation R A A) (n : ℕ) (f g : A) :
    d^[n] (f*g) = ∑ k ∈ range (n+1), n.choose k • (d^[n-k] f * d^[k] g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      d^[n+1] (f*g) = d (∑ k ∈ range (n+1), n.choose k • (d^[n-k] f*d^[k] g)) := by
        rw [Function.iterate_succ_apply', ih]
      _ = (∑ k ∈ range (n+1), n.choose k • (d^[n-k+1] f*d^[k] g)) +
          ∑ k ∈ range (n+1), n.choose k • (d^[n-k] f*d^[k+1] g) := by
        simp only [map_sum, map_nsmul, Derivation.leibniz, smul_eq_mul,
          Function.iterate_succ_apply', nsmul_add, sum_add_distrib]
        simp only [mul_comm, add_comm]
      _ = (∑ k ∈ range (n+1), n.choose (k+1) • (d^[n-k] f*d^[k+1] g)) +
          1 • (d^[n+1] f*d^[0] g) +
          ∑ k ∈ range (n+1), n.choose k • (d^[n-k] f*d^[k+1] g) := by
        congr 1
        refine (sum_range_succ' _ _).trans (congrArg₂ (·+·) ?_ ?_)
        · rw [sum_range_succ, Nat.choose_succ_self, zero_smul, add_zero]
          apply sum_congr rfl
          intro k hk
          rw [mem_range] at hk
          rw [show n - (k+1)+1 = n-k by omega]
        · rw [Nat.choose_zero_right, Nat.sub_zero]
      _ = ((∑ k ∈ range (n+1), n.choose k • (d^[n-k] f*d^[k+1] g)) +
          ∑ k ∈ range (n+1), n.choose (k+1) • (d^[n-k] f*d^[k+1] g)) +
          1 • (d^[n+1] f*d^[0] g) := by abel
      _ = (∑ k ∈ range (n+1), (n+1).choose (k+1) •
          (d^[n+1-(k+1)] f*d^[k+1] g)) + 1 • (d^[n+1] f*d^[0] g) := by
        simp_rw [Nat.choose_succ_succ, Nat.add_sub_add_right, add_smul, sum_add_distrib]
      _ = ∑ k ∈ range (n+1+1), (n+1).choose k •
          (d^[n+1-k] f*d^[k] g) := by
        rw [sum_range_succ' _ (n+1), Nat.choose_zero_right, Nat.sub_zero]
private theorem iterate_prime_leibniz {p : ℕ} [CharP A p] (hp : p.Prime)
    (d : Derivation R A A) (f g : A) :
    d^[p] (f*g) = d^[p] f * g + f * d^[p] g := by
  rw [iterate_leibniz, sum_range_succ]
  have hmid : (∑ k ∈ range p, p.choose k • (d^[p-k] f*d^[k] g)) = d^[p] f*g := by
    rw [sum_eq_single 0]
    · simp
    · intro k hk hk0
      have hz : (p.choose k : A) = 0 :=
        (CharP.cast_eq_zero_iff A p _).mpr (hp.dvd_choose_self hk0 (mem_range.mp hk))
      simp [nsmul_eq_mul,hz]
    · simp [hp.pos]
  rw [hmid]
  simp
private noncomputable def primeIterate {p : ℕ} [CharP A p] (hp : p.Prime)
    (d : Derivation R A A) : Derivation R A A where
  toLinearMap := d.toLinearMap ^ p
  map_one_eq_zero' := by
    simp only [Module.End.pow_apply, Derivation.coeFn_coe]
    change d^[p] 1 = 0
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
    rw [hm, Function.iterate_succ_apply, Derivation.map_one_eq_zero]
    simp only [iterate_map_zero]
  leibniz' f g := by
    simp only [Module.End.pow_apply, Derivation.coeFn_coe]
    change d^[p] (f*g) = _
    rw [iterate_prime_leibniz hp]
    simp [smul_eq_mul,add_comm,mul_comm]
private theorem primeIterate_apply {p : ℕ} [CharP A p] (hp : p.Prime)
    (d : Derivation R A A) (f : A) : primeIterate hp d f = d^[p] f := by
  exact Module.End.pow_apply d.toLinearMap p f
private theorem restricted_power_scalar {p : ℕ} [CharP A p] (hp : p.Prime)
    (y : A) (d d0 : Derivation R A A)
    (hext : ∀ d e : Derivation R A A, d y = e y → d = e)
    (hd0 : d0 y = 1)
    (hker : ∀ f : A, d0 f = 0 → ∃ a : R, f = algebraMap R A a)
    (hu : IsUnit (d y)) :
    ∃ a : R, primeIterate hp d = a • d := by
  obtain ⟨u,hu⟩ := hu
  let e := primeIterate hp d
  let B : A := (↑u⁻¹ : A) * e y
  have he : e = B • d := by
    apply hext
    simp [B,Derivation.smul_apply,smul_eq_mul,←hu,mul_comm,mul_left_comm]
  have hd : d = d y • d0 := by
    apply hext
    simp [Derivation.smul_apply,hd0,smul_eq_mul]
  have hcomm : d (e y) = e (d y) := by
    dsimp [e]
    rw [primeIterate_apply,primeIterate_apply]
    exact (Function.iterate_succ_apply' (⇑d) p y).symm.trans
      (Function.iterate_succ_apply (⇑d) p y)
  have hB : d B = 0 := by
    rw [he,Derivation.smul_apply,Derivation.smul_apply,smul_eq_mul,
      smul_eq_mul,Derivation.leibniz,smul_eq_mul,smul_eq_mul] at hcomm
    have hz : d y * d B = 0 := add_eq_left.mp hcomm
    apply u.isUnit.mul_left_cancel
    simpa [hu] using hz
  have hB0 : d0 B = 0 := by
    have hz : d y * d0 B = 0 := by
      have hh := congrArg (fun D : Derivation R A A => D B) hd
      simpa only [hB,Derivation.smul_apply,smul_eq_mul] using hh.symm
    apply u.isUnit.mul_left_cancel
    simpa [hu] using hz
  obtain ⟨a,ha⟩ := hker B hB0
  refine ⟨a, ?_⟩
  rw [show primeIterate hp d = e by rfl,he,ha]
  ext f
  simp [Derivation.smul_apply,Algebra.smul_def]
end BalaCharP
open Polynomial
namespace BalaJets
noncomputable section
variable {R : Type*} [CommRing R]
theorem root_pow_zero (L : ℕ) : (AdjoinRoot.root (X^L : Polynomial R))^L = 0 := by
  rw [← AdjoinRoot.mk_X, ← map_pow]
  exact AdjoinRoot.mk_self
private theorem jet_derivation_stable (L : ℕ) (hL : (L:R) = 0) (P f : Polynomial R)
    (hf : AdjoinRoot.mk (X^L : Polynomial R) f = 0) :
    AdjoinRoot.mk (X^L : Polynomial R) (Polynomial.mkDerivation R P f) = 0 := by
  apply AdjoinRoot.mk_eq_zero.mpr
  obtain ⟨g,rfl⟩ := AdjoinRoot.mk_eq_zero.mp hf
  simp only [Polynomial.mkDerivation_apply, smul_eq_mul, derivative_mul,
    derivative_X_pow, hL, C_0, zero_mul, zero_add]
  exact dvd_mul_right _ _ |>.mul_right _
theorem existsJetDerivation (L : ℕ) (hL : (L:R) = 0) (P : Polynomial R) :
    ∃ d : Derivation R (AdjoinRoot (X^L : Polynomial R)) (AdjoinRoot (X^L : Polynomial R)),
      ∀ f : Polynomial R, d (AdjoinRoot.mk (X^L : Polynomial R) f) =
        AdjoinRoot.mk (X^L : Polynomial R) (f.derivative * P) := by
  refine ⟨Derivation.liftOfSurjective (f := AdjoinRoot.mkₐ (X^L : Polynomial R))
    AdjoinRoot.mk_surjective (jet_derivation_stable L hL P), ?_⟩
  intro f
  exact Derivation.liftOfSurjective_apply
    (f := AdjoinRoot.mkₐ (X^L : Polynomial R)) AdjoinRoot.mk_surjective
    (jet_derivation_stable L hL P) f
noncomputable def jetDerivation (L : ℕ) (hL : (L:R) = 0) (P : Polynomial R) :
    Derivation R (AdjoinRoot (Polynomial.X ^ L : Polynomial R)) (AdjoinRoot (Polynomial.X ^ L : Polynomial R)) :=
  Classical.choose (existsJetDerivation L hL P)
private theorem jetDerivation_mk (L : ℕ) (hL : (L:R) = 0) (P f : Polynomial R) :
    jetDerivation L hL P (AdjoinRoot.mk (X^L : Polynomial R) f) =
      AdjoinRoot.mk (X^L : Polynomial R) (f.derivative * P) := by
  exact Classical.choose_spec (existsJetDerivation L hL P) f
theorem jetDerivation_root (L : ℕ) (hL : (L:R) = 0) (P : Polynomial R) :
    jetDerivation L hL P (AdjoinRoot.root (X^L : Polynomial R)) =
      AdjoinRoot.mk (X^L : Polynomial R) P := by
  rw [← AdjoinRoot.mk_X, jetDerivation_mk, derivative_X, one_mul]
private theorem jet_derivation_ext (L : ℕ)
    {d e : Derivation R (AdjoinRoot (Polynomial.X ^ L : Polynomial R)) (AdjoinRoot (Polynomial.X ^ L : Polynomial R))}
    (h : d (AdjoinRoot.root (X^L : Polynomial R)) = e (AdjoinRoot.root (X^L : Polynomial R))) :
    d = e := by
  exact Derivation.ext_of_adjoin_eq_top _ AdjoinRoot.adjoinRoot_eq_top (Set.eqOn_singleton.2 h)
private theorem jet_unit_of_constant_one (L : ℕ) (P : Polynomial R) (hP : P.coeff 0 = 1) :
    IsUnit (AdjoinRoot.mk (X^L : Polynomial R) P) := by
  have hd : (X : Polynomial R) ∣ P-1 := by
    rw [X_dvd_iff]
    simp [hP]
  obtain ⟨Q,hQ⟩ := hd
  have he : AdjoinRoot.mk (X^L : Polynomial R) P =
      1 + AdjoinRoot.root (X^L : Polynomial R) * AdjoinRoot.mk (X^L : Polynomial R) Q := by
    have h := congrArg (AdjoinRoot.mk (X^L : Polynomial R)) hQ
    simpa [map_sub, map_mul, AdjoinRoot.mk_X, sub_eq_iff_eq_add, add_comm] using h
  rw [he]
  apply IsNilpotent.isUnit_one_add
  refine ⟨L, ?_⟩
  rw [mul_pow, root_pow_zero, zero_mul]
section CharP
variable [IsDomain R] {p : ℕ} [CharP R p]
private theorem polynomial_constant_of_derivative_zero (hp : p.Prime) (f : Polynomial R)
    (hdeg : f.natDegree < p) (hd : f.derivative = 0) : f = C (f.coeff 0) := by
  have he := Polynomial.expand_contract p hd hp.ne_zero
  have hmul : (contract p f).natDegree * p < p := by
    rw [← Polynomial.natDegree_expand, he]
    exact hdeg
  have hc0 : (contract p f).natDegree = 0 := by
    by_contra hn
    have hle : p ≤ (contract p f).natDegree * p := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right p (Nat.one_le_iff_ne_zero.mpr hn)
    omega
  calc
    f = expand R p (contract p f) := he.symm
    _ = expand R p (C ((contract p f).coeff 0)) :=
      congrArg (expand R p) (eq_C_of_natDegree_eq_zero hc0)
    _ = C (f.coeff 0) := by simp [coeff_contract hp.ne_zero]

private theorem jet_derivative_kernel (hp : p.Prime) (f : AdjoinRoot (Polynomial.X ^ p : Polynomial R))
    (hf : jetDerivation p (CharP.cast_eq_zero R p) 1 f = 0) :
    ∃ a : R, f = algebraMap R (AdjoinRoot (Polynomial.X ^ p : Polynomial R)) a := by
  let g := AdjoinRoot.modByMonicHom (monic_X_pow p : (X^p : Polynomial R).Monic) f
  have hmk : AdjoinRoot.mk (X^p : Polynomial R) g = f := AdjoinRoot.mk_leftInverse _ f
  have hdeg : g.natDegree < p := by
    obtain ⟨g0,hg0⟩ := AdjoinRoot.mk_surjective f
    dsimp [g]
    rw [← hg0, AdjoinRoot.modByMonicHom_mk]
    simpa using natDegree_modByMonic_lt g0 (monic_X_pow p)
      (by
        intro he
        have hh := congrArg natDegree he
        simp only [natDegree_X_pow,natDegree_one] at hh
        exact hp.ne_zero hh)
  have hd0 : AdjoinRoot.mk (X^p : Polynomial R) g.derivative = 0 := by
    have h := jetDerivation_mk p (CharP.cast_eq_zero R p) (1 : Polynomial R) g
    rw [hmk, hf, mul_one] at h
    exact h.symm
  have hd : g.derivative = 0 := by
    by_contra hn
    exact AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_X_pow p) hn
      (by simpa using lt_of_le_of_lt ((natDegree_derivative_le g).trans (Nat.sub_le _ _)) hdeg) hd0
  refine ⟨g.coeff 0, ?_⟩
  rw [← hmk, polynomial_constant_of_derivative_zero hp g hdeg hd]
  simp only [coeff_C,ite_true]
  rfl
end CharP
end
end BalaJets
namespace BalaScalarAnnihilator
variable {R : Type*} [Ring R] {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) R]
private theorem power_progression (A : R) (c : ZMod p)
    (h : A^p = c • A) (j : ℕ) :
    A^(1+j*(p-1)) = c^j • A := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  induction j with
  | zero => simp
  | succ j ih =>
    have he : 1+(j+1)*(p-1) = (1+j*(p-1))+(p-1) := by rw [Nat.add_mul,one_mul]; omega
    rw [he,pow_add,ih,smul_mul_assoc,← pow_succ',Nat.sub_add_cancel hp,h,smul_smul,←pow_succ]
private theorem local_annihilator (A : R) (c : ZMod p) (h : A^p = c • A) :
    A^p * (A^((p-1)^2)-1) = 0 := by
  by_cases hc : c=0
  · simp [h,hc]
  · have hperiod : A^((p-1)^2+1) = A := by
      have hh := power_progression A c h (p-1)
      simpa [pow_two, Nat.add_comm, ZMod.pow_card_sub_one_eq_one hc] using hh
    have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
    calc
      A^p * (A^((p-1)^2)-1) = A^(p-1)*(A^((p-1)^2+1)-A) := by
        simp only [mul_sub,mul_one,←pow_add]
        rw [show p+((p-1)^2) = (p-1)+((p-1)^2+1) by omega,
          ← pow_succ,show (p-1)+1=p by omega]
      _ = 0 := by rw [hperiod,sub_self,mul_zero]
end BalaScalarAnnihilator
namespace BalaLocalPrime
open Polynomial BalaCharP BalaJets BalaScalarAnnihilator
noncomputable section
variable {p : ℕ} [Fact p.Prime]
private local instance jetNontrivial : Nontrivial (AdjoinRoot (Polynomial.X ^ p : Polynomial (ZMod p))) :=
  AdjoinRoot.nontrivial (X^p : Polynomial (ZMod p)) (by simpa using (Fact.out : p.Prime).ne_zero)
private local instance jetCharP : CharP (AdjoinRoot (Polynomial.X ^ p : Polynomial (ZMod p))) p :=
  CharP.of_ringHom_of_ne_zero (algebraMap (ZMod p) (AdjoinRoot (Polynomial.X ^ p : Polynomial (ZMod p)))) p
    (Fact.out : p.Prime).ne_zero
private theorem jet_restricted_power (P : Polynomial (ZMod p)) (hP : P.coeff 0 = 1) :
    ∃ a : ZMod p,
      primeIterate (Fact.out : p.Prime) (jetDerivation p (CharP.cast_eq_zero (ZMod p) p) P) =
        a • jetDerivation p (CharP.cast_eq_zero (ZMod p) p) P := by
  apply restricted_power_scalar (Fact.out : p.Prime)
    (AdjoinRoot.root (X^p : Polynomial (ZMod p))) _
    (jetDerivation p (CharP.cast_eq_zero (ZMod p) p) 1)
  · intro d e h
    exact jet_derivation_ext p h
  · rw [jetDerivation_root,map_one]
  · intro f hf
    exact jet_derivative_kernel (Fact.out : p.Prime) f hf
  · rw [jetDerivation_root]
    exact jet_unit_of_constant_one p P hP
private theorem jet_annihilator (P : Polynomial (ZMod p)) (hP : P.coeff 0 = 1) :
    let D := (jetDerivation p (CharP.cast_eq_zero (ZMod p) p) P).toLinearMap
    D^p * (D^((p-1)^2)-1) = 0 := by
  dsimp only
  obtain ⟨a,ha⟩ := jet_restricted_power P hP
  apply local_annihilator _ a
  have hh := congrArg Derivation.toLinearMap ha
  exact hh
private theorem jet_annihilator_apply (P : Polynomial (ZMod p)) (hP : P.coeff 0 = 1)
    (f : AdjoinRoot (Polynomial.X ^ p : Polynomial (ZMod p))) :
    let D := jetDerivation p (CharP.cast_eq_zero (ZMod p) p) P
    D^[p] (D^[((p-1)^2)] f-f) = 0 := by
  have hh := congrArg (fun D : Module.End (ZMod p) (AdjoinRoot (Polynomial.X ^ p : Polynomial (ZMod p))) => D f)
    (jet_annihilator P hP)
  simpa only [Module.End.mul_apply,Module.End.pow_apply,LinearMap.sub_apply,
    Module.End.one_apply,LinearMap.zero_apply,Derivation.coeFn_coe] using hh
private theorem jet_iterate_mk {R : Type*} [CommRing R] (L : ℕ) (hL : (L:R)=0)
    (P f : Polynomial R) (n : ℕ) :
    (jetDerivation L hL P)^[n] (AdjoinRoot.mk (X^L : Polynomial R) f) =
      AdjoinRoot.mk (X^L : Polynomial R) ((Polynomial.mkDerivation R P)^[n] f) := by
  have hs : Function.Semiconj (AdjoinRoot.mk (X^L : Polynomial R))
      (Polynomial.mkDerivation R P) (jetDerivation L hL P) := by
    intro g
    exact (jetDerivation_mk L hL P g).symm
  exact (hs.iterate_right n f).symm
private theorem polynomial_annihilator_divisible (P : Polynomial (ZMod p))
    (hP : P.coeff 0 = 1) (f : Polynomial (ZMod p)) :
    (X : Polynomial (ZMod p))^p ∣
      (Polynomial.mkDerivation (ZMod p) P)^[p]
        ((Polynomial.mkDerivation (ZMod p) P)^[((p-1)^2)] f-f) := by
  apply AdjoinRoot.mk_eq_zero.mp
  rw [← jet_iterate_mk p (CharP.cast_eq_zero (ZMod p) p),map_sub,
    ← jet_iterate_mk p (CharP.cast_eq_zero (ZMod p) p)]
  exact jet_annihilator_apply P hP _
end
end BalaLocalPrime
namespace BalaFiltration
open Polynomial BalaLocalPrime
noncomputable section
variable {p : ℕ} [Fact p.Prime]
private local instance polynomialEndCharP :
    CharP (Module.End (ZMod p) (Polynomial (ZMod p))) p :=
  CharP.of_ringHom_of_ne_zero
    (algebraMap (ZMod p) (Module.End (ZMod p) (Polynomial (ZMod p)))) p
    (Fact.out : p.Prime).ne_zero
private def Q (D : Derivation (ZMod p) (Polynomial (ZMod p)) (Polynomial (ZMod p))) :
    Module.End (ZMod p) (Polynomial (ZMod p)) :=
  D.toLinearMap^p * (D.toLinearMap^((p-1)^2)-1)
private theorem Q_apply (D : Derivation (ZMod p) (Polynomial (ZMod p)) (Polynomial (ZMod p)))
    (f : Polynomial (ZMod p)) :
    Q D f = D^[p] (D^[((p-1)^2)] f-f) := by
  simp only [Q,Module.End.mul_apply,Module.End.pow_apply,LinearMap.sub_apply,
    Module.End.one_apply,Derivation.coeFn_coe]
private theorem iterate_mul_of_derivation_zero {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (D : Derivation R A A) (a f : A) (ha : D a = 0) (n : ℕ) :
    D^[n] (a*f) = a * D^[n] f := by
  have hs : Function.Semiconj (fun g : A => a*g) D D := by
    intro g
    simp [Derivation.leibniz, ha, smul_eq_mul]
  exact (hs.iterate_right n f).symm
private theorem Q_mul_of_derivation_zero
    (D : Derivation (ZMod p) (Polynomial (ZMod p)) (Polynomial (ZMod p)))
    (a f : Polynomial (ZMod p)) (ha : D a = 0) : Q D (a*f) = a*Q D f := by
  rw [Q_apply,Q_apply,iterate_mul_of_derivation_zero _ _ _ ha,←mul_sub,
    iterate_mul_of_derivation_zero _ _ _ ha]
private theorem derivation_X_multiple (P : Polynomial (ZMod p)) (j : ℕ) :
    Polynomial.mkDerivation (ZMod p) P (X^(p*j)) = 0 := by
  simp [Polynomial.mkDerivation_apply,derivative_X_pow,Nat.cast_mul,CharP.cast_eq_zero (ZMod p) p]
private theorem filtration_annihilator (P : Polynomial (ZMod p)) (hP : P.coeff 0 = 1)
    (f : Polynomial (ZMod p)) (h : ℕ) :
    (X : Polynomial (ZMod p))^(p*h) ∣
      (Q (Polynomial.mkDerivation (ZMod p) P))^[h] f := by
  induction h with
  | zero => simp
  | succ h ih =>
    obtain ⟨g,hg⟩ := ih
    obtain ⟨z,hz⟩ := polynomial_annihilator_divisible P hP g
    refine ⟨z, ?_⟩
    rw [Function.iterate_succ_apply',hg,Q_mul_of_derivation_zero _ _ _ (derivation_X_multiple P h),
      Q_apply,hz,←mul_assoc,←pow_add,Nat.mul_add,Nat.mul_one]
private theorem characteristic_power_expansion {R : Type*} [Ring R] [CharP R p]
    (A : R) (s : ℕ) :
    (A^p * (A^((p-1)^2)-1))^(p^s) =
      A^(p*p^s) * (A^(((p-1)^2)*p^s)-1) := by
  have hc : Commute (A^p) (A^((p-1)^2)-1) :=
    (Commute.pow_pow_self A _ _).sub_right (Commute.one_right _)
  rw [hc.mul_pow,←pow_mul,sub_pow_char_pow_of_commute p s (Commute.one_right _),one_pow,←pow_mul]
private theorem prime_power_filtration_divisible (P : Polynomial (ZMod p)) (hP : P.coeff 0 = 1)
    (f : Polynomial (ZMod p)) (s : ℕ) :
    let D : Module.End (ZMod p) (Polynomial (ZMod p)) :=
      (Polynomial.mkDerivation (ZMod p) P).toLinearMap
    (X : Polynomial (ZMod p))^(p^(s+1)) ∣
      ((D^(p^(s+1)) * (D^(((p-1)^2)*p^s)-1) : Module.End (ZMod p) (Polynomial (ZMod p))) f) := by
  dsimp only
  have hh := filtration_annihilator P hP f (p^s)
  rw [← Module.End.pow_apply] at hh
  rw [Q,characteristic_power_expansion,←pow_succ'] at hh
  exact hh
end
end BalaFiltration
namespace BalaOperator
variable {R : Type*} [Ring R]
private theorem commuting_prime_lift_step {p s : ℕ} (hp : p.Prime) (hs : 1 ≤ s)
    {x y : R} (hxy : Commute x y) (h : (p : R) ^ s ∣ x - y) :
    (p : R) ^ (s + 1) ∣ x ^ p - y ^ p := by
  have hzy : Commute (x-y) y := hxy.sub_left (Commute.refl y)
  obtain ⟨b, hb⟩ := h
  obtain ⟨v, hv⟩ := hzy.exists_add_pow_prime_eq hp
  have he : x ^ p - y ^ p = (x-y) ^ p + (p : R) * (x-y) * y * v := by
    rw [sub_add_cancel] at hv
    rw [hv]
    abel
  rw [he]
  apply dvd_add
  · rw [hb, (Nat.cast_commute p b).pow_left s |>.mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_left (pow_dvd_pow (p : R) (by nlinarith [hp.two_le])) _
  · rw [hb, ← mul_assoc (p : R), ← pow_succ']
    exact dvd_mul_right _ _ |>.mul_right _ |>.mul_right _
private theorem commuting_prime_power_lift {p : ℕ} (hp : p.Prime) {x y : R}
    (hxy : Commute x y) (h : (p : R) ∣ x-y) (r : ℕ) :
    (p : R) ^ (r+1) ∣ x ^ (p ^ r) - y ^ (p ^ r) := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
    simpa [pow_succ, pow_mul] using
      commuting_prime_lift_step hp (by omega : 1 ≤ r+1) (hxy.pow_pow _ _) ih
private theorem operator_lift {p : ℕ} (hp : p.Prime) (A : R) (u t r : ℕ)
    (h : (p : R) ∣ A^u * (A^t-1)) :
    (p : R) ^ (r+1) ∣ A^(u*p^r) * (A^(t*p^r)-1) := by
  have he (n : ℕ) : (A^(u+t))^n - (A^u)^n = A^(u*n) * (A^(t*n)-1) := by
    rw [← pow_mul, ← pow_mul, add_mul, pow_add, mul_sub, mul_one]
  have hb : (p : R) ∣ A^(u+t) - A^u := by simpa [pow_add, mul_sub] using h
  simpa only [he] using commuting_prime_power_lift hp (Commute.pow_pow_self A _ _) hb r
end BalaOperator
namespace BalaMatrix
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem scalar_dvd_iff (p : ℕ) (C : Matrix ι ι ℤ) :
    (p : Matrix ι ι ℤ) ∣ C ↔ ∀ i j, (p : ℤ) ∣ C i j := by
  constructor
  · rintro ⟨B,hB⟩ i j
    refine ⟨B i j, ?_⟩
    rw [hB,←nsmul_eq_mul]
    simp only [Matrix.smul_apply,nsmul_eq_mul]
  · intro h
    classical
    choose B hB using h
    refine ⟨Matrix.of B, ?_⟩
    rw [←nsmul_eq_mul]
    ext i j
    exact hB i j
private theorem scalar_dvd_of_mod_zero (p : ℕ) (C : Matrix ι ι ℤ)
    (h : (Int.castRingHom (ZMod p)).mapMatrix C = 0) : (p : Matrix ι ι ℤ) ∣ C := by
  apply (scalar_dvd_iff p C).mpr
  intro i j
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (C i j) p).mp
  exact congrArg (fun M : Matrix ι ι (ZMod p) => M i j) h
private theorem specified_shift_lift {p : ℕ} (hp : p.Prime) (A : Matrix ι ι ℤ) (u t r : ℕ)
    (h : ((Int.castRingHom (ZMod p)).mapMatrix A)^u *
      (((Int.castRingHom (ZMod p)).mapMatrix A)^t-1) = 0) :
    (p : Matrix ι ι ℤ)^(r+1) ∣ A^(u*p^r)*(A^(t*p^r)-1) := by
  apply BalaOperator.operator_lift hp
  apply scalar_dvd_of_mod_zero
  simpa only [map_mul,map_pow,map_sub,map_one] using h
end BalaMatrix
namespace BalaTruncated
open Polynomial BalaJets
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]
private theorem encode_map (f : R →+* S) (L : ℕ) (v : Fin L → R) :
    ((Polynomial.ofFn L) v).map f = (Polynomial.ofFn L) (fun i => f (v i)) := by
  simp only [Polynomial.ofFn_eq_sum_monomial,Polynomial.map_sum,Polynomial.map_monomial]
private theorem encode_decode_quotient (L : ℕ) (f : Polynomial R) :
    AdjoinRoot.mk (X^L : Polynomial R) ((Polynomial.ofFn L) ((Polynomial.toFn L) f)) =
      AdjoinRoot.mk (X^L : Polynomial R) f := by
  apply AdjoinRoot.mk_eq_mk.mpr
  apply X_pow_dvd_iff.mpr
  intro n hn
  rw [coeff_sub,Polynomial.ofFn_coeff_eq_val_of_lt _ hn]
  simp [Polynomial.toFn]
private def intoJet (R : Type*) [CommRing R] (L : ℕ) : (Fin L → R) →ₗ[R] AdjoinRoot (Polynomial.X ^ L : Polynomial R) :=
  (AdjoinRoot.mkₐ (X^L : Polynomial R)).toLinearMap.comp ((Polynomial.ofFn L))
private theorem intoJet_injective (L : ℕ) : Function.Injective (intoJet R L) := by
  intro v w h
  have hd := X_pow_dvd_iff.mp (AdjoinRoot.mk_eq_mk.mp h)
  ext i
  have hi := hd i i.isLt
  rw [coeff_sub,Polynomial.ofFn_coeff_eq_val_of_lt _ i.isLt,
    Polynomial.ofFn_coeff_eq_val_of_lt _ i.isLt,sub_eq_zero] at hi
  exact hi
def truncation {R : Type*} [CommRing R] (L : ℕ)
    (F : Module.End R (Polynomial R)) : Module.End R (Fin L → R) :=
  ((Polynomial.toFn L)).comp (F.comp ((Polynomial.ofFn L)))
private theorem operator_natural (f : R →+* S) (L : ℕ) (P : Polynomial R) (v : Fin L → R) (i : Fin L) :
    f (truncation L (Polynomial.mkDerivation R P).toLinearMap v i) = truncation L (Polynomial.mkDerivation S (P.map f)).toLinearMap (fun j => f (v j)) i := by
  change f ((Polynomial.mkDerivation R P ((Polynomial.ofFn L) v)).coeff i) =
    (Polynomial.mkDerivation S (P.map f) ((Polynomial.ofFn L) (fun j => f (v j)))).coeff i
  rw [←coeff_map,Polynomial.mkDerivation_apply,smul_eq_mul,Polynomial.map_mul,
    ←derivative_map,encode_map,Polynomial.mkDerivation_apply,smul_eq_mul]
def matrix (R : Type*) [CommRing R] (L : ℕ) (P : Polynomial R) : Matrix (Fin L) (Fin L) R :=
  LinearMap.toMatrixAlgEquiv' (truncation L (Polynomial.mkDerivation R P).toLinearMap)
theorem matrix_natural (f : R →+* S) (L : ℕ) (P : Polynomial R) :
    f.mapMatrix (matrix R L P) = matrix S L (P.map f) := by
  ext i j
  simp only [matrix,RingHom.mapMatrix_apply,Matrix.map_apply,LinearMap.toMatrixAlgEquiv'_apply]
  change f (truncation L (Polynomial.mkDerivation R P).toLinearMap (Pi.single j 1) i) = truncation L (Polynomial.mkDerivation S (P.map f)).toLinearMap (Pi.single j 1) i
  rw [operator_natural]
  have hv : (fun k : Fin L => f ((Pi.single j (1:R) : Fin L → R) k)) = Pi.single j (1:S) := by
    ext k
    simp [Pi.single_apply]
  rw [hv]
private theorem operator_semiconj (L : ℕ) (hL : (L:R)=0) (P : Polynomial R) :
    Function.Semiconj (intoJet R L) (truncation L (Polynomial.mkDerivation R P).toLinearMap) (jetDerivation L hL P) := by
  intro v
  change AdjoinRoot.mk (X^L : Polynomial R)
      ((Polynomial.ofFn L) ((Polynomial.toFn L) (Polynomial.mkDerivation R P ((Polynomial.ofFn L) v)))) =
    jetDerivation L hL P (AdjoinRoot.mk (X^L : Polynomial R) ((Polynomial.ofFn L) v))
  rw [encode_decode_quotient,jetDerivation_mk]
  rfl
end
end BalaTruncated
namespace BalaTruncated
open Polynomial BalaJets BalaLocalPrime
noncomputable section
variable {p : ℕ} [Fact p.Prime]
private theorem jet_prime_power_annihilator (P : Polynomial (ZMod p)) (hP : P.coeff 0 = 1)
    (s : ℕ) (f : AdjoinRoot (Polynomial.X ^ (p^(s+1)) : Polynomial (ZMod p))) :
    let D := jetDerivation (p^(s+1)) (by simp [Nat.cast_pow]) P
    D^[p^(s+1)] (D^[((p-1)^2*p^s)] f-f) = 0 := by
  dsimp only
  obtain ⟨g,rfl⟩ := AdjoinRoot.mk_surjective f
  rw [jet_iterate_mk,←map_sub,jet_iterate_mk]
  apply AdjoinRoot.mk_eq_zero.mpr
  have hh := BalaFiltration.prime_power_filtration_divisible P hP g s
  simpa only [Module.End.mul_apply,Module.End.pow_apply,LinearMap.sub_apply,
    Module.End.one_apply,Derivation.coeFn_coe] using hh
private theorem operator_prime_power_annihilator (P : Polynomial (ZMod p)) (hP : P.coeff 0 = 1)
    (s : ℕ) :
    let D := truncation (p^(s+1)) (Polynomial.mkDerivation (ZMod p) P).toLinearMap
    D^(p^(s+1)) * (D^((p-1)^2*p^s)-1) = 0 := by
  dsimp only
  apply LinearMap.ext
  intro v
  apply intoJet_injective (p^(s+1))
  have hs := operator_semiconj (p^(s+1)) (by simp [Nat.cast_pow]) P
  simp only [Module.End.mul_apply,Module.End.pow_apply,LinearMap.sub_apply,
    Module.End.one_apply,LinearMap.zero_apply,map_zero]
  rw [hs.iterate_right (p^(s+1)),map_sub,hs.iterate_right ((p-1)^2*p^s)]
  exact jet_prime_power_annihilator P hP s _
private theorem matrix_prime_power_annihilator (P : Polynomial (ZMod p)) (hP : P.coeff 0 = 1)
    (s : ℕ) :
    let A := matrix (ZMod p) (p^(s+1)) P
    A^(p^(s+1)) * (A^((p-1)^2*p^s)-1) = 0 := by
  have hh := congrArg (LinearMap.toMatrixAlgEquiv' :
      Module.End (ZMod p) (Fin (p^(s+1)) → ZMod p) ≃ₐ[ZMod p]
        Matrix (Fin (p^(s+1))) (Fin (p^(s+1))) (ZMod p))
    (operator_prime_power_annihilator P hP s)
  simpa only [map_mul,map_pow,map_sub,map_one,map_zero,matrix] using hh
theorem integer_matrix_totient_square (P : Polynomial ℤ) (hP : P.coeff 0 = 1)
    (s : ℕ) :
    (p : Matrix (Fin (p^(s+1))) (Fin (p^(s+1))) ℤ)^(s+1) ∣
      (matrix ℤ (p^(s+1)) P)^(p^(2*s+1)) *
        ((matrix ℤ (p^(s+1)) P)^((Nat.totient (p^(s+1)))^2)-1) := by
  have hP' : (P.map (Int.castRingHom (ZMod p))).coeff 0 = 1 := by simp [hP]
  have hbase := matrix_prime_power_annihilator (P.map (Int.castRingHom (ZMod p))) hP' s
  rw [← matrix_natural] at hbase
  have hlift := BalaMatrix.specified_shift_lift (Fact.out : p.Prime)
    (matrix ℤ (p^(s+1)) P) (p^(s+1)) ((p-1)^2*p^s) s hbase
  have he : p^(s+1)*p^s = p^(2*s+1) := by rw [←pow_add]; congr 1; omega
  have ht : ((p-1)^2*p^s)*p^s = (Nat.totient (p^(s+1)))^2 := by
    rw [Nat.totient_prime_pow_succ (Fact.out : p.Prime)]
    ring
  simpa only [he,ht] using hlift
end
end BalaTruncated
namespace BalaTruncated
open Polynomial BalaJets BalaLocalPrime
noncomputable section
private theorem derivation_map {R S : Type*} [CommRing R] [CommRing S]
    (h : R →+* S) (P f : Polynomial R) (n : ℕ) :
    ((Polynomial.mkDerivation R P)^[n] f).map h =
      (Polynomial.mkDerivation S (P.map h))^[n] (f.map h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply',Polynomial.mkDerivation_apply,smul_eq_mul,
      Polynomial.map_mul,←Polynomial.derivative_map,ih]
theorem jet_annihilator_of_matrix {R : Type*} [CommRing R] (L : ℕ) (hL : (L:R)=0)
    (P : Polynomial R) (u t : ℕ)
    (hA : (matrix R L P)^u*((matrix R L P)^t-1)=0) (f : Polynomial R) :
    let d := jetDerivation L hL P
    d^[u] (d^[t] (AdjoinRoot.mk (X^L : Polynomial R) f) -
      AdjoinRoot.mk (X^L : Polynomial R) f) = 0 := by
  have hD : (truncation L (Polynomial.mkDerivation R P).toLinearMap)^u*((truncation L (Polynomial.mkDerivation R P).toLinearMap)^t-1)=0 := by
    apply (LinearMap.toMatrixAlgEquiv' :
      Module.End R (Fin L → R) ≃ₐ[R] Matrix (Fin L) (Fin L) R).injective
    simpa only [map_mul,map_pow,map_sub,map_one,map_zero,matrix] using hA
  have hv : intoJet R L ((Polynomial.toFn L) f) = AdjoinRoot.mk (X^L : Polynomial R) f :=
    encode_decode_quotient L f
  have hh := congrArg (fun F : Module.End R (Fin L → R) =>
    intoJet R L (F ((Polynomial.toFn L) f))) hD
  have hs := operator_semiconj L hL P
  simp only [Module.End.mul_apply,Module.End.pow_apply,LinearMap.sub_apply,
    Module.End.one_apply,LinearMap.zero_apply,map_zero] at hh
  rw [hs.iterate_right u,map_sub,hs.iterate_right t,hv] at hh
  exact hh
private theorem coeff_zero_annihilator_of_matrix {R : Type*} [CommRing R] (L : ℕ)
    (hL : (L:R)=0) (hpos : 0<L) (P : Polynomial R) (u t : ℕ)
    (hA : (matrix R L P)^u*((matrix R L P)^t-1)=0) (f : Polynomial R) :
    ((Polynomial.mkDerivation R P)^[u]
      ((Polynomial.mkDerivation R P)^[t] f-f)).coeff 0=0 := by
  have hh := jet_annihilator_of_matrix L hL P u t hA f
  dsimp only at hh
  rw [jet_iterate_mk,←map_sub,jet_iterate_mk] at hh
  exact X_pow_dvd_iff.mp (AdjoinRoot.mk_eq_zero.mp hh) 0 hpos
private theorem prime_power_derivative_congruence {p : ℕ} [Fact p.Prime]
    (P : Polynomial ℤ) (hP : P.coeff 0=1) (s : ℕ) (f : Polynomial ℤ) :
    Int.ModEq (p^(s+1) : ℤ)
      (((Polynomial.mkDerivation ℤ P)^[p^(2*s+1)]
        ((Polynomial.mkDerivation ℤ P)^[((Nat.totient (p^(s+1)))^2)] f-f)).coeff 0) 0 := by
  let L := p^(s+1)
  let cast := Int.castRingHom (ZMod L)
  have hd := integer_matrix_totient_square (p:=p) P hP s
  have hz : (cast.mapMatrix (matrix ℤ L P))^(p^(2*s+1))*
      ((cast.mapMatrix (matrix ℤ L P))^((Nat.totient L)^2)-1)=0 := by
    have hc : (p : Matrix (Fin L) (Fin L) ℤ)^(s+1) = (L : Matrix (Fin L) (Fin L) ℤ) := by
      simp [L]
    rw [hc] at hd
    obtain ⟨B,hB⟩ := hd
    have hh := congrArg cast.mapMatrix hB
    have hc0 : (L : Matrix (Fin L) (Fin L) (ZMod L))=0 := by
      ext i j
      simp [Matrix.natCast_apply]
    simpa only [map_mul,map_pow,map_sub,map_one,map_natCast,hc0,
      zero_mul] using hh
  rw [matrix_natural] at hz
  have hcoeff := coeff_zero_annihilator_of_matrix L (by simp [L])
    (pow_pos (Fact.out : p.Prime).pos _) (P.map cast) (p^(2*s+1))
    ((Nat.totient L)^2) hz (f.map cast)
  rw [←derivation_map,←Polynomial.map_sub,←derivation_map,Polynomial.coeff_map] at hcoeff
  apply Int.modEq_zero_iff_dvd.mpr
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ L).mp hcoeff
end
end BalaTruncated
namespace BalaTruncated
open Polynomial
noncomputable section
theorem prime_power_derivative_period {p : ℕ} [Fact p.Prime]
    (P : Polynomial ℤ) (hP : P.coeff 0=1) (s : ℕ) (f : Polynomial ℤ)
    (m : ℕ) (hm : p^(2*s+1) ≤ m) :
    Int.ModEq (p^(s+1) : ℤ)
      (((Polynomial.mkDerivation ℤ P)^[m+(Nat.totient (p^(s+1)))^2] f).coeff 0)
      (((Polynomial.mkDerivation ℤ P)^[m] f).coeff 0) := by
  let D := Polynomial.mkDerivation ℤ P
  let u := p^(2*s+1)
  let t := (Nat.totient (p^(s+1)))^2
  have hh := prime_power_derivative_congruence (p:=p) P hP s (D^[m-u] f)
  change Int.ModEq _ ((D^[u] (D^[t] (D^[m-u] f) - D^[m-u] f)).coeff 0) 0 at hh
  have hs (g h : Polynomial ℤ) : D^[u] (g-h)=D^[u] g-D^[u] h :=
    by simpa only [Module.End.pow_apply,Derivation.coeFn_coe] using
      map_sub (D.toLinearMap^u) g h
  rw [hs,Polynomial.coeff_sub,←Function.iterate_add_apply,
    ←Function.iterate_add_apply,←Function.iterate_add_apply] at hh
  have he : u+t+(m-u)=m+t := by dsimp [u] at *; omega
  have he' : u+(m-u)=m := by dsimp [u] at *; omega
  rw [he,he'] at hh
  simpa only [sub_add_cancel,zero_add] using hh.add_right ((D^[m] f).coeff 0)
end
end BalaTruncated
namespace BalaOddPrimeRoot
variable {R : Type*} [CommRing R]
private theorem unipotent_power {p : ℕ} (hp : p.Prime) (s : ℕ)
    (hchar : (p:R)^(s+1)=0) (x : R) (hx : x^(p^(s+1))=0) :
    (1+x)^(p^(2*s+1))=1 := by
  obtain ⟨b,hb⟩ := (Commute.one_left x).exists_add_pow_prime_pow_eq hp (s+1)
  have hd : (p:R) ∣ (1+x)^(p^(s+1))-1 := by
    rw [hb,hx,one_pow,add_zero,add_sub_cancel_left]
    exact dvd_mul_right _ _ |>.mul_right _ |>.mul_right _
  have hh := dvd_sub_pow_of_dvd_sub hd s
  obtain ⟨z,hz⟩ := hh
  rw [hchar,zero_mul,one_pow] at hz
  have he : (s+1)+s=2*s+1 := by omega
  rw [←pow_mul,←pow_add,he] at hz
  exact sub_eq_zero.mp hz
theorem square_root_in_finite_jet {p : ℕ} (hp : p.Prime) (hp2 : p≠2) (s : ℕ)
    (hchar : (p:R)^(s+1)=0) (x : R) (hx : x^(p^(s+1))=0) :
    ∃ b : R, b^2=1+x ∧ ∃ m : ℕ, b=(1+x)^m := by
  obtain ⟨j,hj⟩ := ((hp.odd_of_ne_two hp2).pow : Odd (p^(2*s+1)))
  refine ⟨(1+x)^(j+1),?_,j+1,rfl⟩
  rw [←pow_mul,show (j+1)*2=p^(2*s+1)+1 by omega,pow_succ,
    unipotent_power hp s hchar x hx,one_mul]
end BalaOddPrimeRoot
namespace BalaLinearTruncation
open Polynomial BalaTruncated
noncomputable section
variable {R : Type*} [CommRing R]
theorem decode_zero_iff (L : ℕ) (f : Polynomial R) :
    (Polynomial.toFn L) f=0 ↔ X^L ∣ f := by
  rw [X_pow_dvd_iff]
  constructor
  · intro h n hn
    exact congrFun h ⟨n,hn⟩
  · intro h
    ext i
    exact h i i.isLt
theorem decode_semiconj (L : ℕ) (F : Module.End R (Polynomial R))
    (hF : ∀ f : Polynomial R, X^L ∣ f → X^L ∣ F f) :
    Function.Semiconj ((Polynomial.toFn L)) F (truncation L F) := by
  intro f
  have hd : X^L ∣ f-(Polynomial.ofFn L) ((Polynomial.toFn L) f) := by
    apply X_pow_dvd_iff.mpr
    intro n hn
    rw [coeff_sub,Polynomial.ofFn_coeff_eq_val_of_lt _ hn]
    simp [Polynomial.toFn]
  have hz := (decode_zero_iff L _).mpr (hF _ hd)
  rw [map_sub,map_sub,sub_eq_zero] at hz
  exact hz
def secondOrder (a b : Polynomial R) : Module.End R (Polynomial R) :=
  (LinearMap.mulLeft R a).comp ((Polynomial.derivative : Module.End R (Polynomial R))^2) +
  (LinearMap.mulLeft R b).comp Polynomial.derivative
theorem secondOrder_apply (a b f : Polynomial R) :
    secondOrder a b f=a*f.derivative.derivative+b*f.derivative := by rfl
private theorem derivative_stable (L : ℕ) (hL : (L:R)=0) (f : Polynomial R)
    (hf : X^L ∣ f) : X^L ∣ f.derivative := by
  obtain ⟨g,rfl⟩ := hf
  rw [derivative_mul,derivative_X_pow,hL,C_0,zero_mul,zero_mul,zero_add]
  exact dvd_mul_right _ _
theorem secondOrder_stable (L : ℕ) (hL : (L:R)=0) (a b f : Polynomial R)
    (hf : X^L ∣ f) : X^L ∣ secondOrder a b f := by
  rw [secondOrder_apply]
  exact dvd_add ((derivative_stable L hL _ (derivative_stable L hL f hf)).mul_left a)
    ((derivative_stable L hL f hf).mul_left b)
private theorem secondOrder_mod_two (a b f : Polynomial (ZMod 2)) :
    secondOrder a b f = Polynomial.mkDerivation (ZMod 2) b f := by
  have hh := Polynomial.iterate_derivative_eq_factorial_smul_sum f 2
  have hz : f.derivative.derivative=0 := by
    simpa only [Function.iterate_succ_apply',Function.iterate_zero_apply,
      Nat.factorial_succ,Nat.factorial_zero,one_mul,nsmul_eq_mul,
      Nat.cast_ofNat,CharP.cast_eq_zero,zero_mul] using hh
  simp only [secondOrder_apply,hz,mul_zero,zero_add,
    Polynomial.mkDerivation_apply,smul_eq_mul,mul_comm]
end
end BalaLinearTruncation
namespace BalaSecondOrderMatrix
open Polynomial BalaTruncated BalaLinearTruncation
noncomputable section
def secondOrderMatrix (R : Type*) [CommRing R] (L : ℕ) (a b : Polynomial R) :
    Matrix (Fin L) (Fin L) R :=
  LinearMap.toMatrixAlgEquiv' (truncation L (secondOrder a b))
theorem secondOrderMatrix_natural {R S : Type*} [CommRing R] [CommRing S]
    (h : R →+* S) (L : ℕ) (a b : Polynomial R) :
    h.mapMatrix (secondOrderMatrix R L a b)=secondOrderMatrix S L (a.map h) (b.map h) := by
  ext i j
  simp only [secondOrderMatrix,RingHom.mapMatrix_apply,Matrix.map_apply,LinearMap.toMatrixAlgEquiv'_apply]
  change h ((secondOrder a b ((Polynomial.ofFn L) (Pi.single j 1))).coeff i) =
    (secondOrder (a.map h) (b.map h) ((Polynomial.ofFn L) (Pi.single j 1))).coeff i
  rw [←coeff_map]
  simp only [secondOrder_apply,Polynomial.map_add,Polynomial.map_mul,
    ←Polynomial.derivative_map,encode_map]
  have hv : (fun k : Fin L => h ((Pi.single j (1:R) : Fin L → R) k)) = Pi.single j (1:S) := by
    ext k
    simp [Pi.single_apply]
  rw [hv]
private theorem matrix_mod_two (L : ℕ) (a b : Polynomial (ZMod 2)) :
    secondOrderMatrix (ZMod 2) L a b=BalaTruncated.matrix (ZMod 2) L b := by
  have h : secondOrder a b = (Polynomial.mkDerivation (ZMod 2) b).toLinearMap := by
    exact LinearMap.ext (secondOrder_mod_two a b)
  unfold secondOrderMatrix BalaTruncated.matrix
  rw [h]
theorem integral_annihilator (a b : Polynomial ℤ) (hb : b.coeff 0=1) (s : ℕ) :
    (2 : Matrix (Fin (2^(s+1))) (Fin (2^(s+1))) ℤ)^(s+1) ∣
      (secondOrderMatrix ℤ (2^(s+1)) a b)^(2^(2*s+1))*
        ((secondOrderMatrix ℤ (2^(s+1)) a b)^((Nat.totient (2^(s+1)))^2)-1) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb' : (b.map (Int.castRingHom (ZMod 2))).coeff 0=1 := by simp [hb]
  have hh := BalaTruncated.matrix_prime_power_annihilator (p:=2)
    (b.map (Int.castRingHom (ZMod 2))) hb' s
  rw [←matrix_mod_two _ (a.map (Int.castRingHom (ZMod 2))),←secondOrderMatrix_natural] at hh
  have hl := BalaMatrix.specified_shift_lift Nat.prime_two (secondOrderMatrix ℤ (2^(s+1)) a b)
    (2^(s+1)) ((2-1)^2*2^s) s hh
  have he : 2^(s+1)*2^s=2^(2*s+1) := by rw [←pow_add]; congr 1; omega
  have ht : ((2-1)^2*2^s)*2^s=(Nat.totient (2^(s+1)))^2 := by
    rw [Nat.totient_prime_pow_succ Nat.prime_two]
    ring
  simpa only [he,ht,Nat.cast_ofNat] using hl
end
end BalaSecondOrderMatrix
end D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod
