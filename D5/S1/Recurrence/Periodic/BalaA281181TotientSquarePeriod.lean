/- GID: D5/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/BalaA281181TotientSquarePeriod
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Autonomous integral derivations yield prescribed totient-square tail periods. -/
/-
admission_basis: open-problem-resolution (#21641; Proved)
escape_witness: none
The claim retains the source expression; its proofs reuse the existing EGF
and primitive owners through compiled coefficient correspondences.
Escape audit unfinished:
https://github.com/the-omega-institute/trureturing/issues/21972
Direct frozen dependencies (declaration identities):
D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff
statement_id: sha256:4352a2872dd069de3ca054aab1c4950930a811b324435173c0e64781d46fc330
D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_derivative
statement_id: sha256:d8c528ef732aa837c3d79d7314200e072b40f5bcdc873683da352f1acf37c5c8
D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_mul
statement_id: sha256:d77958a970452d82e689ee9878ff79fda28b9bc1537bf45041f667d5e694a1f5
D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence.linear_ode_unique
statement_id: sha256:3ee42d0d09e04d4498194d296af5f0f5a145cdae9192b759e0c6e4174d652ebe
D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_encode
statement_id: sha256:352e6f7d24ca45dedb1bc8138765409965b1fb7a21903187a52a0d3fbd0a3bf7
D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_ext
statement_id: sha256:be297942dba1d71d921d56e5059d2544375954e34dd6e505146ebcbbed2baaff
D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode
statement_id: sha256:bb200c57b57d3db01e9c5a71120a010d1a0509f29a9046ca82c6726744329840
Declaration names below are relative to this module.
BalaPolynomialSystem.c: proof_shape: bind-only; consumer: BalaEvenSource.deriv_embed
BalaPolynomialSystem.s: proof_shape: bind-only; consumer: BalaEvenSource.deriv_embed
BalaPolynomialSystem.deriv: proof_shape: bind-only; consumer: BalaEvenSource.deriv_embed
BalaPolynomialSystem.initial: proof_shape: bind-only; consumer: BalaEvenSource.egf_coefficient
BalaPolynomialSystem.deriv_c: proof_shape: bind-only; consumer: BalaEvenSource.deriv_embed
BalaPolynomialSystem.deriv_s: proof_shape: bind-only; consumer: BalaEvenSource.series_second_derivative
BalaPolynomialSystem.initial_c: proof_shape: bind-only; consumer: BalaEvenSource.initial_embed
BalaPolynomialSystem.initial_s: proof_shape: bind-only; consumer: BalaPolynomialSystem.constant_S
BalaPolynomialSystem.C: proof_shape: bind-only; consumer: BalaEvenSource.series_observable
BalaPolynomialSystem.S: proof_shape: bind-only; consumer: BalaEvenSource.series_second_derivative
BalaPolynomialSystem.constant_C: proof_shape: bind-only; consumer: BalaPolynomialSystem.log_derivative
BalaPolynomialSystem.constant_S: proof_shape: bind-only; consumer: BalaPolynomialSystem.log_derivative
BalaPolynomialSystem.derivative_C: proof_shape: content; consumer: BalaPolynomialSystem.log_derivative
BalaPolynomialSystem.derivative_S: proof_shape: content; consumer: BalaPolynomialSystem.A281180_ode
BalaPolynomialSystem.hyperbolic_relation: proof_shape: content; consumer: BalaEvenSource.series_second_derivative
BalaPolynomialSystem.A281180_ode: proof_shape: content; consumer: BalaA281184TotientSquarePeriod.result
BalaPolynomialSystem.H: proof_shape: bind-only; consumer: BalaPolynomialSystem.constant_H
BalaPolynomialSystem.constant_H: proof_shape: bind-only; consumer: BalaPolynomialSystem.minus_eq_exp
BalaPolynomialSystem.derivative_H: proof_shape: bind-only; consumer: BalaPolynomialSystem.minus_eq_exp
BalaPolynomialSystem.plus_eq_exp: proof_shape: content; consumer: BalaPolynomialSystem.cosh_identity
BalaPolynomialSystem.minus_eq_exp: proof_shape: content; consumer: BalaPolynomialSystem.cosh_identity
BalaPolynomialSystem.cosh_identity: proof_shape: content; consumer: result
BalaPolynomialSystem.log_derivative: proof_shape: content; consumer: BalaA281184TotientSquarePeriod.result
BalaPolynomialSystem.evenSequence: proof_shape: bind-only; consumer: BalaPolynomialSystem.even_sequence_coefficient
BalaPolynomialSystem.even_sequence_coefficient: proof_shape: content; consumer: BalaEvenSource.source_even_coefficient
BalaOddBranch.branch_coordinate_derivative: proof_shape: bind-only; consumer: BalaOddBranch.exists_odd_branch
BalaOddBranch.polynomial_system_semiconj: proof_shape: bind-only; consumer: BalaOddBranch.source_derivative_period_odd
BalaOddBranch.atZero: proof_shape: bind-only; consumer: BalaOddBranch.atZero_root
BalaOddBranch.atZero_root: proof_shape: bind-only; consumer: BalaOddBranch.exists_odd_branch
BalaOddBranch.exists_odd_branch: proof_shape: bind-only; consumer: BalaOddBranch.source_derivative_period_odd
BalaTruncated.mod_prime_power_matrix_annihilator: proof_shape: content; consumer: BalaTruncated.prime_power_jet_period
BalaTruncated.prime_power_jet_period: proof_shape: content; consumer: BalaOddBranch.source_derivative_period_odd
BalaOddBranch.source_derivative_period_odd: proof_shape: content; consumer: BalaPolynomialSystem.even_sequence_period
BalaLinearTruncation.coeff_zero_annihilator: proof_shape: bind-only; consumer: BalaSecondOrderMatrix.two_power_annihilator_congruence
BalaLinearTruncation.secondOrder_map: proof_shape: bind-only; consumer: BalaSecondOrderMatrix.two_power_annihilator_congruence
BalaSecondOrderMatrix.two_power_annihilator_congruence: proof_shape: content; consumer: BalaSecondOrderMatrix.two_power_period
BalaSecondOrderMatrix.two_power_period: proof_shape: content; consumer: BalaPolynomialSystem.even_sequence_period
BalaEvenSource.principal: proof_shape: bind-only; consumer: BalaEvenSource.egf_coefficient
BalaEvenSource.drift: proof_shape: bind-only; consumer: BalaEvenSource.drift_constant
BalaEvenSource.series: proof_shape: bind-only; consumer: BalaEvenSource.egf_coefficient
BalaEvenSource.deriv_embed: proof_shape: bind-only; consumer: BalaEvenSource.series_second_derivative
BalaEvenSource.series_second_derivative: proof_shape: content; consumer: BalaEvenSource.even_iterates
BalaEvenSource.even_iterates: proof_shape: content; consumer: BalaEvenSource.egf_coefficient
BalaEvenSource.initial_embed: proof_shape: bind-only; consumer: BalaEvenSource.egf_coefficient
BalaEvenSource.series_observable: proof_shape: content; consumer: BalaEvenSource.source_even_coefficient
BalaEvenSource.egf_coefficient: proof_shape: content; consumer: BalaEvenSource.source_even_coefficient
BalaEvenSource.source_even_coefficient: proof_shape: content; consumer: BalaPolynomialSystem.even_sequence_period
BalaEvenSource.drift_constant: proof_shape: bind-only; consumer: BalaPolynomialSystem.even_sequence_period
BalaPolynomialSystem.even_sequence_period: proof_shape: content; consumer: result
claim: proof_shape: bind-only; consumer: result
result: proof_shape: content; consumer: settling result
-/

import D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod
import D5.S1.Recurrence.Residue.IntegralEGFComposition
import Mathlib.Algebra.MvPolynomial.Derivation
import D5.S1.Recurrence.Algebraic.SchroderIntegralEGF
import D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence
import Mathlib.RingTheory.PowerSeries.Log
import D5.S1.Recurrence.Periodic.BalaA281180TotientSquarePeriod

namespace D5.S1.Recurrence.Periodic.BalaA281181TotientSquarePeriod
open scoped Classical
open D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod
open D5.S1.Recurrence.Periodic.BalaA281180TotientSquarePeriod
open D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod.BalaCharP
open D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod.BalaFiltration
open D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod.BalaJets
open D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod.BalaLinearTruncation
open D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod.BalaLocalPrime
open D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod.BalaMatrix
open D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod.BalaOddPrimeRoot
open D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod.BalaOperator
open D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod.BalaScalarAnnihilator
open D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod.BalaSecondOrderMatrix
open D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod.BalaTruncated
open D5.S1.Recurrence.Periodic.BalaA281180TotientSquarePeriod.BalaCRT
open D5.S1.Recurrence.Periodic.BalaA281180TotientSquarePeriod.BalaFlow

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
namespace BalaPolynomialSystem
open BalaFlow
noncomputable section
def c : (MvPolynomial Bool ℤ) := MvPolynomial.X false
def s : (MvPolynomial Bool ℤ) := MvPolynomial.X true
def deriv (q : ℕ) : Derivation ℤ (MvPolynomial Bool ℤ) (MvPolynomial Bool ℤ) :=
  MvPolynomial.mkDerivation ℤ fun b => if b then c^(q+1) else c^q*s
def initial : (MvPolynomial Bool ℤ) →+* ℤ := MvPolynomial.eval fun b => if b then 0 else 1
private theorem deriv_c (q : ℕ) : deriv q c = c^q*s := by simp [deriv, c]
private theorem deriv_s (q : ℕ) : deriv q s = c^(q+1) := by simp [deriv, s]
private theorem initial_c : initial c = 1 := by simp [initial,c]
private theorem initial_s : initial s = 0 := by simp [initial,s]
def C (q : ℕ) : PowerSeries ℚ := flow (deriv q) initial c
def S (q : ℕ) : PowerSeries ℚ := flow (deriv q) initial s
private theorem constant_C (q : ℕ) : constantCoeff (C q) = 1 := by
  simp [C, constantCoeff_flow, initial_c]
theorem constant_S (q : ℕ) : constantCoeff (S q) = 0 := by
  simp [S, constantCoeff_flow, initial_s]
private theorem derivative_C (q : ℕ) : PowerSeries.derivative (C q) = C q ^ q * S q := by
  change PowerSeries.derivative (flow (deriv q) initial c) = _
  rw [flow_derivative, deriv_c]
  have h := map_mul (flowMap (deriv q) initial) (c^q) s
  rw [map_pow] at h
  simpa only [flowMapApply,C,S] using h
private theorem derivative_S (q : ℕ) : PowerSeries.derivative (S q) = C q ^ (q+1) := by
  change PowerSeries.derivative (flow (deriv q) initial s) = _
  rw [flow_derivative, deriv_s]
  simpa only [flowMapApply,C] using map_pow (flowMap (deriv q) initial) c (q+1)
private theorem hyperbolic_relation (q : ℕ) : C q ^ 2 - S q ^ 2 = 1 := by
  have hd : deriv q (c^2-s^2) = 0 := by
    rw [pow_two, pow_two, map_sub, Derivation.leibniz, Derivation.leibniz,
      deriv_c, deriv_s]
    simp only [smul_eq_mul, pow_succ]
    ring
  have h := flow_of_d_eq_zero (deriv q) initial (c^2-s^2) hd
  rw [← flowMapApply (deriv q) initial (c^2-s^2)] at h
  simp only [map_sub,map_pow] at h
  simpa [flowMapApply,initial_c,initial_s,C,S] using h
theorem A281180_ode : PowerSeries.derivative (S 3) = (1 + S 3 ^ 2)^2 := by
  rw [derivative_S]
  have h := hyperbolic_relation 3
  have hc : C 3 ^ 2 = 1 + S 3 ^ 2 := by linear_combination h
  calc C 3 ^ (3+1) = (C 3^2)^2 := by ring
       _ = _ := by rw [hc]
end
end BalaPolynomialSystem
namespace BalaPolynomialSystem
open D5.S1.Recurrence.Algebraic.SchroderIntegralEGF (primitive primitive_zero derivative_primitive)
open D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence (linear_ode_unique)
noncomputable def H (q : ℕ) : PowerSeries ℚ := primitive (C q ^ q)
theorem constant_H (q : ℕ) : constantCoeff (H q) = 0 := primitive_zero _
theorem derivative_H (q : ℕ) : PowerSeries.derivative (H q) = C q ^ q := derivative_primitive _
private theorem plus_eq_exp (q : ℕ) : C q + S q = (PowerSeries.exp ℚ).subst (H q) := by
  apply linear_ode_unique _ _ (C q ^ q)
  · rw [coeff_zero_eq_constantCoeff, map_add, constant_C, constant_S, add_zero,
      PowerSeries.constantCoeff_eq,
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero (constant_H q)]
    simp
  · rw [map_add, derivative_C, derivative_S, pow_succ]
    ring
  · rw [derivative_subst (HasSubst.of_constantCoeff_zero' (constant_H q)),
      derivative_exp, derivative_H, mul_comm]
private theorem minus_eq_exp (q : ℕ) : C q - S q = (PowerSeries.exp ℚ).subst (-H q) := by
  apply linear_ode_unique _ _ (-(C q ^ q))
  · rw [coeff_zero_eq_constantCoeff, map_sub,
      constant_C, constant_S, sub_zero]
    symm
    rw [PowerSeries.constantCoeff_eq,
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero
        (by change PowerSeries.constantCoeff (-H q) = 0; simp [constant_H])]
    simp
  · rw [map_sub, derivative_C, derivative_S, pow_succ]
    ring
  · rw [derivative_subst (HasSubst.of_constantCoeff_zero' (by simp [constant_H])),
      derivative_exp, map_neg, derivative_H, mul_comm]
theorem cosh_identity (q : ℕ) :
    C q = PowerSeries.C (1 / 2 : ℚ) *
      ((PowerSeries.exp ℚ).subst (H q) + (PowerSeries.exp ℚ).subst (-H q)) := by
  rw [← plus_eq_exp, ← minus_eq_exp]
  have htwo : PowerSeries.C (1 / 2 : ℚ) * (2 : PowerSeries ℚ) = 1 := by
    rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 by exact (map_ofNat PowerSeries.C 2).symm, ← map_mul]
    norm_num
  linear_combination -(C q) * htwo
theorem log_derivative (q : ℕ) :
    PowerSeries.derivative (PowerSeries.logOf (C q + S q)) = C q ^ q := by
  let F := C q + S q
  have hF0 : constantCoeff F = 1 := by simp [F,constant_C,constant_S]
  have hs : HasSubst (F - 1) := HasSubst.of_constantCoeff_zero' (by simp [hF0])
  have hone : subst (F-1) (1 : PowerSeries ℚ) = 1 := by
    rw [← coe_substAlgHom hs]; exact map_one _
  have hunit : (PowerSeries.derivative (log ℚ)).subst (F-1) * F = 1 := by
    have h := congrArg (subst (F-1)) (derivative_log_mul_one_add_X (A := ℚ))
    simpa only [subst_mul hs, subst_add hs, hone, subst_X hs, add_sub_cancel] using h
  have hdF : PowerSeries.derivative F = C q ^ q * F := by
    dsimp [F]
    rw [map_add, derivative_C, derivative_S, pow_succ]
    ring
  have hFn : F ≠ 0 := by intro h; simpa [h] using hF0
  apply mul_right_cancel₀ hFn
  rw [logOf_eq, derivative_subst hs, map_sub, derivative_one, sub_zero, hdF]
  calc
    _ = (C q ^ q * F) * ((PowerSeries.derivative (log ℚ)).subst (F-1) * F) := by ring
    _ = _ := by rw [hunit,mul_one]
noncomputable def evenSequence (q e n : ℕ) : ℤ := initial ((deriv q)^[2*n] (c^e))
theorem even_sequence_coefficient (q e n : ℕ) :
    (evenSequence q e n : ℚ)=eCoeff (C q^e) (2*n) := by
  have h := map_pow (flowMap (deriv q) initial) c e
  simp only [flowMapApply] at h
  rw [C,←h]
  exact (eCoeff_flow (deriv q) initial (c^e) (2*n)).symm
end BalaPolynomialSystem
namespace BalaOddBranch
open BalaPolynomialSystem
variable {R J : Type*} [CommRing R] [CommRing J] [Algebra R J]
private theorem branch_coordinate_derivative (d : Derivation R J J) (q : ℕ) (b y : J)
    (h2 : IsUnit (2:J)) (hb : IsUnit b) (hsquare : b^2=1+y^2)
    (hy : d y=b^(q+1)) : d b=b^q*y := by
  have hh := congrArg d hsquare
  simp only [pow_two,map_add,Derivation.leibniz,Derivation.map_one_eq_zero,
    zero_add,smul_eq_mul] at hh
  rw [hy,pow_succ] at hh
  apply (h2.mul hb).mul_left_cancel
  linear_combination hh
private theorem polynomial_system_semiconj (d : Derivation R J J) (q : ℕ) (b y : J)
    (hb : d b=b^q*y) (hy : d y=b^(q+1)) :
    Function.Semiconj (MvPolynomial.eval₂Hom (Int.castRingHom J) (fun i : Bool => if i then y else b))
      (deriv q) d := by
  intro f
  let φ := MvPolynomial.eval₂Hom (Int.castRingHom J) (fun i : Bool => if i then y else b)
  change φ (deriv q f)=d (φ f)
  induction f using MvPolynomial.induction_on with
  | C z =>
    simp only [MvPolynomial.derivation_C,map_zero]
    have hz : φ (MvPolynomial.C z)=(z:J) := by simp [φ]
    rw [hz,Derivation.map_intCast]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf =>
    have hX : φ (deriv q (MvPolynomial.X i))=d (φ (MvPolynomial.X i)) := by
      cases i <;> simp [deriv,φ,c,s,hb,hy]
    simp only [Derivation.leibniz,smul_eq_mul,map_add,map_mul,hf,hX]
end BalaOddBranch
namespace BalaOddBranch
open Polynomial BalaJets BalaPolynomialSystem
noncomputable section
private def atZero {R : Type*} [CommRing R] (L : ℕ) (hL : 0<L) : AdjoinRoot (Polynomial.X ^ L : Polynomial R) →+* R :=
  AdjoinRoot.lift (RingHom.id R) 0 (by simp [hL.ne'])
private theorem atZero_root {R : Type*} [CommRing R] (L : ℕ) (hL : 0<L) :
    atZero L hL (AdjoinRoot.root (Polynomial.X^L : Polynomial R))=0 := by
  simp [atZero]
private theorem exists_odd_branch (p : ℕ) (hp : p.Prime) (hp2 : p≠2) (s h : ℕ) :
    let L := p^(s+1)
    let J := AdjoinRoot (Polynomial.X ^ L : Polynomial (ZMod L))
    let y : J := AdjoinRoot.root (Polynomial.X^L : Polynomial (ZMod L))
    let d := jetDerivation L (by simp) ((1+Polynomial.X^2)^(h+1) : Polynomial (ZMod L))
    ∃ b : J, b^2=1+y^2 ∧ atZero L (pow_pos hp.pos _) b=1 ∧
      d b=b^(2*h+1)*y ∧ d y=b^((2*h+1)+1) := by
  dsimp only
  let L := p^(s+1)
  let J := AdjoinRoot (Polynomial.X ^ L : Polynomial (ZMod L))
  let y : J := AdjoinRoot.root (Polynomial.X^L : Polynomial (ZMod L))
  let d := jetDerivation L (by simp [L]) ((1+Polynomial.X^2)^(h+1) : Polynomial (ZMod L))
  have hchar : (p:J)^(s+1)=0 := by
    have hc := congrArg (algebraMap (ZMod L) J) (ZMod.natCast_self L)
    have hc' : (L:J)=0 := by simpa only [map_natCast,map_zero] using hc
    simpa only [L,Nat.cast_pow] using hc'
  have hyzero : (y^2)^L=0 := by
    rw [←pow_mul,show 2*L=L*2 by omega,pow_mul,root_pow_zero,zero_pow (by decide : 2≠0)]
  obtain ⟨b,hb,m,hm⟩ := D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod.BalaOddPrimeRoot.square_root_in_finite_jet hp hp2 s hchar (y^2) hyzero
  have hb0 : atZero L (pow_pos hp.pos _) b=1 := by
    rw [hm,map_pow,map_add,map_one,map_pow,atZero_root]
    simp
  have hbu : IsUnit b := by
    rw [hm]
    apply IsUnit.pow
    exact IsNilpotent.isUnit_one_add ⟨L,hyzero⟩
  have h2R : IsUnit (2 : ZMod L) := by
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega : 0<s+1)).mpr
    intro hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1|h2
    · exact hp.ne_one h1
    · exact hp2 h2
  have h2 : IsUnit (2:J) := by
    simpa only [map_ofNat] using h2R.map (algebraMap (ZMod L) J)
  have hdy : d y=b^((2*h+1)+1) := by
    change jetDerivation L _ _ (AdjoinRoot.root (Polynomial.X^L : Polynomial (ZMod L)))=_
    rw [jetDerivation_root]
    simp only [map_pow,map_add,map_one,AdjoinRoot.mk_X]
    rw [←hb,←pow_mul]
    congr 1
  refine ⟨b,hb,hb0,?_,hdy⟩
  exact branch_coordinate_derivative d (2*h+1) b y h2 hbu hb hdy
end
end BalaOddBranch
namespace BalaTruncated
open Polynomial BalaJets
noncomputable section
private theorem mod_prime_power_matrix_annihilator {p : ℕ} [Fact p.Prime]
    (P : Polynomial ℤ) (hP : P.coeff 0=1) (s : ℕ) :
    let L := p^(s+1)
    let A := matrix (ZMod L) L (P.map (Int.castRingHom (ZMod L)))
    A^(p^(2*s+1))*(A^((Nat.totient L)^2)-1)=0 := by
  let L := p^(s+1)
  let cast := Int.castRingHom (ZMod L)
  dsimp only
  rw [←matrix_natural]
  have hd := integer_matrix_totient_square (p:=p) P hP s
  have hc : (p : Matrix (Fin L) (Fin L) ℤ)^(s+1)=(L : Matrix (Fin L) (Fin L) ℤ) := by simp [L]
  rw [hc] at hd
  obtain ⟨B,hB⟩ := hd
  have hh := congrArg cast.mapMatrix hB
  have hc0 : (L : Matrix (Fin L) (Fin L) (ZMod L))=0 := by
    ext i j
    simp [Matrix.natCast_apply]
  simpa only [map_mul,map_pow,map_sub,map_one,map_natCast,hc0,zero_mul] using hh
private theorem prime_power_jet_period {p : ℕ} [Fact p.Prime]
    (P : Polynomial ℤ) (hP : P.coeff 0=1) (s : ℕ)
    (f : AdjoinRoot (Polynomial.X ^ (p^(s+1)) : Polynomial (ZMod (p^(s+1))))) (m : ℕ) (hm : p^(2*s+1)≤m) :
    let d := jetDerivation (p^(s+1)) (by simp : ((p^(s+1):ℕ) : ZMod (p^(s+1)))=0)
      (P.map (Int.castRingHom (ZMod (p^(s+1)))))
    d^[m+(Nat.totient (p^(s+1)))^2] f=d^[m] f := by
  dsimp only
  let L := p^(s+1)
  let P' := P.map (Int.castRingHom (ZMod L))
  let d := jetDerivation L (by simp [L]) P'
  let u := p^(2*s+1)
  let t := (Nat.totient L)^2
  obtain ⟨g,hg⟩ := AdjoinRoot.mk_surjective (d^[m-u] f)
  have hh := jet_annihilator_of_matrix L (by simp [L]) P' u t
    (mod_prime_power_matrix_annihilator (p:=p) P hP s) g
  change d^[u] (d^[t] (AdjoinRoot.mk (Polynomial.X^L : Polynomial (ZMod L)) g)-
    AdjoinRoot.mk (Polynomial.X^L : Polynomial (ZMod L)) g)=0 at hh
  rw [hg] at hh
  have hsub (x y : AdjoinRoot (Polynomial.X ^ L : Polynomial (ZMod L))) : d^[u] (x-y)=d^[u] x-d^[u] y := by
    simpa only [Module.End.pow_apply,Derivation.coeFn_coe] using map_sub (d.toLinearMap^u) x y
  rw [hsub,←Function.iterate_add_apply,←Function.iterate_add_apply,
    ←Function.iterate_add_apply] at hh
  have he : u+t+(m-u)=m+t := by dsimp [u] at *; omega
  have he' : u+(m-u)=m := by dsimp [u] at *; omega
  rw [he,he',sub_eq_zero] at hh
  exact hh
end
end BalaTruncated
namespace BalaOddBranch
open Polynomial BalaJets BalaPolynomialSystem
noncomputable section
private theorem source_derivative_period_odd (p : ℕ) (hp : p.Prime) (hp2 : p≠2)
    (s h : ℕ) (F : (MvPolynomial Bool ℤ)) (m : ℕ) (hm : p^(2*s+1)≤m) :
    Int.ModEq (p^(s+1) : ℤ)
      (initial ((deriv (2*h+1))^[m+(Nat.totient (p^(s+1)))^2] F))
      (initial ((deriv (2*h+1))^[m] F)) := by
  letI : Fact p.Prime := ⟨hp⟩
  let L := p^(s+1)
  let J := AdjoinRoot (Polynomial.X ^ L : Polynomial (ZMod L))
  let y : J := AdjoinRoot.root (Polynomial.X^L : Polynomial (ZMod L))
  let d := jetDerivation L (by simp [L]) ((1+Polynomial.X^2)^(h+1) : Polynomial (ZMod L))
  obtain ⟨b,hbsq,hb0,hdb,hdy⟩ := exists_odd_branch p hp hp2 s h
  let φ := MvPolynomial.eval₂Hom (Int.castRingHom J) (fun i : Bool => if i then y else b)
  let ε := atZero (R:=ZMod L) L (pow_pos hp.pos _)
  have hs : Function.Semiconj φ (deriv (2*h+1)) d :=
    polynomial_system_semiconj d (2*h+1) b y hdb hdy
  have hP : ((1+Polynomial.X^2)^(h+1) : Polynomial ℤ).coeff 0=1 := by
    change Polynomial.constantCoeff ((1+Polynomial.X^2)^(h+1) : Polynomial ℤ)=1
    rw [map_pow,map_add,map_one,map_pow]
    norm_num [Polynomial.constantCoeff]
  have hj := BalaTruncated.prime_power_jet_period (p:=p)
    ((1+Polynomial.X^2)^(h+1)) hP s (φ F) m hm
  have hj' : d^[m+(Nat.totient L)^2] (φ F)=d^[m] (φ F) := by
    simpa only [Polynomial.map_pow,Polynomial.map_add,Polynomial.map_one,
      Polynomial.map_X] using hj
  have hφ : φ ((deriv (2*h+1))^[m+(Nat.totient L)^2] F)=
      φ ((deriv (2*h+1))^[m] F) :=
    (hs.iterate_right _ F).trans (hj'.trans (hs.iterate_right _ F).symm)
  have hε : ε.comp φ=(Int.castRingHom (ZMod L)).comp initial := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [φ,ε,initial]
    · intro i
      cases i
      · simp only [RingHom.comp_apply,φ,MvPolynomial.eval₂Hom_X',Bool.false_eq_true,
          ite_false,initial,MvPolynomial.eval_X,map_one]
        exact hb0
      · simp only [RingHom.comp_apply,φ,MvPolynomial.eval₂Hom_X',ite_true,
          initial,MvPolynomial.eval_X,map_zero]
        exact atZero_root L (pow_pos hp.pos _)
  have hh := congrArg ε hφ
  change (ε.comp φ) _=(ε.comp φ) _ at hh
  rw [hε] at hh
  simpa only [L,Nat.cast_pow] using (ZMod.intCast_eq_intCast_iff _ _ L).mp hh
end
end BalaOddBranch
namespace BalaLinearTruncation
open Polynomial BalaTruncated
noncomputable section
private theorem coeff_zero_annihilator {R : Type*} [CommRing R] (L : ℕ) (hL : 0<L)
    (F : Module.End R (Polynomial R))
    (hstable : ∀ f : Polynomial R, Polynomial.X^L ∣ f → Polynomial.X^L ∣ F f) (u t : ℕ)
    (hA : (LinearMap.toMatrixAlgEquiv' (truncation L F))^u*
      ((LinearMap.toMatrixAlgEquiv' (truncation L F))^t-1)=0) (f : Polynomial R) :
    (F^[u] (F^[t] f-f)).coeff 0=0 := by
  have hT : (truncation L F)^u*((truncation L F)^t-1)=0 := by
    apply (LinearMap.toMatrixAlgEquiv' :
      Module.End R (Fin L → R) ≃ₐ[R] Matrix (Fin L) (Fin L) R).injective
    simpa only [map_mul,map_pow,map_sub,map_one,map_zero] using hA
  have hh := congrArg (fun T : Module.End R (Fin L → R) => T ((Polynomial.toFn L) f)) hT
  simp only [Module.End.mul_apply,Module.End.pow_apply,LinearMap.sub_apply,
    Module.End.one_apply,LinearMap.zero_apply] at hh
  have hs := decode_semiconj L F hstable
  have hz : (Polynomial.toFn L) (F^[u] (F^[t] f-f))=0 := by
    rw [hs.iterate_right u,map_sub,hs.iterate_right t]
    exact hh
  exact X_pow_dvd_iff.mp ((decode_zero_iff L _).mp hz) 0 hL
private theorem secondOrder_map {R S : Type*} [CommRing R] [CommRing S]
    (h : R →+* S) (a b f : Polynomial R) (n : ℕ) :
    ((secondOrder a b)^[n] f).map h=
      (secondOrder (a.map h) (b.map h))^[n] (f.map h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply',secondOrder_apply,Polynomial.map_add,
      Polynomial.map_mul,←Polynomial.derivative_map,ih]
end
end BalaLinearTruncation
namespace BalaSecondOrderMatrix
open Polynomial BalaTruncated BalaLinearTruncation
noncomputable section
private theorem two_power_annihilator_congruence (a b : Polynomial ℤ) (hb : b.coeff 0=1)
    (s : ℕ) (f : Polynomial ℤ) :
    Int.ModEq (2^(s+1) : ℤ)
      (((secondOrder a b)^[2^(2*s+1)]
        ((secondOrder a b)^[((Nat.totient (2^(s+1)))^2)] f-f)).coeff 0) 0 := by
  let L := 2^(s+1)
  let cast := Int.castRingHom (ZMod L)
  have hd := integral_annihilator a b hb s
  have hc : (2 : Matrix (Fin L) (Fin L) ℤ)^(s+1)=(L : Matrix (Fin L) (Fin L) ℤ) := by
    simp [L]
  rw [hc] at hd
  obtain ⟨B,hB⟩ := hd
  have hh := congrArg cast.mapMatrix hB
  have hc0 : (L : Matrix (Fin L) (Fin L) (ZMod L))=0 := by
    ext i j
    simp [Matrix.natCast_apply]
  have hz : (cast.mapMatrix (secondOrderMatrix ℤ L a b))^(2^(2*s+1))*
      ((cast.mapMatrix (secondOrderMatrix ℤ L a b))^((Nat.totient L)^2)-1)=0 := by
    simpa only [map_mul,map_pow,map_sub,map_one,map_natCast,hc0,zero_mul] using hh
  rw [secondOrderMatrix_natural] at hz
  have hcoeff := coeff_zero_annihilator L (pow_pos (by decide : 0<2) _)
    (secondOrder (a.map cast) (b.map cast))
    (secondOrder_stable L (by simp [L]) (a.map cast) (b.map cast))
    (2^(2*s+1)) ((Nat.totient L)^2) hz (f.map cast)
  rw [←secondOrder_map,←Polynomial.map_sub,←secondOrder_map,Polynomial.coeff_map] at hcoeff
  apply Int.modEq_zero_iff_dvd.mpr
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ L).mp hcoeff
private theorem two_power_period (a b : Polynomial ℤ) (hb : b.coeff 0=1)
    (s : ℕ) (f : Polynomial ℤ) (n : ℕ) (hn : 2^(2*s+1)≤n) :
    Int.ModEq (2^(s+1) : ℤ)
      (((secondOrder a b)^[n+(Nat.totient (2^(s+1)))^2] f).coeff 0)
      (((secondOrder a b)^[n] f).coeff 0) := by
  let F := secondOrder a b
  let u := 2^(2*s+1)
  let t := (Nat.totient (2^(s+1)))^2
  have hh := two_power_annihilator_congruence a b hb s (F^[n-u] f)
  change Int.ModEq _ ((F^[u] (F^[t] (F^[n-u] f)-F^[n-u] f)).coeff 0) 0 at hh
  have hsub (x y : Polynomial ℤ) : F^[u] (x-y)=F^[u] x-F^[u] y := by
    simpa only [Module.End.pow_apply] using map_sub (F^u) x y
  rw [hsub,Polynomial.coeff_sub,←Function.iterate_add_apply,
    ←Function.iterate_add_apply,←Function.iterate_add_apply] at hh
  have he : u+t+(n-u)=n+t := by dsimp [u] at *; omega
  have he' : u+(n-u)=n := by dsimp [u] at *; omega
  rw [he,he'] at hh
  simpa only [sub_add_cancel,zero_add] using hh.add_right ((F^[n] f).coeff 0)
end
end BalaSecondOrderMatrix
namespace BalaEvenSource
open BalaPolynomialSystem BalaFlow BalaLinearTruncation
open D5.S1.Recurrence.Residue.IntegralEGFComposition
noncomputable section
private def principal (q : ℕ) : Polynomial ℤ :=
  (1+Polynomial.X)^(2*q)*((1+Polynomial.X)^2-1)
private def drift (q : ℕ) : Polynomial ℤ :=
  (1+Polynomial.X)^(2*q-1)*(((q : Polynomial ℤ)+1)*(1+Polynomial.X)^2-(q : Polynomial ℤ))
private def series (q : ℕ) (f : Polynomial ℤ) : PowerSeries ℚ := flow (deriv q) initial ((Polynomial.aeval (c-1)) f)
private theorem deriv_embed (q : ℕ) (f : Polynomial ℤ) :
    deriv q ((Polynomial.aeval (c-1)) f)=(Polynomial.aeval (c-1)) f.derivative*(c^q*s) := by
  simpa only [Derivation.comp_aeval_eq,smul_eq_mul,map_sub,
    Derivation.map_one_eq_zero,sub_zero,deriv_c] using
    (Derivation.comp_aeval_eq (a:=c-1) (deriv q) f)
private theorem series_second_derivative (q : ℕ) (hq : q=3 ∨ q=7) (f : Polynomial ℤ) :
    PowerSeries.derivative (PowerSeries.derivative (series q f))=series q ((secondOrder (principal q) (drift q)) f) := by
  simp only [series,flow_derivative,deriv_embed,Derivation.leibniz,
    Derivation.leibniz_pow,deriv_c,deriv_s,smul_eq_mul,nsmul_eq_mul]
  simp only [← flowMapApply]
  change (flowMap (deriv q) initial) _=(flowMap (deriv q) initial) _
  simp only [map_add,map_mul,map_pow,map_natCast]
  rw [show (secondOrder (principal q) (drift q)) f=principal q*f.derivative.derivative+drift q*f.derivative from rfl]
  simp only [map_add,map_mul,map_pow,map_sub,map_one,Polynomial.aeval_X,
    principal,drift,map_natCast,sub_add_cancel,add_sub_cancel_right,
    map_add,map_mul,map_pow,map_sub,map_one,map_natCast]
  have hx : (1 : PowerSeries ℚ)+((flowMap (deriv q) initial) c-1)=BalaPolynomialSystem.C q := by
    rw [flowMapApply]
    change 1+(BalaPolynomialSystem.C q-1)=BalaPolynomialSystem.C q
    ring
  rw [hx]
  simp only [flowMapApply]
  change _=(BalaPolynomialSystem.C q^(2*q)*(BalaPolynomialSystem.C q^2-1))*_+
    (BalaPolynomialSystem.C q^(2*q-1)*(((q : PowerSeries ℚ)+1)*(BalaPolynomialSystem.C q)^2-(q : PowerSeries ℚ)))*_
  rcases hq with rfl|rfl
  · have hh := hyperbolic_relation 3
    simp only [BalaPolynomialSystem.C,S,flowMapApply] at hh ⊢
    norm_num
    linear_combination -((flow (deriv 3) initial) (Polynomial.aeval (c-1) f.derivative.derivative))*(flow (deriv 3) initial c)^6*hh +
      -3*((flow (deriv 3) initial) (Polynomial.aeval (c-1) f.derivative))*(flow (deriv 3) initial c)^5*hh
  · have hh := hyperbolic_relation 7
    simp only [BalaPolynomialSystem.C,S,flowMapApply] at hh ⊢
    norm_num
    linear_combination -((flow (deriv 7) initial) (Polynomial.aeval (c-1) f.derivative.derivative))*(flow (deriv 7) initial c)^14*hh +
      -7*((flow (deriv 7) initial) (Polynomial.aeval (c-1) f.derivative))*(flow (deriv 7) initial c)^13*hh
private theorem even_iterates (q : ℕ) (hq : q=3 ∨ q=7) (f : Polynomial ℤ) (n : ℕ) :
    (PowerSeries.derivative)^[2*n] (series q f)=series q (((secondOrder (principal q) (drift q)))^[n] f) := by
  have hs : Function.Semiconj (series q) ((secondOrder (principal q) (drift q))) ((PowerSeries.derivative)^[2]) := by
    intro g
    exact (series_second_derivative q hq g).symm
  simpa only [Function.iterate_mul] using (hs.iterate_right n f).symm
end
end BalaEvenSource
namespace BalaEvenSource
open BalaPolynomialSystem BalaFlow
open D5.S1.Recurrence.Residue.IntegralEGFComposition
noncomputable section
private theorem initial_embed (f : Polynomial ℤ) : initial ((Polynomial.aeval (c-1)) f)=f.coeff 0 := by
  have hc : initial.comp (algebraMap ℤ (MvPolynomial Bool ℤ))=RingHom.id ℤ := Subsingleton.elim _ _
  rw [Polynomial.aeval_def,Polynomial.hom_eval₂,hc]
  simp only [map_sub,initial_c,map_one,sub_self,Polynomial.eval₂_id,
    ←Polynomial.coeff_zero_eq_eval_zero]
private theorem series_observable (q e : ℕ) : series q ((1+Polynomial.X)^e)=BalaPolynomialSystem.C q^e := by
  have hx : (1:(MvPolynomial Bool ℤ))+(c-1)=c := by
    simpa only [add_comm] using sub_add_cancel c 1
  rw [series,← flowMapApply]
  change (flowMap (deriv q) initial) (Polynomial.aeval (c-1) ((1+Polynomial.X)^e))=_
  simp only [map_pow,map_add,map_one,Polynomial.aeval_X,hx]
  rw [flowMapApply]
  rfl
private theorem egf_coefficient (q : ℕ) (hq : q=3 ∨ q=7) (f : Polynomial ℤ) (n : ℕ) :
    ((((secondOrder (principal q) (drift q)))^[n] f).coeff 0 : ℚ)=eCoeff (series q f) (2*n) := by
  have hh := congrArg PowerSeries.constantCoeff (even_iterates q hq f n)
  simpa only [PowerSeries.constantCoeff_iterate_derivative,eCoeff,
    series,constantCoeff_flow,initial_embed] using hh.symm
private theorem source_even_coefficient (q : ℕ) (hq : q=3 ∨ q=7) (e n : ℕ) :
    initial ((deriv q)^[2*n] (c^e))=(((secondOrder (principal q) (drift q)))^[n] ((1+Polynomial.X)^e)).coeff 0 := by
  apply (Int.cast_injective : Function.Injective ((↑) : ℤ → ℚ))
  have hc : (initial ((deriv q)^[2*n] (c^e)) : ℚ)=eCoeff (BalaPolynomialSystem.C q^e) (2*n) :=
    even_sequence_coefficient q e n
  rw [hc,←series_observable q e]
  exact (egf_coefficient q hq ((1+Polynomial.X)^e) n).symm
private theorem drift_constant (q : ℕ) : (drift q).coeff 0=1 := by
  change Polynomial.constantCoeff (drift q)=1
  simp only [drift,map_mul,map_pow,map_sub,map_add,map_one,map_natCast]
  norm_num [Polynomial.constantCoeff,Nat.cast_add] <;> ring
end
end BalaEvenSource
namespace BalaPolynomialSystem
open BalaLinearTruncation
open D5.S1.Recurrence.Residue.IntegralEGFComposition
noncomputable section

theorem even_sequence_period (q : ℕ) (hq : q=3 ∨ q=7) (e : ℕ) :
    ∀ k : ℕ, 1≤k → ∃ N : ℕ, 1≤N ∧ ∀ n : ℕ, N≤n →
      Int.ModEq (k:ℤ) (evenSequence q e (n+(Nat.totient k)^2)) (evenSequence q e n) := by
  apply D5.S1.Recurrence.Periodic.BalaA281180TotientSquarePeriod.BalaCRT.prime_power_periods_to_all_moduli
  intro p r hp hr n hn
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  change (p^(s+1))^2≤n at hn
  have hu : p^(2*s+1)≤(p^(s+1))^2 := by
    rw [←pow_mul]
    apply Nat.pow_le_pow_right hp.pos
    omega
  by_cases hp2 : p=2
  · subst p
    simp only [evenSequence,BalaEvenSource.source_even_coefficient q hq]
    exact BalaSecondOrderMatrix.two_power_period (BalaEvenSource.principal q)
      (BalaEvenSource.drift q) (BalaEvenSource.drift_constant q) s ((1+Polynomial.X)^e)
      n (hu.trans hn)
  · have hodd : ∃ h, q=2*h+1 := by
      rcases hq with rfl|rfl
      · exact ⟨1,by omega⟩
      · exact ⟨3,by omega⟩
    obtain ⟨h,rfl⟩ := hodd
    have hm : p^(2*s+1)≤2*n := (hu.trans hn).trans (by omega)
    have h1 := BalaOddBranch.source_derivative_period_odd p hp hp2 s h (c^e)
      (2*n+(Nat.totient (p^(s+1)))^2) (by omega)
    have h2 := BalaOddBranch.source_derivative_period_odd p hp hp2 s h (c^e) (2*n) hm
    have he : 2*(n+(Nat.totient (p^(s+1)))^2)=
      (2*n+(Nat.totient (p^(s+1)))^2)+(Nat.totient (p^(s+1)))^2 := by omega
    simpa only [evenSequence,he] using h1.trans h2
end
end BalaPolynomialSystem

open D5.S1.Recurrence.Residue.IntegralEGFComposition
def claim : Prop :=
  ∃ (H C : PowerSeries ℚ),
    PowerSeries.constantCoeff H = 0 ∧
    PowerSeries.derivative H = C ^ 3 ∧
    C = PowerSeries.C (1 / 2 : ℚ) *
      ((PowerSeries.exp ℚ).subst H + (PowerSeries.exp ℚ).subst (-H)) ∧
    ∃ a : ℕ → ℤ,
      (∀ n : ℕ, (a n : ℚ) = eCoeff (C ^ 1) (2 * n)) ∧
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n →
        Int.ModEq (k : ℤ) (a (n + (Nat.totient k) ^ 2)) (a n)
open BalaPolynomialSystem
noncomputable section
theorem result : claim := by
  refine ⟨H 3,BalaPolynomialSystem.C 3,constant_H 3,derivative_H 3,cosh_identity 3,
    evenSequence 3 1,even_sequence_coefficient 3 1,?_⟩
  intro k hk
  obtain ⟨N,hN,hp⟩ := even_sequence_period 3 (by omega) 1 k hk
  exact ⟨N,hp⟩
end
end D5.S1.Recurrence.Periodic.BalaA281181TotientSquarePeriod
