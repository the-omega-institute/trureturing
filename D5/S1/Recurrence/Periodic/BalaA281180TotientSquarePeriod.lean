/- GID: D5/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/BalaA281180TotientSquarePeriod
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Autonomous integral derivations yield prescribed totient-square tail periods. -/
/-
admission_basis: open-problem-resolution (#21640; Proved)
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
D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_encode
statement_id: sha256:352e6f7d24ca45dedb1bc8138765409965b1fb7a21903187a52a0d3fbd0a3bf7
D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_ext
statement_id: sha256:be297942dba1d71d921d56e5059d2544375954e34dd6e505146ebcbbed2baaff
D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.constantCoeff_encode
statement_id: sha256:7ab6eca00f6e60caaf4d33e7a1ca32c3800e019418309254c586377c79ffb747
D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode
statement_id: sha256:bb200c57b57d3db01e9c5a71120a010d1a0509f29a9046ca82c6726744329840
Declaration names below are relative to this module.
BalaFlow.flow: proof_shape: bind-only; consumer: BalaFlow.constantCoeff_flow
BalaFlow.eCoeff_flow: proof_shape: bind-only; consumer: BalaFlow.flow_derivative
BalaFlow.flow_mul: proof_shape: content; consumer: BalaFlow.existsFlowMap
BalaFlow.flow_derivative: proof_shape: bind-only; consumer: BalaFlow.flow_of_d_eq_zero
BalaFlow.flow_zero: proof_shape: bind-only; consumer: BalaFlow.existsFlowMap
BalaFlow.flow_one: proof_shape: bind-only; consumer: BalaFlow.existsFlowMap
BalaFlow.flow_add: proof_shape: bind-only; consumer: BalaFlow.existsFlowMap
BalaFlow.existsFlowMap: proof_shape: content; consumer: BalaFlow.flowMap
BalaFlow.flowMap: proof_shape: bind-only; consumer: BalaFlow.flowMapApply
BalaFlow.flowMapApply: proof_shape: bind-only; consumer: source_equation
BalaFlow.constantCoeff_flow: proof_shape: bind-only; consumer: BalaFlow.flow_of_d_eq_zero
BalaFlow.flow_of_d_eq_zero: proof_shape: bind-only; consumer: BalaA281181TotientSquarePeriod.BalaPolynomialSystem.hyperbolic_relation
BalaCRT.eventual_period_multiple: proof_shape: bind-only; consumer: BalaCRT.prime_power_periods_to_all_moduli
BalaCRT.prime_power_periods_to_all_moduli: proof_shape: bind-only; consumer: result
claim: proof_shape: bind-only; consumer: result
P: proof_shape: bind-only; consumer: prime_power_period
sequence: proof_shape: bind-only; consumer: prime_power_period
source_equation: proof_shape: content; consumer: result
prime_power_period: proof_shape: content; consumer: result
result: proof_shape: content; consumer: settling result
-/

import D5.S1.Recurrence.Residue.IntegralEGFComposition
import D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod
import D5.S1.Recurrence.Residue.QuarticEGFFixedPoint
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic

namespace D5.S1.Recurrence.Periodic.BalaA281180TotientSquarePeriod
open D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod
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

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
namespace BalaFlow
variable {A : Type*} [CommRing A] [Algebra ℤ A]
noncomputable def flow (d : Derivation ℤ A A) (ε : A →+* ℤ) (f : A) : PowerSeries ℚ :=
  D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode fun n => (ε (d^[n] f) : ℚ)
theorem eCoeff_flow (d : Derivation ℤ A A) (ε : A →+* ℤ) (f : A) (n : ℕ) :
    eCoeff (flow d ε f) n = (ε (d^[n] f) : ℚ) := by
  exact D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_encode
    (fun n => (ε (d^[n] f) : ℚ)) n
private theorem flow_mul (d : Derivation ℤ A A) (ε : A →+* ℤ) (f g : A) :
    flow d ε (f*g) = flow d ε f * flow d ε g := by
  apply D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_ext
  intro n
  rw [eCoeff_flow, eCoeff_mul]
  have hl := D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod.BalaCharP.iterate_leibniz (R:=ℤ) (A:=A) d n f g
  change d^[n] (f*g) = _ at hl
  rw [hl]
  simp only [map_sum, map_mul, eCoeff_flow, Int.cast_sum, Int.cast_mul,
    nsmul_eq_mul]
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ n := mem_range_succ_iff.mp hi
  simp only [Nat.add_sub_cancel_right,
    Nat.sub_sub_self hi', map_natCast, Int.cast_natCast]
  rw [Nat.choose_symm hi']
  ring
theorem flow_derivative (d : Derivation ℤ A A) (ε : A →+* ℤ) (f : A) :
    PowerSeries.derivative (flow d ε f) = flow d ε (d f) := by
  apply D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_ext
  intro n
  simp [eCoeff_derivative, eCoeff_flow, Function.iterate_succ_apply]
private theorem flow_zero (d : Derivation ℤ A A) (ε : A →+* ℤ) : flow d ε 0 = 0 := by
  ext n
  simp [flow, D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode, iterate_map_zero]
private theorem flow_one (d : Derivation ℤ A A) (ε : A →+* ℤ) : flow d ε 1 = 1 := by
  ext n
  cases n with
  | zero => simp [flow, D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode]
  | succ n => simp [flow, D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode, Function.iterate_succ_apply, Derivation.map_one_eq_zero, iterate_map_zero]
private theorem flow_add (d : Derivation ℤ A A) (ε : A →+* ℤ) (f g : A) :
    flow d ε (f+g) = flow d ε f + flow d ε g := by
  have hi (n : ℕ) : d^[n] (f+g) = d^[n] f + d^[n] g := by
    exact iterate_map_add d n f g
  ext n
  simp [flow, D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode, hi, add_div]
theorem existsFlowMap (d : Derivation ℤ A A) (ε : A →+* ℤ) :
    ∃ φ : A →+* PowerSeries ℚ, ∀ f : A, φ f = flow d ε f := by
  exact ⟨{ toFun := flow d ε
           map_zero' := flow_zero d ε
           map_one' := flow_one d ε
           map_add' := flow_add d ε
           map_mul' := flow_mul d ε }, fun _ => rfl⟩
noncomputable def flowMap (d : Derivation ℤ A A) (ε : A →+* ℤ) : A →+* PowerSeries ℚ :=
  Classical.choose (existsFlowMap d ε)
theorem flowMapApply (d : Derivation ℤ A A) (ε : A →+* ℤ) (f : A) :
    flowMap d ε f = flow d ε f := by
  exact Classical.choose_spec (existsFlowMap d ε) f
theorem constantCoeff_flow (d : Derivation ℤ A A) (ε : A →+* ℤ) (f : A) :
    constantCoeff (flow d ε f) = (ε f : ℚ) := by
  exact D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.constantCoeff_encode
    (fun n => (ε (d^[n] f) : ℚ))
theorem flow_of_d_eq_zero (d : Derivation ℤ A A) (ε : A →+* ℤ) (f : A)
    (hf : d f = 0) : flow d ε f = PowerSeries.C (ε f : ℚ) := by
  apply PowerSeries.derivative.ext
  · simp [flow_derivative, hf, flow_zero]
  · simp [constantCoeff_flow]
end BalaFlow
namespace BalaCRT
private theorem eventual_period_multiple (a : ℕ → ℤ) (k : ℤ) (N t : ℕ)
    (h : ∀ n, N ≤ n → Int.ModEq k (a (n+t)) (a n))
    (j n : ℕ) (hn : N ≤ n) : Int.ModEq k (a (n+t*j)) (a n) := by
  have hF : Function.Periodic (fun m : ℕ => a (m+N) % k) t := by
    intro m
    simpa only [Int.ModEq, Nat.add_right_comm] using h (m+N) (by omega)
  have hh := (hF.nat_mul j) (n-N)
  change a ((n-N+j*t)+N) % k = a ((n-N)+N) % k at hh
  rw [Nat.add_right_comm (n-N) (j*t) N, Nat.sub_add_cancel hn,
    Nat.mul_comm j t] at hh
  exact hh
theorem prime_power_periods_to_all_moduli (a : ℕ → ℤ)
    (h : ∀ p r : ℕ, p.Prime → 0 < r → ∀ n : ℕ, (p^r)^2 ≤ n →
      Int.ModEq (p^r : ℤ) (a (n+(Nat.totient (p^r))^2)) (a n)) :
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      Int.ModEq (k:ℤ) (a (n+(Nat.totient k)^2)) (a n) := by
  intro k hk
  refine ⟨k^2+1,by omega,?_⟩
  intro n hn
  rw [Int.modEq_iff_dvd,←Int.dvd_natAbs,Int.natCast_dvd_natCast]
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p r hp he
  by_cases hr : r=0
  · simp [hr]
  have hsmall : (p^r)^2 ≤ n := by
    have hle : p^r ≤ k := Nat.le_of_dvd (by omega) he
    exact (Nat.pow_le_pow_left hle 2).trans (by omega)
  have hlocal : ∀ m, (p^r)^2 ≤ m →
      Int.ModEq (p^r : ℤ) (a (m+(Nat.totient (p^r))^2)) (a m) :=
    h p r hp (by omega)
  obtain ⟨j,hj⟩ := pow_dvd_pow_of_dvd (Nat.totient_dvd_of_dvd he) 2
  have hm := eventual_period_multiple a (p^r : ℤ) ((p^r)^2)
    ((Nat.totient (p^r))^2) hlocal j n hsmall
  rw [←hj] at hm
  rw [Int.modEq_iff_dvd,←Int.dvd_natAbs] at hm
  exact_mod_cast hm
end BalaCRT

open D5.S1.Recurrence.Residue.IntegralEGFComposition
def claim : Prop :=
  ∃ S : PowerSeries ℚ,
    PowerSeries.constantCoeff S = 0 ∧
    PowerSeries.derivative S = (1 + S ^ 2) ^ 2 ∧
    ∃ a : ℕ → ℤ,
      (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = eCoeff S (2 * n - 1)) ∧
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        Int.ModEq (k : ℤ) (a (n + (Nat.totient k) ^ 2)) (a n)
open Polynomial BalaFlow
noncomputable section
private def P : Polynomial ℤ := (1+Polynomial.X^2)^2
private def sequence (n : ℕ) : ℤ := ((Polynomial.mkDerivation ℤ P)^[2*n-1] Polynomial.X).coeff 0
private theorem source_equation :
    PowerSeries.derivative (flow (Polynomial.mkDerivation ℤ P) Polynomial.constantCoeff Polynomial.X) =
      (1+(flow (Polynomial.mkDerivation ℤ P) Polynomial.constantCoeff Polynomial.X)^2)^2 := by
  rw [flow_derivative,show (Polynomial.mkDerivation ℤ P) Polynomial.X=P from Polynomial.mkDerivation_X ℤ P]
  rw [← flowMapApply (Polynomial.mkDerivation ℤ P) Polynomial.constantCoeff P]
  simp only [P,map_pow,map_add,map_one]
  simp only [flowMapApply]
private theorem prime_power_period (p r : ℕ) (hp : p.Prime) (hr : 0<r)
    (n : ℕ) (hn : (p^r)^2 ≤ n) :
    Int.ModEq (p^r : ℤ) (sequence (n+(Nat.totient (p^r))^2)) (sequence n) := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  letI : Fact p.Prime := ⟨hp⟩
  change (p^(s+1))^2≤n at hn
  have hP : P.coeff 0=1 := by
    change Polynomial.constantCoeff ((1+Polynomial.X^2)^2 : Polynomial ℤ)=1
    rw [map_pow,map_add,map_one,map_pow]
    norm_num [Polynomial.constantCoeff]
  have hu : p^(2*s+1) ≤ (p^(s+1))^2 := by
    rw [←pow_mul]
    apply Nat.pow_le_pow_right hp.pos
    omega
  have hn0 : 1≤n := by
    have hh := pow_pos (pow_pos hp.pos (s+1)) 2
    omega
  have hu' : p^(2*s+1)≤n := hu.trans hn
  have hm : p^(2*s+1)≤2*n-1 := by omega
  have h1 := D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod.BalaTruncated.prime_power_derivative_period (p:=p) P hP s Polynomial.X
    (2*n-1+(Nat.totient (p^(s+1)))^2) (by omega)
  have h2 := D5.S1.Recurrence.Periodic.AutonomousDerivationTotientSquarePeriod.BalaTruncated.prime_power_derivative_period (p:=p) P hP s Polynomial.X (2*n-1) hm
  have he : 2*(n+(Nat.totient (p^(s+1)))^2)-1 =
    (2*n-1+(Nat.totient (p^(s+1)))^2)+(Nat.totient (p^(s+1)))^2 := by omega
  simpa only [sequence,he] using h1.trans h2
theorem result : claim := by
  refine ⟨flow (Polynomial.mkDerivation ℤ P) Polynomial.constantCoeff Polynomial.X,?_,source_equation,sequence,?_,?_⟩
  · simp [constantCoeff_flow]
  · intro n _
    exact (eCoeff_flow (Polynomial.mkDerivation ℤ P) Polynomial.constantCoeff Polynomial.X (2*n-1)).symm
  · exact BalaCRT.prime_power_periods_to_all_moduli sequence prime_power_period
end
end D5.S1.Recurrence.Periodic.BalaA281180TotientSquarePeriod
