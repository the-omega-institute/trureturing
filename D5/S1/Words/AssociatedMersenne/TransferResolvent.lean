/- GID: D5/S1/Words/AssociatedMersenne/TransferResolvent
   generality: G
   mirror-B: D5/B/S1/Words/AssociatedMersenne/TransferResolvent
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A coefficientwise finite matrix resolvent gives the marked trace derivative. -/

/-
admission_basis: escape-witness
Module content theorem: trace_marked_coefficient
Run marks: IsOneRunStart permits r = 0; IsMarkedStart requires positive r.
Singleton correction: [(r,1)] has provisionalDegree min r 2 + 1 and tupleDegree min r 2.
The transfer correction is X * (1 - Y) * Rser before marking and
X * derivative (X * (1 - Y) * Rser) after marking.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14898
Direct frozen dependencies:
  none (the other D5 imports belong to this delivery).
Declarations:
  A_factor: proof_shape: bind-only; escape_witness: none; consumer: TransferResolvent.A_pow_factor
  A_pow_factor: proof_shape: bind-only; escape_witness: none; consumer: TransferResolvent.A_pow_low_coeff
  A_pow_low_coeff: proof_shape: bind-only; escape_witness: none; consumer: TransferResolvent.coeff_matrixGeom_partial
  trace_A_pow_low_coeff: proof_shape: bind-only; escape_witness: none; consumer: TransferResolvent.coeff_euler_transferTrace
  dMatrix_one: proof_shape: bind-only; escape_witness: none; consumer: TransferResolvent.dMatrix_one_sub_A
  dMatrix_mul: proof_shape: bind-only; escape_witness: none; consumer: TransferResolvent.dMatrix_pow
  dMatrix_trace: proof_shape: bind-only; escape_witness: none; consumer: TransferResolvent.derivative_trace_pow
  dMatrix_pow: proof_shape: content; escape_witness: TransferResolvent.dMatrix_pow;
  derivative_trace_pow: proof_shape: content; escape_witness: TransferResolvent.derivative_trace_pow;
  coeff_matrixGeom_partial: proof_shape: bind-only; escape_witness: none; consumer: TransferResolvent.coeff_transferTrace_partial
  matrixPartial_identity: proof_shape: bind-only; escape_witness: none; consumer: TransferResolvent.matrixGeom_inverse
  coeff_mul_matrixGeom_partial: proof_shape: bind-only; escape_witness: none; consumer: TransferResolvent.matrixGeom_inverse
  matrixGeom_inverse: proof_shape: bind-only; escape_witness: none; consumer: TransferResolvent.det_smul_matrixGeom
  det_smul_matrixGeom: proof_shape: bind-only; escape_witness: none; consumer: TransferResolvent.transfer_trace_cleared
  derivative_det_two: proof_shape: bind-only; escape_witness: none; consumer: TransferResolvent.transfer_trace_cleared
  dMatrix_one_sub_A: proof_shape: bind-only; escape_witness: none; consumer: TransferResolvent.transfer_trace_cleared
  transfer_trace_cleared: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.transferTrace_formula
  coeff_euler: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.marked_word_coefficient
  trace_marked_coefficient: proof_shape: content; escape_witness: TransferResolvent.trace_marked_coefficient;
  coeff_transferTrace_partial: proof_shape: bind-only; escape_witness: none; consumer: TransferResolvent.coeff_euler_transferTrace
  coeff_euler_transferTrace: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.degSeries_eq_graphTransferSeries
-/

import D5.S1.Words.AssociatedMersenne.TransferTuples

import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.LinearAlgebra.Matrix.Adjugate

open D5.S1.Words.AssociatedMersenne.CircularWords
open D5.S1.Words.AssociatedMersenne.RunTupleBijection
open D5.S1.Words.AssociatedMersenne.SingleRunDegrees
open D5.S1.Words.AssociatedMersenne.MultiRunDegrees
open D5.S1.Words.AssociatedMersenne.MarkedDegreeEnumeration
open D5.S1.Words.AssociatedMersenne.TransferTuples

namespace D5.S1.Words.AssociatedMersenne.TransferResolvent

open scoped BigOperators

open Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

noncomputable section

local notation "X" => (PowerSeries.X : (PowerSeries (Polynomial ℤ)))

local notation "Y" => (PowerSeries.C (Polynomial.X : Polynomial ℤ) : (PowerSeries (Polynomial ℤ)))

set_option maxHeartbeats 200000

local notation "D" => PowerSeries.derivative (Polynomial ℤ)

set_option maxRecDepth 2048

private def Rtail : (PowerSeries (Polynomial ℤ)) := Y + X^2*Y^2*geom (X^2)

private def B : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ)) :=
  !![Rtail,Rtail*Qser;Rtail,Rtail*Y*Qser]

private lemma A_factor : A = X^3 • B := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [A,B,Rtail,Rser,Matrix.smul_apply,smul_eq_mul] <;> ring

private lemma A_pow_factor (ell : Nat) : A^ell = X^(3*ell) • B^ell := by
  rw [A_factor,smul_pow,← pow_mul]

private theorem A_pow_low_coeff (ell n : Nat) (hn : n < 3*ell) (i j : Fin 2) :
    PowerSeries.coeff n ((A^ell) i j) = 0 := by
  rw [A_pow_factor]
  simp [Matrix.smul_apply,smul_eq_mul,PowerSeries.coeff_X_pow_mul',show ¬3*ell≤n by omega]

private lemma trace_A_pow_low_coeff (ell n : Nat) (hn : n < 3*ell) :
    PowerSeries.coeff n (Matrix.trace (A^ell)) = 0 := by
  simp only [Matrix.trace,map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  exact A_pow_low_coeff ell n hn i i

def dMatrix (M : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ))) : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ)) :=
  fun i j => dsimp% only [Matrix.map_apply] ((M.map D) i j)

private lemma dMatrix_one : dMatrix (1 : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ))) = 0 := by
  funext i j
  by_cases hij : i=j <;> simp [dMatrix,Matrix.one_apply,hij,PowerSeries.derivative_one]

private lemma dMatrix_mul (M N : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ))) :
    dMatrix (M*N) = dMatrix M*N+M*dMatrix N := by
  funext i j
  simp [dMatrix,Matrix.mul_apply,Derivation.leibniz,smul_eq_mul,Finset.sum_add_distrib]
  ring

private lemma dMatrix_trace (M : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ))) :
    D (Matrix.trace M) = Matrix.trace (dMatrix M) := by simp [Matrix.trace,dMatrix]

private lemma dMatrix_pow (M : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ))) (n : Nat) :
    dMatrix (M^n) = ∑ q ∈ Finset.range n, M^q*dMatrix M*M^(n-1-q) := by
  induction n with
  | zero => simp [dMatrix_one]
  | succ n ih =>
    rw [pow_succ]
    rw [dMatrix_mul]
    rw [ih]
    rw [Finset.sum_mul]
    rw [Finset.sum_range_succ]
    simp only [Nat.add_one_sub_one,Nat.sub_self,pow_zero,mul_one]
    apply congrArg (fun K : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ)) => K+M^n*dMatrix M)
    apply Finset.sum_congr rfl
    intro q hq
    have he : n-1-q+1 = n-q := by have := Finset.mem_range.mp hq; omega
    rw [Matrix.mul_assoc,← pow_succ,he]

private theorem derivative_trace_pow (M : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ))) (n : Nat) :
    D (Matrix.trace (M^n)) = (n:(PowerSeries (Polynomial ℤ)))*Matrix.trace (M^(n-1)*dMatrix M) := by
  rw [dMatrix_trace,dMatrix_pow,Matrix.trace_sum]
  have hsum : ∀ q ∈ Finset.range n,
      Matrix.trace (M^q*dMatrix M*M^(n-1-q)) = Matrix.trace (M^(n-1)*dMatrix M) := by
    intro q hq
    rw [Matrix.trace_mul_cycle,← pow_add]
    have he : n-1-q+q = n-1 := by have := Finset.mem_range.mp hq; omega
    rw [he]
  simp_rw [Finset.sum_congr rfl hsum]
  simp [nsmul_eq_mul]

private def matrixPartial (n : Nat) : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ)) :=
  ∑ ell ∈ Finset.range (n+1), A^ell

def matrixGeom : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ)) :=
  fun i j => PowerSeries.mk (fun n =>
    ∑ ell ∈ Finset.range (n+1), PowerSeries.coeff n ((A^ell) i j))

private lemma coeff_matrixGeom_partial (m n : Nat) (hm : m ≤ n) (i j : Fin 2) :
    PowerSeries.coeff m (matrixGeom i j) = PowerSeries.coeff m (matrixPartial n i j) := by
  simp only [matrixGeom,PowerSeries.coeff_mk,matrixPartial,Matrix.sum_apply,map_sum]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro ell hell hel0
  have hn := Finset.mem_range.mp hell
  have hl : m+1 ≤ ell := by simpa only [Finset.mem_range,not_lt] using hel0
  exact A_pow_low_coeff ell m (by omega) i j

private lemma matrixPartial_identity (n : Nat) : (1-A)*matrixPartial n = 1-A^(n+1) := by
  exact mul_neg_geom_sum A (n+1)

private lemma coeff_mul_matrixGeom_partial (M : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ))) (n : Nat) (i j : Fin 2) :
    PowerSeries.coeff n ((M*matrixGeom) i j) =
      PowerSeries.coeff n ((M*matrixPartial n) i j) := by
  simp only [Matrix.mul_apply,map_sum,PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [coeff_matrixGeom_partial p.2 n (by omega)]

theorem matrixGeom_inverse : (1-A)*matrixGeom = 1 := by
  funext i j
  apply PowerSeries.ext
  intro n
  rw [coeff_mul_matrixGeom_partial (1-A) n i j,matrixPartial_identity]
  simp only [Matrix.sub_apply,map_sub]
  rw [A_pow_low_coeff (n+1) n (by omega),sub_zero]

def transferDet : (PowerSeries (Polynomial ℤ)) := Matrix.det (1-A)

def transferTrace : (PowerSeries (Polynomial ℤ)) := Matrix.trace (matrixGeom*dMatrix A)

private lemma det_smul_matrixGeom : transferDet • matrixGeom = Matrix.adjugate (1-A) := by
  calc
    _ = (Matrix.adjugate (1-A)*(1-A))*matrixGeom := by
      rw [Matrix.adjugate_mul,Matrix.smul_mul,one_mul]
      rfl
    _ = _ := by rw [Matrix.mul_assoc,matrixGeom_inverse,mul_one]

private lemma derivative_det_two (M : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ))) :
    D (Matrix.det M) = Matrix.trace (Matrix.adjugate M*dMatrix M) := by
  simp [Matrix.det_fin_two,Matrix.adjugate_fin_two,Matrix.trace,Matrix.mul_apply,
    Fin.sum_univ_two,Matrix.vecMul,dotProduct,dMatrix,Derivation.leibniz,smul_eq_mul]
  ring

private lemma dMatrix_one_sub_A : dMatrix (1-A) = -dMatrix A := by
  funext i j
  simp only [dMatrix,Matrix.sub_apply,map_sub,Matrix.neg_apply]
  have h := congrFun (congrFun dMatrix_one i) j
  change D ((1 : Matrix (Fin 2) (Fin 2) (PowerSeries (Polynomial ℤ))) i j)=0 at h
  rw [h,zero_sub]

theorem transfer_trace_cleared : transferDet*transferTrace = -D transferDet := by
  change transferDet*Matrix.trace (matrixGeom*dMatrix A) = -D (Matrix.det (1-A))
  rw [← smul_eq_mul,← Matrix.trace_smul,← Matrix.smul_mul,det_smul_matrixGeom]
  rw [derivative_det_two,dMatrix_one_sub_A,Matrix.mul_neg,Matrix.trace_neg,neg_neg]

lemma coeff_euler (f : (PowerSeries (Polynomial ℤ))) (n : Nat) :
    PowerSeries.coeff n (X*D f) = (n:(Polynomial ℤ))*PowerSeries.coeff n f := by
  cases n with
  | zero => simp
  | succ n => simp [PowerSeries.coeff_derivative,mul_comm]

theorem trace_marked_coefficient (ell n : Nat) :
    ((ell+1:(Polynomial ℤ))*PowerSeries.coeff n (X*Matrix.trace (A^ell*dMatrix A))) =
      (n:(Polynomial ℤ))*PowerSeries.coeff n (Matrix.trace (A^(ell+1))) := by
  have h := congrArg (fun f : (PowerSeries (Polynomial ℤ)) => PowerSeries.coeff n (X*f))
    (derivative_trace_pow A (ell+1))
  rw [coeff_euler] at h
  have he : (ell+1:(PowerSeries (Polynomial ℤ)))=PowerSeries.C (ell+1:(Polynomial ℤ)) := by simp
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at h
  have hp : X*((ell+1:(PowerSeries (Polynomial ℤ)))*Matrix.trace (A^ell*dMatrix A)) =
      PowerSeries.C (ell+1:(Polynomial ℤ))*(X*Matrix.trace (A^ell*dMatrix A)) := by rw [he]; ring
  rw [hp,PowerSeries.coeff_C_mul] at h
  exact h.symm

private lemma coeff_transferTrace_partial (n : Nat) :
    PowerSeries.coeff n transferTrace =
      ∑ ell ∈ Finset.range (n+1),
        PowerSeries.coeff n (Matrix.trace (A^ell*dMatrix A)) := by
  unfold transferTrace
  simp only [Matrix.trace,Matrix.diag,map_sum]
  have hm (i : Fin 2) :
      PowerSeries.coeff n ((matrixGeom*dMatrix A) i i) =
      PowerSeries.coeff n ((matrixPartial n*dMatrix A) i i) := by
    rw [Matrix.mul_apply,Matrix.mul_apply,map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [coeff_matrixGeom_partial p.1 n (by omega)]
  simp_rw [hm]
  simp only [matrixPartial,Finset.sum_mul,Matrix.sum_apply,map_sum]
  rw [Finset.sum_comm]

theorem coeff_euler_transferTrace (n : Nat) :
    PowerSeries.coeff n (X*transferTrace) =
      ∑ ell ∈ Finset.range (n+1),
        PowerSeries.coeff n (X*Matrix.trace (A^ell*dMatrix A)) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [show X=(PowerSeries.X : (PowerSeries (Polynomial ℤ)))^1 from (pow_one _).symm]
    simp only [PowerSeries.coeff_X_pow_mul]
    rw [coeff_transferTrace_partial]
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro ell hell hel0
    have hell' := Finset.mem_range.mp hell
    have hel0' : n+1≤ell := by simpa only [Finset.mem_range,not_lt] using hel0
    have hc := trace_marked_coefficient ell (n+1)
    have hz := trace_A_pow_low_coeff (ell+1) (n+1) (by omega)
    rw [hz,mul_zero] at hc
    have he : (ell+1:(Polynomial ℤ)) ≠ 0 := by exact_mod_cast (show (ell+1:ℤ)≠0 by omega)
    simpa using (mul_eq_zero.mp hc).resolve_left he

end
end TransferResolvent
