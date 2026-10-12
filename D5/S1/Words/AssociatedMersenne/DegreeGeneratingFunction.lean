/- GID: D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction
   generality: G
   mirror-B: D5/B/S1/Words/AssociatedMersenne/DegreeGeneratingFunction
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The Associated Mersenne degree series satisfies its explicit rational identity. -/

/-
admission_basis: open-problem-resolution (#14818; Proved)
Module content theorem: result
Run marks: IsOneRunStart permits r = 0; IsMarkedStart requires positive r.
Singleton correction: [(r,1)] has provisionalDegree min r 2 + 1 and tupleDegree min r 2.
The transfer correction is X * (1 - Y) * Rser before marking and
X * derivative (X * (1 - Y) * Rser) after marking.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14898
Direct frozen dependencies:
  none (the other D5 imports belong to this delivery).
Declarations:
  denCoeff_large: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.DEN_eq_polynomial
  numCoeff_large: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.NUM_eq_polynomial
  DEN_eq_polynomial: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.DEN_factor_series
  NUM_eq_polynomial: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.NUM_factor_series
  denPolynomial_factor: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.DEN_factor_series
  numPolynomial_factor: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.NUM_factor_series
  coeff_degSeries: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.degSeries_eq_graphTransferSeries
  aS_uS: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.closedSeries_identity
  pS_constant: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.pS_vS
  pS_vS: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.closedSeries_identity
  DEN_factor_series: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.closedSeries_identity
  NUM_factor_series: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.closedSeries_identity
  closedSeries_identity: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.graphTransferSeries_identity
  cS_gS: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.transferTrace_formula
  Rser_aS: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.correction_formula
  transferDet_factor: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.transferTrace_formula
  transferTrace_formula: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.graphTransferSeries_identity
  zeroSeries_cancel: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.graphTransferSeries_identity
  correction_formula: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.graphTransferSeries_identity
  graphTransferSeries_identity: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.result
  coeff_gS: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.coeff_zero_tail
  coeff_zero_tail: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.coeff_zeroSeries
  coeff_zeroSeries: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.degSeries_eq_graphTransferSeries
  runPolynomial_gt: proof_shape: bind-only; escape_witness: none; consumer: DegreeGeneratingFunction.degSeries_eq_graphTransferSeries
  marked_word_coefficient: proof_shape: content; escape_witness: DegreeGeneratingFunction.marked_word_coefficient;
  degSeries_eq_graphTransferSeries: proof_shape: content; escape_witness: DegreeGeneratingFunction.degSeries_eq_graphTransferSeries;
  result: proof_shape: content; escape_witness: DegreeGeneratingFunction.result;
-/

import D5.S1.Words.AssociatedMersenne.TransferResolvent

open D5.S1.Words.AssociatedMersenne.CircularWords
open D5.S1.Words.AssociatedMersenne.RunTupleBijection
open D5.S1.Words.AssociatedMersenne.SingleRunDegrees
open D5.S1.Words.AssociatedMersenne.MultiRunDegrees
open D5.S1.Words.AssociatedMersenne.MarkedDegreeEnumeration
open D5.S1.Words.AssociatedMersenne.TransferTuples
open D5.S1.Words.AssociatedMersenne.TransferResolvent

namespace D5.S1.Words.AssociatedMersenne.DegreeGeneratingFunction

open scoped BigOperators

open Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

noncomputable section

set_option maxRecDepth 4096

local notation "X" => (PowerSeries.X : (PowerSeries (Polynomial ℤ)))

local notation "Y" => (PowerSeries.C (Polynomial.X : Polynomial ℤ) : (PowerSeries (Polynomial ℤ)))

local notation "D" => PowerSeries.derivative (Polynomial ℤ)

noncomputable def degSeries : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk (fun n => ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (N n k : ℤ) * Polynomial.X ^ k)

noncomputable def numCoeff (n : Nat) : Polynomial ℤ :=
  let y : Polynomial ℤ := Polynomial.X
  match n with
    | 0 => 1
    | 1 => 1 - y
    | 2 => -y - 3
    | 3 => y ^ 3 + 5 * y - 4
    | 4 => -3 * y ^ 2 + 7 * y + 2
    | 5 => y ^ 3 - 11 * y + 6
    | 6 => -5 * y ^ 3 + 17 * y ^ 2 - 18 * y + 2
    | 7 => 7 * y ^ 4 - 22 * y ^ 3 + 7 * y ^ 2 + 14 * y - 4
    | 8 => -y ^ 4 + 15 * y ^ 3 - 32 * y ^ 2 + 22 * y - 3
    | 9 => -y ^ 5 - 24 * y ^ 4 + 57 * y ^ 3 - 22 * y ^ 2 - 11 * y + 1
    | 10 => -2 * y ^ 5 + 8 * y ^ 4 - 21 * y ^ 3 + 27 * y ^ 2 - 13 * y + 1
    | 11 => -2 * y ^ 6 - 2 * y ^ 5 + 43 * y ^ 4 - 71 * y ^ 3 + 27 * y ^ 2 + 5 * y
    | 12 => -y ^ 6 + 8 * y ^ 5 - 19 * y ^ 4 + 21 * y ^ 3 - 12 * y ^ 2 + 3 * y
    | 13 => -y ^ 7 - 7 * y ^ 6 + 39 * y ^ 5 - 72 * y ^ 4 + 59 * y ^ 3 - 17 * y ^ 2 - y
    | 14 => 2 * y ^ 6 - 10 * y ^ 5 + 18 * y ^ 4 - 14 * y ^ 3 + 4 * y ^ 2
    | 15 => -14 * y ^ 7 + 64 * y ^ 6 - 114 * y ^ 5 + 98 * y ^ 4 - 40 * y ^ 3 + 6 * y ^ 2
    | 16 => -y ^ 6 + 4 * y ^ 5 - 6 * y ^ 4 + 4 * y ^ 3 - y ^ 2
    | 17 => -6 * y ^ 8 + 39 * y ^ 7 - 97 * y ^ 6 + 118 * y ^ 5 - 72 * y ^ 4 + 19 * y ^ 3 - y ^ 2
    | 19 => 4 * y ^ 8 - 20 * y ^ 7 + 40 * y ^ 6 - 40 * y ^ 5 + 20 * y ^ 4 - 4 * y ^ 3
    | _ => 0

noncomputable def denCoeff (n : Nat) : Polynomial ℤ :=
  let y : Polynomial ℤ := Polynomial.X
  match n with
    | 0 => 1
    | 1 => -y
    | 2 => -4
    | 3 => 3 * y
    | 4 => 6
    | 5 => -y ^ 2 - 2 * y
    | 6 => -4
    | 7 => y ^ 3 + 2 * y ^ 2 - 2 * y
    | 8 => 1
    | 9 => 2 * y ^ 4 - 6 * y ^ 3 + y ^ 2 + 3 * y
    | 11 => y ^ 5 - 7 * y ^ 4 + 12 * y ^ 3 - 5 * y ^ 2 - y
    | 13 => -2 * y ^ 5 + 8 * y ^ 4 - 10 * y ^ 3 + 4 * y ^ 2
    | 15 => y ^ 5 - 3 * y ^ 4 + 3 * y ^ 3 - y ^ 2
    | _ => 0

noncomputable def NUM : PowerSeries (Polynomial ℤ) := PowerSeries.mk numCoeff

noncomputable def DEN : PowerSeries (Polynomial ℤ) := PowerSeries.mk denCoeff

def claim : Prop := degSeries * DEN = NUM

section AlgebraSymbols
local notation "x" => (Polynomial.X : Polynomial (Polynomial ℤ))
local notation "y" => (Polynomial.C (Polynomial.X : Polynomial ℤ) : Polynomial (Polynomial ℤ))

private def aa : (Polynomial (Polynomial ℤ)) := 1 - x ^ 2

private def bb : (Polynomial (Polynomial ℤ)) := x ^ 3 * y * aa + x ^ 5 * y ^ 2

private def pp : (Polynomial (Polynomial ℤ)) := (1 - x * y) * aa ^ 2 - bb * aa + x * (y - 1) * bb ^ 2

private def denPolynomial : (Polynomial (Polynomial ℤ)) := ∑ j ∈ Finset.range 16, Polynomial.monomial j (denCoeff j)

private def numPolynomial : (Polynomial (Polynomial ℤ)) := ∑ j ∈ Finset.range 20, Polynomial.monomial j (numCoeff j)

private lemma denCoeff_large (n : Nat) (hn : 15 < n) : denCoeff n = 0 := by
  unfold denCoeff
  split <;> first | omega | rfl

private lemma numCoeff_large (n : Nat) (hn : 19 < n) : numCoeff n = 0 := by
  unfold numCoeff
  split <;> first | omega | rfl

private lemma DEN_eq_polynomial : DEN = (denPolynomial : PowerSeries (Polynomial ℤ)) := by
  apply PowerSeries.ext
  intro n
  simp only [DEN, PowerSeries.coeff_mk, Polynomial.coeff_coe, denPolynomial,
    Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hn : n < 16
  · simp [Finset.sum_ite_eq', hn]
  · simp [Finset.sum_ite_eq', hn, denCoeff_large n (by omega)]

private lemma NUM_eq_polynomial : NUM = (numPolynomial : PowerSeries (Polynomial ℤ)) := by
  apply PowerSeries.ext
  intro n
  simp only [NUM, PowerSeries.coeff_mk, Polynomial.coeff_coe, numPolynomial,
    Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hn : n < 20
  · simp [Finset.sum_ite_eq', hn]
  · simp [Finset.sum_ite_eq', hn, numCoeff_large n (by omega)]

private lemma denPolynomial_factor : denPolynomial = pp * aa ^ 2 := by
  norm_num [denPolynomial, denCoeff, Finset.sum_range_succ, pp, bb, aa,
    ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_ofNat]
  ring

private lemma numPolynomial_factor : numPolynomial =
    (1 + x * (1-y) + x^2 * (1-y^2)) * pp * aa^2 - x * pp.derivative * aa^2 +
    2*x*aa.derivative*pp*aa +
    x*(1-y)*pp*(bb*aa + x*(bb.derivative*aa-bb*aa.derivative)) := by
  norm_num [numPolynomial, numCoeff, Finset.sum_range_succ, pp, bb, aa,
    ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.C_ofNat]
  ring

end AlgebraSymbols

private lemma coeff_degSeries (n : Nat) : PowerSeries.coeff n degSeries = degreePolynomial n := by
  simp [degSeries, degreePolynomial]

private def vS : (PowerSeries (Polynomial ℤ)) := PowerSeries.invOfUnit (pp : PowerSeries (Polynomial ℤ)) 1

private def closedSeries : (PowerSeries (Polynomial ℤ)) :=
  (1 + X*(1-Y) + X^2*(1-Y^2)) - X*(D (pp : PowerSeries (Polynomial ℤ)))*vS + 2*X*(D (aa : PowerSeries (Polynomial ℤ)))*(geom (X^2)) +
    X*(1-Y)*((bb : PowerSeries (Polynomial ℤ))*(aa : PowerSeries (Polynomial ℤ)) + X*((D (bb : PowerSeries (Polynomial ℤ)))*(aa : PowerSeries (Polynomial ℤ))-(bb : PowerSeries (Polynomial ℤ))*(D (aa : PowerSeries (Polynomial ℤ)))))*(geom (X^2))^2

private lemma aS_uS : (aa : PowerSeries (Polynomial ℤ)) * (geom (X^2)) = 1 := by
  have ha : (aa : PowerSeries (Polynomial ℤ)) = 1-X^2 := by simp [ aa]
  rw [ha]
  exact geom_X2

private lemma pS_constant : PowerSeries.constantCoeff (pp : PowerSeries (Polynomial ℤ)) = 1 := by
  simp [ pp, bb, aa]

private lemma pS_vS : (pp : PowerSeries (Polynomial ℤ))*vS = 1 :=
  PowerSeries.mul_invOfUnit (pp : PowerSeries (Polynomial ℤ)) 1 (by simpa using pS_constant)

private lemma DEN_factor_series : DEN = (pp : PowerSeries (Polynomial ℤ))*(aa : PowerSeries (Polynomial ℤ))^2 := by
  rw [DEN_eq_polynomial, denPolynomial_factor]
  simp

private lemma NUM_factor_series : NUM =
    (1+X*(1-Y)+X^2*(1-Y^2))*(pp : PowerSeries (Polynomial ℤ))*(aa : PowerSeries (Polynomial ℤ))^2-X*(D (pp : PowerSeries (Polynomial ℤ)))*(aa : PowerSeries (Polynomial ℤ))^2+
      2*X*(D (aa : PowerSeries (Polynomial ℤ)))*(pp : PowerSeries (Polynomial ℤ))*(aa : PowerSeries (Polynomial ℤ))+
      X*(1-Y)*(pp : PowerSeries (Polynomial ℤ))*((bb : PowerSeries (Polynomial ℤ))*(aa : PowerSeries (Polynomial ℤ))+X*((D (bb : PowerSeries (Polynomial ℤ)))*(aa : PowerSeries (Polynomial ℤ))-(bb : PowerSeries (Polynomial ℤ))*(D (aa : PowerSeries (Polynomial ℤ))))) := by
  rw [NUM_eq_polynomial, numPolynomial_factor]
  norm_num [ PowerSeries.derivative_coe]
  left; left; left
  exact map_ofNat (Polynomial.coeToPowerSeries.ringHom : (Polynomial (Polynomial ℤ)) →+* (PowerSeries (Polynomial ℤ))) 2

private theorem closedSeries_identity : closedSeries * DEN = NUM := by
  rw [DEN_factor_series, NUM_factor_series]
  unfold closedSeries
  have ha := aS_uS
  have hp := pS_vS
  linear_combination
    (-X*(D (pp : PowerSeries (Polynomial ℤ)))*(aa : PowerSeries (Polynomial ℤ))^2) * hp +
    (2*X*(D (aa : PowerSeries (Polynomial ℤ)))*(pp : PowerSeries (Polynomial ℤ))*(aa : PowerSeries (Polynomial ℤ)) +
      X*(1-Y)*(pp : PowerSeries (Polynomial ℤ))*((bb : PowerSeries (Polynomial ℤ))*(aa : PowerSeries (Polynomial ℤ))+X*((D (bb : PowerSeries (Polynomial ℤ)))*(aa : PowerSeries (Polynomial ℤ))-(bb : PowerSeries (Polynomial ℤ))*(D (aa : PowerSeries (Polynomial ℤ)))))*((aa : PowerSeries (Polynomial ℤ))*(geom (X^2))+1)) * ha

private def cS : (PowerSeries (Polynomial ℤ)) := 1-Y*X

private def zeroSeries : (PowerSeries (Polynomial ℤ)) := 1+X+X^2+(Y*X)^3*(geom (Y*X))

private def graphTransferSeries : (PowerSeries (Polynomial ℤ)) :=
  zeroSeries + X*transferTrace + X*(D (X*(1-Y)*Rser))

private lemma cS_gS : cS*(geom (Y*X))=1 := geom_YX

private lemma Rser_aS : Rser*(aa : PowerSeries (Polynomial ℤ))=(bb : PowerSeries (Polynomial ℤ)) := by
  have ha : (aa : PowerSeries (Polynomial ℤ))=1-X^2 := by simp [aa]
  have h := geom_X2
  unfold Rser
  rw [ha]
  simp only [bb,aa,Polynomial.coe_add,Polynomial.coe_mul,Polynomial.coe_sub,
    Polynomial.coe_pow,Polynomial.coe_X,Polynomial.coe_C,Polynomial.coe_one]
  linear_combination X^5*Y^2*h

private lemma transferDet_factor : transferDet*(aa : PowerSeries (Polynomial ℤ))^2*cS=(pp : PowerSeries (Polynomial ℤ)) := by
  have hq : Qser*cS=X := by
    dsimp [Qser,cS]
    linear_combination X*geom_YX
  have hd := det_A
  change transferDet = _ at hd
  rw [hd]
  have hp : (pp : PowerSeries (Polynomial ℤ))=cS*(aa : PowerSeries (Polynomial ℤ))^2-(bb : PowerSeries (Polynomial ℤ))*(aa : PowerSeries (Polynomial ℤ))+X*(Y-1)*(bb : PowerSeries (Polynomial ℤ))^2 := by
    simp only [pp,cS,aa,Polynomial.coe_add,Polynomial.coe_mul,Polynomial.coe_sub,
      Polynomial.coe_pow,Polynomial.coe_X,Polynomial.coe_C,Polynomial.coe_one]
    ring
  rw [hp]
  dsimp [cS] at *
  linear_combination
    (-Rser*(aa : PowerSeries (Polynomial ℤ))^2*Y+Rser^2*(aa : PowerSeries (Polynomial ℤ))^2*(Y-1))*hq +
    (-(aa : PowerSeries (Polynomial ℤ))+X*(Y-1)*(Rser*(aa : PowerSeries (Polynomial ℤ))+(bb : PowerSeries (Polynomial ℤ))))*Rser_aS

private lemma transferTrace_formula :
    transferTrace = -(D (pp : PowerSeries (Polynomial ℤ)))*vS+2*(D (aa : PowerSeries (Polynomial ℤ)))*(geom (X^2))-Y*(geom (Y*X)) := by
  have hd := transferDet_factor
  have hder := congrArg (fun f : (PowerSeries (Polynomial ℤ)) => D f) hd
  simp only [Derivation.leibniz,map_sub,map_one,map_mul,PowerSeries.derivative_X,
    PowerSeries.derivative_C,smul_eq_mul,PowerSeries.derivative_pow] at hder
  have hc : D cS = -Y := by simp [cS,Derivation.leibniz,smul_eq_mul]
  rw [hc] at hder
  have ht : transferTrace*(pp : PowerSeries (Polynomial ℤ)) = -D (pp : PowerSeries (Polynomial ℤ))+2*(D (aa : PowerSeries (Polynomial ℤ)))*transferDet*(aa : PowerSeries (Polynomial ℤ))*cS-Y*transferDet*(aa : PowerSeries (Polynomial ℤ))^2 := by
    calc
      transferTrace*(pp : PowerSeries (Polynomial ℤ)) = -D transferDet*(aa : PowerSeries (Polynomial ℤ))^2*cS := by
        rw [← hd]
        linear_combination ((aa : PowerSeries (Polynomial ℤ))^2*cS)*transfer_trace_cleared
      _ = _ := by linear_combination -hder
  have ha : (D (aa : PowerSeries (Polynomial ℤ)))*(geom (X^2))*(pp : PowerSeries (Polynomial ℤ)) = (D (aa : PowerSeries (Polynomial ℤ)))*transferDet*(aa : PowerSeries (Polynomial ℤ))*cS := by
    rw [← hd]
    linear_combination (D (aa : PowerSeries (Polynomial ℤ)))*transferDet*(aa : PowerSeries (Polynomial ℤ))*cS*aS_uS
  have hg : Y*(geom (Y*X))*(pp : PowerSeries (Polynomial ℤ))=Y*transferDet*(aa : PowerSeries (Polynomial ℤ))^2 := by
    rw [← hd]
    linear_combination Y*transferDet*(aa : PowerSeries (Polynomial ℤ))^2*cS_gS
  have hmul : transferTrace*(pp : PowerSeries (Polynomial ℤ)) = (-(D (pp : PowerSeries (Polynomial ℤ)))*vS+2*(D (aa : PowerSeries (Polynomial ℤ)))*(geom (X^2))-Y*(geom (Y*X)))*(pp : PowerSeries (Polynomial ℤ)) := by
    linear_combination ht + (D (pp : PowerSeries (Polynomial ℤ)))*pS_vS - 2*ha + hg
  calc
    transferTrace = (transferTrace*(pp : PowerSeries (Polynomial ℤ)))*vS := by rw [mul_assoc,pS_vS,mul_one]
    _ = _ := by rw [hmul,mul_assoc,pS_vS,mul_one]

private lemma zeroSeries_cancel : zeroSeries-X*Y*(geom (Y*X)) = 1+X*(1-Y)+X^2*(1-Y^2) := by
  have hg := cS_gS
  dsimp [zeroSeries,cS] at *
  linear_combination -(Y*X+Y^2*X^2)*hg

private lemma correction_formula :
    X*(D (X*(1-Y)*Rser)) =
      X*(1-Y)*((bb : PowerSeries (Polynomial ℤ))*(aa : PowerSeries (Polynomial ℤ))+X*((D (bb : PowerSeries (Polynomial ℤ)))*(aa : PowerSeries (Polynomial ℤ))-(bb : PowerSeries (Polynomial ℤ))*(D (aa : PowerSeries (Polynomial ℤ)))))*(geom (X^2))^2 := by
  have hr : Rser=(bb : PowerSeries (Polynomial ℤ))*(geom (X^2)) := by
    calc
      _ = Rser*((aa : PowerSeries (Polynomial ℤ))*(geom (X^2))) := by rw [aS_uS,mul_one]
      _ = _ := by rw [← mul_assoc,Rser_aS]
  have ha := congrArg (fun f : (PowerSeries (Polynomial ℤ)) => D f) aS_uS
  simp only [Derivation.leibniz,smul_eq_mul,PowerSeries.derivative_one] at ha
  have hu : D (geom (X^2)) = -(D (aa : PowerSeries (Polynomial ℤ)))*(geom (X^2))^2 := by
    linear_combination (geom (X^2))*ha-(D (geom (X^2)))*aS_uS
  rw [hr]
  simp only [Derivation.leibniz,smul_eq_mul,map_sub,PowerSeries.derivative_one,
    PowerSeries.derivative_C,PowerSeries.derivative_X]
  rw [hu]
  linear_combination -X*(1-Y)*(geom (X^2))*((bb : PowerSeries (Polynomial ℤ))+X*(D (bb : PowerSeries (Polynomial ℤ))))*aS_uS

private theorem graphTransferSeries_identity : graphTransferSeries*DEN=NUM := by
  have he : graphTransferSeries=closedSeries := by
    unfold graphTransferSeries closedSeries
    rw [transferTrace_formula,correction_formula]
    linear_combination zeroSeries_cancel
  rw [he]
  exact closedSeries_identity

private lemma coeff_gS (n : Nat) : PowerSeries.coeff n (geom (Y*X))=(Polynomial.X : Polynomial ℤ)^n := by
  have he : PowerSeries.monomial 1 ((Polynomial.X : Polynomial ℤ)^1)=Y*X := by
    simp [PowerSeries.monomial_eq_C_mul_X_pow]
  have h := geom_monomial_approx 1 1 n (by omega)
  rw [he] at h
  change PowerSeries.coeff n (geom (Y*X))=(Polynomial.X : Polynomial ℤ)^n
  rw [h n (le_refl n)]
  simp only [map_sum,mul_pow,← map_pow,PowerSeries.coeff_C_mul_X_pow]
  simp [Finset.sum_ite_eq',Nat.lt_succ_self]

private lemma coeff_zero_tail (n : Nat) :
    PowerSeries.coeff n ((Y*X)^3*(geom (Y*X)))=if 3≤n then (Polynomial.X : Polynomial ℤ)^n else 0 := by
  rw [mul_pow,mul_assoc,show Y^3=PowerSeries.C ((Polynomial.X : Polynomial ℤ)^3) from (map_pow _ _ _).symm]
  rw [PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul']
  by_cases hn : 3≤n
  · rw [if_pos hn,coeff_gS,← pow_add,show 3+(n-3)=n by omega,if_pos hn]
  · simp [hn]

private theorem coeff_zeroSeries (n : Nat) :
    PowerSeries.coeff n zeroSeries=(Polynomial.X : Polynomial ℤ)^(if n≤2 then 0 else n) := by
  simp only [zeroSeries,map_add,coeff_zero_tail,PowerSeries.coeff_one,
    PowerSeries.coeff_X,PowerSeries.coeff_X_pow]
  by_cases hn : n≤2
  · interval_cases n <;> simp
  · have h3 : 3≤n := by omega
    simp [hn,h3,show n≠0 by omega,show n≠1 by omega,show n≠2 by omega]

private lemma runPolynomial_gt (n ell : Nat) (hn : n < ell) : runPolynomial n ell=0 := by
  unfold runPolynomial
  apply Finset.sum_eq_zero
  intro k hk
  letI : IsEmpty (DegreeRunWords n ell k) := ⟨fun w => by
    have h := runCount_le w.val
    have he := w.property.2.2
    omega⟩
  simp

private lemma marked_word_coefficient (n ell : Nat) :
    runPolynomial n (ell+1)=
      PowerSeries.coeff n (X*Matrix.trace (A^ell*dMatrix A))+
      if ell=0 then PowerSeries.coeff n (X*(PowerSeries.derivative (Polynomial ℤ) (X*(1-Y)*Rser))) else 0 := by
  have hw := polynomial_marked_double_count n (ell+1)
  rw [tuple_transfer_coefficient] at hw
  simp only [Nat.cast_add,Nat.cast_one] at hw
  have ht := trace_marked_coefficient ell n
  have hc := coeff_euler (X*(1-Y)*Rser) n
  have hne : (ell+1:(Polynomial ℤ))≠0 := by exact_mod_cast (show (ell+1:ℤ)≠0 by omega)
  apply mul_left_cancel₀ hne
  by_cases he : ell=0
  · subst ell
    simp only [if_true,Nat.cast_zero,zero_add,one_mul] at *
    linear_combination hw-ht-hc
  · simp only [if_neg he,add_zero] at *
    linear_combination hw-ht

private theorem degSeries_eq_graphTransferSeries : degSeries=graphTransferSeries := by
  apply PowerSeries.ext
  intro n
  rw [coeff_degSeries]
  have hp : degreePolynomial n=runPolynomial n 0+
      ∑ ell ∈ Finset.range (n+1), runPolynomial n (ell+1) := by
    rw [degreePolynomial_partition,Finset.sum_range_succ']
    rw [Finset.sum_range_succ,runPolynomial_gt n (n+1) (by omega),add_zero]
    ring
  rw [hp,runPolynomial_zero]
  simp_rw [marked_word_coefficient]
  rw [Finset.sum_add_distrib]
  have hi : (∑ ell ∈ Finset.range (n+1),
      if ell=0 then PowerSeries.coeff n (X*(PowerSeries.derivative (Polynomial ℤ) (X*(1-Y)*Rser))) else 0) =
      PowerSeries.coeff n (X*(PowerSeries.derivative (Polynomial ℤ) (X*(1-Y)*Rser))) := by
    simp
  rw [hi,← coeff_euler_transferTrace,← coeff_zeroSeries]
  simp only [graphTransferSeries,map_add,add_assoc]

theorem result : claim := by
  unfold claim
  rw [degSeries_eq_graphTransferSeries]
  exact graphTransferSeries_identity

end
end DegreeGeneratingFunction
