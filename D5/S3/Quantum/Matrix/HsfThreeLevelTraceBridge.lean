/- GID: D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfThreeLevelTraceBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Quantum/Matrix/HsfThreeLevelScalarBinding]
   utility: none
   digest: The ordered finite-moment trace cubic is the actual PSD3 closed coordinate cubic. -/

module

public import D5.S3.Quantum.Matrix.HsfThreeLevelScalarBinding

/-! These are the literal closed resolvent
   moments, with the original factor order and K-adjoint sign. This module
   connects their finite trace expression to the closed cubic. The equality
   of these closed functions with the original integrals, differentiation
   under those integrals, and the original HSF derivative/source identity
   are not Lean-formalized here. In particular closed_trace_nonneg does not
   by itself prove the original HSF conjecture. -/

@[expose] public section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients

open PsdThreeCubic
open HsfBalancedSpectralCertificate (tr)

def tauClosed (p q : ℝ) : ℝ := 3*Real.sqrt (p*q)*(p+q)/(2*H p q)
def kappaClosed (p q : ℝ) : ℝ :=
  Real.sqrt (p*q)*(q-p)*(p^2+3*p*q+q^2)/(2*(H p q)^2)
def psiClosed (p q : ℝ) : ℝ := p^2*q^2*Real.sqrt (p*q)*(p+q)/(H p q)^3

def betaNumerator (p q r : ℝ) : ℝ :=
  let e := p*q+q*r+r*p
  (3*e+r*(p+q))*H q r*H r p-r*e*((q+2*r)*H r p+(p+2*r)*H q r)

def betaClosed (p q r : ℝ) : ℝ :=
  Real.sqrt (p*q)*r^3*betaNumerator p q r/(2*H p q*(H q r)^2*(H r p)^2)

def orderedCoefficient (p q r : ℝ) : ℝ :=
  4*tauClosed p q*betaClosed p q r-4*tauClosed p q*tauClosed q r*psiClosed r p-
    (2/27)*tauClosed p q*tauClosed q r*tauClosed r p+
    3*tauClosed p q*kappaClosed q r*kappaClosed r p

def rawNumerator (p q r : ℝ) : ℝ :=
  let a := H p q
  let b := H q r
  let c := H r p
  let L := (p+q)*(q+r)*(r+p)
  24*p*q*(p+q)*r^3*betaNumerator p q r*Q p q r-
    72*p^3*q*r^3*L*a^2*b^2-2*p*q*r*L*(Q p q r)^2+
    9*p*q*r*(p+q)*(r-q)*(p-r)*(q^2+3*q*r+r^2)*(r^2+3*r*p+p^2)*a^2*b*c

private theorem H_symm (p q : ℝ) : H p q = H q p := by unfold H; ring
private theorem Q_cycle (p q r : ℝ) : Q p q r = Q q r p := by unfold Q; ring

private theorem beta_symm (p q r : ℝ) : betaClosed p q r = betaClosed q p r := by
  unfold betaClosed betaNumerator
  rw [mul_comm q p]
  congr 1 <;> dsimp [H] <;> ring

private theorem kappa_skew (p q : ℝ) : kappaClosed p q = -kappaClosed q p := by
  unfold kappaClosed
  rw [mul_comm q p, ← H_symm p q]
  ring

set_option maxRecDepth 4096 in
private theorem ordered_cleared (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    8*(Q p q r)^3*orderedCoefficient p q r = rawNumerator p q r := by
  have hs1 := Real.sq_sqrt hp.le
  have hs2 := Real.sq_sqrt hq.le
  have hs3 := Real.sq_sqrt hr.le
  have h1 := ne_of_gt (H_pos p q hp hq)
  have h2 := ne_of_gt (H_pos q r hq hr)
  have h3 := ne_of_gt (H_pos r p hr hp)
  unfold orderedCoefficient tauClosed betaClosed psiClosed kappaClosed rawNumerator
  simp_rw [Real.sqrt_mul hp.le, Real.sqrt_mul hq.le, Real.sqrt_mul hr.le]
  field_simp [h1, h2, h3]
  dsimp only [Q]
  ring_nf
  simp only [hs1, hs2, hs3]
  <;> ring

private theorem raw_forward (p q r : ℝ) :
    rawNumerator p q r+rawNumerator q r p+rawNumerator r p q = 9*p*q*r*F p q r := by
  unfold rawNumerator betaNumerator Q H F symmetricF
  ring

private theorem ordered_forward (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    orderedCoefficient p q r+orderedCoefficient q r p+orderedCoefficient r p q = Xi p q r/2 := by
  have h1 := ordered_cleared p q r hp hq hr
  have h2 := ordered_cleared q r p hq hr hp
  have h3 := ordered_cleared r p q hr hp hq
  rw [← Q_cycle p q r] at h2
  rw [← Q_cycle q r p, ← Q_cycle p q r] at h3
  have hsum := raw_forward p q r
  have hQ := ne_of_gt (Q_pos p q r hp hq hr)
  have hclear : 8*(Q p q r)^3*(Xi p q r/2) = 9*p*q*r*F p q r := by
    unfold Xi
    field_simp [hQ]
    <;> ring
  have heq : 8*(Q p q r)^3*
      (orderedCoefficient p q r+orderedCoefficient q r p+orderedCoefficient r p q-Xi p q r/2) = 0 := by
    linear_combination h1+h2+h3+hsum-hclear
  have hn : 8*(Q p q r)^3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hQ)
  exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left hn)

def momentMatrix (f : ℝ → ℝ → ℝ) (p : Fin 3 → ℝ) (S : Mat) : Mat :=
  fun i j => (f (p i) (p j) : ℂ)*S i j

def jMatrix (p : Fin 3 → ℝ) (S : Mat) : Mat :=
  fun i j => ∑ k, (betaClosed (p i) (p j) (p k) : ℂ)*S i k*S k j

/-- The exact four ordered traces. The minus-three adjoint term is retained. -/
def closedMomentTrace (p : Fin 3 → ℝ) (S : Mat) : ℝ :=
  let X := momentMatrix tauClosed p S
  let K := momentMatrix kappaClosed p S
  let Psi := momentMatrix psiClosed p S
  4*tr (X*jMatrix p S)-4*tr (X*X*Psi)-(2/27)*tr (X*X*X)-3*tr (X*Kᴴ*K)

def orderedCubic (h : Fin 3 → Fin 3 → Fin 3 → ℝ) (S : Mat) : ℝ :=
  ∑ i, ∑ j, ∑ k, h i j k*(S i j*S j k*S k i).re

private theorem moment_kappa_adjoint (p : Fin 3 → ℝ) (S : Mat) (hS : S.IsHermitian) :
    (momentMatrix kappaClosed p S)ᴴ = -momentMatrix kappaClosed p S := by
  ext i j
  change star ((kappaClosed (p j) (p i) : ℂ)*S j i) = -((kappaClosed (p i) (p j) : ℂ)*S i j)
  rw [star_mul]
  have hentry := hS.apply i j
  rw [hentry]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [kappa_skew (p j) (p i)]
  push_cast
  ring

/-- Ordered trace expansion, with no commutation of matrix factors. -/
theorem trace_to_ordered (p : Fin 3 → ℝ) (S : Mat) (hS : S.IsHermitian) :
    closedMomentTrace p S =
      orderedCubic (fun i j k => orderedCoefficient (p i) (p j) (p k)) S := by
  have hK := moment_kappa_adjoint p S hS
  unfold closedMomentTrace
  dsimp only
  rw [hK]
  simp [tr, momentMatrix, jMatrix, orderedCubic, orderedCoefficient,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
    Complex.mul_re, Complex.mul_im, beta_symm]
  <;> ring

/-- A finite Hermitian coordinate bridge. Its hypotheses specify raw scalar
    coefficients, not a matrix inequality or its conclusion. -/
theorem ordered_to_coordinates (h : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (S : Mat) (hS : S.IsHermitian) (a b c k : ℝ)
    (h0 : h 0 0 0 = 0) (h1 : h 1 1 1 = 0) (h2 : h 2 2 2 = 0)
    (ha0 : h 0 0 1+h 0 1 0+h 1 0 0 = a)
    (ha1 : h 1 1 0+h 1 0 1+h 0 1 1 = a)
    (hb1 : h 1 1 2+h 1 2 1+h 2 1 1 = b)
    (hb2 : h 2 2 1+h 2 1 2+h 1 2 2 = b)
    (hc2 : h 2 2 0+h 2 0 2+h 0 2 2 = c)
    (hc0 : h 0 0 2+h 0 2 0+h 2 0 0 = c)
    (hf : h 0 1 2+h 1 2 0+h 2 0 1 = k/2)
    (hr : h 0 2 1+h 2 1 0+h 1 0 2 = k/2) :
    orderedCubic h S = cubic a b c k S := by
  have h10 : S 1 0 = star (S 0 1) := (hS.apply 1 0).symm
  have h21 : S 2 1 = star (S 1 2) := (hS.apply 2 1).symm
  have h02 : S 0 2 = star (S 2 0) := (hS.apply 0 2).symm
  have hdiag (i : Fin 3) : (S i i).im = 0 := Complex.conj_eq_iff_im.mp (hS.apply i i)
  simp only [orderedCubic, Fin.sum_univ_three, cubic, matrixPair, cycle,
    h0, h1, h2, h10, h21, h02, Complex.sq_norm, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.conj_re, Complex.conj_im,
    Complex.star_def, hdiag]
  linear_combination
    ((S 0 0).re*((S 0 1).re^2+(S 0 1).im^2))*ha0+
    ((S 1 1).re*((S 0 1).re^2+(S 0 1).im^2))*ha1+
    ((S 1 1).re*((S 1 2).re^2+(S 1 2).im^2))*hb1+
    ((S 2 2).re*((S 1 2).re^2+(S 1 2).im^2))*hb2+
    ((S 2 2).re*((S 2 0).re^2+(S 2 0).im^2))*hc2+
    ((S 0 0).re*((S 2 0).re^2+(S 2 0).im^2))*hc0+
    (((S 0 1).re*(S 1 2).re-(S 0 1).im*(S 1 2).im)*(S 2 0).re-
      ((S 0 1).re*(S 1 2).im+(S 0 1).im*(S 1 2).re)*(S 2 0).im)*hf+
    (((S 0 1).re*(S 1 2).re-(S 0 1).im*(S 1 2).im)*(S 2 0).re-
      ((S 0 1).re*(S 1 2).im+(S 0 1).im*(S 1 2).re)*(S 2 0).im)*hr

private theorem ordered_pure (p : ℝ) (hp : 0 < p) : orderedCoefficient p p p = 0 := by
  have h := ordered_forward p p p hp hp hp
  rw [Xi_self] at h
  linarith

private theorem ordered_pair (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    orderedCoefficient p p q+orderedCoefficient p q p+orderedCoefficient q p p = rho p q := by
  have h := ordered_forward p p q hp hp hq
  rw [Xi_double p q hp hq] at h
  linarith only [h]

private theorem Xi_swap_last (p q r : ℝ) : Xi p q r = Xi p r q := by
  unfold Xi
  rw [F_swap_last p q r]
  congr 1 <;> (try dsimp [Q, H]) <;> ring

/-- The actual all-positive closed trace-to-coordinate normal form, including
    six ordered distinct-index contributions and every repeated-index term. -/
theorem closed_trace_normal_form (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (S : Mat) (hS : S.IsHermitian) :
    closedMomentTrace ![p, q, r] S = closedCubic p q r S := by
  rw [trace_to_ordered _ S hS]
  apply ordered_to_coordinates _ S hS (rho p q) (rho q r) (rho r p) (Xi p q r)
  · exact ordered_pure p hp
  · exact ordered_pure q hq
  · exact ordered_pure r hr
  · exact ordered_pair p q hp hq
  · simpa [rho_symm q p hq hp] using ordered_pair q p hq hp
  · exact ordered_pair q r hq hr
  · simpa [rho_symm r q hr hq] using ordered_pair r q hr hq
  · exact ordered_pair r p hr hp
  · simpa [rho_symm p r hp hr] using ordered_pair p r hp hr
  · exact ordered_forward p q r hp hq hr
  · simpa [← Xi_swap_last p q r] using ordered_forward p r q hp hr hq

/-- Positivity of the four finite ordered traces with their actual closed
    moment functions. Integral identification remains outside this theorem. -/
theorem closed_trace_nonneg (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (S : Mat) (hS : S.PosSemidef) : 0 ≤ closedMomentTrace ![p, q, r] S := by
  rw [closed_trace_normal_form p q r hp hq hr S hS.isHermitian]
  exact closed_cubic_nonneg p q r hp hq hr S hS

end D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients
