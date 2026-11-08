/- GID: D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfThreeLevelCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Matrix/HsfThreeLevelScalarBinding.closed_cubic_nonneg; premises=D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients.F_nonneg
   digest: The actual closed pair and triangle coefficients of the HSF size-three remainder. -/

module

public import D5.S3.Quantum.Matrix.HsfBalancedSpectralCertificate
public import D5.S3.Quantum.Matrix.PsdThreeCubicComplex

/-! rho reuses the canonical repeated-index
   coefficient, with the positive common level scale divided out. Xi is the
   literal 6*C_actual coefficient, not twice that coefficient. Definitions
   here have only positive H denominators on positive levels, so collisions
   are included. Identification of closed moments with the original integrals
   is NOT claimed by these algebraic declarations. -/

@[expose] public section
noncomputable section

namespace D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients

open PsdThreeCubic

def H (p q : ℝ) : ℝ := p^2+p*q+q^2

def Q (p q r : ℝ) : ℝ := H p q * H q r * H r p

def edgeNumerator (p q : ℝ) : ℝ :=
  p*q*(p-q)^2*(p^2-p*q+q^2)*(p^2+7*p*q+q^2)

def rho (p q : ℝ) : ℝ := HsfBalancedSpectralCertificate.kappa (q/p)

def symmetricF (e f g : ℝ) : ℝ :=
  e^5*f^5-2*e^3*f^6-7*e*f^7 +
  g*(-2*e^6*f^3+e^4*f^4+34*e^2*f^5+7*f^6) +
  g^2*(-7*e^7*f+34*e^5*f^2-34*e^3*f^3-72*e*f^4) +
  g^3*(7*e^6-72*e^4*f+72*e^2*f^2)

def F (p q r : ℝ) : ℝ := symmetricF (p+q+r) (p*q+q*r+r*p) (p*q*r)

def Xi (p q r : ℝ) : ℝ := 9*p*q*r*F p q r/(4*(Q p q r)^3)

/-- The closed cubic of the actual ordered remainder, in Hermitian coordinates. -/
def closedCubic (p q r : ℝ) (S : Mat) : ℝ :=
  cubic (rho p q) (rho q r) (rho r p) (Xi p q r) S

theorem H_pos (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : 0 < H p q := by
  dsimp [H]
  positivity

theorem Q_pos (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    0 < Q p q r := mul_pos (mul_pos (H_pos p q hp hq) (H_pos q r hq hr)) (H_pos r p hr hp)

/-- Exact two-variable binding to the pre-existing canonical coefficient. -/
theorem rho_closed (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    rho p q = edgeNumerator p q/(12*(H p q)^4) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hH : H p q ≠ 0 := ne_of_gt (H_pos p q hp hq)
  have hd : HsfBalancedSpectralCertificate.den (q/p) = H p q/p^2 := by
    dsimp [HsfBalancedSpectralCertificate.den, H]
    field_simp [hp0]
    <;> ring
  unfold rho HsfBalancedSpectralCertificate.kappa edgeNumerator
  rw [hd]
  field_simp [hp0, hH]
  ring

theorem rho_nonneg (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : 0 ≤ rho p q := by
  rw [rho_closed p q hp hq]
  have hmiddle : 0 < p^2-p*q+q^2 := by
    nlinarith [sq_nonneg (p-q), mul_pos hp hq]
  dsimp [edgeNumerator, H]
  positivity

theorem rho_pos (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hne : p ≠ q) : 0 < rho p q := by
  rw [rho_closed p q hp hq]
  have hmiddle : 0 < p^2-p*q+q^2 := by nlinarith [sq_nonneg (p-q), mul_pos hp hq]
  have hdiff : 0 < (p-q)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  dsimp [edgeNumerator, H]
  positivity

theorem rho_symm (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : rho p q = rho q p := by
  rw [rho_closed p q hp hq, rho_closed q p hq hp]
  congr 1 <;> dsimp [edgeNumerator, H] <;> ring

theorem rho_self (p : ℝ) (hp : 0 < p) : rho p p = 0 := by
  rw [rho_closed p p hp hp]
  simp [edgeNumerator]

private theorem F_swap (p q r : ℝ) : F p q r = F q p r := by
  unfold F
  congr 1 <;> ring

private theorem F_cycle (p q r : ℝ) : F p q r = F q r p := by
  unfold F
  congr 1 <;> ring

private theorem F_reverse (p q r : ℝ) : F p q r = F r q p := by
  unfold F
  congr 1 <;> ring

theorem F_swap_last (p q r : ℝ) : F p q r = F p r q := by
  unfold F
  congr 1 <;> ring

/- The positive ordered-chamber expansion follows below, grouped into
   fourteen low-degree rows. The source generator is not trusted: the
   identity uses Lean ring and each sign proof uses positivity. -/

private def frow2 (y z : ℝ) : ℝ :=
  162*y^2 + 162*y*z + 162*z^2

private theorem frow2_nonneg (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ frow2 y z := by unfold frow2; positivity

private def frow3 (y z : ℝ) : ℝ :=
  1458*y^3 + 2187*y^2*z + 2025*y*z^2 + 648*z^3

private theorem frow3_nonneg (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ frow3 y z := by unfold frow3; positivity

private def frow4 (y z : ℝ) : ℝ :=
  6120*y^4 + 12240*y^3*z + 12528*y^2*z^2 + 6408*y*z^3 +
  1260*z^4

private theorem frow4_nonneg (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ frow4 y z := by unfold frow4; positivity

private def frow5 (y z : ℝ) : ℝ :=
  15912*y^5 + 39780*y^4*z + 47196*y^3*z^2 + 31014*y^2*z^3 +
  10710*y*z^4 + 1512*z^5

private theorem frow5_nonneg (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ frow5 y z := by unfold frow5; positivity

private def frow6 (y z : ℝ) : ℝ :=
  28632*y^6 + 85896*y^5*z + 119754*y^4*z^2 + 96348*y^3*z^3 +
  44964*y^2*z^4 + 11106*y*z^5 + 1182*z^6

private theorem frow6_nonneg (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ frow6 y z := by unfold frow6; positivity

private def frow7 (y z : ℝ) : ℝ :=
  37632*y^7 + 131712*y^6*z + 216756*y^5*z^2 + 212610*y^4*z^3 +
  126078*y^3*z^4 + 42363*y^2*z^5 + 7419*y*z^6 + 600*z^7

private theorem frow7_nonneg (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ frow7 y z := by unfold frow7; positivity

private def frow8 (y z : ℝ) : ℝ :=
  37076*y^8 + 148304*y^7*z + 287522*y^6*z^2 + 343502*y^5*z^3 +
  255452*y^4*z^4 + 111422*y^3*z^5 + 26330*y^2*z^6 + 3152*y*z^7 +
  188*z^8

private theorem frow8_nonneg (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ frow8 y z := by unfold frow8; positivity

private def frow9 (y z : ℝ) : ℝ :=
  27612*y^9 + 124254*y^8*z + 281254*y^7*z^2 + 404537*y^6*z^3 +
  371019*y^5*z^4 + 206131*y^4*z^5 + 64799*y^3*z^6 + 10500*y^2*z^7 +
  802*y*z^8 + 32*z^9

private theorem frow9_nonneg (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ frow9 y z := by unfold frow9; positivity

private def frow10 (y z : ℝ) : ℝ :=
  15464*y^10 + 77320*y^9*z + 201312*y^8*z^2 + 341328*y^7*z^3 +
  376020*y^6*z^4 + 258156*y^5*z^5 + 105090*y^4*z^6 + 23496*y^3*z^7 +
  2520*y^2*z^8 + 106*y*z^9 + 2*z^10

private theorem frow10_nonneg (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ frow10 y z := by unfold frow10; positivity

private def frow11 (y z : ℝ) : ℝ :=
  6392*y^11 + 35156*y^10*z + 103368*y^9*z^2 + 201486*y^8*z^3 +
  259010*y^7*z^4 + 212359*y^6*z^5 + 107269*y^5*z^6 + 31629*y^4*z^7 +
  4907*y^3*z^8 + 321*y^2*z^9 + 5*y*z^10

private theorem frow11_nonneg (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ frow11 y z := by unfold frow11; positivity

private def frow12 (y z : ℝ) : ℝ :=
  1880*y^12 + 11280*y^11*z + 36746*y^10*z^2 + 80330*y^9*z^3 +
  117326*y^8*z^4 + 111404*y^7*z^5 + 67086*y^6*z^6 + 24650*y^5*z^7 +
  5122*y^4*z^8 + 512*y^3*z^9 + 16*y^2*z^10

private theorem frow12_nonneg (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ frow12 y z := by unfold frow12; positivity

private def frow13 (y z : ℝ) : ℝ :=
  368*y^13 + 2392*y^12*z + 8484*y^11*z^2 + 20350*y^10*z^3 +
  33010*y^9*z^4 + 35388*y^8*z^5 + 24590*y^7*z^6 + 10747*y^6*z^7 +
  2781*y^5*z^8 + 375*y^4*z^9 + 19*y^3*z^10

private theorem frow13_nonneg (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ frow13 y z := by unfold frow13; positivity

private def frow14 (y z : ℝ) : ℝ :=
  42*y^14 + 294*y^13*z + 1120*y^12*z^2 + 2898*y^11*z^3 +
  5128*y^10*z^4 + 6082*y^9*z^5 + 4752*y^8*z^6 + 2382*y^7*z^7 +
  726*y^6*z^8 + 120*y^5*z^9 + 8*y^4*z^10

private theorem frow14_nonneg (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ frow14 y z := by unfold frow14; positivity

private def frow15 (y z : ℝ) : ℝ :=
  2*y^15 + 15*y^14*z + 61*y^13*z^2 + 169*y^12*z^3 +
  323*y^11*z^4 + 418*y^10*z^5 + 360*y^9*z^6 + 201*y^8*z^7 +
  69*y^7*z^8 + 13*y^6*z^9 + 1*y^5*z^10

private theorem frow15_nonneg (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ frow15 y z := by unfold frow15; positivity

private def orderedF (x y z : ℝ) : ℝ :=
  x^13*frow2 y z +
  x^12*frow3 y z +
  x^11*frow4 y z +
  x^10*frow5 y z +
  x^9*frow6 y z +
  x^8*frow7 y z +
  x^7*frow8 y z +
  x^6*frow9 y z +
  x^5*frow10 y z +
  x^4*frow11 y z +
  x^3*frow12 y z +
  x^2*frow13 y z +
  x^1*frow14 y z +
  frow15 y z

private theorem orderedF_nonneg (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ orderedF x y z := by

  have h2 := frow2_nonneg y z hy hz

  have h3 := frow3_nonneg y z hy hz

  have h4 := frow4_nonneg y z hy hz

  have h5 := frow5_nonneg y z hy hz

  have h6 := frow6_nonneg y z hy hz

  have h7 := frow7_nonneg y z hy hz

  have h8 := frow8_nonneg y z hy hz

  have h9 := frow9_nonneg y z hy hz

  have h10 := frow10_nonneg y z hy hz

  have h11 := frow11_nonneg y z hy hz

  have h12 := frow12_nonneg y z hy hz

  have h13 := frow13_nonneg y z hy hz

  have h14 := frow14_nonneg y z hy hz

  have h15 := frow15_nonneg y z hy hz

  unfold orderedF
  positivity

private theorem F_ordered_identity (x y z : ℝ) :
    F x (x+y) (x+y+z) = orderedF x y z := by
  unfold F symmetricF orderedF frow2 frow3 frow4 frow5 frow6 frow7 frow8 frow9 frow10 frow11 frow12 frow13 frow14 frow15
  ring


private theorem F_ordered_nonneg (p q r : ℝ) (hp : 0 < p) (hpq : p ≤ q) (hqr : q ≤ r) :
    0 ≤ F p q r := by
  have h := orderedF_nonneg p (q-p) (r-q) hp.le (sub_nonneg.mpr hpq) (sub_nonneg.mpr hqr)
  rw [← F_ordered_identity] at h
  convert h using 1 <;> congr 1 <;> ring

/-- The scalar cycle coefficient has the correct sign for every positive
    triple. This is not a statement about the sign of a complex source cycle. -/
theorem F_nonneg (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) : 0 ≤ F p q r := by
  rcases le_total p q with hpq | hqp
  · rcases le_total q r with hqr | hrq
    · exact F_ordered_nonneg p q r hp hpq hqr
    · rcases le_total p r with hpr | hrp
      · rw [F_swap_last]
        exact F_ordered_nonneg p r q hp hpr hrq
      · rw [← F_cycle r p q]
        exact F_ordered_nonneg r p q hr hrp hpq
  · rcases le_total p r with hpr | hrp
    · rw [F_swap]
      exact F_ordered_nonneg q p r hq hqp hpr
    · rcases le_total q r with hqr | hrq
      · rw [F_cycle]
        exact F_ordered_nonneg q r p hq hqr hrp
      · rw [F_reverse]
        exact F_ordered_nonneg r q p hr hrq hqp

theorem Xi_nonneg (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) : 0 ≤ Xi p q r := by
  have hF := F_nonneg p q r hp hq hr
  have hQ := Q_pos p q r hp hq hr
  unfold Xi
  positivity

/-- Complete collision normalization; the zero pair weight is not divided out. -/
theorem Xi_double (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : Xi p p q = 2*rho p q := by
  have hp0 := ne_of_gt hp
  have hH := ne_of_gt (H_pos p q hp hq)
  have hQ : Q p p q = 3*p^2*(H p q)^2 := by unfold Q H; ring
  have hF : F p p q = 2*p^5*(p-q)^2*(p^2-p*q+q^2)*(p^2+7*p*q+q^2)*(H p q)^2 := by
    unfold F symmetricF H
    ring
  unfold Xi
  rw [hQ, hF, rho_closed p q hp hq]
  unfold edgeNumerator
  field_simp [hp0, hH]
  <;> ring

theorem Xi_self (p : ℝ) : Xi p p p = 0 := by
  have hF : F p p p = 0 := by unfold F symmetricF; ring
  simp [Xi, hF]

/-- Common denominator for the exact P396 comparison. -/
def commonDen (p q r : ℝ) : ℝ := 12*(Q p q r)^4

def edgeScaled (p q r : ℝ) : ℝ := edgeNumerator p q*(H q r)^4*(H r p)^4

def cycleScaled (p q r : ℝ) : ℝ := 27*(p*q*r)*Q p q r*F p q r

def p396 (p q r : ℝ) : ℝ :=
  let a := edgeScaled p q r
  let b := edgeScaled q r p
  let c := edgeScaled r p q
  let k := cycleScaled p q r
  4*(a+b+c)*(a*b+b*c+c*a)+396*a*b*c-(a+b+c)*k^2

private theorem commonDen_cycle (p q r : ℝ) : commonDen p q r = commonDen q r p := by
  unfold commonDen Q
  congr 1 <;> ring

/-- The rho denominators are cleared before any high-degree expansion. -/
theorem edge_scaled (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    edgeScaled p q r = commonDen p q r*rho p q := by
  rw [rho_closed p q hp hq]
  unfold edgeScaled commonDen Q
  rw [mul_pow, mul_pow]
  field_simp [ne_of_gt (H_pos p q hp hq)]
  <;> ring

theorem cycle_scaled (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    cycleScaled p q r = commonDen p q r*Xi p q r := by
  unfold cycleScaled commonDen Xi
  field_simp [ne_of_gt (Q_pos p q r hp hq hr)]
  <;> ring

/-- Exact normalization of the degree-72 certificate to the actual coefficients.
    This theorem is algebraic binding, not positivity of p396. -/
theorem p396_scaled (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    p396 p q r = (commonDen p q r)^3 *
      (4*(rho p q+rho q r+rho r p)*(rho p q*rho q r+rho q r*rho r p+rho r p*rho p q)+
        396*rho p q*rho q r*rho r p-(rho p q+rho q r+rho r p)*(Xi p q r)^2) := by
  have hD1 : commonDen q r p = commonDen p q r := (commonDen_cycle p q r).symm
  have hD2 : commonDen r p q = commonDen p q r := (commonDen_cycle q r p).symm.trans hD1
  unfold p396
  simp only [edge_scaled p q r hp hq hr, edge_scaled q r p hq hr hp,
    edge_scaled r p q hr hp hq, cycle_scaled p q r hp hq hr,
    hD1, hD2]
  ring

end D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients
