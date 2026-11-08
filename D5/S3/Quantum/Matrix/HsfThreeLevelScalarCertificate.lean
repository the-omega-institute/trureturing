/- GID: D5/S3/Quantum/Matrix/HsfThreeLevelScalarCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfThreeLevelScalarCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Matrix/HsfThreeLevelScalarBinding.closed_cubic_nonneg; premises=D5/S3/Quantum/Matrix/HsfThreeLevelScalarIdentity.p396_nonneg
   digest: A positive symmetric certificate for the actual three-level scalar comparison. -/

module

public import D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients

/-! UNCOMPILED source candidate. The P396 input is a fallible completed
   mathematical source, whose separate independent audit is not read here.
   Standard ring/positivity proof bodies below still require real compilation.
   No native computation, reflection framework, new axiom or heartbeat override.
   No original integral identity or full HSF theorem is claimed. -/

@[expose] public section
noncomputable section

namespace D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients

/-- Monomial symmetric polynomial, for a partition i >= j >= k.
    Each distinct permutation occurs once, including the central partition. -/
def monomialSymmetric (i j k : ℕ) (p q r : ℝ) : ℝ :=
  if i = j then
    if j = k then p^i*q^j*r^k
    else p^i*q^j*r^k+q^i*r^j*p^k+r^i*p^j*q^k
  else if j = k then p^i*q^j*r^k+q^i*r^j*p^k+r^i*p^j*q^k
  else p^i*q^j*r^k+p^i*r^j*q^k+q^i*p^j*r^k+
    q^i*r^j*p^k+r^i*p^j*q^k+r^i*q^j*p^k

private theorem monomial_nonneg (i j k : ℕ) (p q r : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) : 0 ≤ monomialSymmetric i j k p q r := by
  unfold monomialSymmetric
  split_ifs <;> positivity

/-- The complement pairing in the complete 81-entry P396 table. -/
def pairedMonomial (i j k : ℕ) (p q r : ℝ) : ℝ :=
  monomialSymmetric i j k p q r +
    if j = 17 then 0 else monomialSymmetric (34-k) (34-j) (34-i) p q r

private theorem paired_nonneg (i j k : ℕ) (p q r : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) : 0 ≤ pairedMonomial i j k p q r := by
  have h := monomial_nonneg i j k p q r hp hq hr
  have h' := monomial_nonneg (34-k) (34-j) (34-i) p q r hp hq hr
  unfold pairedMonomial
  split_ifs <;> positivity

/-- Signed boundary coefficients are kept in their nonnegative factorization. -/
def boundaryW (p q : ℝ) : ℝ :=
  (p-q)^2*(p+q)*(H p q)^2*(p^2-p*q+q^2)^2*(p^2+7*p*q+q^2)^2

def boundaryCertificate (p q r : ℝ) : ℝ := 4*(
  boundaryW q r*(p^34*q*r+(q*r)^18)+
  boundaryW r p*(q^34*r*p+(r*p)^18)+
  boundaryW p q*(r^34*p*q+(p*q)^18))

private theorem boundary_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ boundaryCertificate p q r := by
  have hw (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ boundaryW x y := by
    unfold boundaryW
    positivity
  have h1 := hw q r hq hr
  have h2 := hw r p hr hp
  have h3 := hw p q hp hq
  unfold boundaryCertificate
  positivity

def positiveSlice1 (p q r : ℝ) : ℝ :=
  605002*pairedMonomial 25 25 1 p q r +
  313761*pairedMonomial 26 24 1 p q r +
  199612*pairedMonomial 27 23 1 p q r +
  319069*pairedMonomial 28 22 1 p q r +
  156094*pairedMonomial 29 21 1 p q r +
  39398*pairedMonomial 30 20 1 p q r +
  15572*pairedMonomial 31 19 1 p q r +
  5051*pairedMonomial 32 18 1 p q r +
  504*pairedMonomial 33 17 1 p q r

private theorem slice1_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice1 p q r := by
  have h0 := paired_nonneg 25 25 1 p q r hp hq hr
  have h1 := paired_nonneg 26 24 1 p q r hp hq hr
  have h2 := paired_nonneg 27 23 1 p q r hp hq hr
  have h3 := paired_nonneg 28 22 1 p q r hp hq hr
  have h4 := paired_nonneg 29 21 1 p q r hp hq hr
  have h5 := paired_nonneg 30 20 1 p q r hp hq hr
  have h6 := paired_nonneg 31 19 1 p q r hp hq hr
  have h7 := paired_nonneg 32 18 1 p q r hp hq hr
  have h8 := paired_nonneg 33 17 1 p q r hp hq hr
  unfold positiveSlice1
  positivity

def positiveSlice2 (p q r : ℝ) : ℝ :=
  10743909*pairedMonomial 25 24 2 p q r +
  5726328*pairedMonomial 26 23 2 p q r +
  5654692*pairedMonomial 27 22 2 p q r +
  5187586*pairedMonomial 28 21 2 p q r +
  1987422*pairedMonomial 29 20 2 p q r +
  483020*pairedMonomial 30 19 2 p q r +
  176228*pairedMonomial 31 18 2 p q r +
  52287*pairedMonomial 32 17 2 p q r

private theorem slice2_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice2 p q r := by
  have h0 := paired_nonneg 25 24 2 p q r hp hq hr
  have h1 := paired_nonneg 26 23 2 p q r hp hq hr
  have h2 := paired_nonneg 27 22 2 p q r hp hq hr
  have h3 := paired_nonneg 28 21 2 p q r hp hq hr
  have h4 := paired_nonneg 29 20 2 p q r hp hq hr
  have h5 := paired_nonneg 30 19 2 p q r hp hq hr
  have h6 := paired_nonneg 31 18 2 p q r hp hq hr
  have h7 := paired_nonneg 32 17 2 p q r hp hq hr
  unfold positiveSlice2
  positivity

def positiveSlice3 (p q r : ℝ) : ℝ :=
  108463952*pairedMonomial 24 24 3 p q r +
  80194388*pairedMonomial 25 23 3 p q r +
  51067648*pairedMonomial 26 22 3 p q r +
  49261680*pairedMonomial 27 21 3 p q r +
  31265484*pairedMonomial 28 20 3 p q r +
  8723280*pairedMonomial 29 19 3 p q r +
  1542588*pairedMonomial 30 18 3 p q r +
  605156*pairedMonomial 31 17 3 p q r

private theorem slice3_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice3 p q r := by
  have h0 := paired_nonneg 24 24 3 p q r hp hq hr
  have h1 := paired_nonneg 25 23 3 p q r hp hq hr
  have h2 := paired_nonneg 26 22 3 p q r hp hq hr
  have h3 := paired_nonneg 27 21 3 p q r hp hq hr
  have h4 := paired_nonneg 28 20 3 p q r hp hq hr
  have h5 := paired_nonneg 29 19 3 p q r hp hq hr
  have h6 := paired_nonneg 30 18 3 p q r hp hq hr
  have h7 := paired_nonneg 31 17 3 p q r hp hq hr
  unfold positiveSlice3
  positivity

def positiveSlice4 (p q r : ℝ) : ℝ :=
  574395548*pairedMonomial 24 23 4 p q r +
  370828650*pairedMonomial 25 22 4 p q r +
  269255764*pairedMonomial 26 21 4 p q r +
  214543632*pairedMonomial 27 20 4 p q r +
  96992592*pairedMonomial 28 19 4 p q r +
  16927212*pairedMonomial 29 18 4 p q r +
  1931150*pairedMonomial 30 17 4 p q r

private theorem slice4_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice4 p q r := by
  have h0 := paired_nonneg 24 23 4 p q r hp hq hr
  have h1 := paired_nonneg 25 22 4 p q r hp hq hr
  have h2 := paired_nonneg 26 21 4 p q r hp hq hr
  have h3 := paired_nonneg 27 20 4 p q r hp hq hr
  have h4 := paired_nonneg 28 19 4 p q r hp hq hr
  have h5 := paired_nonneg 29 18 4 p q r hp hq hr
  have h6 := paired_nonneg 30 17 4 p q r hp hq hr
  unfold positiveSlice4
  positivity

def positiveSlice5 (p q r : ℝ) : ℝ :=
  2642231280*pairedMonomial 23 23 5 p q r +
  2118372260*pairedMonomial 24 22 5 p q r +
  1371798086*pairedMonomial 25 21 5 p q r +
  1021378314*pairedMonomial 26 20 5 p q r +
  651096776*pairedMonomial 27 19 5 p q r +
  233668828*pairedMonomial 28 18 5 p q r +
  45686550*pairedMonomial 29 17 5 p q r

private theorem slice5_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice5 p q r := by
  have h0 := paired_nonneg 23 23 5 p q r hp hq hr
  have h1 := paired_nonneg 24 22 5 p q r hp hq hr
  have h2 := paired_nonneg 25 21 5 p q r hp hq hr
  have h3 := paired_nonneg 26 20 5 p q r hp hq hr
  have h4 := paired_nonneg 27 19 5 p q r hp hq hr
  have h5 := paired_nonneg 28 18 5 p q r hp hq hr
  have h6 := paired_nonneg 29 17 5 p q r hp hq hr
  unfold positiveSlice5
  positivity

def positiveSlice6 (p q r : ℝ) : ℝ :=
  8794276088*pairedMonomial 23 22 6 p q r +
  6430027040*pairedMonomial 24 21 6 p q r +
  4523886771*pairedMonomial 25 20 6 p q r +
  3269762208*pairedMonomial 26 19 6 p q r +
  1814014164*pairedMonomial 27 18 6 p q r +
  686861745*pairedMonomial 28 17 6 p q r

private theorem slice6_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice6 p q r := by
  have h0 := paired_nonneg 23 22 6 p q r hp hq hr
  have h1 := paired_nonneg 24 21 6 p q r hp hq hr
  have h2 := paired_nonneg 25 20 6 p q r hp hq hr
  have h3 := paired_nonneg 26 19 6 p q r hp hq hr
  have h4 := paired_nonneg 27 18 6 p q r hp hq hr
  have h5 := paired_nonneg 28 17 6 p q r hp hq hr
  unfold positiveSlice6
  positivity

def positiveSlice7 (p q r : ℝ) : ℝ :=
  26247468288*pairedMonomial 22 22 7 p q r +
  22940308472*pairedMonomial 23 21 7 p q r +
  17275128516*pairedMonomial 24 20 7 p q r +
  13210829476*pairedMonomial 25 19 7 p q r +
  8981170920*pairedMonomial 26 18 7 p q r +
  4594212780*pairedMonomial 27 17 7 p q r

private theorem slice7_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice7 p q r := by
  have h0 := paired_nonneg 22 22 7 p q r hp hq hr
  have h1 := paired_nonneg 23 21 7 p q r hp hq hr
  have h2 := paired_nonneg 24 20 7 p q r hp hq hr
  have h3 := paired_nonneg 25 19 7 p q r hp hq hr
  have h4 := paired_nonneg 26 18 7 p q r hp hq hr
  have h5 := paired_nonneg 27 17 7 p q r hp hq hr
  unfold positiveSlice7
  positivity

def positiveSlice8 (p q r : ℝ) : ℝ :=
  60937077274*pairedMonomial 22 21 8 p q r +
  51524731584*pairedMonomial 23 20 8 p q r +
  41890112880*pairedMonomial 24 19 8 p q r +
  32043272883*pairedMonomial 25 18 8 p q r +
  19586982069*pairedMonomial 26 17 8 p q r

private theorem slice8_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice8 p q r := by
  have h0 := paired_nonneg 22 21 8 p q r hp hq hr
  have h1 := paired_nonneg 23 20 8 p q r hp hq hr
  have h2 := paired_nonneg 24 19 8 p q r hp hq hr
  have h3 := paired_nonneg 25 18 8 p q r hp hq hr
  have h4 := paired_nonneg 26 17 8 p q r hp hq hr
  unfold positiveSlice8
  positivity

def positiveSlice9 (p q r : ℝ) : ℝ :=
  131121471756*pairedMonomial 21 21 9 p q r +
  121919619725*pairedMonomial 22 20 9 p q r +
  104561900952*pairedMonomial 23 19 9 p q r +
  85710012316*pairedMonomial 24 18 9 p q r +
  59908854582*pairedMonomial 25 17 9 p q r

private theorem slice9_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice9 p q r := by
  have h0 := paired_nonneg 21 21 9 p q r hp hq hr
  have h1 := paired_nonneg 22 20 9 p q r hp hq hr
  have h2 := paired_nonneg 23 19 9 p q r hp hq hr
  have h3 := paired_nonneg 24 18 9 p q r hp hq hr
  have h4 := paired_nonneg 25 17 9 p q r hp hq hr
  unfold positiveSlice9
  positivity

def positiveSlice10 (p q r : ℝ) : ℝ :=
  246156714638*pairedMonomial 21 20 10 p q r +
  217979843552*pairedMonomial 22 19 10 p q r +
  182181426960*pairedMonomial 23 18 10 p q r +
  138398982264*pairedMonomial 24 17 10 p q r

private theorem slice10_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice10 p q r := by
  have h0 := paired_nonneg 21 20 10 p q r hp hq hr
  have h1 := paired_nonneg 22 19 10 p q r hp hq hr
  have h2 := paired_nonneg 23 18 10 p q r hp hq hr
  have h3 := paired_nonneg 24 17 10 p q r hp hq hr
  unfold positiveSlice10
  positivity

def positiveSlice11 (p q r : ℝ) : ℝ :=
  434723213784*pairedMonomial 20 20 11 p q r +
  403354654784*pairedMonomial 21 19 11 p q r +
  336762736136*pairedMonomial 22 18 11 p q r +
  263955969408*pairedMonomial 23 17 11 p q r

private theorem slice11_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice11 p q r := by
  have h0 := paired_nonneg 20 20 11 p q r hp hq hr
  have h1 := paired_nonneg 21 19 11 p q r hp hq hr
  have h2 := paired_nonneg 22 18 11 p q r hp hq hr
  have h3 := paired_nonneg 23 17 11 p q r hp hq hr
  unfold positiveSlice11
  positivity

def positiveSlice12 (p q r : ℝ) : ℝ :=
  651774508964*pairedMonomial 20 19 12 p q r +
  565207218120*pairedMonomial 21 18 12 p q r +
  453123772903*pairedMonomial 22 17 12 p q r

private theorem slice12_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice12 p q r := by
  have h0 := paired_nonneg 20 19 12 p q r hp hq hr
  have h1 := paired_nonneg 21 18 12 p q r hp hq hr
  have h2 := paired_nonneg 22 17 12 p q r hp hq hr
  unfold positiveSlice12
  positivity

def positiveSlice13 (p q r : ℝ) : ℝ :=
  896599559504*pairedMonomial 19 19 13 p q r +
  837188338706*pairedMonomial 20 18 13 p q r +
  709752652300*pairedMonomial 21 17 13 p q r

private theorem slice13_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice13 p q r := by
  have h0 := paired_nonneg 19 19 13 p q r hp hq hr
  have h1 := paired_nonneg 20 18 13 p q r hp hq hr
  have h2 := paired_nonneg 21 17 13 p q r hp hq hr
  unfold positiveSlice13
  positivity

def positiveSlice14 (p q r : ℝ) : ℝ :=
  1089028517556*pairedMonomial 19 18 14 p q r +
  984611113899*pairedMonomial 20 17 14 p q r

private theorem slice14_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice14 p q r := by
  have h0 := paired_nonneg 19 18 14 p q r hp hq hr
  have h1 := paired_nonneg 20 17 14 p q r hp hq hr
  unfold positiveSlice14
  positivity

def positiveSlice15 (p q r : ℝ) : ℝ :=
  1306480490248*pairedMonomial 18 18 15 p q r +
  1239974673312*pairedMonomial 19 17 15 p q r

private theorem slice15_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice15 p q r := by
  have h0 := paired_nonneg 18 18 15 p q r hp hq hr
  have h1 := paired_nonneg 19 17 15 p q r hp hq hr
  unfold positiveSlice15
  positivity

def positiveSlice16 (p q r : ℝ) : ℝ :=
  1462001693088*pairedMonomial 18 17 16 p q r

private theorem slice16_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice16 p q r := by
  have h0 := paired_nonneg 18 17 16 p q r hp hq hr
  unfold positiveSlice16
  positivity

def positiveSlice17 (p q r : ℝ) : ℝ :=
  1562862225726*pairedMonomial 17 17 17 p q r

private theorem slice17_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveSlice17 p q r := by
  have h0 := paired_nonneg 17 17 17 p q r hp hq hr
  unfold positiveSlice17
  positivity

def positiveCertificate (p q r : ℝ) : ℝ := boundaryCertificate p q r +
  positiveSlice1 p q r +
  positiveSlice2 p q r +
  positiveSlice3 p q r +
  positiveSlice4 p q r +
  positiveSlice5 p q r +
  positiveSlice6 p q r +
  positiveSlice7 p q r +
  positiveSlice8 p q r +
  positiveSlice9 p q r +
  positiveSlice10 p q r +
  positiveSlice11 p q r +
  positiveSlice12 p q r +
  positiveSlice13 p q r +
  positiveSlice14 p q r +
  positiveSlice15 p q r +
  positiveSlice16 p q r +
  positiveSlice17 p q r

theorem certificate_nonneg (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    0 ≤ positiveCertificate p q r := by
  have h0 := boundary_nonneg p q r hp hq hr
  have h1 := slice1_nonneg p q r hp hq hr
  have h2 := slice2_nonneg p q r hp hq hr
  have h3 := slice3_nonneg p q r hp hq hr
  have h4 := slice4_nonneg p q r hp hq hr
  have h5 := slice5_nonneg p q r hp hq hr
  have h6 := slice6_nonneg p q r hp hq hr
  have h7 := slice7_nonneg p q r hp hq hr
  have h8 := slice8_nonneg p q r hp hq hr
  have h9 := slice9_nonneg p q r hp hq hr
  have h10 := slice10_nonneg p q r hp hq hr
  have h11 := slice11_nonneg p q r hp hq hr
  have h12 := slice12_nonneg p q r hp hq hr
  have h13 := slice13_nonneg p q r hp hq hr
  have h14 := slice14_nonneg p q r hp hq hr
  have h15 := slice15_nonneg p q r hp hq hr
  have h16 := slice16_nonneg p q r hp hq hr
  have h17 := slice17_nonneg p q r hp hq hr
  unfold positiveCertificate
  positivity

theorem certificate_pos (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    0 < positiveCertificate p q r := by
  have h0 := boundary_nonneg p q r hp.le hq.le hr.le
  have h1 := slice1_nonneg p q r hp.le hq.le hr.le
  have h2 := slice2_nonneg p q r hp.le hq.le hr.le
  have h3 := slice3_nonneg p q r hp.le hq.le hr.le
  have h4 := slice4_nonneg p q r hp.le hq.le hr.le
  have h5 := slice5_nonneg p q r hp.le hq.le hr.le
  have h6 := slice6_nonneg p q r hp.le hq.le hr.le
  have h7 := slice7_nonneg p q r hp.le hq.le hr.le
  have h8 := slice8_nonneg p q r hp.le hq.le hr.le
  have h9 := slice9_nonneg p q r hp.le hq.le hr.le
  have h10 := slice10_nonneg p q r hp.le hq.le hr.le
  have h11 := slice11_nonneg p q r hp.le hq.le hr.le
  have h12 := slice12_nonneg p q r hp.le hq.le hr.le
  have h13 := slice13_nonneg p q r hp.le hq.le hr.le
  have h14 := slice14_nonneg p q r hp.le hq.le hr.le
  have h15 := slice15_nonneg p q r hp.le hq.le hr.le
  have h16 := slice16_nonneg p q r hp.le hq.le hr.le
  have h17 : 0 < positiveSlice17 p q r := by
    norm_num [positiveSlice17, pairedMonomial, monomialSymmetric] <;> positivity
  unfold positiveCertificate
  linarith

end D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients
