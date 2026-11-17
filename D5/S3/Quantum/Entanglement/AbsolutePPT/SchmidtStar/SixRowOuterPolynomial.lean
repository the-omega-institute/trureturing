/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.cap_interval_strict; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p2_mid,D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p1_mid_cut
   digest: Fixed exact polynomial bounds for the six-row scalar proof. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowOuterPolynomial
noncomputable section

open SixRowHeadPolynomial (row tensor tensor_nonneg)
open SixRowMiddlePolynomial (T138 cn)

def K : ℝ := 9280/2421
def th23 : ℝ := 2421/324818
def C (z : ℝ) : ℝ := th23*(z+K)^2+K
def F (d : ℝ) : ℝ :=
  -(322397*d^4-193680*d^3-28729280*d^2+45190400*d-45075200)/519708800
def Den (r : ℝ) : ℝ := 4-4*r-11*r^2
def An (r : ℝ) : ℝ := 4-6*r-8*r^2
def V (r q : ℝ) : ℝ := (2-q/2)^2-15*r^2
def T144 (r : ℝ) : ℝ := 4+4*r-35*r^2
def P1 (r q T : ℝ) : ℝ := T*Den r-cn r*V r q-Den r*(q+r*(6-15*r))
def P2 (r d T : ℝ) : ℝ :=
  T*Den r-An r*(4-d^2/10+d^4/1600-15*r^2)-Den r*(d^2/20+r*d)

private def quartic_0Data : List (List (List ℕ)) := [[[24286848, 51956992, 38879168, 19228432, 7697011]]]

private theorem quartic_0_identity (x : ℝ) :
    519708800*(F ((0 : ℝ)+(1 : ℝ)*x)-(1/25 : ℝ)) =
      tensor quartic_0Data 0 1 0 1 x (1-x) := by
  norm_num [quartic_0Data, tensor, row, F, C, K, th23, P1, P2,
    T138, T144, Den, An, cn, V] <;> ring

theorem quartic_0 (x : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) : (1/25 : ℝ) ≤ F ((0 : ℝ)+(1 : ℝ)*x) := by
  have hp := tensor_nonneg quartic_0Data 0 1 0 1 x (1-x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hx (by linarith)
  rw [← quartic_0_identity] at hp
  linarith only [hp]

private def quartic_1Data : List (List (List ℕ)) := [[[7697011, 42347656, 108236840, 119122848, 45214256]]]

private theorem quartic_1_identity (x : ℝ) :
    519708800*(F ((1 : ℝ)+(1 : ℝ)*x)-(1/25 : ℝ)) =
      tensor quartic_1Data 0 1 0 1 x (1-x) := by
  norm_num [quartic_1Data, tensor, row, F, C, K, th23, P1, P2,
    T138, T144, Den, An, cn, V] <;> ring

theorem quartic_1 (x : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) : (1/25 : ℝ) ≤ F ((1 : ℝ)+(1 : ℝ)*x) := by
  have hp := tensor_nonneg quartic_1Data 0 1 0 1 x (1-x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hx (by linarith)
  rw [← quartic_1_identity] at hp
  linarith only [hp]

private def quartic_2Data : List (List (List ℕ)) := [[[45214256, 242591200, 478641896, 407981720, 126394371]]]

private theorem quartic_2_identity (x : ℝ) :
    519708800*(F ((2 : ℝ)+(1 : ℝ)*x)-(1/25 : ℝ)) =
      tensor quartic_2Data 0 1 0 1 x (1-x) := by
  norm_num [quartic_2Data, tensor, row, F, C, K, th23, P1, P2,
    T138, T144, Den, An, cn, V] <;> ring

theorem quartic_2 (x : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) : (1/25 : ℝ) ≤ F ((2 : ℝ)+(1 : ℝ)*x) := by
  have hp := tensor_nonneg quartic_2Data 0 1 0 1 x (1-x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hx (by linarith)
  rw [← quartic_2_identity] at hp
  linarith only [hp]

private def p1_mid_cutData : List (List (List ℕ)) := [[[583091316289, 4337424000906, 6486950545209, 2561706017496, 20989599336]]]

private theorem p1_mid_cut_identity (x : ℝ) :
    8032296960000*(P1 ((1/12 : ℝ)+(7/60 : ℝ)*x) (3/32) (T138 ((1/12 : ℝ)+(7/60 : ℝ)*x))-(10797119/4131840000 : ℝ)) =
      tensor p1_mid_cutData 0 1 0 1 x (1-x) := by
  norm_num [p1_mid_cutData, tensor, row, F, C, K, th23, P1, P2,
    T138, T144, Den, An, cn, V] <;> ring

theorem p1_mid_cut (x : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) : (10797119/4131840000 : ℝ) ≤ P1 ((1/12 : ℝ)+(7/60 : ℝ)*x) (3/32) (T138 ((1/12 : ℝ)+(7/60 : ℝ)*x)) := by
  have hp := tensor_nonneg p1_mid_cutData 0 1 0 1 x (1-x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hx (by linarith)
  rw [← p1_mid_cut_identity] at hp
  linarith only [hp]

private def p1_mid_tailData : List (List (List ℕ)) := [[[36707231813, 220483798752, 342059423328, 184708242432, 29377821312]]]

private theorem p1_mid_tail_identity (x : ℝ) :
    62752320000*(P1 ((1/12 : ℝ)+(7/60 : ℝ)*x) (4-10*((1/12 : ℝ)+(7/60 : ℝ)*x)) (T138 ((1/12 : ℝ)+(7/60 : ℝ)*x))-(944503/2017500 : ℝ)) =
      tensor p1_mid_tailData 0 1 0 1 x (1-x) := by
  norm_num [p1_mid_tailData, tensor, row, F, C, K, th23, P1, P2,
    T138, T144, Den, An, cn, V] <;> ring

theorem p1_mid_tail (x : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) : (944503/2017500 : ℝ) ≤ P1 ((1/12 : ℝ)+(7/60 : ℝ)*x) (4-10*((1/12 : ℝ)+(7/60 : ℝ)*x)) (T138 ((1/12 : ℝ)+(7/60 : ℝ)*x)) := by
  have hp := tensor_nonneg p1_mid_tailData 0 1 0 1 x (1-x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hx (by linarith)
  rw [← p1_mid_tail_identity] at hp
  linarith only [hp]

private def p1_low_cutData : List (List (List ℕ)) := [[[972000, 6937056, 13655925, 10333386, 2679637]]]

private theorem p1_low_cut_identity (x : ℝ) :
    5308416*(P1 ((0 : ℝ)+(1/12 : ℝ)*x) (3/32) (T144 ((0 : ℝ)+(1/12 : ℝ)*x))-(375/2048 : ℝ)) =
      tensor p1_low_cutData 0 1 0 1 x (1-x) := by
  norm_num [p1_low_cutData, tensor, row, F, C, K, th23, P1, P2,
    T138, T144, Den, An, cn, V] <;> ring

theorem p1_low_cut (x : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) : (375/2048 : ℝ) ≤ P1 ((0 : ℝ)+(1/12 : ℝ)*x) (3/32) (T144 ((0 : ℝ)+(1/12 : ℝ)*x)) := by
  have hp := tensor_nonneg p1_low_cutData 0 1 0 1 x (1-x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hx (by linarith)
  rw [← p1_low_cut_identity] at hp
  linarith only [hp]

private def p1_low_tailData : List (List (List ℕ)) := [[[743771, 2465324, 2859852, 1291904, 158245]]]

private theorem p1_low_tail_identity (x : ℝ) :
    663552*(P1 ((0 : ℝ)+(1/12 : ℝ)*x) (29/8) (T144 ((0 : ℝ)+(1/12 : ℝ)*x))-(158245/663552 : ℝ)) =
      tensor p1_low_tailData 0 1 0 1 x (1-x) := by
  norm_num [p1_low_tailData, tensor, row, F, C, K, th23, P1, P2,
    T138, T144, Den, An, cn, V] <;> ring

theorem p1_low_tail (x : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) : (158245/663552 : ℝ) ≤ P1 ((0 : ℝ)+(1/12 : ℝ)*x) (29/8) (T144 ((0 : ℝ)+(1/12 : ℝ)*x)) := by
  have hp := tensor_nonneg p1_low_tailData 0 1 0 1 x (1-x)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hx (by linarith)
  rw [← p1_low_tail_identity] at hp
  linarith only [hp]

private def p2_midData : List (List (List ℕ)) := [[[1021338139734182582, 3442313775186730328, 4684549804592595492, 3127510842561730328, 852039295268397632], [5550924621436730328, 18853180350996921312, 25044819272209381968, 15733795977174921312, 3946598077131309693], [8628795437155095492, 28519323948820381968, 36233833697768072952, 21424877297695381968, 5019429418993243908], [4901894379436730328, 15132803707026921312, 17454385219168381968, 9117936835002921312, 1856489117796149265], [875043100459182582, 2313777039916730328, 2014967047867095492, 588775377820730328, 3976157140817418]]]

private theorem p2_mid_identity (x y : ℝ) :
    1568808000000000000*(P2 ((1/12 : ℝ)+(7/60 : ℝ)*x) ((137/100 : ℝ)*y) (T138 ((1/12 : ℝ)+(7/60 : ℝ)*x))-(8181393293863/3228000000000000 : ℝ)) =
      tensor p2_midData 0 1 x (1-x) y (1-y) := by
  norm_num [p2_midData, tensor, row, F, C, K, th23, P1, P2,
    T138, T144, Den, An, cn, V] <;> ring

theorem p2_mid (x y : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) (hy : 0 ≤ y) (hY : y ≤ 1) : (8181393293863/3228000000000000 : ℝ) ≤ P2 ((1/12 : ℝ)+(7/60 : ℝ)*x) ((137/100 : ℝ)*y) (T138 ((1/12 : ℝ)+(7/60 : ℝ)*x)) := by
  have hp := tensor_nonneg p2_midData 0 1 x (1-x) y (1-y)
    (by norm_num) (by norm_num) hx (by linarith) hy (by linarith)
  rw [← p2_mid_identity] at hp
  linarith only [hp]

private def p2_lowData : List (List (List ℕ)) := [[[0, 0, 9729849600000, 19459699200000, 9501575166072], [51840000000000, 195523200000000, 312827356800000, 246445113600000, 76416393368529], [136080000000000, 509796000000000, 766337712300000, 547607424600000, 153704839087404], [116730000000000, 433608450000000, 634330902600000, 434756455200000, 116482848733509], [32821250000000, 120660650000000, 173078197500000, 115459445000000, 30024077848562]]]

private theorem p2_low_identity (x y : ℝ) :
    25920000000000*(P2 ((0 : ℝ)+(1/12 : ℝ)*x) ((137/100 : ℝ)*y) (T144 ((0 : ℝ)+(1/12 : ℝ)*x))-(0 : ℝ)) =
      tensor p2_lowData 0 1 x (1-x) y (1-y) := by
  norm_num [p2_lowData, tensor, row, F, C, K, th23, P1, P2,
    T138, T144, Den, An, cn, V] <;> ring

theorem p2_low (x y : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) (hy : 0 ≤ y) (hY : y ≤ 1) : (0 : ℝ) ≤ P2 ((0 : ℝ)+(1/12 : ℝ)*x) ((137/100 : ℝ)*y) (T144 ((0 : ℝ)+(1/12 : ℝ)*x)) := by
  have hp := tensor_nonneg p2_lowData 0 1 x (1-x) y (1-y)
    (by norm_num) (by norm_num) hx (by linarith) hy (by linarith)
  rw [← p2_low_identity] at hp
  linarith only [hp]


private def lowSeparationData : List (List (List ℕ)) := [[[0, 0, 9729849600000, 19459699200000, 3021575166072], [51840000000000, 195523200000000, 312827356800000, 246445113600000, 50496393368529], [136080000000000, 509796000000000, 766337712300000, 547607424600000, 114824839087404], [116730000000000, 433608450000000, 634330902600000, 434756455200000, 90562848733509], [26341250000000, 94740650000000, 134198197500000, 89539445000000, 17064077848562]]]
private theorem p2_low_separation_fixed (x y : ℝ)
    (hx : 0 ≤ x) (hX : x ≤ 1) (hy : 0 ≤ y) (hY : y ≤ 1) :
    x^4/4+y^4/4 ≤ P2 (x/12) ((137/100)*y) (T144 (x/12)) := by
  have hid : 25920000000000*(P2 (x/12) ((137/100)*y) (T144 (x/12))-x^4/4-y^4/4) =
      tensor lowSeparationData 0 1 x (1-x) y (1-y) := by
    norm_num [lowSeparationData, tensor, row, P2, T144, Den, An] <;> ring
  have hp := tensor_nonneg lowSeparationData 0 1 x (1-x) y (1-y)
    (by norm_num) (by norm_num) hx (by linarith) hy (by linarith)
  rw [← hid] at hp
  linarith only [hp]

/-- Full closed [0,3] quartic bound, including all three shared faces. -/
theorem quartic_lower (d : ℝ) (hd : 0 ≤ d) (hd' : d ≤ 3) : 1/25 ≤ F d := by
  by_cases h1 : d ≤ 1
  · simpa using quartic_0 d hd h1
  by_cases h2 : d ≤ 2
  · have hh := quartic_1 (d-1) (by linarith) (by linarith)
    convert hh using 1 <;> congr 1 <;> ring
  · have hh := quartic_2 (d-2) (by linarith) (by linarith)
    convert hh using 1 <;> congr 1 <;> ring

/-- Quantitative zero separation for the low P2 table. The subtracted
    x^4 and y^4 terms use the positive last row/column, so endpoints 1
    are included without an open-face Bernstein argument. -/
theorem p2_low_separation (x y : ℝ)
    (hx : 0 ≤ x) (hX : x ≤ 1) (hy : 0 ≤ y) (hY : y ≤ 1) :
    x^4/4+y^4/4 ≤ P2 (x/12) ((137/100)*y) (T144 (x/12)) := by
  -- The fixed identity uses the low table after subtracting these
  -- two polynomials coefficientwise, with a literal ring identity.
  exact p2_low_separation_fixed x y hx hX hy hY

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowOuterPolynomial
