/- GID: D5/S3/Observer/CubicGain/StrictDriftVector
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/StrictDriftVector
   mirror-E: none(waiver:universal-source-inequality)
   anchors: []
   utility: none
   digest: The fourth and fifth M drift coefficients have no common zero on the full closed-r positive-b source. -/

import Mathlib.Tactic

/-! Drift nonvanishing for the literal chronological fifth-M observation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.CubicGain

noncomputable def sourceJ (r b : ℝ) : ℝ := b + r * (1-r) / b
noncomputable def sourceN (r b : ℝ) : ℝ := sourceJ r b + r
noncomputable def parentLambda (r b : ℝ) : ℝ :=
  1 + 6 / (1+b) + 1 / (1+2*b) - 4 / sourceJ r b - 4 / sourceN r b
noncomputable def fifthDrift (r b : ℝ) : ℝ :=
  1 + (1+2*b+sourceN r b) *
    (4 - 15 / sourceJ r b + 20 / (1+b) - 10 / sourceN r b)

def n4 (r b : ℝ) : ℝ :=
  let X := b^2+r-r^2
  let N := X+b*r
  2*(b^2+8*b+4)*X*N - 4*b*(1+b)*(1+2*b)*(X+N)

private def n5 (r b : ℝ) : ℝ :=
  let X := b^2+r-r^2
  let N := X+b*r
  let W := N+b*(1+2*b)
  b*(1+b)*X*N + W*(4*(b+6)*X*N-5*b*(1+b)*(3*N+2*X))

private def obstruction (b : ℝ) : ℝ :=
  27*b^16+198*b^15-24294*b^14-576939*b^13-5180250*b^12-
  22502243*b^11-56647044*b^10-93879326*b^9-112237206*b^8-
  103197064*b^7-77097576*b^6-49669216*b^5-28167328*b^4-
  13027456*b^3-4266880*b^2-834560*b-71680

set_option maxHeartbeats 2000000 in
-- Elaboration checks the complete explicit universal polynomial certificate.
private def bezout4 (r b : ℝ) : ℝ :=
      180 * b ^ 14 * r ^ 5
       + 11448 * b ^ 13 * r ^ 5
       + 278588 * b ^ 12 * r ^ 5
       + 3324536 * b ^ 11 * r ^ 5
       + 21415680 * b ^ 10 * r ^ 5
       + 80239992 * b ^ 9 * r ^ 5
       + 189220048 * b ^ 8 * r ^ 5
       + 289840160 * b ^ 7 * r ^ 5
       + 290137536 * b ^ 6 * r ^ 5
       + 192554624 * b ^ 5 * r ^ 5
       + 90390272 * b ^ 4 * r ^ 5
       + 35008000 * b ^ 3 * r ^ 5
       + 12178432 * b ^ 2 * r ^ 5
       + 3031040 * b ^ 1 * r ^ 5
       + 344064 * r ^ 5
       - 684 * b ^ 15 * r ^ 4
       - 34848 * b ^ 14 * r ^ 4
       - 718748 * b ^ 13 * r ^ 4
       - 7774964 * b ^ 12 * r ^ 4
       - 48877400 * b ^ 11 * r ^ 4
       - 193535744 * b ^ 10 * r ^ 4
       - 521736104 * b ^ 9 * r ^ 4
       - 985203184 * b ^ 8 * r ^ 4
       - 1293903200 * b ^ 7 * r ^ 4
       - 1169700672 * b ^ 6 * r ^ 4
       - 735302528 * b ^ 5 * r ^ 4
       - 340911360 * b ^ 4 * r ^ 4
       - 130714112 * b ^ 3 * r ^ 4
       - 42818560 * b ^ 2 * r ^ 4
       - 9781248 * b ^ 1 * r ^ 4
       - 1032192 * r ^ 4
       + 72 * b ^ 16 * r ^ 3
       - 10200 * b ^ 15 * r ^ 3
       - 463996 * b ^ 14 * r ^ 3
       - 6885364 * b ^ 13 * r ^ 3
       - 47933156 * b ^ 12 * r ^ 3
       - 180921832 * b ^ 11 * r ^ 3
       - 382541928 * b ^ 10 * r ^ 3
       - 365155864 * b ^ 9 * r ^ 3
       + 162714384 * b ^ 8 * r ^ 3
       + 862110048 * b ^ 7 * r ^ 3
       + 1074735040 * b ^ 6 * r ^ 3
       + 763142016 * b ^ 5 * r ^ 3
       + 376390400 * b ^ 4 * r ^ 3
       + 149383680 * b ^ 3 * r ^ 3
       + 48356352 * b ^ 2 * r ^ 3
       + 10469376 * b ^ 1 * r ^ 3
       + 1032192 * r ^ 3
       + 1764 * b ^ 17 * r ^ 2
       + 80541 * b ^ 16 * r ^ 2
       + 1455821 * b ^ 15 * r ^ 2
       + 13686031 * b ^ 14 * r ^ 2
       + 76689615 * b ^ 13 * r ^ 2
       + 294226936 * b ^ 12 * r ^ 2
       + 844655062 * b ^ 11 * r ^ 2
       + 1766329022 * b ^ 10 * r ^ 2
       + 2513890896 * b ^ 9 * r ^ 2
       + 2307463416 * b ^ 8 * r ^ 2
       + 1283011648 * b ^ 7 * r ^ 2
       + 357210464 * b ^ 6 * r ^ 2
       - 23135744 * b ^ 5 * r ^ 2
       - 73011584 * b ^ 4 * r ^ 2
       - 43983360 * b ^ 3 * r ^ 2
       - 16841728 * b ^ 2 * r ^ 2
       - 3719168 * b ^ 1 * r ^ 2
       - 344064 * r ^ 2
       - 684 * b ^ 18 * r ^ 1
       - 13452 * b ^ 17 * r ^ 1
       + 111395 * b ^ 16 * r ^ 1
       + 4154677 * b ^ 15 * r ^ 1
       + 36601398 * b ^ 14 * r ^ 1
       + 166495804 * b ^ 13 * r ^ 1
       + 420628018 * b ^ 12 * r ^ 1
       + 503825006 * b ^ 11 * r ^ 1
       - 47868460 * b ^ 10 * r ^ 1
       - 1003630968 * b ^ 9 * r ^ 1
       - 1488429264 * b ^ 8 * r ^ 1
       - 1202221152 * b ^ 7 * r ^ 1
       - 642851648 * b ^ 6 * r ^ 1
       - 249612928 * b ^ 5 * r ^ 1
       - 71747840 * b ^ 4 * r ^ 1
       - 13651968 * b ^ 3 * r ^ 1
       - 1232896 * b ^ 2 * r ^ 1
       - 1080 * b ^ 19
       - 33408 * b ^ 18
       - 242412 * b ^ 17
       + 1591942 * b ^ 16
       + 29436208 * b ^ 15
       + 153787725 * b ^ 14
       + 393501381 * b ^ 13
       + 549540944 * b ^ 12
       + 429989744 * b ^ 11
       + 212198910 * b ^ 10
       + 155463680 * b ^ 9
       + 208940552 * b ^ 8
       + 213744448 * b ^ 7
       + 148939040 * b ^ 6
       + 72306944 * b ^ 5
       + 23307648 * b ^ 4
       + 4387840 * b ^ 3
       + 358400 * b ^ 2

set_option maxHeartbeats 2000000 in
-- Elaboration checks the complete explicit universal polynomial certificate.
private def bezout5 (r b : ℝ) : ℝ :=
      90 * b ^ 15 * r ^ 3
       + 5904 * b ^ 14 * r ^ 3
       + 150022 * b ^ 13 * r ^ 3
       + 1899384 * b ^ 12 * r ^ 3
       + 13166856 * b ^ 11 * r ^ 3
       + 53430652 * b ^ 10 * r ^ 3
       + 137817440 * b ^ 9 * r ^ 3
       + 235375616 * b ^ 8 * r ^ 3
       + 270615808 * b ^ 7 * r ^ 3
       + 212812928 * b ^ 6 * r ^ 3
       + 118811136 * b ^ 5 * r ^ 3
       + 51307520 * b ^ 4 * r ^ 3
       + 19056640 * b ^ 3 * r ^ 3
       + 5905408 * b ^ 2 * r ^ 3
       + 1220608 * b ^ 1 * r ^ 3
       + 114688 * r ^ 3
       - 252 * b ^ 16 * r ^ 2
       - 12114 * b ^ 15 * r ^ 2
       - 235560 * b ^ 14 * r ^ 2
       - 2433848 * b ^ 13 * r ^ 2
       - 15010288 * b ^ 12 * r ^ 2
       - 60770724 * b ^ 11 * r ^ 2
       - 177308344 * b ^ 10 * r ^ 2
       - 382085824 * b ^ 9 * r ^ 2
       - 593571840 * b ^ 8 * r ^ 2
       - 650061184 * b ^ 7 * r ^ 2
       - 501696768 * b ^ 6 * r ^ 2
       - 281023488 * b ^ 5 * r ^ 2
       - 122390528 * b ^ 4 * r ^ 2
       - 44598272 * b ^ 3 * r ^ 2
       - 13105152 * b ^ 2 * r ^ 2
       - 2555904 * b ^ 1 * r ^ 2
       - 229376 * r ^ 2
       + 54 * b ^ 17 * r ^ 1
       + 588 * b ^ 16 * r ^ 1
       - 24362 * b ^ 15 * r ^ 1
       - 496508 * b ^ 14 * r ^ 1
       - 3732434 * b ^ 13 * r ^ 1
       - 16387296 * b ^ 12 * r ^ 1
       - 41112052 * b ^ 11 * r ^ 1
       - 36880500 * b ^ 10 * r ^ 1
       + 71801552 * b ^ 9 * r ^ 1
       + 257688000 * b ^ 8 * r ^ 1
       + 365277888 * b ^ 7 * r ^ 1
       + 315427200 * b ^ 6 * r ^ 1
       + 189585152 * b ^ 5 * r ^ 1
       + 86548480 * b ^ 4 * r ^ 1
       + 31209472 * b ^ 3 * r ^ 1
       + 8420352 * b ^ 2 * r ^ 1
       + 1449984 * b ^ 1 * r ^ 1
       + 114688 * r ^ 1
       + 180 * b ^ 18
       + 5556 * b ^ 17
       + 39320 * b ^ 16
       - 298030 * b ^ 15
       - 5353380 * b ^ 14
       - 28597384 * b ^ 13
       - 74961340 * b ^ 12
       - 106302376 * b ^ 11
       - 81574504 * b ^ 10
       - 34861008 * b ^ 9
       - 24052448 * b ^ 8
       - 41059008 * b ^ 7
       - 47594368 * b ^ 6
       - 35535616 * b ^ 5
       - 18255360 * b ^ 4
       - 6274048 * b ^ 3
       - 1277952 * b ^ 2
       - 114688 * b ^ 1

set_option maxHeartbeats 2000000 in
-- Exact polynomial expansion and denominator clearing use the larger finite allowance.
private theorem bezout_identity (r b : ℝ) :
    bezout4 r b * n4 r b + bezout5 r b * n5 r b =
      4*b^6*(1+b)*(1+2*b)*obstruction b := by
  unfold bezout4 bezout5 n4 n5 obstruction
  ring

set_option maxHeartbeats 2000000 in
-- Exact polynomial expansion and denominator clearing use the larger finite allowance.
private theorem obstruction_neg (b : ℝ) (hb : 0 < b) (hb4 : b < 4) :
    obstruction b < 0 := by
  have hb2 : b^2 < 16 := by nlinarith
  have htop : 27*b^2+198*b-24294 < 0 := by nlinarith
  have hrest : 0 < 576939*b^13+5180250*b^12+
      22502243*b^11+56647044*b^10+93879326*b^9+112237206*b^8+
      103197064*b^7+77097576*b^6+49669216*b^5+28167328*b^4+
      13027456*b^3+4266880*b^2+834560*b+71680 := by positivity
  have heq : obstruction b = b^14*(27*b^2+198*b-24294) -
      (576939*b^13+5180250*b^12+22502243*b^11+56647044*b^10+
      93879326*b^9+112237206*b^8+103197064*b^7+77097576*b^6+
      49669216*b^5+28167328*b^4+13027456*b^3+4266880*b^2+834560*b+71680) := by
    unfold obstruction
    ring
  rw [heq]
  have := mul_neg_of_pos_of_neg (pow_pos hb 14) htop
  linarith

/-- The fourth numerator in source coordinates. -/
theorem n4_parentLambda (r b : ℝ) (hb : b ≠ 0)
    (hj : sourceJ r b ≠ 0) (hn : sourceN r b ≠ 0)
    (ht : 1+b ≠ 0) (hu : 1+2*b ≠ 0) : n4 r b =
    (1+b)*(1+2*b)*(b^2+r-r^2)*(b^2+r-r^2+b*r)*parentLambda r b := by
  unfold n4 parentLambda
  field_simp [hb,hj,hn,ht,hu]
  unfold sourceN sourceJ
  field_simp [hb]
  <;> ring

/-- The fourth drift coefficient is positive for large positive off-diagonal entry. -/
theorem parentLambda_pos_of_four_le (r b : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hb : 0 < b) (hb4 : 4 ≤ b) : 0 < parentLambda r b := by
  have hc : 0 ≤ r*(1-r)/b := div_nonneg (mul_nonneg hr (by linarith)) hb.le
  have hjb : b ≤ sourceJ r b := by unfold sourceJ; linarith
  have hnb : b ≤ sourceN r b := by unfold sourceN; linarith
  have hji : 4 / sourceJ r b ≤ 4 / b := div_le_div_of_nonneg_left (by norm_num) hb hjb
  have hni : 4 / sourceN r b ≤ 4 / b := div_le_div_of_nonneg_left (by norm_num) hb hnb
  have hnum : 0 < b^2-b-8 := by nlinarith
  have hbase : 0 < 1 + 6/(1+b) - 8/b := by
    have heq : 1+6/(1+b)-8/b = (b^2-b-8)/(b*(1+b)) := by field_simp; ring
    rw [heq]
    exact div_pos hnum (by positivity)
  unfold parentLambda
  have : 0 < 1/(1+2*b) := by positivity
  linarith [show (8 : ℝ)/b = 4/b+4/b by ring]

set_option maxHeartbeats 2000000 in
-- Exact polynomial expansion and denominator clearing use the larger finite allowance.
/-- Endpoints in r are included; no drift, gain, degree, or chart assumption occurs. -/
theorem drift_vector_nonzero (r b : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hb : 0 < b) :
    parentLambda r b ≠ 0 ∨ fifthDrift r b ≠ 0 := by
  have hc : 0 ≤ r*(1-r)/b := div_nonneg (mul_nonneg hr (by linarith)) hb.le
  have hj : 0 < sourceJ r b := by unfold sourceJ; linarith
  have hn : 0 < sourceN r b := by unfold sourceN; linarith
  have ht : 0 < 1+b := by positivity
  have hu : 0 < 1+2*b := by positivity
  by_cases hb4 : b < 4
  · by_contra h
    push_neg at h
    obtain ⟨hl,ha⟩ := h
    have hf : n4 r b = 0 := by
      rw [n4_parentLambda r b (ne_of_gt hb) (ne_of_gt hj) (ne_of_gt hn)
        (ne_of_gt ht) (ne_of_gt hu),hl,mul_zero]
    have hg : n5 r b = 0 := by
      have heq : n5 r b = b*(1+b)*(b^2+r-r^2)*(b^2+r-r^2+b*r)*fifthDrift r b := by
        unfold n5 fifthDrift sourceN sourceJ
        field_simp
        <;> ring
      rw [heq,ha,mul_zero]
    have hid := bezout_identity r b
    rw [hf,hg,mul_zero,mul_zero,add_zero] at hid
    have hneg : 4*b^6*(1+b)*(1+2*b)*obstruction b < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (obstruction_neg b hb hb4)
    linarith
  · left
    exact ne_of_gt (parentLambda_pos_of_four_le r b hr hr1 hb (le_of_not_gt hb4))

#print axioms drift_vector_nonzero

end D5.S3.Observer.CubicGain
