/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/Selection
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/Selection
   mirror-E: none(waiver:adjacent-tail-physical-source)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Integer mask selection in the low and high dyadic regimes. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.HighBCertificates
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusThreeLarge
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusThreeAtTwo
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusThreeAtThree
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusThreeAtFour
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusTwoLarge
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusTwoAtTwo
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusTwoAtThree
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Dyadic
import Batteries.Tactic.OpenPrivate

set_option maxErrors 20
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
open private A B L K SU SV SW E F Common Residual StocksAndResidual HighResidual Windows ceilDiv residueRepresentative chooseM3 chooseV2 chooseM2
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Algebra
open private PlusTwo.positive_1 PlusTwo.negative_1 PlusTwo.positive_2 PlusTwo.negative_2 PlusTwo.positive_4 PlusTwo.negative_4 PlusTwo.positive_large PlusTwo.negative_large
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusTwoLarge
open private PlusTwo.small_a2_cmod0 PlusTwo.small_a2_cmod1 PlusTwo.small_a2_cmod2 PlusTwo.small_a2_cmod3
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusTwoAtTwo
open private PlusTwo.small_a3_cmod0 PlusTwo.small_a3_cmod1 PlusTwo.small_a3_cmod2 PlusTwo.small_a3_cmod3 PlusTwo.small_a3_cmod4 PlusTwo.small_a3_cmod5
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusTwoAtThree
open private PlusThree.positive_1 PlusThree.negative_1 PlusThree.positive_2 PlusThree.negative_2 PlusThree.positive_4 PlusThree.negative_4 PlusThree.positive_8 PlusThree.negative_8 PlusThree.positive_large PlusThree.negative_large
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusThreeLarge
open private PlusThree.small_a2_cmod0 PlusThree.small_a2_cmod1 PlusThree.small_a2_cmod2 PlusThree.small_a2_cmod3
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusThreeAtTwo
open private PlusThree.small_a3_cmod0 PlusThree.small_a3_cmod1 PlusThree.small_a3_cmod2 PlusThree.small_a3_cmod3 PlusThree.small_a3_cmod4 PlusThree.small_a3_cmod5
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusThreeAtThree
open private PlusThree.small_a4_cmod0 PlusThree.small_a4_cmod1 PlusThree.small_a4_cmod2 PlusThree.small_a4_cmod3 PlusThree.small_a4_cmod4 PlusThree.small_a4_cmod5 PlusThree.small_a4_cmod6 PlusThree.small_a4_cmod7
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.PlusThreeAtFour
open private HighB.common HighB.large_b HighB.a_at_least_three HighB.a_two_b_c_plus_four_r1 HighB.a_two_b_c_plus_four_r2 HighB.a_two_b_c_plus_four_r3 HighB.a_two_b_c_plus_four_r4
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.HighBCertificates

open private periodic_nonnegative_inverse dyadic_residue_integer_quotient
  dyadic_small_or_large dyadic_residue plus_two_orthant_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Dyadic

private theorem common_bounds (x z q : ℚ) (hx : 4≤x) (hz : 2*x≤z) (hq : 4≤q) :
    Common x z q := by
  have hh := HighB.common (x-4) (z-2*x) (q-4) (by linarith) (by linarith) (by linarith)
  convert hh using 1 <;> ring

private theorem continuous_second_bound (x z q : ℚ)
    (hx : 4≤x) (hz : 2*x≤z) (h : 32≤q ∨ (8≤x ∧ 16≤q)) :
    0≤A x z q-1-4*L x z-2*q*z*(z+1) := by
  rcases h with hq|⟨hx8,hq⟩
  · have hh := HighB.large_b (x-4) (z-2*x) (q-32) (by linarith) (by linarith) (by linarith)
    convert hh using 1 <;> dsimp [A,L] <;> ring
  · have hh := HighB.a_at_least_three (x-8) (z-2*x) (q-16) (by linarith) (by linarith) (by linarith)
    convert hh using 1 <;> dsimp [A,L] <;> ring

private theorem plus_three_residue_selection (x z u : ℚ) (negative : Bool)
    (hx : 32≤x) (hz : 2*x≤z) (hu : 1≤u) (hux : 2*u≤x)
    (hdyadic : u=1 ∨ u=2 ∨ u=4 ∨ u=8 ∨ 16≤u)
    : ∃ v m : ℚ, v=0 ∧ m=chooseM3 x z u negative ∧ Residual x z 8 v m := by
  have hd : x+1≠0 := by linarith
  rcases hdyadic with h1|h2|h4|h8|hlarge
  · subst u
    cases negative with
    | false =>
      refine ⟨0,((-7) + ((1 / ((1 + x) ^ 1)) * ((-1) + (8 * z)))),rfl,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · have hh := PlusThree.positive_1 (((-32) + x)) ((z + ((-2) * x))) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring
    | true =>
      refine ⟨0,((-6) + ((1 / ((1 + x) ^ 1)) * (((-1) * x) + (8 * z)))),rfl,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · have hh := PlusThree.negative_1 (((-32) + x)) ((z + ((-2) * x))) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring
  · subst u
    cases negative with
    | false =>
      refine ⟨0,((-7) + ((1 / ((1 + x) ^ 1)) * ((-2) + (8 * z)))),rfl,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · have hh := PlusThree.positive_2 (((-32) + x)) ((z + ((-2) * x))) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring
    | true =>
      refine ⟨0,((-6) + ((1 / ((1 + x) ^ 1)) * (1 + ((-1) * x) + (8 * z)))),rfl,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · have hh := PlusThree.negative_2 (((-32) + x)) ((z + ((-2) * x))) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring
  · subst u
    cases negative with
    | false =>
      refine ⟨0,((-7) + ((1 / ((1 + x) ^ 1)) * ((-4) + (8 * z)))),rfl,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · have hh := PlusThree.positive_4 (((-32) + x)) ((z + ((-2) * x))) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring
    | true =>
      refine ⟨0,((-6) + ((1 / ((1 + x) ^ 1)) * (3 + ((-1) * x) + (8 * z)))),rfl,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · have hh := PlusThree.negative_4 (((-32) + x)) ((z + ((-2) * x))) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring
  · subst u
    cases negative with
    | false =>
      refine ⟨0,((-7) + ((1 / ((1 + x) ^ 1)) * ((-8) + (8 * z)))),rfl,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · have hh := PlusThree.positive_8 (((-32) + x)) ((z + ((-2) * x))) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring
    | true =>
      refine ⟨0,((-6) + ((1 / ((1 + x) ^ 1)) * (7 + ((-1) * x) + (8 * z)))),rfl,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · have hh := PlusThree.negative_8 (((-32) + x)) ((z + ((-2) * x))) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring
  · have hu0 : 0≤u-16 := by linarith
    cases negative with
    | false =>
      refine ⟨0,((-7) + ((1 / ((1 + x) ^ 1)) * (((-1) * u) + (8 * z)))),rfl,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative, show ¬u≤8 by linarith, show ¬u≤4 by linarith, show u≠1 by linarith, show u≠2 by linarith, show u≠4 by linarith] <;> field_simp [hd] <;> ring
      · have hh := PlusThree.positive_large (((-16) + u)) ((x + ((-2) * u))) ((z + ((-2) * x))) (by linarith) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring
    | true =>
      refine ⟨0,((-7) + ((1 / ((1 + x) ^ 1)) * ((-1) + u + ((-1) * x) + (8 * z)))),rfl,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative, show ¬u≤8 by linarith, show ¬u≤4 by linarith, show u≠1 by linarith, show u≠2 by linarith, show u≠4 by linarith] <;> field_simp [hd] <;> ring
      · have hh := PlusThree.negative_large (((-16) + u)) ((x + ((-2) * u))) ((z + ((-2) * x))) (by linarith) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring

private theorem plus_two_residue_selection (x z u : ℚ) (negative : Bool)
    (hx : 16≤x) (hz : 2*x≤z) (hu : 1≤u) (hux : 2*u≤x)
    (hdyadic : u=1 ∨ u=2 ∨ u=4 ∨ 8≤u)
    (heven : negative=false → u*x^2/4≤z)
    (hodd : negative=true → u≤4 → x^2≤z)
    : ∃ v m : ℚ, v=chooseV2 x u negative ∧ m=chooseM2 x z u negative ∧ StocksAndResidual x z 4 v m := by
  have hd : x+1≠0 := by linarith
  rcases hdyadic with h1|h2|h4|hlarge
  · subst u
    cases negative with
    | false =>
      have horth : ((1 / 4) * (x ^ 2))≤z := by convert heven rfl using 1 <;> ring
      refine ⟨((-1) + ((1 / 8) * x)),(1 + ((-1 / 2) * x) + ((1 / ((1 + x) ^ 1)) * ((-1) + (4 * z)))),?_,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · have hh := PlusTwo.positive_1 (((-16) + x)) ((z + ((-1 / 4) * (x ^ 2)))) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring
    | true =>
      have horth : x^2≤z := hodd rfl (by norm_num)
      refine ⟨((1 / 8) * x),((-2) + ((-1 / 2) * x) + ((1 / ((1 + x) ^ 1)) * (((-1) * x) + (4 * z)))),?_,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · have hh := PlusTwo.negative_1 (((-16) + x)) ((z + ((-1) * (x ^ 2)))) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring
  · subst u
    cases negative with
    | false =>
      have horth : ((1 / 2) * (x ^ 2))≤z := by convert heven rfl using 1 <;> ring
      refine ⟨((1 / 8) * x),((-3) + ((-1 / 2) * x) + ((1 / ((1 + x) ^ 1)) * ((-2) + (4 * z)))),?_,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · have hh := PlusTwo.positive_2 (((-16) + x)) ((z + ((-1 / 2) * (x ^ 2)))) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring
    | true =>
      have horth : x^2≤z := hodd rfl (by norm_num)
      refine ⟨((1 / 8) * x),((-2) + ((-1 / 2) * x) + ((1 / ((1 + x) ^ 1)) * (1 + ((-1) * x) + (4 * z)))),?_,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · have hh := PlusTwo.negative_2 (((-16) + x)) ((z + ((-1) * (x ^ 2)))) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring
  · subst u
    cases negative with
    | false =>
      have horth : (x ^ 2)≤z := by convert heven rfl using 1 <;> ring
      refine ⟨((-1) + ((1 / 8) * x)),(1 + ((-1 / 2) * x) + ((1 / ((1 + x) ^ 1)) * ((-4) + (4 * z)))),?_,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · have hh := PlusTwo.positive_4 (((-16) + x)) ((z + ((-1) * (x ^ 2)))) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring
    | true =>
      have horth : x^2≤z := hodd rfl (by norm_num)
      refine ⟨(1 + ((1 / 8) * x)),((-6) + ((-1 / 2) * x) + ((1 / ((1 + x) ^ 1)) * (3 + ((-1) * x) + (4 * z)))),?_,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative] <;> field_simp [hd] <;> ring
      · have hh := PlusTwo.negative_4 (((-16) + x)) ((z + ((-1) * (x ^ 2)))) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring
  · have hu0 : 0≤u-8 := by linarith
    cases negative with
    | false =>
      have horth : ((1 / 4) * u * (x ^ 2))≤z := by convert heven rfl using 1 <;> ring
      refine ⟨(((-1 / 4) * u) + ((1 / 8) * x)),((-3) + u + ((-1 / 2) * x) + ((1 / ((1 + x) ^ 1)) * (((-1) * u) + (4 * z)))),?_,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative, show ¬u≤4 by linarith, show u≠1 by linarith, show u≠2 by linarith, show u≠4 by linarith] <;> field_simp [hd] <;> ring
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative, show ¬u≤4 by linarith, show u≠1 by linarith, show u≠2 by linarith, show u≠4 by linarith] <;> field_simp [hd] <;> ring
      · have hh := PlusTwo.positive_large (((-8) + u)) ((x + ((-2) * u))) ((z + ((-1 / 4) * u * (x ^ 2)))) (by linarith) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring
    | true =>
      refine ⟨0,((-3) + ((1 / ((1 + x) ^ 1)) * ((-1) + u + ((-1) * x) + (4 * z)))),?_,?_,?_⟩
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative, show ¬u≤4 by linarith, show u≠1 by linarith, show u≠2 by linarith, show u≠4 by linarith] <;> field_simp [hd] <;> ring
      · norm_num [chooseM3,chooseM2,chooseV2,residueRepresentative, show ¬u≤4 by linarith, show u≠1 by linarith, show u≠2 by linarith, show u≠4 by linarith] <;> field_simp [hd] <;> ring
      · have hh := PlusTwo.negative_large (((-8) + u)) ((x + ((-2) * u))) ((z + ((-2) * x))) (by linarith) (by linarith) (by linarith)
        convert hh using 1 <;> ring_nf <;> field_simp <;> ring

private theorem plus_three_periodic_selection (a c : ℕ) (ha : 2≤a) (hamax : a≤4) (hac : a<c)
    (hex : ¬(a=2 ∧ c=3)) :
    ∃ v m : ℤ, StocksAndResidual ((2:ℚ)^a) ((2:ℚ)^c) 8 (v:ℚ) (m:ℚ) := by
  interval_cases a
  · have hrem : c%4=0 ∨ c%4=1 ∨ c%4=2 ∨ c%4=3 := by omega
    rcases hrem with hr|hr|hr|hr
    · have hc0 : 4≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 2 c 4 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=16+5*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a2_cmod0 (T:ℚ) hTQ
      refine ⟨0,8*T+20,?_⟩
      norm_num only [show (2:ℚ)^2=4 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 5≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 2 c 5 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=32+5*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a2_cmod1 (T:ℚ) hTQ
      refine ⟨2,8*T+33,?_⟩
      norm_num only [show (2:ℚ)^2=4 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 6≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 2 c 6 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=64+5*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a2_cmod2 (T:ℚ) hTQ
      refine ⟨0,8*T+97,?_⟩
      norm_num only [show (2:ℚ)^2=4 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 7≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 2 c 7 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=128+5*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a2_cmod3 (T:ℚ) hTQ
      refine ⟨1,8*T+193,?_⟩
      norm_num only [show (2:ℚ)^2=4 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
  · have hrem : c%6=0 ∨ c%6=1 ∨ c%6=2 ∨ c%6=3 ∨ c%6=4 ∨ c%6=5 := by omega
    rcases hrem with hr|hr|hr|hr|hr|hr
    · have hc0 : 6≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 3 c 6 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=64+9*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a3_cmod0 (T:ℚ) hTQ
      refine ⟨2,8*T+36,?_⟩
      norm_num only [show (2:ℚ)^3=8 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 7≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 3 c 7 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=128+9*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a3_cmod1 (T:ℚ) hTQ
      refine ⟨1,8*T+100,?_⟩
      norm_num only [show (2:ℚ)^3=8 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 8≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 3 c 8 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=256+9*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a3_cmod2 (T:ℚ) hTQ
      refine ⟨0,8*T+221,?_⟩
      norm_num only [show (2:ℚ)^3=8 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 9≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 3 c 9 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=512+9*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a3_cmod3 (T:ℚ) hTQ
      refine ⟨0,8*T+449,?_⟩
      norm_num only [show (2:ℚ)^3=8 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 4≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 3 c 4 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=16+9*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a3_cmod4 (T:ℚ) hTQ
      refine ⟨0,8*T+8,?_⟩
      norm_num only [show (2:ℚ)^3=8 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 5≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 3 c 5 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=32+9*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a3_cmod5 (T:ℚ) hTQ
      refine ⟨0,8*T+22,?_⟩
      norm_num only [show (2:ℚ)^3=8 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
  · have hrem : c%8=0 ∨ c%8=1 ∨ c%8=2 ∨ c%8=3 ∨ c%8=4 ∨ c%8=5 ∨ c%8=6 ∨ c%8=7 := by omega
    rcases hrem with hr|hr|hr|hr|hr|hr|hr|hr
    · have hc0 : 8≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 4 c 8 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=256+17*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a4_cmod0 (T:ℚ) hTQ
      refine ⟨1,8*T+106,?_⟩
      norm_num only [show (2:ℚ)^4=16 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 9≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 4 c 9 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=512+17*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a4_cmod1 (T:ℚ) hTQ
      refine ⟨0,8*T+234,?_⟩
      norm_num only [show (2:ℚ)^4=16 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 10≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 4 c 10 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=1024+17*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a4_cmod2 (T:ℚ) hTQ
      refine ⟨0,8*T+475,?_⟩
      norm_num only [show (2:ℚ)^4=16 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 11≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 4 c 11 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=2048+17*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a4_cmod3 (T:ℚ) hTQ
      refine ⟨0,8*T+957,?_⟩
      norm_num only [show (2:ℚ)^4=16 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 12≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 4 c 12 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=4096+17*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a4_cmod4 (T:ℚ) hTQ
      refine ⟨0,8*T+1921,?_⟩
      norm_num only [show (2:ℚ)^4=16 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 5≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 4 c 5 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=32+17*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a4_cmod5 (T:ℚ) hTQ
      refine ⟨0,8*T+8,?_⟩
      norm_num only [show (2:ℚ)^4=16 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 6≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 4 c 6 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=64+17*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a4_cmod6 (T:ℚ) hTQ
      refine ⟨0,8*T+23,?_⟩
      norm_num only [show (2:ℚ)^4=16 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 7≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 4 c 7 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=128+17*(T:ℚ) := by exact_mod_cast he
      have hh := PlusThree.small_a4_cmod7 (T:ℚ) hTQ
      refine ⟨0,8*T+53,?_⟩
      norm_num only [show (2:ℚ)^4=16 by norm_num]
      rw [heQ]
      refine ⟨by norm_num,?_,?_⟩
      · norm_num; linarith
      · convert hh using 1 <;> push_cast <;> ring

private theorem plus_two_periodic_selection (a c : ℕ) (ha : 2≤a) (hamax : a≤3) (hac : a<c)
    (hex : ¬(a=2 ∧ c=3) ∧ ¬(a=2 ∧ c=5)) :
    ∃ v m : ℤ, StocksAndResidual ((2:ℚ)^a) ((2:ℚ)^c) 4 (v:ℚ) (m:ℚ) := by
  interval_cases a
  · have hrem : c%4=0 ∨ c%4=1 ∨ c%4=2 ∨ c%4=3 := by omega
    rcases hrem with hr|hr|hr|hr
    · have hc0 : 4≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 2 c 4 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=16+5*(T:ℚ) := by exact_mod_cast he
      have hh := PlusTwo.small_a2_cmod0 (T:ℚ) hTQ
      refine ⟨0,4*T+10,?_⟩
      norm_num only [show (2:ℚ)^2=4 by norm_num]
      rw [heQ]
      convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 9≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 2 c 9 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=512+5*(T:ℚ) := by exact_mod_cast he
      have hh := PlusTwo.small_a2_cmod1 (T:ℚ) hTQ
      refine ⟨4,4*T+394,?_⟩
      norm_num only [show (2:ℚ)^2=4 by norm_num]
      rw [heQ]
      convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 6≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 2 c 6 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=64+5*(T:ℚ) := by exact_mod_cast he
      have hh := PlusTwo.small_a2_cmod2 (T:ℚ) hTQ
      refine ⟨2,4*T+42,?_⟩
      norm_num only [show (2:ℚ)^2=4 by norm_num]
      rw [heQ]
      convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 7≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 2 c 7 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=128+5*(T:ℚ) := by exact_mod_cast he
      have hh := PlusTwo.small_a2_cmod3 (T:ℚ) hTQ
      refine ⟨3,4*T+90,?_⟩
      norm_num only [show (2:ℚ)^2=4 by norm_num]
      rw [heQ]
      convert hh using 1 <;> push_cast <;> ring
  · have hrem : c%6=0 ∨ c%6=1 ∨ c%6=2 ∨ c%6=3 ∨ c%6=4 ∨ c%6=5 := by omega
    rcases hrem with hr|hr|hr|hr|hr|hr
    · have hc0 : 6≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 3 c 6 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=64+9*(T:ℚ) := by exact_mod_cast he
      have hh := PlusTwo.small_a3_cmod0 (T:ℚ) hTQ
      refine ⟨2,4*T+18,?_⟩
      norm_num only [show (2:ℚ)^3=8 by norm_num]
      rw [heQ]
      convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 7≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 3 c 7 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=128+9*(T:ℚ) := by exact_mod_cast he
      have hh := PlusTwo.small_a3_cmod1 (T:ℚ) hTQ
      refine ⟨1,4*T+50,?_⟩
      norm_num only [show (2:ℚ)^3=8 by norm_num]
      rw [heQ]
      convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 8≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 3 c 8 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=256+9*(T:ℚ) := by exact_mod_cast he
      have hh := PlusTwo.small_a3_cmod2 (T:ℚ) hTQ
      refine ⟨1,4*T+107,?_⟩
      norm_num only [show (2:ℚ)^3=8 by norm_num]
      rw [heQ]
      convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 9≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 3 c 9 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=512+9*(T:ℚ) := by exact_mod_cast he
      have hh := PlusTwo.small_a3_cmod3 (T:ℚ) hTQ
      refine ⟨4,4*T+210,?_⟩
      norm_num only [show (2:ℚ)^3=8 by norm_num]
      rw [heQ]
      convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 4≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 3 c 4 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=16+9*(T:ℚ) := by exact_mod_cast he
      have hh := PlusTwo.small_a3_cmod4 (T:ℚ) hTQ
      refine ⟨0,4*T+4,?_⟩
      norm_num only [show (2:ℚ)^3=8 by norm_num]
      rw [heQ]
      convert hh using 1 <;> push_cast <;> ring
    · have hc0 : 5≤c := by omega
      obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 3 c 5 (by decide) hc0 (by simpa using hr)
      have hTQ : (0:ℚ)≤(T:ℚ) := by exact_mod_cast hT
      have heQ : (2:ℚ)^c=32+9*(T:ℚ) := by exact_mod_cast he
      have hh := PlusTwo.small_a3_cmod5 (T:ℚ) hTQ
      refine ⟨0,4*T+11,?_⟩
      norm_num only [show (2:ℚ)^3=8 by norm_num]
      rw [heQ]
      convert hh using 1 <;> push_cast <;> ring

private theorem high_periodic_selection (c : ℕ) (hc : 3≤c) :
    ∃ m : ℤ, HighResidual ((2:ℚ)^c) (m:ℚ) := by
  have hrem : c%4=0 ∨ c%4=1 ∨ c%4=2 ∨ c%4=3 := by omega
  rcases hrem with hr|hr|hr|hr
  · have hc0 : 4≤c := by omega
    obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 2 c 4 (by decide) hc0 (by simpa using hr)
    have heQ : (2:ℚ)^c=16+5*(T:ℚ) := by exact_mod_cast he
    have hh := HighB.a_two_b_c_plus_four_r1 (T:ℚ) (by exact_mod_cast hT)
    refine ⟨16*T+40,?_⟩
    rw [heQ]
    convert hh using 1 <;> push_cast <;> ring


  · have hc0 : 5≤c := by omega
    obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 2 c 5 (by decide) hc0 (by simpa using hr)
    have heQ : (2:ℚ)^c=32+5*(T:ℚ) := by exact_mod_cast he
    have hh := HighB.a_two_b_c_plus_four_r2 (T:ℚ) (by exact_mod_cast hT)
    refine ⟨16*T+91,?_⟩
    rw [heQ]
    convert hh using 1 <;> push_cast <;> ring
  · have hc0 : 6≤c := by omega
    obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 2 c 6 (by decide) hc0 (by simpa using hr)
    have heQ : (2:ℚ)^c=64+5*(T:ℚ) := by exact_mod_cast he
    have hh := HighB.a_two_b_c_plus_four_r4 (T:ℚ) (by exact_mod_cast hT)
    refine ⟨16*T+194,?_⟩
    rw [heQ]
    convert hh using 1 <;> push_cast <;> ring
  · have hc0 : 3≤c := by omega
    obtain ⟨T,hT,he⟩ := periodic_nonnegative_inverse 2 c 3 (by decide) hc0 (by simpa using hr)
    have heQ : (2:ℚ)^c=8+5*(T:ℚ) := by exact_mod_cast he
    have hh := HighB.a_two_b_c_plus_four_r3 (T:ℚ) (by exact_mod_cast hT)
    refine ⟨16*T+15,?_⟩
    rw [heQ]
    convert hh using 1 <;> push_cast <;> ring

/-! The large-a q=4 chart with its masks represented by actual integers. -/
private theorem plus_two_integer_residue (a c : ℕ) (ha : 4≤a) (hac : a<c) :
    ∃ v m : ℤ,
      (v:ℚ)=chooseV2 ((2:ℚ)^a) ((2:ℚ)^((c+2)%a))
          (decide (((c+2)/a)%2≠0)) ∧
      (m:ℚ)=chooseM2 ((2:ℚ)^a) ((2:ℚ)^c) ((2:ℚ)^((c+2)%a))
          (decide (((c+2)/a)%2≠0)) ∧
      StocksAndResidual ((2:ℚ)^a) ((2:ℚ)^c) 4 (v:ℚ) (m:ℚ) := by
  let ell := (c+2)/a
  let j := (c+2)%a
  let neg : Bool := decide (ell%2≠0)
  let xI : ℤ := 2^a
  let zI : ℤ := 2^c
  let uI : ℤ := 2^j
  let pA : ℤ := 2^(a-3)
  let pU : ℤ := 2^(j-2)
  have hpowA : (pA:ℚ)=(2:ℚ)^a/8 := by
    dsimp [pA]
    rw [show a=(a-3)+3 by omega, pow_add]
    norm_num
  have hsmall := dyadic_small_or_large j
  obtain ⟨he,hj,hu,hux,hrem⟩ := dyadic_residue a c 2 (by omega)
  obtain ⟨horth0,horth1⟩ := plus_two_orthant_bounds a c ha hac
  have hxQ : (16:ℚ)≤(2:ℚ)^a := by
    convert pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) ha using 1 <;> norm_num
  have hzQ : 2*(2:ℚ)^a≤(2:ℚ)^c := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) (show a+1≤c by omega)
    simpa only [pow_succ,mul_comm] using h
  have huQ : (1:ℚ)≤(2:ℚ)^j := by exact_mod_cast hu
  have huxQ : 2*(2:ℚ)^j≤(2:ℚ)^a := by exact_mod_cast hux
  have hdy : (2:ℚ)^j=1 ∨ (2:ℚ)^j=2 ∨ (2:ℚ)^j=4 ∨ 8≤(2:ℚ)^j := by
    rcases hsmall with h1|h2|h4|h8|hl
    · exact Or.inl (by exact_mod_cast h1)
    · exact Or.inr (Or.inl (by exact_mod_cast h2))
    · exact Or.inr (Or.inr (Or.inl (by exact_mod_cast h4)))
    · exact Or.inr (Or.inr (Or.inr (by exact_mod_cast (le_of_eq h8.symm))))
    · have h : (16:ℚ)≤(2:ℚ)^j := by exact_mod_cast hl
      exact Or.inr (Or.inr (Or.inr (by linarith)))
  have hq : ∃ T : ℤ,
      (2:ℤ)^(c+2)=(if ell%2=0 then uI else xI+1-uI)+(xI+1)*T := by
    simpa [ell,j,xI,uI] using dyadic_residue_integer_quotient a c 2 (by omega)
  obtain ⟨T,hT⟩ := hq
  let vI : ℤ := if ell%2=0 then
      (if uI=1 then pA-1 else if uI=2 then pA else pA-pU)
    else if uI≤4 then pA+(if uI=4 then 1 else 0) else 0
  let mI : ℤ := T-4*vI-(if ell%2=0 then 3 else if uI≤4 then 2 else 3)
  have hres : (2:ℤ)^(c+2)%(xI+1)=if ell%2=0 then uI else xI+1-uI := by
    simpa [xI,uI,ell,j] using hrem
  have hxIc : (xI:ℚ)=(2:ℚ)^a := by simp [xI]
  have huIc : (uI:ℚ)=(2:ℚ)^j := by simp [uI]
  have hule : uI≤4 ↔ (2:ℚ)^j≤4 := by rw [←huIc]; exact_mod_cast (Iff.rfl : uI≤4 ↔ uI≤4)
  have hueq (n : ℤ) : uI=n ↔ (2:ℚ)^j=(n:ℚ) := by rw [←huIc]; exact_mod_cast (Iff.rfl : uI=n ↔ uI=n)
  have hTQ : (T:ℚ)=((4:ℚ)*(2:ℚ)^c-
      (if neg then (2:ℚ)^a+1-(2:ℚ)^j else (2:ℚ)^j))/((2:ℚ)^a+1) := by
    have hTc : (2:ℚ)^(c+2)=(if ell%2=0 then (2:ℚ)^j else (2:ℚ)^a+1-(2:ℚ)^j)+((2:ℚ)^a+1)*(T:ℚ) := by
      dsimp [xI,uI] at hT
      exact_mod_cast hT
    apply (eq_div_iff (by positivity : (2:ℚ)^a+1≠0)).mpr
    by_cases hp : ell%2=0
    all_goals simp [neg,hp,pow_add] at hTc ⊢; nlinarith [hTc]
  have hVc : (vI:ℚ)=chooseV2 ((2:ℚ)^a) ((2:ℚ)^j) neg := by
    by_cases hp : ell%2=0
    · by_cases h1 : uI=1
      · simp [vI,chooseV2,neg,hp,h1,(hueq 1).mp h1,hpowA]
      · by_cases h2 : uI=2
        · simp [vI,chooseV2,neg,hp,h1,h2,show (2:ℚ)^j≠1 from fun h => h1 ((hueq 1).mpr h), (hueq 2).mp h2,hpowA]
        · have hj2 : 2≤j := by
            by_contra hn
            have hj01 : j=0 ∨ j=1 := by omega
            rcases hj01 with h|h <;> simp [uI,h] at h1 h2
          have hpowU : (pU:ℚ)=(2:ℚ)^j/4 := by
            dsimp [pU]
            push_cast
            conv_rhs => rw [show j=(j-2)+2 by omega,pow_add]
            norm_num
          simp [vI,chooseV2,neg,hp,h1,h2,
            show (2:ℚ)^j≠1 from fun h => h1 ((hueq 1).mpr h),
            show (2:ℚ)^j≠2 from fun h => h2 ((hueq 2).mpr h),hpowA,hpowU]
    · by_cases h4 : uI≤4
      · by_cases heq : uI=4
        all_goals simp [vI,chooseV2,neg,hp,h4,(hule.mp h4),heq,hpowA,
          show ((2:ℚ)^j=4 ↔ uI=4) from (hueq 4).symm]
      · simp [vI,chooseV2,neg,hp,h4,show ¬(2:ℚ)^j≤4 from fun h => h4 (hule.mpr h)]
  have hMc : (mI:ℚ)=chooseM2 ((2:ℚ)^a) ((2:ℚ)^c) ((2:ℚ)^j) neg := by
    dsimp only [mI]
    push_cast
    rw [hVc,hTQ]
    by_cases hp : ell%2=0
    · simp [chooseM2,neg,hp,residueRepresentative]
    · by_cases h4 : uI≤4
      · simp [chooseM2,neg,hp,residueRepresentative,h4,hule.mp h4]
      · simp [chooseM2,neg,hp,residueRepresentative,h4,show ¬(2:ℚ)^j≤4 from fun h => h4 (hule.mpr h)]
  obtain ⟨vR,mR,hvR,hmR,hsR⟩ := plus_two_residue_selection
    ((2:ℚ)^a) ((2:ℚ)^c) ((2:ℚ)^j) neg hxQ hzQ huQ huxQ hdy
    (by
      intro hn
      have hp : ell%2=0 := by simpa [neg] using hn
      have h := horth0 hp
      have hQ : (2:ℚ)^j*((2:ℚ)^a)^2≤4*(2:ℚ)^c := by exact_mod_cast h
      linarith)
    (by
      intro hn h4
      have hp : ell%2=1 := by
        have hh : ell%2≠0 := by simpa [neg] using hn
        omega
      exact_mod_cast horth1 hp (by exact_mod_cast h4))
  refine ⟨vI,mI,?_,?_,?_⟩
  · simpa only [neg,ell,j] using hVc
  · simpa only [neg,ell,j] using hMc
  · rw [hvR,hmR,←hVc,←hMc] at hsR
    exact hsR

private theorem plus_three_integer_residue (a c : ℕ) (ha : 5≤a) (hac : a<c) :
    ∃ m : ℤ,
      (m:ℚ)=chooseM3 ((2:ℚ)^a) ((2:ℚ)^c) ((2:ℚ)^((c+3)%a))
          (decide (((c+3)/a)%2≠0)) ∧
      Residual ((2:ℚ)^a) ((2:ℚ)^c) 8 0 (m:ℚ) := by
  let ell := (c+3)/a
  let j := (c+3)%a
  let neg : Bool := decide (ell%2≠0)
  let xI : ℤ := 2^a
  let zI : ℤ := 2^c
  let uI : ℤ := 2^j
  obtain ⟨he,hj,hu,hux,hrem⟩ := dyadic_residue a c 3 (by omega)
  have hsmall := dyadic_small_or_large j
  have hxQ : (32:ℚ)≤(2:ℚ)^a := by
    convert pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) ha using 1 <;> norm_num
  have hzQ : 2*(2:ℚ)^a≤(2:ℚ)^c := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) (show a+1≤c by omega)
    simpa only [pow_succ,mul_comm] using h
  have huQ : (1:ℚ)≤(2:ℚ)^j := by exact_mod_cast hu
  have huxQ : 2*(2:ℚ)^j≤(2:ℚ)^a := by exact_mod_cast hux
  have hdy : (2:ℚ)^j=1 ∨ (2:ℚ)^j=2 ∨ (2:ℚ)^j=4 ∨ (2:ℚ)^j=8 ∨ 16≤(2:ℚ)^j := by
    rcases hsmall with h1|h2|h4|h8|hl
    · exact Or.inl (by exact_mod_cast h1)
    · exact Or.inr (Or.inl (by exact_mod_cast h2))
    · exact Or.inr (Or.inr (Or.inl (by exact_mod_cast h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by exact_mod_cast h8))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by exact_mod_cast hl))))
  obtain ⟨T,hT⟩ : ∃ T : ℤ,
      (2:ℤ)^(c+3)=(if ell%2=0 then uI else xI+1-uI)+(xI+1)*T := by
    simpa [ell,j,xI,uI] using dyadic_residue_integer_quotient a c 3 (by omega)
  let mI : ℤ := T-(if ell%2=0 then 7 else if uI≤8 then 6 else 7)
  have hule : uI≤8 ↔ (2:ℚ)^j≤8 := by dsimp [uI]; exact_mod_cast (Iff.rfl : (2:ℤ)^j≤8 ↔ (2:ℤ)^j≤8)
  have hTQ : (T:ℚ)=((8:ℚ)*(2:ℚ)^c-
      (if neg then (2:ℚ)^a+1-(2:ℚ)^j else (2:ℚ)^j))/((2:ℚ)^a+1) := by
    have hTc : (2:ℚ)^(c+3)=(if ell%2=0 then (2:ℚ)^j else (2:ℚ)^a+1-(2:ℚ)^j)+((2:ℚ)^a+1)*(T:ℚ) := by
      dsimp [xI,uI] at hT
      exact_mod_cast hT
    apply (eq_div_iff (by positivity : (2:ℚ)^a+1≠0)).mpr
    by_cases hp : ell%2=0
    all_goals simp [neg,hp,pow_add] at hTc ⊢; nlinarith [hTc]
  have hMc : (mI:ℚ)=chooseM3 ((2:ℚ)^a) ((2:ℚ)^c) ((2:ℚ)^j) neg := by
    dsimp only [mI]
    push_cast
    rw [hTQ]
    by_cases hp : ell%2=0
    · simp [chooseM3,neg,hp,residueRepresentative]
    · by_cases h8 : uI≤8
      · simp [chooseM3,neg,hp,residueRepresentative,h8,hule.mp h8]
      · simp [chooseM3,neg,hp,residueRepresentative,h8,show ¬(2:ℚ)^j≤8 from fun h => h8 (hule.mpr h)]
  obtain ⟨vR,mR,hvR,hmR,hsR⟩ := plus_three_residue_selection
    ((2:ℚ)^a) ((2:ℚ)^c) ((2:ℚ)^j) neg hxQ hzQ huQ huxQ hdy
  refine ⟨mI,?_,?_⟩
  · simpa only [neg,ell,j] using hMc
  · rw [hvR,hmR,←hMc] at hsR
    exact hsR

private theorem low_integer_selection (a c s : ℕ)
    (hs : s=2 ∨ s=3) (ha : 2≤a) (hac : a<c)
    (hex2 : s=2 → ¬(a=2 ∧ c=3) ∧ ¬(a=2 ∧ c=5))
    (hex3 : s=3 → ¬(a=2 ∧ c=3)) :
    ∃ v m : ℤ,
      StocksAndResidual ((2:ℚ)^a) ((2:ℚ)^c) ((2:ℚ)^s) (v:ℚ) (m:ℚ) := by
  rcases hs with rfl|rfl
  · by_cases ha4 : 4≤a
    · obtain ⟨v,m,hv,hm,hh⟩ := plus_two_integer_residue a c ha4 hac
      exact ⟨v,m,hh⟩
    · have hamax : a≤3 := by omega
      exact plus_two_periodic_selection a c ha hamax hac (hex2 rfl)
  · by_cases ha5 : 5≤a
    · obtain ⟨m,hm,hh⟩ := plus_three_integer_residue a c ha5 hac
      have hz : (1:ℚ)≤(2:ℚ)^c/2 := by
        have hp := pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) (show 1≤c by omega)
        norm_num at hp
        linarith
      refine ⟨0,m,by norm_num,?_,?_⟩
      · norm_num
        linarith
      · convert hh using 1 <;> norm_num

    · have hamax : a≤4 := by omega
      obtain ⟨v,m,hh⟩ := plus_three_periodic_selection a c ha hamax hac (hex3 rfl)
      exact ⟨v,m,hh⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
