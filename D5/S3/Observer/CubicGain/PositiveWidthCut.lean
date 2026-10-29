/- GID: D5/S3/Observer/CubicGain/PositiveWidthCut
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/PositiveWidthCut
   mirror-E: none(waiver:full-domain-strict-positive-parent-width-exclusion)
   anchors: [mathlib/module/Mathlib.Topology.Order.IntermediateValue]
   utility: none
   digest: The positive fifth reading of an original complete parent forces width below the unique positive cubic root. -/

import D5.S3.Observer.CubicGain.OriginalWorld
import Mathlib.Topology.Order.IntermediateValue

/-! The strict width cut uses the unmodified five-row parent equation.
The internal `original_coordinates` correspondence from `OriginalWorld` is reused directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.CubicGain

private theorem positive_cubic_root_gt_two (x : ℝ) (hx : 0 < x)
    (hroot : x ^ 3-8*x-4=0) : 2 < x := by
  by_contra h
  have hx2 : x ≤ 2 := le_of_not_gt h
  have hsq : x^2 ≤ 4 := by nlinarith
  have hcube : x^3 ≤ 4*x := by nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hsq)]
  linarith

private theorem cubic_strict (x y : ℝ) (hx : 2 ≤ x) (hxy : x < y) :
    x^3-8*x-4 < y^3-8*y-4 := by
  have hy : 2 < y := lt_of_le_of_lt hx hxy
  have hxx : 4 ≤ x^2 := by nlinarith
  have hyy : 4 < y^2 := by nlinarith
  have hxy2 : 4 < x*y := by nlinarith
  have hp : 0 < (y-x)*(y^2+x*y+x^2-8) := mul_pos (by linarith) (by linarith)
  nlinarith only [hp]

private theorem positive_width_root : ∃ β : ℝ,
    3 < β ∧ β < 31/10 ∧ β ^ 3-8*β-4=0 ∧
    ∀ x : ℝ, 0 < x → x ^ 3-8*x-4=0 → x=β := by
  have hc : ContinuousOn (fun x : ℝ => x^3-8*x-4) (Set.Icc 3 (31/10)) := by fun_prop
  obtain ⟨β,hβ,hroot⟩ := intermediate_value_Icc (by norm_num : (3:ℝ) ≤ 31/10) hc
    (by norm_num : (0:ℝ) ∈ Set.Icc ((3:ℝ)^3-8*3-4) ((31/10:ℝ)^3-8*(31/10)-4))
  have hlow : 3 < β := by
    have hne : β ≠ 3 := by intro h; subst β; norm_num at hroot
    exact lt_of_le_of_ne hβ.1 (Ne.symm hne)
  have hhigh : β < 31/10 := by
    have hne : β ≠ 31/10 := by intro h; subst β; norm_num at hroot
    exact lt_of_le_of_ne hβ.2 hne
  refine ⟨β,hlow,hhigh,hroot,?_⟩
  intro x hx hxr
  have hx2 := positive_cubic_root_gt_two x hx hxr
  rcases lt_trichotomy x β with h | h | h
  · have := cubic_strict x β hx2.le h
    linarith
  · exact h
  · have := cubic_strict β x (by linarith) h
    linarith

private def widthNumerator (r b : ℝ) : ℝ :=
  (72)*(b-3)^7 +
  (1634 + 624*(1-r^1))*(b-3)^6 +
  (15790 + 456*r^2 + 11711*(1-r^1))*(b-3)^5 +
  (85069 + 1216*r^3 + 5217*r^2 + 90786*(1-r^1))*(b-3)^4 +
  (277599 + 744*(1-r^4) + 16429*r^3 + 20156*r^2 + 372027*(1-r^1))*(b-3)^3 +
  (550481 + 512*(1-r^5) + 5904*(1-r^4) + 82287*r^3 + 22306*r^2 + 849479*(1-r^1))*(b-3)^2 +
  (583167 + 256*r^6 + 3776*(1-r^5) + 14856*(1-r^4) +
    181595*r^3 + 31780*(1-r^2) + 1023870*(1-r^1))*(b-3)^1 +
  (234693 + 736*r^6 + 6624*(1-r^5) + 11616*(1-r^4) + 149321*r^3 + 63651*(1-r^2) + 508239*(1-r^1))

private theorem width_numerator_pos (r b : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hb : 3 ≤ b) : 0 < widthNumerator r b := by
  have ht : 0 ≤ b-3 := by linarith
  have hp (n : ℕ) : 0 ≤ 1-r^n := sub_nonneg.mpr (pow_le_one₀ hr hr1)
  have h1 := hp 1
  have h2 := hp 2
  have h4 := hp 4
  have h5 := hp 5
  unfold widthNumerator
  positivity

set_option maxHeartbeats 2000000 in
-- Denominator clearing checks the full degree-seven universal polynomial identity.
private theorem response_parent_identity (r b e : ℝ) (hb : 0 < b)
    (hj : sourceJ r b ≠ 0) (hn : sourceN r b ≠ 0) :
    fifthResponse (r,b,e) * parentLambda r b -
      fifthDrift r b * parentEq (r,b,e) =
    -6 * widthNumerator r b /
      (5*b*(1+b)*(1+2*b)*(b^2+r*(1-r))*(b^2+r*(1-r)+b*r)) := by
  have ht : 1+b ≠ 0 := ne_of_gt (by positivity : 0 < 1+b)
  have hu : 1+2*b ≠ 0 := ne_of_gt (by positivity : 0 < 1+2*b)
  have hX : b^2+r*(1-r) ≠ 0 := by
    have hh : b * sourceJ r b = b^2+r*(1-r) := by
      unfold sourceJ
      field_simp
    rw [← hh]
    exact mul_ne_zero (ne_of_gt hb) hj
  have hN : b^2+r*(1-r)+b*r ≠ 0 := by
    have hh : b * sourceN r b = b^2+r*(1-r)+b*r := by
      unfold sourceN sourceJ
      field_simp
    rw [← hh]
    exact mul_ne_zero (ne_of_gt hb) hn
  unfold fifthResponse parentEq parentLambda parentB fifthDrift widthNumerator
  dsimp
  field_simp [ne_of_gt hb,ht,hu,hj,hn,hX,hN]
  unfold sourceN sourceJ
  field_simp
  ring

private theorem lambda_pos_beyond_root (r b β : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hβ : 3 < β) (hroot : β ^ 3-8*β-4=0) (hb : β ≤ b) :
    0 < parentLambda r b := by
  have hb0 : 0 < b := by linarith
  have hpoly : 0 ≤ b^3-8*b-4 := by
    rcases eq_or_lt_of_le hb with h | h
    · rw [← h,hroot]
    · have hh := cubic_strict β b (by linarith) h
      linarith
  have hbase : 0 ≤ 1+6/(1+b)+1/(1+2*b)-8/b := by
    have hid : 1+6/(1+b)+1/(1+2*b)-8/b =
        2*(b^3-8*b-4)/(b*(1+b)*(1+2*b)) := by field_simp; ring
    rw [hid]
    exact div_nonneg (by linarith) (by positivity)
  have hjb : b < sourceJ r b := by
    have hh : 0 < r*(1-r)/b := div_pos (mul_pos hr (by linarith)) hb0
    unfold sourceJ
    linarith
  have hnb : b < sourceN r b := by unfold sourceN; linarith
  have hji : 4/sourceJ r b < 4/b := div_lt_div_of_pos_left (by norm_num) hb0 hjb
  have hni : 4/sourceN r b < 4/b := div_lt_div_of_pos_left (by norm_num) hb0 hnb
  unfold parentLambda
  linarith [show (8:ℝ)/b = 4/b+4/b by ring]

/-- The unique positive cubic root bounds every strict parent and every original
complete polynomial world with a strictly positive literal fifth reading. -/
theorem positive_parent_width_cut : ∃ β : ℝ,
    (0 < β ∧ β ^ 3-8*β-4=0 ∧
      ∀ x : ℝ, 0 < x → x ^ 3-8*x-4=0 → x=β) ∧
    (∀ C : Coordinates, StrictParent C → 0 < fifthResponse C → C.2.1 < β) ∧
    (∀ W : OriginalWorld, OriginalParent W → 0 < originalRead W 5 → W.2.1 < β) := by
  obtain ⟨β,hβ,hβu,hroot,hunique⟩ := positive_width_root
  have hnative : ∀ C : Coordinates, StrictParent C → 0 < fifthResponse C → C.2.1 < β := by
    rintro ⟨r,b,e⟩ ⟨hr,hr1,hb,hparent⟩ hp
    by_contra h
    have hlarge : β ≤ b := le_of_not_gt h
    have hl := lambda_pos_beyond_root r b β hr hr1 hβ hroot hlarge
    obtain ⟨hj,hn,ht,hu⟩ := source_positivity r b hr.le hr1.le hb
    have hrr : 0 ≤ r*(1-r) := mul_nonneg hr.le (by linarith)
    have hX : 0 < b^2+r*(1-r) := by positivity
    have hN : 0 < b^2+r*(1-r)+b*r := by positivity
    have hid := response_parent_identity r b e hb (ne_of_gt hj) (ne_of_gt hn)
    have hnum := width_numerator_pos r b hr.le hr1.le (by linarith)
    have hneg : -6*widthNumerator r b /
        (5*b*(1+b)*(1+2*b)*(b^2+r*(1-r))*(b^2+r*(1-r)+b*r)) < 0 :=
      div_neg_of_neg_of_pos (by nlinarith) (by positivity)
    rw [hparent,mul_zero,sub_zero] at hid
    have hpos := mul_pos hp hl
    linarith
  refine ⟨β,⟨by linarith,hroot,hunique⟩,hnative,?_⟩
  intro W hW hp
  obtain ⟨hC,hworld,hresponse⟩ := original_coordinates W hW
  have hresp : 0 < fifthResponse (worldCoordinates (decodeWorld W)) := by
    change 0 < (response (worldCoordinates (decodeWorld W))).1
    rw [hresponse]
    exact hp
  exact hnative _ hC hresp

#print axioms positive_parent_width_cut
end D5.S3.Observer.CubicGain
