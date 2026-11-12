/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointSmallGaps
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportEndpointSmallGaps
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full real small-gap endpoint-one root brackets and integer exclusion. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportClassificationAlgebra
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! The original endpoint-one small-gap argument, for every real a≥2.
All sign identities are kernel polynomial identities. No finite exponent base. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointSmallGaps

open D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra

/-- The complete endpoint-one cubic in the third exponent. -/
def cubic (a b c : ℝ) : ℝ :=
  (a^2+b^2-1)*c^3 +
    (a^3-4*a^2*b^2+2*a^2*b-a^2+2*a*b^2+a*b-3*a+b^3-b^2-3*b+3)*c^2 +
    (a-1)*(b-1)*(2*a*b+3*a+3*b-3)*c +
    (a-1)*(b-1)*(a+b-1)*(a*b+a+b-1)

/-- Identity with the literal quotient's endpoint, without domain restrictions. -/
theorem endpoint_identity (a b c : ℝ) : h a b c 1 = cubic a b c := by
  simp [h, quintic, cubic]
  ring

private theorem strict_root {f : ℝ → ℝ} (l u : ℝ) (hlu : l < u)
    (hf : Continuous f) (hl : f l < 0) (hu : 0 < f u) :
    ∃ x, l < x ∧ x < u ∧ f x = 0 := by
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hlu.le hf.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (f l) (f u) from ⟨hl.le, hu.le⟩)
  refine ⟨x, lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_, hfx⟩
  · intro heq
    have : f l = 0 := by simpa [heq] using hfx
    linarith
  · intro heq
    have : f u = 0 := by simpa [heq] using hfx
    linarith

/-- A cubic with positive leading and constant coefficients cannot have
three distinct positive roots. This retains the source uniqueness argument. -/
theorem no_three_positive (A B D E r s t : ℝ)
    (hA : 0 < A) (hE : 0 < E) (hr0 : 0 < r) (hs0 : 0 < s) (ht0 : 0 < t)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hr : A*r^3+B*r^2+D*r+E = 0)
    (hs : A*s^3+B*s^2+D*s+E = 0)
    (ht : A*t^3+B*t^2+D*t+E = 0) : False := by
  have hdiff (x y : ℝ) (hxy : x ≠ y)
      (hx : A*x^3+B*x^2+D*x+E = 0) (hy : A*y^3+B*y^2+D*y+E = 0) :
      A*(x^2+x*y+y^2)+B*(x+y)+D = 0 := by
    apply (mul_eq_zero.mp (show (x-y)*(A*(x^2+x*y+y^2)+B*(x+y)+D) = 0 by
      calc
        _ = (A*x^3+B*x^2+D*x+E)-(A*y^3+B*y^2+D*y+E) := by ring
        _ = 0 := by rw [hx, hy]; ring)).resolve_left (sub_ne_zero.mpr hxy)
  have hrs' := hdiff r s hrs hr hs
  have hrt' := hdiff r t hrt hr ht
  have hB : A*(r+s+t)+B = 0 := by
    apply (mul_eq_zero.mp (show (s-t)*(A*(r+s+t)+B) = 0 by
      linear_combination hrs' - hrt')).resolve_left (sub_ne_zero.mpr hst)
  have hD : D-A*(r*s+r*t+s*t) = 0 := by
    linear_combination hrs' - (r+s)*hB
  have hE' : E+A*r*s*t = 0 := by
    linear_combination hr - r^2*hB - r*hD
  have : 0 < E+A*r*s*t := by positivity
  linarith

private theorem cubic_unique_bracket (A B D E b L : ℝ)
    (hA : 0 < A) (hE : 0 < E) (hb : 0 < b) (hbL : b ≤ L)
    (hnegB : A*b^3+B*b^2+D*b+E < 0)
    (hnegL : A*L^3+B*L^2+D*L+E < 0)
    (hposU : 0 < A*(L+1)^3+B*(L+1)^2+D*(L+1)+E) :
    ∃! x, b < x ∧ A*x^3+B*x^2+D*x+E = 0 ∧ L < x ∧ x < L+1 := by
  let f : ℝ → ℝ := fun x => A*x^3+B*x^2+D*x+E
  have hf : Continuous f := by fun_prop
  obtain ⟨r, hr0, hrb, hr⟩ := strict_root (f := fun x => -f x) 0 b hb
    (by fun_prop) (by dsimp [f]; linarith) (by dsimp [f]; linarith)
  have hr' : A*r^3+B*r^2+D*r+E = 0 := by dsimp [f] at hr; linarith
  obtain ⟨s, hLs, hsU, hs⟩ := strict_root L (L+1) (by linarith) hf hnegL hposU
  have hbs : b < s := hbL.trans_lt hLs
  refine ⟨s, ⟨hbs, hs, hLs, hsU⟩, ?_⟩
  intro t ht
  by_contra hts
  exact no_three_positive A B D E r s t hA hE hr0 (hb.trans hbs)
    (hb.trans ht.1) (by linarith) (by linarith) (Ne.symm hts) hr' hs ht.2.1

/-- The source lower endpoints, for precisely the two admitted middle gaps. -/
def lower (a : ℝ) (d : Fin 2) : ℝ := if d = 0 then 2*a^2-a-2 else 2*a^2+a-6

private theorem signs_one (a : ℝ) (ha : 2 ≤ a) :
    cubic a (a+1) (a+1) < 0 ∧
    cubic a (a+1) (2*a^2-a-2) < 0 ∧
    0 < cubic a (a+1) (2*a^2-a-1) := by
  have hm : 0 ≤ a-2 := by linarith
  have h1 : -cubic a (a+1) (a+1) =
      4*(a-2)^6+52*(a-2)^5+264*(a-2)^4+664*(a-2)^3+
        848*(a-2)^2+480*(a-2)+64 := by dsimp [cubic]; ring
  have h2 : -cubic a (a+1) (2*a^2-a-2) =
      4*(a-2)^6+52*(a-2)^5+264*(a-2)^4+648*(a-2)^3+
        768*(a-2)^2+376*(a-2)+48 := by dsimp [cubic]; ring
  have h3 : cubic a (a+1) (2*a^2-a-1) =
      4*(a-2)^6+44*(a-2)^5+196*(a-2)^4+456*(a-2)^3+
        592*(a-2)^2+412*(a-2)+120 := by dsimp [cubic]; ring
  constructor
  · have : 0 < -cubic a (a+1) (a+1) := by rw [h1]; positivity
    linarith
  constructor
  · have : 0 < -cubic a (a+1) (2*a^2-a-2) := by rw [h2]; positivity
    linarith
  · rw [h3]; positivity

private theorem signs_two (a : ℝ) (ha : 2 ≤ a) :
    cubic a (a+2) (a+2) < 0 ∧
    cubic a (a+2) (2*a^2+a-6) < 0 ∧
    0 < cubic a (a+2) (2*a^2+a-5) := by
  have hm : 0 ≤ a-2 := by linarith
  have h1 : -cubic a (a+2) (a+2) =
      4*(a-2)^6+68*(a-2)^5+456*(a-2)^4+1516*(a-2)^3+
        2513*(a-2)^2+1689*(a-2)+57 := by dsimp [cubic]; ring
  have h2 : -cubic a (a+2) (2*a^2+a-6) =
      16*(a-2)^5+232*(a-2)^4+1140*(a-2)^3+2119*(a-2)^2+
        1009*(a-2)+57 := by dsimp [cubic]; ring
  have h3 : cubic a (a+2) (2*a^2+a-5) =
      8*(a-2)^6+104*(a-2)^5+476*(a-2)^4+892*(a-2)^3+
        640*(a-2)^2+360*(a-2)+160 := by dsimp [cubic]; ring
  constructor
  · have : 0 < -cubic a (a+2) (a+2) := by rw [h1]; positivity
    linarith
  constructor
  · have : 0 < -cubic a (a+2) (2*a^2+a-6) := by rw [h2]; positivity
    linarith
  · rw [h3]; positivity

/-- For either original gap, there is exactly one endpoint-one root above b,
and it lies between the original consecutive-integer polynomial endpoints. -/
theorem result (a : ℝ) (ha : 2 ≤ a) (d : Fin 2) :
    ∃ r : ℝ, a+(d.val+1 : ℕ) < r ∧ lower a d < r ∧ r < lower a d+1 ∧
      h a (a+(d.val+1 : ℕ)) r 1 = 0 ∧
      ∀ c : ℝ, a+(d.val+1 : ℕ) < c → h a (a+(d.val+1 : ℕ)) c 1 = 0 → c = r := by
  have hb : 0 < a+(d.val+1 : ℕ) := by positivity
  have hA : 0 < a^2+(a+(d.val+1 : ℕ))^2-1 := by nlinarith [sq_nonneg (a+(d.val+1 : ℕ))]
  have hE : 0 < (a-1)*(a+(d.val+1 : ℕ)-1)*(a+(a+(d.val+1 : ℕ))-1)*
      (a*(a+(d.val+1 : ℕ))+a+(a+(d.val+1 : ℕ))-1) := by
    have ha1 : 0 < a-1 := by linarith
    have hb1 : 0 < a+(d.val+1 : ℕ)-1 := by
      have hd : (0 : ℝ) ≤ (d.val+1 : ℕ) := Nat.cast_nonneg _
      linarith
    have hab1 : 0 < a+(a+(d.val+1 : ℕ))-1 := by linarith
    have hab2 : 0 < a*(a+(d.val+1 : ℕ))+a+(a+(d.val+1 : ℕ))-1 := by
      have : 0 < a*(a+(d.val+1 : ℕ)) := mul_pos (by linarith) hb
      linarith
    positivity
  have hbL : a+(d.val+1 : ℕ) ≤ lower a d := by
    fin_cases d <;> norm_num [lower] <;> nlinarith [sq_nonneg (a-2)]
  have hsign : cubic a (a+(d.val+1 : ℕ)) (a+(d.val+1 : ℕ)) < 0 ∧
      cubic a (a+(d.val+1 : ℕ)) (lower a d) < 0 ∧
      0 < cubic a (a+(d.val+1 : ℕ)) (lower a d+1) := by
    fin_cases d
    · convert signs_one a ha using 1 <;> norm_num [lower, sub_eq_add_neg, add_assoc]
    · convert signs_two a ha using 1 <;> norm_num [lower, sub_eq_add_neg, add_assoc]
  obtain ⟨r, hr, huniq⟩ := cubic_unique_bracket
    (a^2+(a+(d.val+1 : ℕ))^2-1)
    (a^3-4*a^2*(a+(d.val+1 : ℕ))^2+2*a^2*(a+(d.val+1 : ℕ))-a^2+
      2*a*(a+(d.val+1 : ℕ))^2+a*(a+(d.val+1 : ℕ))-3*a+
      (a+(d.val+1 : ℕ))^3-(a+(d.val+1 : ℕ))^2-3*(a+(d.val+1 : ℕ))+3)
    ((a-1)*(a+(d.val+1 : ℕ)-1)*(2*a*(a+(d.val+1 : ℕ))+3*a+3*(a+(d.val+1 : ℕ))-3))
    ((a-1)*(a+(d.val+1 : ℕ)-1)*(a+(a+(d.val+1 : ℕ))-1)*
      (a*(a+(d.val+1 : ℕ))+a+(a+(d.val+1 : ℕ))-1))
    (a+(d.val+1 : ℕ)) (lower a d) hA hE hb hbL hsign.1 hsign.2.1 hsign.2.2
  refine ⟨r, hr.1, hr.2.2.1, hr.2.2.2, ?_, ?_⟩
  · rw [endpoint_identity]; exact hr.2.1
  · intro c hc hroot
    have hcroot : cubic a (a+(d.val+1 : ℕ)) c = 0 := by rwa [endpoint_identity] at hroot
    by_contra hcr
    -- A root above b is unique, independently of assuming the bracket for c.
    obtain ⟨s, hs0, hsb, hs⟩ := strict_root
      (f := fun x => -cubic a (a+(d.val+1 : ℕ)) x) 0 (a+(d.val+1 : ℕ)) hb
      (by unfold cubic; fun_prop) (by simpa [cubic] using neg_neg_of_pos hE)
      (by linarith [hsign.1])
    have hsroot : cubic a (a+(d.val+1 : ℕ)) s = 0 := by linarith
    exact no_three_positive _ _ _ _ s r c hA hE hs0 (hb.trans hr.1) (hb.trans hc)
      (by linarith) (by linarith) (Ne.symm hcr) hsroot hr.2.1 hcroot

/-- The complete original integer exclusion for both small middle gaps. -/
theorem integer_nonzero (a c : ℕ) (ha : 2 ≤ a) (d : Fin 2)
    (hc : a+(d.val+1) < c) : h (a : ℝ) ((a+(d.val+1) : ℕ) : ℝ) (c : ℝ) 1 ≠ 0 := by
  intro hz
  obtain ⟨r, hrb, hrl, hru, hr, huniq⟩ := result a (by exact_mod_cast ha) d
  have heq : (c : ℝ) = r := huniq c (by exact_mod_cast hc) (by simpa using hz)
  have hi : ∃ q : ℤ, lower (a : ℝ) d = q := by
    fin_cases d
    · exact ⟨2*(a : ℤ)^2-a-2, by simp [lower]⟩
    · exact ⟨2*(a : ℤ)^2+a-6, by simp [lower]⟩
  obtain ⟨q, hq⟩ := hi
  rw [← heq, hq] at hrl hru
  have hl : q < (c : ℤ) := by exact_mod_cast hrl
  have hu : (c : ℤ) < q+1 := by exact_mod_cast hru
  omega

#print axioms endpoint_identity
#print axioms result
#print axioms integer_nonzero

end D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointSmallGaps
