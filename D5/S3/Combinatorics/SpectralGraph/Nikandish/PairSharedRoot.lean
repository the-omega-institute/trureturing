/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/PairSharedRoot
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/PairSharedRoot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full shared-prime valuation ranges for genuine repeated-pair roots. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairRootArithmetic
import D5.S3.Combinatorics.SpectralGraph.Nikandish.IntegerPrimeOrder

/-! Source: four-prime-shared-prime, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02. Every positive integer
parameter and every integer root s>=2 remain in scope. These are necessary
root conditions, including shared tail primes, not sufficient conditions.
The remainder is the entire integer polynomial, with no finite controls.
-/
set_option autoImplicit false
namespace D5.S3.Combinatorics.SpectralGraph.PairSharedRoot
open PairedIdealIntersectionObstructions IntegerPrimeOrder

def leftFactor (h b c s : ℤ) : ℤ := (s-1)*b-s*c-h
def rightFactor (h b c s : ℤ) : ℤ := s*b-(s-1)*c+h
def cubic (h b c s : ℤ) : ℤ := -h*(s-1)*leftFactor h b c s*rightFactor h b c s
def anchor (b c s : ℤ) : ℤ := -(s-1)^2*(2*s-1)*b^2*c^2

def remainder (h b c s : ℤ) : ℤ :=
  h^4*(4*b*c+2*b+2*c+2) +
  h^3*b*(-b*c*s+4*b*c-b*s+2*b-c^2*s+4*c^2+9*c*s+2*s+1) +
  h^3*c*(-c*s+2*c+2*s+1) +
  h^2*b^2*(-2*c^2*s+4*c^2-2*c*s^2+8*c*s-2*c-2*s^2+4*s-1) +
  h^2*b*c*(-2*c*s^2+8*c*s-2*c+7*s^2-4*s+1) +
  h^2*c^2*(-2*s^2+4*s-1) +
  h*b^2*c*(-s^3+4*s^2-2*s) + h*b*c^2*(-s^3+4*s^2-2*s) +
  h*b^2*c^2*(-4*s^2+9*s-4)

theorem root_expansion (a b c s : ℤ) :
    (tensorK a b c-s • 1).det = cubic (a+1-s) b c s + anchor b c s +
      remainder (a+1-s) b c s := by
  rw [PairRootArithmetic.root_division]
  unfold PairRootArithmetic.rootQuotient cubic leftFactor rightFactor anchor remainder
  ring

theorem remainder_dvd (p e r t N : ℕ) (h b c s : ℤ)
    (hh : (p : ℤ)^e ∣ h) (hb : (p : ℤ)^r ∣ b) (hc : (p : ℤ)^t ∣ c)
    (h4 : N ≤ 4*e) (h31 : N ≤ 3*e+r) (h32 : N ≤ 3*e+t)
    (h21 : N ≤ 2*e+2*r) (h22 : N ≤ 2*e+r+t) (h23 : N ≤ 2*e+2*t)
    (h11 : N ≤ e+2*r+t) (h12 : N ≤ e+r+2*t) (h13 : N ≤ e+2*r+2*t) :
    (p : ℤ)^N ∣ remainder h b c s := by
  unfold remainder
  apply dvd_add
  · apply dvd_add
    · apply dvd_add
      · apply dvd_add
        · apply dvd_add
          · apply dvd_add
            · apply dvd_add
              · apply dvd_add
                · convert monomial_dvd p e r t 4 0 0 N h b c
                    (4*b*c+2*b+2*c+2) hh hb hc (by omega) using 1 <;> ring
                · convert monomial_dvd p e r t 3 1 0 N h b c
                    (-b*c*s+4*b*c-b*s+2*b-c^2*s+4*c^2+9*c*s+2*s+1) hh hb hc
                    (by omega) using 1 <;> ring
              · convert monomial_dvd p e r t 3 0 1 N h b c
                  (-c*s+2*c+2*s+1) hh hb hc (by omega) using 1 <;> ring
            · convert monomial_dvd p e r t 2 2 0 N h b c
                (-2*c^2*s+4*c^2-2*c*s^2+8*c*s-2*c-2*s^2+4*s-1) hh hb hc (by omega) using 1 <;> ring
          · convert monomial_dvd p e r t 2 1 1 N h b c
              (-2*c*s^2+8*c*s-2*c+7*s^2-4*s+1) hh hb hc (by omega) using 1 <;> ring
        · convert monomial_dvd p e r t 2 0 2 N h b c
            (-2*s^2+4*s-1) hh hb hc (by omega) using 1 <;> ring
      · convert monomial_dvd p e r t 1 2 1 N h b c
          (-s^3+4*s^2-2*s) hh hb hc (by omega) using 1 <;> ring
    · convert monomial_dvd p e r t 1 1 2 N h b c
        (-s^3+4*s^2-2*s) hh hb hc (by omega) using 1 <;> ring
  · convert monomial_dvd p e r t 1 2 2 N h b c
      (-4*s^2+9*s-4) hh hb hc (by omega) using 1 <;> ring

private theorem factors_below (p e r t : ℕ) (h b c s : ℤ)
    (hh : ExactOrder p e h) (hb : ExactOrder p r b) (hc : ExactOrder p t c)
    (her : e<r) (hrt : r≤t) :
    ExactOrder p e (leftFactor h b c s) ∧ ExactOrder p e (rightFactor h b c s) := by
  have hb' := lower_power p (e+1) r b (by omega) hb.1
  have hc' := lower_power p (e+1) t c (by omega) hc.1
  have hleft : (p : ℤ)^(e+1) ∣ (s-1)*b-s*c := by
    exact dvd_sub (dvd_mul_of_dvd_right hb' _) (dvd_mul_of_dvd_right hc' _)
  have hright : (p : ℤ)^(e+1) ∣ s*b-(s-1)*c := by
    exact dvd_sub (dvd_mul_of_dvd_right hb' _) (dvd_mul_of_dvd_right hc' _)
  constructor
  · convert add_high p e (-h) ((s-1)*b-s*c) (neg_order p e h hh) hleft using 1 <;>
      simp only [leftFactor] <;> ring
  · convert add_high p e h (s*b-(s-1)*c) hh hright using 1 <;>
      simp only [rightFactor] <;> ring

private theorem factors_above (p e r t : ℕ) [Fact p.Prime] (h b c s : ℤ)
    (hh : ExactOrder p e h) (hb : ExactOrder p r b) (hc : ExactOrder p t c)
    (her : r<e) (hrt : r<t) (hs : ¬(p : ℤ)∣s) (hs1 : ¬(p : ℤ)∣s-1) :
    ExactOrder p r (leftFactor h b c s) ∧ ExactOrder p r (rightFactor h b c s) := by
  have hh' := lower_power p (r+1) e h (by omega) hh.1
  have hc' := lower_power p (r+1) t c (by omega) hc.1
  have hl := mul_order p 0 r (s-1) b (unit_order p (s-1) hs1) hb
  have hr := mul_order p 0 r s b (unit_order p s hs) hb
  simp only [Nat.zero_add] at hl hr
  constructor
  · convert add_high p r ((s-1)*b) (-s*c-h) hl
      (dvd_sub (dvd_mul_of_dvd_right hc' _) hh') using 1 <;>
      simp only [leftFactor] <;> ring
  · convert add_high p r (s*b) (-(s-1)*c+h) hr
      (dvd_add (dvd_mul_of_dvd_right hc' _) hh') using 1 <;>
      simp only [rightFactor] <;> ring

private theorem cubic_order (p e j : ℕ) [Fact p.Prime] (h b c s : ℤ)
    (hh : ExactOrder p e h) (hs1 : ¬(p : ℤ)∣s-1)
    (hl : ExactOrder p j (leftFactor h b c s))
    (hr : ExactOrder p j (rightFactor h b c s)) :
    ExactOrder p (e+2*j) (cubic h b c s) := by
  have h0 := mul_order p e 0 (-h) (s-1) (neg_order p e h hh) (unit_order p (s-1) hs1)
  have h1 := mul_order p (e+0) j (-h*(s-1)) (leftFactor h b c s) h0 hl
  have h2 := mul_order p ((e+0)+j) j (-h*(s-1)*leftFactor h b c s)
    (rightFactor h b c s) h1 hr
  simpa [cubic, two_mul, Nat.add_assoc] using h2

private theorem anchor_order (p r t : ℕ) [Fact p.Prime] (b c s : ℤ)
    (hb : ExactOrder p r b) (hc : ExactOrder p t c)
    (hs1 : ¬(p : ℤ)∣s-1) (hs2 : ¬(p : ℤ)∣2*s-1) :
    ExactOrder p (2*r+2*t) (anchor b c s) := by
  have h1 := pow_order p 0 2 (s-1) (unit_order p (s-1) hs1)
  have h2 := mul_order p (0*2) 0 (-(s-1)^2) (2*s-1)
    (neg_order p (0*2) ((s-1)^2) h1) (unit_order p (2*s-1) hs2)
  have h3 := mul_order p (0*2+0) (r*2) (-(s-1)^2*(2*s-1)) (b^2)
    h2 (pow_order p r 2 b hb)
  have h4 := mul_order p (0*2+0+r*2) (t*2) (-(s-1)^2*(2*s-1)*b^2) (c^2)
    h3 (pow_order p t 2 c hc)
  simpa [anchor, Nat.mul_comm] using h4

/-- Complete ordered valuation alternatives, with no coprime-tail premise. -/
theorem ordered_ranges (p e r t : ℕ) [Fact p.Prime] (h b c s : ℤ)
    (hh : ExactOrder p e h) (hb : ExactOrder p r b) (hc : ExactOrder p t c)
    (he : 0<e) (hrt : r≤t)
    (hs : ¬(p : ℤ)∣s) (hs1 : ¬(p : ℤ)∣s-1) (hs2 : ¬(p : ℤ)∣2*s-1)
    (hz : cubic h b c s + anchor b c s + remainder h b c s = 0) :
    (r<t → e=r ∨ e=2*t) ∧ (r=t → 1≤r ∧ r≤e ∧ e≤2*r) := by
  have ha := anchor_order p r t b c s hb hc hs1 hs2
  have her : r≤e := by
    by_contra hn
    have hl : e<r := by omega
    obtain ⟨hf1,hf2⟩ := factors_below p e r t h b c s hh hb hc hl hrt
    have hcu := cubic_order p e e h b c s hh hs1 hf1 hf2
    have hcu' : ExactOrder p (3*e) (cubic h b c s) := by
      convert hcu using 1 <;> omega
    have har := lower_power p (3*e+1) (2*r+2*t) (anchor b c s) (by omega) ha.1
    have hrem : (p : ℤ)^(3*e+1) ∣ remainder h b c s := by
      apply remainder_dvd p e r t (3*e+1) h b c s hh.1 hb.1 hc.1 <;> omega
    have hd := dvd_add har hrem
    have ht : anchor b c s + remainder h b c s = -cubic h b c s := by linarith
    rw [ht,dvd_neg] at hd
    exact hcu'.2 hd
  constructor
  · intro hlt
    by_cases her' : e=r
    · exact Or.inl her'
    have hr' : r<e := by omega
    obtain ⟨hf1,hf2⟩ := factors_above p e r t h b c s hh hb hc hr' hlt hs hs1
    have hcu := cubic_order p e r h b c s hh hs1 hf1 hf2
    have hrem : (p : ℤ)^(e+2*r+1) ∣ remainder h b c s := by
      apply remainder_dvd p e r t (e+2*r+1) h b c s hh.1 hb.1 hc.1 <;> omega
    have heq := equal_of_high_remainder p (e+2*r) (2*r+2*t)
      (cubic h b c s) (anchor b c s) (remainder h b c s) hcu ha hrem hz
    exact Or.inr (by omega)
  · intro hrt'
    have hr : 1≤r := by
      by_contra hn
      have hr0 : r=0 := by omega
      have ht0 : t=0 := by omega
      have hcub : (p : ℤ)^1 ∣ cubic h b c s := by
        unfold cubic
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_left (dvd_neg.mpr (lower_power p 1 e h he hh.1)) _) _) _
      have hrem : (p : ℤ)^1 ∣ remainder h b c s := by
        apply remainder_dvd p e r t 1 h b c s hh.1 hb.1 hc.1 <;> omega
      have hd := dvd_add hcub hrem
      have ht : cubic h b c s + remainder h b c s = -anchor b c s := by linarith
      rw [ht,dvd_neg] at hd
      have ha0 : ExactOrder p 0 (anchor b c s) := by simpa [hr0,ht0] using ha
      exact ha0.2 hd
    refine ⟨hr,her,?_⟩
    by_contra hn
    have hlarge : 2*r<e := by omega
    have hh' := lower_power p r e h (by omega) hh.1
    have hc' : (p : ℤ)^r ∣ c := by simpa [hrt'] using hc.1
    have hf1 : (p : ℤ)^r ∣ leftFactor h b c s := by
      unfold leftFactor
      exact dvd_sub (dvd_sub (dvd_mul_of_dvd_right hb.1 _)
        (dvd_mul_of_dvd_right hc' _)) hh'
    have hf2 : (p : ℤ)^r ∣ rightFactor h b c s := by
      unfold rightFactor
      exact dvd_add (dvd_sub (dvd_mul_of_dvd_right hb.1 _)
        (dvd_mul_of_dvd_right hc' _)) hh'
    have hcub : (p : ℤ)^(e+2*r) ∣ cubic h b c s := by
      have hd := mul_dvd_mul (mul_dvd_mul
        (dvd_mul_of_dvd_left (dvd_neg.mpr hh.1) (s-1)) hf1) hf2
      simpa [cubic,pow_add,two_mul,Nat.add_assoc,mul_assoc] using hd
    have hcub' := lower_power p (4*r+1) (e+2*r) (cubic h b c s) (by omega) hcub
    have hrem : (p : ℤ)^(4*r+1) ∣ remainder h b c s := by
      apply remainder_dvd p e r t (4*r+1) h b c s hh.1 hb.1 hc.1 <;> omega
    have hd := dvd_add hcub' hrem
    have ht : cubic h b c s + remainder h b c s = -anchor b c s := by linarith
    rw [ht,dvd_neg] at hd
    have ha' : ExactOrder p (4*r) (anchor b c s) := by convert ha using 1 <;> omega
    exact ha'.2 hd

/-- The original min/max formulation, including negative root offsets. -/
theorem root_ranges (a b c s : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (p : ℕ) [Fact p.Prime] (hh : (p : ℤ)∣a+1-s)
    (hgood : ¬(p : ℤ)∣s*(s-1)*(2*s-1))
    (hr : (tensorK a b c-s • 1).det=0) :
    let e := padicValInt p (a+1-s)
    let r := min (padicValInt p b) (padicValInt p c)
    let t := max (padicValInt p b) (padicValInt p c)
    a+1-s≠0 ∧ (r<t → e=r ∨ e=2*t) ∧ (r=t → 1≤r ∧ r≤e ∧ e≤2*r) := by
  dsimp only
  have hn := PairRootArithmetic.root_offset_ne_zero a b c s ha hb hc hr
  have he : 0<padicValInt p (a+1-s) := by
    have hd : (p : ℤ)^1∣a+1-s := by simpa using hh
    have ht := (padicValInt_dvd_iff 1 (a+1-s)).mp hd
    omega
  have hs : ¬(p : ℤ)∣s := by
    intro hd
    exact hgood (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _)
  have hs1 : ¬(p : ℤ)∣s-1 := by
    intro hd
    exact hgood (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _)
  have hs2 : ¬(p : ℤ)∣2*s-1 := by
    intro hd
    exact hgood (dvd_mul_of_dvd_right hd _)
  have hz : cubic (a+1-s) b c s + anchor b c s + remainder (a+1-s) b c s = 0 := by
    rwa [root_expansion] at hr
  rcases le_total (padicValInt p b) (padicValInt p c) with hbc | hcb
  · have h := ordered_ranges p (padicValInt p (a+1-s)) (padicValInt p b)
      (padicValInt p c) (a+1-s) b c s (exact_valuation p _ hn)
      (exact_valuation p b hb.ne') (exact_valuation p c hc.ne') he hbc hs hs1 hs2 hz
    exact ⟨hn, by simpa [min_eq_left hbc,max_eq_right hbc] using h⟩
  · have hz' : cubic (a+1-s) c b s + anchor c b s + remainder (a+1-s) c b s = 0 := by
      rw [←root_expansion]
      have hd : (tensorK a c b-s • 1).det = (tensorK a b c-s • 1).det := by
        rw [PairedIdealIntersectionDeterminants.det_tensorK_sub_scalar,
          PairedIdealIntersectionDeterminants.det_tensorK_sub_scalar]
        ring
      exact hd.trans hr
    have h := ordered_ranges p (padicValInt p (a+1-s)) (padicValInt p c)
      (padicValInt p b) (a+1-s) c b s (exact_valuation p _ hn)
      (exact_valuation p c hc.ne') (exact_valuation p b hb.ne') he hcb hs hs1 hs2 hz'
    exact ⟨hn, by simpa [min_eq_right hcb,max_eq_left hcb] using h⟩

/-- Normalized cubic resonance at every shared positive first order.
The divisions are specified by integer equalities, so no nonintegral
rational can be silently reduced modulo a prime. -/
theorem cubic_resonance (p r : ℕ) [hp : Fact p.Prime] (h b c s H B C : ℤ)
    (hr : 1≤r) (hh : ExactOrder p r h)
    (hH : h=(p : ℤ)^r*H) (hB : b=(p : ℤ)^r*B) (hC : c=(p : ℤ)^r*C)
    (hs1 : ¬(p : ℤ)∣s-1)
    (hz : cubic h b c s + anchor b c s + remainder h b c s = 0) :
    (p : ℤ)∣((s-1)*B-s*C-H)*(s*B-(s-1)*C+H) := by
  have hHu : ¬(p : ℤ)∣H := by
    rintro ⟨v,hv⟩
    apply hh.2
    refine ⟨v,?_⟩
    rw [hH,hv,pow_succ]
    ring
  have hb : (p : ℤ)^r∣b := ⟨B,hB⟩
  have hc : (p : ℤ)^r∣c := ⟨C,hC⟩
  have ha : (p : ℤ)^(3*r+1)∣anchor b c s := by
    convert monomial_dvd p r r r 0 2 2 (3*r+1) h b c (-(s-1)^2*(2*s-1))
        hh.1 hb hc (by omega) using 1 <;> simp only [anchor] <;> ring
  have hrem : (p : ℤ)^(3*r+1)∣remainder h b c s := by
    apply remainder_dvd p r r r (3*r+1) h b c s hh.1 hb hc <;> omega
  have hd := dvd_add ha hrem
  have ht : anchor b c s + remainder h b c s = -cubic h b c s := by linarith
  rw [ht,dvd_neg] at hd
  have he : cubic h b c s = (p : ℤ)^(3*r)*
      ((-H*(s-1))*(((s-1)*B-s*C-H)*(s*B-(s-1)*C+H))) := by
    rw [hH,hB,hC]
    have hex : 3*r=r+r+r := by omega
    rw [hex,pow_add,pow_add]
    unfold cubic leftFactor rightFactor
    ring
  rw [he] at hd
  have hd' := cancel_power p (3*r) _ hd
  have hu : ¬(p : ℤ)∣-H*(s-1) := by
    intro hd
    rcases (Nat.prime_iff_prime_int.mp hp.out).dvd_mul.mp hd with hd | hd
    · exact hHu (dvd_neg.mp hd)
    · exact hs1 hd
  exact ((Nat.prime_iff_prime_int.mp hp.out).dvd_mul.mp hd').resolve_left hu

/-- At first order the shared part of the two tails has exactly first
order. There is no coprimality assumption on the tails. -/
theorem root_first_order (a b c s : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (p : ℕ) [Fact p.Prime] (hh : (p : ℤ)∣a+1-s)
    (hgood : ¬(p : ℤ)∣s*(s-1)*(2*s-1))
    (he : padicValInt p (a+1-s)=1)
    (hr : (tensorK a b c-s • 1).det=0) :
    min (padicValInt p b) (padicValInt p c)=1 := by
  obtain ⟨hn,hu,hv⟩ := root_ranges a b c s ha hb hc p hh hgood hr
  by_cases hl : min (padicValInt p b) (padicValInt p c) <
      max (padicValInt p b) (padicValInt p c)
  · rcases hu hl with hh | hh <;> omega
  · have hh := hv (by omega)
    omega

/-- The normalized original root resonance, with its complete telescope
and with integer quotient witnesses constructed from the actual root. -/
theorem normalized_root_resonance (a b c s : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (p : ℕ) [Fact p.Prime] (hh : (p : ℤ)∣a+1-s)
    (hgood : ¬(p : ℤ)∣s*(s-1)*(2*s-1))
    (he : padicValInt p (a+1-s)=min (padicValInt p b) (padicValInt p c))
    (hr : (tensorK a b c-s • 1).det=0) :
    let r := padicValInt p (a+1-s)
    ∃ H B C : ℤ, a+1-s=(p : ℤ)^r*H ∧ b=(p : ℤ)^r*B ∧ c=(p : ℤ)^r*C ∧
      ¬(p : ℤ)∣H ∧ (p : ℤ)∣((s-1)*B-s*C-H)*(s*B-(s-1)*C+H) := by
  dsimp only
  have hn := PairRootArithmetic.root_offset_ne_zero a b c s ha hb hc hr
  have he1 : 1≤padicValInt p (a+1-s) := by
    have hd : (p : ℤ)^1∣a+1-s := by simpa using hh
    exact ((padicValInt_dvd_iff 1 (a+1-s)).mp hd).resolve_left (by omega)
  have hb' : (p : ℤ)^padicValInt p (a+1-s)∣b := by
    apply (padicValInt_dvd_iff _ b).mpr
    exact Or.inr (by rw [he]; exact min_le_left _ _)
  have hc' : (p : ℤ)^padicValInt p (a+1-s)∣c := by
    apply (padicValInt_dvd_iff _ c).mpr
    exact Or.inr (by rw [he]; exact min_le_right _ _)
  obtain ⟨H,hH,hHu⟩ := unit_decomposition p _ _ (exact_valuation p _ hn)
  obtain ⟨B,hB⟩ := hb'
  obtain ⟨C,hC⟩ := hc'
  have hs1 : ¬(p : ℤ)∣s-1 := by
    intro hd
    exact hgood (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _)
  have hz : cubic (a+1-s) b c s + anchor b c s + remainder (a+1-s) b c s = 0 := by
    rwa [root_expansion] at hr
  exact ⟨H,B,C,hH,hB,hC,hHu,cubic_resonance p _ _ b c s H B C he1
    (exact_valuation p _ hn) hH hB hC hs1 hz⟩

/-- The two distinct normalized residues in the unequal-tail branch.
The integer C is the scaled larger tail, hence vanishes modulo p. -/
theorem unequal_resonance (p : ℕ) [hp : Fact p.Prime] (s H U C : ℤ)
    (hC : (p : ℤ) ∣ C) (hU : ¬(p : ℤ) ∣ U)
    (hs2 : ¬(p : ℤ) ∣ 2*s-1)
    (hres : (p : ℤ) ∣ ((s-1)*U-s*C-H)*(s*U-(s-1)*C+H)) :
    ((p : ℤ) ∣ H-(s-1)*U ∨ (p : ℤ) ∣ H+s*U) ∧
      ¬(p : ℤ) ∣ (s-1)*U-(-s*U) := by
  constructor
  · rcases (Nat.prime_iff_prime_int.mp hp.out).dvd_mul.mp hres with h | h
    · left
      have hd := dvd_add h (dvd_mul_of_dvd_right hC s)
      have he : ((s-1)*U-s*C-H)+s*C = -(H-(s-1)*U) := by ring
      rwa [he,dvd_neg] at hd
    · right
      have hd := dvd_add h (dvd_mul_of_dvd_right hC (s-1))
      convert hd using 1 <;> ring
  · intro hd
    have he : (s-1)*U-(-s*U) = (2*s-1)*U := by ring
    rw [he] at hd
    exact ((Nat.prime_iff_prime_int.mp hp.out).dvd_mul.mp hd).elim hs2 hU

/-- The residue alternatives applied to the actual integer root, when b
is the tail of smaller valuation. Tail exchange gives the other ordering. -/
theorem root_unequal_resonance (a b c s : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (p : ℕ) [Fact p.Prime] (hh : (p : ℤ) ∣ a+1-s)
    (hgood : ¬(p : ℤ) ∣ s*(s-1)*(2*s-1))
    (hlt : padicValInt p b < padicValInt p c)
    (he : padicValInt p (a+1-s) = padicValInt p b)
    (hr : (tensorK a b c-s • 1).det = 0) :
    let r := padicValInt p b
    ∃ H U : ℤ, a+1-s=(p : ℤ)^r*H ∧ b=(p : ℤ)^r*U ∧
      ¬(p : ℤ) ∣ U ∧
      ((p : ℤ) ∣ H-(s-1)*U ∨ (p : ℤ) ∣ H+s*U) ∧
      ¬(p : ℤ) ∣ (s-1)*U-(-s*U) := by
  dsimp only
  have hem : padicValInt p (a+1-s) =
      min (padicValInt p b) (padicValInt p c) := by omega
  obtain ⟨H,U,C,hH,hU,hC,hHu,hres⟩ :=
    normalized_root_resonance a b c s ha hb hc p hh hgood hem hr
  rw [he] at hH hU hC
  have hCu : (p : ℤ) ∣ C := by
    apply cancel_power p (padicValInt p b) C
    rw [←hC]
    exact lower_power p _ _ c (by omega) (padicValInt_dvd c)
  have hUu : ¬(p : ℤ) ∣ U := by
    intro hd
    have hex := exact_valuation p b hb.ne'
    apply hex.2
    obtain ⟨v,hv⟩ := hd
    refine ⟨v,?_⟩
    calc
      b = (p : ℤ)^padicValInt p b*U := hU
      _ = (p : ℤ)^(padicValInt p b+1)*v := by rw [hv,pow_succ]; ring
  have hs2 : ¬(p : ℤ) ∣ 2*s-1 := by
    intro hd
    exact hgood (dvd_mul_of_dvd_right hd _)
  obtain ⟨hres',hdist⟩ := unequal_resonance p s H U C hCu hUu hs2 hres
  exact ⟨H,U,hH,hU,hUu,hres',hdist⟩

end D5.S3.Combinatorics.SpectralGraph.PairSharedRoot
