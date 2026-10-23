/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Nineteen
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Nineteen
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Every real concentrated j in [10,80], including the complete n19 low regime. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates
set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Nineteen
open FiveRowP2Scalar FiveRowP2Certificates
noncomputable section
private def C (z : ℝ) : ℝ := (5/456)*(z+19/5)^2+19/5
private def quartic (d : ℝ) : ℝ :=
  (-451*d^4+280*d^3+27832*d^2-45472*d+60368)/357504

private theorem quartic_0 (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (1/10:ℝ) ≤ quartic (0+t) := by
  have hid : quartic (0+t)-1/10 = (157/2280)*t^0*(1-t)^4 +
      (169/1140)*t^1*(1-t)^3 +
      (499/4560)*t^2*(1-t)^2 +
      (1607/31920)*t^3*(1-t)^1 +
      (34033/1787520)*t^4*(1-t)^0 := by
    unfold quartic
    ring
  have hn : 0 ≤ (157/2280)*t^0*(1-t)^4 +
      (169/1140)*t^1*(1-t)^3 +
      (499/4560)*t^2*(1-t)^2 +
      (1607/31920)*t^3*(1-t)^1 +
      (34033/1787520)*t^4*(1-t)^0 := by positivity
  linarith only [hid,hn]

private theorem quartic_1 (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (1/10:ℝ) ≤ quartic (1+t) := by
  have hid : quartic (1+t)-1/10 = (34033/1787520)*t^0*(1-t)^4 +
      (1424/13965)*t^1*(1-t)^3 +
      (3691/13965)*t^2*(1-t)^2 +
      (4114/13965)*t^3*(1-t)^1 +
      (3127/27930)*t^4*(1-t)^0 := by
    unfold quartic
    ring
  have hn : 0 ≤ (34033/1787520)*t^0*(1-t)^4 +
      (1424/13965)*t^1*(1-t)^3 +
      (3691/13965)*t^2*(1-t)^2 +
      (4114/13965)*t^3*(1-t)^1 +
      (3127/27930)*t^4*(1-t)^0 := by positivity
  linarith only [hid,hn]

private theorem quartic_2 (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (1/10:ℝ) ≤ quartic (2+t) := by
  have hid : quartic (2+t)-1/10 = (3127/27930)*t^0*(1-t)^4 +
      (2798/4655)*t^1*(1-t)^3 +
      (16531/13965)*t^2*(1-t)^2 +
      (4668/4655)*t^3*(1-t)^1 +
      (548593/1787520)*t^4*(1-t)^0 := by
    unfold quartic
    ring
  have hn : 0 ≤ (3127/27930)*t^0*(1-t)^4 +
      (2798/4655)*t^1*(1-t)^3 +
      (16531/13965)*t^2*(1-t)^2 +
      (4668/4655)*t^3*(1-t)^1 +
      (548593/1787520)*t^4*(1-t)^0 := by positivity
  linarith only [hid,hn]

private theorem quartic_margin (d : ℝ) (hd : 0 ≤ d) (hd' : d ≤ 3) :
    (1/10:ℝ) ≤ quartic d := by
  by_cases h1 : d ≤ 1
  · simpa using quartic_0 d hd h1
  · by_cases h2 : d ≤ 2
    · convert quartic_1 (d-1) (by linarith) (by linarith) using 1 <;> congr 1 <;> ring
    · convert quartic_2 (d-2) (by linarith) (by linarith) using 1 <;> congr 1 <;> ring

private theorem low_smallq {r H D a q s : ℝ} (h : Hyp r H D a q s)
    (hq : q ≤ 3/5) :
    (1/10:ℝ) ≤ C (H+r-D)-(a+2*r*H+r^2+q) := by
  let t := Real.sqrt (a+2*r*H+r^2)
  let d := Real.sqrt (14*q)
  have ha' : 0 ≤ a+2*r*H+r^2 := by
    nlinarith [h.a0, mul_nonneg h.r0 h.H0, sq_nonneg r]
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have ht2 : t^2=a+2*r*H+r^2 := Real.sq_sqrt ha'
  have hd2 : d^2=14*q := Real.sq_sqrt (mul_nonneg (by norm_num) h.q0)
  have hd3 : d ≤ 3 := by nlinarith
  have hD : D ≤ d := by nlinarith [h.qmin,h.D0]
  have hH : t ≤ H+r := by nlinarith [h.amax,h.H0,h.r0]
  have hbound : t ≤ 2-q/2 := by nlinarith [h.coupled,h.qcap,sq_nonneg r]
  have hqeq : q=d^2/14 := by nlinarith only [hd2]
  have hmono : C (t-d) ≤ C (H+r-D) := by
    have h1 : 0 ≤ H+r-D-(t-d) := by linarith
    have h2 : 0 ≤ H+r-D+(t-d)+38/5 := by linarith [h.H0,h.r0,h.D0]
    have hp := mul_nonneg h1 h2
    dsimp [C]
    nlinarith only [hp]
  have h0 : (1/10:ℝ) ≤ C (-d)-q := by
    dsimp [C]
    nlinarith [sq_nonneg (-d+19/5)]
  have h1 : (1/10:ℝ) ≤ C (2-q/2-d)-(2-q/2)^2-q := by
    have hp := quartic_margin d hd hd3
    have hid : C (2-d^2/28-d)-(2-d^2/28)^2-d^2/14 = quartic d := by
      unfold C quartic
      ring
    rw [hqeq]
    have hdiv : d^2/14/2 = d^2/28 := by ring
    rw [hdiv, hid]
    exact hp
  have hp := quadratic_lower (5/456-1) (2*(5/456)*(19/5-d))
    ((5/456)*(19/5-d)^2+19/5-q) 0 (2-q/2) t (1/10)
    (by norm_num) ht hbound (by dsimp [C] at h0; nlinarith only [h0])
    (by dsimp [C] at h1; nlinarith only [h1])
  dsimp [C] at hmono ⊢
  nlinarith only [hp,hmono,ht2]

private theorem low_largeq {r H D a q s : ℝ} (h : Hyp r H D a q s)
    (hq : 3/5 ≤ q) :
    (31/100:ℝ) ≤ C (H+r-D)-(a+2*r*H+r^2+q) := by
  have hp : (51/100:ℝ) ≤ phi q := by
    have hh := quadratic_lower (-1/4) 1 0 (3/5) (10/3) q (51/100)
      (by norm_num) hq h.qcap (by norm_num) (by norm_num)
    dsimp [phi]
    nlinarith only [hh]
  have he := (energy_envelopes h).1
  dsimp [C] at *
  nlinarith [sq_nonneg (H+r-D+19/5),sq_nonneg r]

/-- Positive retained-square margin on the COMPLETE closed low interval.
This actually permits every real j>=1. No enumeration or j grid. -/
private theorem low_margin {r H D a q s : ℝ} (h : Hyp r H D a q s)
    (hr : r ≤ 1/12) (j : ℝ) (hj : 1 ≤ j) :
    (2207/328320:ℝ) ≤ (5/456)*(mass 95 j r H D)^2-energy 95 j r H D a q := by
  let M := C (H+r-D)-(a+2*r*H+r^2+q)
  let x := r*(j-1)
  let A := (1/12:ℝ)+2*(5/456)*(H-D)-r*(1-2*(5/456))
  have hx : 0 ≤ x := mul_nonneg h.r0 (by linarith)
  have hid : (5/456)*(mass 95 j r H D)^2-energy 95 j r H D a q =
      M+(5/456)*x^2+x*A := by
    dsimp [M,x,A,C,mass,energy,W]
    ring
  by_cases hq : q ≤ 3/5
  · have hM : (1/10:ℝ) ≤ M := low_smallq h hq
    have hD : D ≤ 3 := by nlinarith [h.qmin,h.D0]
    have hA : -(35/6)*(5/456) ≤ A := by dsimp [A]; linarith [h.H0]
    have hprod := mul_nonneg hx (sub_nonneg.mpr hA)
    have hs := sq_nonneg (x-35/12)
    nlinarith only [hid,hM,hprod,hs]
  · have hM : (31/100:ℝ) ≤ M := low_largeq h (le_of_not_ge hq)
    have hD : D ≤ 5 := by linarith [h.mass,h.H0,h.s0,h.r0]
    have hA : -(59/6)*(5/456) ≤ A := by dsimp [A]; linarith [h.H0]
    have hprod := mul_nonneg hx (sub_nonneg.mpr hA)
    have hs := sq_nonneg (x-59/12)
    nlinarith only [hid,hM,hprod,hs]

private theorem middle_largeq {r H D a q s : ℝ} (h : Hyp r H D a q s)
    (hr : r ≤ 1/5) (hq : 1 ≤ q) : W r H D a q ≤ B r := by
  have hp : (5/9:ℝ) ≤ phi q := by
    have hh := quadratic_lower (-1/4) 1 0 1 (10/3) q (5/9)
      (by norm_num) hq h.qcap (by norm_num) (by norm_num)
    dsimp [phi]
    nlinarith only [hh]
  have he := (energy_envelopes h).1
  have hm := mul_nonneg h.r0 (show 0 ≤ 5-10*r-H-D by linarith [h.mass,h.s0])
  have hrH := mul_nonneg h.r0 h.H0
  have hs : 0 ≤ 1/25-r^2 := by nlinarith [h.r0]
  have hb : (4/1125:ℝ) ≤ 16/45-(6/5)*r-(14/5)*r^2 := by nlinarith
  dsimp [B,W] at *
  nlinarith

/-- Full n19 scalar lemma. All j in [10,80] are covered continuously,
including endpoints; the proof in fact only needs j>=1. -/
theorem concentrated_nineteen (r H D a q s j : ℝ) (h : Hyp r H D a q s)
    (hj : 10 ≤ j) (hj' : j ≤ 80) :
    energy 95 j r H D a q ≤ (5/456)*(mass 95 j r H D)^2 := by
  by_cases hlo : r ≤ 1/12
  · have hm := low_margin h hlo j (by linarith)
    linarith
  have hbudget : W r H D a q ≤ B r := by
    by_cases hmid : r ≤ 1/5
    · by_cases hq : q ≤ 1
      · exact smallq_certificate h (le_of_not_ge hlo) hmid hq
      · exact middle_largeq h hmid (le_of_not_ge hq)
    · exact upper_certificate h (le_of_not_ge hmid)
  have hid : (5/456)*(mass 95 j r H D)^2-energy 95 j r H D a q =
      (5/456)*(mass 95 j r H D-(228/5)*(2+r))^2+B r-W r H D a q := by
    unfold energy mass B W
    ring
  have hs := sq_nonneg (mass 95 j r H D-(228/5)*(2+r))
  nlinarith only [hid,hs,hbudget]
end
end D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Nineteen
