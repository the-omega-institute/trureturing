import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Algebra
set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Analytic
open D5.S0.Certificates.BoxCover.QuadraticCorner
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Algebra

private noncomputable def P (N j r D H : ℝ) := gap N j r H D (D^2) (H^2)
private noncomputable def t (r D : ℝ) := 2-r-D/5
private noncomputable def U (N j r D H : ℝ) :=
  gap N j r H D (D^2) ((2-D/5)^2-2*r*H-10*r^2)

private theorem theta_facts (N : ℝ) (hn : 25 ≤ N) :
    0 < theta N ∧ theta N < 1 ∧ 1 < theta N*N := by
  have hp : 0 < (N+2)^2 := sq_pos_of_pos (by linarith)
  have hpoly := mul_nonneg (show 0 ≤ N-25 by linarith) (show 0 ≤ N+28 by linarith)
  dsimp [theta]
  constructor
  · exact div_pos (by linarith) hp
  constructor
  · apply (div_lt_one hp).2
    nlinarith
  · rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ hp).2
    nlinarith

/-- The displayed H=0 expansion, with its full rational endpoint estimate. -/
private theorem endpoint_zero (N j r D : ℝ)
    (hN : 25 ≤ N) (hN' : N ≤ 90) (hj : 10 ≤ j) (hj' : j ≤ N-15)
    (hr : 0 ≤ r) (hr' : r ≤ 1/10) (hD : 0 ≤ D) (hD' : D ≤ 1/4) :
    783/400 ≤ P N j r D 0 := by
  have hN0 : 0 < N := by linarith
  let den := (N+2)^2
  let k := 8*(N-1)/den
  let c := 4*N*(N-1)/den
  have hd : 0 < den := by dsimp [den]; positivity
  have hc : 3 ≤ c := by
    apply (le_div_iff₀ hd).2
    nlinarith [mul_nonneg (show 0 ≤ N-25 by linarith) (show 0 ≤ N+9 by linarith)]
  have hk0 : 0 ≤ k := by
    dsimp [k]
    exact div_nonneg (by linarith) (le_of_lt hd)
  have hk : k ≤ 8/25 := by
    apply (div_le_iff₀ hd).2
    dsimp [den]
    nlinarith [mul_nonneg (show 0 ≤ N-25 by linarith) (show 0 ≤ N+4 by linarith)]
  have hr2 : r^2 ≤ 1/100 := by nlinarith
  have hj0 : 0 ≤ j := by linarith
  have hj90 : j ≤ 90 := by linarith
  have hjr : j*r^2 ≤ 9/10 := by
    calc
      j*r^2 ≤ j*(1/100) := mul_le_mul_of_nonneg_left hr2 hj0
      _ ≤ 9/10 := by nlinarith
  have hkD : k*D ≤ 2/25 := by
    calc
      k*D ≤ (8/25)*D := mul_le_mul_of_nonneg_right hk hD
      _ ≤ 2/25 := by linarith
  have hD2 : D^2 ≤ 1/16 := by nlinarith
  have hpos1 : 0 ≤ k*(j*r) := mul_nonneg hk0 (mul_nonneg hj0 hr)
  have hpos2 : 0 ≤ theta N*(j*r-D)^2 := mul_nonneg
    (le_of_lt (theta_facts N hN).1) (sq_nonneg _)
  have he : P N j r D 0 = c+(k-r)*(j*r)-k*D+theta N*(j*r-D)^2-D^2 := by
    dsimp [P, gap, mass, energy, theta, c, k, den]
    field_simp
    <;> ring
  rw [he]
  nlinarith only [hc, hjr, hkD, hD2, hpos1, hpos2]

/-- The displayed H=t factorization; both brackets have uniform positive
lower bounds, proved from polynomial endpoint factors rather than an oracle. -/
private theorem endpoint_t (N j r D : ℝ)
    (hN : 25 ≤ N) (hN' : N ≤ 90) (hj : 10 ≤ j) (hj' : j ≤ N-15)
    (hr : 0 ≤ r) (hr' : r ≤ 1/10) (hD : 0 ≤ D) (hD' : D ≤ 1/4) :
    0 ≤ P N j r D (t r D) := by
  have hN0 : 0 < N := by linarith
  let C := N^2-N*j+5*N-8*j+12
  let Cmax := N^2-5*N-68
  let B := 12*(N+2)-C*r-(12/5)*(N+8)*D
  let E := (4/5)*(N-16)*(N+2)-(2/25)*(13*N^2+34*N-92)*D
  have hC : C ≤ Cmax := by
    have hp := mul_nonneg (show 0 ≤ N+8 by linarith) (show 0 ≤ j-10 by linarith)
    dsimp [C, Cmax]
    nlinarith only [hp]
  have hCm : 0 ≤ Cmax := by
    dsimp [Cmax]
    nlinarith [mul_nonneg (show 0 ≤ N-25 by linarith) (show 0 ≤ N+20 by linarith)]
  have hCr : C*r ≤ Cmax/10 := by
    calc
      C*r ≤ Cmax*r := mul_le_mul_of_nonneg_right hC hr
      _ ≤ Cmax/10 := by nlinarith [mul_nonneg hCm (show 0 ≤ 1/10-r by linarith)]
  have hDmul : (12/5)*(N+8)*D ≤ (3/5)*(N+8) := by
    nlinarith [mul_nonneg (show 0 ≤ (12/5)*(N+8) by linarith)
      (show 0 ≤ 1/4-D by linarith)]
  have hB : 261 ≤ B := by
    have hp := mul_nonneg (show 0 ≤ N-25 by linarith) (show 0 ≤ 94-N by linarith)
    dsimp [B, Cmax] at *
    nlinarith only [hCr, hDmul, hp]
  have hcoef : 0 ≤ 13*N^2+34*N-92 := by nlinarith [sq_nonneg (N-25)]
  have hEd : (2/25)*(13*N^2+34*N-92)*D ≤ (1/50)*(13*N^2+34*N-92) := by
    nlinarith [mul_nonneg hcoef (show 0 ≤ 1/4-D by linarith)]
  have hE : 837/50 ≤ E := by
    have hp := mul_nonneg (show 0 ≤ N-25 by linarith) (show 0 ≤ 27*N+81 by linarith)
    dsimp [E]
    nlinarith only [hEd, hp]
  have he : (N+2)^2*P N j r D (t r D) = (j-1)*r*B+D*E := by
    dsimp [P, gap, theta, mass, energy, t, B, C, E]
    field_simp
    <;> ring
  have hp1 := mul_nonneg (mul_nonneg (show 0 ≤ j-1 by linarith) hr)
    (show 0 ≤ B by linarith)
  have hp2 := mul_nonneg hD (show 0 ≤ E by linarith)
  have hd : 0 < (N+2)^2 := by positivity
  nlinarith only [he, hp1, hp2, hd]

/-- Full analytic equality neighbourhood, including r=D=0 and all H.
Only two of the actual necessary caps and q≤D² are used in this region. -/
theorem analytic_region (N j r H D q a : ℝ)
    (hN : 25 ≤ N) (hN' : N ≤ 90) (hj : 10 ≤ j) (hj' : j ≤ N-15)
    (h : Hyp r H D q a) (hr : r ≤ 1/10) (hD : D ≤ 1/4) :
    0 ≤ gap N j r H D q a := by
  have ht : 0 < t r D := by dsimp [t]; linarith [h.r0, h.D0]
  have hf := theta_facts N hN
  have hp0 : 0 ≤ P N j r D 0 :=
    (by norm_num : (0 : ℝ) ≤ 783/400).trans
      (endpoint_zero N j r D hN hN' hj hj' h.r0 hr h.D0 hD)
  have hpt := endpoint_t N j r D hN hN' hj hj' h.r0 hr h.D0 hD
  by_cases hH : H ≤ t r D
  · let c := P N j r D 0
    let l := 2*theta N*(N+j*r-D)-2*(1+r)
    let d := theta N-1
    have hd : max d 0 = 0 := max_eq_right (by dsimp [d]; linarith [hf.2.1])
    have he (v : ℝ) : c+l*v+d*v^2 = P N j r D v := by
      dsimp [c, l, d, P, gap, mass, energy]
      ring
    have hp := quadratic_lower c l d 0 (t r D) H 0 h.H0 hH
      (by rw [he]; exact hp0) (by rw [he]; exact hpt)
    rw [hd] at hp
    have hpH : 0 ≤ P N j r D H := by simpa only [zero_mul, zero_div, sub_zero, he] using hp
    have ha := h.amax
    have hq := h.qsq
    dsimp [P, gap, energy] at *
    linarith
  · have hHt : t r D ≤ H := le_of_lt (lt_of_not_ge hH)
    have hSt : N ≤ mass N j r (t r D) D := by
      have hjr := mul_nonneg (show 0 ≤ j-1 by linarith) h.r0
      dsimp [mass, t]
      nlinarith only [hjr, hD]
    have hder : 0 ≤ 2*theta N*(mass N j r (t r D) D)-2 := by
      have hp := mul_le_mul_of_nonneg_left hSt (le_of_lt hf.1)
      nlinarith [hf.2.2]
    have hdiff : U N j r D H-U N j r D (t r D) =
        (H-t r D)*(2*theta N*(mass N j r (t r D) D)-2+theta N*(H-t r D)) := by
      dsimp [U, gap, mass, energy]
      ring
    have hinc : 0 ≤ U N j r D H-U N j r D (t r D) := by
      rw [hdiff]
      exact mul_nonneg (sub_nonneg.mpr hHt)
        (add_nonneg hder (mul_nonneg (le_of_lt hf.1) (sub_nonneg.mpr hHt)))
    have heq : U N j r D (t r D) = P N j r D (t r D)+9*r^2 := by
      dsimp [U, P, gap, energy, t]
      ring
    have hu : 0 ≤ U N j r D H := by nlinarith only [hinc, heq, hpt, sq_nonneg r]
    have ha := h.starD
    have hq := h.qsq
    dsimp [U, gap, energy] at *
    linarith

end D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Analytic
