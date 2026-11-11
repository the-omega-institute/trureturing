/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Full physical moment hypotheses, positive concentrated mass, and exact all-n parity propagation. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleScalar
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowScalarData
noncomputable section

open SixRowMiddlePolynomial (W slack cn den T138)

/-- Full physical scalar relaxation. The physical extraction is NOT proved
here. Manuscript §§2--3 supply each field from actual normalized pools:
charge -> r range/nonnegative slack; list sums -> H,D,a,q nonnegative;
Cauchy after deleting actual zero slots -> head_cauchy/tail_cauchy;
finite nonnegative sums/0≤d≤1 -> head_sq/q_mass/q_box;
actual special-edge PSD -> head_cap and finite box -> head_box;
actual 2x2 tail minor -> tail_cap; SAME-vector K6/tail -> coupled;
independent permutation covariance -> variance. No purity bound is a field.
The inherited middle structure intentionally has fewer fields. -/
structure PhysicalScalarHyp (r H D a q : ℝ) : Prop extends
    SixRowMiddleScalar.Hyp6 r H D a q where
  r_nonneg : 0 ≤ r
  r_le : r ≤ 2/5
  a_nonneg : 0 ≤ a
  head_cauchy : H^2/14 ≤ a
  tail_cauchy : D^2/20 ≤ q

def mass (N j r H D : ℝ) : ℝ := N+j*r+H-D
def energy (N j r H D a q : ℝ) : ℝ :=
  (2+r)*mass N j r H D-N*(1+r)+W r H D a q

def thetaEven (N : ℝ) : ℝ := 36/(35*N)
def thetaOdd (N : ℝ) : ℝ := 36*(35*N+12)/(35*N+6)^2

def theta (n : ℕ) : ℝ :=
  if n%2=0 then 6/(35*(n:ℝ)) else
    6*(35*(n:ℝ)+2)/(35*(n:ℝ)+1)^2

def centralIndex (n : ℕ) : ℕ := (5*n+1)/2

def kappa (r : ℝ) : ℝ := (4+4*r-35*r^2)/144

def T (N th r : ℝ) : ℝ := N*(1+r)-(2+r)^2/(4*th)
def gap (N j th r H D a q : ℝ) : ℝ :=
  th*(mass N j r H D)^2-energy N j r H D a q

theorem mass_pos (N j r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q)
    (hN : 138 ≤ N) (hj : 15 ≤ j) : 0 < mass N j r H D := by
  have hm := h.mass
  dsimp only [slack] at hm
  have hjr := mul_nonneg (show 0 ≤ j by linarith) h.r_nonneg
  dsimp only [mass]
  linarith only [hm, h.H_nonneg, h.r_nonneg, hN, hjr]

theorem square_completion (N j th r H D a q : ℝ) (ht : th ≠ 0) :
    gap N j th r H D a q =
    th*(mass N j r H D-(2+r)/(2*th))^2+T N th r-W r H D a q := by
  unfold gap energy T
  field_simp [ht]
  <;> ring

theorem endpoint_zero (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q)
    (hr : r=2/5) : H=0 ∧ D=0 ∧ a=0 ∧ q=0 ∧ slack r H D=0 := by
  have hm := h.mass
  dsimp only [slack] at hm
  have hH : H=0 := by linarith only [hm, hr, h.H_nonneg, h.D_nonneg]
  have hD : D=0 := by linarith only [hm, hr, h.H_nonneg, h.D_nonneg]
  have ha : a=0 := by nlinarith only [h.head_sq, h.a_nonneg, hH]
  have hq : q=0 := by linarith only [h.q_box, h.q_nonneg, hD]
  exact ⟨hH,hD,ha,hq,by simp [slack,hr,hH,hD]; norm_num⟩

theorem mass_energy_envelope (r H D a q : ℝ)
    (h : PhysicalScalarHyp r H D a q) :
    W r H D a q ≤ (6-15*r)*(6-14*r) := by
  have hm := h.mass
  dsimp only [slack] at hm
  have hL : 0 ≤ H+D := add_nonneg h.H_nonneg h.D_nonneg
  have hA : a+q ≤ (H+D)^2 := by
    nlinarith only [h.head_sq,h.q_mass,mul_nonneg h.H_nonneg h.D_nonneg]
  have hp := mul_nonneg (show 0 ≤ 6-15*r-(H+D) by linarith only [hm])
    (show 0 ≤ 6-15*r+(H+D)+r by linarith only [hm,hL,h.r_nonneg])
  dsimp only [W]
  nlinarith only [hA,hp]

/-- Derived, not postulated, uniform tail moment improvement. -/
theorem q_le_29_8 (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) : q ≤ 29/8 := by
  let s := slack r H D
  have hs : 0 ≤ s := h.mass
  have hm : s ≤ 6-D := by dsimp [s,slack]; linarith only [h.H_nonneg,h.r_nonneg]
  have hD : D ≤ 6 := by linarith only [hs,hm]
  have hv := h.variance
  change (5/7)*(a-H^2/15)+(q-D^2/21) ≤ 4*s-s^2/3 at hv
  have hmono := mul_nonneg (show 0 ≤ 6-D-s by linarith only [hm])
    (show 0 ≤ 12-(6-D+s) by linarith only [hm,h.D_nonneg])
  have hbound : q ≤ 12-2*D^2/7 := by
    nlinarith only [hv,h.head_cauchy,sq_nonneg H,hmono]
  by_contra hn
  have hq : 29/8 < q := lt_of_not_ge hn
  have ht : 3*q/2 ≤ D := by
    have hc := h.tail_cap
    rcases le_max_iff.mp hc with hc | hc
    · linarith only [hc,hq]
    · linarith only [hc]
  have hp := mul_nonneg (show 0 ≤ D-3*q/2 by linarith only [ht])
    (show 0 ≤ D+3*q/2 by linarith only [h.D_nonneg,h.q_nonneg])
  have hqprod := mul_nonneg (show 0 ≤ q-29/8 by linarith only [hq])
    (show 0 ≤ q+29/8 by linarith only [h.q_nonneg])
  nlinarith only [hbound,hp,hq,hqprod]

theorem kappa_nonneg (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 2/5) : 0 ≤ kappa r := by
  have hh := mul_nonneg (show 0 ≤ 2-5*r by linarith only [hr'])
    (show 0 ≤ 2+7*r by linarith only [hr])
  dsimp only [kappa]
  nlinarith only [hh]

theorem T_even (N r : ℝ) (hN : 0 < N) :
    T N (thetaEven N) r = N*kappa r := by
  unfold T thetaEven kappa
  field_simp [ne_of_gt hN]
  <;> ring

theorem T_odd (N r : ℝ) (hN : 0 < N) :
    T N (thetaOdd N) r = N*kappa r-(2+r)^2/(4*(35*N+12)) := by
  have h1 : 35*N+12 ≠ 0 := by linarith only [hN]
  have h2 : 35*N+6 ≠ 0 := by linarith only [hN]
  unfold T thetaOdd kappa
  field_simp [h1,h2]
  <;> ring

theorem T138_identity (r : ℝ) :
    T138 r = 138*kappa r-(2+r)^2/(4*(35*138+12)) := by
  unfold T138 kappa
  norm_num
  <;> ring

theorem T_even_ge_base (N r : ℝ) (hN : 138 ≤ N)
    (hr : 0 ≤ r) (hr' : r ≤ 2/5) : T138 r ≤ T N (thetaEven N) r := by
  rw [T_even N r (by linarith only [hN]),T138_identity]
  have hp := mul_nonneg (show 0 ≤ N-138 by linarith only [hN])
    (kappa_nonneg r hr hr')
  have hpen : 0 ≤ (2+r)^2/(4*(35*138+12)) := by positivity
  nlinarith only [hp,hpen]

theorem T_odd_ge_base (N r : ℝ) (hN : 138 ≤ N)
    (hr : 0 ≤ r) (hr' : r ≤ 2/5) : T138 r ≤ T N (thetaOdd N) r := by
  rw [T_odd N r (by linarith only [hN]),T138_identity]
  have hp := mul_nonneg (show 0 ≤ N-138 by linarith only [hN])
    (kappa_nonneg r hr hr')
  have hd : 0 < 4*(35*N+12) := by linarith only [hN]
  have hpen : (2+r)^2/(4*(35*N+12)) ≤ (2+r)^2/(4*(35*138+12)) := by
    apply (div_le_div_iff₀ hd (by norm_num)).mpr
    have hh := mul_nonneg (sq_nonneg (2+r)) (show 0 ≤ 140*(N-138) by linarith)
    nlinarith only [hh]
  nlinarith only [hp,hpen]

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowScalarData
