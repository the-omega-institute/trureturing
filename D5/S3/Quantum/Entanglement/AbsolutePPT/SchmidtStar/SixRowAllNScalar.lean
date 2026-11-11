/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowConcentration.original_upper_and_equality; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.concentrated_scalar
   digest: Exact parity propagation and odd integer plateau separation. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowOuterScalar
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowAllNScalar
noncomputable section

open SixRowMiddlePolynomial (W slack T138)
open SixRowScalarData SixRowOuterPolynomial SixRowOuterScalar

/-- Low-r propagation keeps the n24 threshold, rather than the false
    global n23 W threshold. -/
theorem low_threshold_propagation (N r : ℝ) (hN : 150 ≤ N)
    (hr0 : 0 ≤ r) (hr : r ≤ 1/12) :
    T144 r < T N (thetaEven N) r ∧ T144 r < T N (thetaOdd N) r := by
  have hk : 1/36 ≤ kappa r := by
    have hp := mul_nonneg hr0 (show 0 ≤ 4-35*r by linarith only [hr])
    dsimp [kappa]; nlinarith only [hp]
  have hp := mul_nonneg (show 0 ≤ N-144 by linarith only [hN])
    (sub_nonneg.mpr hk)
  have hmain : 1/6 ≤ (N-144)*kappa r := by nlinarith only [hp,hN]
  have hpen : (2+r)^2/(4*(35*N+12)) ≤ 1/1000 := by
    apply (div_le_iff₀ (by linarith only [hN])).mpr
    nlinarith only [hr0,hr,hN]
  have h144 : T144 r=144*kappa r := by dsimp [T144,kappa]; ring
  rw [T_even N r (by linarith only [hN]),T_odd N r (by linarith only [hN]),h144]
  constructor <;> nlinarith only [hmain,hpen]

/-- Even near-central estimate with an explicit delta/3 margin. -/
theorem even_high_gap (N j r H D a q : ℝ)
    (h : PhysicalScalarHyp r H D a q) (hN : 144 ≤ N) (hr : 1/3 ≤ r) :
    (2-5*r)/3 ≤ gap N j (thetaEven N) r H D a q := by
  let d := 2-5*r
  have hd : 0 ≤ d := by dsimp [d]; linarith only [h.r_le]
  have hd' : d ≤ 1/3 := by dsimp [d]; linarith only [hr]
  have hth : 0 < thetaEven N := by unfold thetaEven; positivity
  have hs := square_completion N j (thetaEven N) r H D a q (ne_of_gt hth)
  rw [T_even N r (by linarith only [hN])] at hs
  have hW := mass_energy_envelope r H D a q h
  have hcoef := mul_nonneg (show 0 ≤ N-144 by linarith only [hN])
    (show 0 ≤ 24-7*d by linarith only [hd'])
  have hbound : 1/3 ≤ N*(24-7*d)/720-(42*d+6)/5 := by
    nlinarith only [hcoef,hd']
  have hp := mul_nonneg hd (sub_nonneg.mpr hbound)
  have hsq := mul_nonneg hth.le (sq_nonneg (mass N j r H D-(2+r)/(2*thetaEven N)))
  dsimp only [kappa,d] at *
  nlinarith only [hs,hW,hp,hsq]

def Aplus (N : ℝ) : ℝ := 350*N^3+312075*N^2-256284*N-114804
def Bplus (N : ℝ) : ℝ := 1225*N^3-43470*N^2-61668*N-9288
def Aminus (N : ℝ) : ℝ := 1750*N^3+1527825*N^2-1292580*N-580716
def Bminus (N : ℝ) : ℝ := 6125*N^3-219450*N^2-309060*N-127224

def Mminus (N d : ℝ) : ℝ := 7*N/6-1/5-(N/12-31/10)*d
def Mplus (N d : ℝ) : ℝ := 7*N/6+1/5-(N/12+31/10)*d
def centerOdd (N d : ℝ) : ℝ :=
  7*N/6-7*N*d/72+(12-d)/(10*(35*N+12))
def Gminus (N d : ℝ) : ℝ :=
  (5184+Bminus N*d-Aminus N*d^2)/(150*(35*N+6)^2)
def Gplus (N d : ℝ) : ℝ :=
  (Bplus N*d-Aplus N*d^2)/(30*(35*N+6)^2)

/-- Literal corrected G identities; no decimal or fitted coefficient. -/
theorem odd_endpoint_identities (N d : ℝ) (hN : 138 ≤ N) :
    Gminus N d = thetaOdd N*(Mminus N d)^2-(2+(2-d)/5)*Mminus N d+
      N*(1+(2-d)/5)-(42*d^2+6*d)/5 ∧
    Gplus N d = thetaOdd N*(Mplus N d)^2-(2+(2-d)/5)*Mplus N d+
      N*(1+(2-d)/5)-(42*d^2+6*d)/5 := by
  have hn : 35*N+6 ≠ 0 := by linarith only [hN]
  constructor <;> simp only [Gminus,Gplus,Aminus,Bminus,Aplus,Bplus,thetaOdd,Mminus,Mplus]
    <;> field_simp [hn] <;> ring

/-- Shifted positive-coefficient expansions from the manuscript. -/
theorem odd_coefficients (N : ℝ) (hN : 138 ≤ N) :
    0 < Aplus N ∧ 0 < Aminus N ∧
    0 < 40*Bplus N-Aplus N ∧ 0 < 40*Bminus N-Aminus N := by
  let x := N-138
  have hx : 0 ≤ x := by dsimp [x]; linarith only [hN]
  have h1 : Aplus N=350*x^3+456975*x^2+105872616*x+6827499504 := by dsimp [Aplus,x]; ring
  have h2 : Aminus N=1750*x^3+2252325*x^2+520368120*x+33516068544 := by dsimp [Aminus,x]; ring
  have h3 : 40*Bplus N-Aplus N=48650*x^3+18090225*x^2+2211219864*x+88493542416 := by
    dsimp [Aplus,Bplus,x]; ring
  have h4 : 40*Bminus N-Aminus N=243250*x^3+90399675*x^2+11041881480*x+441482239296 := by
    dsimp [Aminus,Bminus,x]; ring
  refine ⟨?_,?_,?_,?_⟩
  · rw [h1]; positivity
  · rw [h2]; positivity
  · rw [h3]; positivity
  · rw [h4]; positivity

theorem odd_endpoint_signs (N d : ℝ) (hN : 138 ≤ N)
    (hd : 0 ≤ d) (hd' : d ≤ 1/40) :
    0 < Gminus N d ∧ 0 ≤ Gplus N d ∧ (Gplus N d=0 → d=0) := by
  obtain ⟨hAp,hAm,hBp,hBm⟩ := odd_coefficients N hN
  have hp : 0 < Bplus N-Aplus N*d := by
    have hh := mul_nonneg hAp.le (show 0 ≤ 1/40-d by linarith only [hd'])
    nlinarith only [hBp,hh]
  have hm : 0 < Bminus N-Aminus N*d := by
    have hh := mul_nonneg hAm.le (show 0 ≤ 1/40-d by linarith only [hd'])
    nlinarith only [hBm,hh]
  have hden : 0 < (35*N+6)^2 := sq_pos_of_pos (by linarith only [hN])
  have hgn : 0 ≤ Gplus N d := by
    unfold Gplus
    apply div_nonneg _ (by positivity)
    nlinarith only [mul_nonneg hd hp.le]
  refine ⟨?_,hgn,?_⟩
  · unfold Gminus
    apply div_pos _ (by positivity)
    nlinarith only [mul_nonneg hd hm.le]
  · intro hz
    unfold Gplus at hz
    have hh : d*(Bplus N-Aplus N*d)=0 := by
      have hh := (div_eq_zero_iff).mp hz
      rcases hh with hh | hh
      · nlinarith only [hh]
      · exfalso
        have hden0 : 0 < 30*(35*N+6)^2 := by positivity
        linarith only [hh,hden0]
    exact (mul_eq_zero.mp hh).resolve_right (ne_of_gt hp)

/-- The two mass endpoints are separated from the center on the full
    tiny-delta domain. This hypothesis is arithmetic, not a purity bound. -/
theorem odd_center_distances (N d : ℝ) (hN : 138 ≤ N)
    (hd : 0 ≤ d) (hd' : d ≤ 3/N^2) :
    Mminus N d+19/100 < centerOdd N d ∧
    centerOdd N d+19/100 < Mplus N d := by
  have hNp : 0 < N := by linarith only [hN]
  have hdn : d*N^2 ≤ 3 := (le_div_iff₀ (sq_pos_of_pos hNp)).mp hd'
  have hp := mul_nonneg (show 0 ≤ N-100 by linarith only [hN]) (mul_nonneg hd hNp.le)
  have hNd : N*d ≤ 3/100 := by nlinarith only [hdn,hp]
  have hp2 := mul_nonneg (show 0 ≤ N-100 by linarith only [hN]) hd
  have hdsmall : d ≤ 3/10000 := by nlinarith only [hNd,hp2]
  have hden : 0 < 10*(35*N+12) := by linarith only [hN]
  have hpen0 : 0 ≤ (12-d)/(10*(35*N+12)) := div_nonneg (by linarith only [hdsmall]) hden.le
  have hpen1 : (12-d)/(10*(35*N+12)) ≤ 6/17500 := by
    apply (div_le_iff₀ hden).mpr
    linarith only [hN,hd]
  dsimp only [centerOdd,Mminus,Mplus]
  constructor <;> nlinarith only [hNd,hdsmall,hpen0,hpen1,mul_nonneg hNp.le hd]

/-- Away from the very thin integer region, the odd correction is paid
    by a uniform positive margin. -/
theorem odd_high_continuous (N r H D a q : ℝ)
    (h : PhysicalScalarHyp r H D a q) (hN : 138 ≤ N)
    (hr : 79/200 ≤ r) (hd : 3/N^2 ≤ 2-5*r) :
    W r H D a q < T N (thetaOdd N) r := by
  let d := 2-5*r
  have hd0 : 0 ≤ d := by dsimp [d]; linarith only [h.r_le]
  have hd1 : d ≤ 1/40 := by dsimp [d]; linarith only [hr]
  have hNp : 0 < N := by linarith only [hN]
  have hdn : 3 ≤ d*N^2 := (div_le_iff₀ (sq_pos_of_pos hNp)).mp hd
  have hc0 := mul_nonneg hNp.le (show 0 ≤ 1/40-d by linarith only [hd1])
  have hc : N/50 ≤ N*(24-7*d)/720-(42*d+6)/5 := by
    nlinarith only [hc0,hN,hd1]
  have hprod := mul_nonneg hd0 (sub_nonneg.mpr hc)
  have hpen : (12-d)^2/(100*(35*N+12)) ≤ 36/(875*N) := by
    apply (div_le_div_iff₀ (by linarith only [hN]) (by positivity)).mpr
    have hm := mul_nonneg hNp.le (show 0 ≤ 144-(12-d)^2 by nlinarith only [hd0,hd1])
    nlinarith only [hm]
  have hdelta : 3/(50*N) ≤ d*N/50 := by
    apply (div_le_iff₀ (by positivity : 0 < 50*N)).mpr
    nlinarith only [hdn]
  have hpos : 0 < 3/(50*N)-36/(875*N) := by
    have hid : 3/(50*N)-36/(875*N)=33/(1750*N) := by field_simp; ring
    rw [hid]
    positivity
  have hW := mass_energy_envelope r H D a q h
  have hW' : W r H D a q ≤ (42*d^2+6*d)/5 := by
    dsimp only [d] at *
    nlinarith only [hW]
  have hid : N*kappa r-(2+r)^2/(4*(35*N+12)) =
      d*(N*(24-7*d)/720-(42*d+6)/5)-
        (12-d)^2/(100*(35*N+12))+(42*d^2+6*d)/5 := by
    dsimp only [kappa,d]
    have hn : 35*N+12 ≠ 0 := by linarith only [hN]
    field_simp [hn] <;> ring
  rw [T_odd N r hNp,hid]
  nlinarith only [hprod,hpen,hdelta,hpos,hW']

/-- Integer plateau separation in the odd thin interval. k is the lower
    neighboring integer, with its exact arithmetic value; no j is replaced
    by the central value. The conclusion classifies both lower and upper
    half-lattices, including delta=0. -/
theorem odd_high_integer (N r H D a q : ℝ) (j k : ℤ)
    (h : PhysicalScalarHyp r H D a q) (hN : 138 ≤ N)
    (hr : 79/200 ≤ r) (hd : 2-5*r ≤ 3/N^2)
    (hk : (k:ℝ)=(5*N-6)/12) :
    0 ≤ gap N (j:ℝ) (thetaOdd N) r H D a q ∧
    (gap N (j:ℝ) (thetaOdd N) r H D a q=0 →
      r=2/5 ∧ H=0 ∧ D=0 ∧ a=0 ∧ q=0 ∧ j=k+1) := by
  let d := 2-5*r
  let M := mass N (j:ℝ) r H D
  have hd0 : 0 ≤ d := by dsimp [d]; linarith only [h.r_le]
  have hd1 : d ≤ 1/40 := by dsimp [d]; linarith only [hr]
  have hNp : 0 < N := by linarith only [hN]
  have hth : 0 < thetaOdd N := by unfold thetaOdd; positivity
  have hc := odd_center_distances N d hN hd0 hd
  obtain ⟨hGm,hGp,hGpz⟩ := odd_endpoint_signs N d hN hd0 hd1
  obtain ⟨hIm,hIp⟩ := odd_endpoint_identities N d hN
  have hcenter : centerOdd N d=(2+r)/(2*thetaOdd N) := by
    have h1 : 35*N+6 ≠ 0 := by linarith only [hN]
    have h2 : 35*N+12 ≠ 0 := by linarith only [hN]
    dsimp [centerOdd,thetaOdd,d]
    field_simp [h1,h2]
    <;> ring
  have hlin : 2*thetaOdd N*centerOdd N d=2+r := by
    rw [hcenter]
    field_simp [ne_of_gt hth]
  have hdiff (m : ℝ) :
      thetaOdd N*((M-m)*(M+m-2*centerOdd N d)) =
        thetaOdd N*M^2-(2+r)*M-(thetaOdd N*m^2-(2+r)*m) := by
    calc
      _ = thetaOdd N*M^2-thetaOdd N*m^2-(M-m)*(2*thetaOdd N*centerOdd N d) := by ring
      _ = _ := by rw [hlin]; ring
  have hW := mass_energy_envelope r H D a q h
  have hW' : W r H D a q ≤ (42*d^2+6*d)/5 := by
    dsimp [d] at *
    nlinarith only [hW]
  have hm := h.mass
  dsimp only [slack] at hm
  by_cases hj : j ≤ k
  · have hjr : (j:ℝ) ≤ (k:ℝ) := by exact_mod_cast hj
    have hmul := mul_nonneg h.r_nonneg (sub_nonneg.mpr hjr)
    have hM : M ≤ Mminus N d := by
      dsimp [M,mass,Mminus,d]
      nlinarith only [hm,h.H_nonneg,h.D_nonneg,hmul,hk]
    have hprod := mul_nonneg (show 0 ≤ Mminus N d-M by linarith only [hM])
      (show 0 ≤ 2*centerOdd N d-Mminus N d-M by linarith only [hc.1,hM])
    have hcmp := mul_nonneg hth.le hprod
    have hG : Gminus N d ≤ gap N (j:ℝ) (thetaOdd N) r H D a q := by
      have hh : 0 ≤ thetaOdd N*((M-Mminus N d)*(M+Mminus N d-2*centerOdd N d)) := by
        convert hcmp using 1 <;> ring
      rw [hdiff] at hh
      have hrid : r=(2-d)/5 := by dsimp [d]; ring
      dsimp only [gap,energy,M] at *
      rw [← hrid] at hIm
      nlinarith only [hh,hIm,hW']
    exact ⟨by linarith only [hG,hGm],fun hz => by linarith only [hz,hG,hGm]⟩
  · have hj : k+1 ≤ j := by omega
    have hjr : (k:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast hj
    have hmul := mul_nonneg h.r_nonneg (sub_nonneg.mpr hjr)
    have hM : Mplus N d ≤ M := by
      dsimp [M,mass,Mplus,d]
      nlinarith only [hm,h.H_nonneg,h.D_nonneg,hmul,hk]
    have hsum : 0 < M+Mplus N d-2*centerOdd N d := by linarith only [hc.2,hM]
    have hprod := mul_nonneg (show 0 ≤ M-Mplus N d by linarith only [hM]) hsum.le
    have hcmp := mul_nonneg hth.le hprod
    have hG : Gplus N d ≤ gap N (j:ℝ) (thetaOdd N) r H D a q := by
      rw [hdiff] at hcmp
      have hrid : r=(2-d)/5 := by dsimp [d]; ring
      dsimp only [gap,energy,M] at *
      rw [← hrid] at hIp
      nlinarith only [hcmp,hIp,hW']
    refine ⟨by linarith only [hG,hGp],?_⟩
    intro hz
    have hdZ : d=0 := hGpz (by linarith only [hG,hGp,hz])
    have hrZ : r=2/5 := by dsimp [d] at hdZ; linarith only [hdZ]
    obtain ⟨hH,hD,ha,hq,_⟩ := endpoint_zero r H D a q h hrZ
    have hMZ : M=Mplus N d := by
      by_contra hn
      have hmassDiff : 0 < M-Mplus N d := sub_pos.mpr (lt_of_le_of_ne hM (Ne.symm hn))
      have hp : 0 < (M-Mplus N d)*(M+Mplus N d-2*centerOdd N d) := mul_pos hmassDiff hsum
      have hcmp' := mul_pos hth hp
      rw [hdiff (Mplus N d)] at hcmp'
      have hrid : r=(2-d)/5 := by dsimp [d]; ring
      rw [← hrid] at hIp
      dsimp only [gap,energy,M] at *
      nlinarith only [hcmp',hIp,hW',hz,hGp]
    have hjZ : (j:ℝ)=(k:ℝ)+1 := by
      dsimp only [M,mass,Mplus] at hMZ
      rw [hrZ,hH,hD,hdZ] at hMZ
      linarith only [hMZ,hk]
    exact ⟨hrZ,hH,hD,ha,hq,by exact_mod_cast hjZ⟩

private theorem theta_parities (n : ℕ) (hn : 23 ≤ n) :
    (n%2=0 → theta n=thetaEven (6*(n:ℝ))) ∧
    (n%2≠0 → theta n=thetaOdd (6*(n:ℝ))) := by
  have hnR : (23:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := by linarith only [hnR]
  have hn1 : 35*(n:ℝ)+1 ≠ 0 := by linarith only [hnR]
  constructor
  · intro he
    simp only [theta,he,if_true,thetaEven]
    field_simp [hn0]
    <;> ring
  · intro ho
    simp only [theta,ho,if_false,thetaOdd]
    field_simp [hn1]
    <;> ring

/-- The central scalar value is computed from the exact parity-dependent
    integer multiplicity; actual APPT attainment is a separate theorem. -/
theorem central_gap_zero (n : ℕ) (hn : 23 ≤ n) :
    gap (6*(n:ℝ)) (centralIndex n:ℝ) (theta n) (2/5) 0 0 0 0=0 := by
  have hnR : (23:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := by linarith only [hnR]
  have hn1 : 35*(n:ℝ)+1 ≠ 0 := by linarith only [hnR]
  by_cases he : n%2=0
  · have hj : 2*centralIndex n=5*n := by dsimp [centralIndex]; omega
    have hjR : 2*(centralIndex n:ℝ)=5*(n:ℝ) := by exact_mod_cast hj
    dsimp [gap,energy,mass,W,theta]
    simp only [he,if_true]
    field_simp [hn0]
    <;> nlinarith only [hjR]
  · have hmod : n%2=1 := by omega
    have hj : 2*centralIndex n=5*n+1 := by dsimp [centralIndex]; omega
    have hjR : 2*(centralIndex n:ℝ)=5*(n:ℝ)+1 := by exact_mod_cast hj
    have hj' : (centralIndex n:ℝ)=(5*(n:ℝ)+1)/2 := by linarith only [hjR]
    dsimp [gap,energy,mass,W,theta]
    simp only [he,if_false]
    rw [hj']
    field_simp [hn1]
    <;> ring

/-- Full all-n scalar theorem. All plateau indices in the actual interval
    remain quantified. This does not extract the physical hypotheses,
    transfer concentration, or prove literal APPT attainment. -/
theorem concentrated_scalar (n j : ℕ) (hn : 23 ≤ n)
    (hjl : 15 ≤ j) (hju : j ≤ 6*n-21) (r H D a q : ℝ)
    (h : PhysicalScalarHyp r H D a q) :
    0 < mass (6*(n:ℝ)) (j:ℝ) r H D ∧
    energy (6*(n:ℝ)) (j:ℝ) r H D a q ≤
      theta n*(mass (6*(n:ℝ)) (j:ℝ) r H D)^2 ∧
    (energy (6*(n:ℝ)) (j:ℝ) r H D a q =
      theta n*(mass (6*(n:ℝ)) (j:ℝ) r H D)^2 ↔
      r=2/5 ∧ H=0 ∧ D=0 ∧ a=0 ∧ q=0 ∧ j=centralIndex n) := by
  let N : ℝ := 6*(n:ℝ)
  have hnR : (23:ℝ) ≤ n := by exact_mod_cast hn
  have hN : 138 ≤ N := by dsimp [N]; linarith only [hnR]
  have hjR : (15:ℝ) ≤ j := by exact_mod_cast hjl
  have hNp : 0 < N := by linarith only [hN]
  obtain ⟨he,ho⟩ := theta_parities n hn
  have htheta : 0 < theta n := by
    by_cases hem : n%2=0
    · rw [he hem]; unfold thetaEven; positivity
    · rw [ho hem]; unfold thetaOdd; positivity
  have hM := mass_pos N (j:ℝ) r H D a q h hN hjR
  have hsc := square_completion N (j:ℝ) (theta n) r H D a q (ne_of_gt htheta)
  have hgap : 0 ≤ gap N (j:ℝ) (theta n) r H D a q ∧
      (gap N (j:ℝ) (theta n) r H D a q=0 →
        r=2/5 ∧ H=0 ∧ D=0 ∧ a=0 ∧ q=0 ∧ j=centralIndex n) := by
    have strict_of_W : W r H D a q < T N (theta n) r →
        0 < gap N (j:ℝ) (theta n) r H D a q := by
      intro hW
      have hp := mul_nonneg htheta.le
        (sq_nonneg (mass N (j:ℝ) r H D-(2+r)/(2*theta n)))
      linarith only [hsc,hp,hW]
    by_cases hlow : r ≤ 1/12
    · have hstrict : 0 < gap N (j:ℝ) (theta n) r H D a q := by
        by_cases h23 : n=23
        · subst n
          norm_num [N,theta]
          simpa [th23] using n23_low_strict (j:ℝ) r H D a q h hjR hlow
        by_cases h24 : n=24
        · subst n
          norm_num [N,theta]
          simpa using n24_low_strict (j:ℝ) r H D a q h hjR hlow
        have hn25 : 25 ≤ n := by omega
        have hn25R : (25:ℝ) ≤ n := by exact_mod_cast hn25
        have hN150 : 150 ≤ N := by dsimp [N]; linarith only [hn25R]
        have hprop := low_threshold_propagation N r hN150 h.r_nonneg hlow
        have hW := (low_W_le r H D a q h hlow).1
        apply strict_of_W
        by_cases hem : n%2=0
        · rw [he hem]; exact hW.trans_lt hprop.1
        · rw [ho hem]; exact hW.trans_lt hprop.2
      exact ⟨hstrict.le,fun hz => by linarith only [hz,hstrict]⟩
    by_cases hmid : r ≤ 79/200
    · have hW := base_strict r H D a q h (le_of_lt (lt_of_not_ge hlow)) hmid
      have hprop : T138 r ≤ T N (theta n) r := by
        by_cases hem : n%2=0
        · rw [he hem]; exact T_even_ge_base N r hN h.r_nonneg h.r_le
        · rw [ho hem]; exact T_odd_ge_base N r hN h.r_nonneg h.r_le
      have hstrict := strict_of_W (hW.trans_le hprop)
      exact ⟨hstrict.le,fun hz => by linarith only [hz,hstrict]⟩
    have hhigh : 79/200 ≤ r := le_of_lt (lt_of_not_ge hmid)
    by_cases hem : n%2=0
    · have hn24 : 24 ≤ n := by omega
      have hn24R : (24:ℝ) ≤ n := by exact_mod_cast hn24
      have hN144 : 144 ≤ N := by dsimp [N]; linarith only [hn24R]
      have hdelta := even_high_gap N (j:ℝ) r H D a q h hN144 (by linarith only [hhigh])
      rw [← he hem] at hdelta
      have hd0 : 0 ≤ 2-5*r := by linarith only [h.r_le]
      refine ⟨by linarith only [hdelta,hd0],?_⟩
      intro hz
      have hrZ : r=2/5 := by linarith only [hdelta,hz,hd0]
      obtain ⟨hH,hD,ha,hq,_⟩ := endpoint_zero r H D a q h hrZ
      have hT : T N (theta n) (2/5)=0 := by
        rw [he hem,T_even N (2/5) (by linarith only [hN])]
        norm_num [kappa]
      have hcenter : (2+(2/5:ℝ))/(2*theta n)=7*N/6 := by
        rw [he hem]; dsimp [thetaEven]; field_simp; ring
      rw [hrZ,hH,hD,ha,hq,hT,hcenter] at hsc
      have hz0 := hz
      rw [hrZ,hH,hD,ha,hq] at hz0
      norm_num [W] at hsc
      have hjC : (j:ℝ)=5*N/12 := by
        have hsq : (mass N (j:ℝ) (2/5) 0 0-7*N/6)^2=0 := by
          nlinarith only [hsc,hz0,htheta,sq_nonneg (mass N (j:ℝ) (2/5) 0 0-7*N/6)]
        have hmZ := sq_eq_zero_iff.mp hsq
        dsimp only [mass] at hmZ
        linarith only [hmZ]
      have hjEq : 2*j=5*n := by
        have hrEq : (2:ℝ)*(j:ℝ)=5*(n:ℝ) := by dsimp [N] at hjC; linarith only [hjC]
        exact_mod_cast hrEq
      exact ⟨hrZ,hH,hD,ha,hq,by dsimp [centralIndex]; omega⟩
    · rw [ho hem] at hsc ⊢
      by_cases hd : 3/N^2 ≤ 2-5*r
      · have hW := odd_high_continuous N r H D a q h hN hhigh hd
        have hp := mul_nonneg (show 0 ≤ thetaOdd N by unfold thetaOdd; positivity)
          (sq_nonneg (mass N (j:ℝ) r H D-(2+r)/(2*thetaOdd N)))
        have hstrict : 0 < gap N (j:ℝ) (thetaOdd N) r H D a q := by
          linarith only [hsc,hp,hW]
        exact ⟨hstrict.le,fun hz => by linarith only [hz,hstrict]⟩
      · let k : ℕ := 5*n/2
        have hmod : n%2=1 := by omega
        have hki : 2*k+1=5*n := by dsimp [k]; omega
        have hkiR : (2:ℝ)*(k:ℝ)+1=5*(n:ℝ) := by exact_mod_cast hki
        have hk : ((k:ℤ):ℝ)=(5*N-6)/12 := by
          norm_cast
          dsimp [N]
          linarith only [hkiR]
        have hh := odd_high_integer N r H D a q (j:ℤ) (k:ℤ) h hN hhigh
          (le_of_lt (lt_of_not_ge hd)) hk
        norm_cast at hh
        refine ⟨hh.1,?_⟩
        intro hz
        obtain ⟨hrZ,hH,hD,ha,hq,hjK⟩ := hh.2 hz
        exact ⟨hrZ,hH,hD,ha,hq,by dsimp [centralIndex]; omega⟩
  refine ⟨hM,?_,?_⟩
  · dsimp only [gap] at hgap
    linarith only [hgap.1]
  · constructor
    · intro heq
      exact hgap.2 (by dsimp [gap]; linarith only [heq])
    · rintro ⟨hrZ,hH,hD,ha,hq,hjZ⟩
      subst r; subst H; subst D; subst a; subst q; subst j
      have hz := central_gap_zero n hn
      dsimp only [gap] at hz
      linarith only [hz]

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowAllNScalar
