/- GID: D5/S3/Weil/ZetaBridge/ActualReciprocalEnclosure
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualReciprocalEnclosure
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: Full actual-symbol infinite reciprocal enclosure with the explicit cutoff-only arithmetic allowance 336. -/

import D5.S3.Analytic.PolynomialReciprocalBounds
import D5.S3.Weil.ZetaBridge.PrimeSymbolResonance
import D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
import D5.S3.Weil.ZetaBridge.ActualPrimePhaseBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open Polynomial MeasureTheory Set Filter
open scoped Topology BigOperators Interval ComplexConjugate
namespace D5.S3.Weil.ZetaBridge.ActualReciprocalEnclosure
open D5.S3.Analytic.SignedReciprocalQuadrature
open D5.S3.Analytic.PolynomialReciprocalBounds
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
open D5.S3.Weil.ZetaBridge.PrimeSymbolResonance
open D5.S3.Weil.ZetaBridge.ActualFullSymbolTail

/-- The explicit complete Gamma/pole witness, before coefficients and N. -/
def smoothK (c : ℕ) : ℝ := explicitSmoothK c

private lemma smoothK_spec {c : ℕ} (hc : 2 ≤ c) :
    0 < smoothK c ∧ ∀ m : ℕ, 0 < m →
      |(m:ℝ)^2*smoothWeight c m-Real.pi/4| ≤ smoothK c/(m:ℝ) := by
  exact explicitSmoothK_spec c hc

def amplitude (c : ℕ) : ℝ := ∑ q ∈ primeIndices c, primeWeight q

def delta (c m : ℕ) : ℝ := (m:ℝ)^2*smoothWeight c m-Real.pi/4

def baseAllowance (c : ℕ) : ℝ :=
  4+4*primeFirstMoment c/Real.sqrt (mean c)+4*offset c/mean c

/-- Exactly section 3.1, using the explicit proved full-asymptotic witness. -/
def U (c : ℕ) : ℝ := baseAllowance c +
  5*smoothK c*max 1 ((1+2*amplitude c+smoothK c)/mean c)

def functionEnergy (c : ℕ) (F G : ℂ[X]) : ℝ := energy F+mean c*energy G

def baseTerm (c N : ℕ) (F G : ℂ[X]) (j : ℕ) : ℝ :=
  let m := N+j+1
  ‖value F ((N:ℝ)/m) + (primeSymbol c (m:ℤ):ℂ)*value G ((N:ℝ)/m)‖^2/(m:ℝ)^2

def fullTerm (c N : ℕ) (F G : ℂ[X]) (j : ℕ) : ℝ :=
  let m := N+j+1
  ‖value F ((N:ℝ)/m) + ((primeSymbol c (m:ℤ)+delta c m:ℝ):ℂ)*value G ((N:ℝ)/m)‖^2/(m:ℝ)^2

private lemma firstMoment_nonneg (c : ℕ) : 0 ≤ primeFirstMoment c := by
  unfold primeFirstMoment
  exact Finset.sum_nonneg (fun _ _ => div_nonneg (by positivity) (norm_nonneg _))
private lemma primeWeight_nonneg (q : ℕ) : 0 ≤ primeWeight q :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
private lemma amplitude_nonneg (c : ℕ) : 0 ≤ amplitude c :=
  Finset.sum_nonneg (fun q _ => primeWeight_nonneg q)
private lemma primeSymbol_abs_le (c : ℕ) (m : ℤ) : |primeSymbol c m| ≤ amplitude c := by
  unfold primeSymbol amplitude
  calc
    _ ≤ ∑ q ∈ primeIndices c, |primeWeight q * Real.sin (2*Real.pi*(m:ℝ)*theta c q)| :=
      by
        simpa only [Real.norm_eq_abs] using
          (norm_sum_le (primeIndices c)
            (fun q => primeWeight q*Real.sin (2*Real.pi*(m:ℝ)*theta c q)))
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q _
      rw [abs_mul,abs_of_nonneg (primeWeight_nonneg q)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (Real.abs_sin_le_one _) (primeWeight_nonneg q)

private lemma mean_pos {c : ℕ} (hc : 3 ≤ c) : 0 < mean c := by
  have hl : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  exact (div_pos (sq_pos_of_pos hl) (by norm_num)).trans_le (prime_symbol_mean_lower_bound hc)

lemma functionEnergy_integral (c : ℕ) (F G : ℂ[X]) :
    functionEnergy c F G = ∫ t in (0:ℝ)..1, (‖value F t‖^2+mean c*‖value G t‖^2) := by
  have hiF : IntervalIntegrable (fun t : ℝ => ‖value F t‖^2) volume 0 1 :=
    ((value_continuous F).norm.pow 2).intervalIntegrable 0 1
  have hiG : IntervalIntegrable (fun t : ℝ => mean c*‖value G t‖^2) volume 0 1 :=
    (continuous_const.mul ((value_continuous G).norm.pow 2)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hiF hiG, intervalIntegral.integral_const_mul]
  rfl

lemma norm_square_real_add (f g : ℂ) (p : ℝ) :
    ‖f+(p:ℂ)*g‖^2 = ‖f‖^2+2*p*(f*conj g).re+p^2*‖g‖^2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re,Complex.conj_im]
  ring

private lemma centered_prefix {c : ℕ} (hc : 2 ≤ c) (N k : ℕ) :
    |∑ j ∈ Finset.range k, (primeSymbol c ((N+j+1:ℕ):ℤ)^2-mean c)| ≤ offset c := by
  have h := prime_symbol_exact_block hc ((N:ℤ)+1) k
  have he (j : ℕ) : (N:ℤ)+1+(j:ℤ) = ((N+j+1:ℕ):ℤ) := by push_cast; ring
  simpa only [he,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] using h

private lemma first_prefix {c : ℕ} (hc : 2 ≤ c) (N k : ℕ) :
    |∑ j ∈ Finset.range k, primeSymbol c ((N+j+1:ℕ):ℤ)| ≤ primeFirstMoment c := by
  have he (j : ℕ) : (N:ℤ)+1+(j:ℤ) = ((N+j+1:ℕ):ℤ) := by push_cast; ring
  simpa only [he] using prime_first_moment_block hc ((N:ℤ)+1) k

private lemma energy_young {c : ℕ} (hc : 3 ≤ c) (F G : ℂ[X]) :
    2*Real.sqrt (mean c)*(ltwo F*ltwo G) ≤ functionEnergy c F G := by
  have hm := Real.sq_sqrt ((mean_pos hc).le)
  have hF := ltwo_sq F
  have hG := ltwo_sq G
  have hs := sq_nonneg (ltwo F-Real.sqrt (mean c)*ltwo G)
  have he : (Real.sqrt (mean c)*ltwo G)^2 = mean c*energy G := by
    rw [mul_pow,hm,hG]
  unfold functionEnergy
  nlinarith only [hs,hF,he]

/-- The square with delta omitted: its second-moment error stays signed. -/
theorem actual_prime_enclosure {c d N : ℕ} (hc : 3 ≤ c) (hd : 1 ≤ d) (hN : 0 < N)
    (F G : ℂ[X]) (hF : F.natDegree < d) (hG : G.natDegree < d) :
    Summable (baseTerm c N F G) ∧
    |(N:ℝ)*(∑' j : ℕ, baseTerm c N F G j)-functionEnergy c F G| ≤
      (d:ℝ)^2/(N:ℝ)*baseAllowance c*functionEnergy c F G := by
  have hc2 : 2 ≤ c := by omega
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hm := mean_pos hc
  have hs := Real.sqrt_pos.2 hm
  have hD1 := firstMoment_nonneg c
  have hD2 := offset_nonneg c
  let p : ℕ → ℝ := fun j => primeSymbol c ((N+j+1:ℕ):ℤ)
  let z : ℕ → ℝ := fun j => p j^2-mean c
  let qF : ℕ → ℝ := fun j => weight N (mixed F F) (N+j+1:ℕ)
  let qG : ℕ → ℝ := fun j => weight N (mixed G G) (N+j+1:ℕ)
  let qP : ℕ → ℝ := fun j => p j*weight N (mixed F G) (N+j+1:ℕ)
  let qZ : ℕ → ℝ := fun j => z j*weight N (mixed G G) (N+j+1:ℕ)
  have hsf : Summable qF := sample_summable hN (mixed_continuous F F)
  have hsg : Summable qG := sample_summable hN (mixed_continuous G G)
  have hp := polynomial_signed_weighted hd hN F G hF hG hD1 (first_prefix hc2 N)
  have hz := polynomial_signed_weighted hd hN G G hG hG hD2 (centered_prefix hc2 N)
  change Summable qP ∧ _ at hp
  change Summable qZ ∧ _ at hz
  have hid (j : ℕ) : baseTerm c N F G j = qF j+mean c*qG j+2*qP j+qZ j := by
    dsimp only [baseTerm,qF,qG,qP,qZ,p,z,weight]
    rw [norm_square_real_add,mixed_self,mixed_self]
    unfold mixed
    ring
  have hsum : Summable (baseTerm c N F G) :=
    (((hsf.add (hsg.mul_left (mean c))).add (hp.1.mul_left 2)).add hz.1).congr (fun j => (hid j).symm)
  have hts : (∑' j : ℕ, baseTerm c N F G j) =
      tailEnergy N F+mean c*tailEnergy N G+2*(∑' j : ℕ,qP j)+(∑' j : ℕ,qZ j) := by
    simp_rw [hid]
    rw [((hsf.add (hsg.mul_left (mean c))).add (hp.1.mul_left 2)).tsum_add hz.1,
      (hsf.add (hsg.mul_left (mean c))).tsum_add (hp.1.mul_left 2),
      hsf.tsum_add (hsg.mul_left (mean c)), hsg.tsum_mul_left, hp.1.tsum_mul_left]
    simp only [qF, qG, weight, mixed_self, tailEnergy]
  have hqF := polynomial_quadrature hd hN F hF
  have hqG := polynomial_quadrature hd hN G hG
  have hmain : |(N:ℝ)*(tailEnergy N F+mean c*tailEnergy N G)-functionEnergy c F G| ≤
      4*(d:ℝ)^2/(N:ℝ)*functionEnergy c F G := by
    have he : (N:ℝ)*(tailEnergy N F+mean c*tailEnergy N G)-functionEnergy c F G =
        ((N:ℝ)*tailEnergy N F-energy F)+mean c*((N:ℝ)*tailEnergy N G-energy G) := by
      unfold functionEnergy; ring
    rw [he]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul,abs_of_pos hm]
    calc
      _ ≤ 4*(d:ℝ)^2/(N:ℝ)*energy F + mean c*(4*(d:ℝ)^2/(N:ℝ)*energy G) :=
        add_le_add hqF (mul_le_mul_of_nonneg_left hqG hm.le)
      _ = _ := by unfold functionEnergy; ring
  have heJ := energy_young hc F G
  have heG : mean c*energy G ≤ functionEnergy c F G := by
    unfold functionEnergy; linarith [energy_nonneg F]
  have hcross : 2*(4*(d:ℝ)^2*primeFirstMoment c/(N:ℝ)*(ltwo F*ltwo G)) ≤
      (d:ℝ)^2/(N:ℝ)*(4*primeFirstMoment c/Real.sqrt (mean c))*functionEnergy c F G := by
    calc
      _ = ((d:ℝ)^2/(N:ℝ)*(4*primeFirstMoment c/Real.sqrt (mean c))) *
          (2*Real.sqrt (mean c)*(ltwo F*ltwo G)) := by field_simp [hNR.ne',hs.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left heJ (by positivity)
  have hsecond : 4*(d:ℝ)^2*offset c/(N:ℝ)*(ltwo G*ltwo G) ≤
      (d:ℝ)^2/(N:ℝ)*(4*offset c/mean c)*functionEnergy c F G := by
    calc
      _ = ((d:ℝ)^2/(N:ℝ)*(4*offset c/mean c))*(mean c*energy G) := by
        have hGG : ltwo G*ltwo G = energy G := by nlinarith only [ltwo_sq G]
        rw [hGG]
        field_simp [hNR.ne',hm.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left heG (by positivity)
  refine ⟨hsum, ?_⟩
  rw [hts]
  have htri : |(N:ℝ)*(tailEnergy N F+mean c*tailEnergy N G+2*(∑' j,qP j)+(∑' j,qZ j))-
      functionEnergy c F G| ≤
      |(N:ℝ)*(tailEnergy N F+mean c*tailEnergy N G)-functionEnergy c F G|+
        2*|(N:ℝ)*(∑' j,qP j)|+|(N:ℝ)*(∑' j,qZ j)| := by
    have he : (N:ℝ)*(tailEnergy N F+mean c*tailEnergy N G+2*(∑' j,qP j)+(∑' j,qZ j))-
        functionEnergy c F G =
      ((N:ℝ)*(tailEnergy N F+mean c*tailEnergy N G)-functionEnergy c F G)+
        2*((N:ℝ)*(∑' j,qP j))+(N:ℝ)*(∑' j,qZ j) := by ring
    rw [he]
    refine (abs_add_le _ _).trans ?_
    have hi := abs_add_le
      ((N:ℝ)*(tailEnergy N F+mean c*tailEnergy N G)-functionEnergy c F G)
      (2*((N:ℝ)*(∑' j,qP j)))
    have hj := add_le_add hi (le_refl |(N:ℝ)*(∑' j,qZ j)|)
    simpa only [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] using hj
  have ht := htri.trans (add_le_add
    (add_le_add hmain (mul_le_mul_of_nonneg_left hp.2 (by norm_num))) hz.2)
  refine ht.trans ?_
  calc
    _ ≤ 4*(d:ℝ)^2/(N:ℝ)*functionEnergy c F G+
        ((d:ℝ)^2/(N:ℝ)*(4*primeFirstMoment c/Real.sqrt (mean c))*functionEnergy c F G+
        (d:ℝ)^2/(N:ℝ)*(4*offset c/mean c)*functionEnergy c F G) := by
      simpa only [add_assoc] using
        add_le_add (le_refl (4*(d:ℝ)^2/(N:ℝ)*functionEnergy c F G))
          (add_le_add hcross hsecond)
    _ = _ := by unfold baseAllowance; ring

/-- The actual smooth mass is related to the original full arithmetic symbol. -/
lemma actual_symbol_split {c m : ℕ} (hm : 0 < m) :
    arithmeticBoundarySymbol c (m:ℤ) = -(Real.pi/4+primeSymbol c (m:ℤ)+delta c m) := by
  rw [arithmetic_symbol_smooth_split c hm, owner_prime_sum_eq]
  unfold delta
  ring

private lemma square_delta_bound (f g : ℂ) (p e A q K : ℝ)
    (hA : |p| ≤ A) (he : |e| ≤ q) (heK : |e| ≤ K) (hq : 0 ≤ q) :
    |‖f+((p+e:ℝ):ℂ)*g‖^2-‖f+(p:ℂ)*g‖^2| ≤
      q*(‖f‖^2+(1+2*A+K)*‖g‖^2) := by
  have ha : 0 ≤ A := (abs_nonneg p).trans hA
  have hK : 0 ≤ K := (abs_nonneg e).trans heK
  have hm : 2*|(f*conj g).re| ≤ ‖f‖^2+‖g‖^2 := by
    have hc : |(f*conj g).re| ≤ ‖f‖*‖g‖ := by
      simpa only [norm_mul,Complex.norm_conj] using Complex.abs_re_le_norm (f*conj g)
    nlinarith [sq_nonneg (‖f‖-‖g‖)]
  rw [norm_square_real_add,norm_square_real_add]
  have hid : (‖f‖^2+2*(p+e)*(f*conj g).re+(p+e)^2*‖g‖^2)-
      (‖f‖^2+2*p*(f*conj g).re+p^2*‖g‖^2) =
      2*e*(f*conj g).re+(2*p*e+e^2)*‖g‖^2 := by ring
  rw [hid]
  calc
    _ ≤ |2*e*(f*conj g).re|+|(2*p*e+e^2)*‖g‖^2| := abs_add_le _ _
    _ = 2*|e| * |(f*conj g).re|+|2*p*e+e^2| * ‖g‖^2 := by
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
        abs_of_nonneg (sq_nonneg ‖g‖)]
    _ ≤ |e| * (‖f‖^2+‖g‖^2)+(2*A*|e| +|e| ^2)*‖g‖^2 := by
      apply add_le_add
      · nlinarith only [mul_le_mul_of_nonneg_left hm (abs_nonneg e)]
      · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        calc
          |2*p*e+e^2| ≤ |2*p*e|+|e^2| := abs_add_le _ _
          _ = 2*|p| * |e| +|e| ^2 := by
            simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
          _ ≤ 2*A*|e| +|e| ^2 := by gcongr
    _ ≤ q*(‖f‖^2+(1+2*A+K)*‖g‖^2) := by
      have he2 : |e| ^2 ≤ q*K := by
        simpa only [pow_two] using mul_le_mul he heK (abs_nonneg e) hq
      have h1 := mul_le_mul_of_nonneg_right he (sq_nonneg ‖f‖)
      have h2 := mul_le_mul_of_nonneg_right he (sq_nonneg ‖g‖)
      have h3 := mul_le_mul_of_nonneg_left he (show 0 ≤ 2*A*‖g‖^2 by positivity)
      have h4 := mul_le_mul_of_nonneg_right he2 (sq_nonneg ‖g‖)
      nlinarith only [h1,h2,h3,h4]

private lemma delta_tail_bound {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N) (j : ℕ) :
    |delta c (N+j+1)| ≤ smoothK c/(N:ℝ) ∧ |delta c (N+j+1)| ≤ smoothK c := by
  have hK := smoothK_spec hc
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hm : (N:ℝ) ≤ ((N+j+1:ℕ):ℝ) := by exact_mod_cast (show N ≤ N+j+1 by omega)
  have hb := hK.2 (N+j+1) (by omega)
  change |delta c (N+j+1)| ≤ _ at hb
  have hd := hb.trans (div_le_div_of_nonneg_left hK.1.le (by positivity) hm)
  exact ⟨hd,hd.trans ((div_le_iff₀ (by positivity : (0:ℝ)<N)).2 (by nlinarith [hK.1]))⟩

/-- Full c≥3 enclosure (3.2), including all resonances, powers and Gamma/pole terms. -/
theorem actual_full_symbol_enclosure {c d N : ℕ} (hc : 3 ≤ c) (hd : 1 ≤ d)
    (hN : d^2 ≤ N) (F G : ℂ[X]) (hF : F.natDegree < d) (hG : G.natDegree < d) :
    Summable (fullTerm c N F G) ∧
    |(N:ℝ)*(∑' j : ℕ, fullTerm c N F G j)-
      (∫ t in (0:ℝ)..1, (‖value F t‖^2+mean c*‖value G t‖^2))| ≤
      ((d:ℝ)^2*U c/(N:ℝ))*
        (∫ t in (0:ℝ)..1, (‖value F t‖^2+mean c*‖value G t‖^2)) := by
  have hdp : 0 < d := by omega
  have hNp : 0 < N := lt_of_lt_of_le (pow_pos hdp 2) hN
  have hNR : (0:ℝ) < N := by exact_mod_cast hNp
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdim : (d:ℝ)^2 ≤ N := by exact_mod_cast hN
  have hd2 : (1:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have hc2 : 2 ≤ c := by omega
  have hm := mean_pos hc
  have hK := smoothK_spec hc2
  have hK0 : 0 ≤ smoothK c := hK.1.le
  have hA := amplitude_nonneg c
  let L : ℝ := 1+2*amplitude c+smoothK c
  let M : ℝ := max 1 (L/mean c)
  let q : ℝ := smoothK c/(N:ℝ)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hM : 0 ≤ M := le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_left _ _)
  have hq : 0 ≤ q := div_nonneg hK.1.le hNR.le
  let sf : ℕ → ℝ := fun j => ‖value F ((N:ℝ)/(N+j+1:ℕ))‖^2/((N+j+1:ℕ):ℝ)^2
  let sg : ℕ → ℝ := fun j => ‖value G ((N:ℝ)/(N+j+1:ℕ))‖^2/((N+j+1:ℕ):ℝ)^2
  let err : ℕ → ℝ := fun j => fullTerm c N F G j-baseTerm c N F G j
  let env : ℕ → ℝ := fun j => q*(sf j+L*sg j)
  have hsf := square_sample_summable hNp F
  have hsg := square_sample_summable hNp G
  change Summable sf at hsf
  change Summable sg at hsg
  have henv : Summable env := (hsf.add (hsg.mul_left L)).mul_left q
  have herr (j : ℕ) : |err j| ≤ env j := by
    have he := square_delta_bound
      (value F ((N:ℝ)/(N+j+1:ℕ))) (value G ((N:ℝ)/(N+j+1:ℕ)))
      (primeSymbol c ((N+j+1:ℕ):ℤ)) (delta c (N+j+1))
      (amplitude c) q (smoothK c) (primeSymbol_abs_le c _)
      (delta_tail_bound hc2 hNp j).1 (delta_tail_bound hc2 hNp j).2 hq
    dsimp only [err,fullTerm,baseTerm,env,sf,sg,L]
    rw [← sub_div,abs_div,abs_of_nonneg (sq_nonneg (((N+j+1:ℕ):ℝ)))]
    convert div_le_div_of_nonneg_right he (sq_nonneg (((N+j+1:ℕ):ℝ))) using 1 <;> ring
  have hserr : Summable err := henv.of_norm_bounded (fun j => by simpa only [Real.norm_eq_abs] using herr j)
  have hbase := actual_prime_enclosure hc hd hNp F G hF hG
  have hfull : Summable (fullTerm c N F G) :=
    (hserr.add hbase.1).congr (fun j => by dsimp [err]; ring)
  have herrsum : |(∑' j : ℕ,fullTerm c N F G j)-(∑' j : ℕ,baseTerm c N F G j)| ≤
      q*(tailEnergy N F+L*tailEnergy N G) := by
    rw [← hfull.tsum_sub hbase.1]
    calc
      _ ≤ ∑' j : ℕ, |err j| := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hserr.norm
      _ ≤ ∑' j : ℕ, env j := hserr.norm.tsum_le_tsum herr henv
      _ = _ := by
        dsimp only [env]
        rw [(hsf.add (hsg.mul_left L)).tsum_mul_left q,
          hsf.tsum_add (hsg.mul_left L),hsg.tsum_mul_left L]
        rfl
  have hquad (P : ℂ[X]) (hP : P.natDegree < d) : (N:ℝ)*tailEnergy N P ≤ 5*energy P := by
    have hu := (abs_le.mp (polynomial_quadrature hd hNp P hP)).2
    have hr : 4*(d:ℝ)^2/(N:ℝ) ≤ 4 := by apply (div_le_iff₀ hNR).2; nlinarith
    have hh := mul_le_mul_of_nonneg_right hr (energy_nonneg P)
    linarith
  have hmetric : energy F+L*energy G ≤ M*functionEnergy c F G := by
    have h1 : 1 ≤ M := le_max_left _ _
    have h2 : L ≤ M*mean c := (div_le_iff₀ hm).1 (le_max_right _ _)
    have ha := mul_le_mul_of_nonneg_right h1 (energy_nonneg F)
    have hb := mul_le_mul_of_nonneg_right h2 (energy_nonneg G)
    unfold functionEnergy
    nlinarith only [ha,hb]
  have hsmooth : |(N:ℝ)*((∑' j : ℕ,fullTerm c N F G j)-(∑' j : ℕ,baseTerm c N F G j))| ≤
      (d:ℝ)^2/(N:ℝ)*(5*smoothK c*M)*functionEnergy c F G := by
    rw [abs_mul,abs_of_pos hNR]
    calc
      _ ≤ (N:ℝ)*(q*(tailEnergy N F+L*tailEnergy N G)) :=
        mul_le_mul_of_nonneg_left herrsum hNR.le
      _ = q*((N:ℝ)*tailEnergy N F+L*((N:ℝ)*tailEnergy N G)) := by ring
      _ ≤ q*(5*energy F+L*(5*energy G)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hquad F hF)
          (mul_le_mul_of_nonneg_left (hquad G hG) hL)) hq
      _ = 5*q*(energy F+L*energy G) := by ring
      _ ≤ 5*q*(M*functionEnergy c F G) := mul_le_mul_of_nonneg_left hmetric (by positivity)
      _ ≤ _ := by
        have hI : 0 ≤ functionEnergy c F G := add_nonneg (energy_nonneg F) (mul_nonneg hm.le (energy_nonneg G))
        have hs := mul_le_mul_of_nonneg_right hd2
          (show 0 ≤ 5*smoothK c/(N:ℝ)*M*functionEnergy c F G by positivity)
        dsimp only [q]
        convert hs using 1 <;> ring
  refine ⟨hfull, ?_⟩
  rw [← functionEnergy_integral]
  have hid : (N:ℝ)*(∑' j : ℕ,fullTerm c N F G j)-functionEnergy c F G =
      (N:ℝ)*((∑' j : ℕ,fullTerm c N F G j)-(∑' j : ℕ,baseTerm c N F G j))+
      ((N:ℝ)*(∑' j : ℕ,baseTerm c N F G j)-functionEnergy c F G) := by ring
  rw [hid]
  refine (abs_add_le _ _).trans ((add_le_add hsmooth hbase.2).trans_eq ?_)
  dsimp only [U,M,L]
  ring

/- The arithmetic allowance uses the same actual suppliers as the full-symbol enclosure. -/

private lemma mean_ge_sixteenth {c : ℕ} (hc : 3 ≤ c) : (1:ℝ)/16 ≤ mean c := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
  have hlog : (1:ℝ)/2 ≤ Real.log (2:ℝ) := by
    norm_num at h
    exact h
  have hfloor := prime_symbol_mean_lower_bound hc
  have hs : (1:ℝ)/4 ≤ Real.log (2:ℝ)^2 := by
    nlinarith only [hlog,sq_nonneg (Real.log (2:ℝ)-1/2)]
  linarith only [hs,hfloor]

private lemma sqrt_mean_quarter {c : ℕ} (hc : 3 ≤ c) :
    (1:ℝ)/4 ≤ Real.sqrt (mean c) := by
  have he : Real.sqrt ((1:ℝ)/16) = (1:ℝ)/4 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have h := Real.sqrt_le_sqrt (mean_ge_sixteenth hc)
  rwa [he] at h

/-- Exact source allowance (3.1) satisfies (3.3), before F,G,d,N.
This theorem consumes the actual amplitude, actual D1 and D2, and the explicit
full Gamma/pole witness installed in smoothK. -/
theorem U_le_explicit336 {c : ℕ} (hc : 3 ≤ c) :
    U c ≤ 336*(c:ℝ)^2*(1+Real.log (c:ℝ))^3 := by
  let x : ℝ := c
  let s : ℝ := Real.sqrt (c:ℝ)
  let L : ℝ := logLength c
  have hx : 3 ≤ x := by change (3:ℝ) ≤ (c:ℝ); exact_mod_cast hc
  have hx0 : 0 < x := by linarith
  have hL : 0 < L := logLength_pos (show 2≤c by omega)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2 = x := Real.sq_sqrt hx0.le
  have hs1 : 1 ≤ s := by
    by_contra h
    have hslt : s < 1 := lt_of_not_ge h
    have hprod := mul_nonneg (show 0 ≤ 1-s by linarith)
      (show 0 ≤ 1+s by linarith)
    nlinarith only [hprod,hs2,hx]
  have hsx : s ≤ x := by
    have hh := mul_nonneg hs0 (sub_nonneg.mpr hs1)
    nlinarith only [hh,hs2]
  have hA0 := amplitude_nonneg c
  have hK0 := (smoothK_spec (show 2≤c by omega)).1.le
  have hD10 := firstMoment_nonneg c
  have hD20 := offset_nonneg c
  have hm : (1:ℝ)/16 ≤ mean c := mean_ge_sixteenth hc
  have hm0 : 0 < mean c := by linarith
  have hsm := sqrt_mean_quarter hc
  have hsm0 : 0 < Real.sqrt (mean c) := by linarith
  have hA : amplitude c ≤ 2*s*L := ActualPrimePhaseBounds.amplitude_le hc
  have hK : smoothK c ≤ s*L := by
    simpa only [smoothK] using explicitSmoothK_le hc
  have hD1 : primeFirstMoment c ≤ x*s*L^2 := ActualPrimePhaseBounds.firstMoment_le hc
  have hD2 : offset c ≤ x*(2*x+1)*L^3 := ActualPrimePhaseBounds.offset_le hc
  have hfirst : 4*primeFirstMoment c/Real.sqrt (mean c) ≤ 16*primeFirstMoment c := by
    apply (div_le_iff₀ hsm0).2
    nlinarith only [mul_le_mul_of_nonneg_left hsm (show 0≤16*primeFirstMoment c by positivity)]
  have hsecond : 4*offset c/mean c ≤ 64*offset c := by
    apply (div_le_iff₀ hm0).2
    nlinarith only [mul_le_mul_of_nonneg_left hm (show 0≤64*offset c by positivity)]
  have hnum : 1+2*amplitude c+smoothK c ≤ 1+5*s*L := by linarith only [hA,hK]
  have hmax : max 1 ((1+2*amplitude c+smoothK c)/mean c) ≤ 16*(1+5*s*L) := by
    apply max_le
    · have hh : 0 ≤ s*L := mul_nonneg hs0 hL.le
      nlinarith only [hh]
    · apply (div_le_iff₀ hm0).2
      have hh := mul_le_mul_of_nonneg_left hm
        (show 0 ≤ 16*(1+5*s*L) by positivity)
      nlinarith only [hh,hnum]
  have hmax0 : 0 ≤ max 1 ((1+2*amplitude c+smoothK c)/mean c) :=
    (by norm_num : (0:ℝ)≤1).trans (le_max_left _ _)
  have hsmooth : 5*smoothK c*max 1 ((1+2*amplitude c+smoothK c)/mean c) ≤
      80*s*L+400*x*L^2 := by
    calc
      _ = 5*(smoothK c*max 1 ((1+2*amplitude c+smoothK c)/mean c)) := by ring
      _ ≤ 5*((s*L)*(16*(1+5*s*L))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hK hmax hmax0 (by positivity)) (by norm_num)
      _ = 80*s*L+400*s^2*L^2 := by ring
      _ = _ := by rw [hs2]
  have hcoarse : U c ≤ 4+80*s*L+(16*x*s+400*x)*L^2+(128*x^2+64*x)*L^3 := by
    have hd1 := mul_le_mul_of_nonneg_left hD1 (by norm_num : (0:ℝ)≤16)
    have hd2 := mul_le_mul_of_nonneg_left hD2 (by norm_num : (0:ℝ)≤64)
    unfold U baseAllowance
    nlinarith only [hfirst,hsecond,hsmooth,hd1,hd2]
  -- The radical and cutoff obligations are discharged BEFORE polynomial absorption.
  have hx3 : 3*x ≤ x^2 := by
    have hh := mul_nonneg hx0.le (sub_nonneg.mpr hx)
    nlinarith only [hh]
  have hconst : 4 ≤ x^2 := by nlinarith only [hx,hx3]
  have hlinear : 80*s ≤ 27*x^2 := by nlinarith only [hsx,hx3,hx0.le]
  have hquadratic : 16*x*s+400*x ≤ 150*x^2 := by
    have hh := mul_le_mul_of_nonneg_left hsx hx0.le
    nlinarith only [hh,hx3,hx0.le]
  have hcubic : 128*x^2+64*x ≤ 150*x^2 := by
    nlinarith only [hx3,hx0.le]
  have hpoly : U c ≤ x^2*(1+27*L+150*L^2+150*L^3) := by
    have h1 := mul_le_mul_of_nonneg_right hlinear hL.le
    have h2 := mul_le_mul_of_nonneg_right hquadratic (sq_nonneg L)
    have h3 := mul_le_mul_of_nonneg_right hcubic (pow_nonneg hL.le 3)
    nlinarith only [hcoarse,hconst,h1,h2,h3]
  have hcertificate : 0 ≤ 336*(1+L)^3-(1+27*L+150*L^2+150*L^3) := by
    have hid : 336*(1+L)^3-(1+27*L+150*L^2+150*L^3) =
        335+981*L+858*L^2+186*L^3 := by ring
    rw [hid]
    positivity
  have hfinal := mul_nonneg (sq_nonneg x) hcertificate
  change U c ≤ 336*x^2*(1+L)^3
  nlinarith only [hpoly,hfinal]

/-- The uniform constant is consumed by the genuine full-symbol enclosure.
No coefficient is fixed before the cutoff-only bound above. -/
theorem actual_full_symbol_enclosure_explicit336 {c d N : ℕ} (hc : 3 ≤ c)
    (hd : 1 ≤ d) (hN : d^2 ≤ N) (F G : ℂ[X])
    (hF : F.natDegree < d) (hG : G.natDegree < d) :
    Summable (fullTerm c N F G) ∧
    |(N:ℝ)*(∑' j : ℕ, fullTerm c N F G j)-
      (∫ t in (0:ℝ)..1, (‖value F t‖^2+mean c*‖value G t‖^2))| ≤
      ((d:ℝ)^2*(336*(c:ℝ)^2*(1+Real.log (c:ℝ))^3)/(N:ℝ))*
        (∫ t in (0:ℝ)..1, (‖value F t‖^2+mean c*‖value G t‖^2)) := by
  obtain ⟨hs,hb⟩ := actual_full_symbol_enclosure hc hd hN F G hF hG
  refine ⟨hs,hb.trans ?_⟩
  have he : 0 ≤ ∫ t in (0:ℝ)..1, (‖value F t‖^2+mean c*‖value G t‖^2) := by
    rw [← functionEnergy_integral]
    exact add_nonneg (energy_nonneg F) (mul_nonneg (mean_pos hc).le (energy_nonneg G))
  apply mul_le_mul_of_nonneg_right _ he
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact mul_le_mul_of_nonneg_left (U_le_explicit336 hc) (sq_nonneg (d:ℝ))

end D5.S3.Weil.ZetaBridge.ActualReciprocalEnclosure
