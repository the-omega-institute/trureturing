/- GID: D5/S3/Analytic/Probability/NativeCommandLifetime
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/NativeCommandLifetime
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lifetime estimates for finite native commands with both height walls. -/
import Mathlib
import D5.S3.Zeros.Jensen.FactorialJensenKernelBound
import D5.S3.Observer.Hankel.PositiveGramianBalancing
import D5.S3.Arith.Lattices.Klartag.Walk.ChainDrift
import D5.S3.Quantum.Fibers.OriginalControlComposition
/-! Finite fair-sign native commands on a fixed two-wall cylinder. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ContDiff
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Analytic.Probability.NativeCommandLifetime
abbrev Triple := Fin 3 → ℝ
abbrev Covariance := Matrix (Fin 2) (Fin 2) ℝ
abbrev SignPair := Bool × Bool
private def sign (e : Bool) : ℝ := if e then 1 else -1
private def average (f : SignPair → ℝ) : ℝ := (f (false,false) + f (false,true) + f (true,false) + f (true,true)) / 4
private theorem average_nonneg (f : SignPair → ℝ) (hf : ∀ e, 0 ≤ f e) : 0 ≤ average f := by
  unfold average; linarith [hf (false,false),hf (false,true),hf (true,false),hf (true,true)]
private theorem average_mono (f g : SignPair → ℝ) (h : ∀ e, f e ≤ g e) : average f ≤ average g := by
  unfold average; linarith [h (false,false),h (false,true),h (true,false),h (true,true)]
private theorem average_const (c : ℝ) : average (fun _ => c) = c := by
  unfold average; ring
private theorem average_add (f g : SignPair → ℝ) : average (fun e => f e + g e) = average f + average g := by
  unfold average; ring
private theorem average_mul (c : ℝ) (f : SignPair → ℝ) : average (fun e => c * f e) = c * average f := by
  unfold average; ring
/-- Raw coefficients are evaluated on the real lift of the actual phase torus. -/
structure Model where
  r : ℝ
  l : ℝ
  u : ℝ
  r_pos : 0 < r
  lower_pos : 0 < l
  interval_nonempty : l < u
  upper_lt : u < r / 2
  source : Triple
  source_height : source 0 ∈ Ioo l u
  rho : Triple → ℝ
  A : Triple → Covariance
  neighbourhood : Set Triple
  open_neighbourhood : IsOpen neighbourhood
  contains_cylinder : ∀ q : Triple, q 0 ∈ Icc l u → q ∈ neighbourhood
  smooth_rho : ContDiffOn ℝ ∞ rho neighbourhood
  smooth_A : ∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun q => A q i j) neighbourhood
  positive_rho : ∀ q ∈ neighbourhood, 0 < rho q
  positive_A : ∀ q ∈ neighbourhood, (A q).PosDef
  periodic_rho : ∀ (q : Triple) (i j : ℤ), rho (q + ![0,(i : ℝ)*(2*Real.pi),(j : ℝ)*(2*Real.pi)]) = rho q
  periodic_A : ∀ (q : Triple) (i j : ℤ), A (q + ![0,(i : ℝ)*(2*Real.pi),(j : ℝ)*(2*Real.pi)]) = A q
/-- The two original horizontal vector fields in the real coordinate lift. -/
def horizontal (B : Model) (q : Triple) (i : Fin 2) : Triple := if i = 0 then ![1,0,0] else ![0,1/2,1/2-q 0/B.r]
/-- The density drift uses the derivatives of the raw density and covariance. -/
def drift (B : Model) (q : Triple) (j : Fin 2) : ℝ := (B.rho q)⁻¹ * ∑ i : Fin 2, fderiv ℝ (fun x => B.rho x * B.A x i j) q (horizontal B q i)
/-- The positive matrix square root, with no independent choice of covariance. -/
def sigma (B : Model) (q : Triple) : Covariance := D5.S3.Observer.Hankel.PositiveGramianBalancing.gramianRoot (B.A q)
/-- The original source map before taking the two actual period-2π classes. -/
def sourceMap (B : Model) (z : Triple) : Triple := ![B.source 0 + z 0, B.source 1 + z 1/2, B.source 2 + (1/2-B.source 0/B.r)*z 1-z 2/B.r]
/-- The ordinary chord integral has its quadratic chronological area term. -/
def chord (z : Triple) (v : Fin 2 → ℝ) (θ : ℝ) : Triple := ![z 0 + θ*v 0, z 1 + θ*v 1, z 2 + θ*z 0*v 1 + (θ^2/2)*v 0*v 1]
def increment (B : Model) (δ : ℝ) (z : Triple) (e : SignPair) : Fin 2 → ℝ := fun i => drift B (sourceMap B z) i * δ + Real.sqrt (2*δ) * (sigma B (sourceMap B z) i 0 * sign e.1 + sigma B (sourceMap B z) i 1 * sign e.2)
def next (B : Model) (δ : ℝ) (z : Triple) (e : SignPair) : Triple := chord z (increment B δ z e) 1
def Alive (B : Model) (z : Triple) : Prop := (sourceMap B z) 0 ∈ Ioo B.l B.u
/-- This fraction stops the affine height at its first wall. -/
def hitFraction (B : Model) (z : Triple) (v : Fin 2 → ℝ) : ℝ := if 0 < v 0 then min 1 ((B.u - (sourceMap B z) 0) / v 0)
  else if v 0 < 0 then min 1 ((B.l - (sourceMap B z) 0) / v 0)
  else 1
/-- A surviving finite prefix is followed by the original terminal upper-wall leg. -/
def lifetime (B : Model) (δ : ℝ) (z : Triple) : List SignPair → ℝ
  | [] => δ
  | e :: es =>
    if Alive B (next B δ z e) then δ + lifetime B δ (next B δ z e) es
    else δ * hitFraction B z (increment B δ z e)
/-- Survival of endpoint prefixes, with every sign pair receiving mass 1/4. -/
def survival (B : Model) (δ : ℝ) : ℕ → Triple → ℝ
  | 0, z => if Alive B z then 1 else 0
  | m+1, z => if Alive B z then
      average (fun e => survival B δ m (next B δ z e))
    else 0
private theorem next_height (B : Model) (δ : ℝ) (z : Triple) (e : SignPair) : (sourceMap B (next B δ z e)) 0 = (sourceMap B z) 0 + increment B δ z e 0 := by
  simp [sourceMap,next,chord]; ring
private theorem average_exp_sign (d x y : ℝ) : average (fun e => Real.exp (d + x*sign e.1+y*sign e.2)) = Real.exp d * Real.cosh x * Real.cosh y := by
  simp [average,sign,Real.exp_add,Real.exp_sub,Real.cosh_eq,Real.exp_neg]; ring
private theorem exp_step_lower (δ lam D a s t d : ℝ)
    (hδ : 0 ≤ δ) (hlam : 0 ≤ lam) (hD : 0 ≤ D)
    (hd : -D ≤ d) (ha : a ≤ s^2+t^2)
    (hgap : 2 ≤ lam^2*a-lam*D)
    (hsmall : lam^3*D*(s^2+t^2)*δ ≤ 1) :
    1 + δ ≤ average (fun e =>
      Real.exp (lam*(d*δ+Real.sqrt (2*δ)*(s*sign e.1+t*sign e.2)))) := by
  have hs : 1+(lam*Real.sqrt (2*δ)*s)^2/2 ≤ Real.cosh (lam*Real.sqrt (2*δ)*s) := by
    have h := D5.S3.Zeros.Jensen.FactorialJensenKernelBound.even_sum_le_cosh
      2 ((lam*Real.sqrt (2*δ)*s)^2) (sq_nonneg _)
    rw [Real.sqrt_sq_eq_abs,Real.cosh_abs] at h; norm_num [D5.S3.Zeros.Jensen.FactorialJensenKernelBound.evenFactorialSum, Fin.sum_univ_two] at h; simpa using h
  have ht : 1+(lam*Real.sqrt (2*δ)*t)^2/2 ≤ Real.cosh (lam*Real.sqrt (2*δ)*t) := by
    have h := D5.S3.Zeros.Jensen.FactorialJensenKernelBound.even_sum_le_cosh
      2 ((lam*Real.sqrt (2*δ)*t)^2) (sq_nonneg _)
    rw [Real.sqrt_sq_eq_abs,Real.cosh_abs] at h; norm_num [D5.S3.Zeros.Jensen.FactorialJensenKernelBound.evenFactorialSum, Fin.sum_univ_two] at h; simpa using h
  have hsq := Real.sq_sqrt (show 0 ≤ 2*δ by positivity); have hs' : (lam*Real.sqrt (2*δ)*s)^2/2 = lam^2*δ*s^2 := by
    rw [mul_pow,mul_pow,hsq]; ring
  have ht' : (lam*Real.sqrt (2*δ)*t)^2/2 = lam^2*δ*t^2 := by
    rw [mul_pow,mul_pow,hsq]; ring
  rw [hs'] at hs; rw [ht'] at ht; have hc : 1+lam^2*δ*(s^2+t^2) ≤ Real.cosh (lam*Real.sqrt (2*δ)*s) * Real.cosh (lam*Real.sqrt (2*δ)*t) := by
    have hmul := mul_le_mul hs ht (by positivity)
      (le_trans (by positivity) hs)
    have hp : 0 ≤ (lam^2*δ*s^2)*(lam^2*δ*t^2) := by positivity
    nlinarith
  have he : 1-lam*D*δ ≤ Real.exp (lam*d*δ) := by
    have h := Real.add_one_le_exp (lam*d*δ); have hprod : 0 ≤ lam*δ*(d+D) := mul_nonneg (by positivity) (by linarith); nlinarith
  have hmul := mul_le_mul_of_nonneg_right he
    (show 0 ≤ 1+lam^2*δ*(s^2+t^2) by positivity)
  have havg : average (fun e =>
        Real.exp (lam*(d*δ+Real.sqrt (2*δ)*(s*sign e.1+t*sign e.2)))) =
        Real.exp (lam*d*δ) * (Real.cosh (lam*Real.sqrt (2*δ)*s) * Real.cosh (lam*Real.sqrt (2*δ)*t)) := by
    convert average_exp_sign (lam*d*δ) (lam*Real.sqrt (2*δ)*s)
      (lam*Real.sqrt (2*δ)*t) using 1
    · congr 1
      funext e; congr 1; ring
    · ring
  rw [havg]; have hc' := mul_le_mul_of_nonneg_left hc (Real.exp_nonneg (lam*d*δ)); have hrem : lam^3*D*(s^2+t^2)*δ^2 ≤ δ := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall hδ]
  have hmain : 2*δ ≤ (lam^2*(s^2+t^2)-lam*D)*δ := by
    have h := mul_le_mul_of_nonneg_right hgap hδ; have h' := mul_le_mul_of_nonneg_left ha (sq_nonneg lam); nlinarith
  nlinarith
/-- The proof-side endpoint process stops after the first endpoint outside the interval. -/
def stoppedMean (B : Model) (δ : ℝ) (f : Triple → ℝ) : ℕ → Triple → ℝ
  | 0, z => f z
  | m+1, z => if Alive B z then
      average (fun e => stoppedMean B δ f m (next B δ z e))
    else f z
private theorem survival_dead (B : Model) (δ : ℝ) (m : ℕ) (z : Triple)
    (hz : ¬ Alive B z) : survival B δ m z = 0 := by
  cases m <;> simp [survival,hz]
private theorem survival_bounds (B : Model) (δ : ℝ) (m : ℕ) (z : Triple) : 0 ≤ survival B δ m z ∧ survival B δ m z ≤ 1 := by
  induction m generalizing z with
  | zero => simp [survival]; split <;> norm_num
  | succ m ih =>
    by_cases hz : Alive B z
    · rw [survival,if_pos hz]
      exact ⟨average_nonneg _ (fun e => (ih _).1), (average_mono _ (fun _ => 1) (fun e => (ih _).2)).trans_eq (average_const 1)⟩
    · simp [survival,hz]
private theorem survival_antitone (B : Model) (δ : ℝ) (z : Triple) : Antitone (fun m => survival B δ m z) := by
  apply antitone_nat_of_succ_le; intro m; induction m generalizing z with
  | zero =>
    by_cases hz : Alive B z
    · simpa [survival,hz] using (survival_bounds B δ 1 z).2
    · simp [survival,hz]
  | succ m ih =>
    by_cases hz : Alive B z
    · simpa only [survival,if_pos hz] using
        average_mono _ _ (fun e => ih (next B δ z e))
    · simp [survival,hz]
private theorem stopped_drift (B : Model) (δ c : ℝ) (f : Triple → ℝ)
    (hstep : ∀ z, Alive B z → f z + c ≤ average (fun e => f (next B δ z e)))
    (m : ℕ) (z : Triple) :
    stoppedMean B δ f m z + c * survival B δ m z ≤ stoppedMean B δ f (m+1) z := by
  induction m generalizing z with
  | zero =>
    by_cases hz : Alive B z
    · simpa [stoppedMean,survival,hz] using hstep z hz
    · simp [stoppedMean,survival,hz]
  | succ m ih =>
    by_cases hz : Alive B z
    · simp only [stoppedMean,survival,if_pos hz]
      rw [←average_mul,←average_add]; exact average_mono _ _ (fun e => ih _)
    · simp [stoppedMean,survival,hz]
private theorem stopped_cap (B : Model) (δ cap : ℝ) (f : Triple → ℝ)
    (hcap : ∀ z, Alive B z → f z ≤ cap)
    (hnext : ∀ z, Alive B z → ∀ e, f (next B δ z e) ≤ cap)
    (m : ℕ) (z : Triple) (hz : f z ≤ cap) :
    stoppedMean B δ f m z ≤ cap := by
  induction m generalizing z with
  | zero => exact hz
  | succ m ih =>
    by_cases ha : Alive B z
    · simp only [stoppedMean,if_pos ha]
      exact (average_mono _ (fun _ => cap) (fun e => ih _ (hnext z ha e))).trans_eq
        (average_const cap)
    · simpa [stoppedMean,ha] using hz
private theorem finite_occupation_of_step (B : Model) (δ c cap : ℝ)
    (f : Triple → ℝ) (hc : 0 < c)
    (hf : ∀ z, 0 ≤ f z)
    (hcap : ∀ z, Alive B z → f z ≤ cap)
    (hnext : ∀ z, Alive B z → ∀ e, f (next B δ z e) ≤ cap)
    (hstep : ∀ z, Alive B z → f z + c*δ ≤ average (fun e => f (next B δ z e)))
    (m : ℕ) (z : Triple) (hz : Alive B z) :
    δ * ∑ i ∈ Finset.range m, survival B δ i z ≤ cap / c := by
  have ht := D5.S3.Arith.Lattices.Klartag.Walk.ChainDrift.telescope
    (D := fun i => -stoppedMean B δ f i z)
    (drift := fun i => c*δ*survival B δ i z)
    (err := fun _ => 0)
    (m := m) (fun k _ => by
      have h := stopped_drift B δ (c*δ) f hstep k z; linarith)
  have hb := stopped_cap B δ cap f hcap hnext m z (hcap z hz); simp only [Finset.sum_const_zero,add_zero,stoppedMean] at ht; rw [←Finset.mul_sum] at ht; apply (le_div_iff₀ hc).mpr; nlinarith [hf z]
private theorem horizontal_continuous (B : Model) (i : Fin 2) : Continuous (fun q => horizontal B q i) := by
  by_cases hi : i = 0
  · simp only [horizontal,hi,ite_true]
    exact continuous_const
  · simp only [horizontal,hi,ite_false]
    fun_prop
private theorem coefficient_smooth (B : Model) (i j : Fin 2) : ContDiffOn ℝ ∞ (fun q => B.rho q * B.A q i j) B.neighbourhood := B.smooth_rho.mul (B.smooth_A i j)
theorem drift_continuous (B : Model) (j : Fin 2) : ContinuousOn (fun q => drift B q j) B.neighbourhood := by
  apply ContinuousOn.mul
    (B.smooth_rho.continuousOn.inv₀ (fun q hq => ne_of_gt (B.positive_rho q hq)))
  apply continuousOn_finset_sum; intro i _; exact ((coefficient_smooth B i j).continuousOn_fderiv_of_isOpen
    B.open_neighbourhood (by simp)).clm_apply
      (horizontal_continuous B i).continuousOn
private theorem coefficient_fderiv_periodic (B : Model) (i j : Fin 2)
    (q : Triple) (hq : q 0 ∈ Icc B.l B.u) (a b : ℤ) :
    fderiv ℝ (fun x => B.rho x * B.A x i j)
      (q + ![0,(a:ℝ)*(2*Real.pi),(b:ℝ)*(2*Real.pi)]) =
      fderiv ℝ (fun x => B.rho x * B.A x i j) q := by
  let v : Triple := ![0,(a:ℝ)*(2*Real.pi),(b:ℝ)*(2*Real.pi)]; let f : Triple → ℝ := fun x => B.rho x * B.A x i j; have hp : (fun x => f (x+v)) = f := by
    funext x
    dsimp [f,v]
    rw [B.periodic_rho,B.periodic_A]
  have hq' : q+v ∈ B.neighbourhood := B.contains_cylinder (q+v) (by simpa [v] using hq); have hd : DifferentiableAt ℝ f (q+v) := ((coefficient_smooth B i j).differentiableOn (by simp)).differentiableAt
      (B.open_neighbourhood.mem_nhds hq')
  have he := hd.hasFDerivAt.comp q ((hasFDerivAt_id q).add_const v); have he' : HasFDerivAt f (fderiv ℝ f (q+v)) q := by
    simpa only [Function.comp_def,id_eq,ContinuousLinearMap.comp_id,hp] using he
  exact he'.fderiv.symm
theorem drift_periodic (B : Model) (j : Fin 2)
    (q : Triple) (hq : q 0 ∈ Icc B.l B.u) (a b : ℤ) :
    drift B (q + ![0,(a:ℝ)*(2*Real.pi),(b:ℝ)*(2*Real.pi)]) j = drift B q j := by
  unfold drift; rw [B.periodic_rho]; congr 1; apply Finset.sum_congr rfl; intro i _; rw [coefficient_fderiv_periodic B i j q hq a b]; congr 1; simp [horizontal]
private theorem uniform_raw_bounds (B : Model) : ∃ a D U : ℝ, 0 < a ∧ 0 ≤ D ∧ 0 ≤ U ∧ ∀ q : Triple, q 0 ∈ Icc B.l B.u → a ≤ B.A q 0 0 ∧ B.A q 0 0 ≤ U ∧ |drift B q 0| ≤ D := by
  let p := 2*Real.pi; have hp : 0 < p := by dsimp [p]; positivity
  let lo : Triple := ![B.l,0,0]; let hi : Triple := ![B.u,p,p]; let K : Set Triple := Icc lo hi; have hK : IsCompact K := isCompact_Icc; have hsub : K ⊆ B.neighbourhood := by
    intro q hq; exact B.contains_cylinder q ⟨hq.1 0,hq.2 0⟩
  have hA := (B.smooth_A 0 0).continuousOn.mono hsub; have hd := (drift_continuous B 0).abs.mono hsub; obtain ⟨a,ha,haK⟩ := hK.exists_forall_le' hA
    (fun q hq => (B.positive_A q (hsub hq)).diag_pos (i:=0))
  obtain ⟨v,hv⟩ := (hK.image_of_continuousOn hA).bddAbove; obtain ⟨d,hdK⟩ := (hK.image_of_continuousOn hd).bddAbove; refine ⟨a,max 0 d,max 0 v,ha,le_max_left _ _,le_max_left _ _,?_⟩; intro q hq; let q' : Triple := ![q 0,p*Int.fract (q 1/p),p*Int.fract (q 2/p)]; have hq' : q' ∈ K := by
    constructor
    · intro i
      fin_cases i
      · exact hq.1
      · exact mul_nonneg hp.le (Int.fract_nonneg _)
      · exact mul_nonneg hp.le (Int.fract_nonneg _)
    · intro i
      fin_cases i
      · exact hq.2
      · exact (mul_lt_of_lt_one_right hp (Int.fract_lt_one _)).le
      · exact (mul_lt_of_lt_one_right hp (Int.fract_lt_one _)).le
  have hshift : q' = q + ![0,(-⌊q 1/p⌋:ℤ)*(2*Real.pi),(-⌊q 2/p⌋:ℤ)*(2*Real.pi)] := by
    ext i
    fin_cases i
    · simp [q']
    · change p*Int.fract (q 1/p) = q 1+(-⌊q 1/p⌋:ℤ)*p
      have hf := Int.fract_div_mul_self_add_zsmul_eq p (q 1) (ne_of_gt hp); simp only [zsmul_eq_mul,Int.cast_neg] at *; nlinarith
    · change p*Int.fract (q 2/p) = q 2+(-⌊q 2/p⌋:ℤ)*p
      have hf := Int.fract_div_mul_self_add_zsmul_eq p (q 2) (ne_of_gt hp); simp only [zsmul_eq_mul,Int.cast_neg] at *; nlinarith
  have hAp : B.A q' = B.A q := by
    rw [hshift,B.periodic_A]
  have hdp : drift B q' 0 = drift B q 0 := by
    rw [hshift,drift_periodic B 0 q hq]
  rw [←hAp,←hdp]; exact ⟨haK q' hq',(hv (mem_image_of_mem _ hq')).trans (le_max_right _ _), (hdK (mem_image_of_mem _ hq')).trans (le_max_right _ _)⟩
private theorem sigma_row_identity (B : Model) (q : Triple)
    (hq : q 0 ∈ Icc B.l B.u) :
    (sigma B q 0 0)^2 + (sigma B q 0 1)^2 = B.A q 0 0 := by
  obtain ⟨_,hs,hp⟩ := D5.S3.Observer.Hankel.PositiveGramianBalancing.gramianRoot_spec
      (B.A q) (B.positive_A q (B.contains_cylinder q hq))
  have hsym : sigma B q 1 0 = sigma B q 0 1 := by
    simpa [sigma,Matrix.conjTranspose_apply] using
      congrArg (fun S : Covariance => S 0 1) hs
  have he := congrArg (fun S : Covariance => S 0 0) hp; change (sigma B q * sigma B q) 0 0 = _ at he; simpa only [Matrix.mul_apply,Fin.sum_univ_two,hsym,pow_two] using he
private theorem increment_bound (B : Model) (δ D U : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (hraw : ∀ q : Triple, q 0 ∈ Icc B.l B.u → B.A q 0 0 ≤ U ∧ |drift B q 0| ≤ D)
    (z : Triple) (hz : Alive B z) (e : SignPair) :
    |increment B δ z e 0| ≤ D + 4*(U+1) := by
  let q := sourceMap B z; have hq : q 0 ∈ Icc B.l B.u := ⟨hz.1.le,hz.2.le⟩; obtain ⟨ha,hd⟩ := hraw q hq; have hs := sigma_row_identity B q hq; have h0 : |sigma B q 0 0| ≤ U+1 := by
    have hh := sq_abs (sigma B q 0 0); nlinarith [abs_nonneg (sigma B q 0 0),sq_nonneg (sigma B q 0 1),sq_nonneg U]
  have h1 : |sigma B q 0 1| ≤ U+1 := by
    have hh := sq_abs (sigma B q 0 1); nlinarith [abs_nonneg (sigma B q 0 1),sq_nonneg (sigma B q 0 0),sq_nonneg U]
  have hsign (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]
  have hsum : |sigma B q 0 0*sign e.1+sigma B q 0 1*sign e.2| ≤ 2*(U+1) := by
    have hh := abs_add_le (sigma B q 0 0*sign e.1) (sigma B q 0 1*sign e.2); simp only [abs_mul,hsign,mul_one] at hh; linarith
  have hsq : Real.sqrt (2*δ) ≤ 2 := by
    have hh := Real.sq_sqrt (show 0 ≤ 2*δ by positivity); nlinarith [Real.sqrt_nonneg (2*δ)]
  have hdrift : |drift B q 0*δ| ≤ D := by
    rw [abs_mul,abs_of_nonneg hδ]; exact (mul_le_mul_of_nonneg_right hd hδ).trans (by nlinarith)
  have hnoise : |Real.sqrt (2*δ)* (sigma B q 0 0*sign e.1+sigma B q 0 1*sign e.2)| ≤ 4*(U+1) := by
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]; exact (mul_le_mul hsq hsum (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hh := abs_add_le (drift B q 0*δ)
    (Real.sqrt (2*δ)*(sigma B q 0 0*sign e.1+sigma B q 0 1*sign e.2))
  change |_+_| ≤ _; exact hh.trans (add_le_add hdrift hnoise)
private theorem native_occupation_constants (B : Model) : ∃ δ₀ M : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < M ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (z : Triple) (L : ℕ), Alive B z → δ * ∑ i ∈ Finset.range L, survival B δ i z ≤ M := by
  obtain ⟨a,D,U,ha,hD,hU,hraw⟩ := uniform_raw_bounds B; let lam := (D+2)/a+1; have hlam1 : 1 ≤ lam := by
    have hh : 0 ≤ (D+2)/a := div_nonneg (by linarith) ha.le
    dsimp [lam]
    linarith
  have hlam : 0 ≤ lam := by linarith
  have hla : lam*a = D+2+a := by dsimp [lam]; field_simp <;> ring
  have hgap : 2 ≤ lam^2*a-lam*D := by
    have hh : 0 ≤ lam*a := mul_nonneg hlam ha.le; nlinarith
  let δ₀ := min 1 (1/(lam^3*D*U+1)); have hden : 0 < lam^3*D*U+1 := by positivity
  have hδ₀ : 0 < δ₀ := lt_min (by norm_num) (one_div_pos.mpr hden); let C := D+4*(U+1); have hC : 0 ≤ C := by dsimp [C]; positivity
  let cap := Real.exp (lam*(B.u+C)); let c := Real.exp (lam*B.l); have hc : 0 < c := Real.exp_pos _; let M := cap/c; refine ⟨δ₀,M,hδ₀,min_le_left _ _,div_pos (Real.exp_pos _) hc,?_⟩; intro δ hδ hδsmall z L hz; have hδ1 : δ ≤ 1 := hδsmall.trans (min_le_left _ _); have hsmall : lam^3*D*U*δ ≤ 1 := by
    have hle := hδsmall.trans (min_le_right _ _); have hmul := (le_div_iff₀ hden).mp hle; nlinarith
  let f : Triple → ℝ := fun z => Real.exp (lam*(sourceMap B z) 0); have hcap : ∀ z, Alive B z → f z ≤ cap := by
    intro z hz; apply Real.exp_le_exp.mpr; exact mul_le_mul_of_nonneg_left (by linarith [hz.2.le]) hlam
  have hn : ∀ z, Alive B z → ∀ e, f (next B δ z e) ≤ cap := by
    intro z hz e; have hj := increment_bound B δ D U hδ.le hδ1 hD hU
      (fun q hq => ⟨(hraw q hq).2.1,(hraw q hq).2.2⟩) z hz e
    change Real.exp _ ≤ Real.exp _; apply Real.exp_le_exp.mpr; rw [next_height]; have hv : increment B δ z e 0 ≤ C := (le_abs_self _).trans hj
    dsimp [C] at hv
    nlinarith [hz.2.le]
  have hstep : ∀ z, Alive B z → f z + c*δ ≤ average (fun e => f (next B δ z e)) := by
    intro z hz; let q := sourceMap B z; have hq : q 0 ∈ Icc B.l B.u := ⟨hz.1.le,hz.2.le⟩; obtain ⟨haq,hUq,hDq⟩ := hraw q hq; have hrow := sigma_row_identity B q hq; have hsmallq : lam^3*D* ((sigma B q 0 0)^2+(sigma B q 0 1)^2)*δ ≤ 1 := by
      rw [hrow]; have hh := mul_le_mul_of_nonneg_left hUq
        (show 0 ≤ lam^3*D*δ by positivity)
      nlinarith
    have hexp := exp_step_lower δ lam D a (sigma B q 0 0) (sigma B q 0 1)
      (drift B q 0) hδ.le hlam hD
      (neg_le_of_abs_le hDq) (by rwa [hrow]) hgap hsmallq
    have hm := mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg (lam*q 0)); have hcq : c ≤ Real.exp (lam*q 0) := by
      apply Real.exp_le_exp.mpr; exact mul_le_mul_of_nonneg_left hz.1.le hlam
    have heq : average (fun e => f (next B δ z e)) = Real.exp (lam*q 0) * average (fun e => Real.exp (lam*increment B δ z e 0)) := by
      rw [←average_mul]; congr 1; funext e
      dsimp [f,q]
      rw [next_height, mul_add,Real.exp_add]
    rw [heq]; change Real.exp (lam*q 0)+c*δ ≤ _; have hh : c*δ ≤ Real.exp (lam*q 0)*δ := mul_le_mul_of_nonneg_right hcq hδ.le; change 1+δ ≤ average (fun e => Real.exp (lam*increment B δ z e 0)) at hexp; nlinarith
  exact finite_occupation_of_step B δ c cap f hc (fun z => (Real.exp_pos _).le)
    hcap hn hstep L z hz
/-- Independent unreweighted sign pairs on a finite word. -/
def wordMean : ℕ → (List SignPair → ℝ) → ℝ
  | 0, f => f []
  | m+1, f => average (fun e => wordMean m (fun w => f (e::w)))
private theorem wordMean_const (m : ℕ) (c : ℝ) : wordMean m (fun _ => c) = c := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [wordMean,ih,average_const]
private theorem wordMean_mono (m : ℕ) (f g : List SignPair → ℝ)
    (h : ∀ w, w.length = m → f w ≤ g w) : wordMean m f ≤ wordMean m g := by
  induction m generalizing f g with
  | zero => exact h [] rfl
  | succ m ih =>
    apply average_mono; intro e; apply ih; intro w hw; exact h (e::w) (by simp [hw])
private theorem wordMean_add (m : ℕ) (f g : List SignPair → ℝ) : wordMean m (fun w => f w+g w) = wordMean m f+wordMean m g := by
  induction m generalizing f g with
  | zero => rfl
  | succ m ih => simp only [wordMean,ih,average_add]
private theorem average_sum (m : ℕ) (f : ℕ → SignPair → ℝ) : average (fun e => ∑ i ∈ Finset.range m, f i e) = ∑ i ∈ Finset.range m, average (f i) := by
  induction m with
  | zero => simp [average]
  | succ m ih =>
    simp only [Finset.sum_range_succ,average_add,ih]
theorem fraction_bounds (B : Model) (z : Triple) (v : Fin 2 → ℝ)
    (hz : Alive B z) : 0 < hitFraction B z v ∧ hitFraction B z v ≤ 1 := by
  unfold hitFraction; split_ifs with hp hn
  · exact ⟨lt_min (by norm_num) (div_pos (sub_pos.mpr hz.2) hp),min_le_left _ _⟩
  · exact ⟨lt_min (by norm_num) (div_pos_of_neg_of_neg (sub_neg.mpr hz.1) hn), min_le_left _ _⟩
  · norm_num
private theorem lifetime_pos (B : Model) (δ : ℝ) (hδ : 0 < δ)
    (w : List SignPair) (z : Triple) (hz : Alive B z) :
    0 < lifetime B δ z w := by
  induction w generalizing z with
  | nil => exact hδ
  | cons e w ih =>
    simp only [lifetime]; split_ifs with hn
    · exact add_pos hδ (ih _ hn)
    · exact mul_pos hδ (fraction_bounds B z (increment B δ z e) hz).1
private theorem lifetime_le_duration (B : Model) (δ : ℝ) (hδ : 0 ≤ δ)
    (w : List SignPair) (z : Triple) (hz : Alive B z) :
    lifetime B δ z w ≤ (w.length+1:ℕ)*δ := by
  induction w generalizing z with
  | nil => simp [lifetime]
  | cons e w ih =>
    simp only [lifetime]; split_ifs with hn
    · have hh := ih _ hn
      simp only [Nat.cast_add,Nat.cast_one] at hh; simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; linarith
    · have hh := mul_le_mul_of_nonneg_left (fraction_bounds B z (increment B δ z e) hz).2 hδ
      have hlen : 1 ≤ ((e::w).length+1:ℕ) := by simp
      have hlen' : (1:ℝ) ≤ (((e::w).length+1:ℕ):ℝ) := by exact_mod_cast hlen
      nlinarith
private theorem occupation_recurrence (B : Model) (δ : ℝ) (m : ℕ)
    (z : Triple) (hz : Alive B z) :
    δ * ∑ i ∈ Finset.range (m+2), survival B δ i z = δ + average (fun e => δ * ∑ i ∈ Finset.range (m+1), survival B δ i (next B δ z e)) := by
  rw [Finset.sum_range_succ']; simp only [survival,ite_eq_left hz]; rw [average_mul,average_sum]; ring
private theorem mean_lifetime_le_occupation (B : Model) (δ : ℝ) (hδ : 0 ≤ δ)
    (m : ℕ) (z : Triple) (hz : Alive B z) :
    wordMean m (lifetime B δ z) ≤ δ * ∑ i ∈ Finset.range (m+1), survival B δ i z := by
  induction m generalizing z with
  | zero => simp [wordMean,lifetime,survival,hz]
  | succ m ih =>
    rw [occupation_recurrence B δ m z hz,wordMean]
    calc
      _ ≤ average (fun e => δ + δ * ∑ i ∈ Finset.range (m+1), survival B δ i (next B δ z e)) := by
        apply average_mono; intro e; by_cases hn : Alive B (next B δ z e)
        · simp only [lifetime,ite_eq_left hn,wordMean_add,wordMean_const]
          have hh := ih _ hn; linarith
        · have hh := mul_le_mul_of_nonneg_left (fraction_bounds B z (increment B δ z e) hz).2 hδ
          simp only [lifetime,ite_eq_right hn,wordMean_const]; simp only [survival_dead B δ _ _ hn,Finset.sum_const_zero,mul_zero,add_zero]; simpa using hh
      _ = _ := by rw [average_add,average_const]
private theorem survival_add_le (B : Model) (δ c : ℝ) (k : ℕ)
    (hc : ∀ z, survival B δ k z ≤ c) (m : ℕ) (z : Triple) :
    survival B δ (m+k) z ≤ c*survival B δ m z := by
  induction m generalizing z with
  | zero =>
    by_cases hz : Alive B z
    · simpa [survival,hz] using hc z
    · simp [survival_dead B δ _ z hz]
  | succ m ih =>
    have hm : m+1+k = (m+k)+1 := by omega
    rw [hm]; by_cases hz : Alive B z
    · simp only [survival,ite_eq_left hz]
      rw [←average_mul]; exact average_mono _ _ (fun e => ih _)
    · simp [survival_dead B δ _ z hz]
private theorem block_survival (B : Model) (δ M : ℝ) (hδ : 0 < δ) (hM : 0 < M)
    (hocc : ∀ (z : Triple) (L : ℕ), Alive B z → δ * ∑ i ∈ Finset.range L, survival B δ i z ≤ M) :
    ∀ z, survival B δ ⌈2*M/δ⌉₊ z ≤ 1/2 := by
  intro z; by_cases hz : Alive B z
  · have ho := hocc z ⌈2*M/δ⌉₊ hz
    have hsum : (⌈2*M/δ⌉₊:ℝ)*survival B δ ⌈2*M/δ⌉₊ z ≤ ∑ i ∈ Finset.range ⌈2*M/δ⌉₊, survival B δ i z := by
      calc
        _ = ∑ _i ∈ Finset.range ⌈2*M/δ⌉₊, survival B δ ⌈2*M/δ⌉₊ z := by simp
        _ ≤ _ := Finset.sum_le_sum (fun i hi =>
          survival_antitone B δ z (Finset.mem_range.mp hi).le)
    have hceil := Nat.le_ceil (2*M/δ); have htime : 2*M ≤ (⌈2*M/δ⌉₊:ℝ)*δ := (div_le_iff₀ hδ).mp hceil; have hs := (survival_bounds B δ ⌈2*M/δ⌉₊ z).1; have hm := mul_le_mul_of_nonneg_left hsum hδ.le; nlinarith
  · simp [survival_dead B δ _ z hz]
private theorem geometric_survival (B : Model) (δ : ℝ) (b : ℕ)
    (hb : ∀ z, survival B δ b z ≤ 1/2) (j : ℕ) (z : Triple) :
    survival B δ (j*b) z ≤ (1/2:ℝ)^j := by
  induction j with
  | zero => simpa using (survival_bounds B δ 0 z).2
  | succ j ih =>
    rw [Nat.succ_mul,pow_succ]; have h := survival_add_le B δ (1/2) b hb (j*b) z; nlinarith
def lifetimeProbability (B : Model) (δ : ℝ) (m : ℕ) (z : Triple) (t : ℝ) : ℝ := wordMean m (fun w => if t < lifetime B δ z w then 1 else 0)
def excessMean (B : Model) (δ : ℝ) (m : ℕ) (z : Triple) (t : ℝ) : ℝ := wordMean m (fun w => max (lifetime B δ z w-t) 0)
private theorem lifetimeProbability_bounds (B : Model) (δ : ℝ) (m : ℕ)
    (z : Triple) (t : ℝ) :
    0 ≤ lifetimeProbability B δ m z t ∧ lifetimeProbability B δ m z t ≤ 1 := by
  constructor
  · rw [←wordMean_const m 0]
    exact wordMean_mono m _ _ (fun w _ => by split <;> norm_num)
  · rw [←wordMean_const m 1]
    exact wordMean_mono m _ _ (fun w _ => by split <;> norm_num)
private theorem probability_from_prefix (B : Model) (δ : ℝ) (hδ : 0 < δ)
    (k m : ℕ) (z : Triple) (hz : Alive B z) (t : ℝ)
    (ht : (k:ℝ)*δ+δ ≤ t) :
    lifetimeProbability B δ m z t ≤ survival B δ k z := by
  induction k generalizing m z t with
  | zero => simpa [survival,hz] using (lifetimeProbability_bounds B δ m z t).2
  | succ k ih =>
    cases m with
    | zero =>
      have hkt : 0 ≤ (k:ℝ)*δ := by positivity
      have ht' : δ ≤ t := by
        simp only [Nat.cast_add,Nat.cast_one] at ht; nlinarith
      simp only [lifetimeProbability,wordMean,lifetime,not_lt_of_ge ht',ite_false]; exact (survival_bounds B δ (k+1) z).1
    | succ m =>
      simp only [lifetimeProbability,wordMean]; rw [survival,ite_eq_left hz]; apply average_mono; intro e; by_cases hn : Alive B (next B δ z e)
      · simp only [lifetime,ite_eq_left hn]
        have heq : (fun w => if t < δ+lifetime B δ (next B δ z e) w then (1:ℝ) else 0) = (fun w => if t-δ < lifetime B δ (next B δ z e) w then (1:ℝ) else 0) := by
          funext w; congr 1; apply propext; constructor <;> intro hh <;> linarith
        rw [heq]; exact ih m _ hn (t-δ) (by
          simp only [Nat.cast_add,Nat.cast_one] at ht; nlinarith)
      · have hh := mul_le_mul_of_nonneg_left (fraction_bounds B z (increment B δ z e) hz).2 hδ.le
        have hkt : 0 ≤ (k:ℝ)*δ := by positivity
        have ht' : δ*hitFraction B z (increment B δ z e) ≤ t := by
          simp only [Nat.cast_add,Nat.cast_one] at ht; nlinarith
        simp only [lifetime,ite_eq_right hn,not_lt_of_ge ht',ite_false,wordMean_const]; exact (survival_bounds B δ k (next B δ z e)).1
private theorem excess_from_prefix (B : Model) (δ M : ℝ) (hδ : 0 < δ)
    (hmean : ∀ (m : ℕ) (z : Triple), Alive B z → wordMean m (lifetime B δ z) ≤ M)
    (k m : ℕ) (z : Triple) (hz : Alive B z) (t : ℝ)
    (ht : (k:ℝ)*δ ≤ t) :
    excessMean B δ m z t ≤ M*survival B δ k z := by
  induction k generalizing m z t with
  | zero =>
    simp only [Nat.cast_zero,zero_mul] at ht; simp only [survival,ite_eq_left hz,mul_one]; exact (wordMean_mono m _ _ (fun w _ =>
      max_le (by linarith) (lifetime_pos B δ hδ w z hz).le)).trans (hmean m z hz)
  | succ k ih =>
    cases m with
    | zero =>
      have ht' : δ ≤ t := by
        have hk : 0 ≤ (k:ℝ)*δ := by positivity
        simp only [Nat.cast_add,Nat.cast_one] at ht; nlinarith
      simp only [excessMean,wordMean,lifetime,max_eq_right (sub_nonpos.mpr ht')]; have hM : 0 ≤ M := by
        have hh := hmean 0 z hz; simp only [wordMean,lifetime] at hh; linarith
      exact mul_nonneg hM (survival_bounds B δ (k+1) z).1
    | succ m =>
      simp only [excessMean,wordMean]; rw [survival,ite_eq_left hz,←average_mul]; apply average_mono; intro e; by_cases hn : Alive B (next B δ z e)
      · simp only [lifetime,ite_eq_left hn]
        have heq : (fun w => max (δ+lifetime B δ (next B δ z e) w-t) 0) = (fun w => max (lifetime B δ (next B δ z e) w-(t-δ)) 0) := by
          funext w; congr 1; ring
        rw [heq]; exact ih m _ hn (t-δ) (by
          simp only [Nat.cast_add,Nat.cast_one] at ht; nlinarith)
      · have hh := mul_le_mul_of_nonneg_left (fraction_bounds B z (increment B δ z e) hz).2 hδ.le
        have ht' : δ*hitFraction B z (increment B δ z e) ≤ t := by
          have hk : 0 ≤ (k:ℝ)*δ := by positivity
          simp only [Nat.cast_add,Nat.cast_one] at ht; nlinarith
        simp only [lifetime,ite_eq_right hn,max_eq_right (sub_nonpos.mpr ht'),wordMean_const]; have hM : 0 ≤ M := by
          have hh := hmean 0 z hz; simp only [wordMean,lifetime] at hh; linarith
        exact mul_nonneg hM (survival_bounds B δ k (next B δ z e)).1
private theorem native_uniform_estimates (B : Model) : ∃ δ₀ M h : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < M ∧ 0 < h ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (m : ℕ) (z : Triple), Alive B z → (∀ t : ℝ, 0 ≤ t → lifetimeProbability B δ m z t ≤ (1/2:ℝ)^⌊max (t-1) 0/h⌋₊) ∧ (∀ R : ℝ, 1 ≤ R → excessMean B δ m z R ≤ 2*h*(1/2:ℝ)^⌊(R-1)/h⌋₊) := by
  obtain ⟨δ₀,M,hδ₀,hδ₀1,hM,hocc⟩ := native_occupation_constants B; let h := 2*M+1; have hh : 0 < h := by dsimp [h]; positivity
  refine ⟨δ₀,M,h,hδ₀,hδ₀1,hM,hh,?_⟩; intro δ hδ hsmall m z hz; have hδ1 := hsmall.trans hδ₀1; let b : ℕ := ⌈2*M/δ⌉₊; have hb : ∀ z, survival B δ b z ≤ 1/2 := block_survival B δ M hδ hM (hocc δ hδ hsmall); have hbtime : (b:ℝ)*δ ≤ h := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 2*M/δ by positivity); have hc' := mul_lt_mul_of_pos_right hc hδ; have hd : (2*M/δ+1)*δ = 2*M+δ := by field_simp <;> ring
    rw [hd] at hc'
    dsimp [h]
    exact hc'.le.trans (by linarith)
  have htime (j : ℕ) : ((j*b:ℕ):ℝ)*δ ≤ (j:ℝ)*h := by
    have he := mul_le_mul_of_nonneg_left hbtime (Nat.cast_nonneg j : (0:ℝ) ≤ j); simpa only [Nat.cast_mul,mul_assoc] using he
  have hmean : ∀ (m : ℕ) (z : Triple), Alive B z → wordMean m (lifetime B δ z) ≤ M := by
    intro m z hz; exact (mean_lifetime_le_occupation B δ hδ.le m z hz).trans
      (hocc δ hδ hsmall z (m+1) hz)
  constructor
  · intro t ht
    by_cases ht1 : 1 ≤ t
    · let j : ℕ := ⌊max (t-1) 0/h⌋₊
      have hj : (j:ℝ)*h ≤ t-1 := by
        have hf := Nat.floor_le (show 0 ≤ max (t-1) 0/h by positivity); have hp := (le_div_iff₀ hh).mp hf; simpa [j,max_eq_left (by linarith : 0 ≤ t-1)] using hp
      have hkt : ((j*b:ℕ):ℝ)*δ+δ ≤ t := by
        have hc := htime j; linarith
      exact (probability_from_prefix B δ hδ (j*b) m z hz t hkt).trans
        (geometric_survival B δ b hb j z)
    · have hzero : max (t-1) 0 = 0 := max_eq_right (by linarith)
      simpa [hzero] using (lifetimeProbability_bounds B δ m z t).2
  · intro R hR
    let j : ℕ := ⌊(R-1)/h⌋₊; have hj : (j:ℝ)*h ≤ R-1 := (le_div_iff₀ hh).mp (Nat.floor_le (show 0 ≤ (R-1)/h by positivity)); have hkt : ((j*b:ℕ):ℝ)*δ ≤ R := (htime j).trans (by linarith); have hp := excess_from_prefix B δ M hδ hmean (j*b) m z hz R hkt; have hg := geometric_survival B δ b hb j z; have hmg := mul_le_mul_of_nonneg_left hg hM.le; have hMh : M ≤ 2*h := by dsimp [h]; linarith
    exact hp.trans (hmg.trans (mul_le_mul_of_nonneg_right hMh (by positivity)))
def mesh (n : ℕ) : ℝ := 1/(n:ℝ)^2
def nativeProbability (B : Model) (n : ℕ) (t : ℝ) : ℝ := lifetimeProbability B (mesh n) (n^3) 0 t
def nativeExcess (B : Model) (n : ℕ) (R : ℝ) : ℝ := excessMean B (mesh n) (n^3) 0 R
private theorem mesh_eventually_small (δ₀ : ℝ) (hδ₀ : 0 < δ₀) : ∃ n₀ : ℕ, ∀ n ≥ n₀, 0 < mesh n ∧ mesh n ≤ δ₀ := by
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt (max 1 (1/δ₀)); refine ⟨n₀,?_⟩; intro n hn; have hnc : (n₀:ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : 1 ≤ (n:ℝ) := (le_max_left _ _).trans (hn₀.le.trans hnc); have hnpos : 0 < (n:ℝ) := by linarith
  have hbase : 1/δ₀ ≤ (n:ℝ) := (le_max_right _ _).trans (hn₀.le.trans hnc); have hbase' : 1 ≤ (n:ℝ)*δ₀ := (div_le_iff₀ hδ₀).mp hbase; have hpow : (n:ℝ) ≤ (n:ℝ)^2 := by nlinarith
  refine ⟨by dsimp [mesh]; positivity,?_⟩; apply (div_le_iff₀ (sq_pos_of_pos hnpos)).mpr; nlinarith [mul_le_mul_of_nonneg_right hpow hδ₀.le]
private theorem finite_law_estimates (B : Model) : ∃ h M : ℝ, ∃ n₀ : ℕ, 0 < h ∧ 0 < M ∧ ∀ n ≥ n₀, (∀ t : ℝ, 0 ≤ t → nativeProbability B n t ≤ (1/2:ℝ)^⌊max (t-1) 0/h⌋₊) ∧ (∀ R : ℝ, 1 ≤ R → nativeExcess B n R ≤ 2*h*(1/2:ℝ)^⌊(R-1)/h⌋₊) := by
  obtain ⟨δ₀,M,h,hδ₀,hδ₀1,hM,hh,hest⟩ := native_uniform_estimates B; obtain ⟨n₀,hn₀⟩ := mesh_eventually_small δ₀ hδ₀; refine ⟨h,M,n₀,hh,hM,?_⟩; intro n hn; have hz : Alive B 0 := by simpa [Alive,sourceMap] using B.source_height
  exact hest (mesh n) (hn₀ n hn).1 (hn₀ n hn).2 (n^3) 0 hz
private theorem average_eq_sum (f : SignPair → ℝ) : average f = (1/4:ℝ) * ∑ e : SignPair, f e := by
  simp [average,Fintype.sum_prod_type,Fintype.sum_bool]; ring
private theorem wordMean_uniform (m : ℕ) (f : List SignPair → ℝ) : wordMean m f = (1/4:ℝ)^m * ∑ w : Fin m → SignPair, f (List.ofFn w) := by
  induction m generalizing f with
  | zero => simp [wordMean]
  | succ m ih =>
    have he : (∑ w : Fin (m+1) → SignPair, f (List.ofFn w)) = ∑ e : SignPair, ∑ w : Fin m → SignPair, f (e::List.ofFn w) := by
      have hh := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m+1) => SignPair))
        (fun p => f (List.ofFn (Fin.cons p.1 p.2)))
        (fun w => f (List.ofFn w)) (fun _ => rfl)
      simpa [Fintype.sum_prod_type,List.ofFn_succ] using hh.symm
    simp only [wordMean,ih,average_eq_sum,he,pow_succ]; rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    ring
private theorem chord_height (B : Model) (z : Triple) (v : Fin 2 → ℝ) (θ : ℝ) : (sourceMap B (chord z v θ)) 0 = (sourceMap B z) 0 + θ*v 0 := by
  simp [sourceMap,chord]; ring
private theorem chord_inside (B : Model) (z : Triple) (v : Fin 2 → ℝ)
    (hz : Alive B z) (hn : Alive B (chord z v 1))
    (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) : Alive B (chord z v θ) := by
  simp only [Alive,chord_height,one_mul] at hz hn ⊢; have hn' : B.l < (sourceMap B z) 0+v 0 ∧ (sourceMap B z) 0+v 0 < B.u := by simpa using hn
  have hm : 0 ≤ 1-θ := by linarith [hθ.2]
  constructor
  · by_cases he : θ = 0
    · simpa [he] using hz.1
    · have ht : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm he)
      nlinarith [mul_pos ht (sub_pos.mpr hn'.1), mul_nonneg hm (sub_pos.mpr hz.1).le]
  · by_cases he : θ = 0
    · simpa [he] using hz.2
    · have ht : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm he)
      nlinarith [mul_pos ht (sub_pos.mpr hn'.2), mul_nonneg hm (sub_pos.mpr hz.2).le]
private theorem dead_chord_first_hit (B : Model) (z : Triple) (v : Fin 2 → ℝ)
    (hz : Alive B z) (hn : ¬ Alive B (chord z v 1)) :
    ((sourceMap B (chord z v (hitFraction B z v))) 0 = B.l ∨ (sourceMap B (chord z v (hitFraction B z v))) 0 = B.u) ∧
    (∀ θ : ℝ, 0 ≤ θ → θ < hitFraction B z v → Alive B (chord z v θ)) := by
  have hdead : ¬ ((sourceMap B z) 0+v 0 ∈ Ioo B.l B.u) := by
    simpa [Alive,chord_height] using hn
  by_cases hp : 0 < v 0
  · have hright : B.u ≤ (sourceMap B z) 0+v 0 := by
      by_contra hh
      apply hdead; exact ⟨by linarith [hz.1],lt_of_not_ge hh⟩
    have hr : (B.u-(sourceMap B z) 0)/v 0 ≤ 1 := (div_le_one hp).mpr (by linarith); have hf : hitFraction B z v = (B.u-(sourceMap B z) 0)/v 0 := by
      simp [hitFraction,hp,min_eq_right hr]
    rw [hf]; constructor
    · right
      rw [chord_height]; field_simp <;> ring
    · intro θ hθ ht
      rw [Alive,chord_height]; have hmul := (lt_div_iff₀ hp).mp ht; constructor
      · nlinarith [mul_nonneg hθ hp.le,hz.1]
      · linarith
  · have hnz : v 0 < 0 := by
      by_contra hh
      have he : v 0 = 0 := by linarith
      apply hdead; simpa [Alive,he] using hz
    have hleft : (sourceMap B z) 0+v 0 ≤ B.l := by
      by_contra hh
      apply hdead; exact ⟨lt_of_not_ge hh,by linarith [hz.2]⟩
    have hr : (B.l-(sourceMap B z) 0)/v 0 ≤ 1 := (div_le_one_of_neg hnz).mpr (by linarith); have hf : hitFraction B z v = (B.l-(sourceMap B z) 0)/v 0 := by
      simp [hitFraction,hp,hnz,min_eq_right hr]
    rw [hf]; constructor
    · left
      rw [chord_height]; field_simp [ne_of_lt hnz] <;> ring
    · intro θ hθ ht
      rw [Alive,chord_height]; have hmul := (lt_div_iff_of_neg hnz).mp ht; constructor
      · linarith
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos hθ hnz.le,hz.2]
/-- Chord interpolation, holds, and the terminal upper-wall leg. -/
def trajectory (B : Model) (δ : ℝ) (z : Triple) : List SignPair → ℝ → Triple
  | [], t => chord z ![B.u-(sourceMap B z) 0,0] (min (max (t/δ) 0) 1)
  | e::es, t =>
    let v := increment B δ z e
    if Alive B (next B δ z e) then
      if t ≤ δ then chord z v (max (t/δ) 0)
      else trajectory B δ (next B δ z e) es (t-δ)
    else chord z v (min (max (t/δ) 0) (hitFraction B z v))
private theorem trajectory_before_hit (B : Model) (δ : ℝ) (hδ : 0 < δ)
    (w : List SignPair) (z : Triple) (hz : Alive B z)
    (t : ℝ) (ht : 0 ≤ t) (hlt : t < lifetime B δ z w) :
    Alive B (trajectory B δ z w t) := by
  induction w generalizing z t with
  | nil =>
    have hθ : 0 ≤ t/δ := div_nonneg ht hδ.le; have hθ1 : t/δ < 1 := (div_lt_one hδ).mpr hlt; simp only [trajectory,max_eq_left hθ,min_eq_left hθ1.le,Alive,chord_height,Matrix.cons_val_zero]; constructor
    · nlinarith [mul_nonneg hθ (sub_pos.mpr hz.2).le,hz.1]
    · have hh := mul_lt_mul_of_pos_right hθ1 (sub_pos.mpr hz.2)
      nlinarith
  | cons e w ih =>
    by_cases hn : Alive B (next B δ z e)
    · simp only [lifetime,ite_eq_left hn] at hlt
      simp only [trajectory,ite_eq_left hn]; split_ifs with htδ
      · apply chord_inside B z _ hz
          (by simpa [next] using hn) (max (t/δ) 0)
        exact ⟨le_max_right _ _,max_le ((div_le_one hδ).mpr htδ) (by norm_num)⟩
      · exact ih _ hn (t-δ) (by linarith) (by linarith)
    · have hh := dead_chord_first_hit B z (increment B δ z e) hz
        (by simpa [next] using hn)
      have hθ : 0 ≤ t/δ := div_nonneg ht hδ.le; have hθcap : t/δ < hitFraction B z (increment B δ z e) := (div_lt_iff₀ hδ).mpr (by simpa only [lifetime,ite_eq_right hn,mul_comm] using hlt); simp only [trajectory,ite_eq_right hn,max_eq_left hθ,min_eq_left hθcap.le]; exact hh.2 _ hθ hθcap
private theorem trajectory_at_hit (B : Model) (δ : ℝ) (hδ : 0 < δ)
    (w : List SignPair) (z : Triple) (hz : Alive B z) :
    (sourceMap B (trajectory B δ z w (lifetime B δ z w))) 0 = B.l ∨ (sourceMap B (trajectory B δ z w (lifetime B δ z w))) 0 = B.u := by
  induction w generalizing z with
  | nil =>
    right
    simp [trajectory,lifetime,ne_of_gt hδ,chord_height]
  | cons e w ih =>
    by_cases hn : Alive B (next B δ z e)
    · have hl := lifetime_pos B δ hδ w _ hn
      simp only [lifetime,ite_eq_left hn,trajectory]; rw [ite_eq_right (by linarith : ¬δ+lifetime B δ (next B δ z e) w ≤ δ)]; simpa only [add_sub_cancel_left] using ih _ hn
    · have hh := dead_chord_first_hit B z (increment B δ z e) hz
        (by simpa [next] using hn)
      have hc := (fraction_bounds B z (increment B δ z e) hz).1.le; simpa [trajectory,lifetime,hn,ne_of_gt hδ,max_eq_left hc] using hh.1
def firstWallTime (B : Model) (δ : ℝ) (z : Triple) (w : List SignPair) : ℝ := sInf {t : ℝ | 0 ≤ t ∧ ((sourceMap B (trajectory B δ z w t)) 0 = B.l ∨ (sourceMap B (trajectory B δ z w t)) 0 = B.u)}
private theorem firstWallTime_eq_lifetime (B : Model) (δ : ℝ) (hδ : 0 < δ)
    (w : List SignPair) (z : Triple) (hz : Alive B z) :
    firstWallTime B δ z w = lifetime B δ z w := by
  let S : Set ℝ := {t : ℝ | 0 ≤ t ∧ ((sourceMap B (trajectory B δ z w t)) 0 = B.l ∨ (sourceMap B (trajectory B δ z w t)) 0 = B.u)}; have hmem : lifetime B δ z w ∈ S := ⟨(lifetime_pos B δ hδ w z hz).le,trajectory_at_hit B δ hδ w z hz⟩; have hbound : BddBelow S := ⟨0,fun t ht => ht.1⟩; have hleast : ∀ t ∈ S, lifetime B δ z w ≤ t := by
    intro t ht
    by_contra hh
    have ha := trajectory_before_hit B δ hδ w z hz t ht.1 (lt_of_not_ge hh); rcases ht.2 with he | he
    · exact (ne_of_gt ha.1) he
    · exact (ne_of_lt ha.2) he
  exact le_antisymm (csInf_le hbound hmem) (le_csInf ⟨_,hmem⟩ hleast)
def physicalState (B : Model) (z : Triple) : ℝ × AddCircle (2*Real.pi) × AddCircle (2*Real.pi) := ((sourceMap B z) 0,((sourceMap B z) 1 : AddCircle (2*Real.pi)), ((sourceMap B z) 2 : AddCircle (2*Real.pi)))
theorem trajectory_zero (B : Model) (δ : ℝ) (hδ : 0 < δ)
    (w : List SignPair) (z : Triple) (hz : Alive B z) :
    trajectory B δ z w 0 = z := by
  cases w with
  | nil => ext i; fin_cases i <;> simp [trajectory,chord]
  | cons e w =>
    by_cases hn : Alive B (next B δ z e)
    · ext i
      fin_cases i <;> simp [trajectory,hn,hδ.le,chord]
    · have hfrac : 0 ≤ hitFraction B z (increment B δ z e) := by
        exact (fraction_bounds B z (increment B δ z e) hz).1.le
      ext i
      fin_cases i <;> simp [trajectory,hn,chord,min_eq_left hfrac]
def cutParameter (δ cap t : ℝ) : ℝ := min (max (t/δ) 0) cap
def cutChord (δ cap : ℝ) (z : Triple) (v : Fin 2 → ℝ) (t : ℝ) : Triple := chord z v (cutParameter δ cap t)
theorem cutParameter_lipschitz (δ cap : ℝ) : LipschitzWith ‖δ⁻¹‖₊ (cutParameter δ cap) := by
  have hlin : LipschitzWith ‖δ⁻¹‖₊ (fun t : ℝ => t/δ) := by
    rw [lipschitzWith_iff_dist_le_mul]; intro x y; simp only [Real.dist_eq, div_eq_mul_inv, ←sub_mul, abs_mul]; simp [mul_comm]
  exact (hlin.max_const 0).min_const cap
private theorem cutChord_area (δ cap : ℝ) (z : Triple) (v : Fin 2 → ℝ)
    (hcap : 0 ≤ cap) (T : ℝ) :
    (∫ t in (0:ℝ)..T, cutChord δ cap z v t 0 * deriv (fun s => cutChord δ cap z v s 1) t) = cutChord δ cap z v T 2-z 2 := by
  let θ := cutParameter δ cap; have hθ := cutParameter_lipschitz δ cap; have hac : AbsolutelyContinuousOnInterval θ 0 T := hθ.lipschitzOnWith.absolutelyContinuousOnInterval; have hconst (c : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 T := (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval; have hjac : AbsolutelyContinuousOnInterval (fun t => cutChord δ cap z v t 2) 0 T := by
    have h := ((hconst (z 2)).add (hac.const_mul (z 0*v 1))).add
      ((hac.mul hac).const_mul (v 0*v 1/2))
    convert h using 1; funext t; simp [cutChord,chord,θ,Pi.add_apply,Pi.mul_apply] <;> ring
  have hae : ∀ᵐ t ∂volume, cutChord δ cap z v t 0 * deriv (fun s => cutChord δ cap z v s 1) t = deriv (fun s => cutChord δ cap z v s 2) t := by
    filter_upwards [hθ.ae_differentiableAt_real] with t ht; have hd := ht.hasDerivAt; have hb := (hd.mul_const (v 1)).const_add (z 1); have hj := ((hasDerivAt_const t (z 2)).add
      ((hd.mul_const (z 0)).mul_const (v 1))).add
        ((((hd.pow 2).div_const 2).mul_const (v 0)).mul_const (v 1))
    have hb' : deriv (fun s => cutChord δ cap z v s 1) t = deriv θ t*v 1 := by
      simpa [cutChord,chord,θ] using hb.deriv
    have hj' : deriv (fun s => cutChord δ cap z v s 2) t = deriv θ t*z 0*v 1+ ((2*(θ t)^(2-1)*deriv θ t)/2)*v 0*v 1 := by
      have heq : (((fun _ : ℝ => z 2) + (fun s => cutParameter δ cap s*z 0*v 1)) + (fun s => (cutParameter δ cap ^ 2) s/2*v 0*v 1)) = (fun s => cutChord δ cap z v s 2) := by
        funext s; simp [Pi.add_apply,Pi.pow_apply,cutChord,chord]
      rw [heq] at hj; simpa [θ] using hj.deriv
    rw [hb',hj']; simp [cutChord,chord,θ]; ring
  have hi : (∫ t in (0:ℝ)..T, cutChord δ cap z v t 0 * deriv (fun s => cutChord δ cap z v s 1) t) = ∫ t in (0:ℝ)..T, deriv (fun s => cutChord δ cap z v s 2) t := intervalIntegral.integral_congr_ae (hae.mono (fun t ht _ => ht)); rw [hi,hjac.integral_deriv_eq_sub]; simp [cutChord,cutParameter,chord,min_eq_left hcap]
def nativeBase (B : Model) : D5.S3.Quantum.Fibers.FiniteRectangleTransport.Base := (B.r/2,B.r/2,1-B.r)
private theorem cutChord_ac (B : Model) (δ cap : ℝ) (z : Triple) (v : Fin 2 → ℝ)
    (T : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t => (sourceMap B (cutChord δ cap z v t)) 0) 0 T ∧
    AbsolutelyContinuousOnInterval (fun t => cutChord δ cap z v t 1) 0 T := by
  have hθ : AbsolutelyContinuousOnInterval (cutParameter δ cap) 0 T := (cutParameter_lipschitz δ cap).lipschitzOnWith.absolutelyContinuousOnInterval; have hc (c : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 T := (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval; constructor
  · convert (hc (B.source 0+z 0)).add (hθ.const_mul (v 0)) using 1
    funext t; simp [sourceMap,cutChord,chord]; ring
  · convert (hc (z 1)).add (hθ.const_mul (v 1)) using 1
    funext t; simp [cutChord,chord]; ring
private theorem cutChord_original (B : Model) (δ cap : ℝ) (z : Triple) (v : Fin 2 → ℝ)
    (hcap : 0 ≤ cap)
    (hclosed : ∀ θ ∈ Icc (0:ℝ) cap, (sourceMap B (chord z v θ)) 0 ∈ Icc B.l B.u)
    (T : ℝ) (hT : 0 ≤ T) :
    D5.S3.Quantum.Fibers.OriginalControlComposition.OriginalControl (nativeBase B) T
      (fun t => (sourceMap B (cutChord δ cap z v t)) 0)
      (fun t => cutChord δ cap z v t 1) := by
  have hac := cutChord_ac B δ cap z v T; have hk := hac.1; have hb := hac.2; refine ⟨hT,hk.continuousOn,hb.continuousOn,?_,hb.boundedVariationOn,Or.inl ⟨hk,hb⟩⟩; intro t _; have hθmem : cutParameter δ cap t ∈ Icc (0:ℝ) cap := ⟨le_min (le_max_right _ _) hcap,min_le_right _ _⟩; have hh := hclosed (cutParameter δ cap t) hθmem; have hlo : D5.S3.Quantum.Fibers.FiniteRectangleTransport.lower (nativeBase B) = 0 := by
    unfold D5.S3.Quantum.Fibers.FiniteRectangleTransport.lower nativeBase; have he : B.r/2+B.r/2-(1-(1-B.r)) = 0 := by ring
    simp [he]
  have hhi : D5.S3.Quantum.Fibers.FiniteRectangleTransport.upper (nativeBase B) = B.r/2 := by
    simp [D5.S3.Quantum.Fibers.FiniteRectangleTransport.upper,nativeBase]
  rw [hlo,hhi]; exact ⟨B.lower_pos.trans_le hh.1,hh.2.trans_lt B.upper_lt⟩
private theorem dead_chord_closed (B : Model) (z : Triple) (v : Fin 2 → ℝ)
    (hz : Alive B z) (hn : ¬Alive B (chord z v 1)) :
    ∀ θ ∈ Icc (0:ℝ) (hitFraction B z v), (sourceMap B (chord z v θ)) 0 ∈ Icc B.l B.u := by
  intro θ hθ; have hh := dead_chord_first_hit B z v hz hn; obtain ht | he := hθ.2.lt_or_eq
  · exact ⟨(hh.2 θ hθ.1 ht).1.le,(hh.2 θ hθ.1 ht).2.le⟩
  · subst θ
    rcases hh.1 with h | h
    · rw [h]; exact ⟨le_rfl,B.interval_nonempty.le⟩
    · rw [h]; exact ⟨B.interval_nonempty.le,le_rfl⟩
private theorem trajectory_cons_coordinate (B : Model) (δ : ℝ) (hδ : 0 < δ)
    (e : SignPair) (w : List SignPair) (z : Triple)
    (hn : Alive B (next B δ z e)) (i : Fin 3) :
    (fun t => trajectory B δ z (e::w) t i) = D5.S3.Quantum.Fibers.OriginalControlComposition.concatenate
        (fun t => cutChord δ 1 z (increment B δ z e) t i)
        (fun t => trajectory B δ (next B δ z e) w t i) δ := by
  funext t; have hzero := trajectory_zero B δ hδ w (next B δ z e) hn; by_cases ht : t ≤ δ
  · have hθ : max (t/δ) 0 ≤ 1 := max_le ((div_le_one hδ).mpr ht) (by norm_num)
    simp [trajectory,hn,D5.S3.Quantum.Fibers.OriginalControlComposition.concatenate, ht,cutChord,cutParameter,min_eq_left hθ]
  · have hend : cutChord δ 1 z (increment B δ z e) δ = next B δ z e := by
      simp [cutChord,cutParameter,next,ne_of_gt hδ]
    simp [trajectory,hn,D5.S3.Quantum.Fibers.OriginalControlComposition.concatenate, ht,hzero,hend]
private theorem trajectory_cons_height (B : Model) (δ : ℝ) (hδ : 0 < δ)
    (e : SignPair) (w : List SignPair) (z : Triple)
    (hn : Alive B (next B δ z e)) :
    (fun t => (sourceMap B (trajectory B δ z (e::w) t)) 0) = D5.S3.Quantum.Fibers.OriginalControlComposition.concatenate
        (fun t => (sourceMap B (cutChord δ 1 z (increment B δ z e) t)) 0)
        (fun t => (sourceMap B (trajectory B δ (next B δ z e) w t)) 0) δ := by
  have he := trajectory_cons_coordinate B δ hδ e w z hn 0; funext t; have hh := congrFun he t; simp only [sourceMap,Matrix.cons_val_zero]; rw [hh]; unfold D5.S3.Quantum.Fibers.OriginalControlComposition.concatenate; split_ifs <;> ring
private theorem trajectory_original_area (B : Model) (δ : ℝ) (hδ : 0 < δ)
    (w : List SignPair) (z : Triple) (hz : Alive B z) (T : ℝ) (hT : 0 ≤ T) :
    D5.S3.Quantum.Fibers.OriginalControlComposition.OriginalControl (nativeBase B) T
      (fun t => (sourceMap B (trajectory B δ z w t)) 0)
      (fun t => trajectory B δ z w t 1) ∧
    (∫ t in (0:ℝ)..T, trajectory B δ z w t 0 * deriv (fun s => trajectory B δ z w s 1) t) = trajectory B δ z w T 2-z 2 := by
  induction w generalizing z T with
  | nil =>
    have he : trajectory B δ z [] = cutChord δ 1 z ![B.u-(sourceMap B z) 0,0] := rfl; rw [he]; refine ⟨cutChord_original B δ 1 z _ (by norm_num) ?_ T hT, cutChord_area δ 1 z _ (by norm_num) T⟩; intro θ hθ; rw [chord_height]; simp only [Matrix.cons_val_zero]; constructor
    · nlinarith [mul_nonneg hθ.1 (sub_pos.mpr hz.2).le,hz.1]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hθ.2) (sub_pos.mpr hz.2).le]
  | cons e w ih =>
    by_cases hn : Alive B (next B δ z e)
    · have hc : D5.S3.Quantum.Fibers.OriginalControlComposition.OriginalControl
          (nativeBase B) δ
          (fun t => (sourceMap B (cutChord δ 1 z (increment B δ z e) t)) 0)
          (fun t => cutChord δ 1 z (increment B δ z e) t 1) := by
        apply cutChord_original B δ 1 z _ (by norm_num) _ δ hδ.le; intro θ hθ; exact ⟨(chord_inside B z _ hz (by simpa [next] using hn) θ hθ).1.le, (chord_inside B z _ hz (by simpa [next] using hn) θ hθ).2.le⟩
      by_cases htδ : T ≤ δ
      · have he (i : Fin 3) : EqOn
            (fun t => cutChord δ 1 z (increment B δ z e) t i)
            (fun t => trajectory B δ z (e::w) t i) (uIcc 0 T) := by
          intro t ht; rw [uIcc_of_le hT] at ht; have ht' : t ≤ δ := ht.2.trans htδ; have hp : max (t/δ) 0 ≤ 1 := max_le ((div_le_one hδ).mpr ht') (by norm_num); simp [trajectory,hn,ht',cutChord,cutParameter,min_eq_left hp]
        have heh : EqOn
            (fun t => (sourceMap B (cutChord δ 1 z (increment B δ z e) t)) 0)
            (fun t => (sourceMap B (trajectory B δ z (e::w) t)) 0) (uIcc 0 T) := by
          intro t ht; simp only [sourceMap,Matrix.cons_val_zero]; exact congrArg (fun x => B.source 0+x) (he 0 ht)
        have ha := cutChord_ac B δ 1 z (increment B δ z e) T; have hak := ha.1.congr heh; have hab := ha.2.congr (he 1); have hct := cutChord_original B δ 1 z (increment B δ z e) (by norm_num)
          (fun θ hθ => ⟨(chord_inside B z _ hz (by simpa [next] using hn) θ hθ).1.le, (chord_inside B z _ hz (by simpa [next] using hn) θ hθ).2.le⟩) T hT
        refine ⟨⟨hT,hak.continuousOn,hab.continuousOn,?_,hab.boundedVariationOn, Or.inl ⟨hak,hab⟩⟩,?_⟩
        · intro t ht
          rw [←heh ht]; exact hct.2.2.2.1 t ht
        · have hi : (∫ t in (0:ℝ)..T, trajectory B δ z (e::w) t 0 * deriv (fun s => trajectory B δ z (e::w) s 1) t) = ∫ t in (0:ℝ)..T, cutChord δ 1 z (increment B δ z e) t 0 * deriv (fun s => cutChord δ 1 z (increment B δ z e) s 1) t := by
            apply intervalIntegral.integral_congr_uIoo; intro t ht; rw [uIoo_of_le hT] at ht; have hd : deriv (fun s => trajectory B δ z (e::w) s 1) t = deriv (fun s => cutChord δ 1 z (increment B δ z e) s 1) t := by
              apply Filter.EventuallyEq.deriv_eq; filter_upwards [Iio_mem_nhds (ht.2.trans_le htδ)] with s hs; change s < δ at hs; have hp : max (s/δ) 0 ≤ 1 := max_le ((div_le_one hδ).mpr hs.le) (by norm_num); simp [trajectory,hn,hs.le,cutChord,cutParameter,min_eq_left hp]
            change trajectory B δ z (e::w) t 0 * deriv (fun s => trajectory B δ z (e::w) s 1) t = cutChord δ 1 z (increment B δ z e) t 0 * deriv (fun s => cutChord δ 1 z (increment B δ z e) s 1) t; rw [hd]; congr 1; exact (he 0 (by rw [uIcc_of_le hT]; exact ⟨ht.1.le,ht.2.le⟩)).symm
          rw [hi,cutChord_area δ 1 z _ (by norm_num) T]; exact congrArg (fun x => x-z 2)
            (he 2 (by rw [uIcc_of_le hT]; exact ⟨hT,le_rfl⟩))
      · have hS : 0 ≤ T-δ := by linarith
        obtain ⟨hd,hi⟩ := ih (next B δ z e) hn (T-δ) hS; have hjoin : (sourceMap B (cutChord δ 1 z (increment B δ z e) δ)) 0 = (sourceMap B (trajectory B δ (next B δ z e) w 0)) 0 := by
          rw [trajectory_zero B δ hδ w _ hn]; simp [cutChord,cutParameter,next,ne_of_gt hδ]
        have hh := D5.S3.Quantum.Fibers.OriginalControlComposition.concatenate_original
          (nativeBase B) δ (T-δ)
          (fun t => (sourceMap B (cutChord δ 1 z (increment B δ z e) t)) 0)
          (fun t => cutChord δ 1 z (increment B δ z e) t 1)
          (fun t => (sourceMap B (trajectory B δ (next B δ z e) w t)) 0)
          (fun t => trajectory B δ (next B δ z e) w t 1) hc hd hjoin
        have heh := trajectory_cons_height B δ hδ e w z hn; have heb := trajectory_cons_coordinate B δ hδ e w z hn 1; have htime : δ+(T-δ)=T := by ring
        constructor
        · rw [heh,heb,←htime]
          exact hh.1
        · have hint := hh.2.2.2.2.2 (fun k => k-B.source 0)
            (continuous_id.sub continuous_const).continuousOn
          rw [htime,←heh,←heb] at hint; simp only [sourceMap,Matrix.cons_val_zero,add_sub_cancel_left] at hint; rw [cutChord_area δ 1 z _ (by norm_num) δ,hi] at hint; have hend : cutChord δ 1 z (increment B δ z e) δ = next B δ z e := by
            simp [cutChord,cutParameter,next,ne_of_gt hδ]
          rw [hend] at hint
          calc
            _ = next B δ z e 2-z 2+ (trajectory B δ (next B δ z e) w (T-δ) 2-next B δ z e 2) := hint
            _ = _ := by
              simp only [trajectory,ite_eq_left hn,ite_eq_right htδ]; ring
    · have he : trajectory B δ z (e::w) = cutChord δ (hitFraction B z (increment B δ z e)) z (increment B δ z e) := by
        funext t; simp [trajectory,hn,cutChord,cutParameter]
      rw [he]; exact ⟨cutChord_original B δ _ z _ (fraction_bounds B z _ hz).1.le
        (dead_chord_closed B z _ hz (by simpa [next] using hn)) T hT,
        cutChord_area δ _ z _ (fraction_bounds B z _ hz).1.le T⟩
/-- The two executed controls retain their original elapsed cell durations. -/
def command (B : Model) (n : ℕ) (w : Fin (n^3) → SignPair) (t : ℝ) : Triple := trajectory B (mesh n) 0 (List.ofFn w) t
/-- The ordinary chronological integral of the executed controls. -/
def commandArea (B : Model) (n : ℕ) (w : Fin (n^3) → SignPair) (t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, command B n w s 0 * deriv (fun x => command B n w x 1) s
/-- The actual held state uses the integral, in both actual phase circles. -/
def heldState (B : Model) (n : ℕ) (w : Fin (n^3) → SignPair) (t : ℝ) : ℝ × AddCircle (2*Real.pi) × AddCircle (2*Real.pi) := physicalState B ![command B n w t 0,command B n w t 1,commandArea B n w t]
/-- First contact with either actual height wall. -/
def zeta (B : Model) (n : ℕ) (w : Fin (n^3) → SignPair) : ℝ := sInf {t : ℝ | 0 ≤ t ∧ ((heldState B n w t).1 = B.l ∨ (heldState B n w t).1 = B.u)}
/-- The unreweighted uniform law on all independent sign-pair words. -/
def tailProbability (B : Model) (n : ℕ) (t : ℝ) : ℝ := (1/4:ℝ)^(n^3) * ∑ w : Fin (n^3) → SignPair, if t < zeta B n w then 1 else 0
def excessExpectation (B : Model) (n : ℕ) (R : ℝ) : ℝ := (1/4:ℝ)^(n^3) * ∑ w : Fin (n^3) → SignPair, max (zeta B n w-R) 0
theorem actual_state_bridge (B : Model) (n : ℕ) (hn : 0 < mesh n)
    (w : Fin (n^3) → SignPair) (t : ℝ) (ht : 0 ≤ t) :
    commandArea B n w t = command B n w t 2 ∧
    heldState B n w t = physicalState B (command B n w t) := by
  have hz : Alive B 0 := by simpa [Alive,sourceMap] using B.source_height
  have ha := (trajectory_original_area B (mesh n) hn (List.ofFn w) 0 hz t ht).2; have he : commandArea B n w t = command B n w t 2 := by
    simpa [commandArea,command] using ha
  refine ⟨he,?_⟩; rw [heldState,he]; congr 1
  ext i
  fin_cases i <;> simp
private theorem actual_lifetime_bridge (B : Model) (n : ℕ) (hn : 0 < mesh n)
    (w : Fin (n^3) → SignPair) :
    zeta B n w = lifetime B (mesh n) 0 (List.ofFn w) := by
  have hz : Alive B 0 := by simpa [Alive,sourceMap] using B.source_height
  have hs : {t : ℝ | 0 ≤ t ∧ ((heldState B n w t).1 = B.l ∨ (heldState B n w t).1 = B.u)} = {t : ℝ | 0 ≤ t ∧ ((sourceMap B (trajectory B (mesh n) 0 (List.ofFn w) t)) 0 = B.l ∨ (sourceMap B (trajectory B (mesh n) 0 (List.ofFn w) t)) 0 = B.u)} := by
    ext t
    by_cases ht : 0 ≤ t
    · simp only [Set.mem_setOf_eq]
      rw [(actual_state_bridge B n hn w t ht).2]; rfl
    · simp only [mem_setOf_eq,ht,false_and]
  unfold zeta; rw [hs]; exact firstWallTime_eq_lifetime B (mesh n) hn (List.ofFn w) 0 hz
private theorem actual_law_bridge (B : Model) (n : ℕ) (hn : 0 < mesh n) : tailProbability B n = nativeProbability B n ∧ excessExpectation B n = nativeExcess B n := by
  constructor
  · funext t
    unfold tailProbability nativeProbability lifetimeProbability; rw [wordMean_uniform]
    simp_rw [actual_lifetime_bridge B n hn]
  · funext R
    unfold excessExpectation nativeExcess excessMean; rw [wordMean_uniform]
    simp_rw [actual_lifetime_bridge B n hn]
/-- Uniform full-lifetime estimates for the actual finite native command law. -/
theorem actual_lifetime_estimates (B : Model) : ∃ h M : ℝ, ∃ n₀ : ℕ, 0 < h ∧ 0 < M ∧ 1 ≤ n₀ ∧ ∀ n ≥ n₀, (∀ t : ℝ, 0 ≤ t → tailProbability B n t ≤ (1/2:ℝ)^⌊max (t-1) 0/h⌋₊) ∧ (∀ R : ℝ, 1 ≤ R → excessExpectation B n R ≤ 2*h*(1/2:ℝ)^⌊(R-1)/h⌋₊) ∧ (∀ w : Fin (n^3) → SignPair, 0 < zeta B n w ∧ zeta B n w ≤ ((n^3:ℕ)+1:ℝ)*mesh n ∧ ∀ T : ℝ, 0 ≤ T → D5.S3.Quantum.Fibers.OriginalControlComposition.OriginalControl (nativeBase B) T
              (fun t => (heldState B n w t).1)
              (fun t => command B n w t 1) ∧
            commandArea B n w T = command B n w T 2 ∧
            heldState B n w T = physicalState B (command B n w T)) := by
  obtain ⟨h,M,n₀,hh,hM,hest⟩ := finite_law_estimates B; obtain ⟨n₁,hn₁⟩ := mesh_eventually_small 1 (by norm_num); refine ⟨h,M,max (max n₀ n₁) 1,hh,hM,le_max_right _ _,?_⟩; intro n hn; have hn₀ : n₀ ≤ n := (le_max_left n₀ n₁).trans ((le_max_left _ _).trans hn); have hn' : n₁ ≤ n := (le_max_right n₀ n₁).trans ((le_max_left _ _).trans hn); have hδ := (hn₁ n hn').1; have hb := actual_law_bridge B n hδ; obtain ⟨htail,hexcess⟩ := hest n hn₀; refine ⟨?_,?_,?_⟩
  · simpa only [hb.1] using htail
  · simpa only [hb.2] using hexcess
  · intro w
    have hz : Alive B 0 := by simpa [Alive,sourceMap] using B.source_height
    rw [actual_lifetime_bridge B n hδ w]; refine ⟨lifetime_pos B (mesh n) hδ (List.ofFn w) 0 hz,?_,?_⟩
    · simpa using lifetime_le_duration B (mesh n) hδ.le (List.ofFn w) 0 hz
    · intro T hT
      have ho := (trajectory_original_area B (mesh n) hδ (List.ofFn w) 0 hz T hT).1; have hk : (fun t => (heldState B n w t).1) = (fun t => (sourceMap B (command B n w t)) 0) := rfl; rw [hk]; exact ⟨ho,(actual_state_bridge B n hδ w T hT).1, (actual_state_bridge B n hδ w T hT).2⟩
end D5.S3.Analytic.Probability.NativeCommandLifetime
