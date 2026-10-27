/- GID: D5/S3/Quantum/Fibers/OriginalControlMarkedJump
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalControlMarkedJump
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous time and mode loss from the original double-wall jumps. -/

import D5.S3.Quantum.Fibers.OriginalControlComposition
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Measure.WithDensity

/-! The marked output retains terminal success and every time and mode of first loss. -/
noncomputable section
namespace D5.S3.Quantum.Fibers.OriginalControlMarkedJump
open Set Filter Topology MeasureTheory intervalIntegral
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The original double-wall probabilities, with mode 13 in coordinate four. -/
def p (c k : ℝ) : Fin 5 → ℝ :=
  FiniteRectangleTransport.probability (c,c,1-2*c) k

private theorem p_explicit (c k : ℝ) : p c k = ![k,c-k,1-2*c,c-k,k] := by
  funext i
  fin_cases i <;> simp [p,FiniteRectangleTransport.probability] <;> ring

private def originalProbability (c k : ℝ) (hc : c < 1 / 2) (hk : k ∈ Ioo 0 c) :
    InteriorProbabilityPhaseFiber.InteriorProbability 4 :=
  FiniteRectangleTransport.fiberProbability (c,c,1-2*c) k (by
    change 0 < 1-2*c ∧ 1-2*c < 1 ∧ 0 < c ∧ c < 1-(1-2*c) ∧
      0 < c ∧ c < 1-(1-2*c)
    refine ⟨by linarith,by linarith [hk.1,hk.2],by linarith [hk.1,hk.2],
      by linarith [hk.1,hk.2],by linarith [hk.1,hk.2],by linarith [hk.1,hk.2]⟩) (by
    have he : FiniteRectangleTransport.lower (c,c,1-2*c)=0 := by
      dsimp [FiniteRectangleTransport.lower]
      ring_nf
      simp
    simpa [he,FiniteRectangleTransport.upper] using hk)

theorem p_pos (c k : ℝ) (hc : c < 1 / 2) (hk : k ∈ Ioo 0 c) (i : Fin 5) :
    0 < p c k i := (originalProbability c k hc hk).positive i

private theorem p_sum (c k : ℝ) (hc : c < 1 / 2) (hk : k ∈ Ioo 0 c) :
    ∑ i, p c k i = 1 := (originalProbability c k hc hk).total

/-- The original fixed preparation, including its unknown common phase and parity. -/
private def sourceCoordinates (c a beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ) : Fin 5 → ℂ :=
  fun i => if i = 2 then (Real.sqrt (1-2*c) : ℂ) else
    (Real.sqrt (p c a i) : ℂ) * Complex.exp ((-beta : ℝ) * Complex.I) *
      Complex.exp ((-theta i : ℝ) * Complex.I) *
      (if i = 1 ∨ i = 3 then (-1 : ℂ)^m else 1)

/-- The fixed plus and minus vectors of the original preparation. -/
def preparedPlus (theta : Fin 5 → ℝ) (i : Fin 5) : ℂ :=
  if i=0 ∨ i=4 then Complex.exp ((-theta i : ℝ)*Complex.I)/(Real.sqrt 2 : ℂ) else 0

def preparedMinus (theta : Fin 5 → ℝ) (i : Fin 5) : ℂ :=
  if i=1 ∨ i=3 then Complex.exp ((-theta i : ℝ)*Complex.I)/(Real.sqrt 2 : ℂ) else 0

/-- The original input: sqrt(Z)e2+exp(-i beta)(sqrt(2a)U+ + (-1)^m sqrt(2(c-a))U-). -/
def source (c a beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ) (i : Fin 5) : ℂ :=
  (if i=2 then (Real.sqrt (1-2*c) : ℂ) else 0) +
    Complex.exp ((-beta : ℝ)*Complex.I) *
      ((Real.sqrt (2*a) : ℂ)*preparedPlus theta i +
        (-1 : ℂ)^m*(Real.sqrt (2*(c-a)) : ℂ)*preparedMinus theta i)

private theorem source_coordinates (c a beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ) :
    source c a beta m theta=sourceCoordinates c a beta m theta := by
  have ht : (Real.sqrt (2:ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  funext i
  fin_cases i <;> simp [source,sourceCoordinates,preparedPlus,preparedMinus,p_explicit,
    Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num),Complex.ofReal_mul] <;>
    field_simp [ht]

theorem source_diagonal (c a beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (hc : c < 1 / 2) (ha : a ∈ Ioo 0 c) (i : Fin 5) :
    Complex.normSq (source c a beta m theta i) = p c a i := by
  rw [source_coordinates,Complex.normSq_eq_norm_sq]
  by_cases hi : i = 2
  · subst i
    simp [sourceCoordinates,p_explicit,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by linarith : 0 ≤ 1-2*c)]
  · simp only [sourceCoordinates,ite_eq_right hi,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      Complex.norm_exp_ofReal_mul_I, mul_one]
    split_ifs <;> simp [norm_zpow,Real.sq_sqrt (p_pos c a hc ha i).le]

/-- The successful diagonal Kraus action at constant transported phase. -/
def live (c a k S : ℝ) (psi : Fin 5 → ℂ) : Fin 5 → ℂ :=
  fun i => (Real.sqrt S : ℂ) * (Real.sqrt (p c k i / p c a i) : ℂ) * psi i

/-- The rank-one jump's absorbing amplitude, before taking its squared norm. -/
def jump (c a k S : ℝ) (g : Fin 5 → ℝ) (psi : Fin 5 → ℂ) (i : Fin 5) : ℂ :=
  (Real.sqrt (g i) : ℂ) * live c a k S psi i

theorem source_jump_density (c a k S beta : ℝ) (m : ℤ)
    (theta : Fin 5 → ℝ) (g : Fin 5 → ℝ)
    (hc : c < 1 / 2) (ha : a ∈ Ioo 0 c) (hk : k ∈ Ioo 0 c)
    (hS : 0 ≤ S) (hg : ∀ i, 0 ≤ g i) (i : Fin 5) :
    Complex.normSq (jump c a k S g (source c a beta m theta) i) = g i*S*p c k i := by
  simp only [jump,live,Complex.normSq_mul,Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (hg i),Real.mul_self_sqrt hS,
    Real.mul_self_sqrt (div_nonneg (p_pos c k hc hk i).le (p_pos c a hc ha i).le),
    source_diagonal c a beta m theta hc ha]
  field_simp [(p_pos c a hc ha i).ne']

/-- The original successful Kraus matrix on the five live modes. -/
def successfulKraus (c a k S : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal (fun i => (Real.sqrt S : ℂ)*(Real.sqrt (p c k i/p c a i) : ℂ))

/-- The original absorbing row for one retained mode. -/
def absorbingRow (g : Fin 5 → ℝ) (i : Fin 5) : Matrix (Fin 1) (Fin 5) ℂ :=
  fun _ j => if j=i then (Real.sqrt (g i) : ℂ) else 0

/-- The specified jump is the absorbing row times the actual successful matrix. -/
def jumpKraus (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5) :
    Matrix (Fin 1) (Fin 5) ℂ :=
  absorbingRow g i * successfulKraus c a k S

theorem successful_action (c a k S : ℝ) (psi : Fin 5 → ℂ) :
    (successfulKraus c a k S) *ᵥ psi=live c a k S psi := by
  ext i
  simp [successfulKraus,Matrix.mulVec,live]

theorem jump_action (c a k S : ℝ) (g : Fin 5 → ℝ)
    (psi : Fin 5 → ℂ) (i : Fin 5) :
    (jumpKraus c a k S g i *ᵥ psi) 0=jump c a k S g psi i := by
  rw [jumpKraus,← Matrix.mulVec_mulVec,successful_action]
  simp [Matrix.mulVec,absorbingRow,jump,dotProduct,ite_mul]

theorem source_live_mass (c a k S beta : ℝ) (m : ℤ)
    (theta : Fin 5 → ℝ) (hc : c < 1 / 2) (ha : a ∈ Ioo 0 c)
    (hk : k ∈ Ioo 0 c) (hS : 0 ≤ S) :
    (∑ i,Complex.normSq ((successfulKraus c a k S *ᵥ source c a beta m theta) i)) = S := by
  rw [successful_action]
  have he (i : Fin 5) : Complex.normSq (live c a k S (source c a beta m theta) i)=S*p c k i := by
    simpa [jump] using source_jump_density c a k S beta m theta (fun _ => 1)
      hc ha hk hS (fun _ => zero_le_one) i
  simp_rw [he]
  rw [← Finset.mul_sum,p_sum c k hc hk,mul_one]

/-- One affine leg, with its actual positive duration and both original height walls. -/
structure Leg where
  c : ℝ
  x : ℝ
  y : ℝ
  duration : ℝ
  c_lt : c < 1 / 2
  x_pos : 0 < x
  x_lt : x < c
  y_pos : 0 < y
  y_lt : y < c
  duration_pos : 0 < duration

namespace Leg

open D5.S3.Quantum.Fibers.FiniteRectangleTransport

def speed (L : Leg) : ℝ := (L.y-L.x)/L.duration

def height (L : Leg) (t : ℝ) : ℝ := L.x+L.speed*t

def hazard (L : Leg) (t : ℝ) : ℝ :=
  max L.speed 0/L.height t + max (-L.speed) 0/(L.c-L.height t)

def survival (L : Leg) (t : ℝ) : ℝ := Real.exp (-(∫ u in (0:ℝ)..t, L.hazard u))

/-- This is the original logarithmic rate; it is not a prescribed loss density. -/
def jumpRate (L : Leg) (t : ℝ) (i : Fin 5) : ℝ :=
  L.hazard t - deriv (fun u => Real.log (p L.c (L.height u) i)) t

def density (L : Leg) (t : ℝ) (i : Fin 5) : ℝ :=
  L.jumpRate t i * L.survival t * p L.c (L.height t) i

theorem height_bounds (L : Leg) (t : ℝ) (ht : t ∈ Icc 0 L.duration) :
    L.height t ∈ Ioo 0 L.c := by
  have hθ : 0 ≤ t/L.duration ∧ t/L.duration ≤ 1 :=
    ⟨div_nonneg ht.1 L.duration_pos.le,(div_le_one L.duration_pos).mpr ht.2⟩
  have he : L.height t = (1-t/L.duration)*L.x+(t/L.duration)*L.y := by
    dsimp [height,speed]; ring
  rw [he]
  exact convex_Ioo (𝕜:=ℝ) 0 L.c ⟨L.x_pos,L.x_lt⟩ ⟨L.y_pos,L.y_lt⟩
    (by linarith) hθ.1 (by ring)

theorem height_deriv (L : Leg) (t : ℝ) : HasDerivAt L.height L.speed t := by
  change HasDerivAt (fun u : ℝ => L.x+L.speed*u) L.speed t
  simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul L.speed).const_add L.x

private theorem height_cont (L : Leg) : Continuous L.height := by
  exact continuous_iff_continuousAt.mpr (fun t => (L.height_deriv t).continuousAt)

theorem hazard_cont (L : Leg) : ContinuousOn L.hazard (Icc 0 L.duration) := by
  apply ContinuousOn.add
  · exact continuousOn_const.div L.height_cont.continuousOn
      (fun t ht => (L.height_bounds t ht).1.ne')
  · exact continuousOn_const.div (continuousOn_const.sub L.height_cont.continuousOn)
      (fun t ht => (sub_pos.mpr (L.height_bounds t ht).2).ne')

private theorem survival_formula (L : Leg) (t : ℝ) (ht : t ∈ Icc 0 L.duration) :
    L.survival t = if L.x ≤ L.y then L.x/L.height t
      else (L.c-L.x)/(L.c-L.height t) := by
  have hsub : Icc 0 t ⊆ Icc 0 L.duration := Icc_subset_Icc le_rfl ht.2
  have hi : IntervalIntegrable L.hazard volume 0 t :=
    (L.hazard_cont.mono hsub).intervalIntegrable_of_Icc ht.1
  have hk : ∀ u ∈ Icc 0 t, 0 < L.height u := fun u hu => (L.height_bounds u (hsub hu)).1
  have hck : ∀ u ∈ Icc 0 t, 0 < L.c-L.height u :=
    fun u hu => sub_pos.mpr (L.height_bounds u (hsub hu)).2
  by_cases hxy : L.x ≤ L.y
  · have hv : 0 ≤ L.speed := div_nonneg (sub_nonneg.mpr hxy) L.duration_pos.le
    have hh : L.hazard = fun u => L.speed/L.height u := by
      funext u; simp [hazard,max_eq_left hv,max_eq_right (neg_nonpos.mpr hv)]
    have hlog : (∫ u in (0:ℝ)..t,L.hazard u)=Real.log (L.height t)-Real.log L.x := by
      have hz : L.height 0 = L.x := by simp [height]
      rw [← hz]
      apply integral_eq_sub_of_hasDerivAt_of_le ht.1
      · exact (L.height_cont.continuousOn.log (fun u hu => (hk u hu).ne'))
      · intro u hu
        simpa [hh] using (L.height_deriv u).log (hk u ⟨hu.1.le,hu.2.le⟩).ne'
      · exact hi
    rw [survival,hlog,ite_eq_left hxy]
    rw [neg_sub,Real.exp_sub,Real.exp_log L.x_pos,Real.exp_log (hk t ⟨ht.1,le_rfl⟩)]
  · have hv : L.speed ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (le_of_not_ge hxy)) L.duration_pos.le
    have hh : L.hazard = fun u => -L.speed/(L.c-L.height u) := by
      funext u; simp [hazard,max_eq_right hv,max_eq_left (neg_nonneg.mpr hv)]
    have hlog : (∫ u in (0:ℝ)..t,L.hazard u)=
        Real.log (L.c-L.height t)-Real.log (L.c-L.x) := by
      have hz : L.height 0 = L.x := by simp [height]
      rw [← hz]
      apply integral_eq_sub_of_hasDerivAt_of_le ht.1
      · exact (continuousOn_const.sub L.height_cont.continuousOn).log
          (fun u hu => (hck u hu).ne')
      · intro u hu
        simpa [hh] using ((L.height_deriv u).const_sub L.c).log
          (hck u ⟨hu.1.le,hu.2.le⟩).ne'
      · exact hi
    rw [survival,hlog,ite_eq_right hxy]
    rw [neg_sub,Real.exp_sub,Real.exp_log (sub_pos.mpr L.x_lt),
      Real.exp_log (hck t ⟨ht.1,le_rfl⟩)]

private theorem probability_deriv (L : Leg) (t : ℝ) (i : Fin 5) :
    HasDerivAt (fun u => p L.c (L.height u) i)
      (FiniteRectangleTransport.direction i*L.speed) t := by
  exact probability_derivative (L.c,L.c,1-2*L.c) L.height L.speed t
    (L.height_deriv t) i

private theorem jumpRate_formula (L : Leg) (t : ℝ) (ht : t ∈ Icc 0 L.duration)
    (i : Fin 5) : L.jumpRate t i = L.hazard t -
      FiniteRectangleTransport.direction i*L.speed/p L.c (L.height t) i := by
  rw [jumpRate,((L.probability_deriv t i).log
    (p_pos L.c (L.height t) L.c_lt (L.height_bounds t ht) i).ne').deriv]

theorem jumpRate_nonneg (L : Leg) (t : ℝ) (ht : t ∈ Icc 0 L.duration)
    (i : Fin 5) : 0 ≤ L.jumpRate t i := by
  have hk := L.height_bounds t ht
  have hp : 0 < L.c-L.height t := sub_pos.mpr hk.2
  rw [L.jumpRate_formula t ht i]
  by_cases hv : 0 ≤ L.speed
  · have hh : L.hazard t = L.speed/L.height t := by
      simp [hazard,max_eq_left hv,max_eq_right (neg_nonpos.mpr hv)]
    rw [hh,p_explicit]
    have h0 : 0 ≤ L.speed/L.height t := div_nonneg hv hk.1.le
    have h1 : 0 ≤ L.speed/(L.c-L.height t) := div_nonneg hv hp.le
    fin_cases i <;> simp [FiniteRectangleTransport.direction,neg_div] <;> linarith
  · have hv' : L.speed ≤ 0 := le_of_not_ge hv
    have hh : L.hazard t = -L.speed/(L.c-L.height t) := by
      simp [hazard,max_eq_right hv',max_eq_left (neg_nonneg.mpr hv')]
    rw [hh,p_explicit]
    have h0 : L.speed/L.height t ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv' hk.1.le
    have h1 : L.speed/(L.c-L.height t) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv' hp.le
    fin_cases i <;> simp [FiniteRectangleTransport.direction,neg_div] <;> linarith

private theorem rational_survival_deriv (L : Leg) (t : ℝ)
    (ht : t ∈ Icc 0 L.duration) :
    HasDerivAt (fun u => if L.x ≤ L.y then L.x/L.height u
      else (L.c-L.x)/(L.c-L.height u))
      (-L.hazard t*(if L.x ≤ L.y then L.x/L.height t
        else (L.c-L.x)/(L.c-L.height t))) t := by
  have hk := L.height_bounds t ht
  by_cases hxy : L.x ≤ L.y
  · have hv : 0 ≤ L.speed := div_nonneg (sub_nonneg.mpr hxy) L.duration_pos.le
    simp only [ite_eq_left hxy]
    convert (hasDerivAt_const t L.x).div (L.height_deriv t) hk.1.ne' using 1
    dsimp [hazard]
    rw [max_eq_left hv,max_eq_right (neg_nonpos.mpr hv)]
    field_simp [hk.1.ne']
    ring
  · have hv : L.speed ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (le_of_not_ge hxy)) L.duration_pos.le
    simp only [ite_eq_right hxy]
    convert (hasDerivAt_const t (L.c-L.x)).div
      ((L.height_deriv t).const_sub L.c) (sub_pos.mpr hk.2).ne' using 1
    dsimp [hazard]
    rw [max_eq_right hv,max_eq_left (neg_nonneg.mpr hv)]
    field_simp [(sub_pos.mpr hk.2).ne']
    ring

private theorem survival_cont (L : Leg) : ContinuousOn L.survival (Icc 0 L.duration) := by
  have hr : ContinuousOn (fun u => if L.x ≤ L.y then L.x/L.height u
      else (L.c-L.x)/(L.c-L.height u)) (Icc 0 L.duration) := by
    by_cases hxy : L.x ≤ L.y
    · simp only [ite_eq_left hxy]
      exact continuousOn_const.div L.height_cont.continuousOn
        (fun t ht => (L.height_bounds t ht).1.ne')
    · simp only [ite_eq_right hxy]
      exact continuousOn_const.div (continuousOn_const.sub L.height_cont.continuousOn)
        (fun t ht => (sub_pos.mpr (L.height_bounds t ht).2).ne')
  exact hr.congr (fun t ht => L.survival_formula t ht)

private theorem density_cont (L : Leg) (i : Fin 5) :
    ContinuousOn (fun t => L.density t i) (Icc 0 L.duration) := by
  have hp : Continuous (fun t => p L.c (L.height t) i) :=
    continuous_iff_continuousAt.mpr (fun t => (L.probability_deriv t i).continuousAt)
  have hr : ContinuousOn (fun t => L.jumpRate t i) (Icc 0 L.duration) := by
    exact (L.hazard_cont.sub (continuousOn_const.div hp.continuousOn
      (fun t ht => (p_pos L.c (L.height t) L.c_lt (L.height_bounds t ht) i).ne'))).congr
      (fun t ht => L.jumpRate_formula t ht i)
  exact (hr.mul L.survival_cont).mul hp.continuousOn

private theorem integrated_loss (L : Leg) (i : Fin 5) :
    (∫ t in (0:ℝ)..L.duration,L.density t i) =
      p L.c L.x i - L.survival L.duration*p L.c L.y i := by
  let R : ℝ → ℝ := fun u => if L.x ≤ L.y then L.x/L.height u
    else (L.c-L.x)/(L.c-L.height u)
  have hr : ContinuousOn R (Icc 0 L.duration) := by
    apply L.survival_cont.congr
    intro t ht
    exact (L.survival_formula t ht).symm
  have hp : Continuous (fun t => p L.c (L.height t) i) :=
    continuous_iff_continuousAt.mpr (fun t => (L.probability_deriv t i).continuousAt)
  have hid : (∫ t in (0:ℝ)..L.duration, -L.density t i) =
      R L.duration*p L.c (L.height L.duration) i-R 0*p L.c (L.height 0) i := by
    apply integral_eq_sub_of_hasDerivAt_of_le L.duration_pos.le (hr.mul hp.continuousOn)
    · intro t ht
      have ht' : t ∈ Icc 0 L.duration := ⟨ht.1.le,ht.2.le⟩
      have hd := (L.rational_survival_deriv t ht').mul (L.probability_deriv t i)
      convert hd using 1
      rw [density,L.jumpRate_formula t ht',L.survival_formula t ht']
      field_simp [(p_pos L.c (L.height t) L.c_lt (L.height_bounds t ht') i).ne']
      ring
    · exact (L.density_cont i).neg.intervalIntegrable_of_Icc L.duration_pos.le
  have he : L.height L.duration = L.y := by
    dsimp [height,speed]
    field_simp [L.duration_pos.ne']
    ring
  have hz : L.height 0 = L.x := by simp [height]
  have hR0 : R 0 = 1 := by
    dsimp [R]
    rw [hz]
    split_ifs <;> field_simp [L.x_pos.ne',(sub_pos.mpr L.x_lt).ne']
  rw [intervalIntegral.integral_neg,he,hz,hR0,one_mul,
    show R L.duration = L.survival L.duration from
      (L.survival_formula L.duration ⟨L.duration_pos.le,le_rfl⟩).symm] at hid
  linarith

private theorem density_nonneg (L : Leg) (t : ℝ) (ht : t ∈ Icc 0 L.duration)
    (i : Fin 5) : 0 ≤ L.density t i := by
  exact mul_nonneg (mul_nonneg (L.jumpRate_nonneg t ht i) (Real.exp_pos _).le)
    (p_pos L.c (L.height t) L.c_lt (L.height_bounds t ht) i).le

private theorem original_regularity (L : Leg) (chi : ℝ) :
    OriginalControlComposition.OriginalControl (L.c,L.c,1-2*L.c)
      L.duration L.height (fun _ => chi) ∧
    AbsolutelyContinuousOnInterval L.height 0 L.duration ∧
    OriginalControlComposition.FiniteC1Control L.duration L.height (fun _ => chi) := by
  have hLip : LipschitzWith ‖L.speed‖₊ L.height := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [Real.dist_eq,coe_nnnorm,Real.norm_eq_abs]
    rw [show L.height s-L.height t=L.speed*(s-t) by dsimp [height]; ring,abs_mul]
  have hAC := hLip.lipschitzOnWith.absolutelyContinuousOnInterval (a:=0) (b:=L.duration)
  have hchi := (LipschitzWith.const chi).lipschitzOnWith.absolutelyContinuousOnInterval
    (a:=0) (b:=L.duration)
  have hfinite : OriginalControlComposition.FiniteC1Control L.duration L.height (fun _ => chi) := by
    refine ⟨1,fun j : ℕ => (j:ℝ)*L.duration,?_,by simp,by simp,?_⟩
    · intro i j hij
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) L.duration_pos.le
    · intro j hj
      refine ⟨fun _ => L.speed,fun _ => 0,continuousOn_const,continuousOn_const,?_⟩
      intro t ht
      exact ⟨L.height_deriv t,hasDerivAt_const t chi⟩
  refine ⟨⟨L.duration_pos.le,L.height_cont.continuousOn,continuousOn_const,?_,
    hchi.boundedVariationOn,Or.inl ⟨hAC,hchi⟩⟩,hAC,hfinite⟩
  intro t ht
  rw [uIcc_of_le L.duration_pos.le] at ht
  have hl : FiniteRectangleTransport.lower (L.c,L.c,1-2*L.c)=0 := by
    dsimp [FiniteRectangleTransport.lower]
    ring_nf
    simp
  simpa only [hl,FiniteRectangleTransport.upper,min_self] using L.height_bounds t ht

/-- Success, or exact time and original mode of first failure. -/
abbrev Record := Unit ⊕ (Fin 5 × ℝ)

def modeMeasure (L : Leg) (i : Fin 5) : Measure ℝ :=
  (volume.restrict (Ioc 0 L.duration)).withDensity
    (fun t => ENNReal.ofReal (L.density t i))

def markedLaw (L : Leg) : Measure Record :=
  ENNReal.ofReal (L.survival L.duration) • Measure.dirac (Sum.inl ()) +
    ∑ i : Fin 5, (L.modeMeasure i).map (fun t => Sum.inr (i,t))

private theorem modeMeasure_univ (L : Leg) (i : Fin 5) :
    L.modeMeasure i univ=ENNReal.ofReal
      (p L.c L.x i-L.survival L.duration*p L.c L.y i) := by
  rw [modeMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le L.duration_pos.le,L.integrated_loss i]
  · exact ((L.density_cont i).intervalIntegrable_of_Icc L.duration_pos.le).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact L.density_nonneg t ⟨ht.1.le,ht.2⟩ i

private theorem markedLaw_probability (L : Leg) : IsProbabilityMeasure L.markedLaw := by
  apply isProbabilityMeasure_iff.mpr
  have hnon (i : Fin 5) : 0 ≤ p L.c L.x i-L.survival L.duration*p L.c L.y i := by
    rw [← L.integrated_loss i]
    apply intervalIntegral.integral_nonneg L.duration_pos.le
    intro t ht
    exact L.density_nonneg t ht i
  have hsum : (∑ i,(p L.c L.x i-L.survival L.duration*p L.c L.y i))=
      1-L.survival L.duration := by
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,
      p_sum L.c L.x L.c_lt ⟨L.x_pos,L.x_lt⟩,
      p_sum L.c L.y L.c_lt ⟨L.y_pos,L.y_lt⟩,mul_one]
  have hS : 0 ≤ 1-L.survival L.duration := by
    rw [← hsum]
    exact Finset.sum_nonneg (fun i _ => hnon i)
  simp only [markedLaw,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
    Measure.dirac_apply_of_mem (mem_univ _),mul_one,Measure.finsetSum_apply,
    ]
  have hm (i : Fin 5) : Measurable (fun t : ℝ => (Sum.inr (i,t) : Record)) :=
    measurable_inr.comp (measurable_const.prodMk measurable_id)
  simp only [Measure.map_apply (hm _) MeasurableSet.univ,preimage_univ,L.modeMeasure_univ]
  have hSp : 0 ≤ L.survival L.duration := (Real.exp_pos _).le
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnon i),hsum,
    ← ENNReal.ofReal_add hSp hS]
  simp

private theorem markedLaw_apply (L : Leg) (E : Set Record) (hE : MeasurableSet E) :
    L.markedLaw E=(if Sum.inl () ∈ E then ENNReal.ofReal (L.survival L.duration) else 0)+
      ∑ i : Fin 5, ∫⁻ t in (Ioc 0 L.duration) ∩ {t | Sum.inr (i,t) ∈ E},
        ENNReal.ofReal (L.density t i) := by
  have hm (i : Fin 5) : Measurable (fun t : ℝ => (Sum.inr (i,t) : Record)) :=
    measurable_inr.comp (measurable_const.prodMk measurable_id)
  simp only [markedLaw,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
    Measure.dirac_apply' _ hE,Set.indicator_apply,Measure.finsetSum_apply]
  congr 1
  · split_ifs <;> simp_all
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Measure.map_apply (hm i) hE,modeMeasure,
      withDensity_apply _ (hE.preimage (hm i)),
      Measure.restrict_restrict (hE.preimage (hm i))]
    rw [inter_comm]
    rfl

private theorem modeMeasure_no_atoms (L : Leg) (i : Fin 5) (t : ℝ) :
    L.modeMeasure i {t}=0 := by
  change ((volume.restrict (Ioc 0 L.duration)).withDensity
    (fun u => ENNReal.ofReal (L.density u i))) {t}=0
  exact measure_singleton t

private theorem modeMeasure_outside (L : Leg) (i : Fin 5) :
    L.modeMeasure i (Ioc 0 L.duration)ᶜ=0 := by
  apply withDensity_absolutelyContinuous _ _
  simp

/-- On an actual affine original-control leg, the continuous marked measure is
normalized and agrees on every Borel record event with the original Kraus outputs.
The unknown preparation phase and parity are retained. -/
theorem affine_marked_probability (L : Leg) (chi beta : ℝ) (m : ℤ)
    (theta : Fin 5 → ℝ) :
    OriginalControlComposition.OriginalControl (L.c,L.c,1-2*L.c)
      L.duration L.height (fun _ => chi) ∧
    AbsolutelyContinuousOnInterval L.height 0 L.duration ∧
    OriginalControlComposition.FiniteC1Control L.duration L.height (fun _ => chi) ∧
    (∀ t : ℝ, ∀ i : Fin 5,
      (∫ u in (0:ℝ)..t,FiniteRectangleTransport.phaseWeight (L.c,L.c,1-2*L.c)
        (L.height u) i * deriv (fun _ : ℝ => chi) u)=0) ∧
    (∀ i : Fin 5, ∀ t : ℝ, L.modeMeasure i {t}=0) ∧
    (∀ i : Fin 5,L.modeMeasure i (Ioc 0 L.duration)ᶜ=0) ∧
    (∀ t ∈ Icc 0 L.duration,L.survival t = if L.x ≤ L.y then L.x/L.height t
      else (L.c-L.x)/(L.c-L.height t)) ∧
    IsProbabilityMeasure L.markedLaw ∧
    ∀ E : Set Record, MeasurableSet E →
      L.markedLaw E =
        (if Sum.inl () ∈ E then ENNReal.ofReal
          (∑ i, Complex.normSq ((successfulKraus L.c L.x L.y (L.survival L.duration) *ᵥ
            source L.c L.x beta m theta) i)) else 0) +
        ∑ i : Fin 5, ∫⁻ t in (Ioc 0 L.duration) ∩ {t | Sum.inr (i,t) ∈ E},
          ENNReal.ofReal (Complex.normSq
            ((jumpKraus L.c L.x (L.height t) (L.survival t) (L.jumpRate t) i *ᵥ
              source L.c L.x beta m theta) 0)) := by
  obtain ⟨ho,ha,hf⟩ := L.original_regularity chi
  refine ⟨ho,ha,hf,?_,L.modeMeasure_no_atoms,L.modeMeasure_outside,
    L.survival_formula,L.markedLaw_probability,?_⟩
  · intro t i
    simp
  intro E hE
  rw [source_live_mass L.c L.x L.y (L.survival L.duration) beta m theta
    L.c_lt ⟨L.x_pos,L.x_lt⟩ ⟨L.y_pos,L.y_lt⟩ (Real.exp_pos _).le,
    L.markedLaw_apply E hE]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply setLIntegral_congr_fun (measurableSet_Ioc.inter
    (hE.preimage (measurable_inr.comp (measurable_const.prodMk measurable_id))))
  intro t ht
  change ENNReal.ofReal (L.density t i)=ENNReal.ofReal
    (Complex.normSq ((jumpKraus L.c L.x (L.height t) (L.survival t) (L.jumpRate t) i *ᵥ
      source L.c L.x beta m theta) 0))
  rw [jump_action,source_jump_density L.c L.x (L.height t) (L.survival t)
    beta m theta (L.jumpRate t) L.c_lt ⟨L.x_pos,L.x_lt⟩
    (L.height_bounds t ⟨ht.1.1.le,ht.1.2⟩) (Real.exp_pos _).le
    (fun j => L.jumpRate_nonneg t ⟨ht.1.1.le,ht.1.2⟩ j)]
  rfl

end Leg
end D5.S3.Quantum.Fibers.OriginalControlMarkedJump
