/- GID: D5/S3/Quantum/Entanglement/ConcentratableEntanglement/TwoProductConcentratableEntanglement
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/ConcentratableEntanglement/TwoProductConcentratableEntanglement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prove real-order GCE monotone and submodular for literal coherent two-product states. -/

import D5.S3.Quantum.Entanglement.ConcentratableEntanglement.PhysicalTwoProductMoments
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Subsystem monotonicity and submodularity of the actual CFC GCE for literal complex two-product states. -/

noncomputable section
namespace D5.S3.Quantum.Entanglement.ConcentratableEntanglement.TwoProductConcentratableEntanglement

section
open scoped Classical

/-- Abstract convex four-point inequality, with no strictness needed. -/
private theorem mixed_le {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f)
    {x a b : ℝ} (hx : x ∈ s) (ht : x+a+b ∈ s) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    f (x+a) + f (x+b) ≤ f x + f (x+a+b) := by
  by_cases e : a+b=0
  · have ea : a=0 := by linarith
    have eb : b=0 := by linarith
    simp [ea,eb]
  have hd : 0 < a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm e)
  have hsum : a/(a+b) + b/(a+b) = 1 := by field_simp
  have eA : (b/(a+b)) • x + (a/(a+b)) • (x+a+b) = x+a := by
    simp only [smul_eq_mul]; field_simp; ring
  have eB : (a/(a+b)) • x + (b/(a+b)) • (x+a+b) = x+b := by
    simp only [smul_eq_mul]; field_simp; ring
  have A := hf.2 hx ht (div_nonneg hb hd.le) (div_nonneg ha hd.le) (by rw [add_comm]; exact hsum)
  have B := hf.2 hx ht (div_nonneg ha hd.le) (div_nonneg hb hd.le) hsum
  rw [eA,smul_eq_mul,smul_eq_mul] at A
  rw [eB,smul_eq_mul,smul_eq_mul] at B
  have hab := add_le_add A B
  calc
    _ ≤ _ := hab
    _ = _ := by linear_combination (f x + f (x+a+b))*hsum

variable {I : Type*} (w : I → ℝ)
private def mass (A : Finset I) := ∑ i ∈ A, w i

private theorem masked_moment_le (hn : ∀ i, 0 ≤ w i) {f : ℝ → ℝ} {s : Set ℝ}
    (hf : ConvexOn ℝ s f) (hs : ∀ A, mass w A ∈ s)
    (A B M : Finset I) :
    f (mass w (A∩M)) + f (mass w (B∩M)) ≤
      f (mass w ((A∩B)∩M)) + f (mass w ((A∪B)∩M)) := by
  let x := mass w ((A∩B)∩M)
  let a := mass w (A∩M) - x
  let b := mass w (B∩M) - x
  have hA : (A∩B)∩M ⊆ A∩M := by
    intro i hi
    simp only [Finset.mem_inter] at hi ⊢
    exact ⟨hi.1.1,hi.2⟩
  have hB : (A∩B)∩M ⊆ B∩M := by
    intro i hi
    simp only [Finset.mem_inter] at hi ⊢
    exact ⟨hi.1.2,hi.2⟩
  have ha : 0 ≤ a := sub_nonneg.mpr (Finset.sum_le_sum_of_subset_of_nonneg hA (fun i _ _ => hn i))
  have hb : 0 ≤ b := sub_nonneg.mpr (Finset.sum_le_sum_of_subset_of_nonneg hB (fun i _ _ => hn i))
  have hU : (A∩M) ∪ (B∩M) = (A∪B) ∩ M := by
    ext i
    simp only [Finset.mem_inter,Finset.mem_union]
    tauto
  have hI : (A∩M) ∩ (B∩M) = (A∩B) ∩ M := by
    ext i
    simp only [Finset.mem_inter]
    tauto
  have hmod := Finset.sum_union_inter (s₁ := A∩M) (s₂ := B∩M) (f := w)
  rw [hU,hI] at hmod
  change mass w ((A∪B)∩M) + x = mass w (A∩M) + mass w (B∩M) at hmod
  have eA : x+a = mass w (A∩M) := by dsimp [a]; ring
  have eB : x+b = mass w (B∩M) := by dsimp [b]; ring
  have eT : x+a+b = mass w ((A∪B)∩M) := by
    dsimp [a,b]
    exact (by linear_combination -hmod)
  have h := mixed_le hf (hs ((A∩B)∩M)) (by rw [eT]; exact hs _) ha hb
  rwa [eT,eA,eB] at h

/-- Mask bits outside the subsystem multiply numerator and denominator
by precisely the same power of two. -/
private theorem average_restriction (F : Finset I → ℝ) (S T : Finset I) (hst : S ⊆ T) :
    (∑ M ∈ T.powerset, F (S∩M)) / (2:ℝ)^T.card =
      (∑ U ∈ S.powerset, F U) / (2:ℝ)^S.card := by
  have aux (D : Finset I) (hd : Disjoint S D) :
      (∑ M ∈ (S∪D).powerset, F (S∩M)) = (2:ℝ)^D.card * (∑ U ∈ S.powerset, F U) := by
    induction D using Finset.induction_on with
    | empty =>
      simp only [Finset.union_empty, Finset.card_empty, pow_zero, one_mul]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.inter_eq_right.mpr (Finset.mem_powerset.mp hm)]
    | insert i D hi ih =>
      have his : i ∉ S := fun hiS => Finset.disjoint_left.mp hd hiS (Finset.mem_insert_self _ _)
      have hd' : Disjoint S D := by
        exact hd.mono_right (Finset.subset_insert _ _)
      have hlu : S ∪ insert i D = insert i (S∪D) := by
        ext j
        simp only [Finset.mem_union,Finset.mem_insert]
        tauto
      rw [hlu,Finset.sum_powerset_insert (by simp [his,hi])]
      have hc (M : Finset I) : S ∩ insert i M = S ∩ M := by
        ext j
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hj,h|h⟩
          · exact (his (h ▸ hj)).elim
          · exact ⟨hj,h⟩
        · exact fun ⟨hj,hm⟩ => ⟨hj,Or.inr hm⟩
      simp_rw [hc,ih hd',Finset.card_insert_of_notMem hi,pow_succ]
      ring
  let D := T \ S
  have hD : Disjoint S D := Finset.disjoint_sdiff
  have hu : S ∪ D = T := by
    rw [Finset.union_comm]
    exact Finset.sdiff_union_of_subset hst
  have hh := aux D hD
  rw [hu] at hh
  have hct : T.card = S.card + D.card := by
    rw [← Finset.card_union_of_disjoint hD, hu]
  rw [hh,hct,pow_add]
  have hn : (2:ℝ)^D.card ≠ 0 := by positivity
  field_simp

private def averageMoment (f : ℝ → ℝ) (S : Finset I) :=
    (∑ U ∈ S.powerset, f (mass w U)) / (2:ℝ)^S.card

private theorem averaged_moment_supermodular (hn : ∀ i, 0 ≤ w i) {f : ℝ → ℝ} {s : Set ℝ}
    (hf : ConvexOn ℝ s f) (hs : ∀ A, mass w A ∈ s) (A B : Finset I) :
    averageMoment w f A + averageMoment w f B ≤
      averageMoment w f (A∩B) + averageMoment w f (A∪B) := by
  let T := A∪B
  have ha : A ⊆ T := Finset.subset_union_left
  have hb : B ⊆ T := Finset.subset_union_right
  have hi : A∩B ⊆ T := Finset.inter_subset_left.trans ha
  unfold averageMoment
  rw [← average_restriction (fun U => f (mass w U)) A T ha,
      ← average_restriction (fun U => f (mass w U)) B T hb,
      ← average_restriction (fun U => f (mass w U)) (A∩B) T hi,
      ← average_restriction (fun U => f (mass w U)) (A∪B) T (by rfl)]
  rw [← add_div, ← add_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum fun M _ => masked_moment_le w hn hf hs A B M
end

section
open Set

private def radius (L : ℝ) := Real.exp (-(L/2))
private def minGapSq (c L : ℝ) := 1-4*c*(1-radius L)^2
private def gapSq (c L x : ℝ) := 1-4*c*(1-Real.exp (-x))*(1-Real.exp (-(L-x)))

/-- The squared gap of the two eigenvalues is a constant plus one square.
The phases of individual cuts have disappeared. -/
private theorem gap_square_identity (c L x : ℝ) :
    gapSq c L x = minGapSq c L + 16*c*radius L*(Real.sinh ((x-L/2)/2))^2 := by
  let t := (x-L/2)/2
  have eL : Real.exp (-x) = radius L * Real.exp (-t)^2 := by
    rw [radius,pow_two,← Real.exp_add,← Real.exp_add]
    congr 1
    dsimp [t]; ring
  have eR : Real.exp (-(L-x)) = radius L * Real.exp t^2 := by
    rw [radius,pow_two,← Real.exp_add,← Real.exp_add]
    congr 1
    dsimp [t]; ring
  have hmul : Real.exp (-t)*Real.exp t = 1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  have hsum : Real.exp (-t)^2 + Real.exp t^2 = 4 * Real.sinh t ^ 2 + 2 := by
    rw [Real.sinh_eq]
    linear_combination 2*hmul
  have h2 : Real.exp (-t)^2 * Real.exp t^2 = 1 := by
    rw [← mul_pow,hmul,one_pow]
  change gapSq c L x = minGapSq c L + 16*c*radius L*(Real.sinh t)^2
  unfold gapSq minGapSq
  rw [eL,eR]
  linear_combination 4*c*radius L*hsum - 4*c*(radius L)^2*h2

/-- The actual nonzero global norm controls the virtual midpoint as well
as physical cuts. The input lower bound is the reverse triangle estimate. -/
private theorem midpoint_nonnegative {N a L : ℝ} (hN : 0 < N) (ha : 0 ≤ a)
    (hL : 0 ≤ L) (bound : 2*a*(1-radius L) ≤ N) :
    0 ≤ minGapSq ((a/N)^2) L := by
  have hr : radius L ≤ 1 := by
    rw [radius, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hb : 0 ≤ 2*a*(1-radius L) := by positivity
  have hd : (2*a*(1-radius L))/N ≤ 1 := (div_le_one hN).mpr bound
  have hp : 0 ≤ (2*a*(1-radius L))/N := div_nonneg hb hN.le
  have hsq := pow_le_pow_left₀ hp hd 2
  have eq : ((2*a*(1-radius L))/N)^2 = 4*(a/N)^2*(1-radius L)^2 := by ring
  rw [eq,one_pow] at hsq
  unfold minGapSq
  linarith

private theorem gap_sq_le_one {c L x : ℝ} (hc : 0 ≤ c) (hx : x ∈ Icc 0 L) :
    gapSq c L x ≤ 1 := by
  have e₁ : Real.exp (-x) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith [hx.1])
  have e₂ : Real.exp (-(L-x)) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith [hx.2])
  unfold gapSq
  exact sub_le_self _ (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc)
    (sub_nonneg.mpr e₁)) (sub_nonneg.mpr e₂))

private def roundGap (g y : ℝ) := √(g+y^2)

private theorem roundGap_monotone (g : ℝ) : MonotoneOn (roundGap g) (Ici 0) := by
  intro x hx y _ h
  exact Real.sqrt_le_sqrt (add_le_add_right (pow_le_pow_left₀ hx h 2) _)

private theorem roundGap_convex {g : ℝ} (hg : 0 ≤ g) : ConvexOn ℝ univ (roundGap g) := by
  have repr (x : ℝ) : roundGap g x = ‖(⟨√g,x⟩ : ℂ)‖ := by
    rw [roundGap,Complex.norm_def,Complex.normSq_apply,← pow_two,Real.sq_sqrt hg,← pow_two]
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  simp only [repr]
  have combine : (⟨√g,a • x+b • y⟩ : ℂ) =
      a • (⟨√g,x⟩ : ℂ) + b • (⟨√g,y⟩ : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re,Complex.smul_re,smul_eq_mul]
      linear_combination -√g*hab
    · simp only [Complex.add_im,Complex.smul_im,smul_eq_mul]
  rw [combine]
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb,smul_eq_mul] using
    norm_add_le (a • (⟨√g,x⟩ : ℂ)) (b • (⟨√g,y⟩ : ℂ))

private theorem convex_comp_bounded {s t : Set ℝ} {f g : ℝ → ℝ} (hf : ConvexOn ℝ s f)
    (hg : ConvexOn ℝ t g) (hmono : MonotoneOn g t) (hmap : MapsTo f s t) :
    ConvexOn ℝ s (g ∘ f) := by
  refine ⟨hf.1,?_⟩
  intro x hx y hy a b ha hb hab
  have hx' := hmap hx
  have hy' := hmap hy
  exact (hmono (hmap (hf.1 hx hy ha hb hab)) (hg.1 hx' hy' ha hb hab)
    (hf.2 hx hy ha hb hab)).trans (hg.2 hx' hy' ha hb hab)
end

section
open Set

private def traceMoment (K t : ℝ) := ((1+t)/2)^K+((1-t)/2)^K

private theorem traceMoment_even (K t : ℝ) : traceMoment K (-t) = traceMoment K t := by
  unfold traceMoment
  rw [show (1:ℝ)+(-t)=1-t by ring,show (1:ℝ)-(-t)=1+t by ring,add_comm]

private theorem traceMoment_convex {K : ℝ} (hK : 1 ≤ K) :
    ConvexOn ℝ (Icc (-1:ℝ) 1) (traceMoment K) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  have P (z : ℝ) (hz : z ∈ Icc (-1:ℝ) 1) : (1+z)/2 ∈ Ici (0:ℝ) := by
    exact show 0 ≤ (1+z)/2 by linarith [hz.1]
  have Q (z : ℝ) (hz : z ∈ Icc (-1:ℝ) 1) : (1-z)/2 ∈ Ici (0:ℝ) := by
    exact show 0 ≤ (1-z)/2 by linarith [hz.2]
  have p := (convexOn_rpow hK).2 (P x hx) (P y hy) ha hb hab
  have q := (convexOn_rpow hK).2 (Q x hx) (Q y hy) ha hb hab
  have ep : a • ((1+x)/2) + b • ((1+y)/2) = (1+(a • x+b • y))/2 := by
    simp only [smul_eq_mul]; linear_combination hab/2
  have eq : a • ((1-x)/2) + b • ((1-y)/2) = (1-(a • x+b • y))/2 := by
    simp only [smul_eq_mul]; linear_combination hab/2
  rw [ep] at p
  rw [eq] at q
  simp only [traceMoment,smul_eq_mul,mul_add] at p q ⊢
  linarith

/-- Even convex spectral profiles are increasing on their positive half.
This proves the real-order moment monotonicity without differentiating at
a zero eigenvalue. -/
private theorem traceMoment_monotone {K : ℝ} (hK : 1 ≤ K) :
    MonotoneOn (traceMoment K) (Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  by_cases ey : y=0
  · have e : x=y := le_antisymm hxy (by linarith [hx.1])
    rw [e]
  have py : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm ey)
  let a := (x+y)/(2*y)
  let b := (y-x)/(2*y)
  have ha : 0 ≤ a := div_nonneg (add_nonneg hx.1 hy.1) (by positivity)
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hxy) (by positivity)
  have hab : a+b=1 := by dsimp [a,b]; field_simp; ring
  have harg : a • y + b • (-y) = x := by
    dsimp [a,b]; field_simp; ring
  have hy' : y∈Icc (-1:ℝ) 1 := ⟨by linarith [hy.1],hy.2⟩
  have hn' : -y∈Icc (-1:ℝ) 1 := ⟨by linarith [hy.2],by linarith [hy.1]⟩
  have H := (traceMoment_convex hK).2 hy' hn' ha hb hab
  simpa only [harg,traceMoment_even,← add_smul,hab,one_smul] using H

/-- Once the nonnegative one-variable hyperbolic profile is convex, the
actual gap and its real-order trace moment follow by monotone compositions. -/
private theorem spectral_profile_convex {K c L : ℝ} (hK : 1 ≤ K) (hc : 0 ≤ c)
    (hg : 0 ≤ minGapSq c L)
    (hshape : ConvexOn ℝ (Icc 0 L) (fun x => |Real.sinh ((x-L/2)/2)|)) :
    ConvexOn ℝ (Icc 0 L) (fun x => traceMoment K (√(gapSq c L x))) := by
  let B := 4*√(c*radius L)
  have hr : 0 ≤ c*radius L := mul_nonneg hc (Real.exp_nonneg _)
  have hB : 0 ≤ B := by positivity
  let Y := fun x : ℝ => B*|Real.sinh ((x-L/2)/2)|
  have hY : ConvexOn ℝ (Icc 0 L) Y := by
    simpa only [Y,smul_eq_mul] using hshape.smul hB
  have hYm : MapsTo Y (Icc 0 L) (Ici 0) := fun x _ => mul_nonneg hB (abs_nonneg _)
  have hRound := (roundGap_convex hg).subset (subset_univ _) (convex_Ici (0:ℝ))
  have H := convex_comp_bounded hY hRound (roundGap_monotone _) hYm
  have he (x : ℝ) : roundGap (minGapSq c L) (Y x) = √(gapSq c L x) := by
    rw [gap_square_identity,roundGap]
    congr 1
    dsimp [Y,B]
    rw [mul_pow,mul_pow,sq_abs,Real.sq_sqrt hr]
    ring
  have hgap : ConvexOn ℝ (Icc 0 L) (fun x => √(gapSq c L x)) := by
    simpa only [Function.comp_def,he] using H
  have hmap : MapsTo (fun x => √(gapSq c L x)) (Icc 0 L) (Icc (0:ℝ) 1) := by
    intro x hx
    refine ⟨Real.sqrt_nonneg _,?_⟩
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (gap_sq_le_one hc hx)
  have hf := (traceMoment_convex hK).subset (show Icc (0:ℝ) 1 ⊆ Icc (-1:ℝ) 1 from
    fun x hx => ⟨by linarith [hx.1],hx.2⟩) (convex_Icc 0 1)
  exact convex_comp_bounded hgap hf (traceMoment_monotone hK) hmap
end

section
open Set

private theorem sinh_convex_nonnegative : ConvexOn ℝ (Ici 0) Real.sinh := by
  apply convexOn_of_deriv2_nonneg' (convex_Ici _)
  · exact Real.differentiable_sinh.differentiableOn
  · rw [Real.deriv_sinh]
    exact Real.differentiable_cosh.differentiableOn
  · intro x hx
    change 0 ≤ deriv (deriv Real.sinh) x
    rw [Real.deriv_sinh,Real.deriv_cosh]
    exact Real.sinh_nonneg_iff.mpr hx

private theorem abs_sinh_shift_convex (L : ℝ) :
    ConvexOn ℝ (Icc 0 L) (fun x => |Real.sinh ((x-L/2)/2)|) := by
  let shift := fun x : ℝ => (x-L/2)/2
  have hd : ConvexOn ℝ (Icc 0 L) (fun x => |shift x|) := by
    refine ⟨convex_Icc _ _,?_⟩
    intro x _ y _ a b ha hb hab
    have e : shift (a • x+b • y) = a * shift x+b*shift y := by
      dsimp [shift]
      linear_combination L*hab/4
    change |shift (a • x+b • y)| ≤ a*|shift x|+b*|shift y|
    rw [e]
    simpa only [abs_mul,abs_of_nonneg ha,abs_of_nonneg hb] using
      abs_add_le (a*shift x) (b*shift y)
  have hm : MapsTo (fun x => |shift x|) (Icc 0 L) (Ici (0:ℝ)) :=
    fun x _ => (show 0 ≤ |shift x| from abs_nonneg _)
  have hh := convex_comp_bounded hd sinh_convex_nonnegative (Real.sinh_strictMono.monotone.monotoneOn _) hm
  have ev (x : ℝ) : Real.sinh |shift x| = |Real.sinh (shift x)| := by
    by_cases h : 0 ≤ shift x
    · rw [abs_of_nonneg h,abs_of_nonneg (Real.sinh_nonneg_iff.mpr h)]
    · have hn := le_of_not_ge h
      have hn' : Real.sinh (shift x) ≤ 0 := by
        simpa only [Real.sinh_zero] using Real.sinh_strictMono.monotone hn
      rw [abs_of_nonpos hn,Real.sinh_neg,abs_of_nonpos hn']
  simpa only [Function.comp_def,ev,shift] using hh

/-- Unconditional analytic core: every physically admissible coherent
two-product cut profile is convex at every real order above one. -/
private theorem all_real_convex_profile {K c L : ℝ} (hK : 1 ≤ K) (hc : 0 ≤ c)
    (hg : 0 ≤ minGapSq c L) :
    ConvexOn ℝ (Icc 0 L) (fun x => traceMoment K (√(gapSq c L x))) :=
  spectral_profile_convex hK hc hg (abs_sinh_shift_convex L)

open scoped Classical
/-- The normalized trace profile is supermodular on all overlapping
finite subsystems. Weights are the additive log-overlap coordinates;
the midpoint premise is discharged by the actual global norm. -/
private theorem averaged_cut_profile {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) {K c : ℝ} (hK : 1 ≤ K) (hc : 0 ≤ c)
    (hg : 0 ≤ minGapSq c (∑ i,w i)) (A B : Finset I) :
    let L := ∑ i,w i
    let P := averageMoment w (fun x => traceMoment K (√(gapSq c L x)))
    P A+P B ≤ P (A∩B)+P (A∪B) := by
  dsimp only
  apply averaged_moment_supermodular w hw (all_real_convex_profile hK hc hg)
  intro S
  exact ⟨Finset.sum_nonneg (fun i _ => hw i),
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hw i)⟩
end

section
open scoped Classical
open Set


variable {I : Type*} [Fintype I]
private def logWeight (s : I → ℝ) (i : I) := -Real.log (s i)

omit [Fintype I] in
private theorem exp_neg_log_mass (s : I → ℝ) (hp : ∀ i, 0 < s i) (U : Finset I) :
    Real.exp (-(mass (logWeight s) U)) = ∏ i ∈ U, s i := by
  simp only [mass,logWeight,Finset.sum_neg_distrib,neg_neg,Real.exp_sum]
  exact Finset.prod_congr rfl fun i _ => Real.exp_log (hp i)

private def cutDeterminant (s : I → ℝ) (c : ℝ) (U : Finset I) :=
  c*(1-∏ i ∈ U,s i)*(1-∏ i ∈ Finset.univ \ U,s i)

private def cutAverage (s : I → ℝ) (c K : ℝ) (S : Finset I) : ℝ :=
  (∑ U ∈ S.powerset, traceMoment K (√(1-4*cutDeterminant s c U))) / (2:ℝ)^S.card

private def cutGCE (s : I → ℝ) (c K : ℝ) (S : Finset I) := (1-cutAverage s c K S)/(K-1)

private theorem gap_eq_cut_determinant (s : I → ℝ) (hp : ∀ i, 0 < s i) (c : ℝ) (U : Finset I) :
    gapSq c (∑ i,logWeight s i) (mass (logWeight s) U) =
      1-4*cutDeterminant s c U := by
  have q : (∑ i,logWeight s i) - mass (logWeight s) U =
      mass (logWeight s) (Finset.univ \ U) := by
    unfold mass
    apply sub_eq_iff_eq_add.mpr
    exact (Finset.sum_sdiff (Finset.subset_univ U)).symm
  rw [gapSq,q,exp_neg_log_mass s hp U,exp_neg_log_mass s hp (Finset.univ \ U),cutDeterminant]
  ring

/-- All overlapping-subsystem inequalities for the literal positive
overlap profile, with a global-norm premise rather than independent local
assumptions about the midpoint. -/
private theorem cutGCE_submodular (s : I → ℝ) (hp : ∀ i, 0 < s i) (hle : ∀ i, s i ≤ 1)
    {K N a : ℝ} (hK : 1 < K) (hN : 0 < N) (ha : 0 ≤ a)
    (hglobal : 2*a*(1-radius (∑ i,logWeight s i)) ≤ N) (A B : Finset I) :
    cutGCE s ((a/N)^2) K (A∩B) + cutGCE s ((a/N)^2) K (A∪B) ≤
      cutGCE s ((a/N)^2) K A + cutGCE s ((a/N)^2) K B := by
  have hw (i : I) : 0 ≤ logWeight s i :=
    neg_nonneg.mpr (Real.log_nonpos (hp i).le (hle i))
  have hL : 0 ≤ ∑ i,logWeight s i := Finset.sum_nonneg fun i _ => hw i
  have h := averaged_cut_profile (logWeight s) hw hK.le (sq_nonneg (a/N))
    (midpoint_nonnegative hN ha hL hglobal) A B
  dsimp only [averageMoment] at h
  simp only [gap_eq_cut_determinant s hp] at h
  unfold cutGCE cutAverage
  rw [← add_div,← add_div]
  apply div_le_div_of_nonneg_right _ (by linarith)
  linarith
end

section
open scoped Classical
variable {I : Type*} [Fintype I]

private theorem complement_twice (U : Finset I) :
    (Finset.univ \ (Finset.univ \ U)) = U := by
  ext i; simp

omit [Fintype I] in
private theorem sum_relative_complement (F : Finset I → ℝ) (B : Finset I) :
    (∑ U ∈ B.powerset, F (B \ U)) = ∑ U ∈ B.powerset, F U := by
  apply Finset.sum_bij (fun U _ => B \ U)
  · intro U _
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro U hu V hv he
    have h1 : B \ (B \ U)=U := by
      ext i
      simp only [Finset.mem_sdiff,not_and,not_not]
      have hs (h : i∈U) := Finset.mem_powerset.mp hu h
      tauto
    have h2 : B \ (B \ V)=V := by
      ext i
      simp only [Finset.mem_sdiff,not_and,not_not]
      have hs (h : i∈V) := Finset.mem_powerset.mp hv h
      tauto
    simpa only [h1,h2] using congrArg (fun t => B \ t) he
  · intro U hu
    refine ⟨B \ U, Finset.mem_powerset.mpr Finset.sdiff_subset,?_⟩
    ext i
    simp only [Finset.mem_sdiff,not_and,not_not]
    have hs (h : i∈U) := Finset.mem_powerset.mp hu h
    tauto
  · intro U _; rfl

private theorem cutDet_complement (s : I → ℝ) (c : ℝ) (U : Finset I) :
    cutDeterminant s c (Finset.univ \ U) = cutDeterminant s c U := by
  rw [cutDeterminant,complement_twice,cutDeterminant]
  ring

private theorem cutAverage_final_site (s : I → ℝ) (c K : ℝ) (i : I) :
    cutAverage s c K (Finset.univ.erase i) = cutAverage s c K Finset.univ := by
  let B := (Finset.univ : Finset I).erase i
  let F := fun U => traceMoment K (√(1-4*cutDeterminant s c U))
  have hi : i ∉ B := by simp [B]
  have hB : insert i B = Finset.univ := by simp [B]
  have hcard : B.card + 1 = Fintype.card I := by
    rw [← Finset.card_insert_of_notMem hi,hB,Finset.card_univ]
  have hh (U : Finset I) : Finset.univ \ insert i U = B \ U := by
    ext j; simp [B,not_or,and_comm]
  have hcover (U : Finset I) : F (insert i U) = F (B \ U) := by
    have he (X : Finset I) : F (Finset.univ \ X) = F X := by
      simp only [F, cutDet_complement]
    rw [← he (insert i U),hh]
  change (∑ U ∈ B.powerset,F U)/(2:ℝ)^B.card = _
  unfold cutAverage
  change _ = (∑ U ∈ (Finset.univ : Finset I).powerset,F U)/(2:ℝ)^(Finset.univ : Finset I).card
  rw [← hB,Finset.sum_powerset_insert hi,Finset.card_insert_of_notMem hi,pow_succ]
  simp_rw [hcover,sum_relative_complement]
  have hn : (2:ℝ)^B.card ≠ 0 := by positivity
  field_simp
  ring

/-- Every earlier increment of a submodular complement-symmetric profile
dominates the final increment, which vanishes by a bit-complement pairing. -/
private theorem cutGCE_one_site (s : I → ℝ) (c K : ℝ)
    (h : ∀ A B : Finset I, cutGCE s c K (A∩B)+cutGCE s c K (A∪B) ≤
      cutGCE s c K A+cutGCE s c K B)
    (S : Finset I) (i : I) : cutGCE s c K S ≤ cutGCE s c K (insert i S) := by
  by_cases hi : i∈S
  · rw [Finset.insert_eq_of_mem hi]
  let B := (Finset.univ : Finset I).erase i
  have he : insert i S ∩ B = S := by
    ext j; by_cases hji : j=i
    · subst j; simp [B,hi]
    · simp [B,hji]
  have hu : insert i S ∪ B = Finset.univ := by
    ext j; by_cases hji : j=i <;> simp [B,hji]
  have hlast : cutGCE s c K B = cutGCE s c K Finset.univ := by
    unfold cutGCE
    rw [cutAverage_final_site s c K i]
  have hh := h (insert i S) B
  rw [he,hu,hlast] at hh
  linarith

private theorem cutGCE_monotone (s : I → ℝ) (c K : ℝ)
    (h : ∀ A B : Finset I, cutGCE s c K (A∩B)+cutGCE s c K (A∪B) ≤
      cutGCE s c K A+cutGCE s c K B) : Monotone (cutGCE s c K) := by
  intro A B ht
  have grow (D : Finset I) : cutGCE s c K A ≤ cutGCE s c K (D ∪ A) := by
    induction D using Finset.induction_on with
    | empty => simp
    | insert i D _ ih =>
      rw [Finset.insert_union]
      exact ih.trans (cutGCE_one_site s c K h (D ∪ A) i)
  rw [← Finset.sdiff_union_of_subset ht]
  exact grow _
end

section
open Filter Set
open scoped Classical Topology
variable {I : Type*} [Fintype I]

private theorem radius_eq_sqrt_prod (s : I → ℝ) (hp : ∀ i, 0 < s i) :
    radius (∑ i,logWeight s i) = √(∏ i,s i) := by
  have hpos : 0 ≤ radius (∑ i,logWeight s i) := Real.exp_nonneg _
  apply (pow_left_inj₀ hpos (Real.sqrt_nonneg _) (by decide : 2 ≠ 0)).mp
  rw [Real.sq_sqrt (Finset.prod_nonneg fun i _ => (hp i).le),radius,pow_two,← Real.exp_add]
  rw [show -((∑ i,logWeight s i)/2)+ -((∑ i,logWeight s i)/2) = -(∑ i,logWeight s i) by ring]
  exact exp_neg_log_mass s hp Finset.univ

private theorem cutGCE_continuous {c K : ℝ} (hK : 0 ≤ K) (S : Finset I) :
    Continuous (fun s : I → ℝ => cutGCE s c K S) := by
  unfold cutGCE cutAverage cutDeterminant traceMoment
  apply Continuous.div_const
  apply continuous_const.sub
  apply Continuous.div_const
  apply continuous_finsetSum
  intro U _
  apply Continuous.add
  · apply (Real.continuous_rpow_const hK).comp
    fun_prop
  · apply (Real.continuous_rpow_const hK).comp
    fun_prop

/-- Exact overlap profile, including zero local overlaps. They are
approximated inside the scalar unit cube; no change of physical phase, or
assumption about actual nearby tensor decompositions, is needed. -/
private theorem cutGCE_submodular_closed (s : I → ℝ) (h0 : ∀ i, 0 ≤ s i) (h1 : ∀ i, s i ≤ 1)
    {K N a : ℝ} (hK : 1 < K) (hN : 0 < N) (ha : 0 ≤ a)
    (hglobal : 2*a*(1-√(∏ i,s i)) ≤ N) (A B : Finset I) :
    cutGCE s ((a/N)^2) K (A∩B)+cutGCE s ((a/N)^2) K (A∪B) ≤
      cutGCE s ((a/N)^2) K A+cutGCE s ((a/N)^2) K B := by
  let eps := fun n : ℕ => 1/((n:ℝ)+1)
  let v := fun n : ℕ => fun i : I => s i+(eps n)*(1-s i)
  have epos (n : ℕ) : 0 < eps n := by dsimp [eps]; positivity
  have ele (n : ℕ) : eps n ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have ev (n : ℕ) (i : I) : s i ≤ v n i := by
    dsimp [v]; linarith [mul_nonneg (epos n).le (sub_nonneg.mpr (h1 i))]
  have hv (n : ℕ) (i : I) : 0 < v n i := by
    by_cases he : s i=0
    · simpa [v,he] using epos n
    · exact (lt_of_le_of_ne (h0 i) (Ne.symm he)).trans_le (ev n i)
  have hmax (n : ℕ) (i : I) : v n i ≤ 1 := by
    dsimp [v]
    linarith [mul_le_mul_of_nonneg_right (ele n) (sub_nonneg.mpr (h1 i))]
  have hbound (n : ℕ) : 2*a*(1-radius (∑ i,logWeight (v n) i)) ≤ N := by
    rw [radius_eq_sqrt_prod _ (hv n)]
    have hh : (∏ i,s i) ≤ ∏ i,v n i :=
      Finset.prod_le_prod₀ (fun i _ => h0 i) (fun i _ => ev n i)
    exact (mul_le_mul_of_nonneg_left
      (sub_le_sub_left (Real.sqrt_le_sqrt hh) 1) (by positivity : 0 ≤ 2*a)).trans hglobal
  have ep : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have lim : Tendsto v atTop (𝓝 s) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [v,zero_mul,add_zero] using tendsto_const_nhds.add (ep.mul_const (1-s i))
  have hK0 : 0 ≤ K := by linarith
  have H (S : Finset I) : Tendsto (fun n => cutGCE (v n) ((a/N)^2) K S) atTop
      (𝓝 (cutGCE s ((a/N)^2) K S)) :=
    (cutGCE_continuous hK0 S).continuousAt.tendsto.comp lim
  exact le_of_tendsto_of_tendsto' ((H (A∩B)).add (H (A∪B))) ((H A).add (H B))
    (fun n => cutGCE_submodular (v n) (hv n) (hmax n) hK hN ha (hbound n) A B)
end

section
open PhysicalTwoProductMoments
open scoped Classical
universe u v

/-- The actual GCE is the normalized deficiency of the average of the
physical reduced matrices' real power traces over subsets of the subsystem. -/
def physicalGCE (K : ℝ) {I : Type u} [Fintype I] {D : I → Type v}
    [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] (a b : ℂ) (u v : ∀ i, D i → ℂ) (S : Finset I) : ℝ :=
  (1-(∑ U ∈ S.powerset, physicalCutMoment K a b u v U)/(2:ℝ)^S.card)/(K-1)

private abbrev actualOverlap {I : Type*} {D : I → Type*} [∀ i, Fintype (D i)]
    (u v : ∀ i, D i → ℂ) (i : I) :=
  Complex.normSq (overlap (u i) (v i))

/-- Every literal coherent sum of two product vectors with arbitrary complex
coefficients and nonzero total norm has monotone and submodular physical GCE
at every real order K>1, including when local factors are orthogonal. -/
theorem actual_two_product_gce {K : ℝ} (hK : 1 < K) :
    let observed := @physicalGCE.{u,v} K
    ∀ {I : Type u} [Fintype I] {D : I → Type v} [∀ i, Fintype (D i)]
      [∀ i, DecidableEq (D i)] (a b : ℂ) (u v : ∀ i, D i → ℂ),
    (∀ i, overlap (u i) (u i) = 1) →
    (∀ i, overlap (v i) (v i) = 1) →
    totalMass a b u v ≠ 0 →
    let observed := @observed I inferInstance D inferInstance inferInstance a b u v
    Monotone observed ∧ (∀ A B,
      observed (A∩B)+observed (A∪B) ≤ observed A+observed B) := by
  dsimp only
  intro I _ D _ _ a b u v hu hv hn
  have hN : 0 < totalMass a b u v :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)) (Ne.symm hn)
  have hK0 : 0 < K := by linarith
  obtain ⟨hbound,hmass,hcut⟩ := physical_two_product_moments hK0 a b u v hu hv hn
  have hsub := cutGCE_submodular_closed (actualOverlap u v)
    (fun i => Complex.normSq_nonneg _) hbound hK hN (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hmass
  have heq : physicalGCE K a b u v = cutGCE (actualOverlap u v)
      ((‖a‖*‖b‖/totalMass a b u v)^2) K := by
    funext S
    simp only [physicalGCE,cutGCE,cutAverage,cutDeterminant,traceMoment,hcut]
  rw [heq]
  exact ⟨cutGCE_monotone _ _ _ hsub,hsub⟩

end
end D5.S3.Quantum.Entanglement.ConcentratableEntanglement.TwoProductConcentratableEntanglement
