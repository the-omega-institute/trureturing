/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterShortGapSign
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The short-gap mixed derivative from scalar curvature and marginal bounds. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailJet
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterCollisionRadicand
import Mathlib.Algebra.Ring.GeomSum

/-! # An upper bound for the mixed derivative on the short-gap strip -/

open Filter
open scoped BigOperators Topology

namespace RefinedBMV.PositiveCenter

/-- The favorable lower-coordinate term in the short-gap decomposition. -/
noncomputable def shortGapQuotient (h t : ℝ) : ℝ :=
  h + 1/4 - (1 - Real.exp (-((3+2*h)*t))) / upperTailGap h t

/-- The constant quarter can be absorbed into the gap profile, leaving a decaying slope. -/
theorem shortGapQuotient_recenter {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    shortGapQuotient h t = 1 / 4 -
      upperTailSlope h t * (1 - Real.exp (-((3 + h) * t))) := by
  have ha : 0 < upperTailGap h t := by
    rw [expGapMean_eq hh]
    exact mul_pos ht (expGapMean_pos _ _)
  have hgap : h * upperTailGap h t = 1 - Real.exp (-(h * t)) := by
    unfold upperTailGap
    field_simp [hh.ne']
  have hexp : Real.exp (-((3 + 2*h) * t)) =
      Real.exp (-(h*t)) * Real.exp (-((3+h)*t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [shortGapQuotient, ← upperTailGap_logDeriv hh ht,
    (hasDerivAt_upperTailGap (t := t) hh).deriv, hexp]
  field_simp [ha.ne']
  linarith only [hgap]

/-- The geometric term has a positive margin away from the lower endpoint four. -/
theorem shortGapQuotient_lower {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    1 / 4 - 1 / t ≤ shortGapQuotient h t := by
  have ha : 0 < upperTailGap h t := by
    rw [expGapMean_eq hh]
    exact mul_pos ht (expGapMean_pos _ _)
  have hgap : h*upperTailGap h t + Real.exp (-(h*t)) = 1 := by
    unfold upperTailGap
    field_simp [hh.ne']
    ring
  have hrec : 1 / upperTailGap h t = h + upperTailSlope h t := calc
    _ = h + Real.exp (-(h*t)) / upperTailGap h t := by
      field_simp [ha.ne']
      linarith
    _ = _ := by rw [← upperTailGap_logDeriv hh ht, (hasDerivAt_upperTailGap hh).deriv]
  have hbound := div_le_div_of_nonneg_right
    (sub_le_self (1 : ℝ) (Real.exp_pos (-((3+2*h)*t))).le) ha.le
  have hL := (upperTailSlope_bounds hh ht).2.1
  unfold shortGapQuotient
  linarith

theorem shortGapQuotient_nonneg {h t : ℝ} (hh : 0 < h) (ht : 4 ≤ t) :
    0 ≤ shortGapQuotient h t := by
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) ht
  exact (sub_nonneg.mpr hinv).trans (shortGapQuotient_lower hh (by linarith))

theorem shortGapQuotient_deriv_nonneg {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    0 ≤ deriv (shortGapQuotient (3/(p : ℝ))) t := by
  let h : ℝ := 3/(p : ℝ)
  let q : ℝ → ℝ := fun x ↦ Real.exp (-(h*x))
  let P : ℝ → ℝ := fun x ↦ h+1/4-h*∑ i ∈ Finset.range (p+2), q x ^ i
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have heq : shortGapQuotient h =ᶠ[𝓝 t] P := by
    filter_upwards [eventually_gt_nhds ht] with x hx
    have ha : 0 < upperTailGap h x := by
      rw [expGapMean_eq hh]
      exact mul_pos hx (expGapMean_pos _ _)
    have hpower : q x ^ (p+2) = Real.exp (-((3+2*h)*x)) := by
      unfold q
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      dsimp [h]
      field_simp [hpR.ne']
    have hsum := geom_sum_mul_neg (q x) (p+2)
    have hgap : 1-q x = h*upperTailGap h x := by
      unfold q upperTailGap
      field_simp [hh.ne']
    rw [hpower, hgap] at hsum
    unfold shortGapQuotient P
    congr 1
    apply (div_eq_iff ha.ne').2
    linear_combination -hsum
  have hmono : Monotone P := by
    intro x y hxy
    apply sub_le_sub_left
    apply mul_le_mul_of_nonneg_left _ hh.le
    apply Finset.sum_le_sum
    intro i _
    apply pow_le_pow_left₀ (Real.exp_pos _).le _ _
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hxy hh.le))
  exact heq.deriv_eq.symm ▸ hmono.deriv_nonneg

/-- At each positive gap the geometric term is a finite exponential sum.
The right hand side extends through the zero of the denominator. -/
theorem shortGap_geometric_eq {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    let h : ℝ := 3 / (p : ℝ)
    Real.exp (3*t/2) * (1 - Real.exp (-((3+h)*t))) / upperTailGap h t =
      h * ∑ l ∈ Finset.range (p+1), Real.exp ((h*l-3/2)*t) := by
  let h : ℝ := 3 / (p : ℝ)
  let q := Real.exp (-(h*t))
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have h_hp : h*(p : ℝ) = 3 := div_mul_cancel₀ _ hpR.ne'
  have ha : 0 < upperTailGap h t := by
    rw [expGapMean_eq hh]
    exact mul_pos ht (expGapMean_pos _ _)
  have hq : 1-q = h*upperTailGap h t := by
    unfold q upperTailGap
    field_simp [hh.ne']
  have hpower : q^(p+1) = Real.exp (-((3+h)*t)) := by
    unfold q
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    linear_combination -t*h_hp
  have hgeom := geom_sum_mul_neg q (p+1)
  rw [hq, hpower] at hgeom
  have hratio : (1-Real.exp (-((3+h)*t))) / upperTailGap h t =
      h * ∑ l ∈ Finset.range (p+1), q^l := by
    apply (div_eq_iff ha.ne').2
    linear_combination -hgeom
  change Real.exp (3*t/2) * (1 - Real.exp (-((3+h)*t))) / upperTailGap h t =
    h * ∑ l ∈ Finset.range (p+1), Real.exp ((h*l-3/2)*t)
  rw [mul_div_assoc, hratio, ← mul_left_comm, Finset.mul_sum]
  congr 1
  symm
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hlp : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  rw [show p+1-1-l = p-l by omega, Nat.cast_sub hlp]
  unfold q
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  linear_combination t*h_hp

/-- Keep the profile's slope and the geometric correction in the curvature estimate. -/
theorem shortGap_mixed_lt_of_profile_margin
    {α β αv m E q q' s s' s'' j j' j'' z z' ξ ε : ℝ}
    (hα : 0 ≤ α) (hαmax : α ≤ 1/7) (hβ : β ≤ 0) (hβmin : -1/4 ≤ β)
    (hs : 0 ≤ s)
    (hprofile : ε < s'' - (α - β) * s' - (β - m) * E * (q' + (α + m) * q))
    (hj : 0 ≤ j) (hj' : 0 ≤ j') (hj'' : j'/2 ≤ j'')
    (hz : 0 ≤ 1-z) (hz' : 0 ≤ z')
    (hcorrection : z'*j' ≤ ξ*(1/2-α)*(1/2-αv)) :
    -s'' + (α-β)*s' + α*β*s +
      (β-m)*E*(q'+(α+m)*q) +
      ((1-z)*(-j''+(α-β)*j') + z'*j' + α*(β*(1-z)-z')*j) -
      ξ*(1/2-α)*(1/2-αv) < -ε := by
  have hαβmax : α-β ≤ 1/2 := by linarith
  have hF₂ : α*β*s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos hα hβ) hs
  have hJ₁ : -j''+(α-β)*j' ≤ 0 := by
    have h := mul_le_mul_of_nonneg_right hαβmax hj'
    linarith
  have hJ₂ : β*(1-z)-z' ≤ 0 :=
    sub_nonpos.mpr ((mul_nonpos_of_nonpos_of_nonneg hβ hz).trans hz')
  have hJ₃ := mul_nonpos_of_nonneg_of_nonpos hz hJ₁
  have hJ₄ := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos hα hJ₂) hj
  linarith

/-- Positive curvature and nonpositive slope suffice when the geometric correction helps. -/
theorem shortGap_mixed_lt
    {α β αv m E q q' s s' s'' j j' j'' z z' ξ ε : ℝ}
    (hα : 0 ≤ α) (hαmax : α ≤ 1/7) (hβ : β ≤ 0) (hβmin : -1/4 ≤ β)
    (hm : 0 ≤ m) (hE : 0 ≤ E) (hq : 0 ≤ q) (hq' : 0 ≤ q')
    (hs : 0 ≤ s) (hs' : s' ≤ 0) (hs'' : ε < s'')
    (hj : 0 ≤ j) (hj' : 0 ≤ j') (hj'' : j'/2 ≤ j'')
    (hz : 0 ≤ 1-z) (hz' : 0 ≤ z')
    (hcorrection : z'*j' ≤ ξ*(1/2-α)*(1/2-αv)) :
    -s'' + (α-β)*s' + α*β*s +
      (β-m)*E*(q'+(α+m)*q) +
      ((1-z)*(-j''+(α-β)*j') + z'*j' + α*(β*(1-z)-z')*j) -
      ξ*(1/2-α)*(1/2-αv) < -ε := by
  have hF : (α-β)*s' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hβ.trans hα)) hs'
  have hQ : (β-m)*E*(q'+(α+m)*q) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hβ.trans hm)) hE)
      (add_nonneg hq' (mul_nonneg (add_nonneg hα hm) hq))
  exact shortGap_mixed_lt_of_profile_margin hα hαmax hβ hβmin hs
    (by linarith only [hs'', hF, hQ]) hj hj' hj'' hz hz' hcorrection

private noncomputable def leftJet (f : ℝ → ℝ) (u _ : ℝ) : MixedJet ℝ :=
  ⟨f u, deriv f u, 0, 0⟩

private noncomputable def rightJet (f : ℝ → ℝ) (_ v : ℝ) : MixedJet ℝ :=
  ⟨f v, 0, deriv f v, 0⟩

private theorem leftJet_isAt {f : ℝ → ℝ} {u v : ℝ} (hf : DifferentiableAt ℝ f u) :
    MixedJet.IsAt (leftJet f) u v :=
  ⟨Eventually.of_forall fun _ ↦ hf.hasDerivAt, hasDerivAt_const v (f u),
    hasDerivAt_const v (deriv f u)⟩

private theorem rightJet_isAt {f : ℝ → ℝ} {u v : ℝ} (hf : DifferentiableAt ℝ f v) :
    MixedJet.IsAt (rightJet f) u v :=
  ⟨Eventually.of_forall fun y ↦ hasDerivAt_const u (f y), hf.hasDerivAt,
    hasDerivAt_const v (0 : ℝ)⟩

private noncomputable def gapJet (f : ℝ → ℝ) : ℝ → ℝ → MixedJet ℝ :=
  upperGapJet (fun _ ↦ f)

private theorem gapJet_isAt {f : ℝ → ℝ} {u v : ℝ} (hf : ContDiffAt ℝ 2 f (v-u)) :
    MixedJet.IsAt (gapJet f) u v :=
  upperGapJet_isAt (hf.comp (u,v-u) contDiffAt_snd)

/-- Differentiate the four short-gap terms after multiplying by the
separable positive normalization. The last correction is also separable. -/
theorem shortGap_weighted_mixed_formula
    {P V F Q Z J R : ℝ → ℝ} {u v α β αv m : ℝ}
    (hP : HasDerivAt P (α*P u) u) (hV : HasDerivAt V (β*V v) v)
    (hF : ContDiffAt ℝ 2 F (v-u)) (hJ : ContDiffAt ℝ 2 J (v-u))
    (hQ : DifferentiableAt ℝ Q u) (hZ : DifferentiableAt ℝ Z v)
    (hR : HasDerivAt R ((αv-β-1/2)*R v) v) :
    deriv (fun y ↦ deriv (fun x ↦ P x*V y*
      (F (y-x) + Q x*Real.exp (-m*(y-x)) + (1-Z y)*J (y-x) -
        Real.exp (-x/2)*R y)) u) v =
      let d := v-u
      let s := F d
      let s' := deriv F d
      let s'' := deriv (deriv F) d
      let j := J d
      let j' := deriv J d
      let j'' := deriv (deriv J) d
      let z := Z v
      let z' := deriv Z v
      P u*V v *
        (-s''+(α-β)*s'+α*β*s +
          (β-m)*Real.exp (-m*d)*(deriv Q u+(α+m)*Q u) +
          ((1-z)*(-j''+(α-β)*j') + z'*j' + α*(β*(1-z)-z')*j) -
          Real.exp (-u/2)*R v*(1/2-α)*(1/2-αv)) := by
  let E : ℝ → ℝ := fun x ↦ Real.exp (-m*x)
  let C₁ : ℝ → ℝ := fun x ↦ 1-Z x
  let C₂ : ℝ → ℝ := fun x ↦ Real.exp (-x/2)
  have hE : ContDiff ℝ 2 E := by unfold E; fun_prop
  have hC₁ := (hasDerivAt_const v (1 : ℝ)).fun_sub hZ.hasDerivAt
  have hC₁' : deriv C₁ v = -(deriv Z v) := by
    change deriv (fun x ↦ 1-Z x) v = _
    rw [hC₁.deriv, zero_sub]
  have hC₂ : HasDerivAt C₂ (-(1/2)*C₂ u) u := by
    have h := ((hasDerivAt_id' u).const_mul (-1/2 : ℝ)).exp
    convert h using 1
    · funext t
      apply congrArg Real.exp
      ring
    · unfold C₂
      rw [show (-1/2 : ℝ)*u = -u/2 by ring]
      ring
  have hE' : deriv E = fun t ↦ -m*E t := by
    funext t
    have h := ((hasDerivAt_id' t).const_mul (-m)).exp
    change HasDerivAt E (E t * (-m*1)) t at h
    rw [h.deriv]
    ring
  have hE'' : deriv (deriv E) (v-u) = m^2 * E (v-u) := by
    have h := ((hE.contDiffAt (x := v-u)).differentiableAt (by norm_num)).hasDerivAt
    rw [hE', (h.const_mul (-m)).deriv, congrFun hE']
    ring
  let jet (x y : ℝ) :=
    ((leftJet P x y).mul (rightJet V x y)).mul
      ((((gapJet F x y).add ((leftJet Q x y).mul (gapJet E x y))).add
        ((rightJet C₁ x y).mul (gapJet J x y))).sub
        ((leftJet C₂ x y).mul (rightJet R x y)))
  have hjet : MixedJet.IsAt jet u v :=
    ((leftJet_isAt hP.differentiableAt).mul (rightJet_isAt hV.differentiableAt)).mul
      ((((gapJet_isAt hF).add ((leftJet_isAt hQ).mul (gapJet_isAt hE.contDiffAt))).add
        ((rightJet_isAt hC₁.differentiableAt).mul (gapJet_isAt hJ))).sub
        ((leftJet_isAt hC₂.differentiableAt).mul (rightJet_isAt hR.differentiableAt)))
  have hloc :
      (fun y ↦ deriv (fun x ↦ (jet x y).value) u) =ᶠ[𝓝 v] (fun y ↦ (jet u y).du) := by
    filter_upwards [hjet.1] with y hy
    exact hy.deriv
  change deriv (fun y ↦ deriv (fun x ↦ (jet x y).value) u) v = _
  rw [hloc.deriv_eq, hjet.2.2.deriv]
  dsimp only [jet, leftJet, rightJet, gapJet, upperGapJet,
    MixedJet.add, MixedJet.sub, MixedJet.mul]
  simp only [deriv_const, hP.deriv, hV.deriv, hC₁', hC₂.deriv, hR.deriv,
    hE'', congrFun hE']
  dsimp only [C₁, C₂, E]
  ring

#print axioms shortGap_mixed_lt
#print axioms shortGapQuotient_nonneg
#print axioms shortGapQuotient_deriv_nonneg
#print axioms shortGap_weighted_mixed_formula
#print axioms shortGap_geometric_eq

end RefinedBMV.PositiveCenter
