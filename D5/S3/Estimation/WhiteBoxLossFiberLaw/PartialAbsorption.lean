/- GID: D5/S3/Estimation/WhiteBoxLossFiberLaw/PartialAbsorption
   generality: G
   mirror-B: D5/B/S3/Estimation/WhiteBoxLossFiberLaw/PartialAbsorption
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact nonnegative coding certificates for rotating two-atom dictionaries. -/

import D5.S3.Estimation.WhiteBoxLossFiberLaw.TwoAtomMatching
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
noncomputable section

namespace D5.S3.Estimation.WhiteBoxLossFiberLaw.PartialAbsorption

open TwoAtomMatching
open scoped BigOperators RealInnerProductSpace Topology
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem orthogonal_norm_sq (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (a b : ℝ) :
    ‖a • u + b • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real]
  simp [norm_smul, hu, hv, real_inner_smul_left, inner_smul_right, huv,
    Real.norm_eq_abs, sq_abs]

/-- The rotating dictionary is defined on the whole real line. -/
def rotatingDictionary (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (α : ℝ) : UnitDictionary E :=
  ⟨![u, Real.cos α • u + Real.sin α • v], by
    intro i
    fin_cases i
    · exact hu
    · change ‖Real.cos α • u + Real.sin α • v‖ = 1
      apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp
      rw [orthogonal_norm_sq u v hu hv huv]
      nlinarith [Real.sin_sq_add_cos_sq α]⟩

/-- The actual finite four-point expectation, with its zero-sample term retained. -/
def objective (lam p0 pA pAB pB : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0) (α : ℝ) : ℝ :=
  let D := rotatingDictionary u v hu hv huv α
  p0 * codeCost lam 0 D + jointCost lam pA pAB pB u v D

private theorem coordinate_energy (lam a b α : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (c : Fin 2 → ℝ) :
    codeEnergy lam (a • u + b • v) (rotatingDictionary u v hu hv huv α) c =
      ((a - c 0 - Real.cos α * c 1)^2 + (b - Real.sin α * c 1)^2)/2 +
        lam * (c 0 + c 1) := by
  have heq : a • u + b • v - atomCombination (rotatingDictionary u v hu hv huv α) c =
      (a - c 0 - Real.cos α * c 1) • u + (b - Real.sin α * c 1) • v := by
    simp [atomCombination, rotatingDictionary, Fin.sum_univ_two]
    module
  rw [codeEnergy, heq, orthogonal_norm_sq u v hu hv huv, Fin.sum_univ_two]

private theorem native_optimum (lam a b α z0 z1 : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hz0 : 0 ≤ z0) (hz1 : 0 ≤ z1)
    (h0 : 0 ≤ lam - (a - z0 - Real.cos α * z1))
    (h1 : 0 ≤ lam - (Real.cos α * (a - z0 - Real.cos α * z1) +
      Real.sin α * (b - Real.sin α * z1)))
    (hc0 : z0 * (lam - (a - z0 - Real.cos α * z1)) = 0)
    (hc1 : z1 * (lam - (Real.cos α * (a - z0 - Real.cos α * z1) +
      Real.sin α * (b - Real.sin α * z1))) = 0) :
    let D := rotatingDictionary u v hu hv huv α
    let z : Fin 2 → ℝ := ![z0,z1]
    FeasibleCode z ∧ codeCost lam (a • u + b • v) D = codeEnergy lam (a • u + b • v) D z ∧
      ∀ c, FeasibleCode c → codeEnergy lam (a • u + b • v) D z ≤
        codeEnergy lam (a • u + b • v) D c := by
  dsimp only
  have hz : FeasibleCode (![z0,z1] : Fin 2 → ℝ) := by
    intro i; fin_cases i <;> assumption
  have hmin : ∀ c, FeasibleCode c →
      codeEnergy lam (a • u + b • v) (rotatingDictionary u v hu hv huv α) ![z0,z1] ≤
      codeEnergy lam (a • u + b • v) (rotatingDictionary u v hu hv huv α) c := by
    intro c hc
    rw [coordinate_energy, coordinate_energy]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have hid :
        ((a - c 0 - Real.cos α * c 1)^2 + (b - Real.sin α * c 1)^2)/2 + lam*(c 0+c 1) -
        (((a-z0-Real.cos α*z1)^2+(b-Real.sin α*z1)^2)/2+lam*(z0+z1)) =
        ((c 0-z0)+Real.cos α*(c 1-z1))^2/2 + (Real.sin α*(c 1-z1))^2/2 +
        (lam-(a-z0-Real.cos α*z1))*c 0 +
        (lam-(Real.cos α*(a-z0-Real.cos α*z1)+Real.sin α*(b-Real.sin α*z1)))*c 1 := by
      linear_combination -hc0 - hc1
    have hp0 := mul_nonneg h0 (hc 0)
    have hp1 := mul_nonneg h1 (hc 1)
    nlinarith [sq_nonneg ((c 0-z0)+Real.cos α*(c 1-z1)),
      sq_nonneg (Real.sin α*(c 1-z1))]
  unfold codeCost
  refine ⟨hz, le_antisymm ?_ ?_, hmin⟩
  · exact csInf_le ⟨_, by rintro y ⟨c,hc,rfl⟩; exact hmin c hc⟩ ⟨_,hz,rfl⟩
  · have hne : ({y : ℝ | ∃ c, FeasibleCode c ∧ codeEnergy lam (a • u + b • v) (rotatingDictionary u v hu hv huv α) c = y}).Nonempty :=
      ⟨_, ⟨![z0,z1], hz, rfl⟩⟩
    apply le_csInf hne
    rintro y ⟨c,hc,rfl⟩
    exact hmin c hc

private theorem cost_attained (lam : ℝ) (x : E) (D : UnitDictionary E)
    (hlam : 0 < lam) : ∃ c, FeasibleCode c ∧ codeCost lam x D = codeEnergy lam x D c := by
  let R := ‖x‖ ^ 2 / (2 * lam) + 1
  let S : Set (Fin 2 → ℝ) := Icc (fun _ => 0) (fun _ => R)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hzero : (fun _ => (0 : ℝ)) ∈ S := ⟨le_rfl, fun _ => hR⟩
  have hcont : Continuous (codeEnergy lam x D) := by
    unfold codeEnergy atomCombination
    fun_prop
  obtain ⟨z, hz, hmin⟩ := (isCompact_Icc : IsCompact S).exists_isMinOn ⟨_,hzero⟩ hcont.continuousOn
  have hglobal : ∀ c, FeasibleCode c → codeEnergy lam x D z ≤ codeEnergy lam x D c := by
    intro c hc
    by_cases hcs : c ∈ S
    · exact hmin hcs
    have hout : ∃ i, R < c i := by
      by_contra h
      push Not at h
      exact hcs ⟨hc,h⟩
    obtain ⟨i,hi⟩ := hout
    have hmass : c i ≤ ∑ j, c j := by
      exact Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)
    have henergy : lam * c i ≤ codeEnergy lam x D c := by
      unfold codeEnergy
      nlinarith [sq_nonneg ‖x - atomCombination D c‖,
        mul_le_mul_of_nonneg_left hmass hlam.le]
    have hcancel : lam * (‖x‖ ^ 2 / (2 * lam)) = ‖x‖ ^ 2 / 2 := by
      field_simp
    have hstrict : ‖x‖ ^ 2 / 2 < lam * c i := by
      have hh := mul_lt_mul_of_pos_left hi hlam
      dsimp [R] at hh
      nlinarith
    have hzbound := hmin hzero
    have hezero : codeEnergy lam x D (fun _ => 0) = ‖x‖ ^ 2 / 2 := by
      simp [codeEnergy, atomCombination]
    change codeEnergy lam x D z ≤ codeEnergy lam x D (fun _ => 0) at hzbound
    rw [hezero] at hzbound
    linarith
  refine ⟨z,hz.1,?_⟩
  unfold codeCost
  apply le_antisymm
  · exact csInf_le ⟨_, by rintro y ⟨c,hc,rfl⟩; exact hglobal c hc⟩ ⟨z,hz.1,rfl⟩
  · have hne : ({y : ℝ | ∃ c, FeasibleCode c ∧ codeEnergy lam x D c = y}).Nonempty := ⟨_,z,hz.1,rfl⟩
    apply le_csInf hne
    rintro y ⟨c,hc,rfl⟩
    exact hglobal c hc

private theorem zero_cost (lam : ℝ) (D : UnitDictionary E) (hlam : 0 ≤ lam) :
    codeCost lam 0 D = 0 := by
  obtain ⟨hlow,hhigh⟩ := code_cost_bounds lam 0 D hlam
  have hhigh' : codeCost lam 0 D ≤ 0 := by simpa using hhigh
  exact le_antisymm hhigh' hlow

private theorem u_cost (lam α : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1) :
    codeCost lam u (rotatingDictionary u v hu hv huv α) = lam - lam^2/2 := by
  simpa using (code_cost_eq_radial_iff lam 1 u (rotatingDictionary u v hu hv huv α)
    hu hlam hsmall).mpr ⟨0,rfl⟩

private theorem one_atom_cost (lam a b α : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (ht : 0 ≤ a * Real.cos α + b * Real.sin α - lam)
    (hfirst : a - Real.cos α * (a * Real.cos α + b * Real.sin α - lam) ≤ lam) :
    codeCost lam (a • u + b • v) (rotatingDictionary u v hu hv huv α) =
      (a^2+b^2)/2 - (a*Real.cos α+b*Real.sin α-lam)^2/2 := by
  let t := a * Real.cos α + b * Real.sin α - lam
  have htrig := Real.sin_sq_add_cos_sq α
  have hgrad : lam - (Real.cos α * (a - 0 - Real.cos α * t) +
      Real.sin α * (b - Real.sin α * t)) = 0 := by
    dsimp [t]
    linear_combination (a * Real.cos α + b * Real.sin α - lam) * htrig
  have hopt := native_optimum lam a b α 0 t u v hu hv huv (by rfl) ht
    (by dsimp [t]; linarith) hgrad.ge (by ring) (by rw [hgrad]; ring)
  rw [hopt.2.1, coordinate_energy]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  dsimp [t]
  linear_combination ((a * Real.cos α + b * Real.sin α - lam)^2/2) * htrig

private def zSecond (lam a b α : ℝ) : ℝ :=
  (a * Real.cos α + b * Real.sin α - lam - Real.cos α * (a-lam)) /
    (1-Real.cos α^2)

private def zFirst (lam a b α : ℝ) : ℝ := a-lam-Real.cos α*zSecond lam a b α

private def bothValue (lam a b α : ℝ) : ℝ :=
  ((a-zFirst lam a b α-Real.cos α*zSecond lam a b α)^2 +
    (b-Real.sin α*zSecond lam a b α)^2)/2 + lam*(zFirst lam a b α+zSecond lam a b α)

private theorem both_atom_cost (lam a b α : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hden : 1 - Real.cos α ^ 2 ≠ 0)
    (hfirst : 0 ≤ zFirst lam a b α) (hsecond : 0 ≤ zSecond lam a b α) :
    codeCost lam (a • u + b • v) (rotatingDictionary u v hu hv huv α) = bothValue lam a b α := by
  have htrig := Real.sin_sq_add_cos_sq α
  have hgrad0 : lam - (a-zFirst lam a b α-Real.cos α*zSecond lam a b α) = 0 := by
    dsimp [zFirst]; ring
  have hgrad1 : lam - (Real.cos α*(a-zFirst lam a b α-Real.cos α*zSecond lam a b α) +
      Real.sin α*(b-Real.sin α*zSecond lam a b α)) = 0 := by
    dsimp [zFirst,zSecond]
    field_simp [hden]
    linear_combination (b*Real.sin α-lam+Real.cos α*lam) * htrig
  have hopt := native_optimum lam a b α (zFirst lam a b α) (zSecond lam a b α)
    u v hu hv huv hfirst hsecond hgrad0.ge hgrad1.ge
    (by rw [hgrad0]; ring) (by rw [hgrad1]; ring)
  rw [hopt.2.1, coordinate_energy]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rfl

private def leftValue (lam pA pAB pB α : ℝ) : ℝ :=
  pA*(lam-lam^2/2) + pAB*(1-(Real.cos α+Real.sin α-lam)^2/2) +
    pB*(1/2-(Real.sin α-lam)^2/2)

private def rightValue (lam pA pAB pB α : ℝ) : ℝ :=
  pA*(lam-lam^2/2) + pAB*bothValue lam 1 1 α + pB*(1/2-(Real.sin α-lam)^2/2)

private theorem left_value_eventually (lam p0 pA pAB pB : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2) :
    objective lam p0 pA pAB pB u v hu hv huv =ᶠ[𝓝 (Real.pi/4)] leftValue lam pA pAB pB := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsquare : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hq : Real.sqrt 2/2 = 1/Real.sqrt 2 := by field_simp; nlinarith
  have hqpos : 0 < 1/Real.sqrt 2 := by positivity
  have hqlt : 1/Real.sqrt 2 < 1 := by
    rw [div_lt_one hsqrt]
    nlinarith [Real.sqrt_nonneg 2]
  have hunit : lam < 1 := hsmall.trans hqlt
  have hab : 0 < Real.cos (Real.pi/4)+Real.sin (Real.pi/4)-lam := by
    rw [Real.cos_pi_div_four,Real.sin_pi_div_four,hq]
    linarith
  have hinactive : 0 < lam-1+Real.cos (Real.pi/4)*(Real.cos (Real.pi/4)+Real.sin (Real.pi/4)-lam) := by
    rw [Real.cos_pi_div_four,Real.sin_pi_div_four]
    nlinarith [mul_pos hlam (show 0 < 1-Real.sqrt 2/2 by nlinarith)]
  have hvactive : 0 < Real.sin (Real.pi/4)-lam := by
    rw [Real.sin_pi_div_four,hq]; linarith
  have hvinactive : 0 < lam+Real.cos (Real.pi/4)*(Real.sin (Real.pi/4)-lam) := by
    rw [Real.cos_pi_div_four,Real.sin_pi_div_four]
    nlinarith [mul_pos hlam (show 0 < 1-Real.sqrt 2/2 by nlinarith)]
  have habc : Continuous (fun α : ℝ => Real.cos α+Real.sin α-lam) := by fun_prop
  have hiac : Continuous (fun α : ℝ => lam-1+Real.cos α*(Real.cos α+Real.sin α-lam)) := by fun_prop
  have hvac : Continuous (fun α : ℝ => Real.sin α-lam) := by fun_prop
  have hvic : Continuous (fun α : ℝ => lam+Real.cos α*(Real.sin α-lam)) := by fun_prop
  filter_upwards [habc.continuousAt.eventually_const_lt hab,
    hiac.continuousAt.eventually_const_lt hinactive,
    hvac.continuousAt.eventually_const_lt hvactive,
    hvic.continuousAt.eventually_const_lt hvinactive] with α hAB hiA hV hiV
  have hABcost := one_atom_cost lam 1 1 α u v hu hv huv (by simpa using hAB.le) (by nlinarith)
  have hVcost := one_atom_cost lam 0 1 α u v hu hv huv (by simpa using hV.le) (by nlinarith)
  simp only [one_smul,zero_smul,zero_add] at hABcost hVcost
  simp [objective,jointCost,zero_cost lam _ hlam.le,u_cost lam α u v hu hv huv hlam hunit,
    hABcost,hVcost,leftValue]

private theorem right_value_eventually (lam p0 pA pAB pB : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hlam : 0 < lam) (hunit : lam < 1) :
    objective lam p0 pA pAB pB u v hu hv huv =ᶠ[𝓝 (Real.pi/2)] rightValue lam pA pAB pB := by
  have hden : 1-Real.cos (Real.pi/2)^2 ≠ 0 := by norm_num
  have hcont0 : ContinuousAt (zFirst lam 1 1) (Real.pi/2) := by
    unfold zFirst zSecond
    fun_prop (disch := norm_num)
  have hcont1 : ContinuousAt (zSecond lam 1 1) (Real.pi/2) := by
    unfold zSecond
    fun_prop (disch := norm_num)
  have hz0 : 0 < zFirst lam 1 1 (Real.pi/2) := by simpa [zFirst,zSecond] using sub_pos.mpr hunit
  have hz1 : 0 < zSecond lam 1 1 (Real.pi/2) := by simpa [zSecond] using sub_pos.mpr hunit
  have hdc : Continuous (fun α : ℝ => 1-Real.cos α^2) := by fun_prop
  have hvac : Continuous (fun α : ℝ => Real.sin α-lam) := by fun_prop
  have hvic : Continuous (fun α : ℝ => lam+Real.cos α*(Real.sin α-lam)) := by fun_prop
  have hV : 0 < Real.sin (Real.pi/2)-lam := by simpa using sub_pos.mpr hunit
  have hiV : 0 < lam+Real.cos (Real.pi/2)*(Real.sin (Real.pi/2)-lam) := by simpa using hlam
  filter_upwards [hcont0.eventually_const_lt hz0,hcont1.eventually_const_lt hz1,
    hdc.continuousAt.eventually_ne hden,hvac.continuousAt.eventually_const_lt hV,
    hvic.continuousAt.eventually_const_lt hiV] with α hz0 hz1 hd hV hiV
  have hABcost := both_atom_cost lam 1 1 α u v hu hv huv hd hz0.le hz1.le
  have hVcost := one_atom_cost lam 0 1 α u v hu hv huv (by simpa using hV.le) (by nlinarith)
  simp only [one_smul,zero_smul,zero_add] at hABcost hVcost
  simp [objective,jointCost,zero_cost lam _ hlam.le,u_cost lam α u v hu hv huv hlam hunit,
    hABcost,hVcost,rightValue]

private theorem left_value_derivative (lam pA pAB pB α : ℝ) :
    HasDerivAt (leftValue lam pA pAB pB)
      (-pAB*(Real.cos α+Real.sin α-lam)*(Real.cos α-Real.sin α) -
        pB*(Real.sin α-lam)*Real.cos α) α := by
  have hm := ((Real.hasDerivAt_cos α).add (Real.hasDerivAt_sin α)).sub_const lam
  have h := ((hasDerivAt_const α (pA*(lam-lam^2/2))).add
    (((hasDerivAt_const α (1:ℝ)).sub ((hm.pow 2).div_const 2)).const_mul pAB)).add
    (((hasDerivAt_const α (1/2:ℝ)).sub ((((Real.hasDerivAt_sin α).sub_const lam).pow 2).div_const 2)).const_mul pB)
  convert h using 1
  all_goals try rfl
  all_goals norm_num [leftValue, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  all_goals ring

private theorem both_value_derivative (lam : ℝ) :
    HasDerivAt (bothValue lam 1 1) (lam*(1-lam)) (Real.pi/2) := by
  let β := Real.pi/2
  have hg : HasDerivAt Real.cos (-1) β := by simpa [β] using Real.hasDerivAt_cos β
  have hs : HasDerivAt Real.sin 0 β := by simpa [β] using Real.hasDerivAt_sin β
  have hm := ((hg.const_mul 1).add (hs.const_mul 1)).sub_const lam
  have hn := hm.sub (hg.mul_const (1-lam))
  have hd := (hasDerivAt_const β (1:ℝ)).sub (hg.pow 2)
  have hz1 : HasDerivAt (zSecond lam 1 1) (-lam) β := by
    convert hn.div hd (by simp [β]) using 1
    all_goals try rfl
    all_goals norm_num [zSecond, β, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    all_goals ring
  have hz0 : HasDerivAt (zFirst lam 1 1) (1-lam) β := by
    convert (hasDerivAt_const β (1-lam)).sub (hg.mul hz1) using 1
    all_goals try rfl
    all_goals norm_num [zFirst, zSecond, β, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  have hr0 := ((hasDerivAt_const β (1:ℝ)).sub hz0).sub (hg.mul hz1)
  have hr1 := (hasDerivAt_const β (1:ℝ)).sub (hs.mul hz1)
  have h := (((hr0.pow 2).add (hr1.pow 2)).div_const 2).add ((hz0.add hz1).const_mul lam)
  convert h using 1
  all_goals try rfl
  all_goals norm_num [bothValue, zFirst, zSecond, β, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  all_goals ring

private theorem right_value_derivative (lam pA pAB pB : ℝ) :
    HasDerivAt (rightValue lam pA pAB pB) (pAB*lam*(1-lam)) (Real.pi/2) := by
  have h := ((hasDerivAt_const (Real.pi/2) (pA*(lam-lam^2/2))).add
    ((both_value_derivative lam).const_mul pAB)).add
    (((hasDerivAt_const (Real.pi/2) (1/2:ℝ)).sub
      ((((Real.hasDerivAt_sin (Real.pi/2)).sub_const lam).pow 2).div_const 2)).const_mul pB)
  convert h using 1
  all_goals try rfl
  all_goals norm_num [rightValue, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  all_goals ring

private theorem inward_descent {f : ℝ → ℝ} {a b dl dr : ℝ} (hab : a < b)
    (hl : HasDerivAt f dl a) (hr : HasDerivAt f dr b) (hdl : dl < 0) (hdr : 0 < dr) :
    (∃ x ∈ Ioo a b, f x < f a) ∧ (∃ x ∈ Ioo a b, f x < f b) := by
  constructor
  · have ht : Tendsto (slope f a) (𝓝[>] a) (𝓝 dl) :=
      (hasDerivWithinAt_iff_tendsto_slope' (by simp : a ∉ Ioi a)).mp hl.hasDerivWithinAt
    have hn : ∀ᶠ x in 𝓝[>] a, slope f a x < 0 := ht.eventually_lt_const hdl
    have hb : ∀ᶠ x in 𝓝[>] a, x < b :=
      (eventually_lt_nhds hab).filter_mono nhdsWithin_le_nhds
    have hself : ∀ᶠ x in 𝓝[>] a, a < x := self_mem_nhdsWithin
    obtain ⟨x,hx,hs,hxb⟩ := (hself.and (hn.and hb)).exists
    refine ⟨x,⟨hx,hxb⟩,?_⟩
    rw [slope_def_field] at hs
    have hh := (div_lt_iff₀ (sub_pos.mpr hx)).mp hs
    linarith
  · have ht : Tendsto (slope f b) (𝓝[<] b) (𝓝 dr) :=
      (hasDerivWithinAt_iff_tendsto_slope' (by simp : b ∉ Iio b)).mp hr.hasDerivWithinAt
    have hp : ∀ᶠ x in 𝓝[<] b, 0 < slope f b x := ht.eventually_const_lt hdr
    have ha : ∀ᶠ x in 𝓝[<] b, a < x :=
      (eventually_gt_nhds hab).filter_mono nhdsWithin_le_nhds
    have hself : ∀ᶠ x in 𝓝[<] b, x < b := self_mem_nhdsWithin
    obtain ⟨x,hx,hs,hax⟩ := (hself.and (hp.and ha)).exists
    refine ⟨x,⟨hax,hx⟩,?_⟩
    rw [slope_def_field] at hs
    have hh := (lt_div_iff_of_neg (sub_neg.mpr hx)).mp hs
    linarith

/-- Both endpoint derivatives of the genuine optimized four-point objective, ambient
neighborhood differentiability, all interval minimizers, and one common improvement. -/
theorem partial_absorption
    (lam p0 pA pAB pB : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hp0 : 0 ≤ p0) (hpA : 0 ≤ pA) (hpAB : 0 ≤ pAB) (hpB : 0 ≤ pB)
    (hprob : p0+pA+pAB+pB = 1)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2)
    (hAB : 0 < pAB) (hB : 0 < pB) :
    let D := rotatingDictionary u v hu hv huv
    let J := objective lam p0 pA pAB pB u v hu hv huv
    (D (Real.pi/4)).1 1 = bisector u v ∧ (D (Real.pi/2)).1 1 = v ∧
    (∀ α x, ∃ c, FeasibleCode c ∧ codeCost lam x (D α) = codeEnergy lam x (D α) c) ∧
    (∃ U : Set ℝ, IsOpen U ∧ Real.pi/4 ∈ U ∧ ∀ α ∈ U, DifferentiableAt ℝ J α) ∧
    (∃ V : Set ℝ, IsOpen V ∧ Real.pi/2 ∈ V ∧ ∀ α ∈ V, DifferentiableAt ℝ J α) ∧
    HasDerivAt J (-pB*(1/Real.sqrt 2-lam)/Real.sqrt 2) (Real.pi/4) ∧
    HasDerivAt J (pAB*lam*(1-lam)) (Real.pi/2) ∧
    HasDerivWithinAt J (-pB*(1/Real.sqrt 2-lam)/Real.sqrt 2)
      (Icc (Real.pi/4) (Real.pi/2)) (Real.pi/4) ∧
    HasDerivWithinAt J (pAB*lam*(1-lam)) (Icc (Real.pi/4) (Real.pi/2)) (Real.pi/2) ∧
    -pB*(1/Real.sqrt 2-lam)/Real.sqrt 2 < 0 ∧ 0 < pAB*lam*(1-lam) ∧
    (∀ α ∈ Icc (Real.pi/4) (Real.pi/2),
      IsMinOn J (Icc (Real.pi/4) (Real.pi/2)) α → α ∈ Ioo (Real.pi/4) (Real.pi/2)) ∧
    ∃ α ∈ Ioo (Real.pi/4) (Real.pi/2), J α < J (Real.pi/4) ∧ J α < J (Real.pi/2) := by
  dsimp only
  let J := objective lam p0 pA pAB pB u v hu hv huv
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hinv : 1/Real.sqrt 2 < 1 := by
    rw [div_lt_one hsqrt]
    nlinarith [Real.sqrt_nonneg 2]
  have hunit : lam < 1 := hsmall.trans hinv
  have hleft := left_value_eventually lam p0 pA pAB pB u v hu hv huv hlam hsmall
  have hright := right_value_eventually lam p0 pA pAB pB u v hu hv huv hlam hunit
  have hl : HasDerivAt J (-pB*(1/Real.sqrt 2-lam)/Real.sqrt 2) (Real.pi/4) := by
    have hq : Real.sqrt 2/2 = 1/Real.sqrt 2 := by field_simp; nlinarith
    have h := (left_value_derivative lam pA pAB pB (Real.pi/4)).congr_of_eventuallyEq hleft
    convert h using 1
    all_goals try rfl
    all_goals simp only [Real.cos_pi_div_four, Real.sin_pi_div_four, sub_self,
      mul_zero, sub_zero, hq]
    all_goals ring
  have hr : HasDerivAt J (pAB*lam*(1-lam)) (Real.pi/2) :=
    (right_value_derivative lam pA pAB pB).congr_of_eventuallyEq hright
  have hld : ∀ᶠ α in 𝓝 (Real.pi/4), DifferentiableAt ℝ J α := by
    filter_upwards [hleft.eventuallyEq_nhds] with α he
    exact he.differentiableAt_iff.mpr (left_value_derivative lam pA pAB pB α).differentiableAt
  have hdc : Continuous (fun α : ℝ => 1-Real.cos α^2) := by fun_prop
  have hne : 1-Real.cos (Real.pi/2)^2 ≠ 0 := by norm_num
  have hrd : ∀ᶠ α in 𝓝 (Real.pi/2), DifferentiableAt ℝ J α := by
    filter_upwards [hright.eventuallyEq_nhds,hdc.continuousAt.eventually_ne hne] with α he hd
    apply he.differentiableAt_iff.mpr
    unfold rightValue bothValue zFirst zSecond
    fun_prop (disch := assumption)
  obtain ⟨U,hU,hoU,hqU⟩ := eventually_nhds_iff.mp hld
  obtain ⟨V,hV,hoV,hrV⟩ := eventually_nhds_iff.mp hrd
  have hdl : -pB*(1/Real.sqrt 2-lam)/Real.sqrt 2 < 0 := by
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hB) (sub_pos.mpr hsmall)) hsqrt
  have hdr : 0 < pAB*lam*(1-lam) := mul_pos (mul_pos hAB hlam) (sub_pos.mpr hunit)
  have hab : Real.pi/4 < Real.pi/2 := by linarith [Real.pi_pos]
  obtain ⟨⟨xL,hxL,hcostL⟩,⟨xR,hxR,hcostR⟩⟩ := inward_descent hab hl hr hdl hdr
  refine ⟨?_,?_,(fun α x => cost_attained lam x _ hlam),⟨U,hoU,hqU,hU⟩,
    ⟨V,hoV,hrV,hV⟩,hl,hr,hl.hasDerivWithinAt,hr.hasDerivWithinAt,hdl,hdr,?_,?_⟩
  · change Real.cos (Real.pi/4) • u + Real.sin (Real.pi/4) • v = bisector u v
    rw [Real.cos_pi_div_four,Real.sin_pi_div_four]
    have hk : Real.sqrt 2/2 = (Real.sqrt 2)⁻¹ := by field_simp; nlinarith
    simp [hk,bisector,smul_add]
  · simp [rotatingDictionary]
  · intro α hα hmin
    constructor
    · by_contra h
      have he : α = Real.pi/4 := le_antisymm (le_of_not_gt h) hα.1
      subst α
      exact (not_le_of_gt hcostL) (hmin ⟨hxL.1.le,hxL.2.le⟩)
    · by_contra h
      have he : α = Real.pi/2 := le_antisymm hα.2 (le_of_not_gt h)
      subst α
      exact (not_le_of_gt hcostR) (hmin ⟨hxR.1.le,hxR.2.le⟩)
  · by_cases hcomp : J (Real.pi/4) ≤ J (Real.pi/2)
    · exact ⟨xL,hxL,hcostL,hcostL.trans_le hcomp⟩
    · exact ⟨xR,hxR,hcostR.trans (lt_of_not_ge hcomp),hcostR⟩

end D5.S3.Estimation.WhiteBoxLossFiberLaw.PartialAbsorption
