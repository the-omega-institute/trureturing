/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Covariance transport in the actual four-point physical coordinates. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccupationTransport
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedExternalCoefficient

/-! Inverse half-coordinate transport of the signed covariance and labelled Gaussian. -/

set_option autoImplicit false

noncomputable section
open Complex Filter
open scoped Topology BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMPhysicalCovariance

open OriginalFourMActualChart
  (Chart Puncture parameter scale scaleRoot loweringParameter periodRoot relativeB relativeD)
open OriginalFourMSignedOverlap (legSign chartCovariance)
open OriginalGaussianExternalAnalyticCandidate (b)
open OriginalGaussianExternalSignedCandidate (h cauchy)
open OriginalFourMOccupationTransport
  (flags inverseRoot physicalSource signed_physical_source_transport)
open private chartPuncture chosenChartSource chart_parameter_ne_one chart_parameter_ne_zero from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap
open private rawLocal halfJacobian freeCorrection chartScale bLift from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
open private scale_ne from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart
open private chartPuncture_flags inverseRoot_zero inverseRoot_sq inverseRoot_analytic
  rawLocal_analytic root_ne physicalSource_analytic physicalPoint from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccupationTransport

open LatticeGeneratingFieldLocality (LatticeData)
open OriginalFourMActualChart (pullB pullD spatialKernel)
open OriginalGaussianExternalSignedCandidate (E G K rho rationalT)
open OriginalGaussianExternalCandidateCore (rightChart leftChart)
open private chartW chartW_analytic chartW_sum_ne_zero ratT_spatial
  legMap legMap_chart spatial_legMap legMap_involution legMap_sub_one covOnChart from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap
open private chartDifference from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
open private p q s from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart

private def jac (c : Chart) (x : ℝ) (i : Puncture) (u : ℂ) : ℂ :=
  halfJacobian c x i (inverseRoot c x i u)

private def slotCorrection (c : Chart) (x : ℝ) (i j : Puncture) (u v : ℂ) : ℂ :=
  if (flags c i).1 = (flags c j).1 ∧ (flags c i).2 = (flags c j).2 then
    freeCorrection c i (inverseRoot c x i u) (inverseRoot c x i v)
  else 0

private def slotFree (c : Chart) (x : ℝ) (i j : Puncture) (u v : ℂ) : ℂ :=
  if (flags c i).1 = (flags c j).1 ∧ (flags c i).2 = (flags c j).2 then
    cauchy (flags c i).2 (flags c i).2 (rawLocal c x i u) (rawLocal c x i v)
  else 0

/-- The actual normal covariance pulled to physical coordinates, with
the inverse lowering contraction included only at the same puncture. -/
def physicalCovariance (upperA : Bool) (c : Chart) (x : ℝ) (i j : Puncture)
    (u v : ℂ) : ℂ :=
  (chartCovariance upperA c x (flags c i).1 (flags c j).1 (flags c i).2 (flags c j).2
    (rawLocal c x i u) (rawLocal c x j v) - slotCorrection c x i j u v) /
    (jac c x i u * jac c x j v)

private theorem comp_fst {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (fun uv : ℂ × ℂ => f uv.1) (0, 0) :=
  hf.comp_of_eq analyticAt_fst rfl

private theorem comp_snd {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (fun uv : ℂ × ℂ => f uv.2) (0, 0) :=
  hf.comp_of_eq analyticAt_snd rfl

private theorem physicalCovariance_analytic (upperA : Bool) {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) (c : Chart) (i j : Puncture) :
    AnalyticAt ℂ (fun uv : ℂ × ℂ => physicalCovariance upperA c x i j uv.1 uv.2) (0, 0) := by
  have hbi := inverseRoot_analytic hx hx1 c i
  have hi := rawLocal_analytic hx hx1 c i
  have hj := rawLocal_analytic hx hx1 c j
  have hi₀ : rawLocal c x i 0 = 0 := by simp [rawLocal]
  have hj₀ : rawLocal c x j 0 = 0 := by simp [rawLocal]
  have h₁ := comp_fst hi
  have h₂ := comp_snd hj
  let F : ℂ × ℂ → ℂ × ℂ := fun uv => (rawLocal c x i uv.1, rawLocal c x j uv.2)
  have hpair : AnalyticAt ℂ F (0, 0) := h₁.prod h₂
  have hF₀ : F (0, 0) = (0, 0) := Prod.ext hi₀ hj₀
  have hcov : AnalyticAt ℂ (fun uv : ℂ × ℂ => chartCovariance upperA c x
      (flags c i).1 (flags c j).1 (flags c i).2 (flags c j).2
      (rawLocal c x i uv.1) (rawLocal c x j uv.2)) (0, 0) := by
    let C : ℂ × ℂ → ℂ := fun uv => chartCovariance upperA c x
      (flags c i).1 (flags c j).1 (flags c i).2 (flags c j).2 uv.1 uv.2
    have ha : AnalyticAt ℂ C (0, 0) :=
      OriginalFourMSignedOverlap.chart_covariance_analytic hx hx1 upperA c
        (flags c i).1 (flags c j).1 (flags c i).2 (flags c j).2
    change AnalyticAt ℂ (C ∘ F) (0, 0)
    exact AnalyticAt.comp_of_eq (f := F) (g := C) ha hpair hF₀
  have hJ (i : Puncture) : AnalyticAt ℂ (jac c x i) 0 :=
    analyticAt_const.div ((inverseRoot_analytic hx hx1 c i).pow 3) (by simp [inverseRoot_zero])
  have hF : AnalyticAt ℂ (fun uv : ℂ × ℂ => slotCorrection c x i j uv.1 uv.2) (0, 0) := by
    unfold slotCorrection
    split
    · unfold freeCorrection
      have h₁ := comp_fst hbi
      have h₂ := comp_snd hbi
      exact (analyticAt_const.mul (analyticAt_const.add (h₁.mul h₂))).div
        (((analyticAt_const.mul h₁).mul h₂).mul ((h₁.add h₂).pow 2))
        (by norm_num [inverseRoot_zero])
    · exact analyticAt_const
  exact (hcov.sub hF).div ((comp_fst (hJ i)).mul (comp_snd (hJ j)))
    (by simp [jac, halfJacobian, inverseRoot_zero, root_ne hx hx1])

private def ellipticX (c : Chart) (x : ℝ) (i : Puncture) (u : ℂ) : ℂ :=
  let U := physicalPoint x i u
  (U - p c x) / (U - q c x)

private theorem raw_ellipticX {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (c : Chart) (i : Puncture) {u : ℂ}
    (hu : u ≠ 0) (hq : physicalPoint x i u - q c x ≠ 0)
    (hraw : scale c (x : ℂ) i + loweringParameter c i * u ≠ 0)
    (hrawB : b (rawLocal c x i u) ≠ 0) :
    (if (flags c i).1 then leftChart (flags c i).2 (parameter c x) (rawLocal c x i u)
      else rightChart (flags c i).2 (rawLocal c x i u)) = ellipticX c x i u := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hx1' : (x : ℂ) ≠ 1 := by exact_mod_cast hx1.ne
  have h1x := sub_ne_zero.mpr hx1'.symm
  have hnx1 : -1 + (x : ℂ) ≠ 0 := by simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr hx1'
  have hraw0 : rawLocal c x i u ≠ 0 := div_ne_zero hu hraw
  cases c <;> cases i <;>
    simp only [flags, Bool.false_eq_true, ite_true, ite_false, rightChart, leftChart, parameter, rawLocal,
      scale, loweringParameter, zero_mul, one_mul, add_zero, sub_zero, sub_sub_cancel,
      ellipticX, physicalPoint, p, q] at hq hraw ⊢ <;>
    simp only [b, rawLocal, scale, loweringParameter, zero_mul, one_mul, add_zero] at hrawB hraw0 <;>
    field_simp [hu, hx0, h1x, hnx1, hq, hraw, hrawB, hraw0] <;> try ring
  · have hd : -u + (x : ℂ) ≠ 0 := by
      rwa [show -u + (x : ℂ) = -(u - (x : ℂ)) by ring, neg_ne_zero]
    field_simp [hd]
    ring
  · have hd : (-1 : ℂ) + (x : ℂ) * u ≠ 0 := by
      intro he
      apply hraw
      apply mul_right_cancel₀ hx0
      rw [zero_mul, add_mul, neg_mul, inv_mul_cancel₀ hx0]
      linear_combination he
    have hc : 1 - (x : ℂ) * u * (-1 + (x : ℂ) * u)⁻¹ =
        -((-1 + (x : ℂ) * u)⁻¹) := by
      field_simp [hd]
      ring
    rw [hc, inv_neg, inv_inv]
    field_simp [hd]
    ring

private theorem physical_transition {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (i : Puncture)
    {u : ℂ} (hA : physicalPoint x i u - (x : ℂ) ≠ 0) (h0 : physicalPoint x i u ≠ 0) :
    ((x : ℂ) * ellipticX .A x i u - 1 ≠ 0) ∧
    pullB x (ellipticX .A x i u) = ellipticX .B x i u ∧
    pullD x (ellipticX .A x i u) = ellipticX .D x i u := by
  have hx1' : (x : ℂ) ≠ 1 := by exact_mod_cast hx1.ne
  have h1x := sub_ne_zero.mpr hx1'
  let U := physicalPoint x i u
  change U - (x : ℂ) ≠ 0 at hA
  change U ≠ 0 at h0
  have he : (x : ℂ) * ((U - 1)/(U - (x : ℂ))) - 1 = ((x : ℂ)-1)*U/(U-(x : ℂ)) := by
    field_simp [hA]
    ring
  refine ⟨?_, ?_, ?_⟩
  · change (x : ℂ) * ((U - 1)/(U - (x : ℂ))) - 1 ≠ 0
    rw [he]
    exact div_ne_zero (mul_ne_zero h1x h0) hA
  · simp only [pullB, ellipticX, p, q, sub_zero]
    change ((x : ℂ) - 1) / ((x : ℂ)*((U - 1)/(U-(x : ℂ))) - 1) = (U-(x : ℂ))/U
    rw [he]
    field_simp [hA, h0, h1x]
  · simp only [pullD, ellipticX, p, q, sub_zero]
    change ((x : ℂ) - 1) * ((U - 1)/(U-(x : ℂ))) /
      ((x : ℂ)*((U - 1)/(U-(x : ℂ))) - 1) = (U-1)/U
    rw [he]
    field_simp [hA, h0, h1x]

private theorem ellipticX_ne {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (c : Chart)
    (i j : Puncture) {u v : ℂ}
    (hu : physicalPoint x i u - q c x ≠ 0) (hv : physicalPoint x j v - q c x ≠ 0)
    (hsep : physicalPoint x i u ≠ physicalPoint x j v) :
    ellipticX c x i u - ellipticX c x j v ≠ 0 := by
  have hp : p c x - q c x ≠ 0 := by
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hx1' : (x : ℂ) ≠ 1 := by exact_mod_cast hx1.ne
    cases c <;> simp [p, q, hx0, sub_ne_zero.mpr hx1'.symm]
  have h : ellipticX c x i u - ellipticX c x j v =
      (p c x - q c x) * (physicalPoint x i u - physicalPoint x j v) /
        ((physicalPoint x i u - q c x) * (physicalPoint x j v - q c x)) := by
    unfold ellipticX
    field_simp [hu, hv]
    ring
  rw [h]
  exact div_ne_zero (mul_ne_zero hp (sub_ne_zero.mpr hsep)) (mul_ne_zero hu hv)

private theorem signed_spatial (upperA : Bool) {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (c : Chart) (l k e f : Bool) {u v : ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hbu : b u ≠ 0) (hbv : b v ≠ 0)
    (hhu : h e u (parameter c x) ≠ 0) (hhv : h f v (parameter c x) ≠ 0)
    (hW : chartW c x e u + chartW c x f v ≠ 0) (hE : E e f u v (parameter c x) ≠ 0)
    (hG : l = k → G e f u v ≠ 0)
    (hsep : (if l then leftChart e (parameter c x) u else rightChart e u) -
      (if k then leftChart f (parameter c x) v else rightChart f v) ≠ 0) :
    let r := parameter c (x : ℂ)
    let X := if l then leftChart e r u else rightChart e u
    let Y := if k then leftChart f r v else rightChart f v
    chartCovariance upperA c x l k e f u v + (if l = k ∧ e = f then cauchy e f u v else 0) =
      (legSign l * chosenChartSource c x e u) * (legSign k * chosenChartSource c x f v) *
        covOnChart upperA c x X Y := by
  dsimp only
  let r := parameter c (x : ℂ)
  have hright (e : Bool) {v : ℂ} (hv : v ≠ 0) (hbv : b v ≠ 0) :
      rightChart e v - 1 ≠ 0 := by
    cases e
    · exact fun he => hbv (by simpa [rightChart, b] using congrArg Neg.neg he)
    · simp only [rightChart, ite_true, one_div]
      intro he
      exact hbv (by simp [b, inv_eq_one.mp (sub_eq_zero.mp he)])
  have hX := hright e hu hbu
  have hY := hright f hv hbv
  have hleg (e : Bool) {u : ℂ} (hu : u ≠ 0) (hbu : b u ≠ 0) :
      legMap r (rightChart e u) = leftChart e r u :=
    legMap_chart e hu (fun he => hbu (by simp [b, he]))
  have hr : r ≠ 0 := chart_parameter_ne_zero hx hx1 c
  by_cases hl : l = k
  · subst k
    have hJ := (OriginalFourMSignedOverlap.chart_spatial_overlap hx hx1 upperA c e f
      hu hv hbu hbv hhu hhv hW (hG rfl) hE).1 l
    have hrr' : rightChart e u - rightChart f v =
        (if f then -G e f u v else G e f u v) /
          ((if e then u else 1) * (if f then v else 1)) := by
      cases e <;> cases f <;> simp [rightChart, G] <;> field_simp [hu, hv] <;> ring
    have hrr : rightChart e u - rightChart f v ≠ 0 := by
      rw [hrr']
      refine div_ne_zero ?_ (mul_ne_zero ?_ ?_)
      · cases f <;> simp [hG rfl]
      · cases e <;> simp [hu]
      · cases f <;> simp [hv]
    cases l
    · simpa [covOnChart, legSign, sub_add_cancel] using congrArg
        (fun a => a + (if e = f then cauchy e f u v else 0)) hJ
    · simp only [ite_true]
      rw [show leftChart e r u = legMap r (rightChart e u) from (hleg e hu hbu).symm,
          show leftChart f r v = legMap r (rightChart f v) from (hleg f hv hbv).symm,
          covOnChart, spatial_legMap hr hX hY hrr]
      simpa [legSign, sub_add_cancel] using congrArg
        (fun a => a + (if e = f then cauchy e f u v else 0)) hJ
  · have hT := ratT_spatial e f hu hbv hE
    rw [chartCovariance, ite_eq_right hl, hT, ite_eq_right (fun he => hl he.1)]
    cases l <;> cases k
    · exact (hl rfl).elim
    · simp only [covOnChart, Bool.false_eq_true, ite_false, ite_true, legSign, one_mul,
        neg_one_mul, add_zero, mul_neg, neg_mul]
    · have hSep : leftChart e r u - rightChart f v ≠ 0 := by simpa using hsep
      have hcross : rightChart e u - leftChart f r v ≠ 0 := by
        intro he
        apply hSep
        rw [← hleg e hu hbu, sub_eq_zero.mpr (by
          rw [sub_eq_zero.mp he, ← hleg f hv hbv, legMap_involution hr hY])]
      have hg := spatial_legMap hr hX
        (by rw [← hleg f hv hbv, legMap_sub_one hY]; exact div_ne_zero hr hY) hcross
      rw [hleg e hu hbu, ← hleg f hv hbv, legMap_involution hr hY] at hg
      simp only [covOnChart, legSign, Bool.false_eq_true, ite_true, ite_false, one_mul,
        neg_one_mul, neg_mul, add_zero]
      rw [hg, hleg f hv hbv]
    · exact (hl rfl).elim

private theorem point_injective (x : ℂ) (i : Puncture) :
    Function.Injective (physicalPoint x i) := by
  cases i
  all_goals unfold physicalPoint
  · intro a b h; exact add_left_cancel h
  · intro a b h; exact add_left_cancel h
  · exact fun _ _ h => h
  · exact inv_injective

private theorem dense_avoid (f : ℂ → ℂ) (hf : Function.Injective f) (a : ℂ) :
    Dense {v | f v ≠ a} := by
  by_cases h : a ∈ Set.range f
  · obtain ⟨w, rfl⟩ := h
    convert (dense_compl_singleton w) using 1
    ext v
    exact not_congr hf.eq_iff
  · convert (dense_univ : Dense (Set.univ : Set ℂ)) using 1
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact fun e => h ⟨v, e⟩

private def regularPoint (x : ℂ) (i : Puncture) : Set ℂ :=
  ({0} : Set ℂ)ᶜ ∩ ({v | physicalPoint x i v ≠ 0} ∩ {v | physicalPoint x i v ≠ x})

private theorem regularPoint_dense (x : ℂ) (i : Puncture) : Dense (regularPoint x i) := by
  have h : ∀ a, IsOpen {v | physicalPoint x i v ≠ a} := by
    intro a
    by_cases ha : a ∈ Set.range (physicalPoint x i)
    · obtain ⟨w, rfl⟩ := ha
      convert (isOpen_compl_singleton (x := w)) using 1
      ext v
      exact not_congr (point_injective x i).eq_iff
    · convert (isOpen_univ : IsOpen (Set.univ : Set ℂ)) using 1
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact fun e => ha ⟨v, e⟩
  exact (dense_compl_singleton 0).inter_of_isOpen_left
    ((dense_avoid _ (point_injective x i) 0).inter_of_isOpen_left
      (dense_avoid _ (point_injective x i) x) (h 0)) isOpen_compl_singleton

private def regularPair (x : ℂ) (i j : Puncture) : Set (ℂ × ℂ) :=
  {uv | uv.1 ∈ regularPoint x i ∧ uv.2 ∈ regularPoint x j ∧
    physicalPoint x i uv.1 ≠ physicalPoint x j uv.2}

private theorem regularPair_dense (x : ℂ) (i j : Puncture) : Dense (regularPair x i j) := by
  intro uv
  refine mem_closure_iff_nhds.mpr fun S hS => ?_
  obtain ⟨U, hU, V, hV, hsub⟩ := mem_nhds_prod_iff.mp hS
  obtain ⟨u, hu, hregu⟩ := mem_closure_iff_nhds.mp (regularPoint_dense x i uv.1) U hU
  have hd := (regularPoint_dense x j).inter_of_isOpen_right
    (dense_avoid _ (point_injective x j) (physicalPoint x i u)) (by
      by_cases ha : physicalPoint x i u ∈ Set.range (physicalPoint x j)
      · obtain ⟨w, hw⟩ := ha
        rw [← hw]
        convert (isOpen_compl_singleton (x := w)) using 1
        ext v
        exact not_congr (point_injective x j).eq_iff
      · convert (isOpen_univ : IsOpen (Set.univ : Set ℂ)) using 1
        ext v
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact fun e => ha ⟨v, e⟩)
  obtain ⟨v, hv, hregv, hsep⟩ := mem_closure_iff_nhds.mp (hd uv.2) V hV
  exact ⟨(u,v), hsub ⟨hu,hv⟩, hregu,hregv,Ne.symm hsep⟩

private theorem extend_regularPair {x : ℂ} {i j : Puncture} {F H : ℂ × ℂ → ℂ}
    (hF : AnalyticAt ℂ F (0, 0)) (hH : AnalyticAt ℂ H (0, 0))
    (h : ∀ᶠ uv in 𝓝 (0, 0), uv ∈ regularPair x i j → F uv = H uv) :
    F =ᶠ[𝓝 (0, 0)] H := by
  have he : ∀ᶠ uv in 𝓝 (0, 0),
      (uv ∈ regularPair x i j → F uv = H uv) ∧ AnalyticAt ℂ F uv ∧ AnalyticAt ℂ H uv :=
    h.and (hF.eventually_analyticAt.and hH.eventually_analyticAt)
  obtain ⟨U, hU, hUo, h0⟩ := mem_nhds_iff.mp he
  have hf : ContinuousOn F U := fun a ha => (hU ha).2.1.continuousAt.continuousWithinAt
  have hg : ContinuousOn H U := fun a ha => (hU ha).2.2.continuousAt.continuousWithinAt
  have hEq : Set.EqOn F H (U ∩ regularPair x i j) := fun a ha => (hU ha.1).1 ha.2
  exact Filter.mem_of_superset (hUo.mem_nhds h0)
    (hEq.of_subset_closure hf hg Set.inter_subset_left ((regularPair_dense x i j).open_subset_closure_inter hUo))

private theorem raw_near {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (c : Chart) (i : Puncture) :
    ∀ᶠ u : ℂ in 𝓝 0,
      scale c (x : ℂ) i + loweringParameter c i * u ≠ 0 ∧
      b (rawLocal c x i u) ≠ 0 ∧
      h (flags c i).2 (rawLocal c x i u) (parameter c x) ≠ 0 ∧
      inverseRoot c x i u ≠ 0 := by
  have hlocal : ∀ᶠ u : ℂ in 𝓝 0, scale c (x : ℂ) i + loweringParameter c i * u ≠ 0 :=
    (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).eventually_ne
      (by simpa using scale_ne hx hx1 c i)
  have ha := (rawLocal_analytic hx hx1 c i).continuousAt
  have hbc : ContinuousAt (fun u => b (rawLocal c x i u)) 0 := continuousAt_const.sub ha
  have hh : ContinuousAt (fun u => h (flags c i).2 (rawLocal c x i u) (parameter c x)) 0 := by
    cases (flags c i).2 <;> simp only [h, Bool.false_eq_true, ite_false, ite_true]
    · exact continuousAt_const.sub ha
    · exact continuousAt_const.sub (continuousAt_const.mul ha)
  have hh₀ : h (flags c i).2 (rawLocal c x i 0) (parameter c x) ≠ 0 := by
    cases (flags c i).2 <;> simp [h, rawLocal, chart_parameter_ne_one hx hx1 c]
  exact hlocal.and ((hbc.eventually_ne (y := (0 : ℂ)) (by simp [b, rawLocal])).and
    ((hh.eventually_ne hh₀).and ((inverseRoot_analytic hx hx1 c i).continuousAt.eventually_ne
      (y := (0 : ℂ)) (by simp [inverseRoot_zero]))))

private theorem chart_pair_geometry (upperA : Bool) {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (c : Chart) (i j : Puncture) :
    ∀ᶠ uv in 𝓝 ((0 : ℂ), (0 : ℂ)), uv ∈ regularPair x i j →
      (chartCovariance upperA c x (flags c i).1 (flags c j).1 (flags c i).2 (flags c j).2
        (rawLocal c x i uv.1) (rawLocal c x j uv.2) + slotFree c x i j uv.1 uv.2) /
        (jac c x i uv.1 * jac c x j uv.2) =
      physicalSource c x i uv.1 * physicalSource c x j uv.2 *
        covOnChart upperA c x (ellipticX c x i uv.1) (ellipticX c x j uv.2) := by
  let U := fun uv : ℂ × ℂ => rawLocal c x i uv.1
  let V := fun uv : ℂ × ℂ => rawLocal c x j uv.2
  let e := (flags c i).2
  let f := (flags c j).2
  let r := parameter c (x : ℂ)
  have hU : ContinuousAt U (0, 0) :=
    (comp_fst (rawLocal_analytic hx hx1 c i)).continuousAt
  have hV : ContinuousAt V (0, 0) :=
    (comp_snd (rawLocal_analytic hx hx1 c j)).continuousAt
  have hU₀ : U (0, 0) = 0 := by simp [U, rawLocal]
  have hV₀ : V (0, 0) = 0 := by simp [V, rawLocal]
  have hW : ∀ᶠ uv in 𝓝 ((0 : ℂ), (0 : ℂ)), chartW c x e (U uv) + chartW c x f (V uv) ≠ 0 := by
    have hW₁ : ContinuousAt (chartW c x e) (U (0, 0)) := by
      rw [hU₀]; exact (chartW_analytic hx hx1 c e).continuousAt
    have hW₂ : ContinuousAt (chartW c x f) (V (0, 0)) := by
      rw [hV₀]; exact (chartW_analytic hx hx1 c f).continuousAt
    exact ((hW₁.comp hU).add (hW₂.comp hV)).eventually_ne (y := (0 : ℂ)) (by
      simpa only [Pi.add_apply, Function.comp_apply, hU₀, hV₀] using chartW_sum_ne_zero hx hx1 c e f)
  have hE : ∀ᶠ uv in 𝓝 ((0 : ℂ), (0 : ℂ)), E e f (U uv) (V uv) r ≠ 0 := by
    have he : ContinuousAt (fun uv => E e f (U uv) (V uv) r) (0, 0) := by
      cases e <;> cases f <;> simp [E, K, b] <;> fun_prop
    apply he.eventually_ne (y := (0 : ℂ))
    rw [hU₀, hV₀]
    cases e <;> cases f <;> simp [E, K, b, r, chart_parameter_ne_one hx hx1 c]
  have hMix : ∀ᶠ uv in 𝓝 ((0 : ℂ), (0 : ℂ)), 1 - U uv * V uv ≠ 0 :=
    (continuousAt_const.sub (hU.mul hV)).eventually_ne (y := (0 : ℂ)) (by simp [hU₀,hV₀])
  filter_upwards [continuous_fst.continuousAt.eventually (raw_near hx hx1 c i),
    continuous_snd.continuousAt.eventually (raw_near hx hx1 c j), hW, hE, hMix]
    with uv hi hj hW hE hM
  rintro ⟨⟨hi₀, hiP, hiQ⟩, ⟨hj₀, hjP, hjQ⟩, hsep⟩
  have hiq : physicalPoint x i uv.1 - q c x ≠ 0 := by
    cases c
    · exact sub_ne_zero.mpr hiQ
    · simpa [q] using hiP
    · simpa [q] using hiP
  have hjq : physicalPoint x j uv.2 - q c x ≠ 0 := by
    cases c
    · exact sub_ne_zero.mpr hjQ
    · simpa [q] using hjP
    · simpa [q] using hjP
  have hiX := raw_ellipticX hx hx1 c i (by simpa using hi₀) hiq hi.1 hi.2.1
  have hjX := raw_ellipticX hx hx1 c j (by simpa using hj₀) hjq hj.1 hj.2.1
  have hX := ellipticX_ne hx hx1 c i j hiq hjq hsep
  have hnU : U uv ≠ 0 := div_ne_zero (by simpa using hi₀) hi.1
  have hnV : V uv ≠ 0 := div_ne_zero (by simpa using hj₀) hj.1
  have hG : (flags c i).1 = (flags c j).1 → G e f (U uv) (V uv) ≠ 0 := by
    intro hl
    by_cases hef : e = f
    · simp only [G, hef, ite_true]
      intro h
      have h' := sub_eq_zero.mp h
      apply hX
      rw [← hiX, ← hjX, hl, show (flags c i).2 = (flags c j).2 from hef,
        show rawLocal c x i uv.1 = rawLocal c x j uv.2 from h', sub_self]
    · simpa only [G, hef, ite_false] using hM
  have hgeom := signed_spatial upperA hx hx1 c (flags c i).1 (flags c j).1 e f
    hnU hnV hi.2.1 hj.2.1 hi.2.2.1 hj.2.2.1 hW hE hG (by rwa [hiX, hjX])
  dsimp only at hgeom
  rw [hiX, hjX] at hgeom
  have hfree : slotFree c x i j uv.1 uv.2 =
      if (flags c i).1 = (flags c j).1 ∧ e = f then cauchy e f (U uv) (V uv) else 0 := by
    unfold slotFree
    by_cases he : (flags c i).1 = (flags c j).1 ∧ e = f
    · have hi : i = j := by
        rw [← chartPuncture_flags c i, ← chartPuncture_flags c j, he.1, show (flags c i).2 = (flags c j).2 from he.2]
      subst j
      rfl
    · have he' : ¬ ((flags c i).1 = (flags c j).1 ∧ (flags c i).2 = (flags c j).2) := he
      rw [ite_eq_right he, ite_eq_right he']
  rw [hfree, hgeom]
  unfold physicalSource
  simp only [jac, div_eq_mul_inv, mul_inv]
  ring

private theorem same_flags (c : Chart) {i j : Puncture}
    (he : (flags c i).1 = (flags c j).1 ∧ (flags c i).2 = (flags c j).2) : i = j := by
  rw [← chartPuncture_flags c i, ← chartPuncture_flags c j, he.1, he.2]

private theorem subtraction_difference (D : LatticeData) (hu : IsUnit D.G.det)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (c : Chart) (i j : Puncture) :
    ∀ᶠ uv in 𝓝 ((0 : ℂ), (0 : ℂ)), uv ∈ regularPair x i j →
      (slotFree c x i j uv.1 uv.2 + slotCorrection c x i j uv.1 uv.2) /
        (jac c x i uv.1 * jac c x j uv.2) =
      (slotFree .A x i j uv.1 uv.2 + slotCorrection .A x i j uv.1 uv.2) /
        (jac .A x i uv.1 * jac .A x j uv.2) := by
  classical
  by_cases hi : i = j
  · subst j
    have hsum (c : Chart) : ∀ᶠ uv in 𝓝 ((0 : ℂ), (0 : ℂ)),
        inverseRoot c x i uv.1 + inverseRoot c x i uv.2 ≠ 0 := by
      have hcont : ContinuousAt (fun uv : ℂ × ℂ =>
          inverseRoot c x i uv.1 + inverseRoot c x i uv.2) (0, 0) :=
        (comp_fst (inverseRoot_analytic hx hx1 c i)).continuousAt.add
          (comp_snd (inverseRoot_analytic hx hx1 c i)).continuousAt
      exact hcont.eventually_ne (y := (0 : ℂ)) (by norm_num [inverseRoot_zero])
    filter_upwards [continuous_fst.continuousAt.eventually (raw_near hx hx1 .A i),
      continuous_snd.continuousAt.eventually (raw_near hx hx1 .A i),
      continuous_fst.continuousAt.eventually (raw_near hx hx1 c i),
      continuous_snd.continuousAt.eventually (raw_near hx hx1 c i), hsum .A, hsum c]
      with uv hau hav hcu hcv ha hc
    intro hsep
    have huv : uv.1 ≠ uv.2 := fun h => hsep.2.2 (congrArg (physicalPoint x i) h)
    have hfree := OriginalFourMChartProduct.physical_free_subtraction_difference D hu hx hx1
      .A c i (flags .A i).2 (flags c i).2 hau.1 hav.1 hcu.1 hcv.1 huv
      (inverseRoot_sq ..) (inverseRoot_sq ..) (inverseRoot_sq ..) (inverseRoot_sq ..)
      hau.2.2.2 hav.2.2.2 hcu.2.2.2 hcv.2.2.2 ha hc
    dsimp only at hfree
    simp only [slotFree, slotCorrection, true_and, ite_true, jac, add_div]
    linear_combination hfree
  · exact Eventually.of_forall fun uv _ => by
      simp only [slotFree, slotCorrection,
        ite_eq_right (fun he => hi (same_flags c he)), ite_eq_right (fun he => hi (same_flags .A he)),
        zero_add, zero_div]

private def relative : Chart → Puncture → ℂ
  | .A, _ => 1
  | .B, i => relativeB i
  | .D, i => relativeD i

private theorem relative_same_slot (c : Chart) (i : Puncture) : relative c i ^ 2 = 1 := by
  cases c <;> cases i <;> norm_num [relative, relativeB, relativeD]

private def physicalDiscrepancy (upperA : Bool) (c : Chart) (x : ℝ) (i j : Puncture)
    (u v : ℂ) : ℂ :=
  chartDifference upperA c x *
    ((chartScale c x * physicalSource .A x i u) * (chartScale c x * physicalSource .A x j v))

/-- Off the cusps, the physical-coordinate Gaussian covariance has the
same continuation in all three charts, including coincident evaluations.
The discrepancy is expressed in the signed common source units. -/
theorem signed_physical_covariance_transport (D : LatticeData) (hu : IsUnit D.G.det)
    (upperA : Bool) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (c : Chart) (i j : Puncture) :
    (fun uv : ℂ × ℂ => physicalCovariance upperA .A x i j uv.1 uv.2 -
      physicalDiscrepancy upperA c x i j uv.1 uv.2) =ᶠ[𝓝 (0, 0)]
    (fun uv : ℂ × ℂ => relative c i * relative c j * physicalCovariance upperA c x i j uv.1 uv.2) := by
  have hs (i : Puncture) :
      (fun u => chartScale c x * physicalSource .A x i u) =ᶠ[𝓝 (0 : ℂ)]
        (fun u => relative c i * physicalSource c x i u) := by
    cases c
    · simp [chartScale, relative]
    · exact (signed_physical_source_transport hx hx1 i).1
    · exact (signed_physical_source_transport hx hx1 i).2
  have hperiod (u v : ℂ) (huX : (x : ℂ) * ellipticX .A x i u - 1 ≠ 0)
      (hvX : (x : ℂ) * ellipticX .A x j v - 1 ≠ 0)
      (hsep : ellipticX .A x i u - ellipticX .A x j v ≠ 0)
      (htB : pullB x (ellipticX .A x i u) = ellipticX .B x i u)
      (htB' : pullB x (ellipticX .A x j v) = ellipticX .B x j v)
      (htD : pullD x (ellipticX .A x i u) = ellipticX .D x i u)
      (htD' : pullD x (ellipticX .A x j v) = ellipticX .D x j v) :
      covOnChart upperA .A x (ellipticX .A x i u) (ellipticX .A x j v) =
        chartScale c x ^ 2 *
          (covOnChart upperA c x (ellipticX c x i u) (ellipticX c x j v) +
            chartDifference upperA c x) := by
    obtain ⟨hB,hD⟩ := OriginalFourMPeriodSource.covariance_discrepancies upperA hx hx1
      huX hvX hsep
    rw [htB, htB'] at hB
    rw [htD, htD'] at hD
    cases c
    · simp [chartScale, chartDifference]
    · have hl : bLift x ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero)
        (ofReal_ne_zero.mpr (Real.sqrt_pos.2 hx).ne')
      rw [chartScale, inv_pow, ← div_eq_inv_mul, eq_div_iff (pow_ne_zero 2 hl)]
      change _ = covOnChart upperA .B x _ _ + _
      simp only [parameter] at hB
      simp only [covOnChart, chartDifference, parameter, bLift]
      linear_combination hB
    · rw [chartScale, inv_pow, ← div_eq_inv_mul, eq_div_iff (pow_ne_zero 2 I_ne_zero)]
      change _ = covOnChart upperA .D x _ _ + _
      simp only [covOnChart, chartDifference]
      linear_combination hD
  have hc₁ := physicalCovariance_analytic upperA hx hx1 .A i j
  have hc₂ := physicalCovariance_analytic upperA hx hx1 c i j
  have hd : AnalyticAt ℂ (fun uv : ℂ × ℂ =>
      physicalDiscrepancy upperA c x i j uv.1 uv.2) (0, 0) := by
    exact analyticAt_const.mul
      ((analyticAt_const.mul (comp_fst (physicalSource_analytic hx hx1 .A i))).mul
       (analyticAt_const.mul (comp_snd (physicalSource_analytic hx hx1 .A j))))
  apply extend_regularPair (x := (x : ℂ)) (i := i) (j := j) (hc₁.sub hd) (analyticAt_const.mul hc₂)
  filter_upwards [chart_pair_geometry upperA hx hx1 .A i j, chart_pair_geometry upperA hx hx1 c i j,
    subtraction_difference D hu hx hx1 c i j,
    continuous_fst.continuousAt.eventually (hs i), continuous_snd.continuousAt.eventually (hs j)]
    with uv hA hC hfree hsi hsj
  intro hreg
  have ⟨⟨_, hiP, hiQ⟩, ⟨_, hjP, hjQ⟩, hsep⟩ := hreg
  have hiq : physicalPoint x i uv.1 - (x : ℂ) ≠ 0 := sub_ne_zero.mpr hiQ
  have hjq : physicalPoint x j uv.2 - (x : ℂ) ≠ 0 := sub_ne_zero.mpr hjQ
  obtain ⟨hiX, hiB, hiD⟩ := physical_transition hx hx1 i hiq hiP
  obtain ⟨hjX, hjB, hjD⟩ := physical_transition hx hx1 j hjq hjP
  have hsepX := ellipticX_ne hx hx1 .A i j hiq hjq hsep
  have hp := hperiod uv.1 uv.2 hiX hjX hsepX hiB hjB hiD hjD
  have ha := hA hreg
  have hc := hC hreg
  have hf := hfree hreg
  have hslots :
      relative c i * relative c j *
        ((slotFree c x i j uv.1 uv.2 + slotCorrection c x i j uv.1 uv.2) /
          (jac c x i uv.1 * jac c x j uv.2)) =
      (slotFree c x i j uv.1 uv.2 + slotCorrection c x i j uv.1 uv.2) /
          (jac c x i uv.1 * jac c x j uv.2) := by
    by_cases h : (flags c i).1 = (flags c j).1 ∧ (flags c i).2 = (flags c j).2
    · have hij := same_flags c h
      subst j
      rw [← pow_two, relative_same_slot, one_mul]
    · simp [slotFree, slotCorrection, ite_eq_right h]
  have hg :
      physicalSource .A x i uv.1 * physicalSource .A x j uv.2 *
        covOnChart upperA .A x (ellipticX .A x i uv.1) (ellipticX .A x j uv.2) -
          physicalDiscrepancy upperA c x i j uv.1 uv.2 =
      relative c i * relative c j * (physicalSource c x i uv.1 * physicalSource c x j uv.2 *
        covOnChart upperA c x (ellipticX c x i uv.1) (ellipticX c x j uv.2)) := by
    rw [hp]
    unfold physicalDiscrepancy
    have ht : physicalSource .A x i uv.1 * physicalSource .A x j uv.2 * chartScale c x ^ 2 =
      (chartScale c x * physicalSource .A x i uv.1) *
        (chartScale c x * physicalSource .A x j uv.2) := by ring
    rw [← mul_assoc, ht, hsi, hsj]
    ring
  rw [← ha, ← hc] at hg
  change physicalCovariance upperA .A x i j uv.1 uv.2 -
      physicalDiscrepancy upperA c x i j uv.1 uv.2 =
    relative c i * relative c j * physicalCovariance upperA c x i j uv.1 uv.2
  simp only [physicalCovariance, sub_div]
  simp only [add_div] at hg hf hslots
  linear_combination hg + hf + hslots

open NativeAffineExternalCoefficient (coordinateDerivative coordinateJet jetOccupation)
open NativeAffineTransport (affineExponent)
open OriginalChargedRowSource (affineCoefficient)
open FactorialFockMetric (weight)
open private eval_affine from
  D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedExternalCoefficient

section Marked
variable {X J : Type*} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]

private def groupWeights (label : X → J) (v : X → ℂ) (j : J) : ℂ :=
  ∑ i, if label i = j then v i else 0

private theorem groupWeights_zero (label : X → J) : groupWeights label 0 = 0 := by
  funext j
  simp [groupWeights]

private theorem groupWeights_update (label : X → J) (v : X → ℂ) (i : X) (t : ℂ) :
    groupWeights label (Function.update v i t) =
      Function.update (groupWeights label v) (label i) (t + (groupWeights label v (label i) - v i)) := by
  funext j
  have h (v : X → ℂ) (j : J) :
      groupWeights label v j =
        (∑ a ∈ Finset.univ.erase i, if label a = j then v a else 0) +
          (if label i = j then v i else 0) :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  have he : (∑ a ∈ Finset.univ.erase i, if label a = j then Function.update v i t a else 0) =
      ∑ a ∈ Finset.univ.erase i, if label a = j then v a else 0 := by
    exact Finset.sum_congr rfl fun a ha => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]
  rw [h (Function.update v i t) j, he, Function.update_self]
  by_cases hj : j = label i
  · subst j
    rw [Function.update_self, h v (label i)]
    simp only [ite_true]
    ring
  · rw [Function.update_of_ne hj, h v j]
    simp only [ite_eq_right (Ne.symm hj)]

private theorem group_derivative (label : X → J) (i : X) (f : (J → ℂ) → ℂ) :
    coordinateDerivative i (f ∘ groupWeights label) =
      coordinateDerivative (label i) f ∘ groupWeights label := by
  funext v
  simp only [coordinateDerivative, Function.comp_apply, groupWeights_update]
  let F : ℂ → ℂ := fun t => f (Function.update (groupWeights label v) (label i) t)
  change deriv (fun t => F (t + (groupWeights label v (label i) - v i))) (v i) =
    deriv F (groupWeights label v (label i))
  rw [deriv_comp_add_const, add_sub_cancel]


private theorem group_jet (label : X → J) (l : List X) (f : (J → ℂ) → ℂ) :
    coordinateJet l (f ∘ groupWeights label) =
      coordinateJet (l.map label) f ∘ groupWeights label := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
    simp only [coordinateJet, List.map_cons, group_derivative, ih]

private theorem sum_groupWeights (label : X → J) (v : X → ℂ) (a : J → ℂ) :
    (∑ j, a j * groupWeights label v j) = ∑ i, a (label i) * v i := by
  simp only [groupWeights, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [eq_comm]

private theorem grouped_exponent (label : X → J) (A : Matrix J J ℂ) (m : J → ℂ)
    (v : X → ℂ) :
    MvPolynomial.eval (groupWeights label v) (affineExponent A m) =
      (1 / 2 : ℂ) * (∑ i, ∑ j, A (label i) (label j) * v i * v j) +
        ∑ i, m (label i) * v i := by
  rw [eval_affine, sum_groupWeights]
  congr 2
  let g := groupWeights label v
  change (∑ a, ∑ b, A a b * g a * g b) = _
  calc
    _ = ∑ a, g a * (∑ b, A a b * g b) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ a, g a * (∑ j, A a (label j) * v j) := by
      simp_rw [g, sum_groupWeights]
    _ = ∑ j, ∑ a, (A a (label j) * v j) * g a := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ j, ∑ i, (A (label i) (label j) * v j) * v i := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_groupWeights label v (fun a => A a (label j) * v j)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- A distinct external coordinate for each marked oscillator recovers the
literal oscillator occupation with its original product of factorials.
The label map may repeat either colours or modes or both. -/
theorem marked_gaussian_jet (label : X → J) (l : List X) (A : Matrix J J ℂ)
    (m : J → ℂ) (hA : ∀ i j, A i j = A j i) :
    let d := jetOccupation (l.map label)
    coordinateJet l (fun v => Complex.exp (
      (1 / 2 : ℂ) * (∑ i, ∑ j, A (label i) (label j) * v i * v j) + ∑ i, m (label i) * v i)) 0 =
        (weight d : ℂ) * affineCoefficient A m d := by
  dsimp only
  simp_rw [← grouped_exponent label A m]
  change coordinateJet l ((fun v => Complex.exp (MvPolynomial.eval v (affineExponent A m))) ∘
    groupWeights label) 0 = _
  rw [group_jet, Function.comp_apply, groupWeights_zero]
  have h := NativeAffineExternalCoefficient.native_affine_external_jet A m hA (l.map label)
    (jetOccupation (l.map label)).degree le_rfl
  have hw : (weight (jetOccupation (l.map label)) : ℂ) ≠ 0 := by
    exact_mod_cast (FactorialFockMetric.weight_pos _).ne'
  exact ((div_eq_iff hw).mp h).trans (mul_comm _ _)

end Marked

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMPhysicalCovariance
