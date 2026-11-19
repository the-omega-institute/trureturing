/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Identity-principle gluing on the three four-point chart domains. -/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic

/-! The native Euler slit and analytic gluing for the original four-point charts.
The holomorphic channel functions and their initial equalities are inputs. -/

open Complex Filter Set
open scoped Topology

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourPointChartGluing

/-- The Euler slit after continuation across the negative real axis, with the
native puncture at zero removed. -/
def Ω : Set ℂ := {r | 1 - r ∈ Complex.slitPlane ∧ r ≠ 0}

def rA (z : ℂ) : ℂ := 1 - z⁻¹
def rB (z : ℂ) : ℂ := z
def rD (z : ℂ) : ℂ := z⁻¹

def U_A : Set ℂ := {z | z ≠ 0 ∧ rA z ∈ Ω}
def U_B : Set ℂ := {z | z ≠ 0 ∧ rB z ∈ Ω}
def U_D : Set ℂ := {z | z ≠ 0 ∧ rD z ∈ Ω}

/-- The real ray `(-∞, 0]` in the complex plane. -/
def nonpositiveRay : Set ℂ := {z | z.im = 0 ∧ z.re ≤ 0}

/-- The real ray `[1, ∞)` in the complex plane. -/
def rightRay : Set ℂ := {z | z.im = 0 ∧ 1 ≤ z.re}

/-- The real segment `[0, 1]` in the complex plane. -/
def unitSegment : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1}

def doubleSlit : Set ℂ := (nonpositiveRay ∪ rightRay)ᶜ
def puncturedPlane : Set ℂ := ({0, 1} : Set ℂ)ᶜ

private theorem real_of_im_zero {z : ℂ} (hz : z.im = 0) : (z.re : ℂ) = z :=
  Complex.ext rfl (by simpa using hz.symm)

private theorem inv_im_ne_zero_iff {z : ℂ} (hz : z ≠ 0) : z⁻¹.im ≠ 0 ↔ z.im ≠ 0 := by
  rw [Complex.inv_im, div_ne_zero_iff]
  simp [(Complex.normSq_pos.mpr hz).ne']

private theorem rA_ne_zero_iff (z : ℂ) : rA z ≠ 0 ↔ z ≠ 1 := by
  rw [rA, sub_ne_zero, ne_comm]
  exact not_congr inv_eq_one

/-- The residue iterate coordinate is the negative of the native Euler parameter. -/
theorem neg_rA_eq_div {z : ℂ} (hz : z ≠ 0) : -rA z = (1 - z) / z := by
  rw [rA, neg_sub, div_eq_mul_inv, sub_mul, one_mul, mul_inv_cancel₀ hz]

private theorem mem_Ω {z : ℂ} : z ∈ Ω ↔ (z.re < 1 ∨ z.im ≠ 0) ∧ z ≠ 0 := by
  simp [Ω, Complex.mem_slitPlane_iff, sub_pos]

theorem Ω_eq : Ω = ({0} ∪ rightRay)ᶜ := by
  ext z
  rw [mem_Ω]
  simp only [mem_compl_iff, mem_union, mem_singleton_iff, rightRay, mem_ofPred_eq,
    not_or, not_and_or, not_le]
  tauto

theorem U_A_eq : U_A = (nonpositiveRay ∪ {1})ᶜ := by
  ext z
  by_cases hz : z = 0
  · subst z
    simp [U_A, nonpositiveRay]
  change z ≠ 0 ∧ (1 - rA z ∈ Complex.slitPlane ∧ rA z ≠ 0) ↔
    ¬ ((z.im = 0 ∧ z.re ≤ 0) ∨ z = 1)
  rw [show 1 - rA z = z⁻¹ by simp [rA], rA_ne_zero_iff, Complex.mem_slitPlane_iff,
    inv_im_ne_zero_iff hz, Complex.inv_re, div_pos_iff_of_pos_right (Complex.normSq_pos.mpr hz)]
  simp only [not_or, not_and_or, not_le]
  tauto

theorem U_B_eq_Ω : U_B = Ω := by
  ext z
  exact ⟨And.right, fun hz ↦ ⟨hz.2, hz⟩⟩

theorem U_B_eq : U_B = ({0} ∪ rightRay)ᶜ :=
  U_B_eq_Ω.trans Ω_eq

theorem U_D_eq : U_D = unitSegmentᶜ := by
  ext z
  change z ≠ 0 ∧ rD z ∈ Ω ↔ ¬ (z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1)
  by_cases hz : z = 0
  · subst z
    simp
  rw [mem_Ω]
  change (z ≠ 0 ∧ ((z⁻¹.re < 1 ∨ z⁻¹.im ≠ 0) ∧ z⁻¹ ≠ 0)) ↔
    ¬ (z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1)
  rw [and_iff_right hz, and_iff_left (inv_ne_zero hz), inv_im_ne_zero_iff hz]
  by_cases him : z.im = 0
  · have hreInv : z⁻¹.re = z.re⁻¹ := by
      conv_lhs => rw [← real_of_im_zero him, ← Complex.ofReal_inv, Complex.ofReal_re]
    have hre : z.re ≠ 0 := fun h ↦ hz (by simpa [h] using (real_of_im_zero him).symm)
    simp only [him, hreInv, ne_eq, not_true_eq_false, or_false, true_and]
    rcases lt_or_gt_of_ne hre with hn | hp
    · simp [hn.not_ge, (inv_lt_zero.mpr hn).trans zero_lt_one]
    · simp [hp.le, inv_lt_one₀ hp, not_le]
  · simp [him]

private theorem mem_doubleSlit {z : ℂ} :
    z ∈ doubleSlit ↔ z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) := by
  by_cases h : z.im = 0 <;> simp [doubleSlit, nonpositiveRay, rightRay, h, not_le]

theorem U_A_union_U_B : U_A ∪ U_B = puncturedPlane := by
  ext z
  rw [U_A_eq, U_B_eq]
  by_cases h0 : z = 0
  · subst z
    norm_num [nonpositiveRay, rightRay, puncturedPlane]
  by_cases h1 : z = 1
  · subst z
    norm_num [nonpositiveRay, rightRay, puncturedPlane]
  simp only [mem_union, mem_compl_iff, mem_singleton_iff, nonpositiveRay, rightRay,
    mem_ofPred_eq, h0, h1, or_false, false_or, puncturedPlane, mem_insert_iff, not_false_eq_true,
    iff_true, not_and_or, not_le]
  have hre := (lt_or_ge z.re 1).imp id (fun h ↦ zero_lt_one.trans_le h)
  tauto

theorem U_A_inter_U_B : U_A ∩ U_B = doubleSlit := by
  have h0 : ({0} : Set ℂ) ⊆ nonpositiveRay := by
    intro z hz
    rcases mem_singleton_iff.mp hz with rfl
    simp [nonpositiveRay]
  have h1 : ({1} : Set ℂ) ⊆ rightRay := by
    intro z hz
    rcases mem_singleton_iff.mp hz with rfl
    simp [rightRay]
  ext z
  rw [U_A_eq, U_B_eq]
  simp only [mem_inter_iff, mem_compl_iff, mem_union, not_or, doubleSlit]
  have hz0 := @h0 z
  have hz1 := @h1 z
  tauto

theorem U_D_subset_puncturedPlane : U_D ⊆ puncturedPlane := by
  intro z hz
  rw [U_D_eq] at hz
  change ¬ (z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1) at hz
  simp only [puncturedPlane, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · rintro rfl
    exact hz (by simp)
  · rintro rfl
    exact hz (by simp)

private theorem isClosed_nonpositiveRay : IsClosed nonpositiveRay :=
  (isClosed_eq continuous_im continuous_const).inter
    (isClosed_le continuous_re continuous_const)

private theorem isClosed_rightRay : IsClosed rightRay :=
  (isClosed_eq continuous_im continuous_const).inter
    (isClosed_le continuous_const continuous_re)

private theorem isClosed_unitSegment : IsClosed unitSegment :=
  (isClosed_eq continuous_im continuous_const).inter
    ((isClosed_le continuous_const continuous_re).inter (isClosed_le continuous_re continuous_const))

theorem isOpen_U_A : IsOpen U_A := by
  rw [U_A_eq]
  exact (isClosed_nonpositiveRay.union isClosed_singleton).isOpen_compl

theorem isOpen_U_B : IsOpen U_B := by
  rw [U_B_eq]
  exact (isClosed_singleton.union isClosed_rightRay).isOpen_compl

theorem isOpen_U_D : IsOpen U_D := by
  rw [U_D_eq]
  exact isClosed_unitSegment.isOpen_compl

theorem isOpen_Ω : IsOpen Ω := U_B_eq_Ω ▸ isOpen_U_B

theorem isOpen_doubleSlit : IsOpen doubleSlit :=
  U_A_inter_U_B ▸ isOpen_U_A.inter isOpen_U_B

theorem isOpen_puncturedPlane : IsOpen puncturedPlane :=
  U_A_union_U_B ▸ isOpen_U_A.union isOpen_U_B

private def upper : Set ℂ := {z | 0 < z.im}
private def lower : Set ℂ := {z | z.im < 0}
private def middle : Set ℂ := {z | 0 < z.re ∧ z.re < 1}
private def left : Set ℂ := {z | z.re < 0}
private def right : Set ℂ := {z | 1 < z.re}

private theorem isPreconnected_left : IsPreconnected left :=
  ((convex_Iio (𝕜 := ℝ) (0 : ℝ)).linear_preimage Complex.reLm).isPreconnected

private theorem isPreconnected_right : IsPreconnected right :=
  ((convex_Ioi (𝕜 := ℝ) (1 : ℝ)).linear_preimage Complex.reLm).isPreconnected

/-- A preconnected set meeting both open imaginary half-planes joins them. -/
private theorem isPreconnected_halfPlane_union {s : Set ℂ} (hs : IsPreconnected s)
    (hu : (s ∩ upper).Nonempty) (hl : (s ∩ lower).Nonempty) :
    IsPreconnected ((s ∪ upper) ∪ lower) := by
  have upperConvex : Convex ℝ upper := (convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm
  have lowerConvex : Convex ℝ lower := (convex_Iio (0 : ℝ)).linear_preimage Complex.imLm
  obtain ⟨z, hzs, hzl⟩ := hl
  exact (hs.union' hu upperConvex.isPreconnected).union z (Or.inl hzs) hzl
    lowerConvex.isPreconnected

theorem real_mem_doubleSlit {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : (x : ℂ) ∈ doubleSlit :=
  mem_doubleSlit.mpr (Or.inr (by simpa only [Complex.ofReal_re] using And.intro h0 h1))

theorem isPreconnected_doubleSlit : IsPreconnected doubleSlit := by
  have heq : doubleSlit = (middle ∪ upper) ∪ lower := by
    ext z
    simp only [mem_doubleSlit, mem_union, upper, lower, middle, mem_ofPred_eq, ← lt_or_lt_iff_ne]
    tauto
  rw [heq]
  have hmiddle : Convex ℝ middle := (convex_Ioo (0 : ℝ) 1).linear_preimage Complex.reLm
  exact isPreconnected_halfPlane_union hmiddle.isPreconnected
    ⟨⟨1 / 2, 1⟩, by norm_num [middle, upper]⟩
    ⟨⟨1 / 2, -1⟩, by norm_num [middle, lower]⟩

theorem isPreconnected_U_A : IsPreconnected U_A := by
  have heq : U_A = doubleSlit ∪ right := by
    ext z
    rw [U_A_eq]
    simp only [mem_union, mem_doubleSlit, mem_compl_iff, nonpositiveRay, mem_ofPred_eq,
      mem_singleton_iff, right]
    by_cases him : z.im = 0
    · have hz1 : z = 1 ↔ z.re = 1 :=
        ⟨fun h ↦ by simp [h], fun h ↦ Complex.ext (by simpa using h) (by simpa using him)⟩
      simp only [him, true_and, ne_eq, not_true_eq_false, false_or, not_or, not_le, hz1]
      constructor <;> intro h
      · rcases lt_or_gt_of_ne h.2 with hl | hr
        · exact Or.inl ⟨h.1, hl⟩
        · exact Or.inr hr
      · rcases h with ⟨h0, h1⟩ | hr
        · exact ⟨h0, h1.ne⟩
        · exact ⟨zero_lt_one.trans hr, hr.ne'⟩
    · have hz1 : z ≠ 1 := fun h ↦ him (by simp [h])
      simp [him, hz1]
  rw [heq]
  exact isPreconnected_doubleSlit.union' ⟨⟨2, 1⟩, by norm_num [mem_doubleSlit, right]⟩
    isPreconnected_right

theorem isPreconnected_U_B : IsPreconnected U_B := by
  have heq : U_B = doubleSlit ∪ left := by
    ext z
    rw [U_B_eq]
    simp only [mem_union, mem_doubleSlit, mem_compl_iff, rightRay, mem_ofPred_eq,
      mem_singleton_iff, left]
    by_cases him : z.im = 0
    · have hz0 : z = 0 ↔ z.re = 0 :=
        ⟨fun h ↦ by simp [h], fun h ↦ Complex.ext (by simpa using h) (by simpa using him)⟩
      simp only [him, true_and, ne_eq, not_true_eq_false, false_or, not_or, not_le, hz0]
      constructor <;> intro h
      · rcases lt_or_gt_of_ne h.1 with hl | hr
        · exact Or.inr hl
        · exact Or.inl ⟨hr, h.2⟩
      · rcases h with ⟨h0, h1⟩ | hl
        · exact ⟨h0.ne', h1⟩
        · exact ⟨hl.ne, hl.trans zero_lt_one⟩
    · have hz0 : z ≠ 0 := fun h ↦ him (by simp [h])
      simp [him, hz0]
  rw [heq]
  exact isPreconnected_doubleSlit.union' ⟨⟨-1, 1⟩, by norm_num [mem_doubleSlit, left]⟩
    isPreconnected_left

theorem isPreconnected_Ω : IsPreconnected Ω := U_B_eq_Ω ▸ isPreconnected_U_B

theorem isPreconnected_puncturedPlane : IsPreconnected puncturedPlane := by
  rw [← U_A_union_U_B]
  apply isPreconnected_U_A.union' _ isPreconnected_U_B
  rw [U_A_inter_U_B]
  exact ⟨_, real_mem_doubleSlit (x := 1 / 2) (by norm_num) (by norm_num)⟩

theorem isPreconnected_U_D : IsPreconnected U_D := by
  have heq : U_D = ((left ∪ upper) ∪ lower) ∪ right := by
    ext z
    rw [U_D_eq]
    simp only [mem_compl_iff, unitSegment, mem_union, left, upper, lower, right, mem_ofPred_eq,
      not_and_or, not_le, ← lt_or_lt_iff_ne]
    tauto
  rw [heq]
  have h := isPreconnected_halfPlane_union isPreconnected_left
    ⟨⟨-1, 1⟩, by norm_num [left, upper]⟩ ⟨⟨-1, -1⟩, by norm_num [left, lower]⟩
  exact h.union' ⟨⟨2, 1⟩, by norm_num [left, upper, lower, right]⟩ isPreconnected_right

theorem mem_U_D_of_one_lt_norm {z : ℂ} (hz : 1 < ‖z‖) : z ∈ U_D := by
  rw [U_D_eq]
  intro h
  obtain ⟨him, h0, h1⟩ := h
  rw [← real_of_im_zero him, Complex.norm_real, Real.norm_of_nonneg h0] at hz
  exact (not_lt_of_ge h1) hz

theorem inv_mem_U_D_iff {u : ℂ} : u⁻¹ ∈ U_D ↔ u ∈ Ω := by
  change u⁻¹ ≠ 0 ∧ (u⁻¹)⁻¹ ∈ Ω ↔ u ∈ Ω
  rw [inv_inv]
  exact ⟨And.right, fun hu ↦ ⟨inv_ne_zero hu.2, hu⟩⟩

theorem eventually_mem_U_A : ∀ᶠ z in 𝓝[≠] (1 : ℂ), z ∈ U_A := by
  have h : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), 0 < z.re :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
  filter_upwards [h.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz h1
  rw [U_A_eq]
  exact fun h ↦ h.elim (fun h ↦ (not_le_of_gt hz) h.2) h1

theorem eventually_mem_U_B : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ U_B := by
  have h : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), z.re < 1 :=
    (isOpen_lt continuous_re continuous_const).mem_nhds (by simp)
  filter_upwards [h.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz h0
  rw [U_B_eq_Ω]
  exact mem_Ω.mpr ⟨Or.inl hz, h0⟩

theorem eventually_inv_mem_U_D : ∀ᶠ u in 𝓝[≠] (0 : ℂ), u⁻¹ ∈ U_D :=
  eventually_mem_U_B.mono fun _ hu ↦ inv_mem_U_D_iff.mpr (U_B_eq_Ω ▸ hu)

theorem tendsto_rA : Tendsto rA (𝓝[≠] (1 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  have hc : ContinuousAt (fun _ : ℂ ↦ (1 : ℂ)) 1 := continuousAt_const
  have h : ContinuousAt rA 1 :=
    hc.sub (continuousAt_id.inv₀ one_ne_zero)
  refine ⟨?_, ?_⟩
  · have ht : Tendsto rA (𝓝[≠] (1 : ℂ)) (𝓝 (rA 1)) := h.mono_left nhdsWithin_le_nhds
    simpa [rA] using ht
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact (rA_ne_zero_iff z).mpr hz

/-- The identity principle extends the overlap equality, after which the two
charts define a single holomorphic function on the twice-punctured plane. -/
theorem exists_gluing {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A U_A)
    (hB : DifferentiableOn ℂ B U_B) {x : ℂ} (hx : x ∈ doubleSlit)
    (hAB : ∃ᶠ z in 𝓝[≠] x, A z = B z) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F puncturedPlane ∧ EqOn F A U_A ∧ EqOn F B U_B := by
  classical
  have hAn := hA.analyticOnNhd isOpen_U_A
  have hBn := hB.analyticOnNhd isOpen_U_B
  rw [← U_A_inter_U_B] at hx
  have hOverlap : EqOn A B (U_A ∩ U_B) :=
    (hAn.mono inter_subset_left).eqOn_of_preconnected_of_frequently_eq
      (hBn.mono inter_subset_right) (U_A_inter_U_B ▸ isPreconnected_doubleSlit) hx hAB
  let F := U_A.piecewise A B
  have hFA : EqOn F A U_A := fun _ hz ↦ piecewise_eq_of_mem _ _ _ hz
  have hFB : EqOn F B U_B := by
    intro z hz
    by_cases ha : z ∈ U_A
    · exact (hFA ha).trans (hOverlap ⟨ha, hz⟩)
    · exact piecewise_eq_of_notMem _ _ _ ha
  refine ⟨F, ?_, hFA, hFB⟩
  rw [← U_A_union_U_B]
  rintro z (ha | hb)
  · exact (hAn z ha).congr ((isOpen_U_A.eventually_mem ha).mono fun _ h ↦ (hFA h).symm)
  · exact (hBn z hb).congr ((isOpen_U_B.eventually_mem hb).mono fun _ h ↦ (hFB h).symm)

/-- One interior accumulation of equality identifies the D chart on its whole
domain, including the exterior of the closed unit disk. -/
theorem eqOn_D_of_frequently_eq {F D : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F puncturedPlane) (hD : DifferentiableOn ℂ D U_D)
    {y : ℂ} (hy : y ∈ U_D) (hFD : ∃ᶠ z in 𝓝[≠] y, F z = D z) : EqOn F D U_D :=
  (hF.mono U_D_subset_puncturedPlane).eqOn_of_preconnected_of_frequently_eq
    (hD.analyticOnNhd isOpen_U_D) isPreconnected_U_D hy hFD

/-- The D comparison can be supplied against either of the two chart values
already used to define the glued function. -/
theorem eqOn_D_of_chart_overlap {F C D : ℂ → ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F puncturedPlane) (hD : DifferentiableOn ℂ D U_D)
    (hU : IsOpen U) (hFC : EqOn F C U) {y : ℂ} (hy : y ∈ U ∩ U_D)
    (hCD : ∃ᶠ z in 𝓝[≠] y, C z = D z) : EqOn F D U_D :=
  eqOn_D_of_frequently_eq hF hD hy.2 <|
    (hCD.and_eventually ((hU.eventually_mem hy.1).filter_mono nhdsWithin_le_nhds)).mono
      fun _ h ↦ (hFC h.2).trans h.1

theorem germs_of_eqOn {F A B D : ℂ → ℂ}
    (hFA : EqOn F A U_A) (hFB : EqOn F B U_B) (hFD : EqOn F D U_D) :
    (F =ᶠ[𝓝[≠] 1] A) ∧ (F =ᶠ[𝓝[≠] 0] B) ∧
      ((fun u ↦ F u⁻¹) =ᶠ[𝓝[≠] 0] fun u ↦ D u⁻¹) :=
  ⟨eventually_mem_U_A.mono fun _ hz ↦ hFA hz, eventually_mem_U_B.mono fun _ hz ↦ hFB hz,
    eventually_inv_mem_U_D.mono fun _ hu ↦ hFD hu⟩

/-- For one output sector, `A`, `B`, and `D` are the native scalar
combinations before the B prefactor. Their germs at native zero supply the
residue formulas. The A residue coordinate is the reflected native parameter. -/
theorem exists_common_four_point_germ {A B D rawA rawB rawD : ℂ → ℂ} (k : ℤ)
    (hA : DifferentiableOn ℂ A Ω) (hB : DifferentiableOn ℂ B Ω)
    (hD : DifferentiableOn ℂ D Ω) {x y : ℂ} (hx : x ∈ doubleSlit)
    (hAB : ∃ᶠ z in 𝓝[≠] x, A (rA z) = (2 : ℂ) ^ 12 * z ^ k * B (rB z))
    (hDOverlap :
      (y ∈ U_A ∩ U_D ∧ ∃ᶠ z in 𝓝[≠] y, A (rA z) = D (rD z)) ∨
      (y ∈ U_B ∩ U_D ∧ ∃ᶠ z in 𝓝[≠] y, (2 : ℂ) ^ 12 * z ^ k * B (rB z) = D (rD z)))
    (hAgerm : A =ᶠ[𝓝[≠] 0] fun t ↦ rawA (-t))
    (hBgerm : B =ᶠ[𝓝[≠] 0] rawB) (hDgerm : D =ᶠ[𝓝[≠] 0] rawD) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F ({0, 1}ᶜ : Set ℂ) ∧
      (F =ᶠ[𝓝[≠] 1] fun z ↦ rawA ((1 - z) / z)) ∧
      (F =ᶠ[𝓝[≠] 0] fun z ↦ (2 : ℂ) ^ 12 * z ^ k * rawB z) ∧
      ((fun u ↦ F u⁻¹) =ᶠ[𝓝[≠] 0] rawD) := by
  have hAz : DifferentiableOn ℂ (fun z ↦ A (rA z)) U_A :=
    hA.comp (fun z hz ↦
      ((differentiableAt_const (c := (1 : ℂ))).sub
        (differentiableAt_id.inv hz.1)).differentiableWithinAt) (fun _ hz ↦ hz.2)
  have hBz : DifferentiableOn ℂ (fun z ↦ (2 : ℂ) ^ 12 * z ^ k * B (rB z)) U_B := by
    rw [U_B_eq_Ω]
    refine fun z hz ↦ ((differentiableAt_const (c := (2 : ℂ) ^ 12)).mul
      (differentiableAt_id.zpow (Or.inl hz.2))).differentiableWithinAt.mul (hB z hz)
  have hDz : DifferentiableOn ℂ (fun z ↦ D (rD z)) U_D :=
    hD.comp (fun _ hz ↦ (differentiableAt_id.inv hz.1).differentiableWithinAt) (fun _ hz ↦ hz.2)
  obtain ⟨F, hF, hFA, hFB⟩ := exists_gluing hAz hBz hx hAB
  have hFD : EqOn F (fun z ↦ D (rD z)) U_D := by
    rcases hDOverlap with ⟨hy, heq⟩ | ⟨hy, heq⟩
    · exact eqOn_D_of_chart_overlap hF hDz isOpen_U_A hFA hy heq
    · exact eqOn_D_of_chart_overlap hF hDz isOpen_U_B hFB hy heq
  obtain ⟨gA, gB, gD⟩ := germs_of_eqOn hFA hFB hFD
  refine ⟨F, hF.differentiableOn, ?_, ?_, ?_⟩
  · filter_upwards [gA.trans (hAgerm.comp_tendsto tendsto_rA),
      eventually_ne_nhdsWithin (show (1 : ℂ) ≠ 0 by norm_num)] with z hz h0
    simpa only [Function.comp_apply, neg_rA_eq_div h0] using hz
  · exact gB.trans (hBgerm.mono fun z hz ↦ congrArg (fun w ↦ (2 : ℂ) ^ 12 * z ^ k * w) hz)
  · exact (by simpa only [rD, inv_inv] using gD : (fun u ↦ F u⁻¹) =ᶠ[𝓝[≠] 0] D).trans hDgerm

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourPointChartGluing
