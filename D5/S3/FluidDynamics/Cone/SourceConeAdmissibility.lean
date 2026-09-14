/- GID: D5/S3/FluidDynamics/Cone/SourceConeAdmissibility
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Cone/SourceConeAdmissibility
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   utility: none
   digest: Source criterion on a compact family gives eventual cone positive definiteness. -/

import D5.S3.FluidDynamics.Cone.UniformConeStability
import Mathlib.Topology.Order.Compact

noncomputable section
open Set
namespace D5.S3.FluidDynamics.Cone

variable {X : Type*} [TopologicalSpace X]

/-! Port of `positive_uniform_margin`, `compact_source_margins`,
`compact_normalized_cone`, `compact_normalized_cone_gap`, and
`compact_equation_eleven_gap` from `openai/NavierStokesAndEuler`, commit
8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538, file `NavierStokes/UniformCone.lean`,
licensed under Apache-2.0. This is a port rather than an import because upstream
pins Lean v4.34.0-rc2 while this repository pins v4.33.0. -/

theorem normalized_test_negative {a b w : ℝ} (ha : 0 < a)
    (hsecond : 2 * b * w + b ^ 2 / a + (a - 2) * w ^ 2 < 2) :
    (a * (1 + (b / a) ^ 2) - 2) * (w + b / a) ^ 2 < 2 * (1 - b * w / a) ^ 2 := by
  field_simp at hsecond ⊢
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  nlinarith [sq_nonneg (a*w+b), sq_nonneg (a-b*w)]

theorem finite_amplitude_cone {c j v p : ℝ} (hp : 0 < p) (hP : 2 < p * c)
    (hv : v < p * c) (hbound : 4 * c * v < p * (2 * c ^ 2 - (v - 2) * j ^ 2)) :
    v < coneBound (p * c) (p * j) := by
  by_cases hle : v ≤ 2
  · exact relaxed_cone_of_le_two hP hle
  · have htwo : 2 < v := lt_of_not_ge hle
    have hquad : (v - 2) * (p * j) ^ 2 < 2 * (p * c - v) ^ 2 := by
      nlinarith [hbound, sq_nonneg (p*c-v)]
    exact ((true_cone_iff htwo).mpr ⟨hv, hquad⟩).2

private theorem continuousOn_max {K : Set X} {f g : X → ℝ}
    (hf : ContinuousOn f K) (hg : ContinuousOn g K) :
    ContinuousOn (fun x => max (f x) (g x)) K :=
  continuous_max.comp_continuousOn (hf.prodMk hg)

/-- The positive minimum of a continuous positive function on a compact set.
This also covers the empty parameter set. -/
theorem positive_uniform_margin {K : Set X} (hK : IsCompact K)
    {g : X → ℝ} (hg : ContinuousOn g K) (hpos : ∀ x ∈ K, 0 < g x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ε ≤ g x :=
  hK.exists_forall_le' hg hpos

/-- All three strict source inequalities in (11) have a common positive
margin on a continuous compact parameter family. -/
theorem compact_source_margins {K : Set X} (hK : IsCompact K)
    {a b w : X → ℝ} (ha : ContinuousOn a K) (hb : ContinuousOn b K)
    (hw : ContinuousOn w K) (hapos : ∀ x ∈ K, 0 < a x)
    (hfirst : ∀ x ∈ K, 0 < a x - b x * w x)
    (hsecond : ∀ x ∈ K,
      2 * b x * w x + b x ^ 2 / a x + (a x - 2) * w x ^ 2 < 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K,
      ε ≤ a x ∧ ε ≤ a x - b x * w x ∧
        ε ≤ 2 - (2 * b x * w x + b x ^ 2 / a x + (a x - 2) * w x ^ 2) := by
  have hane : ∀ x ∈ K, a x ≠ 0 := fun x hx => ne_of_gt (hapos x hx)
  have hsecond_cont : ContinuousOn
      (fun x => 2 - (2 * b x * w x + b x ^ 2 / a x + (a x - 2) * w x ^ 2)) K :=
    continuousOn_const.sub
      ((((continuousOn_const.mul hb).mul hw).add ((hb.pow 2).div ha hane)).add
        ((ha.sub continuousOn_const).mul (hw.pow 2)))
  obtain ⟨εa, hεa, hbounda⟩ := positive_uniform_margin hK ha hapos
  obtain ⟨εf, hεf, hboundf⟩ :=
    positive_uniform_margin hK (ha.sub (hb.mul hw)) hfirst
  obtain ⟨εs, hεs, hbounds⟩ :=
    positive_uniform_margin hK hsecond_cont (fun x hx => sub_pos.mpr (hsecond x hx))
  refine ⟨min εa (min εf εs), lt_min hεa (lt_min hεf hεs), fun x hx => ?_⟩
  exact ⟨(min_le_left _ _).trans (hbounda x hx),
    ((min_le_right _ _).trans (min_le_left _ _)).trans (hboundf x hx),
    ((min_le_right _ _).trans (min_le_right _ _)).trans (hbounds x hx)⟩

/-- Compact normalized data give one amplitude threshold for the entire family. -/
theorem compact_normalized_cone {K : Set X} (hK : IsCompact K)
    {c j v : X → ℝ} (hc : ContinuousOn c K) (hj : ContinuousOn j K)
    (hv : ContinuousOn v K) (hcpos : ∀ x ∈ K, 0 < c x)
    (hmargin : ∀ x ∈ K, (v x - 2) * j x ^ 2 < 2 * c x ^ 2) :
    ∃ ε p₀ : ℝ, 0 < ε ∧ 0 ≤ p₀ ∧
      (∀ x ∈ K, ε ≤ c x ∧ ε ≤ 2 * c x ^ 2 - (v x - 2) * j x ^ 2) ∧
      ∀ p : ℝ, p₀ < p → ∀ x ∈ K,
        2 < p * c x ∧ v x < coneBound (p * c x) (p * j x) := by
  let d : X → ℝ := fun x => 2 * c x ^ 2 - (v x - 2) * j x ^ 2
  have hd : ContinuousOn d K :=
    (continuousOn_const.mul (hc.pow 2)).sub ((hv.sub continuousOn_const).mul (hj.pow 2))
  have hdpos : ∀ x ∈ K, 0 < d x := fun x hx => sub_pos.mpr (hmargin x hx)
  obtain ⟨εc, hεc, hεcbound⟩ := positive_uniform_margin hK hc hcpos
  obtain ⟨εd, hεd, hεdbound⟩ := positive_uniform_margin hK hd hdpos
  let threshold : X → ℝ := fun x =>
    max 0 (max (2 / c x) (max (v x / c x) (4 * c x * v x / d x)))
  have ht : ContinuousOn threshold K := by
    apply continuousOn_max continuousOn_const
    apply continuousOn_max
    · exact continuousOn_const.div hc (fun x hx => ne_of_gt (hcpos x hx))
    · apply continuousOn_max
      · exact hv.div hc (fun x hx => ne_of_gt (hcpos x hx))
      · exact ((continuousOn_const.mul hc).mul hv).div hd
          (fun x hx => ne_of_gt (hdpos x hx))
  obtain ⟨B, hB⟩ := (hK.image_of_continuousOn ht).bddAbove
  refine ⟨min εc εd, max 0 B, lt_min hεc hεd, le_max_left _ _, ?_, ?_⟩
  · intro x hx
    exact ⟨(min_le_left _ _).trans (hεcbound x hx),
      (min_le_right _ _).trans (hεdbound x hx)⟩
  · intro p hp x hx
    have htx : threshold x < p :=
      lt_of_le_of_lt ((hB (mem_image_of_mem threshold hx)).trans (le_max_right _ _)) hp
    have h₀ : 0 ≤ threshold x := le_max_left _ _
    have h₂ : 2 / c x ≤ threshold x :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hᵥ : v x / c x ≤ threshold x :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    have hdscale : 4 * c x * v x / d x ≤ threshold x :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    have hP : 2 < p * c x := (div_lt_iff₀ (hcpos x hx)).mp (lt_of_le_of_lt h₂ htx)
    refine ⟨hP, finite_amplitude_cone (lt_of_le_of_lt h₀ htx) hP ?_ ?_⟩
    · exact (div_lt_iff₀ (hcpos x hx)).mp (lt_of_le_of_lt hᵥ htx)
    · exact (div_lt_iff₀ (hdpos x hx)).mp (lt_of_le_of_lt hdscale htx)

/-- The eventual relaxed-cone inequalities have uniform positive additive
gaps, independent both of the parameter and of the large amplitude. -/
theorem compact_normalized_cone_gap {K : Set X} (hK : IsCompact K)
    {c j v : X → ℝ} (hc : ContinuousOn c K) (hj : ContinuousOn j K)
    (hv : ContinuousOn v K) (hcpos : ∀ x ∈ K, 0 < c x)
    (hmargin : ∀ x ∈ K, (v x - 2) * j x ^ 2 < 2 * c x ^ 2) :
    ∃ η p₀ : ℝ, 0 < η ∧ 0 ≤ p₀ ∧ ∀ p : ℝ, p₀ < p → ∀ x ∈ K,
      2 + η < p * c x ∧ v x + η < coneBound (p * c x) (p * j x) := by
  obtain ⟨ε, _, hε, _, hbounds, _⟩ := compact_normalized_cone hK hc hj hv hcpos hmargin
  obtain ⟨B, hB⟩ := (hK.image_of_continuousOn (hj.pow 2)).bddAbove
  let M : ℝ := max 0 B + 1
  have hM : 0 < M := by dsimp [M]; linarith [le_max_left (0 : ℝ) B]
  let η : ℝ := ε / (2 * M)
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hM)
  have hηM : η * M = ε / 2 := by
    dsimp [η]
    field_simp [ne_of_gt hM]
  have hshift : ∀ x ∈ K, (v x + η - 2) * j x ^ 2 < 2 * c x ^ 2 := by
    intro x hx
    have hjM : j x ^ 2 ≤ M := by
      calc
        j x ^ 2 ≤ B := hB (mem_image_of_mem (fun y => j y ^ 2) hx)
        _ ≤ max 0 B := le_max_right _ _
        _ ≤ M := by dsimp [M]; linarith
    have hηj : η * j x ^ 2 ≤ ε / 2 :=
      (mul_le_mul_of_nonneg_left hjM hη.le).trans_eq hηM
    have hd := (hbounds x hx).2
    nlinarith
  obtain ⟨_, p₁, _, hp₁, _, hlarge⟩ := compact_normalized_cone hK hc hj
    (hv.add continuousOn_const) hcpos hshift
  refine ⟨η, max p₁ ((2 + η) / ε), hη,
    hp₁.trans (le_max_left _ _), fun p hp x hx => ?_⟩
  have hpold : p₁ < p := lt_of_le_of_lt (le_max_left _ _) hp
  have hpzero : 0 < p := lt_of_le_of_lt hp₁ hpold
  have hpε : 2 + η < p * ε :=
    (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_right _ _) hp)
  refine ⟨lt_of_lt_of_le hpε (mul_le_mul_of_nonneg_left (hbounds x hx).1 hpzero.le), ?_⟩
  exact (hlarge p hpold x hx).2

/-- The manuscript's strict source criterion (11), uniformly on any compact
parameter family. The conclusion supplies uniform normalized margins and a
single threshold for all stress amplitudes above it. -/
theorem compact_equation_eleven {K : Set X} (hK : IsCompact K)
    {a b w : X → ℝ} (ha : ContinuousOn a K) (hb : ContinuousOn b K)
    (hw : ContinuousOn w K) (hapos : ∀ x ∈ K, 0 < a x)
    (hfirst : ∀ x ∈ K, 0 < a x - b x * w x)
    (hsecond : ∀ x ∈ K,
      2 * b x * w x + b x ^ 2 / a x + (a x - 2) * w x ^ 2 < 2) :
    ∃ ε p₀ : ℝ, 0 < ε ∧ 0 ≤ p₀ ∧
      (∀ x ∈ K, ε ≤ 1 - b x * w x / a x ∧
        ε ≤ 2 * (1 - b x * w x / a x) ^ 2 -
          (a x * (1 + (b x / a x) ^ 2) - 2) * (w x + b x / a x) ^ 2) ∧
      ∀ p : ℝ, p₀ < p → ∀ x ∈ K,
        2 < p * (1 - b x * w x / a x) ∧
        a x * (1 + (b x / a x) ^ 2) <
          coneBound (p * (1 - b x * w x / a x)) (p * (w x + b x / a x)) := by
  have hane : ∀ x ∈ K, a x ≠ 0 := fun x hx => ne_of_gt (hapos x hx)
  apply compact_normalized_cone hK
  · exact continuousOn_const.sub ((hb.mul hw).div ha hane)
  · exact hw.add (hb.div ha hane)
  · exact ha.mul (continuousOn_const.add ((hb.div ha hane).pow 2))
  · intro x hx
    apply sub_pos.mpr
    exact (div_lt_one (hapos x hx)).mpr (by linarith [hfirst x hx])
  · intro x hx
    have h := normalized_test_negative (hapos x hx) (hsecond x hx)
    linarith

/-- Equation (11), with a common positive additive gap in both relaxed-cone
inequalities for every parameter and every sufficiently large amplitude. -/
theorem compact_equation_eleven_gap {K : Set X} (hK : IsCompact K)
    {a b w : X → ℝ} (ha : ContinuousOn a K) (hb : ContinuousOn b K)
    (hw : ContinuousOn w K) (hapos : ∀ x ∈ K, 0 < a x)
    (hfirst : ∀ x ∈ K, 0 < a x - b x * w x)
    (hsecond : ∀ x ∈ K,
      2 * b x * w x + b x ^ 2 / a x + (a x - 2) * w x ^ 2 < 2) :
    ∃ η p₀ : ℝ, 0 < η ∧ 0 ≤ p₀ ∧ ∀ p : ℝ, p₀ < p → ∀ x ∈ K,
      2 + η < p * (1 - b x * w x / a x) ∧
        a x * (1 + (b x / a x) ^ 2) + η <
          coneBound (p * (1 - b x * w x / a x)) (p * (w x + b x / a x)) := by
  have hane : ∀ x ∈ K, a x ≠ 0 := fun x hx => ne_of_gt (hapos x hx)
  apply compact_normalized_cone_gap hK
  · exact continuousOn_const.sub ((hb.mul hw).div ha hane)
  · exact hw.add (hb.div ha hane)
  · exact ha.mul (continuousOn_const.add ((hb.div ha hane).pow 2))
  · intro x hx
    apply sub_pos.mpr
    exact (div_lt_one (hapos x hx)).mpr (by linarith [hfirst x hx])
  · intro x hx
    have h := normalized_test_negative (hapos x hx) (hsecond x hx)
    linarith



 theorem compact_source_coneMatrix_posDef {K : Set X} (hK : IsCompact K)
    {a b w : X → ℝ} (ha : ContinuousOn a K) (hb : ContinuousOn b K)
    (hw : ContinuousOn w K) (hapos : ∀ x ∈ K, 0 < a x)
    (hfirst : ∀ x ∈ K, 0 < a x - b x * w x)
    (hsecond : ∀ x ∈ K,
      2 * b x * w x + b x ^ 2 / a x + (a x - 2) * w x ^ 2 < 2)
    (hv : ∀ x ∈ K, 2 < a x * (1 + (b x / a x) ^ 2)) :
    ∃ p₀ : ℝ, 0 ≤ p₀ ∧ ∀ p : ℝ, p₀ < p → ∀ x ∈ K,
      (coneMatrix (p * (1 - b x * w x / a x))
        (p * (w x + b x / a x))
        (a x * (1 + (b x / a x) ^ 2))).PosDef := by
  obtain ⟨η, p₀, hη, hp₀, hgap⟩ := compact_equation_eleven_gap hK ha hb hw hapos hfirst hsecond
  refine ⟨p₀, hp₀, fun p hp x hx => ?_⟩
  apply (cone_condition_iff_posDef (hv x hx)).mp
  exact ⟨by linarith [hgap p hp x hx |>.1], by linarith [hgap p hp x hx |>.2]⟩

#print axioms compact_source_coneMatrix_posDef
#print axioms positive_uniform_margin
#print axioms compact_source_margins
#print axioms compact_normalized_cone
#print axioms compact_normalized_cone_gap
#print axioms compact_equation_eleven_gap
end D5.S3.FluidDynamics.Cone
