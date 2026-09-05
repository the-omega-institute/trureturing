/- GID: D5/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionTransport
   generality: I
   mirror-B: D5/B/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Axis classes, orbits, stabilizers, and five-cycle subgroups are transported to projective space. -/

import D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecompositionEquivariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition

/-- The source quadratic form `q(v) = vᵀHv`, evaluated on the normalized
coordinate supplied by the proved projective equivalence. -/
noncomputable def quadraticForm (p : ProjectiveAxis) : F5 :=
  chartQuadraticForm (projectiveChart p)

/-- The six isotropic, fivefold axes in the actual projective plane. -/
noncomputable def fivefoldAxes : Finset ProjectiveAxis :=
  chartFivefoldAxes.map projectiveChart.symm.toEmbedding

/-- The ten nonsquare, threefold axes in the actual projective plane. -/
noncomputable def threefoldAxes : Finset ProjectiveAxis :=
  chartThreefoldAxes.map projectiveChart.symm.toEmbedding

/-- The fifteen nonzero-square, twofold axes in the actual projective plane. -/
noncomputable def twofoldAxes : Finset ProjectiveAxis :=
  chartTwofoldAxes.map projectiveChart.symm.toEmbedding

theorem mem_mappedAxes (p : ProjectiveAxis) (s : Finset AxisChart) :
    p ∈ s.map projectiveChart.symm.toEmbedding ↔ projectiveChart p ∈ s := by
  constructor
  · rw [Finset.mem_map]
    rintro ⟨q, hq, hqp⟩
    subst p
    rw [projectiveChart_symm_embedding_apply]
    exact hq
  · intro hp
    rw [Finset.mem_map]
    exact ⟨projectiveChart p, hp, projectiveChart.symm_apply_apply p⟩

theorem mem_fivefoldAxes_iff (p : ProjectiveAxis) :
    p ∈ fivefoldAxes ↔ quadraticForm p = 0 := by
  rw [fivefoldAxes, mem_mappedAxes]
  simp [chartFivefoldAxes, quadraticForm]

theorem mem_threefoldAxes_iff (p : ProjectiveAxis) :
    p ∈ threefoldAxes ↔ quadraticForm p = 2 ∨ quadraticForm p = 3 := by
  rw [threefoldAxes, mem_mappedAxes]
  simp [chartThreefoldAxes, quadraticForm]

theorem mem_twofoldAxes_iff (p : ProjectiveAxis) :
    p ∈ twofoldAxes ↔ quadraticForm p = 1 ∨ quadraticForm p = 4 := by
  rw [twofoldAxes, mem_mappedAxes]
  simp [chartTwofoldAxes, quadraticForm]

/-- The subtype of actual projective axes in the concrete isotropic class `𝒜₅`. -/
noncomputable abbrev FivefoldAxis := fivefoldAxes

/-- The finite orbit in the actual projective plane under the induced action. -/
noncomputable def axisOrbit (p : ProjectiveAxis) : Finset ProjectiveAxis :=
  Finset.univ.image fun g : IcosahedralGroup => g • p

theorem axisOrbit_eq_map (p : ProjectiveAxis) :
    axisOrbit p = (chartAxisOrbit (projectiveChart p)).map
      projectiveChart.symm.toEmbedding := by
  classical
  ext q
  constructor
  · simp only [axisOrbit, Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨g, rfl⟩
    rw [Finset.mem_map]
    refine ⟨g • projectiveChart p, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩
    · apply projectiveChart.injective
      rw [projectiveChart_smul, projectiveChart_symm_embedding_apply]
  · rw [Finset.mem_map]
    rintro ⟨r, hr, rfl⟩
    rw [chartAxisOrbit, Finset.mem_image] at hr
    obtain ⟨g, _, rfl⟩ := hr
    rw [axisOrbit, Finset.mem_image]
    refine ⟨g, Finset.mem_univ g, ?_⟩
    apply projectiveChart.injective
    rw [projectiveChart_smul, projectiveChart_symm_embedding_apply]

theorem stabilizer_eq_chart (p : ProjectiveAxis) :
    MulAction.stabilizer IcosahedralGroup p =
      MulAction.stabilizer IcosahedralGroup (projectiveChart p) := by
  ext g
  change g • p = p ↔ g • projectiveChart p = projectiveChart p
  rw [← projectiveChart_smul]
  exact projectiveChart.injective.eq_iff.symm

private noncomputable def stabilizerEquivChart (p : ProjectiveAxis) :
    MulAction.stabilizer IcosahedralGroup p ≃
      MulAction.stabilizer IcosahedralGroup (projectiveChart p) :=
  { toFun := fun g => ⟨g.1, by
      change g.1 • projectiveChart p = projectiveChart p
      rw [← projectiveChart_smul]
      exact congrArg projectiveChart g.2⟩
    invFun := fun g => ⟨g.1, by
      apply projectiveChart.injective
      rw [projectiveChart_smul]
      exact g.2⟩
    left_inv := by intro g; rfl
    right_inv := by intro g; rfl }

theorem stabilizer_card_eq_chart (p : ProjectiveAxis) :
    Fintype.card (MulAction.stabilizer IcosahedralGroup p) =
      Fintype.card (MulAction.stabilizer IcosahedralGroup (projectiveChart p)) :=
  Fintype.card_congr (stabilizerEquivChart p)

noncomputable def toChartFivefoldAxis (p : FivefoldAxis) : ChartFivefoldAxis :=
  ⟨projectiveChart p.1, by
    exact (mem_mappedAxes p.1 chartFivefoldAxes).mp p.2⟩

/-- The five-cycle subgroup, transported along the proved equivariant chart. -/
noncomputable def fiveCycleSubgroup (p : FivefoldAxis) : Subgroup IcosahedralGroup :=
  chartFiveCycleSubgroup (toChartFivefoldAxis p)

noncomputable instance (p : FivefoldAxis) :
    DecidablePred (· ∈ fiveCycleSubgroup p) := Classical.decPred _

theorem mem_fiveCycleSubgroup_iff (p : FivefoldAxis) (g : IcosahedralGroup) :
    g ∈ fiveCycleSubgroup p ↔ g • p.1 = p.1 ∧ g ^ 5 = 1 := by
  change (g • projectiveChart p.1 = projectiveChart p.1 ∧ g ^ 5 = 1) ↔ _
  rw [← projectiveChart_smul]
  constructor <;> rintro ⟨h, h5⟩
  · exact ⟨projectiveChart.injective h, h5⟩
  · exact ⟨congrArg projectiveChart h, h5⟩

end D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition
