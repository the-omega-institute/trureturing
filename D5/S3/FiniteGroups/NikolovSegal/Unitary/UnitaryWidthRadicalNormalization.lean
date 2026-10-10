/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRadicalNormalization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWidthRadicalNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthLeviGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace NikolovSegal.UnitaryWholeGroupWidth
open Matrix UnitarySylow PartIIUnitaryUpperTorus PartIIUnitaryLeviDecomposition
universe u
variable {F : Type u} [Field F] {n : ℕ} {ι : RingAut F}

theorem slCentral_transpose (g : SpecialLinearGroup (Fin n) F) :
    (PartIICentralLevi.embed g).transpose=PartIICentralLevi.embed g.transpose := by
  apply SpecialLinearGroup.ext
  intro i j
  obtain ⟨i,rfl⟩ := (centralKernel% indexEquiv).surjective i
  obtain ⟨j,rfl⟩ := (centralKernel% indexEquiv).surjective j
  change PartIICentralLevi.embed g ((centralKernel% indexEquiv) j) ((centralKernel% indexEquiv) i)=_
  rw [centralKernel% entry,centralKernel% entry]
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  all_goals simp [Matrix.fromBlocks,Matrix.one_apply,SpecialLinearGroup.coe_transpose,Matrix.transpose_apply,eq_comm]

theorem centralEmbed_transpose (g : specialUnitary n ι) :
    transpose (centralEmbed g)=centralEmbed (transpose g) :=
  Subtype.ext (slCentral_transpose g.val)

theorem centralEmbed_positive {g : specialUnitary n ι} (hg : Positive g) :
    Positive (centralEmbed g) :=
  PartIIAmbientUnipotentDecomposition.actual_central_embed_unitriangular g.val hg

theorem centralEmbed_negative {g : specialUnitary n ι} (hg : Negative g) :
    Negative (centralEmbed g) := by
  apply (positive_transpose_iff _).mp
  rw [centralEmbed_transpose]
  exact centralEmbed_positive ((positive_transpose_iff _).mpr hg)

/-- The actual opposite radical is normalized by every actual central SU. -/
theorem central_conjugate_downRadical (b : specialUnitary n ι)
    {g : specialUnitary (n+2) ι} (hg : DownRadical g) :
    DownRadical (centralEmbed b*g*(centralEmbed b)⁻¹) := by
  change UpRadical (transpose (centralEmbed b*g*(centralEmbed b)⁻¹))
  rw [transpose_mul,transpose_mul,transpose_inv,centralEmbed_transpose]
  simpa only [map_inv,inv_inv,mul_assoc] using central_conjugate_upRadical (transpose b)⁻¹ hg

@[simp] theorem upRadical_one : UpRadical (1 : specialUnitary (n+2) ι) := by
  apply upRadical_of_endpoints_middle endpoints_one
  ext i j
  simp [Matrix.submatrix_apply,Matrix.one_apply,mid_injective.eq_iff]

@[simp] theorem downRadical_one : DownRadical (1 : specialUnitary (n+2) ι) := by
  change UpRadical (transpose 1)
  have hh : transpose (1 : specialUnitary (n+2) ι)=1 := by
    apply Subtype.ext; apply SpecialLinearGroup.ext; intro i j; simp [transpose_entry,Matrix.one_apply,eq_comm]
  rw [hh]; exact upRadical_one

theorem upRadical_inv {g : specialUnitary (n+2) ι} (hg : UpRadical g) : UpRadical g⁻¹ :=
  PartIIRadicalCoordinates.actual_radical_inverse_mem g.val hg

theorem downRadical_inv {g : specialUnitary (n+2) ι} (hg : DownRadical g) : DownRadical g⁻¹ := by
  change UpRadical (transpose g⁻¹)
  rw [transpose_inv]
  exact upRadical_inv hg

/-- The accepted actual U=Levi*radical decomposition, in the literal SU carrier. -/
theorem positive_levi_radical {g : specialUnitary (n+2) ι} (hg : Positive g) :
    ∃ b : specialUnitary n ι, ∃ v : specialUnitary (n+2) ι,
      Positive b ∧ UpRadical v ∧ centralEmbed b*v=g := by
  obtain ⟨b,v,hb,hbs,hv,hvs,he⟩ := actual_unitary_ambient_U_decomposition ι g.val hg g.prop
  exact ⟨⟨b,hbs⟩,⟨v,hvs⟩,hb,hv,Subtype.ext he⟩

/-- Genuine opposite decomposition, with the Levi moved to the left by proved normalization. -/
theorem negative_levi_radical {g : specialUnitary (n+2) ι} (hg : Negative g) :
    ∃ b : specialUnitary n ι, ∃ v : specialUnitary (n+2) ι,
      Negative b ∧ DownRadical v ∧ centralEmbed b*v=g := by
  obtain ⟨b,v,hb,hv,he⟩ := positive_levi_radical ((positive_transpose_iff _).mpr hg)
  let c := transpose b
  let w := (centralEmbed c)⁻¹*transpose v*centralEmbed c
  have hc : Negative c := (positive_transpose_iff c).mp (by simpa [c] using hb)
  have ht : DownRadical (transpose v) := by
    change UpRadical (transpose (transpose v)); simpa using hv
  have hw : DownRadical w := by
    simpa only [map_inv,inv_inv] using central_conjugate_downRadical c⁻¹ ht
  have hback := congrArg transpose he
  simp only [transpose_mul,centralEmbed_transpose,transpose_transpose] at hback
  refine ⟨c,w,hc,hw,?_⟩
  change centralEmbed c*((centralEmbed c)⁻¹*transpose v*centralEmbed c)=g
  calc
    _ = transpose v*centralEmbed c := by group
    _ = g := hback

end NikolovSegal.UnitaryWholeGroupWidth
