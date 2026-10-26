/- GID: D5/S3/FiniteGroups/HeadleyDoubledCoordinates
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyDoubledCoordinates
   mirror-E: none(waiver:two-coordinate-kernel)
   anchors: []
   utility: none
   digest: The literal two-coordinate kernel, its decremented coordinates and E4 quotient. -/

import D5.S3.FiniteGroups.HeadleyCoordinateKernel

/-! Literal subgroup kernels, doubled ranges and their E4 quotient. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FiniteGroups.HeadleyDoubledCoordinates
open HeadleyCoordinateKernel Function

variable {r : ℕ} (e : Fin r → ℕ) (i j : Fin r) (hji : j ≠ i)

abbrev Rest := ∀ k : {k : {k // k ≠ i} // k ≠ ⟨j, hji⟩}, ZMod (2 ^ e k.val.val)

abbrev chart := splitTwo (fun k => ZMod (2 ^ e k)) i j hji

/-- Reduce exactly the two chosen positive coordinates. -/
def quotientHom (hi : 0 < e i) (hj : 0 < e j) : Coordinates e →+ ZMod 2 × ZMod 2 :=
  ((reduction (e i) hi).prodMap (reduction (e j) hj)).comp
    ((AddMonoidHom.fst _ (Rest e i j hji)).comp (chart e i j hji).toAddMonoidHom)

theorem quotientHom_surjective (hi : 0 < e i) (hj : 0 < e j) :
    Surjective (quotientHom e i j hji hi hj) := by
  rintro ⟨a,b⟩
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective
    (dvd_pow_self 2 (Nat.ne_of_gt hi)) a
  obtain ⟨y, hy⟩ := ZMod.castHom_surjective
    (dvd_pow_self 2 (Nat.ne_of_gt hj)) b
  refine ⟨(chart e i j hji).symm ((x,y),0), ?_⟩
  change ((reduction (e i) hi).prodMap (reduction (e j) hj))
    (((chart e i j hji) ((chart e i j hji).symm ((x,y),0))).1) = (a,b)
  rw [AddEquiv.apply_symm_apply]
  exact Prod.ext hx hy

private def lowerChart : Coordinates (lower e i j) ≃+
    (ZMod (2 ^ (e i - 1)) × ZMod (2 ^ (e j - 1))) × Rest e i j hji :=
  (chart (lower e i j) i j hji).trans
    (AddEquiv.prodCongr
      (AddEquiv.prodCongr
        (ZMod.ringEquivCongr (by simp [lower])).toAddEquiv
        (ZMod.ringEquivCongr (by simp [lower])).toAddEquiv)
      (AddEquiv.piCongrRight fun k =>
        (ZMod.ringEquivCongr (by
          have hki : k.val.val ≠ i := k.val.property
          have hkj : k.val.val ≠ j := fun h => k.property (Subtype.ext h)
          simp [lower, hki, hkj])).toAddEquiv))

private noncomputable def kernelChartEquiv (hi : 0 < e i) (hj : 0 < e j) :
    (((reduction (e i) hi).prodMap (reduction (e j) hj)).comp
      (AddMonoidHom.fst _ (Rest e i j hji))).ker ≃+ Coordinates (lower e i j) :=
  ((projectionKernelEquiv ((reduction (e i) hi).prodMap (reduction (e j) hj))).trans
    ((AddEquiv.prodCongr (productKernelEquiv _ _) (AddEquiv.refl _)).trans
      (AddEquiv.prodCongr
        (AddEquiv.prodCongr (reductionKernelEquiv (e i) hi)
          (reductionKernelEquiv (e j) hj)) (AddEquiv.refl _)))).trans
            (lowerChart e i j hji).symm

/-- Embed lowered coordinates in the original group through the two cyclic kernel
inclusions; the coordinate chart restores every unselected factor. -/
private noncomputable def lowerEmbedding (hi : 0 < e i) (hj : 0 < e j) :
    Coordinates (lower e i j) →+ Coordinates e :=
  (chart e i j hji).symm.toAddMonoidHom.comp
    ((((reduction (e i) hi).prodMap (reduction (e j) hj)).comp
      (AddMonoidHom.fst _ (Rest e i j hji))).ker.subtype.comp
        (kernelChartEquiv e i j hji hi hj).symm.toAddMonoidHom)

private theorem lowerEmbedding_injective (hi : 0 < e i) (hj : 0 < e j) :
    Injective (lowerEmbedding e i j hji hi hj) :=
  (chart e i j hji).symm.injective.comp
    (Subtype.val_injective.comp (kernelChartEquiv e i j hji hi hj).symm.injective)

/-- The quotient is E4, by the existing surjective first-isomorphism equivalence. -/
noncomputable def quotientEquiv (hi : 0 < e i) (hj : 0 < e j) :
    Coordinates e ⧸ (quotientHom e i j hji hi hj).ker ≃+ ZMod 2 × ZMod 2 :=
  QuotientAddGroup.quotientKerEquivOfSurjective _ (quotientHom_surjective e i j hji hi hj)

/-- Double the selected coordinates and leave every remaining coordinate unchanged. -/
def doubleCoordinates : Coordinates e →+ Coordinates e :=
  (chart e i j hji).symm.toAddMonoidHom.comp
    ((((nsmulAddMonoidHom (α := ZMod (2 ^ e i)) 2).prodMap
      (nsmulAddMonoidHom (α := ZMod (2 ^ e j)) 2)).prodMap
        (AddMonoidHom.id (Rest e i j hji))).comp (chart e i j hji).toAddMonoidHom)

/-- The chosen kernel is exactly the doubled-coordinate range, without any splitting premise. -/
theorem kernel_eq_doubled_range (hi : 0 < e i) (hj : 0 < e j) :
    (quotientHom e i j hji hi hj).ker = (doubleCoordinates e i j hji).range := by
  have hd (y : Coordinates e) : chart e i j hji (doubleCoordinates e i j hji y) =
      ((2 • (chart e i j hji y).1.1, 2 • (chart e i j hji y).1.2),
        (chart e i j hji y).2) := by
    change (chart e i j hji) ((chart e i j hji).symm _) = _
    rw [AddEquiv.apply_symm_apply]
    rfl
  ext x
  constructor
  · intro hx
    have hx1 : (chart e i j hji x).1.1 ∈ (reduction (e i) hi).ker :=
      congrArg Prod.fst hx
    have hx2 : (chart e i j hji x).1.2 ∈ (reduction (e j) hj).ker :=
      congrArg Prod.snd hx
    rw [reduction_kernel_eq_doubled] at hx1 hx2
    obtain ⟨a, ha⟩ := hx1
    obtain ⟨b, hb⟩ := hx2
    refine ⟨(chart e i j hji).symm ((a,b),(chart e i j hji x).2), ?_⟩
    apply (chart e i j hji).injective
    rw [hd, AddEquiv.apply_symm_apply]
    exact Prod.ext (Prod.ext ha hb) rfl
  · rintro ⟨y, rfl⟩
    change quotientHom e i j hji hi hj (doubleCoordinates e i j hji y) = 0
    change ((reduction (e i) hi).prodMap (reduction (e j) hj))
      ((chart e i j hji (doubleCoordinates e i j hji y)).1) = 0
    rw [hd]
    apply Prod.ext
    · change reduction (e i) hi (2 • _) = 0
      rw [map_nsmul]
      exact CharTwo.two_nsmul _
    · change reduction (e j) hj (2 • _) = 0
      rw [map_nsmul]
      exact CharTwo.two_nsmul _

private theorem lowerEmbedding_range (hi : 0 < e i) (hj : 0 < e j) :
    (lowerEmbedding e i j hji hi hj).range = (doubleCoordinates e i j hji).range := by
  have hid : (AddMonoidHom.id (Rest e i j hji)).range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr surjective_id
  simp only [lowerEmbedding, doubleCoordinates, AddMonoidHom.range_comp,
    AddEquiv.toAddMonoidHom_eq_coe, AddEquiv.range_eq_top, AddSubgroup.map_top,
    AddSubgroup.range_subtype, AddMonoidHom.range_prodMap, hid]
  congr 1
  rw [← reduction_kernel_eq_doubled (e i) hi,
    ← reduction_kernel_eq_doubled (e j) hj]
  ext x
  simp [AddMonoidHom.mem_ker, AddSubgroup.mem_prod, Prod.ext_iff]

/-- The actual subgroup type, not a cardinal surrogate, has the two lowered exponents.
The embedding image is the doubled range, identified with the literal kernel. -/
noncomputable def kernelEquiv (hi : 0 < e i) (hj : 0 < e j) :
    (quotientHom e i j hji hi hj).ker ≃+ Coordinates (lower e i j) :=
  ((AddMonoidHom.ofInjective (lowerEmbedding_injective e i j hji hi hj)).trans
    (AddEquiv.addSubgroupCongr ((lowerEmbedding_range e i j hji hi hj).trans
      (kernel_eq_doubled_range e i j hji hi hj).symm))).symm

end D5.S3.FiniteGroups.HeadleyDoubledCoordinates
