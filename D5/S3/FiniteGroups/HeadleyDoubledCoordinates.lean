/- GID: D5/S3/FiniteGroups/HeadleyDoubledCoordinates
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyDoubledCoordinates
   mirror-E: none(waiver:two-coordinate-kernel)
   anchors: []
   utility: none
   digest: The literal two-coordinate kernel, its decremented coordinates and E4 quotient. -/

import D5.S3.FiniteGroups.HeadleyCoordinateKernel

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

private def kernelCompEquiv {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : B →+ C) (E : A ≃+ B) : (f.comp E.toAddMonoidHom).ker ≃+ f.ker :=
  (AddEquiv.addSubgroupCongr (AddMonoidHom.ker_comp_addEquiv f E)).trans
    (E.symm.addSubgroupMap f.ker).symm

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

/-- The actual subgroup type, not a cardinal surrogate, has the two lowered exponents. -/
noncomputable def kernelEquiv (hi : 0 < e i) (hj : 0 < e j) :
    (quotientHom e i j hji hi hj).ker ≃+ Coordinates (lower e i j) :=
  ((kernelCompEquiv
      (((reduction (e i) hi).prodMap (reduction (e j) hj)).comp
        (AddMonoidHom.fst _ (Rest e i j hji))) (chart e i j hji)).trans
    ((projectionKernelEquiv ((reduction (e i) hi).prodMap (reduction (e j) hj))).trans
      ((AddEquiv.prodCongr (productKernelEquiv _ _) (AddEquiv.refl _)).trans
        (AddEquiv.prodCongr
          (AddEquiv.prodCongr (reductionKernelEquiv (e i) hi)
            (reductionKernelEquiv (e j) hj)) (AddEquiv.refl _))))).trans
              (lowerChart e i j hji).symm

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
    simp only [doubleCoordinates, AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
      AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply, AddMonoidHom.prodMap_apply,
      AddMonoidHom.id_apply]
    exact Prod.ext (Prod.ext ha hb) rfl
  · rintro ⟨y, rfl⟩
    change quotientHom e i j hji hi hj (doubleCoordinates e i j hji y) = 0
    change ((reduction (e i) hi).prodMap (reduction (e j) hj))
      ((chart e i j hji (doubleCoordinates e i j hji y)).1) = 0
    simp [doubleCoordinates, map_nsmul, CharTwo.two_nsmul]

end D5.S3.FiniteGroups.HeadleyDoubledCoordinates
