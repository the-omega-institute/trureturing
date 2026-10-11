/- GID: D5/S3/HomologicalAlgebra/Solid/TelescopeEquivalence
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/TelescopeEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.TelescopeComparison
import D5.S3.HomologicalAlgebra.Solid.SequentialPresentation
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-! The saved telescope and the saved ordinary cellular colimit are
quasi-isomorphic for every arbitrary unbounded input. New proofs,
released under the Apache 2.0 license. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits HomologicalComplex

namespace LightCondensed.Solid

local instance telescopeEquivalenceCoproducts :
    HasColimitsOfShape (Discrete ℕ) (CochainComplex LightCondAb ℤ) where
  has_colimit F := by
    haveI : HasColimitsOfShape (Discrete ℕ) LightCondAb := solidification_hasSmallCoproducts ℕ
    haveI (n : ℤ) : HasColimit (F ⋙ eval LightCondAb (.up ℤ) n) := inferInstance
    exact ⟨⟨⟨HomologicalComplex.coconeOfHasColimitEval F,
      HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩

/-- The actual one-minus-transition map is monic in every degree. -/
theorem solidCellularTelescopeDifferential_f_mono
    (K : CochainComplex LightCondAb ℤ) (m : ℤ) :
    Mono ((solidCellularTelescopeDifferential K).f m) := by
  haveI : IsGrothendieckAbelian.{0} LightCondAb := inferInstance
  haveI : AB5OfSize.{0, 0} LightCondAb := inferInstance
  let G := eval LightCondAb (.up ℤ) m
  let A : ℕ → LightCondAb := fun n => G.obj (solidCellularStage K n)
  let a : ∀ n, A n ⟶ A (n + 1) :=
    fun n => G.map (solidCellularStepι (solidCellularStage K n))
  let e := PreservesCoproduct.iso G (solidCellularStage K)
  let d := 𝟙 (∐ A) - Limits.Sigma.desc (fun n => a n ≫ Sigma.ι A (n + 1))
  have hleg (n : ℕ) : G.map (Sigma.ι (solidCellularStage K) n) ≫ e.hom =
      Sigma.ι A n := by
    simpa [e, A, ← PreservesCoproduct.inv_hom] using
      (map_ι_comp_inv_sigmaComparison (G := G) (f := solidCellularStage K) n)
  have hlegInv (n : ℕ) : Sigma.ι A n ≫ e.inv =
      G.map (Sigma.ι (solidCellularStage K) n) := by
    rw [← hleg, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hd : e.inv ≫ G.map (solidCellularTelescopeDifferential K) ≫ e.hom = d := by
    apply Sigma.hom_ext
    intro n
    change Sigma.ι A n ≫ e.inv ≫ G.map (solidCellularTelescopeDifferential K) ≫ e.hom =
      Sigma.ι A n ≫ d
    rw [← Category.assoc, hlegInv, ← G.map_comp_assoc]
    have hn : Sigma.ι (solidCellularStage K) n ≫ solidCellularTelescopeDifferential K =
        Sigma.ι (solidCellularStage K) n -
          solidCellularStepι (solidCellularStage K n) ≫
            Sigma.ι (solidCellularStage K) (n + 1) := by
      simp [solidCellularTelescopeDifferential, Preadditive.comp_sub]
    rw [hn, G.map_sub, Preadditive.sub_comp, G.map_comp, Category.assoc,
      hleg, hleg]
    dsimp only [d]
    rw [Preadditive.comp_sub, Category.comp_id, Sigma.ι_desc]
  have he : G.map (solidCellularTelescopeDifferential K) = e.hom ≫ d ≫ e.inv := by
    rw [← hd]
    simp
  haveI : Mono d := CWSolid.oneMinusSequence_mono A a
  change Mono (G.map (solidCellularTelescopeDifferential K))
  rw [he]
  infer_instance

/-- Monicity is genuine in the category of all unbounded complexes. -/
theorem solidCellularTelescopeDifferential_mono (K : CochainComplex LightCondAb ℤ) :
    Mono (solidCellularTelescopeDifferential K) :=
  HomologicalComplex.mono_of_mono_f _ (solidCellularTelescopeDifferential_f_mono K)

/-- The full saved sum-to-colimit presentation is short exact. -/
theorem solidCellularTelescopeShortComplex_shortExact
    (K : CochainComplex LightCondAb ℤ) :
    (solidCellularTelescopeShortComplex K).ShortExact := by
  haveI : Mono (solidCellularTelescopeShortComplex K).f :=
    solidCellularTelescopeDifferential_mono K
  haveI : Epi (solidCellularTelescopeShortComplex K).g :=
    epi_of_isColimit_cofork (solidCellularTelescopeShortComplex_isCokernel K)
  exact { exact := solidCellularTelescopeShortComplex_exact K }

/-- The saved comparison equals the canonical map attached to this actual
short exact presentation. -/
theorem solidCellularTelescopeToColimit_eq_descShortComplex
    (K : CochainComplex LightCondAb ℤ) :
    solidCellularTelescopeToColimit K =
      CochainComplex.mappingCone.descShortComplex (solidCellularTelescopeShortComplex K) := by
  ext n : 1
  apply CochainComplex.mappingCone.ext_from _ (n + 1) n rfl
  · calc
      _ = 0 := by
        simp [solidCellularTelescopeToColimit, CochainComplex.mappingCone.inl, Homotopy.ofEq]
      _ = _ := (CochainComplex.mappingCone.inl_v_descShortComplex_f
        (solidCellularTelescopeShortComplex K) (n + 1) n (by omega)).symm
  · calc
      _ = (solidCellularTelescopeShortComplex K).g.f n := by
        simp [solidCellularTelescopeToColimit, CochainComplex.mappingCone.inr,
          homotopyCofiber.inr, solidCellularTelescopeShortComplex]
      _ = _ := (CochainComplex.mappingCone.inr_f_descShortComplex_f
        (solidCellularTelescopeShortComplex K) n).symm

/-- The actual mapping telescope is quasi-isomorphic to the actual cellular
colimit, for every input and every integer homology degree. -/
theorem solidCellularTelescopeToColimit_quasiIso
    (K : CochainComplex LightCondAb ℤ) :
    QuasiIso (solidCellularTelescopeToColimit K) := by
  rw [solidCellularTelescopeToColimit_eq_descShortComplex]
  exact CochainComplex.mappingCone.quasiIso_descShortComplex
    (solidCellularTelescopeShortComplex_shortExact K)

/-- The telescope itself is now genuinely derived-local. -/
theorem solidCellularTelescope_homology_solid
    (K : CochainComplex LightCondAb ℤ) (n : ℤ) :
    isSolid ((solidCellularTelescope K).homology n) := by
  haveI := solidCellularTelescopeToColimit_quasiIso K
  exact isSolid.prop_of_iso (asIso (homologyMap (solidCellularTelescopeToColimit K) n)).symm
    (solidCellularColimit_homology_solid K n)

end LightCondensed.Solid
