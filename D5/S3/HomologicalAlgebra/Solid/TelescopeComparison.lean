/- GID: D5/S3/HomologicalAlgebra/Solid/TelescopeComparison
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/TelescopeComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.CellularTelescope

/-! The actual comparison from the mapping telescope to the previously
saved ordinary cellular colimit. This defines and proves the comparison
equations; its quasi-isomorphism property is an explicit remaining theorem,
not an assumed bridge. New proofs, released under Apache 2.0. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits HomologicalComplex

namespace LightCondensed.Solid

local instance telescopeComparisonCoproducts :
    HasColimitsOfShape (Discrete ℕ) (CochainComplex LightCondAb ℤ) where
  has_colimit F := by
    haveI : HasColimitsOfShape (Discrete ℕ) LightCondAb := solidification_hasSmallCoproducts ℕ
    haveI (n : ℤ) : HasColimit (F ⋙ eval LightCondAb (.up ℤ) n) := inferInstance
    exact ⟨⟨⟨HomologicalComplex.coconeOfHasColimitEval F,
      HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩

private def cellularSumToColimit (K : CochainComplex LightCondAb ℤ) :
    (∐ solidCellularStage K) ⟶ solidCellularColimit K :=
  Limits.Sigma.desc (fun n => colimit.ι (solidCellularDiagram K) n)

private theorem telescopeDifferential_comp_colimit (K : CochainComplex LightCondAb ℤ) :
    solidCellularTelescopeDifferential K ≫ cellularSumToColimit K = 0 := by
  apply Sigma.hom_ext
  intro n
  have hstep : solidCellularStepι (solidCellularStage K n) ≫
      colimit.ι (solidCellularDiagram K) (n + 1) = colimit.ι (solidCellularDiagram K) n := by
    simpa [solidCellularDiagram] using
      (colimit.w (solidCellularDiagram K) (homOfLE (Nat.le_succ n)))
  simp only [solidCellularTelescopeDifferential, Preadditive.comp_sub,
    Category.comp_id, Category.id_comp, Sigma.ι_desc, Sigma.ι_desc_assoc,
    Preadditive.sub_comp, Category.assoc, cellularSumToColimit, hstep, sub_self, comp_zero]

/-- The actual telescope-to-colimit chain map induced by the original
cellular cocone. No quasi-isomorphism property is included in this definition. -/
def solidCellularTelescopeToColimit (K : CochainComplex LightCondAb ℤ) :
    solidCellularTelescope K ⟶ solidCellularColimit K :=
  homotopyCofiber.desc (solidCellularTelescopeDifferential K) (cellularSumToColimit K)
    (Homotopy.ofEq (telescopeDifferential_comp_colimit K))

/-- The telescope comparison recovers the original colimit leg at every stage. -/
theorem solidCellularTelescopeToColimit_leg (K : CochainComplex LightCondAb ℤ) (n : ℕ) :
    Sigma.ι (solidCellularStage K) n ≫
        CochainComplex.mappingCone.inr (solidCellularTelescopeDifferential K) ≫
          solidCellularTelescopeToColimit K = colimit.ι (solidCellularDiagram K) n := by
  simp [solidCellularTelescopeToColimit, CochainComplex.mappingCone.inr, cellularSumToColimit]

/-- In particular, the comparison preserves the map from the original
arbitrary unbounded complex into the ordinary saved cellular colimit. -/
theorem solidCellularTelescopeToColimit_input (K : CochainComplex LightCondAb ℤ) :
    solidCellularTelescopeι K ≫ solidCellularTelescopeToColimit K =
      colimit.ι (solidCellularDiagram K) 0 := by
  simpa only [solidCellularTelescopeι, Category.assoc] using
    solidCellularTelescopeToColimit_leg K 0

/-- The original sum-to-colimit presentation, with its proved zero composite. -/
def solidCellularTelescopeShortComplex (K : CochainComplex LightCondAb ℤ) :
    ShortComplex (CochainComplex LightCondAb ℤ) :=
  ShortComplex.mk (solidCellularTelescopeDifferential K) (cellularSumToColimit K)
    (telescopeDifferential_comp_colimit K)

/-- The saved ordinary cellular colimit is genuinely the cokernel of the
one-minus-transition map on the actual sum of all stages. -/
def solidCellularTelescopeShortComplex_isCokernel (K : CochainComplex LightCondAb ℤ) :
    IsColimit (CokernelCofork.ofπ (solidCellularTelescopeShortComplex K).g
      (solidCellularTelescopeShortComplex K).zero) := by
  let S := solidCellularTelescopeShortComplex K
  have descExists {Y : CochainComplex LightCondAb ℤ}
      (g : S.X₂ ⟶ Y) (hg : S.f ≫ g = 0) :
      ∃ u : S.X₃ ⟶ Y, S.g ≫ u = g := by
    have hn (n : ℕ) : solidCellularStepι (solidCellularStage K n) ≫
        (Sigma.ι (solidCellularStage K) (n + 1) ≫ g) = Sigma.ι (solidCellularStage K) n ≫ g := by
      have h := congrArg (Sigma.ι (solidCellularStage K) n ≫ ·) hg
      simp only [S, solidCellularTelescopeShortComplex, solidCellularTelescopeDifferential,
        Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp,
        Sigma.ι_desc_assoc, comp_zero] at h
      exact (sub_eq_zero.mp h).symm
    let c : Cocone (solidCellularDiagram K) :=
      { pt := Y
        ι := NatTrans.ofSequence (fun n => Sigma.ι (solidCellularStage K) n ≫ g)
          (fun n => by simpa [solidCellularDiagram] using hn n) }
    refine ⟨colimit.desc (solidCellularDiagram K) c, ?_⟩
    apply Sigma.hom_ext
    intro n
    change Sigma.ι (solidCellularStage K) n ≫ cellularSumToColimit K ≫
      colimit.desc (solidCellularDiagram K) c = Sigma.ι (solidCellularStage K) n ≫ g
    simp [cellularSumToColimit, c]
  refine CokernelCofork.IsColimit.ofπ S.g S.zero
    (fun g hg => (descExists g hg).choose)
    (fun g hg => (descExists g hg).choose_spec) ?_
  intro Y g hg u hu
  apply colimit.hom_ext
  intro n
  have h := congrArg (Sigma.ι (solidCellularStage K) n ≫ ·)
    (hu.trans (descExists g hg).choose_spec.symm)
  simpa only [S, solidCellularTelescopeShortComplex, cellularSumToColimit,
    Sigma.ι_desc_assoc] using h

/-- Exactness at the middle of the actual telescope presentation. The
remaining short-exactness input is monicity of its first map. -/
theorem solidCellularTelescopeShortComplex_exact (K : CochainComplex LightCondAb ℤ) :
    (solidCellularTelescopeShortComplex K).Exact :=
  (solidCellularTelescopeShortComplex K).exact_of_g_is_cokernel
    (solidCellularTelescopeShortComplex_isCokernel K)

end LightCondensed.Solid
