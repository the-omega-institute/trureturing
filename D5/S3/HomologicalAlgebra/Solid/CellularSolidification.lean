/- GID: D5/S3/HomologicalAlgebra/Solid/CellularSolidification
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/CellularSolidification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.LocalizationDefect

/-!
A concrete unbounded cellular construction from the protected defining
maps.  Each step attaches mapping cones along every chain map from every
integer placement of a defining cell.  The proved null-homotopies below
are actual data.  The sequential colimit is a construction in complexes;
locality and the derived universal property are not claimed here.
-/

noncomputable section
open CategoryTheory Limits MonoidalCategory MonoidalClosed HomologicalComplex

namespace LightCondensed.Solid

/-- All integer placements of the exact small family of defining maps. -/
def solidLocalizationCell (i : SmallModel.{0} LightProfinite × ℤ) :
    CochainComplex LightCondAb ℤ :=
  CochainComplex.mappingCone
    ((single LightCondAb (.up ℤ) i.2).map
      (oneMinusShift ▷ (free ℤ).obj
        ((equivSmallModel LightProfinite).inverse.obj i.1).toCondensed))

private abbrev CellMaps (K : CochainComplex LightCondAb ℤ) :=
  Σ i : SmallModel.{0} LightProfinite × ℤ, solidLocalizationCell i ⟶ K

private abbrev CellIndex (K : CochainComplex LightCondAb ℤ) := Shrink.{0} (CellMaps K)

private def cellFamily (K : CochainComplex LightCondAb ℤ) (j : CellIndex K) :
    CochainComplex LightCondAb ℤ := solidLocalizationCell ((equivShrink (CellMaps K)).symm j).1

private def cellEvaluation (K : CochainComplex LightCondAb ℤ) : ∐ (cellFamily K) ⟶ K :=
  Sigma.desc (fun j => ((equivShrink (CellMaps K)).symm j).2)

/-- One step attaches a cone along every defining-cell map into `K`. -/
def solidCellularStep (K : CochainComplex LightCondAb ℤ) :
    CochainComplex LightCondAb ℤ := CochainComplex.mappingCone (cellEvaluation K)

/-- The map into the next cellular stage. -/
def solidCellularStepι (K : CochainComplex LightCondAb ℤ) : K ⟶ solidCellularStep K :=
  CochainComplex.mappingCone.inr (cellEvaluation K)

set_option backward.isDefEq.respectTransparency false in
/-- Every map from a defining cell is killed by an explicit homotopy at the
next stage.  The degree and the incoming complex are arbitrary. -/
def solidCellularStepHomotopy
    (K : CochainComplex LightCondAb ℤ) (i : SmallModel.{0} LightProfinite × ℤ)
    (g : solidLocalizationCell i ⟶ K) : Homotopy (g ≫ solidCellularStepι K) 0 := by
  let j : CellIndex K := equivShrink (CellMaps K) ⟨i, g⟩
  let e : solidLocalizationCell i ≅ cellFamily K j :=
    eqToIso (by simp [cellFamily, j])
  have h : e.hom ≫ Sigma.ι (cellFamily K) j ≫ cellEvaluation K = g := by
    simp only [cellEvaluation, colimit.ι_desc, Cofan.mk_ι_app]
    have aux (q : CellMaps K) (hq : q = ⟨i, g⟩) :
        eqToHom (congrArg solidLocalizationCell (congrArg Sigma.fst hq).symm) ≫ q.2 = g := by
      subst q
      simp
    exact aux ((equivShrink (CellMaps K)).symm j)
      ((equivShrink (CellMaps K)).symm_apply_apply ⟨i, g⟩)
  have hh := (homotopyCofiber.inrCompHomotopy (cellEvaluation K)
    (fun j => ⟨j - 1, by change j - 1 + 1 = j; omega⟩)).compLeft
    (e.hom ≫ Sigma.ι (cellFamily K) j)
  have h' : (e.hom ≫ Sigma.ι (cellFamily K) j) ≫ cellEvaluation K = g := by
    simpa only [Category.assoc] using h
  simpa only [← Category.assoc, h', comp_zero, solidCellularStepι,
    CochainComplex.mappingCone.inr] using hh

/-- The full sequence starts at an arbitrary unbounded complex. -/
def solidCellularStage (K : CochainComplex LightCondAb ℤ) :
    ℕ → CochainComplex LightCondAb ℤ
  | 0 => K
  | n + 1 => solidCellularStep (solidCellularStage K n)

def solidCellularDiagram (K : CochainComplex LightCondAb ℤ) :
    ℕ ⥤ CochainComplex LightCondAb ℤ :=
  Functor.ofSequence (fun n => solidCellularStepι (solidCellularStage K n))

/-- The actual sequential colimit, formed degreewise, of all cellular stages.
This definition alone asserts neither locality nor a derived adjunction. -/
def solidCellularColimit (K : CochainComplex LightCondAb ℤ) :
    CochainComplex LightCondAb ℤ := colimit (solidCellularDiagram K)

set_option backward.isDefEq.respectTransparency false in
/-- Maps from defining cells that enter at any finite stage are explicitly
null-homotopic in the full sequential colimit. -/
def solidCellularColimitHomotopy
    (K : CochainComplex LightCondAb ℤ) (n : ℕ)
    (i : SmallModel.{0} LightProfinite × ℤ)
    (g : solidLocalizationCell i ⟶ solidCellularStage K n) :
    Homotopy (g ≫ colimit.ι (solidCellularDiagram K) n) 0 := by
  have h : solidCellularStepι (solidCellularStage K n) ≫
      colimit.ι (solidCellularDiagram K) (n + 1) =
        colimit.ι (solidCellularDiagram K) n := by
    simpa [solidCellularDiagram] using
      (colimit.w (solidCellularDiagram K) (homOfLE (Nat.le_succ n)))
  have hh := (solidCellularStepHomotopy (solidCellularStage K n) i g).compRight
    (colimit.ι (solidCellularDiagram K) (n + 1))
  simpa only [Category.assoc, h, zero_comp] using hh

end LightCondensed.Solid
