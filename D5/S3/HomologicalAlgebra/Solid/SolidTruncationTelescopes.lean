/- GID: D5/S3/HomologicalAlgebra/Solid/SolidTruncationTelescopes
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/SolidTruncationTelescopes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.Colimits
import D5.S3.HomologicalAlgebra.Solid.UnboundedUpperTruncationColimit
import D5.S3.HomologicalAlgebra.Solid.UnboundedTruncationColimit
import D5.S3.HomologicalAlgebra.Solid.SequentialPresentation
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-!
Copyright (c) 2026. Released under the Apache 2.0 license.
Both verified unbounded truncation colimits become genuine mapping-cone
quasi-isomorphisms in the protected Solid category. The colimit proofs are
imported unchanged. Monicity reuses the actual AB5 sequence presentation;
no unbounded completeness or generation premise is assumed.
Research: Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits HomologicalComplex

namespace LightCondensed.Solid

/-- Exact filtered colimits and the actual ordinary reflection prove the
Grothendieck property of the protected Solid category. This uses no
projective-resolution, derived-realization, or derived-adjunction premise. -/
instance solid_isGrothendieckAbelian : IsGrothendieckAbelian.{0} Solid := by
  haveI : IsGrothendieckAbelian.{0} LightCondAb := inferInstance
  haveI : HasColimitsOfSize.{0, 0} Solid := ⟨fun J _ => inferInstance⟩
  haveI : HasSeparator Solid := by
    let F := isSolid.ι.leftAdjoint
    let adj : F ⊣ isSolid.ι := Adjunction.ofIsRightAdjoint isSolid.ι
    refine ⟨F.obj (separator LightCondAb), (isSeparator_def _).2 ?_⟩
    intro X Y f g hfg
    apply isSolid.ι.map_injective
    apply (isSeparator_separator LightCondAb).def
    intro h
    let k := (adj.homEquiv (separator LightCondAb) X).symm h
    have hk := congrArg (adj.homEquiv (separator LightCondAb) Y) (hfg k)
    simpa only [Adjunction.homEquiv_naturality_right, k, Equiv.apply_symm_apply] using hk
  haveI : AB5OfSize.{0, 0} Solid := ⟨fun J _ _ => by
    exact HasExactColimitsOfShape.domain_of_functor J isSolid.ι⟩
  exact {}

end LightCondensed.Solid

namespace CWSolid

section
variable {C : Type*} [Category* C] [Abelian C] [IsGrothendieckAbelian.{0} C]
  (F : ℕ ⥤ CochainComplex C ℤ)

def complexSequenceDifferential :
    (∐ fun n => F.obj n) ⟶ ∐ fun n => F.obj n :=
  𝟙 _ - Limits.Sigma.desc (fun n => F.map (homOfLE (Nat.le_succ n)) ≫
    Sigma.ι (fun n => F.obj n) (n + 1))

def complexSequenceToCocone (c : Cocone F) : (∐ fun n => F.obj n) ⟶ c.pt :=
  Limits.Sigma.desc (fun n => c.ι.app n)

private theorem complexSequenceDifferential_comp (c : Cocone F) :
    complexSequenceDifferential F ≫ complexSequenceToCocone F c = 0 := by
  apply Sigma.hom_ext
  intro n
  simp [complexSequenceDifferential, complexSequenceToCocone,
    Preadditive.comp_sub, Preadditive.sub_comp, c.w]

def complexSequenceShortComplex (c : Cocone F) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (complexSequenceDifferential F) (complexSequenceToCocone F c)
    (complexSequenceDifferential_comp F c)

/-- The telescope really presents the specified colimit cocone. -/
def complexSequence_isCokernel (c : Cocone F) (hc : IsColimit c) :
    IsColimit (CokernelCofork.ofπ (complexSequenceShortComplex F c).g
      (complexSequenceShortComplex F c).zero) := by
  let S := complexSequenceShortComplex F c
  have descExists {Y : CochainComplex C ℤ}
      (g : S.X₂ ⟶ Y) (hg : S.f ≫ g = 0) : ∃ u : c.pt ⟶ Y, S.g ≫ u = g := by
    have hn (n : ℕ) : F.map (homOfLE (Nat.le_succ n)) ≫
        (Sigma.ι (fun n => F.obj n) (n + 1) ≫ g) =
          Sigma.ι (fun n => F.obj n) n ≫ g := by
      have h := congrArg (Sigma.ι (fun n => F.obj n) n ≫ ·) hg
      simp only [S, complexSequenceShortComplex, complexSequenceDifferential,
        Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp,
        Sigma.ι_desc_assoc, comp_zero] at h
      simpa only [Category.assoc] using (sub_eq_zero.mp h).symm
    let d : Cocone F :=
      { pt := Y
        ι := NatTrans.ofSequence (fun n => Sigma.ι (fun n => F.obj n) n ≫ g)
          (fun n => by simpa using hn n) }
    refine ⟨hc.desc d, ?_⟩
    apply Sigma.hom_ext
    intro n
    change Sigma.ι (fun n => F.obj n) n ≫ complexSequenceToCocone F c ≫ hc.desc d = _
    simp only [complexSequenceToCocone, Sigma.ι_desc_assoc]
    exact hc.fac d n
  refine CokernelCofork.IsColimit.ofπ S.g S.zero
    (fun g hg => (descExists g hg).choose)
    (fun g hg => (descExists g hg).choose_spec) ?_
  intro Y g hg u hu
  apply hc.hom_ext
  intro n
  have h := congrArg (Sigma.ι (fun n => F.obj n) n ≫ ·)
    (hu.trans (descExists g hg).choose_spec.symm)
  simpa only [S, complexSequenceShortComplex, complexSequenceToCocone,
    Sigma.ι_desc_assoc] using h

theorem complexSequenceDifferential_f_mono (m : ℤ) :
    Mono ((complexSequenceDifferential F).f m) := by
  let G := eval C (.up ℤ) m
  let A : ℕ → C := fun n => G.obj (F.obj n)
  let a : ∀ n, A n ⟶ A (n + 1) :=
    fun n => G.map (F.map (homOfLE (Nat.le_succ n)))
  let e := PreservesCoproduct.iso G (fun n => F.obj n)
  let d := 𝟙 (∐ A) - Limits.Sigma.desc (fun n => a n ≫ Sigma.ι A (n + 1))
  have hleg (n : ℕ) : G.map (Sigma.ι (fun n => F.obj n) n) ≫ e.hom = Sigma.ι A n := by
    simpa [e, A, ← PreservesCoproduct.inv_hom] using
      (map_ι_comp_inv_sigmaComparison (G := G) (f := fun n => F.obj n) n)
  have hlegInv (n : ℕ) : Sigma.ι A n ≫ e.inv = G.map (Sigma.ι (fun n => F.obj n) n) := by
    rw [← hleg, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hd : e.inv ≫ G.map (complexSequenceDifferential F) ≫ e.hom = d := by
    apply Sigma.hom_ext
    intro n
    change Sigma.ι A n ≫ e.inv ≫ G.map (complexSequenceDifferential F) ≫ e.hom =
      Sigma.ι A n ≫ d
    rw [← Category.assoc, hlegInv, ← G.map_comp_assoc]
    have hn : Sigma.ι (fun n => F.obj n) n ≫ complexSequenceDifferential F =
        Sigma.ι (fun n => F.obj n) n - F.map (homOfLE (Nat.le_succ n)) ≫
          Sigma.ι (fun n => F.obj n) (n + 1) := by
      simp [complexSequenceDifferential, Preadditive.comp_sub]
    rw [hn, G.map_sub, Preadditive.sub_comp, G.map_comp, Category.assoc, hleg, hleg]
    dsimp only [d]
    rw [Preadditive.comp_sub, Category.comp_id, Sigma.ι_desc]
  have he : G.map (complexSequenceDifferential F) = e.hom ≫ d ≫ e.inv := by
    rw [← hd]
    simp
  haveI : Mono d := oneMinusSequence_mono A a
  change Mono (G.map (complexSequenceDifferential F))
  rw [he]
  infer_instance

theorem complexSequence_shortExact (c : Cocone F) (hc : IsColimit c) :
    (complexSequenceShortComplex F c).ShortExact := by
  haveI : Mono (complexSequenceShortComplex F c).f :=
    HomologicalComplex.mono_of_mono_f _ (complexSequenceDifferential_f_mono F)
  haveI : Epi (complexSequenceShortComplex F c).g :=
    epi_of_isColimit_cofork (complexSequence_isCokernel F c hc)
  exact { exact := ((complexSequenceShortComplex F c).exact_of_g_is_cokernel
    (complexSequence_isCokernel F c hc)) }

def complexSequenceTelescope : CochainComplex C ℤ :=
  CochainComplex.mappingCone (complexSequenceDifferential F)

def complexSequenceTelescopeToCocone (c : Cocone F) :
    complexSequenceTelescope F ⟶ c.pt :=
  CochainComplex.mappingCone.descShortComplex (complexSequenceShortComplex F c)

theorem complexSequenceTelescopeToCocone_quasiIso (c : Cocone F) (hc : IsColimit c) :
    QuasiIso (complexSequenceTelescopeToCocone F c) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex (complexSequence_shortExact F c hc)

end
end CWSolid

namespace LightCondensed.Solid
open CWSolid

/-- Actual lower telescope in Solid, for an arbitrary unbounded complex. -/
def solidLowerTruncationTelescope (K : CochainComplex Solid ℤ) : CochainComplex Solid ℤ :=
  complexSequenceTelescope (lowerTruncationDiagram K)

def solidLowerTruncationTelescopeToInput (K : CochainComplex Solid ℤ) :
    solidLowerTruncationTelescope K ⟶ K :=
  complexSequenceTelescopeToCocone (lowerTruncationDiagram K) (lowerTruncationCocone K)

theorem solidLowerTruncationTelescopeToInput_quasiIso (K : CochainComplex Solid ℤ) :
    QuasiIso (solidLowerTruncationTelescopeToInput K) :=
  complexSequenceTelescopeToCocone_quasiIso _ _ (lowerTruncationCocone_isColimit K)

/-- Actual good upper telescope in Solid, with no boundedness premise. -/
def solidUpperTruncationTelescope (K : CochainComplex Solid ℤ) : CochainComplex Solid ℤ :=
  complexSequenceTelescope (upperTruncationDiagram K)

def solidUpperTruncationTelescopeToInput (K : CochainComplex Solid ℤ) :
    solidUpperTruncationTelescope K ⟶ K :=
  complexSequenceTelescopeToCocone (upperTruncationDiagram K) (upperTruncationCocone K)

theorem solidUpperTruncationTelescopeToInput_quasiIso (K : CochainComplex Solid ℤ) :
    QuasiIso (solidUpperTruncationTelescopeToInput K) :=
  complexSequenceTelescopeToCocone_quasiIso _ _ (upperTruncationCocone_isColimit K)

end LightCondensed.Solid

#print axioms CWSolid.complexSequenceDifferential
#print axioms LightCondensed.Solid.solid_isGrothendieckAbelian
#print axioms CWSolid.complexSequenceToCocone
#print axioms CWSolid.complexSequenceShortComplex
#print axioms CWSolid.complexSequence_isCokernel
#print axioms CWSolid.complexSequenceDifferential_f_mono
#print axioms CWSolid.complexSequence_shortExact
#print axioms CWSolid.complexSequenceTelescope
#print axioms CWSolid.complexSequenceTelescopeToCocone
#print axioms CWSolid.complexSequenceTelescopeToCocone_quasiIso
#print axioms LightCondensed.Solid.solidLowerTruncationTelescope
#print axioms LightCondensed.Solid.solidLowerTruncationTelescopeToInput
#print axioms LightCondensed.Solid.solidLowerTruncationTelescopeToInput_quasiIso
#print axioms LightCondensed.Solid.solidUpperTruncationTelescope
#print axioms LightCondensed.Solid.solidUpperTruncationTelescopeToInput
#print axioms LightCondensed.Solid.solidUpperTruncationTelescopeToInput_quasiIso
