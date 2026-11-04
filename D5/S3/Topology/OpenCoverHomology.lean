/- GID: D5/S3/Topology/OpenCoverHomology
   generality: G
   mirror-B: D5/B/S3/Topology/OpenCoverHomology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive singular homology splits across open covers with reduced-acyclic intersections. -/
import D5.S3.Topology.TauCeti.AlgebraicTopology.Singular.MayerVietoris.Reduced
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! Positive singular homology splits over open covers via reduced Mayer–Vietoris. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology TauCeti Set

universe w v u
namespace D5.S3.Topology.OpenCoverHomology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- The actual MV inclusion map is invertible in positive degrees when the
intersection is empty or contractible. In particular degree one uses reduced
H₀ of the intersection, rather than incorrectly requiring ordinary H₀ = 0. -/
def inclusionIso {X : TopCat.{w}} {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (hI : IsEmpty ↥(U ∩ V) ∨ ContractibleSpace ↥(U ∩ V))
    (q : ℕ) (hq : 0 < q) :
    (((singularHomologyFunctor C q).obj R).obj (TopCat.of U) ⊞
      ((singularHomologyFunctor C q).obj R).obj (TopCat.of V)) ≅
      ((singularHomologyFunctor C q).obj R).obj X := by
  let r := q - 1
  have hqr : q = r + 1 := (Nat.sub_add_cancel hq).symm
  rw [hqr]
  have hz (n : ℕ) : IsZero ((reducedSingularHomologyFunctor R n).obj
      (TopCat.of ↥(U ∩ V))) := by
    rcases hI with h | h
    · letI := h
      exact isZero_reducedSingularHomologyFunctor_of_isEmpty R _ n
    · letI := h
      exact isZero_reducedSingularHomologyFunctor_of_contractibleSpace R _ n
  let f := SSet.mayerVietorisFromBiprod R
    (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal U)))
    (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal V))) (r + 1)
  have hsource : IsZero ((TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))).homology R (r + 1)) :=
    (hz (r + 1)).of_iso ((reducedSingularHomologySuccIso R r).app _).symm
  letI instMono : Mono f := (TopCat.mayerVietoris_exact₂ R hU hV hUV (r + 1)).mono_g
    (hsource.eq_of_src _ _)
  have hδ : TopCat.mayerVietorisδ R hU hV hUV (r + 1) r = 0 := by
    rw [← TopCat.reducedMayerVietorisδ_comp_ι R hU hV hUV r,
      (hz r).eq_of_tgt (TopCat.reducedMayerVietorisδ R hU hV hUV r) 0, zero_comp]
    rfl
  letI instEpi : Epi f := (TopCat.mayerVietoris_exact₃ R hU hV hUV (r + 1) r).epi_f hδ
  letI instIso : IsIso f := isIso_of_mono_of_epi f
  exact @asIso _ _ _ _ f instIso

/-- Disjoint topological sums are handled by actual open inclusions. This is
singular additivity for a topological sum, not a chain-coproduct assertion. -/
def sumIso (X Y : Type w) [TopologicalSpace X] [TopologicalSpace Y]
    (q : ℕ) (hq : 0 < q) :
    (((singularHomologyFunctor C q).obj R).obj (TopCat.of X) ⊞
      ((singularHomologyFunctor C q).obj R).obj (TopCat.of Y)) ≅
      ((singularHomologyFunctor C q).obj R).obj (TopCat.of (X ⊕ Y)) := by
  let U : Set (TopCat.of (X ⊕ Y)) := range Sum.inl
  let V : Set (TopCat.of (X ⊕ Y)) := range Sum.inr
  have hU : IsOpen U := isOpen_range_inl
  have hV : IsOpen V := isOpen_range_inr
  have hUV : U ∪ V = univ := by ext x; cases x <;> simp [U, V]
  have hI : IsEmpty ↥(U ∩ V) := by
    refine ⟨?_⟩
    rintro ⟨z, ⟨⟨x, hx⟩, ⟨y, hy⟩⟩⟩
    cases (hx.trans hy.symm)
  let eX : X ≃ₜ U := Topology.IsEmbedding.inl.toHomeomorph
  let eY : Y ≃ₜ V := Topology.IsEmbedding.inr.toHomeomorph
  exact (biprod.mapIso
      (((singularHomologyFunctor C q).obj R).mapIso (TopCat.isoOfHomeo eX))
      (((singularHomologyFunctor C q).obj R).mapIso (TopCat.isoOfHomeo eY))) ≪≫
    inclusionIso R hU hV hUV (Or.inl hI) q hq

end D5.S3.Topology.OpenCoverHomology
