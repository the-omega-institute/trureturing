import CFMPGenericInteriorEdge1436Transient
import Mathlib.Topology.Homeomorph.Quotient

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceInteriorTopology1460Candidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate
open Topology Set
variable {T : Type*} [TopologicalSpace T] [DiscreteTopology T]

abbrev PointQuotient (P : RawFacePairing T) (ν : Vertex P) :=
  Quotient (Relation.EqvGen.setoid (Step P (ν := ν)))

def InteriorPatch (P : RawFacePairing T) (ν : Vertex P) (c : T × Fin 4) :
    Set (Point P ν) := {x | x.val.1 = c ∧ Interior P x}

def quotientInteriorPatch (P : RawFacePairing T) (ν : Vertex P) (c : T × Fin 4) :
    Set (PointQuotient P ν) :=
  (@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν)))) '' InteriorPatch P ν c

theorem interior_patch_open (P : RawFacePairing T) (ν : Vertex P) (c : T × Fin 4) :
    IsOpen (InteriorPatch P ν c) := by
  have hI : IsOpen {x : Point P ν | Interior P x} := by
    have he : {x : Point P ν | Interior P x} =
        ⋂ f : Fin 4, ({x | x.val.1.2 = f} ∪ {x | x.val.2 f ≠ 0}) := by
      ext x
      simp only [Set.mem_setOf_eq,Set.mem_iInter,Set.mem_union]
      constructor
      · intro hx f
        by_cases hf : f = x.val.1.2
        · exact Or.inl hf.symm
        · exact Or.inr (hx f hf)
      · intro hx f hf
        rcases hx f with h | h
        · exact False.elim (hf h.symm)
        · exact h
    rw [he]
    apply isOpen_iInter_of_finite
    intro f
    apply IsOpen.union
    · exact (isOpen_discrete {c : T × Fin 4 | c.2 = f}).preimage
        (continuous_fst.comp continuous_subtype_val)
    · exact isOpen_ne_fun
        ((continuous_apply f).comp (continuous_snd.comp continuous_subtype_val))
        continuous_const
  exact ((isOpen_discrete {a : T × Fin 4 | a = c}).preimage
    (continuous_fst.comp continuous_subtype_val)).inter hI

theorem actual_open_interior_quotient (P : RawFacePairing T) (ν : Vertex P)
    (c : T × Fin 4) :
    ((@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν)))) ⁻¹'
        quotientInteriorPatch P ν c = InteriorPatch P ν c) ∧
    IsOpen (quotientInteriorPatch P ν c) := by
  have hs : (@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν)))) ⁻¹'
      quotientInteriorPatch P ν c = InteriorPatch P ν c := by
    ext y
    constructor
    · rintro ⟨z,hz,he⟩
      have hy : y = z := (interior_normal_form P z y hz.2).mp (Quotient.exact he)
      simpa only [hy] using hz
    · intro hy
      exact ⟨y,hy,rfl⟩
  refine ⟨hs,?_⟩
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  rw [hs]
  exact interior_patch_open P ν c

def originalInteriorPatchHomeomorph (P : RawFacePairing T) (ν : Vertex P)
    (c : T × Fin 4) :
    ↥(InteriorPatch P ν c) ≃ₜ ↥(quotientInteriorPatch P ν c) := by
  let q : Point P ν → PointQuotient P ν :=
    @Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν)))
  let U := quotientInteriorPatch P ν c
  have hs := (actual_open_interior_quotient P ν c).1
  have ho := (actual_open_interior_quotient P ν c).2
  let e : ↥(InteriorPatch P ν c) ≃ₜ ↥(q ⁻¹' U) := Homeomorph.setCongr hs.symm
  let f : ↥(InteriorPatch P ν c) → ↥U := U.restrictPreimage q ∘ e
  have hq : IsQuotientMap f :=
    (isQuotientMap_quotient_mk'.restrictPreimage_isOpen ho).comp e.isQuotientMap
  have hf : Function.Injective f := by
    intro a b hab
    have heq : q a.val = q b.val := congrArg Subtype.val hab
    have hb : b.val = a.val :=
      (interior_normal_form P a.val b.val a.property.2).mp (Quotient.exact heq)
    exact Subtype.ext hb.symm
  exact (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hq,hf⟩).homeomorph f

end D5.S3.Geometry.Gluing.RawFaceInteriorTopology1460Candidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceInteriorTopology1460Candidate.interior_patch_open,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorTopology1460Candidate.actual_open_interior_quotient,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorTopology1460Candidate.originalInteriorPatchHomeomorph] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1460 missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1460 disallowed {ax}"
    Lean.logInfo m!"CFMP1460 CHECKED {name} axioms={axioms}"
