import D5.S3.Geometry.Gluing.RelativeDeformationRetract
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Piecewise

noncomputable section

open scoped ContinuousMap unitInterval
open ContinuousMap Set
open D5.S3.Geometry.FiniteConeCollapse (realization realization_mem_iff)
open D5.S3.Geometry.FiniteConeUnionWedge
  (realization_closed realization_intersection realizationInclusion)
open D5.S3.Geometry.FiniteSubcomplexCylinder (Space Subspace)
open D5.S3.Geometry.RelativeDeformationRetract (strongDeformationRetract_of_homotopyEquiv)

namespace D5.S3.Geometry.FiniteSubcomplexDeformationGlue

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A deformation of one half of a finite subcomplex union, fixed on the overlap,
extends by the identity on the other half. If its endpoint lands in the overlap,
then the union deformation retracts onto the second half. -/
theorem deformationRetract_union (A B : PreAbstractSimplicialComplex V)
    (r : C(Space A, Space (A ⊓ B)))
    (h : (ContinuousMap.id (Space A)).HomotopicRel
      ((realizationInclusion inf_le_left).comp r) (Subspace A (A ⊓ B))) :
    ∃ p : C(Space (A ⊔ B), Space B),
      p.comp (realizationInclusion le_sup_right) = ContinuousMap.id (Space B) ∧
      (ContinuousMap.id (Space (A ⊔ B))).HomotopicRel
        ((realizationInclusion le_sup_right).comp p) (Subspace (A ⊔ B) B) := by
  classical
  obtain ⟨H⟩ := h
  let T := A ⊔ B
  let iA : C(Space A, Space T) := realizationInclusion le_sup_left
  let iB : C(Space B, Space T) := realizationInclusion le_sup_right
  let U : Set (I × Space T) := {z | z.2.val ∈ realization A}
  let W : Set (I × Space T) := {z | z.2.val ∈ realization B}
  have hU : IsClosed U :=
    (realization_closed A).preimage (continuous_subtype_val.comp continuous_snd)
  have hW : IsClosed W :=
    (realization_closed B).preimage (continuous_subtype_val.comp continuous_snd)
  have cover (x : Space T) : x.val ∈ realization A ∨ x.val ∈ realization B := by
    obtain ⟨s, hs, hx⟩ := (realization_mem_iff T x.val).mp x.property
    change s ∈ A ∨ s ∈ B at hs
    exact hs.imp (fun ha => (realization_mem_iff A x.val).mpr ⟨s, ha, hx⟩)
      (fun hb => (realization_mem_iff B x.val).mpr ⟨s, hb, hx⟩)
  let F (z : I × Space T) : Space T :=
    if hz : z ∈ U then iA (H (z.1, ⟨z.2.val, hz⟩)) else z.2
  have fixed (z : I × Space T) (hz : z ∈ W) : F z = z.2 := by
    by_cases ha : z ∈ U
    · simp only [F, dite_eq_left ha]
      have overlap : (⟨z.2.val, ha⟩ : Space A) ∈ Subspace A (A ⊓ B) := by
        change z.2.val ∈ realization (A ⊓ B)
        rw [realization_intersection]
        exact ⟨ha, hz⟩
      rw [H.eq_fst z.1 overlap]
      exact Subtype.ext rfl
    · simp [F, ha]
  have hFU : ContinuousOn F U := by
    rw [continuousOn_iff_continuous_domRestrict]
    let toA : U → Space A := fun z => ⟨z.val.2.val, z.property⟩
    have htoA : Continuous toA :=
      ((continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val).subtype_mk _
    have hpair : Continuous (fun z : U => (z.val.1, toA z)) :=
      (continuous_fst.comp continuous_subtype_val).prodMk htoA
    have eq : U.domRestrict F = fun z => iA (H (z.val.1, toA z)) := by
      funext z
      exact dite_eq_left z.property
    rw [eq]
    exact iA.continuous.comp (H.toHomotopy.continuous.comp hpair)
  have hFUc : closure Uᶜ ⊆ W :=
    closure_minimal (fun z hz => (cover z.2).resolve_left hz) hW
  have hF : Continuous F := by
    have hp : Continuous (U.piecewise F Prod.snd) := by
      apply continuous_piecewise
      · intro z hz
        have hz' : z ∈ closure Uᶜ := by
          rw [frontier_eq_closure_inter_closure] at hz
          exact hz.2
        exact fixed z (hFUc hz')
      · simpa only [hU.closure_eq] using hFU
      · exact continuous_snd.continuousOn
    convert hp using 1
    funext z
    by_cases hz : z ∈ U
    · simp [hz]
    · simp [F, hz]
  have end_mem (x : Space T) : (F (1, x)).val ∈ realization B := by
    by_cases hx : (1, x) ∈ U
    · simp only [F, dite_eq_left hx, H.apply_one]
      have hr := (r ⟨x.val, hx⟩).property
      exact ((Set.ext_iff.mp (realization_intersection A B) _).mp hr).2
    · simp only [F, dite_eq_right hx]
      exact (cover x).resolve_left hx
  let p : C(Space T, Space B) :=
    ⟨fun x => ⟨(F (1, x)).val, end_mem x⟩,
      (continuous_subtype_val.comp (hF.comp (continuous_const.prodMk continuous_id))).subtype_mk _⟩
  refine ⟨p, ContinuousMap.ext (fun x => ?_), ⟨?_⟩⟩
  · apply Subtype.ext
    change (F (1, iB x)).val = x.val
    exact congrArg (fun y : Space T => y.val) (fixed (1, iB x) x.property)
  · refine
      { toHomotopy :=
          { toFun := F
            continuous_toFun := hF
            map_zero_left := fun x => ?_
            map_one_left := fun x => Subtype.ext rfl }
        prop' := fun t x hx => fixed (t, x) hx }
    by_cases hx : (0, x) ∈ U
    · simp only [F, dite_eq_left hx, H.apply_zero]
      exact Subtype.ext rfl
    · simp [F, hx]

/-- The realization of a finite subcomplex union is contractible if its second
half is contractible and the overlap includes into the first by a homotopy
equivalence. -/
theorem contractible_union (A B : PreAbstractSimplicialComplex V)
    (e : Space (A ⊓ B) ≃ₕ Space A)
    (he : e.toFun = realizationInclusion inf_le_left)
    [ContractibleSpace (Space B)] : ContractibleSpace (Space (A ⊔ B)) := by
  obtain ⟨r, _, h⟩ := strongDeformationRetract_of_homotopyEquiv inf_le_left e he
  obtain ⟨p, hp, H⟩ := deformationRetract_union A B r h
  let i : C(Space B, Space (A ⊔ B)) := realizationInclusion le_sup_right
  exact (show Space (A ⊔ B) ≃ₕ Space B from
    { toFun := p
      invFun := i
      left_inv := H.homotopic.symm
      right_inv := hp ▸ Homotopic.refl (ContinuousMap.id (Space B)) }).contractibleSpace

end D5.S3.Geometry.FiniteSubcomplexDeformationGlue
