/- GID: D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Presentation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourVacuumC2Presentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Truncated polynomial presentation of the actual norm-four vacuum C2 algebra. -/

import D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Algebra
import D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Exact
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Batteries.Tactic.OpenPrivate

/-! The actual norm-four vacuum C2 algebra is the complex truncated polynomial algebra. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Presentation

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeActualStateFieldCalculus
open NormFourVirasoroVector NormFourVacuumIrreducible NormFourVacuumC2
open NormFourVacuumC2Exact NormFourVacuumC2Algebra
open scoped BigOperators VertexOperator

open private vector_mem full_field_closed
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra
open private all_modes_closed
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible
open private vacuum_mem c2_le cube_mem_c2 representatives representatives_mem
  small small_le three_spanning
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2
open private QuotientSpace unitClass
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Algebra

noncomputable section

/-- An algebra isomorphism from the truncated polynomial algebra
onto the literal actual C2 quotient, sending X to the actual axis class.
The map is built from actual -1 multiplication and the level-six relation;
its surjectivity uses actual negative-word reduction and its injectivity
uses the actual low-weight separator theorem. -/
theorem actual_vacuum_c2_presentation (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    let S := vacuumDescendants D a s
    let C := (C2 D a s).comap S.subtype
    letI := quotientRing D a ha s hs
    letI := quotientAlgebra D a ha s hs
    ∃ E : AdjoinRoot (Polynomial.X^3 : Polynomial ℂ) ≃ₐ[ℂ] (S ⧸ C),
      E (AdjoinRoot.root (Polynomial.X^3 : Polynomial ℂ)) =
        C.mkQ ⟨vector D a s,vector_mem D a ha s hs⟩ := by
  classical
  let S := vacuumDescendants D a s
  let C := (C2 D a s).comap S.subtype
  let Q := S ⧸ C
  letI := quotientRing D a ha s hs
  letI := quotientAlgebra D a ha s hs
  let q : S →ₗ[ℂ] Q := C.mkQ
  let L := mode D a s (-2)
  let v : S := ⟨vector D a s,vector_mem D a ha s hs⟩
  let x : Q := q v
  let r : ℕ → S := fun n =>
    Nat.rec ⟨vacuum D,vacuum_mem D a s⟩
      (fun _ u => ⟨L u.val,all_modes_closed D a ha s hs (-2) u.val u.property⟩) n
  have r_val (n : ℕ) : (r n).val = (L^n) (vacuum D) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        change L (r n).val = (L^(n+1)) (vacuum D)
        rw [ih,pow_succ',Module.End.mul_apply]
  have quotient_step (u : S) :
      q ⟨L u.val,all_modes_closed D a ha s hs (-2) u.val u.property⟩ = x * q u := by
    change q ⟨mu D v.val (-1) u.val,
      full_field_closed D a ha s hs v.val v.property (-1) u.val u.property⟩ = _
    exact (actual_vacuum_c2_algebra D a ha s hs).1 v u
  have quotient_powers (n : ℕ) : q (r n) = x^n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        change q ⟨L (r n).val,
          all_modes_closed D a ha s hs (-2) (r n).val (r n).property⟩ = _
        rw [quotient_step,ih,pow_succ']
  have cubic : x^3 = 0 := by
    rw [← quotient_powers 3]
    apply (Submodule.Quotient.mk_eq_zero C).mpr
    change (r 3).val ∈ C2 D a s
    rw [r_val]
    simpa only [pow_succ',pow_zero,Module.End.mul_apply,Module.End.one_apply] using
      cube_mem_c2 D a ha s hs
  let f : Polynomial ℂ := Polynomial.X^3
  let F : AdjoinRoot f →ₐ[ℂ] Q :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId ℂ Q) x (by simpa [f] using cubic)
  have root_image : F (AdjoinRoot.root f) = x := by simp [F]
  let R : Submodule ℂ Q := F.toLinearMap.range
  have rep_range (i : Fin 3) :
      q ⟨representatives D a s i,representatives_mem D a ha s hs i⟩ ∈ R := by
    have equal : (⟨representatives D a s i,
        representatives_mem D a ha s hs i⟩ : S) = r i.val := by
      apply Subtype.ext
      exact (r_val i.val).symm
    rw [equal,quotient_powers]
    exact LinearMap.mem_range.mpr ⟨(AdjoinRoot.root f)^i.val,by
      change F ((AdjoinRoot.root f)^i.val) = x^i.val
      rw [map_pow,root_image]⟩
  have small_range_aux : small D a s ≤ (R.comap q).map S.subtype := by
    apply Submodule.span_le.mpr
    rintro z ⟨i,rfl⟩
    exact Submodule.mem_map.mpr
      ⟨⟨representatives D a s i,representatives_mem D a ha s hs i⟩,rep_range i,rfl⟩
  have small_range (z : Carrier D) (hz : z ∈ small D a s) :
      q ⟨z,small_le D a ha s hs hz⟩ ∈ R := by
    obtain ⟨w,hw,he⟩ := Submodule.mem_map.mp (small_range_aux hz)
    have equal : w = ⟨z,small_le D a ha s hs hz⟩ := Subtype.ext he
    exact equal ▸ hw
  have surjective : Function.Surjective F := by
    intro y
    obtain ⟨u,rfl⟩ := C.mkQ_surjective y
    obtain ⟨z,hz,w,hw,he⟩ := Submodule.mem_sup.mp
      (three_spanning D a ha s hs u.property)
    have vanish : q ⟨z,c2_le D a ha s hs hz⟩ = 0 :=
      (Submodule.Quotient.mk_eq_zero C).mpr hz
    have equal : (⟨z,c2_le D a ha s hs hz⟩ : S) +
        ⟨w,small_le D a ha s hs hw⟩ = u := Subtype.ext he
    change q u ∈ R
    rw [← equal,map_add,vanish,zero_add]
    exact small_range w hw
  obtain ⟨finite,dimension⟩ := (actual_vacuum_c2_algebra D a ha s hs).2.2
  letI : FiniteDimensional ℂ Q := finite
  letI : FiniteDimensional ℂ (AdjoinRoot f) :=
    (Polynomial.monic_X.pow 3).finite_adjoinRoot
  have domain_dimension : Module.finrank ℂ (AdjoinRoot f) = 3 := by
    change Module.finrank ℂ (Polynomial ℂ ⧸ Ideal.span {f}) = 3
    rw [finrank_quotient_span_eq_natDegree]
    simp [f]
  have injective : Function.Injective F :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := F.toLinearMap) (domain_dimension.trans dimension.symm)).mpr surjective
  refine ⟨AlgEquiv.ofBijective F ⟨injective,surjective⟩,?_⟩
  change F (AdjoinRoot.root f) = x
  exact root_image

end
end D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Presentation
