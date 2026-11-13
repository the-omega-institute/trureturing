/- GID: D5/S3/FiniteGroups/Frobenius/FiniteIsotypicImageSimple
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Frobenius/FiniteIsotypicImageSimple
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Simplicity of the actual algebra image on a finite isotypic semisimple module. -/

import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix

/- The bridge constructs a bijection from the bicommutant onto the actual
   action range. The two matrix arguments below are direct library applications.
   No hypothesis asserts image simplicity or an unproved equivalence. -/

namespace FiniteIsotypicImage

universe u v w

theorem isSimpleRing_actionRange
    {k : Type u} {R : Type v} {U : Type w}
    [Field k] [Ring R] [Algebra k R]
    [AddCommGroup U] [Module k U] [Module R U] [IsScalarTower k R U]
    [Module.Finite k U] [Nontrivial U] [IsSemisimpleModule R U]
    (hU : IsIsotypic R U) :
    IsSimpleRing (Algebra.lsmul k k U (A := R)).range := by
  classical
  letI : Module.Finite R U := Module.Finite.of_restrictScalars_finite k R U
  let E := Module.End R U
  letI : Module.Finite E U := Module.Finite.of_restrictScalars_finite k E U
  letI : IsSimpleRing E := by
    change IsSimpleRing (Module.End R U)
    obtain ⟨n, hn, S, hS, ⟨e⟩⟩ := hU.linearEquiv_fun
    letI : NeZero n := hn
    letI : IsSimpleModule R S := hS
    exact IsSimpleRing.of_ringEquiv
      (e.conjRingEquiv.trans (endVecRingEquivMatrixEnd (Fin n) R S)).symm
      inferInstance
  letI : IsSemisimpleRing E :=
    IsSemisimpleRing.moduleEnd (R := R) (M := U)
  letI : IsArtinianRing E := inferInstance
  letI : IsSemisimpleModule E U := inferInstance
  let B := Module.End E U
  letI : IsSimpleRing B := by
    change IsSimpleRing (Module.End E U)
    obtain ⟨n, hn, S, hS, ⟨e⟩⟩ := (IsSimpleRing.isIsotypic E U).linearEquiv_fun
    letI : NeZero n := hn
    letI : IsSimpleModule E S := hS
    exact IsSimpleRing.of_ringEquiv
      (e.conjRingEquiv.trans (endVecRingEquivMatrixEnd (Fin n) E S)).symm
      inferInstance
  let φ : R →ₐ[k] Module.End k U := Algebra.lsmul k k U
  let ψ : R →+* B := Module.toModuleEnd E (S := R) U
  have hψ : Function.Surjective ψ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := R) (M := U)
  let f : B →+* φ.range :=
    { toFun := fun b =>
        ⟨b.restrictScalars k, by
          obtain ⟨r, hr⟩ := hψ b
          refine ⟨r, LinearMap.ext fun x => ?_⟩
          exact LinearMap.congr_fun hr x⟩
      map_one' := Subtype.ext (LinearMap.ext fun _ => rfl)
      map_mul' := fun _ _ => Subtype.ext (LinearMap.ext fun _ => rfl)
      map_zero' := Subtype.ext (LinearMap.ext fun _ => rfl)
      map_add' := fun _ _ => Subtype.ext (LinearMap.ext fun _ => rfl) }
  have hf_inj : Function.Injective f := by
    intro b c h
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (congrArg Subtype.val h) x
  have hf_surj : Function.Surjective f := by
    intro a
    obtain ⟨r, hr⟩ := a.property
    refine ⟨ψ r, Subtype.ext (LinearMap.ext fun x => ?_)⟩
    exact LinearMap.congr_fun hr x
  exact IsSimpleRing.of_ringEquiv
    (RingEquiv.ofBijective f ⟨hf_inj, hf_surj⟩) inferInstance

end FiniteIsotypicImage
