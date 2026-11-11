/- GID: D5/S3/FiniteGroups/GroupAlgebra/ProjectiveConjugationTrace
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/ProjectiveConjugationTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Maschke, mathlib/module/Mathlib.Algebra.Module.Projective]
   utility: none
   digest: A finite-group module is projective exactly when its coefficient module is projective and an ordinary endomorphism has conjugation trace one. -/

import D5.S3.FiniteGroups.GroupAlgebra.PGroupProjectiveNormRing
import Mathlib.RepresentationTheory.Maschke

/-!
The finite-group projectivity criterion over an arbitrary commutative ring.
The ring, group and module have independent universes. Zero rings, zero
modules, trivial groups and arbitrarily generated modules remain in scope.
Endomorphism composition is not assumed commutative. No group-order inverse,
characteristic, p-group or nilpotence hypothesis is used.

The coefficient-projectivity argument and actual orbit-cover section are
reused from PGroupProjectiveNormRing at their original source location.
The converse uses the unnormalised, CommRing-generic
LinearMap.sumOfConjugatesEquivariant, not equivariantProjection.

This reconstructs the classical projectivity/trace-one criterion. The
supplied attribution is Aljadeff--Ginosar (1996), Lemma 4, and
Aljadeff--Kassel, https://arxiv.org/abs/math/0012038. No literature novelty
or independent bibliographic verification is claimed here.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.GroupAlgebra.ProjectiveConjugationTrace

open scoped MonoidAlgebra
open D5.S3.FiniteGroups.GroupAlgebra.PGroupProjectiveNormRing

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [Fintype G] [AddCommGroup V] [Module R V]

-- Mathlib averages g⁻¹ ∘ t ∘ g. Inversion reindexes this to the displayed
-- g ∘ t ∘ g⁻¹ convention without interchanging any factors.
private theorem sum_inverse_conjugates (ρ : Representation R G V) (t : Module.End R V) :
    (∑ g : G, (ρ g⁻¹).comp (t.comp (ρ g))) =
      ∑ g : G, (ρ g).comp (t.comp (ρ g⁻¹)) := by
  classical
  refine Fintype.sum_bijective (fun g : G => g⁻¹) inv_bijective _ _ ?_
  intro g
  rw [inv_inv]

/-- For a finite group acting on an arbitrary module over a commutative ring,
group-algebra projectivity is equivalent to coefficient projectivity together
with an R-linear endomorphism of conjugation trace one. The group need not
be commutative and the module need not be finitely generated. -/
theorem projective_iff_projective_and_conjugation_trace_one (ρ : Representation R G V) :
    Module.Projective R[G] ρ.asModule ↔
      Module.Projective R V ∧
        ∃ t : Module.End R V,
          (∑ g : G, (ρ g).comp (t.comp (ρ g⁻¹))) = LinearMap.id := by
  classical
  constructor
  · intro hproj
    letI : Module.Projective R[G] ρ.asModule := hproj
    have hR : Module.Projective R V := coefficient_projective_of_projective ρ
    obtain ⟨S, hqS⟩ := orbit_section_of_projective ρ
    let t : Module.End R V :=
      { toFun := fun v => S v 1
        map_add' := by
          intro v w
          exact congrFun (map_add S v w) (1 : G)
        map_smul' := by
          intro r v
          exact congrFun (map_smul S r v) (1 : G) }
    have ht (g : G) (v : V) : t (ρ g v) = S v g := by
      change S (ρ g v) 1 = S v g
      have he := congrFun
        (Representation.IntertwiningMap.isIntertwining ρ
          (rightTranslate (R := R) (P := G) (W := V)) S g v) (1 : G)
      change S (ρ g v) 1 = S v (1 * g) at he
      simpa only [one_mul] using he
    have hinverse :
        (∑ g : G, (ρ g⁻¹).comp (t.comp (ρ g))) = LinearMap.id := by
      apply LinearMap.ext
      intro v
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
      calc
        (∑ g : G, ρ g⁻¹ (t (ρ g v))) = ∑ g : G, ρ g⁻¹ (S v g) := by
          apply Finset.sum_congr rfl
          intro g _
          rw [ht]
        _ = ∑ g : G, ρ g (S v g⁻¹) := by
          refine Fintype.sum_bijective (fun g : G => g⁻¹) inv_bijective _ _ ?_
          intro g
          rw [inv_inv]
        _ = v := hqS v
    exact ⟨hR, t, (sum_inverse_conjugates ρ t).symm.trans hinverse⟩
  · rintro ⟨hR, t, ht⟩
    letI : Module.Projective R V := hR
    have htrace (v : V) : (∑ g : G, ρ g⁻¹ (t (ρ g v))) = v := by
      have he := LinearMap.congr_fun ((sum_inverse_conjugates ρ t).trans ht) v
      simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] using he
    have hsingle (g : G) (v : ρ.asModule) :
        ρ.asModuleEquiv (MonoidAlgebra.single g (1 : R) • v) = ρ g (ρ.asModuleEquiv v) := by
      rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single_one]
    apply Module.Projective.of_lifting_property''
    intro f hf
    let X := ρ.asModule →₀ R[G]
    letI : IsScalarTower R R[G] ρ.asModule := inferInstance
    letI : IsScalarTower R R[G] X := inferInstance
    letI : LinearMap.CompatibleSMul X ρ.asModule R R[G] :=
      LinearMap.IsScalarTower.compatibleSMul
        (M := X) (M₂ := ρ.asModule) (R := R) (S := R[G])
    obtain ⟨s, hs⟩ := Module.projective_lifting_property (f.restrictScalars R)
      ρ.asModuleEquiv.symm.toLinearMap hf
    have hs_apply (v : V) : f (s v) = ρ.asModuleEquiv.symm v :=
      LinearMap.congr_fun hs v
    let π : ρ.asModule →ₗ[R] X := s.comp (t.comp ρ.asModuleEquiv.toLinearMap)
    refine ⟨π.sumOfConjugatesEquivariant G, ?_⟩
    apply LinearMap.ext
    intro v
    apply ρ.asModuleEquiv.injective
    change ρ.asModuleEquiv (f (π.sumOfConjugatesEquivariant G v)) = ρ.asModuleEquiv v
    calc
      ρ.asModuleEquiv (f (π.sumOfConjugatesEquivariant G v)) =
          ∑ g : G, ρ.asModuleEquiv (f (π.conjugate g v)) := by
        rw [LinearMap.sumOfConjugatesEquivariant_apply, map_sum, map_sum]
      _ = ∑ g : G, ρ g⁻¹ (t (ρ g (ρ.asModuleEquiv v))) := by
        apply Finset.sum_congr rfl
        intro g _
        rw [LinearMap.conjugate_apply]
        change ρ.asModuleEquiv
            (f (MonoidAlgebra.single g⁻¹ (1 : R) •
              s (t (ρ.asModuleEquiv (MonoidAlgebra.single g (1 : R) • v))))) =
          ρ g⁻¹ (t (ρ g (ρ.asModuleEquiv v)))
        rw [f.map_smul, hs_apply, hsingle, LinearEquiv.apply_symm_apply, hsingle]
      _ = ρ.asModuleEquiv v := htrace (ρ.asModuleEquiv v)

end D5.S3.FiniteGroups.GroupAlgebra.ProjectiveConjugationTrace
