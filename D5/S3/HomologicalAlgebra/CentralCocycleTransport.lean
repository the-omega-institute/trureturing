/- GID: D5/S3/HomologicalAlgebra/CentralCocycleTransport
   generality: I
   mirror-B: D5/B/S3/HomologicalAlgebra/CentralCocycleTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree]
   utility: none
   digest: Inflated cocycles give an explicit linearization at central elements killed in the quotient. -/

import D5.S3.HomologicalAlgebra.InflatedCubicCandidate
import Mathlib.Algebra.Module.Torsion.Free

/-! For a central element in the kernel of a quotient, the slant multiplier
of an inflated third cocycle vanishes. A change of third-cocycle gauge
provides an explicit scalar correction of the projective action. -/

set_option autoImplicit false

namespace D5.S3.HomologicalAlgebra.CentralCocycleTransport

open InflatedCubicCandidate (d₂ d₃ Normalized)

variable {G H M : Type*} [Group G] [Group H] [AddCommGroup M]

/-- The centralizer multiplier in the convention
`T a * T b = exp(slant z ω a b) • T (a*b)`. -/
def slant (z : G) (ω : G → G → G → M) (a b : G) : M :=
  ω z a b + ω a b z - ω a z b

/-- The two-cochain gauge induces a one-cochain on the centralizer. -/
def gauge (z : G) (B : G → G → M) (a : G) : M := B a z - B z a

/-- The slant of a third cocycle at a central element is a two-cocycle. -/
theorem slant_d₂_zero (z : G) (hz : ∀ a, z * a = a * z) (ω : G → G → G → M)
    (hω : ∀ a b c d, d₃ ω a b c d = 0) (a b c : G) :
    d₂ (slant z ω) a b c = 0 := by
  have h1 := hω z a b c
  have h2 := hω a z b c
  have h3 := hω a b z c
  have h4 := hω a b c z
  simp only [d₃, hz] at h1 h2 h3 h4
  simp only [d₂, slant]
  linear_combination (norm := abel) -h1 + h2 - h3 + h4

/-- The slant of a coboundary gives the coboundary of its induced gauge. -/
theorem slant_coboundary (z : G) (hz : ∀ a, z * a = a * z)
    (B : G → G → M) (a b : G) :
    slant z (d₂ B) a b = gauge z B a + gauge z B b - gauge z B (a * b) := by
  simp only [slant, d₂, gauge, hz]
  abel

/-- For a normalized cocycle lifted from the quotient, the slant at a
central element mapping to the identity is exactly the gauge coboundary. -/
theorem slant_of_inflation_with_gauge (p : G →* H) (z : G)
    (hz : ∀ a, z * a = a * z) (hp : p z = 1)
    (ω : G → G → G → M) (f : H → H → H → M) (hf : Normalized f)
    (B : G → G → M)
    (hω : ∀ a b c, ω a b c = f (p a) (p b) (p c) + d₂ B a b c)
    (a b : G) :
    slant z ω a b = gauge z B a + gauge z B b - gauge z B (a * b) := by
  unfold slant
  rw [hω, hω, hω, hp, (hf (p a) (p b)).1,
    (hf (p a) (p b)).2.2, (hf (p a) (p b)).2.1]
  simpa only [zero_add, slant] using slant_coboundary z hz B a b

/-- Correcting a projective action by the two-cochain gauge gives a linear
action on the same module whenever the anomaly is inflated and its grading
element is central and trivial in the quotient. -/
noncomputable def linearizedAction {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : G →* H) (z : G) (hz : ∀ a, z * a = a * z) (hp : p z = 1)
    (ω : G → G → G → M) (hωnorm : Normalized ω)
    (f : H → H → H → M) (hf : Normalized f) (B : G → G → M)
    (hω : ∀ a b c, ω a b c = f (p a) (p b) (p c) + d₂ B a b c)
    (phase : Multiplicative M →* ℂˣ) (T : G → Module.End ℂ V) (h₁ : T 1 = 1)
    (hmul : ∀ a b, T a * T b =
      (phase (Multiplicative.ofAdd (slant z ω a b)) : ℂ) • T (a * b)) :
    G →* Module.End ℂ V where
  toFun a := (phase (Multiplicative.ofAdd (-gauge z B a)) : ℂ) • T a
  map_one' := by
    have h := slant_of_inflation_with_gauge p z hz hp ω f hf B hω 1 1
    have hzero : slant z ω 1 1 = 0 := by
      simp [slant, (hωnorm z 1).2.2, (hωnorm 1 z).1, (hωnorm z 1).1]
    rw [hzero, mul_one, add_sub_cancel_right] at h
    simp [← h, h₁]
  map_mul' a b := by
    rw [smul_mul_assoc, mul_smul_comm, hmul, smul_smul, smul_smul]
    simp only [← Units.val_mul, ← map_mul]
    congr 3
    change -gauge z B (a * b) = -gauge z B a + -gauge z B b + slant z ω a b
    rw [slant_of_inflation_with_gauge p z hz hp ω f hf B hω]
    abel

/-- Scalar differences between two genuine linearizations form one global
character. This constrains the rephasings on different cyclic subgroups. -/
theorem character_of_scalar_difference {V : Type*} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (T A : G →* Module.End ℂ V) (u : G → ℂˣ)
    (hscale : ∀ g, A g = (u g : ℂ) • T g) :
    ∃ χ : G →* ℂˣ, ∀ g, A g = (χ g : ℂ) • T g := by
  have hnonzero (g : G) : T g ≠ 0 := by
    intro h
    have hunit := T.map_mul g g⁻¹
    rw [mul_inv_cancel, map_one, h, zero_mul] at hunit
    exact one_ne_zero hunit
  let χ : G →* ℂˣ :=
    { toFun := u
      map_one' := by
        apply Units.ext
        apply smul_left_injective ℂ (hnonzero (1 : G))
        change (u 1 : ℂ) • T 1 = (1 : ℂ) • T 1
        rw [← hscale 1, one_smul, A.map_one, T.map_one]
      map_mul' := by
        intro g h
        apply Units.ext
        apply smul_left_injective ℂ (hnonzero (g * h))
        calc
          (u (g * h) : ℂ) • T (g * h) = A (g * h) := (hscale _).symm
          _ = A g * A h := A.map_mul _ _
          _ = ((u g * u h : ℂˣ) : ℂ) • T (g * h) := by
            rw [hscale g, hscale h, smul_mul_assoc, mul_smul_comm,
              smul_smul, Units.val_mul, T.map_mul] }
  exact ⟨χ, hscale⟩

#print axioms slant_d₂_zero
#print axioms linearizedAction
#print axioms character_of_scalar_difference

end D5.S3.HomologicalAlgebra.CentralCocycleTransport
