/- GID: D5/S3/Geometry/MostowPrasadDescent
   generality: G
   mirror-B: D5/B/S3/Geometry/MostowPrasadDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conjugate isometric actions descend to an equivalence of orbit quotients. -/

import D5.S3.Geometry.MostowPrasadRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.MostowPrasadDescent

open D5.S3.Geometry.MostowPrasadRigidity

section OrbitQuotients

variable {G H X : Type*} [Group G] [Group H] [MetricSpace X]

/-- The orbit relation induced by an isometric representation. -/
def orbitSetoid (ρ : G →* (X ≃ᵢ X)) : Setoid X where
  r x y := ∃ g : G, ρ g x = y
  iseqv := by
    constructor
    · intro x
      exact ⟨1, by simp⟩
    · intro x y hxy
      rcases hxy with ⟨g, hxy⟩
      refine ⟨g⁻¹, ?_⟩
      calc
        ρ g⁻¹ y = ρ g⁻¹ (ρ g x) := by rw [hxy]
        _ = ρ (g⁻¹ * g) x := by
          rw [map_mul, IsometryEquiv.mul_apply]
        _ = x := by simp
    · intro x y z hxy hyz
      rcases hxy with ⟨g, hxy⟩
      rcases hyz with ⟨h, hyz⟩
      refine ⟨h * g, ?_⟩
      calc
        ρ (h * g) x = ρ h (ρ g x) := by
          rw [map_mul, IsometryEquiv.mul_apply]
        _ = ρ h y := by rw [hxy]
        _ = z := hyz

/-- The set-theoretic quotient by the representation orbit relation. -/
abbrev OrbitQuotient (ρ : G →* (X ≃ᵢ X)) : Type _ :=
  Quotient (orbitSetoid ρ)

/-- The canonical projection to an orbit quotient. -/
def orbitQuotientMk (ρ : G →* (X ≃ᵢ X)) : X → OrbitQuotient ρ :=
  fun x => Quotient.mk (orbitSetoid ρ) x

theorem orbitQuotientMk_eq_of_orbit
    (ρ : G →* (X ≃ᵢ X)) {x y : X}
    (hxy : ∃ g : G, ρ g x = y) :
    orbitQuotientMk ρ x = orbitQuotientMk ρ y := by
  exact Quotient.sound hxy

end OrbitQuotients

section ConjugacyDescent

variable {G H X : Type*} [Group G] [Group H] [MetricSpace X]

/-- A chosen conjugator transports one isometric representation to another. -/
def IsometricGroupConjugacy
    (e : G ≃* H) (ρ : G →* (X ≃ᵢ X)) (σ : H →* (X ≃ᵢ X))
    (a : X ≃ᵢ X) : Prop :=
  ∀ g : G, σ (e g) = a * ρ g * a⁻¹

private theorem conjugator_maps_orbits
    (e : G ≃* H) (ρ : G →* (X ≃ᵢ X)) (σ : H →* (X ≃ᵢ X))
    (a : X ≃ᵢ X) (hconj : IsometricGroupConjugacy e ρ σ a)
    {x y : X} (hxy : ∃ g : G, ρ g x = y) :
    ∃ h : H, σ h (a x) = a y := by
  rcases hxy with ⟨g, hxy⟩
  refine ⟨e g, ?_⟩
  rw [hconj g]
  simp [IsometryEquiv.mul_apply, hxy, mul_assoc]

private theorem inverse_conjugacy
    (e : G ≃* H) (ρ : G →* (X ≃ᵢ X)) (σ : H →* (X ≃ᵢ X))
    (a : X ≃ᵢ X) (hconj : IsometricGroupConjugacy e ρ σ a) :
    ∀ h : H, ρ (e.symm h) = a⁻¹ * σ h * a := by
  intro h
  obtain ⟨g, rfl⟩ := e.surjective h
  rw [hconj g]
  simp [mul_assoc]

private theorem inverse_conjugator_maps_orbits
    (e : G ≃* H) (ρ : G →* (X ≃ᵢ X)) (σ : H →* (X ≃ᵢ X))
    (a : X ≃ᵢ X) (hconj : IsometricGroupConjugacy e ρ σ a)
    {x y : X} (hxy : ∃ h : H, σ h x = y) :
    ∃ g : G, ρ g (a⁻¹ x) = a⁻¹ y := by
  rcases hxy with ⟨h, hxy⟩
  refine ⟨e.symm h, ?_⟩
  rw [inverse_conjugacy e ρ σ a hconj]
  simp [IsometryEquiv.mul_apply, hxy, mul_assoc]

/-- The conjugator descends to a map between the two orbit quotients. -/
noncomputable def descendedMap
    (e : G ≃* H) (ρ : G →* (X ≃ᵢ X)) (σ : H →* (X ≃ᵢ X))
  (a : X ≃ᵢ X) (hconj : IsometricGroupConjugacy e ρ σ a) :
    OrbitQuotient ρ → OrbitQuotient σ :=
  Quotient.lift (fun x => orbitQuotientMk σ (a x))
    (fun _ _ hxy => orbitQuotientMk_eq_of_orbit σ
      (conjugator_maps_orbits e ρ σ a hconj hxy))

/-- The inverse conjugator descends to the reverse orbit quotient. -/
noncomputable def descendedInverse
    (e : G ≃* H) (ρ : G →* (X ≃ᵢ X)) (σ : H →* (X ≃ᵢ X))
  (a : X ≃ᵢ X) (hconj : IsometricGroupConjugacy e ρ σ a) :
    OrbitQuotient σ → OrbitQuotient ρ :=
  Quotient.lift (fun x => orbitQuotientMk ρ (a⁻¹ x))
    (fun _ _ hxy => orbitQuotientMk_eq_of_orbit ρ
      (inverse_conjugator_maps_orbits e ρ σ a hconj hxy))

/-- Conjugate actions induce an equivalence of their orbit quotients. -/
noncomputable def descendedEquiv
    (e : G ≃* H) (ρ : G →* (X ≃ᵢ X)) (σ : H →* (X ≃ᵢ X))
    (a : X ≃ᵢ X) (hconj : IsometricGroupConjugacy e ρ σ a) :
    OrbitQuotient ρ ≃ OrbitQuotient σ where
  toFun := descendedMap e ρ σ a hconj
  invFun := descendedInverse e ρ σ a hconj
  left_inv := by
    intro q
    induction q using Quotient.inductionOn' with
    | _ x =>
        simp [descendedMap, descendedInverse, orbitQuotientMk, Quotient.lift_mk]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn' with
    | _ x =>
        simp [descendedMap, descendedInverse, orbitQuotientMk, Quotient.lift_mk]

theorem descendedMap_comp_orbitQuotientMk
    (e : G ≃* H) (ρ : G →* (X ≃ᵢ X)) (σ : H →* (X ≃ᵢ X))
    (a : X ≃ᵢ X) (hconj : IsometricGroupConjugacy e ρ σ a) (x : X) :
      descendedMap e ρ σ a hconj (orbitQuotientMk ρ x) =
      orbitQuotientMk σ (a x) := by
  simp [descendedMap, orbitQuotientMk, Quotient.lift_mk]

theorem descendedEquiv_comp_orbitQuotientMk
    (e : G ≃* H) (ρ : G →* (X ≃ᵢ X)) (σ : H →* (X ≃ᵢ X))
    (a : X ≃ᵢ X) (hconj : IsometricGroupConjugacy e ρ σ a) (x : X) :
    descendedEquiv e ρ σ a hconj (orbitQuotientMk ρ x) =
      orbitQuotientMk σ (a x) := by
  change descendedMap e ρ σ a hconj (orbitQuotientMk ρ x) =
    orbitQuotientMk σ (a x)
  exact descendedMap_comp_orbitQuotientMk e ρ σ a hconj x

#print axioms orbitQuotientMk_eq_of_orbit
#print axioms descendedEquiv
#print axioms descendedMap_comp_orbitQuotientMk
#print axioms descendedEquiv_comp_orbitQuotientMk

end ConjugacyDescent

end D5.S3.Geometry.MostowPrasadDescent
