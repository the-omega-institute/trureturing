/- GID: D5/S3/Factorization/Icosahedral/ExteriorSquareRepresentations
   generality: I
   mirror-B: D5/B/S3/Factorization/Icosahedral/ExteriorSquareRepresentations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Hodge eigenspaces give conjugate A5 representations and an equivariant split. -/

import D5.S3.Factorization.Icosahedral.ExteriorSquareCoordinates

/- Library-search audit trail (2026-08-30):
   * Repository searches found no prior typed A5 Hodge-eigenspace decomposition.
   * Pinned Mathlib supplies representation products and equivalences, reused here.
   * Pinned Mathlib has no A5 character table or Galois-conjugacy carrier; this file
     defines the exact quadratic action witness over the existing coordinate model.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Icosahedral.ExteriorSquareThreePlusThree

open scoped MatrixGroups MonoidAlgebra
open D5.S3.Arith.Lattices.ExactDualLatticeFormula
open Module

set_option maxHeartbeats 1000000 in
-- Kernel reduction checks the explicit six-by-six integral product.
set_option maxRecDepth 10000 in
private lemma integral_hodge_square :
    integralHodgeMatrix * integralHodgeMatrix =
      (5 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by
  decide

set_option maxHeartbeats 1000000 in
-- Kernel reduction enumerates all sixty group elements and six-by-six entries.
set_option maxRecDepth 10000 in
private lemma integral_hodge_commutes : ∀ g : A5,
    integralHodgeMatrix * integralWedgeActionMatrix g =
      integralWedgeActionMatrix g * integralHodgeMatrix := by
  decide

private lemma hodge_matrix_square :
    hodgeMatrix * hodgeMatrix = (5 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
  calc
    hodgeMatrix * hodgeMatrix =
        (integralHodgeMatrix * integralHodgeMatrix).map (Int.castRingHom ℝ) :=
      (Matrix.map_mul_intCast integralHodgeMatrix integralHodgeMatrix).symm
    _ = ((5 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ)).map (Int.castRingHom ℝ) := by
      rw [integral_hodge_square]
    _ = (5 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
      ext i j
      simp [Matrix.one_apply, Matrix.ofNat_apply]

private lemma hodge_matrix_commutes (g : A5) :
    hodgeMatrix * realWedgeActionMatrix g = realWedgeActionMatrix g * hodgeMatrix := by
  calc
    hodgeMatrix * realWedgeActionMatrix g =
        (integralHodgeMatrix * integralWedgeActionMatrix g).map (Int.castRingHom ℝ) :=
      (Matrix.map_mul_intCast integralHodgeMatrix (integralWedgeActionMatrix g)).symm
    _ = (integralWedgeActionMatrix g * integralHodgeMatrix).map (Int.castRingHom ℝ) := by
      rw [integral_hodge_commutes]
    _ = realWedgeActionMatrix g * hodgeMatrix :=
      Matrix.map_mul_intCast (integralWedgeActionMatrix g) integralHodgeMatrix

private lemma hodgeEndomorphism_square :
    hodgeEndomorphism ∘ₗ hodgeEndomorphism =
      (5 : ℝ) • LinearMap.id (R := ℝ) (M := AmbientSpace) := by
  rw [hodgeEndomorphism, ← Matrix.mulVecLin_mul, hodge_matrix_square]
  ext x i
  simp

private lemma hodgeEndomorphism_commutes (g : A5) :
    hodgeEndomorphism ∘ₗ coordinateExteriorSquare g =
      coordinateExteriorSquare g ∘ₗ hodgeEndomorphism := by
  rw [coordinateExteriorSquare_apply, hodgeEndomorphism,
    ← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, hodge_matrix_commutes]

/-- The positive `sqrt 5` Hodge eigenspace, the carrier of `V₃`. -/
noncomputable def V₃Space : Submodule ℝ AmbientSpace :=
  LinearMap.ker
    (hodgeEndomorphism -
      Real.sqrt 5 • LinearMap.id (R := ℝ) (M := AmbientSpace))

/-- The negative `sqrt 5` Hodge eigenspace, the carrier of `V₃'`. -/
noncomputable def V₃PrimeSpace : Submodule ℝ AmbientSpace :=
  LinearMap.ker
    (hodgeEndomorphism +
      Real.sqrt 5 • LinearMap.id (R := ℝ) (M := AmbientSpace))

private lemma V₃Space_invariant (g : A5) :
    V₃Space ≤ V₃Space.comap (coordinateExteriorSquare g) := by
  intro x hx
  change hodgeEndomorphism x - Real.sqrt 5 • x = 0 at hx
  change hodgeEndomorphism (coordinateExteriorSquare g x) -
    Real.sqrt 5 • coordinateExteriorSquare g x = 0
  have hc := LinearMap.congr_fun (hodgeEndomorphism_commutes g) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
  calc
    hodgeEndomorphism (coordinateExteriorSquare g x) -
        Real.sqrt 5 • coordinateExteriorSquare g x =
      coordinateExteriorSquare g (hodgeEndomorphism x) -
        coordinateExteriorSquare g (Real.sqrt 5 • x) := by rw [hc]; simp
    _ = coordinateExteriorSquare g
        (hodgeEndomorphism x - Real.sqrt 5 • x) := by rw [map_sub]
    _ = 0 := by rw [hx]; simp

private lemma V₃PrimeSpace_invariant (g : A5) :
    V₃PrimeSpace ≤ V₃PrimeSpace.comap (coordinateExteriorSquare g) := by
  intro x hx
  change hodgeEndomorphism x + Real.sqrt 5 • x = 0 at hx
  change hodgeEndomorphism (coordinateExteriorSquare g x) +
    Real.sqrt 5 • coordinateExteriorSquare g x = 0
  have hc := LinearMap.congr_fun (hodgeEndomorphism_commutes g) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
  calc
    hodgeEndomorphism (coordinateExteriorSquare g x) +
        Real.sqrt 5 • coordinateExteriorSquare g x =
      coordinateExteriorSquare g (hodgeEndomorphism x) +
        coordinateExteriorSquare g (Real.sqrt 5 • x) := by rw [hc]; simp
    _ = coordinateExteriorSquare g
        (hodgeEndomorphism x + Real.sqrt 5 • x) := by rw [map_add]
    _ = 0 := by rw [hx]; simp

/-- The positive three-dimensional icosahedral representation `V₃`. -/
noncomputable def V₃ : Representation ℝ A5 V₃Space :=
  coordinateExteriorSquare.subrepresentation V₃Space V₃Space_invariant

/-- The negative three-dimensional icosahedral representation `V₃'`. -/
noncomputable def V₃Prime : Representation ℝ A5 V₃PrimeSpace :=
  coordinateExteriorSquare.subrepresentation V₃PrimeSpace V₃PrimeSpace_invariant

private lemma sqrt_five_square : Real.sqrt 5 * Real.sqrt 5 = 5 := by
  norm_num

/-- Spectral projection onto the positive Hodge eigenspace. -/
noncomputable def positiveProjection : AmbientSpace →ₗ[ℝ] AmbientSpace :=
  (1 / (2 * Real.sqrt 5)) •
    (Real.sqrt 5 • LinearMap.id (R := ℝ) (M := AmbientSpace) + hodgeEndomorphism)

/-- Spectral projection onto the negative Hodge eigenspace. -/
noncomputable def negativeProjection : AmbientSpace →ₗ[ℝ] AmbientSpace :=
  (1 / (2 * Real.sqrt 5)) •
    (Real.sqrt 5 • LinearMap.id (R := ℝ) (M := AmbientSpace) - hodgeEndomorphism)

private lemma positiveProjection_mem (x : AmbientSpace) :
    positiveProjection x ∈ V₃Space := by
  change hodgeEndomorphism (positiveProjection x) -
    Real.sqrt 5 • positiveProjection x = 0
  have hJ := LinearMap.congr_fun hodgeEndomorphism_square x
  rw [LinearMap.comp_apply] at hJ
  have hJ' : hodgeEndomorphism (hodgeEndomorphism x) =
      (Real.sqrt 5 * Real.sqrt 5) • x := by
    rw [sqrt_five_square]
    simpa using hJ
  simp only [positiveProjection, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply, map_smul, map_add]
  rw [hJ']
  module

private lemma negativeProjection_mem (x : AmbientSpace) :
    negativeProjection x ∈ V₃PrimeSpace := by
  change hodgeEndomorphism (negativeProjection x) +
    Real.sqrt 5 • negativeProjection x = 0
  have hJ := LinearMap.congr_fun hodgeEndomorphism_square x
  rw [LinearMap.comp_apply] at hJ
  have hJ' : hodgeEndomorphism (hodgeEndomorphism x) =
      (Real.sqrt 5 * Real.sqrt 5) • x := by
    rw [sqrt_five_square]
    simpa using hJ
  simp only [negativeProjection, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_smul, map_sub]
  rw [hJ']
  module

private lemma V₃Space_eigen (x : V₃Space) :
    hodgeEndomorphism x.1 = Real.sqrt 5 • x.1 := by
  have hx := x.2
  change hodgeEndomorphism x.1 - Real.sqrt 5 • x.1 = 0 at hx
  exact sub_eq_zero.mp hx

private lemma V₃PrimeSpace_eigen (x : V₃PrimeSpace) :
    hodgeEndomorphism x.1 = -(Real.sqrt 5 • x.1) := by
  have hx := x.2
  change hodgeEndomorphism x.1 + Real.sqrt 5 • x.1 = 0 at hx
  exact eq_neg_of_add_eq_zero_left hx

private lemma projection_scalar_identity :
    (1 / (2 * Real.sqrt 5)) * 2 * Real.sqrt 5 = (1 : ℝ) := by
  field_simp

private lemma positiveProjection_on_V₃Space (x : V₃Space) :
    positiveProjection x.1 = x.1 := by
  simp only [positiveProjection, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply, V₃Space_eigen]
  rw [← two_smul ℝ, smul_smul, smul_smul, projection_scalar_identity, one_smul]

private lemma positiveProjection_on_V₃PrimeSpace (x : V₃PrimeSpace) :
    positiveProjection x.1 = 0 := by
  simp only [positiveProjection, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply, V₃PrimeSpace_eigen]
  module

private lemma negativeProjection_on_V₃Space (x : V₃Space) :
    negativeProjection x.1 = 0 := by
  simp only [negativeProjection, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, V₃Space_eigen]
  module

private lemma negativeProjection_on_V₃PrimeSpace (x : V₃PrimeSpace) :
    negativeProjection x.1 = x.1 := by
  simp only [negativeProjection, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, V₃PrimeSpace_eigen]
  rw [sub_neg_eq_add, ← two_smul ℝ, smul_smul, smul_smul,
    projection_scalar_identity, one_smul]

private lemma positive_add_negative (x : AmbientSpace) :
    positiveProjection x + negativeProjection x = x := by
  simp only [positiveProjection, negativeProjection, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [← smul_add]
  rw [show (Real.sqrt 5 • x + hodgeEndomorphism x) +
      (Real.sqrt 5 • x - hodgeEndomorphism x) =
      (2 : ℝ) • (Real.sqrt 5 • x) by module]
  rw [smul_smul, smul_smul, projection_scalar_identity, one_smul]

/-- The two Hodge components of a six-dimensional exterior vector. -/
noncomputable def hodgeDecompositionMap : AmbientSpace →ₗ[ℝ] V₃Space × V₃PrimeSpace where
  toFun x :=
    (⟨positiveProjection x, positiveProjection_mem x⟩,
      ⟨negativeProjection x, negativeProjection_mem x⟩)
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- Linear direct-sum decomposition into the two Hodge eigenspaces. -/
noncomputable def hodgeDecomposition : AmbientSpace ≃ₗ[ℝ] V₃Space × V₃PrimeSpace :=
  LinearEquiv.ofBijective hodgeDecompositionMap <| by
    constructor
    · intro x y h
      have hp := congrArg (fun z => z.1.1) h
      have hn := congrArg (fun z => z.2.1) h
      change positiveProjection x = positiveProjection y at hp
      change negativeProjection x = negativeProjection y at hn
      calc
        x = positiveProjection x + negativeProjection x := (positive_add_negative x).symm
        _ = positiveProjection y + negativeProjection y := by rw [hp, hn]
        _ = y := positive_add_negative y
    · rintro ⟨x, y⟩
      refine ⟨x.1 + y.1, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change positiveProjection (x.1 + y.1) = x.1
        rw [map_add, positiveProjection_on_V₃Space,
          positiveProjection_on_V₃PrimeSpace, add_zero]
      · apply Subtype.ext
        change negativeProjection (x.1 + y.1) = y.1
        rw [map_add, negativeProjection_on_V₃Space,
          negativeProjection_on_V₃PrimeSpace, zero_add]

/-- Source eigenbasis for the positive `sqrt 5` Hodge eigenspace. -/
noncomputable def positiveEigenbasisMatrix : Matrix (Fin 6) (Fin 3) ℝ :=
  !![(5 + Real.sqrt 5) / 10, (5 - Real.sqrt 5) / 10, -2 * Real.sqrt 5 / 5;
     (-5 + Real.sqrt 5) / 10, 2 * Real.sqrt 5 / 5, (5 + Real.sqrt 5) / 10;
     -2 * Real.sqrt 5 / 5, (-5 - Real.sqrt 5) / 10, (-5 + Real.sqrt 5) / 10;
     1, 0, 0;
     0, 1, 0;
     0, 0, 1]

/-- Source eigenbasis for the negative `sqrt 5` Hodge eigenspace. -/
noncomputable def negativeEigenbasisMatrix : Matrix (Fin 6) (Fin 3) ℝ :=
  !![(5 - Real.sqrt 5) / 10, (5 + Real.sqrt 5) / 10, 2 * Real.sqrt 5 / 5;
     (-5 - Real.sqrt 5) / 10, -2 * Real.sqrt 5 / 5, (5 - Real.sqrt 5) / 10;
     2 * Real.sqrt 5 / 5, (-5 + Real.sqrt 5) / 10, (-5 - Real.sqrt 5) / 10;
     1, 0, 0;
     0, 1, 0;
     0, 0, 1]

/-- Exact quadratic coefficient ring `ℚ(√5)` used by the two source embeddings. -/
abbrev Q5 := QuadraticAlgebra ℚ 5 0

/-- Exact positive Hodge eigenbasis over `ℚ(√5)`. -/
def q5PositiveEigenbasisMatrix : Matrix (Fin 6) (Fin 3) Q5 :=
  !![⟨1 / 2, 1 / 10⟩, ⟨1 / 2, -1 / 10⟩, ⟨0, -2 / 5⟩;
     ⟨-1 / 2, 1 / 10⟩, ⟨0, 2 / 5⟩, ⟨1 / 2, 1 / 10⟩;
     ⟨0, -2 / 5⟩, ⟨-1 / 2, -1 / 10⟩, ⟨-1 / 2, 1 / 10⟩;
     ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]

/-- Exact positive three-dimensional action matrices over `ℚ(√5)`. -/
def q5PositiveActionMatrix (g : A5) : Matrix (Fin 3) (Fin 3) Q5 := fun i j =>
  ((integralWedgeActionMatrix g).map (Int.castRingHom Q5) *
      q5PositiveEigenbasisMatrix) (Fin.natAdd 3 i) j

/-- Integral quadratic coefficient ring used for the kernel-checked frame certificate. -/
abbrev Z5 := QuadraticAlgebra ℤ 5 0

/-- Ten times the positive eigenbasis, now integral over `ℤ[√5]`. -/
def z5PositiveEigenbasisScaled : Matrix (Fin 6) (Fin 3) Z5 :=
  !![⟨5, 1⟩, ⟨5, -1⟩, ⟨0, -4⟩;
     ⟨-5, 1⟩, ⟨0, 4⟩, ⟨5, 1⟩;
     ⟨0, -4⟩, ⟨-5, -1⟩, ⟨-5, 1⟩;
     ⟨10, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨10, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨10, 0⟩]

/-- Ten times the exact positive action chart. -/
def z5PositiveActionScaled (g : A5) : Matrix (Fin 3) (Fin 3) Z5 := fun i j =>
  ((integralWedgeActionMatrix g).map (Int.castRingHom Z5) *
      z5PositiveEigenbasisScaled) (Fin.natAdd 3 i) j

/-- Conjugate integral action used for the negative Hodge eigenspace. -/
def z5NegativeActionScaled (g : A5) : Matrix (Fin 3) (Fin 3) Z5 := fun i j =>
  star (z5PositiveActionScaled g i j)

/-- Three times the first frame factor. -/
def z5FrameLeftScaled : Matrix (Fin 3) (Fin 3) Z5 :=
  !![⟨3, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩;
     ⟨-1, 0⟩, ⟨3, 0⟩, ⟨-1, 0⟩;
     ⟨1, 0⟩, ⟨-1, 0⟩, ⟨3, 0⟩]

/-- One third of the second frame factor. -/
def z5FrameRightDivThree : Matrix (Fin 3) (Fin 3) Z5 :=
  !![⟨8, 0⟩, ⟨2, 0⟩, ⟨-2, 0⟩;
     ⟨2, 0⟩, ⟨8, 0⟩, ⟨2, 0⟩;
     ⟨-2, 0⟩, ⟨2, 0⟩, ⟨8, 0⟩]

/-- Real embedding of the integral quadratic certificate, sending `ω` to `√5`. -/
noncomputable def z5ToReal : Z5 →+* ℝ where
  toFun z := z.re + z.im * Real.sqrt 5
  map_zero' := by simp
  map_one' := by
    simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    push_cast
    ring
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    push_cast
    linear_combination -(x.im : ℝ) * (y.im : ℝ) * sqrt_five_square

/-- Real embedding of `ℚ(√5)`, sending its generator to positive `√5`. -/
noncomputable def q5ToReal : Q5 →+* ℝ where
  toFun z := z.re + z.im * Real.sqrt 5
  map_zero' := by simp
  map_one' := by
    simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    push_cast
    ring
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    push_cast
    linear_combination -(x.im : ℝ) * (y.im : ℝ) * sqrt_five_square

/-- The conjugate real embedding of `ℚ(√5)`, sending its generator to negative `√5`. -/
noncomputable def q5ConjugateToReal : Q5 →+* ℝ :=
  q5ToReal.comp (starRingEnd Q5)

/-- Two real representations given by the conjugate embeddings of one `ℚ(√5)` matrix family. -/
def RepresentationsAreQ5GaloisConjugate
    {M N : Type*} [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N]
    (rho : Representation ℝ A5 M) (sigma : Representation ℝ A5 N)
    (rhoChart : M ≃ₗ[ℝ] (Fin 3 → ℝ))
    (sigmaChart : N ≃ₗ[ℝ] (Fin 3 → ℝ)) : Prop :=
  ∃ exactAction : A5 → Matrix (Fin 3) (Fin 3) Q5,
    (∀ g x, rhoChart (rho g x) =
      Matrix.mulVec ((exactAction g).map q5ToReal) (rhoChart x)) ∧
    (∀ g x, sigmaChart (sigma g x) =
      Matrix.mulVec ((exactAction g).map q5ConjugateToReal) (sigmaChart x))

/-- Positive coordinate-action matrix of the actual real representation. -/
noncomputable def positiveActionMatrix (g : A5) : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  (1 / 10 : ℝ) * z5ToReal (z5PositiveActionScaled g i j)

/-- Negative coordinate-action matrix of the actual real representation. -/
noncomputable def negativeActionMatrix (g : A5) : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  (1 / 10 : ℝ) * z5ToReal (z5NegativeActionScaled g i j)

/-- First real factor in the orbit-frame identity. -/
noncomputable def frameLeft : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, -1 / 3, 1 / 3;
     -1 / 3, 1, -1 / 3;
     1 / 3, -1 / 3, 1]

/-- Second real factor in the orbit-frame identity. -/
def frameRight : Matrix (Fin 3) (Fin 3) ℝ :=
  !![24, 6, -6;
     6, 24, 6;
     -6, 6, 24]

private lemma positiveProjection_commutes_action (g : A5) (x : AmbientSpace) :
    positiveProjection (coordinateExteriorSquare g x) =
      coordinateExteriorSquare g (positiveProjection x) := by
  have hc := LinearMap.congr_fun (hodgeEndomorphism_commutes g) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
  simp only [positiveProjection, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply, map_smul, map_add]
  rw [hc]

private lemma negativeProjection_commutes_action (g : A5) (x : AmbientSpace) :
    negativeProjection (coordinateExteriorSquare g x) =
      coordinateExteriorSquare g (negativeProjection x) := by
  have hc := LinearMap.congr_fun (hodgeEndomorphism_commutes g) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hc
  simp only [negativeProjection, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_smul, map_sub]
  rw [hc]

/-- The coordinate exterior square is equivariantly the product of its Hodge eigenspaces. -/
noncomputable def coordinateHodgeDecompositionEquiv :
    coordinateExteriorSquare.Equiv (V₃.prod V₃Prime) :=
  Representation.Equiv.mk hodgeDecomposition fun g => by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · apply Subtype.ext
      exact positiveProjection_commutes_action g x
    · apply Subtype.ext
      exact negativeProjection_commutes_action g x

/-- The explicit `A₅`-equivariant decomposition `Λ²V₄ ≃ V₃ ⊕ V₃'`. -/
noncomputable def exteriorSquareDecomposition :
    exteriorSquareV₄.Equiv (V₃.prod V₃Prime) :=
  exteriorSquareCoordinateEquiv.trans coordinateHodgeDecompositionEquiv

-- Degenerate probes: the identity action and zero vector respect the split.
example : exteriorSquareV₄ 1 = LinearMap.id := map_one exteriorSquareV₄

example : exteriorSquareDecomposition 0 = 0 :=
  map_zero exteriorSquareDecomposition

end D5.S3.Factorization.Icosahedral.ExteriorSquareThreePlusThree
