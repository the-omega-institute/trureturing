/- GID: D5/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree
   generality: I
   mirror-B: D5/B/S3/Factorization/Icosahedral/ExteriorSquareThreePlusThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The real exterior square of centered A5 splits into conjugate irreducible threes. -/

import D5.S3.Arith.Lattices.ExactDualLatticeFormula
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.RepresentationTheory.Irreducible

/- Library-search audit trail (2026-08-30):
   * Six repository searches by theorem name, Mathlib vocabulary, digest, A5 neighbors,
     generalized representation shape, and exterior-square synonyms found no prior split.
   * Loogle's representation-shape query found `Representation.prod` and `.Equiv`; pinned
     Mathlib also supplies `exteriorPower.map`, `Module.Basis.exteriorPower`, and irreducibility.
   * LeanSearch's equal-character query failed at its API; pinned Mathlib has character
     orthogonality but no A5 character table or equal-character converse used here.
   * Pinned Mathlib has no exterior-power representation wrapper or Galois-conjugacy carrier.
     The definitions below supply those missing typed constructions and reuse the unique Hodge
     matrix from `ExactDualLatticeFormula` rather than copying it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Icosahedral.ExteriorSquareThreePlusThree

open scoped MatrixGroups MonoidAlgebra
open D5.S3.Arith.Lattices.ExactDualLatticeFormula
open Module

/-- The source group, in the repository's existing vocabulary. -/
abbrev A5 := alternatingGroup (Fin 5)

/-- Sum of the five coordinates. -/
def coordinateSum : (Fin 5 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.mul_sum]

/-- The source's centered four-dimensional real space `V₄`. -/
def centeredSpace : Submodule ℝ (Fin 5 → ℝ) :=
  LinearMap.ker coordinateSum

/-- The coordinate-permutation representation of `A₅` on five real coordinates. -/
def coordinatePermutationRepresentation : Representation ℝ A5 (Fin 5 → ℝ) where
  toFun g :=
    { toFun := fun x i => x (((g⁻¹ : A5).val) i)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_one' := by
    apply LinearMap.ext
    intro x
    funext i
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    funext i
    simp

private lemma coordinateSum_permuted (g : A5) (x : Fin 5 → ℝ) :
    coordinateSum (coordinatePermutationRepresentation g x) = coordinateSum x := by
  change (∑ i, x (((g⁻¹ : A5).val) i)) = ∑ i, x i
  exact Equiv.sum_comp (g⁻¹ : A5).val x

/-- The standard centered four-dimensional representation `V₄` of `A₅`. -/
def V₄ : Representation ℝ A5 centeredSpace :=
  coordinatePermutationRepresentation.subrepresentation centeredSpace fun g x hx => by
    change coordinateSum (coordinatePermutationRepresentation g x) = 0
    rw [coordinateSum_permuted]
    exact hx

/-- Exterior-power representations induced functorially by `exteriorPower.map`. -/
noncomputable def exteriorPowerRepresentation {G M : Type*} [Monoid G]
    [AddCommGroup M] [Module ℝ M]
    (n : ℕ) (ρ : Representation ℝ G M) : Representation ℝ G (⋀[ℝ]^n M) where
  toFun g := exteriorPower.map n (ρ g)
  map_one' := by
    rw [map_one]
    change exteriorPower.map n (LinearMap.id (R := ℝ) (M := M)) = LinearMap.id
    exact exteriorPower.map_id
  map_mul' g h := by
    rw [map_mul]
    change exteriorPower.map n ((ρ g) ∘ₗ (ρ h)) =
      exteriorPower.map n (ρ g) ∘ₗ exteriorPower.map n (ρ h)
    exact exteriorPower.map_comp (ρ h) (ρ g)

/-- The source's six-dimensional second-order observation space `W₆ := Λ²V₄`. -/
abbrev W₆ := ⋀[ℝ]^2 centeredSpace

/-- The actual second exterior-power representation on `W₆`. -/
noncomputable def exteriorSquareV₄ : Representation ℝ A5 W₆ :=
  exteriorPowerRepresentation 2 V₄

/-- Build a centered vector from its first four coordinates. -/
def centeredFromCoordinates : (Fin 4 → ℝ) →ₗ[ℝ] centeredSpace where
  toFun x :=
    ⟨Fin.lastCases (-∑ i, x i) x, by
      change (∑ i : Fin 5, (Fin.lastCases (-∑ j, x j) x i : ℝ)) = (0 : ℝ)
      rw [Fin.sum_univ_castSucc]
      change (∑ i : Fin 4, x i) + -(∑ i : Fin 4, x i) = 0
      ring⟩
  map_add' x y := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change -(∑ i : Fin 4, (x + y) i) =
        -(∑ i : Fin 4, x i) + -(∑ i : Fin 4, y i)
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      ring
    · simp
  map_smul' r x := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change -(∑ i : Fin 4, r * x i) = r * -(∑ i : Fin 4, x i)
      rw [← Finset.mul_sum]
      ring
    · simp

/-- Equivalence from four coordinates to the centered space. -/
noncomputable def coordinatesToCentered : (Fin 4 → ℝ) ≃ₗ[ℝ] centeredSpace :=
  LinearEquiv.ofBijective centeredFromCoordinates <| by
    constructor
    · intro x y h
      funext i
      have hi := congrFun (congrArg Subtype.val h) i.castSucc
      simpa [centeredFromCoordinates] using hi
    · intro y
      refine ⟨fun i => y.1 i.castSucc, ?_⟩
      apply Subtype.ext
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change -(∑ j : Fin 4, y.1 j.castSucc) = y.1 (Fin.last 4)
        have hy : coordinateSum y = 0 := y.2
        change (∑ i : Fin 5, y.1 i) = 0 at hy
        rw [Fin.sum_univ_castSucc] at hy
        linarith
      · simp [centeredFromCoordinates]

/-- First-four-coordinate equivalence for the centered space. -/
noncomputable def centeredCoordinates : centeredSpace ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  coordinatesToCentered.symm

@[simp]
private lemma centeredCoordinates_apply (x : centeredSpace) (i : Fin 4) :
    centeredCoordinates x i = x.1 i.castSucc := by
  have h := congrArg (fun y : centeredSpace => y.1 i.castSucc)
    (coordinatesToCentered.apply_symm_apply x)
  change (centeredFromCoordinates (coordinatesToCentered.symm x)).1 i.castSucc =
    x.1 i.castSucc at h
  simpa [centeredCoordinates, centeredFromCoordinates] using h

private lemma centered_last_coordinate (x : centeredSpace) :
    x.1 (Fin.last 4) = -(∑ i : Fin 4, x.1 i.castSucc) := by
  have hx : coordinateSum x = 0 := x.2
  change (∑ i : Fin 5, x.1 i) = 0 at hx
  rw [Fin.sum_univ_castSucc] at hx
  linarith

/-- The source basis `bᵢ = eᵢ - e₅` of the centered space. -/
noncomputable def centeredBasis : Basis (Fin 4) ℝ centeredSpace :=
  Basis.ofEquivFun centeredCoordinates

@[simp]
private lemma centeredBasis_coordinate (i j : Fin 4) :
    centeredCoordinates (centeredBasis i) j = if i = j then 1 else 0 := by
  simpa [centeredBasis] using centeredBasis.equivFun_self i j

private lemma centeredBasis_coord (i : Fin 4) (x : centeredSpace) :
    centeredBasis.coord i x = centeredCoordinates x i := by
  rfl

/-- The ordered pair behind each source wedge coordinate. -/
def wedgePair : Fin 6 → Set.powersetCard (Fin 4) 2 := fun i =>
  ![⟨{0, 1}, by simp [Set.powersetCard.mem_iff]⟩,
    ⟨{0, 2}, by simp [Set.powersetCard.mem_iff]⟩,
    ⟨{0, 3}, by simp [Set.powersetCard.mem_iff]⟩,
    ⟨{1, 2}, by simp [Set.powersetCard.mem_iff]⟩,
    ⟨{1, 3}, by simp [Set.powersetCard.mem_iff]⟩,
    ⟨{2, 3}, by simp [Set.powersetCard.mem_iff]⟩] i

set_option linter.flexible false in
private lemma wedgePair_bijective : Function.Bijective wedgePair := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp [wedgePair] at h ⊢
    all_goals
      have h0 := congrArg (fun s : Finset (Fin 4) => (0 : Fin 4) ∈ s) h
      have h1 := congrArg (fun s : Finset (Fin 4) => (1 : Fin 4) ∈ s) h
      have h2 := congrArg (fun s : Finset (Fin 4) => (2 : Fin 4) ∈ s) h
      have h3 := congrArg (fun s : Finset (Fin 4) => (3 : Fin 4) ∈ s) h
      simp at h0 h1 h2 h3
  · calc
      Fintype.card (Fin 6) = 6 := by simp
      _ = Nat.card (Set.powersetCard (Fin 4) 2) := by
        rw [Set.powersetCard.card]
        rw [Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      _ = Fintype.card (Set.powersetCard (Fin 4) 2) := Nat.card_eq_fintype_card

/-- Identification of the six source wedge coordinates with two-subsets of four indices. -/
noncomputable def wedgePairEquiv : Fin 6 ≃ Set.powersetCard (Fin 4) 2 :=
  Equiv.ofBijective wedgePair wedgePair_bijective

/-- The source-ordered basis `(12,13,14,23,24,34)` of `W₆`. -/
noncomputable def wedgeBasis : Basis (Fin 6) ℝ W₆ :=
  (centeredBasis.exteriorPower 2).reindex wedgePairEquiv.symm

/-- Coordinates of the actual exterior square in the source-ordered basis. -/
noncomputable def wedgeCoordinates : W₆ ≃ₗ[ℝ] AmbientSpace :=
  wedgeBasis.equivFun

/-- The first index in the ordered wedge coordinate. -/
def wedgeFirst : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

/-- The second index in the ordered wedge coordinate. -/
def wedgeSecond : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

private lemma wedgePair_order (i : Fin 6) :
    Set.powersetCard.ofFinEmbEquiv.symm (wedgePair i) 0 = wedgeFirst i ∧
      Set.powersetCard.ofFinEmbEquiv.symm (wedgePair i) 1 = wedgeSecond i := by
  fin_cases i <;>
    norm_num [wedgePair, wedgeFirst, wedgeSecond,
      Set.powersetCard.ofFinEmbEquiv_symm_apply, Finset.orderEmbOfFin_apply] <;>
    simp [Finset.sort_insert]

private lemma wedgeBasis_apply (i : Fin 6) :
    wedgeBasis i = exteriorPower.ιMulti_family ℝ 2 centeredBasis (wedgePair i) := by
  rw [wedgeBasis, Basis.reindex_apply, exteriorPower.basis_apply]
  rfl

/-- Integral matrix of the centered action in the basis `bᵢ = eᵢ - e₅`. -/
def centeredActionMatrix (g : A5) : Matrix (Fin 4) (Fin 4) ℤ := fun i j =>
  if ((g⁻¹ : A5).val i.castSucc) = Fin.last 4 then -1
  else if ((g⁻¹ : A5).val i.castSucc) = j.castSucc then 1 else 0

private lemma centered_action_coordinate (g : A5) (i j : Fin 4) :
    centeredCoordinates (V₄ g (centeredBasis j)) i =
      (centeredActionMatrix g i j : ℝ) := by
  rw [centeredCoordinates_apply]
  change (centeredBasis j).1 ((g⁻¹ : A5).val i.castSucc) = _
  by_cases hlast : ((g⁻¹ : A5).val i.castSucc) = Fin.last 4
  · rw [hlast, centered_last_coordinate]
    have hlast' : (Equiv.symm g.val) i.castSucc = Fin.last 4 := by
      simpa using hlast
    simp [centeredActionMatrix, hlast', ← centeredCoordinates_apply]
  · obtain ⟨k, hk⟩ := Fin.eq_castSucc_of_ne_last hlast
    rw [← hk, ← centeredCoordinates_apply, centeredBasis_coordinate]
    have hk' : k.castSucc = (Equiv.symm g.val) i.castSucc := by
      simpa using hk
    have hkFour : k.castSucc ≠ (4 : Fin 5) := by
      intro h
      exact (Nat.ne_of_lt k.isLt) (by simpa using congrArg Fin.val h)
    simp [centeredActionMatrix, ← hk', hkFour, eq_comm]

/-- Integral second-exterior-power action, expressed by the two-by-two minors. -/
def integralWedgeActionMatrix (g : A5) : Matrix (Fin 6) (Fin 6) ℤ := fun i j =>
  centeredActionMatrix g (wedgeFirst i) (wedgeFirst j) *
      centeredActionMatrix g (wedgeSecond i) (wedgeSecond j) -
    centeredActionMatrix g (wedgeFirst i) (wedgeSecond j) *
      centeredActionMatrix g (wedgeSecond i) (wedgeFirst j)

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

private lemma wedge_action_coordinate (g : A5) (i j : Fin 6) :
    wedgeCoordinates (exteriorSquareV₄ g (wedgeBasis j)) i =
      (integralWedgeActionMatrix g i j : ℝ) := by
  rw [wedgeCoordinates, Basis.equivFun_apply]
  rw [wedgeBasis_apply]
  rw [wedgeBasis, Basis.repr_reindex_apply]
  change (centeredBasis.exteriorPower 2).repr _ (wedgePair i) = _
  rw [exteriorPower.basis_repr_apply]
  change exteriorPower.ιMultiDual ℝ 2 centeredBasis (wedgePair i)
    (exteriorPower.map 2 (V₄ g)
      (exteriorPower.ιMulti_family ℝ 2 centeredBasis (wedgePair j))) = _
  rw [exteriorPower.map_apply_ιMulti_family]
  rw [exteriorPower.ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti]
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply]
  obtain ⟨hi0, hi1⟩ := wedgePair_order i
  obtain ⟨hj0, hj1⟩ := wedgePair_order j
  simp only [Function.comp_apply]
  rw [hi0, hi1, hj0, hj1]
  rw [centeredBasis_coord, centeredBasis_coord, centeredBasis_coord,
    centeredBasis_coord]
  rw [centered_action_coordinate, centered_action_coordinate,
    centered_action_coordinate, centered_action_coordinate]
  norm_num [integralWedgeActionMatrix]
  ring

/-- Transport a representation through a linear equivalence. -/
noncomputable def transportRepresentation {G M N : Type*} [Monoid G]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (ρ : Representation ℝ G M) (e : M ≃ₗ[ℝ] N) : Representation ℝ G N where
  toFun g := e.toLinearMap ∘ₗ (ρ g) ∘ₗ e.symm.toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro x
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    simp

/-- The exterior-square representation in the source's six coordinates. -/
noncomputable def coordinateExteriorSquare : Representation ℝ A5 AmbientSpace :=
  transportRepresentation exteriorSquareV₄ wedgeCoordinates

/-- Coordinate transport is an equivalence of actual `A₅` representations. -/
noncomputable def exteriorSquareCoordinateEquiv :
    exteriorSquareV₄.Equiv coordinateExteriorSquare :=
  Representation.Equiv.mk wedgeCoordinates fun g => by
    apply LinearMap.ext
    intro x
    simp [coordinateExteriorSquare, transportRepresentation]

/-- Real form of the integral exterior-action matrix. -/
def realWedgeActionMatrix (g : A5) : Matrix (Fin 6) (Fin 6) ℝ :=
  (integralWedgeActionMatrix g).map (Int.castRingHom ℝ)

private lemma wedgeCoordinates_symm_basis (j : Fin 6) :
    wedgeCoordinates.symm (Pi.basisFun ℝ (Fin 6) j) = wedgeBasis j := by
  simp [wedgeCoordinates, Pi.basisFun_apply]

private lemma coordinateExteriorSquare_apply (g : A5) :
    coordinateExteriorSquare g = Matrix.mulVecLin (realWedgeActionMatrix g) := by
  apply (Pi.basisFun ℝ (Fin 6)).ext
  intro j
  funext i
  change wedgeCoordinates
    (exteriorSquareV₄ g (wedgeCoordinates.symm (Pi.basisFun ℝ (Fin 6) j))) i = _
  rw [wedgeCoordinates_symm_basis, wedge_action_coordinate]
  fin_cases j <;>
    simp [realWedgeActionMatrix, Matrix.mulVec, dotProduct, Pi.basisFun_apply,
      Fin.sum_univ_succ]

/-- The reused Hodge discriminant matrix as a real linear endomorphism. -/
noncomputable def hodgeEndomorphism : AmbientSpace →ₗ[ℝ] AmbientSpace :=
  Matrix.mulVecLin hodgeMatrix

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

private lemma sqrt_five_ne_zero : Real.sqrt 5 ≠ 0 := by
  positivity

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

set_option maxHeartbeats 2000000 in
-- Kernel reduction evaluates the exact integral quadratic orbit frame.
set_option maxRecDepth 20000 in
private lemma z5_positive_frame_coefficients : ∀ i j a b,
    ∑ g : A5, z5PositiveActionScaled g i a * z5PositiveActionScaled g j b =
      100 * z5FrameLeftScaled i j * z5FrameRightDivThree a b := by
  decide

set_option maxHeartbeats 2000000 in
-- Kernel reduction evaluates the conjugate integral quadratic orbit frame.
set_option maxRecDepth 20000 in
private lemma z5_negative_frame_coefficients : ∀ i j a b,
    ∑ g : A5, z5NegativeActionScaled g i a * z5NegativeActionScaled g j b =
      100 * z5FrameLeftScaled i j * z5FrameRightDivThree a b := by
  decide

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

private lemma positiveActionMatrix_eq_geometric (g : A5) :
    positiveActionMatrix g = fun i j =>
      (realWedgeActionMatrix g * positiveEigenbasisMatrix) (Fin.natAdd 3 i) j := by
  ext i j
  fin_cases j <;>
    simp [positiveActionMatrix, z5PositiveActionScaled, z5PositiveEigenbasisScaled,
      z5ToReal, realWedgeActionMatrix, positiveEigenbasisMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    ring

private lemma negativeActionMatrix_eq_geometric (g : A5) :
    negativeActionMatrix g = fun i j =>
      (realWedgeActionMatrix g * negativeEigenbasisMatrix) (Fin.natAdd 3 i) j := by
  ext i j
  fin_cases j <;>
    simp [negativeActionMatrix, z5NegativeActionScaled, z5PositiveActionScaled,
      z5PositiveEigenbasisScaled, z5ToReal, realWedgeActionMatrix,
      negativeEigenbasisMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private lemma positiveActionMatrix_eq_q5 (g : A5) :
    positiveActionMatrix g = (q5PositiveActionMatrix g).map q5ToReal := by
  ext i j
  fin_cases j <;>
    simp [positiveActionMatrix, z5PositiveActionScaled, z5PositiveEigenbasisScaled,
      z5ToReal, q5PositiveActionMatrix, q5PositiveEigenbasisMatrix, q5ToReal,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private lemma negativeActionMatrix_eq_q5 (g : A5) :
    negativeActionMatrix g = (q5PositiveActionMatrix g).map q5ConjugateToReal := by
  ext i j
  fin_cases j <;>
    simp [negativeActionMatrix, z5NegativeActionScaled, z5PositiveActionScaled,
      z5PositiveEigenbasisScaled, z5ToReal, q5PositiveActionMatrix,
      q5PositiveEigenbasisMatrix, q5ConjugateToReal, q5ToReal, Matrix.mul_apply,
      Fin.sum_univ_succ, starRingEnd_apply, QuadraticAlgebra.star_mk] <;>
    ring

set_option maxHeartbeats 2000000 in
-- The finite coordinate normalization expands all four frame indices.
private lemma positive_frame_coefficients (i j a b : Fin 3) :
    ∑ g : A5, positiveActionMatrix g i a * positiveActionMatrix g j b =
      frameLeft i j * frameRight a b := by
  have h := congrArg z5ToReal (z5_positive_frame_coefficients i j a b)
  simp only [map_sum, map_mul, map_ofNat] at h
  calc
    _ = (1 / 100 : ℝ) * ∑ g : A5,
        z5ToReal (z5PositiveActionScaled g i a) *
          z5ToReal (z5PositiveActionScaled g j b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      simp only [positiveActionMatrix]
      ring
    _ = _ := by
      rw [h]
      fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
        norm_num [frameLeft, frameRight, z5FrameLeftScaled,
          z5FrameRightDivThree, z5ToReal]

set_option maxHeartbeats 2000000 in
-- The conjugate finite coordinate normalization expands all four frame indices.
private lemma negative_frame_coefficients (i j a b : Fin 3) :
    ∑ g : A5, negativeActionMatrix g i a * negativeActionMatrix g j b =
      frameLeft i j * frameRight a b := by
  have h := congrArg z5ToReal (z5_negative_frame_coefficients i j a b)
  simp only [map_sum, map_mul, map_ofNat] at h
  calc
    _ = (1 / 100 : ℝ) * ∑ g : A5,
        z5ToReal (z5NegativeActionScaled g i a) *
          z5ToReal (z5NegativeActionScaled g j b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      simp only [negativeActionMatrix]
      ring
    _ = _ := by
      rw [h]
      fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
        norm_num [frameLeft, frameRight, z5FrameLeftScaled,
          z5FrameRightDivThree, z5ToReal]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Reassociating five nested finite sums needs additional elaboration budget.
private lemma sum_first_to_last
    {R I₀ I₁ I₂ I₃ I₄ : Type*} [AddCommMonoid R]
    [Fintype I₀] [Fintype I₁] [Fintype I₂] [Fintype I₃] [Fintype I₄]
    (f : I₀ → I₁ → I₂ → I₃ → I₄ → R) :
    (∑ i₀, ∑ i₁, ∑ i₂, ∑ i₃, ∑ i₄, f i₀ i₁ i₂ i₃ i₄) =
      ∑ i₁, ∑ i₂, ∑ i₃, ∑ i₄, ∑ i₀, f i₀ i₁ i₂ i₃ i₄ := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i₁ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i₂ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i₃ _
  rw [Finset.sum_comm]

private lemma sum_pair_interchange
    {R I J K L : Type*} [AddCommMonoid R]
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (f : I → J → K → L → R) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) =
      ∑ k, ∑ i, ∑ l, ∑ j, f i j k l := by
  calc
    _ = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]

private lemma sum_first_to_last_four
    {R I₀ I₁ I₂ I₃ : Type*} [AddCommMonoid R]
    [Fintype I₀] [Fintype I₁] [Fintype I₂] [Fintype I₃]
    (f : I₀ → I₁ → I₂ → I₃ → R) :
    (∑ i₀, ∑ i₁, ∑ i₂, ∑ i₃, f i₀ i₁ i₂ i₃) =
      ∑ i₁, ∑ i₂, ∑ i₃, ∑ i₀, f i₀ i₁ i₂ i₃ := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i₁ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i₂ _
  rw [Finset.sum_comm]

private lemma sum_pairs_commute
    {R I J K L : Type*} [AddCommMonoid R]
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (f : I → J → K → L → R) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) =
      ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  calc
    _ = ∑ j, ∑ k, ∑ l, ∑ i, f i j k l := sum_first_to_last_four f
    _ = _ := sum_first_to_last_four fun j k l i => f i j k l

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Expanding the squared orbit pairing produces five nested finite sums.
private lemma orbit_frame_identity
    (B : A5 → Matrix (Fin 3) (Fin 3) ℝ)
    (hB : ∀ i j a b, ∑ g : A5, B g i a * B g j b =
      frameLeft i j * frameRight a b)
    (u v : Fin 3 → ℝ) :
    ∑ g : A5, (dotProduct u (Matrix.mulVec (B g) v)) ^ 2 =
      dotProduct u (Matrix.mulVec frameLeft u) *
        dotProduct v (Matrix.mulVec frameRight v) := by
  classical
  calc
    _ = ∑ g : A5, ∑ j, ∑ b, ∑ i, ∑ a,
        u i * (B g i a * v a) * (u j * (B g j b * v b)) := by
      simp only [dotProduct, Matrix.mulVec, pow_two, Finset.sum_mul,
        Finset.mul_sum]
    _ = ∑ j, ∑ b, ∑ i, ∑ a, ∑ g : A5,
        u i * (B g i a * v a) * (u j * (B g j b * v b)) :=
      sum_first_to_last fun g j b i a =>
        u i * (B g i a * v a) * (u j * (B g j b * v b))
    _ = ∑ j, ∑ b, ∑ i, ∑ a,
        u i * v a * u j * v b * ∑ g : A5, B g i a * B g j b := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = ∑ j, ∑ b, ∑ i, ∑ a,
        u i * v a * u j * v b * (frameLeft i j * frameRight a b) := by
      simp_rw [hB]
    _ = ∑ i, ∑ j, ∑ a, ∑ b,
        u i * v a * u j * v b * (frameLeft i j * frameRight a b) :=
      sum_pair_interchange fun j b i a =>
        u i * v a * u j * v b * (frameLeft i j * frameRight a b)
    _ = ∑ i, ∑ j, ∑ a, ∑ b,
        u a * v i * u b * v j * (frameLeft a b * frameRight i j) :=
      sum_pairs_commute fun i j a b =>
        u i * v a * u j * v b * (frameLeft i j * frameRight a b)
    _ = _ := by
      simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

private lemma three_coordinates_sq_pos {u : Fin 3 → ℝ} (hu : u ≠ 0) :
    0 < u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  have hne : u 0 ≠ 0 ∨ u 1 ≠ 0 ∨ u 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hu
    funext i
    fin_cases i <;> simp_all
  rcases hne with h0 | h1 | h2
  · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (u 1), sq_nonneg (u 2)]
  · nlinarith [sq_nonneg (u 0), sq_pos_of_ne_zero h1, sq_nonneg (u 2)]
  · nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_pos_of_ne_zero h2]

private lemma frameLeft_pos {u : Fin 3 → ℝ} (hu : u ≠ 0) :
    0 < dotProduct u (Matrix.mulVec frameLeft u) := by
  have hnorm := three_coordinates_sq_pos hu
  norm_num [dotProduct, Matrix.mulVec, frameLeft, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (u 0 - u 1), sq_nonneg (u 0 + u 2),
    sq_nonneg (u 1 - u 2)]

private lemma frameRight_pos {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    0 < dotProduct v (Matrix.mulVec frameRight v) := by
  have hnorm := three_coordinates_sq_pos hv
  norm_num [dotProduct, Matrix.mulVec, frameRight, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 0 - v 2),
    sq_nonneg (v 1 + v 2)]

private lemma orbit_frame_pos
    (B : A5 → Matrix (Fin 3) (Fin 3) ℝ)
    (hB : ∀ i j a b, ∑ g : A5, B g i a * B g j b =
      frameLeft i j * frameRight a b)
    {u v : Fin 3 → ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    0 < ∑ g : A5, (dotProduct u (Matrix.mulVec (B g) v)) ^ 2 := by
  rw [orbit_frame_identity B hB]
  exact mul_pos (frameLeft_pos hu) (frameRight_pos hv)

/-- Standard coordinate dot product as a bilinear form. -/
def coordinateDot : LinearMap.BilinForm ℝ (Fin 3 → ℝ) :=
  dotProductBilin ℝ ℝ

private lemma coordinateDot_refl : coordinateDot.IsRefl := by
  intro x y h
  simpa [coordinateDot, dotProduct_comm] using h

private lemma coordinateDot_nondegenerate : coordinateDot.Nondegenerate := by
  constructor
  · intro x hx
    exact dotProduct_self_eq_zero.mp (hx x)
  · intro x hx
    exact dotProduct_self_eq_zero.mp (hx x)

/-- Positive eigenbasis parametrization by three real coordinates. -/
noncomputable def positiveParametrization : (Fin 3 → ℝ) →ₗ[ℝ] AmbientSpace :=
  Matrix.mulVecLin positiveEigenbasisMatrix

/-- Negative eigenbasis parametrization by three real coordinates. -/
noncomputable def negativeParametrization : (Fin 3 → ℝ) →ₗ[ℝ] AmbientSpace :=
  Matrix.mulVecLin negativeEigenbasisMatrix

/-- The last three coordinates in the ordered six-dimensional basis. -/
def lastThreeCoordinates : AmbientSpace →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x i := x (Fin.natAdd 3 i)
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

@[simp]
private lemma fin_addNat_zero_three :
    Fin.addNat (0 : Fin 3) 3 = (3 : Fin 6) := by
  decide

@[simp]
private lemma fin_addNat_one_three :
    Fin.addNat (1 : Fin 3) 3 = (4 : Fin 6) := by
  decide

@[simp]
private lemma fin_addNat_two_three :
    Fin.addNat (2 : Fin 3) 3 = (5 : Fin 6) := by
  decide

private lemma positiveParametrization_eigen (x : Fin 3 → ℝ) :
    hodgeEndomorphism (positiveParametrization x) =
      Real.sqrt 5 • positiveParametrization x := by
  ext i
  fin_cases i <;>
    norm_num [hodgeEndomorphism, hodgeMatrix, integralHodgeMatrix,
      positiveParametrization, positiveEigenbasisMatrix, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring_nf <;> norm_num [Real.sq_sqrt] <;> ring

private lemma negativeParametrization_eigen (x : Fin 3 → ℝ) :
    hodgeEndomorphism (negativeParametrization x) =
      -(Real.sqrt 5 • negativeParametrization x) := by
  ext i
  fin_cases i <;>
    norm_num [hodgeEndomorphism, hodgeMatrix, integralHodgeMatrix,
      negativeParametrization, negativeEigenbasisMatrix, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring_nf <;> norm_num [Real.sq_sqrt] <;> ring

private lemma lastThree_positiveParametrization (x : Fin 3 → ℝ) :
    lastThreeCoordinates (positiveParametrization x) = x := by
  ext i
  fin_cases i <;>
    norm_num [lastThreeCoordinates, positiveParametrization, positiveEigenbasisMatrix,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Fin.natAdd, Fin.addNat]; congr

private lemma lastThree_negativeParametrization (x : Fin 3 → ℝ) :
    lastThreeCoordinates (negativeParametrization x) = x := by
  ext i
  fin_cases i <;>
    norm_num [lastThreeCoordinates, negativeParametrization, negativeEigenbasisMatrix,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Fin.natAdd, Fin.addNat]; congr

private lemma positiveParametrization_reconstructs (x : V₃Space) :
    positiveParametrization (lastThreeCoordinates x.1) = x.1 := by
  have h := V₃Space_eigen x
  have h0 := congrFun h (0 : Fin 6)
  have h1 := congrFun h (1 : Fin 6)
  have h2 := congrFun h (2 : Fin 6)
  norm_num [hodgeEndomorphism, hodgeMatrix, integralHodgeMatrix,
    Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_two] at h0 h1 h2
  rw [show Fin.succ (2 : Fin 5) = (3 : Fin 6) by decide,
    show (Fin.succ (2 : Fin 4)).succ = (4 : Fin 6) by decide,
    show (Fin.succ (2 : Fin 3)).succ.succ = (5 : Fin 6) by decide] at h0 h1 h2
  have hw0 := congrArg (fun y : ℝ => Real.sqrt 5 * y) h0
  have hw1 := congrArg (fun y : ℝ => Real.sqrt 5 * y) h1
  have hw2 := congrArg (fun y : ℝ => Real.sqrt 5 * y) h2
  have hs0 := congrArg (fun y : ℝ => y * x.1 0) sqrt_five_square
  have hs1 := congrArg (fun y : ℝ => y * x.1 1) sqrt_five_square
  have hs2 := congrArg (fun y : ℝ => y * x.1 2) sqrt_five_square
  ext i
  fin_cases i <;>
    norm_num [positiveParametrization, positiveEigenbasisMatrix, lastThreeCoordinates,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · linear_combination (norm := ring_nf) 1 / 8 * h1 - 1 / 8 * h2 + 3 / 20 * hw0 +
      1 / 40 * hw1 + 1 / 40 * hw2 + 3 / 20 * hs0 + 1 / 40 * hs1 +
      1 / 40 * hs2
  · linear_combination (norm := ring_nf) -1 / 8 * h0 + 1 / 8 * h2 + 1 / 40 * hw0 +
      3 / 20 * hw1 + 1 / 40 * hw2 + 1 / 40 * hs0 + 3 / 20 * hs1 +
      1 / 40 * hs2
  · linear_combination (norm := ring_nf) 1 / 8 * h0 - 1 / 8 * h1 + 1 / 40 * hw0 +
      1 / 40 * hw1 + 3 / 20 * hw2 + 1 / 40 * hs0 + 1 / 40 * hs1 +
      3 / 20 * hs2
    apply sub_eq_zero.mpr
    congr
  all_goals congr

private lemma negativeParametrization_reconstructs (x : V₃PrimeSpace) :
    negativeParametrization (lastThreeCoordinates x.1) = x.1 := by
  have h := V₃PrimeSpace_eigen x
  have h0 := congrFun h (0 : Fin 6)
  have h1 := congrFun h (1 : Fin 6)
  have h2 := congrFun h (2 : Fin 6)
  norm_num [hodgeEndomorphism, hodgeMatrix, integralHodgeMatrix,
    Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_two] at h0 h1 h2
  rw [show Fin.succ (2 : Fin 5) = (3 : Fin 6) by decide,
    show (Fin.succ (2 : Fin 4)).succ = (4 : Fin 6) by decide,
    show (Fin.succ (2 : Fin 3)).succ.succ = (5 : Fin 6) by decide] at h0 h1 h2
  have hw0 := congrArg (fun y : ℝ => Real.sqrt 5 * y) h0
  have hw1 := congrArg (fun y : ℝ => Real.sqrt 5 * y) h1
  have hw2 := congrArg (fun y : ℝ => Real.sqrt 5 * y) h2
  have hs0 := congrArg (fun y : ℝ => y * x.1 0) sqrt_five_square
  have hs1 := congrArg (fun y : ℝ => y * x.1 1) sqrt_five_square
  have hs2 := congrArg (fun y : ℝ => y * x.1 2) sqrt_five_square
  ext i
  fin_cases i <;>
    norm_num [negativeParametrization, negativeEigenbasisMatrix, lastThreeCoordinates,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · linear_combination (norm := ring_nf) 1 / 8 * h1 - 1 / 8 * h2 - 3 / 20 * hw0 -
      1 / 40 * hw1 - 1 / 40 * hw2 + 3 / 20 * hs0 + 1 / 40 * hs1 +
      1 / 40 * hs2
  · linear_combination (norm := ring_nf) -1 / 8 * h0 + 1 / 8 * h2 - 1 / 40 * hw0 -
      3 / 20 * hw1 - 1 / 40 * hw2 + 1 / 40 * hs0 + 3 / 20 * hs1 +
      1 / 40 * hs2
  · linear_combination (norm := ring_nf) 1 / 8 * h0 - 1 / 8 * h1 - 1 / 40 * hw0 -
      1 / 40 * hw1 - 3 / 20 * hw2 + 1 / 40 * hs0 + 1 / 40 * hs1 +
      3 / 20 * hs2
    apply sub_eq_zero.mpr
    congr
  all_goals congr

/-- Last-three-coordinate map on the positive eigenspace. -/
noncomputable def V₃CoordinateMap : V₃Space →ₗ[ℝ] (Fin 3 → ℝ) :=
  lastThreeCoordinates.comp V₃Space.subtype

/-- Last-three-coordinate map on the negative eigenspace. -/
noncomputable def V₃PrimeCoordinateMap : V₃PrimeSpace →ₗ[ℝ] (Fin 3 → ℝ) :=
  lastThreeCoordinates.comp V₃PrimeSpace.subtype

/-- Explicit three-coordinate chart for `V₃`. -/
noncomputable def V₃Coordinates : V₃Space ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  LinearEquiv.ofBijective V₃CoordinateMap <| by
    constructor
    · intro x y h
      apply Subtype.ext
      rw [← positiveParametrization_reconstructs x,
        ← positiveParametrization_reconstructs y]
      exact congrArg positiveParametrization h
    · intro y
      refine ⟨⟨positiveParametrization y, ?_⟩, ?_⟩
      · change hodgeEndomorphism (positiveParametrization y) -
          Real.sqrt 5 • positiveParametrization y = 0
        rw [positiveParametrization_eigen, sub_self]
      · exact lastThree_positiveParametrization y

/-- Explicit three-coordinate chart for `V₃'`. -/
noncomputable def V₃PrimeCoordinates : V₃PrimeSpace ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  LinearEquiv.ofBijective V₃PrimeCoordinateMap <| by
    constructor
    · intro x y h
      apply Subtype.ext
      rw [← negativeParametrization_reconstructs x,
        ← negativeParametrization_reconstructs y]
      exact congrArg negativeParametrization h
    · intro y
      refine ⟨⟨negativeParametrization y, ?_⟩, ?_⟩
      · change hodgeEndomorphism (negativeParametrization y) +
          Real.sqrt 5 • negativeParametrization y = 0
        rw [negativeParametrization_eigen]
        module
      · exact lastThree_negativeParametrization y

private lemma V₃Coordinates_action (g : A5) (x : V₃Space) :
    V₃Coordinates (V₃ g x) =
      Matrix.mulVec (positiveActionMatrix g) (V₃Coordinates x) := by
  ext i
  change lastThreeCoordinates (coordinateExteriorSquare g x.1) i = _
  rw [coordinateExteriorSquare_apply]
  rw [← positiveParametrization_reconstructs x]
  rw [positiveActionMatrix_eq_geometric]
  change Matrix.mulVec (realWedgeActionMatrix g)
      (Matrix.mulVec positiveEigenbasisMatrix (lastThreeCoordinates x.1))
        (Fin.natAdd 3 i) = _
  rw [Matrix.mulVec_mulVec]
  rfl

private lemma V₃PrimeCoordinates_action (g : A5) (x : V₃PrimeSpace) :
    V₃PrimeCoordinates (V₃Prime g x) =
      Matrix.mulVec (negativeActionMatrix g) (V₃PrimeCoordinates x) := by
  ext i
  change lastThreeCoordinates (coordinateExteriorSquare g x.1) i = _
  rw [coordinateExteriorSquare_apply]
  rw [← negativeParametrization_reconstructs x]
  rw [negativeActionMatrix_eq_geometric]
  change Matrix.mulVec (realWedgeActionMatrix g)
      (Matrix.mulVec negativeEigenbasisMatrix (lastThreeCoordinates x.1))
        (Fin.natAdd 3 i) = _
  rw [Matrix.mulVec_mulVec]
  rfl

/-- The positive icosahedral summand is three-dimensional. -/
theorem V3_finrank : Module.finrank ℝ V₃Space = 3 := by
  rw [LinearEquiv.finrank_eq V₃Coordinates]
  simp

#print axioms V3_finrank

/-- The negative icosahedral summand is three-dimensional. -/
theorem V3Prime_finrank : Module.finrank ℝ V₃PrimeSpace = 3 := by
  rw [LinearEquiv.finrank_eq V₃PrimeCoordinates]
  simp

#print axioms V3Prime_finrank

private lemma irreducible_of_orbit_frame
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (rho : Representation ℝ A5 M)
    (chart : M ≃ₗ[ℝ] (Fin 3 → ℝ))
    (B : A5 → Matrix (Fin 3) (Fin 3) ℝ)
    (hAction : ∀ g x, chart (rho g x) = Matrix.mulVec (B g) (chart x))
    (hFrame : ∀ i j a b, ∑ g : A5, B g i a * B g j b =
      frameLeft i j * frameRight a b) :
    Representation.IsIrreducible rho := by
  letI : Nontrivial M := chart.toEquiv.nontrivial
  letI : Nontrivial (Subrepresentation rho) := ⟨⟨⊥, ⊤, by
    intro h
    have hm := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top hm⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hSmod : S.toSubmodule ≠ ⊥ := by
    intro h
    apply hS
    apply Subrepresentation.toSubmodule_injective
    exact h
  obtain ⟨v, hvS, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSmod
  let K := S.toSubmodule.map chart.toLinearMap
  have hvcoord : chart v ≠ 0 := by
    intro h
    apply hv
    exact chart.injective (by simpa using h)
  have horth : coordinateDot.orthogonal K = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    by_contra hy0
    have hpos := orbit_frame_pos B hFrame hy0 hvcoord
    have hzero : ∀ g : A5,
        dotProduct y (Matrix.mulVec (B g) (chart v)) = 0 := by
      intro g
      have horbitS := S.apply_mem_toSubmodule g hvS
      have horbitK : chart (rho g v) ∈ K :=
        Submodule.mem_map_of_mem horbitS
      have hortho := hy _ horbitK
      change dotProduct (chart (rho g v)) y = 0 at hortho
      rw [hAction] at hortho
      rw [dotProduct_comm]
      exact hortho
    simp [hzero] at hpos
  have hKtop : K = ⊤ := by
    have hdouble := coordinateDot.orthogonal_orthogonal
      coordinateDot_nondegenerate coordinateDot_refl K
    rw [horth] at hdouble
    simpa using hdouble.symm
  apply Subrepresentation.toSubmodule_injective
  ext x
  constructor
  · intro
    trivial
  · intro
    have hxK : chart x ∈ K := by
      rw [hKtop]
      trivial
    obtain ⟨y, hyS, hy⟩ := Submodule.mem_map.mp hxK
    have hyx : y = x := chart.injective hy
    simpa [hyx] using hyS

/-- The positive three-dimensional icosahedral representation is irreducible. -/
theorem V3_irreducible : Representation.IsIrreducible V₃ :=
  irreducible_of_orbit_frame V₃ V₃Coordinates positiveActionMatrix
    V₃Coordinates_action positive_frame_coefficients

#print axioms V3_irreducible

/-- The negative three-dimensional icosahedral representation is irreducible. -/
theorem V3Prime_irreducible : Representation.IsIrreducible V₃Prime :=
  irreducible_of_orbit_frame V₃Prime V₃PrimeCoordinates negativeActionMatrix
    V₃PrimeCoordinates_action negative_frame_coefficients

#print axioms V3Prime_irreducible

/-- The two irreducible threes are the conjugate real embeddings of one exact action. -/
theorem V3_V3Prime_galois_conjugate :
    RepresentationsAreQ5GaloisConjugate
      V₃ V₃Prime V₃Coordinates V₃PrimeCoordinates := by
  refine ⟨q5PositiveActionMatrix, ?_, ?_⟩
  · intro g x
    rw [V₃Coordinates_action, positiveActionMatrix_eq_q5]
  · intro g x
    rw [V₃PrimeCoordinates_action, negativeActionMatrix_eq_q5]

#print axioms V3_V3Prime_galois_conjugate

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

/-- The exterior square of the centered `A₅` representation splits into the two threes. -/
theorem exteriorSquareV4_equiv_V3_prod_V3Prime :
    Nonempty (exteriorSquareV₄.Equiv (V₃.prod V₃Prime)) :=
  ⟨exteriorSquareDecomposition⟩

#print axioms exteriorSquareV4_equiv_V3_prod_V3Prime

/-- The full fivefold second-order decomposition theorem, including its source qualifiers. -/
theorem exteriorSquareV4_three_plus_three :
    Nonempty (exteriorSquareV₄.Equiv (V₃.prod V₃Prime)) ∧
      Module.finrank ℝ V₃Space = 3 ∧
      Module.finrank ℝ V₃PrimeSpace = 3 ∧
      Representation.IsIrreducible V₃ ∧
      Representation.IsIrreducible V₃Prime ∧
      RepresentationsAreQ5GaloisConjugate
        V₃ V₃Prime V₃Coordinates V₃PrimeCoordinates := by
  exact ⟨exteriorSquareV4_equiv_V3_prod_V3Prime, V3_finrank,
    V3Prime_finrank, V3_irreducible, V3Prime_irreducible,
    V3_V3Prime_galois_conjugate⟩

#print axioms exteriorSquareV4_three_plus_three

-- Degenerate probes: the fixed action respects the identity and the split sends zero to zero.
example : exteriorSquareV₄ 1 = LinearMap.id := map_one exteriorSquareV₄

example : exteriorSquareDecomposition 0 = 0 :=
  map_zero exteriorSquareDecomposition

end D5.S3.Factorization.Icosahedral.ExteriorSquareThreePlusThree
