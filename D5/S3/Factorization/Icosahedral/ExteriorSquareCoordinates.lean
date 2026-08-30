/- GID: D5/S3/Factorization/Icosahedral/ExteriorSquareCoordinates
   generality: I
   mirror-B: D5/B/S3/Factorization/Icosahedral/ExteriorSquareCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Centered A5 coordinates realize its exterior square, including zero and degree zero. -/

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
   * Repository searches found no prior centered A5 exterior-square coordinate transport.
   * Pinned Mathlib supplies `exteriorPower.map` and `Module.Basis.exteriorPower`, reused here.
   * Pinned Mathlib has no exterior-power representation wrapper; this file supplies it and
     reuses the unique Hodge matrix from `ExactDualLatticeFormula` rather than copying it.
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

lemma coordinateExteriorSquare_apply (g : A5) :
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

#print axioms coordinateExteriorSquare_apply

/-- The reused Hodge discriminant matrix as a real linear endomorphism. -/
noncomputable def hodgeEndomorphism : AmbientSpace →ₗ[ℝ] AmbientSpace :=
  Matrix.mulVecLin hodgeMatrix


-- Degenerate probes for the zero vector and degree-zero exterior-power action.
example : coordinateSum 0 = 0 := map_zero coordinateSum

example : exteriorPowerRepresentation 0 V₄ 1 = LinearMap.id :=
  map_one (exteriorPowerRepresentation 0 V₄)

-- The structural instances exclude genuinely empty group and module carriers.
example {G : Type*} [Monoid G] : Nonempty G := ⟨1⟩

example {M : Type*} [AddCommGroup M] : Nonempty M := ⟨0⟩

-- The empty coordinate family is a singleton module, and its trivial action is valid at n = 0.
example (x y : Fin 0 → ℝ) : x = y := by
  ext i
  exact Fin.elim0 i

example :
    exteriorPowerRepresentation 0 (Representation.trivial ℝ Unit (Fin 0 → ℝ)) 1 =
      LinearMap.id :=
  map_one (exteriorPowerRepresentation 0 (Representation.trivial ℝ Unit (Fin 0 → ℝ)))

end D5.S3.Factorization.Icosahedral.ExteriorSquareThreePlusThree
