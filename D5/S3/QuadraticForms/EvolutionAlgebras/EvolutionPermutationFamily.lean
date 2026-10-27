/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/EvolutionPermutationFamily
   mirror-E: none(waiver:general-permutation-family)
   anchors: []
   utility: none
   digest: Coefficient-one permutation evolution products realize their complete diagonal kernel and permutation centralizer. -/


/- Escape audit unfinished for permutationLinear_basis, permutation_mixed, permutation_support:
https://github.com/the-omega-institute/trureturing/issues/22095 -/
import D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily
import D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionSharpBound

/-! Full bilinear evolution automorphisms, their sharp bound, and attaining products. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily

open D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
open D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily
open D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl
open D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionSharpBound
open D5.S3.FiniteGroups.SuccessorQuotient
open D5.S3.FiniteGroups.SuccessorPowerAssignments
open D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight

/-- Reindex coordinates so that the i-th basis vector goes to the σ(i)-th. -/
noncomputable def permutationLinear {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Coord n ≃ₗ[ℂ] Coord n := LinearEquiv.funCongrLeft ℂ ℂ σ.symm

/-- The coefficient-one evolution product with e_i squared equal to e_(σ i). -/
noncomputable def permutationProduct {n : ℕ} (σ : Equiv.Perm (Fin n)) : Product n :=
  coordinateProduct (permutationLinear σ).toLinearMap

theorem permutationLinear_basis {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permutationLinear σ (Pi.basisFun ℂ (Fin n) i) = Pi.basisFun ℂ (Fin n) (σ i) := by
  classical
  ext j
  simp [permutationLinear, Pi.basisFun_apply, Pi.single_apply,
    Equiv.eq_symm_apply, eq_comm]

private theorem permutation_square {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permutationProduct σ (Pi.basisFun ℂ (Fin n) i) (Pi.basisFun ℂ (Fin n) i) =
      Pi.basisFun ℂ (Fin n) (σ i) := by
  change permutationLinear σ (_ * _) = _
  have he : (Pi.basisFun ℂ (Fin n) i : Coord n) * Pi.basisFun ℂ (Fin n) i =
      Pi.basisFun ℂ (Fin n) i := by
    ext j
    simp [Pi.basisFun_apply, Pi.single_apply]
  rw [he, permutationLinear_basis]

theorem permutation_mixed {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i j : Fin n) (hij : i ≠ j) :
    permutationProduct σ (Pi.basisFun ℂ (Fin n) i) (Pi.basisFun ℂ (Fin n) j) = 0 := by
  change permutationLinear σ (_ * _) = 0
  have he : (Pi.basisFun ℂ (Fin n) i : Coord n) * Pi.basisFun ℂ (Fin n) j = 0 := by
    ext k
    by_cases hi : k = i
    · subst k
      simp [Pi.basisFun_apply, Pi.single_apply, hij]
    · simp [Pi.basisFun_apply, Pi.single_apply, hi]
  rw [he, map_zero]

private theorem permutation_perfect {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    perfect (permutationProduct σ) := by
  exact (coordinate_product_square (permutationLinear σ).toLinearMap).trans
    (permutationLinear σ).range

theorem permutation_support {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    supportRelation (permutationProduct σ) (Pi.basisFun ℂ (Fin n)) i j ↔ j = σ i := by
  classical
  unfold supportRelation structureCoefficient squareVector
  rw [permutation_square]
  simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]

private noncomputable def permutationRho {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Aut (permutationProduct σ) →* Equiv.Perm (Fin n) :=
  rho (permutationProduct σ) (Pi.basisFun ℂ (Fin n)) (permutation_mixed σ)
    (permutation_perfect σ)

/-- Every permutation commuting with σ lifts to an actual multiplication automorphism. -/
noncomputable def centralizerLift {n : ℕ} (σ : Equiv.Perm (Fin n))
    (τ : Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n)))) :
    Aut (permutationProduct σ) := by
  refine ⟨permutationLinear τ.val, ?_⟩
  intro x y
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp τ.property
  have hinv : τ.val.symm * σ.symm = σ.symm * τ.val.symm := by
    simpa only [mul_inv_rev, Equiv.Perm.inv_def] using (congrArg Inv.inv hcomm).symm
  ext j
  change (x (σ.symm (τ.val.symm j)) * y (σ.symm (τ.val.symm j))) =
    x (τ.val.symm (σ.symm j)) * y (τ.val.symm (σ.symm j))
  have h := congrArg (fun p : Equiv.Perm (Fin n) => p j) hinv
  change τ.val.symm (σ.symm j) = σ.symm (τ.val.symm j) at h
  rw [h]

private theorem lift_rho {n : ℕ} (σ : Equiv.Perm (Fin n))
    (τ : Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n)))) :
    permutationRho σ (centralizerLift σ τ) = τ.val := by
  classical
  let d := monomialData (permutationProduct σ) (Pi.basisFun ℂ (Fin n))
    (permutation_mixed σ) (permutation_perfect σ) (centralizerLift σ τ)
  apply Equiv.ext
  intro i
  change d.perm i = τ.val i
  have hi := d.image i
  change permutationLinear τ.val (Pi.basisFun ℂ (Fin n) i) =
    d.scalar i • Pi.basisFun ℂ (Fin n) (d.perm i) at hi
  rw [permutationLinear_basis] at hi
  exact ((Pi.basisFun ℂ (Fin n)).linearIndependent.eq_of_smul_apply_eq_smul_apply
    (1 : ℂ) (d.scalar i) (τ.val i) (d.perm i) one_ne_zero (by simpa using hi)).symm

private theorem permutation_range {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (permutationRho σ).range = Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n))) := by
  classical
  apply le_antisymm
  · rintro τ ⟨f, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Equiv.ext
    intro i
    change (permutationRho σ f) (σ i) = σ ((permutationRho σ f) i)
    have h := (monomialData (permutationProduct σ) (Pi.basisFun ℂ (Fin n))
      (permutation_mixed σ) (permutation_perfect σ) f).support i (σ i)
    have h' := h.mp ((permutation_support σ i (σ i)).mpr rfl)
    exact (permutation_support σ _ _).mp h'
  · intro τ hτ
    exact ⟨centralizerLift σ ⟨τ,hτ⟩, lift_rho σ ⟨τ,hτ⟩⟩

private noncomputable def assignmentSquareEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Assignments (supportRelation (permutationProduct σ) (Pi.basisFun ℂ (Fin n)))
      (fun z : ℂˣ => z ^ 2) ≃ SquareAssignments (K := ℂ) σ where
  toFun t := ⟨t.val, fun i => t.property i (σ i) ((permutation_support σ i (σ i)).mpr rfl)⟩
  invFun t := ⟨t.val, by
    intro i j hij
    rw [(permutation_support σ i j).mp hij]
    exact t.property i⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact full group order, from its actual kernel, actual image, and explicit lifts. -/
theorem permutation_aut_card {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Finite (Aut (permutationProduct σ)) ∧
      Nat.card (Aut (permutationProduct σ)) = weight σ.partition.parts := by
  classical
  haveI : Finite (Aut (permutationProduct σ)) :=
    automorphism_finite (permutationProduct σ) (Pi.basisFun ℂ (Fin n))
      (permutation_mixed σ) (permutation_perfect σ)
  refine ⟨inferInstance, ?_⟩
  rw [← Subgroup.card_ker_mul_card_range (permutationRho σ), permutation_range]
  have hk : Nat.card (permutationRho σ).ker = cycleWeight σ := by
    change Nat.card (rho (permutationProduct σ) (Pi.basisFun ℂ (Fin n))
      (permutation_mixed σ) (permutation_perfect σ)).ker = cycleWeight σ
    rw [Nat.card_congr (kernelAssignmentEquiv (permutationProduct σ)
      (Pi.basisFun ℂ (Fin n)) (permutation_mixed σ) (permutation_perfect σ)),
      Nat.card_congr (assignmentSquareEquiv σ), square_assignments_weight_card]
  rw [hk, cycle_weight_centralizer]

/-- These witnesses retain commutativity, naturality, and perfection of all pair products. -/
theorem permutation_family {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    commutative (permutationProduct σ) ∧ hasNaturalBasis (permutationProduct σ) ∧
      perfect (permutationProduct σ) ∧ Finite (Aut (permutationProduct σ)) ∧
      Nat.card (Aut (permutationProduct σ)) = weight σ.partition.parts := by
  refine ⟨?_, coordinate_product_natural _, permutation_perfect σ, permutation_aut_card σ⟩
  intro x y
  change permutationLinear σ (x * y) = permutationLinear σ (y * x)
  rw [mul_comm]

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily
