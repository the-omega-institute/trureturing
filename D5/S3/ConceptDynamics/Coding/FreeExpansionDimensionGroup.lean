/- GID: D5/S3/ConceptDynamics/Coding/FreeExpansionDimensionGroup
   generality: G
   utility: exact inertness criterion for the actual free-expansion dimension group
   digest: The ordered integer adjacency identifies the original H-action on its stationary colimit, and finite-stage exactness equates inertness with positive natural uniformization.
-/
import D5.S3.HomologicalAlgebra.StationaryColimitAction
import D5.S3.FiniteGroups.NaturalGroupMatrixUniformization
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Matrix
open Module
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
open D5.S3.HomologicalAlgebra.StationaryColimitAction
  (StationaryModule induced finite_family_inert_iff_eventual)
open D5.S3.FiniteGroups.NaturalGroupMatrixUniformization

namespace D5.S3.ConceptDynamics.Coding.FreeExpansionDimensionGroup

variable {H : Type*} [Group H] [Fintype H] {n : ℕ}

abbrev VertexModule (H : Type*) [Group H] (n : ℕ) := Fin n → MonoidAlgebra ℤ H

def integerMatrix : GroupMat H n n →+* Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ H) :=
  (MonoidAlgebra.mapRingHom H (Nat.castRingHom ℤ)).mapMatrix

/-- Row adjacency on the actual free abelian group of vertices (i,h). -/
def transition (A : GroupMat H n n) : Module.End ℤ (VertexModule H n) :=
  (integerMatrix A).toLinearMapRight'.restrictScalars ℤ

/-- Original left action on the group coordinate, preserving the base vertex. -/
def leftTranslation (g : H) : Module.End ℤ (VertexModule H n) where
  toFun v i := MonoidAlgebra.single g 1 * v i
  map_add' v w := by funext i; exact mul_add _ _ _
  map_smul' c v := by
    funext i
    change MonoidAlgebra.single g 1 * (c • v i) = c • (MonoidAlgebra.single g 1 * v i)
    exact mul_smul_comm _ _ _

private theorem action_commutes (A : GroupMat H n n) (g : H) :
    Commute (leftTranslation (n := n) g) (transition A) := by
  change leftTranslation g * transition A = transition A * leftTranslation g
  apply LinearMap.ext
  intro v
  exact ((integerMatrix A).toLinearMapRight'.map_smul (MonoidAlgebra.single g 1) v).symm

/-- The stationary group of the actual integer free-expansion adjacency. -/
abbrev DimensionGroup (A : GroupMat H n n) := StationaryModule (transition A)

/-- The original left H-action induced on the stationary group. -/
def groupAction (A : GroupMat H n n) (g : H) : Module.End ℤ (DimensionGroup A) :=
  induced (transition A) (leftTranslation g) (action_commutes A g)

/-- Inertness is identity of the actual induced action, not a power condition. -/
def Inert (A : GroupMat H n n) : Prop :=
  ∀ g : H, groupAction A g = LinearMap.id

def vertexBasis : Basis (Σ _ : Fin n, H) ℤ (VertexModule H n) :=
  Pi.basis fun _ : Fin n => MonoidAlgebra.basis H ℤ

def vertex (i : Fin n) (h : H) : VertexModule H n :=
  Pi.single i (MonoidAlgebra.single h 1)

private theorem vertexBasis_apply (i : Fin n) (h : H) :
    vertexBasis (H := H) (n := n) ⟨i,h⟩ = vertex i h := by
  simp only [vertexBasis, Pi.basis_apply, MonoidAlgebra.basis_apply, vertex]

private theorem translate_vertex (g h : H) (i : Fin n) :
    leftTranslation g (vertex i h) = vertex i (g*h) := by
  classical
  ext j t
  by_cases hij : i = j
  · subst j
    simp [leftTranslation, vertex, MonoidAlgebra.single_mul_single]
  · simp [leftTranslation, vertex, Pi.single_eq_of_ne (Ne.symm hij)]

private theorem transition_power (A : GroupMat H n n) (k : ℕ) (v : VertexModule H n) :
    ((transition A)^k) v = v ᵥ* integerMatrix (A^k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      change (v ᵥ* integerMatrix (A^k)) ᵥ* integerMatrix A =
        v ᵥ* integerMatrix (A^(k+1))
      rw [Matrix.vecMul_vecMul, ← map_mul, ← pow_succ]

/-- Exact adjacency-coordinate identification: from (i,h), a label s reaches
(j,h*s). The inverse and multiplication order are fixed even when H is nonabelian. -/
theorem actual_expansion_adjacency (A : GroupMat H n n) (i j : Fin n) (h t : H) :
    ((transition A (vertex i h)) j).coeff t = ((A i j).coeff (h⁻¹*t) : ℤ) := by
  classical
  change ((Pi.single i (MonoidAlgebra.single h 1) ᵥ* integerMatrix A) j).coeff t = _
  rw [Matrix.single_vecMul]
  simp [integerMatrix, Matrix.row, MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_mapRingHom]

private theorem vertex_mul_coeff (C : GroupMat H n n) (i j : Fin n) (h t : H) :
    ((vertex i h ᵥ* integerMatrix C) j).coeff t = ((C i j).coeff (h⁻¹*t) : ℤ) :=
  actual_expansion_adjacency C i j h t

private theorem stage_implies_uniform (A : GroupMat H n n) {N : ℕ}
    (hN : ∀ g : H, (transition A)^N * leftTranslation g = (transition A)^N) :
    UniformMatrix (A^N) := by
  intro i j t
  have hv := congrArg
    (fun F : Module.End ℤ (VertexModule H n) => ((F (vertex i 1)) j).coeff 1)
    (hN (t⁻¹))
  simp only [Module.End.mul_apply, translate_vertex, mul_one,
    transition_power, vertex_mul_coeff, inv_inv, inv_one, one_mul] at hv
  exact_mod_cast hv

private theorem uniform_implies_stage (A : GroupMat H n n) {N : ℕ}
    (hN : UniformMatrix (A^N)) (g : H) :
    (transition A)^N * leftTranslation g = (transition A)^N := by
  apply (vertexBasis (H := H) (n := n)).ext
  rintro ⟨i,h⟩
  rw [vertexBasis_apply]
  ext j t
  simp only [Module.End.mul_apply, translate_vertex, transition_power, vertex_mul_coeff]
  rw [hN i j ((g*h)⁻¹*t), hN i j (h⁻¹*t)]

/-- The original H-action is inert exactly when a positive power has constant
group coefficients. A finite basis and finite H provide one common stage. -/
theorem inert_iff_uniformizes (A : GroupMat H n n) : Inert A ↔ Uniformizes A := by
  have hfinite := finite_family_inert_iff_eventual
    (vertexBasis (H := H) (n := n)) (transition A) (leftTranslation (n := n))
    (action_commutes A)
  constructor
  · intro hinert
    obtain ⟨N,hN⟩ := hfinite.mp hinert
    refine ⟨N+1, Nat.succ_pos N, ?_⟩
    exact uniform_power_mono A (Nat.le_succ N) (stage_implies_uniform A hN)
  · rintro ⟨N,hNpos,hN⟩
    exact hfinite.mpr ⟨N,uniform_implies_stage A hN⟩

end D5.S3.ConceptDynamics.Coding.FreeExpansionDimensionGroup
