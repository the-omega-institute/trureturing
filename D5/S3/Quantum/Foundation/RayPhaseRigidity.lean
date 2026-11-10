/- GID: D5/S3/Quantum/Foundation/RayPhaseRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/RayPhaseRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ray rigidity; atom 3702db2486a73bbef7dfe05f2d409f45820b15e5114b6a8119c255462339f23a. -/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith

/-!
# Finite ray tests for unitary phase rigidity

Source: AURIC_EXISTENTIAL_QUANTIFIERS_CIRCUIT_SEMIRINGS_AND_QUANTUM_RECORDS_V14,
Proposition 7.6, atom
3702db2486a73bbef7dfe05f2d409f45820b15e5114b6a8119c255462339f23a.

Scope: complex matrices indexed by any finite type, including the empty type.
The theorem needs only the coordinate rays and a family of test rays whose
supports connect all coordinates by chains of overlaps. No single test vector
needs full support. One all-ones test is a special case, so the theorem supplies
the all-rays premise in the source's relative-unitary argument. The scalar has
norm one. The atom's commentary about CP branches and computational semantics
is outside this linear-algebra theorem.

Mathlib's `LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent` handles
all-vector collinearity. The repository's `sparse_probe_coercivity` gives a
quantitative bound for one normalized full-support vector. Neither supplies the
support-chain conclusion for a family with no full-support member.

admission_basis: escape-witness
proof_shape: coordinate_shape_of_connected_ray_tests: content
proof_shape: unitary_phase_of_connected_ray_tests: content
escape_witness: coordinate_shape_of_connected_ray_tests proves propagation of the
diagonal coefficient across support chains,
on the live path to the explicit scalar-matrix construction. There are no D5
prerequisites. The proof uses coordinate-line invariance, compares coefficients
within each test support, and inducts along chains to obtain global scalarity.
-/

set_option autoImplicit false
noncomputable section
open Matrix

namespace D5.S3.Quantum.Foundation.RayPhaseRigidity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The image of a vector lies in its complex line. At zero this is automatic. -/
def PreservesRay (A : Matrix ι ι ℂ) (x : ι → ℂ) : Prop :=
  A *ᵥ x ∈ Submodule.span ℂ {x}

/-- Test supports connect two coordinates when they can be joined by a chain
of tests that are nonzero at both consecutive coordinates. -/
def RaySupportConnected (tests : Set (ι → ℂ)) : Prop :=
  ∀ i j : ι, Relation.ReflTransGen
    (fun i j => ∃ x ∈ tests, x i ≠ 0 ∧ x j ≠ 0) i j

private theorem coordinate_shape_of_connected_ray_tests
    (A : Matrix ι ι ℂ) (hcoord : ∀ i : ι, PreservesRay A (Pi.single i 1))
    (tests : Set (ι → ℂ)) (htests : ∀ x ∈ tests, PreservesRay A x)
    (hconnect : RaySupportConnected tests) :
    (∀ i j : ι, i ≠ j → A i j = 0) ∧ (∀ i j : ι, A i i = A j j) := by
  classical
  have hoff : ∀ i j : ι, i ≠ j → A i j = 0 := by
    intro i j hij
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (hcoord j)
    have he := congrFun hd i
    simpa [Matrix.mulVec_single_one, Pi.single_apply, hij, Ne.symm hij] using he.symm
  have hstep (i j : ι) (hij : ∃ x ∈ tests, x i ≠ 0 ∧ x j ≠ 0) :
      A i i = A j j := by
    obtain ⟨x, hx, hi, hj⟩ := hij
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (htests x hx)
    have hcoeff (k : ι) (hk : x k ≠ 0) : A k k = d := by
      have he := congrFun hd k
      have hsum : (A *ᵥ x) k = A k k * x k := by
        simp only [Matrix.mulVec, dotProduct]
        exact Finset.sum_eq_single k
          (fun j _ hjk => by rw [hoff k j (Ne.symm hjk), zero_mul])
          (fun hk => (hk (Finset.mem_univ k)).elim)
      have hm : d * x k = A k k * x k := by simpa [hsum] using he
      exact (mul_right_cancel₀ hk hm).symm
    exact (hcoeff i hi).trans (hcoeff j hj).symm
  have hchain {i j : ι} (hij : Relation.ReflTransGen
      (fun i j => ∃ x ∈ tests, x i ≠ 0 ∧ x j ≠ 0) i j) : A i i = A j j := by
    induction hij with
    | refl => rfl
    | @tail j k _ hjk ih => exact ih.trans (hstep j k hjk)
  exact ⟨hoff, fun i j => hchain (hconnect i j)⟩

/-- Coordinate rays and any support-connected family of invariant rays force
a unitary to be a single global phase, even in dimension zero. -/
theorem unitary_phase_of_connected_ray_tests
    (A : Matrix ι ι ℂ) (hA : A ∈ Matrix.unitaryGroup ι ℂ)
    (hcoord : ∀ i : ι, PreservesRay A (Pi.single i 1))
    (tests : Set (ι → ℂ)) (htests : ∀ x ∈ tests, PreservesRay A x)
    (hconnect : RaySupportConnected tests) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ A = c • (1 : Matrix ι ι ℂ) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
    exact ⟨1, norm_one, Subsingleton.elim _ _⟩
  | inr hnonempty =>
    obtain ⟨hoff, heq⟩ := coordinate_shape_of_connected_ray_tests A hcoord tests htests hconnect
    let base : ι := Classical.choice hnonempty
    let c : ℂ := A base base
    have hdiag (i : ι) : A i i = c := heq i base
    have hscalar : A = c • (1 : Matrix ι ι ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [hdiag]
      · simp [hoff i j hij, hij]
    refine ⟨c, ?_, hscalar⟩
    have hunit := Matrix.mem_unitaryGroup_iff'.mp hA
    rw [hscalar] at hunit
    have he := congrArg (fun B : Matrix ι ι ℂ => B base base) hunit
    have hprod : star c * c = 1 := by
      simpa [star_smul, Matrix.mul_smul, Matrix.smul_mul, mul_comm] using he
    have hn := congrArg norm hprod
    simp only [norm_mul, norm_star, norm_one] at hn
    nlinarith [norm_nonneg c]

end D5.S3.Quantum.Foundation.RayPhaseRigidity
