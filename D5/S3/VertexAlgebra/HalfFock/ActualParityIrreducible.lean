/- GID: D5/S3/VertexAlgebra/HalfFock/ActualParityIrreducible
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/ActualParityIrreducible
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-source physical modes act irreducibly on each entire actual parity sector. -/

/- proof_shape: fixedParitySlice_irreducible: content
admission_basis: escape-witness
escape_witness: A finite triangular Borcherds induction puts every ordered product
in the span of its original source iterates. Applied to even/odd source pairs,
it makes the sector submodule plus its odd images stable under every full-field
coefficient, while opposite target parity recovers the original intersection.
Classical order-two twisted lattice module irreducibility; no novelty claim. -/
import D5.S3.VertexAlgebra.HalfFock.ActualFieldIrreducible
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.FirstSourceClosure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.HalfFock.ActualParityIrreducible
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeAllStateField
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockPhysicalRescaling LatticeHalfFockGroundRightCurrentTransport
open LatticeHalfFockGroundRightCurrentTransport.Calculus
open LatticeInvolution LatticeHalfFockParityT LatticeHalfFockParityField

open private upper high from D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue

/-- Finite triangular elimination uses the actual truncations at the same vector.
The second family vanishes and the non-leading first terms have smaller distance
from B's cutoff. All signed modes and the original finite supports are retained. -/
private theorem product_mem_of_iterates {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B : VertexOperator ℂ M) (U : ℤ → VertexOperator ℂ M) (gamma : ℤ)
    (law : fullLaw A B U gamma) (W : Submodule ℂ M) (w : M)
    (iterates : ∀ r k : ℤ, ((U r)[[k]]) w ∈ W) (m n : ℤ) :
    (A[[m]]) ((B[[n]]) w) ∈ W := by
  classical
  let K := upper B w
  have inductionStep : ∀ d : ℕ, ∀ n : ℤ, ((K : ℤ)-n).toNat = d →
      ∀ m : ℤ, (A[[m]]) ((B[[n]]) w) ∈ W := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro n distance m
      by_cases outside : (K : ℤ) ≤ n
      · rw [high B w n outside, map_zero]
        exact W.zero_mem
      let l : ℤ := upper A w
      let r := m-l
      obtain ⟨leftFinite, firstFinite, secondFinite, identity⟩ := law l n r w
      have secondZero (j : ℕ) : secondTerm A B l n r w j = 0 := by
        simp only [secondTerm, high A w (l+j) (by dsimp [l]; omega),
          map_zero, smul_zero]
      have secondSum : (∑ᶠ j : ℕ, secondTerm A B l n r w j) = 0 :=
        finsum_eq_zero_of_forall_eq_zero secondZero
      have leftMem : (∑ᶠ j : ℕ, leftTerm U gamma l n r w j) ∈ W := by
        rw [finsum_eq_sum_of_support_subset _ leftFinite.coe_toFinset.ge]
        apply W.sum_mem
        intro j hj
        exact W.smul_mem _ (iterates _ _)
      rw [secondSum, sub_zero] at identity
      rw [identity] at leftMem
      let F := insert 0 firstFinite.toFinset
      have firstSum : (∑ᶠ j : ℕ, firstTerm A B l n r w j) =
          ∑ j ∈ F, firstTerm A B l n r w j := by
        apply finsum_eq_sum_of_support_subset
        exact firstFinite.coe_toFinset.ge.trans (by intro j hj; exact Finset.mem_insert_of_mem hj)
      rw [firstSum] at leftMem
      have tailMem : (∑ j ∈ F.erase 0, firstTerm A B l n r w j) ∈ W := by
        apply W.sum_mem
        intro j hj
        have nonzero : j ≠ 0 := (Finset.mem_erase.mp hj).1
        have smaller : ((K : ℤ)-(n+j)).toNat < d := by omega
        have term := ih _ smaller (n+j) rfl (m-j)
        have indices : l+r-j = m-j := by dsimp [r]; omega
        simpa only [firstTerm, indices] using W.smul_mem (residueWeight r j) term
      have leading := W.sub_mem leftMem tailMem
      rw [Finset.sum_erase_add F _ (Finset.mem_insert_self 0 firstFinite.toFinset)] at leading
      simpa [firstTerm, residueWeight, r] using leading
  exact inductionStep _ n rfl m

end D5.S3.VertexAlgebra.HalfFock.ActualParityIrreducible
