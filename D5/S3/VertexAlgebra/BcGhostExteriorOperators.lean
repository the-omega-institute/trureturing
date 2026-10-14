/- GID: D5/S3/VertexAlgebra/BcGhostExteriorOperators
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostExteriorOperators
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exterior coordinates identify signed ghost creation and annihilation on every state. -/

import D5.S3.VertexAlgebra.BcGhostFockSupport
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostExteriorOperators

noncomputable section

open D5.S3.VertexAlgebra.BcGhostFockSupport

variable {K : Type*} [CommRing K]

abbrev OneParticle (K : Type*) [CommRing K] := ℕ →₀ K
abbrev Exterior (K : Type*) [CommRing K] := ExteriorAlgebra K (OneParticle K)

def exteriorBasis : Module.Basis (Finset ℕ) K (Exterior K) :=
  (Finsupp.basisSingleOne : Module.Basis ℕ K (OneParticle K)).ExteriorAlgebra

/-- Coordinates on the full infinite algebraic Fock space. -/
def exteriorCoordinates : Fock K ≃ₗ[K] Exterior K := exteriorBasis.repr.symm

private def generator (i : ℕ) : Exterior K :=
  ExteriorAlgebra.ι K (Finsupp.single i 1)

private def word (l : List ℕ) : Exterior K := (l.map (generator (K := K))).prod

private theorem exteriorBasis_word (S : Finset ℕ) :
    exteriorBasis (K := K) S = word (S.sort) := by
  rw [exteriorBasis, ExteriorAlgebra.basis_apply_ofCard _ (rfl : S.card = S.card)]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, Finsupp.coe_basisSingleOne]
  unfold word generator
  congr 1
  change List.ofFn ((fun i => ExteriorAlgebra.ι K (Finsupp.single i (1 : K))) ∘
    (S.orderEmbOfFin rfl)) = _
  rw [← List.map_ofFn, List.ofFn_eq_map]
  rw [Finset.listMap_orderEmbOfFin_finRange]

private theorem exteriorBasis_empty : exteriorBasis (K := K) ∅ = 1 := by
  simp [exteriorBasis_word, word]

private theorem exteriorBasis_insert_min (a : ℕ) (S : Finset ℕ)
    (ha : ∀ x ∈ S, a < x) :
    exteriorBasis (K := K) (insert a S) = generator a * exteriorBasis S := by
  have hnot : a ∉ S := fun h => (lt_irrefl a) (ha a h)
  rw [exteriorBasis_word, Finset.sort_insert (· ≤ ·) (fun x hx => (ha x hx).le) hnot,
    exteriorBasis_word]
  simp [word]

private theorem sign_of_le_all (i : ℕ) (S : Finset ℕ) (h : ∀ x ∈ S, i ≤ x) :
    sign (K := K) i S = 1 := by
  have he : S.filter (fun x => x < i) = ∅ := by
    apply Finset.filter_false_of_mem
    intro x hx
    exact not_lt.mpr (h x hx)
  simp [sign, he]

private theorem sign_insert_lt (a i : ℕ) (S : Finset ℕ) (ha : a ∉ S) (hai : a < i) :
    sign (K := K) i (insert a S) = -sign i S := by
  simp [sign, Finset.filter_insert, hai, ha, pow_succ, mul_comm]

private theorem generator_swap (a i : ℕ) (x : Exterior K) :
    generator i * (generator a * x) = -(generator a * (generator i * x)) := by
  have h := ExteriorAlgebra.ι_add_mul_swap (R := K)
    (Finsupp.single i (1 : K)) (Finsupp.single a (1 : K))
  change generator i * generator a + generator a * generator i = 0 at h
  rw [← mul_assoc, eq_neg_of_add_eq_zero_left h, neg_mul, mul_assoc]

private theorem generator_basis (S : Finset ℕ) (i : ℕ) :
    generator (K := K) i * exteriorBasis S =
      if i ∈ S then 0 else sign (K := K) i S • exteriorBasis (K := K) (insert i S) := by
  induction S using Finset.induction_on_min generalizing i with
  | empty =>
      rw [exteriorBasis_insert_min i ∅ (by simp)]
      simp [exteriorBasis_empty, sign]
  | @insert a S ha ih =>
    have hnot : a ∉ S := fun h => (lt_irrefl a) (ha a h)
    rw [exteriorBasis_insert_min a S ha]
    by_cases hia : i = a
    · subst i
      rw [← mul_assoc]
      simp [generator]
    · by_cases hil : i < a
      · have hin : i ∉ insert a S := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨hia, fun h => (not_lt_of_ge hil.le) (ha i h)⟩
        rw [if_neg hin, sign_of_le_all i (insert a S) (by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hil.le
          · exact (hil.trans (ha x hx)).le), one_smul,
          exteriorBasis_insert_min i (insert a S) (by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hil
            · exact hil.trans (ha x hx)), exteriorBasis_insert_min a S ha]
      · have hai : a < i := by omega
        rw [generator_swap, ih]
        by_cases his : i ∈ S
        · simp [his]
        · have hmin : ∀ x ∈ insert i S, a < x := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hai
            · exact ha x hx
          simp only [his, if_false, Finset.mem_insert, hia, or_self]
          rw [sign_insert_lt a i S hnot hai, Finset.insert_comm i a,
            exteriorBasis_insert_min a (insert i S) hmin, mul_smul_comm, neg_smul]

def exteriorContraction (i : ℕ) : Module.End K (Exterior K) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K (OneParticle K)))
    (Finsupp.lapply i)

private theorem contraction_generator (i a : ℕ) (x : Exterior K) :
    exteriorContraction i (generator a * x) =
      (if i = a then (1 : K) else 0) • x - generator a * exteriorContraction i x := by
  unfold exteriorContraction generator
  rw [CliffordAlgebra.contractLeft_ι_mul]
  simp [Finsupp.single_apply, eq_comm]

private theorem contraction_basis (S : Finset ℕ) (i : ℕ) :
    exteriorContraction (K := K) i (exteriorBasis S) =
      if i ∈ S then sign (K := K) i S • exteriorBasis (K := K) (S.erase i) else 0 := by
  induction S using Finset.induction_on_min generalizing i with
  | empty =>
      rw [exteriorBasis_empty]
      simp [exteriorContraction, CliffordAlgebra.contractLeft_one]
  | @insert a S ha ih =>
      have hnot : a ∉ S := fun h => (lt_irrefl a) (ha a h)
      rw [exteriorBasis_insert_min a S ha, contraction_generator, ih]
      by_cases hia : i = a
      · subst i
        rw [if_pos rfl, if_neg hnot]
        simp [hnot, sign_of_le_all a (insert a S) (by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact le_rfl
          · exact (ha x hx).le)]
      · by_cases his : i ∈ S
        · have hai := ha i his
          have hmin : ∀ x ∈ S.erase i, a < x := by
            intro x hx
            exact ha x (Finset.mem_of_mem_erase hx)
          simp only [hia, if_false, zero_smul, his, if_true, Finset.mem_insert,
            false_or, zero_sub]
          rw [Finset.erase_insert_of_ne (Ne.symm hia), exteriorBasis_insert_min a (S.erase i) hmin,
            sign_insert_lt a i S hnot hai, mul_smul_comm, neg_smul]
        · simp [hia, his]

/-- Signed insertion is genuine exterior multiplication on every algebraic state. -/
theorem exterior_create (i : ℕ) (v : Fock K) :
    exteriorCoordinates (create i v) =
      ExteriorAlgebra.ι K (Finsupp.single i 1) * exteriorCoordinates v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv, hw, mul_add]
  | single S a =>
      simp only [create, Finsupp.linearCombination_single, createBasis]
      rw [exteriorCoordinates, Module.Basis.repr_symm_single]
      rw [mul_smul_comm]
      change exteriorBasis.repr.symm (a • _) = a • (generator i * exteriorBasis S)
      rw [generator_basis]
      split_ifs with hi
      · simp
      · simp [smul_smul]

/-- Signed deletion is genuine left contraction on every algebraic state. -/
theorem exterior_annihilate (i : ℕ) (v : Fock K) :
    exteriorCoordinates (annihilate i v) =
      exteriorContraction i (exteriorCoordinates v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv, hw]
  | single S a =>
      simp only [annihilate, Finsupp.linearCombination_single, annihilateBasis]
      rw [exteriorCoordinates, Module.Basis.repr_symm_single]
      simp only [map_smul, contraction_basis]
      split_ifs with hi
      · simp [smul_smul]
      · simp

#print axioms exterior_create
#print axioms exterior_annihilate

end
end D5.S3.VertexAlgebra.BcGhostExteriorOperators
