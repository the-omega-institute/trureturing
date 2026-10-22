/- GID: D5/S3/VertexAlgebra/BcGhostNumber
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostNumber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral signed occupation gives the original full bc Fock modes their ghost degrees. -/

import D5.S3.VertexAlgebra.BcGhostFockSupport

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostNumber

noncomputable section

open D5.S3.VertexAlgebra.BcGhostFockSupport
open scoped BigOperators

variable {K : Type*} [CommRing K]

def degree (subset : Finset ℕ) : ℤ :=
  ((subset.filter fun site => site % 2 = 1).card : ℤ) -
    ((subset.filter fun site => site % 2 = 0).card : ℤ)

private def siteDegree (site : ℕ) : ℤ := if site % 2 = 1 then 1 else -1

def J : Module.End K (Fock K) :=
  Finsupp.linearCombination K (fun subset =>
    (degree subset : K) • Finsupp.single subset 1)

private theorem siteDegree_even (index : ℕ) : siteDegree (2 * index) = -1 := by
  simp [siteDegree, Nat.mul_mod]

private theorem siteDegree_odd (index : ℕ) : siteDegree (2 * index + 1) = 1 := by
  simp [siteDegree, Nat.add_mod, Nat.mul_mod]

theorem degree_insert (site : ℕ) (subset : Finset ℕ) (absent : site ∉ subset) :
    degree (insert site subset) = degree subset + siteDegree site := by
  have parity : site % 2 = 0 ∨ site % 2 = 1 := by omega
  rcases parity with even | odd
  · have notOdd : site % 2 ≠ 1 := by omega
    simp [degree, siteDegree, Finset.filter_insert, even, notOdd, absent] <;> omega
  · have notEven : site % 2 ≠ 0 := by omega
    simp [degree, siteDegree, Finset.filter_insert, odd, notEven, absent] <;> omega

private theorem degree_erase (site : ℕ) (subset : Finset ℕ) (present : site ∈ subset) :
    degree (subset.erase site) = degree subset - siteDegree site := by
  have inserted := degree_insert site (subset.erase site) (by simp)
  rw [Finset.insert_erase present] at inserted
  omega

theorem J_single (subset : Finset ℕ) (scalar : K) :
    J (Finsupp.single subset scalar) =
      (degree subset : K) • Finsupp.single subset scalar := by
  simp [J, smul_smul, Finsupp.smul_single, mul_comm]

private theorem J_create_apply (site : ℕ) (state : Fock K) :
    J (create site state) - create site (J state) =
      (siteDegree site : K) • create site state := by
  induction state using Finsupp.induction_linear with
  | zero => simp
  | add first second firstProof secondProof =>
      simp only [map_add, smul_add]
      calc
        _ = (J (create site first) - create site (J first)) +
            (J (create site second) - create site (J second)) := by abel
        _ = _ := by rw [firstProof, secondProof]
  | single subset scalar =>
      simp only [create, Finsupp.linearCombination_single, J_single, map_smul]
      by_cases present : site ∈ subset
      · simp [createBasis, present]
      · simp only [createBasis, if_neg present, J_single, map_smul]
        rw [degree_insert site subset present]
        simp only [Int.cast_add, add_smul, smul_smul]
        module

private theorem J_annihilate_apply (site : ℕ) (state : Fock K) :
    J (annihilate site state) - annihilate site (J state) =
      -(siteDegree site : K) • annihilate site state := by
  induction state using Finsupp.induction_linear with
  | zero => simp
  | add first second firstProof secondProof =>
      simp only [map_add, smul_add]
      calc
        _ = (J (annihilate site first) - annihilate site (J first)) +
            (J (annihilate site second) - annihilate site (J second)) := by abel
        _ = _ := by rw [firstProof, secondProof]
  | single subset scalar =>
      simp only [annihilate, Finsupp.linearCombination_single, J_single, map_smul]
      by_cases present : site ∈ subset
      · simp only [annihilateBasis, if_pos present, J_single, map_smul]
        rw [degree_erase site subset present]
        simp only [Int.cast_sub, sub_smul, smul_smul]
        module
      · simp [annihilateBasis, present]

theorem J_b_commutator (mode : ℤ) :
    J (K := K) * b mode - b mode * J = -b (K := K) mode := by
  apply LinearMap.ext
  intro state
  change J (b mode state) - b mode (J state) = -(b mode state)
  by_cases creator : mode ≤ -2
  · simpa only [b, if_pos creator, siteDegree_even, Int.cast_neg, Int.cast_one,
      neg_one_smul] using J_create_apply (K := K) (2 * (-mode - 2).toNat) state
  · simpa only [b, if_neg creator, siteDegree_odd, Int.cast_one, neg_one_smul]
      using J_annihilate_apply (K := K) (2 * (mode + 1).toNat + 1) state

theorem J_c_commutator (mode : ℤ) :
    J (K := K) * c mode - c mode * J = c mode := by
  apply LinearMap.ext
  intro state
  change J (c mode state) - c mode (J state) = c mode state
  by_cases creator : mode ≤ 1
  · simpa only [c, if_pos creator, siteDegree_odd, Int.cast_one, one_smul]
      using J_create_apply (K := K) (2 * (1 - mode).toNat + 1) state
  · simpa only [c, if_neg creator, siteDegree_even, Int.cast_neg, Int.cast_one,
      neg_neg, one_smul] using J_annihilate_apply (K := K) (2 * (mode - 2).toNat) state

private theorem J_normalPair_commutator (first second : ℤ) :
    J (K := K) * normalPair first second - normalPair first second * J = 0 := by
  have bDegree := J_b_commutator (K := K) first
  have cDegree := J_c_commutator (K := K) second
  by_cases creator : first ≤ -2
  · simp only [normalPair, if_pos creator, ← Module.End.mul_eq_comp]
    calc
      _ = (J * b first - b first * J) * c second +
          b first * (J * c second - c second * J) := by noncomm_ring
      _ = 0 := by rw [bDegree, cDegree]; simp
  · simp only [normalPair, if_neg creator, ← Module.End.mul_eq_comp]
    calc
      _ = -((J * c second - c second * J) * b first +
          c second * (J * b first - b first * J) : Module.End K (Fock K)) := by noncomm_ring
      _ = 0 := by rw [bDegree, cDegree]; simp

theorem J_L_commutator (mode : ℤ) :
    J (K := K) * L mode - L mode * J = 0 := by
  apply LinearMap.ext
  intro state
  let bound := max (cutoff mode state) (cutoff mode (J state))
  have stateBound : cutoff mode state ≤ bound := le_max_left _ _
  have numberBound : cutoff mode (J state) ≤ bound := le_max_right _ _
  have stateSum := L_interval_sum mode state (-bound) bound
    (neg_le_neg stateBound) stateBound
  have numberSum := L_interval_sum mode (J state) (-bound) bound
    (neg_le_neg numberBound) numberBound
  change J (L mode state) - L mode (J state) = 0
  rw [stateSum, numberSum, map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro index member
  have commutation := congrArg (fun operator : Module.End K (Fock K) => operator state)
    (J_normalPair_commutator (K := K) (mode + index) (-index))
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.zero_apply]
    at commutation
  rw [map_smul, ← smul_sub, commutation, smul_zero]

#print axioms J_b_commutator
#print axioms J_c_commutator
#print axioms J_L_commutator

end

end D5.S3.VertexAlgebra.BcGhostNumber
