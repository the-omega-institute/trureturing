/- GID: D5/S3/Quantum/Fermionic/BcGhostChargeNormalForm
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostChargeNormalForm
   mirror-E: none(waiver:algebraic-ghost-charge-normal-form)
   anchors: []
   utility: none
   digest: The original cubic ghost charge equals the all-state half-normal c/L sum. -/

import D5.S3.Quantum.Fermionic.BcGhostBRST

/-!
# The half-normal form of the original cubic ghost charge

The original cubic charge equals the half-normal sum on every algebraic ghost
state. The ordered terms and their joint expansion have statewise finite support.

The outer ordering and half coefficient reuse the retained
`LatticeBcGhostBrstCharge.N`/`A` source mechanism (retained source SHA256
`c86ba73030f046ed86c83c5e4103a9970910a7b6c83eb1f76860c284b8ccd3a8`).
Only the original `CountableOccupationFock.Fock`, `BcGhostFock.b/c`,
`BcGhostVirasoro.L` and `BcGhostBRST.Qg` occur in this module. The historical
namespace hierarchy is neither imported nor recreated.

The normal/cubic algebra and statewise summation infrastructure belong to the
present `BcGhostVirasoro`, `BcGhostCubic` and `BcGhostBRST` sources. This is a
comparison of their actual operators, without a lattice or criticality premise.
Retain the original ghost-source attribution and the Scott Carnahan/vertexAlg
Apache-2.0 attribution of the related field/normal-product constructions
(vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea), as recorded in
the supplied `BcGhostStateField` source. No literature novelty is claimed.

The only reindexing below is `(n,q) ↦ (-n,q)`. It follows the two-sided support
proof for the actual ordered term and the joint support proof for its expansion.
This connected ghost prerequisite does not complete the Moonshine/VOA/CFT,
anomaly/fusion, string or AdS-CFT objective.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostVirasoro (normal summand summand_finite L)
open D5.S3.Quantum.Fermionic.BcGhostBRST (cubic cubicTerm cubicTerm_finite Qg)
open private normal_eq from D5.S3.Quantum.Fermionic.BcGhostVirasoro
open private cubic_eq c_swap b_ket_tail c_ket_tail from
  D5.S3.Quantum.Fermionic.BcGhostCubic

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostChargeNormalForm

/-- The actual outer normal ordering, before any sum or half coefficient. -/
def orderedTerm (n : ℤ) : Module.End ℂ Fock :=
  if -1 ≤ n then c (-n) * L n else L n * c (-n)

private def ketBound (S : Finset ℕ) : ℤ := (S.sup id + 3 : ℕ)

private theorem L_ket_high (m : ℤ) (S : Finset ℕ)
    (hm : 2 * ketBound S < m) : L m (ket S) = 0 := by
  have hm0 : m ≠ 0 := by dsimp [ketBound] at hm; omega
  change (∑ᶠ q : ℤ, summand m q (ket S)) = 0
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  by_cases hq : ketBound S < q
  · have hc : c q (ket S) = 0 := c_ket_tail q S hq
    have he : normal (m-q) q = b (m-q) * c q := by
      rw [normal_eq]
      simp [hm0]
    simp [summand, he, Module.End.mul_apply, hc]
  · have hp : ketBound S < m-q := by omega
    have hcut : ¬m-q ≤ -2 := by dsimp [ketBound] at hp; omega
    have hb : b (m-q) (ket S) = 0 := b_ket_tail (m-q) S hp
    simp [summand, normal, hcut, Module.End.mul_apply, hb]

private theorem orderedTerm_ket_support (S : Finset ℕ) :
    Function.support (fun n : ℤ => orderedTerm n (ket S)) ⊆
      Set.Icc (-ketBound S) (2 * ketBound S) := by
  intro n hn
  constructor
  · by_contra hlo
    have hnlow : n < -ketBound S := lt_of_not_ge hlo
    have hcut : ¬-1 ≤ n := by dsimp [ketBound] at hnlow; omega
    have hc : c (-n) (ket S) = 0 := c_ket_tail (-n) S (by
      change ketBound S < -n
      omega)
    exact hn (by simp [orderedTerm, hcut, Module.End.mul_apply, hc])
  · by_contra hhi
    have hnhigh : 2 * ketBound S < n := lt_of_not_ge hhi
    have hcut : -1 ≤ n := by dsimp [ketBound] at hnhigh; omega
    have hL := L_ket_high n S hnhigh
    exact hn (by simp [orderedTerm, hcut, Module.End.mul_apply, hL])

/-- Every actual state has its own two-sided bound; no global cutoff is used. -/
theorem orderedTerm_support (v : Fock) :
    ∃ A : ℤ, 0 ≤ A ∧ Function.support (fun n : ℤ => orderedTerm n v) ⊆
      Set.Icc (-A) (2*A) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intro n hn
    exact False.elim (hn (map_zero (orderedTerm n)))
  | add f g hf hg =>
    obtain ⟨A, hA, hf⟩ := hf
    obtain ⟨B, hB, hg⟩ := hg
    refine ⟨max A B, le_trans hA (le_max_left A B), ?_⟩
    intro n hn
    have hmaxA : A ≤ max A B := le_max_left A B
    have hmaxB : B ≤ max A B := le_max_right A B
    by_cases hz : orderedTerm n f = 0
    · have hng : orderedTerm n g ≠ 0 := by
        intro hzero
        exact hn (by simp only [map_add, hz, hzero, add_zero])
      obtain ⟨hl, hu⟩ := hg hng
      exact ⟨by omega, by omega⟩
    · obtain ⟨hl, hu⟩ := hf hz
      exact ⟨by omega, by omega⟩
  | single S a =>
    refine ⟨ketBound S, by dsimp [ketBound]; omega, ?_⟩
    have hs : Finsupp.single S a = a • ket S := by simp [ket]
    intro n hn
    apply orderedTerm_ket_support S
    intro hz
    exact hn (by simp [hs, map_smul, hz])

/-- Finiteness is proved on every input state before any sum linearity is used. -/
theorem orderedTerm_finite (v : Fock) :
    Function.HasFiniteSupport (fun n : ℤ => orderedTerm n v) := by
  obtain ⟨A, _, hA⟩ := orderedTerm_support v
  exact (Set.finite_Icc (-A) (2*A)).subset hA

/-- The half-normal expression is a linear operator on the full original Fock. -/
def halfNormalCharge : Module.End ℂ Fock where
  toFun v := (1/2 : ℂ) • ∑ᶠ n : ℤ, orderedTerm n v
  map_add' v w := by
    simp only [map_add]
    rw [finsum_add_distrib (orderedTerm_finite v) (orderedTerm_finite w), smul_add]
  map_smul' a v := by
    simp only [map_smul]
    rw [← smul_finsum' a (orderedTerm_finite v)]
    exact smul_comm (1/2 : ℂ) a _

private def expandedTerm (n q : ℤ) : Module.End ℂ Fock :=
  if -1 ≤ n then c (-n) * summand n q else summand n q * c (-n)

/-- In the two crossed cuts, the mixed CAR contraction really is zero. -/
private theorem outer_normal (p q : ℤ) :
    (if p ≤ 1 then c p * normal (-p-q) q else normal (-p-q) q * c p) =
      -cubic p q := by
  by_cases hp : p ≤ 1 <;> by_cases hk : -p-q ≤ -2
  · have hbc : b (-p-q) * c p + c p * b (-p-q) = 0 := by
      rw [ghost_mixed_car, if_neg (by omega)]
    simp only [if_pos hp, normal, if_pos hk, cubic_eq, if_pos hk]
    calc
      _ = -(b (-p-q) * c p * c q) +
          (b (-p-q) * c p + c p * b (-p-q)) * c q := by noncomm_ring
      _ = _ := by rw [hbc]; simp
  · simp only [if_pos hp, normal, if_neg hk, cubic_eq, if_neg hk]
    noncomm_ring
  · simp only [if_neg hp, normal, if_pos hk, cubic_eq, if_pos hk]
    calc
      _ = b (-p-q) * (c q * c p) := mul_assoc _ _ _
      _ = _ := by rw [c_swap q p]; noncomm_ring
  · have hbc : b (-p-q) * c p + c p * b (-p-q) = 0 := by
      rw [ghost_mixed_car, if_neg (by omega)]
    have hcc := ghost_c_car p q
    simp only [if_neg hp, normal, if_neg hk, cubic_eq, if_neg hk]
    calc
      _ = -(c p * c q * b (-p-q)) -
          c q * (b (-p-q) * c p + c p * b (-p-q)) +
          (c p * c q + c q * c p) * b (-p-q) := by noncomm_ring
      _ = _ := by rw [hbc, hcc]; simp

private theorem expandedTerm_eq (n q : ℤ) :
    expandedTerm n q = (2 : ℂ) • cubicTerm (-n,q) := by
  have hcut : -n ≤ 1 ↔ -1 ≤ n := by omega
  have hnormal :
      (if -1 ≤ n then c (-n) * normal (n-q) q else normal (n-q) q * c (-n)) =
        -cubic (-n) q := by
    simpa only [neg_neg, hcut] using outer_normal (-n) q
  have hweighted : expandedTerm n q = ((n+q : ℤ) : ℂ) •
      (if -1 ≤ n then c (-n) * normal (n-q) q else normal (n-q) q * c (-n)) := by
    by_cases hn : -1 ≤ n <;>
      simp only [expandedTerm, summand, hn, ↓reduceIte, mul_smul_comm, smul_mul_assoc]
  rw [hweighted, hnormal]
  simp only [cubicTerm, smul_neg, ← neg_smul, smul_smul]
  congr 1
  push_cast
  ring

private def reverseFirst : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun nq := (-nq.1, nq.2)
  invFun pq := (-pq.1, pq.2)
  left_inv nq := by simp
  right_inv pq := by simp

private theorem expandedTerm_finite (v : Fock) :
    Function.HasFiniteSupport (fun nq : ℤ × ℤ => expandedTerm nq.1 nq.2 v) := by
  apply ((cubicTerm_finite v).image reverseFirst).subset
  intro nq hnq
  refine ⟨(-nq.1,nq.2), ?_, ?_⟩
  · intro hz
    exact hnq (by simp [expandedTerm_eq, hz])
  · simp [reverseFirst]

private theorem orderedTerm_expansion (n : ℤ) (v : Fock) :
    orderedTerm n v = ∑ᶠ q : ℤ, expandedTerm n q v := by
  by_cases hn : -1 ≤ n
  · simp only [orderedTerm, if_pos hn, Module.End.mul_apply]
    change c (-n) (∑ᶠ q : ℤ, summand n q v) = _
    rw [map_finsum (c (-n)) (summand_finite n v)]
    apply finsum_congr
    intro q
    simp only [expandedTerm, if_pos hn, Module.End.mul_apply]
  · simp only [orderedTerm, if_neg hn, Module.End.mul_apply]
    change (∑ᶠ q : ℤ, summand n q (c (-n) v)) = _
    apply finsum_congr
    intro q
    simp only [expandedTerm, if_neg hn, Module.End.mul_apply]

/-- The existing cubic equals the literal requested half-normal sum on EVERY
original state, with no lattice, rank, Gram, nilpotence or cohomology premise. -/
theorem Qg_eq_halfNormalCharge (v : Fock) :
    Qg v = (1/2 : ℂ) • ∑ᶠ n : ℤ,
      if -1 ≤ n then c (-n) (L n v) else L n (c (-n) v) := by
  have hcharge : Qg v = halfNormalCharge v := by
    have hE := expandedTerm_finite v
    have hC := cubicTerm_finite v
    change (∑ᶠ pq : ℤ × ℤ, cubicTerm pq v) =
      (1/2 : ℂ) • ∑ᶠ n : ℤ, orderedTerm n v
    symm
    calc
      (1/2 : ℂ) • (∑ᶠ n : ℤ, orderedTerm n v) =
          (1/2 : ℂ) • (∑ᶠ n : ℤ, ∑ᶠ q : ℤ, expandedTerm n q v) := by
        congr 1
        exact finsum_congr (fun n => orderedTerm_expansion n v)
      _ = (1/2 : ℂ) • (∑ᶠ nq : ℤ × ℤ, expandedTerm nq.1 nq.2 v) := by
        rw [finsum_curry _ hE]
      _ = (1/2 : ℂ) • (∑ᶠ nq : ℤ × ℤ, (2 : ℂ) • cubicTerm (-nq.1,nq.2) v) := by
        congr 1
        apply finsum_congr
        intro nq
        exact LinearMap.congr_fun (expandedTerm_eq nq.1 nq.2) v
      _ = (1/2 : ℂ) • (∑ᶠ pq : ℤ × ℤ, (2 : ℂ) • cubicTerm pq v) := by
        congr 1
        exact finsum_comp (g := fun pq : ℤ × ℤ => (2 : ℂ) • cubicTerm pq v)
          reverseFirst reverseFirst.bijective
      _ = (1/2 : ℂ) • ((2 : ℂ) • ∑ᶠ pq : ℤ × ℤ, cubicTerm pq v) := by
        rw [← smul_finsum' (2 : ℂ) hC]
      _ = ∑ᶠ pq : ℤ × ℤ, cubicTerm pq v := by
        rw [smul_smul]
        norm_num
  calc
    Qg v = halfNormalCharge v := hcharge
    _ = _ := by
      change (1/2 : ℂ) • (∑ᶠ n : ℤ, orderedTerm n v) = _
      congr 1
      apply finsum_congr
      intro n
      by_cases hn : -1 ≤ n <;>
        simp only [orderedTerm, hn, ↓reduceIte, Module.End.mul_apply]

end D5.S3.Quantum.Fermionic.BcGhostChargeNormalForm
