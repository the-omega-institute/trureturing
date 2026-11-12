/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTQuartetTransferTail
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTQuartetTransferTail
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Higher original quartet transfer terms vanish after actual zero-count compression. -/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTFullOriginalRaising
import D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
import D5.S3.HomologicalAlgebra.FinitePerturbation

/-!
The original full Q, actual h = R * invM, and zero-count P0 are used on
ALL original states. Both ghost occupations {1} and {1,3} remain present:
their signed degrees are respectively 0 and 1. No b0 condition is imposed.

The power induction follows the support-raising induction in the pinned
LatticeRelativeBRSTCohomology.h_full_remainder_nilpotent_on_relativeMassShell.
Here it uses only fixed charge and a lower degree bound, without the shell,
its upper bound, or nilpotence. This absolute compression theorem leaves the
leading original-Q compression unevaluated.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.LatticeBRSTQuartetTransferTail

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeLightConeCoordinates
open LatticeLightConeCoordinates.NullFrame LatticeQuartetContraction
open LatticeBRSTModeFiltration LatticeBRSTFullOriginalRaising
open D5.S3.Quantum.Fermionic.BcGhostCharge
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
open D5.S3.HomologicalAlgebra

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
variable (B : Module.Basis (Fin t) ℂ F.K)

private theorem exponentDegree_of_noLongitudinal (m : Exponents t)
    (hm : NoLongitudinal m) : exponentDegree m = 0 := by
  classical
  change (∑ x ∈ m.support, (m x : ℤ) * variableWeight x) = 0
  apply Finset.sum_eq_zero
  rintro ⟨l,r⟩ hx
  by_cases hp : l = plus t
  · subst l
    simp [(hm r).1]
  · by_cases hn : l = minus t
    · subst l
      simp [(hm r).2]
    · simp [variableWeight, hp, hn]

private theorem zero_count_degree (i : StateIndex D t)
    (hi : totalCount i = 0) : degree i = 0 ∨ degree i = 1 := by
  classical
  obtain ⟨hm,hS⟩ := (totalCount_zero_iff i).mp hi
  have he := exponentDegree_of_noLongitudinal i.1.2 hm
  rcases hS with hS | hS
  · left
    norm_num [degree, he, hS, charge, Finset.filter_singleton]
  · right
    norm_num [degree, he, hS, charge, Finset.filter_insert,
      Finset.filter_singleton]

/- Extending the genuine diagonal basis action accounts for every finite
basis sum; no alternative state carrier or support certificate is introduced. -/
private theorem P0_actual_coefficient (v : State D) (i : StateIndex D t) :
    (actualBasis F B).repr (P0 F B v) i =
      (if totalCount i = 0 then (1 : ℂ) else 0) *
        (actualBasis F B).repr v i := by
  classical
  have hd : P0 F B = diagonal (actualBasis F B)
      (fun j => if totalCount j = 0 then (1 : ℂ) else 0) := by
    apply (actualBasis F B).ext
    intro j
    rw [P0_basis, diagonal_basis]
  rw [hd, diagonal_coefficient]

private theorem projected_input_support (p : Charge D) (v : State D) :
    HasCharge F B p (P0 F B (chargeProject p v)) ∧
      ∀ i : StateIndex D t,
        (actualBasis F B).repr (P0 F B (chargeProject p v)) i ≠ 0 →
          0 ≤ degree i := by
  classical
  have hs (i : StateIndex D t)
      (hi : (actualBasis F B).repr (P0 F B (chargeProject p v)) i ≠ 0) :
      totalCount i = 0 ∧ i.1.1 = p := by
    rw [P0_actual_coefficient, chargeProject_diagonal F B p,
      diagonal_coefficient] at hi
    constructor
    · by_contra hn
      exact hi (by simp [hn])
    · by_contra hn
      exact hi (by simp [hn])
  constructor
  · intro i hi
    exact (hs i hi).2
  · intro i hi
    rcases zero_count_degree i (hs i hi).1 with hd | hd <;> omega

private theorem P0_eq_zero_of_degree_ge_two (v : State D)
    (hv : ∀ i : StateIndex D t, (actualBasis F B).repr v i ≠ 0 →
      2 ≤ degree i) : P0 F B v = 0 := by
  classical
  rw [← basis_expand (actualBasis F B) v]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro i hi
  have hd := hv i (Finsupp.mem_support_iff.mp hi)
  have hn : totalCount i ≠ 0 := by
    intro hz
    rcases zero_count_degree i hz with he | he <;> omega
  rw [P0_basis, if_neg hn, zero_smul, smul_zero]

/- Positive powers of the ACTUAL h(Q-d0), followed by one more literal
Q-d0, reach degree at least two. No termination hypothesis is needed. -/
private theorem compressed_positive_power
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (r : ℕ) (hr : 1 ≤ r) :
    P0 F B * (LatticeBRST.totalCharge D H - d0 F p) *
        (h F B p * (LatticeBRST.totalCharge D H - d0 F p)) ^ r *
        P0 F B * chargeProject p = 0 := by
  classical
  apply LinearMap.ext
  intro v
  let A : Module.End ℂ (State D) :=
    h F B p * (LatticeBRST.totalCharge D H - d0 F p)
  let y : State D := P0 F B (chargeProject p v)
  have hinput : HasCharge F B p y ∧
      ∀ i : StateIndex D t, (actualBasis F B).repr y i ≠ 0 →
        0 ≤ degree i := projected_input_support F B p v
  have hiter (k : ℕ) :
      HasCharge F B p ((A ^ k) y) ∧
        ∀ i : StateIndex D t,
          (actualBasis F B).repr ((A ^ k) y) i ≠ 0 →
            (k : ℤ) ≤ degree i := by
    induction k with
    | zero => simpa using hinput
    | succ k ih =>
        have hs := (full_remainder_fixed_charge_vectors F B H hHG hGH p
          ((A ^ k) y) ih.1 (k : ℤ) ih.2).2
        constructor
        · simpa only [A, pow_succ', Module.End.mul_apply] using hs.1
        · intro i hi
          have hi' : (actualBasis F B).repr (A ((A ^ k) y)) i ≠ 0 := by
            simpa only [pow_succ', Module.End.mul_apply] using hi
          have hd := hs.2 i hi'
          omega
  have hs := (full_remainder_fixed_charge_vectors F B H hHG hGH p
    ((A ^ r) y) (hiter r).1 (r : ℤ) (hiter r).2).1
  change P0 F B ((LatticeBRST.totalCharge D H - d0 F p) ((A ^ r) y)) = 0
  apply P0_eq_zero_of_degree_ge_two F B
  intro i hi
  have hd := hs.2 i hi
  have hr' : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  omega

/-- Every finite original quartet transfer polynomial of positive length
has the same zero-count compression as its constant term. This equality is
on endomorphisms of all original State D, for every integral charge p. -/
theorem full_original_finite_transfer_compression
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (N : ℕ) (hN : 1 ≤ N) :
    P0 F B * (LatticeBRST.totalCharge D H - d0 F p) *
        FinitePerturbation.inversePolynomial
          (h F B p * (LatticeBRST.totalCharge D H - d0 F p)) N *
        P0 F B * chargeProject p =
      P0 F B * (LatticeBRST.totalCharge D H - d0 F p) *
        P0 F B * chargeProject p := by
  classical
  let delta : Module.End ℂ (State D) := LatticeBRST.totalCharge D H - d0 F p
  let A : Module.End ℂ (State D) := h F B p * delta
  change P0 F B * delta * FinitePerturbation.inversePolynomial A N *
      P0 F B * chargeProject p = P0 F B * delta * P0 F B * chargeProject p
  have hterm (j : ℕ) (hj : 1 ≤ j) :
      P0 F B * delta * (-A) ^ j * P0 F B * chargeProject p = 0 := by
    have ht : P0 F B * delta * A ^ j * P0 F B * chargeProject p = 0 :=
      compressed_positive_power F B H hHG hGH p j hj
    have hsign : (-A) ^ j = ((-1 : ℂ) ^ j) • A ^ j := by
      simpa only [neg_one_smul] using (smul_pow (-1 : ℂ) A j)
    rw [hsign, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      Algebra.smul_mul_assoc, ht, smul_zero]
  unfold FinitePerturbation.inversePolynomial
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  calc
    (∑ j ∈ Finset.range N,
        P0 F B * delta * (-A) ^ j * P0 F B * chargeProject p) =
        P0 F B * delta * (-A) ^ 0 * P0 F B * chargeProject p := by
      apply Finset.sum_eq_single 0
      · intro j hj hj0
        exact hterm j (by omega)
      · intro hz
        exact False.elim (hz (Finset.mem_range.mpr (by omega)))
    _ = P0 F B * delta * P0 F B * chargeProject p := by
      simp only [pow_zero, mul_one]

end D5.S3.VertexAlgebra.LatticeBRSTQuartetTransferTail
