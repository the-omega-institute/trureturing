/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedIterate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedIterate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native current minus-one product yields the complementary modes under the twisted iterate identity. -/

import Mathlib.RingTheory.Binomial
import D5.S3.VertexAlgebra.Lattice.Automorphisms.ConformalGroundTransport
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedQuadratic
import D5.S3.VertexAlgebra.LatticeActualConformalState
import D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport

/-!
Bojko Bakalov and Victor G. Kac, *Twisted Modules over Lattice Vertex Algebras*,
arXiv:math/0402315v3, (3.13) at n = -1 and first grid 1/3. Assume the
coefficientwise identity for a normalized pair of native lattice currents,
together with the two current restrictions and the twisted vacuum field.
The native nonnegative products leave only the vacuum contraction at product
index 1. Its binomial factor at j = 2 is -1/9, giving the zero-mode shift
when the twisted field of the native (-1)-product is isolated.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedIterate

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeActualConformalState
open D5.S3.VertexAlgebra.Lattice.Automorphisms D5.S3.VertexAlgebra.Modules
open ThirdCoverIntegerFactor ThirdCoverComplement ThirdTwistedQuadratic
open scoped BigOperators VertexOperator

private theorem current_product (D : LatticeData) (u v : Fin D.rank → ℂ)
    (n : ℤ) (hn : 0 ≤ n) :
    mu D (ConformalGroundTransport.current D u) n (ConformalGroundTransport.current D v) =
      if n = 1 then ((D.G.map (Int.castRingHom ℂ)).toBilin' u v) • vacuum D else 0 := by
  have hcurrent : ((Y D (ConformalGroundTransport.current D u))[[n]]) =
      ∑ i, u i • ((Y D (currentState D i))[[n]]) := by
    simp only [ConformalGroundTransport.current, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  rw [mu, hcurrent]
  simp only [ConformalGroundTransport.current, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul]
  have index_one : n.toNat = 1 ↔ n = 1 := by omega
  have hb (i j : Fin D.rank) : ((Y D (currentState D i))[[n]]) (currentState D j) =
      if n = 1 then (D.G i j : ℂ) • vacuum D else 0 := by
    simpa only [FullJacobiCurrentTransport.sourceProduct, FullJacobiCurrentTransport.currentState,
      current_state_creation, Int.toNat_of_nonneg hn, index_one] using
      FullJacobiCurrentTransport.source_current_product D i j n.toNat
  simp_rw [hb]
  by_cases h : n = 1
  · simp only [h, ite_true, Matrix.toBilin'_apply, Matrix.map_apply]
    simp_rw [Finset.smul_sum, Finset.sum_smul, smul_smul]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      exact congrArg (fun c : ℂ => c • vacuum D)
        (show v j * (u i * (D.G i j : ℂ)) = u i * (D.G i j : ℂ) * v j
          from mul_comm _ _)
  · simp [h]

private theorem oneThirdChoose_two : Ring.choose (1 / 3 : ℂ) 2 = -1 / 9 := by
  rw [Ring.choose_eq_smul, descPochhammer_succ_right ℤ 1, descPochhammer_one]
  norm_num [Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, Polynomial.smeval_one, smul_eq_mul, Nat.factorial]

/-- The explicit n = -1 instance of (3.13), coefficient by coefficient.
A native index k denotes exponent -k/3 - 1 in the state field. The factor
of z^(-j) gives the native index 3 * (m + 1 - j) on the right. -/
def pairIterate (D : LatticeData) (a b : Carrier D)
    (Ytw : Carrier D →ₗ[ℂ] ℤ → Module.End ℂ ComplementFock) : Prop :=
  ∀ (m : ℤ) (Q : ComplementFock),
    (∑ᶠ k ∈ residue 1,
      (if k < 0 then Ytw a k * Ytw b (3 * m - k)
       else Ytw b (3 * m - k) * Ytw a k) Q) =
      ∑ᶠ j : ℕ, Ring.choose (1 / 3 : ℂ) j •
        Ytw (mu D a ((j : ℤ) - 1) b) (3 * (m + 1 - (j : ℤ))) Q

/-- The pair state is the actual untwisted (-1)-product. The twisted inputs
are the two current restrictions, the vacuum field, and (3.13) on this pair. -/
theorem fractionalVirasoro_of_twistedIterate (D : LatticeData) (u v : Fin D.rank → ℂ)
    (hpair : (D.G.map (Int.castRingHom ℂ)).toBilin' u v = 1)
    (Ytw : Carrier D →ₗ[ℂ] ℤ → Module.End ℂ ComplementFock)
    (hU : ∀ k, Ytw (ConformalGroundTransport.current D u) k =
      if k % 3 = 1 then fractionalCurrent k else 0)
    (hV : ∀ k, Ytw (ConformalGroundTransport.current D v) k =
      if k % 3 = 2 then fractionalCurrent k else 0)
    (hVac : ∀ k, Ytw (vacuum D) k = if k = -3 then 1 else 0)
    (hIterate : pairIterate D (ConformalGroundTransport.current D u)
      (ConformalGroundTransport.current D v) Ytw)
    (m : ℤ) :
    Ytw (mu D (ConformalGroundTransport.current D u) (-1) (ConformalGroundTransport.current D v))
        (3 * (m + 1)) = fractionalVirasoro m := by
  let a := ConformalGroundTransport.current D u
  let b := ConformalGroundTransport.current D v
  apply LinearMap.ext
  intro Q
  have lhs : orderedCoefficient m Q =
      ∑ᶠ k ∈ residue 1, (if k < 0 then Ytw a k * Ytw b (3 * m - k)
        else Ytw b (3 * m - k) * Ytw a k) Q := by
    refine finsum_mem_congr rfl fun k hk => ?_
    have hl : 3 * m - k ∈ residue 2 := by
      change k % 3 = 1 at hk
      change (3 * m - k) % 3 = 2
      omega
    change k % 3 = 1 at hk
    change (3 * m - k) % 3 = 2 at hl
    simp only [a, b, orderedPair, hU k, hV (3 * m - k), hk, hl, ite_true]
  let term (j : ℕ) := Ring.choose (1 / 3 : ℂ) j •
    Ytw (mu D a ((j : ℤ) - 1) b) (3 * (m + 1 - (j : ℤ))) Q
  have hterm : Function.support term ⊆ (↑({0, 2} : Finset ℕ) : Set ℕ) := by
    intro j hj
    by_contra h
    have hj0 : j ≠ 0 := fun hz => h (by simp [hz])
    have hj2 : j ≠ 2 := fun hz => h (by simp [hz])
    apply hj
    dsimp [term, a, b]
    rw [current_product D u v _ (by omega)]
    simp [show (j : ℤ) - 1 ≠ 1 by omega]
  have h := lhs.trans (hIterate m Q)
  change orderedCoefficient m Q = ∑ᶠ j : ℕ, term j at h
  rw [finsum_eq_sum_of_support_subset term hterm, Finset.sum_pair (by decide : (0 : ℕ) ≠ 2)] at h
  have h0 : term 0 = Ytw (mu D a (-1) b) (3 * (m + 1)) Q := by
    simp [term, Ring.choose_zero_right]
  have h2 : term 2 = -((if m = 0 then (1 / 9 : ℂ) else 0) • Q) := by
    have hproduct : mu D a 1 b = vacuum D := by
      simpa only [a, b, ite_true, hpair, one_smul] using current_product D u v 1 (by decide)
    change Ring.choose (1 / 3 : ℂ) 2 • Ytw (mu D a 1 b) (3 * (m + 1 - 2)) Q = _
    rw [oneThirdChoose_two, hproduct, hVac]
    simp only [show 3 * (m + 1 - 2) = -3 ↔ m = 0 by omega]
    split <;> simp [neg_div, neg_smul]
  rw [fractionalVirasoro_apply_ordered, h, h0, h2]
  abel

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedIterate
