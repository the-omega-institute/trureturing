/- GID: D5/S3/Combinatorics/Matroids/RankThreeMinimumInternalAdditions
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeMinimumInternalAdditions
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Raising the ternary potential dimension requires a sharp number of internal triples. -/

import D5.S3.Combinatorics.Matroids.RankThreeInternalTriplePotentials
import D5.S3.Combinatorics.Matroids.RankThreeOmissionPairCount

namespace D5.S3.Combinatorics.Matroids.RankThreeMinimumInternalAdditions

open RankThreeInternalTriplePotentials (Row LiftedLineFamily AllowsExtra potential_finrank_internal_triples)
open RankThreeOmissionPotentialFibers (potentialSpace point_potential_evaluations)
open RankThreeOmissionPairCount (potential_fiber_pair_count_le)
open RankThreeOmissionPotentials (covers)

/-- After the cyclic coefficient becomes available, the total mixed-pair
bound fixes the minimum number of additions to the original lifted lines. -/
theorem internal_additions_lower_bound {d r : ℕ} [NeZero (3*r)] {T U : Type*}
    [Fintype T] [Fintype U] (hd : 0 < d)
    (mixed : T → Fin 3 → Row d × ZMod (3*r))
    (internal : U → Fin 3 → Row d × ZMod (3*r))
    (family : LiftedLineFamily (Sum.elim mixed internal))
    (extra : AllowsExtra (Sum.elim mixed internal))
    (hinj : ∀ t, Function.Injective (Sum.elim mixed internal t))
    (hdis : ∀ t u x y, x ≠ y → covers (Sum.elim mixed internal t) x y →
      covers (Sum.elim mixed internal u) x y → t = u)
    (mixed_count : 6 * Fintype.card T = 3^d * (3^d-1) * (3*r)^2) :
    3^d * r^2 ≤ Fintype.card U := by
  classical
  let points := Sum.elim mixed internal
  let P := potentialSpace points 0
  let e := Module.finrank (ZMod 3) P
  let b := Module.finBasis (ZMod 3) P
  let s := Nat.card {x : Row d × ZMod (3*r) // (fun k => (b k).val x) = 0}
  have dim : e = d+1 := by
    dsimp only [e,P]
    rw [potential_finrank_internal_triples points hd family,ite_eq_left extra]
  have card (q : ℕ) [NeZero q] : Fintype.card (Row d × ZMod q) = 3^d * q := by
    simp [Row,Fintype.card_prod,ZMod.card]
  have count : Fintype.card (Row d × ZMod (3*r)) = 3^e * s :=
    (point_potential_evaluations points hinj hdis 0 b).2.2.1
  have size : s = r := by
    rw [card,dim,pow_succ] at count
    have eq : (3^d * 3) * r = (3^d * 3) * s := by simpa only [Nat.mul_assoc] using count
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) eq).symm
  have bound : 3^e * (3^e-1) * s^2 ≤ 6 * Fintype.card (T ⊕ U) :=
    potential_fiber_pair_count_le points 0 hinj hdis b
  rw [dim,size,pow_succ,Fintype.card_sum,Nat.mul_add,mixed_count] at bound
  let q := 3^d
  have pos : 0 < q := by positivity
  have pred : q * 3 - 1 = 3*(q-1) + 2 := by omega
  change q * 3 * (q * 3 - 1) * r^2 ≤ q * (q-1) * (3*r)^2 + 6 * Fintype.card U at bound
  have expand : q * 3 * (q * 3 - 1) * r^2 =
      q * (q-1) * (3*r)^2 + 6 * (q*r^2) := by
    conv_lhs => rw [pred]
    ring
  rw [expand] at bound
  change q * r^2 ≤ Fintype.card U
  omega

end D5.S3.Combinatorics.Matroids.RankThreeMinimumInternalAdditions
