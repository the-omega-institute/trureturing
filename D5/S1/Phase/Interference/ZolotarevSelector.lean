/- GID: D5/S1/Phase/Interference/ZolotarevSelector
   generality: G
   mirror-B: D5/B/S1/Phase/Interference/ZolotarevSelector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factor the selector symbol through the Zolotarev inverse-residue congruence. -/

/- Library-search audit trail (2026-08-12):
   * `jacobiSym.mul_left` and the frozen
     `SeatTowerConsequences.jacobi_factorization_of_selector_numerator` carry the
     factorization side; `Int.ModEq` and `ZMod` congruence lemmas carry the
     inverse-residue transport. No combined statement was found in the
     repository or the pinned Mathlib tree. -/

import D5.S1.Phase.SeatTowerConsequences

namespace D5.S1.Phase.Interference.ZolotarevSelector

open D5.S1.Phase.SeatTowerConsequences
open scoped BigOperators NumberTheorySymbols

/-- The Zolotarev congruence makes `2 * gamma0` and `-2 * beta`
inverse residues, so their Jacobi symbols agree and the selector factors. -/
theorem zolotarev_selector_congruence
    (beta gamma0 d : Int)
    (hIdentity : 4 * beta * gamma0 ≡ -1 [ZMOD d]) :
    J(2 * gamma0 | d.natAbs) =
      J(2 | d.natAbs) * J(-1 | d.natAbs) * J(beta | d.natAbs) := by
  have hInverse :
      (2 * gamma0) * (2 * (-1) * beta) ≡ 1 [ZMOD d.natAbs] := by
    rw [Int.modEq_natAbs]
    calc
      (2 * gamma0) * (2 * (-1) * beta) = -(4 * beta * gamma0) := by ring
      _ ≡ -(-1) [ZMOD d] := hIdentity.neg
      _ = 1 := by ring
  have hProduct :
      J(2 * gamma0 | d.natAbs) * J(2 * (-1) * beta | d.natAbs) = 1 := by
    rw [← jacobiSym.mul_left]
    simpa using jacobiSym.mod_left' hInverse.eq
  have hSelector :
      J(2 * gamma0 | d.natAbs) = J(2 * (-1) * beta | d.natAbs) := by
    rcases jacobiSym.trichotomy (2 * gamma0) d.natAbs with h | h | h <;>
      rcases jacobiSym.trichotomy (2 * (-1) * beta) d.natAbs with h' | h' | h' <;>
      simp_all
  exact jacobi_factorization_of_selector_numerator beta d.natAbs
    J(2 * gamma0 | d.natAbs) hSelector

/-- A nontrivial instance: the congruence holds modulo five and the selector is
`-1`, so the bridge is not vacuous. -/
theorem zolotarev_selector_congruence_witness :
    (4 * (1 : Int) * 1 ≡ -1 [ZMOD 5]) ∧
      J(2 * (1 : Int) | (5 : Int).natAbs) = -1 ∧
      J(2 * (1 : Int) | (5 : Int).natAbs) =
        J(2 | (5 : Int).natAbs) * J(-1 | (5 : Int).natAbs) *
          J(1 | (5 : Int).natAbs) := by
  have hIdentity : 4 * (1 : Int) * 1 ≡ -1 [ZMOD 5] := by
    norm_num [Int.ModEq]
  refine ⟨hIdentity, ?_, zolotarev_selector_congruence 1 1 5 hIdentity⟩
  change J(2 | 5) = -1
  rw [jacobiSym.at_two (by decide : Odd 5), ZMod.χ₈_nat_eq_if_mod_eight]
  norm_num

end D5.S1.Phase.Interference.ZolotarevSelector
