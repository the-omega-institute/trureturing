/- GID: D5/S3/Quantum/Fermionic/BcGhostBRSTDegree
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostBRSTDegree
   mirror-E: none(waiver:algebraic-total-brst)
   anchors: []
   utility: none
   digest: Ghost degree one of the locally finite cubic charge. -/

import D5.S3.Quantum.Fermionic.BcGhostCubic
import D5.S3.Quantum.Fermionic.BcGhostCharge

/-! The original locally finite cubic BRST charge has ghost degree one. -/


set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostCharge
open private cubic_eq from D5.S3.Quantum.Fermionic.BcGhostCubic

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostBRST

private theorem cubic_ghost_number (p q : ℤ) :
    ghostNumber * cubic p q - cubic p q * ghostNumber = cubic p q := by
  have hp := ghost_number_relations.2.2 p
  have hq := ghost_number_relations.2.2 q
  have hb := ghost_number_relations.2.1 (-p-q)
  by_cases hk : -p-q ≤ -2
  · simp only [cubic_eq, if_pos hk]
    calc
      _ = (ghostNumber * b (-p-q) - b (-p-q) * ghostNumber) * c p * c q +
          b (-p-q) * (ghostNumber * c p - c p * ghostNumber) * c q +
          b (-p-q) * c p * (ghostNumber * c q - c q * ghostNumber) := by
            noncomm_ring
      _ = b (-p-q) * c p * c q := by rw [hb, hp, hq]; noncomm_ring
  · simp only [cubic_eq, if_neg hk]
    calc
      _ = (ghostNumber * c p - c p * ghostNumber) * c q * b (-p-q) +
          c p * (ghostNumber * c q - c q * ghostNumber) * b (-p-q) +
          c p * c q * (ghostNumber * b (-p-q) - b (-p-q) * ghostNumber) := by
            noncomm_ring
      _ = c p * c q * b (-p-q) := by rw [hp, hq, hb]; noncomm_ring

private theorem cubicTerm_ghost_number (pq : ℤ × ℤ) :
    ghostNumber * cubicTerm pq - cubicTerm pq * ghostNumber = cubicTerm pq := by
  unfold cubicTerm
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, cubic_ghost_number]

/-- Degree one of the original full cubic, using statewise finite support on both inputs. -/
theorem ghost_number_Qg : ghostNumber * Qg - Qg * ghostNumber = Qg := by
  apply LinearMap.ext
  intro v
  have hv := cubicTerm_finite v
  have hw := cubicTerm_finite (ghostNumber v)
  have hmap := hv.fun_comp (map_zero ghostNumber)
  change ghostNumber (∑ᶠ pq : ℤ × ℤ, cubicTerm pq v) -
      (∑ᶠ pq : ℤ × ℤ, cubicTerm pq (ghostNumber v)) =
        ∑ᶠ pq : ℤ × ℤ, cubicTerm pq v
  rw [map_finsum ghostNumber hv, ← finsum_sub_distrib hmap hw]
  apply finsum_congr
  intro pq
  exact LinearMap.congr_fun (cubicTerm_ghost_number pq) v

end D5.S3.Quantum.Fermionic.BcGhostBRST
