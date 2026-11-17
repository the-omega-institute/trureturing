/- GID: D5/S3/Combinatorics/Partitions/ColouredEulerLedger
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/ColouredEulerLedger
   mirror-E: none(waiver:symbolic-partition-cardinality)
   anchors: []
   utility: none
   digest: Actual finite coloured partitions have the coefficients of the existing integer Euler ledger. -/

/- admission_basis: escape-witness. Proposed content: coloured_coefficient
identifies the independent finite sigma/Pi/Sym carrier with the existing Euler
ledger through Mathlib's weighted partition generating function and actual
infinite-product uniqueness. utility none: no bounded enumeration or finite
certified instance. This extends the actual objects, not a requested-count
definition of an exponential coefficient. -/

import D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Data.Sym.Card
import D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity

noncomputable section

namespace D5.S3.Combinatorics.Partitions.ColouredEulerLedger

open PowerSeries Finset
open scoped PowerSeries.WithPiTopology
open D5.S1.Recurrence.Witt.PrimitiveEulerLedger
open D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality

/-- For each part size, a multiset of its colours records the colours of its
indistinguishable occurrences. The outer partition fixes all multiplicities. -/
abbrev ColouredPartition (colors : ℕ → ℕ) (n : ℕ) :=
  Σ p : Nat.Partition n,
    (d : ↥p.parts.toFinset) → Sym (Fin (colors d.1)) (p.parts.count d.1)

private theorem card_eq_genFun (colors : ℕ → ℕ) (n : ℕ) :
    (Nat.card (ColouredPartition colors n) : ℤ) =
      coeff n (Nat.Partition.genFun
        (fun d m => (Nat.multichoose (colors d) m : ℤ))) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma, Nat.cast_sum,
    Nat.Partition.coeff_genFun]
  apply sum_congr rfl
  intro p hp
  simp only [Fintype.card_pi, Sym.card_sym_fin_eq_multichoose, Nat.cast_prod]
  simp only [Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  exact Finset.prod_coe_sort p.parts.toFinset
    (fun d => (Nat.multichoose (colors d) (p.parts.count d) : ℤ))

private theorem coeff_euler_nat (n r N : ℕ) :
    coeff N (eulerFactor n (r : ℤ)) =
      if n ∣ N then (Nat.multichoose r (N / n) : ℤ) else 0 := by
  rw [coeff_eulerFactor]
  split_ifs with h
  · rw [Ring.choose_neg', Units.smul_def, Int.coe_negOnePow_natCast]
    have hm : Ring.multichoose (r : ℤ) (N / n) =
        (Nat.multichoose r (N / n) : ℤ) := by
      change (Nat.choose (r + N / n - 1) (N / n) : ℤ) = _
      rw [Nat.multichoose_eq]
    rw [hm, smul_eq_mul, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    norm_num
  · rfl

private theorem local_factor (n r : ℕ) (hn : n ≠ 0) :
    (1 : PowerSeries ℤ) + ∑' j : ℕ,
      (Nat.multichoose r (j + 1) : ℤ) • X ^ (n * (j + 1)) =
        eulerFactor n (r : ℤ) := by
  exact D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.local_factor_of_coeff
    (fun m => (Nat.multichoose r m : ℤ)) (by simp) n hn _ (coeff_euler_nat n r)

/-- The actual generic finite-colour count is the coefficient of the existing
Euler object; it is independent of any definition of a target exponential. -/
theorem coloured_coefficient (colors : ℕ → ℕ) (n : ℕ) :
    coeff n (eulerSeries (fun i => (colors (i + 1) : ℤ))) =
      (Nat.card (ColouredPartition colors n) : ℤ) := by
  classical
  have hg := Nat.Partition.hasProd_genFun
    (fun d m => (Nat.multichoose (colors d) m : ℤ))
  have hp : HasProd (fun i => eulerFactor (i + 1) (colors (i + 1) : ℤ))
      (Nat.Partition.genFun (fun d m => (Nat.multichoose (colors d) m : ℤ))) := by
    convert hg using 1
    funext i
    exact (local_factor (i + 1) (colors (i + 1)) (by omega)).symm
  have he := (hasProd_eulerSeries (fun i => (colors (i + 1) : ℤ))).unique hp
  rw [he, ← card_eq_genFun]

end D5.S3.Combinatorics.Partitions.ColouredEulerLedger
