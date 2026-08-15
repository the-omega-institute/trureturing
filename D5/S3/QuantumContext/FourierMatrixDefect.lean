/- GID: D5/S3/QuantumContext/FourierMatrixDefect
   generality: G
   mirror-B: D5/B/S3/QuantumContext/FourierMatrixDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Relate Fourier-matrix defect to divisor supply and characterize its vanishing. -/

/- Library-search audit trail (2026-08-15):
   * Loogle query `Nat.totient ?_ = ?_` found the exact fiber-count theorem
     `Nat.totient_div_of_dvd`; it is imported and applied below.
   * Loogle found no declaration matching the full divisor-supply identity
     `(sum d in n.divisors, Nat.totient d * (n / d - 1)) = x`.
   * Pinned mathlib also supplies `Nat.sum_div_divisors`,
     `Finset.sum_fiberwise_of_maps_to'`, and `Nat.exists_dvd_of_not_prime2`;
     all three are applied rather than reproved.
   * No local Loogle or LeanSearch executable was installed. A LeanSearch API
     attempt returned a parser error, and repository searches found no theorem
     with this gcd-sum statement and prime vanishing criterion.
-/

import Mathlib.Data.Nat.Totient

open scoped BigOperators

namespace D5.S3.QuantumContext.FourierMatrixDefect

/-- Arithmetic defect of the order-`n` Fourier matrix: each nonzero residue
contributes one less than the size of its common-divisor fiber with `n`. -/
def fourierDefect (n : Nat) : Nat :=
  ∑ k ∈ Finset.Ico 1 n, (Nat.gcd n k - 1)

/-- The Fourier-matrix defect is supplied exactly by nontrivial divisors, and
for orders at least two it vanishes exactly at prime orders. -/
theorem fourier_defect_factor_supply (n : Nat) (hn : 2 ≤ n) :
    fourierDefect n =
        ∑ d ∈ n.divisors.erase 1, Nat.totient d * (n / d - 1) ∧
      (fourierDefect n = 0 ↔ n.Prime) := by
  have hn0 : n ≠ 0 := by omega
  have hMaps : ∀ k ∈ Finset.range n, Nat.gcd n k ∈ n.divisors := by
    intro k hk
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n k, hn0⟩
  have hFactorSupply :
      fourierDefect n =
        ∑ d ∈ n.divisors.erase 1, Nat.totient d * (n / d - 1) := by
    have hFull :
        (∑ k ∈ Finset.range n, (Nat.gcd n k - 1)) =
          ∑ d ∈ n.divisors, Nat.totient d * (n / d - 1) := by
      calc
        (∑ k ∈ Finset.range n, (Nat.gcd n k - 1)) =
            ∑ d ∈ n.divisors,
              ∑ k ∈ Finset.range n with Nat.gcd n k = d, (d - 1) := by
                symm
                exact Finset.sum_fiberwise_of_maps_to' hMaps (fun d => d - 1)
        _ = ∑ d ∈ n.divisors,
              (Finset.filter (fun k => Nat.gcd n k = d) (Finset.range n)).card *
                (d - 1) := by
                apply Finset.sum_congr rfl
                intro d hd
                exact Finset.sum_const_nat (fun _ _ => rfl)
        _ = ∑ d ∈ n.divisors,
              Nat.totient (n / d) * (d - 1) := by
                apply Finset.sum_congr rfl
                intro d hd
                rw [Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]
        _ = ∑ d ∈ n.divisors,
              Nat.totient d * (n / d - 1) := by
                rw [← Nat.sum_div_divisors n
                  (fun d => Nat.totient d * (n / d - 1))]
                apply Finset.sum_congr rfl
                intro d hd
                rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn0]
    have hRange : Finset.range n = insert 0 (Finset.Ico 1 n) := by
      ext k
      simp
      omega
    have hLeft :
        (∑ k ∈ Finset.range n, (Nat.gcd n k - 1)) =
          (n - 1) + fourierDefect n := by
      rw [hRange]
      simp [fourierDefect]
    have hOne : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn0
    have hRight :
        (∑ d ∈ n.divisors, Nat.totient d * (n / d - 1)) =
          (n - 1) + ∑ d ∈ n.divisors.erase 1,
            Nat.totient d * (n / d - 1) := by
      rw [← Finset.insert_erase hOne,
        Finset.sum_insert (Finset.notMem_erase 1 n.divisors)]
      simp
    rw [hLeft, hRight] at hFull
    exact Nat.add_left_cancel hFull
  refine ⟨hFactorSupply, ?_⟩
  constructor
  · intro hzero
    by_contra hnp
    obtain ⟨d, hdvd, hd2, hdlt⟩ := Nat.exists_dvd_of_not_prime2 hn hnp
    have hdMem : d ∈ Finset.Ico 1 n := Finset.mem_Ico.mpr ⟨by omega, hdlt⟩
    have hgcd : Nat.gcd n d = d := Nat.gcd_eq_right_iff_dvd.mpr hdvd
    have hpos : 0 < Nat.gcd n d - 1 := by omega
    have hle : Nat.gcd n d - 1 ≤ fourierDefect n := by
      unfold fourierDefect
      exact Finset.single_le_sum
        (s := Finset.Ico 1 n) (f := fun k => Nat.gcd n k - 1)
        (fun _ _ => Nat.zero_le _) hdMem
    omega
  · intro hp
    rw [hFactorSupply, hp.divisors]
    have hErase : ({1, n} : Finset Nat).erase 1 = {n} := by
      simp [hp.ne_one.symm]
    rw [hErase]
    simp only [Finset.sum_singleton]
    rw [Nat.div_self hp.pos]
    simp

end D5.S3.QuantumContext.FourierMatrixDefect
