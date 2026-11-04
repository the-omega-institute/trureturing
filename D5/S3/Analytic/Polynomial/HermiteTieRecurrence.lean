/- GID: D5/S3/Analytic/Polynomial/HermiteTieRecurrence
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/HermiteTieRecurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The full fifth-lag recurrence of the actual Hermite absolute-tie enumeration. -/

import D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders

namespace D5.S3.Analytic.Polynomial.HermiteTieRecurrence


/-- The complete one-based actual-enumeration recurrence, with integer subtraction. -/
def claim : Prop :=
  ∃ g : ℤ → ℕ,
    (∀ n : ℤ, 1 ≤ n → 0 < g n) ∧
    (∀ n m : ℤ, 1 ≤ n → n < m → g n < g m) ∧
    (∀ k : ℕ, HermiteAbsoluteTieOrders.HasExactlyTwo k ↔ ∃! n : ℤ, 1 ≤ n ∧ k = g n) ∧
    ∀ n : ℤ, 6 ≤ n →
      (g n : ℤ) = (g (n-1) : ℤ) + 2 * (g (n-2) : ℤ) -
        2 * (g (n-3) : ℤ) - (g (n-4) : ℤ) + (g (n-5) : ℤ)

private theorem formula_recurrence (t : ℕ) :
    HermiteAbsoluteTieOrders.a (t+5) = HermiteAbsoluteTieOrders.a (t+4) + 2 * HermiteAbsoluteTieOrders.a (t+3) -
      2 * HermiteAbsoluteTieOrders.a (t+2) - HermiteAbsoluteTieOrders.a (t+1) + HermiteAbsoluteTieOrders.a t := by
  simp [HermiteAbsoluteTieOrders.a, pow_add]
  ring

/-- OEIS A381737 Conjecture 2 for every order and every positive enumeration index. -/
theorem result : claim := by
  let g : ℤ → ℕ := fun n => (HermiteAbsoluteTieOrders.a n.toNat).toNat
  have hg (n : ℤ) (hn : 1 ≤ n) : (g n : ℤ) = HermiteAbsoluteTieOrders.a n.toNat := by
    exact Int.toNat_of_nonneg (HermiteAbsoluteTieOrders.result.1 _ (by omega)).le
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro n hn
    have h := HermiteAbsoluteTieOrders.result.1 n.toNat (by omega)
    rw [← hg n hn] at h
    exact_mod_cast h
  · intro n m hn hnm
    have h := HermiteAbsoluteTieOrders.result.2.1 n.toNat m.toNat (by omega) (by omega)
    rw [← hg n hn, ← hg m (by omega)] at h
    exact_mod_cast h
  · intro k
    constructor
    · intro hk
      obtain ⟨n, ⟨hn, he⟩, hu⟩ := (HermiteAbsoluteTieOrders.result.2.2 k).mp hk
      refine ⟨(n : ℤ), ⟨by omega, ?_⟩, ?_⟩
      · have hh := hg (n : ℤ) (by omega)
        simp only [Int.toNat_natCast] at hh
        exact_mod_cast (he.trans hh.symm)
      · rintro m ⟨hm, hkm⟩
        have hval : (k : ℤ) = HermiteAbsoluteTieOrders.a m.toNat := by
          rw [hkm]; exact hg m hm
        have hidx := hu m.toNat ⟨by omega, hval⟩
        omega
    · rintro ⟨n, ⟨hn, he⟩, _⟩
      apply (HermiteAbsoluteTieOrders.result.2.2 k).mpr
      refine ⟨n.toNat, ⟨by omega, ?_⟩, ?_⟩
      · rw [he]; exact hg n hn
      · rintro m ⟨hm, hem⟩
        have hval : (k : ℤ) = HermiteAbsoluteTieOrders.a n.toNat := by rw [he]; exact hg n hn
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hh := HermiteAbsoluteTieOrders.result.2.1 m n.toNat hm hlt
          omega
        · have hh := HermiteAbsoluteTieOrders.result.2.1 n.toNat m (by omega) hgt
          omega
  · intro n hn
    rw [hg n (by omega), hg (n-1) (by omega), hg (n-2) (by omega),
      hg (n-3) (by omega), hg (n-4) (by omega), hg (n-5) (by omega)]
    have hidx : n.toNat = (n-5).toNat + 5 := by omega
    have hfour : (n-1).toNat = (n-5).toNat + 4 := by omega
    have hthree : (n-2).toNat = (n-5).toNat + 3 := by omega
    have htwo : (n-3).toNat = (n-5).toNat + 2 := by omega
    have hone : (n-4).toNat = (n-5).toNat + 1 := by omega
    rw [hidx, hfour, hthree, htwo, hone]
    exact formula_recurrence (n-5).toNat

end D5.S3.Analytic.Polynomial.HermiteTieRecurrence
