/- GID: D5/S3/Combinatorics/Geometry/MiuraCoreReduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraCoreReduction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Actual residual arrays admit bounded-width chains of signed frozen deletions. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraCoreResidual

/-! A finite one-axis reduction retains the original actual-array relation. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraCoreReduction

open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreContract MiuraCoreResidual

/-- Every step deletes a column from a run containing two actual frozen columns. -/
inductive ColumnReduction {m : ℕ} :
    {n : ℕ} → (Cell m n → ℤ) → {N : ℕ} → (Cell m N → ℤ) → Prop where
  | refl {n : ℕ} (h : Cell m n → ℤ) : ColumnReduction h h
  | step {n N : ℕ} (h : Cell m n → ℤ) (hm : 0 < m) (j k : Fin n)
      (hj : frozenColumn h j) (hk : frozenColumn h k) (hjk : j.val + 1 = k.val)
      {g : Cell m N → ℤ} (tail : ColumnReduction (contractAt h hm j hj) g) :
      ColumnReduction h g

/-- The bounded-width residual is obtained from this very array by actual signed deletions. -/
theorem residual_column_core_exists {m n : ℕ} (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : 0 < m) (h : Cell m n → ℤ) (hn : 2 ≤ n) (hr : Residual a b h) :
    ∃ (N : ℕ) (g : Cell m N → ℤ), 2 ≤ N ∧ N ≤ 2 * (a + b) - 1 ∧
      ColumnReduction h g ∧ Residual a b g := by
  have go : ∀ n (h : Cell m n → ℤ), 2 ≤ n → Residual a b h →
      ∃ (N : ℕ) (g : Cell m N → ℤ), 2 ≤ N ∧ N ≤ 2 * (a + b) - 1 ∧
        ColumnReduction h g ∧ Residual a b g := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro h hn hr
      by_cases hsmall : n ≤ 2 * (a + b) - 1
      · exact ⟨n, h, hn, hsmall, .refl h, hr⟩
      · obtain ⟨j, k, hj, hjk, hk, hcontract⟩ :=
          residual_width_reduction a b h hm hn hr (by omega)
        have hn' : 2 ≤ n - 1 := by omega
        obtain ⟨N, g, hNlo, hNhi, hchain, hg⟩ :=
          ih (n - 1) (by omega) (contractAt h hm j hj) hn' hcontract
        exact ⟨N, g, hNlo, hNhi, .step h hm j k hj hk hjk hchain, hg⟩
  exact go n h hn hr

end D5.S3.Combinatorics.Geometry.MiuraCoreReduction
