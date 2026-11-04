/- GID: D5/S3/Combinatorics/Geometry/MiuraCoreNormal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraCoreNormal
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Actual joint deletion terminates in a residual core with isolated frozen lines. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraCoreJoint
import all D5.S3.Combinatorics.Geometry.MiuraCoreJoint

/-! Termination and simultaneous irreducibility on the original actual rectangle. -/

@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraCoreNormal
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreContract
  MiuraCoreResidual MiuraCoreJoint MiuraSlabIncidence MiuraCoreTranspose

open private joint_trans from D5.S3.Combinatorics.Geometry.MiuraCoreJoint

/-- There is no legal consecutive pair left to shorten. -/
def NoAdjacentFrozen {m n : ℕ} (h : Cell m n → ℤ) : Prop :=
  ¬ ∃ j k : Fin n, j.val + 1 = k.val ∧ frozenColumn h j ∧ frozenColumn h k

private theorem normalize_exists (a b : ℕ) :
    ∀ s m n (h : Cell m n → ℤ), m + n = s → 2 ≤ m → 2 ≤ n → Residual a b h →
      ∃ (M N : ℕ) (g : Cell M N → ℤ),
        2 ≤ M ∧ M ≤ m ∧ 2 ≤ N ∧ N ≤ n ∧ JointReduction h g ∧ Residual a b g ∧
          NoAdjacentFrozen g ∧ NoAdjacentFrozen (transposeHeight g) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro m n h hsum hm hn hr
    classical
    by_cases hc : ∃ j k : Fin n,
        j.val + 1 = k.val ∧ frozenColumn h j ∧ frozenColumn h k
    · obtain ⟨j, k, hjk, hj, hk⟩ := hc
      have hn' : 2 ≤ n - 1 := by have := hk.2.1; have := hj.1; omega
      have hr' := contractAt_residual a b h (by omega) j hj hr
      obtain ⟨M, N, g, hMlo, hMhi, hNlo, hNhi, hchain, hg, hc', hr'⟩ :=
        ih (m + (n - 1)) (by omega) m (n - 1)
          (contractAt h (by omega) j hj) rfl hm hn' hr'
      exact ⟨M, N, g, hMlo, hMhi, hNlo, by omega,
        .column h (by omega) j k hj hk hjk hchain, hg, hc', hr'⟩
    · by_cases hrw : ∃ i k : Fin m,
          i.val + 1 = k.val ∧ frozenColumn (transposeHeight h) i ∧
            frozenColumn (transposeHeight h) k
      · obtain ⟨i, k, hik, hi, hk⟩ := hrw
        have hm' : 2 ≤ m - 1 := by have := hk.2.1; have := hi.1; omega
        have hres := contractRow_residual a b h (by omega) i hi hr
        obtain ⟨M, N, g, hMlo, hMhi, hNlo, hNhi, hchain, hg, hc', hr'⟩ :=
          ih ((m - 1) + n) (by omega) (m - 1) n
            (contractRow h (by omega) i hi) rfl hm' hn hres
        exact ⟨M, N, g, hMlo, by omega, hNlo, hNhi,
          .row h (by omega) i k hi hk hik hchain, hg, hc', hr'⟩
      · exact ⟨m, n, h, hm, le_rfl, hn, le_rfl, .refl h, hr, hc, hrw⟩

/-- A simultaneous finite residual core has no adjacent frozen lines on either axis. -/
theorem residual_reduced_joint_core_exists {m n : ℕ}
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : Cell m n → ℤ) (hm : 2 ≤ m) (hn : 2 ≤ n) (hr : Residual a b h) :
    ∃ (M N : ℕ) (g : Cell M N → ℤ),
      2 ≤ M ∧ M ≤ 2 * (a + b) - 1 ∧ 2 ≤ N ∧ N ≤ 2 * (a + b) - 1 ∧
        JointReduction h g ∧ Residual a b g ∧
          NoAdjacentFrozen g ∧ NoAdjacentFrozen (transposeHeight g) := by
  obtain ⟨M, N, g, hMlo, hMhi, hNlo, hNhi, hchain, hg⟩ :=
    residual_joint_bounded_core_exists a b ha hb h hm hn hr
  obtain ⟨P, Q, f, hPlo, hPhi, hQlo, hQhi, htail, hf, hc, hrw⟩ :=
    normalize_exists a b (M + N) M N g rfl hMlo hNlo hg
  exact ⟨P, Q, f, hPlo, hPhi.trans hMhi, hQlo, hQhi.trans hNhi,
    joint_trans hchain htail, hf, hc, hrw⟩

end D5.S3.Combinatorics.Geometry.MiuraCoreNormal
