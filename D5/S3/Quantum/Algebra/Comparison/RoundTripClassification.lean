/- GID: D5/S3/Quantum/Algebra/Comparison/RoundTripClassification
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Comparison/RoundTripClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2]
   utility: none
   digest: Radial comparison laws constrain the metric Lie algebra. -/
import D5.S3.Quantum.Algebra.RankOneInvariantMetric
import D5.S3.Quantum.Algebra.Comparison.RoundTripRankOne

/-! Metric Lie frames used by the rank-one comparison classification. -/

noncomputable section

open Module
open scoped InnerProductSpace

namespace D5.S3.Quantum.Algebra.Comparison.RoundTripClassification

variable {K : Type*} [LieRing K] [LieAlgebra ℝ K] [FiniteDimensional ℝ K]

attribute [local instance] LieRing.ofAssociativeRing

private theorem metric_lie_frame (B : InnerProductSpace.Core ℝ K)
    (hinv : ∀ x y z : K, B.inner ⁅x, y⁆ z = -B.inner y ⁅x, z⁆)
    (hcent : ∀ a : K, a ≠ 0 → ∀ z : K, ⁅a, z⁆ = 0 → ∃ c : ℝ, z = c • a)
    (hd : finrank ℝ K = 3) :
    ∃ (b : Basis (Fin 3) ℝ K) (μ : ℝ), 0 < μ ∧
      (∀ i j : Fin 3, B.inner (b i) (b j) = if i = j then 1 else 0) ∧
      ⁅b 0, b 1⁆ = μ • b 2 ∧
      ⁅b 1, b 2⁆ = μ • b 0 ∧
      ⁅b 2, b 0⁆ = μ • b 1 := by
  classical
  let : NormedAddCommGroup K := B.toNormedAddCommGroup
  let : InnerProductSpace ℝ K := InnerProductSpace.ofCore B.toCore
  let i : Fin (finrank ℝ K) := ⟨0, by omega⟩
  let a : K := stdOrthonormalBasis ℝ K i
  have haunit : ‖a‖ = 1 := (stdOrthonormalBasis ℝ K).norm_eq_one i
  have ha : a ≠ 0 := by
    intro hz
    have hh := haunit
    simp [hz] at hh
  let br : K →ₗ[ℝ] K →ₗ[ℝ] K := (LieAlgebra.ad ℝ K).toLinearMap
  have hn : br a ≠ 0 := by
    intro hz
    have hle : finrank ℝ K ≤ 1 := finrank_le_one a (fun z => by
      obtain ⟨c, hc⟩ := hcent a ha z (DFunLike.congr_fun hz z)
      exact ⟨c, hc.symm⟩)
    omega
  obtain ⟨μ, u, v, hμ, hu, hv, hau0, hav0, huv0, hau, hav, huv, _⟩ :=
    D5.S3.Quantum.Algebra.RankOneInvariantMetric.min_frame br
      (fun z => lie_self z) (fun x y z => leibniz_lie x y z)
      a haunit hinv (hcent a ha) hn
  change ⁅a, u⁆ = μ • v at hau
  change ⁅a, v⁆ = -μ • u at hav
  change ⁅u, v⁆ = μ • a at huv
  have hua0 : ⟪u, a⟫_ℝ = 0 := by rw [real_inner_comm]; exact hau0
  have hva0 : ⟪v, a⟫_ℝ = 0 := by rw [real_inner_comm]; exact hav0
  have hvu0 : ⟪v, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact huv0
  let e : Fin 3 → K := ![a, u, v]
  have horth : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [e, haunit, hu, hv, hau0, hav0, huv0, hua0, hva0, hvu0,
        real_inner_self_eq_norm_sq]
  let b : Basis (Fin 3) ℝ K :=
    basisOfOrthonormalOfCardEqFinrank horth (by simp [hd])
  have hb (i : Fin 3) : b i = e i := by
    exact congrFun (coe_basisOfOrthonormalOfCardEqFinrank horth (by simp [hd])) i
  refine ⟨b, μ, hμ, ?_, ?_, ?_, ?_⟩
  · intro i j
    change ⟪b i, b j⟫_ℝ = if i = j then 1 else 0
    rw [hb, hb]
    exact (orthonormal_iff_ite.mp horth) i j
  · simpa [hb, e] using hau
  · simpa [hb, e] using huv
  · have hva : ⁅v, a⁆ = μ • u := by
      rw [← lie_skew, hav]
      simp
    simpa [hb, e] using hva

attribute [local instance 100] LieRing.ofAssociativeRing
set_option backward.isDefEq.respectTransparency false

open RoundTripComparison RoundTripRankOne

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] {L : LieSubalgebra ℝ A} {G : Subgroup Aˣ}

/-- The full infinitesimal classification from a faithful bounded round-trip comparison. -/
theorem comparison_classification (D : Data L G) :
    (∀ X : L, 0 ≤ D.h X X) ∧
    (∀ X : L, D.h X X = 0 → X = 0) ∧
    (∀ (t : ℝ) (X : L),
      D.phi (D.exp (t • X)) = Real.cos (t*Real.sqrt (D.h X X/2))^2) ∧
    (∀ (t : ℝ) (X : L),
      D.exp (t • X) = 1 ↔ ∃ n : ℤ, t*Real.sqrt (D.h X X/2) = Real.pi*n) ∧
    (∀ X Y : L, ⁅X,Y⁆ = 0 → X = 0 ∨ ∃ c : ℝ, Y = c • X) ∧
    (∀ C X Y : L, D.h ⁅C,X⁆ Y + D.h X ⁅C,Y⁆ = 0) ∧
    (finrank ℝ L = 0 ∨ finrank ℝ L = 1 ∨ finrank ℝ L = 3) ∧
    (finrank ℝ L = 3 →
      ∃ (b : Basis (Fin 3) ℝ L) (μ : ℝ), 0 < μ ∧
        (∀ i j : Fin 3, D.h (b i) (b j) = if i = j then 1 else 0) ∧
        ⁅b 0,b 1⁆ = μ • b 2 ∧ ⁅b 1,b 2⁆ = μ • b 0 ∧ ⁅b 2,b 0⁆ = μ • b 1) := by
  classical
  obtain ⟨hnonneg, hdef, hcos, hperiod, hinv⟩ := metric_consequences D
  have hcent := centralizer_line D
  let B := metricCore D
  have hinv' (x y z : L) : B.inner ⁅x,y⁆ z = -B.inner y ⁅x,z⁆ := by
    change D.h ⁅x,y⁆ z = -D.h y ⁅x,z⁆
    linarith [hinv x y z]
  have hdim : finrank ℝ L = 0 ∨ finrank ℝ L = 1 ∨ finrank ℝ L = 3 := by
    by_cases hz : ∀ x : L, x = 0
    · letI : Subsingleton L := ⟨fun x y => (hz x).trans (hz y).symm⟩
      exact Or.inl (finrank_zero_of_subsingleton (R := ℝ) (M := L))
    · push Not at hz
      obtain ⟨x, hx⟩ := hz
      exact Or.inr (D5.S3.Quantum.Algebra.RankOneInvariantMetric.finrank_eq_one_or_three
        B hinv' x hx (hcent x hx))
  refine ⟨hnonneg, hdef, hcos, hperiod, ?_, hinv, hdim, ?_⟩
  · intro X Y hXY
    by_cases hX : X = 0
    · exact Or.inl hX
    · exact Or.inr (hcent X hX Y hXY)
  · intro hd
    exact metric_lie_frame B hinv' hcent hd

end D5.S3.Quantum.Algebra.Comparison.RoundTripClassification
