/- GID: D5/S3/Constants/SelfSimilar/GoldenCompatibleIFS
   generality: I
   mirror-B: D5/B/S3/Constants/SelfSimilar/GoldenCompatibleIFS
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite nonempty golden IFSs with positive exponents have unique compact attractors. -/

import Mathlib

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'golden_compatible_ifs_has_unique_attractor' D5 Golden/Frozen/accepted`
     returned no hit; repository searches for `IFS`, `attractor`, `Hutchinson`,
     `self-similar`, and `Moran` found no public or private attractor theorem.
   * `D5.S3.Constants.MoranComplexDimensions.moran_complex_dimension` concerns the
     complexified Moran equation only, so it supplies no compact-set fixed point.
   * Pinned mathlib has no IFS or Hutchinson theorem, but it supplies the complete
     Hausdorff metric space `NonemptyCompacts`, its finite-union operation, and
     `ContractingWith.fixedPoint_isFixedPt` / `ContractingWith.fixedPoint_unique`.
     The proof below lifts the branch similarities to the Hutchinson operator and
     applies these Banach fixed-point declarations rather than reproving Banach. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.SelfSimilar.GoldenCompatibleIFS

open scoped NNReal
open TopologicalSpace

/-- Finite planar IFS data whose branch exponents are positive and whose rotation
indices prescribe the angles `2 * pi * {m_i * phi}`. -/
structure GoldenIFS (ι : Type*) where
  exponent : ι → ℕ
  exponent_pos : ∀ i, 0 < exponent i
  rotationIndex : ι → ℤ
  translation : ι → ℂ

/-- The prescribed golden rotation angle `2 * pi * {m * phi}`. -/
noncomputable def rotationAngle (m : ℤ) : ℝ :=
  2 * Real.pi * Int.fract ((m : ℝ) * Real.goldenRatio)

/-- The branch `z ↦ phi^(-k_i) R_(theta_i) z + t_i`, represented on the complex plane. -/
noncomputable def GoldenIFS.branch {ι : Type*} (S : GoldenIFS ι) (i : ι) (z : ℂ) : ℂ :=
  ((Real.goldenRatio⁻¹ ^ S.exponent i : ℝ) : ℂ) *
      Complex.exp ((rotationAngle (S.rotationIndex i) : ℂ) * Complex.I) * z +
    S.translation i

/-- Each affine complex branch is continuous. -/
theorem branch_continuous {ι : Type*} (S : GoldenIFS ι) (i : ι) :
    Continuous (S.branch i) := by
  unfold GoldenIFS.branch
  fun_prop

/-- Each golden-compatible branch has exact contraction ratio `phi^(-k_i)`. -/
theorem branch_dist_eq {ι : Type*} (S : GoldenIFS ι) (i : ι) (x y : ℂ) :
    dist (S.branch i x) (S.branch i y) =
      Real.goldenRatio⁻¹ ^ S.exponent i * dist x y := by
  have hratio : 0 < Real.goldenRatio⁻¹ ^ S.exponent i := by
    positivity
  rw [Complex.dist_eq, Complex.dist_eq]
  calc
    ‖S.branch i x - S.branch i y‖ =
        ‖((Real.goldenRatio⁻¹ ^ S.exponent i : ℝ) : ℂ) *
          Complex.exp ((rotationAngle (S.rotationIndex i) : ℂ) * Complex.I) *
            (x - y)‖ := by
      congr 1
      simp only [GoldenIFS.branch]
      ring
    _ = Real.goldenRatio⁻¹ ^ S.exponent i * ‖x - y‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real,
        Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs, abs_of_pos hratio]
      ring

/-- The common upper bound `phi⁻¹` for all positive-exponent branch ratios. -/
noncomputable def goldenContraction : ℝ≥0 :=
  ⟨Real.goldenRatio⁻¹, by positivity⟩

/-- A positive exponent makes the exact branch ratio strictly smaller than one. -/
theorem branch_ratio_lt_one {ι : Type*} (S : GoldenIFS ι) (i : ι) :
    Real.goldenRatio⁻¹ ^ S.exponent i < 1 := by
  exact pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
    (Nat.ne_of_gt (S.exponent_pos i))

/-- The image of a nonempty compact set under one branch. -/
noncomputable def GoldenIFS.compactBranch {ι : Type*} (S : GoldenIFS ι) (i : ι)
    (K : NonemptyCompacts ℂ) : NonemptyCompacts ℂ :=
  K.map (S.branch i) (branch_continuous S i)

/-- The Hutchinson operator, the finite union of all branch images. -/
noncomputable def GoldenIFS.hutchinson {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : GoldenIFS ι) (K : NonemptyCompacts ℂ) : NonemptyCompacts ℂ :=
  Finset.univ.sup' Finset.univ_nonempty fun i ↦ S.compactBranch i K

private theorem compactBranch_lipschitz {ι : Type*} (S : GoldenIFS ι) (i : ι) :
    LipschitzWith goldenContraction (S.compactBranch i) := by
  apply LipschitzWith.of_dist_le_mul
  intro K L
  change Metric.hausdorffDist ((S.branch i) '' (K : Set ℂ))
      ((S.branch i) '' (L : Set ℂ)) ≤
    Real.goldenRatio⁻¹ * Metric.hausdorffDist (K : Set ℂ) L
  have hpoint : ∀ (A B : NonemptyCompacts ℂ) (x : ℂ), x ∈ A →
      ∃ y ∈ B, dist (S.branch i x) (S.branch i y) ≤
        Real.goldenRatio⁻¹ * Metric.hausdorffDist (A : Set ℂ) B := by
    intro A B x hx
    obtain ⟨y, hy, hxy⟩ := B.isCompact.exists_infDist_eq_dist B.nonempty x
    refine ⟨y, hy, ?_⟩
    have hfinite : Metric.hausdorffEDist (A : Set ℂ) B ≠ ⊤ :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded A.nonempty B.nonempty
        A.isCompact.isBounded B.isCompact.isBounded
    have hdist : dist x y ≤ Metric.hausdorffDist (A : Set ℂ) B := by
      rw [← hxy]
      exact Metric.infDist_le_hausdorffDist_of_mem hx hfinite
    rw [branch_dist_eq]
    apply mul_le_mul
    · exact pow_le_of_le_one (by positivity)
        (le_of_lt (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio))
        (Nat.ne_of_gt (S.exponent_pos i))
    · exact hdist
    · exact dist_nonneg
    · positivity
  apply Metric.hausdorffDist_le_of_mem_dist
  · exact mul_nonneg (by positivity) Metric.hausdorffDist_nonneg
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hpoint K L x hx
    exact ⟨S.branch i y, ⟨y, hy, rfl⟩, hxy⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hyx⟩ := hpoint L K y hy
    exact ⟨S.branch i x, ⟨x, hx, rfl⟩, by
      simpa only [Metric.hausdorffDist_comm] using hyx⟩

private theorem finite_hutchinson_lipschitz {ι : Type*} (S : GoldenIFS ι)
    (s : Finset ι) (hs : s.Nonempty) :
    LipschitzWith goldenContraction
      (fun K ↦ s.sup' hs fun i ↦ S.compactBranch i K) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
      simpa only [Finset.sup'_singleton] using compactBranch_lipschitz S i
  | cons i s hi hs ih =>
      simp only [Finset.sup'_cons hs]
      simpa only [Function.comp_def, one_mul, max_self] using
        TopologicalSpace.NonemptyCompacts.lipschitz_sup.comp
          ((compactBranch_lipschitz S i).prodMk ih)

/-- The finite-union Hutchinson operator is a contraction with common bound `phi⁻¹`. -/
theorem hutchinson_contracting {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : GoldenIFS ι) : ContractingWith goldenContraction S.hutchinson := by
  constructor
  · change Real.goldenRatio⁻¹ < (1 : ℝ)
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  · exact finite_hutchinson_lipschitz S Finset.univ Finset.univ_nonempty

/-- Every finite nonempty golden-compatible planar IFS has a unique nonempty compact
attractor satisfying `F = ⋃ i, S_i '' F`. -/
theorem golden_compatible_ifs_has_unique_attractor {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : GoldenIFS ι) : ∃! F : NonemptyCompacts ℂ, F = S.hutchinson F := by
  let hcontract := hutchinson_contracting S
  let F := hcontract.fixedPoint S.hutchinson
  refine ⟨F, hcontract.fixedPoint_isFixedPt.symm, ?_⟩
  intro K hK
  exact hcontract.fixedPoint_unique hK.symm

/-- A concrete two-branch golden-compatible IFS used as an executable smoke instance. -/
noncomputable def goldenBinaryIFS : GoldenIFS (Fin 2) where
  exponent := fun _ ↦ 1
  exponent_pos := fun _ ↦ Nat.zero_lt_succ 0
  rotationIndex := fun i ↦ if i = 0 then 0 else 1
  translation := fun i ↦ if i = 0 then 0 else 1

example : ∃! F : NonemptyCompacts ℂ, F = goldenBinaryIFS.hutchinson F :=
  golden_compatible_ifs_has_unique_attractor goldenBinaryIFS

#print axioms golden_compatible_ifs_has_unique_attractor

end D5.S3.Constants.SelfSimilar.GoldenCompatibleIFS
