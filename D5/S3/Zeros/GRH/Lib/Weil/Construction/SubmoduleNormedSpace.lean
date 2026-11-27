/- GID: D5/S3/Zeros/GRH/Lib/Weil/Construction/SubmoduleNormedSpace
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Construction/SubmoduleNormedSpace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Construction.SubmoduleNormedSpace. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Construction/SubmoduleNormedSpace.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Groups.ValuationPair
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Elementary identities for the Heisenberg bicharacter and the vacuum function. Heisenberg
representation twisted by a group element preserving the cocycle. Shortcut instance: a complex
subspace of a normed space is normed. -/

attribute [simp] Heisenberg.norm_eq_one Heisenberg.self_eq_one Heisenberg.Rep.norm_map
  Heisenberg.Rep.mul Heisenberg.MultiplierAction.Δ_one Heisenberg.MultiplierAction.Δ_inv

attribute [fun_prop] Heisenberg.cont Heisenberg.Rep.cont

variable {W} [AddCommGroup W] [TopologicalSpace W] {H : Heisenberg W} {X} [NormedAddCommGroup X]
  [NormedSpace ℂ X] (R : H.Rep X) (x y w) {_ : MeasurableSpace W} {μ e}

namespace Heisenberg

@[simp] lemma β_ne_zero : H.β x y ≠ 0 := by simp [← norm_pos_iff]

@[simp] lemma β_zero_left : H.β 0 y = 1 := by simpa using H.2 0 0 y

@[simp] lemma β_mul_β : H.β x y * H.β y x = 1 := by simpa [↓H.2, H.3] using H.4 (x + y)

@[simp] lemma β_zero_right : H.β y 0 = 1 := by simpa using H.3 y 0 0

@[simp] lemma β_neg_left : H.β (-x) y = H.β y x := inv_unique (by simp [← H.2]) (β_mul_β ..)

@[simp] lemma β_neg_right : H.β x (-y) = H.β y x := by rw [← β_neg_left, neg_neg]

@[simp] lemma conj_β : starRingEnd ℂ (H.β x y) = H.β y x := by simp [← Complex.inv_eq_conj, field]

@[simp] lemma Rep.rho_zero_apply : R.ρ 0 w = w := eq_of_norm_sub_eq_zero (by simp [← R.3 0])

lemma IsVacuum.integral_norm_sq_eq_one (he :
  H.IsVacuum μ e) : ∫ x, ‖e x‖ ^ 2 ∂μ = 1 := by simpa [he.2, he.3, he.4,
  ← Complex.ofReal_inj, ← integral_complex_ofReal, ← Complex.mul_conj'] using he.5 0 0

lemma IsVacuum.norm_le_one (he : H.IsVacuum μ e) : ‖e x‖ ≤ 1 := by simpa [he.3, ← sq,
  he.integral_norm_sq_eq_one] using (he.5 x x ▸ MeasureTheory.norm_integral_le_integral_norm _ :)

end Heisenberg

variable {W : _} [AddCommGroup W] [TopologicalSpace W] {H : Heisenberg W} [MeasurableSpace W] {μ e
  X : _} [NormedAddCommGroup X] [NormedSpace ℂ X] (R : H.Rep X) {G} [Group G] [TopologicalSpace G]
  [DistribMulAction G W] [ContinuousSMul G W] {c} (A : H.MultiplierAction μ e G c)

/-- For a Heisenberg representation ρ, an action A of G on W preserving β, and g in G, the
Heisenberg representation x ↦ ρ(gx) on the same space. -/
@[simps] def Heisenberg.Rep.moveBy (g : G) : H.Rep X :=
  ⟨(R.ρ <| g • ·), by simp [A.1], by simp, by fun_prop⟩

@[simp] lemma Heisenberg.Rep.moveBy_one : R.moveBy A 1 = R := by simp [moveBy]

noncomputable instance {E} [NormedAddCommGroup E] [NormedSpace ℂ E] (V : Submodule ℂ E) :
    @NormedSpace ℂ V _ NormedAddCommGroup.toSeminormedAddCommGroup := V.normedSpace
