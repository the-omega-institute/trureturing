/- GID: D5/S3/ContinuousObservables/C128IdealConsequences
   generality: I
   mirror-B: D5/B/S3/ContinuousObservables/C128IdealConsequences
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Topology.UrysohnsLemma]
   utility: none
   digest: The whole matrix C0 algebra is nonzero and has no two-sided identity; whole selfadjoint ideal sections detect the ambient Jordan annihilator pointwise. -/

import D5.S3.ContinuousObservables.C128IdealJordan
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Local sections, nonunitality, and the ambient annihilator -/

noncomputable section

open Set Filter
open scoped Topology ZeroAtInfty ComplexOrder

namespace D5.S3.ContinuousObservables.C128IdealConsequences

open C0Multipliers C128ZeroExtension C128IdealJordan

private theorem upper_interval_subset : Ioo (1 / 5 : ℝ) (1 / 4) ⊆ sourceDomain := by
  intro t ht
  refine ⟨⟨by linarith [ht.1], ht.2⟩, ?_⟩
  rintro ⟨n, hn, heq⟩
  have hn' : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hrec : 1 / (n : ℝ) ≤ 1 / 5 :=
    one_div_le_one_div_of_le (by norm_num) hn'
  linarith [ht.1]

private def localSelfAdjoint (t : sourceDomain) : selfAdjoint SourceAlgebra := by
  let f := (local_unit (B := MatrixFiber) {t} isCompact_singleton).choose
  exact ⟨(1 / 2 : ℝ) • (f + star f), by
    simp only [selfAdjoint.mem_iff, star_smul, star_trivial, star_add, star_star, add_comm]⟩

private theorem localSelfAdjoint_value (t : sourceDomain) :
    (localSelfAdjoint t).val t = 1 := by
  have hf := (local_unit (B := MatrixFiber) {t} isCompact_singleton).choose_spec.2 t
    (mem_singleton t)
  change (1 / 2 : ℝ) •
    ((local_unit (B := MatrixFiber) {t} isCompact_singleton).choose t +
      star ((local_unit (B := MatrixFiber) {t} isCompact_singleton).choose t)) = 1
  rw [hf, star_one, ← two_smul ℝ (1 : MatrixFiber), smul_smul]
  norm_num

private def approach (n : ℕ) : sourceDomain :=
  ⟨1 / 4 - 1 / (40 * ((n : ℝ) + 1)), upper_interval_subset (by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hd : (40 : ℝ) ≤ 40 * ((n : ℝ) + 1) := by nlinarith
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 40) hd
    constructor
    · linarith
    · have : 0 < 1 / (40 * ((n : ℝ) + 1)) := by positivity
      linarith)⟩

private theorem approach_limit :
    Tendsto (fun n => inclusion (approach n)) atTop (𝓝 (⟨1 / 4, by norm_num⟩ : Y)) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun n : ℕ => 1 / 4 - 1 / (40 * ((n : ℝ) + 1))) atTop (𝓝 (1 / 4))
  have h : Tendsto (fun n : ℕ => (40 : ℝ)⁻¹ * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (40 : ℝ)⁻¹
  convert (tendsto_const_nhds (x := (1 / 4 : ℝ))).sub h using 1 <;>
    simp [one_div, mul_inv, mul_comm]

/-- Jordan annihilation of the whole ideal is equivalent to vanishing at every point
of U. The local sections are obtained through the inverse of the onto isometry j. -/
theorem annihilator_iff (a : X) :
    (∀ r : I, S a r.val = 0) ↔ ∀ t : sourceDomain, a.val (inclusion t) = 0 := by
  constructor
  · intro h t
    let r : I := j.symm (localSelfAdjoint t)
    have hr : r.val.val (inclusion t) = 1 := by
      have he := whole_selfadjoint_ideal.2.2.2.1 r t
      rw [show j r = localSelfAdjoint t from j.apply_symm_apply _] at he
      exact he.symm.trans (localSelfAdjoint_value t)
    have he := congrArg (fun b : X => b.val (inclusion t)) (h r)
    change (1 / 2 : ℝ) •
      (a.val (inclusion t) * r.val.val (inclusion t) +
        r.val.val (inclusion t) * a.val (inclusion t)) = 0 at he
    rw [hr, mul_one, one_mul, ← two_smul ℝ, smul_smul] at he
    norm_num at he
    exact he
  · intro h r
    apply Subtype.ext
    apply ContinuousMap.ext
    intro y
    by_cases hy : (y : ℝ) ∈ sourceDomain
    · have ha := h ⟨y, hy⟩
      change (1 / 2 : ℝ) • (a.val y * r.val.val y + r.val.val y * a.val y) = 0
      change a.val y = 0 at ha
      simp [ha]
    · change (1 / 2 : ℝ) • (a.val y * r.val.val y + r.val.val y * a.val y) = 0
      simp [r.property y hy]

/-- The whole matrix C0 algebra is nonzero and admits no two-sided multiplicative identity. -/
theorem nonzero_nonunital :
    (∃ r : I, r ≠ 0) ∧ (∃ f : SourceAlgebra, f ≠ 0) ∧
    ¬ ∃ e : SourceAlgebra, ∀ f : SourceAlgebra, e * f = f ∧ f * e = f := by
  constructor
  · let t : sourceDomain := ⟨9 / 40, upper_interval_subset (by norm_num)⟩
    have hn : ¬ ∀ r : I, S 1 r.val = 0 := by
      intro hh
      have hv := (annihilator_iff 1).mp hh t
      exact one_ne_zero hv
    push_neg at hn
    obtain ⟨r, hr⟩ := hn
    refine ⟨r, ?_⟩
    intro hz
    apply hr
    rw [hz]
    apply Subtype.ext
    simp [S]
  constructor
  · let t : sourceDomain := ⟨9 / 40, upper_interval_subset (by norm_num)⟩
    refine ⟨(localSelfAdjoint t).val, ?_⟩
    intro hz
    have h := localSelfAdjoint_value t
    rw [hz] at h
    exact zero_ne_one h
  · rintro ⟨e, he⟩
    have heval (t : sourceDomain) : e t = 1 := by
      have h := congrArg (fun f : SourceAlgebra => f t) (he (localSelfAdjoint t).val).1
      change e t * (localSelfAdjoint t).val t = (localSelfAdjoint t).val t at h
      simpa [localSelfAdjoint_value] using h
    have hquarter : (1 / 4 : ℝ) ∉ sourceDomain := by
      intro h
      exact (lt_irrefl (1 / 4 : ℝ)) h.1.2
    have hz : zeroExtension e (⟨1 / 4, by norm_num⟩ : Y) = 0 := by
      change zeroExtension e _ = 0
      have h := whole_zero_extension.2.1
      have hm : zeroExtension e ∈ wholeIdeal := by
        change extensionHom e ∈ (wholeIdeal : Set C(Y, MatrixFiber))
        rw [← h]
        exact ⟨e, rfl⟩
      exact hm _ hquarter
    have hlim : Tendsto (fun n => zeroExtension e (inclusion (approach n))) atTop (𝓝 0) := by
      have hl := (zeroExtension e).continuous.tendsto
        (⟨1 / 4, by norm_num⟩ : Y) |>.comp approach_limit
      rw [hz] at hl
      exact hl
    have hone : ∀ n, zeroExtension e (inclusion (approach n)) = 1 := fun n =>
      (whole_zero_extension.2.2.2.2.1 e (approach n)).trans (heval _)
    have : (1 : MatrixFiber) = 0 := tendsto_nhds_unique
      (tendsto_const_nhds.congr (fun n => (hone n).symm)) hlim
    exact one_ne_zero this


end D5.S3.ContinuousObservables.C128IdealConsequences
