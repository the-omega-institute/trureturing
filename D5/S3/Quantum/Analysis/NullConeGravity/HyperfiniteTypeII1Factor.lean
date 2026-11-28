/- GID: D5/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/HyperfiniteTypeII1Factor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dyadic matrix traces, projection equivalence, and minus-sided affine covariance on Lebesgue L². -/

import OmegaBuild.Commands
import D5.S3.MeasureTheory.AffineTranslationSpectrum
import D5.S3.MeasureTheory.AffineStrongContinuity
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecificLimits.Basic
import D5.S3.LinearAlgebra.Matrix.ProjectionSpectrum
import D5.S3.OperatorAlgebra.TracialRegularRepresentation
import D5.S3.OperatorAlgebra.NormalVectorFunctional

/-! Normalized traces on finite matrix algebras and their dyadic direct limit. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Analysis.NullConeGravity.HyperfiniteTypeII1Factor

open Matrix Unitary
open scoped ComplexOrder

/-- Complex square matrices of dimension `d`. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- The matrix algebra at level `n` of the dyadic tower. -/
abbrev Stage (n : ℕ) := Mat (2 ^ n)

/-- The ordinary trace divided by the dimension. -/
def normalizedTrace (d : ℕ) : Mat d →ₗ[ℂ] ℂ :=
  ((d : ℂ)⁻¹) • traceLinearMap (Fin d) ℂ ℂ

private theorem normalizedTrace_apply (d : ℕ) (a : Mat d) :
    normalizedTrace d a = (d : ℂ)⁻¹ * trace a := rfl

theorem normalizedTrace_one {d : ℕ} (hd : 0 < d) :
    normalizedTrace d 1 = 1 := by
  rw [normalizedTrace_apply, trace_one, Fintype.card_fin]
  exact inv_mul_cancel₀ (by exact_mod_cast hd.ne')

theorem normalizedTrace_mul_comm {d : ℕ} (a b : Mat d) :
    normalizedTrace d (a * b) = normalizedTrace d (b * a) := by
  simp only [normalizedTrace_apply, trace_mul_comm a b]

theorem normalizedTrace_star {d : ℕ} (a : Mat d) :
    normalizedTrace d (star a) = star (normalizedTrace d a) := by
  simp [normalizedTrace_apply, star_eq_conjTranspose, trace_conjTranspose, star_mul, mul_comm]

theorem normalizedTrace_faithful {d : ℕ} (hd : 0 < d) (a : Mat d) :
    (normalizedTrace d (star a * a)).im = 0 ∧
      0 ≤ (normalizedTrace d (star a * a)).re ∧
      (normalizedTrace d (star a * a) = 0 ↔ a = 0) := by
  have htrace : trace (star a * a) =
      ((∑ i : Fin d, ∑ j : Fin d, Complex.normSq (a j i) : ℝ) : ℂ) := by
    simp only [trace, diag_apply, mul_apply, star_eq_conjTranspose, conjTranspose_apply]
    push_cast
    simp only [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [normalizedTrace_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [htrace, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    exact Complex.ofReal_im _
  · rw [htrace, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    rw [Complex.ofReal_re]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg d))
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
  · rw [mul_eq_zero, or_iff_right (inv_ne_zero hd')]
    exact trace_conjTranspose_mul_self_eq_zero_iff (A := a)

private theorem traceForm_on_units {d : ℕ} (φ : Mat d →ₗ[ℂ] ℂ)
    (hφ : ∀ a b, φ (a * b) = φ (b * a)) (o i j : Fin d) :
    φ (single i j 1) = if i = j then φ (single o o 1) else 0 := by
  by_cases hij : i = j
  · subst j
    simpa only [single_mul_single_same, mul_one, ite_true] using
      hφ (single i o 1) (single o i 1)
  · have hz : single i j (1 : ℂ) * single i i 1 = 0 :=
      Matrix.single_mul_single_of_ne (c := (1 : ℂ)) i j i (Ne.symm hij) 1
    simpa only [single_mul_single_same, hz, mul_one, map_zero, ite_eq_right hij] using
      hφ (single i i 1) (single i j 1)

theorem normalizedTrace_unique {d : ℕ} (hd : 0 < d)
    (φ : Mat d →ₗ[ℂ] ℂ) (h₁ : φ 1 = 1)
    (hφ : ∀ a b, φ (a * b) = φ (b * a)) :
    φ = normalizedTrace d := by
  let o : Fin d := ⟨0, hd⟩
  have ho : (d : ℂ) * φ (single o o 1) = 1 := by
    rw [← sum_single_one (m := Fin d) (α := ℂ), map_sum] at h₁
    have hsum : (∑ i : Fin d, φ (single i i 1)) = ∑ _ : Fin d, φ (single o o 1) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [traceForm_on_units φ hφ o i i, ite_eq_left rfl]
    simpa [hsum, nsmul_eq_mul] using h₁
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hc : φ (single o o 1) = (d : ℂ)⁻¹ := by
    apply (mul_right_inj' hd').mp
    simpa [mul_inv_cancel₀ hd'] using ho
  apply LinearMap.ext
  intro a
  rw [matrix_eq_sum_single a, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_one (a i j), ← smul_eq_mul, ← smul_single, map_smul, map_smul]
  rw [traceForm_on_units φ hφ o, hc]
  by_cases hij : i = j
  · subst j
    simp [normalizedTrace_apply]
  · simp [normalizedTrace_apply, hij]

/-- The successor map `a ↦ a ⊗ I₂` in lexicographic coordinates. -/
def embed (n : ℕ) : Stage n →⋆ₐ[ℂ] Stage (n + 1) :=
  Omega.MatrixTensorIdentity.embed (pow_succ (2 : ℕ) n).symm

theorem embed_injective (n : ℕ) : Function.Injective (embed n) :=
  Omega.MatrixTensorIdentity.embed_injective (pow_succ (2 : ℕ) n).symm (by decide)

theorem normalizedTrace_embed (n : ℕ) (a : Stage n) :
    normalizedTrace (2 ^ (n + 1)) (embed n a) = normalizedTrace (2 ^ n) a := by
  rw [normalizedTrace_apply, normalizedTrace_apply]
  unfold embed
  rw [Omega.MatrixTensorIdentity.trace_embed, pow_succ (2 : ℕ) n, Nat.cast_mul,
    _root_.mul_inv_rev]
  norm_num
  ring

/-- Transition maps built by composing the successor embeddings. -/
def transition {n m : ℕ} (h : n ≤ m) : Stage n →⋆ₐ[ℂ] Stage m :=
  Nat.leRecOn h (fun {k} f => (embed k).comp f) (StarAlgHom.id ℂ (Stage n))

private theorem transition_succ {n m : ℕ} (h : n ≤ m) :
    transition (Nat.le.step h) = (embed m).comp (transition h) := by
  unfold transition
  exact Nat.leRecOn_succ (C := fun k => Stage n →⋆ₐ[ℂ] Stage k) h
    (StarAlgHom.id ℂ (Stage n))

private theorem transition_refl (n : ℕ) :
    transition (le_refl n) = StarAlgHom.id ℂ (Stage n) := by
  exact Nat.leRecOn_self (C := fun k => Stage n →⋆ₐ[ℂ] Stage k)
    (StarAlgHom.id ℂ (Stage n))

theorem transition_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (transition h) := by
  induction h with
  | refl => rw [transition_refl]; exact fun _ _ h => h
  | @step m h ih =>
    rw [transition_succ h]
    exact (embed_injective m).comp ih

theorem normalizedTrace_transition {n m : ℕ} (h : n ≤ m) (a : Stage n) :
    normalizedTrace (2 ^ m) (transition h a) = normalizedTrace (2 ^ n) a := by
  induction h with
  | refl => rw [transition_refl]; rfl
  | @step m h ih => rw [transition_succ h, StarAlgHom.comp_apply, normalizedTrace_embed, ih]

/-- A diagonal projection on the first `k` coordinates. -/
abbrev rankProjection := Omega.MatrixProjectionSpectrum.rankProjection

open Omega.MatrixProjectionSpectrum (rankProjection_trace projection_cutoff)

private theorem rankProjection_mul {d k l : ℕ} (hkl : k ≤ l) :
    rankProjection d k * rankProjection d l = rankProjection d k := by
  unfold rankProjection Omega.MatrixProjectionSpectrum.rankProjection
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : (i : ℕ) < k
  · simp [h, h.trans_le hkl]
  · simp [h]

theorem embed_rankProjection (n k : ℕ) :
    embed n (rankProjection (2 ^ n) k) = rankProjection (2 ^ (n + 1)) (2 * k) := by
  let e := Omega.MatrixTensorIdentity.indices (pow_succ (2 : ℕ) n).symm
  unfold embed rankProjection Omega.MatrixProjectionSpectrum.rankProjection
  rw [Omega.MatrixTensorIdentity.embed_diagonal]
  congr 1
  funext i
  obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective i
  change (if (((e.symm (e (a, b))).1 : Fin (2 ^ n)) : ℕ) < k then (1 : ℂ) else 0) = _
  rw [Equiv.symm_apply_apply]
  change (if (a : ℕ) < k then (1 : ℂ) else 0) =
    if (b : ℕ) + 2 * (a : ℕ) < 2 * k then 1 else 0
  have hb := b.isLt
  have he : (a : ℕ) < k ↔ (b : ℕ) + 2 * (a : ℕ) < 2 * k := by omega
  simp [he]

theorem rankProjection_spec {d k : ℕ} (hk : k ≤ d) :
    IsStarProjection (rankProjection d k) ∧
      normalizedTrace d (rankProjection d k) = (k : ℂ) / d := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change diagonal _ * diagonal _ = diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : (i : ℕ) < k <;> simp [h]
  · change (diagonal _)ᴴ = diagonal _
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    by_cases h : (i : ℕ) < k <;> simp [h]
  · rw [normalizedTrace_apply, rankProjection_trace hk, div_eq_mul_inv, mul_comm]

theorem projection_equiv_iff_trace {d : ℕ} (hd : 0 < d) {p q : Mat d}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (∃ u : unitary (Mat d), star (u : Mat d) * p * u = q) ↔
      normalizedTrace d p = normalizedTrace d q := by
  constructor
  · rintro ⟨u, rfl⟩
    calc
      normalizedTrace d p = normalizedTrace d (p * (u : Mat d) * star (u : Mat d)) := by
        rw [mul_assoc, mul_star_self_of_mem u.property, mul_one]
      _ = _ := by rw [normalizedTrace_mul_comm, ← mul_assoc]
  · intro h
    obtain ⟨k, _, hkp, hp'⟩ := projection_cutoff hp
    obtain ⟨l, _, hlq, hq'⟩ := projection_cutoff hq
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    simp only [normalizedTrace_apply, hp', hq', mul_right_inj' (inv_ne_zero hd')] at h
    have hkl : k = l := by exact_mod_cast h
    subst l
    let hpH : p.IsHermitian := hp.isSelfAdjoint
    let hqH : q.IsHermitian := hq.isSelfAdjoint
    have he : hpH.eigenvalues = hqH.eigenvalues := funext fun i => (hkp i).trans (hlq i).symm
    let u := hpH.eigenvectorUnitary
    let v := hqH.eigenvectorUnitary
    refine ⟨u * star v, ?_⟩
    have hpD := hpH.conjStarAlgAut_star_eigenvectorUnitary
    have hqD := hqH.conjStarAlgAut_star_eigenvectorUnitary
    rw [he, ← hqD] at hpD
    have H : conjStarAlgAut ℂ (Mat d) (v * star u) p = q := by
      rw [conjStarAlgAut_mul_apply]
      change conjStarAlgAut ℂ (Mat d) v (conjStarAlgAut ℂ (Mat d) (star u) p) = q
      rw [hpD]
      change conjStarAlgAut ℂ (Mat d) v (conjStarAlgAut ℂ (Mat d) (star v) q) = q
      rw [← conjStarAlgAut_symm]
      exact (conjStarAlgAut ℂ (Mat d) v).apply_symm_apply q
    simpa [conjStarAlgAut_apply, coe_star, star_mul, mul_assoc] using H

theorem projection_mvn_iff_trace {d : ℕ} (hd : 0 < d) {p q : Mat d}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (∃ v : Mat d, v * star v = p ∧ star v * v = q) ↔
      normalizedTrace d p = normalizedTrace d q := by
  constructor
  · rintro ⟨v, rfl, rfl⟩
    exact normalizedTrace_mul_comm _ _
  · intro h
    obtain ⟨u, hu⟩ := (projection_equiv_iff_trace hd hp hq).mpr h
    refine ⟨p * ↑u, ?_, ?_⟩
    · simp only [star_mul, hp.isSelfAdjoint.star_eq]
      rw [← mul_assoc, mul_assoc p, mul_star_self_of_mem u.property, mul_one, hp.isIdempotentElem.eq]
    · simp only [star_mul, hp.isSelfAdjoint.star_eq]
      rw [mul_assoc, ← mul_assoc p, hp.isIdempotentElem.eq, ← mul_assoc, hu]

private def stageMap (n m : ℕ) (h : n ≤ m) : Stage n →⋆ₐ[ℂ] Stage m :=
  transition h

/-- The transition maps agree on all compositions. -/
instance directedSystem : DirectedSystem Stage (stageMap · · ·) where
  map_self := by
    intro n a
    change transition (le_refl n) a = a
    rw [transition_refl]
    rfl
  map_map := by
    intro k j i h₁ h₂ a
    change transition h₂ (transition h₁ a) = transition (h₁.trans h₂) a
    induction h₂ with
    | refl => rw [transition_refl]; rfl
    | @step m h ih =>
      rw [transition_succ h, transition_succ (h₁.trans h),
        StarAlgHom.comp_apply, StarAlgHom.comp_apply, ih]

/-- The algebraic union of the dyadic matrix algebras. -/
abbrev Ralg := DirectLimit Stage stageMap

/-- The canonical inclusion of a finite matrix algebra into the algebraic union. -/
def stageInclusion (n : ℕ) : Stage n →⋆ₐ[ℂ] Ralg where
  toAlgHom := DirectLimit.Algebra.of Stage stageMap n
  map_star' _ := rfl

theorem stageInclusion_injective (n : ℕ) :
    Function.Injective (stageInclusion n) :=
  DirectLimit.mk_injective stageMap (fun _ _ h => transition_injective h) n

theorem stageInclusion_transition {n m : ℕ} (h : n ≤ m) (a : Stage n) :
    stageInclusion m (transition h a) = stageInclusion n a :=
  DirectLimit.Algebra.of_f (f := stageMap) h a

/-- The trace induced by the compatible normalized matrix traces. -/
def algTrace : Ralg →ₗ[ℂ] ℂ :=
  DirectLimit.Module.lift ℂ ℕ Stage stageMap (fun n => normalizedTrace (2 ^ n))
    (fun _ _ h a => normalizedTrace_transition h a)

theorem algTrace_stage (n : ℕ) (a : Stage n) :
    algTrace (stageInclusion n a) = normalizedTrace (2 ^ n) a := rfl

private theorem algTrace_one : algTrace 1 = 1 := by
  rw [← map_one (stageInclusion 0), algTrace_stage]
  exact normalizedTrace_one (by positivity)

private theorem algTrace_cyclic (a b : Ralg) : algTrace (a * b) = algTrace (b * a) := by
  obtain ⟨n, a, b, ha, hb⟩ := DirectLimit.exists_eq_mk₂ stageMap a b
  change _ = stageInclusion n a at ha
  change _ = stageInclusion n b at hb
  rw [ha, hb, ← map_mul, ← map_mul, algTrace_stage, algTrace_stage]
  exact normalizedTrace_mul_comm a b

private theorem algTrace_star (a : Ralg) : algTrace (star a) = star (algTrace a) := by
  obtain ⟨n, x, h⟩ := DirectLimit.exists_eq_mk stageMap a
  change a = stageInclusion n x at h
  rw [h, ← map_star, algTrace_stage, algTrace_stage]
  exact normalizedTrace_star x

private theorem algTrace_faithful (a : Ralg) :
    (algTrace (star a * a)).im = 0 ∧ 0 ≤ (algTrace (star a * a)).re ∧
      (algTrace (star a * a) = 0 ↔ a = 0) := by
  obtain ⟨n, x, h⟩ := DirectLimit.exists_eq_mk stageMap a
  change a = stageInclusion n x at h
  rw [h, ← map_star, ← map_mul, algTrace_stage, ← map_zero (stageInclusion n)]
  exact (normalizedTrace_faithful (by positivity) x).imp_right fun hf =>
    hf.imp_right (fun h => h.trans (stageInclusion_injective n).eq_iff.symm)

theorem algTrace_spec : algTrace 1 = 1 ∧
    (∀ a b, algTrace (a * b) = algTrace (b * a)) ∧
    (∀ a, algTrace (star a) = star (algTrace a)) ∧
    (∀ a, (algTrace (star a * a)).im = 0 ∧
      0 ≤ (algTrace (star a * a)).re ∧ (algTrace (star a * a) = 0 ↔ a = 0)) :=
  ⟨algTrace_one, algTrace_cyclic, algTrace_star, algTrace_faithful⟩

theorem algTrace_unique (φ : Ralg →ₗ[ℂ] ℂ) (h₁ : φ 1 = 1)
    (hφ : ∀ a b, φ (a * b) = φ (b * a)) : φ = algTrace := by
  apply LinearMap.ext
  intro a
  obtain ⟨n, x, h⟩ := DirectLimit.exists_eq_mk stageMap a
  change a = stageInclusion n x at h
  rw [h, algTrace_stage]
  have hs := normalizedTrace_unique (by positivity : 0 < 2 ^ n)
    (φ.comp (stageInclusion n).toAlgHom.toLinearMap)
    (by simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_one] using h₁)
    (fun b c => by
      change φ (stageInclusion n (b * c)) = φ (stageInclusion n (c * b))
      exact (congrArg φ (map_mul (stageInclusion n) b c)).trans
        ((hφ (stageInclusion n b) (stageInclusion n c)).trans
          (congrArg φ (map_mul (stageInclusion n) c b)).symm))
  exact LinearMap.congr_fun hs x

theorem alg_center_iff (a : Ralg) :
    (∀ b, Commute a b) ↔ ∃ c : ℂ, a = c • 1 := by
  constructor
  · intro h
    obtain ⟨n, x, hx⟩ := DirectLimit.exists_eq_mk stageMap a
    change a = stageInclusion n x at hx
    have hc : x ∈ Set.center (Mat (2 ^ n)) := by
      apply Set.mem_center_iff.mpr
      refine ⟨fun y => ?_, fun _ _ => (mul_assoc _ _ _).symm, fun _ _ => mul_assoc _ _ _⟩
      apply stageInclusion_injective n
      simpa only [map_mul, hx] using (h (stageInclusion n y)).eq
    rw [Matrix.center_eq_range] at hc
    obtain ⟨c, rfl⟩ := hc
    refine ⟨c, ?_⟩
    rw [hx]
    change stageInclusion n (algebraMap ℂ (Stage n) c) = _
    rw [AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one]
  · rintro ⟨c, rfl⟩ b
    rw [← Algebra.algebraMap_eq_smul_one]
    exact Algebra.commutes _ _

theorem alg_projection_trace_iff (t : ℂ) :
    (∃ p, IsStarProjection p ∧ algTrace p = t) ↔
      ∃ n k : ℕ, k ≤ 2 ^ n ∧ t = (k : ℂ) / ((2 ^ n : ℕ) : ℂ) := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨n, x, hx⟩ := DirectLimit.exists_eq_mk stageMap p
    change p = stageInclusion n x at hx
    subst p
    have hx : IsStarProjection x := by
      constructor
      · exact stageInclusion_injective n (by simpa only [map_mul] using hp.isIdempotentElem.eq)
      · exact stageInclusion_injective n
          (by simpa only [map_star] using hp.isSelfAdjoint.star_eq)
    obtain ⟨k, hk, _, htrace⟩ := projection_cutoff hx
    exact ⟨n, k, hk, by rw [algTrace_stage, normalizedTrace_apply, htrace, div_eq_mul_inv,
      mul_comm]⟩
  · rintro ⟨n, k, hk, rfl⟩
    exact ⟨stageInclusion n (rankProjection (2 ^ n) k),
      (rankProjection_spec hk).1.map (stageInclusion n), (rankProjection_spec hk).2⟩

private def cutoff (s : ℝ) (n : ℕ) : ℕ := ⌊(2 ^ n : ℝ) * s⌋₊

private theorem cutoff_le {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    cutoff s n ≤ 2 ^ n := by
  have h := (Nat.floor_le (mul_nonneg (by positivity) hs.1)).trans
    (mul_le_of_le_one_right (by positivity : 0 ≤ (2 ^ n : ℝ)) hs.2)
  unfold cutoff
  exact_mod_cast h

private theorem cutoff_mono {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    2 * cutoff s n ≤ cutoff s (n + 1) := by
  apply Nat.le_floor
  push_cast
  rw [pow_succ]
  calc
    _ ≤ 2 * ((2 ^ n : ℝ) * s) := by
      gcongr
      exact Nat.floor_le (mul_nonneg (by positivity) hs)
    _ = _ := by ring

private theorem cutoff_tendsto {s : ℝ} (hs : 0 ≤ s) :
    Filter.Tendsto (fun n : ℕ => (cutoff s n : ℝ) / (2 ^ n : ℝ))
      Filter.atTop (nhds s) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hl : Filter.Tendsto (fun n => s - (1 / 2 : ℝ) ^ n) Filter.atTop (nhds s) := by
    simpa only [sub_zero] using hp.const_sub s
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds (fun n => ?_)
    (fun n => ?_)
  · have hn : 0 < (2 ^ n : ℝ) := by positivity
    rw [div_pow, one_pow]
    apply (le_div_iff₀ hn).mpr
    have h := Nat.lt_floor_add_one ((2 ^ n : ℝ) * s)
    rw [sub_mul, div_mul_cancel₀ _ hn.ne']
    unfold cutoff
    linarith
  · apply (div_le_iff₀ (by positivity)).mpr
    rw [mul_comm]
    exact Nat.floor_le (mul_nonneg (by positivity) hs)

/-- The real projection dimensions of the algebraic union are dense in the unit interval. -/
theorem dyadicTrace_closure :
    closure {s : ℝ | ∃ p : Ralg, IsStarProjection p ∧ algTrace p = (s : ℂ)} = Set.Icc 0 1 := by
  apply le_antisymm
  · apply closure_minimal _ isClosed_Icc
    rintro s ⟨p, hp, hs⟩
    obtain ⟨n, k, hk, he⟩ := (alg_projection_trace_iff (s : ℂ)).mp ⟨p, hp, hs⟩
    have he' : s = (k : ℝ) / (2 ^ n : ℝ) := by
      apply Complex.ofReal_injective
      push_cast
      simpa using he
    rw [he']
    exact ⟨by positivity, (div_le_one (by positivity)).mpr (by exact_mod_cast hk)⟩
  · intro s hs
    apply mem_closure_of_tendsto (cutoff_tendsto hs.1)
    exact Filter.Eventually.of_forall fun n =>
      (alg_projection_trace_iff _).mpr ⟨n, cutoff s n, cutoff_le hs n, by push_cast; rfl⟩

open scoped MatrixOrder Matrix.Norms.L2Operator in
private theorem algebraic_square_bound (a : Ralg) :
    ∃ (c : ℝ) (b : Ralg), 0 ≤ c ∧ (c ^ 2 : ℂ) • 1 - star a * a = star b * b := by
  obtain ⟨n, x, hx⟩ := DirectLimit.exists_eq_mk stageMap a
  change a = stageInclusion n x at hx
  obtain ⟨b, hb⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    (sub_nonneg.mpr (CStarAlgebra.star_mul_le_algebraMap_norm_sq x))
  change algebraMap ℂ (Stage n) ((‖x‖ ^ 2 : ℝ) : ℂ) - star x * x = star b * b at hb
  refine ⟨‖x‖, stageInclusion n b, norm_nonneg _, ?_⟩
  rw [hx]
  convert congrArg (stageInclusion n) hb using 1 <;>
    simp only [map_sub, map_star, map_mul, AlgHomClass.commutes,
      ← Algebra.algebraMap_eq_smul_one, ← Complex.ofReal_pow]

/-- The faithful trace and the finite matrix bounds defining its regular representation. -/
def dyadicTraceData : Omega.TracialRegularRepresentation.TraceData Ralg where
  trace := algTrace
  one := algTrace_one
  cyclic := algTrace_cyclic
  star' := algTrace_star
  positive x := (algTrace_faithful x).2.1
  faithful x := (algTrace_faithful x).2.2.mp
  bounded := algebraic_square_bound

/-- The concrete bicommutant of the dyadic tower on its tracial Hilbert space. -/
def dyadicBicommutant : VonNeumannAlgebra (Omega.TracialRegularRepresentation.Hilbert
    dyadicTraceData) := Omega.TracialRegularRepresentation.bicommutant dyadicTraceData

open Omega.TracialRegularRepresentation in
theorem dyadicVacuumTrace_spec :
    vacuumTrace dyadicTraceData 1 = 1 ∧
    (∀ z ∈ dyadicBicommutant, ∀ w ∈ dyadicBicommutant, vacuumTrace dyadicTraceData (z * w) =
      vacuumTrace dyadicTraceData (w * z)) ∧
    (∀ z ∈ dyadicBicommutant, vacuumTrace dyadicTraceData (star z * z) =
      (‖z (vacuum dyadicTraceData)‖ ^ 2 : ℝ) ∧
      (vacuumTrace dyadicTraceData (star z * z) = 0 ↔ z = 0)) :=
  ⟨vacuumTrace_one _, fun _ hz _ hw => vacuumTrace_cyclic _ hz hw,
    fun _ hz => vacuumTrace_faithful _ hz⟩

open Omega.TracialRegularRepresentation in
/-- The real part of the vacuum trace preserves suprema of bounded increasing positive nets. -/
theorem dyadicVacuumTrace_normal {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (T : ι → Hilbert dyadicTraceData →L[ℂ] Hilbert dyadicTraceData)
    (hM : ∀ i, T i ∈ dyadicBicommutant) (hMono : Monotone T) (hPos : ∀ i, 0 ≤ T i)
    {r : ℝ} (hr : 0 ≤ r)
    (hBound : ∀ i, T i ≤ algebraMap ℝ (Hilbert dyadicTraceData →L[ℂ] Hilbert dyadicTraceData) r) :
    ∃ S, S ∈ dyadicBicommutant ∧ IsLUB (Set.range T) S ∧
      IsLUB (Set.range fun i => (vacuumTrace dyadicTraceData (T i)).re)
        (vacuumTrace dyadicTraceData S).re := by
  obtain ⟨S, hSM, hSL, hE⟩ :=
    Omega.NormalVectorFunctional.exists_isLUB_expectation dyadicBicommutant T hM hMono hPos hr hBound
  exact ⟨S, hSM, hSL, hE (vacuum dyadicTraceData)⟩

open Omega.TracialRegularRepresentation in
theorem completed_center_iff (z : Hilbert dyadicTraceData →L[ℂ] Hilbert dyadicTraceData)
    (hz : z ∈ dyadicBicommutant) : (∀ w ∈ dyadicBicommutant, Commute z w) ↔
      ∃ c : ℂ, z = c • 1 := by
  refine ⟨fun h => ⟨_, scalar_of_commute_left dyadicTraceData (by exact algTrace_unique) hz
    (fun a => h _ (left_mem_bicommutant _ a))⟩, ?_⟩
  rintro ⟨c, rfl⟩ w _
  rw [← Algebra.algebraMap_eq_smul_one]
  exact Algebra.commutes _ _

open Omega.TracialRegularRepresentation in
/-- The faithful action of each finite matrix algebra on the tracial Hilbert space. -/
def representedStage (n : ℕ) :
    Stage n →⋆ₐ[ℂ] (Hilbert dyadicTraceData →L[ℂ] Hilbert dyadicTraceData) :=
  (leftHom dyadicTraceData).comp (stageInclusion n)

open Omega.TracialRegularRepresentation in
theorem representedMatrix_spec (n : ℕ) : Function.Injective (representedStage n) ∧
    (∀ a, representedStage n a ∈ dyadicBicommutant) ∧
    (∀ a, vacuumTrace dyadicTraceData (representedStage n a) = normalizedTrace (2 ^ n) a) := by
  refine ⟨(leftHom_injective _).comp (stageInclusion_injective n),
    fun a => left_mem_bicommutant dyadicTraceData (stageInclusion n a), fun a => ?_⟩
  let x : Domain dyadicTraceData := stageInclusion n a
  exact (vacuumTrace_left dyadicTraceData x).trans (algTrace_stage n a)

private theorem representedStage_embed (n : ℕ) (a : Stage n) :
    representedStage (n + 1) (embed n a) = representedStage n a := by
  have h := stageInclusion_transition (Nat.le_succ n) a
  rw [transition_succ (le_refl n), transition_refl] at h
  exact congrArg (Omega.TracialRegularRepresentation.leftHom dyadicTraceData) h
open Omega.TracialRegularRepresentation in
/-- The increasing full matrix algebras are strongly dense in the concrete bicommutant. -/
theorem matrix_tower_strongly_dense {ι : Type*} [Fintype ι]
    {z : Hilbert dyadicTraceData →L[ℂ] Hilbert dyadicTraceData} (hz : z ∈ dyadicBicommutant)
    (x : ι → Hilbert dyadicTraceData) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (a : Stage n), ∀ i, ‖representedStage n a (x i) - z (x i)‖ < ε := by
  obtain ⟨b, hb⟩ := exists_algebraic_approximation dyadicTraceData hz x hε
  obtain ⟨n, a, ha⟩ := DirectLimit.exists_eq_mk stageMap (show Ralg from b)
  change b = (stageInclusion n a : Domain dyadicTraceData) at ha
  subst b
  exact ⟨n, a, hb⟩

set_option maxHeartbeats 550000 in
open Omega.TracialRegularRepresentation Filter Topology in
/-- The trace range of projections of the concrete bicommutant is the full unit interval. -/
theorem completed_projection_trace_range (s : ℝ) :
    (∃ p ∈ dyadicBicommutant, IsStarProjection p ∧ vacuumTrace dyadicTraceData p = (s : ℂ)) ↔
      s ∈ Set.Icc 0 1 := by
  have hone : IsStarProjection (1 : Hilbert dyadicTraceData →L[ℂ] Hilbert dyadicTraceData) :=
    IsStarProjection.one _
  constructor
  · rintro ⟨p, _, hp, ht⟩
    have hp' : p ≤ 1 := (hp.le_iff_mul_eq_left hone).mpr (mul_one p)
    have hpos := (ContinuousLinearMap.nonneg_iff_isPositive.mp hp.nonneg).re_inner_nonneg_right
      (vacuum dyadicTraceData)
    have hneg := (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (sub_nonneg.mpr hp')).re_inner_nonneg_right
      (vacuum dyadicTraceData)
    change 0 ≤ (vacuumTrace dyadicTraceData p).re at hpos
    rw [ht, Complex.ofReal_re] at hpos
    simp only [ContinuousLinearMap.sub_apply, inner_sub_right] at hneg
    change 0 ≤ (vacuumTrace dyadicTraceData 1 - vacuumTrace dyadicTraceData p).re at hneg
    rw [vacuumTrace_one, ht, Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hneg
    exact ⟨hpos, sub_nonneg.mp hneg⟩
  · intro hs
    let P (n : ℕ) := representedStage n (rankProjection (2 ^ n) (cutoff s n))
    have hP (n : ℕ) : IsStarProjection (P n) :=
      (rankProjection_spec (cutoff_le hs n)).1.map (representedStage n)
    have hM (n : ℕ) : P n ∈ dyadicBicommutant := (representedMatrix_spec n).2.1 _
    have hmono : Monotone P := monotone_nat_of_le_succ fun n => by
      apply ((hP n).le_iff_mul_eq_left (hP (n + 1))).mpr
      have hn : P n = representedStage (n + 1) (rankProjection (2 ^ (n + 1)) (2 * cutoff s n)) := by
        change representedStage n (rankProjection (2 ^ n) (cutoff s n)) = _
        rw [← representedStage_embed n, embed_rankProjection]
      rw [hn]
      change _ * representedStage (n + 1) (rankProjection (2 ^ (n + 1)) (cutoff s (n + 1))) = _
      rw [← map_mul, rankProjection_mul (cutoff_mono hs.1 n)]
    have hB (n : ℕ) : P n ≤ 1 :=
      ((hP n).le_iff_mul_eq_left hone).mpr (mul_one _)
    obtain ⟨S, hS, _, hlim⟩ := Omega.NormalVectorFunctional.exists_isLUB_strong_tendsto
      dyadicBicommutant P hM hmono (fun n => (hP n).nonneg) (by norm_num : (0 : ℝ) ≤ 1)
      (fun n => by simpa using hB n)
    refine ⟨S, hS, strong_projection_limit dyadicTraceData hP hmono hlim, ?_⟩
    have ht : Tendsto (fun n => vacuumTrace dyadicTraceData (P n)) atTop
        (𝓝 (vacuumTrace dyadicTraceData S)) :=
      tendsto_const_nhds.inner (𝕜 := ℂ) (hlim (vacuum dyadicTraceData))
    have hc : Tendsto (fun n => vacuumTrace dyadicTraceData (P n)) atTop (𝓝 (s : ℂ)) := by
      apply (Complex.continuous_ofReal.continuousAt.tendsto.comp (cutoff_tendsto hs.1)).congr
      intro n
      dsimp [P]
      rw [(representedMatrix_spec n).2.2, (rankProjection_spec (cutoff_le hs n)).2]
      push_cast
      rfl
    exact tendsto_nhds_unique ht hc

end D5.S3.Quantum.Analysis.NullConeGravity.HyperfiniteTypeII1Factor

namespace D5.S3.Quantum.Analysis.NullConeGravity.HyperfiniteTypeII1Factor

open MeasureTheory Omega.RealAffine

/-- Minus-sided modular time on the real affine group. -/
abbrev MinusAffine := Affine (-2 * Real.pi)

/-- Translation and dilation act on the same Lebesgue Hilbert space. -/
def minusSidedAction : MinusAffine →* (PositionL2 ≃ₗᵢ[ℂ] PositionL2) :=
  affineUnitary (-2 * Real.pi)

/-- The action in exponential coordinates, with the positive translation sign. -/
theorem minusSidedAction_ae (s a : ℝ) (f : PositionL2) :
    ⇑(minusSidedAction ⟨s, a⟩ f) =ᵐ[volume]
      fun x => (Real.exp (Real.pi * s) : ℂ) *
        f (Real.exp (2 * Real.pi * s) * (x + a)) := by
  have hs : -2 * Real.pi * s = -(2 * (Real.pi * s)) := by ring
  have hs' : -2 * Real.pi * s = -(2 * Real.pi * s) := by ring
  have hsq (z : ℝ) : Real.sqrt (Real.exp (2 * z)) = Real.exp z := by
    rw [two_mul, Real.exp_add, ← pow_two, Real.sqrt_sq (Real.exp_pos _).le]
  have hw : (Real.sqrt (scale (⟨s, a⟩ : MinusAffine)))⁻¹ = Real.exp (Real.pi * s) := by
    change (Real.sqrt (Real.exp (-2 * Real.pi * s)))⁻¹ = _
    rw [hs, ← mul_neg, hsq, Real.exp_neg, inv_inv]
  have ha (x : ℝ) :
      (x + a) / scale (⟨s, a⟩ : MinusAffine) =
        Real.exp (2 * Real.pi * s) * (x + a) := by
    change (x + a) / Real.exp (-2 * Real.pi * s) = _
    rw [hs', Real.exp_neg, div_inv_eq_mul, mul_comm]
  filter_upwards [affineUnitary_ae (⟨s, a⟩ : MinusAffine) f] with x hx
  exact hx.trans (by rw [hw, ha])

/-- Modular conjugation rescales translations by at least one at nonpositive time. -/
theorem minusSided_covariance (s a : ℝ) (hs : s ≤ 0) :
    let c := -2 * Real.pi
    let slope := Real.exp (c * s)
    1 ≤ slope ∧
      minusSidedAction (dilation c s) * minusSidedAction (translation c a) *
          (minusSidedAction (dilation c s))⁻¹ =
        minusSidedAction (translation c (slope * a)) := by
  dsimp only
  refine ⟨Real.one_le_exp_iff.mpr (mul_nonneg_of_nonpos_of_nonpos (by linarith [Real.pi_pos]) hs),
    ?_⟩
  simpa only [map_mul, map_inv] using
    congrArg minusSidedAction (conj_translation (c := -2 * Real.pi) s a)

end D5.S3.Quantum.Analysis.NullConeGravity.HyperfiniteTypeII1Factor
