/- GID: D5/S3/Quantum/Foundation/SectionPositiveLift
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/SectionPositiveLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Whole-cone positive lifts and common finite pure exclusions in native real or complex PSD sections. -/

import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Inner
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Tactic

/-!
The carrier is the original normalized real subspace of real symmetric or complex
Hermitian matrices. Complex vectors and complex rank one matrices retain their
native field. The arbitrary-unit support and determinant normalization is an
outside bridge; no such normalization, classification, PRE or full Z0 is proved here.
-/

noncomputable section
open scoped Matrix ComplexOrder InnerProductSpace RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.SectionPositiveLift

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- Native rank one PSD matrix, without normalizing or changing fields. -/
def rankOne (v : ι → 𝕜) : HermitianMat ι 𝕜 :=
  ⟨Matrix.vecMulVec v (star v), (Matrix.posSemidef_vecMulVec_self_star v).isHermitian⟩

/-- The entire PSD section of the specified original real linear subspace. -/
def cone (L : Submodule ℝ (HermitianMat ι 𝕜)) : PointedCone ℝ L where
  carrier := {X | 0 ≤ (X : HermitianMat ι 𝕜)}
  zero_mem' := by change (0 : HermitianMat ι 𝕜) ≤ 0; exact le_rfl
  add_mem' := by
    intro X Y hX hY
    change 0 ≤ (X : HermitianMat ι 𝕜) at hX
    change 0 ≤ (Y : HermitianMat ι 𝕜) at hY
    change 0 ≤ (X : HermitianMat ι 𝕜) + (Y : HermitianMat ι 𝕜)
    exact add_nonneg hX hY
  smul_mem' := by
    intro r X hX
    change 0 ≤ (r : ℝ) • (X : HermitianMat ι 𝕜)
    exact smul_nonneg r.property hX

private lemma mem_cone (L : Submodule ℝ (HermitianMat ι 𝕜)) (X : L) :
    X ∈ cone L ↔ 0 ≤ (X : HermitianMat ι 𝕜) := Iff.rfl

/-- The original trace unit restricted to the entire real subspace. -/
def unit (L : Submodule ℝ (HermitianMat ι 𝕜)) : L →ₗ[ℝ] ℝ :=
  { toFun := fun X => X.val.trace
    map_add' := fun X Y => HermitianMat.trace_add X.val Y.val
    map_smul' := fun r X => HermitianMat.trace_smul X.val r }

/-- Properness on every original positive element. -/
def Proper {L : Submodule ℝ (HermitianMat ι 𝕜)} (f : L →ₗ[ℝ] ℝ) : Prop :=
  ∀ X ∈ cone L, 0 ≤ f X ∧ f X ≤ unit L X

/-- All same-unit PSD lifts, with orthogonality for the real trace pairing. -/
def lifts (L : Submodule ℝ (HermitianMat ι 𝕜)) : Set (HermitianMat ι 𝕜) :=
  {M | 0 ≤ M ∧ M - 1 ∈ Lᗮ}

/-- The native outer product is positive semidefinite. -/
lemma rankOne_nonneg (v : ι → 𝕜) : 0 ≤ rankOne v :=
  HermitianMat.zero_le_iff.mpr (Matrix.posSemidef_vecMulVec_self_star v)

/-- Trace pairing against a native outer product is its quadratic reading. -/
lemma pair_rankOne (A : HermitianMat ι 𝕜) (v : ι → 𝕜) :
    (⟪A, rankOne v⟫_ℝ : 𝕜) = star v ⬝ᵥ (A.mat *ᵥ v) := by
  rw [HermitianMat.inner_eq_trace_rc]
  change (A.mat * Matrix.vecMulVec v (star v)).trace = _
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

private lemma rankOne_trace (v : ι → 𝕜) (hv : star v ⬝ᵥ v = 1) :
    (rankOne v).trace = 1 := by
  apply RCLike.ofReal_injective (K := 𝕜)
  calc
    ((rankOne v).trace : 𝕜) = (rankOne v).mat.trace := HermitianMat.trace_eq_trace_rc _
    _ = (1 : 𝕜) := by
      change (Matrix.vecMulVec v (star v)).trace = 1
      rw [Matrix.trace_vecMulVec, dotProduct_comm, hv]
    _ = ((1 : ℝ) : 𝕜) := by simp

private lemma ambient_majorization (Y : HermitianMat ι 𝕜) :
    ∃ t : ℝ, 0 ≤ t ∧ 0 ≤ Y + t • 1 := by
  let t : ℝ := ∑ i, |(-Y).H.eigenvalues i|
  have ht : 0 ≤ t := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hb : -Y ≤ t • 1 := by
    apply (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff (-Y).H t).mp
    intro i
    exact (le_abs_self _).trans (Finset.single_le_sum
      (fun j _ => abs_nonneg ((-Y).H.eigenvalues j)) (Finset.mem_univ i))
  exact ⟨t, ht, by simpa [add_comm] using add_le_add_left hb Y⟩

/-- Every positive functional on the whole section has an ambient PSD representative.
The extension tests every ambient rank one matrix, including those outside L. -/
theorem positive_functional_psd_lift
    (L : Submodule ℝ (HermitianMat ι 𝕜)) (hI : (1 : HermitianMat ι 𝕜) ∈ L)
    (f : L →ₗ[ℝ] ℝ) (hf : ∀ X : L, 0 ≤ (X : HermitianMat ι 𝕜) → 0 ≤ f X) :
    ∃ E : HermitianMat ι 𝕜, 0 ≤ E ∧ ∀ X : L, f X = ⟪E, (X : HermitianMat ι 𝕜)⟫_ℝ := by
  let pmap : HermitianMat ι 𝕜 →ₗ.[ℝ] ℝ := ⟨L, f⟩
  obtain ⟨g, hg, hpos⟩ := riesz_extension
    (PointedCone.positive ℝ (HermitianMat ι 𝕜)) pmap hf (by
      intro Y
      obtain ⟨t, ht, hY⟩ := ambient_majorization Y
      exact ⟨⟨t • 1, L.smul_mem t hI⟩, by simpa [add_comm] using hY⟩)
  let E : HermitianMat ι 𝕜 :=
    (InnerProductSpace.toDual ℝ (HermitianMat ι 𝕜)).symm g.toContinuousLinearMap
  have hE (X : HermitianMat ι 𝕜) : ⟪E, X⟫_ℝ = g X :=
    InnerProductSpace.toDual_symm_apply
  refine ⟨E, ?_, fun X => (hg X).symm.trans (hE X).symm⟩
  apply HermitianMat.zero_le_iff.mpr
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨E.H, fun v => ?_⟩
  rw [← pair_rankOne E v]
  have h := hpos (rankOne v) (rankOne_nonneg v)
  rw [← hE] at h
  exact RCLike.ofReal_nonneg.mpr h

private lemma sandwich_rankOne (M : HermitianMat ι 𝕜) (v : ι → 𝕜)
    (hv : star v ⬝ᵥ (M.mat *ᵥ v) = 1) :
    (rankOne v).mat * M.mat * (rankOne v).mat = (rankOne v).mat := by
  change Matrix.vecMulVec v (star v) * M.mat * Matrix.vecMulVec v (star v) = _
  rw [Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec, ← Matrix.dotProduct_mulVec, hv]
  change Matrix.vecMulVec v (1 • star v) = Matrix.vecMulVec v (star v)
  rw [one_smul]

/-- Singular-safe rank one deflation. The upper bound is M itself. -/
theorem rank_one_deflation (M : HermitianMat ι 𝕜) (hM : 0 ≤ M)
    (v : ι → 𝕜) (hv : star v ⬝ᵥ (M.mat *ᵥ v) = 1) :
    0 ≤ (rankOne v).conj M.mat ∧ 0 ≤ M - (rankOne v).conj M.mat := by
  refine ⟨HermitianMat.conj_nonneg M.mat (rankOne_nonneg v), ?_⟩
  apply HermitianMat.zero_le_iff.mpr
  let Q := 1 - (rankOne v).mat * M.mat
  have hQ : Q.conjTranspose * M.mat * Q =
      M.mat - M.mat * (rankOne v).mat * M.mat := by
    have hp := sandwich_rankOne M v hv
    simp only [Q, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, M.H.eq, (rankOne v).H.eq]
    calc
      (1 - M.mat * (rankOne v).mat) * M.mat * (1 - (rankOne v).mat * M.mat) =
          M.mat - M.mat * (rankOne v).mat * M.mat -
          M.mat * (rankOne v).mat * M.mat +
          M.mat * ((rankOne v).mat * M.mat * (rankOne v).mat) * M.mat := by
            noncomm_ring
      _ = M.mat - M.mat * (rankOne v).mat * M.mat := by rw [hp]; abel
  have h := (HermitianMat.zero_le_iff.mp hM).conjTranspose_mul_mul_same Q
  rw [hQ] at h
  simpa [HermitianMat.conj_apply_mat, M.H.eq] using h

private lemma mem_lifts_iff (L : Submodule ℝ (HermitianMat ι 𝕜))
    (M : HermitianMat ι 𝕜) :
    M ∈ lifts L ↔ 0 ≤ M ∧ ∀ X : L, ⟪M, (X : HermitianMat ι 𝕜)⟫_ℝ = unit L X := by
  constructor
  · rintro ⟨hM, horth⟩
    refine ⟨hM, fun X => ?_⟩
    have h := (L.mem_orthogonal' (M - 1)).mp horth X.val X.property
    simpa [inner_sub_left, unit, sub_eq_zero] using h
  · rintro ⟨hM, hval⟩
    refine ⟨hM, (L.mem_orthogonal' (M - 1)).mpr ?_⟩
    intro X hX
    simpa [inner_sub_left, unit, sub_eq_zero] using hval ⟨X, hX⟩

private lemma conj_rankOne (M : HermitianMat ι 𝕜) (v : ι → 𝕜) :
    (rankOne v).conj M.mat = rankOne (M.mat *ᵥ v) := by
  apply HermitianMat.ext
  change M.mat * Matrix.vecMulVec v (star v) * M.mat.conjTranspose =
    Matrix.vecMulVec (M.mat *ᵥ v) (star (M.mat *ᵥ v))
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

private lemma deflated_reading (M : HermitianMat ι 𝕜) (v w : ι → 𝕜) :
    (⟪(rankOne v).conj M.mat, rankOne w⟫_ℝ : 𝕜) =
      (star w ⬝ᵥ (M.mat *ᵥ v)) * (star v ⬝ᵥ (M.mat *ᵥ w)) := by
  rw [pair_rankOne, conj_rankOne]
  change star w ⬝ᵥ (Matrix.vecMulVec (M.mat *ᵥ v) (star (M.mat *ᵥ v)) *ᵥ w) = _
  rw [Matrix.vecMulVec_mulVec]
  simp only [dotProduct_smul, op_smul_eq_smul, smul_eq_mul]
  rw [Matrix.star_mulVec, M.H.eq, ← Matrix.dotProduct_mulVec]
  ring

/-- A single original proper effect realizes an arbitrary finite list of pure
zeros exactly when one same-unit positive lift realizes all cross zeros.
The list may be empty and may repeat entries. -/
theorem common_original_effect_lift
    (L : Submodule ℝ (HermitianMat ι 𝕜)) (hI : (1 : HermitianMat ι 𝕜) ∈ L)
    (v : ι → 𝕜) (hv : star v ⬝ᵥ v = 1) (hp : rankOne v ∈ L)
    (m : ℕ) (w : Fin m → (ι → 𝕜))
    (hq : ∀ j, rankOne (w j) ∈ L) :
    (∃ f : L →ₗ[ℝ] ℝ, Proper f ∧ f ⟨rankOne v, hp⟩ = 1 ∧
      ∀ j, f ⟨rankOne (w j), hq j⟩ = 0) ↔
    ∃ M ∈ lifts L, ∀ j, star v ⬝ᵥ (M.mat *ᵥ w j) = 0 := by
  constructor
  · rintro ⟨f, hf, hfp, hfq⟩
    obtain ⟨E, hE, he⟩ := positive_functional_psd_lift L hI f (fun X hX => (hf X ((mem_cone L X).mpr hX)).1)
    obtain ⟨F, hF, hFf⟩ := positive_functional_psd_lift L hI (unit L - f)
      (fun X hX => sub_nonneg.mpr (hf X ((mem_cone L X).mpr hX)).2)
    have hFp : ⟪F, rankOne v⟫_ℝ = 0 := by
      rw [← hFf ⟨rankOne v, hp⟩]
      simp [unit, hfp, rankOne_trace v hv]
    have hFv : F.mat *ᵥ v = 0 :=
      (HermitianMat.zero_le_iff.mp hF).dotProduct_mulVec_zero_iff.mp (by
        rw [← pair_rankOne F v, hFp]; simp)
    refine ⟨E + F, (mem_lifts_iff L (E + F)).mpr ⟨add_nonneg hE hF, ?_⟩, ?_⟩
    · intro X
      rw [inner_add_left, ← he X, ← hFf X]
      simp
    · intro j
      have hEw : E.mat *ᵥ w j = 0 :=
        (HermitianMat.zero_le_iff.mp hE).dotProduct_mulVec_zero_iff.mp (by
          rw [← pair_rankOne E (w j), ← he ⟨rankOne (w j), hq j⟩, hfq j]; simp)
      simp only [HermitianMat.mat_add, Matrix.add_mulVec, dotProduct_add, hEw, dotProduct_zero,
        zero_add]
      rw [Matrix.dotProduct_mulVec, ← F.H.eq, ← Matrix.star_mulVec, hFv]
      simp
  · rintro ⟨M, hM, hzero⟩
    obtain ⟨hMpos, hMu⟩ := (mem_lifts_iff L M).mp hM
    have hMv : star v ⬝ᵥ (M.mat *ᵥ v) = 1 := by
      rw [← pair_rankOne, hMu ⟨rankOne v, hp⟩]
      simp [unit, rankOne_trace v hv]
    obtain ⟨hE, hComp⟩ := rank_one_deflation M hMpos v hMv
    let E := (rankOne v).conj M.mat
    let f : L →ₗ[ℝ] ℝ := (HermitianMat.innerₗ E).comp L.subtype
    refine ⟨f, ?_, ?_, ?_⟩
    · intro X hX
      have hX := (mem_cone L X).mp hX
      refine ⟨HermitianMat.inner_ge_zero hE hX, ?_⟩
      have hc := HermitianMat.inner_ge_zero hComp hX
      rw [inner_sub_left, hMu X] at hc
      exact sub_nonneg.mp hc
    · change ⟪E, rankOne v⟫_ℝ = 1
      apply RCLike.ofReal_injective (K := 𝕜)
      rw [deflated_reading, hMv, mul_one]
      simp
    · intro j
      change ⟪E, rankOne (w j)⟫_ℝ = 0
      apply RCLike.ofReal_injective (K := 𝕜)
      rw [deflated_reading, hzero j, mul_zero]
      simp

/-- The same-unit lift set has the full real affine dimension of the trace
orthogonal complement, as well as compactness, convexity and fixed trace. -/
theorem lift_geometry
    (L : Submodule ℝ (HermitianMat ι 𝕜)) (hI : (1 : HermitianMat ι 𝕜) ∈ L) :
    (lifts L).Nonempty ∧ IsCompact (lifts L) ∧ Convex ℝ (lifts L) ∧
    (∀ M ∈ lifts L, M.trace = Fintype.card ι) ∧
    (affineSpan ℝ (lifts L)).direction = Lᗮ ∧
    Module.finrank ℝ (affineSpan ℝ (lifts L)).direction = Module.finrank ℝ Lᗮ := by
  have hone : (1 : HermitianMat ι 𝕜) ∈ lifts L := ⟨zero_le_one, by simp⟩
  have htrace (M : HermitianMat ι 𝕜) (hM : M ∈ lifts L) : M.trace = Fintype.card ι := by
    have h := (mem_lifts_iff L M).mp hM |>.2 ⟨1, hI⟩
    simpa [unit] using h
  have hclosed : IsClosed (lifts L) :=
    HermitianMat.isClosed_nonneg.inter
      (Lᗮ.closed_of_finiteDimensional.preimage (continuous_id.sub continuous_const))
  have hcompact : IsCompact (lifts L) :=
    isCompact_Icc.of_isClosed_subset hclosed (fun M hM =>
      ⟨hM.1, by simpa [htrace M hM] using HermitianMat.le_trace_smul_one hM.1⟩)
  have hconvex : Convex ℝ (lifts L) := by
    intro M hM N hN a b ha hb hab
    refine ⟨add_nonneg (smul_nonneg ha hM.1) (smul_nonneg hb hN.1), ?_⟩
    have heq : a • M + b • N - 1 = a • (M - 1) + b • (N - 1) := by
      calc
        a • M + b • N - 1 = a • M + b • N - (a + b) • 1 := by rw [hab, one_smul]
        _ = a • (M - 1) + b • (N - 1) := by module
    rw [heq]
    exact Lᗮ.add_mem (Lᗮ.smul_mem a hM.2) (Lᗮ.smul_mem b hN.2)
  have hle : affineSpan ℝ (lifts L) ≤ AffineSubspace.mk' 1 Lᗮ :=
    affineSpan_le.mpr (fun M hM => hM.2)
  have hdir : (affineSpan ℝ (lifts L)).direction = Lᗮ := by
    apply le_antisymm
    · simpa using AffineSubspace.direction_le hle
    · intro N hN
      obtain ⟨t, ht, hNt⟩ := ambient_majorization N
      let a : ℝ := (t + 1)⁻¹
      have ha : 0 < a := inv_pos.mpr (by linarith)
      have hpos : 0 ≤ 1 + a • N := by
        have hh := add_nonneg hNt (show 0 ≤ (1 : HermitianMat ι 𝕜) from zero_le_one)
        have hs := smul_nonneg ha.le hh
        have heq : a • (N + t • 1 + 1) = 1 + a • N := by
          simp only [smul_add, smul_smul]
          have hat : a * t + a = 1 := by dsimp [a]; field_simp
          calc
            a • N + (a * t) • 1 + a • 1 = a • N + (a * t + a) • 1 := by
              rw [add_smul]; abel
            _ = 1 + a • N := by rw [hat, one_smul, add_comm]
        rwa [heq] at hs
      have hmem : 1 + a • N ∈ lifts L :=
        ⟨hpos, by simpa using Lᗮ.smul_mem a hN⟩
      have hd := AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ (lifts L) hmem) (subset_affineSpan ℝ (lifts L) hone)
      have hscale := (affineSpan ℝ (lifts L)).direction.smul_mem a⁻¹ hd
      simpa [smul_smul, ha.ne'] using hscale
  exact ⟨⟨1, hone⟩, hcompact, hconvex, htrace, hdir, by rw [hdir]⟩

end D5.S3.Quantum.Foundation.SectionPositiveLift
