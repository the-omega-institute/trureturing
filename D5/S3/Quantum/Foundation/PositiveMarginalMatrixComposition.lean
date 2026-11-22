/- GID: D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/PositiveMarginalMatrixComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive marginals determine joint rank and commuting Jordan embeddings. -/

import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity
import D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Positive marginals on full complex Hermitian matrices

The binary data are equation (15) of the Barnum–Hilgert Library note.
Deterministic readback bounds the joint size from below. Real product
spanning gives the reverse bound. The completed product frames yield
the matrix and Jordan multiplication laws in (16) and the ranks in (18).
-/

noncomputable section
open Matrix Unitary
open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace TensorProduct BigOperators

namespace PositiveMarginalMatrixComposition

open D5.S3.Quantum.Measurement.BasisMeasurementProjection (HermitianSpace)
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
  (identityHermitian hermitian_space_finrank)
open D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity (zero_trace_mul_eq_zero)
open D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace (trace_rank_one)

abbrev H (n : ℕ) := HermitianSpace n
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev unitH (n : ℕ) : H n := identityHermitian n

def tr {n : ℕ} (x : H n) : ℝ := x.val.trace.re
def pairing {n : ℕ} (x y : H n) : ℝ := (x.val * y.val).trace.re

/-- The full effect interval for the canonical trace. -/
def IsEffect {n : ℕ} (f : H n) : Prop :=
  f.val.PosSemidef ∧ (1 - f.val).PosSemidef

/-- Equation (15) except for spanning, which is supplied separately to the
dimension equality. The maps and readback are real-linear on the full carriers. -/
structure Marginals {a b d : ℕ} (M : H a →ₗ[ℝ] H b →ₗ[ℝ] H d)
    (RA : H d →ₗ[ℝ] H a) (RB : H d →ₗ[ℝ] H b) : Prop where
  prep_pos : ∀ x y, x.val.PosSemidef → y.val.PosSemidef → (M x y).val.PosSemidef
  posA : ∀ z, z.val.PosSemidef → (RA z).val.PosSemidef
  posB : ∀ z, z.val.PosSemidef → (RB z).val.PosSemidef
  tpA : ∀ z, tr (RA z) = tr z
  tpB : ∀ z, tr (RB z) = tr z
  readA : ∀ x y, RA (M x y) = tr y • x
  readB : ∀ x y, RB (M x y) = tr x • y

def Spans {a b d : ℕ} (M : H a →ₗ[ℝ] H b →ₗ[ℝ] H d) : Prop :=
  Submodule.span ℝ {z | ∃ x y, M x y = z} = ⊤

variable {a b d n : ℕ}

private theorem herm (x : H n) : x.val.IsHermitian := x.property

private def ofHerm (x : Mat n) (hx : x.IsHermitian) : H n := ⟨x, hx⟩

@[simp] private theorem val_unit : (unitH n).val = 1 := rfl
@[simp] private theorem val_ofHerm (x : Mat n) (hx) : (ofHerm x hx).val = x := rfl

private theorem coe_pairing (x y : H n) : (pairing x y : ℂ) = (x.val * y.val).trace := by
  unfold pairing
  apply Complex.conj_eq_iff_re.mp
  change star ((x.val * y.val).trace) = (x.val * y.val).trace
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, (herm x).eq, (herm y).eq,
    Matrix.trace_mul_comm]

private theorem coe_tr (x : H n) : (tr x : ℂ) = x.val.trace := by
  simpa [pairing, tr] using coe_pairing (unitH n) x

@[simp] private theorem tr_smul (c : ℝ) (x : H n) : tr (c • x) = c * tr x := by
  simp [tr, Matrix.trace_smul]

scoped instance (k : ℕ) : NormedAddCommGroup (Mat k) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one
scoped instance (k : ℕ) : InnerProductSpace ℂ (Mat k) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one
scoped instance (k : ℕ) : InnerProductSpace ℝ (Mat k) :=
  InnerProductSpace.rclikeToReal ℂ (Mat k)

theorem inner_eq_pairing (x y : H n) : ⟪x, y⟫_ℝ = pairing x y := by
  change (y.val * 1 * x.valᴴ).trace.re = _
  rw [mul_one, (herm x).eq, Matrix.trace_mul_comm]
  rfl

/-- The marginal adjoint for the real canonical trace pairing. -/
def effect (R : H d →ₗ[ℝ] H n) : H n →ₗ[ℝ] H d := R.adjoint

theorem effect_pairing (R : H d →ₗ[ℝ] H n) (f : H n) (z : H d) :
    pairing (effect R f) z = pairing f (R z) := by
  simpa only [effect, inner_eq_pairing] using LinearMap.adjoint_inner_left R z f

theorem effect_pos (R : H d →ₗ[ℝ] H n)
    (hR : ∀ z, z.val.PosSemidef → (R z).val.PosSemidef)
    (f : H n) (hf : f.val.PosSemidef) : (effect R f).val.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (herm _)
  intro v
  let Z := ofHerm (Matrix.vecMulVec v (star v))
    (Matrix.posSemidef_vecMulVec_self_star v).isHermitian
  have hg : 0 ≤ pairing (effect R f) Z := by
    rw [effect_pairing]
    exact RHLinalg.trace_mul_nonneg_of_posSemidef hf
      (hR Z (Matrix.posSemidef_vecMulVec_self_star v))
  change 0 ≤ ((effect R f).val * Matrix.vecMulVec v (star v)).trace.re at hg
  rw [trace_rank_one] at hg
  exact Complex.nonneg_iff.mpr ⟨hg, ((herm (effect R f)).im_star_dotProduct_mulVec_self v).symm⟩

theorem effect_unital (R : H d →ₗ[ℝ] H n) (hR : ∀ z, tr (R z) = tr z) :
    effect R (unitH n) = unitH d := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_eq_pairing, inner_eq_pairing, effect_pairing]
  simpa [pairing, tr] using hR z

private def diagProj (i : Fin n) : Mat n :=
  Matrix.diagonal (fun j => if i = j then 1 else 0)

private theorem diagProj_psd (i : Fin n) : (diagProj i).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro j
  by_cases h : i = j <;> simp [h]

private theorem diagProj_mul (i j : Fin n) :
    diagProj i * diagProj j = if i = j then diagProj i else 0 := by
  rw [diagProj, diagProj, Matrix.diagonal_mul_diagonal]
  by_cases h : i = j
  · subst j
    rw [ite_eq_left rfl]
    congr 1
    funext k
    by_cases hk : i = k <;> simp [hk]
  · rw [ite_eq_right h, ← Matrix.diagonal_zero]
    congr 1
    funext k
    by_cases hi : i = k
    · subst k
      simp [Ne.symm h]
    · simp [hi]

private theorem diagProj_trace (i : Fin n) : (diagProj i).trace = 1 := by
  simp [diagProj, Matrix.trace_diagonal, Finset.sum_ite_eq]

private theorem diagProj_rank (i : Fin n) : (diagProj i).rank = 1 := by
  classical
  rw [diagProj, Matrix.rank_diagonal, Fintype.card_eq_one_iff]
  refine ⟨⟨i, by simp⟩, fun k => Subtype.ext ?_⟩
  by_contra h
  exact k.property (by simp [Ne.symm h])

private theorem sum_diag (c : Fin n → ℝ) :
    ∑ i, c i • diagProj i = Matrix.diagonal (fun i => (c i : ℂ)) := by
  ext j k
  by_cases h : j = k
  · subst k
    simp [diagProj, Matrix.sum_apply, Matrix.smul_apply]
  · simp [diagProj, Matrix.sum_apply, Matrix.smul_apply, h]

private def conjU (U : ↥(unitary (Mat n))) : Mat n ≃⋆ₐ[ℂ] Mat n :=
  Unitary.conjStarAlgAut ℂ (Mat n) U

private theorem conjU_psd (U : ↥(unitary (Mat n))) {P : Mat n} (h : P.PosSemidef) :
    (conjU U P).PosSemidef :=
  (Unitary.isUnit_coe (U := U)).posSemidef_star_right_conjugate_iff.mpr h

private theorem conjU_trace (U : ↥(unitary (Mat n))) (P : Mat n) :
    (conjU U P).trace = P.trace := by
  change ((U.val * P) * star U.val).trace = _
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

private theorem conjU_rank (U : ↥(unitary (Mat n))) (P : Mat n) :
    (conjU U P).rank = P.rank := by
  have hle (V : ↥(unitary (Mat n))) (Q : Mat n) : (conjU V Q).rank ≤ Q.rank :=
    (Matrix.rank_mul_le_left (V.val * Q) (star V.val)).trans
      (Matrix.rank_mul_le_right V.val Q)
  apply le_antisymm (hle U P)
  have hh := hle (star U) (conjU U P)
  have he : conjU (star U) (conjU U P) = P := by
    let F := Unitary.conjStarAlgAut ℂ (Mat n)
    change (F (star U)) ((F U) P) = P
    change (F (star U) * F U) P = P
    rw [← map_mul, Unitary.star_mul_self, map_one]
    rfl
  simpa only [he] using hh

/-- The conjugate of a diagonal coordinate projection in the given unitary frame. -/
def frameProjection (U : ↥(unitary (Mat n))) (i : Fin n) : H n :=
  ofHerm (conjU U (diagProj i)) (conjU_psd U (diagProj_psd i)).isHermitian

theorem proj_psd (U : ↥(unitary (Mat n))) (i : Fin n) :
    (frameProjection U i).val.PosSemidef := conjU_psd U (diagProj_psd i)

theorem proj_trace (U : ↥(unitary (Mat n))) (i : Fin n) :
    (frameProjection U i).val.trace = 1 := by
  change (conjU U (diagProj i)).trace = 1
  rw [conjU_trace, diagProj_trace]

theorem proj_rank (U : ↥(unitary (Mat n))) (i : Fin n) :
    (frameProjection U i).val.rank = 1 := by
  change (conjU U (diagProj i)).rank = 1
  rw [conjU_rank, diagProj_rank]

theorem proj_mul (U : ↥(unitary (Mat n))) (i j : Fin n) :
    (frameProjection U i).val * (frameProjection U j).val =
      if i = j then (frameProjection U i).val else 0 := by
  change conjU U (diagProj i) * conjU U (diagProj j) = _
  rw [← map_mul, diagProj_mul]
  split <;> simp [frameProjection]

private theorem sum_proj_weighted (U : ↥(unitary (Mat n))) (c : Fin n → ℝ) :
    (∑ i, c i • frameProjection U i : H n).val = conjU U (Matrix.diagonal fun i => (c i : ℂ)) := by
  rw [← sum_diag]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, frameProjection, val_ofHerm, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (LinearMap.map_smul_of_tower (conjU U).toAlgEquiv.toLinearMap
    (c i) (diagProj i)).symm

theorem sum_frameProjection (U : ↥(unitary (Mat n))) : ∑ i, frameProjection U i = unitH n := by
  apply Subtype.ext
  simpa using sum_proj_weighted U (fun _ => 1)

private theorem spectral (x : H n) :
    x = ∑ i, (herm x).eigenvalues i • frameProjection (herm x).eigenvectorUnitary i := by
  apply Subtype.ext
  rw [sum_proj_weighted]
  exact (herm x).spectral_theorem

private theorem spectral_mul_frameProjection (x : H n) (i : Fin n) :
    x.val * (frameProjection (herm x).eigenvectorUnitary i).val =
      (herm x).eigenvalues i • (frameProjection (herm x).eigenvectorUnitary i).val := by
  have hx := congrArg Subtype.val (spectral x)
  nth_rw 1 [hx]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Matrix.sum_mul, Matrix.smul_mul,
    proj_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private theorem rank_one_spectral (x : H n) (hr : x.val.rank = 1) :
    ∃ i, (herm x).eigenvalues i ≠ 0 ∧
      x = (herm x).eigenvalues i • frameProjection (herm x).eigenvectorUnitary i := by
  classical
  rw [(herm x).rank_eq_card_non_zero_eigs, Fintype.card_eq_one_iff] at hr
  obtain ⟨i, hi⟩ := hr
  have hz (j : Fin n) (hj : j ≠ i.val) : (herm x).eigenvalues j = 0 := by
    by_contra h
    exact hj (congrArg Subtype.val (hi ⟨j, h⟩))
  refine ⟨i.val, i.property, ?_⟩
  calc
    x = _ := spectral x
    _ = _ := Finset.sum_eq_single i.val
      (fun j _ hj => by rw [hz j hj, zero_smul]) (by simp)

private theorem pure_in_frame (x : H n) (hr : x.val.rank = 1) (ht : x.val.trace = 1) :
    ∃ i, x = frameProjection (herm x).eigenvectorUnitary i := by
  obtain ⟨i, _, hs⟩ := rank_one_spectral x hr
  have he := congrArg tr hs
  have htr : tr x = 1 := by simp [tr, ht]
  rw [tr_smul, htr, show tr (frameProjection (herm x).eigenvectorUnitary i) = 1 by
    simp [tr, proj_trace], mul_one] at he
  refine ⟨i, hs.trans ?_⟩
  rw [← he, one_smul]


variable {M : H a →ₗ[ℝ] H b →ₗ[ℝ] H d}
  {RA : H d →ₗ[ℝ] H a} {RB : H d →ₗ[ℝ] H b}

theorem trace_prep (h : Marginals M RA RB) (x : H a) (y : H b) :
    tr (M x y) = tr y * tr x := by
  rw [← h.tpA, h.readA, tr_smul]

private theorem proj_tr (U : ↥(unitary (Mat n))) (i : Fin n) : tr (frameProjection U i) = 1 := by
  simp [tr, proj_trace]

private theorem proj_delta (U : ↥(unitary (Mat n))) (i j : Fin n) :
    pairing (frameProjection U i) (frameProjection U j) = if i = j then 1 else 0 := by
  unfold pairing
  rw [proj_mul]
  split <;> simp [proj_trace]

private theorem deterministic (e z : H d) (he : e.val.PosSemidef)
    (hc : (1 - e.val).PosSemidef) (hz : z.val.PosSemidef) (ht : z.val.trace = 1)
    (δ : Prop) [Decidable δ] (hp : pairing e z = if δ then 1 else 0) :
    e.val * z.val = if δ then z.val else 0 := by
  have hp' := coe_pairing e z
  rw [hp] at hp'
  by_cases hδ : δ
  · rw [ite_eq_left hδ, Complex.ofReal_one] at hp'
    rw [ite_eq_left hδ]
    have ht' : ((1 - e.val) * z.val).trace = 0 := by
      rw [sub_mul, one_mul, Matrix.trace_sub, ht, ← hp']
      norm_num
    have hh := zero_trace_mul_eq_zero (1 - e.val) z.val hc hz ht'
    rw [sub_mul, one_mul, sub_eq_zero] at hh
    exact hh.symm
  · rw [ite_eq_right hδ, Complex.ofReal_zero] at hp'
    rw [ite_eq_right hδ]
    exact zero_trace_mul_eq_zero e.val z.val he hz hp'.symm

theorem frameProjection_isEffect (U : ↥(unitary (Mat n))) (i : Fin n) :
    IsEffect (frameProjection U i) := by
  refine ⟨proj_psd U i, ?_⟩
  have he : 1 - (frameProjection U i).val = conjU U (1 - diagProj i) := by
    simp [frameProjection, map_sub]
  rw [he]
  apply conjU_psd
  rw [← Matrix.diagonal_one, diagProj, Matrix.diagonal_sub]
  apply Matrix.PosSemidef.diagonal
  intro j
  by_cases h : i = j <;> simp [h]

theorem effect_map_interval (R : H d →ₗ[ℝ] H n)
    (hp : ∀ z, z.val.PosSemidef → (R z).val.PosSemidef)
    (ht : ∀ z, tr (R z) = tr z) (f : H n) (hf : IsEffect f) :
    IsEffect (effect R f) := by
  refine ⟨effect_pos R hp f hf.1, ?_⟩
  have hv := effect_pos R hp (unitH n - f) hf.2
  rwa [map_sub, Submodule.coe_sub, effect_unital R ht, val_unit] at hv

private abbrev prepared (M : H a →ₗ[ℝ] H b →ₗ[ℝ] H d)
    (U : ↥(unitary (Mat a))) (V : ↥(unitary (Mat b))) (k : Fin a × Fin b) : H d :=
  M (frameProjection U k.1) (frameProjection V k.2)

private theorem prepared_trace (h : Marginals M RA RB)
    (U : ↥(unitary (Mat a))) (V : ↥(unitary (Mat b))) (k : Fin a × Fin b) :
    (prepared M U V k).val.trace = 1 := by
  rw [← coe_tr, trace_prep h, proj_tr, proj_tr, one_mul, Complex.ofReal_one]

private theorem prepared_psd (h : Marginals M RA RB)
    (U : ↥(unitary (Mat a))) (V : ↥(unitary (Mat b))) (k : Fin a × Fin b) :
    (prepared M U V k).val.PosSemidef :=
  h.prep_pos _ _ (proj_psd U k.1) (proj_psd V k.2)

private theorem deterministicA (h : Marginals M RA RB)
    (U : ↥(unitary (Mat a))) (V : ↥(unitary (Mat b))) (i : Fin a) (k : Fin a × Fin b) :
    (effect RA (frameProjection U i)).val * (prepared M U V k).val =
      if i = k.1 then (prepared M U V k).val else 0 := by
  obtain ⟨he, hc⟩ := effect_map_interval RA h.posA h.tpA _ (frameProjection_isEffect U i)
  apply deterministic _ _ he hc (prepared_psd h U V k) (prepared_trace h U V k)
  rw [effect_pairing]
  change pairing (frameProjection U i) (RA (M (frameProjection U k.1) (frameProjection V k.2))) = _
  rw [h.readA, proj_tr, one_smul, proj_delta]

private theorem deterministicB (h : Marginals M RA RB)
    (U : ↥(unitary (Mat a))) (V : ↥(unitary (Mat b))) (j : Fin b) (k : Fin a × Fin b) :
    (effect RB (frameProjection V j)).val * (prepared M U V k).val =
      if j = k.2 then (prepared M U V k).val else 0 := by
  obtain ⟨he, hc⟩ := effect_map_interval RB h.posB h.tpB _ (frameProjection_isEffect V j)
  apply deterministic _ _ he hc (prepared_psd h U V k) (prepared_trace h U V k)
  rw [effect_pairing]
  change pairing (frameProjection V j) (RB (M (frameProjection U k.1) (frameProjection V k.2))) = _
  rw [h.readB, proj_tr, one_smul, proj_delta]

private theorem mul_flip {X Y : Mat n} (hx : X.IsHermitian) (hy : Y.IsHermitian)
    (e : X * Y = Y) : Y * X = Y := by
  simpa only [Matrix.conjTranspose_mul, hx.eq, hy.eq] using
    congrArg Matrix.conjTranspose e

private theorem mul_flip_zero {X Y : Mat n} (hx : X.IsHermitian) (hy : Y.IsHermitian)
    (e : X * Y = 0) : Y * X = 0 := by
  simpa only [Matrix.conjTranspose_mul, hx.eq, hy.eq, Matrix.conjTranspose_zero] using
    congrArg Matrix.conjTranspose e

private theorem orthogonal_of_reading {E X Y : Mat n} (he : E.IsHermitian)
    (hx : X.IsHermitian) (hfix : E * X = X) (hkill : E * Y = 0) : X * Y = 0 := by
  calc
    X * Y = (X * E) * Y := by rw [mul_flip he hx hfix]
    _ = 0 := by rw [mul_assoc, hkill, mul_zero]

private theorem prepared_mul_zero (h : Marginals M RA RB)
    (U : ↥(unitary (Mat a))) (V : ↥(unitary (Mat b))) {k l : Fin a × Fin b} (hne : k ≠ l) :
    (prepared M U V k).val * (prepared M U V l).val = 0 := by
  by_cases hkl : k.1 = l.1
  · have hn : k.2 ≠ l.2 := fun e => hne (Prod.ext hkl e)
    exact orthogonal_of_reading (herm (effect RB (frameProjection V k.2))) (herm _)
      (by simpa using deterministicB h U V k.2 k)
      (by simpa [hn] using deterministicB h U V k.2 l)
  · exact orthogonal_of_reading (herm (effect RA (frameProjection U k.1))) (herm _)
      (by simpa using deterministicA h U V k.1 k)
      (by simpa [hkl] using deterministicA h U V k.1 l)

/-- The prepared states of any two unitary frames have orthogonal supports.
This conclusion uses no spanning hypothesis. -/
theorem frame_orthogonal (h : Marginals M RA RB)
    (U : ↥(unitary (Mat a))) (V : ↥(unitary (Mat b))) :
    Pairwise fun k l : Fin a × Fin b =>
      (M (frameProjection U k.1) (frameProjection V k.2)).val *
        (M (frameProjection U l.1) (frameProjection V l.2)).val = 0 :=
  fun _ _ hne => prepared_mul_zero h U V hne

/-- A complete product frame, represented by normalized projections in the
actual joint carrier. -/
private theorem frame_completion (h : Marginals M RA RB)
    (U : ↥(unitary (Mat a))) (V : ↥(unitary (Mat b))) :
    a * b ≤ d ∧ (d = a * b →
      (∑ k, prepared M U V k) = unitH d ∧
      (∀ k, (prepared M U V k).val.rank = 1) ∧
      ∀ k l, (prepared M U V k).val * (prepared M U V l).val =
        if k = l then (prepared M U V k).val else 0) := by
  classical
  let ρ : Fin a × Fin b → H d := prepared M U V
  have hn (k) : ∃ i, (herm (ρ k)).eigenvalues i ≠ 0 := by
    by_contra! hzero
    have he : (ρ k).val = 0 :=
      (herm (ρ k)).eigenvalues_eq_zero_iff.mp (funext hzero)
    have ht := prepared_trace h U V k
    change (ρ k).val.trace = 1 at ht
    simp [he] at ht
  choose i hi using hn
  let P (k : Fin a × Fin b) : H d := frameProjection (herm (ρ k)).eigenvectorUnitary (i k)
  let S : Mat d := ∑ k, (P k).val
  have hρP (k) : (ρ k).val * (P k).val = (herm (ρ k)).eigenvalues (i k) • (P k).val :=
    spectral_mul_frameProjection _ _
  have kill (k l) (hne : k ≠ l) : (ρ k).val * (P l).val = 0 := by
    have hh := congrArg (fun X : Mat d => X * (P l).val) (frame_orthogonal h U V hne)
    change ((ρ k).val * (ρ l).val) * (P l).val = 0 * (P l).val at hh
    rw [mul_assoc, hρP, Matrix.mul_smul, zero_mul, smul_eq_zero] at hh
    exact hh.resolve_left (hi l)
  have hPρ (k l) (hne : k ≠ l) : (P k).val * (ρ l).val = 0 :=
    mul_flip_zero (herm (ρ l)) (herm (P k)) (kill l k (Ne.symm hne))
  have hP (k l) : (P k).val * (P l).val = if k = l then (P k).val else 0 := by
    by_cases hh : k = l
    · subst l
      simpa [P] using proj_mul (herm (ρ k)).eigenvectorUnitary (i k) (i k)
    · have he := congrArg (fun X : Mat d => X * (P l).val) (hPρ k l hh)
      change ((P k).val * (ρ l).val) * (P l).val = 0 * (P l).val at he
      rw [mul_assoc, hρP, Matrix.mul_smul, zero_mul, smul_eq_zero] at he
      simpa [hh] using he.resolve_left (hi l)
  have hSS : S * S = S := by
    simp only [S, Matrix.sum_mul, Matrix.mul_sum, hP]
    simp
  have hS : S.IsHermitian := by
    simpa only [Submodule.coe_sum] using herm (∑ k, P k)
  have hc : (1 - S).PosSemidef := by
    convert Matrix.posSemidef_self_mul_conjTranspose (1 - S) using 1
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hS.eq]
    noncomm_ring [hSS]
  have hSt : S.trace = (a * b : ℕ) := by
    simp [S, Matrix.trace_sum, P, proj_trace, Fintype.card_prod, Nat.cast_mul]
  have ht : (1 - S).trace = (d : ℂ) - (a * b : ℕ) := by
    simp [Matrix.trace_sub, hSt, Matrix.trace_one]
  constructor
  · have hnr := Complex.nonneg_iff.mp hc.trace_nonneg
    rw [ht, Complex.sub_re, Complex.natCast_re, Complex.natCast_re] at hnr
    exact_mod_cast (sub_nonneg.mp hnr.1 : (a * b : ℕ) ≤ (d : ℝ))
  · intro hd
    have he : S = 1 := by
      have hh : (1 - S) = 0 := hc.trace_eq_zero_iff.mp (by simp [ht, hd])
      exact (sub_eq_zero.mp hh).symm
    have hρ (k) : ρ k = P k := by
      have hm : (ρ k).val = (herm (ρ k)).eigenvalues (i k) • (P k).val := by
        calc
          (ρ k).val = (ρ k).val * S := by rw [he, mul_one]
          _ = _ := by
            rw [show S = ∑ l, (P l).val from rfl, Matrix.mul_sum,
              Finset.sum_eq_single k (fun l _ hne => kill k l (Ne.symm hne)) (by simp), hρP]
      have hh : ρ k = (herm (ρ k)).eigenvalues (i k) • P k := Subtype.ext hm
      have hs := congrArg tr hh
      have hz : tr (ρ k) = 1 := by simp [tr, ρ, prepared_trace h U V k]
      rw [tr_smul, hz, show tr (P k) = 1 from proj_tr _ _, mul_one] at hs
      exact hh.trans (by rw [← hs, one_smul])
    refine ⟨Subtype.ext ?_, ?_, ?_⟩
    · change (∑ k, ρ k : H d).val = 1
      simp only [hρ, Submodule.coe_sum]
      exact he
    · intro k
      change (ρ k).val.rank = 1
      rw [hρ]
      exact proj_rank _ _
    · intro k l
      change (ρ k).val * (ρ l).val = if k = l then (ρ k).val else 0
      simpa only [hρ] using hP k l

/-- Perfect product readback already forces the lower bound on joint size. -/
theorem rank_lower_bound (h : Marginals M RA RB) : a * b ≤ d :=
  (frame_completion h 1 1).1

theorem lift_surjective (hs : Spans M) : Function.Surjective (TensorProduct.lift M) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hs]
  apply Submodule.span_le.mpr
  rintro z ⟨x, y, rfl⟩
  exact ⟨x ⊗ₜ[ℝ] y, TensorProduct.lift.tmul x y⟩

/-- Joint size and real dimension follow from readback and spanning. -/
theorem rank_dimension (h : Marginals M RA RB) (hs : Spans M) :
    d = a * b ∧ Module.finrank ℝ (H d) = Module.finrank ℝ (H a) * Module.finrank ℝ (H b) := by
  have hdim := LinearMap.finrank_le_finrank_of_surjective (lift_surjective hs)
  rw [Module.finrank_tensorProduct, hermitian_space_finrank, hermitian_space_finrank,
    hermitian_space_finrank, ← mul_pow] at hdim
  have hu : d ≤ a * b := by
    by_contra! hn
    exact (not_lt_of_ge hdim) (Nat.pow_lt_pow_left hn (by decide : 2 ≠ 0))
  have he := le_antisymm hu (rank_lower_bound h)
  exact ⟨he, by simp only [hermitian_space_finrank, he, mul_pow]⟩

private theorem sum_prepared (U : ↥(unitary (Mat a))) (V : ↥(unitary (Mat b))) :
    (∑ k, prepared M U V k) = M (unitH a) (unitH b) := by
  simp only [Fintype.sum_prod_type, ← sum_frameProjection U, ← sum_frameProjection V,
    map_sum, LinearMap.sum_apply]
  exact Finset.sum_comm

theorem prep_unital (h : Marginals M RA RB) (hs : Spans M) :
    M (unitH a) (unitH b) = unitH d :=
  (sum_prepared 1 1).symm.trans ((frame_completion h 1 1).2 (rank_dimension h hs).1).1

theorem prep_rank_one (h : Marginals M RA RB) (hs : Spans M) (x : H a) (y : H b)
    (hx : x.val.rank = 1) (htx : x.val.trace = 1)
    (hy : y.val.rank = 1) (hty : y.val.trace = 1) :
    (M x y).val.rank = 1 := by
  obtain ⟨i, hi⟩ := pure_in_frame x hx htx
  obtain ⟨j, hj⟩ := pure_in_frame y hy hty
  exact (congrArg (fun z : H d => z.val.rank) (congrArg₂ (fun x y => M x y) hi hj)).trans
    (((frame_completion h _ _).2 (rank_dimension h hs).1).2.1 (i, j))

/-- The actual preparation preserves rank-one products of arbitrary
Hermitian inputs of rank one, including either sign. -/
theorem prep_rank_one_preserver (h : Marginals M RA RB) (hs : Spans M) (x : H a) (y : H b)
    (hx : x.val.rank = 1) (hy : y.val.rank = 1) : (M x y).val.rank = 1 := by
  obtain ⟨i, hci, hxi⟩ := rank_one_spectral x hx
  obtain ⟨j, hcj, hyj⟩ := rank_one_spectral y hy
  let c := (herm x).eigenvalues i * (herm y).eigenvalues j
  let P := frameProjection (herm x).eigenvectorUnitary i
  let Q := frameProjection (herm y).eigenvectorUnitary j
  have he : M x y = c • M P Q := by
    calc
      M x y = M ((herm x).eigenvalues i • P) ((herm y).eigenvalues j • Q) :=
        congrArg₂ (fun u v => M u v) hxi hyj
      _ = _ := by simp [c, smul_smul, mul_comm]
  rw [he]
  change ((c : ℂ) • (M P Q).val).rank = 1
  rw [Matrix.rank_smul_of_mem_nonZeroDivisors]
  · exact prep_rank_one h hs P Q (proj_rank _ _) (proj_trace _ _) (proj_rank _ _) (proj_trace _ _)
  · exact mem_nonZeroDivisors_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (mul_ne_zero hci hcj))

private theorem mul_prepared_eq (h : Marginals M RA RB) (hs : Spans M)
    (U : ↥(unitary (Mat a))) (V : ↥(unitary (Mat b))) (i : Fin a) (j : Fin b) :
    (effect RA (frameProjection U i)).val * (effect RB (frameProjection V j)).val =
      (M (frameProjection U i) (frameProjection V j)).val := by
  classical
  let ρ : Fin a × Fin b → H d := prepared M U V
  let E := (effect RA (frameProjection U i)).val
  let F := (effect RB (frameProjection V j)).val
  have hsum : ∑ k, (ρ k).val = (1 : Mat d) := by
    simpa only [Submodule.coe_sum, val_unit] using
      congrArg Subtype.val ((frame_completion h U V).2 (rank_dimension h hs).1).1
  have hv (k) : (E * F) * (ρ k).val = if (i, j) = k then (ρ k).val else 0 := by
    by_cases hki : i = k.1 <;> by_cases hkj : j = k.2 <;>
      simp [E, F, ρ, mul_assoc, deterministicA h, deterministicB h, Prod.ext_iff, hki, hkj]
  change E * F = (ρ (i, j)).val
  calc
    E * F = (E * F) * 1 := (mul_one _).symm
    _ = ∑ k, (E * F) * (ρ k).val := by rw [← hsum, Matrix.mul_sum]
    _ = (ρ (i, j)).val := by simp [hv]

theorem spectral_ext {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f g : H n →ₗ[ℝ] V)
    (h : ∀ (U : ↥(unitary (Mat n))) i, f (frameProjection U i) = g (frameProjection U i))
    (x : H n) :
    f x = g x := by
  calc
    f x = f (∑ i, (herm x).eigenvalues i • frameProjection (herm x).eigenvectorUnitary i) :=
      congrArg f (spectral x)
    _ = g (∑ i, (herm x).eigenvalues i • frameProjection (herm x).eigenvectorUnitary i) := by
      simp only [map_sum, map_smul, h]
    _ = g x := congrArg g (spectral x).symm

/-- The actual preparation is the product of the two marginal adjoints. -/
theorem effect_mul (h : Marginals M RA RB) (hs : Spans M) (x : H a) (y : H b) :
    (effect RA x).val * (effect RB y).val = (M x y).val := by
  let E := (HermitianSpace d).subtype.comp (effect RA)
  let F := (HermitianSpace d).subtype.comp (effect RB)
  let K := (HermitianSpace d).subtype
  change E x * F y = K (M x y)
  apply spectral_ext ((LinearMap.mulRight ℝ (F y)).comp E) (K.comp (M.flip y)) _ x
  intro U i
  change E (frameProjection U i) * F y = K (M (frameProjection U i) y)
  apply spectral_ext ((LinearMap.mulLeft ℝ (E (frameProjection U i))).comp F)
    (K.comp (M (frameProjection U i))) _ y
  intro V j
  exact mul_prepared_eq h hs U V i j

/-- The marginal adjoints commute in the ambient complex matrix algebra. -/
theorem effect_commute (h : Marginals M RA RB) (hs : Spans M) (x : H a) (y : H b) :
    Commute (effect RA x).val (effect RB y).val := by
  have he := congrArg Matrix.conjTranspose (effect_mul h hs x y)
  simp only [Matrix.conjTranspose_mul, (herm _).eq] at he
  exact (effect_mul h hs x y).trans he.symm

theorem effect_injectiveA [NeZero b] (h : Marginals M RA RB) :
    Function.Injective (effect RA) := by
  intro x y he
  apply ext_inner_right ℝ
  intro z
  let q := frameProjection (1 : ↥(unitary (Mat b))) (0 : Fin b)
  have hh := congrArg (fun f => pairing f (M z q)) he
  rw [effect_pairing, effect_pairing, h.readA, proj_tr, one_smul] at hh
  simpa only [inner_eq_pairing] using hh

theorem effect_injectiveB [NeZero a] (h : Marginals M RA RB) :
    Function.Injective (effect RB) := by
  intro x y he
  apply ext_inner_right ℝ
  intro z
  let p := frameProjection (1 : ↥(unitary (Mat a))) (0 : Fin a)
  have hh := congrArg (fun f => pairing f (M p z)) he
  rw [effect_pairing, effect_pairing, h.readB, proj_tr, one_smul] at hh
  simpa only [inner_eq_pairing] using hh

/-- The ordinary matrix square, with its Hermitian carrier. -/
private def square (x : H n) : H n := ofHerm (x.val * x.val) (by
  change (x.val * x.val)ᴴ = x.val * x.val
  rw [Matrix.conjTranspose_mul, (herm x).eq])

/-- The symmetrized matrix product. -/
def jordan (x y : H n) : H n := ofHerm ((2 : ℝ)⁻¹ • (x.val * y.val + y.val * x.val)) (by
  change (((2 : ℝ)⁻¹ : ℝ) • (x.val * y.val + y.val * x.val))ᴴ = _
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, (herm x).eq, (herm y).eq, add_comm])

private theorem square_spectral (x : H n) :
    square x = ∑ i, ((herm x).eigenvalues i * (herm x).eigenvalues i) •
      frameProjection (herm x).eigenvectorUnitary i := by
  apply Subtype.ext
  rw [sum_proj_weighted]
  change x.val * x.val = _
  have hx := (herm x).spectral_theorem
  nth_rw 1 2 [hx]
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp [Complex.ofReal_mul]

private theorem linear_reading {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : H d →ₗ[ℝ] H n) (P : ι → H n) (z : H d) (j : ι)
    (read : ∀ i, (effect R (P i)).val * z.val = if i = j then z.val else 0)
    (c : ι → ℝ) :
    (effect R (∑ i, c i • P i)).val * z.val = c j • z.val := by
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul_of_tower,
    Matrix.sum_mul, Matrix.smul_mul, read]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [hkj]
  · simp

private theorem square_from_reading {ι : Type*} [Fintype ι]
    (T : ι → H d) (hs : ∑ k, (T k).val = 1) (E F : Mat d)
    (c : ι → ℝ) (read : ∀ k, E * (T k).val = c k • (T k).val)
    (read_sq : ∀ k, F * (T k).val = (c k * c k) • (T k).val) : E * E = F := by
  have hv : ∀ k, (E * E) * (T k).val = F * (T k).val := by
    intro k
    rw [mul_assoc, read, Matrix.mul_smul, read, smul_smul, read_sq]
  calc
    E * E = (E * E) * 1 := (mul_one _).symm
    _ = F * 1 := by rw [← hs, Matrix.mul_sum, Matrix.mul_sum]; simp only [hv]
    _ = F := mul_one _

private theorem effect_squareA (h : Marginals M RA RB) (hs : Spans M) (x : H a) :
    (effect RA x).val * (effect RA x).val = (effect RA (square x)).val := by
  let U := (herm x).eigenvectorUnitary
  let V : ↥(unitary (Mat b)) := 1
  have hsum : ∑ k, (prepared M U V k).val = 1 := by
    simpa only [Submodule.coe_sum, val_unit] using
      congrArg Subtype.val ((frame_completion h U V).2 (rank_dimension h hs).1).1
  refine square_from_reading (prepared M U V) hsum _ _
    (fun k => (herm x).eigenvalues k.1) ?_ ?_
  · intro k
    nth_rw 1 [spectral x]
    exact linear_reading RA (frameProjection U) _ k.1 (fun i => deterministicA h U V i k) _
  · intro k
    rw [square_spectral]
    exact linear_reading RA (frameProjection U) _ k.1 (fun i => deterministicA h U V i k) _

private theorem effect_squareB (h : Marginals M RA RB) (hs : Spans M) (x : H b) :
    (effect RB x).val * (effect RB x).val = (effect RB (square x)).val := by
  let U : ↥(unitary (Mat a)) := 1
  let V := (herm x).eigenvectorUnitary
  have hsum : ∑ k, (prepared M U V k).val = 1 := by
    simpa only [Submodule.coe_sum, val_unit] using
      congrArg Subtype.val ((frame_completion h U V).2 (rank_dimension h hs).1).1
  refine square_from_reading (prepared M U V) hsum _ _
    (fun k => (herm x).eigenvalues k.2) ?_ ?_
  · intro k
    nth_rw 1 [spectral x]
    exact linear_reading RB (frameProjection V) _ k.2 (fun j => deterministicB h U V j k) _
  · intro k
    rw [square_spectral]
    exact linear_reading RB (frameProjection V) _ k.2 (fun j => deterministicB h U V j k) _

private theorem jordan_polarization (x y : H n) :
    jordan x y = (2 : ℝ)⁻¹ • (square (x + y) - square x - square y) := by
  apply Subtype.ext
  change (2 : ℝ)⁻¹ • (x.val * y.val + y.val * x.val) =
    (2 : ℝ)⁻¹ • ((x.val + y.val) * (x.val + y.val) - x.val * x.val - y.val * y.val)
  congr 1
  noncomm_ring

private theorem jordan_of_square (F : H n →ₗ[ℝ] H d)
    (hs : ∀ x, (F x).val * (F x).val = (F (square x)).val) (x y : H n) :
    F (jordan x y) = jordan (F x) (F y) := by
  rw [jordan_polarization, jordan_polarization, map_smul, map_sub, map_sub]
  apply Subtype.ext
  simp only [Submodule.coe_smul_of_tower, Submodule.coe_sub, ← hs, map_add,
    Submodule.coe_add]
  rfl

theorem effect_jordanA (h : Marginals M RA RB) (hs : Spans M) (f x : H a) :
    effect RA (jordan f x) = jordan (effect RA f) (effect RA x) :=
  jordan_of_square _ (effect_squareA h hs) f x

theorem effect_jordanB (h : Marginals M RA RB) (hs : Spans M) (g y : H b) :
    effect RB (jordan g y) = jordan (effect RB g) (effect RB y) :=
  jordan_of_square _ (effect_squareB h hs) g y

theorem effect_jordan_commute (h : Marginals M RA RB) (hs : Spans M)
    (x : H a) (y : H b) (z : H d) :
    jordan (effect RA x) (jordan (effect RB y) z) =
      jordan (effect RB y) (jordan (effect RA x) z) := by
  apply Subtype.ext
  simp only [jordan, val_ofHerm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.add_mul, smul_add]
  have hc := (effect_commute h hs x y).eq
  let A := (effect RA x).val
  let B := (effect RB y).val
  change A * B = B * A at hc
  change
    ((2 : ℝ)⁻¹) • (((2 : ℝ)⁻¹) • (A * (B * z.val))) +
      ((2 : ℝ)⁻¹) • (((2 : ℝ)⁻¹) • (A * (z.val * B))) +
      (((2 : ℝ)⁻¹) • (((2 : ℝ)⁻¹) • (B * z.val * A)) +
      ((2 : ℝ)⁻¹) • (((2 : ℝ)⁻¹) • (z.val * B * A))) =
    ((2 : ℝ)⁻¹) • (((2 : ℝ)⁻¹) • (B * (A * z.val))) +
      ((2 : ℝ)⁻¹) • (((2 : ℝ)⁻¹) • (B * (z.val * A))) +
      (((2 : ℝ)⁻¹) • (((2 : ℝ)⁻¹) • (A * z.val * B)) +
      ((2 : ℝ)⁻¹) • (((2 : ℝ)⁻¹) • (z.val * A * B)))
  simp only [← mul_assoc, hc]
  have hz : z.val * B * A = z.val * A * B := by rw [mul_assoc, ← hc, ← mul_assoc]
  rw [hz]
  abel

/-- The effect product is the actual preparation under the trace identification. -/
theorem effect_product (h : Marginals M RA RB) (hs : Spans M) (f : H a) (g : H b) :
    jordan (effect RA f) (effect RB g) = M f g := by
  apply Subtype.ext
  simp only [jordan, val_ofHerm, ← (effect_commute h hs f g).eq, effect_mul h hs,
    ← two_smul ℝ, smul_smul]
  norm_num

end PositiveMarginalMatrixComposition
