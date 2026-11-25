/- GID: D5/S3/Quantum/Measurement/Auric/UnequalGeometryFrames
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/UnequalGeometryFrames
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct and recover flat projection states from rank-capped effects on arbitrary labeled fibers. -/

import D5.S3.Quantum.Measurement.Auric.UnequalPhysicalTargets
import D5.S3.Quantum.Measurement.Auric.DisjointSpectralSuppliers

/-! Frames for the fixed-law geometry on arbitrary labeled coordinate fibers. -/

namespace D5.S3.Quantum.Measurement.Auric.GeometryFrames

open _root_.Matrix
open scoped Matrix BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)
open D5.S3.Quantum.Measurement.Auric.CoordinatePinching (coordinatePVM)
open D5.S3.Quantum.Measurement.Auric.EqualBlockProjection (gain)
open D5.S3.Quantum.Measurement.Auric.EqualBlockEffects (entropyIntegrand)
open D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects (Feasible spectralSum)

open D5.S3.Quantum.Measurement.Auric.EqualBlockProjection (trace_projection)

noncomputable section

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

abbrev Fiber (c : ι → Fin 3) (j : Fin 3) := {a : ι // c a = j}

def fiberRows (c : ι → Fin 3) (V : Matrix ι n ℂ) (j : Fin 3) :
    Matrix (Fiber c j) n ℂ :=
  V.submatrix Subtype.val id

def fiberCompression (c : ι → Fin 3) (P : Matrix ι ι ℂ) (j : Fin 3) :
    Matrix (Fiber c j) (Fiber c j) ℂ :=
  P.submatrix Subtype.val Subtype.val

def rowEffects (c : ι → Fin 3) (V : Matrix ι n ℂ) (j : Fin 3) :
    Matrix n n ℂ :=
  (fiberRows c V j)ᴴ * fiberRows c V j

theorem fiberCompression_projected (c : ι → Fin 3) (P : Matrix ι ι ℂ) (j : Fin 3) :
    fiberCompression c ((coordinatePVM c).proj j * P * (coordinatePVM c).proj j) j =
      fiberCompression c P j := by
  ext a b
  change ((coordinatePVM c).proj j * P * (coordinatePVM c).proj j) a.val b.val =
    P a.val b.val
  simp [coordinatePVM, Matrix.mul_diagonal, Matrix.diagonal_mul, a.property, b.property]

theorem trace_coordinate_mul (c : ι → Fin 3) (P : Matrix ι ι ℂ) (j : Fin 3) :
    ((coordinatePVM c).proj j * P).trace = (fiberCompression c P j).trace := by
  classical
  calc
    ((coordinatePVM c).proj j * P).trace =
        ∑ a ∈ Finset.univ.filter (fun a => c a = j), P a a := by
      rw [Finset.sum_filter]
      simp only [Matrix.trace, Matrix.diag, coordinatePVM, Matrix.diagonal_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : c a = j <;> simp [ha]
    _ = (fiberCompression c P j).trace := by
      change (∑ a ∈ Finset.univ.filter (fun a => c a = j), P a a) =
        ∑ a : Fiber c j, P a.val a.val
      exact Finset.sum_subtype (Finset.univ.filter (fun a => c a = j))
        (fun a => by simp) (fun a : ι => P a a)

theorem fiberCompression_rowGram (c : ι → Fin 3) (V : Matrix ι n ℂ) (j : Fin 3) :
    fiberCompression c (V * Vᴴ) j = fiberRows c V j * (fiberRows c V j)ᴴ := by
  ext a b
  rfl

private theorem fiberCompression_one_sub (c : ι → Fin 3) (P : Matrix ι ι ℂ) (j : Fin 3) :
    fiberCompression c (1 - P) j = 1 - fiberCompression c P j := by
  unfold fiberCompression
  rw [Matrix.submatrix_sub]
  change (1 : Matrix ι ι ℂ).submatrix Subtype.val Subtype.val - _ = _
  rw [Matrix.submatrix_one _ Subtype.val_injective]

theorem trace_rowEffects (c : ι → Fin 3) (V : Matrix ι n ℂ) (j : Fin 3) :
    (rowEffects c V j).trace = ((coordinatePVM c).proj j * (V * Vᴴ)).trace := by
  rw [rowEffects, Matrix.trace_mul_comm, trace_coordinate_mul, fiberCompression_rowGram]

theorem sum_rowEffects (c : ι → Fin 3) (V : Matrix ι n ℂ) :
    (∑ j, rowEffects c V j) = Vᴴ * V := by
  classical
  ext a b
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, rowEffects]
  let f (i : ι) := star (V i a) * V i b
  change (∑ j : Fin 3, ∑ i : Fiber c j, f i.val) = ∑ i : ι, f i
  rw [← Fintype.sum_sigma' (fun (j : Fin 3) (i : Fiber c j) => f i.val)]
  exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv c) _ f (fun _ => rfl)

private theorem rowGram_idempotent {V : Matrix ι n ℂ} (hV : Vᴴ * V = 1) :
    (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
  rw [Matrix.mul_assoc V Vᴴ, ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]

private theorem rank_frame {V : Matrix ι n ℂ} (hV : Vᴴ * V = 1) :
    (V * Vᴴ).rank = Fintype.card n := by
  rw [Matrix.rank_self_mul_conjTranspose, ← Matrix.rank_conjTranspose_mul_self V,
    hV, Matrix.rank_one]

theorem feasible_rowEffects (c : ι → Fin 3) (V : Matrix ι n ℂ) (hV : Vᴴ * V = 1)
    {d : ℕ} {t : Fin 3 → ℝ} (hQ : FlatAtTrace c d t (V * Vᴴ)) :
    Feasible (capacity c) t (rowEffects c V) := by
  refine ⟨fun j => Matrix.posSemidef_conjTranspose_mul_self (fiberRows c V j),
    (sum_rowEffects c V).trans hV, ?_, ?_⟩
  · intro j
    rw [trace_rowEffects]
    exact hQ.2.2.2.1 j
  · intro j
    exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_card_height (fiberRows c V j))

theorem exists_flat_frame (c : ι → Fin 3) {t : Fin 3 → ℝ}
    {A : Fin 3 → Matrix n n ℂ} (hA : Feasible (capacity c) t A) :
    ∃ V : Matrix ι n ℂ, Vᴴ * V = 1 ∧ FlatAtTrace c (Fintype.card n) t (V * Vᴴ) ∧
      rowEffects c V = A := by
  classical
  choose U hU hdiag using
    fun j => exists_flat_rows_of_rank_le (hA.1 j) (hA.2.2.2 j)
  let e (j : Fin 3) : Fiber c j ≃ Fin (capacity c j) := Fintype.equivFin (Fiber c j)
  let V : Matrix ι n ℂ := fun a b => U (c a) (e (c a) ⟨a, rfl⟩) b
  have hrows (j : Fin 3) : fiberRows c V j = (U j).submatrix (e j) id := by
    ext a b
    rcases a with ⟨a, ha⟩
    subst j
    rfl
  have hGrams : rowEffects c V = A := by
    funext j
    rw [rowEffects, hrows, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv _ _ id (e j) id, Matrix.submatrix_id_id, hU]
  have hV : Vᴴ * V = 1 := by
    rw [← sum_rowEffects c V, hGrams]
    exact hA.2.1
  refine ⟨V, hV,
    ⟨Matrix.isHermitian_mul_conjTranspose_self V, rowGram_idempotent hV, rank_frame hV, ?_, ?_⟩,
    hGrams⟩
  · intro j
    rw [← trace_rowEffects, hGrams]
    exact hA.2.2.1 j
  · intro a
    let j := c a
    let x : Fiber c j := ⟨a, rfl⟩
    have hdiag' := hdiag j (e j x)
    rw [hA.2.2.1 j] at hdiag'
    have hblock :
        fiberCompression c (V * Vᴴ) j = ((U j) * (U j)ᴴ).submatrix (e j) (e j) := by
      rw [fiberCompression_rowGram, hrows, Matrix.conjTranspose_submatrix]
      exact (Matrix.submatrix_mul _ _ (e j) id (e j) Function.bijective_id).symm
    exact (congrArg (fun M : Matrix (Fiber c j) (Fiber c j) ℂ => (M x x).re) hblock).trans
      hdiag'

theorem fiber_capacity_pos (c : ι → Fin 3) (a : ι) : 0 < capacity c (c a) :=
  Fintype.card_pos_iff.mpr ⟨⟨a, rfl⟩⟩

theorem flatAtTrace_complement {c : ι → Fin 3} {r : ℕ} {s : Fin 3 → ℝ}
    {P : Matrix ι ι ℂ} (hP : FlatAtTrace c r s P) :
    FlatAtTrace c (Fintype.card ι - r) (fun j => (capacity c j : ℝ) - s j) (1 - P) := by
  have hrN : r ≤ Fintype.card ι := hP.2.2.1 ▸ Matrix.rank_le_card_width P
  have hidem : (1 - P) * (1 - P) = 1 - P := by
    simp [Matrix.sub_mul, Matrix.mul_sub, hP.2.1]
  refine ⟨Matrix.isHermitian_one.sub hP.1, hidem, ?_, ?_, ?_⟩
  · have ht := trace_projection (1 - P) hidem
    rw [Matrix.trace_sub, Matrix.trace_one, trace_projection P hP.2.1, hP.2.2.1,
      ← Nat.cast_sub hrN] at ht
    exact_mod_cast ht.symm
  · intro j
    have ht : (fiberCompression c P j).trace.re = s j := by
      rw [← trace_coordinate_mul]
      exact hP.2.2.2.1 j
    rw [trace_coordinate_mul, fiberCompression_one_sub, Matrix.trace_sub, Matrix.trace_one,
      Complex.sub_re, Complex.natCast_re, ht]
    rfl
  · intro a
    have hm : (capacity c (c a) : ℝ) ≠ 0 := by
      exact_mod_cast (fiber_capacity_pos c a).ne'
    rw [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re,
      hP.2.2.2.2, sub_div, div_self hm]

private def stateOfFlatAtTrace {c : ι → Fin 3} {r : ℕ} {s : Fin 3 → ℝ}
    {P : Matrix ι ι ℂ} (hr : 0 < r) (hP : FlatAtTrace c r s P) : DensityState ι := by
  refine ⟨CStarMatrix.ofMatrix ((r : ℂ)⁻¹ • P), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    apply Matrix.PosSemidef.nonneg
    have hpos : P.PosSemidef := by
      simpa only [hP.1.eq, hP.2.1] using Matrix.posSemidef_conjTranspose_mul_self P
    exact hpos.smul (by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.nonneg_iff]
      exact ⟨inv_nonneg.mpr (Nat.cast_nonneg r), by simp⟩)
  · change Matrix.trace ((r : ℂ)⁻¹ • P) = 1
    rw [Matrix.trace_smul, trace_projection P hP.2.1, hP.2.2.1, smul_eq_mul,
      inv_mul_cancel₀ (by exact_mod_cast hr.ne')]

def branchRank (ι : Type*) [Fintype ι] (r : ℕ) (flip : Bool) : ℕ :=
  if flip then Fintype.card ι - r else r

def branchTrace (c : ι → Fin 3) (r : ℕ) (q : Fin 3 → ℝ) (flip : Bool) : Fin 3 → ℝ :=
  if flip then (fun j => (capacity c j : ℝ) - (r : ℝ) * q j) else (fun j => (r : ℝ) * q j)

def frameProjection (flip : Bool) (V : Matrix ι n ℂ) : Matrix ι ι ℂ :=
  if flip then 1 - V * Vᴴ else V * Vᴴ

theorem frameProjection_isProjection (flip : Bool) {V : Matrix ι n ℂ} (hV : Vᴴ * V = 1) :
    (frameProjection flip V).IsHermitian ∧
      frameProjection flip V * frameProjection flip V = frameProjection flip V := by
  have hQ := Matrix.isHermitian_mul_conjTranspose_self V
  have hQQ := rowGram_idempotent hV
  cases flip
  · exact ⟨hQ, hQQ⟩
  · refine ⟨Matrix.isHermitian_one.sub hQ, ?_⟩
    simp [frameProjection, Matrix.sub_mul, Matrix.mul_sub, hQQ]

theorem fiberCompression_frameProjection (c : ι → Fin 3)
    (flip : Bool) (V : Matrix ι n ℂ) (j : Fin 3) :
    fiberCompression c (frameProjection flip V) j =
      if flip then 1 - fiberRows c V j * (fiberRows c V j)ᴴ
      else fiberRows c V j * (fiberRows c V j)ᴴ := by
  cases flip <;> simp [frameProjection, fiberCompression_one_sub, fiberCompression_rowGram]

/-- The same frame specifies the state matrix and all three effects. -/
def StateFrame (c : ι → Fin 3) (r : ℕ) (flip : Bool) (ρ : DensityState ι)
    (V : Matrix ι (Fin (branchRank ι r flip)) ℂ) : Prop :=
  Vᴴ * V = 1 ∧ CStarMatrix.ofMatrix.symm ρ.1 = ((r : ℂ)⁻¹) • frameProjection flip V

theorem exists_frame_of_inputAtLaw {c : ι → Fin 3} {r : ℕ} {q : Fin 3 → ℝ}
    {ρ : DensityState ι} (hρ : InputAtLaw c r q ρ) (flip : Bool) :
    ∃ V : Matrix ι (Fin (branchRank ι r flip)) ℂ,
      StateFrame c r flip ρ V ∧
      Feasible (capacity c) (branchTrace c r q flip) (rowEffects c V) := by
  obtain ⟨P, hP, hρP⟩ := hρ
  let Q : Matrix ι ι ℂ := if flip then 1 - P else P
  have hQ : FlatAtTrace c (branchRank ι r flip) (branchTrace c r q flip) Q := by
    cases flip
    · simpa [Q, branchRank, branchTrace] using hP
    · simpa [Q, branchRank, branchTrace] using flatAtTrace_complement hP
  obtain ⟨V, hV, hVQ⟩ := exists_projection_frame hQ.1 hQ.2.1 hQ.2.2.1
  have hPV : frameProjection flip V = P := by
    cases flip <;> simp [frameProjection, hVQ, Q, sub_sub_cancel]
  have hVFlat : FlatAtTrace c (branchRank ι r flip) (branchTrace c r q flip) (V * Vᴴ) := by
    simpa only [hVQ] using hQ
  refine ⟨V, ⟨hV, ?_⟩, feasible_rowEffects c V hV hVFlat⟩
  simpa only [hPV] using hρP

theorem exists_inputAtLaw_of_feasible {c : ι → Fin 3} {r : ℕ} {q : Fin 3 → ℝ}
    (hr : 0 < r) (hrN : r ≤ Fintype.card ι) {flip : Bool}
    {A : Fin 3 → Matrix (Fin (branchRank ι r flip)) (Fin (branchRank ι r flip)) ℂ}
    (hA : Feasible (capacity c) (branchTrace c r q flip) A) :
    ∃ (ρ : DensityState ι) (V : Matrix ι (Fin (branchRank ι r flip)) ℂ),
      InputAtLaw c r q ρ ∧ StateFrame c r flip ρ V ∧ rowEffects c V = A := by
  obtain ⟨V, hV, hFlat, hEffects⟩ := exists_flat_frame c hA
  have hQ : FlatAtTrace c (branchRank ι r flip) (branchTrace c r q flip) (V * Vᴴ) := by
    simpa only [Fintype.card_fin] using hFlat
  have hP : FlatAtTrace c r (fun j => (r : ℝ) * q j) (frameProjection flip V) := by
    cases flip
    · simpa [frameProjection, branchRank, branchTrace] using hQ
    · simpa [frameProjection, branchRank, branchTrace, Nat.sub_sub_self hrN, sub_sub_cancel]
        using flatAtTrace_complement hQ
  let ρ := stateOfFlatAtTrace hr hP
  have hρ : CStarMatrix.ofMatrix.symm ρ.1 = ((r : ℂ)⁻¹) • frameProjection flip V := rfl
  exact ⟨ρ, V, ⟨frameProjection flip V, hP, hρ⟩, ⟨hV, hρ⟩, hEffects⟩

theorem exists_inputAtLaw_iff_exists_feasible {c : ι → Fin 3} {r : ℕ} {q : Fin 3 → ℝ}
    (hr : 0 < r) (hrN : r ≤ Fintype.card ι) (flip : Bool) :
    (∃ ρ : DensityState ι, InputAtLaw c r q ρ) ↔
      ∃ A : Fin 3 → Matrix (Fin (branchRank ι r flip)) (Fin (branchRank ι r flip)) ℂ,
        Feasible (capacity c) (branchTrace c r q flip) A := by
  constructor
  · rintro ⟨ρ, hρ⟩
    obtain ⟨V, _, hV⟩ := exists_frame_of_inputAtLaw hρ flip
    exact ⟨rowEffects c V, hV⟩
  · rintro ⟨A, hA⟩
    obtain ⟨ρ, _, hρ, _, _⟩ := exists_inputAtLaw_of_feasible hr hrN hA
    exact ⟨ρ, hρ⟩

/-- Range equality reduces to the pointwise entropy calculation on the shared frame. -/
theorem geometryStatement_of_frame_gain (c : ι → Fin 3) (r : ℕ) (q : Fin 3 → ℝ)
    (hGain : 0 < r → ∀ (flip : Bool) (ρ : DensityState ι)
      (V : Matrix ι (Fin (branchRank ι r flip)) ℂ),
      StateFrame c r flip ρ V →
      ∀ hp : ∀ j, (rowEffects c V j).PosSemidef,
        gain c ρ = spectralSum (entropyIntegrand flip) (rowEffects c V) hp / (r : ℝ)) :
    GeometryStatement c r q := by
  intro hr hrN flip
  have ht : branchTrace c r q flip =
      (fun j => if flip then (capacity c j : ℝ) - (r : ℝ) * q j else (r : ℝ) * q j) := by
    cases flip <;> rfl
  change gainValues c r q =
    (fun x : ℝ => x / r) '' effectValues flip (branchRank ι r flip) (capacity c)
      (fun j => if flip then (capacity c j : ℝ) - (r : ℝ) * q j else (r : ℝ) * q j)
  rw [← ht]
  ext x
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    obtain ⟨V, hFrame, hA⟩ := exists_frame_of_inputAtLaw hρ flip
    exact ⟨_, ⟨rowEffects c V, hA, rfl⟩, (hGain hr flip ρ V hFrame hA.1).symm⟩
  · rintro ⟨y, ⟨A, hA, hy⟩, rfl⟩
    obtain ⟨ρ, V, hρ, hFrame, hEffects⟩ := exists_inputAtLaw_of_feasible hr hrN hA
    subst A
    exact ⟨ρ, hρ, (hGain hr flip ρ V hFrame hA.1).trans
      (congrArg (fun z : ℝ => z / (r : ℝ)) hy)⟩

end

end D5.S3.Quantum.Measurement.Auric.GeometryFrames
