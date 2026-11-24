/- GID: D5/S3/Quantum/Measurement/Auric/EqualBlockProjection
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/EqualBlockProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact attained entropy gain for three equal coordinate blocks of a flat-rank state. -/

import D5.S3.Quantum.Measurement.Auric.EqualBlockEffects
import D5.S3.Quantum.Measurement.Auric.ProjectionFrames
import D5.S3.Quantum.Measurement.Auric.CoordinatePinching
import D5.S3.Quantum.Information.OrthogonalRecordEntropy
import D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
import D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity

/-! The attained entropy gain for three equal coordinate blocks of a flat-rank state. -/

namespace D5.S3.Quantum.Measurement.Auric.EqualBlockProjection

open _root_.Matrix
open EqualBlockEffects
open _root_.D5.S3.Quantum.Measurement.Auric.CoordinatePinching
open _root_.D5.S3.Quantum.Measurement.Auric.ProjectionFrames
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Divergence.VonNeumannEntropyPinching (vonNeumannEntropy)
open _root_.D5.S3.Observer.Conditioning (unreadState)
open scoped Matrix BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity (fourierRows fourierRows_gram)

noncomputable section

local instance {n : Type*} [Fintype n] [DecidableEq n] :
    ContinuousFunctionalCalculus ℝ (CStarMatrix n n ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
variable {m : ℕ}

private def blockRows (E : (Fin m × Fin 3) ≃ ι) (V : Matrix ι n ℂ) (j : Fin 3) :
    Matrix (Fin m) n ℂ :=
  V.submatrix (fun a => E (a, j)) id

private theorem sum_blockGrams (E : (Fin m × Fin 3) ≃ ι) (V : Matrix ι n ℂ) :
    (∑ j, (blockRows E V j)ᴴ * blockRows E V j) = Vᴴ * V := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    blockRows, Matrix.submatrix_apply, id_eq]
  let f (i : ι) := star (V i a) * V i b
  change (∑ j : Fin 3, ∑ i : Fin m, f (E (i, j))) = ∑ i : ι, f i
  rw [Finset.sum_comm, ← Fintype.sum_prod_type (fun x : Fin m × Fin 3 => f (E x))]
  exact Fintype.sum_equiv E _ f (fun _ => rfl)

private theorem blockGrams_feasible (E : (Fin m × Fin 3) ≃ ι) (V : Matrix ι n ℂ)
    (hm : 0 < m) (hv : Vᴴ * V = 1)
    (hdiag : ∀ i, ((V * Vᴴ) i i).re = (Fintype.card n : ℝ) / (3 * m)) :
    Feasible m (fun j => (blockRows E V j)ᴴ * blockRows E V j) := by
  refine ⟨fun _ => Matrix.posSemidef_conjTranspose_mul_self _, (sum_blockGrams E V).trans hv,
    ?_, fun j => ?_⟩
  · intro j
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    have hrow (a : Fin m) :
        ((blockRows E V j * (blockRows E V j)ᴴ) a a).re =
          (Fintype.card n : ℝ) / (3 * m) := by
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, blockRows] using hdiag (E (a, j))
    simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hmr : (m : ℝ) ≠ 0 := by positivity
    field_simp
  · apply (Matrix.rank_mul_le_right _ _).trans
    simpa using Matrix.rank_le_card_height (blockRows E V j)

private theorem exists_flat_rows {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (hm : 0 < m) (hr : A.rank ≤ m) :
    ∃ V : Matrix (Fin m) n ℂ, Vᴴ * V = A ∧
      ∀ i, ((V * Vᴴ) i i).re = (Matrix.trace A).re / m := by
  classical
  letI : NeZero m := ⟨hm.ne'⟩
  let e := hA.isHermitian.eigenvalues
  let S := {i : n // e i ≠ 0}
  have hs : Fintype.card S ≤ m := by
    rw [← hA.isHermitian.rank_eq_card_non_zero_eigs]
    exact hr
  let emb : S ↪ Fin m := (Fintype.equivFin S).toEmbedding.trans (Fin.castLEEmb hs)
  let F := fourierRows m m le_rfl
  let D : Matrix (Fin m) n ℂ := fun i j =>
    if hj : e j ≠ 0 then ((Real.sqrt (e j) : ℝ) : ℂ) * F i (emb ⟨j, hj⟩) else 0
  let s : ℝ := (Real.sqrt (m : ℝ))⁻¹
  let W : Matrix (Fin m) n ℂ := (s : ℂ) • D
  let U : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let V := W * Uᴴ
  have hN : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hFt : F * Fᴴ = (m : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) :=
    fourierRows_gram m m le_rfl
  have hFN : (m : ℂ)⁻¹ • Fᴴ * F = 1 := by
    apply mul_eq_one_comm.mp
    rw [Matrix.mul_smul, hFt, smul_smul, inv_mul_cancel₀ hN, one_smul]
  have hF : Fᴴ * F = (m : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    calc
      Fᴴ * F = (m : ℂ) • ((m : ℂ)⁻¹ • (Fᴴ * F)) := by
        rw [smul_smul, mul_inv_cancel₀ hN, one_smul]
      _ = _ := by rw [← Matrix.smul_mul, hFN]
  have hscale : (s : ℂ) * (s : ℂ) * (m : ℂ) = 1 := by
    have hmr : (0 : ℝ) < m := by exact_mod_cast hm
    have hsqrt : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hmr)
    have hreal : s * s * (m : ℝ) = 1 := by
      dsimp [s]
      field_simp
      nlinarith only [Real.sq_sqrt hmr.le]
    exact_mod_cast hreal
  have hcol (i j : n) (hi : e i ≠ 0) (hj : e j ≠ 0) :
      (Dᴴ * D) i j =
        ((Real.sqrt (e i) : ℝ) : ℂ) * ((Real.sqrt (e j) : ℝ) : ℂ) *
          (Fᴴ * F) (emb ⟨i, hi⟩) (emb ⟨j, hj⟩) := by
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Matrix.conjTranspose_apply]
    change star (D k i) * D k j = _
    simp only [D, dite_eq_left hi, dite_eq_left hj, star_mul, Complex.star_def,
      Complex.conj_ofReal]
    ring
  have hW : Wᴴ * W = diagonal fun i => ((e i : ℝ) : ℂ) := by
    ext i j
    simp only [W, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul,
      Complex.star_def, Complex.conj_ofReal, smul_eq_mul, Matrix.smul_apply]
    by_cases hi : e i = 0
    · have hz : (Dᴴ * D) i j = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro k _
        change star (D k i) * D k j = 0
        simp [D, hi]
      by_cases hij : i = j
      · subst j
        simp [hz, hi]
      · simp [hz, Matrix.diagonal_apply_ne _ hij]
    by_cases hj : e j = 0
    · by_cases hij : i = j
      · subst j
        exact (hi hj).elim
      · have hz : (Dᴴ * D) i j = 0 := by
          rw [Matrix.mul_apply]
          apply Finset.sum_eq_zero
          intro k _
          change star (D k i) * D k j = 0
          simp [D, hj]
        simp [hz, Matrix.diagonal_apply_ne _ hij]
    rw [hcol i j hi hj, hF]
    by_cases hij : i = j
    · subst j
      have hsqrt : ((Real.sqrt (e i) : ℝ) : ℂ) * ((Real.sqrt (e i) : ℝ) : ℂ) = (e i : ℂ) := by
        exact_mod_cast (Real.mul_self_sqrt (hA.eigenvalues_nonneg i))
      simp only [hsqrt, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        Matrix.diagonal_apply_eq]
      linear_combination (e i : ℂ) * hscale
    · have he : emb ⟨i, hi⟩ ≠ emb ⟨j, hj⟩ :=
        fun h => hij (congrArg Subtype.val (emb.injective h))
      simp [Matrix.diagonal_apply, Matrix.one_apply, he, hij]
  have hu : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hA.isHermitian.eigenvectorUnitary.prop
  have hV : Vᴴ * V = A := by
    dsimp only [V]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Wᴴ W, hW, ← Matrix.mul_assoc]
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal, U, e] using hA.isHermitian.spectral_theorem.symm
  have hVW : V * Vᴴ = W * Wᴴ := by
    simp only [V, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hu, Matrix.one_mul]
  refine ⟨V, hV, fun i => ?_⟩
  rw [hVW]
  have hreal : s * s = (m : ℝ)⁻¹ := by
    have h := congrArg Complex.re hscale
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_natCast, Complex.ofReal_re,
      Complex.one_re] at h
    rw [inv_eq_one_div]
    exact (eq_div_iff (show (m : ℝ) ≠ 0 by positivity)).2 h
  have hn (i j : Fin m) : ‖F i j‖ = 1 := by simp [F, fourierRows, AddChar.norm_apply]
  have hterm (j : n) : (W i j * star (W i j)).re = e j / (m : ℝ) := by
    rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
    change ‖(s : ℂ) * D i j‖ ^ 2 = _
    by_cases hj : e j = 0
    · simp [D, hj]
    · simp only [D, dite_eq_left hj, norm_mul, Complex.norm_real, Real.norm_eq_abs, hn, mul_one]
      rw [abs_of_nonneg (show 0 ≤ s by positivity), abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [mul_pow, Real.sq_sqrt (hA.eigenvalues_nonneg j), pow_two, hreal, div_eq_mul_inv, mul_comm]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, hterm]
  rw [← Finset.sum_div, hA.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
  rfl

private def coordinateBlocks (c : ι → Fin 3)
    (hc : ∀ j, Fintype.card {i // c i = j} = m) : (Fin m × Fin 3) ≃ ι :=
  (Equiv.prodComm _ _).trans <|
    (Equiv.sigmaEquivProd (Fin 3) (Fin m)).symm.trans <|
      (Equiv.sigmaCongrRight fun j => Fintype.equivOfCardEq ((Fintype.card_fin m).trans (hc j).symm)).trans
        (Equiv.sigmaFiberEquiv c)

private theorem coordinateBlocks_apply (c : ι → Fin 3)
    (hc : ∀ j, Fintype.card {i // c i = j} = m) (a : Fin m × Fin 3) :
    c (coordinateBlocks c hc a) = a.2 := by
  exact ((Fintype.equivOfCardEq ((Fintype.card_fin m).trans (hc a.2).symm)) a.1 :
    {i // c i = a.2}).prop

private theorem capacity_card (c : ι → Fin 3)
    (hc : ∀ j, Fintype.card {i // c i = j} = m) : Fintype.card ι = 3 * m := by
  simpa [Nat.mul_comm] using (Fintype.card_congr (coordinateBlocks c hc)).symm

private theorem trace_projection (P : Matrix ι ι ℂ) (hP : P * P = P) :
    Matrix.trace P = (P.rank : ℂ) := by
  have hidem : IsIdempotentElem P.mulVecLin := by
    change P.mulVecLin.comp P.mulVecLin = P.mulVecLin
    rw [← Matrix.mulVecLin_mul, hP]
  have ht := (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ ι)] at ht
  change (LinearMap.toMatrix' (Matrix.toLin' P)).trace = (P.rank : ℂ) at ht
  rwa [LinearMap.toMatrix'_toLin'] at ht

def FlatProjection (r : ℕ) (P : Matrix ι ι ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P ∧ P.rank = r ∧
    ∀ i, P i i = (r : ℂ) / Fintype.card ι

private theorem FlatProjection.complement {r : ℕ} {P : Matrix ι ι ℂ} (h : FlatProjection r P)
    (hc : 0 < Fintype.card ι) :
    FlatProjection (Fintype.card ι - r) (1 - P) := by
  have hr : r ≤ Fintype.card ι := h.2.2.1 ▸ Matrix.rank_le_card_width P
  have hi : (1 - P) * (1 - P) = 1 - P := by
    simp [Matrix.sub_mul, Matrix.mul_sub, h.2.1]
  have hc0 : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨Matrix.isHermitian_one.sub h.1, hi, ?_, ?_⟩
  · have hh := trace_projection (1 - P) hi
    rw [Matrix.trace_sub, Matrix.trace_one, trace_projection _ h.2.1, h.2.2.1,
      ← Nat.cast_sub hr] at hh
    exact_mod_cast hh.symm
  · intro i
    rw [Matrix.sub_apply, Matrix.one_apply_eq, h.2.2.2 i, Nat.cast_sub hr, sub_div,
      div_self hc0]

private theorem FlatProjection.posSemidef {r : ℕ} {P : Matrix ι ι ℂ}
    (h : FlatProjection r P) : P.PosSemidef := by
  simpa only [h.1.eq, h.2.1] using Matrix.posSemidef_conjTranspose_mul_self P

def flatState {r : ℕ} {P : Matrix ι ι ℂ} (hr : 0 < r) (h : FlatProjection r P) :
    DensityState ι := by
  refine ⟨CStarMatrix.ofMatrix ((r : ℂ)⁻¹ • P), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    apply Matrix.PosSemidef.nonneg
    exact h.posSemidef.smul (by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.nonneg_iff]
      exact ⟨inv_nonneg.mpr (Nat.cast_nonneg r), by simp⟩)
  · change Matrix.trace ((r : ℂ)⁻¹ • P) = 1
    rw [trace_smul, trace_projection P h.2.1, h.2.2.1, smul_eq_mul,
      inv_mul_cancel₀ (by exact_mod_cast hr.ne')]

private theorem exists_flat_frame (c : ι → Fin 3) (hc : ∀ j, Fintype.card {i // c i = j} = m)
    (hm : 0 < m) {A : Fin 3 → Matrix n n ℂ} (hA : Feasible m A) :
    ∃ V : Matrix ι n ℂ, Vᴴ * V = 1 ∧
      FlatProjection (Fintype.card n) (V * Vᴴ) ∧
      ∀ j, (blockRows (coordinateBlocks c hc) V j)ᴴ * blockRows (coordinateBlocks c hc) V j = A j := by
  choose W hW hrow using fun j => exists_flat_rows (hA.1 j) hm (hA.2.2.2 j)
  let E := coordinateBlocks c hc
  let V : Matrix ι n ℂ := fun i a => W (E.symm i).2 (E.symm i).1 a
  have hrows (j : Fin 3) : blockRows E V j = W j := by
    ext i a
    change W (E.symm (E (i, j))).2 (E.symm (E (i, j))).1 a = _
    rw [Equiv.symm_apply_apply]
  have hv : Vᴴ * V = 1 := by
    rw [← sum_blockGrams E V]
    simp_rw [hrows, hW]
    exact hA.2.1
  refine ⟨V, hv, ⟨Matrix.isHermitian_mul_conjTranspose_self V, ?_, ?_, ?_⟩,
    fun j => by rw [hrows, hW]⟩
  · rw [Matrix.mul_assoc V Vᴴ, ← Matrix.mul_assoc Vᴴ V, hv, Matrix.one_mul]
  · rw [Matrix.rank_self_mul_conjTranspose, ← Matrix.rank_conjTranspose_mul_self V,
      hv, Matrix.rank_one]
  · intro i
    obtain ⟨⟨a,j⟩, rfl⟩ := E.surjective i
    have hr := hrow j a
    rw [hA.2.2.1] at hr
    have hentry (x : n) : V (E (a, j)) x = W j a x := by
      change W (E.symm (E (a, j))).2 (E.symm (E (a, j))).1 x = _
      rw [Equiv.symm_apply_apply]
    have hre : ((V * Vᴴ) (E (a,j)) (E (a,j))).re =
        ((W j * (W j)ᴴ) a a).re := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hentry]
    have hi := congrFun (Matrix.isHermitian_mul_conjTranspose_self V).coe_re_diag (E (a,j))
    change ((↑(((V * Vᴴ) (E (a,j)) (E (a,j))).re) : ℂ)) =
      (V * Vᴴ) (E (a,j)) (E (a,j)) at hi
    rw [← hi, hre, hr, capacity_card c hc, div_div]
    norm_num [Complex.ofReal_div, Complex.ofReal_natCast, Nat.cast_mul]

private theorem coordinate_pinching_blocks (c : ι → Fin 3)
    (hc : ∀ j, Fintype.card {i // c i = j} = m)
    (X : Matrix ι ι ℂ) :
    Matrix.reindex (coordinateBlocks c hc).symm (coordinateBlocks c hc).symm
      (unreadState (coordinatePVM c).proj X) =
      Matrix.blockDiagonal (fun j => X.submatrix (fun a => coordinateBlocks c hc (a,j))
        (fun a => coordinateBlocks c hc (a,j))) := by
  ext x y
  rcases x with ⟨a,j⟩
  rcases y with ⟨b,k⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    Matrix.blockDiagonal_apply, unreadState, Matrix.sum_apply]
  change (∑ z : Fin 3,
    (diagonal (fun i => if c i = z then (1 : ℂ) else 0) * X *
      diagonal (fun i => if c i = z then (1 : ℂ) else 0))
      (coordinateBlocks c hc (a,j)) (coordinateBlocks c hc (b,k))) = _
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, coordinateBlocks_apply]
  by_cases h : j = k
  · subst k
    simp only [if_pos rfl]
    classical
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun z : Fin 3 => j = z)]
    simp [Finset.filter_eq', mul_ite, ite_mul]
  · simp only [if_neg h]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hz : j = z
    · have hk : k ≠ z := fun hk => h (hz.trans hk.symm)
      simp [hz, hk]
    · simp [hz]

private def spectralSum (f : ℝ → ℝ) {X : Matrix n n ℂ} (hX : X.IsHermitian) : ℝ :=
  ∑ i, f (hX.eigenvalues i)

private theorem spectralSum_roots (f : ℝ → ℝ) {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    spectralSum f hX = (X.charpoly.roots.map (f ∘ Complex.re)).sum := by
  rw [hX.roots_charpoly_eq_eigenvalues]
  simp [spectralSum, Multiset.map_map, Function.comp_def, RCLike.ofReal_eq_complex_ofReal]

private theorem spectralSum_reindex (e : n ≃ ι) (f : ℝ → ℝ) {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (hE : (Matrix.reindex e e X).IsHermitian) :
    spectralSum f hE = spectralSum f hX := by
  rw [spectralSum_roots _ hE, spectralSum_roots _ hX, Matrix.charpoly_reindex]

private theorem spectralSum_blocks (f : ℝ → ℝ) (A : Fin 3 → Matrix n n ℂ)
    (hA : ∀ j, (A j).IsHermitian) (h : (Matrix.blockDiagonal A).IsHermitian) :
    spectralSum f h = ∑ j, spectralSum f (hA j) := by
  have hc : (Matrix.blockDiagonal A).charpoly = ∏ j, (A j).charpoly := by
    simp only [Matrix.charpoly]
    rw [← Matrix.det_blockDiagonal]
    congr 1
    ext ⟨i,j⟩ ⟨k,l⟩
    by_cases h' : j = l
    · subst l
      simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Matrix.blockDiagonal_apply]
    · simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Matrix.blockDiagonal_apply, h']
  simp_rw [spectralSum_roots]
  rw [hc, Polynomial.roots_prod]
  · simp [Multiset.sum_bind, Multiset.map_bind, Finset.sum_eq_multiset_sum]
  · exact Finset.prod_ne_zero_iff.mpr fun j _ => (Matrix.charpoly_monic (A j)).ne_zero

private theorem spectralSum_gram (V : Matrix ι n ℂ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    spectralSum f (Matrix.isHermitian_mul_conjTranspose_self V) =
      spectralSum f (Matrix.isHermitian_conjTranspose_mul_self V) := by
  rw [spectralSum_roots, spectralSum_roots]
  have h := congrArg Polynomial.roots (Matrix.charpoly_mul_comm' V Vᴴ)
  rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
    (Matrix.charpoly_monic _).ne_zero),
    Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic _).ne_zero), Polynomial.roots_X_pow, Polynomial.roots_X_pow] at h
  simpa [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul,
    Multiset.sum_nsmul, Function.comp_def, hf] using
    congrArg (fun t : Multiset ℂ => (t.map (f ∘ Complex.re)).sum) h

private theorem spectralSum_affine (f : ℝ → ℝ) {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (a b : ℝ) (hY : ((a : ℂ) • (1 : Matrix n n ℂ) + (b : ℂ) • X).IsHermitian) :
    spectralSum f hY = spectralSum (fun x => f (a + b*x)) hX := by
  let evals := hX.eigenvalues
  let T := Unitary.conjStarAlgAut ℂ _ hX.eigenvectorUnitary
  let D := diagonal fun i => ((a + b * evals i : ℝ) : ℂ)
  have hd : (a : ℂ) • (1 : Matrix n n ℂ) + (b : ℂ) • X = T D := by
    have hD : D = (a : ℂ) • (1 : Matrix n n ℂ) +
        (b : ℂ) • diagonal (RCLike.ofReal ∘ evals) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [D, Complex.ofReal_add, Complex.ofReal_mul, Function.comp_def,
          RCLike.ofReal_eq_complex_ofReal]
      · simp [D, Matrix.one_apply, hij]
    rw [hD, map_add, map_smul, map_smul, map_one]
    exact congrArg (fun Y => (a : ℂ) • 1 + (b : ℂ) • Y) hX.spectral_theorem
  have hc : ((a : ℂ) • (1 : Matrix n n ℂ) + (b : ℂ) • X).charpoly = D.charpoly := by
    rw [hd, show T D = _ from Unitary.conjStarAlgAut_apply _ _,
      Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]
  rw [spectralSum_roots, hc]
  unfold D spectralSum
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map,
      Function.comp_def, Complex.ofReal_re, Finset.sum_eq_multiset_sum, evals]
  · exact Finset.prod_ne_zero_iff.mpr fun _ _ => Polynomial.X_sub_C_ne_zero _

private theorem entropy_spectral (ρ : DensityState n) :
    vonNeumannEntropy ρ =
      spectralSum Real.negMulLog
        (Matrix.nonneg_iff_posSemidef.mp (show 0 ≤ CStarMatrix.ofMatrix.symm ρ.1 from
          map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.nonnegative)).isHermitian := by
  let A := CStarMatrix.ofMatrix.symm ρ.1
  have hA : A.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (show 0 ≤ CStarMatrix.ofMatrix.symm ρ.1 from
          map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.nonnegative)).isHermitian
  have hmap : CStarMatrix.ofMatrix (cfc Real.negMulLog A) =
      cfc Real.negMulLog (CStarMatrix.ofMatrix A) :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.negMulLog A
      (A.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous
      hA.isSelfAdjoint hA.isSelfAdjoint
  have hent :=
    _root_.D5.S3.Quantum.Information.OrthogonalRecordEntropy.entropy_eq_trace_cfc
      (show _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState n
        from ρ)
  change vonNeumannEntropy ρ =
    (Matrix.trace (CStarMatrix.ofMatrix.symm (cfc Real.negMulLog (CStarMatrix.ofMatrix A)))).re
    at hent
  rw [hent]
  rw [← hmap]
  change (Matrix.trace (cfc Real.negMulLog A)).re = _
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Matrix.trace_map, Matrix.trace_diagonal, Complex.re_sum]
  rfl

private theorem spectralSum_scale_entropy {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (q : ℝ) (hY : ((q : ℂ) • X).IsHermitian) :
    spectralSum Real.negMulLog hY =
      q * spectralSum Real.negMulLog hX + (Matrix.trace X).re * Real.negMulLog q := by
  have h := spectralSum_affine Real.negMulLog hX 0 q
    (show ((0 : ℂ) • 1 + (q : ℂ) • X).IsHermitian by simpa using hY)
  simp only [Complex.ofReal_zero, zero_smul, zero_add] at h
  rw [h]
  have hf (x : ℝ) : Real.negMulLog (q * x) = q * Real.negMulLog x + x * Real.negMulLog q := by
    rw [Real.negMulLog_mul]
    ring
  simp only [spectralSum, hf, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hX.trace_eq_sum_eigenvalues, Complex.re_sum]
  rfl

private theorem entropy_flat_projection {P : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (hP2 : P*P=P) : spectralSum Real.negMulLog hP = 0 := by
  unfold spectralSum
  apply Finset.sum_eq_zero
  intro j _
  let D := diagonal fun i => ((hP.eigenvalues i : ℝ) : ℂ)
  let T := Unitary.conjStarAlgAut ℂ _ (star hP.eigenvectorUnitary)
  have hd : T P = D := hP.conjStarAlgAut_star_eigenvectorUnitary
  have hi : D * D = D := by rw [← hd, ← map_mul, hP2]
  have hz : hP.eigenvalues j * hP.eigenvalues j = hP.eigenvalues j := by
    simpa [D, Matrix.diagonal_mul_diagonal, Complex.mul_re] using
      congrArg (fun X : Matrix ι ι ℂ => (X j j).re) hi
  have h := mul_eq_zero.mp (show hP.eigenvalues j * (hP.eigenvalues j - 1) = 0 by
    rw [mul_sub, mul_one, hz, sub_self])
  rcases h with he | he
  · simp [he]
  · simp [sub_eq_zero.mp he]

private theorem exists_projection_frame {d : ℕ} {Q : Matrix ι ι ℂ}
    (hQ : FlatProjection d Q) (hd : d < Fintype.card ι) :
    ∃ V : Matrix ι (Fin d) ℂ, Vᴴ * V = 1 ∧ V * Vᴴ = Q := by
  by_cases hz : Q = 0
  · have hzero : d = 0 := by simpa [hz] using hQ.2.2.1.symm
    subst d
    exact ⟨0, by ext i; exact Fin.elim0 i, by simp [hz]⟩
  have hone : Q ≠ 1 := by
    intro h
    have hh := hQ.2.2.1
    rw [h, Matrix.rank_one] at hh
    omega
  obtain ⟨k, l, _, _, _, V, _, hV, _, hVQ, _⟩ :=
    exists_complementary_frames Q hQ.1 hQ.2.1 hz hone
  have hr : Q.rank = k := by
    rw [← hVQ, Matrix.rank_self_mul_conjTranspose, ← Matrix.rank_conjTranspose_mul_self V,
      hV, Matrix.rank_one, Fintype.card_fin]
  have hdk : d = k := hQ.2.2.1.symm.trans hr
  exact hdk.symm ▸ ⟨V, hV, hVQ⟩

def gain (c : ι → Fin 3) (ρ : DensityState ι) : ℝ :=
  vonNeumannEntropy ((pinchingChannel (coordinatePVM c)).mapState ρ) - vonNeumannEntropy ρ

private theorem gain_eq_rowEffects (c : ι → Fin 3)
    (hc : ∀ j, Fintype.card {i // c i = j} = m) (flip : Bool)
    {r : ℕ} (hr : 0 < r) (V : Matrix ι n ℂ)
    (hP : FlatProjection r (if flip then 1 - V*Vᴴ else V*Vᴴ)) :
    gain c (flatState hr hP) =
      effectEntropy flip
        (fun j => (blockRows (coordinateBlocks c hc) V j)ᴴ *
          blockRows (coordinateBlocks c hc) V j)
        (fun j => Matrix.posSemidef_conjTranspose_mul_self _) / r := by
  let Q := V * Vᴴ
  let P := if flip then 1 - Q else Q
  let E := coordinateBlocks c hc
  let U := unreadState (coordinatePVM c).proj P
  let q : ℝ := (r : ℝ)⁻¹
  let Ψ := pinchingChannel (coordinatePVM c)
  let ρ := flatState hr hP
  have hρ : CStarMatrix.ofMatrix.symm ρ.1 = (q : ℂ) • P := by
    simp [ρ, flatState, q, P, Q]
  have hΨ : CStarMatrix.ofMatrix.symm (Ψ.mapState ρ).1 = (q : ℂ) • U := by
    change CStarMatrix.ofMatrix.symm (Ψ.toCompletelyPositiveMap ρ.1) = _
    rw [← CStarMatrix.ofMatrix.apply_symm_apply ρ.1, hρ, pinchingChannel_apply]
    simp only [unreadState, U, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  have hU : U.IsHermitian := by
    have hp : U.PosSemidef := by
      unfold U unreadState
      apply Matrix.posSemidef_sum
      intro j _
      have hJ := (coordinatePVM c).hermitian j
      simpa only [hJ.eq] using hP.posSemidef.mul_mul_conjTranspose_same ((coordinatePVM c).proj j)
    exact hp.isHermitian
  have htr : Matrix.trace U = Matrix.trace P := by
    have he := Ψ.trace_preserving ρ.1
    change Matrix.trace (CStarMatrix.ofMatrix.symm (Ψ.mapState ρ).1) =
      Matrix.trace (CStarMatrix.ofMatrix.symm ρ.1) at he
    rw [hΨ, hρ, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul] at he
    apply mul_left_cancel₀ _ he
    simp [q, hr.ne']
  have hspec (M N : Matrix ι ι ℂ) (h : M = N) (hM : M.IsHermitian) (hN : N.IsHermitian) :
      spectralSum Real.negMulLog hM = spectralSum Real.negMulLog hN := by
    subst N
    rfl
  have hqP : ((q : ℂ) • P).IsHermitian := hρ ▸
    (Matrix.nonneg_iff_posSemidef.mp (show 0 ≤ CStarMatrix.ofMatrix.symm ρ.1 from
          map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.nonnegative)).isHermitian
  have hqU : ((q : ℂ) • U).IsHermitian := hΨ ▸
    (Matrix.nonneg_iff_posSemidef.mp (show 0 ≤ CStarMatrix.ofMatrix.symm (Ψ.mapState ρ).1 from
          map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (Ψ.mapState ρ).nonnegative)).isHermitian
  change vonNeumannEntropy (Ψ.mapState ρ) - vonNeumannEntropy ρ = _
  rw [entropy_spectral, entropy_spectral, hspec _ _ hΨ _ hqU, hspec _ _ hρ _ hqP,
    spectralSum_scale_entropy hU, spectralSum_scale_entropy hP.1, htr,
    entropy_flat_projection hP.1 hP.2.1]
  change q * spectralSum Real.negMulLog hU + P.trace.re * Real.negMulLog q -
    (q * 0 + P.trace.re * Real.negMulLog q) = _
  simp only [mul_zero, zero_add, add_sub_cancel_right]
  let B (j : Fin 3) := P.submatrix (fun a => E (a,j)) (fun a => E (a,j))
  have hB (j : Fin 3) : (B j).IsHermitian := hP.1.submatrix _
  have hBD : (Matrix.blockDiagonal B).IsHermitian := Matrix.isHermitian_blockDiagonal_iff.mpr hB
  have hXE := coordinate_pinching_blocks c hc P
  have hE : (Matrix.reindex E.symm E.symm U).IsHermitian := hXE.symm ▸ hBD
  have hSp : spectralSum Real.negMulLog hU = ∑ j, spectralSum Real.negMulLog (hB j) := by
    rw [← spectralSum_reindex E.symm _ hU hE, spectralSum_roots, hXE,
      ← spectralSum_roots _ hBD, spectralSum_blocks _ _ hB hBD]
  rw [hSp, div_eq_mul_inv, mul_comm _ q]
  unfold effectEntropy
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  let W := blockRows E V j
  have hWW : Q.submatrix (fun a => E (a,j)) (fun a => E (a,j)) = W * Wᴴ := by
    ext a b
    simp [Q, W, blockRows, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hz : entropyIntegrand flip 0 = 0 := by cases flip <;> simp [entropyIntegrand]
  have hBj : B j = if flip then 1 - W*Wᴴ else W*Wᴴ := by
    cases flip
    · exact hWW
    · ext a b
      simp [B, P, Matrix.one_apply, E.injective.eq_iff, ← hWW]
  have haff : spectralSum Real.negMulLog (hB j) =
      spectralSum (entropyIntegrand flip) (Matrix.isHermitian_mul_conjTranspose_self W) := by
    cases flip
    · rw [spectralSum_roots, hBj]
      exact (spectralSum_roots _ _).symm
    · change B j = 1 - W * Wᴴ at hBj
      have hsub : (1 - W * Wᴴ).IsHermitian := hBj ▸ hB j
      have heq : ((1 : ℝ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) +
          ((-1 : ℝ) : ℂ) • (W * Wᴴ) = 1 - W * Wᴴ := by
        simp [sub_eq_add_neg]
      have hh := spectralSum_affine Real.negMulLog
        (Matrix.isHermitian_mul_conjTranspose_self W) 1 (-1)
        (heq.symm ▸ hsub)
      rw [spectralSum_roots, heq, ← spectralSum_roots _ hsub] at hh
      rw [spectralSum_roots _ (hB j), hBj, ← spectralSum_roots _ hsub]
      simp only [neg_one_mul, ← sub_eq_add_neg] at hh
      exact hh
  rw [haff, spectralSum_gram W _ hz]
  rfl

private theorem flatState_congr {r : ℕ} (hr : 0 < r) {P Q : Matrix ι ι ℂ}
    (hP : FlatProjection r P) (hQ : FlatProjection r Q) (h : P = Q) :
    flatState hr hP = flatState hr hQ := by
  subst Q
  rfl

private theorem effectEntropy_congr (flip : Bool) {A B : Fin 3 → Matrix n n ℂ}
    (hA : ∀ j, (A j).PosSemidef) (hB : ∀ j, (B j).PosSemidef) (he : A = B) :
    effectEntropy flip A hA = effectEntropy flip B hB := by
  subst B
  rfl

/-- Exact maximum of the entropy gain of the original coordinate pinching for
a flat projection of fixed rank and constant diagonal. -/
theorem isGreatest_flat_record_gain (c : ι → Fin 3) (m r : ℕ) (hm : 0 < m) (hr : 0 < r)
    (hc : ∀ j, Fintype.card {i // c i = j} = m) (hrN : r ≤ 3 * m) :
    IsGreatest {s : ℝ | ∃ P : Matrix ι ι ℂ, ∃ hP : FlatProjection r P,
      gain c (flatState hr hP) = s}
      (entropyBound (@decide (3 * m - r < r) (Classical.propDecidable _))
        m (min r (3 * m - r)) / r) := by
  classical
  let flip := @decide (3 * m - r < r) (Classical.propDecidable _)
  let d := min r (3*m-r)
  let E := coordinateBlocks c hc
  have hN := capacity_card c hc
  have hn0 : 0 < Fintype.card ι := by rw [hN]; omega
  have hdN : d < Fintype.card ι := by dsimp [d]; rw [hN]; omega
  have hmid : 3*(d-m) ≤ d := by dsimp [d]; omega
  have hopt := isGreatest_effectEntropy (n := Fin d) flip m (by simpa using hmid)
  have hr0 : (0 : ℝ) ≤ r := by positivity
  constructor
  · obtain ⟨A, hA, hval⟩ := hopt.1
    obtain ⟨V, hv, hQ, hblocks⟩ := exists_flat_frame c hc hm hA
    let Q := V*Vᴴ
    let P := if flip then 1-Q else Q
    have hP : FlatProjection r P := by
      by_cases hf : 3*m-r < r
      · have hcomp := hQ.complement hn0
        have hdim : Fintype.card ι - Fintype.card (Fin d) = r := by
          rw [hN, Fintype.card_fin]
          dsimp [d]
          omega
        rw [hdim] at hcomp
        simpa [P, flip, hf, Q] using hcomp
      · have hdim : Fintype.card (Fin d) = r := by
          rw [Fintype.card_fin]
          dsimp [d]
          omega
        simpa [P, flip, hf, hdim, Q] using hQ
    refine ⟨P, hP, ?_⟩
    rw [gain_eq_rowEffects c hc flip hr V hP]
    rw [effectEntropy_congr flip _ hA.1 (funext hblocks), hval]
    simp [flip, d]
  · rintro s ⟨P, hP, rfl⟩
    let Q := if flip then 1-P else P
    have hQ : FlatProjection d Q := by
      by_cases hf : 3*m-r < r
      · simpa [Q, flip, hf, d, hN, Nat.min_eq_right hf.le] using hP.complement hn0
      · simpa [Q, flip, hf, d, Nat.min_eq_left (Nat.le_of_not_lt hf)] using hP
    obtain ⟨V,hv,hVQ⟩ := exists_projection_frame hQ hdN
    let P' := if flip then 1-V*Vᴴ else V*Vᴴ
    have hP' : P' = P := by
      dsimp only [P']
      rw [hVQ]
      cases he : flip <;> simp [Q, he]
    let hP'' : FlatProjection r P' := hP'.symm ▸ hP
    have hρ := flatState_congr hr hP'' hP hP'
    rw [← hρ, gain_eq_rowEffects c hc flip hr V hP'']
    let A (j : Fin 3) := (blockRows E V j)ᴴ * blockRows E V j
    have hA : Feasible m A := blockGrams_feasible E V hm hv (by
      intro i
      rw [hVQ, hQ.2.2.2, hN]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
        Complex.ofReal_re, Nat.cast_mul, Nat.cast_ofNat]
      rw [Fintype.card_fin])
    have hs := hopt.2 (show effectEntropy flip A hA.1 ∈ _ from ⟨A,hA,rfl⟩)
    exact div_le_div_of_nonneg_right (by simpa using hs) hr0

#print axioms isGreatest_flat_record_gain

end
end D5.S3.Quantum.Measurement.Auric.EqualBlockProjection
