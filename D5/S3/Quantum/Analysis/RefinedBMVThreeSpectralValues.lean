/- GID: D5/S3/Quantum/Analysis/RefinedBMVThreeSpectralValues
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVThreeSpectralValues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Refined BMV lower bounds with at most three spectral values of the first factor. -/

import D5.S3.Quantum.Analysis.RefinedBMVDimThree

/-!
# Refined BMV with three spectral values

Spectral labels index the same cubic trace defect as in the three-dimensional
proof. The operators associated to the labels are positive compressions by the
square root of the second factor, with no restriction on the ranks of the
spectral projections.
-/

open Matrix NormedSpace
open scoped ComplexOrder BigOperators MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace RefinedBMV.ThreeSpectralValues

open DimThree (defect_cycle defect_swap defect_diag defect_nonneg pairing_all
  criterion_nonneg_ordered mean_map trace_gap word_counts)

variable {n : Type*} [Fintype n]

private theorem trace_cycle (A B C : Matrix n n ℂ) :
    trace (B * C * A) = trace (A * B * C) :=
  (trace_mul_cycle B C A)

private theorem trace_reverse {A B C : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) :
    trace (B * A * C) = star (trace (A * B * C)) := by
  rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_mul, hA.eq, hB.eq, hC.eq,
    ← mul_assoc, trace_cycle C B A]

/-- Cauchy–Schwarz for the Hilbert–Schmidt pairing weighted by the third factor.
This is the ordinary Hilbert–Schmidt pairing after right multiplication by its square root. -/
private theorem trace_cauchy {A B C : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.PosSemidef) :
    0 ≤ trace (A * A * C) ∧ 0 ≤ trace (B * B * C) ∧
      ‖trace (A * B * C)‖ ^ 2 ≤ (trace (A * A * C)).re * (trace (B * B * C)).re := by
  have ha : trace (A * C * Aᴴ) = trace (A * A * C) := by
    rw [hA.eq, trace_mul_cycle]
  have hb : trace (B * C * Bᴴ) = trace (B * B * C) := by
    rw [hB.eq, trace_mul_cycle]
  have hab : trace (B * C * Aᴴ) = trace (A * B * C) := by
    rw [hA.eq, trace_mul_cycle]
  refine ⟨?_, ?_, ?_⟩
  · rw [← ha]
    exact (hC.mul_mul_conjTranspose_same A).trace_nonneg
  · rw [← hb]
    exact (hC.mul_mul_conjTranspose_same B).trace_nonneg
  let : _ := C.toMatrixSeminormedAddCommGroup hC
  let : _ := C.toMatrixInnerProductSpace hC
  have hs (X Y : Matrix n n ℂ) : inner ℂ X Y = trace (Y * C * Xᴴ) := rfl
  have hc := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) A B) 2
  rw [hs, hab, mul_pow, norm_sq_eq_re_inner (𝕜 := ℂ) A, norm_sq_eq_re_inner (𝕜 := ℂ) B,
    hs, hs, ha, hb] at hc
  exact hc

/-- Three positive matrix factors obey the cubic defect inequality under the scalar pairing
criterion, in any finite dimension. -/
theorem operator_walk_nonneg (d : ℝ → ℝ → ℝ → ℝ) (a : Fin 3 → ℝ)
    (C : Fin 3 → Matrix n n ℂ) (hC : ∀ i, (C i).PosSemidef)
    (hn : ∀ i j k, 0 ≤ d (a i) (a j) (a k)) (hdiag : ∀ x, d x x x = 0)
    (hswap : ∀ x y z, d y x z = d x y z) (hrotate : ∀ x y z, d y z x = d x y z)
    (hpair : d (a 0) (a 1) (a 2) ≤ DimThree.paired d (a 0) (a 1) (a 2)) :
    0 ≤ ∑ i, ∑ j, ∑ k, trace (C i * C j * C k) * (d (a i) (a j) (a k) : ℂ) := by
  let δ (i k : Fin 3) := d (a i) (a i) (a k)
  let q (i k : Fin 3) := (trace (C i * C i * C k)).re
  let t := trace (C 0 * C 1 * C 2)
  let w (i j k : Fin 3) := trace (C i * C j * C k) * (d (a i) (a j) (a k) : ℂ)
  have hcycle (i j k : Fin 3) : w j k i = w i j k := by
    simp only [w, hrotate, trace_cycle (C i) (C j) (C k)]
  have hreverse (i j k : Fin 3) : w j i k = star (w i j k) := by
    simp only [w, trace_reverse (hC i).isHermitian (hC j).isHermitian (hC k).isHermitian,
      hswap, star_mul, Complex.star_def, Complex.conj_ofReal]
    exact mul_comm _ _
  have hzero (i : Fin 3) : w i i i = 0 := by simp [w, hdiag]
  have hrepeat (i j : Fin 3) : w i i j = (q i j * δ i j : ℝ) := by
    have hq := (trace_cauchy (hC i).isHermitian (hC i).isHermitian (hC j)).1
    have hre : (q i j : ℂ) = trace (C i * C i * C j) :=
      Complex.ext rfl (Complex.nonneg_iff.mp hq).2
    simp only [w, δ, Complex.ofReal_mul, hre]
  have hrepeat₁ (i j : Fin 3) : w i j i = (q i j * δ i j : ℝ) :=
    (hcycle i i j).trans (hrepeat i j)
  have hrepeat₂ (i j : Fin 3) : w j i i = (q i j * δ i j : ℝ) :=
    (hcycle i j i).trans (hrepeat₁ i j)
  have hcounter : w 0 2 1 = star (w 0 1 2) :=
    (hcycle 1 0 2).trans (hreverse 0 1 2)
  have htriangle : w 0 1 2 + star (w 0 1 2) =
      (2 * t.re * d (a 0) (a 1) (a 2) : ℝ) := by
    rw [Complex.star_def, Complex.add_conj, Complex.ofReal_inj]
    simp [w, t, Complex.mul_re, mul_assoc]
  have hexpand : (∑ i, ∑ j, ∑ k, w i j k) =
      (3 * (q 1 0 * δ 1 0 + q 2 0 * δ 2 0 + (q 0 1 * δ 0 1 + q 2 1 * δ 2 1) +
        (q 0 2 * δ 0 2 + q 1 2 * δ 1 2)) + 6 * t.re * d (a 0) (a 1) (a 2) : ℝ) := by
    simp only [Fin.sum_univ_three, hzero, zero_add, add_zero]
    simp only [hrepeat, hrepeat₁, hrepeat₂,
      hcycle 0 1 2, hcycle 1 2 0, hcycle 0 2 1, hcycle 2 1 0, hcounter]
    calc
      _ = 3 * (((q 1 0 * δ 1 0 : ℝ) : ℂ) + (q 2 0 * δ 2 0) +
          ((q 0 1 * δ 0 1) + (q 2 1 * δ 2 1)) +
          ((q 0 2 * δ 0 2) + (q 1 2 * δ 1 2))) +
          3 * (w 0 1 2 + star (w 0 1 2)) := by push_cast; ring
      _ = _ := by rw [htriangle]; push_cast; ring
  have hbound (i j k : Fin 3) (ht : ‖trace (C i * C j * C k)‖ = ‖t‖) :
      2 * ‖t‖ * Real.sqrt (δ i k * δ j k) ≤ q i k * δ i k + q j k * δ j k := by
    obtain ⟨hi, hj, hc⟩ := trace_cauchy (hC i).isHermitian (hC j).isHermitian (hC k)
    rw [ht] at hc
    have hδ : 0 ≤ δ i k * δ j k := mul_nonneg (hn i i k) (hn j j k)
    rw [mul_assoc]
    refine two_mul_le_add_of_sq_le_mul
      (mul_nonneg (Complex.nonneg_iff.mp hi).1 (hn i i k))
      (mul_nonneg (Complex.nonneg_iff.mp hj).1 (hn j j k)) ?_
    rw [mul_pow, Real.sq_sqrt hδ]
    calc
      _ ≤ (q i k * q j k) * (δ i k * δ j k) := mul_le_mul_of_nonneg_right hc hδ
      _ = _ := by ring
  have h0 := hbound 1 2 0 (congrArg norm (trace_cycle (C 0) (C 1) (C 2)))
  have h1 := hbound 0 2 1 (by
    rw [trace_cycle (C 1) (C 0) (C 2),
      trace_reverse (hC 0).isHermitian (hC 1).isHermitian (hC 2).isHermitian, norm_star])
  have h2 := hbound 0 1 2 rfl
  have htotal := mul_le_mul_of_nonneg_left hpair (show 0 ≤ 2 * ‖t‖ by positivity)
  change 2 * ‖t‖ * d (a 0) (a 1) (a 2) ≤
    2 * ‖t‖ * (Real.sqrt (δ 1 0 * δ 2 0) + Real.sqrt (δ 0 1 * δ 2 1) +
      Real.sqrt (δ 0 2 * δ 1 2)) at htotal
  have ht := mul_le_mul_of_nonneg_right ((abs_le.mp (Complex.abs_re_le_norm t)).1) (hn 0 1 2)
  change 0 ≤ ∑ i, ∑ j, ∑ k, w i j k
  rw [hexpand, Complex.zero_le_real]
  nlinarith only [h0, h1, h2, htotal, ht]

variable [DecidableEq n]

private def spectralProjection (label : n → Fin 3) (i : Fin 3) : Matrix n n ℂ :=
  diagonal fun j ↦ if label j = i then 1 else 0

private theorem compressed_walk (B : Matrix n n ℂ) (hB : B.PosSemidef)
    (label : n → Fin 3) (f : Fin 3 → Fin 3 → Fin 3 → ℂ) :
    walk B (fun i j k ↦ f (label i) (label j) (label k)) =
      ∑ i, ∑ j, ∑ k,
        trace ((CFC.sqrt B * spectralProjection label i * CFC.sqrt B) *
          (CFC.sqrt B * spectralProjection label j * CFC.sqrt B) *
          (CFC.sqrt B * spectralProjection label k * CFC.sqrt B)) * f i j k := by
  let S := CFC.sqrt B
  have hS : S * S = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  let ind (i : Fin 3) (j : n) : ℂ := if label j = i then 1 else 0
  let g (i j k : Fin 3) (u v w : n) : ℂ := ind i u * ind j v * ind k w
  have pick (v : n) (F : Fin 3 → ℂ) : (∑ i, F i * ind i v) = F (label v) := by
    simp [ind, mul_ite]
  have hf : (fun i j k ↦ f (label i) (label j) (label k)) =
      ∑ i, ∑ j, ∑ k, f i j k • g i j k := by
    funext u v w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, g, ← mul_assoc, pick]
  have hg (i j k : Fin 3) : walk B (g i j k) =
      trace ((S * spectralProjection label i * S) * (S * spectralProjection label j * S) *
        (S * spectralProjection label k * S)) := by
    rw [show walk B (g i j k) =
      trace (spectralProjection label i * (B * (spectralProjection label j *
        (B * (spectralProjection label k * B))))) from
      (trace_diagonal_walk B (ind i) (ind j) (ind k)).symm]
    rw [show (S * spectralProjection label i * S) * (S * spectralProjection label j * S) *
        (S * spectralProjection label k * S) =
        S * (spectralProjection label i * (B * (spectralProjection label j *
          (B * (spectralProjection label k * S))))) by
      rw [← hS]
      simp only [mul_assoc]]
    rw [trace_mul_comm S]
    simp only [mul_assoc]
    rw [hS]
  rw [hf]
  simp only [map_sum, map_smul, hg, smul_eq_mul, mul_comm, S]

private theorem diagonal_bound {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (a : Fin 3 → ℝ) (ha : ∀ i, 0 ≤ a i) (label : n → Fin 3)
    (B : Matrix n n ℂ) (hB : B.PosSemidef) :
    trace (((diagonal fun i ↦ (a (label i) : ℂ)) ^ p * B) ^ 3) ≤
      DimThree.wordMean p ((diagonal fun i ↦ (a (label i) : ℂ)) ^ 3) B := by
  let C (i : Fin 3) := CFC.sqrt B * spectralProjection label i * CFC.sqrt B
  have hC (i : Fin 3) : (C i).PosSemidef := by
    have hP : (spectralProjection label i).PosSemidef := by
      apply posSemidef_diagonal_iff.mpr
      intro j
      split <;> simp
    have hS := (CFC.sqrt_nonneg B).posSemidef.isHermitian
    simpa only [C, hS.eq] using hP.mul_mul_conjTranspose_same (CFC.sqrt B)
  have hn := operator_walk_nonneg (DimThree.defect p) a C hC
    (fun i j k ↦ defect_nonneg hp _ _ _ (ha i) (ha j) (ha k))
    (defect_diag hp) (defect_swap hp) (defect_cycle hp)
    (pairing_all hp (criterion_nonneg_ordered p hp) _ _ _ (ha 0) (ha 1) (ha 2))
  rw [← compressed_walk B hB label
    (fun i j k ↦ ((DimThree.defect p (a i) (a j) (a k) : ℝ) : ℂ)), ← trace_gap hp] at hn
  have hlen : (0 : ℝ) < (DimThree.gaps p).length := by exact_mod_cast (word_counts hp).2.1
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hn
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    Complex.sub_re, Complex.sub_im, zero_mul, sub_zero, add_zero] at hre him
  exact Complex.le_def.mpr ⟨sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hlen).mp hre),
    (sub_eq_zero.mp (mul_eq_zero.mp him.symm |>.resolve_left hlen.ne')).symm⟩

omit [DecidableEq n] in
private theorem spectral_labels (values : n → ℝ) (h : (Finset.univ.image values).card ≤ 3)
    (base : ℝ) : ∃ a : Fin 3 → ℝ, ∃ label : n → Fin 3, (∀ i, values i = a (label i)) ∧
      ∀ k, a k = base ∨ ∃ i, a k = values i := by
  classical
  let s := Finset.univ.image values
  let e := s.equivFin
  let idx (i : n) : s := ⟨values i, Finset.mem_image_of_mem values (Finset.mem_univ i)⟩
  let label (i : n) := Fin.castLE h (e (idx i))
  let a (k : Fin 3) := if hk : k.val < s.card then (e.symm ⟨k.val, hk⟩ : ℝ) else base
  refine ⟨a, label, fun i ↦ ?_, fun k ↦ ?_⟩
  · have hi : (label i).val < s.card := (e (idx i)).isLt
    dsimp only [a]
    rw [dite_eq_left hi]
    exact (congrArg Subtype.val (e.symm_apply_apply (idx i))).symm
  · by_cases hk : k.val < s.card
    · right
      have hm := (e.symm ⟨k.val, hk⟩).property
      rcases Finset.mem_image.mp hm with ⟨i, _, hi⟩
      exact ⟨i, by simp [a, hk, hi]⟩
    · exact Or.inl (dite_eq_right hk)

/-- The strong refined BMV product bound for five, six, or seven first factors and
three second factors. The first PSD matrix has at most three distinct eigenvalues. -/
theorem product_bound {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hs : (Finset.univ.image hA.isHermitian.eigenvalues).card ≤ 3) :
    trace (((A ^ ((p : ℝ) / 3)) * B) ^ 3) ≤ DimThree.wordMean p A B := by
  obtain ⟨a, label, hlabel, ha⟩ := spectral_labels _ hs 0
  have ha₀ (i : Fin 3) : 0 ≤ a i := by
    rcases ha i with h | ⟨k, h⟩
    · rw [h]
    · rw [h]
      exact hA.eigenvalues_nonneg k
  let H := hA.isHermitian
  let U := H.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℂ _ (star U)
  let x (i : Fin 3) := a i ^ (1 / 3 : ℝ)
  let D := diagonal fun i ↦ (x (label i) : ℂ)
  have hB' : (f B).PosSemidef := by
    change (Unitary.conjStarAlgAut ℂ _ (star U) B).PosSemidef
    rw [Unitary.conjStarAlgAut_star_apply]
    exact hB.conjTranspose_mul_mul_same (U : Matrix n n ℂ)
  have hd : f A = D ^ 3 := by
    rw [H.conjStarAlgAut_star_eigenvectorUnitary, diagonal_pow]
    congr 1
    funext i
    change (hA.isHermitian.eigenvalues i : ℂ) = (x (label i) : ℂ) ^ 3
    dsimp only [x]
    rw [hlabel i, ← Complex.ofReal_pow, Complex.ofReal_inj,
      ← Real.rpow_mul_natCast (ha₀ _)]
    norm_num
  have hpow : f (A ^ ((p : ℝ) / 3)) = D ^ p := by
    rw [CFC.rpow_eq_cfc_real hA.nonneg, H.cfc_eq, Matrix.IsHermitian.cfc]
    have hf : f.symm = Unitary.conjStarAlgAut ℂ _ U := by simp [f]
    change f (Unitary.conjStarAlgAut ℂ _ U _) = _
    rw [← hf, StarAlgEquiv.apply_symm_apply, diagonal_pow]
    congr 1
    funext i
    change ((hA.isHermitian.eigenvalues i ^ ((p : ℝ) / 3) : ℝ) : ℂ) =
      (x (label i) : ℂ) ^ p
    dsimp only [x]
    rw [hlabel i, ← Complex.ofReal_pow, Complex.ofReal_inj,
      ← Real.rpow_mul_natCast (ha₀ _)]
    congr 1
    ring
  have h := diagonal_bound hp x (fun i ↦ Real.rpow_nonneg (ha₀ i) _) label (f B) hB'
  change trace ((D ^ p * f B) ^ 3) ≤ DimThree.wordMean p (D ^ 3) (f B) at h
  rw [← hd, ← hpow, ← map_mul f, ← map_pow f, trace_conjugation] at h
  exact h.trans_eq (mean_map p f.toAlgEquiv (trace_conjugation (star U)) A B)

/-- The exact finite-dimensional dyadic trace comparison with three factors. -/
theorem trace_exp_le_cube (H K : Matrix n n ℂ) (hH : H.IsHermitian)
    (hK : K.IsHermitian) :
    trace (exp ((3 : ℝ) • H + (3 : ℝ) • K)) ≤ trace ((exp H * exp K) ^ 3) := by
  rcases isEmpty_or_nonempty n with hempty | hne
  · let : _ := hempty
    simp only [trace_eq_zero_of_isEmpty, le_refl]
  let : _ := hne
  let : NeZero (Fintype.card n) := ⟨Fintype.card_ne_zero⟩
  let e := Fintype.equivFin n
  let f := Matrix.reindexAlgEquiv ℂ ℂ e
  have htr (A : Matrix n n ℂ) : trace (f A) = trace A := by
    change (∑ i, A (e.symm i) (e.symm i)) = ∑ i, A i i
    exact e.symm.sum_comp (fun i ↦ A i i)
  let : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  let : NormedAlgebra ℚ (Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have hExp (A : Matrix n n ℂ) : f (exp A) = exp (f A) :=
    NormedSpace.map_exp f
      (continuous_matrix fun i j ↦ continuous_apply_apply (e.symm i) (e.symm j)) A
  have hSmul (r : ℝ) (A : Matrix n n ℂ) : f (r • A) = r • f A := rfl
  have hfH : (f H).IsHermitian := (isHermitian_submatrix_equiv e.symm).mpr hH
  have hfK : (f K).IsHermitian := (isHermitian_submatrix_equiv e.symm).mpr hK
  have h := exponential_trace_le_cube (f H) (f K) hfH hfK
  rw [← hSmul, ← hSmul, ← map_add f, ← hExp, htr, ← hExp, ← hExp,
    ← map_mul f, ← map_pow f, htr] at h
  refine Complex.le_def.mpr ⟨h, ?_⟩
  have he : IsSelfAdjoint (trace (exp ((3 : ℝ) • H + (3 : ℝ) • K))) := by
    change star (trace _) = _
    rw [← trace_conjTranspose, ((hH.smul (by simp : star (3 : ℝ) = 3)).add
      (hK.smul (by simp : star (3 : ℝ) = 3))).exp.eq]
  rw [(Complex.im_eq_zero_iff_isSelfAdjoint _).mpr he,
    (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr (trace_cube_isSelfAdjoint _ _ hH.exp hK.exp)]

/-- The refined BMV exponential lower bound at five, six, or seven first factors,
when the first Hermitian matrix has at most three distinct eigenvalues. -/
theorem exponential_bound {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (H K : Matrix n n ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hs : (Finset.univ.image hH.eigenvalues).card ≤ 3) :
    trace (exp ((p : ℝ) • H + (3 : ℝ) • K)) ≤ DimThree.wordMean p (exp H) (exp K) := by
  obtain ⟨a, label, hlabel, _⟩ := spectral_labels _ hs 0
  let U := hH.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℂ _ (star U)
  let T : Matrix n n ℂ := (1 / 3 : ℝ) • H
  let X := exp T
  let x (i : Fin 3) := Real.exp ((1 / 3 : ℝ) * a i)
  let D := diagonal fun i ↦ (x (label i) : ℂ)
  have hT : T.IsHermitian := hH.smul (by simp : star (1 / 3 : ℝ) = 1 / 3)
  let : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hf_cont : Continuous f := by
    change Continuous (fun A : Matrix n n ℂ ↦
      Unitary.conjStarAlgAut ℂ _ (star U) A)
    simp only [Unitary.conjStarAlgAut_star_apply]
    exact (continuous_const.mul continuous_id).mul continuous_const
  have hdiag : f H = diagonal (RCLike.ofReal ∘ hH.eigenvalues) :=
    hH.conjStarAlgAut_star_eigenvectorUnitary
  have hf_smul : f ((1 / 3 : ℝ) • H) = (1 / 3 : ℝ) • f H :=
    f.toAlgEquiv.toLinearEquiv.map_smul_of_tower _ _
  have hd : f X = D := by
    rw [show X = exp ((1 / 3 : ℝ) • H) by rfl, NormedSpace.map_exp f hf_cont,
      hf_smul, hdiag, ← diagonal_smul, exp_diagonal]
    congr 1
    funext i
    rw [Pi.exp_def]
    change exp ((1 / 3 : ℝ) • (hH.eigenvalues i : ℂ)) = (x (label i) : ℂ)
    rw [← Complex.exp_eq_exp_ℂ, RCLike.real_smul_eq_coe_mul, RCLike.ofReal_eq_complex_ofReal,
      ← Complex.ofReal_mul, ← Complex.ofReal_exp, hlabel i]
  have hB : (exp K).PosSemidef := hK.isSelfAdjoint.exp_nonneg.posSemidef
  have hB' : (f (exp K)).PosSemidef := by
    change (Unitary.conjStarAlgAut ℂ _ (star U) (exp K)).PosSemidef
    rw [Unitary.conjStarAlgAut_star_apply]
    exact hB.conjTranspose_mul_mul_same (U : Matrix n n ℂ)
  have h := diagonal_bound hp x (fun i ↦ (Real.exp_pos _).le) label (f (exp K)) hB'
  change trace ((D ^ p * f (exp K)) ^ 3) ≤ DimThree.wordMean p (D ^ 3) (f (exp K)) at h
  rw [← hd, ← map_pow f, ← map_mul f, ← map_pow f, trace_conjugation, ← map_pow f] at h
  change _ ≤ DimThree.wordMean p (f.toAlgEquiv (X ^ 3)) (f.toAlgEquiv (exp K)) at h
  rw [mean_map p f.toAlgEquiv (trace_conjugation (star U))] at h
  have hpow (k : ℕ) : X ^ k = exp ((k : ℝ) • T) := by
    rw [Nat.cast_smul_eq_nsmul, Matrix.exp_nsmul]
  have h3 : X ^ (3 : ℕ) = exp H := by
    rw [hpow]
    norm_num [T, smul_smul]
  rw [h3, hpow p] at h
  have ht := trace_exp_le_cube ((p : ℝ) • T) K
    (hT.smul (by simp : star (p : ℝ) = p)) hK
  have hScale : (3 : ℝ) • ((p : ℝ) • T) = (p : ℝ) • H := by
    dsimp only [T]
    rw [smul_smul, smul_smul]
    congr 1
    ring
  rw [hScale] at ht
  exact ht.trans h

#print axioms operator_walk_nonneg
#print axioms product_bound
#print axioms exponential_bound

end RefinedBMV.ThreeSpectralValues
