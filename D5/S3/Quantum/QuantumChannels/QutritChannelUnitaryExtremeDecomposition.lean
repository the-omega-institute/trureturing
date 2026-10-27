/- GID: D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Unitary and doubly extreme decomposition of the equal-modulus HMR qutrit channel. -/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The equal-modulus HMR channel and its unitary and extreme-point decomposition. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open MatrixMap

namespace D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition

/-- The four operators of Haagerup, Musat and Ruskai, in their source order. -/
def hmrKraus (α β : ℂ) : Fin 4 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![α, 0, 0; 0, 0, 1; 0, 0, 0],
    !![0, 0, β; 0, 0, 0; 0, 1, 0],
    !![0, -1, 0; 0, 0, 0; -star β, 0, 0],
    !![0, 0, 0; 1, 0, 0; 0, 0, star α]]

/-- The source convention places the adjoint of each operator on the left. -/
def hmrChannel (α β : ℂ) : MatrixMap (Fin 3) (Fin 3) ℂ :=
  (1 / 2 : ℂ) • of_kraus (fun k => star (hmrKraus α β k))
    (fun k => star (hmrKraus α β k))

/-- A map is unital when it preserves the identity matrix. -/
def IsUnital (φ : MatrixMap (Fin 3) (Fin 3) ℂ) : Prop := φ 1 = 1

/-- Trace preservation is required on every complex matrix. -/
def IsTracePreserving (φ : MatrixMap (Fin 3) (Fin 3) ℂ) : Prop :=
  ∀ x, (φ x).trace = x.trace

private def krausChannel (y : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ) :
    MatrixMap (Fin 3) (Fin 3) ℂ :=
  of_kraus (fun i => star (y i)) (fun i => star (y i))

private def baseKraus : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  fun i => (1 / (2 * Real.sqrt 3) : ℂ) •
    (![!![-1, -(Real.sqrt 2 : ℂ), 1;
          (Real.sqrt 2 : ℂ), 0, -(Real.sqrt 2 : ℂ);
          -1, (Real.sqrt 2 : ℂ), 1],
       !![1, (Real.sqrt 2 : ℂ), 1;
          (Real.sqrt 2 : ℂ), 0, (Real.sqrt 2 : ℂ);
          1, (Real.sqrt 2 : ℂ), 1],
       !![1, -(Real.sqrt 2 : ℂ), 1;
          -(Real.sqrt 2 : ℂ), 0, (Real.sqrt 2 : ℂ);
          -1, (Real.sqrt 2 : ℂ), -1]] i)

private def baseUnitary : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 2 : ℂ) • !![1, -(Real.sqrt 2 : ℂ), -1;
    (Real.sqrt 2 : ℂ), 0, (Real.sqrt 2 : ℂ);
    -1, -(Real.sqrt 2 : ℂ), 1]

private def diagonalPhase (r : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![r, 1, r⁻¹]

private def conjugateChannel (d e : Matrix (Fin 3) (Fin 3) ℂ)
    (φ : MatrixMap (Fin 3) (Fin 3) ℂ) : MatrixMap (Fin 3) (Fin 3) ℂ :=
  (of_kraus (fun _ : Fin 1 => star e) (fun _ : Fin 1 => star e)).comp
    (φ.comp (of_kraus (fun _ : Fin 1 => star d) (fun _ : Fin 1 => star d)))

private lemma conjugate_action (d e : Matrix (Fin 3) (Fin 3) ℂ)
    (φ : MatrixMap (Fin 3) (Fin 3) ℂ) (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    conjugateChannel d e φ ρ = star e * φ (star d * ρ * d) * e := by
  unfold conjugateChannel of_kraus
  simp only [LinearMap.comp_apply, Fin.sum_univ_one,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]

private lemma hmr_action (α β : ℂ) (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    hmrChannel α β ρ = (1 / 2 : ℂ) • ∑ i, star (hmrKraus α β i) * ρ * hmrKraus α β i := by
  unfold hmrChannel of_kraus
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

private lemma kraus_action (y : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    krausChannel y ρ = ∑ i, star (y i) * ρ * y i := by
  unfold krausChannel of_kraus
  simp only [LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

private lemma choi_domination (φ θ η : MatrixMap (Fin 3) (Fin 3) ℂ)
    (t s : ℝ) (hs : 0 ≤ s) (hη : η.IsCompletelyPositive)
    (hseg : t • θ + s • η = φ) :
    (choi_matrix φ - t • choi_matrix θ).PosSemidef := by
  have heq : choi_matrix φ - t • choi_matrix θ = s • choi_matrix η := by
    rw [← hseg]
    ext ⟨i, j⟩ ⟨k, l⟩
    change (t • θ + s • η) (Matrix.single j l 1) i k -
      t • θ (Matrix.single j l 1) i k = s • η (Matrix.single j l 1) i k
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Matrix.add_apply, Matrix.smul_apply]
    abel
  rw [heq]
  exact ((choi_PSD_iff_CP_map η).mp hη).smul hs

private lemma coefficients_unique
    (z : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (hli : LinearIndependent ℂ (fun p : Fin 3 × Fin 3 => z p.1 p.2))
    (hdiag : ∑ i, z i i = 1) (h : Matrix (Fin 3) (Fin 3) ℂ)
    (hsum : ∑ i, ∑ j, h i j • z i j = 1) : h = 1 := by
  have hzero : ∑ p : Fin 3 × Fin 3,
      (h p.1 p.2 - (1 : Matrix (Fin 3) (Fin 3) ℂ) p.1 p.2) • z p.1 p.2 = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, Fintype.sum_prod_type]
    rw [hsum]
    simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [hdiag, sub_self]
  have hc := Fintype.linearIndependent_iff.mp hli _ hzero
  ext i j
  exact sub_eq_zero.mp (hc (i, j))

private lemma kraus_tp (y : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (htp : ∑ i, y i * star (y i) = 1) : IsTracePreserving (krausChannel y) := by
  intro ρ
  rw [kraus_action, Matrix.trace_sum]
  calc
    ∑ i, (star (y i) * ρ * y i).trace = ∑ i, (ρ * (y i * star (y i))).trace := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (star (y i)) (ρ * y i)
    _ = ρ.trace := by
      rw [← Matrix.trace_sum, ← Matrix.mul_sum, htp, Matrix.mul_one]

private lemma choi_range_lift (y : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (θ : MatrixMap (Fin 3) (Fin 3) ℂ) (t : ℝ) (ht : 0 < t)
    (hθ : θ.IsCompletelyPositive)
    (hdom : (choi_matrix (krausChannel y) - t • choi_matrix θ).PosSemidef) :
    ∃ h : Matrix (Fin 3) (Fin 3) ℂ, ∀ ρ,
      θ ρ = ∑ i, ∑ j, h i j • (star (y i) * ρ * y j) := by
  let v : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ :=
    fun p i => star (y i) p.1 p.2
  have hc : choi_matrix (krausChannel y) = v * vᴴ := by
    unfold krausChannel
    rw [choi_of_kraus]
    ext p q
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    rfl
  have hbpos := (choi_PSD_iff_CP_map θ).mp hθ
  obtain ⟨k, hk⟩ := exists_kraus_of_choi_PSD (choi_matrix θ) hbpos
  let b : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
    fun p i => k i p.1 p.2
  have hb : choi_matrix θ = b * bᴴ := by
    rw [hk, choi_of_kraus]
    ext p q
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    rfl
  have hker : ∀ w, choi_matrix (krausChannel y) *ᵥ w = 0 →
      choi_matrix θ *ᵥ w = 0 := by
    sorry
  have hkerb : ∀ w, choi_matrix (krausChannel y) *ᵥ w = 0 → bᴴ *ᵥ w = 0 := by
    intro w hw
    apply (Matrix.self_mul_conjTranspose_mulVec_eq_zero b w).mp
    rw [← hb]
    exact hker w hw
  have hfactor : ∃ q : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ,
      bᴴ = q * choi_matrix (krausChannel y) := by
    sorry
  obtain ⟨q, hq⟩ := hfactor
  have hcstar : (choi_matrix (krausChannel y))ᴴ = choi_matrix (krausChannel y) := by
    rw [hc, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hbq : b = choi_matrix (krausChannel y) * qᴴ := by
    have heq := congrArg Matrix.conjTranspose hq
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul, hcstar] using heq
  let h := vᴴ * qᴴ * q * v
  have hmatrix : choi_matrix θ = v * h * vᴴ := by
    calc
      choi_matrix θ = b * bᴴ := hb
      _ = (choi_matrix (krausChannel y) * qᴴ) *
          (q * choi_matrix (krausChannel y)) := congrArg₂ (· * ·) hbq hq
      _ = v * h * vᴴ := by
        rw [hc]
        dsimp only [h]
        simp only [Matrix.mul_assoc]
  refine ⟨h, fun ρ => ?_⟩
  calc
    θ ρ = of_choi_matrix (choi_matrix θ) ρ :=
      congrArg (fun f : MatrixMap (Fin 3) (Fin 3) ℂ => f ρ) (choi_map_inv θ).symm
    _ = ∑ i, ∑ j, h i j • (star (y i) * ρ * y j) := by
      rw [hmatrix]
      change (fun a c => ∑ j, ∑ l, ρ j l * (v * h * vᴴ) (a, j) (c, l)) = _
      ext a c
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Fin.sum_univ_three]
      dsimp only [v]
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_star]
      ring

private lemma extreme_ucp_of_independent
    (y : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (hu : ∑ i, star (y i) * y i = 1)
    (hli : LinearIndependent ℂ
      (fun p : Fin 3 × Fin 3 => star (y p.1) * y p.2)) :
    krausChannel y ∈ Set.extremePoints ℝ
      {θ : MatrixMap (Fin 3) (Fin 3) ℂ | θ.IsCompletelyPositive ∧ IsUnital θ} := by
  refine ⟨⟨of_kraus_isCompletelyPositive _, ?_⟩, ?_⟩
  · change krausChannel y 1 = 1
    rw [kraus_action]
    simpa only [Matrix.mul_one] using hu
  · intro θ hθ η hη hseg
    obtain ⟨t, s, ht, hs, hts, hseg⟩ := hseg
    obtain ⟨h, hh⟩ := choi_range_lift y θ t ht hθ.1
      (choi_domination _ θ η t s hs.le hη.1 hseg)
    have hsum : ∑ i, ∑ j, h i j • (star (y i) * y j) = 1 := by
      simpa only [Matrix.mul_one] using (hh 1).symm.trans hθ.2
    have hid := coefficients_unique (fun i j => star (y i) * y j) hli hu h hsum
    apply LinearMap.ext
    intro ρ
    rw [hh, hid, kraus_action]
    simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private lemma extreme_cpt_of_independent
    (y : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (htp : ∑ i, y i * star (y i) = 1)
    (hli : LinearIndependent ℂ
      (fun p : Fin 3 × Fin 3 => y p.1 * star (y p.2))) :
    krausChannel y ∈ Set.extremePoints ℝ
      {θ : MatrixMap (Fin 3) (Fin 3) ℂ |
        θ.IsCompletelyPositive ∧ IsTracePreserving θ} := by
  refine ⟨⟨of_kraus_isCompletelyPositive _, kraus_tp y htp⟩, ?_⟩
  intro θ hθ η hη hseg
  obtain ⟨t, s, ht, hs, hts, hseg⟩ := hseg
  obtain ⟨h, hh⟩ := choi_range_lift y θ t ht hθ.1
    (choi_domination _ θ η t s hs.le hη.1 hseg)
  have hsum : ∑ i, ∑ j, h i j • (y j * star (y i)) = 1 := by
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro ρ
    rw [Matrix.mul_one]
    calc
      (ρ * ∑ i, ∑ j, h i j • (y j * star (y i))).trace = (θ ρ).trace := by
        rw [hh]
        simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        simpa only [Matrix.mul_assoc] using
          (Matrix.trace_mul_comm (star (y i)) (ρ * y j)).symm
      _ = ρ.trace := hθ.2 ρ
  have hsumt : ∑ i, ∑ j, h j i • (y i * star (y j)) = 1 := by
    rw [Finset.sum_comm]
    exact hsum
  have hid := coefficients_unique (fun i j => y i * star (y j)) hli htp hᵀ hsumt
  have hhId : h = 1 := by
    have := congrArg Matrix.transpose hid
    simpa only [Matrix.transpose_transpose, Matrix.transpose_one] using this
  apply LinearMap.ext
  intro ρ
  rw [hh, hhId, kraus_action]
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private lemma choi_rank_of_independent
    (y : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (hli : LinearIndependent ℂ
      (fun p : Fin 3 × Fin 3 => star (y p.1) * y p.2)) :
    (choi_matrix (krausChannel y)).rank = 3 := by
  have hy : LinearIndependent ℂ y := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc j
    have hz : ∑ p : Fin 3 × Fin 3,
        (if p.1 = 0 then c p.2 else 0) • (star (y p.1) * y p.2) = 0 := by
      rw [Fintype.sum_prod_type]
      simp only [ite_smul, zero_smul, Finset.sum_ite_irrel, Finset.sum_const_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      simp_rw [← Matrix.mul_smul]
      rw [← Matrix.mul_sum, hc, Matrix.mul_zero]
    have heq := Fintype.linearIndependent_iff.mp hli _ hz (0, j)
    simpa using heq
  have hstar : LinearIndependent ℂ (fun i => star (y i)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc j
    have heq := congrArg star hc
    simp only [star_sum, star_smul, star_star, star_zero] at heq
    have hj := Fintype.linearIndependent_iff.mp hy _ heq j
    exact star_eq_zero.mp hj
  let v : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ := fun p i => star (y i) p.1 p.2
  have hv : LinearIndependent ℂ vᵀ.row := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc j
    have hz : ∑ i, c i • star (y i) = 0 := by
      ext a b
      have heq := congrFun hc (a, b)
      change (∑ i, c i • star (y i) a b) = 0 at heq
      change (∑ i, c i • star (y i)) a b = 0
      simpa only [Matrix.sum_apply, Matrix.smul_apply] using heq
    exact Fintype.linearIndependent_iff.mp hstar _ hz j
  have hchoi : choi_matrix (krausChannel y) = v * vᴴ := by
    unfold krausChannel
    rw [choi_of_kraus]
    ext p q
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    rfl
  rw [hchoi, Matrix.rank_self_mul_conjTranspose, ← Matrix.rank_transpose v]
  exact hv.rank_matrix

private lemma base_unital : ∑ i, star (baseKraus i) * baseKraus i = 1 := by
  have htwo : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hthree : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hne : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseKraus, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.vecMul_apply_eq_sum] <;>
    field_simp <;> ring_nf <;> norm_num [map_ofNat, htwo, hthree]

private lemma base_trace : ∑ i, baseKraus i * star (baseKraus i) = 1 := by
  have htwo : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hthree : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hne : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [baseKraus, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.vecMul_apply_eq_sum] <;>
    field_simp <;> ring_nf <;> norm_num [map_ofNat, htwo, hthree]

set_option maxHeartbeats 2000000 in
-- The nine dual-coordinate identities expand finite matrix products over complex radicals.
private lemma base_left_independent : LinearIndependent ℂ
    (fun p : Fin 3 × Fin 3 => star (baseKraus p.1) * baseKraus p.2) := by
  have htwo : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hthree : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hne : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))
  apply Fintype.linearIndependent_iff.mpr
  intro c hc p
  let z : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
    ![
      ![!![(-1 / 6 : ℂ), (1 / 4 : ℂ) * (Real.sqrt 2 : ℂ), -1;
          (1 / 4 : ℂ) * (Real.sqrt 2 : ℂ), (4 / 3 : ℂ), (1 / 4 : ℂ) * (Real.sqrt 2 : ℂ);
          -1, (1 / 4 : ℂ) * (Real.sqrt 2 : ℂ), (-1 / 6 : ℂ)],
        !![0, (-3 / 2 : ℂ) * (Real.sqrt 2 : ℂ), 0;
          0, 0, 0;
          0, (3 / 2 : ℂ) * (Real.sqrt 2 : ℂ), 0],
        !![(-1 / 2 : ℂ), (3 / 4 : ℂ) * (Real.sqrt 2 : ℂ), 0;
          (-3 / 4 : ℂ) * (Real.sqrt 2 : ℂ), 1, (-3 / 4 : ℂ) * (Real.sqrt 2 : ℂ);
          0, (3 / 4 : ℂ) * (Real.sqrt 2 : ℂ), (-1 / 2 : ℂ)]],
      ![!![0, 0, 0;
          (-3 / 2 : ℂ) * (Real.sqrt 2 : ℂ), 0, (3 / 2 : ℂ) * (Real.sqrt 2 : ℂ);
          0, 0, 0],
        !![(1 / 3 : ℂ), (1 / 4 : ℂ) * (Real.sqrt 2 : ℂ), (1 / 2 : ℂ);
          (1 / 4 : ℂ) * (Real.sqrt 2 : ℂ), (1 / 3 : ℂ), (1 / 4 : ℂ) * (Real.sqrt 2 : ℂ);
          (1 / 2 : ℂ), (1 / 4 : ℂ) * (Real.sqrt 2 : ℂ), (1 / 3 : ℂ)],
        !![(-3 / 2 : ℂ), 0, (3 / 2 : ℂ);
          0, 0, 0;
          (-3 / 2 : ℂ), 0, (3 / 2 : ℂ)]],
      ![!![(-1 / 2 : ℂ), (-3 / 4 : ℂ) * (Real.sqrt 2 : ℂ), 0;
          (3 / 4 : ℂ) * (Real.sqrt 2 : ℂ), 1, (3 / 4 : ℂ) * (Real.sqrt 2 : ℂ);
          0, (-3 / 4 : ℂ) * (Real.sqrt 2 : ℂ), (-1 / 2 : ℂ)],
        !![(-3 / 2 : ℂ), 0, (-3 / 2 : ℂ);
          0, 0, 0;
          (3 / 2 : ℂ), 0, (3 / 2 : ℂ)],
        !![(5 / 6 : ℂ), (-1 / 2 : ℂ) * (Real.sqrt 2 : ℂ), (1 / 2 : ℂ);
          (-1 / 2 : ℂ) * (Real.sqrt 2 : ℂ), (-2 / 3 : ℂ), (-1 / 2 : ℂ) * (Real.sqrt 2 : ℂ);
          (1 / 2 : ℂ), (-1 / 2 : ℂ) * (Real.sqrt 2 : ℂ), (5 / 6 : ℂ)]]]
  have heq : (∑ a, ∑ b, z p.1 p.2 a b *
      (∑ q : Fin 3 × Fin 3, c q •
        (star (baseKraus q.1) * baseKraus q.2)) a b) = c p := by
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      norm_num [z, baseKraus, Fintype.sum_prod_type, Fin.sum_univ_three,
        Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.vecMul_apply_eq_sum] <;>
      field_simp <;> ring_nf <;> norm_num [map_ofNat, htwo, hthree] <;> ring
  rw [hc] at heq
  simpa using heq.symm

set_option maxHeartbeats 2000000 in
-- The nine dual-coordinate identities expand finite matrix products over complex radicals.
private lemma base_right_independent : LinearIndependent ℂ
    (fun p : Fin 3 × Fin 3 => baseKraus p.1 * star (baseKraus p.2)) := by
  have htwo : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hthree : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hne : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))
  apply Fintype.linearIndependent_iff.mpr
  intro c hc p
  let z : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
    ![
      ![!![(5 / 6 : ℂ), (-1 / 2 : ℂ) * (Real.sqrt 2 : ℂ), (1 / 2 : ℂ);
          (-1 / 2 : ℂ) * (Real.sqrt 2 : ℂ), (-2 / 3 : ℂ), (-1 / 2 : ℂ) * (Real.sqrt 2 : ℂ);
          (1 / 2 : ℂ), (-1 / 2 : ℂ) * (Real.sqrt 2 : ℂ), (5 / 6 : ℂ)],
        !![(-3 / 2 : ℂ), 0, (-3 / 2 : ℂ);
          0, 0, 0;
          (3 / 2 : ℂ), 0, (3 / 2 : ℂ)],
        !![(1 / 2 : ℂ), (3 / 4 : ℂ) * (Real.sqrt 2 : ℂ), 0;
          (-3 / 4 : ℂ) * (Real.sqrt 2 : ℂ), -1, (-3 / 4 : ℂ) * (Real.sqrt 2 : ℂ);
          0, (3 / 4 : ℂ) * (Real.sqrt 2 : ℂ), (1 / 2 : ℂ)]],
      ![!![(-3 / 2 : ℂ), 0, (3 / 2 : ℂ);
          0, 0, 0;
          (-3 / 2 : ℂ), 0, (3 / 2 : ℂ)],
        !![(1 / 3 : ℂ), (1 / 4 : ℂ) * (Real.sqrt 2 : ℂ), (1 / 2 : ℂ);
          (1 / 4 : ℂ) * (Real.sqrt 2 : ℂ), (1 / 3 : ℂ), (1 / 4 : ℂ) * (Real.sqrt 2 : ℂ);
          (1 / 2 : ℂ), (1 / 4 : ℂ) * (Real.sqrt 2 : ℂ), (1 / 3 : ℂ)],
        !![0, 0, 0;
          (3 / 2 : ℂ) * (Real.sqrt 2 : ℂ), 0, (-3 / 2 : ℂ) * (Real.sqrt 2 : ℂ);
          0, 0, 0]],
      ![!![(1 / 2 : ℂ), (-3 / 4 : ℂ) * (Real.sqrt 2 : ℂ), 0;
          (3 / 4 : ℂ) * (Real.sqrt 2 : ℂ), -1, (3 / 4 : ℂ) * (Real.sqrt 2 : ℂ);
          0, (-3 / 4 : ℂ) * (Real.sqrt 2 : ℂ), (1 / 2 : ℂ)],
        !![0, (3 / 2 : ℂ) * (Real.sqrt 2 : ℂ), 0;
          0, 0, 0;
          0, (-3 / 2 : ℂ) * (Real.sqrt 2 : ℂ), 0],
        !![(-1 / 6 : ℂ), (1 / 4 : ℂ) * (Real.sqrt 2 : ℂ), -1;
          (1 / 4 : ℂ) * (Real.sqrt 2 : ℂ), (4 / 3 : ℂ), (1 / 4 : ℂ) * (Real.sqrt 2 : ℂ);
          -1, (1 / 4 : ℂ) * (Real.sqrt 2 : ℂ), (-1 / 6 : ℂ)]]]
  have heq : (∑ a, ∑ b, z p.1 p.2 a b *
      (∑ q : Fin 3 × Fin 3, c q •
        (baseKraus q.1 * star (baseKraus q.2))) a b) = c p := by
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      norm_num [z, baseKraus, Fintype.sum_prod_type, Fin.sum_univ_three,
        Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.vecMul_apply_eq_sum] <;>
      field_simp <;> ring_nf <;> norm_num [map_ofNat, htwo, hthree] <;> ring
  rw [hc] at heq
  simpa using heq.symm

private lemma base_decomposition :
    baseUnitary ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
    ∀ ρ, hmrChannel (1 / Real.sqrt 2) (1 / Real.sqrt 2) ρ =
      (1 / 4 : ℂ) • (star baseUnitary * ρ * baseUnitary) +
      (3 / 4 : ℂ) • krausChannel baseKraus ρ := by
  have htwo : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hthree : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hne : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))
  have hfour : (Real.sqrt 2 : ℂ) ^ 4 = 4 := by
    calc
      (Real.sqrt 2 : ℂ) ^ 4 = ((Real.sqrt 2 : ℂ) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [htwo]; norm_num
  have hnetwo : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
  constructor
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [baseUnitary, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.vecMul_apply_eq_sum] <;>
      ring_nf <;> norm_num [map_ofNat, htwo, hfour]
  · intro ρ
    rw [hmr_action, kraus_action]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [hmrKraus, baseKraus, baseUnitary, Matrix.mul_apply,
        Fin.sum_univ_three, Fin.sum_univ_four, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, Matrix.vecMul_apply_eq_sum] <;>
      field_simp <;> ring_nf <;> norm_num [map_ofNat, htwo, hthree, hfour] <;> ring

private lemma phase_parameters (α β : ℂ)
    (hα : ‖α‖ = 1 / Real.sqrt 2) (hβ : ‖β‖ = 1 / Real.sqrt 2) :
    ∃ r s : ℂ, ‖r‖ = 1 ∧ ‖s‖ = 1 ∧
      r * s ^ 2 = (Real.sqrt 2 : ℂ) * α ∧ r ^ 2 / s = (Real.sqrt 2 : ℂ) * β := by
  let u := (Real.sqrt 2 : ℂ) * α
  let v := (Real.sqrt 2 : ℂ) * β
  have hu : ‖u‖ = 1 := by
    dsimp only [u]
    rw [norm_mul, hα, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2)]
    exact mul_one_div_cancel (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  have hv : ‖v‖ = 1 := by
    dsimp only [v]
    rw [norm_mul, hβ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2)]
    exact mul_one_div_cancel (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (u * v ^ 2) (by decide : 0 < 5)
  have hrnorm : ‖r‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg r) (by decide : 5 ≠ 0)).mp
    rw [← norm_pow, hr, norm_mul, norm_pow, hu, hv]
    norm_num
  have hrne : r ≠ 0 := by intro hz; simp only [hz, norm_zero] at hrnorm; norm_num at hrnorm
  have hvne : v ≠ 0 := by intro hz; simp only [hz, norm_zero] at hv; norm_num at hv
  refine ⟨r, r ^ 2 / v, hrnorm, ?_, ?_, ?_⟩
  · rw [norm_div, norm_pow, hrnorm, hv]
    norm_num
  · change r * (r ^ 2 / v) ^ 2 = u
    field_simp
    linear_combination hr
  · change r ^ 2 / (r ^ 2 / v) = v
    field_simp

private lemma diagonal_unitary (r : ℂ) (hr : ‖r‖ = 1) :
    diagonalPhase r ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  have hstar : star r * r = 1 := by
    change starRingEnd ℂ r * r = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hr]
    norm_num
  have hrne : r ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hr
    norm_num at hr
  have hmem : r ∈ unitary ℂ :=
    (isUnit_iff_ne_zero.mpr hrne).mem_unitary_of_star_mul_self hstar
  change Matrix.diagonal ![r, 1, r⁻¹] ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ)
  rw [Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
  intro i
  fin_cases i
  · exact hmem
  · exact (unitary ℂ).one_mem
  · apply (isUnit_iff_ne_zero.mpr (inv_ne_zero hrne)).mem_unitary_of_star_mul_self
    calc
      star (r⁻¹) * r⁻¹ = (r * star r)⁻¹ := by rw [_root_.mul_inv_rev, star_inv₀]
      _ = 1 := by rw [mul_comm r, hstar, inv_one]

set_option maxHeartbeats 1000000 in
-- The phase identity expands the nine entries of two finite Kraus sums.
private lemma phase_reduction (α β : ℂ)
    (hα : ‖α‖ = 1 / Real.sqrt 2) (hβ : ‖β‖ = 1 / Real.sqrt 2) :
    ∃ r s : ℂ, diagonalPhase r ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
      diagonalPhase s ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
      hmrChannel α β = conjugateChannel (diagonalPhase r) (diagonalPhase s)
        (hmrChannel (1 / Real.sqrt 2) (1 / Real.sqrt 2)) := by
  obtain ⟨r, s, hr, hs, hαphase, hβphase⟩ := phase_parameters α β hα hβ
  refine ⟨r, s, diagonal_unitary r hr, diagonal_unitary s hs, ?_⟩
  have hrne : r ≠ 0 := by intro hz; rw [hz, norm_zero] at hr; norm_num at hr
  have hsne : s ≠ 0 := by intro hz; rw [hz, norm_zero] at hs; norm_num at hs
  have hrstar : (starRingEnd ℂ) r = r⁻¹ := by
    rw [← one_div r]
    apply (eq_div_iff hrne).mpr
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hr]
    norm_num
  have hsstar : (starRingEnd ℂ) s = s⁻¹ := by
    rw [← one_div s]
    apply (eq_div_iff hsne).mpr
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hs]
    norm_num
  have htwo : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hfour : (Real.sqrt 2 : ℂ) ^ 4 = 4 := by
    calc
      (Real.sqrt 2 : ℂ) ^ 4 = ((Real.sqrt 2 : ℂ) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [htwo]; norm_num
  have hnetwo : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
  have halpha : α = r * s ^ 2 / (Real.sqrt 2 : ℂ) := by
    apply (eq_div_iff hnetwo).mpr
    linear_combination -hαphase
  have hbeta : β = (r ^ 2 / s) / (Real.sqrt 2 : ℂ) := by
    apply (eq_div_iff hnetwo).mpr
    linear_combination -hβphase
  apply LinearMap.ext
  intro ρ
  rw [conjugate_action, hmr_action, hmr_action]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hmrKraus, diagonalPhase, halpha, hbeta, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_four, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.vecMul_apply_eq_sum, star_mul, star_div₀,
      star_pow, hrstar, hsstar] <;>
    field_simp <;> ring_nf <;> norm_num [map_ofNat, htwo, hfour] <;> ring

private lemma conjugate_cp (d e : Matrix (Fin 3) (Fin 3) ℂ)
    (φ : MatrixMap (Fin 3) (Fin 3) ℂ) (hφ : φ.IsCompletelyPositive) :
    (conjugateChannel d e φ).IsCompletelyPositive := by
  obtain ⟨k, hk⟩ := IsCompletelyPositive.exists_kraus φ hφ
  have heq : conjugateChannel d e φ =
      of_kraus (fun i => star e * k i * star d) (fun i => star e * k i * star d) := by
    apply LinearMap.ext
    intro ρ
    rw [conjugate_action, hk]
    unfold of_kraus
    simp only [LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mul_sum, Finset.sum_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [heq]
  exact of_kraus_isCompletelyPositive _

private lemma conjugate_unital (d e : Matrix (Fin 3) (Fin 3) ℂ)
    (hd : d ∈ Matrix.unitaryGroup (Fin 3) ℂ) (he : e ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (φ : MatrixMap (Fin 3) (Fin 3) ℂ) (hφ : IsUnital φ) :
    IsUnital (conjugateChannel d e φ) := by
  change conjugateChannel d e φ 1 = 1
  rw [conjugate_action, Matrix.mul_one, (Matrix.mem_unitaryGroup_iff').mp hd, hφ,
    Matrix.mul_one, (Matrix.mem_unitaryGroup_iff').mp he]

private lemma conjugate_tp (d e : Matrix (Fin 3) (Fin 3) ℂ)
    (hd : d ∈ Matrix.unitaryGroup (Fin 3) ℂ) (he : e ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (φ : MatrixMap (Fin 3) (Fin 3) ℂ) (hφ : IsTracePreserving φ) :
    IsTracePreserving (conjugateChannel d e φ) := by
  intro ρ
  rw [conjugate_action, Matrix.trace_mul_cycle, (Matrix.mem_unitaryGroup_iff).mp he,
    Matrix.one_mul, hφ, Matrix.trace_mul_cycle, (Matrix.mem_unitaryGroup_iff).mp hd,
    Matrix.one_mul]

private lemma conjugate_inverse (d e : Matrix (Fin 3) (Fin 3) ℂ)
    (hd : d ∈ Matrix.unitaryGroup (Fin 3) ℂ) (he : e ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (φ : MatrixMap (Fin 3) (Fin 3) ℂ) :
    conjugateChannel (star d) (star e) (conjugateChannel d e φ) = φ := by
  apply LinearMap.ext
  intro ρ
  rw [conjugate_action, conjugate_action, star_star, star_star]
  simp only [← Matrix.mul_assoc, (Matrix.mem_unitaryGroup_iff').mp hd,
    (Matrix.mem_unitaryGroup_iff).mp he, Matrix.one_mul]
  simp only [Matrix.mul_assoc, (Matrix.mem_unitaryGroup_iff').mp hd,
    (Matrix.mem_unitaryGroup_iff).mp he, Matrix.mul_one]

private lemma conjugate_extreme (d e : Matrix (Fin 3) (Fin 3) ℂ)
    (hd : d ∈ Matrix.unitaryGroup (Fin 3) ℂ) (he : e ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (p : MatrixMap (Fin 3) (Fin 3) ℂ → Prop)
    (hforward : ∀ φ, p φ → p (conjugateChannel d e φ))
    (hbackward : ∀ φ, p φ → p (conjugateChannel (star d) (star e) φ))
    (φ : MatrixMap (Fin 3) (Fin 3) ℂ) (hφ : φ ∈ Set.extremePoints ℝ {θ | p θ}) :
    conjugateChannel d e φ ∈ Set.extremePoints ℝ {θ | p θ} := by
  let f : (MatrixMap (Fin 3) (Fin 3) ℂ) ≃ₗ[ℝ] (MatrixMap (Fin 3) (Fin 3) ℂ) :=
    { toFun := conjugateChannel d e
      invFun := conjugateChannel (star d) (star e)
      left_inv := conjugate_inverse d e hd he
      right_inv := by
        intro θ
        simpa only [star_star] using
          conjugate_inverse (star d) (star e) (Unitary.star_mem hd) (Unitary.star_mem he) θ
      map_add' := by
        intro θ η
        apply LinearMap.ext
        intro ρ
        simp only [conjugate_action, LinearMap.add_apply, Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro t θ
        apply LinearMap.ext
        intro ρ
        simp only [conjugate_action, LinearMap.smul_apply, Matrix.mul_smul,
          Matrix.smul_mul, RingHom.id_apply] }
  have himage : f '' {θ | p θ} = {θ | p θ} := by
    ext θ
    constructor
    · rintro ⟨η, hη, rfl⟩
      exact hforward η hη
    · intro hθ
      refine ⟨f.symm θ, hbackward θ hθ, f.apply_symm_apply θ⟩
  have hx : f φ ∈ f '' Set.extremePoints ℝ {θ | p θ} := ⟨φ, hφ, rfl⟩
  rw [image_extremePoints f, himage] at hx
  exact hx

set_option maxHeartbeats 1000000 in
-- The Choi congruence expands four finite matrix-index sums.
private lemma conjugate_rank_le (d e : Matrix (Fin 3) (Fin 3) ℂ)
    (φ : MatrixMap (Fin 3) (Fin 3) ℂ) :
    (choi_matrix (conjugateChannel d e φ)).rank ≤ (choi_matrix φ).rank := by
  let q : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
    fun a b => star (e b.1 a.1) * star (d a.2 b.2)
  have hφ (x : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
      φ x i j = ∑ a, ∑ b, x a b * choi_matrix φ (i, a) (j, b) := by
    change φ x i j = of_choi_matrix (choi_matrix φ) x i j
    rw [choi_map_inv]
  have hsingle (i j : Fin 3) :
      star d * Matrix.single i j 1 * d = fun a b => star (d i a) * d j b := by
    ext a b
    change (∑ k : Fin 3, (∑ l : Fin 3,
      star (d l a) * Matrix.single i j (1 : ℂ) l k) * d k b) = _
    simp [Matrix.single_apply, ite_and]
  have hchoi : choi_matrix (conjugateChannel d e φ) = q * choi_matrix φ * qᴴ := by
    ext ⟨a, i⟩ ⟨c, j⟩
    change conjugateChannel d e φ (Matrix.single i j 1) a c = _
    rw [conjugate_action, hsingle i j]
    simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      hφ, Fintype.sum_prod_type, Fin.sum_univ_three]
    dsimp only [q]
    simp only [star_mul, star_star]
    ring
  rw [hchoi]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

private lemma conjugate_rank (d e : Matrix (Fin 3) (Fin 3) ℂ)
    (hd : d ∈ Matrix.unitaryGroup (Fin 3) ℂ) (he : e ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (φ : MatrixMap (Fin 3) (Fin 3) ℂ) :
    (choi_matrix (conjugateChannel d e φ)).rank = (choi_matrix φ).rank := by
  apply le_antisymm (conjugate_rank_le d e φ)
  have hle := conjugate_rank_le (star d) (star e) (conjugateChannel d e φ)
  rw [conjugate_inverse d e hd he φ] at hle
  exact hle

private lemma transport (d e u : Matrix (Fin 3) (Fin 3) ℂ)
    (φ ψ : MatrixMap (Fin 3) (Fin 3) ℂ)
    (hd : d ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (he : e ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hcp : ψ.IsCompletelyPositive) (hunit : IsUnital ψ) (htp : IsTracePreserving ψ)
    (hrank : (choi_matrix ψ).rank = 3)
    (hucp : ψ ∈ Set.extremePoints ℝ
      {θ : MatrixMap (Fin 3) (Fin 3) ℂ | θ.IsCompletelyPositive ∧ IsUnital θ})
    (hcpt : ψ ∈ Set.extremePoints ℝ
      {θ : MatrixMap (Fin 3) (Fin 3) ℂ |
        θ.IsCompletelyPositive ∧ IsTracePreserving θ})
    (hdec : ∀ ρ, φ ρ = (1 / 4 : ℂ) • (star u * ρ * u) + (3 / 4 : ℂ) • ψ ρ) :
    ∃ (v : Matrix (Fin 3) (Fin 3) ℂ) (η : MatrixMap (Fin 3) (Fin 3) ℂ),
      v ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧ η.IsCompletelyPositive ∧ IsUnital η ∧
      IsTracePreserving η ∧ (choi_matrix η).rank = 3 ∧
      η ∈ Set.extremePoints ℝ
        {θ : MatrixMap (Fin 3) (Fin 3) ℂ | θ.IsCompletelyPositive ∧ IsUnital θ} ∧
      η ∈ Set.extremePoints ℝ
        {θ : MatrixMap (Fin 3) (Fin 3) ℂ |
          θ.IsCompletelyPositive ∧ IsTracePreserving θ} ∧
      ∀ ρ, conjugateChannel d e φ ρ =
        (1 / 4 : ℂ) • (star v * ρ * v) + (3 / 4 : ℂ) • η ρ := by
  have hds := Unitary.star_mem hd
  have hes := Unitary.star_mem he
  refine ⟨d * u * e, conjugateChannel d e ψ,
    (Matrix.unitaryGroup (Fin 3) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin 3) ℂ).mul_mem hd hu) he,
    conjugate_cp d e ψ hcp, conjugate_unital d e hd he ψ hunit,
    conjugate_tp d e hd he ψ htp, ?_, ?_, ?_, ?_⟩
  · rw [conjugate_rank d e hd he ψ, hrank]
  · exact conjugate_extreme d e hd he _
      (fun θ hθ => ⟨conjugate_cp d e θ hθ.1, conjugate_unital d e hd he θ hθ.2⟩)
      (fun θ hθ => ⟨conjugate_cp (star d) (star e) θ hθ.1,
        conjugate_unital (star d) (star e) hds hes θ hθ.2⟩) ψ hucp
  · exact conjugate_extreme d e hd he _
      (fun θ hθ => ⟨conjugate_cp d e θ hθ.1, conjugate_tp d e hd he θ hθ.2⟩)
      (fun θ hθ => ⟨conjugate_cp (star d) (star e) θ hθ.1,
        conjugate_tp (star d) (star e) hds hes θ hθ.2⟩) ψ hcpt
  · intro ρ
    rw [conjugate_action, hdec, conjugate_action]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      star_mul, Matrix.mul_assoc]

/-- Every equal-modulus HMR channel has a unitary and doubly extreme decomposition. -/
theorem result : ∀ α β : ℂ, ‖α‖ = 1 / Real.sqrt 2 → ‖β‖ = 1 / Real.sqrt 2 →
    ∃ (u : Matrix (Fin 3) (Fin 3) ℂ) (lam : ℝ)
      (ψ : MatrixMap (Fin 3) (Fin 3) ℂ),
      u ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧ 0 ≤ lam ∧ lam ≤ 1 ∧
      ψ.IsCompletelyPositive ∧ IsUnital ψ ∧ IsTracePreserving ψ ∧
      (choi_matrix ψ).rank = 3 ∧
      ψ ∈ Set.extremePoints ℝ
        {θ : MatrixMap (Fin 3) (Fin 3) ℂ | θ.IsCompletelyPositive ∧ IsUnital θ} ∧
      ψ ∈ Set.extremePoints ℝ
        {θ : MatrixMap (Fin 3) (Fin 3) ℂ |
          θ.IsCompletelyPositive ∧ IsTracePreserving θ} ∧
      ∀ ρ, hmrChannel α β ρ = (lam : ℂ) • (star u * ρ * u) +
        ((1 - lam : ℝ) : ℂ) • ψ ρ := by
  intro α β hα hβ
  obtain ⟨r, s, hr, hs, hphase⟩ := phase_reduction α β hα hβ
  have hucp := extreme_ucp_of_independent baseKraus base_unital base_left_independent
  have hcpt := extreme_cpt_of_independent baseKraus base_trace base_right_independent
  have hprops := extremePoints_subset hcpt
  have hu := (extremePoints_subset hucp).2
  obtain ⟨u, ψ, hun, hcp, hunit, htp, hrank, hue, hte, hdec⟩ :=
    transport (diagonalPhase r) (diagonalPhase s) baseUnitary
      (hmrChannel (1 / Real.sqrt 2) (1 / Real.sqrt 2)) (krausChannel baseKraus)
      hr hs base_decomposition.1 hprops.1 hu hprops.2
      (choi_rank_of_independent baseKraus base_left_independent)
      hucp hcpt base_decomposition.2
  refine ⟨u, 1 / 4, ψ, hun, by norm_num, by norm_num,
    hcp, hunit, htp, hrank, hue, hte, ?_⟩
  intro ρ
  rw [hphase, hdec]
  norm_num

end D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition
