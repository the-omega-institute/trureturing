/- GID: D5/S3/Quantum/Analysis/RefinedBMVUniformThreeSpectrum
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The trace comparison from scalar pairing at every first degree. -/

import D5.S3.Quantum.Analysis.RefinedBMVThreeSpectralValues
import D5.S3.Quantum.Analysis.RefinedBMVUniformWords

/-! The matrix comparison from scalar pairing at arbitrary degree. -/

open Matrix NormedSpace
open scoped ComplexOrder BigOperators MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace RefinedBMV.UniformThreeSpectrum

open ThreeSpectralValues (operator_walk_nonneg trace_exp_le_cube)
open DimThree (defect paired gaps mean_map trace_gap_all word_counts_all)

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem defect_cycle_all (p : ℕ) (a x y : ℝ) :
    defect p x y a = defect p a x y := by
  let f (g : ℕ × ℕ × ℕ) := (x ^ 3) ^ g.1 * (y ^ 3) ^ g.2.1 * (a ^ 3) ^ g.2.2
  have h := ((DimThree.gaps_cycle_all p).map f).sum_eq
  simp only [List.map_map] at h
  unfold defect
  congr 1
  · change ((gaps p).map f).sum = _
    rw [← h]
    congr 1
    apply List.map_congr_left
    intro g _
    dsimp [f]
    ring
  · rw [show x * y * a = a * x * y by ring]

/-- The defect vanishes when all three roots coincide. -/
theorem defect_diag_all (p : ℕ) (a : ℝ) : defect p a a a = 0 := by
  unfold defect
  have h : ((gaps p).map fun g =>
      (a ^ 3) ^ g.1 * (a ^ 3) ^ g.2.1 * (a ^ 3) ^ g.2.2) =
        (gaps p).map (fun _ => (a ^ 3) ^ p) := by
    refine List.map_congr_left fun g hg => ?_
    rw [← pow_add, ← pow_add, (DimThree.mem_gaps_iff_total p g).mp hg]
  rw [h, List.map_const', List.sum_replicate, nsmul_eq_mul]
  rw [show a * a * a = a ^ 3 by ring, sub_self]

/-- The scalar corner inequality implies nonnegativity of the defect. -/
theorem defect_nonneg_all (p : ℕ) (a x y : ℝ)
    (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ defect p a x y := (Real.sqrt_nonneg _).trans (DimThree.defect_corner p ha hx hy)

/-- Uniform matrix lift from the scalar pairing, to be used by the all-degree certificate. -/
def ScalarPairing (p : ℕ) : Prop :=
  ∀ a x y : ℝ, 0 ≤ a → 0 ≤ x → 0 ≤ y → defect p a x y ≤ paired (defect p) a x y

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

private theorem diagonal_bound {p : ℕ} (hp : ScalarPairing p)
    (hswap : ∀ (a x y : ℝ), defect p x a y = defect p a x y)
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
    (fun i j k ↦ defect_nonneg_all p _ _ _ (ha i) (ha j) (ha k))
    (defect_diag_all p) hswap (defect_cycle_all p)
    (hp _ _ _ (ha 0) (ha 1) (ha 2))
  rw [← compressed_walk B hB label
    (fun i j k ↦ ((DimThree.defect p (a i) (a j) (a k) : ℝ) : ℂ)), ← trace_gap_all p] at hn
  have hlen : (0 : ℝ) < (DimThree.gaps p).length := by exact_mod_cast (word_counts_all p).2.1
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

/-- The refined BMV product bound for an arbitrary first degree, given scalar pairing.
The first PSD matrix has at most three distinct eigenvalues. -/
theorem product_bound {p : ℕ} (hp : ScalarPairing p)
    (hswap : ∀ (a x y : ℝ), defect p x a y = defect p a x y)
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
  have h := diagonal_bound hp hswap x (fun i ↦ Real.rpow_nonneg (ha₀ i) _) label (f B) hB'
  change trace ((D ^ p * f B) ^ 3) ≤ DimThree.wordMean p (D ^ 3) (f B) at h
  rw [← hd, ← hpow, ← map_mul f, ← map_pow f, trace_conjugation] at h
  exact h.trans_eq (mean_map p f.toAlgEquiv (trace_conjugation (star U)) A B)

/-- The refined BMV exponential lower bound from scalar pairing,
when the first Hermitian matrix has at most three distinct eigenvalues. -/
theorem exponential_bound {p : ℕ} (hp : ScalarPairing p)
    (hswap : ∀ (a x y : ℝ), defect p x a y = defect p a x y)
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
  have h := diagonal_bound hp hswap x (fun i ↦ (Real.exp_pos _).le) label (f (exp K)) hB'
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

#print axioms product_bound
#print axioms exponential_bound

end RefinedBMV.UniformThreeSpectrum
