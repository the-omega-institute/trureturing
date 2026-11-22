/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/MatrixLift
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The singular four-spectral-value product bound from zero-centered kernel positivity. -/

import D5.S3.Quantum.Analysis.RefinedBMVExtremeWalk
import D5.S3.Quantum.Analysis.RefinedBMVIntervalKernel
import D5.S3.Quantum.Analysis.RefinedBMVThreeSpectrumCertificate

/-! The spectrum-local Schur walk for a singular PSD matrix with at most four
distinct eigenvalues, conditional on the zero-centered upper kernel. -/

open Matrix
open scoped ComplexOrder BigOperators MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace RefinedBMV.FourSpectrumLift

open ExtremeWalk (upperKernel centeredKernel defect_eq_cyclic_all)
open DimThree (defect defect_corner gaps mean_map trace_gap_all word_counts_all)
open UniformThreeSpectrum (defect_diag_all defect_nonneg_all)

universe u

section CenteredWalk

/-- Extend the actual upper block by zero and add the rank-one lower block. -/
private theorem centeredKernel_posSemidef_of_upper {n : Type u} [Finite n] {p : ℕ} (a : ℝ) (x : n → ℝ)
    (hUpper : (Matrix.of fun i j : {i // a < x i} ↦
      upperKernel p a (x i) (x j)).PosSemidef) :
    (Matrix.of fun i j ↦ centeredKernel p a (x i) (x j)).PosSemidef := by
  classical
  let := Fintype.ofFinite n
  let Above := {i // a < x i}
  let M : Matrix Above Above ℝ := Matrix.of fun i j ↦ upperKernel p a (x i) (x j)
  let E : Matrix n Above ℝ := Matrix.of fun i j ↦ if i = j.val then 1 else 0
  let v (i : n) : ℝ := if x i < a then √(defect p (x i) (x i) a) else 0
  have hsum_above (g : Above → ℝ) (i : n) :
      ∑ k, E i k * g k = if hi : a < x i then g ⟨i, hi⟩ else 0 := by
    split_ifs with hi
    · rw [Finset.sum_eq_single (⟨i, hi⟩ : Above)]
      · simp [E]
      · intro k _ hk
        have hne : i ≠ k.val := fun h ↦ hk (Subtype.ext h.symm)
        simp [E, hne]
      · simp
    · apply Finset.sum_eq_zero
      intro k _
      have hne : i ≠ k.val := fun h ↦ hi (h ▸ k.property)
      simp [E, hne]
  have hmul (C : Matrix Above n ℝ) (i j : n) :
      (E * C) i j = if hi : a < x i then C ⟨i, hi⟩ j else 0 :=
    hsum_above (fun k ↦ C k j) i
  have hright (i : Above) (j : n) :
      (M * Eᴴ) i j = if hj : a < x j then M i ⟨j, hj⟩ else 0 := by
    simpa only [mul_apply, conjTranspose_apply, star_trivial, mul_comm] using
      hsum_above (fun k ↦ M i k) j
  have hsum := (hUpper.mul_mul_conjTranspose_same E).add
    (posSemidef_vecMulVec_self_star v)
  change (E * M * Eᴴ + vecMulVec v (star v)).PosSemidef at hsum
  convert hsum using 1
  ext i j
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.mul_assoc, hmul, hright,
    vecMulVec_apply, star_trivial]
  by_cases hi : a < x i
  · by_cases hj : a < x j
    · simp [centeredKernel, hi, hj, M, v, not_lt_of_ge hi.le]
    · simp [centeredKernel, hi, hj, v, not_lt_of_ge hi.le]
  · by_cases hj : a < x j
    · simp [centeredKernel, hi, hj, v, not_lt_of_ge hj.le]
    · by_cases hli : x i < a <;> by_cases hlj : x j < a <;>
        simp [centeredKernel, hi, hj, hli, hlj, v]

variable {n : Type u} [Fintype n]

private theorem walk_defect_nonneg {p : ℕ}
    (a : n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hCentered : ∀ i, (Matrix.of fun j k ↦ centeredKernel p (a i) (a j) (a k)).PosSemidef)
    (B : Matrix n n ℂ) (hB : B.PosSemidef) :
    0 ≤ walk B (fun i j k ↦ ((defect p (a i) (a j) (a k) : ℝ) : ℂ)) := by
  classical
  let g : n → n → n → ℂ := fun i j k ↦ centeredKernel p (a i) (a j) (a k)
  have hg : 0 ≤ walk B g := by
    change 0 ≤ ∑ i, ∑ j, ∑ k, B i j * B j k * B k i * g i j k
    apply Finset.sum_nonneg
    intro i _
    let G : Matrix n n ℝ := Matrix.of fun j k ↦ centeredKernel p (a i) (a j) (a k)
    have hc := D5.S3.Weil.Probability.FiniteGaussianSchoenberg.ofReal_posSemidef G
      (hCentered i)
    have hSchur : (B ⊙ G.map Complex.ofReal).PosSemidef := hB.hadamard hc
    let v : n → ℂ := fun j ↦ B j i
    convert hSchur.dotProduct_mulVec_nonneg v using 1
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    have hstar : star (B j i) = B i j := congrFun (congrFun hB.isHermitian i) j
    simp only [Pi.star_apply, v, hstar, hadamard_apply, Matrix.map_apply, G,
      Matrix.of_apply, g]
    ring
  have h : (fun i j k ↦ ((defect p (a i) (a j) (a k) : ℝ) : ℂ)) =
      g + (fun i j k ↦ g j k i) + (fun i j k ↦ g k i j) := by
    funext i j k
    simp only [Pi.add_apply, g]
    exact_mod_cast defect_eq_cyclic_all p (a i) (a j) (a k) (ha i) (ha j) (ha k)
  rw [h, map_add, map_add, walk_rotate B (fun i j k ↦ g j k i), walk_rotate B g]
  exact add_nonneg (add_nonneg hg hg) hg

variable [DecidableEq n]

/-- Centered positivity on the given diagonal sample suffices for the trace-word comparison. -/
private theorem diagonal_bound_of_centered {p : ℕ}
    (a : n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hCentered : ∀ i, (Matrix.of fun j k ↦ centeredKernel p (a i) (a j) (a k)).PosSemidef)
    (B : Matrix n n ℂ) (hB : B.PosSemidef) :
    trace (((diagonal fun i ↦ (a i : ℂ)) ^ p * B) ^ 3) ≤
      DimThree.wordMean p ((diagonal fun i ↦ (a i : ℂ)) ^ 3) B := by
  have hn := walk_defect_nonneg a ha hCentered B hB
  rw [← trace_gap_all p] at hn
  have hlen : (0 : ℝ) < (gaps p).length := by exact_mod_cast (word_counts_all p).2.1
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hn
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    Complex.sub_re, Complex.sub_im, zero_mul, sub_zero, add_zero] at hre him
  exact Complex.le_def.mpr ⟨sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hlen).mp hre),
    (sub_eq_zero.mp (mul_eq_zero.mp him.symm |>.resolve_left hlen.ne')).symm⟩

end CenteredWalk

/-- The upper kernel at center zero is PSD on every finite sample of positive roots. -/
def ZeroUpperPSD (p : ℕ) : Prop :=
  ∀ {ι : Type u} [Fintype ι] (x : ι → ℝ), (∀ i, 0 < x i) →
    (Matrix.of fun i j ↦ upperKernel p 0 (x i) (x j)).PosSemidef

private theorem upperKernel_diag (p : ℕ) (a x : ℝ) :
    upperKernel p a x x = defect p a x x := by
  simp [upperKernel, defect_diag_all]

private theorem upperKernel_bounds {p : ℕ} (hp : 0 < p) {a x y : ℝ}
    (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    0 ≤ upperKernel p a x y ∧
      upperKernel p a x y ≤ √(defect p a x x * defect p a y y) := by
  have hx := ha.trans hax
  have hy := hx.trans hxy
  let q := defect p a a y * defect p x x y
  let w := defect p a x x * defect p a y y
  let d := defect p a x y
  have hq : 0 ≤ q := mul_nonneg (defect_nonneg_all p _ _ _ ha ha hy)
    (defect_nonneg_all p _ _ _ hx hx hy)
  have hw : 0 ≤ w := mul_nonneg (defect_nonneg_all p _ _ _ ha hx hx)
    (defect_nonneg_all p _ _ _ ha hy hy)
  have hd : 0 ≤ d := defect_nonneg_all p _ _ _ ha hx hy
  have hcorner : √q ≤ d := defect_corner p ha hx hy
  have hquartic := DividedDifference.ordered_quartic_nonneg p hp ha hax hxy
  change 0 ≤ 4 * q * w - (d ^ 2 - q - w) ^ 2 at hquartic
  have hsq : (d ^ 2 - q - w) ^ 2 ≤ (2 * √q * √w) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hq, Real.sq_sqrt hw]
    linarith
  have hcross : d ^ 2 - q - w ≤ 2 * √q * √w :=
    (le_abs_self _).trans ((sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
      (by rwa [sq_abs]))
  have hbound : d ≤ √q + √w := by
    apply (sq_le_sq₀ hd (by positivity)).mp
    nlinarith [Real.sq_sqrt hq, Real.sq_sqrt hw]
  simp only [upperKernel, min_eq_left hxy, max_eq_right hxy]
  refine ⟨sub_nonneg.mpr hcorner, ?_⟩
  change d - √q ≤ √w
  linarith

private theorem two_by_two_posSemidef {d e m : ℝ}
    (hd : 0 ≤ d) (he : 0 ≤ e) (hm : 0 ≤ m) (hm' : m ≤ √(d * e)) :
    (Matrix.of fun i j : Fin 2 ↦ if i = j then (if i = 0 then d else e) else m).PosSemidef := by
  let t := √d * √e
  let ρ := m / t
  have ht : 0 ≤ t := by positivity
  have hmt : m ≤ t := by rwa [Real.sqrt_mul hd] at hm'
  have hρ : 0 ≤ ρ := div_nonneg hm ht
  have hρ' : ρ ≤ 1 := div_le_one_of_le₀ hmt ht
  have htm : t * ρ = m := by
    by_cases hz : t = 0
    · have hm0 : m = 0 := le_antisymm (hz ▸ hmt) hm
      simp [hz, hm0]
    · exact mul_div_cancel₀ m hz
  -- Zero boundary rows and columns leave the normalized two-value kernel.
  let C (i j : ℕ) : ℝ := if i = 0 ∨ j = 3 then 0 else if i = j then 1 else ρ
  have hC := IntervalKernel.posSemidef_truncation (𝕜 := ℝ) (n := 2) C (by
    intro i j hij hj
    rcases (show i = 0 ∧ j = 0 ∨ i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 1 by omega) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num [C] <;> linarith)
  have hmix₁ : √d * ρ * √e = m := by
    calc
      _ = t * ρ := by
        dsimp [t]
        ring
      _ = m := htm
  have hmix₂ : √e * ρ * √d = m := by
    convert hmix₁ using 1
    ring
  let v (i : Fin 2) := if i = 0 then √d else √e
  have h := hC.mul_mul_conjTranspose_same (diagonal v)
  rw [diagonal_conjTranspose] at h
  convert h using 1
  ext i j
  simp only [mul_diagonal, diagonal_mul, Matrix.of_apply, star_trivial]
  fin_cases i <;> fin_cases j <;>
    norm_num [C, v, Fin.val_zero, Fin.val_one, ← pow_two,
      Real.sq_sqrt hd, Real.sq_sqrt he, hmix₁, hmix₂]

private theorem upperKernel_posSemidef_of_card_le_two {p : ℕ} (hp : 0 < p)
    {ι : Type u} [Fintype ι] (a : ℝ) (ha : 0 ≤ a) (x : ι → ℝ) (hax : ∀ i, a < x i)
    (hs : (Finset.univ.image x).card ≤ 2) :
    (Matrix.of fun i j ↦ upperKernel p a (x i) (x j)).PosSemidef := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · let := hι
    have he : (Matrix.of fun i j ↦ upperKernel p a (x i) (x j)) = 0 := by
      ext i j
      exact isEmptyElim i
    rw [he]
    exact Matrix.PosSemidef.zero
  obtain ⟨i₀⟩ := hι
  let S := Finset.univ.image x
  have hmem (i : ι) : x i ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hS : S.Nonempty := ⟨x i₀, hmem i₀⟩
  let l := S.min' hS
  let r := S.max' hS
  have hl : l ∈ S := S.min'_mem hS
  have hr : r ∈ S := S.max'_mem hS
  have hlr : l ≤ r := S.min'_le _ hr
  have hal : a < l := by
    obtain ⟨i, _, h⟩ := Finset.mem_image.mp hl
    exact h ▸ hax i
  have hvalues (i : ι) : x i = l ∨ x i = r := by
    by_cases h : l = r
    · exact Or.inl (le_antisymm ((S.le_max' _ (hmem i)).trans h.ge) (S.min'_le _ (hmem i)))
    · have hpair : {l, r} = S := Finset.eq_of_subset_of_card_le
        (by simp [Finset.insert_subset_iff, hl, hr]) (by simpa [Finset.card_pair h] using hs)
      simpa [← hpair] using hmem i
  let f (i : ι) : Fin 2 := if x i = l then 0 else 1
  let y (i : Fin 2) := if i = 0 then l else r
  have hy (i : ι) : y (f i) = x i := by
    rcases hvalues i with hi | hi
    · simp [y, f, hi]
    · by_cases h : x i = l
      · simp [y, f, h]
      · dsimp only [f]
        rw [if_neg h]
        simpa [y] using hi.symm
  have hl₀ := ha.trans hal.le
  have hr₀ := hl₀.trans hlr
  obtain ⟨hm, hm'⟩ := upperKernel_bounds hp ha hal.le hlr
  have hGram := two_by_two_posSemidef
    (defect_nonneg_all p _ _ _ ha hl₀ hl₀) (defect_nonneg_all p _ _ _ ha hr₀ hr₀) hm hm'
  have hGram_eq : (Matrix.of fun i j : Fin 2 ↦ upperKernel p a (y i) (y j)) =
      Matrix.of (fun i j : Fin 2 ↦
        if i = j then (if i = 0 then defect p a l l else defect p a r r) else upperKernel p a l r) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [y, upperKernel_diag]
    simp only [upperKernel, min_comm r l, max_comm r l]
  rw [← hGram_eq] at hGram
  convert hGram.submatrix f using 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, hy]

variable {n : Type u} [Fintype n]

/-- Centered PSD on a nonnegative finite sample containing zero and at most four values. -/
theorem centered_posSemidef {p : ℕ} (hp : 0 < p) (hZero : ZeroUpperPSD.{u} p)
    (x : n → ℝ) (hx : ∀ i, 0 ≤ x i) (hz : 0 ∈ Finset.univ.image x)
    (hs : (Finset.univ.image x).card ≤ 4) (i : n) :
    (Matrix.of fun j k ↦ centeredKernel p (x i) (x j) (x k)).PosSemidef := by
  classical
  apply centeredKernel_posSemidef_of_upper
  let y (j : {j // x i < x j}) := x j.val
  change (Matrix.of fun j k ↦ upperKernel p (x i) (y j) (y k)).PosSemidef
  rcases (hx i).eq_or_lt with hi | hi
  · have h := hZero y (fun j ↦ by simpa only [hi] using j.property)
    convert h using 1
    ext j k
    simp only [Matrix.of_apply, hi]
  · let S := Finset.univ.image x
    have hxi : x i ∈ S.erase 0 :=
      Finset.mem_erase.mpr ⟨hi.ne', Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    have hsub : Finset.univ.image y ⊆ (S.erase 0).erase (x i) := by
      intro v hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_erase.mpr ⟨j.property.ne', Finset.mem_erase.mpr
        ⟨(hi.trans j.property).ne', Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hxi, Finset.card_erase_of_mem hz] at hcard
    exact upperKernel_posSemidef_of_card_le_two hp _ (hx i) y Subtype.property (by omega)

variable [DecidableEq n]

/-- The all-degree refined BMV product bound for a singular PSD first factor with
at most four distinct eigenvalues, given PSD of the zero-centered upper kernel. -/
theorem product_bound_singular {p : ℕ} (hp : 0 < p) (hZero : ZeroUpperPSD.{u} p)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hSing : A.det = 0) (hs : (Finset.univ.image hA.isHermitian.eigenvalues).card ≤ 4) :
    trace (((A ^ ((p : ℝ) / 3)) * B) ^ 3) ≤ DimThree.wordMean p A B := by
  let H := hA.isHermitian
  let U := H.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℂ _ (star U)
  let x (i : n) := H.eigenvalues i ^ (1 / 3 : ℝ)
  let D := diagonal fun i ↦ (x i : ℂ)
  have hx (i : n) : 0 ≤ x i := Real.rpow_nonneg (hA.eigenvalues_nonneg i) _
  have hxs : (Finset.univ.image x).card ≤ 4 := by
    rw [show x = (fun t : ℝ ↦ t ^ (1 / 3 : ℝ)) ∘ H.eigenvalues from rfl, ← Finset.image_image]
    exact Finset.card_image_le.trans hs
  have hxz : 0 ∈ Finset.univ.image x := by
    rw [H.det_eq_prod_eigenvalues, Finset.prod_eq_zero_iff] at hSing
    obtain ⟨i, _, hi⟩ := hSing
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩
    have he : H.eigenvalues i = 0 := (RCLike.ofReal_eq_zero (K := ℂ)).mp hi
    simp [x, he]
  have hB' : (f B).PosSemidef := by
    change (Unitary.conjStarAlgAut ℂ _ (star U) B).PosSemidef
    rw [Unitary.conjStarAlgAut_star_apply]
    exact hB.conjTranspose_mul_mul_same (U : Matrix n n ℂ)
  have hd : f A = D ^ 3 := by
    rw [H.conjStarAlgAut_star_eigenvectorUnitary, diagonal_pow]
    congr 1
    funext i
    change (H.eigenvalues i : ℂ) = (x i : ℂ) ^ 3
    dsimp only [x]
    rw [← Complex.ofReal_pow, Complex.ofReal_inj,
      ← Real.rpow_mul_natCast (hA.eigenvalues_nonneg i)]
    norm_num
  have hpow : f (A ^ ((p : ℝ) / 3)) = D ^ p := by
    rw [CFC.rpow_eq_cfc_real hA.nonneg, H.cfc_eq, Matrix.IsHermitian.cfc]
    have hf : f.symm = Unitary.conjStarAlgAut ℂ _ U := by simp [f]
    change f (Unitary.conjStarAlgAut ℂ _ U _) = _
    rw [← hf, StarAlgEquiv.apply_symm_apply, diagonal_pow]
    congr 1
    funext i
    change ((H.eigenvalues i ^ ((p : ℝ) / 3) : ℝ) : ℂ) = (x i : ℂ) ^ p
    dsimp only [x]
    rw [← Complex.ofReal_pow, Complex.ofReal_inj,
      ← Real.rpow_mul_natCast (hA.eigenvalues_nonneg i)]
    congr 1
    ring
  have h := diagonal_bound_of_centered x hx (centered_posSemidef hp hZero x hx hxz hxs) (f B) hB'
  change trace ((D ^ p * f B) ^ 3) ≤ DimThree.wordMean p (D ^ 3) (f B) at h
  rw [← hd, ← hpow, ← map_mul f, ← map_pow f, trace_conjugation] at h
  exact h.trans_eq (mean_map p f.toAlgEquiv (trace_conjugation (star U)) A B)

#print axioms product_bound_singular

end RefinedBMV.FourSpectrumLift
