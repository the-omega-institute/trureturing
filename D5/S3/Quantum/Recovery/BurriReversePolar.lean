/- GID: D5/S3/Quantum/Recovery/BurriReversePolar
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/BurriReversePolar
   mirror-E: none(waiver:unfinished-actual-decoder-comparison)
   anchors: []
   utility: none
   digest: Exact radical parameters and positive right-polar blocks. -/

import D5.S3.Quantum.Recovery.BurriReverseDecoder
import D5.S3.Quantum.Matrix.SpectralPower

/-! Exact radical block congruences and an active source-ordered SVD. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Matrix.SpectralPower
open D5.S3.Quantum.Recovery.BurriReverseDecoder

namespace D5.S3.Quantum.Recovery.BurriReversePolar

def s : ℝ := Real.sqrt 11
def t : ℝ := Real.sqrt 10
def den (l : ℝ) : ℝ := Real.sqrt ((l * s + 3 * t) ^ 2 + (s - t) ^ 2)
def cosine (l : ℝ) : ℝ := (l * s + 3 * t) / den l
def sine (l : ℝ) : ℝ := (s - t) / den l
def U : Matrix B B ℂ := activeU (cosine 4) (cosine 2) (sine 4) (sine 2)

private theorem root_facts : s ^ 2 = 11 ∧ t ^ 2 = 10 ∧ 0 < t ∧ t < s := by
  have hs : s ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have ht : t ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have hp : 0 < t := Real.sqrt_pos.2 (by norm_num)
  have hn : 0 ≤ s := Real.sqrt_nonneg _
  exact ⟨hs, ht, hp, by nlinarith⟩

theorem den_positive (l : ℝ) : 0 < den l := by
  apply Real.sqrt_pos.2
  have h := root_facts.2.2.2
  nlinarith [sq_nonneg (l * s + 3 * t), sq_pos_of_pos (sub_pos.mpr h)]

theorem parameters (l : ℝ) : cosine l ^ 2 + sine l ^ 2 = 1 ∧ 0 < sine l := by
  have hd := den_positive l
  have hsq : den l ^ 2 = (l * s + 3 * t) ^ 2 + (s - t) ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  constructor
  · unfold cosine sine
    field_simp
    nlinarith
  · exact div_pos (sub_pos.mpr root_facts.2.2.2) hd

theorem actual_unitary : Uᴴ * U = 1 ∧ U * Uᴴ = 1 :=
  rotation_unitary _ _ _ _ (parameters 4).1 (parameters 2).1

theorem actual_polynomial_gap :
    0 < 108 - ((4 * cosine 4 + 2 * cosine 2 + sine 4 + sine 2) ^ 2 + 36 +
      (3 * cosine 4 + 3 * cosine 2 - (sine 4 + sine 2)) ^ 2) :=
  gap_positive _ _ _ _ (parameters 4).1 (parameters 2).1
    (add_pos (parameters 4).2 (parameters 2).2)

/-- The two literal two-dimensional source blocks, with the positive scalar omitted. -/
def block (l c k : ℝ) : Matrix A A ℂ :=
  !![(l * s : ℝ), t; s, 3 * t] * !![(c : ℝ), k; -k, c] |>.map (algebraMap ℝ ℂ)

def lead (l : ℝ) : ℝ :=
  (l ^ 2 * s ^ 2 + (3 * l - 1) * s * t + t ^ 2) / den l
def offdiag (l : ℝ) : ℝ := (l * s ^ 2 + 3 * t ^ 2) / den l
def trailing (l : ℝ) : ℝ :=
  (s ^ 2 + (3 * l - 1) * s * t + 9 * t ^ 2) / den l

set_option maxHeartbeats 2000000 in
-- The explicit matrix entries reduce to polynomial identities.
theorem block_symmetric (l : ℝ) :
    block l (cosine l) (sine l) =
      !![(lead l : ℂ), (offdiag l : ℂ); (offdiag l : ℂ), (trailing l : ℂ)] := by
  have hn := ne_of_gt (den_positive l)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, cosine, sine, lead, offdiag, trailing, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.map_apply]
  all_goals push_cast; field_simp; ring

theorem block_determinant (l : ℝ) :
    lead l * trailing l - offdiag l ^ 2 = (3 * l - 1) * s * t := by
  have hn := ne_of_gt (den_positive l)
  have hsq : den l ^ 2 = (l * s + 3 * t) ^ 2 + (s - t) ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  unfold lead trailing offdiag
  rw [div_mul_div_comm, div_pow, ← pow_two, ← sub_div]
  apply (div_eq_iff (pow_ne_zero 2 hn)).mpr
  rw [hsq]
  ring

theorem block_positive (l : ℝ) (hl : 2 ≤ l) :
    (block l (cosine l) (sine l)).PosDef := by
  obtain ⟨hs, ht, htpos, hst⟩ := root_facts
  have hspos : 0 < s := lt_trans htpos hst
  have hcoef : 0 < 3 * l - 1 := by linarith
  rw [block_symmetric]
  apply posDef_two
  · unfold lead
    apply div_pos _ (den_positive l)
    positivity
  · rw [block_determinant]
    positivity

/-- Unnormalized Hadamard columns for each coupled source block. -/
def columns (z : ℝ) : Matrix B A ℂ := fun p j =>
  if j = 0 then
    if p.2 = 0 then (if p.1 = 0 then 1 else (z : ℂ)) else 0
  else if p.2 = 2 then (if p.1 = 0 then 1 else -(z : ℂ)) else 0
def middleColumns : Matrix B A ℂ := fun p j => if p = (j, 1) then 1 else 0
def middleBlock : Matrix A A ℂ :=
  !![3 * (t : ℂ), -(t : ℂ); -(t : ℂ), 3 * (t : ℂ)]
def activeM : Matrix B B ℂ :=
  (1 / 62 : ℂ) • (Y * Matrix.diagonal (fun p => if p.2 = 0 then (s : ℂ) else t))

set_option maxHeartbeats 2000000 in
-- The explicit matrix entries reduce to polynomial identities.
theorem polar_decomposition (cp cm kp km : ℝ) :
    activeM * activeU cp cm kp km =
      (1 / 124 : ℂ) •
        (columns 1 * block 4 cp kp * (columns 1)ᴴ +
          columns (-1) * block 2 cm km * (columns (-1))ᴴ) +
      (1 / 62 : ℂ) • (middleColumns * middleBlock * middleColumnsᴴ) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
    norm_num [activeM, activeU, BurriReverseDecoder.rotation, sign, Y, amplitude, columns,
      middleColumns, middleBlock, block, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
      Complex.ext_iff, Complex.div_re, Complex.div_im]
  all_goals ring

theorem actual_polar_positive : (activeM * U).PosSemidef := by
  rw [U, polar_decomposition]
  have hp := (block_positive 4 (by norm_num)).posSemidef.mul_mul_conjTranspose_same (columns 1)
  have hm := (block_positive 2 (by norm_num)).posSemidef.mul_mul_conjTranspose_same (columns (-1))
  have htpos : 0 < t := root_facts.2.2.1
  have ht : middleBlock.PosSemidef := by
    have h := posDef_two (3 * t) (-t) (3 * t)
      (by positivity : 0 < 3 * t) (by nlinarith [root_facts.2.1] : 0 < 3 * t * (3 * t) - (-t) ^ 2)
    simpa [middleBlock] using h.posSemidef
  exact ((hp.add hm).smul (by norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im])).add
    ((ht.mul_mul_conjTranspose_same middleColumns).smul
      (by norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im]))

/-- An actual nonnegative SVD in the source right-polar convention on the active block. -/
theorem active_svd :
    ∃ H T : Matrix.unitaryGroup B ℂ, ∃ v : B → ℝ,
      (∀ i, 0 ≤ v i) ∧
      activeM = (H : Matrix B B ℂ) * Matrix.diagonal (fun i => (v i : ℂ)) * T ∧
      U = (T : Matrix B B ℂ)ᴴ * (H : Matrix B B ℂ)ᴴ := by
  let h := actual_polar_positive.isHermitian
  let H := h.eigenvectorUnitary
  let u : Matrix.unitaryGroup B ℂ := ⟨U, by
    simpa only [Unitary.mem_iff, star_eq_conjTranspose] using actual_unitary⟩
  have hd : Matrix.diagonal (RCLike.ofReal ∘ h.eigenvalues) =
      Matrix.diagonal (fun i => (h.eigenvalues i : ℂ)) := by
    ext i j
    simp [Matrix.diagonal_apply, Function.comp_apply, RCLike.ofReal_eq_complex_ofReal]
  have hspec : activeM * U = (H : Matrix B B ℂ) *
      Matrix.diagonal (fun i => (h.eigenvalues i : ℂ)) * (H : Matrix B B ℂ)ᴴ := by
    have hs : activeM * U = (H : Matrix B B ℂ) *
        Matrix.diagonal (RCLike.ofReal ∘ h.eigenvalues) * (H : Matrix B B ℂ)ᴴ := by
      simpa only [Unitary.conjStarAlgAut_apply, H, star_eq_conjTranspose]
        using h.spectral_theorem
    exact hs.trans (congrArg
      (fun D : Matrix B B ℂ => (H : Matrix B B ℂ) * D * (H : Matrix B B ℂ)ᴴ) hd)
  refine ⟨H, star H * star u, h.eigenvalues,
    actual_polar_positive.eigenvalues_nonneg, ?_, ?_⟩
  · change activeM = (H : Matrix B B ℂ) * _ * ((H : Matrix B B ℂ)ᴴ * Uᴴ)
    calc
      activeM = (activeM * U) * Uᴴ := by
        rw [Matrix.mul_assoc, actual_unitary.2, Matrix.mul_one]
      _ = _ := (congrArg (fun Z : Matrix B B ℂ => Z * Uᴴ) hspec).trans
        (Matrix.mul_assoc _ _ _)
  · change U = ((H : Matrix B B ℂ)ᴴ * Uᴴ)ᴴ * (H : Matrix B B ℂ)ᴴ
    have hh : (H : Matrix B B ℂ) * (H : Matrix B B ℂ)ᴴ = 1 := by
      simpa only [star_eq_conjTranspose] using H.prop.2
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hh, Matrix.mul_one]

#print axioms actual_unitary
#print axioms actual_polynomial_gap
#print axioms actual_polar_positive
#print axioms active_svd

end D5.S3.Quantum.Recovery.BurriReversePolar
