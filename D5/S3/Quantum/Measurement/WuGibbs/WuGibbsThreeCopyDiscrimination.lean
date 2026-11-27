/- GID: D5/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/WuGibbs/WuGibbsThreeCopyDiscrimination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact three-copy Helstrom bias exceeds every first-qubit PPT payoff for mixed Wu Gibbs rotations with positive Bloch coordinates. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation
import D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
import D5.S3.Quantum.Matrix.SpectralPower
import D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound
import OmegaBuild.Commands

/-! Exact three-copy discrimination for the active qubit of the Wu Gibbs rotation.
The Dicke subspace and two alternating-pair subspaces give the positive and negative
parts of the density difference. The fixed-cut comparison is with the numerical
PPT comparison in Conlon et al., arXiv:2408.06678. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination

open _root_.Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_sub_orthogonal)
open D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite (partialTranspose)
open D5.S3.Quantum.Matrix.SpectralPower (posDef_two)
open D5.S3.Quantum.Matrix.AbedNikolaevaNovikovAFDensityBound (trace_pair_pos)

abbrev Qubits := Fin 2 × (Fin 2 × Fin 2)
abbrev Mat := Matrix Qubits Qubits ℂ
private abbrev Q (R : Type) := Matrix (Fin 2) (Fin 2) R
private abbrev Parity := Fin 2 ⊕ Fin 2
private abbrev Blocks := Parity ⊕ Parity

private def a (z : ℝ) : ℝ := (1 + z) / 2
private def d (z : ℝ) : ℝ := (1 - z) / 2
private def b (x : ℝ) : ℝ := x / 2
private def raw (a d b : ℝ) : Q ℝ := !![a, b; b, d]

private abbrev complexify {m n : Type} (A : Matrix m n ℝ) : Matrix m n ℂ :=
  A.map Complex.ofReal

/-- The qubit `(I + z Z + x X) / 2` in the active computational basis. -/
def qubit (x z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  complexify (raw (a z) (d z) (b x))

/-- Three independent copies, with the first qubit on the first product factor. -/
def threeCopy (x z : ℝ) : Mat := qubit x z ⊗ₖ (qubit x z ⊗ₖ qubit x z)

/-- The difference of the two normalized three-copy hypotheses. -/
def difference (x z : ℝ) : Mat := threeCopy x z - threeCopy (-x) z

private def computationalIndex : Qubits ≃ Fin 8 :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv

private def blockIndex : Blocks ≃ Fin 8 :=
  (Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv

private def basisTable (r s : ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, r, 0, s, 0, r * s, 0;
     0, 0, r, 0, -s, 0, r * s, 0;
     0, r, 0, 0, 0, 0, 0, 2 * r * s;
     0, 0, r, 0, 0, 0, -2 * r * s, 0;
     0, r, 0, 0, 0, s, 0, -r * s;
     0, r, 0, 0, 0, -s, 0, -r * s;
     0, 0, 0, 1, 0, 0, 0, 0]

private def splitBasis (r s : ℝ) : Matrix Qubits Blocks ℝ :=
  (basisTable r s).submatrix computationalIndex blockIndex

private def dickeScale : ℝ := 1 / Real.sqrt 3
private def pairScale : ℝ := 1 / Real.sqrt 2

/-- Columns are the even Dicke kets, odd Dicke kets, `v ⊗ w`, and
`(v ⊗ w + 2 • (w ⊗ v)) / √3`, where `w = (|01⟩ - |10⟩) / √2`. -/
private def basis : Matrix Qubits Blocks ℂ := complexify (splitBasis dickeScale pairScale)

private def chiral (B : Q ℂ) : Matrix Parity Parity ℂ := fromBlocks 0 B Bᴴ 0

private def doubleBlock (A B : Matrix Parity Parity ℂ) : Matrix Blocks Blocks ℂ :=
  fromBlocks A 0 0 B

private def flip : Q ℂ := !![0, 1; 1, 0]

private def radius (z : ℝ) : ℝ := Real.sqrt (1 + z ^ 2 + z ^ 4)

private def u (z : ℝ) : ℝ := (3 * dickeScale) * (1 + z ^ 2) / (2 * radius z)
private def v (z : ℝ) : ℝ := (1 - z ^ 2) / (2 * radius z)

private def polar (z : ℝ) : Q ℂ := complexify (!![u z, -v z; v z, u z])

private def symBlock (r a d b : ℝ) : Q ℂ :=
  complexify (!![3 * r * a ^ 2, b ^ 2; 2 * a * d + b ^ 2, 3 * r * d ^ 2])

private def deltaBlocks (r a d b : ℝ) : Matrix Blocks Blocks ℂ :=
  doubleBlock (chiral (((2 * b : ℝ) : ℂ) • symBlock r a d b))
    (fromBlocks (((2 * b*(a * d-b ^ 2) : ℝ) : ℂ) • flip) 0 0
      (((2 * b*(a * d-b ^ 2) : ℝ) : ℂ) • flip))

private def signBlocks (z : ℝ) : Matrix Blocks Blocks ℂ :=
  doubleBlock (chiral (polar z)) (fromBlocks flip 0 0 flip)

/-- The self-adjoint sign used by the collective measurement. -/
def sign (z : ℝ) : Mat := basis * signBlocks z * basisᴴ

/-- The explicit effect for guessing the positively rotated hypothesis. -/
def optimalEffect (z : ℝ) : Mat := (1 / 2 : ℂ) • (1 + sign z)

/-- The equal-prior collective bias. -/
def bias (x z : ℝ) : ℝ := x * (radius z + (1 - x ^ 2 - z ^ 2) / 2)

private theorem dickeScale_sq : dickeScale ^ 2 = 1 / 3 := by
  unfold dickeScale
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private theorem pairScale_sq : pairScale ^ 2 = 1 / 2 := by
  unfold pairScale
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem radius_pos (z : ℝ) : 0 < radius z := by
  unfold radius
  exact Real.sqrt_pos.2 (by positivity)

private theorem radius_sq (z : ℝ) : radius z ^ 2 = 1 + z ^ 2 + z ^ 4 :=
  Real.sq_sqrt (by positivity)

private theorem splitBasis_orthogonal (r s : ℝ) (hr : r ^ 2 = 1 / 3) (hs : s ^ 2 = 1 / 2) :
    (basisTable r s)ᵀ * basisTable r s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisTable, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;>
    ring_nf <;> norm_num [hr, hs]

private theorem basis_columns : basisᴴ * basis = 1 := by
  have h : (basisTable dickeScale pairScale)ᵀ * basisTable dickeScale pairScale = 1 :=
    splitBasis_orthogonal _ _ dickeScale_sq pairScale_sq
  ext i j
  have hij := congrArg (fun A : Matrix (Fin 8) (Fin 8) ℝ => A (blockIndex i) (blockIndex j)) h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hij
  change (∑ k : Qubits,
    star (↑(basisTable dickeScale pairScale (computationalIndex k) (blockIndex i)) : ℂ) *
      ↑(basisTable dickeScale pairScale (computationalIndex k) (blockIndex j))) = _
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  rw [computationalIndex.sum_comp (fun k => basisTable dickeScale pairScale k (blockIndex i) *
    basisTable dickeScale pairScale k (blockIndex j)), hij, Matrix.one_apply]
  by_cases he : i = j
  · simp [he]
  · simp [he, blockIndex.injective.ne he]

private theorem basis_rows : basis * basisᴴ = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv (blockIndex.trans computationalIndex.symm)).mp basis_columns

private def rawDifference (a d b : ℝ) : Mat :=
  complexify (raw a d b ⊗ₖ (raw a d b ⊗ₖ raw a d b) -
    raw a d (-b) ⊗ₖ (raw a d (-b) ⊗ₖ raw a d (-b)))

private theorem difference_raw (x z : ℝ) :
    difference x z = rawDifference (a z) (d z) (b x) := by
  ext i j
  simp [difference, threeCopy, qubit, rawDifference, b, Matrix.kroneckerMap_apply,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub, neg_div]

set_option maxHeartbeats 1800000 in
-- The eight column checks simplify the three tensor factors entrywise.
private theorem difference_intertwines (a d b r s : ℝ) (hr : r ^ 2 = 1 / 3) :
    rawDifference a d b * complexify (splitBasis r s) =
      complexify (splitBasis r s) * deltaBlocks r a d b := by
  have hrC : (r : ℂ) ^ 2 = 1 / 3 := by
    rw [← Complex.ofReal_pow, hr]
    norm_num
  ext i j
  rcases i with ⟨i₁, i₂, i₃⟩
  rcases j with (j | j) <;> rcases j with (j | j) <;>
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases i₃ <;> fin_cases j <;>
    norm_num [rawDifference, raw, deltaBlocks, doubleBlock, chiral, symBlock, flip,
      splitBasis, basisTable, computationalIndex, blockIndex, finProdFinEquiv, finSumFinEquiv,
      Fin.castAdd, Fin.castLE, Fin.addNat,
      Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fintype.sum_sum_type,
      Fin.sum_univ_two, Complex.star_def, smul_eq_mul] <;>
    ring_nf <;> norm_num [hrC] <;> ring

private theorem difference_blocks (x z : ℝ) :
    difference x z = basis * deltaBlocks dickeScale (a z) (d z) (b x) * basisᴴ := by
  have h := difference_intertwines (a z) (d z) (b x) dickeScale pairScale dickeScale_sq
  change rawDifference (a z) (d z) (b x) * basis =
    basis * deltaBlocks dickeScale (a z) (d z) (b x) at h
  rw [difference_raw, ← h, Matrix.mul_assoc, basis_rows, Matrix.mul_one]

private theorem chiral_adjoint (B : Q ℂ) : (chiral B)ᴴ = chiral B := by
  simp [chiral, Matrix.fromBlocks_conjTranspose]

private theorem flip_adjoint : flipᴴ = flip := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flip, Matrix.conjTranspose_apply]

private theorem flip_square : flip * flip = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [flip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

private theorem rotation_norm (z : ℝ) : u z ^ 2 + v z ^ 2 = 1 := by
  have hr : (3 * dickeScale) ^ 2 = 3 := by
    rw [mul_pow, dickeScale_sq]
    norm_num
  unfold u v
  rw [div_pow, div_pow, ← add_div, mul_pow (3 * dickeScale), hr]
  apply (div_eq_iff (pow_ne_zero 2 (ne_of_gt (mul_pos (by norm_num) (radius_pos z))))).mpr
  rw [one_mul, mul_pow, radius_sq]
  ring

private theorem polar_columns (z : ℝ) : (polar z)ᴴ * polar z = 1 := by
  have h : ((u z : ℝ) : ℂ) ^ 2 + ((v z : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast rotation_norm z
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [polar, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.one_apply, Complex.star_def] <;>
    first | linear_combination h | ring

private theorem polar_rows (z : ℝ) : polar z * (polar z)ᴴ = 1 :=
  mul_eq_one_comm.mp (polar_columns z)

private theorem signBlocks_sq (z : ℝ) : signBlocks z * signBlocks z = 1 := by
  simp [signBlocks, doubleBlock, chiral, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one,
    polar_columns, polar_rows, flip_square]

private theorem sign_adjoint (z : ℝ) : (sign z)ᴴ = sign z := by
  simp [sign, signBlocks, doubleBlock, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    Matrix.fromBlocks_conjTranspose, chiral_adjoint, flip_adjoint]

private theorem sign_square (z : ℝ) : sign z * sign z = 1 := by
  simp [sign, Matrix.mul_assoc, ← Matrix.mul_assoc basisᴴ,
    basis_columns, ← Matrix.mul_assoc (signBlocks z), signBlocks_sq, basis_rows]

private def gap (x z : ℝ) : ℝ := a z * d z - b x ^ 2

private theorem gap_formula (x z : ℝ) : gap x z = (1 - x ^ 2 - z ^ 2) / 4 := by
  unfold gap a d b
  ring

private theorem diagonal_pos (z : ℝ) (hz : z ^ 2 < 1) : 0 < a z ∧ 0 < d z := by
  have h₁ : -1 < z := by nlinarith
  have h₂ : z < 1 := by nlinarith
  constructor
  · unfold a; linarith
  · unfold d; linarith

private theorem qubit_state (x z : ℝ) (h : x ^ 2 + z ^ 2 < 1) :
    (qubit x z).PosDef ∧ (qubit x z).trace = 1 := by
  refine ⟨?_, ?_⟩
  · have ha := (diagonal_pos z (by nlinarith [sq_nonneg x])).1
    have hg : 0 < gap x z := by rw [gap_formula]; linarith
    convert posDef_two (a z) (b x) (d z) ha hg using 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · rw [Matrix.trace, Fin.sum_univ_two]
    change (a z : ℂ) + (d z : ℂ) = 1
    exact_mod_cast (show a z + d z = 1 by unfold a d; ring)

/-- Both physical hypotheses are normalized, positive definite three-copy states. -/
theorem threeCopy_states (x z : ℝ) (h : x ^ 2 + z ^ 2 < 1) :
    (threeCopy x z).PosDef ∧ (threeCopy x z).trace = 1 ∧
    (threeCopy (-x) z).PosDef ∧ (threeCopy (-x) z).trace = 1 := by
  have state (y : ℝ) (hy : y ^ 2 + z ^ 2 < 1) :
      (threeCopy y z).PosDef ∧ (threeCopy y z).trace = 1 := by
    obtain ⟨hp, ht⟩ := qubit_state y z hy
    exact ⟨hp.kronecker (hp.kronecker hp), by simp [threeCopy, Matrix.trace_kronecker, ht]⟩
  exact ⟨(state x h).1, (state x h).2, state (-x) (by simpa using h)⟩

private def upperBlock (x z : ℝ) : Q ℂ := (x : ℂ) • symBlock dickeScale (a z) (d z) (b x)
private def polarFactor (x z : ℝ) : Q ℂ := (polar z)ᴴ * upperBlock x z

set_option maxHeartbeats 600000 in
-- The certificate includes the entrywise multiplication, determinant and trace of the polar factor.
private theorem polarFactor_certificate (x z : ℝ) (hx : 0 < x) (h : x ^ 2 + z ^ 2 < 1) :
    (polarFactor x z).PosDef ∧ (polarFactor x z).trace.re = x * radius z := by
  let A := 3 * dickeScale * a z ^ 2
  let B := b x ^ 2
  let C := 2 * a z * d z + b x ^ 2
  let D := 3 * dickeScale * d z ^ 2
  let p := x * (u z * A + v z * C)
  let q := x * (u z * B + v z * D)
  let r := x * (-v z * B + u z * D)
  have hoff : -v z * A + u z * C = u z * B + v z * D := by
    dsimp [A, B, C, D, u, v, a, d]
    field_simp [ne_of_gt (radius_pos z)]
    ring
  have he : polarFactor x z = complexify (raw p r q) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [polarFactor, polar, upperBlock, symBlock, raw, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.star_def,
        smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_add] <;>
      dsimp [p, q, r, A, B, C, D] <;> ring_nf
    dsimp [A, B, C, D] at hoff
    linear_combination x * hoff
  have hzz : z ^ 2 < 1 := by nlinarith [sq_nonneg x]
  obtain ⟨ha, hd⟩ := diagonal_pos z hzz
  have hs : 0 < dickeScale := by unfold dickeScale; positivity
  have hrad := radius_pos z
  have hu : 0 < u z := by
    unfold u
    positivity
  have hv : 0 < v z := by unfold v; exact div_pos (by linarith) (by positivity)
  have hp : 0 < p := by dsimp [p, A, C]; positivity
  have hmul : ((3 * dickeScale) ^ 2) = 3 := by
    rw [mul_pow, dickeScale_sq]
    norm_num
  have hdet : p * r - q ^ 2 = x ^ 2 * (gap x z) * (3 * a z * d z + b x ^ 2) := by
    have hdet1 : (polar z).det = 1 := by
      rw [Matrix.det_fin_two]
      norm_num [polar, ← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_sub]
      exact_mod_cast (show u z * u z + v z * v z = 1 by nlinarith [rotation_norm z])
    have hdetR :
        (x * (3 * dickeScale * a z ^ 2)) * (x * (3 * dickeScale * d z ^ 2)) -
            (x * b x ^ 2) * (x * (2 * a z * d z + b x ^ 2)) =
          x ^ 2 * gap x z * (3 * a z * d z + b x ^ 2) := by
      unfold gap
      linear_combination (x ^ 2 * a z ^ 2 * d z ^ 2) * hmul
    have hdet2 : (upperBlock x z).det =
        ((x ^ 2 * gap x z * (3 * a z * d z + b x ^ 2) : ℝ) : ℂ) := by
      rw [Matrix.det_fin_two]
      simpa [upperBlock, symBlock, smul_eq_mul] using congrArg Complex.ofReal hdetR
    have hdet3 := congrArg Matrix.det he
    rw [polarFactor, Matrix.det_mul, Matrix.det_conjTranspose, hdet1, star_one, one_mul,
      hdet2, Matrix.det_fin_two] at hdet3
    norm_num [raw, ← Complex.ofReal_mul, ← Complex.ofReal_sub] at hdet3
    simpa [pow_two] using hdet3.symm
  have hg : 0 < gap x z := by rw [gap_formula]; linarith
  have hpd : 0 < p * r - q ^ 2 := by rw [hdet]; positivity
  constructor
  · rw [he]
    convert posDef_two p q r hp hpd using 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · rw [he]
    simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
    change ((p : ℂ) + (r : ℂ)).re = _
    rw [Complex.add_re, Complex.ofReal_re, Complex.ofReal_re]
    have htrace : p + r = x * (u z * (A + D) + v z * (C - B)) := by
      dsimp [p, r]
      ring
    rw [htrace]
    congr 1
    have hAD : A + D = 3 * dickeScale * (1 + z ^ 2) / 2 := by dsimp [A, D, a, d]; ring
    have hCB : C - B = (1 - z ^ 2) / 2 := by dsimp [C, B, a, d]; ring
    rw [hAD, hCB]
    unfold u v
    field_simp [ne_of_gt (radius_pos z)]
    linear_combination (1 + z ^ 2) ^ 2 * hmul - 4 * radius_sq z

private theorem block_trace {m n : Type} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    (fromBlocks A 0 0 B).trace = A.trace + B.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

private theorem block_posDef {m n : Type} [Finite m] [Finite n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) : (fromBlocks A 0 0 B).PosDef := by
  classical
  let := Fintype.ofFinite m
  let := Fintype.ofFinite n
  let := hA.isUnit.invertible
  have hp : (fromBlocks A (0 : Matrix m n ℂ) 0 B).PosSemidef := by
    have h := (Matrix.PosDef.fromBlocks₁₁ (0 : Matrix m n ℂ) B hA).mpr
    simpa using h (by simpa using hB.posSemidef)
  exact hp.posDef_iff_isUnit.mpr (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hA.isUnit, hB.isUnit⟩)

private theorem transport_mul (A B : Matrix Blocks Blocks ℂ) :
    (basis * A * basisᴴ) * (basis * B * basisᴴ) = basis * (A * B) * basisᴴ := by
  rw [Matrix.mul_assoc (basis * A), ← Matrix.mul_assoc basisᴴ, ← Matrix.mul_assoc basisᴴ,
    basis_columns, Matrix.one_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc]

private theorem transport_trace (A : Matrix Blocks Blocks ℂ) :
    (basis * A * basisᴴ).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, basis_columns, Matrix.one_mul]

private theorem difference_adjoint (x z : ℝ) : (difference x z)ᴴ = difference x z := by
  rw [difference_blocks]
  simp [deltaBlocks, doubleBlock, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    Matrix.fromBlocks_conjTranspose, chiral_adjoint, flip_adjoint, Matrix.conjTranspose_smul]

private theorem difference_trace (x z : ℝ) (h : x ^ 2 + z ^ 2 < 1) :
    (difference x z).trace = 0 := by
  obtain ⟨_, hpos, _, hneg⟩ := threeCopy_states x z h
  rw [difference, Matrix.trace_sub, hpos, hneg, sub_self]

private theorem signed_difference (x z : ℝ)
    (hx : 0 < x) (h : x ^ 2 + z ^ 2 < 1) :
    (sign z * difference x z).PosDef ∧
      (sign z * difference x z).trace.re = 2 * bias x z := by
  let U := polar z
  let H := polarFactor x z
  let K : Q ℂ := ((x * gap x z : ℝ) : ℂ) • 1
  obtain ⟨hH, htrace⟩ := polarFactor_certificate x z hx h
  have hB : U * H = upperBlock x z := by
    change polar z * ((polar z)ᴴ * upperBlock x z) = _
    rw [← Matrix.mul_assoc, polar_rows, Matrix.one_mul]
  have htop : U * (upperBlock x z)ᴴ = U * H * Uᴴ := by
    rw [← hB, Matrix.conjTranspose_mul, hH.isHermitian.eq]
    exact (Matrix.mul_assoc _ _ _).symm
  have hb : 2 * b x = x := by unfold b; ring
  let c : ℂ := ↑(x * gap x z)
  have hΔ : deltaBlocks dickeScale (a z) (d z) (b x) =
      doubleBlock (chiral (upperBlock x z)) (fromBlocks (c • flip) 0 0 (c • flip)) := by
    unfold deltaBlocks upperBlock
    rw [hb]
    rfl
  have hsym : chiral (polar z) * chiral (upperBlock x z) =
      fromBlocks (U * H * Uᴴ) 0 0 H := by
    simp only [chiral, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add]
    rw [show polar z * (upperBlock x z)ᴴ = _ from htop,
      show (polar z)ᴴ * upperBlock x z = H from rfl]
  have hpair : flip * (c • flip) = K := by
    rw [Matrix.mul_smul, flip_square]
  have hblocks : signBlocks z * deltaBlocks dickeScale (a z) (d z) (b x) =
      doubleBlock (fromBlocks (U * H * Uᴴ) 0 0 H) (fromBlocks K 0 0 K) := by
    simp [hΔ, signBlocks, doubleBlock, Matrix.fromBlocks_multiply, hsym, hpair]
  rw [sign, difference_blocks, transport_mul, hblocks]
  constructor
  · have hU : Function.Injective Uᴴ.mulVec := by
      apply Matrix.mulVec_injective_of_isUnit
      exact isUnit_iff_exists_inv.mpr ⟨U, polar_columns z⟩
    have hK : K.PosDef := by
      have hg : 0 < gap x z := by rw [gap_formula]; linarith
      have hprod : 0 < x * gap x z := mul_pos hx hg
      have hdiag : K = diagonal (fun _ : Fin 2 => ((x * gap x z : ℝ) : ℂ)) := by
        ext i j
        by_cases h : i = j <;> simp [K, h]
      rw [hdiag, Matrix.posDef_diagonal_iff]
      exact fun _ => by exact_mod_cast hprod
    have hp := block_posDef (block_posDef
      (by simpa using hH.conjTranspose_mul_mul_same hU) hH) (block_posDef hK hK)
    have hinj : Function.Injective basisᴴ.mulVec := by
      intro f g hfg
      simpa only [Matrix.mulVec_mulVec, basis_rows, Matrix.one_mulVec]
        using congrArg (basis *ᵥ ·) hfg
    simpa only [doubleBlock, Matrix.conjTranspose_conjTranspose] using
      hp.conjTranspose_mul_mul_same hinj
  · have ht : (U * H * Uᴴ).trace = H.trace := by
      rw [Matrix.trace_mul_cycle, show Uᴴ * U = 1 from polar_columns z, Matrix.one_mul]
    change H.trace.re = x * radius z at htrace
    simp only [transport_trace, doubleBlock, block_trace, ht, Complex.add_re, htrace]
    have hKt : K.trace.re = 2 * (x * gap x z) := by
      rw [Matrix.trace_smul, Matrix.trace_one]
      norm_num [K, smul_eq_mul, Complex.mul_re]
      ring
    rw [hKt, gap_formula, bias]
    ring

private theorem effect_projection {n : Type} [Fintype n] [DecidableEq n]
    (S : Matrix n n ℂ) (hs : Sᴴ = S) (hsq : S * S = 1) :
    let P := (1 / 2 : ℂ) • (1 + S)
    Pᴴ = P ∧ P * P = P := by
  dsimp only
  constructor
  · simp [Matrix.conjTranspose_smul, hs]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hsq]
    module

private theorem zero_of_compression {n : Type} [Fintype n]
    {E P : Matrix n n ℂ} (hE : E.PosSemidef) (hP : Pᴴ = P)
    (hz : P * E * P = 0) : E * P = 0 := by
  classical
  obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hE.nonneg
  change E = Yᴴ * Y at hY
  have hs : (Y * P)ᴴ * (Y * P) = 0 := by
    rw [Matrix.conjTranspose_mul, hP, ← Matrix.mul_assoc, Matrix.mul_assoc P, ← hY, hz]
  have ht : Y * P = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (by rw [hs]; simp)
  rw [hY, Matrix.mul_assoc, ht, Matrix.mul_zero]

private theorem effect_optimality {n : Type} [Fintype n] [DecidableEq n]
    (S D : Matrix n n ℂ) (hS : Sᴴ = S) (hS₂ : S * S = 1)
    (hD : Dᴴ = D) (htr : D.trace = 0) (hA : (S * D).PosDef) :
    let P := (1 / 2 : ℂ) • (1 + S)
    let k := (S * D).trace.re / 2
    P.PosSemidef ∧ (1 - P).PosSemidef ∧ (P * D).trace.re = k ∧
      traceNorm D = 2 * k ∧
      ∀ F : Matrix n n ℂ, F.PosSemidef → (1 - F).PosSemidef →
        (F * D).trace.re ≤ k ∧ ((F * D).trace.re = k ↔ F = P) := by
  dsimp only
  let P : Matrix n n ℂ := (1 / 2 : ℂ) • (1 + S)
  let Q : Matrix n n ℂ := 1 - P
  let A := S * D
  let Ap := P * A * P
  let Aq := Q * A * Q
  obtain ⟨hP, hP₂⟩ := effect_projection S hS hS₂
  change Pᴴ = P at hP
  change P * P = P at hP₂
  have hQ : Qᴴ = Q := by simp [Q, hP]
  have hQ₂ : Q * Q = Q := by dsimp [Q]; noncomm_ring [hP₂]
  have hPQ : P * Q = 0 := by dsimp [Q]; noncomm_ring [hP₂]
  have hPpos : P.PosSemidef := by simpa [hP, hP₂] using Matrix.posSemidef_conjTranspose_mul_self P
  have hQpos : Q.PosSemidef := by simpa [hQ, hQ₂] using Matrix.posSemidef_conjTranspose_mul_self Q
  have hAD : S * D = D * S := by
    simpa only [Matrix.conjTranspose_mul, hS, hD] using hA.isHermitian.eq.symm
  have hAS : S * A = A * S := by
    dsimp [A]
    rw [Matrix.mul_assoc, hAD]
  have hPA : P * A = A * P := by
    simp [P, Matrix.add_mul, Matrix.mul_add, hAS]
  have hQA : Q * A = A * Q := by
    dsimp [Q]
    noncomm_ring [hPA]
  have hpq : P + Q = 1 := by dsimp [Q]; abel
  have hdiff : P - Q = S := by
    dsimp [Q, P]
    module
  have hp : Ap = P * A := by
    dsimp [Ap]
    rw [Matrix.mul_assoc, ← hPA, ← Matrix.mul_assoc, hP₂]
  have hq : Aq = Q * A := by
    dsimp [Aq]
    rw [Matrix.mul_assoc, ← hQA, ← Matrix.mul_assoc, hQ₂]
  have hsplit : D = Ap - Aq := by
    rw [hp, hq, ← Matrix.sub_mul, hdiff]
    simp [A, ← Matrix.mul_assoc, hS₂]
  have htotal : Ap + Aq = A := by rw [hp, hq, ← Matrix.add_mul, hpq, Matrix.one_mul]
  have hAp : Ap.PosSemidef := by
    simpa only [hP] using hA.posSemidef.conjTranspose_mul_mul_same P
  have hAq : Aq.PosSemidef := by
    simpa only [hQ] using hA.posSemidef.conjTranspose_mul_mul_same Q
  have horth : Ap * Aq = 0 := by
    rw [hp, hq, hPA]
    simp [← Matrix.mul_assoc, Matrix.mul_assoc A P Q, hPQ]
  have ht : Ap.trace = Aq.trace := by
    have h := congrArg Matrix.trace hsplit
    rw [htr, Matrix.trace_sub] at h
    exact sub_eq_zero.mp h.symm
  have hval : (P * D).trace.re = A.trace.re / 2 := by
    have hPD : P * D = Ap := by
      calc
        P * D = (P * P) * A - (P * Q) * A := by
          rw [hsplit, Matrix.mul_sub, hp, hq, Matrix.mul_assoc P P, Matrix.mul_assoc P Q]
        _ = Ap := by rw [hP₂, hPQ, Matrix.zero_mul, sub_zero, hp]
    rw [hPD]
    have h := congrArg (fun M : Matrix n n ℂ => M.trace.re) htotal
    simp only [Matrix.trace_add, Complex.add_re, ← ht] at h
    linarith
  refine ⟨hPpos, hQpos, hval, ?_, ?_⟩
  · calc
      traceNorm D = Ap.trace.re + Aq.trace.re :=
        hsplit ▸ traceNorm_sub_orthogonal Ap Aq hAp hAq horth
      _ = 2 * (A.trace.re / 2) := by
        rw [← htotal, Matrix.trace_add, Complex.add_re]
        ring
  · intro F hF hFc
    let G := P * (1 - F) * P
    let H := Q * F * Q
    have hG : G.PosSemidef := by simpa only [hP] using hFc.conjTranspose_mul_mul_same P
    have hH : H.PosSemidef := by simpa only [hQ] using hF.conjTranspose_mul_mul_same Q
    have pair (E L : Matrix n n ℂ) :
        (A * (L * E * L)).trace = (E * (L * A * L)).trace := by
      rw [Matrix.trace_mul_cycle', ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.trace_mul_comm ((L * A) * L) E]
    have hgap : A.trace.re / 2 - (F * D).trace.re =
        (A * G).trace.re + (A * H).trace.re := by
      change _ = (A * (P * (1 - F) * P)).trace.re + (A * (Q * F * Q)).trace.re
      rw [pair, pair, ← show Ap = P * A * P from rfl, ← show Aq = Q * A * Q from rfl,
        sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, hsplit, Matrix.mul_sub,
        Matrix.trace_sub, Complex.sub_re]
      have h := congrArg (fun M : Matrix n n ℂ => M.trace.re) htotal
      simp only [Matrix.trace_add, Complex.add_re, ← ht] at h
      linarith
    have hGn := (Complex.nonneg_iff.mp (hA.posSemidef.trace_mul_nonneg hG)).1
    have hHn := (Complex.nonneg_iff.mp (hA.posSemidef.trace_mul_nonneg hH)).1
    refine ⟨by linarith, ?_⟩
    constructor
    · intro he
      have hzG : G = 0 := by
        by_contra hn
        have hz : 0 < (A * G).trace.re :=
          trace_pair_pos A G hA hG hn
        linarith
      have hzH : H = 0 := by
        by_contra hn
        have hz : 0 < (A * H).trace.re :=
          trace_pair_pos A H hA hH hn
        linarith
      have hFP := zero_of_compression hFc hP hzG
      have hFQ := zero_of_compression hF hQ hzH
      calc
        F = F * (P + Q) := by rw [hpq, Matrix.mul_one]
        _ = P := by
          rw [Matrix.mul_add, hFQ, add_zero]
          simpa [sub_mul] using (sub_eq_zero.mp (show P - F * P = 0 by
            simpa only [sub_mul, Matrix.one_mul] using hFP)).symm
    · rintro rfl
      exact hval

/-- Helstrom's bound is attained by the explicit effect. Equality determines the
entire complex binary effect, and the trace norm is twice the stated bias. -/
theorem threeCopy_helstrom (x z : ℝ) (hx : 0 < x) (h : x ^ 2 + z ^ 2 < 1) :
    let D := difference x z
    let P := optimalEffect z
    P.PosSemidef ∧ (1 - P).PosSemidef ∧ (P * D).trace.re = bias x z ∧
      traceNorm D = 2 * bias x z ∧
      ∀ F : Mat, F.PosSemidef → (1 - F).PosSemidef →
        (F * D).trace.re ≤ bias x z ∧ ((F * D).trace.re = bias x z ↔ F = P) := by
  obtain ⟨hp, he⟩ := signed_difference x z hx h
  have hk : (sign z * difference x z).trace.re / 2 = bias x z := by linarith
  simpa only [optimalEffect, hk] using
    effect_optimality (sign z) (difference x z) (sign_adjoint z) (sign_square z)
      (difference_adjoint x z) (difference_trace x z h) hp

/-- Transpose the first qubit in the computational basis. -/
abbrev firstTranspose (F : Mat) : Mat := partialTranspose Fᵀ

/-- The same physical density difference is invariant under the fixed-cut transpose. -/
theorem difference_firstTranspose (x z : ℝ) :
    firstTranspose (difference x z) = difference x z := by
  have hq (y : ℝ) (i j : Fin 2) : qubit y z i j = qubit y z j i := by
    fin_cases i <;> fin_cases j <;> rfl
  ext i j
  simp only [firstTranspose, partialTranspose, Matrix.transpose_apply, difference,
    Matrix.sub_apply, threeCopy, Matrix.kroneckerMap_apply]
  rw [hq x j.1 i.1, hq (-x) j.1 i.1]

private theorem firstTranspose_trace (F D : Mat) :
    (firstTranspose F * D).trace = (F * firstTranspose D).trace := by
  let M (a c : Fin 2) (b d : Fin 2 × Fin 2) : ℂ := F (c,b) (a,d) * D (c,d) (a,b)
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Fintype.sum_prod_type (α₁ := Fin 2) (α₂ := Fin 2 × Fin 2),
    firstTranspose, partialTranspose, Matrix.transpose_apply]
  change (∑ a, ∑ b, ∑ c, ∑ d, M a c b d) = ∑ a, ∑ b, ∑ c, ∑ d, M c a b d
  calc
    _ = ∑ a, ∑ c, ∑ b, ∑ d, M a c b d :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ c, ∑ a, ∑ b, ∑ d, M a c b d := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

/-- The change of the `000,111` entry of the optimal sign under partial
transposition, which swaps it with the `100,011` entry. -/
theorem sign_firstTranspose_entry (z : ℝ) :
    (sign z (0,0,0) (1,1,1) - sign z (1,0,0) (0,1,1)).re =
      2 / 3 * (1 - (1 - z ^ 2) / Real.sqrt (1 + z ^ 2 + z ^ 4)) := by
  have h₁ : sign z (0,0,0) (1,1,1) = ((-v z : ℝ) : ℂ) := by
    norm_num [sign, basis, splitBasis, basisTable, computationalIndex, blockIndex,
      finProdFinEquiv, finSumFinEquiv, Fin.castAdd, Fin.castLE, Fin.addNat,
      signBlocks, doubleBlock, chiral, polar, flip,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Complex.star_def]
  have h₂ : sign z (1,0,0) (0,1,1) =
      ((dickeScale ^ 2 * v z - 4 * dickeScale ^ 2 * pairScale ^ 2 : ℝ) : ℂ) := by
    norm_num [sign, basis, splitBasis, basisTable, computationalIndex, blockIndex,
      finProdFinEquiv, finSumFinEquiv, Fin.castAdd, Fin.castLE, Fin.addNat,
      signBlocks, doubleBlock, chiral, polar, flip,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Complex.star_def, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_neg,
      ← Complex.ofReal_sub]
    congr 1
    · ring_nf
    · ring
  rw [h₁, h₂, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re, dickeScale_sq, pairScale_sq]
  unfold v radius
  ring

/-- Every binary PPT effect across the first-qubit cut has strictly smaller bias
throughout the mixed, noncommuting interior of the Wu family. -/
theorem threeCopy_ppt_lt (x z : ℝ) (hx : 0 < x) (hz : 0 < z) (h : x ^ 2 + z ^ 2 < 1)
    (F : Mat) (hF : F.PosSemidef) (hFc : (1 - F).PosSemidef)
    (hΓ : (firstTranspose F).PosSemidef) (hΓc : (1 - firstTranspose F).PosSemidef) :
    (F * difference x z).trace.re < bias x z := by
  obtain ⟨_, _, _, _, hopt⟩ := threeCopy_helstrom x z hx h
  obtain ⟨hle, huniq⟩ := hopt F hF hFc
  refine lt_of_le_of_ne hle ?_
  intro he
  have hΓe : (firstTranspose F * difference x z).trace.re = bias x z := by
    rw [firstTranspose_trace, difference_firstTranspose, he]
  have hP := huniq.mp he
  have hPΓ := (hopt (firstTranspose F) hΓ hΓc).2.mp hΓe
  have hfix : firstTranspose (optimalEffect z) = optimalEffect z := by simpa [hP] using hPΓ
  have hc := congrArg (fun E : Mat => (E (0,0,0) (1,1,1)).re) hfix
  change (optimalEffect z (1,0,0) (0,1,1)).re =
    (optimalEffect z (0,0,0) (1,1,1)).re at hc
  have hc' : (sign z (0,0,0) (1,1,1) - sign z (1,0,0) (0,1,1)).re = 0 := by
    have h1 : (1 : Mat) (1,0,0) (0,1,1) = 0 := by norm_num [Matrix.one_apply]
    have h2 : (1 : Mat) (0,0,0) (1,1,1) = 0 := by norm_num [Matrix.one_apply]
    norm_num [optimalEffect, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      h1, h2, Complex.mul_re, Complex.div_re] at hc
    rw [Complex.sub_re]
    linarith
  have hr : 1 < radius z := by
    change 1 < Real.sqrt (1 + z ^ 2 + z ^ 4)
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
    nlinarith [sq_pos_of_pos hz, sq_nonneg (z ^ 2)]
  have hratio : (1 - z ^ 2) / radius z < 1 := by
    apply (div_lt_iff₀ (radius_pos z)).mpr
    nlinarith [sq_nonneg z]
  have hsign : 0 < 2 / 3 * (1 - (1 - z ^ 2) / radius z) :=
    mul_pos (by norm_num) (sub_pos.mpr hratio)
  rw [sign_firstTranspose_entry] at hc'
  exact hsign.ne' hc'

#print axioms threeCopy_states
#print axioms threeCopy_helstrom
#print axioms threeCopy_ppt_lt

end D5.S3.Quantum.Measurement.WuGibbsThreeCopyDiscrimination
