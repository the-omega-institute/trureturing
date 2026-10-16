/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Purity
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Purity
   mirror-E: none(waiver:exact-rational-certificate)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Purity.claim; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Data.certificate; result=D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Purity.result; claim=D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Purity.claim
   digest: Both rank-three pencils and the uniform rank-four inequality bound arbitrary length-28 spectral purity by one twenty-fifth. -/

/-
proof_shape: purity_bound: content; result: content
admission_basis: escape-witness
escape_witness: The exact quadratic identity combines gap-weighted pencil
  traces, uniform rank-four mass terms, undivided Schur minors and mixed
  polarization. The latter cross-pencils term is essential in this certificate.
Private helpers: certificate_identity: content; pencil_psd: bind-only,
  consumed by result; certificate_nonnegative and
  gap_nonnegative: bind-only, consumed by purity_bound.
Direct reuse: QutritSpectralReduction.K1, K2, psd_of_rat_ldl;
  RHLinalg.trace_mul_nonneg_of_posSemidef.
Escape audit evidence remains uncompiled; see issues 17689 and 17734.
No literal APPT-to-spectral bridge is asserted in this module.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.RankFourLength28Data
import D5.S3.Quantum.Matrix.DivisionFreeSchur
import D5.S3.Weil.ZetaLinear.RankTrace

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 128000000
set_option maxRecDepth 65536

open Matrix
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.RankFourLength28Purity
open QutritSpectralReduction
open RankFourLength28Data
open D5.S3.Quantum.Matrix.DivisionFreeSchur

/-- First three and last six coordinates, in the original qutrit order. -/
def boundary (l : Fin 28 → ℝ) : Fin 9 → ℝ :=
  ![l 0, l 1, l 2, l 22, l 23, l 24, l 25, l 26, l 27]

def pencil (l : Fin 28 → ℝ) : Fin 2 → Matrix (Fin 3) (Fin 3) ℝ :=
  ![QutritSpectralReduction.K1 (boundary l), QutritSpectralReduction.K2 (boundary l)]

/-- The uniform rank-four necessary mass difference, in zero-based indexing. -/
def L4 (l : Fin 28 → ℝ) : ℝ :=
  (∑ i : Fin 10, l ⟨18 + i.val, by omega⟩) -
  (∑ i : Fin 6, l ⟨i.val, by omega⟩)

def gap (l : Fin 28 → ℝ) : Fin 28 → ℝ :=
  ![l 0-l 1, l 1-l 2, l 2-l 3, l 3-l 4, l 4-l 5, l 5-l 6,
    l 6-l 7, l 7-l 8, l 8-l 9, l 9-l 10, l 10-l 11, l 11-l 12,
    l 12-l 13, l 13-l 14, l 14-l 15, l 15-l 16, l 16-l 17,
    l 17-l 18, l 18-l 19, l 19-l 20, l 20-l 21, l 21-l 22,
    l 22-l 23, l 23-l 24, l 24-l 25, l 25-l 26, l 26-l 27, l 27]

/-- Coordinates transverse to the equality ray; no sign is assumed for y. -/
def transverse (x : Fin 28 → ℝ) : Fin 27 → ℝ :=
  ![x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11,
    x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20,
    x 21, x 22, x 23, x 24, x 25, x 26, x 0 - 2*x 27]

def v : Fin 3 → ℝ := ![1,1,0]
def U : Matrix (Fin 3) (Fin 2) ℝ := !![1,0; -1,0; 0,1]

private noncomputable def rhs (l : Fin 28 → ℝ) : ℝ :=
  let x := gap l
  let y := transverse x
  let K := pencil l
  let q := fun a => quadratic (K a) v
  quadratic (castMat certificate.P.rational) y +
  quadratic (castMat certificate.H) x +
  (∑ s : Fin 2, ∑ i : Fin 28,
    x i * (castMat (certificate.B s i).rational * K s).trace) +
  L4 l * (∑ i : Fin 28, (certificate.w i : ℝ) * x i) +
  (∑ a : Fin 2, ∑ s : Fin 2,
    q a * (castMat (certificate.D a s).rational * K s).trace) +
  L4 l * (∑ a : Fin 2, (certificate.gamma a : ℝ) * q a) +
  (∑ s : Fin 2,
    (castMat (certificate.C s.castSucc).rational * schur (K s) v U).trace) +
  (castMat (certificate.C 2).rational * mixed (K 0) (K 1) v U).trace

/- This is an equality of real polynomials with rational coefficients. The
  finite expansions and ring normalization construct a kernel proof; no Python
  checker, solver result or floating-point spectrum is a logical premise. -/
private theorem certificate_identity (l : Fin 28 → ℝ) :
    (∑ i, l i)^2 / 25 - (∑ i, (l i)^2) = rhs l := by
  classical
  norm_num [rhs, quadratic, schur, mixed, compressed, cross, gap, transverse,
    pencil, boundary, L4, v, U, QutritSpectralReduction.K1,
    QutritSpectralReduction.K2, RankFourLength28Data.certificate,
    RankFourLength28Data.endpoint, castMat, Matrix.map_apply, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.vecMulVec, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.add_apply, Fin.sum_univ_succ]
  <;> ring

private theorem gap_nonnegative (l : Fin 28 → ℝ) (ho : Antitone l)
    (hn : ∀ i, 0 ≤ l i) (i : Fin 28) : 0 ≤ gap l i := by
  fin_cases i <;> simp only [gap, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons]
  all_goals first | exact hn 27 | exact sub_nonneg.mpr (ho (by decide))

private theorem certificate_nonnegative (l : Fin 28 → ℝ)
    (hx : ∀ i, 0 ≤ gap l i) (hK : ∀ s, (pencil l s).PosSemidef)
    (h4 : 0 ≤ L4 l) : 0 ≤ rhs l := by
  have hq (s : Fin 2) : 0 ≤ quadratic (pencil l s) v := by
    simpa [quadratic] using (hK s).dotProduct_mulVec_nonneg v
  have hp : 0 ≤ quadratic (castMat certificate.P.rational) (transverse (gap l)) := by
    simpa [quadratic] using certificate.P.positive.dotProduct_mulVec_nonneg
      (transverse (gap l))
  have hh : 0 ≤ quadratic (castMat certificate.H) (gap l) := by
    unfold quadratic
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hx i) (mul_nonneg
        (by exact_mod_cast certificate.H_nonnegative i j) (hx j))
  have hb : 0 ≤ ∑ s : Fin 2, ∑ i : Fin 28,
      gap l i * (castMat (certificate.B s i).rational * pencil l s).trace :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ =>
      mul_nonneg (hx i) (RHLinalg.trace_mul_nonneg_of_posSemidef
        (certificate.B s i).positive (hK s))
  have hw : 0 ≤ L4 l * (∑ i : Fin 28, (certificate.w i : ℝ) * gap l i) :=
    mul_nonneg h4 (Finset.sum_nonneg fun i _ =>
      mul_nonneg (by exact_mod_cast certificate.w_nonnegative i) (hx i))
  have hd : 0 ≤ ∑ a : Fin 2, ∑ s : Fin 2,
      quadratic (pencil l a) v *
        (castMat (certificate.D a s).rational * pencil l s).trace :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun s _ =>
      mul_nonneg (hq a) (RHLinalg.trace_mul_nonneg_of_posSemidef
        (certificate.D a s).positive (hK s))
  have hg : 0 ≤ L4 l * (∑ a : Fin 2,
      (certificate.gamma a : ℝ) * quadratic (pencil l a) v) :=
    mul_nonneg h4 (Finset.sum_nonneg fun a _ =>
      mul_nonneg (by exact_mod_cast certificate.gamma_nonnegative a) (hq a))
  have hs : 0 ≤ ∑ s : Fin 2,
      (castMat (certificate.C s.castSucc).rational * schur (pencil l s) v U).trace :=
    Finset.sum_nonneg fun s _ => RHLinalg.trace_mul_nonneg_of_posSemidef
      (certificate.C s.castSucc).positive (schur_posSemidef (hK s) v U)
  have hm : 0 ≤ (castMat (certificate.C 2).rational *
      mixed (pencil l 0) (pencil l 1) v U).trace :=
    RHLinalg.trace_mul_nonneg_of_posSemidef (certificate.C 2).positive
      (mixed_posSemidef (hK 0) (hK 1) v U)
  dsimp only [rhs]
  linarith only [hp, hh, hb, hw, hd, hg, hs, hm]

/-- No restriction on the number of distinct spectral values is imposed. Both
  qutrit pencils and the additional rank-four mass inequality are retained. -/
theorem purity_bound (l : Fin 28 → ℝ) (ho : Antitone l)
    (hn : ∀ i, 0 ≤ l i) (ht : ∑ i, l i = 1)
    (h₁ : (QutritSpectralReduction.K1 (boundary l)).PosSemidef)
    (h₂ : (QutritSpectralReduction.K2 (boundary l)).PosSemidef)
    (h4 : 0 ≤ L4 l) : ∑ i, (l i)^2 ≤ (1 : ℝ)/25 := by
  have hK (s : Fin 2) : (pencil l s).PosSemidef := by
    fin_cases s
    · simpa only [pencil, Matrix.cons_val_zero] using h₁
    · simpa [pencil] using h₂
  have hnonneg := certificate_nonnegative l (gap_nonnegative l ho hn) hK h4
  rw [← certificate_identity, ht] at hnonneg
  norm_num only [one_pow, one_div] at hnonneg ⊢
  linarith only [hnonneg]

/-- Dropping L4 is a strictly weaker spectral relaxation, with an explicit counterexample. -/
def claim : Prop :=
  ∀ l : Fin 28 → ℝ, Antitone l → (∀ i, 0 ≤ l i) → (∑ i, l i) = 1 →
    (QutritSpectralReduction.K1 (boundary l)).PosSemidef →
    (QutritSpectralReduction.K2 (boundary l)).PosSemidef →
    ∑ i, (l i)^2 ≤ (1 : ℝ)/25

def spectrum (i : Fin 28) : ℝ := if i.val < 9 then 2/37 else 1/37

private theorem pencil_psd :
    (castMat (!![2/37,-1/37,-1/37; -1/37,2/37,-1/37;
      -1/37,-1/37,2/37] : Matrix (Fin 3) (Fin 3) ℚ)).PosSemidef := by
  apply psd_of_rat_ldl _ !![1,0,0; -1/2,1,0; -1/2,-1,1] ![2/37,3/74,0]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> norm_num

/-- The literal target is a negation of the literal Prop-valued claim. -/
theorem result : ¬ claim := by
  intro h
  have ho : Antitone spectrum := by
    intro i j hij
    simp only [spectrum]
    split_ifs <;> first | norm_num | omega
  have hn (i : Fin 28) : 0 ≤ spectrum i := by
    simp only [spectrum]
    split_ifs <;> norm_num
  have ht : (∑ i, spectrum i) = 1 := by
    norm_num [spectrum, Fin.sum_univ_succ]
  have h₁ : (QutritSpectralReduction.K1 (boundary spectrum)).PosSemidef := by
    convert pencil_psd using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [QutritSpectralReduction.K1, boundary, spectrum, castMat]
  have h₂ : (QutritSpectralReduction.K2 (boundary spectrum)).PosSemidef := by
    convert pencil_psd using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [QutritSpectralReduction.K2, boundary, spectrum, castMat]
  have hp := h spectrum ho hn ht h₁ h₂
  norm_num [spectrum, Fin.sum_univ_succ] at hp


end D5.S3.Quantum.Entanglement.AbsolutePPT.RankFourLength28Purity
