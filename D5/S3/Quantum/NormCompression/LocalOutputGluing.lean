/- GID: D5/S3/Quantum/NormCompression/LocalOutputGluing
   generality: G
   mirror-B: none(waiver:ordinary-finite-power-supplier)
   mirror-E: none(waiver:ordinary-finite-power-supplier)
   anchors: []
   utility: none
   digest: Actual compression budgets glue over orthogonal local output resolutions. -/

import D5.S3.Quantum.NormCompression.FinitePowerConcavity
import D5.S3.Quantum.Lieb.PositiveMapJensen
import D5.S3.Quantum.Lieb.PowerConvexity

noncomputable section

namespace D5.S3.Quantum.NormCompression.LocalOutputGluing

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.NormCompression.UpperBranchReduction
open D5.S3.Quantum.NormCompression.FinitePowerConcavity

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

private theorem schattenPow_row_trace {H C : Type u}
    [Fintype H] [DecidableEq H] [Fintype C] [DecidableEq C]
    {q : ℝ} (hq : 0 < q) (A : Matrix H C ℂ) :
    schattenPow (2 * q) A = (cfc (fun x : ℝ => x ^ q) (A * Aᴴ)).trace.re := by
  rw [schattenPow_eq_rowGram (2 * q) (by positivity) A,
    D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum _
      (Matrix.isHermitian_mul_conjTranspose_self A)]
  congr 1
  ext j
  congr 1
  ring

private theorem trace_re_mono {H : Type u} [Fintype H] [DecidableEq H]
    {A B : Matrix H H ℂ} (h : A ≤ B) : A.trace.re ≤ B.trace.re := by
  have ht := (RCLike.nonneg_iff.mp (Matrix.le_iff.mp h).trace_nonneg).1
  change 0 ≤ (B - A).trace.re at ht
  rw [Matrix.trace_sub, Complex.sub_re] at ht
  exact sub_nonneg.mp ht

/- The existing all-Hilbert power Jensen supplier is used on the full PSD
cone. No SPD or invertible-congruence domain is substituted for it. -/
private theorem isometric_power_jensen {H K : Type u}
    [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    {q : ℝ} (hq : q ∈ Set.Icc 1 2) (V : Matrix H K ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix H H ℂ) (hA : A.PosSemidef) :
    cfc (fun x : ℝ => x ^ q) (Vᴴ * A * V) ≤
      Vᴴ * cfc (fun x : ℝ => x ^ q) A * V := by
  let Φ : Matrix H H ℂ →ₚ[ℂ] Matrix K K ℂ := PositiveLinearMap.mk₀
    { toFun := fun X => Vᴴ * X * V
      map_add' := by intro X Y; simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c X; simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
    (by intro X hX; exact ((Matrix.nonneg_iff_posSemidef.mp hX).conjTranspose_mul_mul_same V).nonneg)
  have hΦ : Φ 1 = 1 := by
    change Vᴴ * (1 : Matrix H H ℂ) * V = 1
    simpa only [Matrix.mul_one] using hV
  have hcond := D5.S3.Quantum.Lieb.PowerConvexity.condIciAll_rpow.{u} hq
  exact D5.S3.Quantum.Lieb.PositiveMapJensen.positive_unital_jensen
    (@hcond.1)
    (Real.continuous_rpow_const (by linarith [hq.1])).continuousOn Φ hΦ A hA

/-- Pinching bound for actual arbitrary rectangular complex row pieces.
The isometric embeddings form a complete local output resolution. -/
theorem row_piece_schattenPow_sum_le {I H C : Type u} {K : I → Type u}
    [Fintype I] [Fintype H] [DecidableEq H] [Fintype C] [DecidableEq C]
    [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    {q : ℝ} (hq : q ∈ Set.Icc 1 2)
    (V : ∀ i, Matrix H (K i) ℂ) (hV : ∀ i, (V i)ᴴ * V i = 1)
    (hres : ∑ i, V i * (V i)ᴴ = 1) (A : Matrix H C ℂ) :
    (∑ i, schattenPow (2 * q) ((V i)ᴴ * A)) ≤ schattenPow (2 * q) A := by
  have hq0 : 0 < q := by linarith [hq.1]
  let P := cfc (fun x : ℝ => x ^ q) (A * Aᴴ)
  have hi (i : I) : schattenPow (2 * q) ((V i)ᴴ * A) ≤
      (((V i)ᴴ * P * V i).trace).re := by
    rw [schattenPow_row_trace hq0]
    have hGram : ((V i)ᴴ * A) * ((V i)ᴴ * A)ᴴ = (V i)ᴴ * (A * Aᴴ) * V i := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [hGram]
    exact trace_re_mono (isometric_power_jensen hq (V i) (hV i)
      (A * Aᴴ) (Matrix.posSemidef_self_mul_conjTranspose A))
  calc
    _ ≤ ∑ i, (((V i)ᴴ * P * V i).trace).re := Finset.sum_le_sum (fun i _ => hi i)
    _ = (P * (∑ i, V i * (V i)ᴴ)).trace.re := by
      have hcycle (i : I) : (((V i)ᴴ * P * V i).trace).re =
          (P * (V i * (V i)ᴴ)).trace.re := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
      simp_rw [hcycle]
      rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum]
    _ = P.trace.re := by rw [hres, Matrix.mul_one]
    _ = schattenPow (2 * q) A := (schattenPow_row_trace hq0 A).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem Fq_finset_sum_ge {ι : Type*} {m : Type*} [Fintype m] [DecidableEq m] {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (s : Finset ι) (W : ι → Matrix (Fin 2) m ℝ)
    (hW : ∀ i ∈ s, ∀ b j, 0 ≤ W i b j) :
    (∑ i ∈ s, Fq q (W i)) ≤ Fq q (∑ i ∈ s, W i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Fq_nonneg q 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hiW := hW i (Finset.mem_insert_self i s)
    have hsW := fun k hk => hW k (Finset.mem_insert_of_mem hk)
    have hsnonneg : ∀ b j, 0 ≤ (∑ k ∈ s, W k) b j := by
      intro b j
      rw [Matrix.sum_apply]
      exact Finset.sum_nonneg (fun k hk => hsW k hk b j)
    have hstep := Fq_add_ge (m := m) hq1 hq2 (W i) (∑ k ∈ s, W k) hiW hsnonneg
    have hleft : Fq q (W i) + (∑ k ∈ s, Fq q (W k)) ≤
        Fq q (W i) + Fq q (∑ k ∈ s, W k) :=
      by have hI := ih hsW; linarith only [hI]
    apply le_trans hleft
    convert! hstep using 1 <;> rfl

section Families

variable {J H₀ H₁ : Type u} {C : J → Type u}
    [Fintype J] [DecidableEq J] [Fintype H₀] [DecidableEq H₀]
    [Fintype H₁] [DecidableEq H₁]
    [∀ j, Fintype (C j)] [∀ j, DecidableEq (C j)]

/-- The table consists of the actual p-th Schatten powers of the block maps. -/
def columnPowerTable (q : ℝ) (A : ∀ j, Matrix H₀ (C j) ℂ)
    (B : ∀ j, Matrix H₁ (C j) ℂ) : Matrix (Fin 2) J ℝ :=
  fun b j => if b = 0 then schattenPow (2 * q) (A j) else schattenPow (2 * q) (B j)

private theorem columnPowerTable_nonneg (q : ℝ) (A : ∀ j, Matrix H₀ (C j) ℂ)
    (B : ∀ j, Matrix H₁ (C j) ℂ) : ∀ b j, 0 ≤ columnPowerTable q A B b j := by
  intro b j
  unfold columnPowerTable
  split_ifs <;> exact schattenPow_nonneg _ _

private theorem Fq_columnPowerTable (q : ℝ) (A : ∀ j, Matrix H₀ (C j) ℂ)
    (B : ∀ j, Matrix H₁ (C j) ℂ) :
    Fq q (columnPowerTable q A B) = schattenPow (2 * q) (compression (2 * q) A B) := by
  unfold Fq
  congr 1
  ext b j
  simp only [Aq, columnPowerTable, compression, schattenNorm]
  split_ifs <;> rfl

/-- The actual two-row compression budgets satisfy the gluing estimate for
arbitrary finite complex column maps and complete orthogonal local outputs.
Both local output dimensions and every original column dimension may vary
or be empty. This consumes the all-real finite-power cone concavity. -/
theorem local_output_compression_budget {I : Type u} {K₀ K₁ : I → Type u}
    [Fintype I] [∀ i, Fintype (K₀ i)] [∀ i, DecidableEq (K₀ i)]
    [∀ i, Fintype (K₁ i)] [∀ i, DecidableEq (K₁ i)]
    {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (V₀ : ∀ i, Matrix H₀ (K₀ i) ℂ) (V₁ : ∀ i, Matrix H₁ (K₁ i) ℂ)
    (hV₀ : ∀ i, (V₀ i)ᴴ * V₀ i = 1) (hV₁ : ∀ i, (V₁ i)ᴴ * V₁ i = 1)
    (hres₀ : ∑ i, V₀ i * (V₀ i)ᴴ = 1) (hres₁ : ∑ i, V₁ i * (V₁ i)ᴴ = 1)
    (A : ∀ j, Matrix H₀ (C j) ℂ) (B : ∀ j, Matrix H₁ (C j) ℂ) :
    (∑ i, schattenPow (2 * q) (compression (2 * q)
      (fun j => (V₀ i)ᴴ * A j) (fun j => (V₁ i)ᴴ * B j))) ≤
      schattenPow (2 * q) (compression (2 * q) A B) := by
  let T := fun i => columnPowerTable q (fun j => (V₀ i)ᴴ * A j) (fun j => (V₁ i)ᴴ * B j)
  have hT (i : I) : ∀ b j, 0 ≤ T i b j := columnPowerTable_nonneg q _ _
  have hsum : ∀ b j, 0 ≤ (∑ i, T i) b j := by
    intro b j
    simp only [Matrix.sum_apply]
    exact Finset.sum_nonneg (fun i _ => hT i b j)
  have horder : ∀ b j, (∑ i, T i) b j ≤ columnPowerTable q A B b j := by
    intro b j
    rw [Matrix.sum_apply]
    by_cases hb : b = 0
    · simpa only [T, columnPowerTable, hb, ite_true, ite_false] using
        row_piece_schattenPow_sum_le ⟨hq1.le, hq2.le⟩ V₀ hV₀ hres₀ (A j)
    · simpa only [T, columnPowerTable, hb, ite_true, ite_false] using
        row_piece_schattenPow_sum_le ⟨hq1.le, hq2.le⟩ V₁ hV₁ hres₁ (B j)
  have h := (Fq_finset_sum_ge hq1 hq2 Finset.univ T (fun i _ => hT i)).trans
    (monotoneOn_Fq hq1 hq2 (∑ i, T i) (columnPowerTable q A B) hsum horder)
  simpa only [T, Fq_columnPowerTable] using h

end Families

end D5.S3.Quantum.NormCompression.LocalOutputGluing
