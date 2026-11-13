/- GID: D5/S3/ContinuousObservables/PhaseSynthesisLifting
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/PhaseSynthesisLifting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native phase factors lift on the same projected unitary encoding. -/

import D5.S3.ContinuousObservables.ProjectedUnitaryLifting
import D5.S3.ContinuousObservables.PhaseSynthesis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0; the full license is in
`docs/reports/licenses/auto-res-lean-qsvt-LICENSE.txt`.
Authors of the reused proofs: shosonoda.

Original source: auto-res/lean-qsvt@42c4b9149d5957db497e4226bc02da92d10f7a3c,
QSVT/QSP/Conversion.lean, Wrot_eq_Rref through seqW_apply_zero_zero_eq.
The native scalar interface reuses PhaseSynthesis.mul_signal_phase and its original
polynomial recursion. The conversion preserves the 00 entry; its full matrix formula
retains a right diagonal factor and a power of i.
Replace the transplanted conversion when equivalent declarations are available at the
receiver's own pinned Mathlib revision.
-/
namespace D5.S3.ContinuousObservables.PhaseSynthesisLifting

open Matrix Complex D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Scalar
open scoped Real

private theorem phaseZ_mul_phaseZ (φ ψ : ℝ) : phaseZ φ * phaseZ ψ = phaseZ (φ + ψ) := by
  simp only [phaseZ, Matrix.mul_fin_two, mul_zero, add_zero, zero_mul, zero_add, ← Complex.exp_add]
  congr 2 <;> push_cast <;> ring_nf


private theorem Wrot_eq_Rref (x : ℝ) :
    Wrot x = I • (phaseZ (-(π / 4)) * Rref x * phaseZ (-(π / 4))) := by
  set e : ℂ := Complex.exp (I * ((-(π / 4) : ℝ) : ℂ)) with he_def
  set f : ℂ := Complex.exp (-(I * ((-(π / 4) : ℝ) : ℂ))) with hf_def
  have he : e * e = -I := by
    rw [he_def, ← Complex.exp_add]
    refine Eq.trans ?_ Complex.exp_neg_pi_div_two_mul_I
    congr 1; push_cast; ring
  have hf : f * f = I := by
    rw [hf_def, ← Complex.exp_add]
    refine Eq.trans ?_ Complex.exp_pi_div_two_mul_I
    congr 1; push_cast; ring
  have hef : e * f = 1 := by
    rw [he_def, hf_def, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hP : phaseZ (-(π / 4)) = !![e, 0; 0, f] := rfl
  rw [hP]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Wrot, Rref]
  · linear_combination (-I * (x : ℂ)) * he + (x : ℂ) * I_sq
  · linear_combination (-(Real.sqrt (1 - x ^ 2) : ℂ)) * hef
  · linear_combination (-(Real.sqrt (1 - x ^ 2) : ℂ)) * hef
  · linear_combination (I * (x : ℂ)) * hf + (x : ℂ) * I_sq


private theorem phaseZ_mul_Wrot_mul_phaseZ (φ ψ x : ℝ) :
    phaseZ φ * Wrot x * phaseZ ψ = I • (phaseZ (φ - π / 4) * Rref x * phaseZ (ψ - π / 4)) := by
  rw [Wrot_eq_Rref, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc phaseZ φ * (phaseZ (-(π / 4)) * Rref x * phaseZ (-(π / 4))) * phaseZ ψ
      = (phaseZ φ * phaseZ (-(π / 4))) * Rref x * (phaseZ (-(π / 4)) * phaseZ ψ) := by
        simp only [mul_assoc]
    _ = _ := by rw [phaseZ_mul_phaseZ, phaseZ_mul_phaseZ, ← sub_eq_add_neg, neg_add_eq_sub]


private theorem seqW_cons (φ₀ φ x : ℝ) (Φ : List ℝ) :
    seqW φ₀ (φ :: Φ) x = I • (phaseZ (φ₀ - π / 4) * Rref x * seqW (φ - π / 4) Φ x) := by
  simp only [seqW, List.map_cons, List.prod_cons]
  rw [← mul_assoc, ← mul_assoc, phaseZ_mul_Wrot_mul_phaseZ, Matrix.smul_mul]
  simp only [mul_assoc]


noncomputable def shift (φ₀ : ℝ) (Φ' : List ℝ) : List ℝ :=
  (φ₀ - π / 4) :: Φ'.dropLast.map (· - π / 2)


private theorem seqW_append_singleton (φ₀ ψ x : ℝ) (L : List ℝ) :
    seqW φ₀ (L ++ [ψ]) x =
      (I ^ (L.length + 1)) •
        (seqR ((φ₀ - π / 4) :: L.map (· - π / 2)) x * phaseZ (ψ - π / 4)) := by
  induction L generalizing φ₀ with
  | nil =>
    rw [List.nil_append, seqW_cons, seqW, List.map_nil, List.prod_nil, mul_one]
    simp [seqR, mul_assoc]
  | cons φ L ih =>
    rw [List.cons_append, seqW_cons, ih, Matrix.mul_smul, smul_smul, ← pow_succ',
      List.length_cons, List.map_cons]
    congr 1
    rw [show φ - π / 4 - π / 4 = φ - π / 2 by ring]
    simp only [seqR, mul_assoc]


private theorem seqW_eq_seqR (φ₀ x : ℝ) {Φ' : List ℝ} (hΦ : Φ' ≠ []) :
    seqW φ₀ Φ' x =
      (I ^ Φ'.length) • (seqR (shift φ₀ Φ') x * phaseZ (Φ'.getLast hΦ - π / 4)) := by
  obtain ⟨L, ψ, rfl⟩ : ∃ L ψ, Φ' = L ++ [ψ] := by
    rcases List.eq_nil_or_concat Φ' with h | ⟨L, ψ, h⟩
    · exact absurd h hΦ
    · exact ⟨L, ψ, by simpa using h⟩
  rw [seqW_append_singleton, shift, List.dropLast_concat, List.getLast_concat,
    List.length_append, List.length_singleton]


private theorem phaseZ_mul_apply_zero_zero (a : ℝ) (M : M₂) :
    (phaseZ a * M) 0 0 = Complex.exp (I * a) * M 0 0 := by
  simp [phaseZ, Matrix.mul_apply, Fin.sum_univ_two]


private theorem mul_phaseZ_apply_zero_zero (a : ℝ) (M : M₂) :
    (M * phaseZ a) 0 0 = M 0 0 * Complex.exp (I * a) := by
  simp [phaseZ, Matrix.mul_apply, Fin.sum_univ_two]


private theorem I_pow_eq_exp (d : ℕ) : I ^ d = Complex.exp (I * (((d : ℝ) * (π / 2) : ℝ) : ℂ)) := by
  have h : Complex.exp (I * (((d : ℝ) * (π / 2) : ℝ) : ℂ)) = Complex.exp (π / 2 * I) ^ d := by
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [h, Complex.exp_pi_div_two_mul_I]


noncomputable def cor8Phases (φ₀ : ℝ) (Φ' : List ℝ) (hΦ : Φ' ≠ []) : List ℝ :=
  (φ₀ + Φ'.getLast hΦ + ((Φ'.length : ℝ) - 1) * (π / 2)) :: Φ'.dropLast.map (· - π / 2)

@[simp]
private theorem cor8Phases_length (φ₀ : ℝ) (Φ' : List ℝ) (hΦ : Φ' ≠ []) :
    (cor8Phases φ₀ Φ' hΦ).length = Φ'.length := by
  simp only [cor8Phases, List.length_cons, List.length_map, List.length_dropLast]
  have := List.length_pos_of_ne_nil hΦ
  omega


private theorem seqW_apply_zero_zero_eq (φ₀ x : ℝ) {Φ' : List ℝ} (hΦ : Φ' ≠ []) :
    (seqW φ₀ Φ' x) 0 0 = (seqR (cor8Phases φ₀ Φ' hΦ) x) 0 0 := by
  rw [seqW_eq_seqR φ₀ x hΦ, shift, cor8Phases, seqR, seqR, Matrix.smul_apply,
    smul_eq_mul, mul_phaseZ_apply_zero_zero, mul_assoc (phaseZ (φ₀ - π / 4)),
    mul_assoc (phaseZ (φ₀ + Φ'.getLast hΦ + ((Φ'.length : ℝ) - 1) * (π / 2))),
    phaseZ_mul_apply_zero_zero, phaseZ_mul_apply_zero_zero, I_pow_eq_exp]
  have key : Complex.exp (I * (((Φ'.length : ℝ) * (π / 2) : ℝ) : ℂ)) *
      Complex.exp (I * ((φ₀ - π / 4 : ℝ) : ℂ)) *
      Complex.exp (I * ((Φ'.getLast hΦ - π / 4 : ℝ) : ℂ)) =
      Complex.exp (I * ((φ₀ + Φ'.getLast hΦ + ((Φ'.length : ℝ) - 1) * (π / 2) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  linear_combination (Rref x * seqR (Φ'.dropLast.map (· - π / 2)) x) 0 0 * key

end D5.S3.ContinuousObservables.PhaseSynthesisLifting

namespace D5.S3.ContinuousObservables.PhaseSynthesisLifting
open Polynomial Complex Matrix
open D5.S3.ContinuousObservables.ProjectedUnitaryLifting
open D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Scalar
open D5.S3.ContinuousObservables.IntervalSOSCompletion
open D5.S3.ContinuousObservables.IntervalSOSCompletion.Poly
open D5.S3.ContinuousObservables.PhaseSynthesis

private theorem seqW_row {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (φ₀ : ℝ) (Φ : List ℝ) :
    seqW φ₀ Φ x 0 0 = (qspPolyW φ₀ Φ).1.eval (x : ℂ) ∧
    seqW φ₀ Φ x 0 1 = I * (qspPolyW φ₀ Φ).2.eval (x : ℂ) *
      (Real.sqrt (1 - x ^ 2) : ℂ) := by
  have hc : x ^ 2 + Real.sqrt (1 - x ^ 2) ^ 2 = 1 := by
    rw [Real.sq_sqrt (by nlinarith [hx.1, hx.2])]
    ring
  induction Φ using List.reverseRecOn with
  | nil => simp [seqW, phaseZ, qspPolyW_nil]
  | append_singleton Φ φ ih =>
    have hstep := PhaseSynthesis.mul_signal_phase hc φ
      ((qspPolyW φ₀ Φ).1.eval (x : ℂ))
      ((qspPolyW φ₀ Φ).2.eval (x : ℂ)) 0 0
    have hzero := congrArg (fun M : Matrix (ZMod 2) (ZMod 2) ℂ => M 0 0) hstep
    have hone := congrArg (fun M : Matrix (ZMod 2) (ZMod 2) ℂ => M 0 1) hstep
    have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    simp only [PhaseSynthesis.matrix2, Matrix.mul_apply, hu, Finset.sum_insert,
      Finset.mem_singleton, zero_ne_one, not_false_eq_true, Finset.sum_singleton,
      ite_true, ite_false, one_ne_zero, zero_mul, mul_zero, add_zero, zero_add] at hzero hone
    have hcat : seqW φ₀ (Φ ++ [φ]) x = seqW φ₀ Φ x * (Wrot x * phaseZ φ) := by
      simp only [seqW, List.map_append, List.prod_append, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    rw [hcat, qspPolyW_concat]
    simp only [stepW, eval_mul, eval_C, eval_add, eval_X, eval_sub, eval_pow, eval_one,
      Matrix.mul_apply, Fin.sum_univ_two, Wrot, phaseZ, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      mul_zero, zero_mul, add_zero, zero_add, ih.1, ih.2]
    exact ⟨hzero, hone⟩

private theorem reflection_entry {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (φ₀ : ℝ) (Φ : List ℝ) (hne : Φ ≠ []) :
    seqR (cor8Phases φ₀ Φ hne) x 0 0 = (qspPolyW φ₀ Φ).1.eval (x : ℂ) := by
  rw [← seqW_apply_zero_zero_eq φ₀ x hne]
  exact (seqW_row hx φ₀ Φ).1

/-- The original native completion, phase tuple and signed-circle field also give the
compressed polynomial of the original raw projected unitary. -/
theorem native_phase_lifting
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H]
    (rawU Pi PiTilde : H →ₗ[ℂ] H)
    (hU : star rawU * rawU = 1) (hU' : rawU * star rawU = 1)
    (hPi : IsStarProjection Pi) (hPiTilde : IsStarProjection PiTilde)
    (d : ℕ) (hd : 0 < d) (p : ℝ[X]) (hp : p.natDegree ≤ d)
    (hpar : HasParity (p.map (algebraMap ℝ ℂ)) d)
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∃ (B C : ℝ[X]) (Ufield : D5.S3.ContinuousObservables.CentralWinding.CyclicObservable 2)
      (φ₀ : ℝ) (Φ : List ℝ) (hne : Φ ≠ []),
      1 - p ^ 2 = B ^ 2 + (1 - X ^ 2) * C ^ 2 ∧
      B.natDegree ≤ d ∧ C.natDegree ≤ d - 1 ∧ (d = 0 → C = 0) ∧
      HasParity (B.map (algebraMap ℝ ℂ)) d ∧
      HasParity (C.map (algebraMap ℝ ℂ)) (d - 1) ∧
      Ufield = phaseCompletion p B C ∧ star Ufield * Ufield = 1 ∧
      Ufield * star Ufield = 1 ∧ (∀ t, (Ufield t).det = 1) ∧
      (∀ t, (Ufield t 0 0).re = p.eval
        (D5.S3.ContinuousObservables.CentralWinding.windingPhase t).re) ∧
      Φ.length = d ∧
      qspPolyW φ₀ Φ = (p.map (algebraMap ℝ ℂ) + Polynomial.C I * B.map (algebraMap ℝ ℂ),
        C.map (algebraMap ℝ ℂ)) ∧ phaseProduct φ₀ Φ = Ufield ∧
      let Ψ := cor8Phases φ₀ Φ hne
      let P := p.map (algebraMap ℝ ℂ) + Polynomial.C I * B.map (algebraMap ℝ ℂ)
      let E := ofRaw rawU Pi PiTilde hU hU' hPi hPiTilde
      let A := PiTilde * rawU * Pi
      Ψ.length = d ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, seqR Ψ x 0 0 = P.eval (x : ℂ)) ∧
      (Even d → Pi * altSeq E Ψ * Pi =
        Pi * aeval (LinearMap.adjoint A * A) (evenRoot P) * Pi) ∧
      (Odd d → PiTilde * altSeq E Ψ * Pi =
        A * aeval (LinearMap.adjoint A * A) (oddRoot P)) := by
  obtain ⟨B, C, Ufield, φ₀, Φ, hsos, hB, hC, hC0, hBp, hCp,
    hfield, hleft, hright, hdet, hre, hlen, hpair, hproduct⟩ :=
    exists_phase_factorization d p hp hpar (fun x hx =>
      (sq_le_one_iff_abs_le_one _).mpr (hbound x hx))
  have hne : Φ ≠ [] := by intro h; simp [h] at hlen; omega
  let Ψ := cor8Phases φ₀ Φ hne
  let P := p.map (algebraMap ℝ ℂ) + Polynomial.C I * B.map (algebraMap ℝ ℂ)
  let E := ofRaw rawU Pi PiTilde hU hU' hPi hPiTilde
  have hlenΨ : Ψ.length = d := by simp [Ψ, hlen]
  have hPpar : HasParity P d := hpar.add (hBp.C_mul I)
  have hentry : ∀ x ∈ Set.Icc (0 : ℝ) 1, seqR Ψ x 0 0 = P.eval (x : ℂ) := by
    intro x hx
    rw [reflection_entry ⟨by linarith [hx.1], hx.2⟩ φ₀ Φ hne, hpair]
  let R := if Even d then evenRoot P else oddRoot P
  have hscalar : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      seqR Ψ x 0 0 = if Even Ψ.length then R.eval ((x : ℂ) ^ 2)
        else (x : ℂ) * R.eval ((x : ℂ) ^ 2) := by
    intro x hx
    rw [hentry x hx, hlenΨ]
    by_cases he : Even d
    · simp only [R, ite_eq_left he]
      exact (hPpar.1 he).eval_eq _
    · simp only [R, ite_eq_right he]
      have hodd := (hPpar.2 (Nat.not_even_iff_odd.mp he)).eq_X_mul_oddRoot_comp
      conv_lhs => rw [hodd]
      simp only [eval_mul, eval_X, eval_comp, eval_pow]
  have hlift := polynomial_lifting E Ψ R hscalar
  refine ⟨B, C, Ufield, φ₀, Φ, hne, hsos, hB, hC, hC0, hBp, hCp,
    hfield, hleft, hright, hdet, hre, hlen, hpair, hproduct, hlenΨ, hentry, ?_, ?_⟩
  · intro he
    have h := hlift.1 (by rwa [hlenΨ])
    simpa only [R, ite_eq_left he, E, Ψ, P, ofRaw, Encoding.ProjUnitaryEncoding.encoded] using h
  · intro ho
    have he := Nat.not_even_iff_odd.mpr ho
    have h := hlift.2 (by rwa [hlenΨ])
    simpa only [R, ite_eq_right he, E, Ψ, P, ofRaw, Encoding.ProjUnitaryEncoding.encoded] using h

end D5.S3.ContinuousObservables.PhaseSynthesisLifting
