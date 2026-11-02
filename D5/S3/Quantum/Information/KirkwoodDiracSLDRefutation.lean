/- GID: D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/KirkwoodDiracSLDRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation.claim; result=D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation.result; claim=D5/S3/Quantum/Information/KirkwoodDiracSLDRefutation.claim
   digest: A dimension-nine KD-real SLD counterexample to the mixed-state conjecture. -/


import D5.S3.Quantum.Information.FisherDiscord.Defs
import D5.S3.Quantum.Information.SLDSpectralEnergy
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
Public declarations retain the source's literal qLeft, symbolLeft, IsKDReal and claim bodies;
proofs use the existing IsDensity, IsSLD and fisherSLD owners rather than duplicate definitions.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
qLeft, symbolLeft, IsKDReal and claim are definition declarations; result has proof_shape: bind-only under the open-problem-resolution basis.
qLeft: proof_shape: definition; escape_witness: none.
symbolLeft: proof_shape: definition; escape_witness: none.
IsKDReal: proof_shape: definition; escape_witness: none.
claim: proof_shape: definition; escape_witness: none.
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#22488; Refuted)
Direct frozen dependencies: D5/S3/Quantum/Information/SLDSpectralEnergy.IsDensity (declaration statement_id sha256:a10738dfb34d3f9f15b31e2052545ae2dd6f812042123ae918dc2a16912f1e85); D5/S3/Quantum/Information/FisherDiscord/Defs.IsSLD (declaration statement_id sha256:d30ae5ab817bda3eb2639fac27e80267bd55b577c4aa8d9fe42dceb809167fac); D5/S3/Quantum/Information/FisherDiscord/Defs.fisherSLD (declaration statement_id sha256:a10e9fb09ad396c68000881b5cddbd6a1d3087ccbce5f1749b87d1f238bc798c).
Private auxiliary declarations are consumed on the live result path and are all proof_shape: bind-only; none is an escape witness.
-/


set_option maxHeartbeats 20000000
set_option maxRecDepth 4000
noncomputable section
open scoped Matrix BigOperators ComplexOrder

namespace D5.S3.Quantum.Information.KirkwoodDiracSLDRefutation

namespace SprietKirkwoodDiracSLD
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.Information.FisherDiscord.Defs (IsSLD fisherSLD)

/-- The left KD distribution Q^{KD,ℓ}_{x,k}(C). -/
def qLeft {d : ℕ} (a b : Matrix.unitaryGroup (Fin d) ℂ)
    (C : Matrix (Fin d) (Fin d) ℂ) (x k : Fin d) : ℂ :=
  star (((a : Matrix (Fin d) (Fin d) ℂ)ᴴ * (b : Matrix (Fin d) (Fin d) ℂ)) x k) *
    (((a : Matrix (Fin d) (Fin d) ℂ)ᴴ * C * (b : Matrix (Fin d) (Fin d) ℂ)) x k)

/-- The literal observable symbol: inverse overlap times the matrix coefficient. -/
noncomputable def symbolLeft {d : ℕ} (a b : Matrix.unitaryGroup (Fin d) ℂ)
    (C : Matrix (Fin d) (Fin d) ℂ) (x k : Fin d) : ℂ :=
  (((a : Matrix (Fin d) (Fin d) ℂ)ᴴ * (b : Matrix (Fin d) (Fin d) ℂ)) x k)⁻¹ *
    (((a : Matrix (Fin d) (Fin d) ℂ)ᴴ * C * (b : Matrix (Fin d) (Fin d) ℂ)) x k)

/-- V^{sa}_{KD,real}: Hermitian operators whose left KD symbol is real everywhere. -/
def IsKDReal {d : ℕ} (a b : Matrix.unitaryGroup (Fin d) ℂ)
    (C : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  C.IsHermitian ∧ ∀ (x : Fin d) (k : Fin d), (symbolLeft a b C x k).im = 0

/-- The source assertion, quoted from arXiv:2511.01996v2, §6.3 immediately after (6.23):
"In view of what precedes, it is tempting to conjecture that, if \hat \rho and \hat X are both KD real, the optimal observable \hat L must not be KD-real itself, provided \rm I_{QF} does not vanish." -/
def claim : Prop :=
  ∀ (d : ℕ), 0 < d →
    ∀ (a : Matrix.unitaryGroup (Fin d) ℂ) (b : Matrix.unitaryGroup (Fin d) ℂ),
      (∀ (x : Fin d) (k : Fin d),
        (((a : Matrix (Fin d) (Fin d) ℂ)ᴴ * (b : Matrix (Fin d) (Fin d) ℂ)) x k) ≠ 0) →
      ∀ (ρ : Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ),
        IsDensity ρ →
        IsKDReal a b ρ → IsKDReal a b X →
        (∃ (L : Matrix (Fin d) (Fin d) ℂ), IsSLD ρ X L) ∧
          ∀ (L : Matrix (Fin d) (Fin d) ℂ),
            IsSLD ρ X L → 4 * fisherSLD ρ L ≠ 0 → ¬ IsKDReal a b L

end SprietKirkwoodDiracSLD

namespace Probe
private noncomputable def z : ℂ := ⟨-1/2, Real.sqrt 3 / 2⟩
private noncomputable def ph (n : ℕ) : ℂ :=
  if n % 3 = 0 then 1 else if n % 3 = 1 then z else star z
private noncomputable def fourier : Matrix (Fin 9) (Fin 9) ℂ := fun x k =>
  ph ((x.val / 3) * (k.val / 3) + (x.val % 3) * (k.val % 3)) / 3

private noncomputable def proj : Matrix (Fin 9) (Fin 9) ℂ :=
  !![⟨(1 / 3), 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(1 / 3), 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(1 / 3), 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨(1 / 3), 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 6), (-1 / 6) * Real.sqrt 3⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 6), (1 / 6) * Real.sqrt 3⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨(1 / 3), 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 6), (1 / 6) * Real.sqrt 3⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 6), (-1 / 6) * Real.sqrt 3⟩;
    ⟨(1 / 3), 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(1 / 3), 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(1 / 3), 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨(-1 / 6), (1 / 6) * Real.sqrt 3⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(1 / 3), 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 6), (-1 / 6) * Real.sqrt 3⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 6), (-1 / 6) * Real.sqrt 3⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(1 / 3), 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 6), (1 / 6) * Real.sqrt 3⟩;
    ⟨(1 / 3), 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(1 / 3), 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(1 / 3), 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨(-1 / 6), (-1 / 6) * Real.sqrt 3⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 6), (1 / 6) * Real.sqrt 3⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(1 / 3), 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 6), (1 / 6) * Real.sqrt 3⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 6), (-1 / 6) * Real.sqrt 3⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(1 / 3), 0⟩]
private noncomputable def obs : Matrix (Fin 9) (Fin 9) ℂ :=
  !![⟨0, 0⟩, ⟨(1 / 2), 0⟩, ⟨(1 / 2), 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨(1 / 2), 0⟩, ⟨0, 0⟩, ⟨(1 / 2), 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨(1 / 2), 0⟩, ⟨(1 / 2), 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 4), (1 / 4) * Real.sqrt 3⟩, ⟨(-1 / 4), (-1 / 4) * Real.sqrt 3⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 4), (-1 / 4) * Real.sqrt 3⟩, ⟨0, 0⟩, ⟨(-1 / 4), (1 / 4) * Real.sqrt 3⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 4), (1 / 4) * Real.sqrt 3⟩, ⟨(-1 / 4), (-1 / 4) * Real.sqrt 3⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 4), (-1 / 4) * Real.sqrt 3⟩, ⟨(-1 / 4), (1 / 4) * Real.sqrt 3⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 4), (1 / 4) * Real.sqrt 3⟩, ⟨0, 0⟩, ⟨(-1 / 4), (-1 / 4) * Real.sqrt 3⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 4), (-1 / 4) * Real.sqrt 3⟩, ⟨(-1 / 4), (1 / 4) * Real.sqrt 3⟩, ⟨0, 0⟩]
private noncomputable def sld : Matrix (Fin 9) (Fin 9) ℂ :=
  !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 9) * Real.sqrt 3, 0⟩, ⟨(1 / 9) * Real.sqrt 3, 0⟩, ⟨0, 0⟩, ⟨(1 / 9) * Real.sqrt 3, 0⟩, ⟨(-1 / 9) * Real.sqrt 3, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 18) * Real.sqrt 3, (-1 / 6)⟩, ⟨0, 0⟩, ⟨(1 / 18) * Real.sqrt 3, (1 / 6)⟩, ⟨(1 / 18) * Real.sqrt 3, (-1 / 6)⟩, ⟨0, 0⟩, ⟨(-1 / 18) * Real.sqrt 3, (1 / 6)⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(1 / 18) * Real.sqrt 3, (-1 / 6)⟩, ⟨(-1 / 18) * Real.sqrt 3, (1 / 6)⟩, ⟨0, 0⟩, ⟨(-1 / 18) * Real.sqrt 3, (-1 / 6)⟩, ⟨(1 / 18) * Real.sqrt 3, (1 / 6)⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨(-1 / 18) * Real.sqrt 3, (1 / 6)⟩, ⟨(1 / 18) * Real.sqrt 3, (1 / 6)⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(1 / 18) * Real.sqrt 3, (-1 / 6)⟩, ⟨(-1 / 18) * Real.sqrt 3, (-1 / 6)⟩;
    ⟨(-1 / 9) * Real.sqrt 3, 0⟩, ⟨0, 0⟩, ⟨(-1 / 18) * Real.sqrt 3, (-1 / 6)⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(-1 / 18) * Real.sqrt 3, (1 / 6)⟩, ⟨0, 0⟩, ⟨(-1 / 9) * Real.sqrt 3, 0⟩;
    ⟨(1 / 9) * Real.sqrt 3, 0⟩, ⟨(1 / 18) * Real.sqrt 3, (-1 / 6)⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨(1 / 18) * Real.sqrt 3, (1 / 6)⟩, ⟨(1 / 9) * Real.sqrt 3, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨(1 / 18) * Real.sqrt 3, (1 / 6)⟩, ⟨(-1 / 18) * Real.sqrt 3, (1 / 6)⟩, ⟨0, 0⟩, ⟨(-1 / 18) * Real.sqrt 3, (-1 / 6)⟩, ⟨(1 / 18) * Real.sqrt 3, (-1 / 6)⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨(1 / 9) * Real.sqrt 3, 0⟩, ⟨0, 0⟩, ⟨(1 / 18) * Real.sqrt 3, (-1 / 6)⟩, ⟨(1 / 18) * Real.sqrt 3, (1 / 6)⟩, ⟨0, 0⟩, ⟨(1 / 9) * Real.sqrt 3, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨(-1 / 9) * Real.sqrt 3, 0⟩, ⟨(-1 / 18) * Real.sqrt 3, (-1 / 6)⟩, ⟨0, 0⟩, ⟨(-1 / 18) * Real.sqrt 3, (1 / 6)⟩, ⟨(-1 / 9) * Real.sqrt 3, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

private noncomputable def rho : Matrix (Fin 9) (Fin 9) ℂ := (1/12 : ℝ) • (1 + proj)

set_option Elab.async false in
private theorem sqrt3_sq : Real.sqrt 3 ^ 2 = (3 : ℝ) := by
  exact Real.sq_sqrt (by norm_num)

set_option Elab.async false in
private theorem sqrt3_cube : Real.sqrt 3 ^ 3 = (3 : ℝ) * Real.sqrt 3 := by
  rw [pow_succ, sqrt3_sq]


set_option Elab.async false in
private theorem phase_norm (n : ℕ) : ph n * star (ph n) = 1 := by
  unfold ph
  split_ifs <;> apply Complex.ext <;> norm_num [z, Complex.mul_re, Complex.mul_im]
    <;> (try constructor) <;> nlinarith [sqrt3_sq]

set_option Elab.async false in
private theorem fourier_inverse (x k : Fin 9) :
    (fourier x k)⁻¹ = 9 * star (fourier x k) := by
  apply inv_eq_of_mul_eq_one_right
  calc
    fourier x k * (9 * star (fourier x k)) =
        ph ((x.val / 3) * (k.val / 3) + (x.val % 3) * (k.val % 3)) *
          star (ph ((x.val / 3) * (k.val / 3) + (x.val % 3) * (k.val % 3))) := by
      simp [fourier]
      ring
    _ = 1 := phase_norm _

set_option Elab.async false in
private theorem fourier_nonzero (x k : Fin 9) : fourier x k ≠ 0 := by
  intro h
  have hn := phase_norm ((x.val / 3) * (k.val / 3) + (x.val % 3) * (k.val % 3))
  have hz : ph ((x.val / 3) * (k.val / 3) + (x.val % 3) * (k.val % 3)) = 0 := by
    simpa [fourier] using h
  rw [hz] at hn
  norm_num at hn

set_option Elab.async false in
private theorem fourier_unitary : fourierᴴ * fourier = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;>
    norm_num only [fourier, ph, z, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply,
      Matrix.cons_val, RCLike.ofReal_eq_complex_ofReal, ↓reduceIte,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.add_apply, Matrix.one_apply,
      Fin.sum_univ_zero, Fin.coe_ofNat_eq_mod, Fin.isValue, Fin.ext_iff, Fin.val_ofNat,
      Fin.val_natCast, Fin.val_zero, Fin.val_one, Fin.val_succ, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
      mul_zero, zero_mul, one_mul, mul_one, add_zero, zero_add, sub_zero, zero_sub,
      neg_zero, neg_neg, and_true, true_and]
    <;> (try constructor) <;> ring_nf <;> simp only [sqrt3_sq] <;> ring

private noncomputable def baseA : Matrix.unitaryGroup (Fin 9) ℂ := 1
private noncomputable def baseB : Matrix.unitaryGroup (Fin 9) ℂ :=
  ⟨fourier, Matrix.mem_unitaryGroup_iff'.mpr fourier_unitary⟩


set_option Elab.async false in
private theorem obs_hermitian : obs.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obs, Complex.ext_iff] <;> (try constructor) <;> ring

set_option Elab.async false in
private theorem sld_hermitian : sld.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sld, Complex.ext_iff] <;> (try constructor) <;> ring

set_option Elab.async false in
private theorem proj_gram : projᴴ * proj = proj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;>
    norm_num only [proj, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Matrix.cons_val, RCLike.ofReal_eq_complex_ofReal, ↓reduceIte,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.add_apply, Matrix.one_apply,
      Fin.sum_univ_zero, Fin.coe_ofNat_eq_mod, Fin.isValue, Fin.ext_iff, Fin.val_ofNat,
      Fin.val_natCast, Fin.val_zero, Fin.val_one, Fin.val_succ, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
      mul_zero, zero_mul, one_mul, mul_one, add_zero, zero_add, sub_zero, zero_sub,
      neg_zero, neg_neg, and_true, true_and]
    <;> (try constructor) <;> ring_nf <;> simp only [sqrt3_sq] <;> ring

set_option Elab.async false in
private theorem rho_positive : rho.PosDef := by
  unfold rho
  have hp : proj.PosSemidef := by
    rw [← proj_gram]
    exact Matrix.posSemidef_conjTranspose_mul_self proj
  exact (Matrix.PosDef.one.add_posSemidef hp).smul (by norm_num : (0:ℝ) < 1/12)

set_option Elab.async false in
private theorem rho_trace : Matrix.trace rho = 1 := by
  norm_num [rho, proj, Matrix.trace, Matrix.diag, Fin.sum_univ_succ,
    Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, Complex.ext_iff, Complex.mul_re, Complex.mul_im]

set_option Elab.async false in
private theorem rho_coefficient (x k : Fin 9) :
    ((9 * star (fourier x k)) * ((rho * fourier) x k)).im = 0 := by
  fin_cases x <;> fin_cases k <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    norm_num only [rho, proj, fourier, ph, z, Matrix.mul_apply, Matrix.smul_apply,
      RCLike.real_smul_eq_coe_mul, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply,
      Matrix.cons_val, RCLike.ofReal_eq_complex_ofReal, ↓reduceIte,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.add_apply, Matrix.one_apply,
      Fin.sum_univ_zero, Fin.coe_ofNat_eq_mod, Fin.isValue, Fin.ext_iff, Fin.val_ofNat,
      Fin.val_natCast, Fin.val_zero, Fin.val_one, Fin.val_succ, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
      mul_zero, zero_mul, one_mul, mul_one, add_zero, zero_add, sub_zero, zero_sub,
      neg_zero, neg_neg, and_true, true_and]
    <;> (try constructor) <;> ring_nf <;> simp only [sqrt3_sq, sqrt3_cube] <;> ring

set_option Elab.async false in
private theorem obs_coefficient (x k : Fin 9) :
    ((9 * star (fourier x k)) * ((obs * fourier) x k)).im = 0 := by
  fin_cases x <;> fin_cases k <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    norm_num only [obs, fourier, ph, z, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq_apply,
      Matrix.cons_val, RCLike.ofReal_eq_complex_ofReal, ↓reduceIte,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.add_apply, Matrix.one_apply,
      Fin.sum_univ_zero, Fin.coe_ofNat_eq_mod, Fin.isValue, Fin.ext_iff, Fin.val_ofNat,
      Fin.val_natCast, Fin.val_zero, Fin.val_one, Fin.val_succ, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
      mul_zero, zero_mul, one_mul, mul_one, add_zero, zero_add, sub_zero, zero_sub,
      neg_zero, neg_neg, and_true, true_and]
    <;> (try constructor) <;> ring_nf <;> simp only [sqrt3_sq, sqrt3_cube] <;> ring

set_option Elab.async false in
private theorem sld_coefficient (x k : Fin 9) :
    ((9 * star (fourier x k)) * ((sld * fourier) x k)).im = 0 := by
  fin_cases x <;> fin_cases k <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ] <;>
    norm_num only [sld, fourier, ph, z, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq_apply,
      Matrix.cons_val, RCLike.ofReal_eq_complex_ofReal, ↓reduceIte,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.add_apply, Matrix.one_apply,
      Fin.sum_univ_zero, Fin.coe_ofNat_eq_mod, Fin.isValue, Fin.ext_iff, Fin.val_ofNat,
      Fin.val_natCast, Fin.val_zero, Fin.val_one, Fin.val_succ, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
      mul_zero, zero_mul, one_mul, mul_one, add_zero, zero_add, sub_zero, zero_sub,
      neg_zero, neg_neg, and_true, true_and]
    <;> (try constructor) <;> ring_nf <;> simp only [sqrt3_sq] <;> ring


set_option Elab.async false in
private theorem sld_equation :
    Complex.I • (rho * obs - obs * rho) = (1/2 : ℂ) • (sld * rho + rho * sld) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    norm_num only [rho, proj, obs, sld, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
      RCLike.real_smul_eq_coe_mul, Fin.sum_univ_succ, Complex.ext_iff,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq_apply,
      Matrix.cons_val, RCLike.ofReal_eq_complex_ofReal, ↓reduceIte,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.add_apply, Matrix.one_apply,
      Fin.sum_univ_zero, Fin.coe_ofNat_eq_mod, Fin.isValue, Fin.ext_iff, Fin.val_ofNat,
      Fin.val_natCast, Fin.val_zero, Fin.val_one, Fin.val_succ, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
      mul_zero, zero_mul, one_mul, mul_one, add_zero, zero_add, sub_zero, zero_sub,
      neg_zero, neg_neg, and_true, true_and]
    <;> (try constructor) <;> ring_nf <;> simp only [sqrt3_sq] <;> ring

set_option Elab.async false in
private theorem qfi_value :
    (Matrix.trace (rho * sld * sld)).re = 1/6 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]
  norm_num [rho, proj, sld, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.smul_apply,
    RCLike.real_smul_eq_coe_mul, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]
  <;> (try constructor) <;> nlinarith [sqrt3_sq]


set_option Elab.async false in
private theorem kd_real_of_coefficient (C : Matrix (Fin 9) (Fin 9) ℂ) (hC : C.IsHermitian)
    (h : ∀ x k, ((9 * star (fourier x k)) * ((C * fourier) x k)).im = 0) :
    SprietKirkwoodDiracSLD.IsKDReal baseA baseB C := by
  refine ⟨hC, ?_⟩
  intro x k
  simpa only [SprietKirkwoodDiracSLD.symbolLeft, baseA, baseB,
    Matrix.UnitaryGroup.one_val, Matrix.conjTranspose_one, Matrix.one_mul,
    fourier_inverse] using h x k
end Probe

namespace SprietKirkwoodDiracSLD
open scoped Matrix ComplexOrder

theorem result : ¬ claim := by
  intro h
  have hn : ∀ x k, (((Probe.baseA : Matrix (Fin 9) (Fin 9) ℂ)ᴴ *
      (Probe.baseB : Matrix (Fin 9) (Fin 9) ℂ)) x k) ≠ 0 := by
    simpa only [Probe.baseA, Probe.baseB, Matrix.UnitaryGroup.one_val,
      Matrix.conjTranspose_one, Matrix.one_mul] using Probe.fourier_nonzero
  have hr := Probe.kd_real_of_coefficient Probe.rho Probe.rho_positive.isHermitian Probe.rho_coefficient
  have hx := Probe.kd_real_of_coefficient Probe.obs Probe.obs_hermitian Probe.obs_coefficient
  have hl := Probe.kd_real_of_coefficient Probe.sld Probe.sld_hermitian Probe.sld_coefficient
  have hq : 4 * D5.S3.Quantum.Information.FisherDiscord.Defs.fisherSLD Probe.rho Probe.sld ≠ 0 := by
    unfold D5.S3.Quantum.Information.FisherDiscord.Defs.fisherSLD
    rw [Probe.qfi_value]
    norm_num
  exact (h 9 (by norm_num) Probe.baseA Probe.baseB hn Probe.rho Probe.obs
    ⟨Probe.rho_positive.posSemidef, Probe.rho_trace⟩ hr hx).2 Probe.sld
      ⟨Probe.sld_hermitian, Probe.sld_equation⟩ hq hl

end SprietKirkwoodDiracSLD

end D5.S3.Quantum.Information.KirkwoodDiracSLDRefutation
