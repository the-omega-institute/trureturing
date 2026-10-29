/- GID: D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.claim; result=D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.result; claim=D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.claim
   digest: A mixed state on two by three levels violates skew-coherence polygamy. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.SLDSpectralEnergy

/-! A counterexample to Yu, arXiv:1704.04871v1, Eq. (2) and Appendix D. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Information.SkewCoherencePolygamyMixedRefutation

open Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.SLDSpectralEnergy
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

/-- Yu's skew-information coherence in the given reference basis. -/
def skewCoherence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) : ℝ :=
  1 - ∑ k, (CFC.sqrt ρ k k).re ^ 2

/-- Mixed-state polygamy in every bipartite total dimension at least six. -/
def claim : Prop :=
  ∀ m n : ℕ, 6 ≤ m * n →
    ∀ ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      IsDensity ρ →
        1 - skewCoherence ρ ≤
          (1 - skewCoherence (partialTraceRight ρ)) *
          (1 - skewCoherence (partialTraceLeft ρ))

private def rho : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
  fun p q =>
    if p.2 = 2 then
      if q.2 = 2 then (if p.1 = q.1 then 1 / 4 else 3 / 17) else 0
    else if q.2 = 2 then 0
    else if p = q then 1 / 8
    else if p.1 = q.1 ∨ p.2 = q.2 then 3 / 34 else 9 / 136

private def tau : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a c => if a = c then 1 / 2 else 6 / 17

private def beta : Matrix (Fin 3) (Fin 3) ℂ :=
  fun b d =>
    if b = 2 then (if d = 2 then 1 / 2 else 0)
    else if d = 2 then 0 else if b = d then 1 / 4 else 3 / 17

private def rootRho : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
  fun p q => (((if p.2 = 2 then
    if q.2 = 2 then
      Real.sqrt 29 + (if p.1 = q.1 then Real.sqrt 5 else -Real.sqrt 5)
    else 0
    else if q.2 = 2 then 0
    else if p = q then 5
    else if p.1 = q.1 ∨ p.2 = q.2 then 2 else 1) /
      (2 * Real.sqrt 68) : ℝ) : ℂ)

private def rootTau : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a c => (((Real.sqrt 29 +
    (if a = c then Real.sqrt 5 else -Real.sqrt 5)) /
      (2 * Real.sqrt 34) : ℝ) : ℂ)

private def rootBeta : Matrix (Fin 3) (Fin 3) ℂ :=
  fun b d => ((if b = 2 then (if d = 2 then 1 / Real.sqrt 2 else 0)
    else if d = 2 then 0
    else (Real.sqrt 29 + (if b = d then Real.sqrt 5 else -Real.sqrt 5)) /
      (2 * Real.sqrt 68) : ℝ) : ℂ)

private lemma coherence_complement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) :
    1 - skewCoherence ρ = ∑ k, (CFC.sqrt ρ k k).re ^ 2 := by
  change 1 - (1 - _) = _
  ring

private lemma root_rho_positive : rootRho.PosSemidef := by
  let r : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
    fun p q => (((if p.2 = 2 then
      if q.2 = 2 then
        Real.sqrt 29 + (if p.1 = q.1 then Real.sqrt 5 else -Real.sqrt 5)
      else 0
      else if q.2 = 2 then 0
      else if p = q then 5
      else if p.1 = q.1 ∨ p.2 = q.2 then 2 else 1) /
        (2 * Real.sqrt 68) : ℝ) : ℂ)
  let v : Fin 6 → (Fin 2 × Fin 3 → ℂ) := ![
    (fun p => if p.2 = 2 then 0 else 1),
    (fun p => if p.2 = 2 then 0 else if p.2 = 0 then 1 else -1),
    (fun p => if p.2 = 2 then 0 else if p.1 = 0 then 1 else -1),
    (fun p => if p.2 = 2 then 0 else
      (if p.1 = 0 then 1 else -1) * (if p.2 = 0 then 1 else -1)),
    (fun p => if p.2 = 2 then 1 else 0),
    (fun p => if p.2 = 2 then (if p.1 = 0 then 1 else -1) else 0)]
  let w : Fin 6 → ℝ := ![5 / 2, 1, 1, 1 / 2, Real.sqrt 29, Real.sqrt 5]
  have hw (k : Fin 6) : 0 ≤ w k := by
    fin_cases k <;> norm_num [w]
  have hp : (∑ k : Fin 6, w k • vecMulVec (v k) (star (v k))).PosSemidef :=
    Matrix.posSemidef_sum _ fun k _ =>
      (Matrix.posSemidef_vecMulVec_self_star (v k)).smul (hw k)
  have he : rootRho = (1 / (2 * Real.sqrt 68) : ℝ) •
      (∑ k : Fin 6, w k • vecMulVec (v k) (star (v k))) := by
    change r = _
    ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [r, Matrix.smul_apply, Matrix.sum_apply,
        Fin.sum_univ_succ, Matrix.vecMulVec_apply, Pi.star_apply, v, w,
        Complex.real_smul] <;> ring
  rw [he]
  exact hp.smul (by positivity)

private lemma root_rho_square : rootRho * rootRho = rho := by
  have root_rho_apply (p q : Fin 2 × Fin 3) :
      rootRho p q = (((if p.2 = 2 then
        if q.2 = 2 then
          Real.sqrt 29 + (if p.1 = q.1 then Real.sqrt 5 else -Real.sqrt 5)
        else 0
        else if q.2 = 2 then 0 else if p = q then 5
        else if p.1 = q.1 ∨ p.2 = q.2 then 2 else 1) /
          (2 * Real.sqrt 68) : ℝ) : ℂ) := rfl
  have rho_apply (p q : Fin 2 × Fin 3) :
      rho p q = if p.2 = 2 then
        if q.2 = 2 then (if p.1 = q.1 then 1 / 4 else 3 / 17) else 0
      else if q.2 = 2 then 0 else if p = q then 1 / 8
      else if p.1 = q.1 ∨ p.2 = q.2 then 3 / 34 else 9 / 136 := rfl
  have cast_one := Complex.ofReal_one.symm
  have cast_nat (n : ℕ) [n.AtLeastTwo] := (Complex.ofReal_ofNat n).symm
  have cast_mul := fun x y : ℝ => (Complex.ofReal_mul x y).symm
  have cast_div := fun x y : ℝ => (Complex.ofReal_div x y).symm
  have cast_add := fun x y : ℝ => (Complex.ofReal_add x y).symm
  have cast_inv := fun x : ℝ => (Complex.ofReal_inv x).symm
  have cast_neg := fun x : ℝ => (Complex.ofReal_neg x).symm
  have cast_sub := fun x y : ℝ => (Complex.ofReal_sub x y).symm
  have h68 : Real.sqrt 68 ≠ 0 := by positivity
  have hs68 := Real.sq_sqrt (show (0 : ℝ) ≤ 68 by norm_num)
  have hs29 := Real.sq_sqrt (show (0 : ℝ) ≤ 29 by norm_num)
  have hs5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_succ,
      root_rho_apply, rho_apply] <;>
    simp only [cast_one, cast_nat, cast_mul, cast_div, cast_add, cast_inv,
      cast_neg, cast_sub, Complex.ofReal_inj] <;> field_simp <;> nlinarith

private lemma rho_density : IsDensity rho := by
  constructor
  · have hp := Matrix.posSemidef_conjTranspose_mul_self rootRho
    rw [root_rho_positive.isHermitian.eq, root_rho_square] at hp
    exact hp
  · let d : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
      fun p q =>
        if p.2 = 2 then
          if q.2 = 2 then (if p.1 = q.1 then 1 / 4 else 3 / 17) else 0
        else if q.2 = 2 then 0
        else if p = q then 1 / 8
        else if p.1 = q.1 ∨ p.2 = q.2 then 3 / 34 else 9 / 136
    change (∑ p, d p p) = 1
    norm_num [d, Fintype.sum_prod_type, Fin.sum_univ_succ]

private lemma marginal_right : partialTraceRight rho = tau := by
  let d : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
    fun p q =>
      if p.2 = 2 then
        if q.2 = 2 then (if p.1 = q.1 then 1 / 4 else 3 / 17) else 0
      else if q.2 = 2 then 0
      else if p = q then 1 / 8
      else if p.1 = q.1 ∨ p.2 = q.2 then 3 / 34 else 9 / 136
  let t : Matrix (Fin 2) (Fin 2) ℂ :=
    fun a c => if a = c then 1 / 2 else 6 / 17
  ext a c
  change (∑ b : Fin 3, d (a, b) (c, b)) = t a c
  fin_cases a <;> fin_cases c <;>
    norm_num [d, t, Fin.sum_univ_succ]

private lemma marginal_left : partialTraceLeft rho = beta := by
  let d : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
    fun p q =>
      if p.2 = 2 then
        if q.2 = 2 then (if p.1 = q.1 then 1 / 4 else 3 / 17) else 0
      else if q.2 = 2 then 0
      else if p = q then 1 / 8
      else if p.1 = q.1 ∨ p.2 = q.2 then 3 / 34 else 9 / 136
  let t : Matrix (Fin 3) (Fin 3) ℂ :=
    fun b d =>
      if b = 2 then (if d = 2 then 1 / 2 else 0)
      else if d = 2 then 0 else if b = d then 1 / 4 else 3 / 17
  ext b e
  change (∑ a : Fin 2, d (a, b) (a, e)) = t b e
  fin_cases b <;> fin_cases e <;>
    norm_num [d, t, Fin.sum_univ_succ]

private lemma root_tau_positive : rootTau.PosSemidef := by
  let r : Matrix (Fin 2) (Fin 2) ℂ :=
    fun a c => (((Real.sqrt 29 +
      (if a = c then Real.sqrt 5 else -Real.sqrt 5)) /
        (2 * Real.sqrt 34) : ℝ) : ℂ)
  let v : Fin 2 → ℂ := ![1, -1]
  have hp : (Real.sqrt 29 • vecMulVec (fun _ : Fin 2 => (1 : ℂ))
      (star (fun _ : Fin 2 => (1 : ℂ))) +
      Real.sqrt 5 • vecMulVec v (star v)).PosSemidef :=
    ((Matrix.posSemidef_vecMulVec_self_star _).smul (Real.sqrt_nonneg 29)).add
      ((Matrix.posSemidef_vecMulVec_self_star v).smul (Real.sqrt_nonneg 5))
  have he : rootTau = (1 / (2 * Real.sqrt 34) : ℝ) •
      (Real.sqrt 29 • vecMulVec (fun _ : Fin 2 => (1 : ℂ))
        (star (fun _ : Fin 2 => (1 : ℂ))) +
        Real.sqrt 5 • vecMulVec v (star v)) := by
    change r = _
    ext a c
    fin_cases a <;> fin_cases c <;>
      simp only [r, Matrix.smul_apply, Matrix.add_apply,
        Matrix.vecMulVec_apply, Pi.star_apply] <;>
      norm_num [v, Complex.real_smul] <;> ring
  rw [he]
  exact hp.smul (by positivity)

private lemma root_tau_square : rootTau * rootTau = tau := by
  have root_tau_apply (a c : Fin 2) :
      rootTau a c = (((Real.sqrt 29 +
        (if a = c then Real.sqrt 5 else -Real.sqrt 5)) /
          (2 * Real.sqrt 34) : ℝ) : ℂ) := rfl
  have tau_apply (a c : Fin 2) :
      tau a c = if a = c then 1 / 2 else 6 / 17 := rfl
  have cast_one := Complex.ofReal_one.symm
  have cast_nat (n : ℕ) [n.AtLeastTwo] := (Complex.ofReal_ofNat n).symm
  have cast_mul := fun x y : ℝ => (Complex.ofReal_mul x y).symm
  have cast_div := fun x y : ℝ => (Complex.ofReal_div x y).symm
  have cast_add := fun x y : ℝ => (Complex.ofReal_add x y).symm
  have cast_inv := fun x : ℝ => (Complex.ofReal_inv x).symm
  have cast_neg := fun x : ℝ => (Complex.ofReal_neg x).symm
  have cast_sub := fun x y : ℝ => (Complex.ofReal_sub x y).symm
  have h34 : Real.sqrt 34 ≠ 0 := by positivity
  have hs34 := Real.sq_sqrt (show (0 : ℝ) ≤ 34 by norm_num)
  have hs29 := Real.sq_sqrt (show (0 : ℝ) ≤ 29 by norm_num)
  have hs5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  ext a c
  fin_cases a <;> fin_cases c <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, root_tau_apply, tau_apply] <;>
    simp only [cast_one, cast_nat, cast_mul, cast_div, cast_add, cast_inv,
      cast_neg, cast_sub, Complex.ofReal_inj] <;> field_simp <;> nlinarith

private lemma root_beta_positive : rootBeta.PosSemidef := by
  let r : Matrix (Fin 3) (Fin 3) ℂ :=
    fun b d => ((if b = 2 then (if d = 2 then 1 / Real.sqrt 2 else 0)
      else if d = 2 then 0
      else (Real.sqrt 29 + (if b = d then Real.sqrt 5 else -Real.sqrt 5)) /
        (2 * Real.sqrt 68) : ℝ) : ℂ)
  let v : Fin 3 → ℂ := ![1, 1, 0]
  let w : Fin 3 → ℂ := ![1, -1, 0]
  let z : Fin 3 → ℂ := ![0, 0, 1]
  have hp : (Real.sqrt 29 • vecMulVec v (star v) +
      Real.sqrt 5 • vecMulVec w (star w)).PosSemidef :=
    ((Matrix.posSemidef_vecMulVec_self_star v).smul (Real.sqrt_nonneg 29)).add
      ((Matrix.posSemidef_vecMulVec_self_star w).smul (Real.sqrt_nonneg 5))
  have he : rootBeta = (1 / (2 * Real.sqrt 68) : ℝ) •
      (Real.sqrt 29 • vecMulVec v (star v) +
        Real.sqrt 5 • vecMulVec w (star w)) +
      (1 / Real.sqrt 2 : ℝ) • vecMulVec z (star z) := by
    change r = _
    ext b d
    fin_cases b <;> fin_cases d <;>
      simp only [r, Matrix.smul_apply, Matrix.add_apply,
        Matrix.vecMulVec_apply, Pi.star_apply] <;>
      norm_num [v, w, z, Complex.real_smul] <;> ring
  rw [he]
  exact (hp.smul (by positivity)).add
    ((Matrix.posSemidef_vecMulVec_self_star z).smul (by positivity))

private lemma root_beta_square : rootBeta * rootBeta = beta := by
  have root_beta_apply (b d : Fin 3) :
      rootBeta b d = ((if b = 2 then (if d = 2 then 1 / Real.sqrt 2 else 0)
        else if d = 2 then 0
        else (Real.sqrt 29 + (if b = d then Real.sqrt 5 else -Real.sqrt 5)) /
          (2 * Real.sqrt 68) : ℝ) : ℂ) := rfl
  have beta_apply (b d : Fin 3) :
      beta b d = if b = 2 then (if d = 2 then 1 / 2 else 0)
      else if d = 2 then 0 else if b = d then 1 / 4 else 3 / 17 := rfl
  have cast_one := Complex.ofReal_one.symm
  have cast_nat (n : ℕ) [n.AtLeastTwo] := (Complex.ofReal_ofNat n).symm
  have cast_mul := fun x y : ℝ => (Complex.ofReal_mul x y).symm
  have cast_div := fun x y : ℝ => (Complex.ofReal_div x y).symm
  have cast_add := fun x y : ℝ => (Complex.ofReal_add x y).symm
  have cast_inv := fun x : ℝ => (Complex.ofReal_inv x).symm
  have cast_neg := fun x : ℝ => (Complex.ofReal_neg x).symm
  have cast_sub := fun x y : ℝ => (Complex.ofReal_sub x y).symm
  have h68 : Real.sqrt 68 ≠ 0 := by positivity
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hs68 := Real.sq_sqrt (show (0 : ℝ) ≤ 68 by norm_num)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs29 := Real.sq_sqrt (show (0 : ℝ) ≤ 29 by norm_num)
  have hs5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  ext b d
  fin_cases b <;> fin_cases d <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, root_beta_apply, beta_apply] <;>
    simp only [cast_one, cast_nat, cast_mul, cast_div, cast_add, cast_inv,
      cast_neg, cast_sub, Complex.ofReal_inj] <;> field_simp <;> nlinarith

private lemma sqrt_rho : CFC.sqrt rho = rootRho := by
  exact (CFC.sqrt_eq_iff rho rootRho rho_density.1.nonneg
    root_rho_positive.nonneg).2 root_rho_square

private lemma sqrt_tau : CFC.sqrt tau = rootTau := by
  have hp := partialTraceRight_posSemidef rho_density.1
  rw [marginal_right] at hp
  exact (CFC.sqrt_eq_iff tau rootTau hp.nonneg root_tau_positive.nonneg).2 root_tau_square

private lemma sqrt_beta : CFC.sqrt beta = rootBeta := by
  have hp := partialTraceLeft_posSemidef rho_density.1
  rw [marginal_left] at hp
  exact (CFC.sqrt_eq_iff beta rootBeta hp.nonneg root_beta_positive.nonneg).2 root_beta_square

private lemma value_rho :
    1 - skewCoherence rho = (25 / 34 + (1 / 2 + Real.sqrt 145 / 34)) / 2 := by
  have he := congrArg (fun a : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ =>
    ∑ k, (a k k).re ^ 2) sqrt_rho
  refine (coherence_complement rho).trans (he.trans ?_)
  let r : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
    fun p q => (((if p.2 = 2 then
      if q.2 = 2 then
        Real.sqrt 29 + (if p.1 = q.1 then Real.sqrt 5 else -Real.sqrt 5)
      else 0
      else if q.2 = 2 then 0
      else if p = q then 5
      else if p.1 = q.1 ∨ p.2 = q.2 then 2 else 1) /
        (2 * Real.sqrt 68) : ℝ) : ℂ)
  change (∑ k, (r k k).re ^ 2) = _
  have h68 : Real.sqrt 68 ≠ 0 := by positivity
  have h34 : Real.sqrt 34 ≠ 0 := by positivity
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hs68 := Real.sq_sqrt (show (0 : ℝ) ≤ 68 by norm_num)
  have hs34 := Real.sq_sqrt (show (0 : ℝ) ≤ 34 by norm_num)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs29 := Real.sq_sqrt (show (0 : ℝ) ≤ 29 by norm_num)
  have hs5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hm : Real.sqrt 29 * Real.sqrt 5 = Real.sqrt 145 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  simp only [r, Fintype.sum_prod_type, Fin.sum_univ_succ, Complex.ofReal_re]
  norm_num
  field_simp
  nlinarith

private lemma value_tau :
    1 - skewCoherence tau = 1 / 2 + Real.sqrt 145 / 34 := by
  have he := congrArg (fun a : Matrix (Fin 2) (Fin 2) ℂ =>
    ∑ k, (a k k).re ^ 2) sqrt_tau
  refine (coherence_complement tau).trans (he.trans ?_)
  let r : Matrix (Fin 2) (Fin 2) ℂ :=
    fun a c => (((Real.sqrt 29 +
      (if a = c then Real.sqrt 5 else -Real.sqrt 5)) /
        (2 * Real.sqrt 34) : ℝ) : ℂ)
  change (∑ k, (r k k).re ^ 2) = _
  have h68 : Real.sqrt 68 ≠ 0 := by positivity
  have h34 : Real.sqrt 34 ≠ 0 := by positivity
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hs68 := Real.sq_sqrt (show (0 : ℝ) ≤ 68 by norm_num)
  have hs34 := Real.sq_sqrt (show (0 : ℝ) ≤ 34 by norm_num)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs29 := Real.sq_sqrt (show (0 : ℝ) ≤ 29 by norm_num)
  have hs5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hm : Real.sqrt 29 * Real.sqrt 5 = Real.sqrt 145 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  simp only [r, Fin.sum_univ_succ, Complex.ofReal_re]
  norm_num
  field_simp
  nlinarith

private lemma value_beta :
    1 - skewCoherence beta = ((1 / 2 + Real.sqrt 145 / 34) + 1) / 2 := by
  have he := congrArg (fun a : Matrix (Fin 3) (Fin 3) ℂ =>
    ∑ k, (a k k).re ^ 2) sqrt_beta
  refine (coherence_complement beta).trans (he.trans ?_)
  let r : Matrix (Fin 3) (Fin 3) ℂ :=
    fun b d => ((if b = 2 then (if d = 2 then 1 / Real.sqrt 2 else 0)
      else if d = 2 then 0
      else (Real.sqrt 29 + (if b = d then Real.sqrt 5 else -Real.sqrt 5)) /
        (2 * Real.sqrt 68) : ℝ) : ℂ)
  change (∑ k, (r k k).re ^ 2) = _
  have h68 : Real.sqrt 68 ≠ 0 := by positivity
  have h34 : Real.sqrt 34 ≠ 0 := by positivity
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hs68 := Real.sq_sqrt (show (0 : ℝ) ≤ 68 by norm_num)
  have hs34 := Real.sq_sqrt (show (0 : ℝ) ≤ 34 by norm_num)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs29 := Real.sq_sqrt (show (0 : ℝ) ≤ 29 by norm_num)
  have hs5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hm : Real.sqrt 29 * Real.sqrt 5 = Real.sqrt 145 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  simp only [r, Fin.sum_univ_succ, Complex.ofReal_re]
  norm_num
  field_simp
  nlinarith

private lemma violation_gap :
    (1 - skewCoherence rho) -
      (1 - skewCoherence tau) * (1 - skewCoherence beta) =
        (208 - 17 * Real.sqrt 145) / 1156 := by
  have he := congrArg₂ (fun a b : ℝ => a - b) value_rho
    (congrArg₂ (fun a b : ℝ => a * b) value_tau value_beta)
  refine he.trans ?_
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 145 by norm_num)
  nlinarith

private lemma strict_violation :
    (1 - skewCoherence tau) * (1 - skewCoherence beta) < 1 - skewCoherence rho := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 145 by norm_num)
  have hn := Real.sqrt_nonneg (145 : ℝ)
  have hlt : 17 * Real.sqrt 145 < 208 := by nlinarith
  have hpos : 0 < (208 - 17 * Real.sqrt 145) / 1156 := by linarith
  exact sub_pos.mp (lt_of_lt_of_eq hpos violation_gap.symm)

/-- The registered two by three mixed state refutes the conjecture. -/
theorem result : ¬ claim := by
  intro h
  have hi := h 2 3 (by norm_num) rho rho_density
  have hr := congrArg (fun a : Matrix (Fin 2) (Fin 2) ℂ => 1 - skewCoherence a)
    marginal_right
  have hl := congrArg (fun b : Matrix (Fin 3) (Fin 3) ℂ => 1 - skewCoherence b)
    marginal_left
  exact (not_le_of_gt strict_violation)
    (le_of_le_of_eq hi (congrArg₂ (fun x y : ℝ => x * y) hr hl))

end

end D5.S3.Quantum.Information.SkewCoherencePolygamyMixedRefutation
