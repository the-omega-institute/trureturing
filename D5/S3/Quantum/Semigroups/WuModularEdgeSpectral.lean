/- GID: D5/S3/Quantum/Semigroups/WuModularEdgeSpectral
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuModularEdgeSpectral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite paired Gibbs jump trace as a common real-power spectral edge sum. -/

import D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization
import D5.S3.Quantum.Lieb.PositiveMapJensen
import D5.S3.Quantum.Recovery.BKMRelativeDensity

/-!
The ordinary-trace energy in Wu, arXiv:2610.33686v1, (3.54), has a per-entry
representation for paired modular jumps. The positive and zero spectral endpoint
products give separate formulas in the same eigenframe of the density.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open _root_.Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Semigroups.WuModularEdgeSpectral

open D5.S3.Quantum.Matrix.SpectralPower (mpow mpow_one)
open D5.S3.Quantum.Lieb.PositiveMapJensen (cfc_intertwining)
open D5.S3.Quantum.Recovery.BKMRelativeDensity (mpow_smul_of_nonneg)

variable {n : Type*} [Fintype n] [DecidableEq n]

private def eigenbasis {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ :=
  (Unitary.conjStarAlgAut ℂ _ hρ.eigenvectorUnitary).symm

/-- The squared entry of the physical jump in the spectral frame of the density. -/
def edgeWeight {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (J : Matrix n n ℂ) (i j : n) : ℝ :=
  Complex.normSq (eigenbasis hρ J i j)

private theorem eigenbasis_adjoint {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (J : Matrix n n ℂ) :
    eigenbasis hρ Jᴴ = (eigenbasis hρ J)ᴴ := by
  exact map_star (eigenbasis hρ) J

private theorem edgeWeight_adjoint {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (J : Matrix n n ℂ) (i j : n) :
    edgeWeight hρ Jᴴ j i = edgeWeight hρ J i j := by
  rw [edgeWeight, eigenbasis_adjoint, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.normSq_conj, edgeWeight]

private theorem eigenbasis_cfc {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (f : ℝ → ℝ) :
    eigenbasis hρ (cfc f ρ) = diagonal (fun i => (f (hρ.eigenvalues i) : ℂ)) := by
  simp only [hρ.cfc_eq, Matrix.IsHermitian.cfc, eigenbasis, StarAlgEquiv.symm_apply_apply,
    RCLike.ofReal_eq_complex_ofReal]
  rfl

private theorem trace_eigenbasis {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (A : Matrix n n ℂ) :
    (eigenbasis hρ A).trace = A.trace := by
  rw [eigenbasis, Unitary.conjStarAlgAut_symm_apply, Matrix.trace_mul_cycle,
    ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.one_mul]

/-- Mixed real powers use the same squared entries for any exponents on the same density. -/
private theorem trace_mpow_sandwich {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (J : Matrix n n ℂ) (p q : ℝ) :
    (mpow ρ p * (J * mpow ρ q * Jᴴ)).trace.re =
      ∑ i, ∑ j, hρ.eigenvalues i ^ p * hρ.eigenvalues j ^ q * edgeWeight hρ J i j := by
  rw [← trace_eigenbasis hρ (mpow ρ p * (J * mpow ρ q * Jᴴ))]
  simp only [map_mul, eigenbasis_adjoint, mpow, eigenbasis_cfc, ← Matrix.mul_assoc]
  exact WuCubicConditionalTensorization.trace_diagonal_overlap _ _ _

private theorem trace_mpow_sandwich_adjoint {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (J : Matrix n n ℂ) (p q : ℝ) :
    (mpow ρ p * (Jᴴ * mpow ρ q * J)).trace.re =
      ∑ i, ∑ j, hρ.eigenvalues j ^ p * hρ.eigenvalues i ^ q * edgeWeight hρ J i j := by
  calc
    _ = ∑ i, ∑ j, hρ.eigenvalues i ^ p * hρ.eigenvalues j ^ q * edgeWeight hρ Jᴴ i j := by
      simpa only [Matrix.conjTranspose_conjTranspose] using trace_mpow_sandwich hρ Jᴴ p q
    _ = _ := by
      rw [Finset.sum_comm (f := fun i j =>
        hρ.eigenvalues i ^ p * hρ.eigenvalues j ^ q * edgeWeight hρ Jᴴ i j)]
      simp only [edgeWeight_adjoint]

private theorem mpow_zero_hermitian {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    mpow ρ 0 = 1 := by
  simpa only [mpow, Real.rpow_zero] using cfc_const_one ℝ ρ hρ.isSelfAdjoint

private theorem mpow_mul_complement {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (p : ℝ) :
    mpow ρ (1 - p) * mpow ρ p = ρ := by
  apply (eigenbasis hρ.isHermitian).injective
  have hid : eigenbasis hρ.isHermitian ρ =
      diagonal (fun i => (hρ.isHermitian.eigenvalues i : ℂ)) := by
    rw [eigenbasis, Unitary.conjStarAlgAut_symm,
      hρ.isHermitian.conjStarAlgAut_star_eigenvectorUnitary]
    rfl
  rw [map_mul]
  change eigenbasis hρ.isHermitian (cfc (fun x : ℝ => x ^ (1 - p)) ρ) *
      eigenbasis hρ.isHermitian (cfc (fun x : ℝ => x ^ p) ρ) = eigenbasis hρ.isHermitian ρ
  rw [eigenbasis_cfc, eigenbasis_cfc, hid, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  simp only [Pi.mul_apply, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  have he : 1 - p + p = (1 : ℝ) := sub_add_cancel 1 p
  have hn : 1 - p + p ≠ 0 := he.symm ▸ one_ne_zero
  rw [← Real.rpow_add' (hρ.eigenvalues_nonneg i) hn, he, Real.rpow_one]

private theorem mpow_comp_nonneg {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    mpow (mpow ρ p) q = mpow ρ (p * q) := by
  have hρp : (0 : Matrix n n ℂ) ≤ CFC.rpow ρ p := CFC.rpow_nonneg
  change cfc (fun x : ℝ => x ^ q) (mpow ρ p) = cfc (fun x : ℝ => x ^ (p * q)) ρ
  rw [show mpow ρ p = CFC.rpow ρ p from (CFC.rpow_eq_cfc_real hρ.nonneg).symm,
    ← CFC.rpow_eq_cfc_real hρp, ← CFC.rpow_eq_cfc_real hρ.nonneg]
  exact CFC.rpow_rpow_of_exponent_nonneg ρ p q hp hq hρ.nonneg

private theorem mpow_adjoint {D : Matrix n n ℂ} (p : ℝ) :
    (mpow D p)ᴴ = mpow D p := by
  change IsSelfAdjoint (cfc (fun x : ℝ => x ^ p) D)
  exact cfc_predicate _ _

private theorem mpow_modular {D J : Matrix n n ℂ} (hD : D.PosDef)
    {q p : ℝ} (hq : 0 < q) (hp : 0 ≤ p) (hJ : D * J = q • (J * D)) :
    mpow D p * J = q ^ p • (J * mpow D p) := by
  have hqD : (q • D).IsHermitian := by
    change (q • D)ᴴ = q • D
    rw [Matrix.conjTranspose_smul, star_trivial, hD.isHermitian.eq]
  have h := cfc_intertwining D (q • D) hD.isHermitian hqD J
    (by simpa only [Matrix.mul_smul] using hJ) (fun x => x ^ p)
  change mpow D p * J = J * mpow (q • D) p at h
  rw [mpow_smul_of_nonneg hD.posSemidef.nonneg hq.le hp, Matrix.mul_smul] at h
  exact h

omit [DecidableEq n] in
private theorem modular_adjoint {D J : Matrix n n ℂ} (hD : D.IsHermitian)
    {q : ℝ} (hq : q ≠ 0) (hJ : D * J = q • (J * D)) :
    D * Jᴴ = q⁻¹ • (Jᴴ * D) := by
  have h := congrArg (fun A : Matrix n n ℂ => Aᴴ) hJ
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, star_trivial, hD.eq] at h
  rw [h, smul_smul, inv_mul_cancel₀ hq, one_smul]

private def dissipator (V X : Matrix n n ℂ) : Matrix n n ℂ :=
  (1 / 2 : ℝ) • ((Vᴴ * V) * X + X * (Vᴴ * V)) - Vᴴ * X * V

private theorem embed_dissipator {D V : Matrix n n ℂ} (hD : D.PosDef)
    {q g : ℝ} (hq : 0 < q) (hg : 0 ≤ g) (hV : D * V = q • (V * D))
    (M : Matrix n n ℂ) :
    let G := mpow D g
    let H := mpow D (-g)
    G * dissipator V (H * M * H) * G =
      (1 / 2 : ℝ) • ((Vᴴ * V) * M + M * (Vᴴ * V)) -
        (q⁻¹) ^ (g + g) • (Vᴴ * M * V) := by
  let G := mpow D g
  let H := mpow D (-g)
  let P := Vᴴ * V
  let c := (q⁻¹) ^ g
  change G * dissipator V (H * M * H) * G =
    (1 / 2 : ℝ) • (P * M + M * P) - (q⁻¹) ^ (g + g) • (Vᴴ * M * V)
  have hG : G = CFC.rpow D g := (CFC.rpow_eq_cfc_real hD.posSemidef.nonneg).symm
  have hH : H = CFC.rpow D (-g) := (CFC.rpow_eq_cfc_real hD.posSemidef.nonneg).symm
  have hGH : G * H = 1 := by
    rw [hG, hH]
    exact CFC.rpow_mul_rpow_neg g hD.isStrictlyPositive
  have hHG : H * G = 1 := by
    rw [hH, hG]
    exact CFC.rpow_neg_mul_rpow g hD.isStrictlyPositive
  have hgV : G * V = q ^ g • (V * G) := mpow_modular hD hq hg hV
  have hgAdj : G * Vᴴ = c • (Vᴴ * G) :=
    mpow_modular hD (inv_pos.mpr hq) hg (modular_adjoint hD.isHermitian hq.ne' hV)
  have hc : c * q ^ g = 1 := by
    dsimp only [c]
    rw [← Real.mul_rpow (inv_nonneg.mpr hq.le) hq.le, inv_mul_cancel₀ hq.ne', Real.one_rpow]
  have hP : G * P = P * G := by
    change G * (Vᴴ * V) = (Vᴴ * V) * G
    rw [← Matrix.mul_assoc, hgAdj, Matrix.smul_mul, Matrix.mul_assoc, hgV, Matrix.mul_smul,
      smul_smul, hc, one_smul, Matrix.mul_assoc]
  have hLeft : G * (P * (H * M * H)) * G = P * M := by
    calc
      _ = (G * P) * H * M * (H * G) := by simp only [Matrix.mul_assoc]
      _ = _ := by simp only [hP, Matrix.mul_assoc P G H, hGH, hHG, Matrix.mul_one]
  have hRight : G * ((H * M * H) * P) * G = M * P := by
    calc
      _ = (G * H) * M * (H * P * G) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        simp only [Matrix.mul_assoc H P G, ← hP, ← Matrix.mul_assoc H G P,
          hGH, hHG, Matrix.one_mul]
  have hLower : G * Vᴴ * H = c • Vᴴ := by
    rw [hgAdj, Matrix.smul_mul, Matrix.mul_assoc, hGH, Matrix.mul_one]
  have hUpper : H * V * G = c • V := by
    have h := congrArg (fun A : Matrix n n ℂ => Aᴴ) hLower
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_smul, star_trivial, mpow_adjoint, H, G, Matrix.mul_assoc] using h
  have hMixed : G * (Vᴴ * (H * M * H) * V) * G =
      (q⁻¹) ^ (g + g) • (Vᴴ * M * V) := by
    calc
      _ = (G * Vᴴ * H) * M * (H * V * G) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hLower, hUpper, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        dsimp only [c]
        rw [Real.rpow_add (inv_pos.mpr hq)]
  simp only [dissipator, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
  rw [hLeft, hRight, hMixed]

/-- Paired dissipators with the physical rates `2a` and `2b`. -/
def pairedGenerator (a b : ℝ) (J X : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 * a) • dissipator J X + (2 * b) • dissipator Jᴴ X

/-- One quarter of the ordinary embedded trace, so multiplication by `s * s/(s-1)`
gives the energy normalization of the exponent reduction. -/
private def pairedTrace (s a b : ℝ) (D ρ J : Matrix n n ℂ) : ℝ :=
  let G := mpow D (1 / (2 * s))
  let H := mpow D (-(1 / (2 * s)))
  let M := mpow ρ (1 / s)
  (1 / 4 : ℝ) * (mpow M (s - 1) * (G * pairedGenerator a b J (H * M * H) * G)).trace.re

private theorem embedded_dissipator_trace {D ρ V : Matrix n n ℂ} (hD : D.PosDef)
    (hρ : ρ.PosSemidef) {q g : ℝ} (hq : 0 < q) (hg : 0 ≤ g)
    (hV : D * V = q • (V * D)) (p : ℝ) :
    let G := mpow D g
    let H := mpow D (-g)
    let M := mpow ρ p
    let Q := mpow ρ (1 - p)
    (Q * (G * dissipator V (H * M * H) * G)).trace.re =
      (ρ * (Vᴴ * V)).trace.re -
        (q⁻¹) ^ (g + g) * (Q * (Vᴴ * M * V)).trace.re := by
  let M := mpow ρ p
  let Q := mpow ρ (1 - p)
  let P := Vᴴ * V
  have hQM : Q * M = ρ := mpow_mul_complement hρ p
  have hMQ : M * Q = ρ := by
    simpa only [show 1 - (1 - p) = p by ring] using mpow_mul_complement hρ (1 - p)
  have hLeft : (Q * (P * M)).trace = (ρ * P).trace := by
    rw [Matrix.trace_mul_cycle', ← Matrix.mul_assoc M Q P, hMQ]
  have hRight : (Q * (M * P)).trace = (ρ * P).trace := by
    rw [← Matrix.mul_assoc, hQM]
  change (Q * (mpow D g * dissipator V (mpow D (-g) * M * mpow D (-g)) *
      mpow D g)).trace.re = (ρ * P).trace.re - (q⁻¹) ^ (g + g) * (Q * (Vᴴ * M * V)).trace.re
  rw [embed_dissipator hD hq hg hV M]
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_add, Complex.sub_re, Complex.smul_re, Complex.add_re,
    smul_eq_mul]
  rw [hLeft, hRight]
  ring

/-- The contribution of an edge with weighted endpoint eigenvalues `u` and `v`. -/
private def edgeKernel (p u v : ℝ) : ℝ :=
  (u + v - (v ^ (1 - p) * u ^ p + u ^ (1 - p) * v ^ p)) / 2

private theorem rate_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : ℝ) :
    a * (b / a) ^ p = a ^ (1 - p) * b ^ p := by
  rw [Real.div_rpow hb.le ha.le, Real.rpow_sub ha, Real.rpow_one]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos ha p)]

/-- Paired modular jumps have an exact edge expansion for every real `s > 1`.
The intertwining premise is the modular eigenjump equation with the faithful
Gibbs matrix on the right. The density may be singular. -/
private theorem pairedTrace_eq_edges {D ρ J : Matrix n n ℂ} (hD : D.PosDef) (hρ : ρ.PosSemidef)
    {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 1 < s)
    (hJ : D * J = (a / b) • (J * D)) :
    pairedTrace s a b D ρ J =
      ∑ i, ∑ j, edgeWeight hρ.isHermitian J i j *
        edgeKernel (1 / s) (b * hρ.isHermitian.eigenvalues i)
          (a * hρ.isHermitian.eigenvalues j) := by
  let p : ℝ := 1 / s
  let g : ℝ := 1 / (2 * s)
  let eigenvalue := hρ.isHermitian.eigenvalues
  let w := edgeWeight hρ.isHermitian J
  have hs₀ : 0 < s := lt_trans zero_lt_one hs
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hgp : g + g = p := by
    dsimp [g, p]
    field_simp [hs₀.ne'] <;> ring
  have hpow : mpow (mpow ρ p) (s - 1) = mpow ρ (1 - p) := by
    rw [mpow_comp_nonneg hρ hp (sub_nonneg.mpr hs.le)]
    congr 1
    dsimp [p]
    field_simp [hs₀.ne'] <;> ring
  have hAdj : D * Jᴴ = (b / a) • (Jᴴ * D) := by
    simpa only [inv_div] using modular_adjoint hD.isHermitian (div_pos ha hb).ne' hJ
  have hProjLower : (ρ * (Jᴴ * J)).trace.re = ∑ i, ∑ j, eigenvalue j * w i j := by
    simpa only [mpow_one hρ.isHermitian, mpow_zero_hermitian hρ.isHermitian,
      Matrix.mul_one, Real.rpow_one, Real.rpow_zero, mul_one] using
      trace_mpow_sandwich_adjoint hρ.isHermitian J 1 0
  have hProjUpper : (ρ * (J * Jᴴ)).trace.re = ∑ i, ∑ j, eigenvalue i * w i j := by
    simpa only [mpow_one hρ.isHermitian, mpow_zero_hermitian hρ.isHermitian,
      Matrix.mul_one, Real.rpow_one, Real.rpow_zero, mul_one] using
      trace_mpow_sandwich hρ.isHermitian J 1 0
  have hlower := embedded_dissipator_trace hD hρ (div_pos ha hb) hg hJ p
  have hupper := embedded_dissipator_trace hD hρ (div_pos hb ha) hg hAdj p
  simp only [hgp, inv_div, Matrix.conjTranspose_conjTranspose] at hlower hupper
  change (1 / 4 : ℝ) * (mpow (mpow ρ p) (s - 1) *
      (mpow D g * pairedGenerator a b J (mpow D (-g) * mpow ρ p * mpow D (-g)) *
        mpow D g)).trace.re =
    ∑ i, ∑ j, w i j * edgeKernel p (b * eigenvalue i) (a * eigenvalue j)
  rw [hpow]
  simp only [pairedGenerator, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]
  rw [hlower, hupper, hProjLower, hProjUpper, trace_mpow_sandwich_adjoint hρ.isHermitian,
    trace_mpow_sandwich hρ.isHermitian]
  have rate (left right : ℝ) (hleft : 0 < left) (hright : 0 < right) (x y : ℝ) :
      2 * left * (x - (right / left) ^ p * y) =
        2 * left * x - 2 * (left ^ (1 - p) * right ^ p) * y := by
    rw [← rate_rpow hleft hright]
    ring
  rw [rate a b ha hb, rate b a hb ha]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [edgeKernel, eigenvalue, w, Real.mul_rpow ha.le (hρ.eigenvalues_nonneg j),
    Real.mul_rpow hb.le (hρ.eigenvalues_nonneg i)]
  ring

/-- The zero-product case is the contribution from the boundary of the density support. -/
def coshEdgeKernel (p u v : ℝ) : ℝ :=
  if u * v = 0 then (u + v) / 2
  else
    let x := |Real.log (u / v)| / 2
    Real.sqrt (u * v) * (Real.cosh x - Real.cosh (|2 * p - 1| * x))

private theorem symmetric_rpow_cosh {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (p : ℝ) :
    v ^ (1 - p) * u ^ p + u ^ (1 - p) * v ^ p =
      2 * Real.sqrt (u * v) * Real.cosh (|2 * p - 1| * (|Real.log (u / v)| / 2)) := by
  let x := Real.log (u / v) / 2
  let k := 2 * p - 1
  have hroot : Real.sqrt (u * v) = Real.exp ((Real.log u + Real.log v) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (mul_pos hu hv), Real.log_mul hu.ne' hv.ne']
    congr 1
    ring
  have hplus : Real.sqrt (u * v) * Real.exp (k * x) = v ^ (1 - p) * u ^ p := by
    rw [hroot, ← Real.exp_add, Real.rpow_def_of_pos hv, Real.rpow_def_of_pos hu, ← Real.exp_add]
    apply congrArg Real.exp
    dsimp [k, x]
    rw [Real.log_div hu.ne' hv.ne']
    ring
  have hminus : Real.sqrt (u * v) * Real.exp (-(k * x)) = u ^ (1 - p) * v ^ p := by
    rw [hroot, ← Real.exp_add, Real.rpow_def_of_pos hu, Real.rpow_def_of_pos hv, ← Real.exp_add]
    apply congrArg Real.exp
    dsimp [k, x]
    rw [Real.log_div hu.ne' hv.ne']
    ring
  have habs : |2 * p - 1| * (|Real.log (u / v)| / 2) = |k * x| := by
    dsimp [k, x]
    rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [habs, Real.cosh_abs, Real.cosh_eq, ← hplus, ← hminus]
  ring

/-- The symmetric powers vanish on zero-product edges because both exponents are positive. -/
theorem edgeKernel_eq_cosh {p u v : ℝ} (hp : 0 < p) (hp₁ : p < 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    edgeKernel p u v = coshEdgeKernel p u v := by
  by_cases hz : u * v = 0
  · rw [coshEdgeKernel, ite_eq_left hz]
    rcases mul_eq_zero.mp hz with h | h <;>
      simp [edgeKernel, h, Real.zero_rpow hp.ne', Real.zero_rpow (sub_pos.mpr hp₁).ne']
  · have hu' : 0 < u := lt_of_le_of_ne hu (fun h => hz (by rw [← h, zero_mul]))
    have hv' : 0 < v := lt_of_le_of_ne hv (fun h => hz (by rw [← h, mul_zero]))
    have hsum : u + v = 2 * Real.sqrt (u * v) * Real.cosh (|Real.log (u / v)| / 2) := by
      simpa only [mul_one, one_mul, sub_self, Real.rpow_zero, Real.rpow_one,
        show (2 : ℝ) - 1 = 1 by norm_num, abs_one] using symmetric_rpow_cosh hu' hv' 1
    rw [coshEdgeKernel, ite_eq_right hz, edgeKernel, symmetric_rpow_cosh hu' hv' p, hsum]
    ring

/-- The ordinary embedded trace in the cosh form of the exponent reduction. -/
private theorem pairedTrace_eq_cosh {D ρ J : Matrix n n ℂ} (hD : D.PosDef) (hρ : ρ.PosSemidef)
    {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 1 < s)
    (hJ : D * J = (a / b) • (J * D)) :
    pairedTrace s a b D ρ J =
      ∑ i, ∑ j, edgeWeight hρ.isHermitian J i j *
        coshEdgeKernel (1 / s) (b * hρ.isHermitian.eigenvalues i)
          (a * hρ.isHermitian.eigenvalues j) := by
  have hs₀ : 0 < s := lt_trans zero_lt_one hs
  have hp : 0 < 1 / s := one_div_pos.mpr hs₀
  have hp₁ : 1 / s < 1 := (div_lt_iff₀ hs₀).mpr (by simpa only [one_mul] using hs)
  rw [pairedTrace_eq_edges hD hρ ha hb hs hJ]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [edgeKernel_eq_cosh hp hp₁ (mul_nonneg hb.le (hρ.eigenvalues_nonneg i))
    (mul_nonneg ha.le (hρ.eigenvalues_nonneg j))]

/-- The cosh expansion for a finite family of jumps and their adjoints with mode-dependent
rates. Every mode uses the same spectral frame of the density as in the quadratic case. -/
theorem generatorTrace_eq_cosh {ι : Type*} [Fintype ι]
    {D ρ : Matrix n n ℂ} (hD : D.PosDef) (hρ : ρ.PosSemidef)
    (a b : ι → ℝ) (J : ι → Matrix n n ℂ) {s : ℝ} (hs : 1 < s)
    (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k)
    (hJ : ∀ k, D * J k * D⁻¹ = (a k / b k) • J k) :
    let G := mpow D (1 / (2 * s))
    let H := mpow D (-(1 / (2 * s)))
    let M := mpow ρ (1 / s)
    let X := H * M * H
    (1 / 4 : ℝ) * (mpow M (s - 1) *
      (G * (∑ k, pairedGenerator (a k) (b k) (J k) X) * G)).trace.re =
      ∑ k, ∑ i, ∑ j, edgeWeight hρ.isHermitian (J k) i j *
        coshEdgeKernel (1 / s) (b k * hρ.isHermitian.eigenvalues i)
          (a k * hρ.isHermitian.eigenvalues j) := by
  dsimp only
  simp only [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hdet : IsUnit D.det := D.isUnit_iff_isUnit_det.mp hD.isUnit
  have hk : D * J k = (a k / b k) • (J k * D) := by
    simpa only [Matrix.nonsing_inv_mul_cancel_right D (D * J k) hdet, Matrix.smul_mul] using
      congrArg (fun A : Matrix n n ℂ => A * D) (hJ k)
  exact pairedTrace_eq_cosh hD hρ (ha k) (hb k) hs hk

end D5.S3.Quantum.Semigroups.WuModularEdgeSpectral
