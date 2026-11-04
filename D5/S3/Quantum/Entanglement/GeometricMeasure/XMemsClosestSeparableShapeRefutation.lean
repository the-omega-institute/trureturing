/- GID: D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.claim; result=D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.result; claim=D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.claim
   digest: A fully separable 3-qubit state beats every fully separable state of CSS shape. -/

import D5.S3.Geometry.Hyperideal.GramDomainContraction
import D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation
import D5.S3.Quantum.Information.BargmannImaginaryMaximizers
import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability
import D5.S3.Quantum.Entanglement.FullySeparableExchangeObstruction
import D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums
import D5.S3.Quantum.QuantumChannels.TwirlingPhaseRetrievabilityCounterexample

/-! The low-branch reading of Consiglio–Apollaro–Wieśniak, arXiv:2209.01430v2,
Appendix A, equation (A11). Qubit zero is the most significant bit. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.Entanglement.FullySeparableExchangeObstruction
  (IsFullySeparableLocal density_psd)
open D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation (sum_bits)

namespace D5.S3.Quantum.Entanglement.GeometricMeasure.XMemsClosestSeparableShapeRefutation

/-- Equation (A1) on its low branch, where both f and g equal 1/(N+1). -/
def xmems (n : ℕ) (γ : ℂ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun x y => if x = y then
    if x = (fun _ => 1) ∨ (∃ k : Fin n, k.val = 0 ∧ x k = 0) then
      1 / ((2 : ℂ) ^ (n - 1) + 1) else 0
    else if x = (fun _ => 0) ∧ y = (fun _ => 1) then γ
    else if x = (fun _ => 1) ∧ y = (fun _ => 0) then star γ else 0

/-- The matrix in equation (A11), with the source's parameters a, b and d. -/
def cssShape (n : ℕ) (a b : ℝ) (d : ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun x y => if x = y then
    if x = (fun _ => 0) ∨ x = (fun _ => 1) then (a / 2 : ℝ)
    else if ∃ k : Fin n, k.val = 0 ∧ x k = 0 then
      (b / ((2 : ℝ) ^ (n - 1) - 1) : ℝ)
    else ((1 - a - b) / ((2 : ℝ) ^ (n - 1) - 1) : ℝ)
    else if x = (fun _ => 0) ∧ y = (fun _ => 1) then d
    else if x = (fun _ => 1) ∧ y = (fun _ => 0) then star d else 0

/-- The parameter restrictions of equation (A11). -/
def IsCssShape {n : ℕ} (σ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : Prop :=
  ∃ (a b : ℝ) (d : ℂ), 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧
    a + b ≤ 1 ∧ ‖d‖ ≤ a / 2 ∧ σ = cssShape n a b d

/-- Squared Hilbert–Schmidt distance. -/
def hsSq {n : ℕ} (ρ σ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : ℝ :=
  D5.S3.Quantum.Tomography.RankOneContextCommutator.hilbertSchmidtSquare (ρ - σ)

/-- Every low-branch X-MEMS has a closest fully separable state of form (A11). -/
def claim : Prop := ∀ n : ℕ, 2 ≤ n → ∀ γ : ℂ,
  ‖γ‖ ≤ 1 / ((2 : ℝ) ^ (n - 1) + 1) →
  ∃ σ, IsFullySeparableLocal σ ∧ IsCssShape σ ∧
    ∀ τ, IsFullySeparableLocal τ → hsSq (xmems n γ) σ ≤ hsSq (xmems n γ) τ

private theorem fullySeparable_iff (n : ℕ) (ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    ρ ∈ convexHull ℝ {σ | ∃ p : Fin n → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ k, IsDensity (p k)) ∧ σ = Matrix.piProd p} ↔ IsFullySeparableLocal ρ := by
  classical
  constructor
  · intro h
    obtain ⟨ι, fi, w, z, hw, hsum, hz, he⟩ := mem_convexHull_iff_exists_fintype.mp h
    let := fi
    choose p hp hzp using hz
    let e := Fintype.equivFin ι
    refine ⟨Fintype.card ι, w ∘ e.symm,
      fun j v => (D5.S3.Quantum.Information.ActualPureQubitCostInfimum.densityBridge
        (p (e.symm j) v) (hp (e.symm j) v).1 (hp (e.symm j) v).2).val,
      fun j => hw (e.symm j), ?_, ?_⟩
    · simpa only [Function.comp_apply, e.symm.sum_comp] using hsum
    · intro x y
      have hexy := congrArg (fun M => M x y) he.symm
      rw [← e.symm.sum_comp] at hexy
      dsimp only [D5.S3.Quantum.Information.ActualPureQubitCostInfimum.densityBridge]
      simpa only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul,
        hzp, Matrix.piProd, Matrix.of_apply, Function.comp_apply,
        CStarMatrix.ofMatrix_apply] using hexy
  · rintro ⟨k, p, σ, hp, hsum, he⟩
    apply mem_convexHull_of_exists_fintype p
      (fun j => Matrix.piProd (fun v => CStarMatrix.ofMatrix.symm (σ j v).val)) hp hsum
    · intro j
      refine ⟨_, fun v => ⟨density_psd (σ j v), (σ j v).property.2⟩, rfl⟩
    · ext x y
      simpa only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, Matrix.piProd,
        Matrix.of_apply, CStarMatrix.ofMatrix_symm_apply] using
        (he x y).symm

private theorem hsSq_entries {n : ℕ}
    (ρ σ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    hsSq ρ σ = ∑ x, ∑ y, Complex.normSq (ρ x y - σ x y) := by
  have h := congrArg Complex.re
    (D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace (ρ - σ))
  change _ = hsSq ρ σ at h
  rw [← h, ← D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability.entryNormSq_eq_hs_sq]
  simp only [D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.entryNormSq,
    Matrix.sub_apply, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

private theorem pair_sqrt (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (u * v) ≤ (u + v) / 2 := by
  have h := D5.S3.Geometry.Hyperideal.GramDomainContraction.twice_sqrt_product_le_add u v hu hv
  linarith

private theorem weighted_sqrt (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (u * v) ≤ u / 6 + 3 * v / 2 := by
  have h := pair_sqrt (u / 3) (3 * v) (by positivity) (by positivity)
  have he : u / 3 * (3 * v) = u * v := by
    rw [← mul_assoc, div_mul_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
  rw [he] at h
  linarith

private theorem product_bounds (p : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hp : ∀ k, IsDensity (p k)) :
    (Matrix.piProd p ![0,0,0] ![1,1,1]).re ≤
      (Matrix.piProd p ![0,0,1] ![0,0,1]).re / 6 +
        3 * (Matrix.piProd p ![1,1,0] ![1,1,0]).re / 2 ∧
    (Matrix.piProd p ![0,0,0] ![1,1,1]).re ≤
      (Matrix.piProd p ![0,0,0] ![0,0,0]).re / 12 +
        (Matrix.piProd p ![0,1,1] ![0,1,1]).re / 12 +
        3 * (Matrix.piProd p ![1,0,1] ![1,0,1]).re / 4 +
        3 * (Matrix.piProd p ![1,1,0] ![1,1,0]).re / 4 := by
  let a : Fin 3 → ℝ := fun k => (p k 0 0).re
  let b : Fin 3 → ℝ := fun k => (p k 1 1).re
  have ha (k) : 0 ≤ a k := (hp k).1.diag_nonneg.1
  have hb (k) : 0 ≤ b k := (hp k).1.diag_nonneg.1
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have hb0 := hb 0
  have hb1 := hb 1
  have hb2 := hb 2
  have hd (k : Fin 3) (i : Fin 2) : p k i i = ((p k i i).re : ℂ) :=
    ((hp k).1.isHermitian.coe_re_apply_self i).symm
  have hdiag (x : Fin 3 → Fin 2) :
      (Matrix.piProd p x x).re = ∏ k, (p k (x k) (x k)).re := by
    have he : Matrix.piProd p x x = ((∏ k, (p k (x k) (x k)).re : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
      change (∏ k, p k (x k) (x k)) = _
      exact Finset.prod_congr rfl (fun k _ => hd k (x k))
    exact congrArg Complex.re he
  have hn : (Matrix.piProd p ![0,0,0] ![1,1,1]).re ≤
      Real.sqrt (∏ k, a k * b k) := by
    apply (Complex.re_le_norm _).trans
    apply Real.le_sqrt_of_sq_le
    have he (k : Fin 3) : ‖p k 0 1‖ ^ 2 ≤ a k * b k := by
      simpa only [Complex.normSq_eq_norm_sq, a, b] using
        D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound (hp k).1 0 1
    dsimp only [Matrix.piProd]
    simpa [norm_prod, Fin.prod_univ_succ, mul_pow] using
      Finset.prod_le_prod₀ (fun k (_ : k ∈ Finset.univ) => sq_nonneg ‖p k 0 1‖)
        (fun k (_ : k ∈ Finset.univ) => he k)
  have he : (∏ k, a k * b k) =
      (a 0 * a 1 * b 2) * (b 0 * b 1 * a 2) := by
    simp [Fin.prod_univ_succ]
    ring
  have hfirst : (Matrix.piProd p ![0,0,0] ![1,1,1]).re ≤
      (a 0 * a 1 * b 2) / 6 + 3 * (b 0 * b 1 * a 2) / 2 := by
    apply hn.trans
    rw [he]
    exact weighted_sqrt _ _ (by positivity) (by positivity)
  have hroot : Real.sqrt (∏ k, a k * b k) =
      Real.sqrt (a 0 * b 0) * Real.sqrt (a 1 * b 1 * (a 2 * b 2)) := by
    rw [← Real.sqrt_mul (mul_nonneg ha0 hb0)]
    congr 1
    simp [Fin.prod_univ_succ]
  have hp1 := pair_sqrt (a 1 * a 2) (b 1 * b 2) (by positivity) (by positivity)
  have hp2 := pair_sqrt (a 1 * b 2) (b 1 * a 2) (by positivity) (by positivity)
  have harg1 : a 1 * a 2 * (b 1 * b 2) = a 1 * b 1 * (a 2 * b 2) :=
    mul_mul_mul_comm _ _ _ _
  have harg2 : a 1 * b 2 * (b 1 * a 2) = a 1 * b 1 * (a 2 * b 2) := by
    rw [mul_mul_mul_comm, mul_comm (b 2) (a 2)]
  rw [harg1] at hp1
  rw [harg2] at hp2
  have hw := weighted_sqrt (a 0) (b 0) ha0 hb0
  have hm := mul_le_mul_of_nonneg_right hw
    (Real.sqrt_nonneg (a 1 * b 1 * (a 2 * b 2)))
  have hm1 := mul_le_mul_of_nonneg_left hp1 (div_nonneg ha0 (by norm_num : (0:ℝ) ≤ 6))
  have hm2 := mul_le_mul_of_nonneg_left hp2 (by positivity : 0 ≤ 3 * b 0 / 2)
  have hsecond : (Matrix.piProd p ![0,0,0] ![1,1,1]).re ≤
      a 0 * a 1 * a 2 / 12 + a 0 * b 1 * b 2 / 12 +
        3 * (b 0 * a 1 * b 2) / 4 + 3 * (b 0 * b 1 * a 2) / 4 := by
    rw [hroot] at hn
    nlinarith only [hn, hm, hm1, hm2]
  constructor
  · simpa [hdiag, Fin.prod_univ_succ, mul_assoc, a, b] using hfirst
  · simpa [hdiag, Fin.prod_univ_succ, mul_assoc, a, b] using hsecond

private theorem separable_bounds (σ : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)
    (hσ : IsFullySeparableLocal σ) :
    (σ ![0,0,0] ![1,1,1]).re ≤
      ((σ ![0,0,1] ![0,0,1]).re / 6 + 3 * (σ ![1,1,0] ![1,1,0]).re / 2) / 5 +
      4 / 5 * ((σ ![0,0,0] ![0,0,0]).re / 12 +
        (σ ![0,1,1] ![0,1,1]).re / 12 +
        3 * (σ ![1,0,1] ![1,0,1]).re / 4 +
        3 * (σ ![1,1,0] ![1,1,0]).re / 4) := by
  let s : Set (Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ) :=
    {σ | (σ ![0,0,0] ![1,1,1]).re ≤
      ((σ ![0,0,1] ![0,0,1]).re / 6 + 3 * (σ ![1,1,0] ![1,1,0]).re / 2) / 5 +
      4 / 5 * ((σ ![0,0,0] ![0,0,0]).re / 12 +
        (σ ![0,1,1] ![0,1,1]).re / 12 +
        3 * (σ ![1,0,1] ![1,0,1]).re / 4 +
        3 * (σ ![1,1,0] ![1,1,0]).re / 4)}
  let f : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ → ℝ := fun σ =>
    (((σ ![0,0,1] ![0,0,1]).re / 6 + 3 * (σ ![1,1,0] ![1,1,0]).re / 2) / 5 +
      4 / 5 * ((σ ![0,0,0] ![0,0,0]).re / 12 +
        (σ ![0,1,1] ![0,1,1]).re / 12 +
        3 * (σ ![1,0,1] ![1,0,1]).re / 4 +
        3 * (σ ![1,1,0] ![1,1,0]).re / 4)) - (σ ![0,0,0] ![1,1,1]).re
  have hf : IsLinearMap ℝ f := by
    constructor
    · intro x y
      simp only [f, Matrix.add_apply, Complex.add_re]
      ring
    · intro u x
      simp only [f, Matrix.smul_apply, Complex.smul_re, smul_eq_mul]
      ring
  have hc : Convex ℝ s := by
    simpa only [f, s, sub_nonneg] using convex_halfSpace_ge hf (0 : ℝ)
  apply (convexHull_min (t := s) ?_ hc) ((fullySeparable_iff 3 σ).mpr hσ)
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨h1, h2⟩ := product_bounds p hp
  change (Matrix.piProd p ![0,0,0] ![1,1,1]).re ≤ ((Matrix.piProd p ![0,0,1] ![0,0,1]).re / 6 + 3 * (Matrix.piProd p ![1,1,0] ![1,1,0]).re / 2) / 5 +
      4 / 5 * ((Matrix.piProd p ![0,0,0] ![0,0,0]).re / 12 + (Matrix.piProd p ![0,1,1] ![0,1,1]).re / 12 +
        3 * (Matrix.piProd p ![1,0,1] ![1,0,1]).re / 4 + 3 * (Matrix.piProd p ![1,1,0] ![1,1,0]).re / 4)
  linarith

private theorem shape_distance (a b : ℝ) (d : ℂ) :
    hsSq (xmems 3 (11 / 112)) (cssShape 3 a b d) =
      2 * (1 / 5 - a / 2) ^ 2 + 3 * (1 / 5 - b / 3) ^ 2 +
        3 * ((1 - a - b) / 3) ^ 2 + 2 * ((11 / 112 - d.re) ^ 2 + d.im ^ 2) := by
  rw [hsSq_entries]
  let f (x y : Fin 3 → Fin 2) := Complex.normSq (xmems 3 (11 / 112) x y - (cssShape 3 a b d) x y)
  change ∑ x, ∑ y, f x y = _
  have row (x : Fin 3 → Fin 2) : ∑ y, f x y =
      f x ![0,0,0] + f x ![0,0,1] + f x ![0,1,0] + f x ![0,1,1] +
        f x ![1,0,0] + f x ![1,0,1] + f x ![1,1,0] + f x ![1,1,1] :=
    sum_bits (f x)
  have column (y : Fin 3 → Fin 2) : ∑ x, f x y =
      f ![0,0,0] y + f ![0,0,1] y + f ![0,1,0] y + f ![0,1,1] y +
        f ![1,0,0] y + f ![1,0,1] y + f ![1,1,0] y + f ![1,1,1] y :=
    sum_bits (fun x => f x y)
  simp only [row, Finset.sum_add_distrib, column]
  dsimp only [f]
  dsimp only [xmems, cssShape]
  norm_num [Complex.normSq_apply,
    show (fun _ : Fin 3 => (0 : Fin 2)) = ![0,0,0] from by simp only [Matrix.vec_single_eq_const, Matrix.vecCons_const],
    show (fun _ : Fin 3 => (1 : Fin 2)) = ![1,1,1] from by simp only [Matrix.vec_single_eq_const, Matrix.vecCons_const]]
  ring

private theorem shape_lower (σ : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)
    (hσ : IsFullySeparableLocal σ) (hs : IsCssShape σ) :
    (109 / 23520 : ℝ) ≤ hsSq (xmems 3 (11 / 112)) σ := by
  obtain ⟨a, b, d, _, _, _, _, _, _, rfl⟩ := hs
  have hd := separable_bounds (cssShape 3 a b d) hσ
  dsimp only [cssShape] at hd
  norm_num [show (fun _ : Fin 3 => (0 : Fin 2)) = ![0,0,0] from by simp only [Matrix.vec_single_eq_const, Matrix.vecCons_const],
    show (fun _ : Fin 3 => (1 : Fin 2)) = ![1,1,1] from by simp only [Matrix.vec_single_eq_const, Matrix.vecCons_const]] at hd
  rw [shape_distance]
  nlinarith only [hd, sq_nonneg (a / 2 - 3 / 16), sq_nonneg (b / 3 - 3 / 16),
    sq_nonneg ((1 - a - b) / 3 - 1 / 48), sq_nonneg (d.re - 1 / 16), sq_nonneg d.im]

private def wordIndex (x : Fin 3 → Fin 2) : Fin 8 :=
  finFunctionFinEquiv (x ∘ Fin.rev)

private def tau : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ :=
  fun x y => if x = y then
    (![356409,359991,359991,363609,39601,39999,39999,360401] (wordIndex x) : ℂ) / 1920000
    else if (x = ![0,0,0] ∧ y = ![1,1,1]) ∨
      (x = ![1,1,1] ∧ y = ![0,0,0]) then 119997 / 1920000 else 0

private def magnitude (t : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then Real.sqrt t else Real.sqrt (1 - t)

private def localVector (t : ℝ) (c : ZMod 3) : Fin 2 → ℂ :=
  D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude.latitude
    (1 - t) (ZMod.stdAddChar c)

private def localState (t : ℝ) (c : ZMod 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity (localVector t c)

private theorem localState_entry (t : ℝ) (c : ZMod 3) (i j : Fin 2) :
    localState t c i j = (magnitude t i * magnitude t j : ℝ) *
      ZMod.stdAddChar (c * ((i.val : ZMod 3) - (j.val : ZMod 3))) := by
  dsimp only [localState, D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity]
  simp only [Matrix.vecMulVec_apply, Pi.star_apply]
  have hv (i : Fin 2) : localVector t c i =
      (magnitude t i : ℂ) * ZMod.stdAddChar (c * (i.val : ZMod 3)) := by
    fin_cases i <;>
      dsimp only [localVector, magnitude,
        D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude.latitude] <;>
      norm_num
  simp only [hv]
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul,
    D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Fourier.char_star]
  rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

private theorem magnitude_sq (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin 2) :
    magnitude t i ^ 2 = if i = 0 then t else 1 - t := by
  dsimp only [magnitude]
  split_ifs
  · exact Real.sq_sqrt ht
  · exact Real.sq_sqrt (sub_nonneg.mpr ht1)

private theorem localState_density (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (c : ZMod 3) :
    IsDensity (localState t c) := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  change (Matrix.vecMulVec (localVector t c) (star (localVector t c))).trace = 1
  rw [Matrix.trace_vecMulVec, dotProduct_comm]
  dsimp only [localVector]
  rw [D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude.latitude_dot
    (1 - t) (by linarith) (by linarith)]
  have hz : star (ZMod.stdAddChar c) * ZMod.stdAddChar c = 1 := by
    have h := D5.S3.Quantum.QuantumChannels.TwirlingPhaseRetrievabilityCounterexample.chi_unit
      1 (Multiplicative.ofAdd c)
    change star (ZMod.stdAddChar ((1 : ZMod 3) * c)) * ZMod.stdAddChar (1 * c) = 1 at h
    simpa only [one_mul] using h
  rw [mul_assoc, hz, mul_one]
  push_cast
  ring

private def phaseProduct (a b : ZMod 3) :
    Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ :=
  Matrix.piProd ![localState (9 / 10) a, localState (199 / 400) b,
    localState (199 / 400) (-a-b)]

private def wordMagnitude (x : Fin 3 → Fin 2) : ℝ :=
  magnitude (9 / 10) (x 0) * magnitude (199 / 400) (x 1) * magnitude (199 / 400) (x 2)

private def frequency (x y : Fin 3 → Fin 2) (k : Fin 3) : ZMod 3 :=
  ((x k).val : ZMod 3) - ((y k).val : ZMod 3) - ((x 2).val : ZMod 3) + ((y 2).val : ZMod 3)

private theorem phaseProduct_entry (a b : ZMod 3) (x y : Fin 3 → Fin 2) :
    phaseProduct a b x y = (wordMagnitude x * wordMagnitude y : ℝ) *
      ZMod.stdAddChar (a * frequency x y 0 + b * frequency x y 1) := by
  calc
    phaseProduct a b x y = (wordMagnitude x * wordMagnitude y : ℝ) *
        (ZMod.stdAddChar (a * (((x 0).val : ZMod 3) - ((y 0).val : ZMod 3))) *
          ZMod.stdAddChar (b * (((x 1).val : ZMod 3) - ((y 1).val : ZMod 3))) *
          ZMod.stdAddChar ((-a-b) * (((x 2).val : ZMod 3) - ((y 2).val : ZMod 3)))) := by
      dsimp only [phaseProduct, Matrix.piProd, wordMagnitude]
      simp only [Matrix.of_apply, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one, localState_entry,
        Complex.ofReal_mul, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
      ring
    _ = _ := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 2
      dsimp only [frequency]
      ring

private theorem character_average (u v : ZMod 3) :
    (∑ a : ZMod 3, ∑ b : ZMod 3, ZMod.stdAddChar (a * u + b * v)) =
      if u = 0 ∧ v = 0 then (9 : ℂ) else 0 := by
  simp_rw [AddChar.map_add_eq_mul, ← Finset.mul_sum,
    AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar 3)]
  rw [← Finset.sum_mul, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar 3)]
  by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> norm_num [hu, hv]

private theorem phase_support (x y : Fin 3 → Fin 2) :
    (frequency x y 0 = 0 ∧ frequency x y 1 = 0) ↔
      x = y ∨ (x = ![0,0,0] ∧ y = ![1,1,1]) ∨
        (x = ![1,1,1] ∧ y = ![0,0,0]) := by
  revert x y
  decide

private theorem phase_average_entry (x y : Fin 3 → Fin 2) :
    (∑ a : ZMod 3, ∑ b : ZMod 3, phaseProduct a b) x y =
      if x = y ∨ (x = ![0,0,0] ∧ y = ![1,1,1]) ∨
        (x = ![1,1,1] ∧ y = ![0,0,0]) then
        9 * (wordMagnitude x * wordMagnitude y : ℝ) else 0 := by
  simp only [Matrix.sum_apply, phaseProduct_entry]
  simp_rw [← Finset.mul_sum]
  rw [character_average]
  simp only [phase_support]
  split_ifs <;> push_cast <;> ring

private theorem wordMagnitude_sq (x : Fin 3 → Fin 2) :
    wordMagnitude x ^ 2 =
      (if x 0 = 0 then 9 / 10 else 1 / 10) *
      (if x 1 = 0 then 199 / 400 else 201 / 400) *
      (if x 2 = 0 then 199 / 400 else 201 / 400) := by
  dsimp only [wordMagnitude]
  simp only [mul_pow,
    magnitude_sq (9 / 10) (by norm_num) (by norm_num),
    magnitude_sq (199 / 400) (by norm_num) (by norm_num)]
  norm_num

private theorem corner_magnitude : wordMagnitude ![0,0,0] * wordMagnitude ![1,1,1] =
    (119997 / 1600000 : ℝ) := by
  have hr : Real.sqrt (9 / 10) * Real.sqrt (1 / 10) = (3 / 10 : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9 / 10)]
    norm_num [Real.sqrt_div]
  calc
    _ = (Real.sqrt (9 / 10) * Real.sqrt (1 / 10)) *
        Real.sqrt (199 / 400) ^ 2 * Real.sqrt (201 / 400) ^ 2 := by
      dsimp only [wordMagnitude, magnitude]
      norm_num
      ring
    _ = _ := by rw [hr, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]; norm_num

private theorem word_cases (x : Fin 3 → Fin 2) :
    x = ![0,0,0] ∨ x = ![0,0,1] ∨ x = ![0,1,0] ∨ x = ![0,1,1] ∨
      x = ![1,0,0] ∨ x = ![1,0,1] ∨ x = ![1,1,0] ∨ x = ![1,1,1] := by
  classical
  have h : (∑ y : Fin 3 → Fin 2, if x = y then (1 : ℕ) else 0) =
      (if x = ![0,0,0] then 1 else 0) + (if x = ![0,0,1] then 1 else 0) +
      (if x = ![0,1,0] then 1 else 0) + (if x = ![0,1,1] then 1 else 0) +
      (if x = ![1,0,0] then 1 else 0) + (if x = ![1,0,1] then 1 else 0) +
      (if x = ![1,1,0] then 1 else 0) + (if x = ![1,1,1] then 1 else 0) :=
    sum_bits (fun y : Fin 3 → Fin 2 => if x = y then (1 : ℕ) else 0)
  by_contra hx
  simp only [not_or] at hx
  simp_all

private theorem tau_mixture : tau =
    (5 / 54 : ℝ) • (∑ a : ZMod 3, ∑ b : ZMod 3, phaseProduct a b) +
      (1 / 6 : ℝ) • Matrix.piProd (fun _ => localState 0 0) := by
  have hc : wordMagnitude ![1,1,1] * wordMagnitude ![0,0,0] = (119997 / 1600000 : ℝ) := by
    rw [mul_comm]
    exact corner_magnitude
  ext x y
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, phase_average_entry]
  rcases word_cases x with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases word_cases y with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp only [tau, wordIndex, Matrix.piProd, finFunctionFinEquiv] <;>
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, localState_entry] <;>
    dsimp only [magnitude] <;>
    norm_num [wordMagnitude_sq, ← pow_two, corner_magnitude, hc,
      Complex.real_smul, Fin.sum_univ_succ, Fin.rev]

private theorem tau_separable : IsFullySeparableLocal tau := by
  apply (fullySeparable_iff 3 tau).mp
  let s : Set (Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ) :=
    convexHull ℝ {σ | ∃ p : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ k, IsDensity (p k)) ∧ σ = Matrix.piProd p}
  have hp (a b : ZMod 3) : phaseProduct a b ∈ s := by
    apply subset_convexHull ℝ _
    refine ⟨![localState (9 / 10) a, localState (199 / 400) b,
      localState (199 / 400) (-a-b)], ?_, rfl⟩
    intro k
    fin_cases k <;> exact localState_density _ (by norm_num) (by norm_num) _
  have hb : Matrix.piProd (fun _ => localState 0 0) ∈ s := by
    apply subset_convexHull ℝ _
    exact ⟨_, fun _ => localState_density 0 (by norm_num) (by norm_num) 0, rfl⟩
  have hc : Convex ℝ (s) := convex_convexHull ℝ _
  have hrow (a : ZMod 3) :
      (∑ b : ZMod 3, (1 / 3 : ℝ) • phaseProduct a b) ∈ s := by
    apply hc.sum_mem
    · intro _ _; norm_num
    · norm_num
    · intro b _; exact hp a b
  have havg : (∑ a : ZMod 3, (1 / 3 : ℝ) •
      (∑ b : ZMod 3, (1 / 3 : ℝ) • phaseProduct a b)) ∈ s := by
    apply hc.sum_mem
    · intro _ _; norm_num
    · norm_num
    · intro a _; exact hrow a
  have h := hc havg hb (by norm_num : (0 : ℝ) ≤ 5 / 6)
    (by norm_num : (0 : ℝ) ≤ 1 / 6) (by norm_num)
  rw [tau_mixture]
  convert h using 1
  simp only [← Finset.smul_sum, smul_smul]
  norm_num

private theorem tau_distance : hsSq (xmems 3 (11 / 112)) tau =
    (417965512477 / 90316800000000 : ℝ) := by
  rw [hsSq_entries]
  let f (x y : Fin 3 → Fin 2) := Complex.normSq (xmems 3 (11 / 112) x y - (tau) x y)
  change ∑ x, ∑ y, f x y = _
  have row (x : Fin 3 → Fin 2) : ∑ y, f x y =
      f x ![0,0,0] + f x ![0,0,1] + f x ![0,1,0] + f x ![0,1,1] +
        f x ![1,0,0] + f x ![1,0,1] + f x ![1,1,0] + f x ![1,1,1] :=
    sum_bits (f x)
  have column (y : Fin 3 → Fin 2) : ∑ x, f x y =
      f ![0,0,0] y + f ![0,0,1] y + f ![0,1,0] y + f ![0,1,1] y +
        f ![1,0,0] y + f ![1,0,1] y + f ![1,1,0] y + f ![1,1,1] y :=
    sum_bits (fun x => f x y)
  simp only [row, Finset.sum_add_distrib, column]
  dsimp only [f]
  dsimp only [xmems, tau, wordIndex, finFunctionFinEquiv]
  norm_num [Complex.normSq_apply, Fin.sum_univ_succ, Fin.rev,
    show (fun _ : Fin 3 => (0 : Fin 2)) = ![0,0,0] from by simp only [Matrix.vec_single_eq_const, Matrix.vecCons_const],
    show (fun _ : Fin 3 => (1 : Fin 2)) = ![1,1,1] from by simp only [Matrix.vec_single_eq_const, Matrix.vecCons_const]]

private theorem distance_gap : (417965512477 / 90316800000000 : ℝ) < 109 / 23520 := by
  norm_num

/-- The three-qubit instance γ = 11/112 refutes the low-branch conjecture. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨σ, hσ, hs, hmin⟩ := h 3 (by norm_num) (11 / 112) (by norm_num)
  have hlo := shape_lower σ hσ hs
  have hhi := hmin tau tau_separable
  rw [tau_distance] at hhi
  exact (not_lt_of_ge (hlo.trans hhi)) distance_gap

end D5.S3.Quantum.Entanglement.GeometricMeasure.XMemsClosestSeparableShapeRefutation
