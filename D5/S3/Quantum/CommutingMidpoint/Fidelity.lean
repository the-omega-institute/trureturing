/- GID: D5/S3/Quantum/CommutingMidpoint/Fidelity
   generality: G
   mirror-B: D5/B/S3/Quantum/CommutingMidpoint/Fidelity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Matrix root-fidelity identities and binary preparation estimates used by commuting midpoint contraction. -/

import D5.S3.Quantum.GeneralizedFidelity
import D5.S3.Quantum.GNSMatrix
import D5.S0.Observation.MatrixTracePowerSum
import D5.S3.Quantum.Information.ActualQubitChordObstruction
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.CommutingMidpoint

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius InnerProductSpace
open D5.S3.Quantum.GeneralizedFidelity
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum

/-- Root, unsquared Uhlmann fidelity on actual matrices. -/
def rootFidelity {n : Type*} [Fintype n] [DecidableEq n]
    (S T : Matrix n n ℂ) : ℝ :=
  (trace (CFC.sqrt (CFC.sqrt S * T * CFC.sqrt S))).re

/-- The squared generalized Bures quantity is an actual Hilbert--Schmidt square,
including singular input matrices. -/
theorem bures_eq_weighted_root_norm_sq {n : Type*} [Fintype n] [DecidableEq n]
    (S V T : Matrix n n ℂ) (hS : S.PosSemidef) (hV : V.PosSemidef)
    (hT : T.PosDef) :
    bures T S V =
      ‖(CFC.sqrt T)⁻¹ * (CFC.sqrt (CFC.sqrt T * S * CFC.sqrt T) -
        CFC.sqrt (CFC.sqrt T * V * CFC.sqrt T))‖ ^ 2 := by
  classical
  let K := CFC.sqrt T
  let H := CFC.sqrt (K * S * K)
  let J := CFC.sqrt (K * V * K)
  have hK : Kᴴ = K := (CFC.sqrt_nonneg T).posSemidef.isHermitian.eq
  have hH : Hᴴ = H := (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq
  have hJ : Jᴴ = J := (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq
  have hK2 : K * K = T := CFC.sqrt_mul_sqrt_self T hT.posSemidef.nonneg
  have hKu : IsUnit K := (CFC.isUnit_sqrt_iff T hT.posSemidef.nonneg).mpr hT.isUnit
  have hKd : IsUnit K.det := K.isUnit_iff_isUnit_det.mp hKu
  have hKI : K⁻¹ * K = 1 := K.nonsing_inv_mul hKd
  have hIK : K * K⁻¹ = 1 := K.mul_nonsing_inv hKd
  have hInv : T⁻¹ = K⁻¹ * K⁻¹ := by rw [← hK2, Matrix.mul_inv_rev]
  have hInvStar : T⁻¹ᴴ = T⁻¹ := hT.inv.isHermitian.eq
  have hKIStar : K⁻¹ᴴ = K⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hK]
  have root_square (X : Matrix n n ℂ) (hX : X.PosSemidef) :
      CFC.sqrt (K * X * K) * CFC.sqrt (K * X * K) = K * X * K := by
    have hp : (K * X * K).PosSemidef := by
      simpa only [hK] using hX.mul_mul_conjTranspose_same K
    exact CFC.sqrt_mul_sqrt_self _ hp.nonneg
  have diagonal_term (X : Matrix n n ℂ) (hX : X.PosSemidef) :
      trace (CFC.sqrt (K * X * K) * T⁻¹ * CFC.sqrt (K * X * K)) = trace X := by
    rw [Matrix.trace_mul_cycle, root_square X hX, Matrix.trace_mul_comm, hInv]
    calc
      trace (K⁻¹ * K⁻¹ * (K * X * K)) = trace (K⁻¹ * X * K) := by
        congr 1
        calc
          _ = K⁻¹ * (K⁻¹ * K) * X * K := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hKI]; simp
      _ = trace X := by
        rw [Matrix.trace_mul_cycle]
        simp only [Matrix.mul_assoc, hIK, Matrix.one_mul]
  have cross : (trace (J * T⁻¹ * H)).re = (trace (H * T⁻¹ * J)).re := by
    have hh : (H * T⁻¹ * J)ᴴ = J * T⁻¹ * H := by
      simp only [Matrix.conjTranspose_mul, hH, hJ, hInvStar, Matrix.mul_assoc]
    rw [← hh, Matrix.trace_conjTranspose]
    simp
  have norm_identity := congrArg Complex.re
    (D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace (K⁻¹ * (H - J)))
  simp only [Complex.ofReal_re, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
    hH, hJ, hKIStar, Matrix.mul_assoc] at norm_identity
  have product : (H - J) * (K⁻¹ * (K⁻¹ * (H - J))) =
      H * T⁻¹ * H + J * T⁻¹ * J - H * T⁻¹ * J - J * T⁻¹ * H := by
    rw [hInv]
    noncomm_ring
  rw [product, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_add,
    diagonal_term S hS, diagonal_term V hV] at norm_identity
  simp only [Complex.sub_re, Complex.add_re, cross] at norm_identity
  dsimp [bures, fidelity]
  rw [Matrix.trace_add, Complex.add_re]
  change (trace S).re + (trace V).re - 2 * (trace (H * T⁻¹ * J)).re = _
  linarith only [norm_identity]

private theorem trace_square_two (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (trace M) ^ 2 = trace (M * M) + 2 * M.det := by
  have h := D5.S0.Observation.MatrixTracePowerSum.trace_pow_add_two M 0
  norm_num [pow_two] at h
  linear_combination -h

private theorem sqrt_trace_square_two (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.PosSemidef) :
    (trace (CFC.sqrt M)).re ^ 2 = (trace M).re + 2 * Real.sqrt M.det.re := by
  have hR := (CFC.sqrt_nonneg M).posSemidef
  have hi := (Complex.nonneg_iff.mp hR.trace_nonneg).2
  have hd : (CFC.sqrt M).det = (Real.sqrt M.det.re : ℂ) := by
    rw [hM.det_sqrt, RCLike.sqrt_of_nonneg hM.det_nonneg]
    rfl
  have h := congrArg Complex.re (trace_square_two (CFC.sqrt M))
  rw [CFC.sqrt_mul_sqrt_self M hM.nonneg, hd] at h
  norm_num [pow_two, Complex.mul_re, Complex.add_re, hi.symm] at h
  nlinarith only [h]

theorem rootFidelity_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (S T : Matrix n n ℂ) : 0 ≤ rootFidelity S T :=
  (Complex.nonneg_iff.mp (CFC.sqrt_nonneg _).posSemidef.trace_nonneg).1

theorem rootFidelity_sq_formula (S T : Matrix (Fin 2) (Fin 2) ℂ)
    (hS : S.PosSemidef) (hT : T.PosSemidef) :
    rootFidelity S T ^ 2 = (trace (S * T)).re +
      2 * Real.sqrt (S.det.re * T.det.re) := by
  have hK := (CFC.sqrt_nonneg S).posSemidef
  have hZ : (CFC.sqrt S * T * CFC.sqrt S).PosSemidef := by
    simpa only [hK.isHermitian.eq] using hT.mul_mul_conjTranspose_same (CFC.sqrt S)
  have ht : trace (CFC.sqrt S * T * CFC.sqrt S) = trace (S * T) := by
    rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self S hS.nonneg]
  have hd : (CFC.sqrt S * T * CFC.sqrt S).det = S.det * T.det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    have h := congrArg Matrix.det (CFC.sqrt_mul_sqrt_self S hS.nonneg)
    rw [Matrix.det_mul] at h
    calc
      (CFC.sqrt S).det * T.det * (CFC.sqrt S).det =
        (CFC.sqrt S).det * (CFC.sqrt S).det * T.det := by ring
      _ = S.det * T.det := by rw [h]
  have hSi := (Complex.nonneg_iff.mp hS.det_nonneg).2
  have hTi := (Complex.nonneg_iff.mp hT.det_nonneg).2
  have h := sqrt_trace_square_two _ hZ
  rw [ht, hd] at h
  simpa only [rootFidelity, Complex.mul_re, hSi.symm, hTi.symm,
    zero_mul, sub_zero] using h

private theorem rootFidelity_symm (S T : Matrix (Fin 2) (Fin 2) ℂ)
    (hS : S.PosSemidef) (hT : T.PosSemidef) :
    rootFidelity S T = rootFidelity T S := by
  have h1 := rootFidelity_sq_formula S T hS hT
  have h2 := rootFidelity_sq_formula T S hT hS
  rw [Matrix.trace_mul_comm T S, mul_comm T.det.re S.det.re] at h2
  nlinarith only [h1, h2, rootFidelity_nonneg S T, rootFidelity_nonneg T S]

open scoped Matrix.Norms.L2Operator in
private theorem rootFidelity_sq_ge_of_order {n : Type*} [Fintype n] [DecidableEq n]
    (S T : Matrix n n ℂ) (hS : S.PosSemidef) (htr : trace S = 1)
    (t : ℝ) (ht : 0 ≤ t) (hTS : (T - t ^ 2 • S).PosSemidef) :
    t ^ 2 ≤ rootFidelity S T ^ 2 := by
  have hs := (CFC.sqrt_nonneg S).posSemidef
  have hself : CFC.sqrt S * S * CFC.sqrt S = S * S := by
    calc
      _ = CFC.sqrt S * (CFC.sqrt S * CFC.sqrt S) * CFC.sqrt S := by
        rw [CFC.sqrt_mul_sqrt_self S hS.nonneg]
      _ = (CFC.sqrt S * CFC.sqrt S) * (CFC.sqrt S * CFC.sqrt S) := by
        simp only [Matrix.mul_assoc]
      _ = S * S := by rw [CFC.sqrt_mul_sqrt_self S hS.nonneg]
  have hpos := hTS.mul_mul_conjTranspose_same (CFC.sqrt S)
  rw [hs.isHermitian.eq] at hpos
  have hdiff : CFC.sqrt S * (T - t ^ 2 • S) * CFC.sqrt S =
      CFC.sqrt S * T * CFC.sqrt S - (t • S) * (t • S) := by
    simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, hself, pow_two]
  rw [hdiff] at hpos
  have hroot : CFC.sqrt ((t • S) * (t • S)) ≤
      CFC.sqrt (CFC.sqrt S * T * CFC.sqrt S) :=
    CFC.sqrt_le_sqrt _ _ (Matrix.le_iff.mpr hpos)
  rw [CFC.sqrt_mul_self (t • S) (hS.smul ht).nonneg] at hroot
  have htrace := (Complex.le_def.mp
    ((Matrix.tracePositiveLinearMap n ℝ ℂ).monotone hroot)).1
  change (trace (t • S)).re ≤
    (trace (CFC.sqrt (CFC.sqrt S * T * CFC.sqrt S))).re at htrace
  have hval : (trace (t • S)).re = t := by
    simp [Matrix.trace_smul, htr, Complex.smul_re]
  rw [hval] at htrace
  change t ≤ rootFidelity S T at htrace
  nlinarith only [htrace, ht, rootFidelity_nonneg S T]

/-- The actual qubit root fidelity is at least one half in squared convention
when the second state is dominated by twice the reference. -/
theorem fidelity_sq_lower_bound_from_half_order
    (S T : Matrix (Fin 2) (Fin 2) ℂ) (hS : S.PosSemidef)
    (hT : T.PosSemidef) (htrS : trace S = 1)
    (hTS : (T - (1 / 2 : ℝ) • S).PosSemidef) :
    1 / 2 ≤ rootFidelity T S ^ 2 := by
  have ht : Real.sqrt (1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have h := rootFidelity_sq_ge_of_order S T hS htrS
    (Real.sqrt (1 / 2)) (Real.sqrt_nonneg _) (by simpa only [ht] using hTS)
  rw [ht, rootFidelity_symm S T hS hT] at h
  exact h

/-- Binary root fidelity, including zero probabilities. -/
def binaryFidelity (p q : ℝ) : ℝ :=
  Real.sqrt (p * q) + Real.sqrt ((1 - p) * (1 - q))

private theorem preparation_coordinate (p q x y : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (p*q) * x + Real.sqrt ((1-p)*(1-q)) * y ≤
      Real.sqrt ((p*x+(1-p)*y)*(q*x+(1-q)*y)) := by
  let a : Fin 2 → ℝ := ![p*x, (1-p)*y]
  let b : Fin 2 → ℝ := ![q*x, (1-q)*y]
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    fin_cases i
    · exact mul_nonneg hp.1 hx
    · exact mul_nonneg (sub_nonneg.mpr hp.2) hy
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    fin_cases i
    · exact mul_nonneg hq.1 hx
    · exact mul_nonneg (sub_nonneg.mpr hq.2) hy
  have h := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin 2)) ha hb
  simp only [Fin.sum_univ_two, a, b,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
  have hleft (a b z : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : 0 ≤ z) :
      Real.sqrt (a*z) * Real.sqrt (b*z) = Real.sqrt (a*b) * z := by
    rw [← Real.sqrt_mul (mul_nonneg ha hz)]
    have he : a*z*(b*z) = (a*b)*z^2 := by ring
    rw [he, Real.sqrt_mul (mul_nonneg ha hb), Real.sqrt_sq hz]
  rw [hleft p q x hp.1 hq.1 hx,
    hleft (1-p) (1-q) y (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hq.2) hy,
    ← Real.sqrt_mul (add_nonneg (mul_nonneg hp.1 hx)
      (mul_nonneg (sub_nonneg.mpr hp.2) hy))] at h
  exact h

/-- Preparing either of two binary distributions cannot lower root fidelity. -/
theorem classical_binary_preparation_fidelity (p q x y : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    binaryFidelity p q ≤
      binaryFidelity (p*x+(1-p)*y) (q*x+(1-q)*y) := by
  have h0 := preparation_coordinate p q x y hp hq hx.1 hy.1
  have h1 := preparation_coordinate p q (1-x) (1-y) hp hq
    (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2)
  have he1 : p*(1-x)+(1-p)*(1-y) = 1-(p*x+(1-p)*y) := by ring
  have he2 : q*(1-x)+(1-q)*(1-y) = 1-(q*x+(1-q)*y) := by ring
  rw [he1, he2] at h1
  dsimp [binaryFidelity]
  linarith only [h0, h1]

private theorem rootFidelity_pos_of_posDef {n : Type*} [Fintype n]
    [DecidableEq n] (T S : Matrix n n ℂ) (hT : T.PosDef)
    (hS : S.PosSemidef) (htrS : trace S = 1) : 0 < rootFidelity T S := by
  have hn := rootFidelity_nonneg T S
  by_contra h
  have hz : rootFidelity T S = 0 := le_antisymm (le_of_not_gt h) hn
  let K := CFC.sqrt T
  let Z := K * S * K
  have hK := (CFC.sqrt_nonneg T).posSemidef
  have hZ : Z.PosSemidef := by
    have hk : Kᴴ = K := hK.isHermitian.eq
    change (K * S * K).PosSemidef
    simpa only [hk] using hS.mul_mul_conjTranspose_same K
  have hR := (CFC.sqrt_nonneg Z).posSemidef
  have htrace : trace (CFC.sqrt Z) = 0 := by
    apply Complex.ext
    · exact hz
    · exact (Complex.nonneg_iff.mp hR.trace_nonneg).2.symm
  have hroot := hR.trace_eq_zero_iff.mp htrace
  have hzero : Z = 0 := by
    rw [← CFC.sqrt_mul_sqrt_self Z hZ.nonneg, hroot, Matrix.zero_mul]
  have hu : IsUnit K := (CFC.isUnit_sqrt_iff T hT.posSemidef.nonneg).mpr hT.isUnit
  have hd : IsUnit K.det := K.isUnit_iff_isUnit_det.mp hu
  have hi : K⁻¹ * K = 1 := K.nonsing_inv_mul hd
  have hj : K * K⁻¹ = 1 := K.mul_nonsing_inv hd
  have hSzero : S = 0 := by
    have he := congrArg (fun X : Matrix n n ℂ => K⁻¹ * X * K⁻¹) hzero
    change K⁻¹ * (K * S * K) * K⁻¹ = _ at he
    have heq : K⁻¹ * (K * S * K) * K⁻¹ = S := by
      calc
        _ = (K⁻¹*K)*S*(K*K⁻¹) := by simp only [Matrix.mul_assoc]
        _ = S := by rw [hi, hj]; simp
    simpa only [heq, Matrix.mul_zero, Matrix.zero_mul] using he
  rw [hSzero, Matrix.trace_zero] at htrS
  exact zero_ne_one htrS

private theorem cayley_trace_two (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (trace M) • M = M * M + M.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h := D5.S0.Observation.MatrixTracePowerSum.pow_add_two M 0
  norm_num [pow_two] at h
  exact (sub_eq_iff_eq_add.mp h.symm)

private theorem sqrt_times_trace_two (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.PosSemidef) :
    ((trace (CFC.sqrt M)).re : ℂ) • CFC.sqrt M =
      M + (Real.sqrt M.det.re : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hi := (Complex.nonneg_iff.mp (CFC.sqrt_nonneg M).posSemidef.trace_nonneg).2
  have hr : ((trace (CFC.sqrt M)).re : ℂ) = trace (CFC.sqrt M) := by
    apply Complex.ext <;> simp [hi.symm]
  have hd : (CFC.sqrt M).det = (Real.sqrt M.det.re : ℂ) := by
    rw [hM.det_sqrt, RCLike.sqrt_of_nonneg hM.det_nonneg]
    rfl
  rw [hr, cayley_trace_two, CFC.sqrt_mul_sqrt_self M hM.nonneg, hd]

private theorem triple_trace_real (S V T : Matrix (Fin 2) (Fin 2) ℂ)
    (hS : S.IsHermitian) (hV : V.IsHermitian) (hT : T.IsHermitian)
    (hs : trace S = 1) (hv : trace V = 1) (ht : trace T = 1) :
    2 * (trace (T * S * V)).re =
      (trace (T * S)).re + (trace (T * V)).re + (trace (S * V)).re - 1 := by
  have hrepr (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.IsHermitian)
      (htX : trace X = 1) : X = blochMatrix 1 (bloch X) := by
    simpa only [htX, Complex.one_re] using (bloch_geometry_of_isHermitian X hX).1
  rw [hrepr S hS hs, hrepr V hV hv, hrepr T hT ht]
  simp [D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

private theorem trace_inverse_two (T : Matrix (Fin 2) (Fin 2) ℂ)
    (ht : trace T = 1) : trace T⁻¹ = T.det⁻¹ := by
  rw [Matrix.inv_def, Matrix.trace_smul, Matrix.adjugate_fin_two]
  have h : trace (!![T 1 1, -T 0 1; -T 1 0, T 0 0] : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    simpa [Matrix.trace, Fin.sum_univ_two, add_comm] using ht
  rw [h]
  simp

private theorem fidelity_scaled_trace (S V T : Matrix (Fin 2) (Fin 2) ℂ)
    (hS : S.PosSemidef) (hV : V.PosSemidef) (hT : T.PosDef)
    (hs : trace S = 1) (hv : trace V = 1) (ht : trace T = 1) :
    rootFidelity T S * rootFidelity T V * (fidelity T S V).re =
      (trace (T * S * V)).re + Real.sqrt (T.det.re * S.det.re) +
        Real.sqrt (T.det.re * V.det.re) + Real.sqrt (S.det.re * V.det.re) := by
  let K := CFC.sqrt T
  let Z := K * S * K
  let W := K * V * K
  let H := CFC.sqrt Z
  let J := CFC.sqrt W
  let a := rootFidelity T S
  let b := rootFidelity T V
  let d := Real.sqrt T.det.re
  let e := Real.sqrt S.det.re
  let g := Real.sqrt V.det.re
  have hK : Kᴴ = K := (CFC.sqrt_nonneg T).posSemidef.isHermitian.eq
  have hK2 : K * K = T := CFC.sqrt_mul_sqrt_self T hT.posSemidef.nonneg
  have hu : IsUnit K := (CFC.isUnit_sqrt_iff T hT.posSemidef.nonneg).mpr hT.isUnit
  have hd : IsUnit K.det := K.isUnit_iff_isUnit_det.mp hu
  have hi : K⁻¹ * K = 1 := K.nonsing_inv_mul hd
  have hj : K * K⁻¹ = 1 := K.mul_nonsing_inv hd
  have hInv : T⁻¹ = K⁻¹ * K⁻¹ := by rw [← hK2, Matrix.mul_inv_rev]
  have sandwich_det (X : Matrix (Fin 2) (Fin 2) ℂ) :
      (K * X * K).det = T.det * X.det := by
    have h := congrArg Matrix.det hK2
    rw [Matrix.det_mul] at h
    simp only [Matrix.det_mul]
    calc
      K.det * X.det * K.det = (K.det * K.det) * X.det := by ring
      _ = T.det * X.det := by rw [h]
  have sandwich_root (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.PosSemidef) :
      ((rootFidelity T X : ℝ) : ℂ) • CFC.sqrt (K * X * K) =
        K * X * K + (Real.sqrt (T.det.re * X.det.re) : ℂ) • 1 := by
    have hpos : (K * X * K).PosSemidef := by
      simpa only [hK] using hX.mul_mul_conjTranspose_same K
    have h := sqrt_times_trace_two _ hpos
    rw [sandwich_det] at h
    have hti := (Complex.nonneg_iff.mp hT.posSemidef.det_nonneg).2
    have hxi := (Complex.nonneg_iff.mp hX.det_nonneg).2
    simpa only [rootFidelity, Complex.mul_re, hti.symm, hxi.symm,
      zero_mul, sub_zero] using h
  have hH := sandwich_root S hS
  have hJ := sandwich_root V hV
  have hright : K * T⁻¹ = K⁻¹ := by
    rw [hInv, ← Matrix.mul_assoc, hj, Matrix.one_mul]
  have hmiddle : K * T⁻¹ * K = 1 := by rw [hright, hi]
  have hSZ : trace (Z * T⁻¹) = 1 := by
    change trace (K*S*K*T⁻¹) = 1
    calc
      _ = trace (K*S*K⁻¹) := by rw [Matrix.mul_assoc (K*S), hright]
      _ = trace S := Matrix.trace_conj hu S
      _ = 1 := hs
  have hVW : trace (T⁻¹ * W) = 1 := by
    rw [Matrix.trace_mul_comm]
    change trace (K*V*K*T⁻¹) = 1
    calc
      _ = trace (K*V*K⁻¹) := by rw [Matrix.mul_assoc (K*V), hright]
      _ = trace V := Matrix.trace_conj hu V
      _ = 1 := hv
  have hZW : trace (Z * T⁻¹ * W) = trace (T*S*V) := by
    change trace (K*S*K*T⁻¹*(K*V*K)) = _
    calc
      _ = trace (K*S*(K*T⁻¹*K)*V*K) := by simp only [Matrix.mul_assoc]
      _ = trace (K*S*V*K) := by rw [hmiddle, Matrix.mul_one]
      _ = trace (K*K*S*V) := by
        rw [Matrix.trace_mul_cycle]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hK2]
  dsimp only [Z, W] at hSZ hVW hZW
  have hc : ((a*b : ℝ) : ℂ) * fidelity T S V =
      trace (T*S*V) + (Real.sqrt (T.det.re*S.det.re) : ℂ) +
        (Real.sqrt (T.det.re*V.det.re) : ℂ) +
        (Real.sqrt (T.det.re*S.det.re) : ℂ) *
          (Real.sqrt (T.det.re*V.det.re) : ℂ) * trace T⁻¹ := by
    calc
      _ = trace (((a : ℂ) • H) * T⁻¹ * ((b : ℂ) • J)) := by
        change ((a*b : ℝ) : ℂ) * trace (H * T⁻¹ * J) = _
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
          smul_smul, smul_eq_mul, Complex.ofReal_mul]
        ring
      _ = _ := by
        rw [hH, hJ]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
          Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.trace_add,
          Matrix.trace_smul, smul_eq_mul, hSZ, hVW, hZW]
        ring
  have htd := (Complex.nonneg_iff.mp hT.posSemidef.det_nonneg).1
  have hsd := (Complex.nonneg_iff.mp hS.det_nonneg).1
  have hvd := (Complex.nonneg_iff.mp hV.det_nonneg).1
  have htdpos := (Complex.pos_iff.mp hT.det_pos).1
  have hti := (Complex.nonneg_iff.mp hT.posSemidef.det_nonneg).2
  have htdreal : T.det = (T.det.re : ℂ) := by
    apply Complex.ext <;> simp [hti.symm]
  rw [trace_inverse_two T ht, htdreal] at hc
  have hcre := congrArg Complex.re hc
  simp only [Complex.ofReal_mul, ← Complex.ofReal_inv, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, zero_mul,
    mul_zero, sub_zero, zero_add, add_zero] at hcre
  have hds : Real.sqrt (T.det.re*S.det.re) = d*e := Real.sqrt_mul htd _
  have hdv : Real.sqrt (T.det.re*V.det.re) = d*g := Real.sqrt_mul htd _
  have hsv : Real.sqrt (S.det.re*V.det.re) = e*g := Real.sqrt_mul hsd _
  rw [hds, hdv]
  rw [hds, hdv] at hcre
  have hdd : d^2 = T.det.re := Real.sq_sqrt htd
  have hcancel : d*e*(d*g)*T.det.re⁻¹ = e*g := by
    calc
      _ = (d^2*T.det.re⁻¹)*(e*g) := by ring
      _ = e*g := by rw [hdd, mul_inv_cancel₀ (ne_of_gt htdpos), one_mul]
  rw [hcancel] at hcre
  rw [hsv]
  exact hcre

/-- The ordered-root quotient holds for all complex qubit states, with singular
S and V allowed and only the reference T required positive definite. -/
theorem qubit_root_fidelity_quotient (S V T : Matrix (Fin 2) (Fin 2) ℂ)
    (hS : S.PosSemidef) (hV : V.PosSemidef) (hT : T.PosDef)
    (hs : trace S = 1) (hv : trace V = 1) (ht : trace T = 1) :
    0 < rootFidelity T S ∧ 0 < rootFidelity T V ∧
      (fidelity T S V).re =
        (rootFidelity T S ^ 2 + rootFidelity T V ^ 2 + rootFidelity S V ^ 2 - 1) /
          (2 * rootFidelity T S * rootFidelity T V) := by
  have ha := rootFidelity_pos_of_posDef T S hT hS hs
  have hb := rootFidelity_pos_of_posDef T V hT hV hv
  refine ⟨ha, hb, ?_⟩
  apply (eq_div_iff (by positivity : 2*rootFidelity T S*rootFidelity T V ≠ 0)).mpr
  have hab := fidelity_scaled_trace S V T hS hV hT hs hv ht
  have ha2 := rootFidelity_sq_formula T S hT.posSemidef hS
  have hb2 := rootFidelity_sq_formula T V hT.posSemidef hV
  have hc2 := rootFidelity_sq_formula S V hS hV
  have htr := triple_trace_real S V T hS.isHermitian hV.isHermitian hT.isHermitian hs hv ht
  nlinarith only [hab, ha2, hb2, hc2, htr]

end D5.S3.Quantum.CommutingMidpoint
