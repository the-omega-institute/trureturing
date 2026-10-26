/- GID: D5/S3/Quantum/CommutingMidpoint
   generality: G
   mirror-B: D5/B/S3/Quantum/CommutingMidpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/CommutingMidpoint.claim; result=D5/S3/Quantum/CommutingMidpoint.result; claim=D5/S3/Quantum/CommutingMidpoint.claim
   digest: Commuting qubit inputs contract generalized Bures distance at the scalar midpoint reference. -/

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

private theorem rootFidelity_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (S T : Matrix n n ℂ) : 0 ≤ rootFidelity S T :=
  (Complex.nonneg_iff.mp (CFC.sqrt_nonneg _).posSemidef.trace_nonneg).1

private theorem rootFidelity_sq_formula (S T : Matrix (Fin 2) (Fin 2) ℂ)
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

private theorem bloch_hermitian (r : EuclideanSpace ℝ (Fin 3)) :
    (blochMatrix 1 r).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochMatrix, Matrix.conjTranspose_apply, sub_eq_add_neg]

private theorem bloch_physical (r : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ ≤ 1) :
    (blochMatrix 1 r).PosSemidef := by
  have hh := bloch_hermitian r
  have ht := congrArg Complex.re hh.trace_eq_sum_eigenvalues
  rw [blochMatrix_trace] at ht
  simp only [Fin.sum_univ_two, Complex.add_re, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_re, Complex.one_re] at ht
  have hd := congrArg Complex.re hh.det_eq_prod_eigenvalues
  rw [D5.S3.Quantum.Information.ActualQubitChordObstruction.det_bloch] at hd
  simp only [Fin.prod_univ_two, Complex.mul_re, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hd
  have hp : 0 ≤ hh.eigenvalues 0 * hh.eigenvalues 1 := by
    nlinarith only [hd, hr, norm_nonneg r]
  apply hh.posSemidef_iff_eigenvalues_nonneg.mpr
  have h0 : 0 ≤ hh.eigenvalues 0 := by
    nlinarith only [ht, hp, sq_nonneg (hh.eigenvalues 0)]
  have h1 : 0 ≤ hh.eigenvalues 1 := by
    nlinarith only [ht, hp, sq_nonneg (hh.eigenvalues 1)]
  intro i
  fin_cases i
  · exact h0
  · exact h1

private theorem bloch_trace_pair (r s : EuclideanSpace ℝ (Fin 3)) :
    (trace (blochMatrix 1 r * blochMatrix 1 s)).re = (1 + ⟪r,s⟫_ℝ)/2 := by
  simp [Matrix.trace, Matrix.mul_apply, blochMatrix, Fin.sum_univ_two,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three,
    Complex.mul_re, Complex.mul_im] <;> ring

private theorem bloch_root_fidelity_sq (r s : EuclideanSpace ℝ (Fin 3))
    (hr : ‖r‖ ≤ 1) (hs : ‖s‖ ≤ 1) :
    rootFidelity (blochMatrix 1 r) (blochMatrix 1 s) ^ 2 =
      (1 + ⟪r,s⟫_ℝ + Real.sqrt (1-‖r‖^2)*Real.sqrt (1-‖s‖^2))/2 := by
  rw [rootFidelity_sq_formula _ _ (bloch_physical r hr) (bloch_physical s hs),
    bloch_trace_pair,
    D5.S3.Quantum.Information.ActualQubitChordObstruction.det_bloch,
    D5.S3.Quantum.Information.ActualQubitChordObstruction.det_bloch]
  simp only [Complex.ofReal_re]
  have hr2 : 0 ≤ 1-‖r‖^2 := by nlinarith only [hr, norm_nonneg r]
  have hs2 : 0 ≤ 1-‖s‖^2 := by nlinarith only [hs, norm_nonneg s]
  rw [Real.sqrt_mul (div_nonneg hr2 (by norm_num)),
    Real.sqrt_div hr2, Real.sqrt_div hs2]
  norm_num <;> ring

private theorem binaryFidelity_dot (p q : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    binaryFidelity p q = Real.sqrt p * Real.sqrt q +
      Real.sqrt (1-p) * Real.sqrt (1-q) := by
  rw [binaryFidelity, Real.sqrt_mul hp.1,
    Real.sqrt_mul (sub_nonneg.mpr hp.2)]

private theorem binary_unit (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt p ^ 2 + Real.sqrt (1-p) ^ 2 = 1 := by
  rw [Real.sq_sqrt hp.1, Real.sq_sqrt (sub_nonneg.mpr hp.2)] <;> ring

private theorem binaryFidelity_gram (r s t : ℝ)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    binaryFidelity r s ^ 2 + binaryFidelity r t ^ 2 + binaryFidelity s t ^ 2 - 1 =
      2 * binaryFidelity r s * binaryFidelity r t * binaryFidelity s t := by
  rw [binaryFidelity_dot r s hr hs, binaryFidelity_dot r t hr ht,
    binaryFidelity_dot s t hs ht]
  let a := Real.sqrt r
  let b := Real.sqrt (1-r)
  let c := Real.sqrt s
  let d := Real.sqrt (1-s)
  let e := Real.sqrt t
  let f := Real.sqrt (1-t)
  have hu : a^2+b^2=1 := binary_unit r hr
  have hv : c^2+d^2=1 := binary_unit s hs
  have hw : e^2+f^2=1 := binary_unit t ht
  have hpoly : (a*c+b*d)^2*(e^2+f^2) + (a*e+b*f)^2*(c^2+d^2) +
      (c*e+d*f)^2*(a^2+b^2) - 2*(a*c+b*d)*(a*e+b*f)*(c*e+d*f) =
      (a^2+b^2)*(c^2+d^2)*(e^2+f^2) := by ring
  rw [hu, hv, hw] at hpoly
  change (a*c+b*d)^2+(a*e+b*f)^2+(c*e+d*f)^2-1 =
    2*(a*c+b*d)*(a*e+b*f)*(c*e+d*f)
  nlinarith only [hpoly]

/-- The affine vector along the full Bloch-ball chord with perpendicular foot d. -/
def chordVector (d e : EuclideanSpace ℝ (Fin 3)) (z : ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  d + (Real.sqrt (1-‖d‖^2)*(2*z-1)) • e

/-- Actual trace-one complex matrix on the full Bloch chord. -/
def chordState (d e : EuclideanSpace ℝ (Fin 3)) (z : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ := blochMatrix 1 (chordVector d e z)

private theorem line_inner (d e : EuclideanSpace ℝ (Fin 3))
    (hde : ⟪d,e⟫_ℝ = 0) (he : ‖e‖ = 1) (x y : ℝ) :
    ⟪d+x•e,d+y•e⟫_ℝ = ‖d‖^2+x*y := by
  have hed : ⟪e,d⟫_ℝ = 0 := by rw [real_inner_comm, hde]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hde, hed, he,
    one_pow, mul_zero, add_zero, zero_add, mul_one] <;> ring

private theorem chord_inner (d e : EuclideanSpace ℝ (Fin 3))
    (hde : ⟪d,e⟫_ℝ = 0) (he : ‖e‖ = 1) (hd : ‖d‖^2 < 1) (x y : ℝ) :
    ⟪chordVector d e x,chordVector d e y⟫_ℝ =
      ‖d‖^2+(1-‖d‖^2)*(2*x-1)*(2*y-1) := by
  rw [chordVector, chordVector, line_inner d e hde he]
  have hroot := Real.sq_sqrt (show 0 ≤ 1-‖d‖^2 by linarith)
  calc
    _ = ‖d‖^2+Real.sqrt (1-‖d‖^2)^2*(2*x-1)*(2*y-1) := by ring
    _ = _ := by rw [hroot]

private theorem chord_norm_sq (d e : EuclideanSpace ℝ (Fin 3))
    (hde : ⟪d,e⟫_ℝ = 0) (he : ‖e‖ = 1) (hd : ‖d‖^2 < 1) (x : ℝ) :
    ‖chordVector d e x‖^2 = ‖d‖^2+(1-‖d‖^2)*(2*x-1)^2 := by
  rw [← real_inner_self_eq_norm_sq, chord_inner d e hde he hd] <;> ring

private theorem chord_norm_le (d e : EuclideanSpace ℝ (Fin 3))
    (hde : ⟪d,e⟫_ℝ = 0) (he : ‖e‖ = 1) (hd : ‖d‖^2 < 1)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : ‖chordVector d e x‖ ≤ 1 := by
  have h := chord_norm_sq d e hde he hd x
  have hprod := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have hsq : (2*x-1)^2 ≤ 1 := by nlinarith only [hprod]
  have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 1-‖d‖^2 by linarith)
  nlinarith only [h, hmul, norm_nonneg (chordVector d e x)]

private theorem chord_posDef (d e : EuclideanSpace ℝ (Fin 3))
    (hde : ⟪d,e⟫_ℝ = 0) (he : ‖e‖ = 1) (hd : ‖d‖^2 < 1)
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1) : (chordState d e r).PosDef := by
  have hp := bloch_physical _ (chord_norm_le d e hde he hd r ⟨hr.1.le,hr.2.le⟩)
  apply hp.posDef_iff_det_ne_zero.mpr
  change (blochMatrix 1 (chordVector d e r)).det ≠ 0
  rw [D5.S3.Quantum.Information.ActualQubitChordObstruction.det_bloch,
    chord_norm_sq d e hde he hd]
  have hprod : 0 < (1-‖d‖^2)*r*(1-r) :=
    mul_pos (mul_pos (sub_pos.mpr hd) hr.1) (sub_pos.mpr hr.2)
  have heq : (1-(‖d‖^2+(1-‖d‖^2)*(2*r-1)^2))/4 =
      (1-‖d‖^2)*r*(1-r) := by ring
  rw [heq]
  exact_mod_cast ne_of_gt hprod

private theorem binaryFidelity_square (x y : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    binaryFidelity x y ^ 2 =
      (1+(2*x-1)*(2*y-1)+4*Real.sqrt x*Real.sqrt (1-x)*
        Real.sqrt y*Real.sqrt (1-y))/2 := by
  rw [binaryFidelity_dot x y hx hy]
  ring_nf
  rw [Real.sq_sqrt hx.1, Real.sq_sqrt hy.1,
    Real.sq_sqrt (sub_nonneg.mpr hx.2), Real.sq_sqrt (sub_nonneg.mpr hy.2)] <;> ring

private theorem binaryFidelity_le_one (x y : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    binaryFidelity x y ≤ 1 := by
  have hpoly : (Real.sqrt x*Real.sqrt y+Real.sqrt (1-x)*Real.sqrt (1-y))^2 +
      (Real.sqrt x*Real.sqrt (1-y)-Real.sqrt (1-x)*Real.sqrt y)^2 =
      (Real.sqrt x^2+Real.sqrt (1-x)^2)*(Real.sqrt y^2+Real.sqrt (1-y)^2) := by ring
  rw [binary_unit x hx, binary_unit y hy] at hpoly
  rw [← binaryFidelity_dot x y hx hy] at hpoly
  nlinarith only [hpoly,
    sq_nonneg (Real.sqrt x*Real.sqrt (1-y)-Real.sqrt (1-x)*Real.sqrt y)]

private theorem chord_complement (d e : EuclideanSpace ℝ (Fin 3))
    (hde : ⟪d,e⟫_ℝ = 0) (he : ‖e‖ = 1) (hd : ‖d‖^2 < 1)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt (1-‖chordVector d e x‖^2) =
      2*Real.sqrt (1-‖d‖^2)*Real.sqrt x*Real.sqrt (1-x) := by
  have hnorm := chord_norm_le d e hde he hd x hx
  apply (Real.sqrt_eq_iff_eq_sq (by nlinarith only [hnorm, norm_nonneg (chordVector d e x)])
    (by positivity)).mpr
  rw [chord_norm_sq d e hde he hd, mul_pow, mul_pow, mul_pow,
    Real.sq_sqrt (show 0 ≤ 1-‖d‖^2 by linarith),
    Real.sq_sqrt hx.1, Real.sq_sqrt (sub_nonneg.mpr hx.2)] <;> ring

private theorem chord_root_fidelity_sq (d e : EuclideanSpace ℝ (Fin 3))
    (hde : ⟪d,e⟫_ℝ = 0) (he : ‖e‖ = 1) (hd : ‖d‖^2 < 1)
    (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    rootFidelity (chordState d e x) (chordState d e y)^2 =
      ‖d‖^2+(1-‖d‖^2)*binaryFidelity x y^2 := by
  rw [chordState, chordState,
    bloch_root_fidelity_sq _ _ (chord_norm_le d e hde he hd x hx)
      (chord_norm_le d e hde he hd y hy),
    chord_inner d e hde he hd,
    chord_complement d e hde he hd x hx, chord_complement d e hde he hd y hy,
    binaryFidelity_square x y hx hy]
  have hroot := Real.sq_sqrt (show 0 ≤ 1-‖d‖^2 by linarith)
  calc
    _ = (1+(‖d‖^2+(1-‖d‖^2)*(2*x-1)*(2*y-1))+
        4*Real.sqrt (1-‖d‖^2)^2*Real.sqrt x*Real.sqrt (1-x)*
          Real.sqrt y*Real.sqrt (1-y))/2 := by ring
    _ = _ := by rw [hroot]; ring

/-- Exact sign-sensitive factorization on an actual complex Bloch chord. -/
theorem qubit_chord_factorization (d e : EuclideanSpace ℝ (Fin 3))
    (hde : ⟪d,e⟫_ℝ = 0) (he : ‖e‖ = 1) (hd : ‖d‖^2 < 1)
    (r s t : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let a := rootFidelity (chordState d e r) (chordState d e s)
    let b := rootFidelity (chordState d e r) (chordState d e t)
    let f := (fidelity (chordState d e r) (chordState d e s) (chordState d e t)).re
    let w := binaryFidelity s t
    0 < a ∧ 0 < b ∧ 0 ≤ f ∧ 0 ≤ w ∧
      (f^2-w^2)*a^2*b^2 = ‖d‖^2*(1-w^2)*(a^2+b^2-1) ∧
      (1 ≤ a^2+b^2 → w ≤ f) := by
  let R := chordState d e r
  let S := chordState d e s
  let V := chordState d e t
  let a := rootFidelity R S
  let b := rootFidelity R V
  let f := (fidelity R S V).re
  let u := binaryFidelity r s
  let v := binaryFidelity r t
  let w := binaryFidelity s t
  let tau := ‖d‖^2
  let k := 1-tau
  have hr' : r ∈ Set.Icc (0 : ℝ) 1 := ⟨hr.1.le,hr.2.le⟩
  have hR : R.PosDef := chord_posDef d e hde he hd r hr
  have hS : S.PosSemidef := bloch_physical _ (chord_norm_le d e hde he hd s hs)
  have hV : V.PosSemidef := bloch_physical _ (chord_norm_le d e hde he hd t ht)
  have htrace (z : ℝ) : trace (chordState d e z) = 1 := blochMatrix_trace 1 _
  have hq := qubit_root_fidelity_quotient S V R hS hV hR (htrace s) (htrace t) (htrace r)
  have ha : 0 < a := hq.1
  have hb : 0 < b := hq.2.1
  have ha2 : a^2 = tau+k*u^2 := chord_root_fidelity_sq d e hde he hd r s hr' hs
  have hb2 : b^2 = tau+k*v^2 := chord_root_fidelity_sq d e hde he hd r t hr' ht
  have hc2 := chord_root_fidelity_sq d e hde he hd s t hs ht
  have hg : u^2+v^2+w^2-1=2*u*v*w := binaryFidelity_gram r s t hr' hs ht
  have hscaled : f*a*b = tau+k*u*v*w := by
    have h := (eq_div_iff (by positivity : 2*a*b ≠ 0)).mp hq.2.2
    change f*(2*a*b) = a^2+b^2+rootFidelity S V^2-1 at h
    rw [ha2, hb2, hc2] at h
    change f*(2*a*b) = tau+k*u^2+(tau+k*v^2)+(tau+k*w^2)-1 at h
    linear_combination (1/2)*h + (k/2)*hg
  have hu : 0 ≤ u := by dsimp [u,binaryFidelity]; positivity
  have hv : 0 ≤ v := by dsimp [v,binaryFidelity]; positivity
  have hw : 0 ≤ w := by dsimp [w,binaryFidelity]; positivity
  have htau : 0 ≤ tau := sq_nonneg _
  have hk : 0 ≤ k := by dsimp [k,tau]; linarith
  have hf : 0 ≤ f := by
    have hprod : 0 ≤ f*(a*b) := by
      rw [← mul_assoc, hscaled]
      positivity
    exact (mul_nonneg_iff_of_pos_right (mul_pos ha hb)).mp hprod
  have hfactor : (f^2-w^2)*a^2*b^2 = tau*(1-w^2)*(a^2+b^2-1) := by
    calc
      _ = (f*a*b)^2-w^2*a^2*b^2 := by ring
      _ = (tau+k*u*v*w)^2-w^2*(tau+k*u^2)*(tau+k*v^2) := by
        rw [hscaled, ha2, hb2]
      _ = tau*(1-w^2)*((tau+k*u^2)+(tau+k*v^2)-1) := by
        dsimp [k]
        linear_combination -tau*(1-tau)*hg
      _ = _ := by rw [← ha2, ← hb2]
  refine ⟨ha,hb,hf,hw,hfactor,?_⟩
  intro hab
  have hwle : w ≤ 1 := binaryFidelity_le_one s t hs ht
  have hwsq : 0 ≤ 1-w^2 := by nlinarith only [hw,hwle]
  have hab' : 0 ≤ a^2+b^2-1 := by linarith only [hab]
  have hright : 0 ≤ tau*(1-w^2)*(a^2+b^2-1) := by positivity
  have hleft : 0 ≤ (f^2-w^2)*a^2*b^2 := by rw [hfactor]; exact hright
  have hsq : 0 ≤ f^2-w^2 :=
    (mul_nonneg_iff_of_pos_right (mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hb))).mp
      (by simpa only [mul_assoc] using hleft)
  nlinarith only [hsq, hf, hw]

private theorem binaryFidelity_self (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    binaryFidelity x x = 1 := by
  unfold binaryFidelity
  rw [← pow_two x, ← pow_two (1-x)]
  rw [Real.sqrt_sq hx.1, Real.sqrt_sq (sub_nonneg.mpr hx.2)] <;> ring

private theorem binaryFidelity_sq_lt_one (s t : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hst : s ≠ t) : binaryFidelity s t ^ 2 < 1 := by
  have hcross : Real.sqrt s*Real.sqrt (1-t)-Real.sqrt (1-s)*Real.sqrt t ≠ 0 := by
    intro hz
    have h := congrArg (fun z : ℝ => z^2) (sub_eq_zero.mp hz)
    rw [mul_pow, mul_pow, Real.sq_sqrt hs.1, Real.sq_sqrt ht.1,
      Real.sq_sqrt (sub_nonneg.mpr hs.2), Real.sq_sqrt (sub_nonneg.mpr ht.2)] at h
    exact hst (by nlinarith only [h])
  have hpoly : (Real.sqrt s*Real.sqrt t+Real.sqrt (1-s)*Real.sqrt (1-t))^2 +
      (Real.sqrt s*Real.sqrt (1-t)-Real.sqrt (1-s)*Real.sqrt t)^2 =
      (Real.sqrt s^2+Real.sqrt (1-s)^2)*(Real.sqrt t^2+Real.sqrt (1-t)^2) := by ring
  rw [binary_unit s hs, binary_unit t ht,
    ← binaryFidelity_dot s t hs ht] at hpoly
  nlinarith only [hpoly, sq_pos_of_ne_zero hcross]

/-- The sign criterion on one chord is sharp, with diameter and equal-state
fibers included as exact identities. -/
theorem qubit_chord_strict_sign_and_boundary (d e : EuclideanSpace ℝ (Fin 3))
    (hde : ⟪d,e⟫_ℝ = 0) (he : ‖e‖ = 1) (hd : ‖d‖^2 < 1)
    (r s t : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let a := rootFidelity (chordState d e r) (chordState d e s)
    let b := rootFidelity (chordState d e r) (chordState d e t)
    let f := (fidelity (chordState d e r) (chordState d e s) (chordState d e t)).re
    let w := binaryFidelity s t
    (0 < ‖d‖^2 → s ≠ t → (w ≤ f ↔ 1 ≤ a^2+b^2) ∧ (f=w ↔ a^2+b^2=1)) ∧
      (‖d‖^2=0 → f=w) ∧ (s=t → f=w ∧ w=1) := by
  let a := rootFidelity (chordState d e r) (chordState d e s)
  let b := rootFidelity (chordState d e r) (chordState d e t)
  let f := (fidelity (chordState d e r) (chordState d e s) (chordState d e t)).re
  let w := binaryFidelity s t
  obtain ⟨ha,hb,hf,hw,hfactor,hcomparison⟩ :=
    qubit_chord_factorization d e hde he hd r s t hr hs ht
  have hab : 0 < a^2*b^2 := mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hb)
  have hfactor' : (f^2-w^2)*(a^2*b^2) = ‖d‖^2*(1-w^2)*(a^2+b^2-1) := by
    simpa only [mul_assoc] using hfactor
  refine ⟨?_,?_,?_⟩
  · intro hdt hst
    have hgap : 0 < 1-w^2 := by
      have h := binaryFidelity_sq_lt_one s t hs ht hst
      linarith only [h]
    have hc : 0 < ‖d‖^2*(1-w^2) := mul_pos hdt hgap
    constructor
    · constructor
      · intro h
        have hsq : 0 ≤ f^2-w^2 := by nlinarith only [h,hf,hw]
        have hp := mul_nonneg hsq hab.le
        rw [hfactor'] at hp
        have hm := (mul_nonneg_iff_of_pos_left hc).mp hp
        linarith only [hm]
      · exact hcomparison
    · constructor
      · intro h
        change f = w at h
        have hz : ‖d‖^2*(1-w^2)*(a^2+b^2-1)=0 := by
          rw [← hfactor', h, sub_self, zero_mul]
        have hm := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hc)
        linarith only [hm]
      · intro h
        have hz : (f^2-w^2)*(a^2*b^2)=0 := by rw [hfactor',h]; ring
        have hsq := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hab)
        nlinarith only [hsq,hf,hw]
  · intro hdt
    have hz : (f^2-w^2)*(a^2*b^2)=0 := by rw [hfactor',hdt,zero_mul,zero_mul]
    have hsq := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hab)
    nlinarith only [hsq,hf,hw]
  · intro hst
    have hw1 : w=1 := by simpa only [w,hst] using binaryFidelity_self t ht
    have hp := chord_posDef d e hde he hd r hr
    have hps := bloch_physical _ (chord_norm_le d e hde he hd s hs)
    have hB := bures_eq_weighted_root_norm_sq (chordState d e s)
      (chordState d e s) (chordState d e r) hps hps hp
    simp only [sub_self, Matrix.mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] at hB
    unfold bures at hB
    have hts : trace (chordState d e s) = 1 := blochMatrix_trace 1 _
    rw [Matrix.trace_add, hts] at hB
    have hf1 : f=1 := by
      change (fidelity (chordState d e r) (chordState d e s) (chordState d e t)).re=1
      rw [← hst]
      norm_num at hB
      linarith only [hB]
    exact ⟨hf1.trans hw1.symm,hw1⟩

private theorem full_chord_of_distinct (a b : EuclideanSpace ℝ (Fin 3))
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hne : a ≠ b) :
    ∃ (d e : EuclideanSpace ℝ (Fin 3)) (x y : ℝ),
      ⟪d,e⟫_ℝ=0 ∧ ‖e‖=1 ∧ ‖d‖^2<1 ∧
      x ∈ Set.Icc (0 : ℝ) 1 ∧ y ∈ Set.Icc (0 : ℝ) 1 ∧ x ≠ y ∧
      a=chordVector d e x ∧ b=chordVector d e y ∧
      (x+y)/2 ∈ Set.Ioo (0 : ℝ) 1 := by
  let l := ‖b-a‖
  have hl : 0 < l := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  let e := l⁻¹ • (b-a)
  have he : ‖e‖=1 := by
    change ‖l⁻¹ • (b-a)‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hl)]
    exact inv_mul_cancel₀ (ne_of_gt hl)
  have hdiff : b-a = l • e := by
    dsimp [e]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hl), one_smul]
  let c := ⟪a,e⟫_ℝ
  let d := a-c•e
  have hde : ⟪d,e⟫_ℝ=0 := by
    simp only [d, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, he, one_pow, mul_one]
    exact sub_self c
  have haa : a=d+c•e := by dsimp [d]; abel
  have hbb : b=d+(c+l)•e := by
    rw [add_smul, ← add_assoc, ← haa, ← hdiff]
    abel
  have hanorm : ‖a‖^2=‖d‖^2+c^2 := by
    rw [haa, ← real_inner_self_eq_norm_sq, line_inner d e hde he]
    ring
  have hbnorm : ‖b‖^2=‖d‖^2+(c+l)^2 := by
    rw [hbb, ← real_inner_self_eq_norm_sq, line_inner d e hde he]
    ring
  have ha2 : ‖a‖^2 ≤ 1 := by nlinarith only [ha,norm_nonneg a]
  have hb2 : ‖b‖^2 ≤ 1 := by nlinarith only [hb,norm_nonneg b]
  have hd : ‖d‖^2<1 := by
    by_contra h
    have hc0 : c=0 := by nlinarith only [h,ha2,hanorm,sq_nonneg c]
    have hcl0 : c+l=0 := by nlinarith only [h,hb2,hbnorm,sq_nonneg (c+l)]
    linarith only [hc0,hcl0,hl]
  let h := Real.sqrt (1-‖d‖^2)
  have hh : 0 < h := Real.sqrt_pos.mpr (by linarith)
  have hh2 : h^2=1-‖d‖^2 := Real.sq_sqrt (by linarith)
  have hcLo : -h ≤ c := by nlinarith only [ha2,hanorm,hh2,hh]
  have hcHi : c ≤ h := by nlinarith only [ha2,hanorm,hh2,hh]
  have hbLo : -h ≤ c+l := by nlinarith only [hb2,hbnorm,hh2,hh]
  have hbHi : c+l ≤ h := by nlinarith only [hb2,hbnorm,hh2,hh]
  let x := (c/h+1)/2
  let y := ((c+l)/h+1)/2
  have hcdivLo : -1 ≤ c/h := (le_div_iff₀ hh).mpr (by linarith only [hcLo])
  have hcdivHi : c/h ≤ 1 := (div_le_iff₀ hh).mpr (by simpa using hcHi)
  have hbdivLo : -1 ≤ (c+l)/h := (le_div_iff₀ hh).mpr (by linarith only [hbLo])
  have hbdivHi : (c+l)/h ≤ 1 := (div_le_iff₀ hh).mpr (by simpa using hbHi)
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := by dsimp [x]; constructor <;> linarith
  have hy : y ∈ Set.Icc (0 : ℝ) 1 := by dsimp [y]; constructor <;> linarith
  have hxy : x < y := by
    dsimp [x,y]
    gcongr
    linarith only [hl]
  have hcx : h*(2*x-1)=c := by
    dsimp [x]
    field_simp [ne_of_gt hh]
    <;> ring
  have hcy : h*(2*y-1)=c+l := by
    dsimp [y]
    field_simp [ne_of_gt hh]
    <;> ring
  refine ⟨d,e,x,y,hde,he,hd,hx,hy,ne_of_lt hxy,?_,?_,?_⟩
  · change a=d+(h*(2*x-1))•e
    rw [hcx]
    exact haa
  · change b=d+(h*(2*y-1))•e
    rw [hcy]
    exact hbb
  · constructor <;> linarith only [hx.1,hx.2,hy.1,hy.2,hxy]

/-- The real affine combination of two actual complex matrices. -/
def mixture (p : ℝ) (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  p • A + (1-p) • B

private theorem chord_mixture (d e : EuclideanSpace ℝ (Fin 3)) (x y p : ℝ) :
    mixture p (chordState d e x) (chordState d e y) =
      chordState d e (p*x+(1-p)*y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [mixture,chordState,chordVector,blochMatrix,Complex.mul_re,Complex.mul_im] <;> ring

private theorem mixture_probability (p x y : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : p*x+(1-p)*y ∈ Set.Icc (0 : ℝ) 1 := by
  have hpc : 0 ≤ 1-p := sub_nonneg.mpr hp.2
  constructor
  · exact add_nonneg (mul_nonneg hp.1 hx.1) (mul_nonneg hpc hy.1)
  · have h1 := mul_le_mul_of_nonneg_left hx.2 hp.1
    have h2 := mul_le_mul_of_nonneg_left hy.2 hpc
    linarith only [h1,h2]

private theorem mixture_posSemidef (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (p : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) : (mixture p A B).PosSemidef :=
  (hA.smul hp.1).add (hB.smul (sub_nonneg.mpr hp.2))

private theorem mixture_trace (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : trace A=1) (hB : trace B=1) (p : ℝ) : trace (mixture p A B)=1 := by
  simp [mixture,Matrix.trace_add,Matrix.trace_smul,hA,hB] <;> ring

private theorem midpoint_half_order (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (p : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (mixture (1/2) A B - (1/2 : ℝ) • mixture p A B).PosSemidef := by
  have he : mixture (1/2) A B - (1/2 : ℝ) • mixture p A B =
      (1/2 : ℝ) • mixture (1-p) A B := by
    dsimp [mixture]
    module
  rw [he]
  apply (mixture_posSemidef A B hA hB (1-p)
    (by constructor <;> linarith only [hp.1, hp.2])).smul
  norm_num

private theorem fidelity_same_state (S T : Matrix (Fin 2) (Fin 2) ℂ)
    (hS : S.PosSemidef) (hT : T.PosDef) (hs : trace S=1) :
    (fidelity T S S).re=1 := by
  have h := bures_eq_weighted_root_norm_sq S S T hS hS hT
  simp only [sub_self, Matrix.mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at h
  unfold bures at h
  rw [Matrix.trace_add, hs] at h
  norm_num at h
  linarith only [h]

/-- Arbitrary prepared qubit outputs obey the transported midpoint bound,
including noncommuting outputs and singular prepared or mixed states. -/
theorem prepared_qubit_midpoint_fidelity
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htA : trace A=1) (htB : trace B=1) (p q : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hT : (mixture (1/2) A B).PosDef) :
    binaryFidelity p q ≤ (fidelity (mixture (1/2) A B) (mixture p A B) (mixture q A B)).re ∧
      0 ≤ bures (mixture (1/2) A B) (mixture p A B) (mixture q A B) ∧
      bures (mixture (1/2) A B) (mixture p A B) (mixture q A B) ≤ 2-2*binaryFidelity p q := by
  have hS := mixture_posSemidef A B hA hB p hp
  have hV := mixture_posSemidef A B hA hB q hq
  have htS := mixture_trace A B htA htB p
  have htV := mixture_trace A B htA htB q
  have hnonneg : 0 ≤ bures (mixture (1/2) A B) (mixture p A B) (mixture q A B) := by
    rw [bures_eq_weighted_root_norm_sq _ _ _ hS hV hT]
    exact sq_nonneg _
  have hf : binaryFidelity p q ≤
      (fidelity (mixture (1/2) A B) (mixture p A B) (mixture q A B)).re := by
    by_cases heq : A=B
    · subst B
      have hm (z : ℝ) : mixture z A A=A := by dsimp [mixture]; module
      rw [hm,hm,hm, fidelity_same_state A A hA (by simpa only [hm] using hT) htA]
      exact binaryFidelity_le_one p q hp hq
    · have hrepr (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.PosSemidef)
          (htX : trace X=1) : X=blochMatrix 1 (bloch X) := by
        simpa only [htX,Complex.one_re] using (bloch_geometry_of_isHermitian X hX.isHermitian).1
      have hne : bloch A ≠ bloch B := by
        intro h
        apply heq
        rw [hrepr A hA htA,hrepr B hB htB,h]
      have hrA : ‖bloch A‖ ≤ 1 := by
        simpa only [htA,Complex.one_re] using norm_bloch_le_trace_of_posSemidef A hA
      have hrB : ‖bloch B‖ ≤ 1 := by
        simpa only [htB,Complex.one_re] using norm_bloch_le_trace_of_posSemidef B hB
      obtain ⟨d,e,x,y,hde,he,hd,hx,hy,hxy,ha,hb,hr⟩ :=
        full_chord_of_distinct (bloch A) (bloch B) hrA hrB hne
      have hAA : A=chordState d e x := by rw [hrepr A hA htA,ha]; rfl
      have hBB : B=chordState d e y := by rw [hrepr B hB htB,hb]; rfl
      let r := (x+y)/2
      let s := p*x+(1-p)*y
      let t := q*x+(1-q)*y
      have hs := mixture_probability p x y hp hx hy
      have ht := mixture_probability q x y hq hx hy
      have hrr : mixture (1/2) A B=chordState d e r := by
        rw [hAA,hBB,chord_mixture]
        congr 1
        dsimp [r]
        ring
      have hss : mixture p A B=chordState d e s := by rw [hAA,hBB,chord_mixture]
      have htt : mixture q A B=chordState d e t := by rw [hAA,hBB,chord_mixture]
      have ha2 := fidelity_sq_lower_bound_from_half_order _ _ hS hT.posSemidef htS
        (midpoint_half_order A B hA hB p hp)
      have hb2 := fidelity_sq_lower_bound_from_half_order _ _ hV hT.posSemidef htV
        (midpoint_half_order A B hA hB q hq)
      rw [hrr,hss] at ha2
      rw [hrr,htt] at hb2
      have hc := qubit_chord_factorization d e hde he hd r s t hr hs ht
      have hcompare := hc.2.2.2.2.2 (by linarith only [ha2,hb2])
      rw [hrr,hss,htt]
      exact (classical_binary_preparation_fidelity p q x y hp hq hx hy).trans hcompare
  refine ⟨hf,hnonneg,?_⟩
  unfold bures
  rw [Matrix.trace_add,htS,htV]
  norm_num
  linarith only [hf]

private theorem bloch_commutator_gram (a b : EuclideanSpace ℝ (Fin 3)) :
    let P := blochMatrix 1 a
    let Q := blochMatrix 1 b
    (trace ((P*Q-Q*P)ᴴ*(P*Q-Q*P))).re =
      (‖a‖^2*‖b‖^2-⟪a,b⟫_ℝ^2)/2 := by
  dsimp
  let x := a 1*b 2-a 2*b 1
  let y := a 2*b 0-a 0*b 2
  let z := a 0*b 1-a 1*b 0
  let C : Matrix (Fin 2) (Fin 2) ℂ :=
    !![(z : ℂ)*Complex.I/2, ((y : ℂ)+(x : ℂ)*Complex.I)/2;
      (-(y : ℂ)+(x : ℂ)*Complex.I)/2, -(z : ℂ)*Complex.I/2]
  have hC : blochMatrix 1 a*blochMatrix 1 b-blochMatrix 1 b*blochMatrix 1 a=C := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [Matrix.mul_apply,blochMatrix,Fin.sum_univ_two,C,x,y,z,
        Complex.mul_re,Complex.mul_im] <;> ring
  rw [hC]
  have hnorm : (trace (Cᴴ*C)).re=(x^2+y^2+z^2)/2 := by
    norm_num [Matrix.trace,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fin.sum_univ_two,C,Complex.mul_re,Complex.mul_im,
      starRingEnd_apply,RCLike.star_def] <;> ring
  rw [hnorm]
  simp only [EuclideanSpace.real_norm_sq_eq,PiLp.inner_apply,RCLike.inner_apply,
    Fin.sum_univ_three]
  dsimp [x,y,z]
  ring

private theorem commuting_chord_zero_foot (d e : EuclideanSpace ℝ (Fin 3))
    (hde : ⟪d,e⟫_ℝ=0) (he : ‖e‖=1) (hd : ‖d‖^2<1)
    (x y : ℝ) (hxy : x ≠ y)
    (hcomm : chordState d e x*chordState d e y = chordState d e y*chordState d e x) :
    ‖d‖^2=0 := by
  have h := bloch_commutator_gram (chordVector d e x) (chordVector d e y)
  change (trace ((chordState d e x*chordState d e y-chordState d e y*chordState d e x)ᴴ*
    (chordState d e x*chordState d e y-chordState d e y*chordState d e x))).re = _ at h
  rw [hcomm,sub_self,Matrix.conjTranspose_zero,Matrix.zero_mul,Matrix.trace_zero,
    Complex.zero_re,chord_norm_sq d e hde he hd,chord_norm_sq d e hde he hd,
    chord_inner d e hde he hd] at h
  have hpoly : (‖d‖^2+(1-‖d‖^2)*(2*x-1)^2)*
      (‖d‖^2+(1-‖d‖^2)*(2*y-1)^2)-
      (‖d‖^2+(1-‖d‖^2)*(2*x-1)*(2*y-1))^2 =
      ‖d‖^2*(4*(1-‖d‖^2)*(x-y)^2) := by ring
  have hz : ‖d‖^2*(4*(1-‖d‖^2)*(x-y)^2)=0 := by linarith only [h,hpoly]
  have hpos : 0 < 4*(1-‖d‖^2)*(x-y)^2 := by
    apply mul_pos
    · positivity
    · exact sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hpos)

/-- The scalar maximally mixed qubit reference, as an actual complex matrix. -/
def midpointReference : Matrix (Fin 2) (Fin 2) ℂ := (1/2 : ℝ) • 1

private theorem midpointReference_posDef : midpointReference.PosDef :=
  Matrix.PosDef.one.smul (show (0 : ℝ)<1/2 by norm_num)

private theorem rootFidelity_self (S : Matrix (Fin 2) (Fin 2) ℂ)
    (hS : S.PosSemidef) (hs : trace S=1) : rootFidelity S S=1 := by
  have hroot := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hprod : CFC.sqrt S*S*CFC.sqrt S=S*S := by
    calc
      _ = CFC.sqrt S*(CFC.sqrt S*CFC.sqrt S)*CFC.sqrt S := by rw [hroot]
      _ = (CFC.sqrt S*CFC.sqrt S)*(CFC.sqrt S*CFC.sqrt S) := by simp only [Matrix.mul_assoc]
      _ = S*S := by rw [hroot]
  rw [rootFidelity,hprod,CFC.sqrt_mul_self S hS.nonneg,hs] <;> rfl

private theorem map_mixture (Phi : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
    (p : ℝ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Phi (mixture p A B)=mixture p (Phi A) (Phi B) := by
  change (Phi.restrictScalars ℝ) (p • A+(1-p) • B)=_
  simp only [mixture,map_add,map_smul] <;> rfl

/-- Every positive trace-preserving complex-linear qubit map obeys the
transported-reference midpoint inequality on commuting density inputs. -/
theorem commuting_midpoint_all_positive_trace_preserving
    (P Q : Matrix (Fin 2) (Fin 2) ℂ)
    (Phi : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (htP : trace P=1) (htQ : trace Q=1)
    (hcomm : P*Q=Q*P)
    (hpos : ∀ M, M.PosSemidef → (Phi M).PosSemidef)
    (htrace : ∀ M, trace (Phi M)=trace M) (hT : (Phi midpointReference).PosDef) :
    rootFidelity P Q=(fidelity midpointReference P Q).re ∧
      rootFidelity P Q ≤ (fidelity (Phi midpointReference) (Phi P) (Phi Q)).re ∧
      bures (Phi midpointReference) (Phi P) (Phi Q) ≤ bures midpointReference P Q := by
  have hvalues : rootFidelity P Q=(fidelity midpointReference P Q).re ∧
      rootFidelity P Q ≤ (fidelity (Phi midpointReference) (Phi P) (Phi Q)).re := by
    by_cases heq : P=Q
    · subst Q
      rw [rootFidelity_self P hP htP,
        fidelity_same_state P midpointReference hP midpointReference_posDef htP,
        fidelity_same_state (Phi P) (Phi midpointReference) (hpos P hP) hT
          ((htrace P).trans htP)]
      exact ⟨rfl,le_rfl⟩
    · have hrepr (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.PosSemidef)
          (htX : trace X=1) : X=blochMatrix 1 (bloch X) := by
        simpa only [htX,Complex.one_re] using (bloch_geometry_of_isHermitian X hX.isHermitian).1
      have hne : bloch P ≠ bloch Q := by
        intro h
        apply heq
        rw [hrepr P hP htP,hrepr Q hQ htQ,h]
      have hrP : ‖bloch P‖ ≤ 1 := by
        simpa only [htP,Complex.one_re] using norm_bloch_le_trace_of_posSemidef P hP
      have hrQ : ‖bloch Q‖ ≤ 1 := by
        simpa only [htQ,Complex.one_re] using norm_bloch_le_trace_of_posSemidef Q hQ
      obtain ⟨d,e,x,y,hde,he,hd,hx,hy,hxy,hpx,hqy,hr⟩ :=
        full_chord_of_distinct (bloch P) (bloch Q) hrP hrQ hne
      have hp : P=chordState d e x := by rw [hrepr P hP htP,hpx]; rfl
      have hq : Q=chordState d e y := by rw [hrepr Q hQ htQ,hqy]; rfl
      have hzero : ‖d‖^2=0 := commuting_chord_zero_foot d e hde he hd x y hxy (by rwa [← hp,← hq])
      have hd0 : d=0 := norm_eq_zero.mp (by nlinarith only [hzero,norm_nonneg d])
      have hR : midpointReference=chordState d e (1/2) := by
        rw [hd0]
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [midpointReference,chordState,chordVector,blochMatrix]
      have hhalf : (1/2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> norm_num
      have hFin := (qubit_chord_strict_sign_and_boundary d e hde he hd (1/2) x y hhalf hx hy).2.1 hzero
      rw [← hp,← hq,← hR] at hFin
      have hUsq := chord_root_fidelity_sq d e hde he hd x y hx hy
      rw [← hp,← hq,hzero] at hUsq
      norm_num at hUsq
      have hU : rootFidelity P Q=binaryFidelity x y := by
        have hw : 0 ≤ binaryFidelity x y := by dsimp [binaryFidelity]; positivity
        nlinarith only [hUsq,rootFidelity_nonneg P Q,hw]
      refine ⟨hU.trans hFin.symm,?_⟩
      let E1 := chordState d e 1
      let E0 := chordState d e 0
      have hE1 : E1.PosSemidef := bloch_physical _ (chord_norm_le d e hde he hd 1 (by norm_num))
      have hE0 : E0.PosSemidef := bloch_physical _ (chord_norm_le d e hde he hd 0 (by norm_num))
      have htr1 : trace E1=1 := blochMatrix_trace 1 _
      have htr0 : trace E0=1 := blochMatrix_trace 1 _
      have hm (z : ℝ) : chordState d e z=mixture z E1 E0 := by
        dsimp [E1,E0]
        rw [chord_mixture]
        congr 1
        ring
      have hPhiP : Phi P=mixture x (Phi E1) (Phi E0) := by rw [hp,hm,map_mixture]
      have hPhiQ : Phi Q=mixture y (Phi E1) (Phi E0) := by rw [hq,hm,map_mixture]
      have hPhiR : Phi midpointReference=mixture (1/2) (Phi E1) (Phi E0) := by rw [hR,hm,map_mixture]
      have hprepared := prepared_qubit_midpoint_fidelity (Phi E1) (Phi E0)
        (hpos E1 hE1) (hpos E0 hE0) ((htrace E1).trans htr1) ((htrace E0).trans htr0)
        x y hx hy (by rwa [← hPhiR])
      rw [hU,hPhiR,hPhiP,hPhiQ]
      exact hprepared.1
  refine ⟨hvalues.1,hvalues.2,?_⟩
  unfold bures
  rw [Matrix.trace_add,Matrix.trace_add,htrace P,htrace Q,htP,htQ]
  linarith only [hvalues.1,hvalues.2]

open D5.S3.Quantum.Foundation.FiniteStateChannel

/-- The complete midpoint conclusion on the existing all-amplification CPTP
carrier, with nonnegativity of both squared quantities and the distance bound. -/
theorem commuting_midpoint_canonical_CPTP
    (P Q : Matrix (Fin 2) (Fin 2) ℂ) (channel : QuantumChannel (Fin 2) (Fin 2))
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (htP : trace P=1) (htQ : trace Q=1)
    (hcomm : P*Q=Q*P) (hT : (rawMatrix channel midpointReference).PosDef) :
    0 ≤ bures (rawMatrix channel midpointReference) (rawMatrix channel P) (rawMatrix channel Q) ∧
      0 ≤ bures midpointReference P Q ∧
      bures (rawMatrix channel midpointReference) (rawMatrix channel P) (rawMatrix channel Q) ≤
        bures midpointReference P Q ∧
      Real.sqrt (bures (rawMatrix channel midpointReference) (rawMatrix channel P) (rawMatrix channel Q)) ≤
        Real.sqrt (bures midpointReference P Q) := by
  let Phi : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
    ((CStarMatrix.ofMatrixStarAlgEquiv.symm.toAlgEquiv.toLinearEquiv.toLinearMap).comp
      channel.toCompletelyPositiveMap.toLinearMap).comp
        CStarMatrix.ofMatrixStarAlgEquiv.toAlgEquiv.toLinearEquiv.toLinearMap
  have hraw (M : Matrix (Fin 2) (Fin 2) ℂ) : Phi M=rawMatrix channel M := rfl
  have hpos (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.PosSemidef) : (Phi M).PosSemidef := by
    change (rawMatrix channel M).PosSemidef
    exact (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
      (map_nonneg channel.toCompletelyPositiveMap
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hM.nonneg))).posSemidef
  have htrace (M : Matrix (Fin 2) (Fin 2) ℂ) : trace (Phi M)=trace M :=
    channel.trace_preserving (CStarMatrix.ofMatrix M)
  have h := commuting_midpoint_all_positive_trace_preserving P Q Phi hP hQ htP htQ hcomm hpos htrace hT
  have hB : bures (rawMatrix channel midpointReference) (rawMatrix channel P) (rawMatrix channel Q) ≤
      bures midpointReference P Q := h.2.2
  refine ⟨?_,?_,hB,Real.sqrt_le_sqrt hB⟩
  · rw [bures_eq_weighted_root_norm_sq (rawMatrix channel P) (rawMatrix channel Q)
      (rawMatrix channel midpointReference) (by exact hpos P hP) (by exact hpos Q hQ) hT]
    exact sq_nonneg _
  · rw [bures_eq_weighted_root_norm_sq _ _ _ hP hQ midpointReference_posDef]
    exact sq_nonneg _

/-- Universal physical channel monotonicity with the transported reference. -/
def Good (P Q R : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ channel : QuantumChannel (Fin 2) (Fin 2), (rawMatrix channel R).PosDef →
    bures (rawMatrix channel R) (rawMatrix channel P) (rawMatrix channel Q) ≤ bures R P Q

private theorem commuting_input_fidelity
    (P Q : Matrix (Fin 2) (Fin 2) ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (htP : trace P=1) (htQ : trace Q=1)
    (hcomm : P*Q=Q*P) :
    (fidelity midpointReference P Q).re=rootFidelity P Q := by
  exact (commuting_midpoint_all_positive_trace_preserving P Q (LinearMap.id)
    hP hQ htP htQ hcomm (fun _ h => h) (fun _ => rfl)
    midpointReference_posDef).1.symm

/-- A faithful density pair lies strictly outside scalar balance while every
admissible physical channel contracts its transported-reference distance. -/
theorem faithful_Good_outside_balance :
    let P : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(9/10 : ℂ),1/10]
    let Q : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(4/5 : ℂ),1/5]
    P.PosDef ∧ Q.PosDef ∧ midpointReference.PosDef ∧
      trace P=1 ∧ trace Q=1 ∧ trace midpointReference=1 ∧
      Good P Q midpointReference ∧
      rootFidelity midpointReference P^2=4/5 ∧
      rootFidelity midpointReference Q^2=9/10 ∧
      rootFidelity P Q^2=49/50 ∧
      |rootFidelity midpointReference P^2-rootFidelity midpointReference Q^2|=1/10 ∧
      1-rootFidelity P Q^2=1/50 ∧
      1-rootFidelity P Q^2 <
        |rootFidelity midpointReference P^2-rootFidelity midpointReference Q^2| ∧
      bures midpointReference P Q=2-7*Real.sqrt 2/5 := by
  classical
  dsimp only
  let P : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(9/10 : ℂ),1/10]
  let Q : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(4/5 : ℂ),1/5]
  have hP : P.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.lt_def]
  have hQ : Q.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.lt_def]
  have htP : trace P=1 := by norm_num [P,Matrix.trace,Fin.sum_univ_two]
  have htQ : trace Q=1 := by norm_num [Q,Matrix.trace,Fin.sum_univ_two]
  have htR : trace midpointReference=1 := by
    norm_num [midpointReference,Matrix.trace,Fin.sum_univ_two]
  have hcomm : P*Q=Q*P := by
    dsimp [P,Q]
    rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact mul_comm _ _
  have hGood : Good P Q midpointReference := by
    intro channel hT
    exact (commuting_midpoint_canonical_CPTP P Q channel hP.posSemidef hQ.posSemidef
      htP htQ hcomm hT).2.2.1
  have ha : rootFidelity midpointReference P^2=4/5 := by
    rw [rootFidelity_sq_formula _ _ midpointReference_posDef.posSemidef hP.posSemidef]
    norm_num [P,midpointReference,Matrix.trace,Matrix.det_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal_apply]
  have hb : rootFidelity midpointReference Q^2=9/10 := by
    rw [rootFidelity_sq_formula _ _ midpointReference_posDef.posSemidef hQ.posSemidef]
    norm_num [Q,midpointReference,Matrix.trace,Matrix.det_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal_apply]
  have hc : rootFidelity P Q^2=49/50 := by
    rw [rootFidelity_sq_formula _ _ hP.posSemidef hQ.posSemidef]
    norm_num [P,Q,Matrix.trace,Matrix.det_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal_apply]
  have hgap : |rootFidelity midpointReference P^2-rootFidelity midpointReference Q^2|=1/10 := by
    rw [ha,hb]
    norm_num
  have hres : 1-rootFidelity P Q^2=1/50 := by rw [hc]; norm_num
  have hcroot : rootFidelity P Q=7*Real.sqrt 2/10 := by
    have hsq : Real.sqrt 2^2=2 := Real.sq_sqrt (by norm_num)
    have hn := rootFidelity_nonneg P Q
    have h2 := Real.sqrt_nonneg (2 : ℝ)
    nlinarith only [hc,hsq,hn,h2]
  refine ⟨hP,hQ,midpointReference_posDef,htP,htQ,htR,hGood,
    ha,hb,hc,hgap,hres,?_,?_⟩
  · rw [hgap,hres]
    norm_num
  · unfold bures
    rw [Matrix.trace_add,htP,htQ,commuting_input_fidelity P Q hP.posSemidef
      hQ.posSemidef htP htQ hcomm,hcroot]
    norm_num
    <;> ring

/-- A rank-one input also gives an exact outside-balance triple with universal
transported-reference contraction. -/
theorem singular_Good_outside_balance :
    let P : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(1 : ℂ),0]
    let Q : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(3/4 : ℂ),1/4]
    P.PosSemidef ∧ Q.PosSemidef ∧ midpointReference.PosDef ∧
      trace P=1 ∧ trace Q=1 ∧ trace midpointReference=1 ∧ P.rank=1 ∧
      Good P Q midpointReference ∧
      rootFidelity midpointReference P^2=1/2 ∧
      rootFidelity midpointReference Q^2=1/2+Real.sqrt 3/4 ∧
      rootFidelity P Q^2=3/4 ∧
      |rootFidelity midpointReference P^2-rootFidelity midpointReference Q^2|=Real.sqrt 3/4 ∧
      1-rootFidelity P Q^2=1/4 ∧
      1-rootFidelity P Q^2 <
        |rootFidelity midpointReference P^2-rootFidelity midpointReference Q^2| ∧
      bures midpointReference P Q=2-Real.sqrt 3 := by
  classical
  dsimp only
  let P : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(1 : ℂ),0]
  let Q : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(3/4 : ℂ),1/4]
  have hP : P.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.le_def]
  have hQ : Q.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.le_def]
  have htP : trace P=1 := by norm_num [P,Matrix.trace,Fin.sum_univ_two]
  have htQ : trace Q=1 := by norm_num [Q,Matrix.trace,Fin.sum_univ_two]
  have htR : trace midpointReference=1 := by
    norm_num [midpointReference,Matrix.trace,Fin.sum_univ_two]
  have hcomm : P*Q=Q*P := by
    dsimp [P,Q]
    rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact mul_comm _ _
  have hGood : Good P Q midpointReference := by
    intro channel hT
    exact (commuting_midpoint_canonical_CPTP P Q channel hP hQ htP htQ hcomm hT).2.2.1
  have hrank : P.rank=1 := by
    dsimp [P]
    rw [Matrix.rank_diagonal,Fintype.card_subtype]
    have hfilter : Finset.univ.filter (fun i : Fin 2 => ![(1 : ℂ),0] i ≠ 0) = {0} := by
      ext i
      fin_cases i <;> norm_num
    rw [hfilter, Finset.card_singleton]
  have ha : rootFidelity midpointReference P^2=1/2 := by
    rw [rootFidelity_sq_formula _ _ midpointReference_posDef.posSemidef hP]
    norm_num [P,midpointReference,Matrix.trace,Matrix.det_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal_apply]
  have hb0 : rootFidelity midpointReference Q^2=1/2+2*Real.sqrt (3/64) := by
    rw [rootFidelity_sq_formula _ _ midpointReference_posDef.posSemidef hQ]
    norm_num [Q,midpointReference,Matrix.trace,Matrix.det_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal_apply]
  have hb : rootFidelity midpointReference Q^2=1/2+Real.sqrt 3/4 := by
    rw [hb0,Real.sqrt_div (by norm_num),show Real.sqrt (64 : ℝ)=8 by norm_num]
    ring
  have hc : rootFidelity P Q^2=3/4 := by
    rw [rootFidelity_sq_formula _ _ hP hQ]
    norm_num [P,Q,Matrix.trace,Matrix.det_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal_apply]
  have h3n : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
  have h3s : Real.sqrt (3 : ℝ)^2=3 := Real.sq_sqrt (by norm_num)
  have hgap : |rootFidelity midpointReference P^2-rootFidelity midpointReference Q^2|=Real.sqrt 3/4 := by
    rw [ha,hb,abs_of_nonpos (by linarith only [h3n])]
    ring
  have hres : 1-rootFidelity P Q^2=1/4 := by rw [hc]; norm_num
  have hcroot : rootFidelity P Q=Real.sqrt 3/2 := by
    nlinarith only [hc,h3s,h3n,rootFidelity_nonneg P Q]
  refine ⟨hP,hQ,midpointReference_posDef,htP,htQ,htR,hrank,hGood,
    ha,hb,hc,hgap,hres,?_,?_⟩
  · rw [hgap,hres]
    nlinarith only [h3s,h3n]
  · unfold bures
    rw [Matrix.trace_add,htP,htQ,commuting_input_fidelity P Q hP hQ htP htQ hcomm,hcroot]
    norm_num
    <;> ring

/-- The proposed physical necessity of scalar balance, including its entire
state domain and its universal common-channel quantifier. -/
def claim : Prop :=
  ∀ (P Q R : Matrix (Fin 2) (Fin 2) ℂ),
    P.PosSemidef → Q.PosSemidef → R.PosDef →
    trace P=1 → trace Q=1 → trace R=1 → Good P Q R →
    |rootFidelity R P^2-rootFidelity R Q^2| ≤ 1-rootFidelity P Q^2

/-- Scalar balance is not necessary for physical transported-reference
contraction, even when all three input states are positive definite. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨hP,hQ,hR,htP,htQ,htR,hGood,_ha,_hb,_hc,_hgap,_hres,hstrict,_hB⟩ :=
    faithful_Good_outside_balance
  have hbalance := h _ _ _ hP.posSemidef hQ.posSemidef hR htP htQ htR hGood
  exact (not_le_of_gt hstrict) hbalance

end D5.S3.Quantum.CommutingMidpoint
