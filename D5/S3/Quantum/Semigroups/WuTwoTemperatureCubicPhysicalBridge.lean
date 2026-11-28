/- GID: D5/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuTwoTemperatureCubicPhysicalBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical two-temperature cubic Gibbs bridge from CAR jump matrices to the ordinary Wu trace. -/

/-
proof_shape: content
admission_basis: escape-witness
escape_witness: The explicit product Gibbs matrix D = d r ⊗ₖ d R, its positive sixth root G,
and the lowering/raising jump intertwining identities establish the modular sandwich. The
trace calculation then identifies each physical mode with the directed cubic cost and sums
the two modes to Wu's ordinary cubic trace.
-/

import D5.S3.Quantum.Semigroups.WuTwoModeCliffordPluecker

/-! The physical cubic trace for two CAR modes with positive ratios `R, r`.
Occupation order is `00,01,10,11` and mode order is right then left.
The density uses the left factor at `r` and the right factor at `R`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuTwoTemperatureCubicPhysicalBridge

open WuCubicOperatorBridge (Frame Mat Occupation dissipator)
open WuCubicThermalBasis (a b e)
open WuTwoModeCliffordPluecker (jump jump_right jump_left)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (pauliMatrix)
open D5.S3.Quantum.FiniteDimensional (qubitZ)
open private gamma from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private trace_spectral_sandwich from D5.S3.Quantum.Semigroups.WuCubicOperatorBridge

def localEntry (t : ℝ) (k : Fin 2) : ℝ :=
  if k = 0 then a t else b t

def d (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal fun k => (localEntry t k : ℂ)

def gibbsEntry (R r : ℝ) (o : Occupation) : ℝ :=
  localEntry r o.1 * localEntry R o.2

def D (R r : ℝ) : Mat := diagonal fun o => (gibbsEntry R r o : ℂ)

theorem D_eq_tensor (R r : ℝ) : D R r = d r ⊗ₖ d R := by
  simp only [D, d, Matrix.diagonal_kronecker_diagonal, gibbsEntry, Complex.ofReal_mul]

private theorem a_pos {t : ℝ} (ht : 0 < t) : 0 < a t := by
  unfold a
  positivity

private theorem localEntry_pos {t : ℝ} (ht : 0 < t) (k : Fin 2) :
    0 < localEntry t k := by
  unfold localEntry
  split
  · exact a_pos ht
  · exact mul_pos (pow_pos ht 3) (a_pos ht)

theorem gibbsEntry_pos {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (o : Occupation) :
    0 < gibbsEntry R r o :=
  mul_pos (localEntry_pos hr o.1) (localEntry_pos hR o.2)

theorem D_posDef {R r : ℝ} (hR : 0 < R) (hr : 0 < r) : (D R r).PosDef :=
  Matrix.PosDef.diagonal (fun o => by exact_mod_cast gibbsEntry_pos hR hr o)

/-- At `r = 1` these are the reference entries in `WuTracialSpectatorRepeatedMiddle`. -/
theorem gibbsEntry_tracial (R : ℝ) (o : Occupation) :
    gibbsEntry R 1 o = if o.2 = 0 then a R / 2 else b R / 2 := by
  have ha : a 1 = (1 / 2 : ℝ) := by norm_num [a]
  have hb : b 1 = (1 / 2 : ℝ) := by norm_num [a, b]
  by_cases h : o.2 = 0 <;> simp [gibbsEntry, localEntry, ha, hb, h, div_eq_mul_inv, mul_comm]

private def localRoot (t : ℝ) (k : Fin 2) : ℝ :=
  let s := a t ^ (1 / 6 : ℝ)
  if k = 0 then s else s * Real.sqrt t

private def rootEntry (R r : ℝ) (o : Occupation) : ℝ :=
  localRoot r o.1 * localRoot R o.2

def G (R r : ℝ) : Mat := diagonal fun o => (rootEntry R r o : ℂ)

def GInv (R r : ℝ) : Mat := diagonal fun o => ((rootEntry R r o : ℂ)⁻¹)

private theorem localRoot_pos {t : ℝ} (ht : 0 < t) (k : Fin 2) :
    0 < localRoot t k := by
  have hs : 0 < a t ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos (a_pos ht) _
  by_cases hk : k = 0
  · simpa [localRoot, hk] using hs
  · simpa [localRoot, hk] using mul_pos hs (Real.sqrt_pos.2 ht)

private theorem rootEntry_pos {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (o : Occupation) :
    0 < rootEntry R r o :=
  mul_pos (localRoot_pos hr o.1) (localRoot_pos hR o.2)

private theorem localRoot_pow_six {t : ℝ} (ht : 0 < t) (k : Fin 2) :
    localRoot t k ^ 6 = localEntry t k := by
  have hs : (a t ^ (1 / 6 : ℝ)) ^ (6 : ℕ) = a t := by
    rw [← Real.rpow_mul_natCast (a_pos ht).le]
    norm_num
  have hq : Real.sqrt t ^ 6 = t ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, Real.sq_sqrt ht.le]
  by_cases hk : k = 0
  · simp only [localRoot, localEntry, if_pos hk]
    exact hs
  · simp only [localRoot, localEntry, if_neg hk, mul_pow, hs, hq]
    unfold b
    ring

private theorem rootEntry_pow_six {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (o : Occupation) :
    rootEntry R r o ^ 6 = gibbsEntry R r o := by
  rw [rootEntry, gibbsEntry, mul_pow, localRoot_pow_six hr, localRoot_pow_six hR]

theorem G_pow_six {R r : ℝ} (hR : 0 < R) (hr : 0 < r) : G R r ^ 6 = D R r := by
  rw [G, D, Matrix.diagonal_pow]
  congr 1
  funext o
  rw [Pi.pow_apply, ← Complex.ofReal_pow, rootEntry_pow_six hR hr]

/-- `G` is the positive sixth root used in Wu's cubic sandwich. -/
theorem G_eq_cfc {R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    G R r = cfc (fun x : ℝ => x ^ (1 / 6 : ℝ)) (D R r) := by
  have hDiag : cfc (fun x : ℝ => x ^ (1 / 6 : ℝ)) (D R r) =
      diagonal (fun o => ((gibbsEntry R r o ^ (1 / 6 : ℝ) : ℝ) : ℂ)) := by
    simpa only [D, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      Matrix.cfc_diagonal_real (𝕜 := ℂ) (gibbsEntry R r) (fun x => x ^ (1 / 6 : ℝ))
  rw [hDiag, G]
  congr 1
  funext o
  apply congrArg Complex.ofReal
  rw [← rootEntry_pow_six hR hr o, one_div]
  simpa only [Nat.cast_ofNat] using
    (Real.pow_rpow_inv_natCast (n := 6) (rootEntry_pos hR hr o).le (by decide)).symm

theorem G_mul_GInv {R r : ℝ} (hR : 0 < R) (hr : 0 < r) : G R r * GInv R r = 1 := by
  rw [G, GInv, Matrix.diagonal_mul_diagonal]
  change diagonal (fun o => (rootEntry R r o : ℂ) * (rootEntry R r o : ℂ)⁻¹) =
    diagonal (fun _ : Occupation => (1 : ℂ))
  congr 1
  funext o
  have ho : (rootEntry R r o : ℂ) ≠ 0 := by exact_mod_cast (rootEntry_pos hR hr o).ne'
  exact mul_inv_cancel₀ ho

theorem GInv_mul_G {R r : ℝ} (hR : 0 < R) (hr : 0 < r) : GInv R r * G R r = 1 := by
  have hc : Commute (GInv R r) (G R r) := by
    unfold GInv G
    exact Matrix.commute_diagonal
      (fun o : Occupation => (rootEntry R r o : ℂ)⁻¹)
      (fun o : Occupation => (rootEntry R r o : ℂ))
  exact hc.eq.trans (G_mul_GInv hR hr)

private theorem G_adjoint (R r : ℝ) : (G R r)ᴴ = G R r := by
  simp only [G, Matrix.diagonal_conjTranspose]
  congr 1
  funext o
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]

/-- Right and left ratios in the right-then-left order of `jump`. -/
def modeRatio (R r : ℝ) (j : Fin 2) : ℝ := ![R, r] j

def modeGenerator (t : ℝ) (J X : Mat) : Mat :=
  (2 * (a t : ℂ)) • dissipator J X + (2 * (b t : ℂ)) • dissipator Jᴴ X

/-- The Kirchhoff generator at rates `2a t, 2b t` for each mode's ratio `t`. -/
def generator (R r : ℝ) (X : Mat) : Mat :=
  modeGenerator R (jump 0) X + modeGenerator r (jump 1) X

theorem generator_eq_cold_add_tracial (R : ℝ) (X : Mat) :
    generator R 1 X = modeGenerator R (jump 0) X + WuTwoModeCliffordPluecker.tracial 1 X := by
  have haReal : 2 * a 1 = 1 := by norm_num [a]
  have hbReal : 2 * b 1 = 1 := by norm_num [a, b]
  have ha : 2 * (a 1 : ℂ) = 1 := by exact_mod_cast haReal
  have hb : 2 * (b 1 : ℂ) = 1 := by exact_mod_cast hbReal
  simp only [generator, modeGenerator, WuTwoModeCliffordPluecker.tracial, ha, hb, one_smul]

/-- Along a lowering edge the source root is `√t` times the target root.
The other mode's local root occurs in both product entries. -/
theorem jump_mul_G (R r : ℝ) (j : Fin 2) :
    jump j * G R r = (Real.sqrt (modeRatio R r j) : ℂ) • (G R r * jump j) := by
  ext ⟨i₁, i₂⟩ ⟨k₁, k₂⟩
  simp only [G, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  fin_cases j <;> fin_cases i₁ <;> fin_cases i₂ <;> fin_cases k₁ <;> fin_cases k₂ <;>
    norm_num [jump_right, jump_left, pauliMatrix, qubitZ, e, Matrix.kroneckerMap_apply,
      Matrix.diagonal_apply, Matrix.one_apply, rootEntry, localRoot, modeRatio, Complex.ofReal_mul] <;>
    ring

theorem G_mul_jump_adjoint (R r : ℝ) (j : Fin 2) :
    G R r * (jump j)ᴴ = (Real.sqrt (modeRatio R r j) : ℂ) • ((jump j)ᴴ * G R r) := by
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, G_adjoint,
    Complex.star_def, Complex.conj_ofReal] using
      congrArg (fun X : Mat => Xᴴ) (jump_mul_G R r j)

private theorem sandwich_dissipator (G₀ J X : Mat) (q : ℂ)
    (hJ : J * G₀ = q • (G₀ * J)) (hAdj : G₀ * Jᴴ = q • (Jᴴ * G₀)) :
    G₀ * dissipator J X * G₀ =
      (1 / 2 : ℂ) • (Jᴴ * J * (G₀ * X * G₀) + (G₀ * X * G₀) * (Jᴴ * J)) -
        q ^ 2 • (Jᴴ * (G₀ * X * G₀) * J) := by
  have hP : G₀ * (Jᴴ * J) = (Jᴴ * J) * G₀ := by
    calc
      _ = (G₀ * Jᴴ) * J := (Matrix.mul_assoc _ _ _).symm
      _ = q • (Jᴴ * (G₀ * J)) := by rw [hAdj, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_assoc, hJ, Matrix.mul_smul]
  have hLeft : G₀ * ((Jᴴ * J) * X) * G₀ = (Jᴴ * J) * (G₀ * X * G₀) := by
    rw [← Matrix.mul_assoc G₀ (Jᴴ * J) X, hP]
    simp only [Matrix.mul_assoc]
  have hRight : G₀ * (X * (Jᴴ * J)) * G₀ = (G₀ * X * G₀) * (Jᴴ * J) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Jᴴ J G₀, ← hP]
  have hGain : G₀ * (Jᴴ * X * J) * G₀ = q ^ 2 • (Jᴴ * (G₀ * X * G₀) * J) := by
    calc
      _ = (G₀ * Jᴴ) * X * (J * G₀) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hAdj, hJ]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two, Matrix.mul_assoc]
  simp only [dissipator, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, hLeft, hRight, hGain]

private def modularTerm (t : ℝ) (J M : Mat) : Mat :=
  ((a t : ℂ) • (Jᴴ * J * M + M * (Jᴴ * J)) -
    (2 * (a t : ℂ) * (t : ℂ)) • (Jᴴ * M * J)) +
  ((b t : ℂ) • (J * Jᴴ * M + M * (J * Jᴴ)) -
    (2 * (b t : ℂ) * (t : ℂ)⁻¹) • (J * M * Jᴴ))

private theorem sandwich_modeGenerator (G₀ J X : Mat) (t : ℝ) (q : ℂ) (hq : q ≠ 0)
    (hq2 : q ^ 2 = (t : ℂ))
    (hJ : J * G₀ = q • (G₀ * J)) (hAdj : G₀ * Jᴴ = q • (Jᴴ * G₀)) :
    G₀ * modeGenerator t J X * G₀ = modularTerm t J (G₀ * X * G₀) := by
  have hRaise : Jᴴ * G₀ = q⁻¹ • (G₀ * Jᴴ) := by
    rw [hAdj, inv_smul_smul₀ hq]
  have hRaiseAdj : G₀ * (Jᴴ)ᴴ = q⁻¹ • ((Jᴴ)ᴴ * G₀) := by
    rw [Matrix.conjTranspose_conjTranspose, hJ, inv_smul_smul₀ hq]
  have half (c : ℂ) : 2 * c * (1 / 2 : ℂ) = c := by ring
  simp only [modeGenerator, modularTerm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, sandwich_dissipator G₀ J X q hJ hAdj,
    sandwich_dissipator G₀ Jᴴ X q⁻¹ hRaise hRaiseAdj, Matrix.conjTranspose_conjTranspose,
    inv_pow, hq2, smul_sub, smul_smul, half]

/-- One directed cell includes the paired lowering and raising contributions. -/
def cost (t x y : ℝ) : ℝ := gamma t * (t * x - y) ^ 2 * (t * x + y)

def weight (U : Frame) (j : Fin 2) (i k : Fin 4) : ℝ :=
  Complex.normSq ((Uᴴ * jump j * U) i k)

def energy (t : ℝ) (U : Frame) (j : Fin 2) (v : Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ k, cost t (v i) (v k) * weight U j i k

private theorem modularTerm_trace {t : ℝ} (ht : 0 < t) (U : Frame)
    (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1) (v : Fin 4 → ℝ) (J : Mat) :
    let M := U * diagonal (fun i => (v i : ℂ)) * Uᴴ
    (9 / 8 : ℝ) * (M ^ 2 * modularTerm t J M).trace.re =
      ∑ i, ∑ k, cost t (v i) (v k) * Complex.normSq ((Uᴴ * J * U) i k) := by
  let M := U * diagonal (fun i => (v i : ℂ)) * Uᴴ
  change (9 / 8 : ℝ) * (M ^ 2 * modularTerm t J M).trace.re = _
  have trace_sandwich (A : Mat) (p q : ℕ) :
      (M ^ p * Aᴴ * M ^ q * A).trace.re =
        ∑ i, ∑ k, Complex.normSq ((Uᴴ * A * U) i k) * v k ^ p * v i ^ q :=
    trace_spectral_sandwich U hU hUU v A p q
  have trace_anticommutator (A : Mat) :
      (M ^ 2 * (Aᴴ * A * M + M * (Aᴴ * A))).trace.re =
        2 * ∑ i, ∑ k, Complex.normSq ((Uᴴ * A * U) i k) * v k ^ 3 := by
    have left : (M ^ 2 * (Aᴴ * A * M)).trace = (M ^ 3 * Aᴴ * M ^ 0 * A).trace := by
      rw [Matrix.trace_mul_cycle', ← Matrix.mul_assoc M, ← pow_succ',
        pow_zero, Matrix.mul_one, Matrix.mul_assoc]
    have right : (M ^ 2 * (M * (Aᴴ * A))).trace = (M ^ 3 * Aᴴ * M ^ 0 * A).trace := by
      rw [← Matrix.mul_assoc, ← pow_succ, pow_zero, Matrix.mul_one, Matrix.mul_assoc]
    rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, left, right, trace_sandwich]
    simp only [pow_zero, mul_one, two_mul]
  have adjoint_weight (i k : Fin 4) :
      Complex.normSq ((Uᴴ * Jᴴ * U) k i) = Complex.normSq ((Uᴴ * J * U) i k) := by
    have h : Uᴴ * Jᴴ * U = (Uᴴ * J * U)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [h, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  have upper_anticommutator := trace_anticommutator Jᴴ
  rw [Matrix.conjTranspose_conjTranspose, Finset.sum_comm] at upper_anticommutator
  simp only [adjoint_weight] at upper_anticommutator
  have upper_sandwich := trace_sandwich Jᴴ 2 1
  rw [Matrix.conjTranspose_conjTranspose, Finset.sum_comm] at upper_sandwich
  simp only [adjoint_weight, pow_one] at upper_sandwich
  have lower_sandwich := trace_sandwich J 2 1
  simp only [pow_one] at lower_sandwich
  have lowerCoeff : 2 * (a t : ℂ) * (t : ℂ) = ((2 * a t * t : ℝ) : ℂ) := by
    push_cast
    rfl
  have upperCoeff : 2 * (b t : ℂ) * (t : ℂ)⁻¹ = ((2 * a t * t ^ 2 : ℝ) : ℂ) := by
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    push_cast
    simp only [b, Complex.ofReal_mul, Complex.ofReal_pow]
    field_simp [ht']
  have prefactor : gamma t = (9 / 4) * a t := by
    rw [gamma, a, div_mul_div_comm, mul_one]
  unfold modularTerm
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re,
    Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
    Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, lowerCoeff, upperCoeff,
    Complex.re_ofReal_mul]
  rw [trace_anticommutator J, upper_anticommutator]
  simp only [Matrix.mul_assoc] at lower_sandwich upper_sandwich ⊢
  rw [lower_sandwich, upper_sandwich]
  simp only [mul_assoc, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [cost, prefactor, b]
  ring

/-- A single physical mode in any Gibbs sandwich satisfying the lowering and
raising intertwining laws. The spectral weight uses the target as its row. -/
theorem mode_trace_of_intertwining {t : ℝ} (ht : 0 < t) (U : Frame)
    (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1) (v : Fin 4 → ℝ) (G₀ J X : Mat)
    (q : ℂ) (hq : q ≠ 0) (hq2 : q ^ 2 = (t : ℂ))
    (hJ : J * G₀ = q • (G₀ * J)) (hAdj : G₀ * Jᴴ = q • (Jᴴ * G₀))
    (hM : G₀ * X * G₀ = U * diagonal (fun i => (v i : ℂ)) * Uᴴ) :
    let M := U * diagonal (fun i => (v i : ℂ)) * Uᴴ
    (9 / 8 : ℝ) * (M ^ 2 * (G₀ * modeGenerator t J X * G₀)).trace.re =
      ∑ i, ∑ k, cost t (v i) (v k) * Complex.normSq ((Uᴴ * J * U) i k) := by
  dsimp only
  rw [sandwich_modeGenerator G₀ J X t q hq hq2 hJ hAdj, hM]
  exact modularTerm_trace ht U hU hUU v J

/-- The physical trace of one mode. The proof uses the modular factors `t` and
`t⁻¹` on the gain terms of the lowering and raising jumps, respectively. -/
theorem mode_energy_eq_operator {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (U : Frame)
    (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1) (j : Fin 2) (v : Fin 4 → ℝ) :
    let M := U * diagonal (fun i => (v i : ℂ)) * Uᴴ
    let X := GInv R r * M * GInv R r
    energy (modeRatio R r j) U j v =
      (9 / 8 : ℝ) *
        (M ^ 2 * (G R r * modeGenerator (modeRatio R r j) (jump j) X * G R r)).trace.re := by
  let M := U * diagonal (fun i => (v i : ℂ)) * Uᴴ
  let X := GInv R r * M * GInv R r
  let t := modeRatio R r j
  let q : ℂ := (Real.sqrt t : ℂ)
  change energy t U j v = (9 / 8 : ℝ) * (M ^ 2 * (G R r * modeGenerator t (jump j) X * G R r)).trace.re
  have ht : 0 < t := by
    fin_cases j <;> simp [t, modeRatio, hR, hr]
  have hq : q ≠ 0 := by
    change (Real.sqrt t : ℂ) ≠ 0
    exact_mod_cast (Real.sqrt_pos.2 ht).ne'
  have hq2 : q ^ 2 = (t : ℂ) := by
    change (Real.sqrt t : ℂ) ^ 2 = (t : ℂ)
    exact_mod_cast Real.sq_sqrt ht.le
  have hM : G R r * X * G R r = M := by
    calc
      _ = (G R r * GInv R r) * M * (GInv R r * G R r) := by simp only [X, Matrix.mul_assoc]
      _ = _ := by rw [G_mul_GInv hR hr, GInv_mul_G hR hr, Matrix.one_mul, Matrix.mul_one]
  exact (mode_trace_of_intertwining ht U hU hUU v (G R r) (jump j) X q hq hq2
    (jump_mul_G R r j) (G_mul_jump_adjoint R r j) hM).symm

/-- The ordinary cubic trace in Wu v1 (3.54) for `D = d r ⊗ₖ d R`.
The identity holds for arbitrary real spectral roots, including zero roots. -/
theorem energy_eq_operator {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (U : Frame)
    (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1) (v : Fin 4 → ℝ) :
    let M := U * diagonal (fun i => (v i : ℂ)) * Uᴴ
    energy R U 0 v + energy r U 1 v =
      (9 / 8 : ℝ) * (M ^ 2 * (G R r * generator R r (GInv R r * M * GInv R r) * G R r)).trace.re := by
  let M := U * diagonal (fun i => (v i : ℂ)) * Uᴴ
  change energy (modeRatio R r 0) U 0 v + energy (modeRatio R r 1) U 1 v =
    (9 / 8 : ℝ) * (M ^ 2 * (G R r * generator R r (GInv R r * M * GInv R r) * G R r)).trace.re
  rw [mode_energy_eq_operator hR hr U hU hUU 0 v, mode_energy_eq_operator hR hr U hU hUU 1 v]
  simp only [M, modeRatio, Matrix.cons_val_zero, Matrix.cons_val_one, generator,
    Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Complex.add_re, mul_add]

end D5.S3.Quantum.Semigroups.WuTwoTemperatureCubicPhysicalBridge
