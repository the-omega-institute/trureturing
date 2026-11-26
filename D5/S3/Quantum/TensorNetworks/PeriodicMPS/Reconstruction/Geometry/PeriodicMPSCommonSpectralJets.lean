/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSCommonSpectralJets
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSCommonSpectralJets
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Literal trace-word derivatives specialize to the common spectral witness. -/
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-! The rational transfer-jet certificate at the common zero/repeated-root witness.
The suffix contraction and dual-number lift follow PeriodicMPSTwoSiteDifferential,
where the corresponding lemmas are private. -/

namespace PeriodicMPSCommonSpectralJets

open Matrix Polynomial TrivSqZeroExt
open scoped BigOperators Matrix Kronecker

set_option maxHeartbeats 1000000

abbrev Bits := Fin 2 × Fin 2
abbrev Entry := Bits × Bits
abbrev Direction := Fin 4 × Fin 2 × Fin 2
abbrev Core (R : Type*) := Matrix (Fin 2) (Fin 2) R
abbrev Transfer (R : Type*) := Matrix Bits Bits R

/-- The word product along a binary suffix in its original order. -/
def suffixProduct {R : Type*} [Semiring R]
    (K : Fin 2 → Core R) {m : ℕ} (w : Fin m → Fin 2) : Core R :=
  (List.ofFn fun i => K (w i)).prod

def wordReadout {R : Type*} [Semiring R]
    (K : Fin 2 → Core R) (p : Bits) {m : ℕ} (w : Fin m → Fin 2) : R :=
  (K p.1 * K p.2 * suffixProduct K w).trace

/-- Complexified adjacent-pair Gram entry, with the same suffix on both sides. -/
def literalGram {R : Type*} [Semiring R]
    (K B : Fin 2 → Core R) (m : ℕ) (p : Entry) : R :=
  ∑ w : Fin m → Fin 2, wordReadout K p.1 w * wordReadout B p.2 w

def transfer {R : Type*} [Add R] [Mul R] (K B : Fin 2 → Core R) : Transfer R :=
  K 0 ⊗ₖ B 0 + K 1 ⊗ₖ B 1

def insertion {R : Type*} [Semiring R] (K B : Fin 2 → Core R) (p : Entry) :
    Transfer R :=
  (K p.1.1 * K p.1.2) ⊗ₖ (B p.2.1 * B p.2.2)

def contraction {R : Type*} [CommSemiring R] (K B : Fin 2 → Core R)
    (m : ℕ) (p : Entry) : R :=
  (insertion K B p * transfer K B ^ m).trace

private theorem transfer_pow {R : Type*} [CommSemiring R]
    (K B : Fin 2 → Core R) (m : ℕ) :
    transfer K B ^ m =
      ∑ w : Fin m → Fin 2, suffixProduct K w ⊗ₖ suffixProduct B w := by
  induction m with
  | zero => simp [suffixProduct, Finset.univ_unique]
  | succ m ih =>
    rw [pow_succ', ih, ← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 2)).sum_comp,
      Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, suffixProduct, List.ofFn_succ, Fin.cons_zero,
      Fin.cons_succ, List.prod_cons, Fin.sum_univ_two]
    unfold transfer
    simp_rw [Matrix.mul_kronecker_mul, ← Finset.mul_sum, ← add_mul]

theorem literalGram_eq_contraction {R : Type*} [CommSemiring R]
    (K B : Fin 2 → Core R) (m : ℕ) (p : Entry) :
    literalGram K B m p = contraction K B m p := by
  rw [contraction, transfer_pow, Matrix.mul_sum, Matrix.trace_sum, literalGram]
  apply Finset.sum_congr rfl
  intro w _
  rw [insertion, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  rfl

def cores : Fin 4 → Core ℚ :=
  ![!![0, 1; -1, 1], !![0, 1; 0, 0], !![0, 3; -1, 1], !![-3, 3; -1, 3]]

def ketIndex (i : Fin 2) : Fin 4 := ⟨i.val, by omega⟩
def braIndex (i : Fin 2) : Fin 4 := ⟨2 + i.val, by omega⟩

def rows : Fin 9 → Entry :=
  ![((0, 0), (0, 0)), ((0, 0), (0, 1)), ((0, 0), (1, 1)),
    ((0, 1), (0, 0)), ((0, 1), (0, 1)), ((0, 1), (1, 0)), ((0, 1), (1, 1)),
    ((1, 1), (0, 0)), ((1, 1), (0, 1))]

def columns : Fin 9 → Direction :=
  ![(0, 0, 0), (0, 0, 1), (0, 1, 0), (1, 0, 0), (1, 1, 0),
    (2, 0, 0), (2, 0, 1), (2, 1, 1), (3, 0, 0)]

def unit (d : Direction) (a : Fin 4) (i j : Fin 2) : ℚ :=
  if (a, i, j) = d then 1 else 0

def jetCore (d : Direction) (a : Fin 4) : Core (DualNumber ℚ) :=
  fun i j => ⟨cores a i j, unit d a i j⟩

noncomputable def lineCore (d : Direction) (a : Fin 4) : Core (Polynomial ℚ) :=
  fun i j => C (cores a i j) + X * C (unit d a i j)

/-- The literal derivative along a single coordinate line, as a polynomial derivative at zero. -/
noncomputable def literalJacobian (m : ℕ) : Matrix (Fin 9) (Fin 9) ℚ :=
  fun i j => (literalGram (lineCore (columns j) ∘ ketIndex)
    (lineCore (columns j) ∘ braIndex) m (rows i)).derivative.eval 0

def jetTransfer (d : Direction) : Transfer (DualNumber ℚ) :=
  transfer (jetCore d ∘ ketIndex) (jetCore d ∘ braIndex)

def jetInsertion (d : Direction) (p : Entry) : Transfer (DualNumber ℚ) :=
  insertion (jetCore d ∘ ketIndex) (jetCore d ∘ braIndex) p

/-- The nine output entries differentiated in the nine specified coordinate directions. -/
def J (m : ℕ) : Matrix (Fin 9) (Fin 9) ℚ :=
  fun i j => ((jetInsertion (columns j) (rows i) * jetTransfer (columns j) ^ m).trace).snd

private def dualEval : Polynomial ℚ →+* DualNumber ℚ :=
  eval₂RingHom (inlHom ℚ ℚ) DualNumber.eps

private theorem dualEval_snd (q : Polynomial ℚ) : (dualEval q).snd = q.coeff 1 := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, snd_add, coeff_add, hp, hq]
  | monomial n a =>
    rcases n with _ | _ | n
    · simp [dualEval]
    · simp [dualEval, ← C_mul_X_pow_eq_monomial]
    · have h : (DualNumber.eps : DualNumber ℚ) ^ (n + 2) = 0 := by
        rw [pow_add, DualNumber.eps_pow_two, mul_zero]
      simp [dualEval, ← C_mul_X_pow_eq_monomial, h]

private theorem map_lineCore (d : Direction) (a : Fin 4) :
    (lineCore d a).map dualEval = jetCore d a := by
  apply Matrix.ext
  intro i j
  change dualEval (C (cores a i j) + X * C (unit d a i j)) = ⟨_, _⟩
  apply TrivSqZeroExt.ext <;> simp [dualEval]

private theorem map_contraction {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (K B : Fin 2 → Core R) (m : ℕ) (p : Entry) :
    f (contraction K B m p) =
      contraction (fun i => (K i).map f) (fun i => (B i).map f) m p := by
  let g : Transfer R →+* Transfer S := RingHom.mapMatrix f
  have hK (A D : Core R) : g (A ⊗ₖ D) = A.map f ⊗ₖ D.map f := by
    ext i j
    exact f.map_mul _ _
  rw [contraction, AddMonoidHom.map_trace f]
  change (g (_ * _ ^ _)).trace = _
  simp only [contraction, map_mul, map_pow, insertion, transfer, map_add, hK]
  let g₂ : Core R →+* Core S := RingHom.mapMatrix f
  simp only [show ∀ A D : Core R, (A * D).map f = A.map f * D.map f from g₂.map_mul]

theorem literalJacobian_eq_J (m : ℕ) : literalJacobian m = J m := by
  ext i j
  unfold literalJacobian
  simp only [← coeff_zero_eq_eval_zero, coeff_derivative, zero_add, Nat.cast_zero, mul_one]
  rw [← dualEval_snd, literalGram_eq_contraction, map_contraction]
  simp only [Function.comp_apply, map_lineCore]
  rfl

def baseTransfer : Transfer ℚ := transfer (cores ∘ ketIndex) (cores ∘ braIndex)

private def toBits : Fin 4 ≃ Bits := (finProdFinEquiv (m := 2) (n := 2)).symm

def packedBaseTransfer : Matrix (Fin 4) (Fin 4) ℚ :=
  baseTransfer.submatrix toBits toBits

theorem packedBaseTransfer_eq : packedBaseTransfer = !![
    0, 0, -3, 6;
    0, 0, -2, 4;
    0, -3, 0, 3;
    1, -1, -1, 1] := by
  apply Matrix.ext
  intro i j
  exact (by decide +kernel : ∀ ij : Fin 4 × Fin 4, packedBaseTransfer ij.1 ij.2 =
    (!![0, 0, -3, 6; 0, 0, -2, 4; 0, -3, 0, 3; 1, -1, -1, 1] :
      Matrix (Fin 4) (Fin 4) ℚ) ij.1 ij.2) (i, j)

private def fstRing : DualNumber ℚ →+* ℚ := (fstHom ℚ ℚ ℚ).toRingHom

private theorem fst_jetTransfer (d : Direction) :
    RingHom.mapMatrix fstRing (jetTransfer d) = baseTransfer := by
  ext i j
  change fstRing ((jetTransfer d) i j) = baseTransfer i j
  rfl

private theorem square_zero_of_fst_zero (M : Transfer (DualNumber ℚ))
    (h : RingHom.mapMatrix fstRing M = 0) : M * M = 0 := by
  have hz (i j : Bits) : (M i j).fst = 0 := congrFun (congrFun h i) j
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply TrivSqZeroExt.ext
  · simp [hz]
  · simp [hz]

theorem baseTransfer_charpoly :
    baseTransfer.charpoly = X * (X - 3) * (X + 1)^2 := by
  have reindex : packedBaseTransfer.charpoly = baseTransfer.charpoly :=
    Matrix.charpoly_reindex toBits.symm baseTransfer
  let M : Matrix (Fin 4) (Fin 4) ℚ[X] :=
    !![X, 0, 3, -6; 0, X, 2, -4; 0, 3, X, -3; -1, 1, 1, X - 1]
  have hM : packedBaseTransfer.charmatrix = M := by
    rw [packedBaseTransfer_eq]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [M, Matrix.charmatrix_apply, Matrix.diagonal_apply, map_ofNat]
  rw [← reindex, Matrix.charpoly, hM, Matrix.det_succ_column_zero, Fin.sum_univ_four]
  have h₀ : M.submatrix ((0 : Fin 4).succAbove) Fin.succ =
      !![X, 2, -4; 3, X, -3; 1, 1, X - 1] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have h₃ : M.submatrix ((3 : Fin 4).succAbove) Fin.succ =
      !![0, 3, -6; X, 2, -4; 3, X, -3] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h₀, h₃]
  norm_num [M, Matrix.det_fin_three]
  ring

private theorem base_annihilator :
    baseTransfer ^ 4 - baseTransfer ^ 3 - 5 • baseTransfer ^ 2 - 3 • baseTransfer = 0 := by
  have hpoly : baseTransfer.charpoly = X ^ 4 - X ^ 3 - 5 • X ^ 2 - 3 • X := by
    rw [baseTransfer_charpoly]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have h := Matrix.aeval_self_charpoly baseTransfer
  rw [hpoly] at h
  simpa only [map_pow, aeval_X, map_sub, map_nsmul] using h

/-- Squaring the lifted quartic annihilator kills its first-order part.
The two powers belonging to the zero root leave six recurrence terms after the shift. -/
private theorem jet_annihilator {S : Type*} [CommRing S]
    (T : Matrix Bits Bits S)
    (h : (T ^ 4 - T ^ 3 - 5 • T ^ 2 - 3 • T) *
      (T ^ 4 - T ^ 3 - 5 • T ^ 2 - 3 • T) = 0) :
    T ^ 8 = 2 • T ^ 7 + 9 • T ^ 6 - 4 • T ^ 5 - 31 • T ^ 4 -
      30 • T ^ 3 - 9 • T ^ 2 := by
  calc
    T ^ 8 = (T ^ 4 - T ^ 3 - 5 • T ^ 2 - 3 • T) *
        (T ^ 4 - T ^ 3 - 5 • T ^ 2 - 3 • T) +
        (2 • T ^ 7 + 9 • T ^ 6 - 4 • T ^ 5 - 31 • T ^ 4 -
          30 • T ^ 3 - 9 • T ^ 2) := by
      have hpoly : (X : ℤ[X]) ^ 8 = (X ^ 4 - X ^ 3 - 5 • X ^ 2 - 3 • X) *
          (X ^ 4 - X ^ 3 - 5 • X ^ 2 - 3 • X) +
          (2 • X ^ 7 + 9 • X ^ 6 - 4 • X ^ 5 - 31 • X ^ 4 -
            30 • X ^ 3 - 9 • X ^ 2) := by
        simp only [nsmul_eq_mul, Nat.cast_ofNat]
        ring
      simpa only [map_pow, aeval_X, map_mul, map_add, map_sub, map_nsmul] using
        congrArg (aeval T : ℤ[X] →ₐ[ℤ] Matrix Bits Bits S) hpoly
    _ = _ := by rw [h, zero_add]

private theorem jet_power_recurrence (d : Direction) (n : ℕ) :
    (jetTransfer d) ^ (n + 8) =
      2 • (jetTransfer d) ^ (n + 7) + 9 • (jetTransfer d) ^ (n + 6) -
      4 • (jetTransfer d) ^ (n + 5) - 31 • (jetTransfer d) ^ (n + 4) -
      30 • (jetTransfer d) ^ (n + 3) - 9 • (jetTransfer d) ^ (n + 2) := by
  let T := jetTransfer d
  have h : (T ^ 4 - T ^ 3 - 5 • T ^ 2 - 3 • T) *
      (T ^ 4 - T ^ 3 - 5 • T ^ 2 - 3 • T) = 0 := by
    apply square_zero_of_fst_zero
    simpa only [map_sub, map_pow, map_nsmul, T, fst_jetTransfer] using base_annihilator
  simpa only [mul_add, mul_sub, mul_smul_comm, ← pow_add, T] using
    congrArg (fun M => T ^ n * M) (jet_annihilator T h)

/-- The degree-six recurrence starts at suffix length eight. -/
theorem J_recurrence (n : ℕ) :
    J (n + 8) = 2 • J (n + 7) + 9 • J (n + 6) - 4 • J (n + 5) -
      31 • J (n + 4) - 30 • J (n + 3) - 9 • J (n + 2) := by
  ext i j
  have h := congrArg (fun M =>
    ((jetInsertion (columns j) (rows i) * M).trace).snd)
    (jet_power_recurrence (columns j) n)
  simpa only [J, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    mul_add, mul_sub, mul_smul_comm, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, snd_add, snd_sub, snd_smul] using h

/-- The six coefficient matrices of L, with common denominator 768. -/
def coefficientNumerators (k : Fin 6) : Matrix (Fin 9) (Fin 9) ℤ :=
  ![!![-124200, -119544, -4440, 118692, -4788, -57240, -26328, 38208, -55512;
       -46602, -45342, -3078, 52785, 3123, -19782, -9942, 13680, -22734;
       215298, 207270, 12942, -223506, -1728, 99522, 48654, -71712, 103986;
       -62478, -62154, -2706, 57591, -6963, -28098, -12738, 19200, -27594;
       61668, 62316, -36, -57618, 1674, 28764, 13980, -22176, 27900;
       -110007, -110709, -2961, 116757, 2574, -47871, -23505, 33984, -49815;
       109512, 110808, 6552, -116586, 3798, 49680, 24408, -36288, 52272;
       0, 0, 0, -4752, -9840, 0, 0, 0, 0;
       0, 0, 0, 4320, 1296, 0, 0, 0, 0],
    !![193140, 196188, 8940, -203400, -900, 87300, 41580, -65280, 94788;
       69825, 70467, 1335, -76410, -9765, 30645, 14295, -14400, 31077;
       -344070, -353682, -8010, 367740, 19710, -166590, -80010, 109440, -174942;
       102167, 103621, 2801, -107766, 5037, 43971, 21329, -33408, 47571;
       -103506, -101622, -6558, 101268, 5274, -46458, -21342, 31104, -50202;
       180819, 180153, 7317, -190782, -18351, 79407, 37173, -49536, 83583;
       -173922, -174630, -1806, 190836, 8298, -80586, -38094, 50688, -84330;
       0, 0, 0, -960, 8640, 0, 0, 0, 0;
       0, 0, 0, -5760, -2880, 0, 0, 0, 0],
    !![-106800, -97680, 1200, 100800, 18000, -48240, -21840, 23040, -48240;
       -35100, -30420, -900, 32400, 8100, -15660, -6660, 5760, -15660;
       185400, 164520, 1800, -172800, -37800, 83160, 36360, -34560, 83160;
       -51780, -45900, -540, 48240, 10620, -23220, -10140, 9600, -23220;
       50040, 46440, -1080, -47520, -7560, 22680, 10440, -11520, 22680;
       -87660, -78660, -180, 82080, 16740, -39420, -17460, 17280, -39420;
       80280, 68040, 3240, -73440, -20520, 35640, 14760, -11520, 35640;
       0, 0, 0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0, 0, 0],
    !![16800, 12000, 2400, -14400, -7200, 7200, 2400, 0, 7200;
       4200, 3000, 600, -3600, -1800, 1800, 600, 0, 1800;
       -25200, -18000, -3600, 21600, 10800, -10800, -3600, 0, -10800;
       7000, 5000, 1000, -6000, -3000, 3000, 1000, 0, 3000;
       -8400, -6000, -1200, 7200, 3600, -3600, -1200, 0, -3600;
       12600, 9000, 1800, -10800, -5400, 5400, 1800, 0, 5400;
       -8400, -6000, -1200, 7200, 3600, -3600, -1200, 0, -3600;
       0, 0, 0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0, 0, 0],
    !![-216, 2808, -3240, 1116, 180, 1944, 216, 1728, 216;
       -1782, 1566, -1530, 207, 1485, 582, -42, 144, 1230;
       5886, -4518, 5490, -2286, -2880, -1218, 498, -2016, -1074;
       270, -54, -1134, 9, -1485, 450, 450, 0, -54;
       540, -108, -2268, 18, 630, 1188, 612, -864, -252;
       -585, 117, 657, -1557, -270, 1023, -303, 576, 663;
       1080, -216, 2664, 1386, 810, -528, 168, -576, 1488;
       0, 0, 0, 144, -2448, 0, 0, 0, 0;
       0, 0, 0, 288, -1296, 0, 0, 0, 0],
    !![108, 324, -972, 216, 756, 540, 180, 0, -36;
       -9, -27, 81, -18, -63, -45, -15, 0, 3;
       -18, -54, 162, -36, -126, -90, -30, 0, 6;
       81, 243, -729, 162, 567, 405, 135, 0, -27;
       162, 486, -1458, 324, 1134, 810, 270, 0, -54;
       -63, -189, 567, -126, -441, -315, -105, 0, 21;
       -126, -378, 1134, -252, -882, -630, -210, 0, 42;
       0, 0, 0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0, 0, 0]] k

def coefficient (k : Fin 6) : Matrix (Fin 9) (Fin 9) ℚ :=
  fun i j => (coefficientNumerators k i j : ℚ) / 768

/-- The replay's bivariate matrix polynomial, evaluated over the rationals. -/
def L (m q : ℚ) : Matrix (Fin 9) (Fin 9) ℚ :=
  coefficient 0 + m • coefficient 1 + m ^ 2 • coefficient 2 + m ^ 3 • coefficient 3 +
    q • (coefficient 4 + m • coefficient 5)

def closedForm (m : ℕ) : Matrix (Fin 9) (Fin 9) ℚ :=
  ((-1 : ℚ) ^ m) • L (m : ℚ) ((-3 : ℚ) ^ m)

private theorem scalar_closedForm_recurrence (a b c d e f : ℚ) (n : ℕ) :
    let u := fun m : ℕ => (-1 : ℚ) ^ m *
      (a + (m : ℚ) * b + (m : ℚ) ^ 2 * c + (m : ℚ) ^ 3 * d +
        (-3 : ℚ) ^ m * (e + (m : ℚ) * f))
    u (n + 8) = 2 * u (n + 7) + 9 * u (n + 6) - 4 * u (n + 5) -
      31 * u (n + 4) - 30 * u (n + 3) - 9 * u (n + 2) := by
  simp only [pow_add, Nat.cast_add]
  norm_num
  ring

private theorem closedForm_recurrence (n : ℕ) :
    closedForm (n + 8) =
      2 • closedForm (n + 7) + 9 • closedForm (n + 6) - 4 • closedForm (n + 5) -
      31 • closedForm (n + 4) - 30 • closedForm (n + 3) - 9 • closedForm (n + 2) := by
  ext i j
  simpa only [closedForm, L, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    ← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_ofNat, smul_eq_mul] using
    scalar_closedForm_recurrence (coefficient 0 i j) (coefficient 1 i j)
      (coefficient 2 i j) (coefficient 3 i j) (coefficient 4 i j) (coefficient 5 i j) n

private abbrev Packed (R : Type*) := Vector (Vector R 4) 4

private def pack {R : Type*} (M : Transfer R) : Packed R :=
  Vector.ofFn fun i => Vector.ofFn fun j => M (toBits i) (toBits j)

private def unpack {R : Type*} (values : Packed R) : Transfer R :=
  fun i j => (values.get (toBits.symm i)).get (toBits.symm j)

@[simp] private theorem unpack_pack {R : Type*} (M : Transfer R) : unpack (pack M) = M := by
  apply Matrix.ext
  intro i j
  change (Vector.ofFn (fun u : Fin 4 => Vector.ofFn (fun v : Fin 4 => M (toBits u) (toBits v))))[
    (toBits.symm i).val][(toBits.symm j).val] = _
  simp [Vector.getElem_ofFn]

private def cachedJetPower (d : Direction) : ℕ → Packed (DualNumber ℚ)
  | 0 => pack 1
  | n + 1 => pack (unpack (cachedJetPower d n) * jetTransfer d)

@[simp] private theorem cachedJetPower_eq (d : Direction) (m : ℕ) :
    unpack (cachedJetPower d m) = jetTransfer d ^ m := by
  induction m with
  | zero => simp [cachedJetPower]
  | succ m ih => simp [cachedJetPower, ih, pow_succ]

private def seedCheck (k : Fin 6) : Bool :=
  (List.finRange 9).all fun j =>
    let power := cachedJetPower (columns j) (k.val + 2)
    (List.finRange 9).all fun i =>
      (((jetInsertion (columns j) (rows i) * unpack power).trace).snd ==
        closedForm (k.val + 2) i j)

/-- Six exact initial 9×9 matrices checked directly from the cores and coordinate directions. -/
theorem initial_values (k : Fin 6) : J (k.val + 2) = closedForm (k.val + 2) := by
  have h : ∀ k : Fin 6, seedCheck k = true := by
    intro k
    fin_cases k <;> decide +kernel
  apply Matrix.ext
  intro i j
  have hj := List.all_eq_true.mp (h k) j (by simp)
  have hi := List.all_eq_true.mp hj i (by simp)
  have heq := beq_iff_eq.mp hi
  rw [cachedJetPower_eq] at heq
  exact heq

theorem J_eq_closedForm (m : ℕ) (hm : 2 ≤ m) : J m = closedForm m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h : m < 8
    · simpa only [Nat.sub_add_cancel hm] using initial_values ⟨m - 2, by omega⟩
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + 8 := ⟨m - 8, by omega⟩
      rw [J_recurrence, closedForm_recurrence, ih (n + 7) (by omega) (by omega),
        ih (n + 6) (by omega) (by omega), ih (n + 5) (by omega) (by omega),
        ih (n + 4) (by omega) (by omega), ih (n + 3) (by omega) (by omega),
        ih (n + 2) (by omega) (by omega)]

theorem literalJacobian_eq_closedForm (m : ℕ) (hm : 2 ≤ m) :
    literalJacobian m = ((-1 : ℚ) ^ m) • L (m : ℚ) ((-3 : ℚ) ^ m) :=
  (literalJacobian_eq_J m).trans (J_eq_closedForm m hm)

private abbrev SquareData (n : ℕ) := Vector (Vector ℚ n) n

private def store {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : SquareData n :=
  Vector.ofFn fun i => Vector.ofFn fun j => M i j

private def read {n : ℕ} (A : SquareData n) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (A.get i).get j

@[simp] private theorem read_store {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    read (store M) = M := by
  apply Matrix.ext
  intro i j
  change (Vector.ofFn (fun u : Fin n => Vector.ofFn (M u)))[i.val][j.val] = _
  simp

private def schur {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j => M i.succ j.succ - (M i.succ 0 / M 0 0) * M 0 j.succ

private theorem det_schur {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (h : M 0 0 ≠ 0) : M.det = M 0 0 * (schur M).det := by
  let V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
    fun i j => if j = 0 ∧ i ≠ 0 then M i 0 / M 0 0 else 0
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := 1 - V
  have hE : E.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      change (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) i i -
        (if i = 0 ∧ i ≠ 0 then M i 0 / M 0 0 else 0) = 1
      simp
    · intro i j hij
      change i < j at hij
      have hj : j ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le i) hij)
      change (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) i j -
        (if j = 0 ∧ i ≠ 0 then M i 0 / M 0 0 else 0) = 0
      simp [ne_of_lt hij, hj]
  have hmul (i j : Fin (n + 1)) :
      (E * M) i j = M i j - if i = 0 then 0 else (M i 0 / M 0 0) * M 0 j := by
    rw [show E * M = M - V * M by simp only [E, sub_mul, Matrix.one_mul]]
    rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ]
    by_cases hi : i = 0 <;> simp [V, hi]
  have hcol (i : Fin n) : (E * M) i.succ 0 = 0 := by
    rw [hmul]
    simp [h]
  have hsub : (E * M).submatrix Fin.succ Fin.succ = schur M := by
    apply Matrix.ext
    intro i j
    simp [hmul, schur]
  calc
    M.det = (E * M).det := by rw [Matrix.det_mul, hE, one_mul]
    _ = M 0 0 * (schur M).det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      simp [hmul, hsub]

private def pivotDet : (n : ℕ) → SquareData n → Option ℚ
  | 0, _ => some 1
  | n + 1, A =>
    let M := read A
    if M 0 0 = 0 then none else
      (pivotDet n (store (schur M))).map fun d => M 0 0 * d

private theorem pivotDet_sound (n : ℕ) (A : SquareData n) (d : ℚ)
    (h : pivotDet n A = some d) : (read A).det = d := by
  induction n generalizing d with
  | zero => simpa [pivotDet, Matrix.det_fin_zero] using h
  | succ n ih =>
    by_cases hp : read A 0 0 = 0
    · simp [pivotDet, hp] at h
    · rw [det_schur (read A) hp]
      cases hd : pivotDet n (store (schur (read A))) with
      | none => simp [pivotDet, hp, hd] at h
      | some value =>
        have hv := ih _ value hd
        rw [read_store] at hv
        rw [hv]
        simpa [pivotDet, hp, hd] using h

def firstDeterminants (k : Fin 3) : ℚ :=
  ![-172426958296135330636800, 16417370257298913435094794240,
    146384793435805972584442385837400] k

/-- Exact determinants of the same literal minor at suffix lengths 5, 6 and 7. -/
theorem literalJacobian_first_determinants (k : Fin 3) :
    (literalJacobian (k.val + 5)).det = firstDeterminants k := by
  rw [literalJacobian_eq_J, J_eq_closedForm _ (by omega),
    ← read_store (closedForm (k.val + 5))]
  apply pivotDet_sound
  fin_cases k <;> decide +kernel

theorem literalJacobian_first_nonzero (k : Fin 3) :
    (literalJacobian (k.val + 5)).det ≠ 0 := by
  rw [literalJacobian_first_determinants]
  exact (by decide +kernel : ∀ k : Fin 3, firstDeterminants k ≠ 0) k

/-- The zero of B² at the witness still has both indicated transverse derivatives. -/
theorem B_squared_jet :
    (cores 1)^2 = 0 ∧
    ((jetCore (columns 3) 1)^2).map (fun z => z.snd) = cores 1 ∧
    ((jetCore (columns 4) 1)^2).map (fun z => z.snd) = 1 := by
  refine ⟨Matrix.ext ?_, Matrix.ext ?_, Matrix.ext ?_⟩
  · intro i j
    exact (by decide +kernel : ∀ ij : Bits, ((cores 1)^2) ij.1 ij.2 = 0) (i, j)
  · intro i j
    exact (by decide +kernel : ∀ ij : Bits,
      (((jetCore (columns 3) 1)^2) ij.1 ij.2).snd = cores 1 ij.1 ij.2) (i, j)
  · intro i j
    exact (by decide +kernel : ∀ ij : Bits,
      (((jetCore (columns 4) 1)^2) ij.1 ij.2).snd = (1 : Core ℚ) ij.1 ij.2) (i, j)

end PeriodicMPSCommonSpectralJets
