/- GID: D5/S3/Quantum/GeneralizedFidelity
   generality: G
   mirror-B: D5/B/S3/Quantum/GeneralizedFidelity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/GeneralizedFidelity.claim; result=D5/S3/Quantum/GeneralizedFidelity.result; claim=D5/S3/Quantum/GeneralizedFidelity.claim
   digest: A bit-flip channel violates generalized-fidelity data processing for qubits. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.PointerBasis

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.GeneralizedFidelity

open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius

/-- Generalized fidelity with the actual positive matrix square roots. -/
def fidelity {n : Type*} [Fintype n] [DecidableEq n]
    (R P Q : Matrix n n ℂ) : ℂ :=
  Matrix.trace (CFC.sqrt (CFC.sqrt R * P * CFC.sqrt R) * R⁻¹ *
    CFC.sqrt (CFC.sqrt R * Q * CFC.sqrt R))

/-- The real squared generalized Bures--Wasserstein quantity. -/
def bures {n : Type*} [Fintype n] [DecidableEq n]
    (R P Q : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (P + Q)).re - 2 * (fidelity R P Q).re

/-- The raw matrix action of the canonical completely positive channel. -/
def rawMatrix (channel : QuantumChannel (Fin 2) (Fin 2)) (M : QubitMatrix) :
    QubitMatrix :=
  CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix M))

/-- Unrestricted qubit data processing, permitting singular input states. -/
def claim : Prop :=
  ∀ (P Q R : QubitMatrix) (channel : QuantumChannel (Fin 2) (Fin 2)),
    P.PosSemidef → Q.PosSemidef → Matrix.trace P = 1 → Matrix.trace Q = 1 →
    R.PosDef → Matrix.trace R = 1 → (rawMatrix channel R).PosDef →
    bures (rawMatrix channel R) (rawMatrix channel P) (rawMatrix channel Q) ≤ bures R P Q

-- The six matrix-root certificates and the interval estimates share one proof.
set_option maxHeartbeats 800000 in
/-- Generalized Bures--Wasserstein data processing fails already for qubits. -/
theorem result : ¬ claim := by
  classical
  let m (a b c : ℝ) : QubitMatrix := !![(a : ℂ), (b : ℂ); (b : ℂ), (c : ℂ)]
  let diag (u v : ℝ) : QubitMatrix := Matrix.diagonal ![(u : ℂ), (v : ℂ)]
  let P : QubitMatrix := m (1/10) (3/10) (9/10)
  let Q : QubitMatrix := m (4/5) (2/5) (1/5)
  let Phi (M : QubitMatrix) : QubitMatrix := (31/32 : ℂ) • M + (1/32 : ℂ) • (qubitX * M * qubitX)
  obtain ⟨a0, ha0, h0⟩ : ∃ a : ℝ, a = Real.sqrt (31/32) ∧ a^2 = 31/32 :=
    ⟨_, rfl, Real.sq_sqrt (by norm_num)⟩
  obtain ⟨a1, ha1, h1⟩ : ∃ a : ℝ, a = Real.sqrt (1/32) ∧ a^2 = 1/32 :=
    ⟨_, rfl, Real.sq_sqrt (by norm_num)⟩
  let K : Fin 2 → QubitMatrix := ![(a0 : ℂ) • (1 : QubitMatrix), (a1 : ℂ) • qubitX]
  have h0C : (a0 : ℂ)^2 = (31/32 : ℂ) := by
    rw [← Complex.ofReal_pow, h0]
    norm_num
  have h1C : (a1 : ℂ)^2 = (1/32 : ℂ) := by
    rw [← Complex.ofReal_pow, h1]
    norm_num
  have hXstar : qubitX.conjTranspose = qubitX := by
    simpa only [Matrix.star_eq_conjTranspose] using qubit_weyl_star.2.1
  have hXpow : qubitX^2 = 1 := qubit_weyl_star.2.2.2.1
  have hK : (∑ r, (K r).conjTranspose * K r) = 1 := by
    rw [Fin.sum_univ_two]
    dsimp [K]
    simp [Matrix.conjTranspose_smul, hXstar, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, smul_pow, ← pow_two, hXpow, h0, h1, h0C, h1C,
      RCLike.star_def, ← add_smul]
    norm_num
  obtain ⟨channel, hchannel⟩ := finite_kraus_quantum_channel K hK
  have hPhi : ∀ M : QubitMatrix, rawMatrix channel M = Phi M := by
    intro M
    rw [rawMatrix, hchannel]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [K, Phi, qubitX, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two, Matrix.conjTranspose_apply, RCLike.star_def] <;>
      ring_nf <;> simp [h0C, h1C] <;> ring
  have hFourier : ∀ M : QubitMatrix, Phi M =
      D5.S3.Quantum.PointerBasis.fourierPhaseDamping
        (⟨15/16, by norm_num⟩ : D5.S3.Quantum.QubitWitnesses.DampingCoefficient) M := by
    intro M
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Phi, qubitX, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        D5.S3.Quantum.PointerBasis.fourierPhaseDamping,
        D5.S3.Quantum.PointerBasis.phaseDampingInBasis,
        D5.S3.Quantum.PointerBasis.hadamardCoordinateEquiv,
        D5.S3.Quantum.PointerBasis.hadamardCoordinates,
        D5.S3.Quantum.QubitWitnesses.phaseDamping] <;> ring
  have hP : P.PosSemidef := by
    have h := (Matrix.posSemidef_conjTranspose_mul_self
      (!![(1 : ℂ), 3; 0, 0] : QubitMatrix)).smul (show (0 : ℝ) ≤ 1/10 by norm_num)
    convert h using 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [P, m, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat, RCLike.star_def]
  have hQ : Q.PosSemidef := by
    have h := (Matrix.posSemidef_conjTranspose_mul_self
      (!![(2 : ℂ), 1; 0, 0] : QubitMatrix)).smul (show (0 : ℝ) ≤ 1/5 by norm_num)
    convert h using 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Q, m, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat, RCLike.star_def]
  have htrP : Matrix.trace P = 1 := by norm_num [P, m, Matrix.trace, Fin.sum_univ_two]
  have htrQ : Matrix.trace Q = 1 := by norm_num [Q, m, Matrix.trace, Fin.sum_univ_two]
  have horder : ∀ M : QubitMatrix, M.PosSemidef → (rawMatrix channel M).PosSemidef := by
    intro M hM
    have hCS : 0 ≤ CStarMatrix.ofMatrix M :=
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hM.nonneg
    apply Matrix.nonneg_iff_posSemidef.mp
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
      (map_nonneg channel.toCompletelyPositiveMap hCS)
  have htrace : ∀ M : QubitMatrix, Matrix.trace (rawMatrix channel M) = Matrix.trace M := by
    intro M
    exact channel.trace_preserving (CStarMatrix.ofMatrix M)
  have hdiagPD : ∀ u v : ℝ, 0 < u → 0 < v → (diag u v).PosDef := by
    intro u v hu hv
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · change (0 : ℂ) < (u : ℂ)
      exact_mod_cast hu
    · change (0 : ℂ) < (v : ℂ)
      exact_mod_cast hv
  have hdiagRoot : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
      CFC.sqrt (diag u v) = diag (Real.sqrt u) (Real.sqrt v) := by
    intro u v hu hv
    apply CFC.sqrt_unique
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [diag, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.ofReal_mul,
          Real.mul_self_sqrt hu, Real.mul_self_sqrt hv]
    · exact (Matrix.PosSemidef.diagonal (by
        intro i
        fin_cases i <;> simp [Real.sqrt_nonneg])).nonneg
  have hroot : ∀ a b c d q : ℝ, (m a b c).PosSemidef → 0 ≤ d →
      d^2 = a*c-b^2 → q = a+c+2*d → 0 < q →
      CFC.sqrt (m a b c) = m ((a+d)/Real.sqrt q) (b/Real.sqrt q)
        ((c+d)/Real.sqrt q) := by
    intro a b c d q hT hd hd2 hq hqpos
    have hspos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqpos
    have hs2 := Real.sq_sqrt hqpos.le
    apply CFC.sqrt_unique
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [m, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
          ← Complex.ofReal_add, ← Complex.ofReal_mul] <;>
        norm_cast <;> field_simp [ne_of_gt hspos] <;>
        first | linear_combination hd2 - a * hs2 - a * hq
              | linear_combination -b * hs2 - b * hq
              | linear_combination hd2 - c * hs2 - c * hq
    · have hpos := (hT.add ((Matrix.PosSemidef.one : (1 : QubitMatrix).PosSemidef).smul hd)).smul
        (show 0 ≤ (Real.sqrt q)⁻¹ from inv_nonneg.mpr hspos.le)
      have hcand : m ((a+d)/Real.sqrt q) (b/Real.sqrt q) ((c+d)/Real.sqrt q) =
          (Real.sqrt q)⁻¹ • (m a b c + d • (1 : QubitMatrix)) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [m, smul_eq_mul, div_eq_mul_inv, ← Complex.ofReal_add,
            ← Complex.ofReal_mul] <;> norm_cast <;> ring
      rw [hcand]
      exact hpos.nonneg
  have heval : ∀ u v a b c d f g D E p q : ℝ,
      0 < u → 0 < v → (m a b c).PosSemidef → (m d f g).PosSemidef →
      0 ≤ D → 0 ≤ E → D^2 = u*v*(a*c-b^2) → E^2 = u*v*(d*g-f^2) →
      p = u*a+v*c+2*D → q = u*d+v*g+2*E → 0 < p → 0 < q →
      fidelity (diag u v) (m a b c) (m d f g) =
        ((u*a*d+v*c*g+(u+v)*b*f+D*(d+g)+E*(a+c)+D*E*(u⁻¹+v⁻¹)) /
          (Real.sqrt p * Real.sqrt q) : ℝ) := by
    intro u v a b c d f g D E p q hu hv hP0 hQ0 hD hE hD2 hE2 hp hq hp0 hq0
    have hsu := Real.sq_sqrt hu.le
    have hsv := Real.sq_sqrt hv.le
    have hsand : ∀ a b c : ℝ, diag (Real.sqrt u) (Real.sqrt v) * m a b c *
        diag (Real.sqrt u) (Real.sqrt v) =
        m (u*a) (Real.sqrt u*Real.sqrt v*b) (v*c) := by
      intro a b c
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [diag, m, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
          ← Complex.ofReal_add, ← Complex.ofReal_mul] <;>
        norm_cast <;> ring_nf <;> simp [hsu, hsv] <;> ring
    have hself : (diag (Real.sqrt u) (Real.sqrt v)).conjTranspose =
        diag (Real.sqrt u) (Real.sqrt v) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diag, Matrix.conjTranspose_apply]
    have hsandpos : ∀ a b c : ℝ, (m a b c).PosSemidef →
        (m (u*a) (Real.sqrt u*Real.sqrt v*b) (v*c)).PosSemidef := by
      intro a b c hh
      rw [← hsand]
      simpa only [hself] using hh.mul_mul_conjTranspose_same
        (diag (Real.sqrt u) (Real.sqrt v))
    have hDp : D^2 = (u*a)*(v*c)-(Real.sqrt u*Real.sqrt v*b)^2 := by
      simp only [mul_pow, hsu, hsv]
      linear_combination hD2
    have hEq : E^2 = (u*d)*(v*g)-(Real.sqrt u*Real.sqrt v*f)^2 := by
      simp only [mul_pow, hsu, hsv]
      linear_combination hE2
    have hrootP := hroot (u*a) (Real.sqrt u*Real.sqrt v*b) (v*c) D p
      (hsandpos a b c hP0) hD hDp hp hp0
    have hrootQ := hroot (u*d) (Real.sqrt u*Real.sqrt v*f) (v*g) E q
      (hsandpos d f g hQ0) hE hEq hq hq0
    have hinv : (diag u v)⁻¹ = diag u⁻¹ v⁻¹ := by
      have huC : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu
      have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hv
      apply Matrix.inv_eq_left_inv
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [diag, Matrix.mul_apply, Fin.sum_univ_two, Complex.ofReal_inv, huC, hvC]
    rw [fidelity, hdiagRoot u v hu.le hv.le, hsand, hsand, hrootP, hrootQ, hinv]
    simp [diag, m, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, ← Complex.ofReal_add, ← Complex.ofReal_mul]
    norm_cast
    field_simp [ne_of_gt hu, ne_of_gt hv,
      ne_of_gt (Real.sqrt_pos.mpr hp0), ne_of_gt (Real.sqrt_pos.mpr hq0)]
    ring_nf
    simp only [hsu, hsv]
    ring
  have hPout : rawMatrix channel P = m (1/8) (3/10) (7/8) := by
    rw [hPhi]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Phi, P, m, qubitX, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have hQout : rawMatrix channel Q = m (25/32) (2/5) (7/32) := by
    rw [hPhi]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Phi, Q, m, qubitX, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have hfamily : ∀ e : ℝ, 0 < e → e ≤ 1/1000 →
      (diag (1-e) e).PosDef ∧ Matrix.trace (diag (1-e) e) = 1 ∧
      (rawMatrix channel (diag (1-e) e)).PosDef ∧
      bures (diag (1-e) e) P Q < 3/5 ∧
      3/5 < bures (rawMatrix channel (diag (1-e) e)) (rawMatrix channel P)
        (rawMatrix channel Q) := by
    intro e hepos hebound
    have he1 : e < 1 := lt_of_le_of_lt hebound (by norm_num)
    have hue : 0 < 1-e := sub_pos.mpr he1
    let u : ℝ := (31-30*e)/32
    let v : ℝ := (1+30*e)/32
    have hu : 0 < u := by dsimp [u]; linarith only [hebound]
    have hv : 0 < v := by dsimp [v]; linarith only [hepos]
    have huv : u+v = 1 := by dsimp [u, v]; ring
    have hRout : rawMatrix channel (diag (1-e) e) = diag u v := by
      rw [hPhi]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Phi, diag, u, v, qubitX, Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Fin.sum_univ_two] <;> push_cast <;> ring
    have hRPD := hdiagPD (1-e) e hue hepos
    have hRtrace : Matrix.trace (diag (1-e) e) = 1 := by
      simp [diag, Matrix.trace, Fin.sum_univ_two]
    have hRoutPD : (rawMatrix channel (diag (1-e) e)).PosDef := by
      rw [hRout]
      exact hdiagPD u v hu hv
    let p : ℝ := (1+8*e)/10
    let q : ℝ := (4-3*e)/5
    have hp : 0 < p := by dsimp [p]; linarith only [hepos]
    have hq : 0 < q := by dsimp [q]; linarith only [hebound]
    have hin0 := heval (1-e) e (1/10) (3/10) (9/10) (4/5) (2/5) (1/5) 0 0 p q
      hue hepos hP hQ (by norm_num) (by norm_num) (by ring) (by ring)
      (by dsimp [p]; ring) (by dsimp [q]; ring) hp hq
    have hinF : fidelity (diag (1-e) e) P Q =
        ((2+e)/(10*(Real.sqrt p*Real.sqrt q)) : ℝ) := by
      rw [hin0]
      congr 1
      field_simp
      ring
    have hdenpos : 0 < 10*(Real.sqrt p*Real.sqrt q) := by
      exact mul_pos (by norm_num) (mul_pos (Real.sqrt_pos.mpr hp) (Real.sqrt_pos.mpr hq))
    have hden2 : (10*(Real.sqrt p*Real.sqrt q))^2 = 2*(4+29*e-24*e^2) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hp.le, Real.sq_sqrt hq.le]
      dsimp [p, q]
      ring
    have hrad : 0 < 2*(4+29*e-24*e^2) := by
      rw [← hden2]
      exact sq_pos_of_pos hdenpos
    have hden : Real.sqrt (2*(4+29*e-24*e^2)) = 10*(Real.sqrt p*Real.sqrt q) :=
      (Real.sqrt_eq_iff_eq_sq hrad.le hdenpos.le).mpr hden2.symm
    rw [← hden] at hinF
    have hFin : (fidelity (diag (1-e) e) P Q).re =
        (2+e)/Real.sqrt (2*(4+29*e-24*e^2)) := by rw [hinF, Complex.ofReal_re]
    have hFinlt : (7/10 : ℝ) < (fidelity (diag (1-e) e) P Q).re := by
      rw [hFin]
      apply (lt_div_iff₀ (Real.sqrt_pos.mpr hrad)).mpr
      have hs : ((7/10)*Real.sqrt (2*(4+29*e-24*e^2)))^2 < (2+e)^2 := by
        rw [mul_pow, Real.sq_sqrt hrad.le]
        nlinarith only [hebound, sq_nonneg e]
      exact (sq_lt_sq₀ (by positivity) (by linarith only [hepos])).mp hs
    let S : ℝ := Real.sqrt (961+27900*e-27900*e^2)
    have hz : 961 ≤ 961+27900*e-27900*e^2 := by
      nlinarith only [mul_nonneg hepos.le hue.le]
    have hz0 : 0 ≤ 961+27900*e-27900*e^2 := by linarith only [hz]
    have hS0 : 0 ≤ S := Real.sqrt_nonneg _
    have hS2 : S^2 = 961+27900*e-27900*e^2 := Real.sq_sqrt hz0
    have hS31 : 31 ≤ S := by
      apply (sq_le_sq₀ (by norm_num) hS0).mp
      rw [hS2]
      nlinarith only [hz]
    have hS32 : S < 32 := by
      apply (sq_lt_sq₀ hS0 (by norm_num)).mp
      rw [hS2]
      nlinarith only [hebound, sq_nonneg e]
    have hSlinear : S ≤ 31+450*e := by
      apply (sq_le_sq₀ hS0 (by linarith only [hepos])).mp
      rw [hS2]
      nlinarith only [sq_nonneg e]
    let A : ℝ := (95+450*e+S)/640
    let B : ℝ := (1955-1350*e+3*S)/2560
    have hAlo : 63/320 ≤ A := by dsimp [A]; linarith only [hepos, hS31]
    have hAhi : A ≤ 1/4 := by dsimp [A]; linarith only [hebound, hSlinear]
    have hBlo : 3/4 ≤ B := by dsimp [B]; linarith only [hebound, hS31]
    have hBhi : B ≤ 4/5 := by dsimp [B]; linarith only [hSlinear]
    have hApos : 0 < A := by linarith only [hAlo]
    have hBpos : 0 < B := by linarith only [hBlo]
    have hpout : (m (1/8) (3/10) (7/8)).PosSemidef := by
      rw [← hPout]
      exact horder P hP
    have hqout : (m (25/32) (2/5) (7/32)).PosSemidef := by
      rw [← hQout]
      exact horder Q hQ
    have hout0 := heval u v (1/8) (3/10) (7/8) (25/32) (2/5) (7/32)
      (S/1280) (3*S/5120) A B hu hv hpout hqout (by positivity) (by positivity)
      (by dsimp [u, v]; linear_combination (1/1638400 : ℝ) * hS2)
      (by dsimp [u, v]; linear_combination (9/26214400 : ℝ) * hS2)
      (by dsimp [A, u, v]; ring) (by dsimp [B, u, v]; ring) hApos hBpos
    have hinvsum : u⁻¹+v⁻¹ = (u+v)/(u*v) := by
      field_simp [ne_of_gt hu, ne_of_gt hv]
      ring
    have hcross : (S/1280)*(3*S/5120)*(u⁻¹+v⁻¹) = 93/6400 := by
      rw [hinvsum, huv]
      field_simp [ne_of_gt hu, ne_of_gt hv]
      dsimp [u, v]
      nlinarith only [hS2]
    have houtN : u*(1/8)*(25/32)+v*(7/8)*(7/32)+(u+v)*(3/10)*(2/5)+
        (S/1280)*(25/32+7/32)+(3*S/5120)*(1/8+7/8)+
        (S/1280)*(3*S/5120)*(u⁻¹+v⁻¹) = (A+B-707/1600)/2 := by
      rw [hcross]
      dsimp [A, B, u, v]
      ring
    have hABpos : 0 < A*B := mul_pos hApos hBpos
    have hABsqrt : 0 < Real.sqrt (A*B) := Real.sqrt_pos.mpr hABpos
    have hFout : (fidelity (diag u v) (m (1/8) (3/10) (7/8))
        (m (25/32) (2/5) (7/32))).re = (A+B-707/1600)/(2*Real.sqrt (A*B)) := by
      rw [hout0, Complex.ofReal_re, houtN, ← Real.sqrt_mul hApos.le]
      field_simp [ne_of_gt hABsqrt]
    let H (x y : ℝ) := (x+y-707/1600)^2-49*x*y/25
    have hHA : H A B-H (63/320) B =
        (A-63/320)*(A+63/320+B/25-2*(707/1600)) := by dsimp [H]; ring
    have hHB : H (63/320) B-H (63/320) (4/5) =
        (B-4/5)*(B+4/5+(63/320)/25-2*(707/1600)) := by dsimp [H]; ring
    have hfactorA : A+63/320+B/25-2*(707/1600) ≤ -3239/8000 := by
      linarith only [hAhi, hBhi]
    have hfactorB : 5393/8000 ≤ B+4/5+(63/320)/25-2*(707/1600) := by
      linarith only [hBlo]
    have hprodA : (A-63/320)*(A+63/320+B/25-2*(707/1600)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hAlo) (by linarith only [hfactorA])
    have hprodB : (B-4/5)*(B+4/5+(63/320)/25-2*(707/1600)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hBhi) (by linarith only [hfactorB])
    have hcorner : H (63/320) (4/5) = -27/40000 := by norm_num [H]
    have hH : H A B ≤ -27/40000 := by linarith only [hHA, hHB, hprodA, hprodB, hcorner]
    have hnpos : 0 < A+B-707/1600 := by linarith only [hAlo, hBlo]
    have hFsq : (A+B-707/1600)^2 < ((7/5)*Real.sqrt (A*B))^2 := by
      rw [mul_pow, Real.sq_sqrt hABpos.le]
      dsimp [H] at hH
      nlinarith only [hH]
    have hFnum : A+B-707/1600 < (7/5)*Real.sqrt (A*B) :=
      (sq_lt_sq₀ hnpos.le (by positivity)).mp hFsq
    have hFoutlt : (fidelity (diag u v) (m (1/8) (3/10) (7/8))
        (m (25/32) (2/5) (7/32))).re < 7/10 := by
      rw [hFout]
      apply (div_lt_iff₀ (mul_pos (by norm_num) hABsqrt)).mpr
      linarith only [hFnum]
    refine ⟨hRPD, hRtrace, hRoutPD, ?_, ?_⟩
    · rw [bures, Matrix.trace_add, htrP, htrQ]
      simp only [Complex.add_re, Complex.one_re]
      linarith only [hFinlt]
    · rw [bures, Matrix.trace_add, htrace, htrace, htrP, htrQ]
      simp only [Complex.add_re, Complex.one_re]
      rw [hRout, hPout, hQout]
      linarith only [hFoutlt]
  intro hclaim
  obtain ⟨hPD, htr, houtPD, hin, hout⟩ := hfamily (1/1000) (by norm_num) (by norm_num)
  have hdpi := hclaim P Q (diag (1-1/1000) (1/1000)) channel
    hP hQ htrP htrQ hPD htr houtPD
  linarith only [hdpi, hin, hout]

#print axioms result

end D5.S3.Quantum.GeneralizedFidelity
