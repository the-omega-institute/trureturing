/- GID: D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.claim; result=D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.result; claim=D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.claim
   digest: Four unitary encodings beat every unassisted strategy below half-unit energy. -/

import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation
import D5.S3.Quantum.FiniteDimensional

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Entanglement.EnergyRestrictedUnitaryEncodingRefutation

open _root_.Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker InnerProductSpace

/-- A POVM on any finite carrier; on `Fin d` this is the existing POVM predicate. -/
def IsPOVM {n B : Type} [Fintype n] [DecidableEq n] [Fintype B]
    (M : B → Matrix n n ℂ) : Prop :=
  (∀ b, (M b).PosSemidef) ∧ ∑ b, M b = 1

/-- A shared unit vector, local unitary encodings, and joint POVMs. -/
def UnitaryStrategy {X Y B : Type} [Fintype B] {dA dB : ℕ}
    (Ψ : Fin dA × Fin dB → ℂ) (_U : X → unitaryGroup (Fin dA) ℂ)
    (M : Y → B → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) : Prop :=
  (∑ i, Complex.normSq (Ψ i)) = 1 ∧ ∀ y, IsPOVM (M y)

/-- Alice acts on her factor and transmits it to Bob. -/
def encoded {X : Type} {dA dB : ℕ} (Ψ : Fin dA × Fin dB → ℂ)
    (U : X → unitaryGroup (Fin dA) ℂ) (x : X) : Fin dA × Fin dB → ℂ :=
  ((U x : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) *ᵥ Ψ

/-- The Born probability of an outcome of the joint measurement. -/
def unitaryProb {X Y B : Type} {dA dB : ℕ} (Ψ : Fin dA × Fin dB → ℂ)
    (U : X → unitaryGroup (Fin dA) ℂ)
    (M : Y → B → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (b : B) (x : X) (y : Y) : ℝ :=
  (star (encoded Ψ U x) ⬝ᵥ (M y b *ᵥ encoded Ψ U x)).re

/-- The vacuum population of Alice's reduced message. -/
def unitaryVacuum {X : Type} {dA dB : ℕ} [NeZero dA]
    (Ψ : Fin dA × Fin dB → ℂ) (U : X → unitaryGroup (Fin dA) ℂ) (x : X) : ℝ :=
  ∑ j, ‖encoded Ψ U x (0, j)‖ ^ 2

/-- Density messages represented by ensembles on any complex Hilbert space, with arbitrary
    discrete shared randomness and bounded positive-operator-valued measurements. -/
def QCStrategy {X Y B H L K : Type} [Fintype B] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (vac : H) (q : L → ℝ)
    (p : L → X → K → ℝ) (ψ : L → X → K → H)
    (N : L → Y → B → (H →L[ℂ] H)) : Prop :=
  ‖vac‖ = 1 ∧ (∀ l, 0 ≤ q l) ∧ HasSum q 1 ∧
    (∀ l x k, 0 ≤ p l x k) ∧ (∀ l x, HasSum (p l x) 1) ∧
    (∀ l x k, ‖ψ l x k‖ = 1) ∧
    ∀ l y, (∀ b, 0 ≤ N l y b) ∧ ∑ b, N l y b = 1

/-- Shared randomness and each message ensemble average the Born probabilities. -/
def qcProb {X Y B H L K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (q : L → ℝ) (p : L → X → K → ℝ) (ψ : L → X → K → H)
    (N : L → Y → B → (H →L[ℂ] H)) (b : B) (x : X) (y : Y) : ℝ :=
  ∑' l, q l * ∑' k, p l x k * (⟪ψ l x k, N l y b (ψ l x k)⟫_ℂ).re

/-- The energy constraint averages vacuum populations over both distributions. -/
def qcVacuum {X H L K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (vac : H) (q : L → ℝ) (p : L → X → K → ℝ) (ψ : L → X → K → H) (x : X) : ℝ :=
  ∑' l, q l * ∑' k, p l x k * ‖⟪vac, ψ l x k⟫_ℂ‖ ^ 2

/-- An arbitrary finite linear communication task. -/
def taskValue {X Y B : Type} [Fintype X] [Fintype Y] [Fintype B]
    (c p : B → X → Y → ℝ) : ℝ := ∑ b, ∑ x, ∑ y, c b x y * p b x y

/-- Unitary entanglement assistance would be resourceless for every finite task. -/
def claim : Prop :=
  ∀ (X Y B : Type) [Fintype X] [Fintype Y] [Fintype B]
    (c : B → X → Y → ℝ) (ω : ℝ), 0 ≤ ω → ω < 1 / 2 →
    ∀ (dA dB : ℕ) [NeZero dA] (Ψ : Fin dA × Fin dB → ℂ)
      (U : X → unitaryGroup (Fin dA) ℂ)
      (M : Y → B → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
      UnitaryStrategy Ψ U M → (∀ x, 1 - ω ≤ unitaryVacuum Ψ U x) →
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H) (vac : H) (L K : Type) (q : L → ℝ)
        (p : L → X → K → ℝ) (ψ : L → X → K → H)
        (N : L → Y → B → (H →L[ℂ] H)),
        QCStrategy vac q p ψ N ∧ (∀ x, 1 - ω ≤ qcVacuum vac q p ψ x) ∧
          taskValue c (unitaryProb Ψ U M) ≤ taskValue c (qcProb q p ψ N)

private theorem involution_bound (A N : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (hAA : A * A = 1) (ht : trace A = 0)
    (hN : N.PosSemidef) (hNc : (1 - N).PosSemidef) :
    (trace (N * A)).re ≤ 1 := by
  let P := (1 / 2 : ℝ) • (1 + A)
  let Q := (1 / 2 : ℝ) • (1 - A)
  have hp : P * P = P := by
    dsimp [P]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hAA]
    module
  have hq : Q * Q = Q := by
    dsimp [Q]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hAA]
    module
  have hph : P.IsHermitian := (isHermitian_one.add hA).smul (by simp [IsSelfAdjoint])
  have hqh : Q.IsHermitian := (isHermitian_one.sub hA).smul (by simp [IsSelfAdjoint])
  have hpp : P.PosSemidef := by
    simpa only [hph.eq, hp] using posSemidef_conjTranspose_mul_self P
  have hqp : Q.PosSemidef := by
    simpa only [hqh.eq, hq] using posSemidef_conjTranspose_mul_self Q
  have hnq := (Complex.nonneg_iff.mp (hN.trace_mul_nonneg hqp)).1
  have hnp := (Complex.nonneg_iff.mp (hNc.trace_mul_nonneg hpp)).1
  have hpt : trace P = 1 := by simp [P, Matrix.trace_smul, Matrix.trace_add, ht]
  have ha : A = P - Q := by dsimp [P, Q]; module
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, hpt] at hnp
  rw [ha, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  simp only [Complex.sub_re, Complex.one_re] at hnp
  linarith

private theorem two_level_involution (s : ℝ) (c : ℂ) (hs : s ^ 2 + Complex.normSq c = 1) :
    let A : Matrix (Fin 2) (Fin 2) ℂ := !![-(s : ℂ), c; star c, s]
    A.IsHermitian ∧ A * A = 1 ∧ trace A = 0 := by
  dsimp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im,
        Complex.normSq_apply] at hs ⊢ <;> nlinarith [hs]
  · simp [Matrix.trace, Fin.sum_univ_two]

private theorem two_level_bound (N : Matrix (Fin 2) (Fin 2) ℂ)
    (hN : N.PosSemidef) (hNc : (1 - N).PosSemidef)
    (s : ℝ) (c : ℂ) (hs0 : 0 ≤ s) (hs : s ^ 2 + Complex.normSq c = 1) :
    (star (![c, (s : ℂ)] : Fin 2 → ℂ) ⬝ᵥ (N *ᵥ ![c, (s : ℂ)])).re - (N 0 0).re ≤ s := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![-(s : ℂ), c; star c, s]
  obtain ⟨hA, hAA, ht⟩ := two_level_involution s c hs
  have hb := involution_bound A N hA hAA ht hN hNc
  have heq : (star (![c, (s : ℂ)] : Fin 2 → ℂ) ⬝ᵥ (N *ᵥ ![c, (s : ℂ)])).re - (N 0 0).re =
      s * (trace (N * A)).re := by
    simp [A, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im, Complex.normSq_apply] at hs ⊢
    linear_combination hs * (N 0 0).re
  rw [heq]
  nlinarith

private def rotation : unitaryGroup (Fin 2) ℂ :=
  ⟨!![(4 / 5 : ℂ), -3 / 5; 3 / 5, 4 / 5], by
    rw [mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, map_ofNat]⟩

private def phase : unitaryGroup (Fin 2) ℂ :=
  ⟨D5.S3.Quantum.FiniteDimensional.qubitZ, by
    rw [mem_unitaryGroup_iff, D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.2.1,
      ← pow_two]
    exact D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.2.2.2⟩

private def protocolU (x : Fin 2 × Fin 2) : unitaryGroup (Fin 2) ℂ :=
  phase ^ x.1.val * rotation * phase ^ x.2.val

private def shared (p : Fin 2 × Fin 2) : ℂ :=
  (![![(4 / 5 : ℂ), 0], ![0, 3 / 5]] : Fin 2 → Fin 2 → ℂ) p.1 p.2

private def measurementVector (x p : Fin 2 × Fin 2) : ℂ :=
  (![![(1 / 2 : ℂ), -(-1) ^ x.2.val / 2],
    ![(-1) ^ x.1.val / 2, (-1) ^ (x.1.val + x.2.val) / 2]] : Fin 2 → Fin 2 → ℂ) p.1 p.2

private def protocolM (_y : Unit) (b : Fin 2 × Fin 2) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  vecMulVec (measurementVector b) (star (measurementVector b))

private def coefficients (b x : Fin 2 × Fin 2) (_y : Unit) : ℝ :=
  if b = x then 1 / 4 else 0

private theorem protocol_encoded (x : Fin 2 × Fin 2) :
    encoded shared protocolU x = fun p : Fin 2 × Fin 2 =>
      (![![(16 / 25 : ℂ), -9 / 25 * (-1) ^ x.2.val],
        ![12 / 25 * (-1) ^ x.1.val, 12 / 25 * (-1) ^ (x.1.val + x.2.val)]] :
          Fin 2 → Fin 2 → ℂ) p.1 p.2 := by
  rw [encoded.eq_1, protocolU.eq_1, phase.eq_1, rotation.eq_1]
  ext p
  rcases x with ⟨u, v⟩
  rcases p with ⟨i, j⟩
  fin_cases u <;> fin_cases v <;> fin_cases i <;> fin_cases j <;>
    norm_num [shared.eq_1,
      D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply,
      Matrix.mul_apply]

private theorem protocol_valid : UnitaryStrategy shared protocolU protocolM := by
  constructor
  · simp_rw [shared.eq_1]
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply]
  · intro y
    constructor
    · intro b
      exact posSemidef_vecMulVec_self_star (measurementVector b)
    · simp_rw [protocolM.eq_1]
      ext p q
      rcases p with ⟨i, j⟩
      rcases q with ⟨k, l⟩
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
        norm_num [measurementVector.eq_1, Matrix.sum_apply, Fintype.sum_prod_type,
          Fin.sum_univ_two, Matrix.vecMulVec_apply, Matrix.one_apply, Prod.mk.injEq]

private theorem protocol_vacuum (x : Fin 2 × Fin 2) :
    unitaryVacuum shared protocolU x = 337 / 625 := by
  rw [unitaryVacuum]
  simp only [protocol_encoded]
  rcases x with ⟨u, v⟩
  fin_cases u <;> fin_cases v <;>
    norm_num [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]

private theorem protocol_value :
    taskValue coefficients (unitaryProb shared protocolU protocolM) = 2401 / 2500 := by
  have hp (x : Fin 2 × Fin 2) : unitaryProb shared protocolU protocolM x x () = 2401 / 2500 := by
    rw [unitaryProb, protocol_encoded, protocolM.eq_1]
    rcases x with ⟨u, v⟩
    fin_cases u <;> fin_cases v <;>
      norm_num [measurementVector.eq_1, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.vecMulVec_apply,
        map_ofNat]
  rw [taskValue.eq_1]
  simp_rw [coefficients.eq_1]
  simp [hp]

theorem residual_norm {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (g v : H) (hg : ‖g‖ = 1) (hv : ‖v‖ = 1) :
    ‖v - ⟪g, v⟫_ℂ • g‖ ^ 2 = 1 - ‖⟪g, v⟫_ℂ‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), hv, norm_smul, hg, inner_smul_right, ← inner_conj_symm v g]
  change 1 ^ 2 - 2 * (⟪g, v⟫_ℂ * star ⟪g, v⟫_ℂ).re +
    (‖⟪g, v⟫_ℂ‖ * 1) ^ 2 = 1 - ‖⟪g, v⟫_ℂ‖ ^ 2
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, one_pow, mul_one,
    Complex.normSq_eq_norm_sq]
  ring

private def compression {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : Fin 2 → H) (E : H →L[ℂ] H) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ⟪D i, E (D j)⟫_ℂ

private theorem compression_pairing {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : Fin 2 → H) (E : H →L[ℂ] H) (z : Fin 2 → ℂ) :
    star z ⬝ᵥ (compression D E *ᵥ z) =
      ⟪∑ i, z i • D i, E (∑ i, z i • D i)⟫_ℂ := by
  simp [compression.eq_1, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

private theorem compression_pos {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : Fin 2 → H) (E : H →L[ℂ] H) (hE : 0 ≤ E) :
    (compression D E).PosSemidef := by
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive (f := E)).mp hE
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [compression, Matrix.conjTranspose_apply]
    change (starRingEnd ℂ) ⟪D j, E (D i)⟫_ℂ = _
    rw [inner_conj_symm]
    exact hp.isSymmetric (D i) (D j)
  · intro z
    rw [compression_pairing]
    exact hp.inner_nonneg_right _

private theorem pure_bound {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : H →L[ℂ] H) (hE : 0 ≤ E) (hEc : 0 ≤ 1 - E)
    (g v : H) (hg : ‖g‖ = 1) (hv : ‖v‖ = 1) :
    (⟪v, E v⟫_ℂ).re - (⟪g, E g⟫_ℂ).re ≤
      Real.sqrt (1 - ‖⟪g, v⟫_ℂ‖ ^ 2) := by
  let c := ⟪g, v⟫_ℂ
  let s := Real.sqrt (1 - ‖c‖ ^ 2)
  have hr := residual_norm g v hg hv
  change ‖v - c • g‖ ^ 2 = 1 - ‖c‖ ^ 2 at hr
  have he0 : 0 ≤ 1 - ‖c‖ ^ 2 := by rw [← hr]; positivity
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - ‖c‖ ^ 2 := Real.sq_sqrt he0
  change _ ≤ s
  by_cases hs : s = 0
  · have hr0 : v - c • g = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (v - c • g)]
    have hcn : Complex.normSq c = 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [hs2]
    rw [sub_eq_zero.mp hr0]
    simp only [map_smul, inner_smul_left, inner_smul_right]
    rw [← mul_assoc, mul_comm c, ← Complex.normSq_eq_conj_mul_self, hcn, Complex.ofReal_one, one_mul, hs]
    simp
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    let w := (s : ℂ)⁻¹ • (v - c • g)
    have hrn : ‖v - c • g‖ = s := by nlinarith [norm_nonneg (v - c • g)]
    have hw : ‖w‖ = 1 := by
      simp [w, norm_smul, hrn, abs_of_pos hspos, ne_of_gt hspos]
    have hgw : ⟪g, w⟫_ℂ = 0 := by
      simp [w, c, inner_self_eq_norm_sq_to_K, hg]
    have hwg : ⟪w, g⟫_ℂ = 0 := by rw [← inner_conj_symm, hgw]; simp
    let D : Fin 2 → H := ![g, w]
    let N := compression D E
    have hD : compression D (1 : H →L[ℂ] H) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [compression, D, hgw, hwg, inner_self_eq_norm_sq_to_K, hg, hw]
    have hN : N.PosSemidef := compression_pos D E hE
    have hNc : (1 - N).PosSemidef := by
      convert compression_pos D (1 - E) hEc using 1
      rw [← hD]
      ext i j
      simp [N, compression]
    have hvD : ∑ i, (![c, (s : ℂ)] : Fin 2 → ℂ) i • D i = v := by
      simp only [Fin.sum_univ_two, D, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, w, smul_smul]
      rw [mul_inv_cancel₀ (by exact_mod_cast ne_of_gt hspos), one_smul]
      module
    have hread := compression_pairing D E ![c, (s : ℂ)]
    rw [hvD] at hread
    rw [← hread]
    exact two_level_bound N hN hNc s c hs0 (by rw [Complex.normSq_eq_norm_sq]; linarith)

private theorem weighted_summable {L : Type} (w f : L → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) :
    Summable (fun i => w i * f i) :=
  Summable.of_nonneg_of_le (fun i => mul_nonneg (hw i) (hf i).1)
    (fun i => by nlinarith [hw i, (hf i).2]) hs.summable

private theorem weighted_bounds {L : Type} (w f : L → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) :
    0 ≤ ∑' i, w i * f i ∧ (∑' i, w i * f i) ≤ 1 := by
  constructor
  · exact tsum_nonneg (fun i => mul_nonneg (hw i) (hf i).1)
  · rw [← hs.tsum_eq]
    exact (weighted_summable w f hw hs hf).tsum_le_tsum
      (fun i => by nlinarith [hw i, (hf i).2]) hs.summable

private theorem sqrt_average {L : Type} (w t : L → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    (∑' i, w i * Real.sqrt (t i)) ≤ Real.sqrt (∑' i, w i * t i) := by
  have hw2 (i : L) : (Real.sqrt (w i)) ^ (2 : ℝ) = w i := by
    rw [Real.rpow_ofNat, Real.sq_sqrt (hw i)]
  have ht2 (i : L) : (Real.sqrt (w i * t i)) ^ (2 : ℝ) = w i * t i := by
    rw [Real.rpow_ofNat, Real.sq_sqrt (mul_nonneg (hw i) (ht i).1)]
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
    (f := fun i => Real.sqrt (w i)) (g := fun i => Real.sqrt (w i * t i))
    Real.HolderConjugate.two_two (fun i => Real.sqrt_nonneg _)
    (fun i => Real.sqrt_nonneg _)
    (by simpa only [hw2] using hs.summable)
    (by simpa only [ht2] using weighted_summable w t hw hs ht)
  have hprod (i : L) :
      Real.sqrt (w i) * Real.sqrt (w i * t i) = w i * Real.sqrt (t i) := by
    rw [Real.sqrt_mul (hw i), ← mul_assoc, Real.mul_self_sqrt (hw i)]
  simpa only [hw2, ht2, ← Real.sqrt_eq_rpow, hs.tsum_eq, Real.sqrt_one, one_mul,
    hprod] using h

private theorem overlap_bounds {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (g v : H) (hg : ‖g‖ = 1) (hv : ‖v‖ = 1) :
    0 ≤ ‖⟪g, v⟫_ℂ‖ ^ 2 ∧ ‖⟪g, v⟫_ℂ‖ ^ 2 ≤ 1 := by
  refine ⟨sq_nonneg _, ?_⟩
  have h := norm_inner_le_norm (𝕜 := ℂ) g v
  rw [hg, hv, mul_one] at h
  nlinarith [norm_nonneg ⟪g, v⟫_ℂ]

private theorem effect_probability_bounds {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (E : H →L[ℂ] H) (hE : 0 ≤ E) (hEc : 0 ≤ 1 - E)
    (v : H) (hv : ‖v‖ = 1) :
    0 ≤ (⟪v, E v⟫_ℂ).re ∧ (⟪v, E v⟫_ℂ).re ≤ 1 := by
  constructor
  · exact ((ContinuousLinearMap.nonneg_iff_isPositive (f := E)).mp hE).re_inner_nonneg_right v
  · have hc := ((ContinuousLinearMap.nonneg_iff_isPositive (f := 1 - E)).mp hEc).re_inner_nonneg_right v
    change 0 ≤ (⟪v, v - E v⟫_ℂ).re at hc
    rw [inner_sub_right, Complex.sub_re, inner_self_eq_norm_sq_to_K] at hc
    norm_num [hv] at hc
    linarith

private theorem ensemble_bound {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : H →L[ℂ] H) (hE : 0 ≤ E) (hEc : 0 ≤ 1 - E)
    (g : H) (hg : ‖g‖ = 1) (w : K → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : HasSum w 1)
    (v : K → H) (hv : ∀ k, ‖v k‖ = 1) :
    (∑' k, w k * (⟪v k, E (v k)⟫_ℂ).re) ≤
      (⟪g, E g⟫_ℂ).re + Real.sqrt (1 - ∑' k, w k * ‖⟪g, v k⟫_ℂ‖ ^ 2) := by
  have ha (k : K) := overlap_bounds g (v k) hg (hv k)
  have he (k : K) : 0 ≤ 1 - ‖⟪g, v k⟫_ℂ‖ ^ 2 ∧ 1 - ‖⟪g, v k⟫_ℂ‖ ^ 2 ≤ 1 := by
    constructor <;> linarith [(ha k).1, (ha k).2]
  have hprob := weighted_summable w (fun k => (⟪v k, E (v k)⟫_ℂ).re) hw hs
    (fun k => effect_probability_bounds E hE hEc (v k) (hv k))
  have hroot := weighted_summable w (fun k => Real.sqrt (1 - ‖⟪g, v k⟫_ℂ‖ ^ 2)) hw hs
    (fun k => ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr (he k).2⟩)
  have herr : (∑' k, w k * (1 - ‖⟪g, v k⟫_ℂ‖ ^ 2)) =
      1 - ∑' k, w k * ‖⟪g, v k⟫_ℂ‖ ^ 2 := by
    simp_rw [mul_sub, mul_one]
    rw [hs.summable.tsum_sub (weighted_summable w _ hw hs ha), hs.tsum_eq]
  calc
    (∑' k, w k * (⟪v k, E (v k)⟫_ℂ).re) ≤
        ∑' k, (w k * (⟪g, E g⟫_ℂ).re + w k * Real.sqrt (1 - ‖⟪g, v k⟫_ℂ‖ ^ 2)) := by
      apply hprob.tsum_le_tsum _ ((hs.summable.mul_right _).add hroot)
      intro k
      have hb := mul_le_mul_of_nonneg_left (pure_bound E hE hEc g (v k) hg (hv k)) (hw k)
      nlinarith
    _ = (⟪g, E g⟫_ℂ).re + ∑' k, w k * Real.sqrt (1 - ‖⟪g, v k⟫_ℂ‖ ^ 2) := by
      rw [(hs.summable.mul_right _).tsum_add hroot, tsum_mul_right, hs.tsum_eq, one_mul]
    _ ≤ (⟪g, E g⟫_ℂ).re + Real.sqrt (∑' k, w k * (1 - ‖⟪g, v k⟫_ℂ‖ ^ 2)) :=
      add_le_add (le_refl _) (sqrt_average w _ hw hs he)
    _ = _ := by rw [herr]

private theorem diagonal_task (p : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Unit → ℝ) :
    taskValue coefficients p = (1 / 4) * ∑ x, p x x () := by
  rw [taskValue.eq_1]
  simp_rw [coefficients.eq_1]
  simp [ite_mul, Finset.mul_sum]

private theorem qc_bound {H L K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (vac : H) (q : L → ℝ) (p : L → (Fin 2 × Fin 2) → K → ℝ)
    (ψ : L → (Fin 2 × Fin 2) → K → H)
    (M : L → Unit → (Fin 2 × Fin 2) → (H →L[ℂ] H))
    (h : QCStrategy vac q p ψ M) (ω : ℝ)
    (henergy : ∀ x, 1 - ω ≤ qcVacuum vac q p ψ x) :
    taskValue coefficients (qcProb q p ψ M) ≤ 1 / 4 + Real.sqrt ω := by
  classical
  rcases h with ⟨hg, hq, hqs, hp, hps, hψ, hM⟩
  let a (l : L) (x : Fin 2 × Fin 2) := ∑' k, p l x k * ‖⟪vac, ψ l x k⟫_ℂ‖ ^ 2
  let r (l : L) (x : Fin 2 × Fin 2) := ∑' k, p l x k * (⟪ψ l x k, M l () x (ψ l x k)⟫_ℂ).re
  let z (l : L) (x : Fin 2 × Fin 2) := (⟪vac, M l () x vac⟫_ℂ).re
  have hEc (l : L) (x : Fin 2 × Fin 2) : 0 ≤ 1 - M l () x := by
    apply sub_nonneg.mpr
    rw [← (hM l ()).2]
    exact Finset.single_le_sum (fun b _ => (hM l ()).1 b) (Finset.mem_univ x)
  have ha (l : L) (x : Fin 2 × Fin 2) : 0 ≤ a l x ∧ a l x ≤ 1 :=
    weighted_bounds (p l x) _ (hp l x) (hps l x)
      (fun k => overlap_bounds vac (ψ l x k) hg (hψ l x k))
  have hr (l : L) (x : Fin 2 × Fin 2) : 0 ≤ r l x ∧ r l x ≤ 1 :=
    weighted_bounds (p l x) _ (hp l x) (hps l x)
      (fun k => effect_probability_bounds (M l () x) ((hM l ()).1 x) (hEc l x)
        (ψ l x k) (hψ l x k))
  have hz (l : L) (x : Fin 2 × Fin 2) : 0 ≤ z l x ∧ z l x ≤ 1 :=
    effect_probability_bounds (M l () x) ((hM l ()).1 x) (hEc l x) vac hg
  have he (l : L) (x : Fin 2 × Fin 2) : 0 ≤ 1 - a l x ∧ 1 - a l x ≤ 1 := by
    constructor <;> linarith [(ha l x).1, (ha l x).2]
  have hpoint (x : Fin 2 × Fin 2) :
      qcProb q p ψ M x x () ≤ (∑' l, q l * z l x) + Real.sqrt ω := by
    have hprob := weighted_summable q (fun l => r l x) hq hqs (fun l => hr l x)
    have hbase := weighted_summable q (fun l => z l x) hq hqs (fun l => hz l x)
    have hroot := weighted_summable q (fun l => Real.sqrt (1 - a l x)) hq hqs
      (fun l => ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr (he l x).2⟩)
    have herr : (∑' l, q l * (1 - a l x)) = 1 - qcVacuum vac q p ψ x := by
      simp_rw [mul_sub, mul_one]
      rw [hqs.summable.tsum_sub (weighted_summable q _ hq hqs (fun l => ha l x)),
        hqs.tsum_eq]
      rfl
    calc
      qcProb q p ψ M x x () = ∑' l, q l * r l x := rfl
      _ ≤ ∑' l, (q l * z l x + q l * Real.sqrt (1 - a l x)) := by
        apply hprob.tsum_le_tsum _ (hbase.add hroot)
        intro l
        have hb := mul_le_mul_of_nonneg_left
          (ensemble_bound (M l () x) ((hM l ()).1 x) (hEc l x) vac hg
            (p l x) (hp l x) (hps l x) (ψ l x) (hψ l x)) (hq l)
        dsimp only [r, z, a]
        nlinarith
      _ = (∑' l, q l * z l x) + ∑' l, q l * Real.sqrt (1 - a l x) :=
        hbase.tsum_add hroot
      _ ≤ (∑' l, q l * z l x) + Real.sqrt (∑' l, q l * (1 - a l x)) :=
        add_le_add (le_refl _) (sqrt_average q _ hq hqs (fun l => he l x))
      _ ≤ (∑' l, q l * z l x) + Real.sqrt ω := by
        apply add_le_add (le_refl _)
        apply Real.sqrt_le_sqrt
        rw [herr]
        linarith [henergy x]
  have htotal : (∑ x, ∑' l, q l * z l x) = 1 := by
    rw [← Summable.tsum_finsetSum (fun x _ =>
      weighted_summable q (fun l => z l x) hq hqs (fun l => hz l x))]
    calc
      (∑' l, ∑ x, q l * z l x) = ∑' l, q l * 1 := by
        apply tsum_congr
        intro l
        rw [← Finset.mul_sum]
        congr 1
        have ht := congrArg (fun E : H →L[ℂ] H => (⟪vac, E vac⟫_ℂ).re) (hM l ()).2
        simpa [z, _root_.sum_apply, inner_sum, inner_self_eq_norm_sq_to_K, hg] using ht
      _ = 1 := by simpa only [mul_one] using hqs.tsum_eq
  calc
    taskValue coefficients (qcProb q p ψ M) = (1 / 4) * ∑ x, qcProb q p ψ M x x () :=
      diagonal_task _
    _ ≤ (1 / 4) * ∑ x, ((∑' l, q l * z l x) + Real.sqrt ω) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => hpoint x)) (by norm_num)
    _ = 1 / 4 + Real.sqrt ω := by
      rw [Finset.sum_add_distrib, htotal]
      norm_num [Fintype.sum_prod_type, Fin.sum_univ_two]
      ring

theorem result : ¬ claim := by
  intro hc
  obtain ⟨H, hH, hI, hC, vac, L, K, q, p, ψ, M, hvalid, henergy, hvalue⟩ :=
    hc (Fin 2 × Fin 2) Unit (Fin 2 × Fin 2) coefficients (288 / 625)
      (by norm_num) (by norm_num) 2 2 shared protocolU protocolM protocol_valid
      (by intro x; rw [protocol_vacuum]; norm_num)
  let _ : NormedAddCommGroup H := hH
  let _ : InnerProductSpace ℂ H := hI
  let _ : CompleteSpace H := hC
  have hb := qc_bound vac q p ψ M hvalid (288 / 625) henergy
  have hs : Real.sqrt (288 / 625 : ℝ) < 17 / 25 := by
    apply (Real.sqrt_lt (by norm_num) (by norm_num)).2
    norm_num
  rw [protocol_value] at hvalue
  linarith

end D5.S3.Quantum.Entanglement.EnergyRestrictedUnitaryEncodingRefutation
