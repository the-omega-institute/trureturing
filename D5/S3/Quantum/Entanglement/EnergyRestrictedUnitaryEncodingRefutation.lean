/- GID: D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.claim; result=D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.result; claim=D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.claim
   digest: Four unitary encodings beat every unassisted strategy below half-unit energy. -/

import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Entanglement.EnergyRestrictedUnitaryEncodingRefutation

open _root_.Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker InnerProductSpace
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
open D5.S3.Quantum.Reduction.IsometricCompression (compress)

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

/-- Finite shared randomness, density messages, and conditional POVMs. -/
def QCStrategy {X Y B L : Type} [Fintype B] [Fintype L] {d : ℕ}
    (q : L → ℝ) (ρ : L → X → Matrix (Fin d) (Fin d) ℂ)
    (M : L → Y → B → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ l, 0 ≤ q l) ∧ ∑ l, q l = 1 ∧ (∀ l x, IsDensity (ρ l x)) ∧
    ∀ l y, D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM (M l y)

/-- Shared randomness averages the conditional Born probabilities. -/
def qcProb {X Y B L : Type} [Fintype L] {d : ℕ}
    (q : L → ℝ) (ρ : L → X → Matrix (Fin d) (Fin d) ℂ)
    (M : L → Y → B → Matrix (Fin d) (Fin d) ℂ) (b : B) (x : X) (y : Y) : ℝ :=
  ∑ l, q l * (trace (ρ l x * M l y b)).re

/-- The energy constraint averages vacuum populations over shared randomness. -/
def qcVacuum {X L : Type} [Fintype L] {d : ℕ} [NeZero d]
    (q : L → ℝ) (ρ : L → X → Matrix (Fin d) (Fin d) ℂ) (x : X) : ℝ :=
  ∑ l, q l * (ρ l x 0 0).re

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
      ∃ (d : ℕ) (_ : NeZero d) (L : Type) (_ : Fintype L)
        (q : L → ℝ) (ρ : L → X → Matrix (Fin d) (Fin d) ℂ)
        (N : L → Y → B → Matrix (Fin d) (Fin d) ℂ),
        QCStrategy q ρ N ∧ (∀ x, 1 - ω ≤ qcVacuum q ρ x) ∧
          taskValue c (unitaryProb Ψ U M) ≤ taskValue c (qcProb q ρ N)

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

private theorem residual_norm {d : ℕ} [NeZero d]
    (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖ = 1) :
    ‖v - v 0 • (PiLp.single 2 0 1 : EuclideanSpace ℂ (Fin d))‖ ^ 2 =
      1 - Complex.normSq (v 0) := by
  let g : EuclideanSpace ℂ (Fin d) := PiLp.single 2 0 1
  have hg : ‖g‖ = 1 := by simp [g]
  have hgv : ⟪g, v⟫_ℂ = v 0 := by
    simpa [g] using EuclideanSpace.inner_single_left 0 (1 : ℂ) v
  have hvg : ⟪v, g⟫_ℂ = star (v 0) := by rw [← inner_conj_symm, hgv]; rfl
  change ‖v - v 0 • g‖ ^ 2 = _
  rw [norm_sub_sq (𝕜 := ℂ), hv, norm_smul, hg, inner_smul_right, hvg]
  change 1 ^ 2 - 2 * (v 0 * star (v 0)).re + (‖v 0‖ * 1) ^ 2 = 1 - Complex.normSq (v 0)
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, one_pow, mul_one,
    ← Complex.normSq_eq_norm_sq]
  ring

private theorem vacuum_frame {d : ℕ} [NeZero d] (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖ = 1)
    (s : ℝ) (hs : 0 < s) (he : s ^ 2 = 1 - Complex.normSq (v 0)) :
    ∃ D : Matrix (Fin d) (Fin 2) ℂ, Dᴴ * D = 1 ∧
      D *ᵥ ![v 0, (s : ℂ)] = v ∧ D *ᵥ ![1, 0] = Pi.single 0 1 := by
  let g : EuclideanSpace ℂ (Fin d) := PiLp.single 2 0 1
  let w : EuclideanSpace ℂ (Fin d) := (s : ℂ)⁻¹ • (v - v 0 • g)
  have hg : ‖g‖ = 1 := by simp [g]
  have hgv : ⟪g, v⟫_ℂ = v 0 := by simpa [g] using EuclideanSpace.inner_single_left 0 (1 : ℂ) v
  have hr := residual_norm v hv
  change ‖v - v 0 • g‖ ^ 2 = 1 - Complex.normSq (v 0) at hr
  rw [← he] at hr
  have hw : ‖w‖ = 1 := by
    have hrn : ‖v - v 0 • g‖ = s := by nlinarith [norm_nonneg (v - v 0 • g)]
    simp [w, norm_smul, hrn, abs_of_pos hs, ne_of_gt hs]
  have hgw : ⟪g, w⟫_ℂ = 0 := by
    simp [w, hgv, inner_self_eq_norm_sq_to_K, hg]
  have hwg : ⟪w, g⟫_ℂ = 0 := by rw [← inner_conj_symm, hgw]; simp
  let D : Matrix (Fin d) (Fin 2) ℂ := fun i j => (![g i, w i] : Fin 2 → ℂ) j
  refine ⟨D, ?_, ?_, ?_⟩
  · have hi (a b : EuclideanSpace ℂ (Fin d)) :
        star a.ofLp ⬝ᵥ b.ofLp = ⟪a, b⟫_ℂ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    ext i j
    fin_cases i <;> fin_cases j
    · change star g.ofLp ⬝ᵥ g.ofLp = 1
      rw [hi]; simp [inner_self_eq_norm_sq_to_K, hg]
    · change star g.ofLp ⬝ᵥ w.ofLp = 0
      rw [hi, hgw]
    · change star w.ofLp ⬝ᵥ g.ofLp = 0
      rw [hi, hwg]
    · change star w.ofLp ⬝ᵥ w.ofLp = 1
      rw [hi]; simp [inner_self_eq_norm_sq_to_K, hw]
  · ext i
    simp [D, Matrix.mulVec, dotProduct, Fin.sum_univ_two, w, PiLp.smul_apply]
    field_simp
    ring
  · ext i
    simp [D, Matrix.mulVec, dotProduct, Fin.sum_univ_two, g, Pi.single_apply]

private theorem pure_bound {d : ℕ} [NeZero d] (E : Matrix (Fin d) (Fin d) ℂ)
    (hE : E.PosSemidef) (hEc : (1 - E).PosSemidef)
    (v : EuclideanSpace ℂ (Fin d)) (hv : ‖v‖ = 1) :
    (star v.ofLp ⬝ᵥ (E *ᵥ v.ofLp)).re - (E 0 0).re ≤
      Real.sqrt (1 - Complex.normSq (v 0)) := by
  let s := Real.sqrt (1 - Complex.normSq (v 0))
  let g : EuclideanSpace ℂ (Fin d) := PiLp.single 2 0 1
  have he0 : 0 ≤ 1 - Complex.normSq (v 0) := by
    rw [← residual_norm v hv]
    positivity
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - Complex.normSq (v 0) := Real.sq_sqrt he0
  change (star v.ofLp ⬝ᵥ (E *ᵥ v.ofLp)).re - (E 0 0).re ≤ s
  by_cases hs : s = 0
  · have hr0 : v - v 0 • g = 0 := by
      apply norm_eq_zero.mp
      have hr := residual_norm v hv
      change ‖v - v 0 • g‖ ^ 2 = 1 - Complex.normSq (v 0) at hr
      nlinarith [norm_nonneg (v - v 0 • g)]
    have hcn : Complex.normSq (v 0) = 1 := by nlinarith [hs2]
    have hvec : v.ofLp = v 0 • Pi.single 0 1 := by
      have hf := congrArg WithLp.ofLp (sub_eq_zero.mp hr0)
      simpa [g] using hf
    have hcalc : star v.ofLp ⬝ᵥ (E *ᵥ v.ofLp) = E 0 0 := by
      rw [hvec]
      simp only [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
      simp only [Pi.star_single, star_one, Matrix.mulVec_single_one,
        single_dotProduct, one_mul, smul_eq_mul]
      change v 0 * (star (v 0) * E 0 0) = E 0 0
      rw [← mul_assoc, mul_comm (v 0), Complex.star_def,
        ← Complex.normSq_eq_conj_mul_self, hcn, Complex.ofReal_one, one_mul]
    rw [hcalc, sub_self, hs]
  · obtain ⟨D, hD, hvD, hgD⟩ := vacuum_frame v hv s (lt_of_le_of_ne hs0 (Ne.symm hs)) hs2
    let N := compress D E
    have hN : N.PosSemidef := hE.conjTranspose_mul_mul_same D
    have hNc : (1 - N).PosSemidef := by
      have hp := hEc.conjTranspose_mul_mul_same D
      simpa only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, hD, N, compress] using hp
    have pairing (z : Fin 2 → ℂ) :
        star z ⬝ᵥ (N *ᵥ z) = star (D *ᵥ z) ⬝ᵥ (E *ᵥ (D *ᵥ z)) := by
      dsimp [N, compress]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
        vecMul_conjTranspose, star_star]
    have hn00 : N 0 0 = E 0 0 := by
      have hp := pairing ![1, 0]
      rw [hgD] at hp
      simpa [dotProduct, Fin.sum_univ_two, Matrix.mulVec_single_one,
        Matrix.mulVec, Pi.single_apply] using hp
    have hread := pairing ![v 0, (s : ℂ)]
    rw [hvD] at hread
    rw [← hread, ← hn00]
    exact two_level_bound N hN hNc s (v 0) hs0 (by linarith [hs2])

private theorem sqrt_average {L : Type} [Fintype L] (q e : L → ℝ)
    (hq : ∀ l, 0 ≤ q l) (ht : ∑ l, q l = 1) (he : ∀ l, 0 ≤ e l) :
    (∑ l, q l * Real.sqrt (e l)) ≤ Real.sqrt (∑ l, q l * e l) := by
  simpa only [smul_eq_mul] using Real.strictConcaveOn_sqrt.concaveOn.le_map_sum
    (t := Finset.univ) (w := q) (p := e) (fun l _ => hq l) ht (fun l _ => he l)

private theorem effect_bound {d : ℕ} [NeZero d]
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsDensity ρ)
    (E : Matrix (Fin d) (Fin d) ℂ) (hE : E.PosSemidef) (hEc : (1 - E).PosSemidef) :
    (trace (E * ρ)).re - (E 0 0).re ≤ Real.sqrt (1 - (ρ 0 0).re) := by
  classical
  let t := hρ.1.isHermitian.eigenvalues
  let v := hρ.1.isHermitian.eigenvectorBasis
  have ht (j : Fin d) : 0 ≤ t j := hρ.1.eigenvalues_nonneg j
  have hsum : ∑ j, t j = 1 :=
    D5.S3.Quantum.Matrix.CartesianVariance.density_eigenvalues_sum ρ hρ
  have hn (j : Fin d) : ‖v j‖ = 1 := v.orthonormal.1 j
  have hdiag : (ρ 0 0).re = ∑ j, t j * Complex.normSq (v j 0) := by
    rw [D5.S3.Quantum.Matrix.CartesianVariance.hermitian_spectral_sum ρ hρ.1.isHermitian]
    simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      Complex.normSq_apply, Complex.mul_re, t, v]
  have hread : (trace (E * ρ)).re =
      ∑ j, t j * (star (v j).ofLp ⬝ᵥ (E *ᵥ (v j).ofLp)).re := by
    have hh := congrArg Complex.re
      (D5.S3.Quantum.Matrix.CartesianVariance.hermitian_trace_spectral ρ E hρ.1.isHermitian)
    rw [Matrix.trace_mul_comm] at hh
    simpa only [Complex.re_sum, Complex.smul_re, smul_eq_mul,
      EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, dotProduct_comm, t, v] using hh
  have he (j : Fin d) : 0 ≤ 1 - Complex.normSq (v j 0) := by
    rw [← residual_norm (v j) (hn j)]
    positivity
  have hj := sqrt_average t (fun j => 1 - Complex.normSq (v j 0)) ht hsum he
  have havg : (∑ j, t j * (1 - Complex.normSq (v j 0))) = 1 - (ρ 0 0).re := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hsum, hdiag]
  calc
    (trace (E * ρ)).re - (E 0 0).re =
        ∑ j, t j * ((star (v j).ofLp ⬝ᵥ (E *ᵥ (v j).ofLp)).re - (E 0 0).re) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul, hread]
    _ ≤ ∑ j, t j * Real.sqrt (1 - Complex.normSq (v j 0)) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (pure_bound E hE hEc (v j) (hn j)) (ht j))
    _ ≤ Real.sqrt (1 - (ρ 0 0).re) := by simpa only [havg] using hj

private theorem diagonal_task (p : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → Unit → ℝ) :
    taskValue coefficients p = (1 / 4) * ∑ x, p x x () := by
  rw [taskValue.eq_1]
  simp_rw [coefficients.eq_1]
  simp [ite_mul, Finset.mul_sum]

private theorem qc_bound {L : Type} [Fintype L] {d : ℕ} [NeZero d]
    (q : L → ℝ) (ρ : L → (Fin 2 × Fin 2) → Matrix (Fin d) (Fin d) ℂ)
    (M : L → Unit → (Fin 2 × Fin 2) → Matrix (Fin d) (Fin d) ℂ)
    (h : QCStrategy q ρ M) (ω : ℝ) (henergy : ∀ x, 1 - ω ≤ qcVacuum q ρ x) :
    taskValue coefficients (qcProb q ρ M) ≤ 1 / 4 + Real.sqrt ω := by
  classical
  let e (x : Fin 2 × Fin 2) := ∑ l, q l * (1 - (ρ l x 0 0).re)
  have he0 (l : L) (x : Fin 2 × Fin 2) : 0 ≤ 1 - (ρ l x 0 0).re :=
    sub_nonneg.mpr (D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.state_diag_le_one
      (h.2.2.1 l x).1 (h.2.2.1 l x).2 0)
  have he (x : Fin 2 × Fin 2) : 0 ≤ e x :=
    Finset.sum_nonneg (fun l _ => mul_nonneg (h.1 l) (he0 l x))
  have heω (x : Fin 2 × Fin 2) : e x ≤ ω := by
    have hx := henergy x
    dsimp [e]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, h.2.1]
    change 1 - qcVacuum q ρ x ≤ ω
    linarith
  have hpoint (x : Fin 2 × Fin 2) :
      qcProb q ρ M x x () ≤ (∑ l, q l * (M l () x 0 0).re) + Real.sqrt (e x) := by
    have hj := sqrt_average q (fun l => 1 - (ρ l x 0 0).re) h.1 h.2.1 (fun l => he0 l x)
    calc
      qcProb q ρ M x x () ≤
          ∑ l, q l * ((M l () x 0 0).re + Real.sqrt (1 - (ρ l x 0 0).re)) := by
        apply Finset.sum_le_sum
        intro l _
        apply mul_le_mul_of_nonneg_left _ (h.1 l)
        have hm := h.2.2.2 l ()
        have hc : (1 - M l () x).PosSemidef := by
          change M l () x ≤ 1
          rw [← hm.2]
          exact Finset.single_le_sum (fun b _ => (hm.1 b).nonneg) (Finset.mem_univ x)
        have hb := effect_bound (ρ l x) (h.2.2.1 l x) (M l () x) (hm.1 x) hc
        rw [Matrix.trace_mul_comm] at hb
        linarith
      _ = (∑ l, q l * (M l () x 0 0).re) +
          ∑ l, q l * Real.sqrt (1 - (ρ l x 0 0).re) := by
        simp only [mul_add, Finset.sum_add_distrib]
      _ ≤ _ := add_le_add (le_refl _) hj
  have htotal : (∑ x, ∑ l, q l * (M l () x 0 0).re) = 1 := by
    rw [Finset.sum_comm]
    calc
      (∑ l, ∑ x, q l * (M l () x 0 0).re) = ∑ l, q l * 1 := by
        apply Finset.sum_congr rfl
        intro l _
        rw [← Finset.mul_sum]
        congr 1
        have hm := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (A 0 0).re) (h.2.2.2 l ()).2
        simpa [Matrix.sum_apply] using hm
      _ = 1 := by simpa only [mul_one] using h.2.1
  have hjx := sqrt_average (fun _ : Fin 2 × Fin 2 => (1 / 4 : ℝ)) e
    (by intro x; norm_num) (by norm_num [Fintype.sum_prod_type, Fin.sum_univ_two]) he
  have havg : (∑ x : Fin 2 × Fin 2, (1 / 4 : ℝ) * e x) ≤ ω := by
    calc
      _ ≤ ∑ _x : Fin 2 × Fin 2, (1 / 4 : ℝ) * ω :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (heω x) (by norm_num))
      _ = ω := by norm_num [Fintype.sum_prod_type, Fin.sum_univ_two]; ring
  calc
    taskValue coefficients (qcProb q ρ M) = (1 / 4) * ∑ x, qcProb q ρ M x x () := diagonal_task _
    _ ≤ (1 / 4) * ∑ x, ((∑ l, q l * (M l () x 0 0).re) + Real.sqrt (e x)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => hpoint x)) (by norm_num)
    _ = 1 / 4 + ∑ x, (1 / 4 : ℝ) * Real.sqrt (e x) := by
      rw [Finset.sum_add_distrib, htotal, mul_add, mul_one, Finset.mul_sum]
    _ ≤ 1 / 4 + Real.sqrt (∑ x, (1 / 4 : ℝ) * e x) := add_le_add (le_refl _) hjx
    _ ≤ 1 / 4 + Real.sqrt ω := add_le_add (le_refl _) (Real.sqrt_le_sqrt havg)

theorem result : ¬ claim := by
  intro hc
  obtain ⟨d, hd, L, hL, q, ρ, M, hvalid, henergy, hvalue⟩ :=
    hc (Fin 2 × Fin 2) Unit (Fin 2 × Fin 2) coefficients (288 / 625)
      (by norm_num) (by norm_num) 2 2 shared protocolU protocolM protocol_valid
      (by intro x; rw [protocol_vacuum]; norm_num)
  let _ : NeZero d := hd
  let _ : Fintype L := hL
  have hb := qc_bound q ρ M hvalid (288 / 625) henergy
  have hs : Real.sqrt (288 / 625 : ℝ) < 17 / 25 := by
    apply (Real.sqrt_lt (by norm_num) (by norm_num)).2
    norm_num
  rw [protocol_value] at hvalue
  linarith

end D5.S3.Quantum.Entanglement.EnergyRestrictedUnitaryEncodingRefutation
