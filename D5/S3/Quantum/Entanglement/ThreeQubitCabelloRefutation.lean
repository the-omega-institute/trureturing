/- GID: D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.claim; result=D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.result; claim=D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.claim
   digest: A three-qubit state beats Cereceda's 9/64 Cabello bound (1609.04763). -/

/-
proof_shape: result: bind-only (evaluation of the definitions at one explicit state and
  observables: the sums over `Fin 2` by `norm_num`, genuine entanglement by three 2 × 2
  determinants)
escape_witness: null
admission_basis: open-problem-resolution (issue #11927; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation

/-- The amplitude `⟨a ⊗ b ⊗ c | ψ⟩` of a three-qubit vector `ψ` along the product of the
qubit vectors `a`, `b`, `c`. -/
def amp (a b c : Fin 2 → ℂ) (ψ : Fin 2 → Fin 2 → Fin 2 → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, star (a i) * star (b j) * star (c k) * ψ i j k

/-- The joint probability `|⟨a ⊗ b ⊗ c | ψ⟩|²` of the three outcomes whose eigenvectors are
`a`, `b`, `c`, for a unit vector `ψ`. -/
def prob (a b c : Fin 2 → ℂ) (ψ : Fin 2 → Fin 2 → Fin 2 → ℂ) : ℝ :=
  Complex.normSq (amp a b c ψ)

/-- `e` and `f` are an orthonormal basis of `ℂ²`: the eigenvectors of a `±1`-valued qubit
observable for the outcomes `+1` and `−1`. -/
def IsONB (e f : Fin 2 → ℂ) : Prop :=
  ∑ i, star (e i) * e i = 1 ∧ ∑ i, star (f i) * f i = 1 ∧ ∑ i, star (e i) * f i = 0

/-- `ψ` is a product across the cut separating qubit 1 from qubits 2 and 3. -/
def ProductCut1 (ψ : Fin 2 → Fin 2 → Fin 2 → ℂ) : Prop :=
  ∃ (a : Fin 2 → ℂ) (b : Fin 2 → Fin 2 → ℂ), ∀ i j k, ψ i j k = a i * b j k

/-- `ψ` is a product across the cut separating qubit 2 from qubits 1 and 3. -/
def ProductCut2 (ψ : Fin 2 → Fin 2 → Fin 2 → ℂ) : Prop :=
  ∃ (a : Fin 2 → ℂ) (b : Fin 2 → Fin 2 → ℂ), ∀ i j k, ψ i j k = a j * b i k

/-- `ψ` is a product across the cut separating qubit 3 from qubits 1 and 2. -/
def ProductCut3 (ψ : Fin 2 → Fin 2 → Fin 2 → ℂ) : Prop :=
  ∃ (a : Fin 2 → ℂ) (b : Fin 2 → Fin 2 → ℂ), ∀ i j k, ψ i j k = a k * b i j

/-- `ψ` is genuinely entangled: it is a product across none of the three cuts. -/
def GenuinelyEntangled (ψ : Fin 2 → Fin 2 → Fin 2 → ℂ) : Prop :=
  ¬ ProductCut1 ψ ∧ ¬ ProductCut2 ψ ∧ ¬ ProductCut3 ψ

/-- Cereceda's conjecture (arXiv:1609.04763), upper bound: for every genuinely entangled unit
three-qubit state and all local observables `U_k`, `D_k` (eigenvectors `up k`, `um k` and
`dp k`, `dm k`) with `P(D₁U₂U₃|+++) = P(U₁D₂U₃|+++) = P(U₁U₂D₃|+++) = 0` and
`Q = P(D₁D₂D₃|−−−) > 0`, the violation `C = P(U₁U₂U₃|+++) − Q` is at most `9/64`. -/
def claim : Prop :=
  ∀ (ψ : Fin 2 → Fin 2 → Fin 2 → ℂ) (up um dp dm : Fin 3 → Fin 2 → ℂ),
    ∑ i, ∑ j, ∑ k, Complex.normSq (ψ i j k) = 1 → GenuinelyEntangled ψ →
    (∀ k, IsONB (up k) (um k)) → (∀ k, IsONB (dp k) (dm k)) →
    prob (dp 0) (up 1) (up 2) ψ = 0 → prob (up 0) (dp 1) (up 2) ψ = 0 →
    prob (up 0) (up 1) (dp 2) ψ = 0 → 0 < prob (dm 0) (dm 1) (dm 2) ψ →
    prob (up 0) (up 1) (up 2) ψ - prob (dm 0) (dm 1) (dm 2) ψ ≤ 9 / 64

/-- The conjecture fails: with `U_k = σ_z`, `D_k` with eigenvectors `(3, 4)/5`, `(−4, 3)/5`, and
`ψ = (16|000⟩ − 12 Σ|weight 1⟩ − 15 Σ|weight 2⟩ + 9|111⟩)/38`, the constraints vanish,
`Q = 790321/22562500 > 0` and `C = 3209679/22562500 > 9/64`. -/
theorem result : ¬ claim := by
  intro h
  -- the amplitudes of the witness, by Hamming weight
  let w : Fin 2 → Fin 2 → Fin 2 → ℝ := fun i j k =>
    (![16, -12, -15, 9] : Fin 4 → ℝ) ⟨i.val + j.val + k.val, by omega⟩ / 38
  let uP : Fin 2 → ℝ := ![1, 0]
  let uM : Fin 2 → ℝ := ![0, 1]
  let dP : Fin 2 → ℝ := ![3 / 5, 4 / 5]
  let dM : Fin 2 → ℝ := ![-4 / 5, 3 / 5]
  let C : (Fin 2 → ℝ) → Fin 2 → ℂ := fun v i => (v i : ℂ)
  let ψ : Fin 2 → Fin 2 → Fin 2 → ℂ := fun i j k => (w i j k : ℂ)
  -- amplitudes and inner products of real vectors are real
  have hamp : ∀ a b c : Fin 2 → ℝ, amp (C a) (C b) (C c) ψ =
      ((∑ i, ∑ j, ∑ k, a i * b j * c k * w i j k : ℝ) : ℂ) := by
    intro a b c
    simp only [amp, C, ψ, Complex.star_def, Complex.conj_ofReal]
    push_cast
    rfl
  have hprob : ∀ a b c : Fin 2 → ℝ, prob (C a) (C b) (C c) ψ =
      (∑ i, ∑ j, ∑ k, a i * b j * c k * w i j k) ^ 2 := by
    intro a b c
    rw [prob, hamp, Complex.normSq_ofReal, sq]
  have hinner : ∀ a b : Fin 2 → ℝ, ∑ i, star (C a i) * C b i = ((∑ i, a i * b i : ℝ) : ℂ) := by
    intro a b
    simp only [C, Complex.star_def, Complex.conj_ofReal]
    push_cast
    rfl
  have honb : ∀ e f : Fin 2 → ℝ, ∑ i, e i * e i = 1 → ∑ i, f i * f i = 1 →
      ∑ i, e i * f i = 0 → IsONB (C e) (C f) := by
    intro e f he hf hef
    refine ⟨?_, ?_, ?_⟩
    · rw [hinner, he]; simp
    · rw [hinner, hf]; simp
    · rw [hinner, hef]; simp
  -- a product across a cut forces a vanishing 2 × 2 determinant, which the witness violates
  have hdet : (w 0 0 0 : ℂ) * w 1 0 1 ≠ (w 0 0 1 : ℂ) * w 1 0 0 := by
    simp only [w]
    norm_num
  have hent : GenuinelyEntangled ψ := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨a, b, hab⟩
      apply hdet
      change ψ 0 0 0 * ψ 1 0 1 = ψ 0 0 1 * ψ 1 0 0
      rw [hab 0 0 0, hab 1 0 1, hab 0 0 1, hab 1 0 0]
      ring
    · rintro ⟨a, b, hab⟩
      apply hdet
      have e1 : ψ 1 0 1 = ψ 1 1 0 := by simp only [ψ, w]; norm_num
      have e2 : ψ 0 0 1 = ψ 0 1 0 := by simp only [ψ, w]; norm_num
      change ψ 0 0 0 * ψ 1 0 1 = ψ 0 0 1 * ψ 1 0 0
      rw [e1, e2, hab 0 0 0, hab 1 1 0, hab 0 1 0, hab 1 0 0]
      ring
    · rintro ⟨a, b, hab⟩
      apply hdet
      have e1 : ψ 1 0 1 = ψ 0 1 1 := by simp only [ψ, w]; norm_num
      have e2 : ψ 1 0 0 = ψ 0 1 0 := by simp only [ψ, w]; norm_num
      change ψ 0 0 0 * ψ 1 0 1 = ψ 0 0 1 * ψ 1 0 0
      rw [e1, e2, hab 0 0 0, hab 0 1 1, hab 0 0 1, hab 0 1 0]
      ring
  have hnorm : ∑ i, ∑ j, ∑ k, Complex.normSq (ψ i j k) = 1 := by
    simp only [ψ, Complex.normSq_ofReal, w, Fin.sum_univ_two]
    norm_num
  have key := h ψ (fun _ => C uP) (fun _ => C uM) (fun _ => C dP) (fun _ => C dM) hnorm hent
    (fun _ => honb uP uM (by simp [uP, Fin.sum_univ_two]) (by simp [uM, Fin.sum_univ_two])
      (by simp [uP, uM, Fin.sum_univ_two]))
    (fun _ => honb dP dM (by simp [dP, Fin.sum_univ_two]; norm_num)
      (by simp [dM, Fin.sum_univ_two]; norm_num) (by simp [dP, dM, Fin.sum_univ_two]; norm_num))
  simp only [hprob] at key
  simp only [w, uP, dP, dM, Fin.sum_univ_two] at key
  norm_num at key

end D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation
