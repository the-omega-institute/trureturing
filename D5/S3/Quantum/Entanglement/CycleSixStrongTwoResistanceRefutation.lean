/- GID: D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.claim; result=D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.result; claim=D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.claim
   digest: The six-cycle state loses genuine entanglement after tracing out qubits 0 and 2. -/

/-
proof_shape: result: bind-only (explicit four-term convex product construction,
  rank-one positivity from Mathlib, finite phase and trace normalization)
escape_witness: none
admission_basis: open-problem-resolution (#11502; Refuted)
Direct frozen dependencies:
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
  statement_id: sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
  D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence.partialTraceFirst
  statement_id: sha256:60de08083a292a636d655dff7f5b06843146c051021ffe2d0b604db457edc565
-/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2048

noncomputable section
namespace D5.S3.Quantum.Entanglement.CycleSixStrongTwoResistanceRefutation

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence (partialTraceFirst)
open scoped BigOperators ComplexOrder MatrixOrder

/-- A finite convex combination of products of single-qubit density matrices. -/
def IsFullySeparable {V : Type} [Fintype V] [DecidableEq V]
    (ρ : Matrix (V → Bool) (V → Bool) ℂ) : Prop :=
  ∃ (k : ℕ) (p : Fin k → ℝ) (σ : Fin k → V → DensityState Bool),
    (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
      ∀ x y, ρ x y = ∑ j, (p j : ℂ) * ∏ v, (σ j v).val (x v) (y v)

/-- Each term may use a different nontrivial bipartition. The tensor product
is pulled back by restriction of a configuration to the two complementary sets. -/
def IsBiseparable {V : Type} [Fintype V] [DecidableEq V]
    (ρ : Matrix (V → Bool) (V → Bool) ℂ) : Prop :=
  ∃ (k : ℕ) (p : Fin k → ℝ) (A : Fin k → Finset V)
    (σ : (j : Fin k) → DensityState (A j → Bool))
    (τ : (j : Fin k) → DensityState (↥((A j)ᶜ) → Bool)),
    (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
    (∀ j, (A j).Nonempty ∧ ((A j)ᶜ).Nonempty) ∧
    ∀ x y, ρ x y = ∑ j, (p j : ℂ) *
      (σ j).val (fun v => x v.val) (fun v => y v.val) *
      (τ j).val (fun v => x v.val) (fun v => y v.val)

/-- Genuine multipartite entanglement is the absence of a biseparable decomposition. -/
def IsGME {V : Type} [Fintype V] [DecidableEq V]
    (ρ : Matrix (V → Bool) (V → Bool) ℂ) : Prop := ¬ IsBiseparable ρ

/-- Reassemble traced and retained bit configurations on complementary qubit sets. -/
def joinBits {V : Type} [DecidableEq V] (J : Finset V)
    (z : J → Bool) (x : {v : V // v ∉ J} → Bool) (v : V) : Bool :=
  if h : v ∈ J then z ⟨v, h⟩ else x ⟨v, h⟩

/-- Partial trace over a finite set, using the finite bipartite partial trace
on the explicitly reindexed matrix. -/
def partialTrace {V : Type} [Fintype V] [DecidableEq V]
    (ρ : Matrix (V → Bool) (V → Bool) ℂ) (J : Finset V) :
    Matrix ({v : V // v ∉ J} → Bool) ({v : V // v ∉ J} → Bool) ℂ :=
  partialTraceFirst (ρ.submatrix (fun q => joinBits J q.1 q.2)
    (fun q => joinBits J q.1 q.2))

/-- The normalized graph-state amplitudes of the labelled cycle, for n ≥ 3.
The formula also defines an amplitude vector for other positive n. -/
def cycleGraphState (n : ℕ) [NeZero n] (x : Fin n → Bool) : ℂ :=
  (-1 : ℂ) ^ (∑ i : Fin n, (x i).toNat *
    (x ⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩).toNat) /
    (Real.sqrt (2 ^ n) : ℂ)

/-- The three source conditions: initial GME, GME after every m-particle loss,
and full separability after every (m+1)-particle loss. -/
def IsStrongResistant {n : ℕ} (m : ℕ) (ψ : (Fin n → Bool) → ℂ) : Prop :=
  IsGME (Matrix.vecMulVec ψ (star ψ)) ∧
  (∀ J : Finset (Fin n), J.card = m →
    IsGME (partialTrace (Matrix.vecMulVec ψ (star ψ)) J)) ∧
  (∀ J : Finset (Fin n), J.card = m + 1 →
    IsFullySeparable (partialTrace (Matrix.vecMulVec ψ (star ψ)) J))

/-- The C₆, m = 2 clause of Han, Zhang and Zhang's question. -/
def claim : Prop := IsStrongResistant 2 (cycleGraphState 6)

/-- Tracing out {0,2} gives four products across {1} | {3,4,5}. -/
theorem result : ¬ claim := by
  classical
  let J : Finset (Fin 6) := {0, 2}
  let R := {v : Fin 6 // v ∉ J}
  let q1 : R := ⟨1, by decide⟩
  let q3 : R := ⟨3, by decide⟩
  let q4 : R := ⟨4, by decide⟩
  let q5 : R := ⟨5, by decide⟩
  let A : Finset R := {q1}
  let t : Fin 4 → Bool := fun j => decide (2 ≤ j.val)
  let u : Fin 4 → Bool := fun j => decide (j.val % 2 = 1)
  let a : Fin 4 → (A → Bool) → ℂ := fun j x =>
    (-1 : ℂ) ^ ((t j).toNat * (x ⟨q1, by simp [A]⟩).toNat +
      (u j).toNat * (x ⟨q1, by simp [A]⟩).toNat)
  let b : Fin 4 → (↥(Aᶜ) → Bool) → ℂ := fun j x =>
    let x3 := (x ⟨q3, by decide⟩).toNat
    let x4 := (x ⟨q4, by decide⟩).toNat
    let x5 := (x ⟨q5, by decide⟩).toNat
    (-1 : ℂ) ^ (x3 * x4 + x4 * x5 + (u j).toNat * x3 + (t j).toNat * x5)
  have phase : ∀ e : ℕ, (-1 : ℂ) ^ e * star ((-1 : ℂ) ^ e) = 1 := by
    intro e
    simp only [star_pow, star_neg, star_one, ← mul_pow]
    norm_num
  let density : {ι : Type} → [Fintype ι] → [DecidableEq ι] →
      (v : ι → ℂ) → (∀ x, v x * star (v x) = 1) →
      (h : 0 < Fintype.card ι) → DensityState ι := fun {ι} _ _ v hv h =>
    ⟨CStarMatrix.ofMatrix ((Fintype.card ι : ℝ)⁻¹ • Matrix.vecMulVec v (star v)),
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
        ((Matrix.posSemidef_vecMulVec_self_star v).smul (by positivity)).nonneg,
      by
        change Matrix.trace ((Fintype.card ι : ℝ)⁻¹ •
          Matrix.vecMulVec v (star v)) = 1
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.smul_apply,
          Matrix.vecMulVec_apply, Pi.star_apply, Complex.real_smul,
          Complex.ofReal_inv, Complex.ofReal_natCast]
        simp only [hv, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt h))⟩
  let σ : Fin 4 → DensityState (A → Bool) := fun j =>
    density (a j) (fun x => phase _) (by exact Fintype.card_pos)
  let τ : Fin 4 → DensityState (↥(Aᶜ) → Bool) := fun j =>
    density (b j) (fun x => phase _) (by exact Fintype.card_pos)
  have ha : ∀ j x y, (σ j).val x y = (1 / 2 : ℂ) * a j x * star (a j y) := by
    intro j x y
    change (Fintype.card (A → Bool) : ℝ)⁻¹ • (a j x * star (a j y)) = _
    have cardA : Fintype.card A = 1 := by simp [A]
    simp only [Fintype.card_fun, cardA, Fintype.card_bool]
    norm_num [Complex.real_smul]
    ring
  have hb : ∀ j x y, (τ j).val x y = (1 / 8 : ℂ) * b j x * star (b j y) := by
    intro j x y
    change (Fintype.card (↥(Aᶜ) → Bool) : ℝ)⁻¹ • (b j x * star (b j y)) = _
    have cardR : Fintype.card R = 4 := by decide
    have cardA : Fintype.card A = 1 := by simp [A]
    have cardB : Fintype.card ↥(Aᶜ) = 3 := by
      rw [Fintype.card_coe, Finset.card_compl, ← Fintype.card_coe, cardA]
      exact congrArg (fun n => n - 1) cardR
    simp only [Fintype.card_fun, cardB, Fintype.card_bool]
    norm_num [Complex.real_smul]
    ring
  let e : (J → Bool) ≃ Fin 4 :=
    { toFun := fun z => ⟨2 * (z ⟨0, by decide⟩).toNat +
        (z ⟨2, by decide⟩).toNat, by
          cases z ⟨0, by decide⟩ <;> cases z ⟨2, by decide⟩ <;> decide⟩
      invFun := fun j v => if v.val = 0 then t j else u j
      left_inv := by
        intro z
        funext v
        fin_cases v <;> cases h0 : z ⟨0, by decide⟩ <;>
          cases h2 : z ⟨2, by decide⟩ <;> simp [t, u, h0, h2]
      right_inv := by intro j; fin_cases j <;> rfl }
  have hfactor : ∀ (j : Fin 4) (x : R → Bool),
      cycleGraphState 6 (joinBits J (e.symm j) x) =
        a j (fun v => x v.val) * b j (fun v => x v.val) / 8 := by
    intro j x
    change cycleGraphState 6 (joinBits J
      (fun v => if v.val = 0 then t j else u j) x) = _
    unfold joinBits
    simp only [cycleGraphState, Fin.sum_univ_succ]
    norm_num [J, t, u, a, b, q1, q3, q4, q5, A,
      Fin.ext_iff]
    simp only [← pow_add]
    apply congrArg (fun k : ℕ => (-1 : ℂ) ^ k)
    dsimp only [Fin.succ]
    simp only [show (⟨3, by decide⟩ : Fin 6) = 3 from rfl,
      show (⟨4, by decide⟩ : Fin 6) = 4 from rfl,
      show (⟨5, by decide⟩ : Fin 6) = 5 from rfl]
    ring
  have hbis : IsBiseparable
      (partialTrace (Matrix.vecMulVec (cycleGraphState 6) (star (cycleGraphState 6))) J) := by
    refine ⟨4, fun _ => 1 / 4, fun _ => A, σ, τ, ?_, ?_, ?_, ?_⟩
    · intro j; norm_num
    · norm_num [Fin.sum_univ_succ]
    · intro j
      exact ⟨⟨q1, by simp [A]⟩, ⟨q3, by change q3 ∈ Aᶜ; decide⟩⟩
    · intro x y
      change (∑ z : J → Bool, cycleGraphState 6 (joinBits J z x) *
        star (cycleGraphState 6 (joinBits J z y))) = _
      rw [← e.symm.sum_comp]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hfactor, hfactor, ha, hb]
      simp only [star_div₀, star_mul, star_ofNat]
      norm_num
      ring
  intro h
  exact h.2.1 J (by decide) hbis

#print axioms result
end D5.S3.Quantum.Entanglement.CycleSixStrongTwoResistanceRefutation
