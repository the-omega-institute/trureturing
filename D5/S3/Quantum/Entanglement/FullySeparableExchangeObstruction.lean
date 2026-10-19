/- GID: D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/FullySeparableExchangeObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zero exchanged diagonals exclude coherence in fully separable states. -/

/-
admission_basis: escape-witness
escape_witness: separable_exchange_zero
Escape audit unfinished for density_psd: https://github.com/the-omega-institute/trureturing/issues/19102.
Escape audit unfinished under issue #15589: the dependent-family registration still lacks full source reconstruction, equivalence, variation, sensitivity, and observational-dependence evidence; the delivered-head DTR reading is `DTR-Unregistered` (Observe) for `separable_exchange_zero`, and no `declared_validated` claim is made.
Direct frozen dependencies:
  D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence.partialTraceFirst
    statement_id: sha256:60de08083a292a636d655dff7f5b06843146c051021ffe2d0b604db457edc565
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
    statement_id: sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
proof_shape: joinLocal: definition; escape_witness: none
  consumers: diagonal_partial_trace_separable, partial_trace_diag, partialTraceLocal, flagState_large_loss_diagonal, flagState_exchanged_diagonals, flagState_coherence_nonzero
  frozen dependencies: none
proof_shape: partialTraceLocal: definition; escape_witness: none
  consumers: IsMResistant, flagState_kept_entangled, result, diagonal_partial_trace_separable, partial_trace_diag, flagState_large_loss_diagonal, flagState_exchanged_diagonals, flagState_coherence_nonzero
  frozen dependencies: partialTraceFirst
proof_shape: IsFullySeparableLocal: definition; escape_witness: none
  consumers: IsMResistant, flagState_kept_entangled, diagonal_separable, result, separable_exchange_zero, diagonal_partial_trace_separable, flagState_entangled
  frozen dependencies: DensityState
proof_shape: density_psd: bind-only; escape_witness: none
  consumers: density_zero_col, separable_exchange_zero, density_zero_row
  frozen dependencies: DensityState
proof_shape: density_zero_col: bind-only; escape_witness: none
  consumers: separable_exchange_zero, density_zero_row
  frozen dependencies: DensityState
proof_shape: density_zero_row: bind-only; escape_witness: none
  consumers: separable_exchange_zero
  frozen dependencies: DensityState
proof_shape: separable_exchange_zero: content; escape_witness: separable_exchange_zero
  consumers: flagState_kept_entangled, flagState_entangled
  frozen dependencies: DensityState
Definitions are not proof declarations. Compiler-generated proof constants inherit
the identity of their frozen source owner; they have no separate Freeze identity.
utility none: arbitrary finite carriers and universal constructions; no bounded
enumeration, checker, numeric reduction, or certified finite instance.
-/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.Entanglement.FullySeparableExchangeObstruction
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence (partialTraceFirst)
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

def joinLocal {V L : Type} [DecidableEq V] (J : Finset V)
    (z : J → L) (x : {v : V // v ∉ J} → L) (v : V) : L :=
  if h : v ∈ J then z ⟨v, h⟩ else x ⟨v, h⟩

def partialTraceLocal {V L : Type} [Fintype V] [DecidableEq V]
    [Fintype L] [DecidableEq L]
    (ρ : Matrix (V → L) (V → L) ℂ) (J : Finset V) :
    Matrix ({v : V // v ∉ J} → L) ({v : V // v ∉ J} → L) ℂ :=
  partialTraceFirst (ρ.submatrix (fun q => joinLocal J q.1 q.2)
    (fun q => joinLocal J q.1 q.2))

def IsFullySeparableLocal {V L : Type} [Fintype V] [DecidableEq V]
    [Fintype L] [DecidableEq L]
    (ρ : Matrix (V → L) (V → L) ℂ) : Prop :=
  ∃ (k : ℕ) (p : Fin k → ℝ) (σ : Fin k → V → DensityState L),
    (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
      ∀ x y, ρ x y = ∑ j, (p j : ℂ) * ∏ v, (σ j v).val (x v) (y v)

variable {V L : Type} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

theorem density_psd (σ : DensityState L) :
    (CStarMatrix.ofMatrix.symm σ.val).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.2.1)

private theorem density_zero_col (σ : DensityState L) (a b : L)
    (hz : σ.val a a = 0) : σ.val b a = 0 := by
  have hquad : star (Pi.single a (1 : ℂ)) ⬝ᵥ
      ((CStarMatrix.ofMatrix.symm σ.val) *ᵥ Pi.single a 1) = 0 := by
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hz
  have h := ((density_psd σ).dotProduct_mulVec_zero_iff (x := (Pi.single a 1))).mp hquad
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun h b

private theorem density_zero_row (σ : DensityState L) (a b : L)
    (hz : σ.val a a = 0) : σ.val a b = 0 := by
  have h : star (σ.val b a) = σ.val a b := (density_psd σ).isHermitian.apply a b
  rw [density_zero_col σ a b hz, star_zero] at h
  exact h.symm

/-- A fully separable state cannot have coherence across a vanishing exchanged diagonal. -/
theorem separable_exchange_zero (ρ : Matrix (V → L) (V → L) ℂ)
    (hρ : IsFullySeparableLocal ρ) (x y : V → L) (i : V)
    (hz : ρ (Function.update x i (y i)) (Function.update x i (y i)) = 0) :
    ρ x y = 0 := by
  classical
  obtain ⟨k, p, σ, hp, hsum, he⟩ := hρ
  let u := Function.update x i (y i)
  have hd (j : Fin k) (v : V) : 0 ≤ (σ j v).val (u v) (u v) :=
    (density_psd (σ j v)).diag_nonneg
  have hn (j : Fin k) : 0 ≤ (p j : ℂ) * ∏ v, (σ j v).val (u v) (u v) :=
    mul_nonneg ((by exact_mod_cast hp j)) (Finset.prod_nonneg (fun v _ => hd j v))
  have ht (j : Fin k) : (p j : ℂ) * ∏ v, (σ j v).val (u v) (u v) = 0 := by
    have hs : (∑ j, (p j : ℂ) * ∏ v, (σ j v).val (u v) (u v)) = 0 :=
      (he u u).symm.trans hz
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hs j (Finset.mem_univ j)
  rw [he]
  apply Finset.sum_eq_zero
  intro j _
  rcases mul_eq_zero.mp (ht j) with hj | hj
  · simp [hj]
  · obtain ⟨v, _, hv⟩ := Finset.prod_eq_zero_iff.mp hj
    have hxy : (σ j v).val (x v) (y v) = 0 := by
      by_cases hvi : v = i
      · subst v
        simp only [u, Function.update_self] at hv
        exact density_zero_col (σ j i) (y i) (x i) hv
      · simp only [u, Function.update_of_ne hvi] at hv
        exact density_zero_row (σ j v) (x v) (y v) hv
    rw [Finset.prod_eq_zero (Finset.mem_univ v) hxy, mul_zero]


end D5.S3.Quantum.Entanglement.FullySeparableExchangeObstruction
