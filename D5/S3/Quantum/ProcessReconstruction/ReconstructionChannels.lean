/- GID: D5/S3/Quantum/ProcessReconstruction/ReconstructionChannels
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/ReconstructionChannels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Canonical unitary and reduced channels with finite reference duality. -/

import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Canonical unitary and reduced channels with finite reference duality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence

namespace UnitaryReconstruction

universe u

variable {a b : Type u} {c r : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c] [Fintype r] [DecidableEq r]

theorem channel_ext {C D : QuantumChannel a b}
    (h : ∀ X, C.toCompletelyPositiveMap X = D.toCompletelyPositiveMap X) : C = D := by
  have hp : C.toCompletelyPositiveMap = D.toCompletelyPositiveMap := by
    cases C with
    | mk C hC =>
      cases D with
      | mk D hD =>
        change ∀ X, C X = D X at h
        cases C
        cases D
        congr
        apply LinearMap.ext
        exact h
  cases C
  cases D
  cases hp
  rfl

def conjugation (U : unitaryGroup a ℂ) : QuantumChannel a a :=
  (finite_kraus_quantum_channel (fun _ : Unit => U.val) (by
    simpa only [Fintype.sum_unique, Matrix.star_eq_conjTranspose]
      using (Unitary.star_mul_self_of_mem U.prop))).choose

theorem conjugation_apply (U : unitaryGroup a ℂ) (X : Matrix a a ℂ) :
    CStarMatrix.ofMatrix.symm ((conjugation U).toCompletelyPositiveMap
      (CStarMatrix.ofMatrix X)) = U.val * X * U.valᴴ := by
  unfold conjugation
  simpa using (finite_kraus_quantum_channel (fun _ : Unit => U.val)
    (by
      simpa only [Fintype.sum_unique, Matrix.star_eq_conjTranspose]
        using (Unitary.star_mul_self_of_mem U.prop))).choose_spec X

def pick (e : a ≃ c × b) (z : c) : Matrix b a ℂ :=
  fun i j => if e.symm (z,i) = j then 1 else 0

omit [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
theorem pick_sandwich (e : a ≃ c × b) (z : c) (X : Matrix a a ℂ) :
    pick e z * X * (pick e z)ᴴ = X.submatrix (fun i => e.symm (z,i)) (fun i => e.symm (z,i)) := by
  ext i j
  simp [pick, Matrix.mul_apply, Matrix.conjTranspose_apply]

set_option linter.unusedDecidableInType false in
omit [Fintype a] in
theorem pick_complete (e : a ≃ c × b) : ∑ z, (pick e z)ᴴ * pick e z = 1 := by
  ext x y
  rw [Matrix.sum_apply]
  have h (z : c) (j : b) : (e.symm (z,j) = x) ↔ z = (e x).1 ∧ j = (e x).2 := by
    rw [Equiv.symm_apply_eq, Prod.mk.injEq]
  have h' (z : c) (j : b) : (e.symm (z,j) = y) ↔ z = (e y).1 ∧ j = (e y).2 := by
    rw [Equiv.symm_apply_eq, Prod.mk.injEq]
  have he : x = y ↔ (e x).1 = (e y).1 ∧ (e x).2 = (e y).2 := by
    rw [← e.apply_eq_iff_eq, Prod.ext_iff]
  simp only [pick, Matrix.mul_apply, Matrix.conjTranspose_apply, h, h',
    Matrix.one_apply, he]
  by_cases hx : (e x).1 = (e y).1 <;> by_cases hy : (e x).2 = (e y).2 <;>
    simp [*, ite_and, apply_ite, eq_comm]

/-- Trace out the first factor after identifying the output basis with `c × b`. -/
def discard (e : a ≃ c × b) : QuantumChannel a b :=
  (finite_kraus_quantum_channel (pick e) (pick_complete e)).choose

theorem discard_apply (e : a ≃ c × b) (X : Matrix a a ℂ) :
    CStarMatrix.ofMatrix.symm ((discard e).toCompletelyPositiveMap
      (CStarMatrix.ofMatrix X)) = partialTraceFirst (X.submatrix e.symm e.symm) := by
  unfold discard
  rw [(finite_kraus_quantum_channel (pick e) (pick_complete e)).choose_spec]
  ext i j
  simp [Matrix.sum_apply, pick_sandwich, partialTraceFirst]

/-- The input index remains the entire global system. -/
def reducedConjugation (e : a ≃ c × b) (U : unitaryGroup a ℂ) : QuantumChannel a b :=
  (discard e).comp (conjugation U)

def referenceMatrix (C : QuantumChannel a b) (X : Matrix (r × a) (r × a) ℂ) :
    Matrix (r × b) (r × b) ℂ :=
  CStarMatrix.ofMatrix.symm (referenceAction C (CStarMatrix.ofMatrix X))

theorem referenceMatrix_apply (C : QuantumChannel a b) (X : Matrix (r × a) (r × a) ℂ)
    (i j : r) (u v : b) :
    referenceMatrix C X (i,u) (j,v) =
      C.toCompletelyPositiveMap (CStarMatrix.ofMatrix (fun x y => X (i,x) (j,y))) u v := rfl

theorem referenceMatrix_comp {d : Type u} [Fintype d] [DecidableEq d]
    (C : QuantumChannel b d) (D : QuantumChannel a b)
    (X : Matrix (r × a) (r × a) ℂ) :
    referenceMatrix (C.comp D) X = referenceMatrix C (referenceMatrix D X) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  rw [referenceMatrix_apply, referenceMatrix_apply]
  exact congrArg (fun M : CStarMatrix d d ℂ => M u v) (QuantumChannel.comp_apply C D _)

theorem referenceMatrix_discard (e : a ≃ c × b) (X : Matrix (r × a) (r × a) ℂ)
    (i j : r) (u v : b) :
    referenceMatrix (discard e) X (i,u) (j,v) =
      ∑ z, X (i,e.symm (z,u)) (j,e.symm (z,v)) := by
  rw [referenceMatrix_apply]
  exact congrArg (fun M : Matrix b b ℂ => M u v)
    (discard_apply e (fun x y => X (i,x) (j,y)))

def referenceUnitary (r : Type*) [Fintype r] [DecidableEq r] (U : unitaryGroup a ℂ) :
    unitaryGroup (r × a) ℂ :=
  ⟨(1 : Matrix r r ℂ) ⊗ₖ U.val, by
    apply Matrix.mem_unitaryGroup_iff.mpr
    change ((1 : Matrix r r ℂ) ⊗ₖ U.val) * ((1 : Matrix r r ℂ) ⊗ₖ U.val)ᴴ = 1
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
    have hu : U.val * U.valᴴ = 1 := Unitary.mul_star_self_of_mem U.prop
    simp only [Matrix.conjTranspose_one, Matrix.mul_one, hu, Matrix.one_kronecker_one]⟩

theorem referenceMatrix_conjugation (U : unitaryGroup a ℂ)
    (X : Matrix (r × a) (r × a) ℂ) :
    referenceMatrix (conjugation U) X =
      (referenceUnitary r U).val * X * (referenceUnitary r U).valᴴ := by
  ext ⟨i,u⟩ ⟨j,v⟩
  rw [referenceMatrix_apply]
  rw [show (conjugation U).toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (fun x y => X (i,x) (j,y))) u v =
      (U.val * (of fun x y => X (i,x) (j,y)) * U.valᴴ) u v from
    congrArg (fun M : Matrix a a ℂ => M u v) (conjugation_apply U _)]
  simp [referenceUnitary, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply,
    Matrix.kroneckerMap_apply, Matrix.conjTranspose_kronecker]

/-- Lift an observable by the identity on the discarded output, leaving the
reference as part of the observable. -/
def liftObservable (e : a ≃ c × b) (S : Matrix (r × b) (r × b) ℂ) :
    Matrix (r × a) (r × a) ℂ :=
  fun p q => if (e p.2).1 = (e q.2).1 then S (p.1,(e p.2).2) (q.1,(e q.2).2) else 0

theorem trace_liftObservable (e : a ≃ c × b) (S : Matrix (r × b) (r × b) ℂ)
    (X : Matrix (r × a) (r × a) ℂ) :
    (liftObservable e S * X).trace = (S * referenceMatrix (discard e) X).trace := by
  let f : c × (r × b) ≃ r × a :=
    { toFun := fun p => (p.2.1, e.symm (p.1, p.2.2))
      invFun := fun p => ((e p.2).1, (p.1, (e p.2).2))
      left_inv := by rintro ⟨z,i,u⟩; simp
      right_inv := by rintro ⟨i,u⟩; simp }
  have hf (p : c × (r × b)) : f p = (p.2.1,e.symm (p.1,p.2.2)) := rfl
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [← f.sum_comp]
  conv_lhs => enter [2, p]; rw [← f.sum_comp]
  rw [Fintype.sum_prod_type]
  have h (z : c) (p : r × b) :
      (∑ q : c × (r × b), liftObservable e S (f (z,p)) (f q) * X (f q) (f (z,p))) =
      ∑ q : r × b, S p q * X (f (z,q)) (f (z,p)) := by
    rw [Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro q _
    simp [hf, liftObservable, ite_mul]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [show referenceMatrix (discard e) X q p = _ from
    referenceMatrix_discard e X q.1 p.1 q.2 p.2, Finset.mul_sum]
  simp only [hf]

theorem referenceError_le_two (C D : QuantumChannel a b) (ρ : DensityState (r × a)) :
    referenceError C D ρ ≤ 2 := by
  have hstate (σ : DensityState (r × b)) : traceNorm (CStarMatrix.ofMatrix.symm σ.1) = 1 := by
    have hp : (CStarMatrix.ofMatrix.symm σ.1).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.2.1)
    have h := traceNorm_of_posSemidef hp
    change (traceNorm (CStarMatrix.ofMatrix.symm σ.1) : ℂ) = Matrix.trace σ.1 at h
    rw [σ.2.2] at h
    exact_mod_cast h
  unfold referenceError
  rw [sub_eq_add_neg]
  exact (traceNorm_add_le _ _).trans (by rw [traceNorm_neg, hstate, hstate]; norm_num)

theorem diamondDistance_nonneg' (C D : QuantumChannel a b) : 0 ≤ diamondDistance C D :=
  le_csSup ⟨2, by
    rintro x (hx | ⟨n, ρ, rfl⟩)
    · have : x = 0 := hx
      norm_num [this]
    · exact referenceError_le_two C D ρ⟩ (Or.inl rfl)

theorem diamondDistance_le (C D : QuantumChannel a b) {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ (n : ℕ) (ρ : DensityState (Fin n × a)), referenceError C D ρ ≤ t) :
    diamondDistance C D ≤ t := by
  apply csSup_le (show ({0} ∪ {x : ℝ | ∃ n : ℕ, ∃ ρ : DensityState (Fin n × a),
    x = referenceError C D ρ}).Nonempty from ⟨0, Or.inl rfl⟩)
  rintro x (hx | ⟨n, ρ, rfl⟩)
  · have : x = 0 := hx
    simpa [this] using ht
  · exact h n ρ

theorem referenceError_le_diamond (C D : QuantumChannel a b) (ρ : DensityState (r × a)) :
    referenceError C D ρ ≤ diamondDistance C D := by
  obtain ⟨τ, _, hτ⟩ := (D5.S3.Quantum.Foundation.FiniteDiamondDistance.result C D).2.1 ρ
  exact hτ.trans (le_csSup ⟨2, by
    rintro x (hx | ⟨n, σ, rfl⟩)
    · have : x = 0 := hx
      norm_num [this]
    · exact referenceError_le_two C D σ⟩ (Or.inr ⟨_, τ, rfl⟩))

end UnitaryReconstruction
