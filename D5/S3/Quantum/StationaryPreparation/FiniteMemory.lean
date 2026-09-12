/- GID: D5/S3/Quantum/StationaryPreparation/FiniteMemory
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/FiniteMemory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Hilbert emissions have a fixed circuit and a stationary dimension bound. -/

import D5.S3.Quantum.StationaryPreparation.PhysicalGram
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators TensorProduct ComplexOrder

namespace D5.S3.Quantum.StationaryPreparation.FiniteMemory
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
variable {A : Type*} [Fintype A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact tensor coefficients in the alphabet basis, with values in the original memory. -/
def coefficients (I : Type*) [Fintype I] : Space I ⊗[ℂ] H ≃ₗ[ℂ] (I → H) := by
  classical
  exact (TensorProduct.equivFinsuppOfBasisLeft (EuclideanSpace.basisFun I ℂ).toBasis).trans
    (Finsupp.linearEquivFunOnFinite ℂ H I)

theorem coefficients_tmul (I : Type*) [Fintype I] (z : Space I) (x : H) (i : I) :
    coefficients I (z ⊗ₜ[ℂ] x) i = z i • x := by
  classical
  simp [coefficients]

/-- Apply the fixed emission and read each successive symbol in the order of the word. -/
def wordMemory (V : H →ₗᵢ[ℂ] Space A ⊗[ℂ] H) : List A → H →ₗ[ℂ] H
  | [] => LinearMap.id
  | i :: w => (wordMemory V w).comp
      ((LinearMap.proj i).comp ((coefficients A).toLinearMap.comp V.toLinearMap))

/-- The full emitted tensor, reconstructed from all its word coefficients. -/
def output (V : H →ₗᵢ[ℂ] Space A ⊗[ℂ] H) (n : ℕ) (x : H) :
    Space (Fin n → A) ⊗[ℂ] H :=
  (coefficients (Fin n → A)).symm (fun w => wordMemory V (List.ofFn w) x)

theorem output_coefficients (V : H →ₗᵢ[ℂ] Space A ⊗[ℂ] H)
    (n : ℕ) (x : H) (w : Fin n → A) :
    coefficients (Fin n → A) (output V n x) w = wordMemory V (List.ofFn w) x := by
  simp [output]

theorem output_zero (V : H →ₗᵢ[ℂ] Space A ⊗[ℂ] H) (x : H) (w : Fin 0 → A) :
    coefficients (Fin 0 → A) (output V 0 x) w = x := by
  simp [output_coefficients, wordMemory]

theorem output_succ (V : H →ₗᵢ[ℂ] Space A ⊗[ℂ] H)
    (n : ℕ) (x : H) (w : Fin (n + 1) → A) :
    coefficients (Fin (n + 1) → A) (output V (n + 1) x) w =
      coefficients (Fin n → A) (output V n (coefficients A (V x) (w 0))) (Fin.tail w) := by
  have hw : List.ofFn w = w 0 :: List.ofFn (Fin.tail w) := by
    conv_lhs => rw [← Fin.cons_self_tail w]
    exact List.ofFn_cons _ _
  rw [output_coefficients, output_coefficients, hw]
  rfl

theorem output_eq_tmul_iff (V : H →ₗᵢ[ℂ] Space A ⊗[ℂ] H)
    (n : ℕ) (x f : H) (ψ : Space (Fin n → A)) :
    output V n x = ψ ⊗ₜ[ℂ] f ↔ ∀ w : Fin n → A,
      wordMemory V (List.ofFn w) x = ψ w • f := by
  rw [← (coefficients (Fin n → A)).injective.eq_iff, funext_iff]
  simp only [output_coefficients, coefficients_tmul]

private theorem coefficients_map (V : H →ₗᵢ[ℂ] Space A ⊗[ℂ] H)
    (I : Type*) [Fintype I] (z : Space I ⊗[ℂ] H) (i : I) :
    coefficients I (TensorProduct.map (LinearMap.id : Space I →ₗ[ℂ] Space I)
      V.toLinearMap z) i = V (coefficients I z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul y h => simp [TensorProduct.map_tmul, coefficients_tmul]
  | add z z' hz hz' => simp [map_add, hz, hz']

theorem output_tensor_step (V : H →ₗᵢ[ℂ] Space A ⊗[ℂ] H) (n : ℕ) (x : H) :
    TensorProduct.map (LinearMap.id : Space (Fin n → A) →ₗ[ℂ] Space (Fin n → A))
      V.toLinearMap (output V n x) =
    (coefficients (Fin n → A)).symm (fun w => (coefficients A).symm
      (fun i => coefficients (Fin (n + 1) → A) (output V (n + 1) x) (Fin.snoc w i))) := by
  have hlast (m : ℕ) (w : Fin m → A) (i : A) (y : H) :
      coefficients (Fin (m + 1) → A) (output V (m + 1) y) (Fin.snoc w i) =
        coefficients A (V (coefficients (Fin m → A) (output V m y) w)) i := by
    induction m generalizing y with
    | zero => simp only [output_succ, output_zero, Fin.snoc_zero]
    | succ m ih =>
      have htail : Fin.tail (α := fun _ : Fin (m + 2) => A) (Fin.snoc w i) =
          Fin.snoc (α := fun _ : Fin (m + 1) => A) (Fin.tail w) i := by
        ext j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · simp [Fin.tail]
        · simp only [Fin.tail, Fin.succ_castSucc, Fin.snoc_castSucc]
      rw [output_succ, output_succ V m y w, htail, Fin.snoc_apply_zero]
      exact ih (Fin.tail w) (coefficients A (V y) (w 0))
  apply (coefficients (Fin n → A)).injective
  ext w
  rw [LinearEquiv.apply_symm_apply, coefficients_map]
  apply (coefficients A).injective
  ext i
  rw [LinearEquiv.apply_symm_apply]
  exact (hlast n w i x).symm

variable (H) [FiniteDimensional ℂ H]

def coordinates : H ≃ₗᵢ[ℂ] Space (Fin (Module.finrank ℂ H)) :=
  (stdOrthonormalBasis ℂ H).repr

def tensorCoordinates (I : Type*) [Fintype I] :
    Space I ⊗[ℂ] H ≃ₗᵢ[ℂ] Space (I × Fin (Module.finrank ℂ H)) :=
  ((EuclideanSpace.basisFun I ℂ).tensorProduct (stdOrthonormalBasis ℂ H)).repr

variable {H}

theorem tensorCoordinates_apply (I : Type*) [Fintype I]
    (z : Space I ⊗[ℂ] H) (i : I) (k : Fin (Module.finrank ℂ H)) :
    tensorCoordinates H I z (i, k) = coordinates H (coefficients I z i) k := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
    simp [tensorCoordinates, coordinates, coefficients_tmul, mul_comm]
  | add z z' hz hz' => simp [map_add, hz, hz']

theorem exists_fixed_unitary (blank : A) (V : H →ₗᵢ[ℂ] Space A ⊗[ℂ] H) :
    ∃ U : Unitary (A × Fin (Module.finrank ℂ H)),
      (∀ x : H, PhysicalGram.emission blank U (coordinates H x) =
        tensorCoordinates H A (V x)) ∧
      (∀ (w : List A) (x : H), PhysicalGram.prefixMemory blank U w (coordinates H x) =
        coordinates H (wordMemory V w x)) ∧
      (∀ (n t : ℕ) (x : H), circuit (fun _ => U) n t
        (initialized blank n (coordinates H x)) =
        tensorCoordinates H (Fin n → A) (output V n x)) := by
  classical
  let e := coordinates H
  let T := tensorCoordinates H A
  obtain ⟨U, hU⟩ := exists_unitary_agree
    (PhysicalGram.emission blank (LinearIsometryEquiv.refl ℂ _))
    (T.toLinearIsometry.comp (V.comp e.symm.toLinearIsometry))
  have hstep (x : H) : PhysicalGram.emission blank U (coordinates H x) =
      tensorCoordinates H A (V x) := by
    simpa [PhysicalGram.emission, e, T] using hU (e x)
  have hletter (i : A) (x : H) : PhysicalGram.letter blank U i (coordinates H x) =
      coordinates H (coefficients A (V x) i) := by
    ext k
    rw [PhysicalGram.letter_apply, hstep, tensorCoordinates_apply]
  have hword (w : List A) (x : H) :
      PhysicalGram.prefixMemory blank U w (coordinates H x) =
        coordinates H (wordMemory V w x) := by
    induction w using List.reverseRecOn with
    | nil => rfl
    | append_singleton w i ih =>
      rw [PhysicalGram.prefix_append, ih, PhysicalGram.prefix_cons,
        PhysicalGram.prefix_nil, hletter]
      apply congrArg (coordinates H)
      have h := congrArg (fun z : Space (Fin w.length → A) ⊗[ℂ] (Space A ⊗[ℂ] H) =>
        coefficients A (coefficients (Fin w.length → A) z w.get) i)
        (output_tensor_step V w.length x)
      simpa only [coefficients_map, LinearEquiv.apply_symm_apply, output_coefficients,
        List.ofFn_succ_last, Fin.snoc_castSucc, Fin.snoc_last, List.ofFn_get] using h
  refine ⟨U, hstep, hword, ?_⟩
  intro n t x
  ext ⟨w, k⟩
  rw [PhysicalGram.circuit_fixed_coefficients, hword, tensorCoordinates_apply,
    output_coefficients]

theorem output_norm (blank : A) (V : H →ₗᵢ[ℂ] Space A ⊗[ℂ] H)
    (n : ℕ) (x : H) : ‖output V n x‖ = ‖x‖ := by
  obtain ⟨U, _, _, hU⟩ := exists_fixed_unitary blank V
  have h := congrArg norm (hU n 0 x)
  simpa using h.symm

theorem stationary_memory_dimension_lower_bound [DecidableEq A] [Nonempty A]
    (a : Multiset A) (V : H →ₗᵢ[ℂ] Space A ⊗[ℂ] H)
    (x f : H) (hx : ‖x‖ = 1) (hf : ‖f‖ = 1)
    (hout : output V a.card x = WithLp.toLp 2 (sectorVector a.card a) ⊗ₜ[ℂ] f) :
    (∏ i, (a.count i + 1)) - Finset.univ.sup a.count ≤ Module.finrank ℂ H := by
  classical
  let blank : A := Classical.choice inferInstance
  obtain ⟨U, _, hword, _⟩ := exists_fixed_unitary blank V
  have hcoeff := (output_eq_tmul_iff V a.card x f
    (WithLp.toLp 2 (sectorVector a.card a))).mp hout
  have hphysical (w : Fin a.card → A) (k : Fin (Module.finrank ℂ H)) :
      circuit (fun _ => U) a.card 0 (initialized blank a.card (coordinates H x)) (w, k) =
        sectorVector a.card a w * coordinates H f k := by
    rw [PhysicalGram.circuit_fixed_coefficients, hword, hcoeff]
    simp
  simpa using PhysicalGram.stationary_memory_dimension_lower_bound a blank U
    (coordinates H x) (coordinates H f) (by simpa using hx) (by simpa using hf) hphysical

def capacityOccupation (a : A → ℕ) : Multiset A :=
  Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm a)

theorem count_capacityOccupation [DecidableEq A] (a : A → ℕ) (i : A) :
    (capacityOccupation a).count i = a i := by
  simp [capacityOccupation]

theorem card_capacityOccupation (a : A → ℕ) :
    (capacityOccupation a).card = ∑ i, a i := by
  classical
  simp [capacityOccupation, Finsupp.card_toMultiset, Finsupp.sum_fintype]

theorem stationary_capacity_dimension_lower_bound [DecidableEq A] [Nonempty A]
    (a : A → ℕ) (V : H →ₗᵢ[ℂ] Space A ⊗[ℂ] H)
    (x f : H) (hx : ‖x‖ = 1) (hf : ‖f‖ = 1)
    (hout : output V (capacityOccupation a).card x =
      WithLp.toLp 2 (sectorVector (capacityOccupation a).card (capacityOccupation a)) ⊗ₜ[ℂ] f) :
    (∏ i, (a i + 1)) - Finset.univ.sup a ≤ Module.finrank ℂ H := by
  simpa only [count_capacityOccupation] using
    stationary_memory_dimension_lower_bound (capacityOccupation a) V x f hx hf hout

end D5.S3.Quantum.StationaryPreparation.FiniteMemory
