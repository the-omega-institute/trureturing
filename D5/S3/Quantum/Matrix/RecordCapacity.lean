/- GID: D5/S3/Quantum/Matrix/RecordCapacity
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/RecordCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonzero equivariant idempotent resolutions obey commutant capacity bounds. -/

import Mathlib.LinearAlgebra.Trace
import Mathlib.Data.Matrix.Block
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Matrix.RecordCapacity

open scoped BigOperators

/-- The ranks of an idempotent resolution add to the dimension of the carrier. -/
theorem sum_range_finrank_of_idempotent_sum
    {K V I : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype I] (p : I → Module.End K V)
    (hid : ∀ i, IsIdempotentElem (p i)) (hsum : ∑ i, p i = 1) :
    ∑ i, Module.finrank K (LinearMap.range (p i)) = Module.finrank K V := by
  have htrace : (∑ i, (Module.finrank K (LinearMap.range (p i)) : K)) =
      (Module.finrank K V : K) := by
    calc
      _ = ∑ i, LinearMap.trace K V (p i) :=
        Finset.sum_congr rfl fun i _ =>
          (LinearMap.IsIdempotentElem.isProj_range _ (hid i)).trace.symm
      _ = LinearMap.trace K V (∑ i, p i) := (map_sum _ _ _).symm
      _ = _ := by rw [hsum, LinearMap.trace_one]
  exact_mod_cast htrace

/-- Every nonzero idempotent consumes at least one dimension in a resolution of identity. -/
theorem card_le_finrank_of_idempotent_sum
    {K V I : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype I] (p : I → Module.End K V)
    (hid : ∀ i, IsIdempotentElem (p i)) (hne : ∀ i, p i ≠ 0)
    (hsum : ∑ i, p i = 1) : Fintype.card I ≤ Module.finrank K V := by
  have hpos (i : I) : 1 ≤ Module.finrank K (LinearMap.range (p i)) := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hz
    apply hne i
    apply LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero (hid i)
    rw [(LinearMap.IsIdempotentElem.isProj_range _ (hid i)).trace, hz, Nat.cast_zero]
  calc
    Fintype.card I = ∑ _ : I, 1 := by simp
    _ ≤ ∑ i, Module.finrank K (LinearMap.range (p i)) :=
      Finset.sum_le_sum fun i _ => hpos i
    _ = _ := sum_range_finrank_of_idempotent_sum p hid hsum

/-- The actual commutant of the supplied shared symmetry. -/
def commutant {G n : Type*} [Group G] [Fintype n] [DecidableEq n]
    (U : G →* Matrix n n ℂ) : Subalgebra ℂ (Matrix n n ℂ) :=
  Subalgebra.centralizer ℂ (Set.range U)

/-- Equivariance places a matrix in the commutant as an algebra element. -/
def equivariantElement {G n : Type*} [Group G] [Fintype n] [DecidableEq n]
    (U : G →* Matrix n n ℂ) (P : Matrix n n ℂ)
    (hP : ∀ g, P * U g = U g * P) : commutant U :=
  ⟨P, (Subalgebra.mem_centralizer_iff ℂ).mpr fun _ ⟨g, hg⟩ => hg ▸ (hP g).symm⟩

/-- A finite nonzero idempotent resolution in any complex algebra is bounded by its dimension. -/
theorem algebra_card_le_finrank
    {A I : Type*} [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ A] [Fintype I]
    (p : I → A) (hid : ∀ i, IsIdempotentElem (p i)) (hne : ∀ i, p i ≠ 0)
    (hsum : ∑ i, p i = 1) : Fintype.card I ≤ Module.finrank ℂ A := by
  let f := Algebra.lmul ℂ A
  apply card_le_finrank_of_idempotent_sum (fun i => f (p i))
  · intro i
    exact (hid i).map f
  · intro i h
    exact hne i (Algebra.lmul_injective (h.trans f.map_zero.symm))
  · rw [← map_sum, hsum, map_one]

/-- Conditional capacity bound; the shared symmetry and record equivariance are inputs. -/
theorem equivariant_record_card_le_commutant_finrank
    {G n I : Type*} [Group G] [Fintype n] [DecidableEq n] [Fintype I]
    (U : G →* Matrix n n ℂ) (P : I → Matrix n n ℂ)
    (hrecord : CompleteOrthogonalIdempotents P) (hne : ∀ i, P i ≠ 0)
    (hequivariant : ∀ i g, P i * U g = U g * P i) :
    Fintype.card I ≤ Module.finrank ℂ (commutant U) := by
  let p : I → commutant U := fun i => equivariantElement U (P i) (hequivariant i)
  apply algebra_card_le_finrank p
  · intro i
    apply Subtype.ext
    exact (hrecord.idem i).eq
  · intro i h
    exact hne i (congrArg Subtype.val h)
  · apply Subtype.ext
    change (commutant U).val (∑ i, p i) = (commutant U).val 1
    rw [map_sum, map_one]
    exact hrecord.complete

/-- A resolution in a product of matrix algebras has at most the sum of the block sizes. -/
theorem matrix_blocks_card_le_sum
    {B I : Type*} [Fintype B] [Fintype I] (m : B → ℕ)
    (p : I → ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ)
    (hid : ∀ i, IsIdempotentElem (p i)) (hne : ∀ i, p i ≠ 0)
    (hsum : ∑ i, p i = 1) : Fintype.card I ≤ ∑ b, m b := by
  classical
  let f := Matrix.toLinAlgEquiv'.toRingHom.comp
    (Matrix.blockDiagonal'RingHom (fun b => Fin (m b)) ℂ)
  have hf : Function.Injective f :=
    Matrix.toLinAlgEquiv'.injective.comp Matrix.blockDiagonal'_injective
  have hbound := card_le_finrank_of_idempotent_sum (fun i => f (p i))
    (fun i => (hid i).map f)
    (fun i h => hne i (hf (h.trans f.map_zero.symm)))
    (by rw [← map_sum, hsum, map_one])
  simpa only [Module.finrank_pi, Fintype.card_sigma, Fintype.card_fin] using hbound

/-- The sharp bound for a supplied block decomposition of the actual commutant. -/
theorem equivariant_record_card_le_sum
    {G n I B : Type*} [Group G] [Fintype n] [DecidableEq n] [Fintype I]
    [Fintype B] (U : G →* Matrix n n ℂ) (m : B → ℕ)
    (e : commutant U ≃ₐ[ℂ] ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ)
    (P : I → Matrix n n ℂ) (hrecord : CompleteOrthogonalIdempotents P)
    (hne : ∀ i, P i ≠ 0) (hequivariant : ∀ i g, P i * U g = U g * P i) :
    Fintype.card I ≤ ∑ b, m b := by
  classical
  let p : I → commutant U := fun i => equivariantElement U (P i) (hequivariant i)
  have hid (i : I) : IsIdempotentElem (p i) := Subtype.ext (hrecord.idem i).eq
  have hp : ∑ i, p i = 1 := by
    apply Subtype.ext
    change (commutant U).val (∑ i, p i) = (commutant U).val 1
    rw [map_sum, map_one]
    exact hrecord.complete
  apply matrix_blocks_card_le_sum m (fun i => e (p i))
  · exact fun i => (hid i).map e
  · intro i h
    exact hne i (congrArg Subtype.val (e.injective (h.trans e.map_zero.symm)))
  · rw [← map_sum, hp, map_one]

/-- Upstream Wedderburn–Artin supplies block sizes that bound every equivariant resolution. -/
theorem semisimple_commutant_has_record_capacity
    {G n : Type*} [Group G] [Fintype n] [DecidableEq n]
    (U : G →* Matrix n n ℂ) [IsSemisimpleRing (commutant U)] :
    ∃ (k : ℕ) (m : Fin k → ℕ), (∀ b, NeZero (m b)) ∧
      Nonempty (commutant U ≃ₐ[ℂ] ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ) ∧
      ∀ (I : Type) [Fintype I] (P : I → Matrix n n ℂ),
        CompleteOrthogonalIdempotents P → (∀ i, P i ≠ 0) →
        (∀ i g, P i * U g = U g * P i) → Fintype.card I ≤ ∑ b, m b := by
  classical
  obtain ⟨k, m, hm, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (commutant U)
  exact ⟨k, m, hm, ⟨e⟩, fun I _ P hrecord hne hequivariant =>
    equivariant_record_card_le_sum U m e P hrecord hne hequivariant⟩

end D5.S3.Quantum.Matrix.RecordCapacity
