/- GID: D5/S3/ObserverMemory/InverseLimits/TraceRankCombinatorics
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/InverseLimits/TraceRankCombinatorics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Trace and range rank count periodic points and iterate images. -/

import Mathlib

/- Library-search audit trail (2026-08-18):
   * Repository searches for trace/fixed-point and rank/image operator identities found no equal
     or stronger theorem. `FunctionGraphSpectrumCollision` defines the two cardinality spectra,
     while `FiniteCapacity` contains a related pullback-space dimension result.
   * Pinned Mathlib supplies `Finsupp.lmapDomain_comp`, `Finsupp.range_lmapDomain`,
     `Finsupp.basisSingleOne`, `LinearMap.trace_eq_matrix_trace`, and
     `finrank_span_set_eq_card`; they are applied below. No complete combined theorem was found.
   * The `loogle` and `leansearch` executables were absent from PATH. -/

namespace D5.S3.ObserverMemory.InverseLimits.TraceRankCombinatorics

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

/-- The linear operator sending the basis vector at `y` to the basis vector at `tau y`. -/
noncomputable def transferOperator {Y : Type*} (tau : Y -> Y) :
    (Y →₀ ℂ) →ₗ[ℂ] (Y →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ tau

private theorem transferOperator_pow {Y : Type*} (tau : Y -> Y) (n : Nat) :
    transferOperator tau ^ n = Finsupp.lmapDomain ℂ ℂ (tau^[n]) := by
  induction n with
  | zero => simp [transferOperator, Module.End.one_eq_id]
  | succ n ih =>
      rw [pow_succ, ih, Module.End.mul_eq_comp]
      unfold transferOperator
      rw [<- Finsupp.lmapDomain_comp, Function.iterate_succ]

/-- For a self-map of a finite set, the trace of every positive transfer-operator power counts
its fixed points, while the range rank of every natural power counts its image. -/
theorem trace_rank_combinatorial_meaning
    {Y : Type*} [Finite Y]
    (tau : Y -> Y) (r : {n : Nat // 1 <= n}) (k : Nat) :
    LinearMap.trace ℂ (Y →₀ ℂ) (transferOperator tau ^ (r : Nat)) =
        (Nat.card {y : Y // (tau^[(r : Nat)]) y = y} : ℂ) /\
      Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k)) =
        Nat.card (Set.range (tau^[k])) := by
  classical
  letI := Fintype.ofFinite Y
  constructor
  · rw [transferOperator_pow, LinearMap.trace_eq_matrix_trace ℂ Finsupp.basisSingleOne]
    rw [Nat.card_eq_fintype_card]
    simp [Matrix.trace, LinearMap.toMatrix_apply, Finsupp.coe_basisSingleOne,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
      Finset.sum_boole, Fintype.card_subtype]
  · rw [transferOperator_pow, Finsupp.range_lmapDomain]
    have h_independent :
        LinearIndepOn ℂ id (Set.range fun y : Y => Finsupp.single y (1 : ℂ)) :=
      Finsupp.basisSingleOne.linearIndependent.linearIndepOn_id
    have h_subset :
        Set.range (fun y : Y => Finsupp.single ((tau^[k]) y) (1 : ℂ)) ⊆
          Set.range (fun y : Y => Finsupp.single y (1 : ℂ)) := by
      rintro _ ⟨y, rfl⟩
      exact ⟨(tau^[k]) y, rfl⟩
    rw [finrank_span_set_eq_card (h_independent.mono h_subset),
      Nat.card_eq_fintype_card, Set.toFinset_range, <- Set.toFinset_card,
      Set.toFinset_range]
    calc
      (Finset.univ.image (fun y => Finsupp.single ((tau^[k]) y) (1 : ℂ))).card =
          ((Finset.univ.image (tau^[k])).image
            (fun y => Finsupp.single y (1 : ℂ))).card := by
            change
              (Finset.univ.image
                ((fun y : Y => Finsupp.single y (1 : ℂ)) ∘ (tau^[k]))).card = _
            rw [Finset.image_image]
      _ = (Finset.univ.image (tau^[k])).card :=
        Finset.card_image_of_injective _ (Finsupp.single_left_injective one_ne_zero)

example : Nonempty (Fin 1) := ⟨0⟩

example :
    LinearMap.trace ℂ (Fin 1 →₀ ℂ)
        (transferOperator (fun x : Fin 1 => x) ^ 1) = 1 /\
      Module.finrank ℂ
          (LinearMap.range (transferOperator (fun x : Fin 1 => x) ^ 0)) = 1 := by
  simpa using trace_rank_combinatorial_meaning
    (tau := fun x : Fin 1 => x) (r := ⟨1, by omega⟩) (k := 0)

#print axioms trace_rank_combinatorial_meaning

end D5.S3.ObserverMemory.InverseLimits.TraceRankCombinatorics
