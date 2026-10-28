/- GID: D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.claim; result=D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.result; claim=D5/S3/Quantum/Matrix/Toeplitz/FactorizationRefutation.claim
   digest: A common field of definition obstructs uniformly short Toeplitz products up to invertible left multiplication. -/

import D5.S3.Combinatorics.Matroids.LinearRado
import D5.S3.Weil.TestFunctions.LiCurvatureCriterion
import Mathlib.RingTheory.AlgebraicIndependent.RankAndCardinality
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Cardinal IntermediateField
open scoped BigOperators IntermediateField.algebraAdjoinAdjoin

namespace D5.S3.Quantum.Matrix.Toeplitz.FactorizationRefutation

/-- Equality on every pair of adjacent entries of an ordinary diagonal. -/
def IsOrdinaryToeplitz {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ (i j : Fin n) (hi : i.val + 1 < n) (hj : j.val + 1 < n),
    T i j = T ⟨i.val + 1, hi⟩ ⟨j.val + 1, hj⟩

/-- The dimension-uniform single-left-multiplier assertion in Conjecture 5.1. -/
def claim : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
    ∀ M : Matrix (Fin n) (Fin n) ℂ,
      ∃ (P : Matrix (Fin n) (Fin n) ℂ)
        (T : Fin C → Matrix (Fin n) (Fin n) ℂ),
        IsUnit P ∧ (∀ k, IsOrdinaryToeplitz (T k)) ∧
          M = P * (List.ofFn T).prod

private lemma exists_independent (ι : Type) [Fintype ι] :
    ∃ x : ι → ℂ, AlgebraicIndependent ℚ x := by
  classical
  have huncount : ¬ #ℂ ≤ ℵ₀ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum.not_ge
  have hna : ¬ Algebra.IsAlgebraic ℚ ℂ := by
    intro h
    letI := h
    apply huncount
    exact (Algebra.IsAlgebraic.cardinalMk_le_max ℚ ℂ).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ ℂ
  haveI : Nonempty s := hs.nonempty_iff_transcendental.mpr
    (Algebra.transcendental_iff_not_isAlgebraic.mpr hna)
  have hcard : ℵ₀ ≤ #s := by
    by_contra h
    have hsmall : #s ≤ ℵ₀ := (lt_of_not_ge h).le
    have heq : #ℂ = max (max #ℚ #s) ℵ₀ := by
      simpa only [Cardinal.lift_id, sup_eq_max] using hs.lift_cardinalMk_eq_max_lift
    exact huncount (heq.trans_le (max_le (max_le Cardinal.mk_le_aleph0 hsmall) le_rfl))
  obtain ⟨f⟩ : Nonempty (ι ↪ s) := Cardinal.lift_mk_le'.mp (by
    simpa only [Cardinal.lift_id] using (Cardinal.mk_lt_aleph0 ι).le.trans hcard)
  exact ⟨fun i => (f i : ℂ), hs.1.comp f f.injective⟩

private lemma generated_field_trdeg {ι : Type} [Fintype ι] (g : ι → ℂ) :
    Algebra.trdeg ℚ (IntermediateField.adjoin ℚ (Set.range g)) ≤ (Fintype.card ι : Cardinal) := by
  classical
  let K := IntermediateField.adjoin ℚ (Set.range g)
  let gK : ι → K := fun i => ⟨g i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩
  let J := IntermediateField.adjoin ℚ (Set.range gK)
  have hJ : J = ⊤ := by
    apply (IntermediateField.lift_injective K)
    change IntermediateField.lift (IntermediateField.adjoin ℚ (Set.range gK)) =
      IntermediateField.lift (⊤ : IntermediateField ℚ K)
    rw [IntermediateField.lift_adjoin]
    have himage : Subtype.val '' Set.range gK = Set.range g := by
      ext x
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨gK i, ⟨i, rfl⟩, rfl⟩
    rw [himage]
    ext x
    simp only [K, IntermediateField.lift, IntermediateField.mem_map,
      IntermediateField.mem_top, true_and]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩
  let A := Algebra.adjoin ℚ (Set.range gK)
  letI : Algebra.IsAlgebraic A K := ⟨fun x => by
    let y : J := ⟨x, by rw [hJ]; trivial⟩
    exact (Algebra.IsAlgebraic.isAlgebraic (R := A) y).algHom
      (IsScalarTower.toAlgHom A J K)⟩
  exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ (Set.range gK)).trans
    (by simpa only [Cardinal.mk_fintype] using Cardinal.mk_range_le gK)

end D5.S3.Quantum.Matrix.Toeplitz.FactorizationRefutation
