/- GID: D5/S3/Observer/Completion/BareTowerDimensionClassification
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/BareTowerDimensionClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bare orthogonal towers are classified by the Hilbert dimensions of their blocks. -/

import Mathlib.Analysis.InnerProductSpace.l2Space

/- Library-search audit trail (2026-08-28):
   * Current-tree searches for bare Hilbert towers, blockwise unitary classification,
     componentwise `lp` equivalences, and common-index Hilbert bases found no exact theorem.
   * Pinned Mathlib supplies `HilbertBasis`, `exists_hilbertBasis`, `HilbertBasis.repr`,
     `lp.memℓp`, and `lp.norm_eq_tsum_rpow`; each is applied directly below.
   * `OrthonormalBasis.equiv` is finite-dimensional, so it cannot classify the unrestricted
     terminal residual. The local bridge instead uses general Hilbert bases and the Hilbert sum. -/

namespace D5.S3.Observer.Completion.BareTowerDimensionClassification

open RCLike
open scoped ENNReal lp

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v

private def componentwiseLpEquiv
    {K I : Type*} [RCLike K]
    {Block Block' : I -> Type*}
    [forall i, NormedAddCommGroup (Block i)]
    [forall i, InnerProductSpace K (Block i)]
    [forall i, NormedAddCommGroup (Block' i)]
    [forall i, InnerProductSpace K (Block' i)]
    (equiv : forall i, Block i ≃ₗᵢ[K] Block' i) :
    lp Block 2 ≃ₗᵢ[K] lp Block' 2 where
  toFun f :=
    ⟨fun i => equiv i (f i), by
      apply memℓp_gen
      simpa using (lp.memℓp f).summable (by norm_num : 0 < (2 : ENNReal).toReal)⟩
  invFun f :=
    ⟨fun i => (equiv i).symm (f i), by
      apply memℓp_gen
      simpa using (lp.memℓp f).summable (by norm_num : 0 < (2 : ENNReal).toReal)⟩
  left_inv f := by
    apply lp.ext
    funext i
    exact (equiv i).symm_apply_apply (f i)
  right_inv f := by
    apply lp.ext
    funext i
    exact (equiv i).apply_symm_apply (f i)
  map_add' f g := by
    apply lp.ext
    funext i
    exact (equiv i).map_add (f i) (g i)
  map_smul' scalar f := by
    apply lp.ext
    funext i
    exact (equiv i).map_smul scalar (f i)
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
    congr 1
    apply tsum_congr
    intro i
    change ‖equiv i (f i)‖ ^ (2 : ENNReal).toReal =
      ‖f i‖ ^ (2 : ENNReal).toReal
    rw [(equiv i).norm_map]

private theorem componentwiseLpEquiv_single
    {K I : Type*} [RCLike K] [DecidableEq I]
    {Block Block' : I -> Type*}
    [forall i, NormedAddCommGroup (Block i)]
    [forall i, InnerProductSpace K (Block i)]
    [forall i, NormedAddCommGroup (Block' i)]
    [forall i, InnerProductSpace K (Block' i)]
    (equiv : forall i, Block i ≃ₗᵢ[K] Block' i) (i : I) (x : Block i) :
    componentwiseLpEquiv equiv (lp.single 2 i x) =
      lp.single 2 i (equiv i x) := by
  apply lp.ext
  funext j
  by_cases hji : j = i
  · subst j
    simp [componentwiseLpEquiv]
  · simp [componentwiseLpEquiv, lp.single_apply, hji]

/-- A bare tower is represented by its canonical Hilbert sum. The index `none` is the initial
block, `some (some n)` is shell `n`, and `some none` is the terminal residual. Tower equivalence
is a global unitary with a unitary computation rule on every canonical block. Equality of Hilbert
dimension is expressed independently by the existence of Hilbert bases with one common index.
The three source clauses classify the initial block, every shell, and the terminal residual. -/
theorem bare_tower_dimension_classification
    {K : Type u} [RCLike K]
    {Block Block' : Option (Option Nat) -> Type v}
    [forall i, NormedAddCommGroup (Block i)]
    [forall i, InnerProductSpace K (Block i)]
    [forall i, CompleteSpace (Block i)]
    [forall i, NormedAddCommGroup (Block' i)]
    [forall i, InnerProductSpace K (Block' i)]
    [forall i, CompleteSpace (Block' i)] :
    (exists globalUnitary : lp Block 2 ≃ₗᵢ[K] lp Block' 2,
      exists blockUnitary : forall i, Block i ≃ₗᵢ[K] Block' i,
        forall i x,
          globalUnitary (lp.single 2 i x) =
            lp.single 2 i (blockUnitary i x)) ↔
      ((exists index : Type v,
          Nonempty (HilbertBasis index K (Block none)) /\
            Nonempty (HilbertBasis index K (Block' none))) /\
        (forall n, exists index : Type v,
          Nonempty (HilbertBasis index K (Block (some (some n)))) /\
            Nonempty (HilbertBasis index K (Block' (some (some n))))) /\
        exists index : Type v,
          Nonempty (HilbertBasis index K (Block (some none))) /\
            Nonempty (HilbertBasis index K (Block' (some none)))) := by
  constructor
  · rintro ⟨_, blockUnitary, _⟩
    have sameDimension : forall i, exists index : Type v,
        Nonempty (HilbertBasis index K (Block i)) /\
          Nonempty (HilbertBasis index K (Block' i)) := by
      intro i
      obtain ⟨index, basis, _⟩ := exists_hilbertBasis (𝕜 := K) (E := Block i)
      refine ⟨index, ⟨basis⟩, ?_⟩
      exact ⟨HilbertBasis.ofRepr ((blockUnitary i).symm.trans basis.repr)⟩
    exact ⟨sameDimension none,
      fun n => sameDimension (some (some n)), sameDimension (some none)⟩
  · rintro ⟨initialDimension, shellDimension, residualDimension⟩
    rcases initialDimension with ⟨initialIndex, ⟨initialBasis⟩, ⟨initialBasis'⟩⟩
    rcases residualDimension with ⟨residualIndex, ⟨residualBasis⟩, ⟨residualBasis'⟩⟩
    choose shellIndex shellBasis shellBasis' using shellDimension
    let blockUnitary : forall i, Block i ≃ₗᵢ[K] Block' i := fun
      | none => initialBasis.repr.trans initialBasis'.repr.symm
      | some none => residualBasis.repr.trans residualBasis'.repr.symm
      | some (some n) =>
          (Classical.choice (shellBasis n)).repr.trans
            (Classical.choice (shellBasis' n)).repr.symm
    let globalUnitary : lp Block 2 ≃ₗᵢ[K] lp Block' 2 :=
      componentwiseLpEquiv blockUnitary
    refine ⟨globalUnitary, blockUnitary, ?_⟩
    intro i x
    exact componentwiseLpEquiv_single blockUnitary i x

/-- The carrier and equivalence side are inhabited by the constant real block family. -/
example :
    let Block : Option (Option Nat) -> Type := fun _ => Real
    exists globalUnitary : lp Block 2 ≃ₗᵢ[Real] lp Block 2,
      exists blockUnitary : forall i, Block i ≃ₗᵢ[Real] Block i,
        forall i x,
          globalUnitary (lp.single 2 i x) =
            lp.single 2 i (blockUnitary i x) := by
  dsimp only
  let blockUnitary : forall _ : Option (Option Nat), Real ≃ₗᵢ[Real] Real :=
    fun _ => LinearIsometryEquiv.refl Real Real
  let globalUnitary : lp (fun _ : Option (Option Nat) => Real) 2 ≃ₗᵢ[Real]
      lp (fun _ : Option (Option Nat) => Real) 2 :=
    componentwiseLpEquiv blockUnitary
  refine ⟨globalUnitary, blockUnitary, ?_⟩
  intro i x
  exact componentwiseLpEquiv_single blockUnitary i x

#print axioms bare_tower_dimension_classification

end

end D5.S3.Observer.Completion.BareTowerDimensionClassification
