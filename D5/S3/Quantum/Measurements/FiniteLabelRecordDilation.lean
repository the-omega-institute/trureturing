/- GID: D5/S3/Quantum/Measurements/FiniteLabelRecordDilation
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/FiniteLabelRecordDilation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp memory dimension for perfect finite label records with a pure environment. -/

import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set

/-! Perfect readout of a supported basis label by a memory with a finite pure environment. -/

open scoped BigOperators DirectSum ComplexOrder MatrixOrder InnerProductSpace

namespace D5.S3.Quantum.Measurements.FiniteLabelRecordDilation

open Matrix

variable {B J : Type*} [Fintype B] [DecidableEq B] [Fintype J]

private abbrev Fiber {P : Set B} (label : P → J) (j : J) := {b : P // label b = j}

/-- The memory slots required by the individual label classes. -/
noncomputable def memorySlots {P : Set B} (label : P → J) (e : ℕ) : ℕ :=
  ∑ j, Nat.card (Fiber label j) ⌈/⌉ e

def slice {d e : ℕ} (V : Matrix (Fin d × Fin e) B ℂ) (b : B) (t : Fin e) :
    Fin d → ℂ :=
  fun m => V (m, t) b

/-- The partial trace over the pure Stinespring environment of the outer product
of the joint basis column at `b`. -/
def reducedColumn {d e : ℕ} (V : Matrix (Fin d × Fin e) B ℂ) (b : B) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ t, vecMulVec (slice V b t) (star (slice V b t))

/-- A full-input isometry and a memory POVM that reads every supported label
with probability one. The extra outcome allows unused memory even for an empty label type. -/
def HasPerfectLabelRecord {P : Set B} (label : P → J) (d e : ℕ) : Prop :=
  ∃ (V : Matrix (Fin d × Fin e) B ℂ) (E : Option J → Matrix (Fin d) (Fin d) ℂ),
    Vᴴ * V = 1 ∧ (∀ j, (E j).PosSemidef) ∧ (∑ j, E j) = 1 ∧
      ∀ b : P, (E (some (label b)) * reducedColumn V b).trace = 1

omit [Fintype B] [DecidableEq B] in
theorem trace_mul_reducedColumn {d e : ℕ}
    (V : Matrix (Fin d × Fin e) B ℂ) (b : B) (A : Matrix (Fin d) (Fin d) ℂ) :
    (A * reducedColumn V b).trace = ∑ t, star (slice V b t) ⬝ᵥ (A *ᵥ slice V b t) := by
  simp only [reducedColumn, Finset.mul_sum, Matrix.trace_sum, Matrix.mul_vecMulVec,
    Matrix.trace_vecMulVec, dotProduct_comm]

omit [Fintype B] in
theorem reducedColumn_trace {d e : ℕ}
    (V : Matrix (Fin d × Fin e) B ℂ) (hV : Vᴴ * V = 1) (b : B) :
    (reducedColumn V b).trace = 1 := by
  have h := congrArg (fun M : Matrix B B ℂ => M b b) hV
  rw [← one_mul (reducedColumn V b), trace_mul_reducedColumn]
  simp only [one_mulVec, dotProduct]
  rw [Finset.sum_comm]
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, slice] using h

private theorem columns_independent {d e : ℕ}
    (V : Matrix (Fin d × Fin e) B ℂ) (hV : Vᴴ * V = 1) :
    LinearIndependent ℂ (fun b cell => V cell b) := by
  have hInjective : Function.Injective V.mulVecLin := by
    apply Function.LeftInverse.injective (g := Vᴴ.mulVecLin)
    intro x
    change Vᴴ *ᵥ (V *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, hV, Matrix.one_mulVec]
  change LinearIndependent ℂ V.col
  simpa [Function.comp_def] using
    ((Pi.basisFun ℂ B).linearIndependent.map' V.mulVecLin
      (LinearMap.ker_eq_bot.mpr hInjective))

private theorem slots_necessary {P : Set B} {label : P → J} {d e : ℕ} (he : 0 < e)
    (h : HasPerfectLabelRecord label d e) :
    Fintype.card B ≤ d * e ∧ memorySlots label e ≤ d := by
  classical
  obtain ⟨V, E, hV, hE, hSum, hRead⟩ := h
  have hColumns := columns_independent V hV
  refine ⟨?_, ?_⟩
  · simpa [Module.finrank_pi, Fintype.card_prod] using hColumns.fintype_card_le_finrank
  let M : J → Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
    fun j => LinearMap.ker (1 - E (some j)).toEuclideanLin
  have hUpper (j : Option J) : E j ≤ 1 := by
    rw [← hSum]
    exact Finset.single_le_sum (fun k _ => (hE k).nonneg) (Finset.mem_univ j)
  have hFix (j : J) (x : M j) :
      (E (some j)).toEuclideanLin x = (x : EuclideanSpace ℂ (Fin d)) := by
    have hx : (1 - E (some j)).toEuclideanLin x = 0 := x.property
    have hx' : (x : EuclideanSpace ℂ (Fin d)) - (E (some j)).toEuclideanLin x = 0 := by
      simpa only [map_sub, Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.sub_apply,
        LinearMap.id_apply] using hx
    exact (sub_eq_zero.mp hx').symm
  have hOrth : OrthogonalFamily ℂ (fun j => M j) (fun j => (M j).subtypeₗᵢ) := by
    intro i j hij x y
    have hLe : E (some i) ≤ 1 - E (some j) := by
      have hErase := Finset.sum_erase_add Finset.univ E (Finset.mem_univ (some j))
      rw [hSum] at hErase
      rw [← eq_sub_of_add_eq hErase]
      exact Finset.single_le_sum (fun k _ => (hE k).nonneg)
        (Finset.mem_erase.mpr ⟨by simpa using hij, Finset.mem_univ _⟩)
    let v : Fin d → ℂ := WithLp.ofLp (y : EuclideanSpace ℂ (Fin d))
    have hy : (1 - E (some j)) *ᵥ v = 0 := by
      have hy' : WithLp.toLp 2 ((1 - E (some j)) *ᵥ v) = 0 := y.property
      exact congrArg WithLp.ofLp hy'
    have hZero : star v ⬝ᵥ (E (some i) *ᵥ v) = 0 := by
      have hNonneg := (hE (some i)).dotProduct_mulVec_nonneg v
      have hDiff := (Matrix.le_iff.mp hLe).dotProduct_mulVec_nonneg v
      rw [Matrix.sub_mulVec, dotProduct_sub, hy, dotProduct_zero, zero_sub, neg_nonneg] at hDiff
      exact le_antisymm hDiff hNonneg
    have hKill : (E (some i)).toEuclideanLin y = 0 := by
      have hv := (hE (some i)).dotProduct_mulVec_zero_iff.mp hZero
      change WithLp.toLp 2 (E (some i) *ᵥ v) = 0
      rw [hv]
      rfl
    change ⟪(x : EuclideanSpace ℂ (Fin d)), (y : EuclideanSpace ℂ (Fin d))⟫_ℂ = 0
    rw [← hFix i x, (Matrix.isSymmetric_toEuclideanLin_iff.mpr (hE (some i)).isHermitian) _ _,
      hKill, inner_zero_right]
  have hDim : (∑ j, Module.finrank ℂ (M j)) ≤ d := by
    have h : Module.finrank ℂ (⨁ j, M j) ≤ Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) :=
      LinearMap.finrank_le_finrank_of_injective hOrth.independent.dfinsupp_lsum_injective
    simpa only [Module.finrank_directSum, finrank_euclideanSpace_fin] using h
  refine (Finset.sum_le_sum fun j _ => (ceilDiv_le_iff_le_mul he).2 ?_).trans hDim
  let (j : J) : Fintype (Fiber label j) := Fintype.ofFinite _
  have hSlice (j : J) (b : Fiber label j) (t : Fin e) :
      WithLp.toLp 2 (slice V b.1.1 t) ∈ M j := by
    let A := 1 - E (some j)
    have hA : A.PosSemidef := Matrix.le_iff.mp (hUpper (some j))
    have hTrace : (A * reducedColumn V b.1.1).trace = 0 := by
      rw [sub_mul, one_mul, Matrix.trace_sub, reducedColumn_trace V hV]
      have hb := hRead b.1
      rw [b.property] at hb
      rw [hb, sub_self]
    rw [trace_mul_reducedColumn] at hTrace
    have hZero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun t _ => hA.dotProduct_mulVec_nonneg (slice V b.1.1 t))).mp hTrace t
      (Finset.mem_univ t)
    have hv := hA.dotProduct_mulVec_zero_iff.mp hZero
    change WithLp.toLp 2 (A *ᵥ slice V b.1.1 t) = 0
    rw [hv]
    rfl
  let column (b : Fiber label j) : Fin e → M j :=
    fun t => ⟨WithLp.toLp 2 (slice V b.1.1 t), hSlice j b t⟩
  let forget : (Fin e → M j) →ₗ[ℂ] ((Fin d × Fin e) → ℂ) :=
    { toFun := fun f cell => WithLp.ofLp (f cell.2 : EuclideanSpace ℂ (Fin d)) cell.1
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hRestricted : LinearIndependent ℂ (fun b : Fiber label j => fun cell => V cell b.1.1) :=
    hColumns.comp _ (Subtype.val_injective.comp Subtype.val_injective)
  have hInd : LinearIndependent ℂ column := LinearIndependent.of_comp forget hRestricted
  have hCount := hInd.fintype_card_le_finrank
  rw [← Nat.card_eq_fintype_card (α := Fiber label j), Module.finrank_pi_fintype] at hCount
  simpa using hCount

theorem extend_into_joint_basis {A C : Type*} [Fintype A] [Fintype C]
    (P : Set A) (f : P ↪ C) (h : Fintype.card A ≤ Fintype.card C) :
    ∃ g : A ↪ C, ∀ b : P, g b = f b := by
  classical
  let : Fintype P := Fintype.ofFinite P
  let : Fintype (↥Pᶜ) := Fintype.ofFinite _
  let : Fintype (Set.range f) := Fintype.ofFinite _
  let : Fintype (↥(Set.range f)ᶜ) := Fintype.ofFinite _
  have hCard : Fintype.card (Set.range f) = Fintype.card P :=
    (Fintype.card_congr (Equiv.ofInjective f f.injective)).symm
  have hFree : Fintype.card (↥Pᶜ) ≤ Fintype.card (↥(Set.range f)ᶜ) := by
    rw [Fintype.card_compl_set, Fintype.card_compl_set, hCard]
    exact Nat.sub_le_sub_right h _
  let g₀ := (Function.Embedding.nonempty_of_card_le hFree).some
  let g := (Equiv.Set.sumCompl P).symm.toEmbedding.trans
    (((Equiv.ofInjective f f.injective).toEmbedding.sumMap g₀).trans
      (Equiv.Set.sumCompl (Set.range f)).toEmbedding)
  exact ⟨g, fun b => by simp [g]⟩

omit [Fintype B] in
private theorem record_of_basis_embedding {P : Set B} {label : P → J} {d e : ℕ}
    (g : B ↪ (Fin d × Fin e)) (read : Fin d → Option J)
    (hRead : ∀ b : P, read (g b).1 = some (label b)) :
    HasPerfectLabelRecord label d e := by
  classical
  let V : Matrix (Fin d × Fin e) B ℂ := fun cell b => if cell = g b then 1 else 0
  let E (j : Option J) : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal fun m => if read m = j then 1 else 0
  refine ⟨V, E, ?_, ?_, ?_, ?_⟩
  · ext b c
    rw [Matrix.mul_apply, Finset.sum_eq_single (g b)]
    · rw [Matrix.conjTranspose_apply]
      change star (if g b = g b then (1 : ℂ) else 0) *
        (if g b = g c then 1 else 0) = (1 : Matrix B B ℂ) b c
      simp only [g.injective.eq_iff, ite_true, star_one, one_mul, Matrix.one_apply]
    · intro cell _ hn
      rw [Matrix.conjTranspose_apply, show V cell b = 0 from ite_eq_right hn, star_zero, zero_mul]
    · simp
  · intro j
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro m
    split <;> simp
  · ext m n
    by_cases h : m = n
    · subst n
      simp only [Matrix.sum_apply, E, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      simpa only [eq_comm] using (Finset.sum_ite_eq (s := Finset.univ) (a := read m)
        (b := fun _ => (1 : ℂ))).trans (ite_eq_left (Finset.mem_univ _))
    · simp [E, Matrix.sum_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  · intro b
    have hCell : read (g b).1 = some (label b) := hRead b
    rw [trace_mul_reducedColumn]
    rw [Finset.sum_eq_single (g b).2]
    · simp only [E, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply]
      rw [Finset.sum_eq_single (g b).1]
      · have hEntry : slice V b (g b).2 (g b).1 = 1 := ite_eq_left rfl
        simp only [hEntry, hCell, ite_true, star_one, mul_one]
      · intro m _ hm
        have hEntry : slice V b (g b).2 m = 0 :=
          ite_eq_right (fun h => hm (congrArg Prod.fst h))
        rw [hEntry, star_zero, zero_mul]
      · simp
    · intro t _ ht
      have hSliceZero : slice V b t = 0 := by
        funext m
        exact ite_eq_right (fun h => ht (congrArg Prod.snd h))
      rw [hSliceZero, Matrix.mulVec_zero, dotProduct_zero]
    · simp

private theorem record_of_slots {P : Set B} {label : P → J} {d e : ℕ} (he : 0 < e)
    (hGlobal : Fintype.card B ≤ d * e) (hSlots : memorySlots label e ≤ d) :
    HasPerfectLabelRecord label d e := by
  classical
  let r (j : J) := Nat.card (Fiber label j) ⌈/⌉ e
  let block : (Σ j, Fin (r j)) ↪ Fin d := (Function.Embedding.nonempty_of_card_le (by
    simpa [r, memorySlots, Fintype.card_sigma] using hSlots)).some
  let (j : J) : Fintype (Fiber label j) := Fintype.ofFinite _
  let cells (j : J) : Fiber label j ↪ (Fin (r j) × Fin e) :=
    (Function.Embedding.nonempty_of_card_le (by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, ← Nat.card_eq_fintype_card]
      simpa [Nat.mul_comm] using (ceilDiv_le_iff_le_mul he).mp (le_refl (r j)))).some
  let pack : P ↪ (Fin d × Fin e) :=
    (Equiv.sigmaFiberEquiv label).symm.toEmbedding.trans
      ((Function.Embedding.sigmaMap (Function.Embedding.refl J) cells).trans
        ((Equiv.sigmaProdDistrib (fun j => Fin (r j)) (Fin e)).symm.toEmbedding.trans
          (block.prodMap (Function.Embedding.refl (Fin e)))))
  obtain ⟨g, hg⟩ := extend_into_joint_basis P pack (by simpa using hGlobal)
  let read (m : Fin d) : Option J :=
    if hm : m ∈ Set.range block then
      some ((Equiv.ofInjective block block.injective).symm ⟨m, hm⟩).1
    else none
  have hReadBlock (x : Σ j, Fin (r j)) : read (block x) = some x.1 := by
    have hx : block x ∈ Set.range block := ⟨x, rfl⟩
    rw [show read (block x) = some ((Equiv.ofInjective block block.injective).symm
      (⟨block x, hx⟩ : Set.range block)).1 by simp only [read, dite_eq_left hx]]
    exact congrArg (fun y => some y.1)
      ((Equiv.ofInjective block block.injective).symm_apply_apply x)
  apply record_of_basis_embedding g read
  intro b
  rw [hg]
  exact hReadBlock _

/-- An actual finite isometric encoder with pure environment of dimension `e`
admits a perfect memory label measurement exactly when all input coordinates fit
jointly and the individual rounded label blocks fit in memory. -/
theorem perfectLabelRecord_iff {P : Set B} (label : P → J) {d e : ℕ} (he : 0 < e) :
    HasPerfectLabelRecord label d e ↔ Fintype.card B ≤ d * e ∧ memorySlots label e ≤ d :=
  ⟨slots_necessary he, fun h => record_of_slots he h.1 h.2⟩

private def threeOneLabel (b : (Set.univ : Set (Fin 4))) : Bool :=
  b.1 == (3 : Fin 4)

/-- The joint budget and the number of labels alone allow this instance,
but the two classes require three memory coordinates. -/
private theorem joint_and_label_counts_insufficient :
    Fintype.card (Fin 4) ≤ 2 * 2 ∧ Fintype.card Bool ≤ 2 ∧
      ¬ HasPerfectLabelRecord threeOneLabel 2 2 := by
  have hThree : Nat.card (Fiber threeOneLabel false) = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hOne : Nat.card (Fiber threeOneLabel true) = 1 := by
    rw [Nat.card_eq_fintype_card]
    decide
  refine ⟨by decide, by decide, fun h => ?_⟩
  have hSlots := ((perfectLabelRecord_iff threeOneLabel (by decide)).mp h).2
  rw [memorySlots, Fintype.sum_bool, hThree, hOne] at hSlots
  exact (by decide : ¬ (3 ⌈/⌉ 2 + 1 ⌈/⌉ 2 ≤ 2)) hSlots

#print axioms perfectLabelRecord_iff
#print axioms joint_and_label_counts_insufficient

end D5.S3.Quantum.Measurements.FiniteLabelRecordDilation
