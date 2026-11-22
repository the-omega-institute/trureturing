/- GID: D5/S3/Combinatorics/Matroids/CircuitWeightBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/CircuitWeightBlocks
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: An integral basis concentrates the weights on one index per partition block. -/

module

public import D5.S3.Combinatorics.Matroids.PuncturedCircuitWeightBasis

/-! A weight basis adapted to a partition of the circuit coordinates. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.CircuitWeightBlocks

open Finset PuncturedCircuitWeightBasis

set_option autoImplicit false

variable {I B : Type*} [Fintype I] [DecidableEq I] [DecidableEq B]

/-- Every fiber retains its coordinate span, and the weight on each fiber
is concentrated on a single basis vector with coefficient the fiber gcd. -/
theorem exists_weight_basis_by_fiber (block : I → B) (hblock : Function.Surjective block)
    (weight : I → ℕ) (hweight : ∀ i, 0 < weight i) :
    ∃ (b : Module.Basis I ℤ (I → ℤ)) (z : B → I),
      (∀ j, block (z j) = j) ∧
      (∀ i j, block i ≠ block j → b i j = 0) ∧
      (∀ i j, block i ≠ block j → b.equivFun (Pi.single i 1) j = 0) ∧
      ∀ i, b.equivFun (fun j => (weight j : ℤ)) i =
        if z (block i) = i then (univ.filter (fun j => block j = block i)).gcd weight else 0 := by
  classical
  let A : B → Finset I := fun j => univ.filter (fun i => block i = j)
  have hA (j : B) : (A j).Nonempty := by
    obtain ⟨i, hi⟩ := hblock j
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  choose inner z hz using fun j => weight_basis_on_set (A j) (hA j) weight hweight
  let index : (Σ j, A j) ≃ I :=
    (Equiv.sigmaCongrRight fun j => Equiv.subtypeEquivRight (fun i => by simp [A])).trans
      (Equiv.sigmaFiberEquiv block)
  let fibers := (LinearEquiv.piCongrLeft' ℤ (fun _ : I => ℤ) index.symm).trans
    (LinearEquiv.piCurry ℤ fun j (_ : A j) => ℤ)
  let coordinates := fibers.trans
    ((LinearEquiv.piCongrRight fun j => (inner j).equivFun).trans fibers.symm)
  let b := (Pi.basisFun ℤ I).map coordinates.symm
  have hmem (j : B) (i : A j) : block i.val = j := (mem_filter.mp i.prop).2
  have hvars (v : I → ℤ) (j : B) (i : A j) : fibers v j i = v i.val := rfl
  have hb (i : I) : coordinates (b i) = Pi.single i 1 := by
    rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
    funext k
    by_cases h : i = k <;> simp [Pi.basisFun, h]
  have hin (i : I) (j : B) : (inner j).equivFun (fibers (b i) j) =
      fibers (Pi.single i 1) j := by
    have h := congrArg (fun v => fibers v j) (hb i)
    change fibers (fibers.symm (fun a => (inner a).equivFun (fibers (b i) a))) j = _ at h
    rw [fibers.apply_symm_apply] at h
    exact h
  let label (i : I) : A (block i) := ⟨i, by simp [A]⟩
  have hread (i : I) (v : ∀ a, A a → ℤ) : fibers.symm v i = v (block i) (label i) := by
    have h := congrArg (fun f => f (block i) (label i)) (fibers.apply_symm_apply v)
    simpa only [hvars, label] using h
  have hzero (i j : I) (hij : block i ≠ block j) :
      fibers (Pi.single i (1 : ℤ)) (block j) = 0 := by
    funext k
    rw [hvars]
    have hki : k.val ≠ i := fun h => hij ((congrArg block h).symm.trans (hmem (block j) k))
    simp [hki]
  refine ⟨b, fun j => (z j).val, fun j => hmem j (z j), ?_, ?_, ?_⟩
  · intro i j hij
    have h := (inner (block j)).equivFun.injective
      ((hin i (block j)).trans ((hzero i j hij).trans (map_zero _).symm))
    have h' := congrFun h (label j)
    simpa only [hvars, Pi.zero_apply] using h'
  · intro i j hij
    change fibers.symm (fun a => (inner a).equivFun (fibers (Pi.single i 1) a)) j = 0
    rw [hread, hzero i j hij, map_zero]
    rfl
  · intro i
    change fibers.symm (fun a => (inner a).equivFun (fibers (fun t => (weight t : ℤ)) a)) i = _
    rw [hread]
    have h : fibers (fun a => (weight a : ℤ)) (block i) =
        (fun a : A (block i) => (weight a.val : ℤ)) := rfl
    rw [h, hz (block i), map_smul, Pi.smul_apply, Module.Basis.equivFun_self]
    have hk : z (block i) = label i ↔ (z (block i)).val = i := Subtype.ext_iff
    simp [hk, A]

omit [Fintype I] in
/-- A change of basis preserving each side of a coordinate subset in both
directions preserves the vanishing of the alternating coefficient there. -/
theorem tuple_vanishing_iff_of_supported_change {J N : Type*} [Finite I] [Finite J] [AddCommGroup N]
    (F : Finset I) (b : Module.Basis I ℤ (I → ℤ)) (e : J ≃ F)
    (hforward : ∀ i ∈ F, ∀ j ∉ F, b i j = 0)
    (hbackward : ∀ i ∈ F, ∀ j ∉ F, b.equivFun (Pi.single i 1) j = 0)
    (f : (I → ℤ) [⋀^J]→ₗ[ℤ] N) :
    f (fun i => Pi.single (e i : I) 1) = 0 ↔ f (fun i => b (e i : I)) = 0 := by
  let standard := Pi.basisFun ℤ I
  let old : F → I → ℤ := fun i => standard i.val
  let new : F → I → ℤ := fun i => b i.val
  have hold : Set.range old = standard '' (F : Set I) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.prop, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hnew : Set.range new = b '' (F : Set I) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.prop, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hspan : Submodule.span ℤ (Set.range old) = Submodule.span ℤ (Set.range new) := by
    rw [hold, hnew]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      change standard i ∈ Submodule.span ℤ (b '' (F : Set I))
      rw [b.mem_span_image, Finsupp.support_subset_iff]
      intro j hj
      simpa [standard] using hbackward i hi j hj
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      exact Pi.mem_spanSubset_iff.mpr (hforward i hi)
  let oldBasis : Module.Basis F ℤ (Submodule.span ℤ (Set.range old)) :=
    Module.Basis.span (standard.linearIndependent.comp Subtype.val Subtype.val_injective)
  let newBasis : Module.Basis F ℤ (Submodule.span ℤ (Set.range new)) :=
    Module.Basis.span (b.linearIndependent.comp Subtype.val Subtype.val_injective)
  have hOld : f (fun i => Pi.single (e i : I) 1) = 0 ↔
      f.compLinearMap (Submodule.span ℤ (Set.range old)).subtype = 0 := by
    rw [eq_zero_iff_basis_tuple e oldBasis]
    simp [oldBasis, old, standard, Function.comp_def]
  have hNew : f (fun i => b (e i : I)) = 0 ↔
      f.compLinearMap (Submodule.span ℤ (Set.range new)).subtype = 0 := by
    rw [eq_zero_iff_basis_tuple e newBasis]
    simp [newBasis, new, Function.comp_def]
  rw [hOld, hNew, hspan]

end D5.S3.Combinatorics.Matroids.CircuitWeightBlocks
