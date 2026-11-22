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
  refine ⟨b, fun j => (z j).val, fun j => hmem j (z j), ?_, ?_⟩
  · intro i j hij
    have hzero : fibers (Pi.single i (1 : ℤ)) (block j) = 0 := by
      funext k
      rw [hvars]
      have hki : k.val ≠ i := fun h => hij ((congrArg block h).symm.trans (hmem (block j) k))
      simp [hki]
    have h := (inner (block j)).equivFun.injective
      ((hin i (block j)).trans (hzero.trans (map_zero _).symm))
    have hj : j ∈ A (block j) := by simp [A]
    have h' := congrFun h (⟨j, hj⟩ : A (block j))
    simpa only [hvars, Pi.zero_apply] using h'
  · intro i
    let j := block i
    let k : A j := ⟨i, by simp [A, j]⟩
    change coordinates (fun a => (weight a : ℤ)) i = _
    have hread (v : ∀ a, A a → ℤ) : fibers.symm v i = v j k := by
      have h := congrArg (fun f => f j k) (fibers.apply_symm_apply v)
      simpa only [hvars, k] using h
    change fibers.symm (fun a => (inner a).equivFun (fibers (fun t => (weight t : ℤ)) a)) i = _
    rw [hread]
    have h : fibers (fun a => (weight a : ℤ)) j = (fun a : A j => (weight a.val : ℤ)) := rfl
    rw [h, hz j, map_smul, Pi.smul_apply, Module.Basis.equivFun_self]
    have hk : z j = k ↔ (z j).val = i := Subtype.ext_iff
    simp [hk, A, j]

end D5.S3.Combinatorics.Matroids.CircuitWeightBlocks
