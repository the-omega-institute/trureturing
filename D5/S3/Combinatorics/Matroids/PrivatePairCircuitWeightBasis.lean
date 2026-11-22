/- GID: D5/S3/Combinatorics/Matroids/PrivatePairCircuitWeightBasis
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/PrivatePairCircuitWeightBasis
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Private pairs give distinct zero-weight intersections for overlapping faces. -/

module

public import D5.S3.Combinatorics.Matroids.CircuitWeightBlocks

/-! Simultaneous weight coordinates for faces with private pairs. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.PrivatePairCircuitWeightBasis

open Finset CircuitWeightBlocks

set_option autoImplicit false

/-- If every face has two distinct indices belonging to no other face, an
integral change of basis preserves all faces and the pivot while separating
the faces by their intersections with the zero-weight indices. -/
theorem exists_private_pair_weight_basis {I J : Type*} [Finite I] [DecidableEq I]
    (F : J → Finset I) (root : I) (hroot : ∀ t, root ∉ F t)
    (hprivate : ∀ t, ∃ i ∈ F t, ∃ j ∈ F t, i ≠ j ∧
      ∀ s ≠ t, i ∉ F s ∧ j ∉ F s)
    (weight : I → ℕ) (hweight : ∀ i, 0 < weight i) :
    ∃ (b : Module.Basis I ℤ (I → ℤ)) (w : I → ℕ) (A : Finset I),
      (∀ i, b.equivFun (fun j => (weight j : ℤ)) i = (w i : ℤ)) ∧
      (∀ i ∈ A, w i = 0) ∧ root ∉ A ∧ Function.Injective (fun t => F t ∩ A) ∧
      (∀ t, ∀ i ∈ F t, ∀ j ∉ F t, b i j = 0 ∧ b.equivFun (Pi.single i 1) j = 0) ∧
      (∀ j ≠ root, b.equivFun (Pi.single root 1) j = 0) := by
  classical
  let _ := Fintype.ofFinite I
  let signature (i : I) : (J → Bool) × Bool := (fun t => decide (i ∈ F t), decide (i = root))
  let block (i : I) : Set.range signature := ⟨signature i, ⟨i, rfl⟩⟩
  have hsurj : Function.Surjective block := by
    rintro ⟨_, i, rfl⟩
    exact ⟨i, rfl⟩
  obtain ⟨b, z, _, hforward, hinverse, hcoords⟩ :=
    exists_weight_basis_by_fiber block hsurj weight hweight
  let w (i : I) :=
    if z (block i) = i then (univ.filter (fun j => block j = block i)).gcd weight else 0
  let A := (univ.filter fun i => w i = 0).erase root
  have passive (t : J) : ∃ i ∈ F t, i ∈ A ∧ ∀ s ≠ t, i ∉ F s := by
    obtain ⟨i, hi, j, hj, hij, hother⟩ := hprivate t
    have hiRoot : i ≠ root := fun h => hroot t (h ▸ hi)
    have hjRoot : j ≠ root := fun h => hroot t (h ▸ hj)
    have same : block i = block j := by
      apply Subtype.ext
      apply Prod.ext
      · funext s
        change decide (i ∈ F s) = decide (j ∈ F s)
        by_cases h : s = t
        · subst s
          simp [hi, hj]
        · simp [(hother s h).1, (hother s h).2]
      · change decide (i = root) = decide (j = root)
        simp [hiRoot, hjRoot]
    have memPassive {x : I} (hx : x ≠ root) (hz : w x = 0) : x ∈ A :=
      mem_erase.mpr ⟨hx, by simp [hz]⟩
    by_cases hz : z (block i) = i
    · exact ⟨j, hj, memPassive hjRoot (by simp [w, ← same, hz, hij]),
        fun s hs => (hother s hs).2⟩
    · exact ⟨i, hi, memPassive hiRoot (by simp [w, hz]), fun s hs => (hother s hs).1⟩
  refine ⟨b, w, A, fun i => by simpa only [w, Nat.cast_ite, Nat.cast_zero] using hcoords i,
    fun i hi => (mem_filter.mp (mem_of_mem_erase hi)).2, notMem_erase _ _, ?_, ?_, ?_⟩
  · intro s t h
    change F s ∩ A = F t ∩ A at h
    by_contra hne
    obtain ⟨i, hi, hA, hother⟩ := passive s
    have hs : i ∈ F s ∩ A := mem_inter.mpr ⟨hi, hA⟩
    rw [h] at hs
    exact hother t (fun he => hne he.symm) (mem_inter.mp hs).1
  · intro t i hi j hj
    have hne : block i ≠ block j := by
      intro he
      have hv := congrArg (fun s : Set.range signature => s.val.1 t) he
      simp [block, signature, hi, hj] at hv
    exact ⟨hforward i j hne, hinverse i j hne⟩
  · intro j hj
    apply hinverse
    intro he
    have hv := congrArg (fun s : Set.range signature => s.val.2) he
    simp [block, signature, hj] at hv

end D5.S3.Combinatorics.Matroids.PrivatePairCircuitWeightBasis
