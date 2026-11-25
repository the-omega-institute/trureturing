/- GID: D5/S3/Combinatorics/Matroids/SunflowerCircuitWeightBasis
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/SunflowerCircuitWeightBasis
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Disjoint petals have distinct intersections with the zero-weight indices. -/

module

public import D5.S3.Combinatorics.Matroids.CircuitWeightBlocks

/-! Weight coordinates adapted to disjoint petals and a common pivot. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.SunflowerCircuitWeightBasis

open Finset CircuitWeightBlocks

set_option autoImplicit false

/-- Disjoint petals of size at least two admit a simultaneous integral change of
basis that preserves each petal and the pivot, and leaves a zero-weight index
in every petal. -/
theorem exists_sunflower_weight_basis {I J : Type*} [Finite I] [DecidableEq I]
    (F : J → Finset I) (hdisjoint : Pairwise fun s t => Disjoint (F s) (F t))
    (hlarge : ∀ t, 1 < (F t).card) (root : I) (hroot : ∀ t, root ∉ F t)
    (weight : I → ℕ) (hweight : ∀ i, 0 < weight i) :
    ∃ (b : Module.Basis I ℤ (I → ℤ)) (w : I → ℕ) (A : Finset I),
      (∀ i, b.equivFun (fun j => (weight j : ℤ)) i = (w i : ℤ)) ∧
      (∀ i ∈ A, w i = 0) ∧ root ∉ A ∧ Function.Injective (fun t => F t ∩ A) ∧
      (∀ t, ∀ i ∈ F t, ∀ j ∉ F t,
        b i j = 0 ∧ b.equivFun (Pi.single i 1) j = 0) ∧
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
  have same_block {t : J} {i j : I} (hi : i ∈ F t) (hj : j ∈ F t) : block i = block j := by
    apply Subtype.ext
    apply Prod.ext
    · funext s
      change decide (i ∈ F s) = decide (j ∈ F s)
      by_cases hs : t = s
      · subst s
        simp [hi, hj]
      · have his : i ∉ F s := fun h => Finset.disjoint_left.mp (hdisjoint hs) hi h
        have hjs : j ∉ F s := fun h => Finset.disjoint_left.mp (hdisjoint hs) hj h
        simp [his, hjs]
    · have hir : i ≠ root := fun h => hroot t (h ▸ hi)
      have hjr : j ≠ root := fun h => hroot t (h ▸ hj)
      change decide (i = root) = decide (j = root)
      simp [hir, hjr]
  have passive (t : J) : ∃ i, i ∈ F t ∧ i ∈ A := by
    obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp (hlarge t)
    have hblock := same_block hi hj
    have hex : ∃ k ∈ F t, w k = 0 := by
      by_cases hz : z (block i) = i
      · exact ⟨j, hj, by simp [w, ← hblock, hz, hij]⟩
      · exact ⟨i, hi, by simp [w, hz]⟩
    obtain ⟨k, hk, hw⟩ := hex
    exact ⟨k, hk, mem_erase.mpr ⟨fun h => hroot t (h ▸ hk), by simp [hw]⟩⟩
  refine ⟨b, w, A, fun i => by simpa only [w, Nat.cast_ite, Nat.cast_zero] using hcoords i,
    fun i hi => (mem_filter.mp (mem_of_mem_erase hi)).2, notMem_erase _ _, ?_, ?_, ?_⟩
  · intro s t he
    change F s ∩ A = F t ∩ A at he
    by_contra hne
    obtain ⟨i, hi, hA⟩ := passive s
    have hiA : i ∈ F s ∩ A := mem_inter.mpr ⟨hi, hA⟩
    rw [he] at hiA
    exact Finset.disjoint_left.mp (hdisjoint hne) hi (mem_inter.mp hiA).1
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

end D5.S3.Combinatorics.Matroids.SunflowerCircuitWeightBasis
