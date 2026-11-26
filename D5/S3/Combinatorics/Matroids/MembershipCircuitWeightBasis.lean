/- GID: D5/S3/Combinatorics/Matroids/MembershipCircuitWeightBasis
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/MembershipCircuitWeightBasis
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Common-pivot omitted bases distinguished by membership classes. -/

module

public import D5.S3.Combinatorics.Matroids.CircuitWeightBlocks

/-! Weight coordinates distinguishing faces by shared membership classes. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.MembershipCircuitWeightBasis

open Finset CircuitWeightBlocks

set_option autoImplicit false

/-- A supported integral basis separates all faces on their zero-weight coordinates. -/
theorem exists_membership_separating_weight_basis {I J : Type*} [Finite I] [DecidableEq I]
    (F : J → Finset I) (root : I) (hroot : ∀ t, root ∉ F t)
    (hsep : ∀ s t, s ≠ t → ∃ i j, i ≠ j ∧
      (∀ u, i ∈ F u ↔ j ∈ F u) ∧
      ((i ∈ F s ∧ i ∉ F t) ∨ (i ∈ F t ∧ i ∉ F s)))
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
  have memPassive {x : I} (hx : x ≠ root) (hz : w x = 0) : x ∈ A :=
    mem_erase.mpr ⟨hx, by simp [hz]⟩
  refine ⟨b, w, A, fun i => by simpa only [w, Nat.cast_ite, Nat.cast_zero] using hcoords i,
    fun i hi => (mem_filter.mp (mem_of_mem_erase hi)).2, notMem_erase _ _, ?_, ?_, ?_⟩
  · intro s t he
    change F s ∩ A = F t ∩ A at he
    by_contra hne
    obtain ⟨i, j, hij, hsame, hdiff⟩ := hsep s t hne
    have hiRoot : i ≠ root := by
      intro hi
      rcases hdiff with hs | ht
      · exact hroot s (hi ▸ hs.1)
      · exact hroot t (hi ▸ ht.1)
    have hjRoot : j ≠ root := by
      intro hj
      rcases hdiff with hs | ht
      · exact hroot s (hj ▸ (hsame s).mp hs.1)
      · exact hroot t (hj ▸ (hsame t).mp ht.1)
    have hblock : block i = block j := by
      apply Subtype.ext
      apply Prod.ext
      · funext u
        change decide (i ∈ F u) = decide (j ∈ F u)
        by_cases hm : i ∈ F u
        · simp [hm, (hsame u).mp hm]
        · have hnot : j ∉ F u := fun hj => hm ((hsame u).mpr hj)
          simp [hm, hnot]
      · change decide (i = root) = decide (j = root)
        simp [hiRoot, hjRoot]
    have hpassive : ∃ x ∈ A, ∀ u, i ∈ F u ↔ x ∈ F u := by
      by_cases hz : z (block i) = i
      · exact ⟨j, memPassive hjRoot (by simp [w, ← hblock, hz, hij]), hsame⟩
      · exact ⟨i, memPassive hiRoot (by simp [w, hz]), fun _ => Iff.rfl⟩
    obtain ⟨x, hx, hxmem⟩ := hpassive
    have htest (u : J) : i ∈ F u ↔ x ∈ F u ∩ A := (hxmem u).trans (by simp [hx])
    have hst : i ∈ F s ↔ i ∈ F t := (htest s).trans (by rw [he]; exact (htest t).symm)
    exact hdiff.elim (fun hs => hs.2 (hst.mp hs.1)) (fun ht => ht.2 (hst.mpr ht.1))
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


end D5.S3.Combinatorics.Matroids.MembershipCircuitWeightBasis
