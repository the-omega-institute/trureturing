import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9StarProjection

/-! The three-axis star block count for Q9 Problem 2. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9StarBlock

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip directionEdges direction_edge_count)
open Q9StarProjection (HasStarProjection)
open private AtCenter center_of_leaf every_center_is_full from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9StarProjection

attribute [local instance] Classical.propDecidable

/-- In a balanced induced cubic Q9 support with an all-false or singleton pattern
on three axes, suppose singleton membership is constant within each erased fibre.
Every selected all-false vertex then has all three singleton neighbours. Each
singleton layer has size `p` with `18 * p = 5 * C.card`, so `C.card = 6 * m`
forces `3 ∣ m`, and order 72 forces a half of size 20 on each chosen axis. -/
theorem star_block {C : Finset (Q 9)} {axes : Finset (Fin 9)}
    (haxes : axes.card = 3)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hstar : HasStarProjection C axes (fun _ => false))
    (hfibre : ∀ x : Q 9, (∀ a ∈ axes, x a = false) →
      ∀ a ∈ axes, ∀ b ∈ axes, flip x a ∈ C ↔ flip x b ∈ C) :
    (∀ x ∈ C, (∀ a ∈ axes, x a = false) → ∀ a ∈ axes, flip x a ∈ C) ∧
    (∀ a ∈ axes, 18 * (C.filter (fun x => x a = true)).card = 5 * C.card) ∧
    (∀ m : ℕ, C.card = 6 * m → 3 ∣ m) ∧
    (C.card = 72 → ∀ a ∈ axes, (C.filter (fun x => x a = true)).card = 20) := by
  classical
  have hfull (x : Q 9) (hx : x ∈ C) (hzero : ∀ a ∈ axes, x a = false)
      (a : Fin 9) (ha : a ∈ axes) : flip x a ∈ C :=
    every_center_is_full haxes hr hb hstar hx hzero ha
  obtain ⟨i, hi⟩ : axes.Nonempty := card_pos.mp (by omega)
  let Z := C.filter (AtCenter axes (fun _ => false))
  let L (a : Fin 9) := C.filter (fun x => x a = true)
  let M := (univ : Finset (Q 9)).filter
    (fun x => AtCenter axes (fun _ => false) x ∧ flip x i ∈ C)
  have hZedges : directionEdges C i = Z.card := by
    unfold directionEdges
    congr 1
    ext x
    simp only [Z, mem_filter]
    refine ⟨?_, fun ⟨hx, hz⟩ => ⟨hx, hz i hi, hfull x hx hz i hi⟩⟩
    rintro ⟨hx, hxi, hflip⟩
    have hleaf : flip x i i ≠ (fun _ : Fin 9 => false) i := by simp [hxi]
    have hz := center_of_leaf hstar hi hflip hleaf
    exact ⟨hx, by simpa only [BalancedCriticalSpectrum.flip_flip] using hz⟩
  have hZ : 6 * Z.card = C.card := by
    rw [← hZedges]
    exact direction_edge_count (d := 3) C hr hb i
  -- Erasing the singleton bit identifies every layer with the same set of bases.
  have hL (a : Fin 9) (ha : a ∈ axes) : (L a).card = M.card := by
    have hinv : Function.Involutive (fun x : Q 9 => flip x a) :=
      fun x => BalancedCriticalSpectrum.flip_flip x a
    apply card_bijective _ hinv.bijective
    intro x
    simp only [L, M, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hx, hxa⟩
      have hz := center_of_leaf hstar ha hx (by simp [hxa])
      exact ⟨hz, (hfibre _ hz a ha i hi).mp
        (by simpa only [BalancedCriticalSpectrum.flip_flip] using hx)⟩
    · rintro ⟨hz, hleaf⟩
      have hxa : flip x a a = false := hz a ha
      exact ⟨by simpa only [BalancedCriticalSpectrum.flip_flip] using
          (hfibre _ hz i hi a ha).mp hleaf,
        by simpa using hxa⟩
  have hdisj : (axes : Set (Fin 9)).PairwiseDisjoint L := by
    intro a ha b hb' hab
    apply disjoint_left.mpr
    intro x hxa hxb
    obtain ⟨hx, hxa⟩ := mem_filter.mp hxa
    have hfalse : x b = false := hstar x hx a b ha hb' hab (by simp [hxa])
    simpa [hfalse] using (mem_filter.mp hxb).2
  have hZdisj : Disjoint Z (axes.biUnion L) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, ha, hleaf⟩ := mem_biUnion.mp hy
    have hxa : x a = false := (mem_filter.mp hx).2 a ha
    simpa [hxa] using (mem_filter.mp hleaf).2
  have hcover : Z ∪ axes.biUnion L = C := by
    ext x
    simp only [mem_union, Z, L, mem_filter, mem_biUnion]
    constructor
    · rintro (⟨hx, _⟩ | ⟨a, ha, hx, _⟩) <;> exact hx
    · intro hx
      by_cases hz : AtCenter axes (fun _ => false) x
      · exact Or.inl ⟨hx, hz⟩
      · right
        by_contra hn
        apply hz
        intro a ha
        cases hxa : x a
        · rfl
        · exact False.elim (hn ⟨a, ha, hx, hxa⟩)
  have htotal : Z.card + 3 * M.card = C.card := by
    rw [← haxes, ← sum_const_nat hL, ← card_biUnion hdisj,
      ← card_union_of_disjoint hZdisj, hcover]
  have hcount (a : Fin 9) (ha : a ∈ axes) : 18 * (L a).card = 5 * C.card := by
    rw [hL a ha]
    omega
  refine ⟨hfull, hcount, ?_, ?_⟩
  · intro m hm
    have := hcount i hi
    omega
  · intro hC a ha
    have := hcount a ha
    change (L a).card = 20
    omega

#print axioms star_block

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9StarBlock
