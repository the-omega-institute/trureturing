/- GID: D5/S3/Combinatorics/Graph/URSComponentParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/URSComponentParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.DegreeSum]
   utility: none
   digest: Two-element fibres and reflected counts force odd-order array connectivity. -/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.URSComponentParity

open Finset

/-- The actual column-symbol fibre in one indexed permutation array. -/
def fibre {n : ℕ} (ρ : Fin (2 * n) → Equiv.Perm (Fin n)) (x p : Fin n) :
    Finset (Fin (2 * n)) := univ.filter fun i => ρ i x = p

/-- Joint counts use the same actual row indices as the fibres. -/
def pairCount {n : ℕ} (ρ : Fin (2 * n) → Equiv.Perm (Fin n))
    (x y p q : Fin n) : ℕ :=
  (univ.filter fun i => ρ i x = p ∧ ρ i y = q).card

/-- Distinct row indices are joined when they share an actual cell fibre. -/
def fibreGraph {n : ℕ} (ρ : Fin (2 * n) → Equiv.Perm (Fin n)) :
    SimpleGraph (Fin (2 * n)) where
  Adj i j := i ≠ j ∧ ∃ x, ρ i x = ρ j x
  symm := ⟨by rintro i j ⟨hne, x, hx⟩; exact ⟨hne.symm, x, hx.symm⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

/-- Odd-order uniform reflected arrays have a connected graph on their original row indices.
The conclusion requires neither an identity first row nor lexicographic sorting. -/
theorem fibre_graph_connected {n : ℕ} (hn : Odd n) (hn3 : 3 ≤ n)
    (ρ : Fin (2 * n) → Equiv.Perm (Fin n))
    (hf : ∀ x p, (fibre ρ x p).card = 2)
    (hr : ∀ x y p q, x ≠ y → p ≠ q →
      pairCount ρ x y p q = pairCount ρ x y q p) :
    (fibreGraph ρ).Connected := by
  classical
  let x₀ : Fin n := ⟨0, by omega⟩
  have cut_four : ∀ S : Finset (Fin (2 * n)), (∃ i, i ∉ S) →
      (∀ i ∈ S, ∀ j x, ρ i x = ρ j x → j ∈ S) → 4 ∣ S.card := by
    intro S hproper hclosed
    obtain ⟨i, hi⟩ := hproper
    let P : Fin n → Finset (Fin n) := fun x => S.image fun j => ρ j x
    have hP : ∀ x j, ρ j x ∈ P x ↔ j ∈ S := by
      intro x j
      constructor
      · rintro hj
        obtain ⟨k, hk, heq⟩ := mem_image.mp hj
        exact hclosed k hk j x heq
      · intro hj
        exact mem_image_of_mem (fun k => ρ k x) hj
    have hsize : ∀ x, S.card = (P x).card * 2 := by
      intro x
      have hpart := card_eq_sum_card_image (fun j => ρ j x) S
      have hfib : ∀ p ∈ P x, (S.filter fun j => ρ j x = p).card = 2 := by
        intro p hp
        have heq : (S.filter fun j => ρ j x = p) = fibre ρ x p := by
          ext j
          simp only [mem_filter, fibre, mem_univ, true_and]
          constructor
          · exact And.right
          · intro hj
            exact ⟨(hP x j).mp (hj ▸ hp), hj⟩
        rw [heq]
        exact hf x p
      change S.card = ∑ p ∈ P x, (S.filter fun j => ρ j x = p).card at hpart
      rw [sum_congr rfl hfib] at hpart
      simpa using hpart
    have reverse : ∀ x y : Fin n, x ≠ y →
        ∃ j, ρ j x = ρ i y ∧ ρ j y = ρ i x := by
      intro x y hxy
      have hpq : ρ i x ≠ ρ i y := fun h => hxy ((ρ i).injective h)
      have hpos : 0 < pairCount ρ x y (ρ i x) (ρ i y) := by
        apply card_pos.mpr
        exact ⟨i, by simp⟩
      rw [hr x y (ρ i x) (ρ i y) hxy hpq] at hpos
      obtain ⟨j, hj⟩ := card_pos.mp hpos
      exact ⟨j, by simpa using hj⟩
    have hsym : ∀ x y, ρ i y ∈ P x → ρ i x ∈ P y := by
      intro x y hxy
      have hne : x ≠ y := by
        intro heq
        subst y
        exact hi ((hP x i).mp hxy)
      obtain ⟨j, hjx, hjy⟩ := reverse x y hne
      have hj : j ∈ S := (hP x j).mp (hjx ▸ hxy)
      rw [← hjy]
      exact (hP y j).mpr hj
    let K : SimpleGraph (Fin n) := {
      Adj := fun x y => ρ i y ∈ P x
      symm := ⟨hsym⟩
      loopless := ⟨by intro x hx; exact hi ((hP x i).mp hx)⟩ }
    let s : ℕ := (P x₀).card
    have hdegree : ∀ x, K.degree x = s := by
      intro x
      have himage : (K.neighborFinset x).image (ρ i) = P x := by
        ext p
        constructor
        · rintro hp
          obtain ⟨y, hy, hyeq⟩ := mem_image.mp hp
          have : ρ i y ∈ P x := (K.mem_neighborFinset x y).mp hy
          simpa [hyeq] using this
        · intro hp
          obtain ⟨y, hy⟩ := (ρ i).surjective p
          refine mem_image.mpr ⟨y, (K.mem_neighborFinset x y).mpr ?_, hy⟩
          change ρ i y ∈ P x
          simpa [hy] using hp
      have hcard := congrArg Finset.card himage
      rw [card_image_of_injective _ (ρ i).injective,
        K.card_neighborFinset_eq_degree] at hcard
      have hx := hsize x
      have hx₀ := hsize x₀
      dsimp [s]
      omega
    have hes : Even s := by
      by_contra he
      have hos : Odd s := Nat.not_even_iff_odd.mp he
      have hh := K.even_card_odd_degree_vertices
      have hset : (univ.filter fun x => Odd (K.degree x)) = (univ : Finset (Fin n)) := by
        ext x
        simp [hdegree, hos]
      rw [hset] at hh
      have hen : Even n := by simpa using hh
      exact (Nat.not_even_iff_odd.mpr hn) hen
    obtain ⟨k, hk⟩ := hes
    refine ⟨k, ?_⟩
    have hs := hsize x₀
    change s = k + k at hk
    change S.card = s * 2 at hs
    omega
  let G := fibreGraph ρ
  let : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  refine ⟨?_⟩
  intro u v
  by_contra huv
  let S : Finset (Fin (2 * n)) := univ.filter fun j => G.Reachable u j
  have hS : ∀ j, j ∈ S ↔ G.Reachable u j := by intro j; simp [S]
  have hu : u ∈ S := (hS u).mpr (SimpleGraph.Reachable.refl u)
  have hv : v ∉ S := fun h => huv ((hS v).mp h)
  have hclosed : ∀ i ∈ S, ∀ j x, ρ i x = ρ j x → j ∈ S := by
    intro i hi j x hx
    by_cases hij : i = j
    · simpa [← hij] using hi
    · apply (hS j).mpr
      exact ((hS i).mp hi).trans (SimpleGraph.Adj.reachable ⟨hij, x, hx⟩)
  have hcclosed : ∀ i ∈ univ \ S, ∀ j x, ρ i x = ρ j x → j ∈ univ \ S := by
    intro i hi j x hx
    simp only [mem_sdiff, mem_univ, true_and] at hi ⊢
    intro hj
    exact hi (hclosed j hj i x hx.symm)
  have hfour := cut_four S ⟨v, hv⟩ hclosed
  have hcfour := cut_four (univ \ S) ⟨u, by simp [hu]⟩ hcclosed
  have htotal : (univ \ S).card + S.card = 2 * n := by
    simpa using card_sdiff_add_card_eq_card (subset_univ S)
  have hdiv : 4 ∣ 2 * n := htotal ▸ Nat.dvd_add hcfour hfour
  obtain ⟨k, hk⟩ := hdiv
  obtain ⟨t, ht⟩ := hn
  omega

end D5.S3.Combinatorics.Graph.URSComponentParity
