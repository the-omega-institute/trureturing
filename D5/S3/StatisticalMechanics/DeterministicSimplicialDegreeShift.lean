/- GID: D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The d-degree set equals zero together with the vertex-degree set d generations earlier. -/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

namespace D5.S3.StatisticalMechanics.DeterministicSimplicialDegreeShift

open Finset

variable {V : Type} [DecidableEq V]

 def dsc (v₀ : V) (v : ℕ → Finset V → V) : ℕ → Finset (Finset V)
  | 0 => {{v₀}}
  | s + 1 => dsc v₀ v s ∪ (dsc v₀ v s).biUnion
      (fun σ => σ.powerset.image (fun β => insert (v (s + 1) σ) β))

 def upperDegree (C : Finset (Finset V)) (τ : Finset V) : ℕ :=
  (C.filter (fun ρ => τ ⊆ ρ ∧ ρ.card = τ.card + 1)).card

 def degreeSet (C : Finset (Finset V)) (d : ℕ) : Set ℕ :=
  {k | ∃ τ ∈ C, τ.card = d + 1 ∧ upperDegree C τ = k}

 def claim : Prop :=
  ∀ (V : Type) [DecidableEq V] (v₀ : V) (v : ℕ → Finset V → V),
    Function.Injective (Function.uncurry v) → (∀ s σ, v s σ ≠ v₀) →
    ∀ d n : ℕ, 1 ≤ d → d + 1 ≤ n →
      degreeSet (dsc v₀ v n) d = insert 0 (degreeSet (dsc v₀ v (n - d)) 0)

private def link (C : Finset (Finset V)) (τ : Finset V) : Finset (Finset V) :=
  (C.filter (τ ⊆ ·)).image (· \ τ)

private def simplexSum (f : ℕ → ℕ) (r : ℕ) : ℕ :=
  ∑ j ∈ range (r + 1), r.choose j * f j

private def weight : ℕ → ℕ → ℕ
  | 0, r => if r = 1 then 1 else 0
  | t + 1, r => weight t r + simplexSum (fun j => weight t (j + 1)) r

private def g (t r : ℕ) : ℕ := simplexSum (weight t) r

private def linkWeight (C : Finset (Finset V)) (τ : Finset V) (f : ℕ → ℕ) : ℕ :=
  ∑ α ∈ link C τ, f α.card

private theorem mem_dsc_succ (v₀ : V) (v : ℕ → Finset V → V) (n : ℕ)
    (ρ : Finset V) :
    ρ ∈ dsc v₀ v (n + 1) ↔ ρ ∈ dsc v₀ v n ∨
      ∃ σ ∈ dsc v₀ v n, ∃ β ⊆ σ, insert (v (n + 1) σ) β = ρ := by
  sorry

private theorem vertices_earlier (v₀ : V) (v : ℕ → Finset V → V)
    {n : ℕ} {σ : Finset V} (hσ : σ ∈ dsc v₀ v n) {x : V} (hx : x ∈ σ) :
    x = v₀ ∨ ∃ s ≤ n, ∃ ρ, x = v s ρ := by
  sorry

private theorem fresh (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    {n s : ℕ} (hns : n < s) {σ : Finset V} (hσ : σ ∈ dsc v₀ v n)
    (ρ : Finset V) : v s ρ ∉ σ := by
  sorry

private theorem face_bounds (v₀ : V) (v : ℕ → Finset V → V)
    {n : ℕ} {σ : Finset V} (hσ : σ ∈ dsc v₀ v n) :
    1 ≤ σ.card ∧ σ.card ≤ n + 1 := by
  sorry

private theorem downward (v₀ : V) (v : ℕ → Finset V → V)
    {n : ℕ} {σ τ : Finset V} (hσ : σ ∈ dsc v₀ v n) (hτ : τ ⊆ σ)
    (hne : τ.Nonempty) : τ ∈ dsc v₀ v n := by
  sorry

private theorem face_exists (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    ∃ σ ∈ dsc v₀ v n, σ.card = k := by
  sorry

private theorem degree_link (C : Finset (Finset V)) (τ : Finset V) :
    upperDegree C τ = linkWeight C τ (weight 0) := by
  sorry

private theorem link_weight_update (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    {n : ℕ} {τ : Finset V} (hτ : τ ∈ dsc v₀ v n) (q : ℕ) :
    linkWeight (dsc v₀ v (n + 1)) τ (weight q) =
      linkWeight (dsc v₀ v n) τ (weight (q + 1)) := by
  sorry

private theorem link_evolution (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    {s : ℕ} {τ : Finset V} (hτ : τ ∈ dsc v₀ v s) (t q : ℕ) :
    linkWeight (dsc v₀ v (s + t)) τ (weight q) =
      linkWeight (dsc v₀ v s) τ (weight (q + t)) := by
  sorry

private theorem birth_link (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    {s : ℕ} {σ η : Finset V} (hσ : σ ∈ dsc v₀ v s) (hη : η ⊆ σ) :
    link (dsc v₀ v (s + 1)) (insert (v (s + 1) σ) η) = (σ \ η).powerset := by
  sorry

private theorem birth_degree (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    {s : ℕ} {σ η : Finset V} (hσ : σ ∈ dsc v₀ v s) (hη : η ⊆ σ) (t : ℕ) :
    upperDegree (dsc v₀ v (s + 1 + t)) (insert (v (s + 1) σ) η) =
      g t (σ.card - η.card) := by
  sorry

private theorem positive_degree_types (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    {d n : ℕ} (hd : 1 ≤ d) (hn : d + 1 ≤ n) :
    degreeSet (dsc v₀ v n) d = {k | ∃ t r : ℕ, t + r ≤ n - d ∧ g t r = k} := by
  sorry

private theorem vertex_degree_types (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    (m : ℕ) :
    degreeSet (dsc v₀ v m) 0 =
      {k | k = g m 0 ∨ ∃ t r : ℕ, 1 ≤ r ∧ t + r ≤ m ∧ g t r = k} := by
  sorry

private theorem g_zero_zero : g 0 0 = 0 := by
  sorry

private theorem g_shift (t : ℕ) : g (t + 1) 0 = g t 1 := by
  sorry

private theorem compare_types {m : ℕ} (hm : 1 ≤ m) :
    {k | ∃ t r : ℕ, t + r ≤ m ∧ g t r = k} =
      insert 0 {k | k = g m 0 ∨ ∃ t r : ℕ, 1 ≤ r ∧ t + r ≤ m ∧ g t r = k} := by
  sorry

 theorem result : claim := by
  intro V _ v₀ v hi h₀ d n hd hn
  rw [positive_degree_types v₀ v hi h₀ hd hn,
    vertex_degree_types v₀ v hi h₀, compare_types (by omega : 1 ≤ n - d)]

end D5.S3.StatisticalMechanics.DeterministicSimplicialDegreeShift
