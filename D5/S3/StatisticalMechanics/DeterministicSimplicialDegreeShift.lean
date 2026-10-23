/- GID: D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Degree sets shift by dimension and acquire zero. -/
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
  simp [dsc]

private theorem vertices_earlier (v₀ : V) (v : ℕ → Finset V → V)
    {n : ℕ} {σ : Finset V} (hσ : σ ∈ dsc v₀ v n) {x : V} (hx : x ∈ σ) :
    x = v₀ ∨ ∃ s ≤ n, ∃ ρ, x = v s ρ := by
  induction n generalizing σ x with
  | zero =>
    have h : σ = {v₀} := by simpa [dsc] using hσ
    exact Or.inl (by simpa [h] using hx)
  | succ n ih =>
    rcases (mem_dsc_succ v₀ v n σ).mp hσ with hold | ⟨ρ, hρ, β, hβ, rfl⟩
    · rcases ih hold hx with h | ⟨s, hs, ρ, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨s, Nat.le_step hs, ρ, he⟩
    · rcases mem_insert.mp hx with h | h
      · exact Or.inr ⟨n + 1, le_rfl, ρ, h⟩
      · rcases ih hρ (hβ h) with h | ⟨s, hs, ρ, he⟩
        · exact Or.inl h
        · exact Or.inr ⟨s, Nat.le_step hs, ρ, he⟩

private theorem fresh (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    {n s : ℕ} (hns : n < s) {σ : Finset V} (hσ : σ ∈ dsc v₀ v n)
    (ρ : Finset V) : v s ρ ∉ σ := by
  intro hx
  rcases vertices_earlier v₀ v hσ hx with h | ⟨t, ht, α, he⟩
  · exact h₀ s ρ h
  · have he' : (s, ρ) = (t, α) := hi he
    have := congrArg Prod.fst he'
    omega

private theorem face_bounds (v₀ : V) (v : ℕ → Finset V → V)
    {n : ℕ} {σ : Finset V} (hσ : σ ∈ dsc v₀ v n) :
    1 ≤ σ.card ∧ σ.card ≤ n + 1 := by
  induction n generalizing σ with
  | zero =>
    have h : σ = {v₀} := by simpa [dsc] using hσ
    simp [h]
  | succ n ih =>
    rcases (mem_dsc_succ v₀ v n σ).mp hσ with h | ⟨ρ, hρ, β, hβ, rfl⟩
    · have := ih h
      omega
    · have hb := card_le_card hβ
      have hp := (ih hρ).2
      exact ⟨one_le_card.mpr (insert_nonempty _ _),
        (card_insert_le _ _).trans (by omega)⟩

private theorem downward (v₀ : V) (v : ℕ → Finset V → V)
    {n : ℕ} {σ τ : Finset V} (hσ : σ ∈ dsc v₀ v n) (hτ : τ ⊆ σ)
    (hne : τ.Nonempty) : τ ∈ dsc v₀ v n := by
  induction n generalizing σ τ with
  | zero =>
    have hσ' : σ = {v₀} := by simpa [dsc] using hσ
    have : τ = {v₀} := (eq_singleton_iff_nonempty_unique_mem).mpr
      ⟨hne, fun x hx => mem_singleton.mp (hσ' ▸ hτ hx)⟩
    simpa [dsc, this]
  | succ n ih =>
    apply (mem_dsc_succ v₀ v n τ).mpr
    rcases (mem_dsc_succ v₀ v n σ).mp hσ with h | ⟨ρ, hρ, β, hβ, rfl⟩
    · exact Or.inl (ih h hτ hne)
    · by_cases hx : v (n + 1) ρ ∈ τ
      · refine Or.inr ⟨ρ, hρ, τ.erase (v (n + 1) ρ), ?_, insert_erase hx⟩
        intro a ha
        have hat := mem_of_mem_erase ha
        rcases mem_insert.mp (hτ hat) with he | hb
        · exact False.elim ((ne_of_mem_erase ha) he)
        · exact hβ hb
      · exact Or.inl (ih hρ (fun a ha => hβ ((mem_insert.mp (hτ ha)).resolve_left
          (fun he => hx (he ▸ ha)))) hne)

private theorem face_exists (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    ∃ σ ∈ dsc v₀ v n, σ.card = k := by
  have hmax : ∀ n, ∃ σ ∈ dsc v₀ v n, σ.card = n + 1 := by
    intro n
    induction n with
    | zero => exact ⟨{v₀}, by simp [dsc], by simp⟩
    | succ n ih =>
      obtain ⟨σ, hσ, hc⟩ := ih
      refine ⟨insert (v (n + 1) σ) σ,
        (mem_dsc_succ v₀ v n _).mpr (Or.inr ⟨σ, hσ, σ, Subset.rfl, rfl⟩), ?_⟩
      rw [card_insert_of_notMem (fresh v₀ v hi h₀ (by omega) hσ σ), hc]
  obtain ⟨σ, hσ, hc⟩ := hmax n
  obtain ⟨τ, hτ, htc⟩ := exists_subset_card_eq (hc ▸ hkn)
  exact ⟨τ, downward v₀ v hσ hτ (one_le_card.mp (htc ▸ hk)), htc⟩

private theorem degree_link (C : Finset (Finset V)) (τ : Finset V) :
    upperDegree C τ = linkWeight C τ (weight 0) := by
  rw [linkWeight, link, sum_image]
  · rw [upperDegree, ← filter_filter, card_eq_sum_ones, sum_filter]
    apply sum_congr rfl
    intro ρ hρ
    have ht := (mem_filter.mp hρ).2
    have hc := card_sdiff_add_card_eq_card ht
    simp only [weight]
    split_ifs <;> omega
  · exact fun a ha b hb he => superset_injOn_sdiff τ
      (mem_filter.mp ha).2 (mem_filter.mp hb).2 he

private theorem link_weight_update (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    {n : ℕ} {τ : Finset V} (hτ : τ ∈ dsc v₀ v n) (q : ℕ) :
    linkWeight (dsc v₀ v (n + 1)) τ (weight q) =
      linkWeight (dsc v₀ v n) τ (weight (q + 1)) := by
  sorry

private theorem dsc_mono (v₀ : V) (v : ℕ → Finset V → V) :
    Monotone (dsc v₀ v) := by
  apply monotone_nat_of_le_succ
  intro n
  exact subset_union_left

private theorem link_evolution (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    {s : ℕ} {τ : Finset V} (hτ : τ ∈ dsc v₀ v s) (t q : ℕ) :
    linkWeight (dsc v₀ v (s + t)) τ (weight q) =
      linkWeight (dsc v₀ v s) τ (weight (q + t)) := by
  induction t generalizing q with
  | zero => simp
  | succ t ih =>
    rw [show s + (t + 1) = (s + t) + 1 by omega,
      link_weight_update v₀ v hi h₀ (dsc_mono v₀ v (by omega) hτ), ih]
    congr 2
    omega

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
  simp [g, simplexSum, weight]

private theorem g_shift (t : ℕ) : g (t + 1) 0 = g t 1 := by
  simp [g, simplexSum, weight, sum_range_succ]

private theorem compare_types {m : ℕ} (hm : 1 ≤ m) :
    {k | ∃ t r : ℕ, t + r ≤ m ∧ g t r = k} =
      insert 0 {k | k = g m 0 ∨ ∃ t r : ℕ, 1 ≤ r ∧ t + r ≤ m ∧ g t r = k} := by
  ext k
  constructor
  · rintro ⟨t, r, htr, rfl⟩
    by_cases hr : r = 0
    · subst r
      cases t with
      | zero => exact Set.mem_insert_iff.mpr (Or.inl g_zero_zero)
      | succ t =>
        apply Set.mem_insert_iff.mpr
        exact Or.inr (Or.inr ⟨t, 1, le_rfl, by omega, (g_shift t).symm⟩)
    · exact Set.mem_insert_iff.mpr (Or.inr (Or.inr ⟨t, r, by omega, htr, rfl⟩))
  · intro hk
    rcases Set.mem_insert_iff.mp hk with rfl | h
    · exact ⟨0, 0, by omega, g_zero_zero⟩
    · rcases h with rfl | ⟨t, r, hr, htr, he⟩
      · exact ⟨m, 0, by omega, rfl⟩
      · exact ⟨t, r, htr, he⟩

theorem result : claim := by
  intro V _ v₀ v hi h₀ d n hd hn
  rw [positive_degree_types v₀ v hi h₀ hd hn,
    vertex_degree_types v₀ v hi h₀, compare_types (by omega : 1 ≤ n - d)]

end D5.S3.StatisticalMechanics.DeterministicSimplicialDegreeShift
