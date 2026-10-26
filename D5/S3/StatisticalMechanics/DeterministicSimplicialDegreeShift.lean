/- GID: D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Degree sets shift by dimension and acquire zero. -/
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
      · exact Or.inr ⟨s, Nat.le_succ_of_le hs, ρ, he⟩
    · rcases mem_insert.mp hx with h | h
      · exact Or.inr ⟨n + 1, le_rfl, ρ, h⟩
      · rcases ih hρ (hβ h) with h | ⟨s, hs, ρ, he⟩
        · exact Or.inl h
        · exact Or.inr ⟨s, Nat.le_succ_of_le hs, ρ, he⟩

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

private theorem mem_link (C : Finset (Finset V)) (τ α : Finset V) :
    α ∈ link C τ ↔ Disjoint τ α ∧ τ ∪ α ∈ C := by
  constructor
  · rintro h
    obtain ⟨ρ, hρ, rfl⟩ := mem_image.mp h
    obtain ⟨hρ, ht⟩ := mem_filter.mp hρ
    exact ⟨disjoint_sdiff_self_right, (union_sdiff_of_subset ht).symm ▸ hρ⟩
  · rintro ⟨hd, h⟩
    exact mem_image.mpr ⟨τ ∪ α, mem_filter.mpr ⟨h, subset_union_left⟩,
      union_sdiff_cancel_left hd⟩

private theorem new_vertex_mem (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    {n : ℕ} (σ : Finset V) {ρ β : Finset V} (hρ : ρ ∈ dsc v₀ v n) (hβ : β ⊆ ρ) :
    v (n + 1) σ ∈ insert (v (n + 1) ρ) β ↔ σ = ρ := by
  have hf := fresh v₀ v hi h₀ (by omega : n < n + 1) hρ σ
  constructor
  · intro h
    rcases mem_insert.mp h with he | hb
    · have hep : (n + 1, σ) = (n + 1, ρ) := hi he
      exact congrArg Prod.snd hep
    · exact False.elim (hf (hβ hb))
  · rintro rfl
    exact mem_insert_self _ _

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

private theorem link_growth (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    {n : ℕ} {τ : Finset V} (hτ : τ ∈ dsc v₀ v n) :
    link (dsc v₀ v (n + 1)) τ = link (dsc v₀ v n) τ ∪
      (link (dsc v₀ v n) τ).biUnion (fun α =>
        α.powerset.image (insert (v (n + 1) (τ ∪ α)))) := by
  ext η
  rw [mem_link, mem_union]
  constructor
  · rintro ⟨hd, h⟩
    rcases (mem_dsc_succ v₀ v n _).mp h with hold | ⟨σ, hσ, β, hβ, he⟩
    · exact Or.inl ((mem_link _ _ _).mpr ⟨hd, hold⟩)
    · have hf := fresh v₀ v hi h₀ (by omega : n < n + 1) hτ σ
      have htβ : τ ⊆ β := by
        intro x hx
        exact (mem_insert.mp (he.symm ▸ mem_union_left η hx)).resolve_left
          (fun heq : x = v (n + 1) σ => hf (heq ▸ hx))
      have htσ := htβ.trans hβ
      apply Or.inr
      apply mem_biUnion.mpr
      refine ⟨σ \ τ, (mem_link _ _ _).mpr
        ⟨disjoint_sdiff_self_right, (union_sdiff_of_subset htσ).symm ▸ hσ⟩, ?_⟩
      apply mem_image.mpr
      refine ⟨β \ τ, mem_powerset.mpr (sdiff_subset_sdiff hβ Subset.rfl), ?_⟩
      rw [union_sdiff_of_subset htσ]
      have hh := congrArg (· \ τ) he
      rw [insert_sdiff_of_notMem β hf, union_sdiff_cancel_left hd] at hh
      exact hh
  · rintro (h | h)
    · obtain ⟨hd, hc⟩ := (mem_link _ _ _).mp h
      exact ⟨hd, (mem_dsc_succ v₀ v n _).mpr (Or.inl hc)⟩
    · obtain ⟨α, ha, hh⟩ := mem_biUnion.mp h
      obtain ⟨β, hb, rfl⟩ := mem_image.mp hh
      have hbα := mem_powerset.mp hb
      obtain ⟨hd, hc⟩ := (mem_link _ _ _).mp ha
      have hf := fresh v₀ v hi h₀ (by omega : n < n + 1) hτ (τ ∪ α)
      refine ⟨disjoint_insert_right.mpr ⟨hf, hd.mono_right hbα⟩, ?_⟩
      apply (mem_dsc_succ v₀ v n _).mpr
      apply Or.inr
      refine ⟨τ ∪ α, hc, τ ∪ β, union_subset_union_right hbα, ?_⟩
      ext x
      simp only [mem_insert, mem_union]
      tauto

private theorem weighted_growth (L : Finset (Finset V)) (u : Finset V → V)
    (hu : Set.InjOn u L) (hf : ∀ α ∈ L, ∀ β ∈ L, u α ∉ β) (f : ℕ → ℕ) :
    (∑ η ∈ L ∪ L.biUnion (fun α => α.powerset.image (insert (u α))), f η.card) =
      ∑ α ∈ L, (f α.card + simplexSum (fun j => f (j + 1)) α.card) := by
  have hd : Disjoint L (L.biUnion (fun α => α.powerset.image (insert (u α)))) := by
    apply disjoint_left.mpr
    intro η hη hh
    obtain ⟨α, ha, he⟩ := mem_biUnion.mp hh
    obtain ⟨β, hb, rfl⟩ := mem_image.mp he
    exact hf α ha _ hη (mem_insert_self _ _)
  have hp : (L : Set (Finset V)).PairwiseDisjoint
      (fun α => α.powerset.image (insert (u α))) := by
    intro α ha γ hγ hne
    apply disjoint_left.mpr
    intro η hη hh
    obtain ⟨β, hb, rfl⟩ := mem_image.mp hη
    obtain ⟨δ, hδ, he⟩ := mem_image.mp hh
    have hm : u α ∈ insert (u γ) δ := he.symm ▸ mem_insert_self _ _
    rcases mem_insert.mp hm with heq | hm
    · exact hne (hu ha hγ heq)
    · exact hf α ha γ hγ (mem_powerset.mp hδ hm)
  rw [sum_union hd, sum_biUnion hp, ← sum_add_distrib]
  apply sum_congr rfl
  intro α hα
  congr 1
  rw [sum_image]
  · have hc : ∀ β ∈ α.powerset, (insert (u α) β).card = β.card + 1 := by
      intro β hb
      exact card_insert_of_notMem (fun h => hf α hα α hα (mem_powerset.mp hb h))
    calc
      _ = ∑ β ∈ α.powerset, f (β.card + 1) :=
        sum_congr rfl (fun β hb => congrArg f (hc β hb))
      _ = _ := by simpa [simplexSum, nsmul_eq_mul] using
        (sum_powerset_apply_card (fun j => f (j + 1)) (x := α))
  · exact insert_erase_invOn.2.injOn.mono (fun β hb =>
      notMem_mono (mem_powerset.mp hb) (hf α hα α hα))

private theorem link_weight_update (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    {n : ℕ} {τ : Finset V} (hτ : τ ∈ dsc v₀ v n) (q : ℕ) :
    linkWeight (dsc v₀ v (n + 1)) τ (weight q) =
      linkWeight (dsc v₀ v n) τ (weight (q + 1)) := by
  have hu : Set.InjOn (fun α => v (n + 1) (τ ∪ α)) (link (dsc v₀ v n) τ) := by
    intro α ha β hb he
    have he' : (n + 1, τ ∪ α) = (n + 1, τ ∪ β) := hi he
    have he'' := congrArg Prod.snd he'
    have hda := ((mem_link _ _ _).mp ha).1
    have hdb := ((mem_link _ _ _).mp hb).1
    simpa [union_sdiff_cancel_left hda, union_sdiff_cancel_left hdb] using
      congrArg (· \ τ) he''
  have hf : ∀ α ∈ link (dsc v₀ v n) τ, ∀ β ∈ link (dsc v₀ v n) τ,
      v (n + 1) (τ ∪ α) ∉ β := by
    intro α ha β hb hmem
    exact fresh v₀ v hi h₀ (by omega : n < n + 1)
      ((mem_link _ _ _).mp hb).2 (τ ∪ α) (mem_union_right _ hmem)
  unfold linkWeight
  rw [link_growth v₀ v hi h₀ hτ, weighted_growth _ _ hu hf]
  rfl

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
  ext α
  rw [mem_link, mem_powerset]
  have hfs := fresh v₀ v hi h₀ (by omega : s < s + 1) hσ σ
  constructor
  · rintro ⟨hd, h⟩
    rcases (mem_dsc_succ v₀ v s _).mp h with hold | ⟨ρ, hρ, β, hβ, he⟩
    · exact False.elim ((fresh v₀ v hi h₀ (by omega) hold σ)
        (mem_union_left _ (mem_insert_self _ _)))
    · have hv : v (s + 1) σ ∈ insert (v (s + 1) ρ) β :=
        he.symm ▸ mem_union_left α (mem_insert_self _ _)
      have hp := (new_vertex_mem v₀ v hi h₀ σ hρ hβ).mp hv
      subst ρ
      intro x hx
      have hxt : x ∉ insert (v (s + 1) σ) η := fun hm =>
        disjoint_left.mp hd hm hx
      have hxb : x ∈ β := (mem_insert.mp (he.symm ▸ mem_union_right _ hx)).resolve_left
        (fun he => hxt (he ▸ mem_insert_self _ _))
      exact mem_sdiff.mpr ⟨hβ hxb, fun hm => hxt (mem_insert_of_mem hm)⟩
  · intro ha
    have hd : Disjoint (insert (v (s + 1) σ) η) α := by
      apply disjoint_left.mpr
      intro x hx hxa
      have hdiff := mem_sdiff.mp (ha hxa)
      rcases mem_insert.mp hx with rfl | hx
      · exact hfs hdiff.1
      · exact hdiff.2 hx
    refine ⟨hd, (mem_dsc_succ v₀ v s _).mpr (Or.inr ⟨σ, hσ, η ∪ α, ?_, ?_⟩)⟩
    · exact union_subset hη (fun x hx => (mem_sdiff.mp (ha hx)).1)
    · ext x
      simp only [mem_insert, mem_union]
      tauto

private theorem birth_degree (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    {s : ℕ} {σ η : Finset V} (hσ : σ ∈ dsc v₀ v s) (hη : η ⊆ σ) (t : ℕ) :
    upperDegree (dsc v₀ v (s + 1 + t)) (insert (v (s + 1) σ) η) =
      g t (σ.card - η.card) := by
  have hb : insert (v (s + 1) σ) η ∈ dsc v₀ v (s + 1) :=
    (mem_dsc_succ v₀ v s _).mpr (Or.inr ⟨σ, hσ, η, hη, rfl⟩)
  rw [degree_link, link_evolution v₀ v hi h₀ hb, zero_add, linkWeight,
    birth_link v₀ v hi h₀ hσ hη, sum_powerset_apply_card]
  simp [g, simplexSum, card_sdiff_of_subset hη, nsmul_eq_mul]

private theorem face_origin (v₀ : V) (v : ℕ → Finset V → V)
    {n : ℕ} {τ : Finset V} (hτ : τ ∈ dsc v₀ v n) :
    τ = {v₀} ∨ ∃ s t : ℕ, ∃ σ η : Finset V, s + 1 + t = n ∧
      σ ∈ dsc v₀ v s ∧ η ⊆ σ ∧ τ = insert (v (s + 1) σ) η := by
  induction n with
  | zero => exact Or.inl (by simpa [dsc] using hτ)
  | succ n ih =>
    rcases (mem_dsc_succ v₀ v n τ).mp hτ with hold | ⟨σ, hσ, η, hη, he⟩
    · rcases ih hold with hroot | ⟨s, t, σ, η, hn, hσ, hη, he⟩
      · exact Or.inl hroot
      · exact Or.inr ⟨s, t + 1, σ, η, by omega, hσ, hη, he⟩
    · exact Or.inr ⟨n, 0, σ, η, by omega, hσ, hη, he.symm⟩

private theorem root_degree (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    (n : ℕ) : upperDegree (dsc v₀ v n) {v₀} = g n 0 := by
  rw [degree_link]
  have he := link_evolution v₀ v hi h₀ (s := 0) (τ := {v₀}) (by simp [dsc]) n 0
  simpa [linkWeight, link, dsc, g, simplexSum, filter_singleton] using he

private theorem positive_degree_types (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    {d n : ℕ} (hd : 1 ≤ d) (hn : d + 1 ≤ n) :
    degreeSet (dsc v₀ v n) d = {k | ∃ t r : ℕ, t + r ≤ n - d ∧ g t r = k} := by
  ext k
  constructor
  · rintro ⟨τ, hτ, hcard, hk⟩
    rcases face_origin v₀ v hτ with rfl | ⟨s, t, σ, η, hst, hσ, hη, rfl⟩
    · simp only [card_singleton] at hcard
      omega
    · have hf := notMem_mono hη (fresh v₀ v hi h₀ (by omega : s < s + 1) hσ σ)
      rw [card_insert_of_notMem hf] at hcard
      have hb := (face_bounds v₀ v hσ).2
      have hec := card_le_card hη
      refine ⟨t, σ.card - η.card, by omega, ?_⟩
      rw [← birth_degree v₀ v hi h₀ hσ hη t, hst]
      exact hk
  · rintro ⟨t, r, htr, hk⟩
    let s := n - t - 1
    have hst : s + 1 + t = n := by dsimp [s]; omega
    obtain ⟨σ, hσ, hc⟩ := face_exists v₀ v hi h₀ (n := s) (k := d + r)
      (by omega) (by omega)
    obtain ⟨η, hη, hec⟩ := exists_subset_card_eq (show d ≤ σ.card by omega)
    have hf := notMem_mono hη (fresh v₀ v hi h₀ (by omega : s < s + 1) hσ σ)
    have hb : insert (v (s + 1) σ) η ∈ dsc v₀ v (s + 1) :=
      (mem_dsc_succ v₀ v s _).mpr (Or.inr ⟨σ, hσ, η, hη, rfl⟩)
    refine ⟨insert (v (s + 1) σ) η, dsc_mono v₀ v (by omega) hb,
      by rw [card_insert_of_notMem hf, hec], ?_⟩
    rw [← hst, birth_degree v₀ v hi h₀ hσ hη t, hc, hec]
    simpa using hk

private theorem vertex_degree_types (v₀ : V) (v : ℕ → Finset V → V)
    (hi : Function.Injective (Function.uncurry v)) (h₀ : ∀ s σ, v s σ ≠ v₀)
    (m : ℕ) :
    degreeSet (dsc v₀ v m) 0 =
      {k | k = g m 0 ∨ ∃ t r : ℕ, 1 ≤ r ∧ t + r ≤ m ∧ g t r = k} := by
  ext k
  constructor
  · rintro ⟨τ, hτ, hcard, hk⟩
    rcases face_origin v₀ v hτ with rfl | ⟨s, t, σ, η, hst, hσ, hη, rfl⟩
    · exact Or.inl (hk.symm.trans (root_degree v₀ v hi h₀ m))
    · have hf := notMem_mono hη (fresh v₀ v hi h₀ (by omega : s < s + 1) hσ σ)
      rw [card_insert_of_notMem hf] at hcard
      have hec : η.card = 0 := by omega
      have hb := face_bounds v₀ v hσ
      refine Or.inr ⟨t, σ.card, hb.1, by omega, ?_⟩
      have he := birth_degree v₀ v hi h₀ hσ hη t
      rw [hst, hec, Nat.sub_zero] at he
      exact he.symm.trans hk
  · rintro (hk | ⟨t, r, hr, htr, hk⟩)
    · refine ⟨{v₀}, dsc_mono v₀ v (Nat.zero_le m) (by simp [dsc]), by simp, ?_⟩
      exact (root_degree v₀ v hi h₀ m).trans hk.symm
    · let s := m - t - 1
      have hst : s + 1 + t = m := by dsimp [s]; omega
      obtain ⟨σ, hσ, hc⟩ := face_exists v₀ v hi h₀ (n := s) (k := r) hr (by omega)
      have hb : insert (v (s + 1) σ) ∅ ∈ dsc v₀ v (s + 1) :=
        (mem_dsc_succ v₀ v s _).mpr (Or.inr ⟨σ, hσ, ∅, empty_subset _, rfl⟩)
      refine ⟨insert (v (s + 1) σ) ∅, dsc_mono v₀ v (by omega) hb, by simp, ?_⟩
      rw [← hst, birth_degree v₀ v hi h₀ hσ (empty_subset σ) t, hc]
      simpa using hk

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
