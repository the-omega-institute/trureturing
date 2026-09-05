/- GID: D5/S1/Phase/CoordinateDeletionFrequencyTransport
   generality: G
   mirror-B: D5/B/S1/Phase/CoordinateDeletionFrequencyTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Transport coordinate frequencies and union closure through finite coordinate deletion. -/

import Mathlib

/- Library-search audit trail (2026-09-05):
   * Current `origin/dev` has no declaration or conclusion-shape match for either
     public theorem. Its coordinate-erasure results concern injective readouts,
     not frequencies in finite set families.
   * Pinned Mathlib supplies `Finset.card_le_mul_card_image`,
     `Finset.card_le_card_of_injOn`, `Finset.card_powerset`,
     `Finset.filter_image`, and `Finset.sdiff_union_inter`; these are used below.
   * No exact upstream theorem packages either atom, so the fibre injection and
     its counting consequences are proved here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Phase.CoordinateDeletionFrequencyTransport

/-- Deleting coordinates outside `j` cannot create more distinct sets containing
`j` than there were original sets containing `j`. -/
private theorem member_count_after_deletion_le
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (D : Finset α) (j : α) (hjD : j ∉ D) :
    ((F.image fun A ↦ A \ D).filter fun B ↦ j ∈ B).card ≤
      (F.filter fun A ↦ j ∈ A).card := by
  rw [Finset.filter_image]
  simpa [hjD] using
    (Finset.card_image_le
      (s := F.filter fun A ↦ j ∈ A) (f := fun A ↦ A \ D))

/-- The non-`j` part of every deletion fibre injects into `D.powerset` by
the deleted-coordinate trace `A ∩ D`. -/
private theorem nonmember_count_after_deletion_le
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (D : Finset α) (j : α) (hjD : j ∉ D) :
    (F.filter fun A ↦ j ∉ A).card ≤
      2 ^ D.card * ((F.image fun A ↦ A \ D).filter fun B ↦ j ∉ B).card := by
  let S := F.filter fun A ↦ j ∉ A
  let f : Finset α → Finset α := fun A ↦ A \ D
  rw [Finset.filter_image]
  have hfilter : F.filter (fun A ↦ j ∉ A \ D) = S := by
    ext A
    simp [S, hjD]
  change S.card ≤
    2 ^ D.card * ((F.filter (fun A ↦ j ∉ A \ D)).image f).card
  rw [hfilter]
  apply Finset.card_le_mul_card_image S (2 ^ D.card)
  intro B hB
  rw [← Finset.card_powerset D]
  apply Finset.card_le_card_of_injOn (fun A ↦ A ∩ D)
  · intro A hA
    exact Finset.mem_powerset.mpr Finset.inter_subset_right
  · intro A hA C hC htrace
    have hAfiber : A \ D = B := by
      simpa [f] using (Finset.mem_filter.mp hA).2
    have hCfiber : C \ D = B := by
      simpa [f] using (Finset.mem_filter.mp hC).2
    change A ∩ D = C ∩ D at htrace
    calc
      A = (A \ D) ∪ (A ∩ D) := (Finset.sdiff_union_inter A D).symm
      _ = (C \ D) ∪ (C ∩ D) := by rw [hAfiber, hCfiber, htrace]
      _ = C := Finset.sdiff_union_inter C D

/-- Cardinality form of the nonmember transport bound. -/
private theorem nonmember_card_sub_after_deletion_le
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (D : Finset α) (j : α) (hjD : j ∉ D) :
    F.card - (F.filter fun A ↦ j ∈ A).card ≤
      2 ^ D.card *
        ((F.image fun A ↦ A \ D).card -
          ((F.image fun A ↦ A \ D).filter fun B ↦ j ∈ B).card) := by
  have hF := Finset.card_filter_add_card_filter_not
    (s := F) (fun A ↦ j ∈ A)
  have hG := Finset.card_filter_add_card_filter_not
    (s := F.image fun A ↦ A \ D) (fun B ↦ j ∈ B)
  have hcount := nonmember_count_after_deletion_le F D j hjD
  calc
    F.card - (F.filter fun A ↦ j ∈ A).card =
        (F.filter fun A ↦ j ∉ A).card := by omega
    _ ≤ 2 ^ D.card *
        ((F.image fun A ↦ A \ D).filter fun B ↦ j ∉ B).card := hcount
    _ = 2 ^ D.card *
        ((F.image fun A ↦ A \ D).card -
          ((F.image fun A ↦ A \ D).filter fun B ↦ j ∈ B).card) := by
      congr 1
      omega

private theorem quantitative_frequency_transport
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (D : Finset α) (j : α) (r : ℕ)
    (hDcard : D.card = r) (hjD : j ∉ D) :
    let G := F.image fun A ↦ A \ D
    let N := F.card
    let M := G.card
    let x := (F.filter fun A ↦ j ∈ A).card
    let b := (G.filter fun B ↦ j ∈ B).card
    (b + 2 ^ r * (M - b)) * x ≥ b * N := by
  dsimp only
  have hbx := member_count_after_deletion_le F D j hjD
  have hnon := nonmember_card_sub_after_deletion_le F D j hjD
  have hxN : (F.filter fun A ↦ j ∈ A).card ≤ F.card :=
    Finset.card_filter_le _ _
  rw [hDcard] at hnon
  have hN :
      F.card ≤ (F.filter fun A ↦ j ∈ A).card +
        2 ^ r *
          ((F.image fun A ↦ A \ D).card -
            ((F.image fun A ↦ A \ D).filter fun B ↦ j ∈ B).card) := by
    omega
  have hmul := Nat.mul_le_mul_right
    (2 ^ r *
      ((F.image fun A ↦ A \ D).card -
        ((F.image fun A ↦ A \ D).filter fun B ↦ j ∈ B).card)) hbx
  calc
    ((F.image fun A ↦ A \ D).filter fun B ↦ j ∈ B).card * F.card ≤
        ((F.image fun A ↦ A \ D).filter fun B ↦ j ∈ B).card *
          ((F.filter fun A ↦ j ∈ A).card +
            2 ^ r *
              ((F.image fun A ↦ A \ D).card -
                ((F.image fun A ↦ A \ D).filter fun B ↦ j ∈ B).card)) :=
      Nat.mul_le_mul_left _ hN
    _ ≤ ((F.image fun A ↦ A \ D).filter fun B ↦ j ∈ B).card *
          (F.filter fun A ↦ j ∈ A).card +
        (F.filter fun A ↦ j ∈ A).card *
          (2 ^ r *
            ((F.image fun A ↦ A \ D).card -
              ((F.image fun A ↦ A \ D).filter fun B ↦ j ∈ B).card)) := by
      rw [Nat.mul_add]
      exact Nat.add_le_add_left hmul _
    _ = (((F.image fun A ↦ A \ D).filter fun B ↦ j ∈ B).card +
          2 ^ r *
            ((F.image fun A ↦ A \ D).card -
              ((F.image fun A ↦ A \ D).filter fun B ↦ j ∈ B).card)) *
        (F.filter fun A ↦ j ∈ A).card := by ring

private theorem half_frequency_transport
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (D : Finset α) (j : α) (r : ℕ)
    (hDcard : D.card = r) (hjD : j ∉ D) :
    let G := F.image fun A ↦ A \ D
    let N := F.card
    let M := G.card
    let x := (F.filter fun A ↦ j ∈ A).card
    let b := (G.filter fun B ↦ j ∈ B).card
    2 * b ≥ M → (2 ^ r + 1) * x ≥ N := by
  dsimp only
  intro hhalf
  have hbx := member_count_after_deletion_le F D j hjD
  have hnon := nonmember_card_sub_after_deletion_le F D j hjD
  have hxN : (F.filter fun A ↦ j ∈ A).card ≤ F.card :=
    Finset.card_filter_le _ _
  have hbM :
      ((F.image fun A ↦ A \ D).filter fun B ↦ j ∈ B).card ≤
        (F.image fun A ↦ A \ D).card := Finset.card_filter_le _ _
  rw [hDcard] at hnon
  have hN :
      F.card ≤ (F.filter fun A ↦ j ∈ A).card +
        2 ^ r *
          ((F.image fun A ↦ A \ D).card -
            ((F.image fun A ↦ A \ D).filter fun B ↦ j ∈ B).card) := by
    omega
  have hdiff :
      (F.image fun A ↦ A \ D).card -
          ((F.image fun A ↦ A \ D).filter fun B ↦ j ∈ B).card ≤
        (F.filter fun A ↦ j ∈ A).card := by
    omega
  have hmul := Nat.mul_le_mul_left (2 ^ r) hdiff
  calc
    F.card ≤ (F.filter fun A ↦ j ∈ A).card +
        2 ^ r *
          ((F.image fun A ↦ A \ D).card -
            ((F.image fun A ↦ A \ D).filter fun B ↦ j ∈ B).card) := hN
    _ ≤ (F.filter fun A ↦ j ∈ A).card +
        2 ^ r * (F.filter fun A ↦ j ∈ A).card :=
      Nat.add_le_add_left hmul _
    _ = (2 ^ r + 1) * (F.filter fun A ↦ j ∈ A).card := by ring

/-- The quantitative frequency inequality and its half-frequency consequence
after deleting `r` coordinates. -/
theorem quantitative_and_half_frequency_transport
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (D : Finset α) (j : α) (r : ℕ)
    (hDcard : D.card = r) (hjD : j ∉ D) :
    let G := F.image fun A ↦ A \ D
    let N := F.card
    let M := G.card
    let x := (F.filter fun A ↦ j ∈ A).card
    let b := (G.filter fun B ↦ j ∈ B).card
    (b + 2 ^ r * (M - b)) * x ≥ b * N ∧
      (2 * b ≥ M → (2 ^ r + 1) * x ≥ N) := by
  constructor
  · exact quantitative_frequency_transport F D j r hDcard hjD
  · exact half_frequency_transport F D j r hDcard hjD

/-- Coordinate deletion preserves union closure of a finite set family. -/
theorem union_closed_after_deletion
    {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (D : Finset α)
    (hUnion : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) :
    ∀ A ∈ F.image (fun S ↦ S \ D),
      ∀ B ∈ F.image (fun S ↦ S \ D),
        A ∪ B ∈ F.image (fun S ↦ S \ D) := by
  intro A hA B hB
  rcases Finset.mem_image.mp hA with ⟨A₀, hA₀, rfl⟩
  rcases Finset.mem_image.mp hB with ⟨B₀, hB₀, rfl⟩
  refine Finset.mem_image.mpr ⟨A₀ ∪ B₀, hUnion A₀ hA₀ B₀ hB₀, ?_⟩
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

example :
    let F : Finset (Finset ℕ) := {∅, {1}, {2}, {1, 2}}
    let D : Finset ℕ := {2}
    let j : ℕ := 1
    let G := F.image fun A ↦ A \ D
    let N := F.card
    let M := G.card
    let x := (F.filter fun A ↦ j ∈ A).card
    let b := (G.filter fun B ↦ j ∈ B).card
    D.card = 1 ∧ j ∉ D ∧ N = 4 ∧ M = 2 ∧ x = 2 ∧ b = 1 ∧
      (b + 2 ^ 1 * (M - b)) * x ≥ b * N ∧
      (2 * b ≥ M → (2 ^ 1 + 1) * x ≥ N) ∧
      (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) := by
  decide

#print axioms quantitative_and_half_frequency_transport
#print axioms union_closed_after_deletion

end D5.S1.Phase.CoordinateDeletionFrequencyTransport
