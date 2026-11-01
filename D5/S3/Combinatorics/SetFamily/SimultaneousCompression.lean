/- GID: D5/S3/Combinatorics/SetFamily/SimultaneousCompression
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SetFamily/SimultaneousCompression
   mirror-E: none(waiver:general-structural-theorem)
   anchors: []
   utility: none
   digest: Local compression preserves cross-intersection after coordinate deletion. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Local replacement, full projection fibres, and two separate weighted masses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace D5.S3.Combinatorics.SetFamily.SimultaneousCompression

variable {α : Type*} [DecidableEq α]

/-- Each member of the first family meets every member of the second. -/
def CrossIntersecting (A B : Finset (Finset α)) : Prop :=
  ∀ X ∈ A, ∀ Y ∈ B, ¬ Disjoint X Y

/-- Replace a distinguished coordinate by another one. -/
def shift (s t : α) (X : Finset α) : Finset α := insert s (X.erase t)

private def moved (A : Finset (Finset α)) (s t : α) : Finset (Finset α) :=
  A.filter fun X => t ∈ X ∧ shift s t X ∉ A

/-- Move selected t-traces to their s-trace and its feasible u-extension. -/
def compressedFamily (Ω A : Finset (Finset α)) (s t u : α) : Finset (Finset α) :=
  (A \ moved A s t) ∪ (moved A s t).image (shift s t) ∪
    (((moved A s t).image fun X => insert u (shift s t X)).filter (· ∈ Ω))

private lemma moved_mem {A : Finset (Finset α)} {s t : α} {X : Finset α}
    (hX : X ∈ moved A s t) : X ∈ A ∧ t ∈ X ∧ shift s t X ∉ A := by
  simpa only [moved, mem_filter] using hX

private lemma compressed_cases {Ω A : Finset (Finset α)} {s t u : α}
    {X : Finset α} (hX : X ∈ compressedFamily Ω A s t u) :
    (X ∈ A ∧ (t ∈ X → shift s t X ∈ A)) ∨
      (s ∈ X ∧ ∃ Z ∈ A, t ∈ Z ∧ ∀ a ∈ Z.erase t, a ∈ X) := by
  rcases mem_union.mp hX with hX | hX
  · rcases mem_union.mp hX with hX | hX
    · rcases mem_sdiff.mp hX with ⟨hXA, hXm⟩
      left
      refine ⟨hXA, ?_⟩
      intro ht
      by_contra hs
      exact hXm (mem_filter.mpr ⟨hXA, ht, hs⟩)
    · obtain ⟨Z, hZ, rfl⟩ := mem_image.mp hX
      obtain ⟨hZA, htZ, _⟩ := moved_mem hZ
      right
      refine ⟨by simp [shift], Z, hZA, htZ, ?_⟩
      intro a ha
      exact mem_insert_of_mem ha
  · obtain ⟨hX, _⟩ := mem_filter.mp hX
    obtain ⟨Z, hZ, rfl⟩ := mem_image.mp hX
    obtain ⟨hZA, htZ, _⟩ := moved_mem hZ
    right
    refine ⟨by simp [shift], Z, hZA, htZ, ?_⟩
    intro a ha
    exact mem_insert_of_mem (mem_insert_of_mem ha)

private lemma compressed_subset {Ω A : Finset (Finset α)} {s t u : α}
    (hA : A ⊆ Ω)
    (hshift : ∀ X ∈ Ω, t ∈ X → shift s t X ∈ Ω) :
    compressedFamily Ω A s t u ⊆ Ω := by
  intro X hX
  rcases mem_union.mp hX with hX | hX
  · rcases mem_union.mp hX with hX | hX
    · exact hA (mem_sdiff.mp hX).1
    · obtain ⟨Z, hZ, rfl⟩ := mem_image.mp hX
      obtain ⟨hZA, htZ, _⟩ := moved_mem hZ
      exact hshift Z (hA hZA) htZ
  · exact (mem_filter.mp hX).2

private lemma compressed_cross_one_sided {Ω A B : Finset (Finset α)} {s t u : α}
    (hA : A ⊆ Ω)
    (hexcludes : ∀ Z ∈ Ω, t ∈ Z → s ∉ Z ∧ u ∉ Z)
    (hcross : CrossIntersecting A B)
    {X Y : Finset α}
    (hX : X ∈ compressedFamily Ω A s t u)
    (hY : Y ∈ compressedFamily Ω B s t u) (hsY : s ∉ Y) :
    ¬ Disjoint (X.erase t) (Y.erase t) := by
  intro hd
  have meet_eq : ∀ {a}, a ∈ X → a ∈ Y → a = t := by
    intro a haX haY
    by_contra hat
    exact (disjoint_left.mp hd) (mem_erase.mpr ⟨hat, haX⟩)
      (mem_erase.mpr ⟨hat, haY⟩)
  have hYold : Y ∈ B ∧ (t ∈ Y → shift s t Y ∈ B) := by
    rcases compressed_cases hY with h | h
    · exact h
    · exact False.elim (hsY h.1)
  rcases compressed_cases hX with hXold | hXnew
  · by_cases htX : t ∈ X
    · obtain ⟨a, haShift, haY⟩ := not_disjoint_iff.mp
        (hcross (shift s t X) (hXold.2 htX) Y hYold.1)
      rcases mem_insert.mp haShift with has | haR
      · exact hsY (has ▸ haY)
      · exact (mem_erase.mp haR).1 (meet_eq (mem_erase.mp haR).2 haY)
    · obtain ⟨a, haX, haY⟩ := not_disjoint_iff.mp (hcross X hXold.1 Y hYold.1)
      exact htX (meet_eq haX haY ▸ haX)
  · obtain ⟨_, Z, hZA, htZ, hRest⟩ := hXnew
    have htY : t ∈ Y := by
      obtain ⟨a, haZ, haY⟩ := not_disjoint_iff.mp (hcross Z hZA Y hYold.1)
      by_cases hat : a = t
      · exact hat ▸ haY
      · exact False.elim (hat (meet_eq (hRest a (mem_erase.mpr ⟨hat, haZ⟩)) haY))
    obtain ⟨a, haZ, haShift⟩ := not_disjoint_iff.mp
      (hcross Z hZA (shift s t Y) (hYold.2 htY))
    rcases mem_insert.mp haShift with has | haR
    · exact (hexcludes Z (hA hZA) htZ).1 (has ▸ haZ)
    · have hat := (mem_erase.mp haR).1
      exact hat (meet_eq (hRest a (mem_erase.mpr ⟨hat, haZ⟩)) (mem_erase.mp haR).2)

private lemma compressed_cross {Ω A B : Finset (Finset α)} {s t u : α}
    (hA : A ⊆ Ω) (hB : B ⊆ Ω) (hst : s ≠ t)
    (hexcludes : ∀ Z ∈ Ω, t ∈ Z → s ∉ Z ∧ u ∉ Z)
    (hcross : CrossIntersecting A B) :
    CrossIntersecting
      ((compressedFamily Ω A s t u).image (fun X => X.erase t))
      ((compressedFamily Ω B s t u).image (fun X => X.erase t)) := by
  intro X hX Y hY
  obtain ⟨X, hXC, rfl⟩ := mem_image.mp hX
  obtain ⟨Y, hYC, rfl⟩ := mem_image.mp hY
  by_cases hsY : s ∈ Y
  · by_cases hsX : s ∈ X
    · intro hd
      exact (disjoint_left.mp hd) (mem_erase.mpr ⟨hst, hsX⟩)
        (mem_erase.mpr ⟨hst, hsY⟩)
    · have hc : CrossIntersecting B A := by
        intro V hV W hW hd
        exact hcross W hW V hV hd.symm
      intro hd
      exact compressed_cross_one_sided hB hexcludes hc hYC hXC hsX hd.symm
  · exact compressed_cross_one_sided hA hexcludes hcross hXC hYC hsY

private lemma augmented_not_mem {Ω A B : Finset (Finset α)} {s t u : α}
    (hA : A ⊆ Ω) (hB : B ⊆ Ω)
    (hexcludes : ∀ Z ∈ Ω, t ∈ Z → s ∉ Z ∧ u ∉ Z)
    (hshift : ∀ Z ∈ Ω, t ∈ Z → shift s t Z ∈ Ω)
    (hcross : CrossIntersecting A B)
    (hmaxA : ∀ Z ∈ Ω, (∀ Y ∈ B, ¬ Disjoint Z Y) → Z ∈ A)
    {X : Finset α} (hX : X ∈ moved A s t) :
    insert u (shift s t X) ∉ A := by
  obtain ⟨hXA, htX, hsXA⟩ := moved_mem hX
  intro hAug
  apply hsXA
  apply hmaxA _ (hshift X (hA hXA) htX)
  intro Y hY hd
  have htY : t ∈ Y := by
    obtain ⟨a, haX, haY⟩ := not_disjoint_iff.mp (hcross X hXA Y hY)
    by_cases hat : a = t
    · exact hat ▸ haY
    · exact False.elim ((disjoint_left.mp hd)
        (mem_insert_of_mem (mem_erase.mpr ⟨hat, haX⟩)) haY)
  obtain ⟨a, haAug, haY⟩ := not_disjoint_iff.mp
    (hcross (insert u (shift s t X)) hAug Y hY)
  rcases mem_insert.mp haAug with hau | haShift
  · exact (hexcludes Y (hB hY) htY).2 (hau ▸ haY)
  · exact (disjoint_left.mp hd) haShift haY

private lemma compressed_nonempty {Ω A : Finset (Finset α)} {s t u : α}
    (hA : A.Nonempty) : (compressedFamily Ω A s t u).Nonempty := by
  obtain ⟨X, hX⟩ := hA
  by_cases hm : X ∈ moved A s t
  · exact ⟨shift s t X, mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hm))⟩
  · exact ⟨X, mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨hX, hm⟩))⟩

/-- Sum of the individual exact-trace weights. -/
def mass (w : Finset α → ℝ) (A : Finset (Finset α)) : ℝ := ∑ X ∈ A, w X

/-- Forget a coordinate by summing over every feasible original trace. -/
def marginalWeight (Ω : Finset (Finset α)) (w : Finset α → ℝ)
    (t : α) (R : Finset α) : ℝ :=
  ∑ X ∈ Ω with X.erase t = R, w X

private lemma shift_recover {s t : α} {X : Finset α} (hs : s ∉ X) (ht : t ∈ X) :
    insert t ((shift s t X).erase s) = X := by
  rw [shift, erase_insert (by intro h; exact hs (mem_erase.mp h).2), insert_erase ht]

private lemma compressed_mass_eq {Ω A B : Finset (Finset α)} {s t u : α}
    (hA : A ⊆ Ω) (hB : B ⊆ Ω) (hsu : s ≠ u)
    (hexcludes : ∀ Z ∈ Ω, t ∈ Z → s ∉ Z ∧ u ∉ Z)
    (hshift : ∀ Z ∈ Ω, t ∈ Z → shift s t Z ∈ Ω)
    (hcross : CrossIntersecting A B)
    (hmaxA : ∀ Z ∈ Ω, (∀ Y ∈ B, ¬ Disjoint Z Y) → Z ∈ A)
    (w : Finset α → ℝ)
    (hlaw : ∀ X ∈ Ω, t ∈ X →
      w X = w (shift s t X) + if insert u (shift s t X) ∈ Ω then
        w (insert u (shift s t X)) else 0) :
    mass w (compressedFamily Ω A s t u) = mass w A := by
  let M := moved A s t
  let S := M.image (shift s t)
  let U := (M.image fun X => insert u (shift s t X)).filter (· ∈ Ω)
  have hM : M ⊆ A := fun X hX => (moved_mem hX).1
  have hno (X : Finset α) (hX : X ∈ M) : s ∉ X ∧ u ∉ X :=
    hexcludes X (hA (hM hX)) (moved_mem hX).2.1
  have hnu (X : Finset α) (hX : X ∈ M) : u ∉ shift s t X := by
    simp [shift, Ne.symm hsu, (hno X hX).2]
  have hSi : Set.InjOn (shift s t) M := by
    intro X hX Y hY heq
    have h := congrArg (fun Z : Finset α => insert t (Z.erase s)) heq
    rwa [shift_recover (hno X hX).1 (moved_mem hX).2.1,
      shift_recover (hno Y hY).1 (moved_mem hY).2.1] at h
  have hUi : Set.InjOn (fun X => insert u (shift s t X)) M := by
    intro X hX Y hY heq
    apply hSi hX hY
    have h := congrArg (fun Z : Finset α => Z.erase u) heq
    simpa only [erase_insert (hnu X hX), erase_insert (hnu Y hY)] using h
  have hAS : Disjoint (A \ M) S := by
    apply disjoint_left.mpr
    intro Z hZ hZS
    obtain ⟨X, hX, rfl⟩ := mem_image.mp hZS
    exact (moved_mem hX).2.2 (mem_sdiff.mp hZ).1
  have hAU : Disjoint ((A \ M) ∪ S) U := by
    apply disjoint_left.mpr
    intro Z hZ hZU
    obtain ⟨hZi, _⟩ := mem_filter.mp hZU
    obtain ⟨X, hX, rfl⟩ := mem_image.mp hZi
    rcases mem_union.mp hZ with hZA | hZS
    · exact augmented_not_mem hA hB hexcludes hshift hcross hmaxA hX
        (mem_sdiff.mp hZA).1
    · obtain ⟨Y, hY, heq⟩ := mem_image.mp hZS
      have hu : u ∈ shift s t Y := heq.symm ▸ mem_insert_self _ _
      exact hnu Y hY hu
  have hsumS : (∑ X ∈ S, w X) = ∑ X ∈ M, w (shift s t X) := sum_image hSi
  have hsumU : (∑ X ∈ U, w X) = ∑ X ∈ M,
      if insert u (shift s t X) ∈ Ω then w (insert u (shift s t X)) else 0 := by
    rw [show U = (M.image fun X => insert u (shift s t X)).filter (· ∈ Ω) from rfl,
      sum_filter, sum_image hUi]
  change (∑ X ∈ ((A \ M) ∪ S) ∪ U, w X) = ∑ X ∈ A, w X
  rw [sum_union hAU, sum_union hAS, hsumS, hsumU, add_assoc, ← sum_add_distrib]
  have heq : (∑ X ∈ M, (w (shift s t X) +
      if insert u (shift s t X) ∈ Ω then w (insert u (shift s t X)) else 0)) =
      ∑ X ∈ M, w X := by
    apply sum_congr rfl
    intro X hX
    exact (hlaw X (hA (hM hX)) (moved_mem hX).2.1).symm
  rw [heq]
  exact sum_sdiff hM

private lemma mass_le_marginal {Ω A : Finset (Finset α)} (hA : A ⊆ Ω)
    (w : Finset α → ℝ) (hw : ∀ X ∈ Ω, 0 ≤ w X) (t : α) :
    mass w A ≤ mass (marginalWeight Ω w t) (A.image fun X => X.erase t) := by
  unfold mass marginalWeight
  rw [sum_fiberwise_eq_sum_filter]
  apply sum_le_sum_of_subset_of_nonneg
  · intro X hX
    exact mem_filter.mpr ⟨hA hX, mem_image_of_mem _ hX⟩
  · intro X hX _
    exact hw X (mem_filter.mp hX).1

private def polar (Ω A : Finset (Finset α)) : Finset (Finset α) :=
  Ω.filter fun X => ∀ Y ∈ A, ¬ Disjoint X Y

private lemma maximal_pair {Ω A B : Finset (Finset α)}
    (hA : A ⊆ Ω) (hB : B ⊆ Ω) (hc : CrossIntersecting A B) :
    ∃ C D : Finset (Finset α), A ⊆ C ∧ B ⊆ D ∧ C ⊆ Ω ∧ D ⊆ Ω ∧
      CrossIntersecting C D ∧
      (∀ X ∈ Ω, (∀ Y ∈ D, ¬ Disjoint X Y) → X ∈ C) ∧
      (∀ Y ∈ Ω, (∀ X ∈ C, ¬ Disjoint Y X) → Y ∈ D) := by
  let C := polar Ω B
  let D := polar Ω C
  have hAC : A ⊆ C := by
    intro X hX
    exact mem_filter.mpr ⟨hA hX, hc X hX⟩
  have hBD : B ⊆ D := by
    intro Y hY
    refine mem_filter.mpr ⟨hB hY, ?_⟩
    intro X hX hd
    exact (mem_filter.mp hX).2 Y hY hd.symm
  refine ⟨C, D, hAC, hBD, filter_subset _ _, filter_subset _ _, ?_, ?_, ?_⟩
  · intro X hX Y hY hd
    exact (mem_filter.mp hY).2 X hX hd.symm
  · intro X hX hcX
    exact mem_filter.mpr ⟨hX, fun Y hY => hcX Y (hBD hY)⟩
  · intro Y hY hcY
    exact mem_filter.mpr ⟨hY, hcY⟩

/-- Two independently weighted cross-intersecting families admit the same
coordinate deletion. The one-to-two local law is required separately for each
weight, and the reduced weights sum over the full feasible projection fibres. -/
theorem exists_simultaneous_compression
    (Ω A B : Finset (Finset α)) (s t u : α)
    (hA : A ⊆ Ω) (hB : B ⊆ Ω) (hst : s ≠ t) (hsu : s ≠ u)
    (hexcludes : ∀ X ∈ Ω, t ∈ X → s ∉ X ∧ u ∉ X)
    (hshift : ∀ X ∈ Ω, t ∈ X → shift s t X ∈ Ω)
    (w v : Finset α → ℝ) (hw : ∀ X ∈ Ω, 0 ≤ w X) (hv : ∀ X ∈ Ω, 0 ≤ v X)
    (hwlaw : ∀ X ∈ Ω, t ∈ X →
      w X = w (shift s t X) + if insert u (shift s t X) ∈ Ω then
        w (insert u (shift s t X)) else 0)
    (hvlaw : ∀ X ∈ Ω, t ∈ X →
      v X = v (shift s t X) + if insert u (shift s t X) ∈ Ω then
        v (insert u (shift s t X)) else 0)
    (hcross : CrossIntersecting A B) :
    ∃ C D : Finset (Finset α),
      C ⊆ Ω.image (fun X => X.erase t) ∧ D ⊆ Ω.image (fun X => X.erase t) ∧
      CrossIntersecting C D ∧
      mass w A ≤ mass (marginalWeight Ω w t) C ∧
      mass v B ≤ mass (marginalWeight Ω v t) D ∧
      (A.Nonempty → C.Nonempty) ∧ (B.Nonempty → D.Nonempty) := by
  obtain ⟨A', B', hAA', hBB', hA', hB', hc, hmA, hmB⟩ := maximal_pair hA hB hcross
  have hcb : CrossIntersecting B' A' := by
    intro X hX Y hY hd
    exact hc Y hY X hX hd.symm
  let C := compressedFamily Ω A' s t u
  let D := compressedFamily Ω B' s t u
  have hC : C ⊆ Ω := compressed_subset hA' hshift
  have hD : D ⊆ Ω := compressed_subset hB' hshift
  refine ⟨C.image (fun X => X.erase t), D.image (fun X => X.erase t),
    image_subset_image hC, image_subset_image hD,
    compressed_cross hA' hB' hst hexcludes hc, ?_, ?_, ?_, ?_⟩
  · calc
      mass w A ≤ mass w A' :=
        sum_le_sum_of_subset_of_nonneg hAA' (fun X hX _ => hw X (hA' hX))
      _ = mass w C := (compressed_mass_eq hA' hB' hsu hexcludes hshift hc hmA w hwlaw).symm
      _ ≤ _ := mass_le_marginal hC w hw t
  · calc
      mass v B ≤ mass v B' :=
        sum_le_sum_of_subset_of_nonneg hBB' (fun X hX _ => hv X (hB' hX))
      _ = mass v D := (compressed_mass_eq hB' hA' hsu hexcludes hshift hcb hmB v hvlaw).symm
      _ ≤ _ := mass_le_marginal hD v hv t
  · intro hne
    exact (compressed_nonempty (hne.mono hAA')).image _
  · intro hne
    exact (compressed_nonempty (hne.mono hBB')).image _


/-- Closure under feasible supersets, relative to the current trace universe. -/
def RelativelyUpper (Ω A : Finset (Finset α)) : Prop :=
  ∀ X ∈ A, ∀ Y ∈ Ω, X ⊆ Y → Y ∈ A

omit [DecidableEq α] in
private lemma maximal_upper {Ω A B : Finset (Finset α)}
    (hc : CrossIntersecting A B)
    (hm : ∀ Y ∈ Ω, (∀ Z ∈ B, ¬ Disjoint Y Z) → Y ∈ A) :
    RelativelyUpper Ω A := by
  intro X hX Y hY hXY
  apply hm Y hY
  intro Z hZ hd
  obtain ⟨a, haX, haZ⟩ := not_disjoint_iff.mp (hc X hX Z hZ)
  exact disjoint_left.mp hd (hXY haX) haZ

/-- Coherent exact-trace data on all reduced supports. The local hypotheses
are geometric and scalar conditions; cross-intersection after deletion is
supplied by the compression theorem, rather than assumed in this structure. -/
structure DeletionSystem (J : Finset α) where
  feasible : Finset α → Finset (Finset α)
  leftWeight : Finset α → Finset α → ℝ
  rightWeight : Finset α → Finset α → ℝ
  terminal : Finset α → Prop
  left_nonneg : ∀ H ⊆ J, ∀ X ∈ feasible H, 0 ≤ leftWeight H X
  right_nonneg : ∀ H ⊆ J, ∀ X ∈ feasible H, 0 ≤ rightWeight H X
  projection : ∀ H ⊆ J, ∀ t ∈ H,
    (feasible H).image (fun X => X.erase t) = feasible (H.erase t)
  left_marginal : ∀ H ⊆ J, ∀ t ∈ H, ∀ R ∈ feasible (H.erase t),
    marginalWeight (feasible H) (leftWeight H) t R = leftWeight (H.erase t) R
  right_marginal : ∀ H ⊆ J, ∀ t ∈ H, ∀ R ∈ feasible (H.erase t),
    marginalWeight (feasible H) (rightWeight H) t R = rightWeight (H.erase t) R
  local_move : ∀ H ⊆ J, ¬ terminal H → ∃ s t u : α,
    t ∈ H ∧ s ≠ t ∧ s ≠ u ∧
    (∀ X ∈ feasible H, t ∈ X → s ∉ X ∧ u ∉ X) ∧
    (∀ X ∈ feasible H, t ∈ X → shift s t X ∈ feasible H) ∧
    (∀ X ∈ feasible H, t ∈ X →
      leftWeight H X = leftWeight H (shift s t X) +
        if insert u (shift s t X) ∈ feasible H then
          leftWeight H (insert u (shift s t X)) else 0) ∧
    (∀ X ∈ feasible H, t ∈ X →
      rightWeight H X = rightWeight H (shift s t X) +
        if insert u (shift s t X) ∈ feasible H then
          rightWeight H (insert u (shift s t X)) else 0)

/-- Repeated common deletions reach a terminal support. Both final families
are relatively upper, remain cross-intersecting, retain nonemptiness, and
have at least their respective original masses. -/
theorem exists_terminal_compression (J : Finset α) (S : DeletionSystem J)
    (A B : Finset (Finset α)) (hA : A ⊆ S.feasible J) (hB : B ⊆ S.feasible J)
    (hc : CrossIntersecting A B) :
    ∃ K : Finset α, ∃ C D : Finset (Finset α),
      K ⊆ J ∧ S.terminal K ∧ C ⊆ S.feasible K ∧ D ⊆ S.feasible K ∧
      CrossIntersecting C D ∧ RelativelyUpper (S.feasible K) C ∧
      RelativelyUpper (S.feasible K) D ∧
      mass (S.leftWeight J) A ≤ mass (S.leftWeight K) C ∧
      mass (S.rightWeight J) B ≤ mass (S.rightWeight K) D ∧
      (A.Nonempty → C.Nonempty) ∧ (B.Nonempty → D.Nonempty) := by
  classical
  suffices h : ∀ H : Finset α, H ⊆ J → ∀ A B : Finset (Finset α),
      A ⊆ S.feasible H → B ⊆ S.feasible H → CrossIntersecting A B →
      ∃ K : Finset α, ∃ C D : Finset (Finset α),
        K ⊆ H ∧ S.terminal K ∧ C ⊆ S.feasible K ∧ D ⊆ S.feasible K ∧
        CrossIntersecting C D ∧ RelativelyUpper (S.feasible K) C ∧
        RelativelyUpper (S.feasible K) D ∧
        mass (S.leftWeight H) A ≤ mass (S.leftWeight K) C ∧
        mass (S.rightWeight H) B ≤ mass (S.rightWeight K) D ∧
        (A.Nonempty → C.Nonempty) ∧ (B.Nonempty → D.Nonempty) by
    exact h J Subset.rfl A B hA hB hc
  intro H
  induction H using Finset.strongInductionOn
  rename_i H ih
  intro hHJ A B hA hB hc
  by_cases ht : S.terminal H
  · obtain ⟨C, D, hAC, hBD, hC, hD, hCD, hmC, hmD⟩ := maximal_pair hA hB hc
    have hDC : CrossIntersecting D C := by
      intro X hX Y hY hd
      exact hCD Y hY X hX hd.symm
    exact ⟨H, C, D, Subset.rfl, ht, hC, hD, hCD,
      maximal_upper hCD hmC, maximal_upper hDC hmD,
      sum_le_sum_of_subset_of_nonneg hAC
        (fun X hX _ => S.left_nonneg H hHJ X (hC hX)),
      sum_le_sum_of_subset_of_nonneg hBD
        (fun X hX _ => S.right_nonneg H hHJ X (hD hX)),
      fun hne => hne.mono hAC, fun hne => hne.mono hBD⟩
  · obtain ⟨s, t, u, htH, hst, hsu, hex, hsh, hwl, hvl⟩ := S.local_move H hHJ ht
    obtain ⟨C, D, hC, hD, hCD, hw, hv, hneC, hneD⟩ :=
      exists_simultaneous_compression (S.feasible H) A B s t u hA hB hst hsu
        hex hsh (S.leftWeight H) (S.rightWeight H)
        (S.left_nonneg H hHJ) (S.right_nonneg H hHJ) hwl hvl hc
    rw [S.projection H hHJ t htH] at hC hD
    have hw' : mass (S.leftWeight H) A ≤ mass (S.leftWeight (H.erase t)) C := by
      convert hw using 1
      apply sum_congr rfl
      intro X hX
      exact (S.left_marginal H hHJ t htH X (hC hX)).symm
    have hv' : mass (S.rightWeight H) B ≤ mass (S.rightWeight (H.erase t)) D := by
      convert hv using 1
      apply sum_congr rfl
      intro X hX
      exact (S.right_marginal H hHJ t htH X (hD hX)).symm
    obtain ⟨K, E, F, hK, hterm, hE, hF, hEF, huE, huF, hwK, hvK, hneE, hneF⟩ :=
      ih (H.erase t) (erase_ssubset htH) ((erase_subset t H).trans hHJ) C D hC hD hCD
    exact ⟨K, E, F, hK.trans (erase_subset t H), hterm, hE, hF, hEF, huE, huF,
      hw'.trans hwK, hv'.trans hvK, fun hne => hneE (hneC hne),
      fun hne => hneF (hneD hne)⟩

end D5.S3.Combinatorics.SetFamily.SimultaneousCompression
