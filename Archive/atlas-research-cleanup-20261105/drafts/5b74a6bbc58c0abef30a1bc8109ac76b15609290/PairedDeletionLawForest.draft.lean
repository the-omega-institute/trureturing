import D5.S3.Combinatorics.CircularWords.PairedDeletionLaw
import D5.S3.Observer.Tomography.InformationallyCompletePairForest

set_option autoImplicit false

namespace D5.S3.Combinatorics.CircularWords.PairedDeletionLaw
open scoped BigOperators
universe u v
variable {α : Type u} [DecidableEq α]

/-- A faithful real encoding of the whole output of any finite channel.
This encodes each paired value, rather than the individual deletion marginals. -/
noncomputable def finiteEncoding {ι : Type v} [Fintype ι] {Y : Type*}
    (f : ι → Y) (i : ι) : ℝ := by
  classical
  letI := (Set.finite_range f).fintype
  exact ((Fintype.equivFin (Set.range f) ⟨f i, ⟨i,rfl⟩⟩).val : ℝ)

theorem finiteEncoding_eq_iff {ι : Type v} [Fintype ι] {Y : Type*}
    (f : ι → Y) (i j : ι) : finiteEncoding f i = finiteEncoding f j ↔ f i = f j := by
  classical
  letI := (Set.finite_range f).fintype
  change (((Fintype.equivFin (Set.range f) ⟨f i, ⟨i,rfl⟩⟩).val : ℝ) =
    ((Fintype.equivFin (Set.range f) ⟨f j, ⟨j,rfl⟩⟩).val : ℝ)) ↔ _
  constructor
  · intro h
    have hn := Nat.cast_injective h
    have he := (Fintype.equivFin (Set.range f)).injective (Fin.ext hn)
    exact congrArg Subtype.val he
  · intro h
    have he : (⟨f i, ⟨i,rfl⟩⟩ : Set.range f) = ⟨f j, ⟨j,rfl⟩⟩ := Subtype.ext h
    rw [he]

private theorem encoding_law_eq {ι : Type v} [Fintype ι] [DecidableEq ι] {Y : Type*}
    (f : ι → Y) (μ ν : ι → ℝ)
    (h : D5.S3.Observer.Tomography.InformationallyCompletePairForest.distribution
      (finiteEncoding f) μ =
      D5.S3.Observer.Tomography.InformationallyCompletePairForest.distribution
      (finiteEncoding f) ν) : pushforward f μ = pushforward f ν := by
  classical
  funext y
  by_cases hy : ∃ i, f i = y
  · obtain ⟨i,rfl⟩ := hy
    have he := congrFun h ({finiteEncoding f i} : Set ℝ)
    simpa only [D5.S3.Observer.Tomography.InformationallyCompletePairForest.distribution,
      Set.mem_singleton_iff, finiteEncoding_eq_iff, pushforward] using he
  · have he : Finset.univ.filter (fun i => f i = y) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun hi => hy ⟨i,hi⟩
    simp only [pushforward, he, Finset.sum_empty]

/-- The actual paired deletion laws instantiate the existing real-valued
informational-completeness interface through faithful finite encodings. -/
theorem encoded_isICPair {ι : Type v} [Fintype ι] [DecidableEq ι]
    {A : Finset α} (hA : 4 ≤ A.card)
    {a b c : α} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (X : ι → Cycle α) (hi : Function.Injective X)
    (hn : ∀ i, (X i).Nodup) (hs : ∀ i, (X i).toFinset = A) :
    D5.S3.Observer.Tomography.InformationallyCompletePairForest.IsICPair
      (finiteEncoding (fun i => paired a b (X i)))
      (finiteEncoding (fun i => paired b c (X i))) := by
  intro μ ν _hμ _hν hF hG
  exact signed_injective hA ha hb hc hab hbc hac X hi hn hs μ ν
    (encoding_law_eq _ μ ν hF) (encoding_law_eq _ μ ν hG)

/-- The published forest characterization now yields both joint injectivity
and acyclicity for the faithfully encoded actual channels. -/
theorem encoded_forest {ι : Type v} [Fintype ι] [DecidableEq ι]
    {A : Finset α} (hA : 4 ≤ A.card)
    {a b c : α} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (X : ι → Cycle α) (hi : Function.Injective X)
    (hn : ∀ i, (X i).Nodup) (hs : ∀ i, (X i).toFinset = A) :
    Function.Injective (fun i =>
      (finiteEncoding (fun j => paired a b (X j)) i,
       finiteEncoding (fun j => paired b c (X j)) i)) ∧
    (D5.S3.Observer.Tomography.InformationallyCompletePairForest.fiberGraph
      (finiteEncoding (fun i => paired a b (X i)))
      (finiteEncoding (fun i => paired b c (X i)))).IsAcyclic := by
  exact (D5.S3.Observer.Tomography.InformationallyCompletePairForest.result _ _).mp
    (encoded_isICPair hA ha hb hc hab hbc hac X hi hn hs)

end D5.S3.Combinatorics.CircularWords.PairedDeletionLaw
