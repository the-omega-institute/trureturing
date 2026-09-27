/- GID: D5/S3/Combinatorics/ArrowWilfPartition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowWilfPartition
   mirror-E: none(waiver:finite-partition-by-extremal-foata-fixed-point)
   anchors: [mathlib/module/Mathlib.Data.Finset.Max]
   utility: none
   digest: Avoiding words partition by their extremal Foata fixed point. -/

import D5.S3.Combinatorics.ArrowWilfCountingCore
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowWilfPartition

noncomputable section

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArrowWilfCountingCore

/-- Words satisfying a chosen avoidance predicate. -/
abbrev Avoiding (s : Finset ℕ) (P : Word s → Prop) := {p : Word s // P p}

/-- A word with prescribed largest fixed point. -/
abbrev MaxFixedFiber (s : Finset ℕ) (P : Word s → Prop) (m : ↑s) :=
  {p : Word s // P p ∧ hat p.1 m.1 = m.1 ∧
    ∀ g ∈ s, m.1 < g → hat p.1 g ≠ g}

/-- A word with prescribed smallest fixed point. -/
abbrev MinFixedFiber (s : Finset ℕ) (P : Word s → Prop) (m : ↑s) :=
  {p : Word s // P p ∧ hat p.1 m.1 = m.1 ∧
    ∀ g ∈ s, g < m.1 → hat p.1 g ≠ g}

/-- Send a word to the no-fixed case or its largest fixed-point fiber. -/
def maxFixedPartitionMap (s : Finset ℕ) (P : Word s → Prop) :
    Avoiding s P → NoFixed s ⊕ Σ m : ↑s, MaxFixedFiber s P m := by
  intro p
  classical
  by_cases h0 : ∀ f ∈ s, hat p.1 f ≠ f
  · exact Sum.inl ⟨p.1, h0⟩
  · let F := s.filter (fun f => hat p.1 f = f)
    have hF : F.Nonempty := by
      push Not at h0
      obtain ⟨f, hf, hfix⟩ := h0
      exact ⟨f, Finset.mem_filter.mpr ⟨hf, hfix⟩⟩
    let m := F.max' hF
    have hm : m ∈ F := Finset.max'_mem F hF
    refine Sum.inr ⟨⟨m, (Finset.mem_filter.mp hm).1⟩, ⟨p.1, p.2,
      (Finset.mem_filter.mp hm).2, ?_⟩⟩
    intro g hg hmg hfix
    have hgF : g ∈ F := Finset.mem_filter.mpr ⟨hg, hfix⟩
    exact (not_le.mpr hmg) (Finset.le_max' F g hgF)

/-- Partition avoiding words by absence or largest occurrence of a Foata fixed point. -/
def maxFixedPartitionEquiv (s : Finset ℕ) (P : Word s → Prop)
    (hP0 : ∀ p : Word s, (∀ f ∈ s, hat p.1 f ≠ f) → P p) :
    Avoiding s P ≃ NoFixed s ⊕ Σ m : ↑s, MaxFixedFiber s P m where
  toFun := maxFixedPartitionMap s P
  invFun
    | Sum.inl p => ⟨p.1, hP0 p.1 p.2⟩
    | Sum.inr ⟨_, p⟩ => ⟨p.1, p.2.1⟩
  left_inv p := by
    classical
    change (match maxFixedPartitionMap s P p with
      | Sum.inl q => (⟨q.1, hP0 q.1 q.2⟩ : Avoiding s P)
      | Sum.inr ⟨_, q⟩ => ⟨q.1, q.2.1⟩) = p
    unfold maxFixedPartitionMap
    split_ifs <;> rfl
  right_inv q := by
    classical
    cases q with
    | inl p =>
        change maxFixedPartitionMap s P ⟨p.1, hP0 p.1 p.2⟩ = Sum.inl p
        unfold maxFixedPartitionMap
        split_ifs with h
        · congr
        · exact (h p.2).elim
    | inr q =>
        rcases q with ⟨m, p⟩
        have hnot : ¬ ∀ f ∈ s, hat p.1 f ≠ f := by
          intro h
          exact h m.1 m.2 p.2.2.1
        change maxFixedPartitionMap s P ⟨p.1, p.2.1⟩ = Sum.inr ⟨m, p⟩
        unfold maxFixedPartitionMap
        simp only [hnot, dite_false]
        let F := s.filter (fun f => hat p.1 f = f)
        have hF : F.Nonempty := ⟨m.1, Finset.mem_filter.mpr ⟨m.2, p.2.2.1⟩⟩
        have hmax : F.max' hF = m.1 := by
          apply (Finset.max'_eq_iff F hF m.1).2
          refine ⟨Finset.mem_filter.mpr ⟨m.2, p.2.2.1⟩, ?_⟩
          intro g hg
          have hgs := (Finset.mem_filter.mp hg).1
          have hgf := (Finset.mem_filter.mp hg).2
          by_contra hle
          exact p.2.2.2 g hgs (lt_of_not_ge hle) hgf
        have hfirst :
            (⟨F.max' hF, (Finset.mem_filter.mp (Finset.max'_mem F hF)).1⟩ : ↑s) = m :=
          Subtype.ext hmax
        apply congrArg Sum.inr
        apply Sigma.ext hfirst
        refine (Subtype.heq_iff_coe_eq ?_).2 rfl
        intro x
        change (P x ∧ hat x.1 (F.max' hF) = F.max' hF ∧
          ∀ g ∈ s, F.max' hF < g → hat x.1 g ≠ g) ↔
          (P x ∧ hat x.1 m.1 = m.1 ∧
            ∀ g ∈ s, m.1 < g → hat x.1 g ≠ g)
        rw [hmax]

/-- Send a word to the no-fixed case or its smallest fixed-point fiber. -/
def minFixedPartitionMap (s : Finset ℕ) (P : Word s → Prop) :
    Avoiding s P → NoFixed s ⊕ Σ m : ↑s, MinFixedFiber s P m := by
  intro p
  classical
  by_cases h0 : ∀ f ∈ s, hat p.1 f ≠ f
  · exact Sum.inl ⟨p.1, h0⟩
  · let F := s.filter (fun f => hat p.1 f = f)
    have hF : F.Nonempty := by
      push Not at h0
      obtain ⟨f, hf, hfix⟩ := h0
      exact ⟨f, Finset.mem_filter.mpr ⟨hf, hfix⟩⟩
    let m := F.min' hF
    have hm : m ∈ F := Finset.min'_mem F hF
    refine Sum.inr ⟨⟨m, (Finset.mem_filter.mp hm).1⟩, ⟨p.1, p.2,
      (Finset.mem_filter.mp hm).2, ?_⟩⟩
    intro g hg hgm hfix
    have hgF : g ∈ F := Finset.mem_filter.mpr ⟨hg, hfix⟩
    exact (not_le.mpr hgm) (Finset.min'_le F g hgF)

/-- Partition avoiding words by absence or smallest occurrence of a Foata fixed point. -/
def minFixedPartitionEquiv (s : Finset ℕ) (P : Word s → Prop)
    (hP0 : ∀ p : Word s, (∀ f ∈ s, hat p.1 f ≠ f) → P p) :
    Avoiding s P ≃ NoFixed s ⊕ Σ m : ↑s, MinFixedFiber s P m where
  toFun := minFixedPartitionMap s P
  invFun
    | Sum.inl p => ⟨p.1, hP0 p.1 p.2⟩
    | Sum.inr ⟨_, p⟩ => ⟨p.1, p.2.1⟩
  left_inv p := by
    classical
    change (match minFixedPartitionMap s P p with
      | Sum.inl q => (⟨q.1, hP0 q.1 q.2⟩ : Avoiding s P)
      | Sum.inr ⟨_, q⟩ => ⟨q.1, q.2.1⟩) = p
    unfold minFixedPartitionMap
    split_ifs <;> rfl
  right_inv q := by
    classical
    cases q with
    | inl p =>
        change minFixedPartitionMap s P ⟨p.1, hP0 p.1 p.2⟩ = Sum.inl p
        unfold minFixedPartitionMap
        split_ifs with h
        · congr
        · exact (h p.2).elim
    | inr q =>
        rcases q with ⟨m, p⟩
        have hnot : ¬ ∀ f ∈ s, hat p.1 f ≠ f := by
          intro h
          exact h m.1 m.2 p.2.2.1
        change minFixedPartitionMap s P ⟨p.1, p.2.1⟩ = Sum.inr ⟨m, p⟩
        unfold minFixedPartitionMap
        simp only [hnot, dite_false]
        let F := s.filter (fun f => hat p.1 f = f)
        have hF : F.Nonempty := ⟨m.1, Finset.mem_filter.mpr ⟨m.2, p.2.2.1⟩⟩
        have hmin : F.min' hF = m.1 := by
          apply (Finset.min'_eq_iff F hF m.1).2
          refine ⟨Finset.mem_filter.mpr ⟨m.2, p.2.2.1⟩, ?_⟩
          intro g hg
          have hgs := (Finset.mem_filter.mp hg).1
          have hgf := (Finset.mem_filter.mp hg).2
          by_contra hle
          exact p.2.2.2 g hgs (lt_of_not_ge hle) hgf
        have hfirst :
            (⟨F.min' hF, (Finset.mem_filter.mp (Finset.min'_mem F hF)).1⟩ : ↑s) = m :=
          Subtype.ext hmin
        apply congrArg Sum.inr
        apply Sigma.ext hfirst
        refine (Subtype.heq_iff_coe_eq ?_).2 rfl
        intro x
        change (P x ∧ hat x.1 (F.min' hF) = F.min' hF ∧
          ∀ g ∈ s, g < F.min' hF → hat x.1 g ≠ g) ↔
          (P x ∧ hat x.1 m.1 = m.1 ∧
            ∀ g ∈ s, g < m.1 → hat x.1 g ≠ g)
        rw [hmin]

end

end D5.S3.Combinatorics.ArrowWilfPartition
