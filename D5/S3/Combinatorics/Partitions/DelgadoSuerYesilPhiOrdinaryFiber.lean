/- GID: D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiOrdinaryFiber
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiOrdinaryFiber
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The row-deletion fiber over the numerical set missing only one consists of the ordinary semigroups. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#458)
escape_witness: rowLength_frob_eq_one_iff (the Frobenius row has length one exactly when no
  positive member lies below F) and phi_eq_iff (the deleted boundary is {1} exactly when only
  the Frobenius row is retained and it has length one, since retained labels strictly increase).
proof_shape:
  ordinary: definition; consumer: result.
  frob_mem, le_frob: bind-only helpers; consumers: rowLength_frob_eq_one_iff, phi_eq_iff,
    result.
  rowLength_frob_eq_one_iff: content; consumer: phi_eq_iff.
  phi_eq_iff: content; consumer: result.
  result: content.
Direct frozen dependencies: D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation
  (NumericalSet, members, frobenius, Semigroup, PseudoFrobenius, AlmostSymmetric, rowLength,
  retainedRows, inverseBoundary, phi, deletion_is_inverse_boundary).
Search record (§3.1): the frozen module proves the omission of 1 and non-surjectivity; its
  inverse-boundary relabelling lemma is reused; no D5 module or pinned Mathlib declaration
  describes the fiber of the row deletion.
-/

import D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation
import Mathlib.Tactic

/-! # The fiber of pseudo-Frobenius row deletion over `ℕ₀ ∖ {1}`

For every proper numerical set `U` with Frobenius number `F`, the row deletion `Φ` gives
`ℕ₀ ∖ {1}` exactly when `U = {0} ∪ {n : n > F}`. For every `m ≥ 2` the ordinary semigroup
`O_m = {0} ∪ {n : n ≥ m}` is almost symmetric with Frobenius number `m - 1`, so the fiber has
exactly one source at each positive Frobenius number.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiOrdinaryFiber

open D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation

attribute [local instance] DelgadoSuerYesilPhiRefutation.instDecidableMemNatSetMembers

/-- The ordinary numerical set `O_m = {0} ∪ {n : n ≥ m}`, with gaps `1, …, m - 1`. -/
def ordinary (m : ℕ) (hm : 2 ≤ m) : NumericalSet where
  gaps := Finset.Icc 1 (m - 1)
  proper := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  zero_not_gap := by simp

private lemma frob_mem (U : NumericalSet) : frobenius U ∈ U.gaps := Finset.max'_mem _ _

private lemma le_frob (U : NumericalSet) {g : ℕ} (hg : g ∈ U.gaps) : g ≤ frobenius U :=
  Finset.le_max' _ _ hg

/-- The members of `U` other than `0` all exceed `F` exactly when `rowLength U F = 1`. -/
private lemma rowLength_frob_eq_one_iff (U : NumericalSet) :
    rowLength U (frobenius U) = 1 ↔ ∀ a, 0 < a → a < frobenius U → a ∉ members U := by
  have hFp : 0 < frobenius U := by
    have := frob_mem U
    have h0 := U.zero_not_gap
    by_contra h
    exact h0 (by rwa [show frobenius U = 0 by omega] at this)
  have h0 : 0 ∈ (Finset.range (frobenius U)).filter (fun a => a ∈ members U) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hFp, U.zero_not_gap⟩
  constructor
  · intro h a ha haF ham
    have ha' : a ∈ (Finset.range (frobenius U)).filter (fun a => a ∈ members U) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr haF, ham⟩
    have hle := Finset.card_le_card (Finset.insert_subset ha' (Finset.singleton_subset_iff.mpr h0))
    rw [Finset.card_pair (by omega)] at hle
    unfold rowLength at h
    omega
  · intro h
    unfold rowLength
    rw [Finset.card_eq_one]
    refine ⟨0, Finset.eq_singleton_iff_unique_mem.mpr ⟨h0, fun a ha => ?_⟩⟩
    obtain ⟨haF, ham⟩ := Finset.mem_filter.mp ha
    by_contra hne
    exact h a (by omega) (Finset.mem_range.mp haF) ham

/-- `Φ(U) = ℕ₀ ∖ {1}` exactly when `U = {0} ∪ {n : n > F(U)}`. -/
private lemma phi_eq_iff (U : NumericalSet) :
    phi U = {n | n ≠ 1} ↔ members U = {n | n = 0 ∨ frobenius U < n} := by
  classical
  set F := frobenius U with hFdef
  set R := retainedRows U with hRdef
  have hRsub : R ⊆ U.gaps := Finset.filter_subset _ _
  have hFR : F ∈ R := Finset.mem_filter.mpr ⟨frob_mem U, Or.inl rfl⟩
  have hdel := deletion_is_inverse_boundary U R hRsub
  have hphi : ∀ n, n ∈ phi U ↔ n ∉ inverseBoundary R (rowLength U) := by
    intro n
    simp only [phi, Set.mem_ofPred_eq, ← hRdef, hdel]
  have hmembers : (members U = {n | n = 0 ∨ F < n}) ↔
      ∀ a, 0 < a → a < F → a ∉ members U := by
    constructor
    · intro h a ha haF ham
      rw [h] at ham
      rcases ham with h0 | hlt
      · omega
      · omega
    · intro h
      ext n
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro hn
        by_contra hc
        push Not at hc
        rcases lt_or_eq_of_le hc.2 with hlt | heq
        · exact h n (by omega) hlt hn
        · exact hn (heq ▸ frob_mem U)
      · rintro (rfl | hlt)
        · exact U.zero_not_gap
        · intro hg
          have := le_frob U hg
          omega
  rw [hmembers, ← rowLength_frob_eq_one_iff U]
  constructor
  · intro h
    have hB : inverseBoundary R (rowLength U) = {1} := by
      ext n
      have := hphi n
      rw [h] at this
      simp only [Set.mem_ofPred_eq, Finset.mem_singleton] at this ⊢
      constructor
      · intro hn
        by_contra hne
        exact (this.mp hne) hn
      · rintro rfl
        by_contra hn
        exact (this.mpr hn) rfl
    have hval : ∀ r ∈ R, rowLength U r + (R.filter (fun q => q < r)).card = 1 := by
      intro r hr
      have : rowLength U r + (R.filter (fun q => q < r)).card ∈
          inverseBoundary R (rowLength U) := Finset.mem_image_of_mem _ hr
      rw [hB] at this
      exact Finset.mem_singleton.mp this
    have hRF : R.filter (fun q => q < F) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨hrR, hrF⟩ := Finset.mem_filter.mp hr
      have h1 := hval r hrR
      have h2 := hval F hFR
      have hmono : rowLength U r ≤ rowLength U F := by
        apply Finset.card_le_card
        intro a ha
        obtain ⟨ha, hm⟩ := Finset.mem_filter.mp ha
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp ha) hrF), hm⟩
      have hcount : (R.filter (fun q => q < r)).card + 1 ≤ (R.filter (fun q => q < F)).card := by
        have hsub : insert r (R.filter (fun q => q < r)) ⊆ R.filter (fun q => q < F) := by
          intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hr
          · obtain ⟨hqR, hqr⟩ := Finset.mem_filter.mp hq
            exact Finset.mem_filter.mpr ⟨hqR, lt_trans hqr hrF⟩
        have := Finset.card_le_card hsub
        rwa [Finset.card_insert_of_notMem (by simp)] at this
      omega
    have := hval F hFR
    rwa [hRF, Finset.card_empty, Nat.add_zero] at this
  · intro h
    have hsmall : ∀ a, 0 < a → a < F → a ∉ members U := (rowLength_frob_eq_one_iff U).mp h
    have hR : R = {F} := by
      ext r
      simp only [Finset.mem_singleton]
      constructor
      · intro hr
        obtain ⟨hrg, hr'⟩ := Finset.mem_filter.mp hr
        rcases hr' with h' | hnp
        · exact h'
        · exfalso
          apply hnp
          refine ⟨hrg, fun s hs hsm hg => ?_⟩
          have hsF : F < s := by
            by_contra hc
            push Not at hc
            rcases lt_or_eq_of_le hc with hlt | heq
            · exact hsmall s hs hlt hsm
            · exact hsm (heq ▸ frob_mem U)
          have := le_frob U hg
          omega
      · rintro rfl
        exact hFR
    have h' : rowLength U F = 1 := h
    ext n
    rw [hphi]
    simp only [Set.mem_ofPred_eq, inverseBoundary, hR, Finset.image_singleton,
      Finset.mem_singleton, Finset.filter_singleton, lt_irrefl, ↓reduceIte, Finset.card_empty,
      Nat.add_zero, h']

/-- For every proper numerical set `U`, `Φ(U) = ℕ₀ ∖ {1}` exactly when
`U = {0} ∪ {n : n > F(U)}`; for every `m ≥ 2` the ordinary set `O_m` is an almost symmetric
numerical semigroup with Frobenius number `m - 1` and members `{0} ∪ {n : n ≥ m}`, and
`Φ(O_m) = ℕ₀ ∖ {1}`. -/
theorem result :
    (∀ U : NumericalSet,
      phi U = {n | n ≠ 1} ↔ members U = {n | n = 0 ∨ frobenius U < n}) ∧
    (∀ (m : ℕ) (hm : 2 ≤ m),
      Semigroup (ordinary m hm) ∧ AlmostSymmetric (ordinary m hm) ∧
      frobenius (ordinary m hm) = m - 1 ∧
      members (ordinary m hm) = {n | n = 0 ∨ m ≤ n} ∧
      phi (ordinary m hm) = {n | n ≠ 1}) := by
  classical
  refine ⟨phi_eq_iff, fun m hm => ?_⟩
  have hmem : members (ordinary m hm) = {n | n = 0 ∨ m ≤ n} := by
    ext n
    simp only [members, ordinary, Finset.mem_Icc, Set.mem_ofPred_eq]
    omega
  have hF : frobenius (ordinary m hm) = m - 1 := by
    apply le_antisymm
    · exact (Finset.mem_Icc.mp (frob_mem (ordinary m hm))).2
    · exact le_frob (ordinary m hm) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hS : Semigroup (ordinary m hm) := by
    intro a b ha hb
    rw [hmem] at ha hb ⊢
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    omega
  refine ⟨hS, ⟨hS, ?_⟩, hF, hmem, ?_⟩
  · have hpf : (ordinary m hm).gaps.filter (PseudoFrobenius (ordinary m hm)) =
        (ordinary m hm).gaps := by
      apply Finset.filter_true_of_mem
      intro f hf
      refine ⟨hf, fun s hs hsm => ?_⟩
      rw [hmem] at hsm ⊢
      simp only [Set.mem_ofPred_eq] at hsm ⊢
      omega
    rw [hpf, hF]
    simp only [ordinary, Nat.card_Icc]
    omega
  · rw [phi_eq_iff, hmem, hF]
    ext n
    simp only [Set.mem_ofPred_eq]
    omega

end D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiOrdinaryFiber
