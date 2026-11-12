/- GID: D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation
   mirror-E: none(waiver:analytic-unrestricted-refutation)
   anchors: [mathlib/module/Mathlib.Data.Finset.Max]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.claim; result=D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.result; claim=D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.claim
   digest: Original pseudo-Frobenius row deletion always retains a length-one row. -/

import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Set.Defs
import Mathlib.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation

/-- A proper cofinite subset of the naturals containing zero, encoded by all its gaps. -/
structure NumericalSet where
  gaps : Finset ℕ
  proper : gaps.Nonempty
  zero_not_gap : 0 ∉ gaps

/-- Membership is the complement of the complete finite gap set. -/
def members (U : NumericalSet) : Set ℕ := {n | n ∉ U.gaps}

/-- The largest gap; the carrier excludes the improper numerical set. -/
def frobenius (U : NumericalSet) : ℕ := U.gaps.max' U.proper

/-- Additive closure, with no bound on either summand. -/
def Semigroup (U : NumericalSet) : Prop :=
  ∀ a b : ℕ, a ∈ members U → b ∈ members U → a + b ∈ members U

/-- The original pseudo-Frobenius condition quantifies over every positive source element. -/
def PseudoFrobenius (U : NumericalSet) (f : ℕ) : Prop :=
  f ∈ U.gaps ∧ ∀ s : ℕ, 0 < s → s ∈ members U → f + s ∈ members U

/-- The genus/type equality, in addition to additive closure. -/
def AlmostSymmetric (U : NumericalSet) : Prop :=
  Semigroup U ∧ 2 * U.gaps.card = frobenius U +
    (U.gaps.filter (PseudoFrobenius U)).card

/-- Exactly one of each complementary pair belongs, including both endpoints. -/
def Symmetric (U : NumericalSet) : Prop :=
  ∀ a : ℕ, a ≤ frobenius U → (a ∈ members U ↔ frobenius U - a ∉ members U)

/-- The horizontal coordinate of the upward step labelled r: right steps before r. -/
def rowLength (U : NumericalSet) (r : ℕ) : ℕ :=
  ((Finset.range r).filter (fun a => a ∈ members U)).card

/-- Original row labels, deleting exactly PF(U) except the Frobenius row. -/
def retainedRows (U : NumericalSet) : Finset ℕ :=
  U.gaps.filter (fun r => r = frobenius U ∨ ¬ PseudoFrobenius U r)

/-- Inverse boundary: an up step has label x+y, where x is its row length and
    y counts preceding up steps. The finite row labels are ordered increasingly. -/
def inverseBoundary (rows : Finset ℕ) (lengths : ℕ → ℕ) : Finset ℕ :=
  rows.image (fun r => lengths r + (rows.filter (fun q => q < r)).card)

/-- Row deletion preserves each retained horizontal coordinate, then inverts the boundary. -/
def phi (U : NumericalSet) : Set ℕ :=
  {n | n ∉ inverseBoundary (retainedRows U) (rowLength U)}

private theorem original_boundary_label (U : NumericalSet) (r : ℕ) :
    rowLength U r + (U.gaps.filter (fun q => q < r)).card = r := by
  have he : U.gaps.filter (fun q => q < r) =
      (Finset.range r).filter (fun q => q ∉ members U) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_range, members, Set.mem_setOf_eq, not_not]
    exact and_comm
  rw [he]
  exact (Finset.card_filter_add_card_filter_not (s := Finset.range r)
    (fun q => q ∈ members U)).trans (Finset.card_range r)

/-- Inverting the complete row boundary recovers precisely the original gaps. -/
private theorem inverse_original_boundary (U : NumericalSet) :
    inverseBoundary U.gaps (rowLength U) = U.gaps := by
  have he : ∀ r, rowLength U r + (U.gaps.filter (fun q => q < r)).card = r :=
    original_boundary_label U
  simp only [inverseBoundary, he, Finset.image_id]

private theorem length_one (U : NumericalSet) (r : ℕ) (hr : 0 < r)
    (h : ∀ a, 0 < a → a < r → a ∉ members U) : rowLength U r = 1 := by
  have he : (Finset.range r).filter (fun a => a ∈ members U) = {0} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨ha, hm⟩
      by_contra hn
      exact h a (by omega) ha hm
    · rintro rfl
      exact ⟨hr, U.zero_not_gap⟩
  rw [rowLength, he, Finset.card_singleton]

private theorem retained_length_one (U : NumericalSet) (hS : Semigroup U) :
    ∃ r ∈ retainedRows U, rowLength U r = 1 := by
  let small := (Finset.range (frobenius U + 1)).filter
    (fun a => 0 < a ∧ a ∈ members U)
  have hF : frobenius U ∈ U.gaps := Finset.max'_mem _ _
  have hFp : 0 < frobenius U := by
    have hn := U.zero_not_gap
    by_contra h
    have hz : frobenius U = 0 := by omega
    exact hn (hz ▸ hF)
  by_cases hs : small.Nonempty
  · let M := small.max' hs
    have hM := Finset.mem_filter.mp (Finset.max'_mem small hs)
    have hMp : 0 < M := hM.2.1
    have hMm : M ∈ members U := hM.2.2
    have hMF : M < frobenius U := by
      have hle := Finset.mem_range.mp hM.1
      have hne : M ≠ frobenius U := by intro he; exact hMm (he ▸ hF)
      omega
    let r := frobenius U - M
    have hrp : 0 < r := by dsimp [r]; omega
    have hrM : r + M = frobenius U := by dsimp [r]; omega
    have hrg : r ∈ U.gaps := by
      by_contra h
      have hc := hS r M h hMm
      rw [hrM] at hc
      exact hc hF
    have hnp : ¬ PseudoFrobenius U r := by
      intro hp
      have hc := hp.2 M hMp hMm
      rw [hrM] at hc
      exact hc hF
    refine ⟨r, Finset.mem_filter.mpr ⟨hrg, Or.inr hnp⟩, length_one U r hrp ?_⟩
    intro a hap har ham
    have hc := hS M a hMm ham
    have hma : M + a ∈ small := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, ?_, hc⟩ <;> dsimp [r] at har <;> omega
    have hmax := Finset.le_max' small (M+a) hma
    change M + a ≤ M at hmax
    omega
  · refine ⟨frobenius U, Finset.mem_filter.mpr ⟨hF, Or.inl rfl⟩,
      length_one U (frobenius U) hFp ?_⟩
    intro a hap ha ham
    apply hs
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hap, ham⟩⟩

/-- Every proper numerical semigroup has 1 absent after the original row deletion. -/
theorem phi_omits_one (U : NumericalSet) (hS : Semigroup U) : 1 ∉ phi U := by
  obtain ⟨r, hr, hlen⟩ := retained_length_one U hS
  let R := retainedRows U
  have hR : R.Nonempty := ⟨r, hr⟩
  let q := R.min' hR
  have hq : q ∈ R := Finset.min'_mem _ _
  have hqr : q ≤ r := Finset.min'_le _ _ hr
  have hqg : q ∈ U.gaps := (Finset.mem_filter.mp hq).1
  have hqp : 0 < q := by
    have hn := U.zero_not_gap
    by_contra h
    have hz : q = 0 := by omega
    exact hn (hz ▸ hqg)
  have hmono : rowLength U q ≤ rowLength U r := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨ha, hm⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp ha) hqr), hm⟩
  have hpos : 0 < rowLength U q := by
    apply Finset.card_pos.mpr
    exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqp, U.zero_not_gap⟩⟩
  have hqlen : rowLength U q = 1 := by omega
  have hbefore : R.filter (fun a => a < q) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨ha, haq⟩ := Finset.mem_filter.mp ha
    have hqa := Finset.min'_le R a ha
    change q ≤ a at hqa
    omega
  change ¬ (1 ∉ inverseBoundary R (rowLength U))
  intro hn
  apply hn
  apply Finset.mem_image.mpr
  refine ⟨q, hq, ?_⟩
  rw [hqlen, hbefore, Finset.card_empty, Nat.add_zero]

/-- The unrestricted forall-target/exists-source surjectivity event. -/
def claim : Prop :=
  ∀ T : NumericalSet, Symmetric T →
    ∃ S : NumericalSet, AlmostSymmetric S ∧ phi S = members T

private def counterexample : NumericalSet where
  gaps := {2, 3}
  proper := by simp
  zero_not_gap := by simp

private theorem counterexample_symmetric : Symmetric counterexample := by
  have hF : frobenius counterexample = 3 := by decide
  intro a ha
  rw [hF] at ha ⊢
  simp only [members, Set.mem_setOf_eq, counterexample, Finset.mem_insert,
    Finset.mem_singleton, not_or, not_not]
  omega

theorem result : ¬ claim := by
  intro h
  obtain ⟨S, hS, he⟩ := h counterexample counterexample_symmetric
  have hone : 1 ∈ members counterexample := by decide
  rw [← he] at hone
  exact phi_omits_one S hS.1 hone

end D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation
