/- GID: D5/S3/Combinatorics/Sequenceability/OriginalFiniteOrderComponentBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/OriginalFiniteOrderComponentBound
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected]
   utility: none
   digest: An annihilating order bounds the actual q-containing support components. -/

import D5.S3.Combinatorics.Sequenceability.BooleanRowChargeConnectivity

/-!
A finite annihilator of a designated label bounds the components meeting that
coordinate in the graph of all proper original minimal zero supports.
The finite-family selection argument adapts the caller-supplied source
(SHA256 98a4f52df6f323420d9d3cb97cb7df1b420a3c4673d9b0ccb6e1172bc87de01c).
The charge obstruction is supplied by BooleanRowChargeConnectivity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderComponentBound

open scoped BigOperators
open DisjointMinimalZeroOrdering (MinimalZeroSupport)
open BooleanRowChargeConnectivity

universe u v
variable {α : Type u} {G : Type v} [AddCommGroup G]

open Classical in
/-- Count actual components of the graph on ALL proper original minimal zero
supports that contain at least one q-containing support. If m >= 2 annihilates
f(q), this count is strictly less than m. Paths may pass through q-free supports.
There is no incidence, finite-group, injectivity, or nonzero-label hypothesis. -/
theorem q_containing_component_card_lt
    (f : α → G) (Y : Finset α) (E : Finset (Finset α))
    (hE : ∀ B : Finset α, B ∈ E ↔ B ⊂ Y ∧ MinimalZeroSupport f B)
    (q : α) (m : ℕ) (hm : 2 ≤ m) (hmzero : m • f q = 0) :
    (((Finset.univ : Finset E).filter (fun a => q ∈ a.val)).image
      (supportIntersectionGraph E q).connectedComponentMk).card < m := by
  classical
  let H := supportIntersectionGraph E q
  let T : Finset E := Finset.univ.filter (fun a => q ∈ a.val)
  let C := T.image H.connectedComponentMk
  change C.card < m
  by_contra hn
  have hmC : m ≤ C.card := by omega
  obtain ⟨S, hSC, hScard⟩ := Finset.exists_subset_card_eq hmC
  have hrep : ∀ c : S, ∃ a : E, a ∈ T ∧ H.connectedComponentMk a = c.val := by
    intro c
    exact Finset.mem_image.mp (hSC c.property)
  choose r hrT hrC using hrep
  have hrinj : Function.Injective r := by
    intro c d he
    apply Subtype.ext
    exact (hrC c).symm.trans ((congrArg H.connectedComponentMk he).trans (hrC d))
  let U : Finset E := Finset.univ.image r
  have hUcard : U.card = m := by
    calc
      U.card = (Finset.univ : Finset S).card :=
        Finset.card_image_of_injective _ hrinj
      _ = S.card := by simp
      _ = m := hScard
  have hUq : ∀ a ∈ U, q ∈ a.val := by
    intro a ha
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_filter.mp (hrT c)).2
  have hUsep : ∀ a ∈ U, ∀ b ∈ U, a ≠ b →
      H.connectedComponentMk a ≠ H.connectedComponentMk b := by
    intro a ha b hb hab he
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hb
    have hcd : c = d := Subtype.ext ((hrC c).symm.trans (he.trans (hrC d)))
    exact hab (congrArg r hcd)
  have hUnonempty : U.Nonempty := Finset.card_pos.mp (by omega : 0 < U.card)
  have data (a : E) : a.val ⊂ Y ∧ MinimalZeroSupport f a.val :=
    (hE _).mp a.property
  -- At least two selected representatives force nonempty punctures, even if
  -- f(q)=0: an exception-only minimal support would force every other
  -- q-containing selected support to be the very same original support.
  have hUport : ∀ a ∈ U, (a.val \ ({q} : Finset α)).Nonempty := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < U.card) a
    by_contra hnport
    have hab : a.val ⊆ b.val := by
      intro i hi
      have hiq : i = q := by
        by_contra hne
        exact hnport ⟨i, Finset.mem_sdiff.mpr
          ⟨hi, by simpa only [Finset.mem_singleton] using hne⟩⟩
      simpa only [hiq] using hUq b hb
    have he : a.val = b.val :=
      (data b).2.2.2 a.val hab (data a).2.1 (data a).2.2.1
    exact hba (Subtype.ext he.symm)
  have hUmeet : ∀ a ∈ U, (a.val ∩ ({q} : Finset α)).Nonempty := by
    intro a ha
    exact ⟨q, Finset.mem_inter.mpr ⟨hUq a ha, Finset.mem_singleton_self q⟩⟩
  have hall : ∀ B : Finset α,
      B ∈ E ↔ B ⊆ Y ∧ B ≠ Y ∧ MinimalZeroSupport f B := by
    intro B
    simpa only [Finset.ssubset_iff_subset_ne, and_assoc] using hE B
  have hnonzero :=
    separated_component_charge_sum_ne_zero f Y E hall {q} U hUnonempty
      hUmeet hUport (by
        rw [supportIntersectionGraphOutside_singleton E q]
        exact hUsep)
  apply hnonzero
  calc
    (∑ a ∈ U, ∑ i ∈ a.val ∩ ({q} : Finset α), f i) = ∑ _a ∈ U, f q := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.inter_singleton_of_mem (hUq a ha), Finset.sum_singleton]
    _ = U.card • f q := by simp
    _ = m • f q := by rw [hUcard]
    _ = 0 := hmzero

end D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderComponentBound
