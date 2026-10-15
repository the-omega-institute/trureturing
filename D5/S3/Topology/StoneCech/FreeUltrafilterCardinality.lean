/- GID: D5/S3/Topology/StoneCech/FreeUltrafilterCardinality
   generality: G
   mirror-B: D5/B/S3/Topology/StoneCech/FreeUltrafilterCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit infinite Boolean patterns supply two-to-continuum free ultrafilters. -/

import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Logic.Equiv.Finset

/-!
# Classical cardinal supply of free ultrafilters

Finite traces of subsets of the naturals construct an independent family
on a countable coding set. Every Boolean assignment extends, together with
the cofinite filter, to a free ultrafilter; its membership readout recovers
the assignment. This is classical infrastructure, with no claim to solve
the subsequent problem of distinct projected cluster values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Function

namespace D5.S3.Topology.StoneCech.FreeUltrafilterCardinality

private abbrev Code := ℕ × Finset (Finset ℕ)

private noncomputable def trace (n : ℕ) (A : Set ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun k => k ∈ A)

private def family (A : Set ℕ) : Set Code := {x | trace x.1 A ∈ x.2}

private def pattern {I X : Type} (V : I → Set X) (T : Set I)
    (s : Finset I) : Set X := {x | ∀ i ∈ s, x ∈ V i ↔ i ∈ T}

private theorem traces_eventually_ne {A B : Set ℕ} (hAB : A ≠ B) :
    ∀ᶠ n in atTop, trace n A ≠ trace n B := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, ¬ (k ∈ A ↔ k ∈ B) := by
    by_contra! h
    exact hAB (Set.ext h)
  filter_upwards [eventually_gt_atTop k] with n hn heq
  apply hk
  have hm := Finset.ext_iff.mp heq k
  simpa only [trace, Finset.mem_filter, Finset.mem_range, hn, true_and] using hm

private theorem traces_eventually_injOn (s : Finset (Set ℕ)) :
    ∀ᶠ n in atTop, Set.InjOn (trace n) (s : Set (Set ℕ)) := by
  classical
  have h : ∀ᶠ n in atTop, ∀ A ∈ s, ∀ B ∈ s, A ≠ B → trace n A ≠ trace n B := by
    apply (eventually_all_finset s).2
    intro A hA
    apply (eventually_all_finset s).2
    intro B hB
    by_cases hAB : A = B
    · exact Filter.Eventually.of_forall (fun _ h => (h hAB).elim)
    · exact (traces_eventually_ne hAB).mono (fun _ h _ => h)
  filter_upwards [h] with n hn A hA B hB heq
  by_contra hAB
  exact hn A hA B hB hAB heq

private theorem code_patterns_infinite (T : Set (Set ℕ)) (s : Finset (Set ℕ)) :
    (pattern family T s).Infinite := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.1 (traces_eventually_injOn s)
  let f : ℕ → Code := fun t =>
    (N + t, (s.filter (fun A => A ∈ T)).image (trace (N + t)))
  apply Set.infinite_of_injective_forall_mem (f := f)
  · intro a b hab
    have := congrArg Prod.fst hab
    dsimp [f] at this
    omega
  · intro t A hA
    change trace (N + t) A ∈ (s.filter (fun B => B ∈ T)).image (trace (N + t)) ↔ A ∈ T
    constructor
    · intro h
      obtain ⟨B, hB, heq⟩ := Finset.mem_image.1 h
      obtain ⟨hBs, hBT⟩ := Finset.mem_filter.1 hB
      have hBA := hN (N + t) (Nat.le_add_right N t) hBs hA heq
      exact hBA ▸ hBT
    · intro hAT
      exact Finset.mem_image.2 ⟨A, Finset.mem_filter.2 ⟨hA, hAT⟩, rfl⟩

private def natFamily (A : Set ℕ) : Set ℕ := (Encodable.encode' Code) '' family A

private theorem nat_patterns_infinite (T : Set (Set ℕ)) (s : Finset (Set ℕ)) :
    (pattern natFamily T s).Infinite := by
  have h := (code_patterns_infinite T s).image (Encodable.encode' Code).injective.injOn
  apply h.mono
  rintro _ ⟨x, hx, rfl⟩ A hA
  have hm : Encodable.encode' Code x ∈ natFamily A ↔ x ∈ family A :=
    (Encodable.encode' Code).injective.mem_set_image
  exact hm.trans (hx A hA)

private theorem exists_realizing_ultrafilter {I : Type} (V : I → Set ℕ)
    (hV : ∀ (T : Set I) (s : Finset I), (pattern V T s).Infinite) (T : Set I) :
    ∃ u : {u : Ultrafilter ℕ // (u : Filter ℕ) ≤ cofinite},
      ∀ i, V i ∈ u.val ↔ i ∈ T := by
  classical
  let F : Finset I → Filter ℕ := fun s => cofinite ⊓ 𝓟 (pattern V T s)
  have hd : Directed (· ≥ ·) F := by
    intro s t
    refine ⟨s ∪ t, inf_le_inf_left _ (principal_mono.2 ?_),
      inf_le_inf_left _ (principal_mono.2 ?_)⟩
    · intro x hx i hi
      exact hx i (Finset.mem_union_left t hi)
    · intro x hx i hi
      exact hx i (Finset.mem_union_right s hi)
  have hn : ∀ s, (F s).NeBot := fun s => cofinite_inf_principal_neBot_iff.2 (hV T s)
  let f : Filter ℕ := ⨅ s, F s
  haveI : f.NeBot := iInf_neBot_of_directed' hd hn
  let u : Ultrafilter ℕ := Ultrafilter.of f
  have hu (s : Finset I) : (u : Filter ℕ) ≤ F s :=
    (Ultrafilter.of_le f).trans (iInf_le F s)
  refine ⟨⟨u, (hu ∅).trans inf_le_left⟩, ?_⟩
  intro i
  have hp : pattern V T {i} ∈ (u : Filter ℕ) :=
    le_principal_iff.1 ((hu {i}).trans inf_le_right)
  constructor
  · intro hi
    by_contra hiT
    have hc : (V i)ᶜ ∈ (u : Filter ℕ) := mem_of_superset hp (by
      intro x hx
      exact fun hxi => hiT ((hx i (Finset.mem_singleton_self i)).1 hxi))
    exact Filter.compl_notMem hi hc
  · intro hiT
    exact mem_of_superset hp (fun x hx => (hx i (Finset.mem_singleton_self i)).2 hiT)

/-- There are at least two-to-continuum free ultrafilters on the naturals.
The independent family and the injection of all assignments are constructed
in the proof; no cardinal-supply or independence hypothesis is assumed. -/
theorem continuum_power_le_mk_freeUltrafilter_nat :
    2 ^ Cardinal.continuum ≤
      Cardinal.mk {u : Ultrafilter ℕ // (u : Filter ℕ) ≤ Filter.cofinite} := by
  classical
  choose u hu using exists_realizing_ultrafilter natFamily nat_patterns_infinite
  have hinj : Function.Injective u := by
    intro T R hTR
    apply Set.ext
    intro i
    rw [← hu T i, ← hu R i, hTR]
  have hc := Cardinal.mk_le_of_injective hinj
  simpa only [Cardinal.mk_set, Cardinal.mk_nat, Cardinal.two_power_aleph0] using hc

end D5.S3.Topology.StoneCech.FreeUltrafilterCardinality
