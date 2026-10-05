/- GID: D5/S3/Arith/FibonacciAtomic/Scale38RawEndpointSpectrum
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Raw endpoint address vocabulary and pairwise indistinguishability obstructions for the Scale38 family. -/

import D5.S3.Arith.FibonacciAtomic.RawEndpointPeeling
import D5.S3.Arith.FibonacciAtomic.Scale38LeafFrontierResponse
import Mathlib.Data.Fin.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Scale38RawEndpointSpectrum

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout leaves vector)
open ActualJointResponseCostCore (survivors)
open ActualImageSevenLeafSeparation (leafLabel leafAddresses seven_leaf_separation)
open Scale38NestedCompensation (family)
open Scale38LeafFrontierResponse (LeafRow labelledFrontier)
open RawEndpointPeeling (Peels)

local notation "Index" => fun k : Nat => Unit ⊕ (Fin k ⊕ Fin k)

/-- A native-index version of the endpoint predicate supplied by RawEndpointPeeling. -/
def rawEndpoint (k : Nat) (z : Index k) : Prop :=
  let m := Fintype.card (Index k)
  let e : Index k ≃ Fin m := Fintype.equivFin (Index k)
  let F : Fin m → Source := family k ∘ e.symm
  ∃ qs : List Address, Peels F (e z) Finset.univ qs

/-- Pairwise equality on all target leaves prevents a safe raw peeling. -/
theorem no_peel_of_leaf_agreement {m : Nat} (F : Fin m → Source)
    (z i j : Fin m) (hiz : i ≠ z) (hjz : j ≠ z) (hij : i ≠ j)
    (agree : ∀ q, q ∈ leaves (F z) → readout q (F i) = readout q (F j))
    (compat : ∀ q, q ∈ leaves (F z) →
      readout q (F i) = readout q (F z) ∨
        readout q (F i) = .branch ∨ readout q (F i) = .absent) :
    ¬ ∃ qs : List Address, Peels F z Finset.univ qs := by
  rintro ⟨qs, hqs⟩
  have carry : ∀ (S : Finset (Fin m)) (qs : List Address),
      Peels F z S qs → i ∈ S → j ∈ S → False := by
    intro S rest
    induction rest generalizing S with
    | nil =>
        intro htail hi hj
        exact hiz (Finset.mem_singleton.mp (htail hi))
    | cons q rest ih =>
        intro htail hi hj
        rcases htail with ⟨hq, hbr, hab, hnext⟩
        rcases compat q hq with he | hbranch
        · exact ih _ hnext
            (Finset.mem_filter.mpr ⟨hi, he⟩)
            (Finset.mem_filter.mpr ⟨hj, (agree q hq).symm.trans he⟩)
        · rcases hbranch with hbranch | habsent
          · have hcard := hbr
            have hboth : i ∈ survivors S (vector F q) .branch ∧
                j ∈ survivors S (vector F q) .branch := by
              constructor
              · exact Finset.mem_filter.mpr ⟨hi, by simpa [vector] using hbranch⟩
              · exact Finset.mem_filter.mpr ⟨hj, by
                  simpa [vector] using (agree q hq).symm.trans hbranch⟩
            exact (hij (Finset.card_le_one_iff.mp hcard hboth.1 hboth.2)).elim
          · have hcard := hab
            have hboth : i ∈ survivors S (vector F q) .absent ∧
                j ∈ survivors S (vector F q) .absent := by
              constructor
              · exact Finset.mem_filter.mpr ⟨hi, by simpa [vector] using habsent⟩
              · exact Finset.mem_filter.mpr ⟨hj, by
                  simpa [vector] using (agree q hq).symm.trans habsent⟩
            exact (hij (Finset.card_le_one_iff.mp hcard hboth.1 hboth.2)).elim
  exact carry _ qs hqs (Finset.mem_univ i) (Finset.mem_univ j)

private theorem compatible_of_nonconflict {P Q : Source}
    (hconf : ActualImageSevenLeafSeparation.Nonconflict P Q) :
    ∀ a, a ∈ leaves P →
      readout a Q = readout a P ∨ readout a Q = .branch ∨ readout a Q = .absent := by
  intro a ha
  have haddr : a ∈ leafAddresses P := by simpa [leafAddresses] using ha
  obtain ⟨b, hb⟩ := (seven_leaf_separation.1 P).2 a |>.mp haddr
  have labels := (seven_leaf_separation.2.1 P Q).2.2.mp hconf a
  cases hp : readout a P <;> cases hq : readout a Q <;>
    simp only [leafLabel, hp, hq] at hb labels ⊢
  all_goals try { exact Or.inl rfl }
  all_goals try { exact Or.inr (Or.inl rfl) }
  all_goals try { exact Or.inr (Or.inr rfl) }
  all_goals simp_all

private theorem frontier_row_agreement {k : Nat} (hk : 1 ≤ k)
    {Z U V : Index k} (hUZ : U ≠ Z) (hVZ : V ≠ Z)
    (row_eq : ∀ (r : LeafRow k), r.target = Z →
      ∀ (a : Address) (c : Bool), (a, c) ∈ r.block →
        r.reply U c = r.reply V c) :
    ∀ a, a ∈ leaves (family k Z) → readout a (family k U) = readout a (family k V) := by
  intro a ha
  have haddr : a ∈ leafAddresses (family k Z) := by
    simpa [leafAddresses] using ha
  have hsome := (seven_leaf_separation.1 (family k Z)).2 a |>.mp haddr
  obtain ⟨c, hc⟩ := hsome
  have hfront : (a,c) ∈ labelledFrontier (family k Z) := by
    simpa [labelledFrontier] using hc
  have H := Scale38LeafFrontierResponse.result k hk
  rcases H with ⟨_, _, _, _, _, _, _, _, _, _, _, _, cover, responses⟩
  obtain ⟨r, hr, hblock⟩ := cover Z a c hfront
  have hru := responses r U (by intro h; exact hUZ (by simpa [hr] using h)) a c hblock
  have hrv := responses r V (by intro h; exact hVZ (by simpa [hr] using h)) a c hblock
  exact hru.trans ((row_eq r hr a c hblock).trans hrv.symm)

/-- Row-level response certificates lift to equality on every target leaf. -/
theorem leaf_agreement_of_rows {k : Nat} (hk : 1 ≤ k)
    {Z U V : Index k} (hUZ : U ≠ Z) (hVZ : V ≠ Z)
    (row_eq : ∀ (r : LeafRow k), r.target = Z →
      ∀ (a : Address) (c : Bool), (a, c) ∈ r.block →
        r.reply U c = r.reply V c) :
    ∀ a, a ∈ leaves (family k Z) → readout a (family k U) = readout a (family k V) :=
  frontier_row_agreement hk hUZ hVZ row_eq

end D5.S3.Arith.FibonacciAtomic.Scale38RawEndpointSpectrum
