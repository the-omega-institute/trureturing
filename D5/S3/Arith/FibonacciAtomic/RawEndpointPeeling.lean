/- GID: D5/S3/Arith/FibonacciAtomic/RawEndpointPeeling
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/RawEndpointPeeling
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Leaf peeling and actual raw controllers for nested-compensation endpoint costs. -/

import D5.S3.Arith.FibonacciAtomic.Scale38NestedCompensation
import Mathlib.Data.Finset.Option

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.RawEndpointPeeling

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition
open ActualJointResponseCostCore (Controller controllerPolicy controllerOutcome verifyController
  survivors Recipe gain representative phase_foundation)
open ActualImageSevenLeafSeparation (leafAddresses leafLabel Nonconflict seven_leaf_separation)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)

/-- The target is retained in the survivor set. Each query is a target leaf,
and its two distinct nonleaf reply groups have at most one member each. -/
def Peels {m : Nat} (F : Fin m → Source) (z : Fin m) :
    Finset (Fin m) → List Address → Prop
  | S, [] => S ⊆ {z}
  | S, q :: qs => q ∈ leaves (F z) ∧
      (survivors S (vector F q) .branch).card ≤ 1 ∧
      (survivors S (vector F q) .absent).card ≤ 1 ∧
      Peels F z (survivors S (vector F q) (readout q (F z))) qs

/-- Follow the target reply until the first different reply. A singleton
response group selects its complete verifier; other replies start acquisition. -/
noncomputable def peelController {m : Nat} (F : Fin m → Source) (z : Fin m) :
    Finset (Fin m) → List Address → Controller
  | _, [] => verifyController (F z) (leaves (F z))
  | S, q :: qs => .query q (fun y =>
      if y = readout q (F z) then
        peelController F z (survivors S (vector F q) y) qs
      else if h : ∃ i, survivors S (vector F q) y = {i} then
        verifyController (F (Classical.choose h)) (leaves (F (Classical.choose h)))
      else .fallback)


/-- All raw endpoint targets are exactly the safely peelable targets. Every safe
list yields an all-source strategy with its actual controller and exact paid sets. -/
theorem result (k : Nat) (hk : 1 ≤ k) :
    let m := Fintype.card (Unit ⊕ (Fin k ⊕ Fin k))
    let e := Fintype.equivFin (Unit ⊕ (Fin k ⊕ Fin k))
    let F := Scale38NestedCompensation.family k ∘ e.symm
    ∀ z : Fin m,
      ((∃ π : Strategy, ∀ i, cost π (F i) = 3*k+14 - (if i = z then 1 else 0)) ↔
        ∃ qs : List Address, Peels F z Finset.univ qs) ∧
      (∀ qs : List Address, Peels F z Finset.univ qs → ∃ π : Strategy,
        π.policy = controllerPolicy (peelController F z Finset.univ qs) ∧
        (∀ U, terminal π U = controllerOutcome (peelController F z Finset.univ qs) U) ∧
        (∀ i, cost π (F i) = 3*k+14 - (if i = z then 1 else 0)) ∧
        paid (terminal π (F z)).1 = leafAddresses (F z) ∧
        ∀ i, i ≠ z → ∃ q,
          qs.find? (fun a => decide (chi (readout a (F i)) = 1)) = some q ∧
          q ∉ leafAddresses (F i) ∧
          paid (terminal π (F i)).1 = leafAddresses (F i) ∪ {q}) := by
  classical
  dsimp only
  let m := Fintype.card (Unit ⊕ (Fin k ⊕ Fin k))
  let e : (Unit ⊕ (Fin k ⊕ Fin k)) ≃ Fin m := Fintype.equivFin _
  let F : Fin m → Source := Scale38NestedCompensation.family k ∘ e.symm
  have foundation := Scale38NestedCompensation.result k hk
  have hm : 0 < m := by simp [m, Fintype.card_sum]
  have positive (i : Fin m) : Positive (F i) :=
    ⟨Scale38NestedCompensation.preFamily k (e.symm i), (foundation.2.1 (e.symm i)).2.1⟩
  have injective : Function.Injective F := foundation.1.comp e.symm.injective
  have nc (i j : Fin m) : Nonconflict (F i) (F j) := foundation.2.2.2.1 (e.symm i) (e.symm j)
  have size (i : Fin m) : (F i).length = 3*k+13 := (foundation.2.1 (e.symm i)).2.2.2.2.1
  have leaf_card (i : Fin m) : (leafAddresses (F i)).card = 3*k+13 :=
    (foundation.2.1 (e.symm i)).2.2.2.2.2
  have leaf_length (U : Source) : (leaves U).length = U.length := by
    apply FreeMagma.rec (motive := fun V : Source => (leaves V).length = V.length)
      (fun _ => rfl) (fun s t hs ht => ?_) U
    simp only [leaves, List.length_append, List.length_map, hs, ht, FreeMagma.length]
  have leaf_zero (U : Source) (q : Address) : q ∈ leaves U ↔ chi (readout q U) = 0 := by
    have h := (seven_leaf_separation.1 U).2 q
    change q ∈ (leaves U).toFinset ↔ _ at h
    rw [List.mem_toFinset] at h
    rw [h]
    cases hr : readout q U <;> simp [leafLabel, hr, chi]
  have agree (q : Address) (i j : Fin m)
      (hi : chi (readout q (F i)) = 0) (hj : chi (readout q (F j)) = 0) :
      readout q (F i) = readout q (F j) := by
    have labels := (seven_leaf_separation.2.1 (F i) (F j)).2.2.mp (nc i j)
    cases hr : readout q (F i) <;> cases hs : readout q (F j) <;>
      simp only [hr, hs, chi] at hi hj
    all_goals try omega
    all_goals try rfl
    · exact Bool.noConfusion (labels q true false (by simp [leafLabel, hr])
        (by simp [leafLabel, hs]))
    · exact Bool.noConfusion (labels q false true (by simp [leafLabel, hr])
        (by simp [leafLabel, hs]))
  have zero_card (S : Finset (Fin m)) (r : Recipe F S)
      (hz : ∀ i ∈ S, gain r i = 0) : S.card ≤ 1 := by
    cases r with
    | singleton i => simp
    | split S a hs next =>
      obtain ⟨q, hq⟩ := a.property
      have hc (i : Fin m) (hi : i ∈ S) : chi (readout q (F i)) = 0 := by
        have h := hz i hi
        simp only [gain, hi, ↓reduceDIte] at h
        have hqi := congrFun hq i
        change readout q (F i) = a.val i at hqi
        rw [hqi]
        omega
      have him : (S.image a.val).card ≤ 1 := Finset.card_le_one.mpr (by
        intro x hx y hy
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
        rw [← congrFun hq i, ← congrFun hq j]
        exact agree q i j (hc i hi) (hc j hj))
      omega
  have extract : ∀ (S : Finset (Fin m)) (r : Recipe F S) (z : Fin m),
      z ∈ S → gain r z = 0 → (∀ i ∈ S, gain r i ≤ 1) →
      ∃ qs, Peels F z S qs := by
    intro S r
    induction r with
    | singleton i =>
      intro z hz _ _
      obtain rfl := Finset.mem_singleton.mp hz
      exact ⟨[], Finset.Subset.refl _⟩
    | split S a hs next ih =>
      intro z hz hzero hbound
      let q := representative F a
      have hq : vector F q = a.val :=
        (List.Shortlex.wf (InvImage.wf Bool.toNat Nat.lt_wfRel.wf)).min_mem
          {u | vector F u = a.val} a.property
      have at_reply (i : Fin m) (his : i ∈ S) (y : Reply) (he : a.val i = y)
          (hy : (survivors S a.val y).Nonempty) :
          gain (Recipe.split S a hs next) i = chi y + gain (next y hy) i := by
        subst y
        simp only [gain, his, ↓reduceDIte]
      have hcz : chi (a.val z) = 0 := by
        simp only [gain, hz, ↓reduceDIte] at hzero
        omega
      have hzc : z ∈ survivors S a.val (a.val z) := by simp [survivors, hz]
      have hne : (survivors S a.val (a.val z)).Nonempty := ⟨z, hzc⟩
      have ht : gain (next (a.val z) hne) z = 0 := by
        simpa only [gain, hz, ↓reduceDIte, hcz, Nat.zero_add] using hzero
      have hb : ∀ i ∈ survivors S a.val (a.val z), gain (next (a.val z) hne) i ≤ 1 := by
        intro i hi
        obtain ⟨his, hiy⟩ := Finset.mem_filter.mp hi
        have hi' := hbound i his
        rw [at_reply i his (a.val z) hiy hne] at hi'
        omega
      obtain ⟨qs, hqs⟩ := ih (a.val z) hne z hzc ht hb
      refine ⟨q :: qs, ?_⟩
      have group (y : Reply) (hy : chi y = 1) : (survivors S a.val y).card ≤ 1 := by
        by_cases hn : (survivors S a.val y).Nonempty
        · apply zero_card _ (next y hn)
          intro i hi
          obtain ⟨his, hiy⟩ := Finset.mem_filter.mp hi
          have h := hbound i his
          rw [at_reply i his y hiy hn, hy] at h
          omega
        · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
          simp
      simp only [Peels]
      refine ⟨leaf_zero (F z) q |>.mpr ?_, ?_, ?_, ?_⟩
      · simpa only [vector, ← hq] using hcz
      · simpa only [hq] using group .branch rfl
      · simpa only [hq] using group .absent rfl
      · have hqz : readout q (F z) = a.val z := congrFun hq z
        simpa only [hq, hqz] using hqs
  intro z
  have outcome :
      (∀ S qs U, (controllerOutcome (peelController F z S qs) U).2 = true ↔ Positive U) ∧
      (∀ S qs, Peels F z S qs → ∀ i ∈ S,
        paid (controllerOutcome (peelController F z S qs) (F i)).1 =
          leafAddresses (F i) ∪
            (qs.find? (fun q => decide (chi (readout q (F i)) = 1))).toFinset ∧
        ((qs.find? (fun q => decide (chi (readout q (F i)) = 1))) = none ↔ i = z)) := by
    constructor
    · intro S qs
      induction qs generalizing S with
      | nil => exact phase_foundation.2.1 (F z) (positive z)
      | cons q qs ih =>
        intro U
        simp only [peelController, controllerOutcome]
        by_cases he : readout q U = readout q (F z)
        · simp only [he, ↓reduceIte]
          exact ih _ U
        · simp only [he, ↓reduceIte]
          by_cases h : ∃ i, survivors S (vector F q) (readout q U) = {i}
          · simp only [h, ↓reduceDIte]
            exact phase_foundation.2.1 _ (positive (Classical.choose h)) U
          · simp only [h, ↓reduceDIte, controllerOutcome]
            exact acquisition_foundation.1 U
    · intro S qs
      induction qs generalizing S with
      | nil =>
        intro hp i hi
        have hiz : i = z := Finset.mem_singleton.mp (hp hi)
        subst i
        simp only [peelController, phase_foundation.2.2.1]
        simp [paid, leafAddresses, List.map_map, Function.comp_def]
      | cons q qs ih =>
        intro hp i hi
        obtain ⟨hq, hbr, hab, htail⟩ := hp
        have hcz := (leaf_zero (F z) q).mp hq
        by_cases he : readout q (F i) = readout q (F z)
        · have hchild : i ∈ survivors S (vector F q) (readout q (F z)) := by
            exact Finset.mem_filter.mpr ⟨hi, he⟩
          obtain ⟨hpaid, hnone⟩ := ih _ htail i hchild
          have hci : chi (readout q (F i)) = 0 := by rw [he]; exact hcz
          have hleaf : q ∈ leafAddresses (F i) := by
            simpa [leafAddresses] using (leaf_zero (F i) q).mpr hci
          simp only [peelController, controllerOutcome, he, ↓reduceIte]
          simp only [paid, List.map_cons, List.toFinset_cons]
          change insert q (paid (controllerOutcome
            (peelController F z (survivors S (vector F q) (readout q (F z))) qs) (F i)).1) = _ ∧ _
          rw [hpaid]
          constructor
          · simpa [hci, List.find?] using
              (Finset.insert_eq_of_mem (Finset.mem_union_left
                (qs.find? (fun q => decide (chi (readout q (F i)) = 1))).toFinset hleaf))
          · simpa [hci, List.find?] using hnone
        · have hci : chi (readout q (F i)) = 1 := by
            cases hr : readout q (F i) <;> simp only [hr, chi]
            · exact False.elim (he (agree q i z (by simp [hr, chi]) hcz))
            · exact False.elim (he (agree q i z (by simp [hr, chi]) hcz))
          have hycard : (survivors S (vector F q) (readout q (F i))).card ≤ 1 := by
            cases hr : readout q (F i) <;> simp only [hr, chi] at hci
            · omega
            · omega
            · exact hr ▸ hbr
            · exact hr ▸ hab
          have hyi : i ∈ survivors S (vector F q) (readout q (F i)) := by
            exact Finset.mem_filter.mpr ⟨hi, rfl⟩
          have hy : ∃ j, survivors S (vector F q) (readout q (F i)) = {j} := by
            refine ⟨i, Finset.eq_singleton_iff_unique_mem.mpr ⟨hyi, ?_⟩⟩
            intro j hj
            exact Finset.card_le_one.mp hycard j hj i hyi
          have chosen : Classical.choose hy = i := by
            have hm : i ∈ ({Classical.choose hy} : Finset (Fin m)) :=
              Classical.choose_spec hy ▸ hyi
            exact (Finset.mem_singleton.mp hm).symm
          have hiz : i ≠ z := by intro h; subst i; exact he rfl
          simp only [peelController, controllerOutcome, he, ↓reduceIte, hy, ↓reduceDIte, chosen]
          rw [phase_foundation.2.2.1]
          simp [paid, leafAddresses, List.map_map, Function.comp_def, List.find?, hci, hiz,
            Finset.union_singleton]
  have realize (qs : List Address) (hp : Peels F z Finset.univ qs) :
      ∃ π : Strategy,
        π.policy = controllerPolicy (peelController F z Finset.univ qs) ∧
        (∀ U, terminal π U = controllerOutcome (peelController F z Finset.univ qs) U) ∧
        (∀ i, cost π (F i) = 3*k+14 - (if i = z then 1 else 0)) ∧
        paid (terminal π (F z)).1 = leafAddresses (F z) ∧
        ∀ i, i ≠ z → ∃ q,
          qs.find? (fun a => decide (chi (readout a (F i)) = 1)) = some q ∧
          q ∉ leafAddresses (F i) ∧
          paid (terminal π (F i)).1 = leafAddresses (F i) ∪ {q} := by
    let c := peelController F z Finset.univ qs
    let π : Strategy := {
      policy := controllerPolicy c
      correct := fun U => ⟨(controllerOutcome c U).1.length+1, controllerOutcome c U,
        phase_foundation.1 c U, outcome.1 Finset.univ qs U⟩ }
    have terminal_eq (U : Source) : terminal π U = controllerOutcome c U := by
      have ht := Classical.choose_spec (Classical.choose_spec (π.correct U))
      exact source_foundation.2.2.2.2.2.2.2 _ _ _ _ _ _ _ ht.1 (phase_foundation.1 c U)
    have bills (i : Fin m) := outcome.2 Finset.univ qs hp i (Finset.mem_univ i)
    have exits (i : Fin m) (hiz : i ≠ z) : ∃ q,
        qs.find? (fun a => decide (chi (readout a (F i)) = 1)) = some q ∧
        q ∉ leafAddresses (F i) ∧
        paid (terminal π (F i)).1 = leafAddresses (F i) ∪ {q} := by
      cases he : qs.find? (fun a => decide (chi (readout a (F i)) = 1)) with
      | none => exact False.elim (hiz ((bills i).2.mp he))
      | some q =>
        have hc : chi (readout q (F i)) = 1 := of_decide_eq_true
          (List.find?_some (p := fun a : Address => decide (chi (readout a (F i)) = 1)) he)
        have hn : q ∉ leafAddresses (F i) := by
          intro hq
          have hz := (leaf_zero (F i) q).mp (by simpa [leafAddresses] using hq)
          omega
        refine ⟨q, rfl, hn, ?_⟩
        rw [terminal_eq]
        simpa only [c, he, Option.toFinset_some] using (bills i).1
    have target : paid (terminal π (F z)).1 = leafAddresses (F z) := by
      rw [terminal_eq]
      have hn := (bills z).2.mpr rfl
      simpa only [c, hn, Option.toFinset_none, Finset.union_empty] using (bills z).1
    have costs (i : Fin m) : cost π (F i) = 3*k+14 - (if i = z then 1 else 0) := by
      by_cases hiz : i = z
      · subst i
        change (paid (terminal π (F z)).1).card = _
        rw [target, leaf_card z]
        simp
        all_goals omega
      · obtain ⟨q, he, hn, hb⟩ := exits i hiz
        change (paid (terminal π (F i)).1).card = _
        rw [hb, Finset.union_singleton, Finset.card_insert_of_notMem hn, leaf_card i]
        simp only [if_neg hiz, Nat.sub_zero]
        all_goals omega
    exact ⟨π, rfl, terminal_eq, costs, target, exits⟩
  refine ⟨⟨?_, ?_⟩, realize⟩
  · rintro ⟨π, hcost⟩
    have hc := ActualJointResponseCostCore.result m hm F positive injective
    obtain ⟨v, ⟨r, hr⟩, hdom⟩ := hc.2.2.2.1 π
    have hzero : gain r z = 0 := by
      have h := hdom z
      rw [hr z, leaf_length, size z, hcost z] at h
      simp at h
      omega
    have hbound (i : Fin m) (_hi : i ∈ (Finset.univ : Finset (Fin m))) : gain r i ≤ 1 := by
      have h := hdom i
      rw [hr i, leaf_length, size i, hcost i] at h
      split_ifs at h <;> omega
    exact extract Finset.univ r z (Finset.mem_univ _) hzero hbound
  · rintro ⟨qs, hqs⟩
    obtain ⟨π, _, _, hcost, _⟩ := realize qs hqs
    exact ⟨π, hcost⟩

end D5.S3.Arith.FibonacciAtomic.RawEndpointPeeling
