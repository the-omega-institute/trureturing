/- GID: D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Arbitrary-template delayed leaf certificates with exact chronological costs. -/

import D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
import D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate
import D5.S3.Arith.FibonacciAtomic.ActualJointResponseCostCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate

open GenealogicalFiberTransport (Source substitution composition)
open ActualTreeReadoutAcquisition (Address Reply readout leaves)
open ActualLeafHistoryRigidity (subtree)
open ActualImageSevenLeafSeparation (leafAddresses leafLabel)
open DelayedOriginalReadout
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)

/-- Literal reply to a Boolean leaf label. -/
def leafReply (b : Bool) : Reply := if b then .alpha else .beta

/-- The label at a known template leaf; defaults to beta off its frontier. -/
def leafBit (g : Source) (p : Address) : Bool := readout p g == .alpha

/-- The beta label requires one extra right edge at odd epochs. -/
def leafDelay (N : Nat) (b : Bool) : Nat := N/2 + N%2 * (if b then 0 else 1)

/-- The expected leaf label is swapped precisely at odd epochs. -/
def expected (N : Nat) (b : Bool) : Reply :=
  leafReply (if N%2 = 0 then b else !b)

/-- One physical probe for each original template leaf, in frontier order. -/
def templateQueries (N : Nat) (g : Source) : List Address :=
  (leaves g).map (fun p => p ++ rights (leafDelay N (leafBit g p)))

/-- Expected replies are computed from the known template only. -/
def templateExpected (N : Nat) (g : Source) : List Reply :=
  (leaves g).map (fun p => expected N (leafBit g p))

/-- Total terminal checking rejects malformed reply lists. -/
def templateCheck (N : Nat) (g : Source) (rs : List Reply) : Bool :=
  decide (rs = templateExpected N g)

/-- Delayed matching imposes no promise on the competing finite tree. -/
def DelayedMatches (N : Nat) (g u : Source) : Prop :=
  ∀ p ∈ leaves g,
    readout (p ++ rights (leafDelay N (leafBit g p))) (substitution^[N] u) =
      expected N (leafBit g p)

private theorem leaf_bit_reply (g : Source) (p : Address) (hp : p ∈ leaves g) :
    readout p g = leafReply (leafBit g p) := by
  obtain ⟨b, hb⟩ := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 g).2 p
    |>.mp (List.mem_toFinset.mpr hp)
  cases hr : readout p g <;> cases b <;> simp [leafLabel, hr] at hb <;>
    simp [leafBit, hr, leafReply]

private theorem leaf_separation (N : Nat) (b : Bool) (u : Source) :
    readout (rights (leafDelay N b)) (substitution^[N] u) = expected N b ↔ u = .of b := by
  have h := right_clock_readout (leafDelay N b) (substitution^[N] u)
  rw [right_clock_iterate] at h
  have hm := Nat.mod_lt N (by decide : 0 < 2)
  have hd := Nat.mod_add_div N 2
  have hh : readout (rights (leafDelay N b)) (substitution^[N] u) = expected N b ↔
      rightClock u = (if b then 0 else 1) := by
    cases b
    · by_cases he : N%2 = 0
      · simp only [expected, if_pos he, leafReply, Bool.false_eq_true, if_false]
        exact h.2.2.1.trans (by
          simp only [leafDelay, Bool.false_eq_true, if_false, Nat.mul_one]
          omega)
      · have he' : N%2 = 1 := by omega
        simp only [expected, if_neg he, Bool.not_false, leafReply, if_true]
        exact h.2.1.trans (by
          simp only [leafDelay, Bool.false_eq_true, if_false, Nat.mul_one]
          omega)
    · by_cases he : N%2 = 0
      · simp only [expected, if_pos he, leafReply, if_true]
        exact h.2.1.trans (by simp only [leafDelay, if_true, Nat.mul_zero, Nat.add_zero]; omega)
      · have he' : N%2 = 1 := by omega
        simp only [expected, if_neg he, Bool.not_true, leafReply, Bool.false_eq_true, if_false]
        exact h.2.2.1.trans (by simp only [leafDelay, if_true, Nat.mul_zero, Nat.add_zero]; omega)
  rw [hh]
  cases b <;> cases u with
  | of c => cases c <;> simp [rightClock] <;> intro he <;> cases he
  | mul x y => simp [rightClock] <;> omega

/-- Depth and label of the known template's rightmost original leaf. -/
def rightTip : Source → Nat × Bool
  | .of b => (0,b)
  | .mul _ y => ((rightTip y).1+1, (rightTip y).2)

private theorem right_tip_leaf (g : Source) :
    rights (rightTip g).1 ∈ leaves g ∧
    readout (rights (rightTip g).1) g = leafReply (rightTip g).2 := by
  induction g with
  | of b => cases b <;> simp [rightTip, rights, leaves, readout, leafReply]
  | mul x y hx hy =>
    simp only [rightTip, rights, List.replicate_succ, leaves, readout]
    constructor
    · apply List.mem_append_right
      exact List.mem_map.mpr ⟨rights (rightTip y).1, hy.1, rfl⟩
    · exact hy.2

private theorem branch_leaf_rejection (N : Nat) (x y : Source) (b : Bool) :
    ¬ DelayedMatches N (.mul x y) (.of b) := by
  intro hmatches
  let g : Source := .mul x y
  let j := (rightTip g).1
  let c := (rightTip g).2
  have hj : 0 < j := by simp [j, g, rightTip]
  have ht := right_tip_leaf g
  have bit : leafBit g (rights j) = c := by
    unfold leafBit
    change (readout (rights (rightTip g).1) g == .alpha) = (rightTip g).2
    rw [ht.2]
    cases h : (rightTip g).2 <;> rfl
  have matchTip := hmatches (rights j) ht.1
  change readout (rights j ++ rights (leafDelay N (leafBit g (rights j))))
    (substitution^[N] (.of b)) = expected N (leafBit g (rights j)) at matchTip
  rw [bit] at matchTip
  have he : rights j ++ rights (leafDelay N c) = rights (j + leafDelay N c) :=
    (List.replicate_add _ _ _).symm
  rw [he] at matchTip
  have h := right_clock_readout (j + leafDelay N c) (substitution^[N] (.of b))
  rw [right_clock_iterate] at h
  have hm := Nat.mod_lt N (by decide : 0 < 2)
  have hd := Nat.mod_add_div N 2
  cases hc : c <;> simp only [hc] at h matchTip
  · by_cases he : N%2 = 0
    · simp only [expected, if_pos he, leafReply, Bool.false_eq_true, if_false] at matchTip
      have hc := h.2.2.1.mp matchTip
      cases b <;> simp [rightClock, leafDelay, he] at hc <;> omega
    · have he' : N%2 = 1 := by omega
      simp only [expected, if_neg he, Bool.not_false, leafReply, if_true] at matchTip
      have hc := h.2.1.mp matchTip
      cases b <;> simp [rightClock, leafDelay, he'] at hc <;> omega
  · by_cases he : N%2 = 0
    · simp only [expected, if_pos he, leafReply, if_true] at matchTip
      have hc := h.2.1.mp matchTip
      cases b <;> simp [rightClock, leafDelay, he] at hc <;> omega
    · have he' : N%2 = 1 := by omega
      simp only [expected, if_neg he, Bool.not_true, leafReply, Bool.false_eq_true, if_false] at matchTip
      have hc := h.2.2.1.mp matchTip
      cases b <;> simp [rightClock, leafDelay, he'] at hc <;> omega

/-- Delayed matches reflect every original leaf reply, even for different-shaped competitors. -/
theorem delayed_leaf_reflection (N : Nat) (g u : Source) (h : DelayedMatches N g u) :
    ∀ p ∈ leaves g, readout p u = readout p g := by
  induction g generalizing u with
  | of b =>
    have hb : leafBit (.of b) [] = b := by cases b <;> rfl
    have hh := h [] (by simp [leaves])
    simp only [List.nil_append, hb] at hh
    have hu := (leaf_separation N b u).mp hh
    subst u
    intro p hp
    rfl
  | mul x y hx hy =>
    cases u with
    | of b => exact (branch_leaf_rejection N x y b h).elim
    | mul s t =>
      have hm : substitution^[N] (.mul s t) = .mul (substitution^[N] s) (substitution^[N] t) :=
        Function.Semiconj₂.iterate (fun a b => substitution.map_mul a b) N s t
      have hl : DelayedMatches N x s := by
        intro p hp
        have hh := h (false::p) (List.mem_append_left _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
        simpa only [hm, List.cons_append, readout, leafBit] using hh
      have hr : DelayedMatches N y t := by
        intro p hp
        have hh := h (true::p) (List.mem_append_right _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
        simpa only [hm, List.cons_append, readout, leafBit] using hh
      intro p hp
      simp only [leaves, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩
      · exact hx s hl p hp
      · exact hy t hr p hp

private theorem delayed_self (N : Nat) (g : Source) : DelayedMatches N g g := by
  induction g with
  | of b =>
    intro p hp
    have hp' : p = [] := by simpa [leaves] using hp
    subst p
    have hb : leafBit (.of b) [] = b := by cases b <;> rfl
    simpa only [List.nil_append, hb] using (leaf_separation N b (.of b)).mpr rfl
  | mul x y hx hy =>
    have hm : substitution^[N] (.mul x y) = .mul (substitution^[N] x) (substitution^[N] y) :=
      Function.Semiconj₂.iterate (fun a b => substitution.map_mul a b) N x y
    intro p hp
    simp only [leaves, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩
    · simpa only [hm, List.cons_append, readout, leafBit] using hx p hp
    · simpa only [hm, List.cons_append, readout, leafBit] using hy p hp

/-- The delayed certificate identifies the whole original source over all finite trees. -/
theorem delayed_template_certificate (N : Nat) (g u : Source) :
    DelayedMatches N g u ↔ u = g := by
  constructor
  · intro h
    exact ActualTreeReadoutAcquisition.source_foundation.2.2.1 g u
      (delayed_leaf_reflection N g u h)
  · intro he
    subst u
    exact delayed_self N g

private theorem probe_injective (N : Nat) (g : Source) :
    Set.InjOn (fun p => p ++ rights (leafDelay N (leafBit g p))) {p | p ∈ leaves g} := by
  intro p hp q hq he
  have hp' := leaf_bit_reply g p hp
  have hq' := leaf_bit_reply g q hq
  have leafNode := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have leafPrefix := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.1
  have cp : p.IsPrefix (p ++ rights (leafDelay N (leafBit g p))) := List.prefix_append _ _
  have cq : q.IsPrefix (p ++ rights (leafDelay N (leafBit g p))) := by
    rw [show p ++ rights (leafDelay N (leafBit g p)) = q ++ rights (leafDelay N (leafBit g q)) from he]
    exact List.prefix_append _ _
  rcases List.prefix_or_prefix_of_prefix cp cq with h | h
  · exact (leafPrefix g p q (leafBit g p) (leafBit g q)
      (leafNode g p (leafBit g p) hp') (leafNode g q (leafBit g q) hq') h).1
  · exact (leafPrefix g q p (leafBit g q) (leafBit g p)
      (leafNode g q (leafBit g q) hq') (leafNode g p (leafBit g p) hp') h).1.symm

/-- Sum of original leaf depths. -/
def leafAddressSum (g : Source) : Nat := ((leaves g).map List.length).sum

/-- Maximum delayed probe length, with zero as the empty-list default. -/
def delayedRadius (N : Nat) (g : Source) : Nat :=
  ((leaves g).map (fun p => p.length + N/2 + N%2 * (if leafBit g p then 0 else 1))).foldr max 0

private theorem leaf_list_counts (g : Source) :
    (leaves g).length = g.length ∧
    ((leaves g).map (fun p => if leafBit g p then 0 else 1)).sum = (composition g).2 := by
  have hn := (ActualJointResponseCostCore.cost_foundation.1 g).1
  have hc := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 g).1
  have hb := (ActualImageAddressCertificate.leaf_data g).2
  constructor
  · simpa only [leafAddresses, List.toFinset_card_of_nodup hn] using hc
  · have pointwise : ((leaves g).map (fun p => if leafBit g p then 0 else 1)) =
        (leaves g).map (fun p => if readout p g = .beta then 1 else 0) := by
      apply List.map_congr_left
      intro p hp
      have hr := leaf_bit_reply g p hp
      cases hb : leafBit g p <;> simp [hb, leafReply] at hr ⊢ <;> simp [hr]
    have filterSum (ps : List Address) :
        (ps.map (fun p => if readout p g = .beta then 1 else 0)).sum =
          (ps.filter (fun p => readout p g = .beta)).length := by
      induction ps with
      | nil => rfl
      | cons p ps ih =>
        by_cases hb : readout p g = .beta <;> simp [hb, ih, Nat.add_comm]
    have heq : ((leaves g).map (fun p => if leafBit g p then 0 else 1)).sum =
        ((leaves g).filter (fun p => readout p g = .beta)).length := by
      rw [pointwise]; exact filterSum (leaves g)
    rw [heq]
    have hf := hn.filter (fun p => readout p g = .beta)
    change ((leaves g).toFinset.filter (fun p => readout p g = .beta)).card = _ at hb
    rw [List.filter_toFinset, List.toFinset_card_of_nodup hf] at hb
    exact hb

/-- Distinct physical probes attain the exact original-leaf count, word sum and radius. -/
theorem delayed_template_resources (N : Nat) (g : Source) :
    (templateQueries N g).Nodup ∧
    (templateQueries N g).length = g.length ∧
    ((templateQueries N g).map List.length).sum =
      leafAddressSum g + (N/2)*g.length + (N%2)*(composition g).2 ∧
    ((templateQueries N g).map List.length).foldr max 0 = delayedRadius N g := by
  have hn := (ActualJointResponseCostCore.cost_foundation.1 g).1
  have hc := leaf_list_counts g
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hn.map_on (probe_injective N g)
  · simpa [templateQueries] using hc.1
  · simp only [templateQueries, List.map_map, Function.comp_def,
      List.length_append, rights, List.length_replicate, leafDelay]
    simp only [List.sum_map_add, List.sum_map_mul_left, List.map_const', List.sum_replicate, leafAddressSum,
      hc.1, hc.2, smul_eq_mul]
    ring
  · simp [templateQueries, delayedRadius, List.map_map, Function.comp_def, rights, leafDelay,
      Nat.add_assoc]

private theorem template_check_correct (N : Nat) (g u : Source) :
    templateCheck N g ((templateQueries N g).map (fun q => readout q (substitution^[N] u))) = true ↔
      u = g := by
  rw [← delayed_template_certificate N g u]
  simp only [templateCheck, decide_eq_true_eq, templateQueries, templateExpected,
    List.map_map, Function.comp_def, List.map_eq_map_iff]
  rfl

/-- A finite full-list physical checker terminates and pays once per original template leaf. -/
theorem delayed_template_service (N : Nat) (g u : Source) :
    let qs := templateQueries N g
    let finish := fun h : Hist (fun _ : Address => Reply) => templateCheck N g (h.map Sigma.snd)
    execute readout (listController qs finish) (qs.length+1) [] (substitution^[N] u) =
      some (listTrace qs (substitution^[N] u),
        templateCheck N g ((qs.map (fun q => readout q (substitution^[N] u))))) ∧
    (templateCheck N g (qs.map (fun q => readout q (substitution^[N] u))) = true ↔ u = g) ∧
    (listTrace qs (substitution^[N] u)).length = g.length ∧
    (((listTrace qs (substitution^[N] u)).map (fun a => a.1.length)).sum =
      leafAddressSum g + (N/2)*g.length + (N%2)*(composition g).2) ∧
    (((listTrace qs (substitution^[N] u)).map (fun a => a.1.length)).foldr max 0 = delayedRadius N g) := by
  dsimp only
  have run := (fixed_list_execution (templateQueries N g)
    (fun h => templateCheck N g (h.map Sigma.snd)) (substitution^[N] u)).2.1
  simp only [listTrace, List.map_map, Function.comp_def] at run
  have hr := delayed_template_resources N g
  refine ⟨run, template_check_correct N g u, ?_, ?_, ?_⟩
  · simpa [listTrace] using hr.2.1
  · simpa [listTrace, List.map_map, Function.comp_def] using hr.2.2.1
  · simpa [listTrace, List.map_map, Function.comp_def] using hr.2.2.2

#print axioms delayed_template_service
end D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate
