/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativePromiseCausalBoundary
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Every native promised comb has the causal history inverse and opposite legal slot orders. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointCausalOrder
import D5.S3.Arith.FibonacciAtomic.FourExitRawEndpointSpectrum

/-! All-assignment native promise and the causal versus serial history boundary. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativePromiseCausalBoundary

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address readout)
open ActualLeafHistoryRigidity (OutputContext)
open NativeMaterialRootRecognition (D)
open NativeGuardedLeafRepair (Call run context_run D_mul)
open NativeFreshSensorGrowth (run_append)
open NativeEndpointEventIdeals
open FourExitRawEndpointSpectrum (comb)
open ActualImageSevenLeafSeparation (E A)

/-- The original gadgets D1=A and D0=z, with C=E. -/
def slot (b : Bool) : Source := if b then A else FourExitRawEndpointSpectrum.z

/-- The four-leaf marker ((C,alpha),alpha), retaining the original cone. -/
def marker : Source := .mul (NativeFreshSensorGrowth.cone false) (.of true)

/-- All assignments, with no support, group, sampling or controller restriction. -/
def promise (N : ℕ) (z : Fin (15 * N) → Bool) : Source :=
  comb (15 * N) (fun i => slot (z i)) marker

private theorem domain_slot (b : Bool) : D (slot b) := by
  have ha : D (.of true) := NativeGuardedLeafRepair.alphaRHistory.domain
  have hb : D (.of false) := NativeGuardedLeafRepair.betaFHistory.domain
  have hc : D E := (D_mul _ _).mpr ⟨hb, ha, by simp [readout]⟩
  cases b
  · exact (D_mul _ _).mpr ⟨hb, hc, by simp [readout]⟩
  · exact (D_mul _ _).mpr ⟨hc, hb, by simp [E, readout]⟩

private theorem domain_marker : D marker := by
  have ha : D (.of true) := NativeGuardedLeafRepair.alphaRHistory.domain
  have hb : D (.of false) := NativeGuardedLeafRepair.betaFHistory.domain
  have hc : D E := (D_mul _ _).mpr ⟨hb, ha, by simp [readout]⟩
  have hca : D (.mul E (.of true)) :=
    (D_mul _ _).mpr ⟨hc, ha, by simp [E, readout]⟩
  exact (D_mul _ _).mpr ⟨hca, ha, by simp [NativeFreshSensorGrowth.cone, readout]⟩

private theorem domain_comb (k : ℕ) (f : Fin k → Bool) :
    D (comb k (fun i => slot (f i)) marker) := by
  induction k with
  | zero => exact domain_marker
  | succ k ih =>
      apply (D_mul _ _).mpr
      exact ⟨domain_slot (f 0), ih (fun i => f i.succ), by cases h : f 0 <;>
        simp [slot, h, A, FourExitRawEndpointSpectrum.z, readout]⟩

private theorem native_existence (b : Bool) (t : Source) (hb : Born b t) :
    ∃ w, run (.of b) w = some t := by
  obtain ⟨l, hl⟩ :=
    (D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity.result
      (∅ : Set (Event b t)) Set.univ isLowerSet_empty isLowerSet_univ
      (Set.empty_subset _)).2.1
  have hr := (execution_adequacy b t hb ∅ Set.univ isLowerSet_empty isLowerSet_univ l).mp hl
  have re : raw b t ∅ = ∅ := by ext e; simp [raw]
  have ru : raw b t Set.univ = (events b t : Set Call) := by ext e; simp [raw]
  have ce := partial_empty b t hb
  have cf := cut_full b t hb
  rw [re, ru, ce, cf] at hr
  exact ⟨_, hr⟩

/-- Literal two-event insertions into C, before any ambient address shift. -/
private def insertion (b : Bool) : List Call :=
  if b then [.split [false], .promote [true]] else [.promote [true], .split [true]]

private theorem insertion_run (b : Bool) : run E (insertion b) = some (slot b) := by
  cases b <;> rfl

private theorem opposite_slots (a b : Bool) (r : Source) :
    ∃ w v, w ≠ v ∧
      run (.mul E (.mul E r)) w = some (.mul (slot a) (.mul (slot b) r)) ∧
      run (.mul E (.mul E r)) v = some (.mul (slot a) (.mul (slot b) r)) := by
  let u := (insertion a).map (Call.shift [false])
  let v := (insertion b).map (Call.shift [true, false])
  have h00 := context_run (.left .hole (.mul E r)) (insertion_run a)
  have h01 := context_run (.right (slot a) (.left .hole r)) (insertion_run b)
  have h10 := context_run (.right E (.left .hole r)) (insertion_run b)
  have h11 := context_run (.left .hole (.mul (slot b) r)) (insertion_run a)
  have hne : u ++ v ≠ v ++ u := by
    cases a <;> cases b <;> decide
  exact ⟨u ++ v, v ++ u, hne, run_append h00 h01, run_append h10 h11⟩

private theorem two_slot_histories (n : ℕ) (hn : 2 ≤ n) (z : Fin n → Bool) :
    ∃ w v : List Call, w ≠ v ∧
      run (.of true) w = some (comb n (fun i => slot (z i)) marker) ∧
      run (.of true) v = some (comb n (fun i => slot (z i)) marker) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have hkt : n = k + 2 := by omega
  clear hk
  subst n
  let r := comb k (fun i => slot (z i.succ.succ)) marker
  have hp : comb (k + 2) (fun i => slot (z i)) marker =
      .mul (slot (z 0)) (.mul (slot (z 1)) r) := rfl
  have hbase : D (.mul E (.mul E r)) := by
    have ha : D (.of true) := NativeGuardedLeafRepair.alphaRHistory.domain
    have hb : D (.of false) := NativeGuardedLeafRepair.betaFHistory.domain
    have he : D E := (D_mul _ _).mpr ⟨hb, ha, by simp [readout]⟩
    have hr := domain_comb k (fun i => z i.succ.succ)
    exact (D_mul _ _).mpr ⟨he, (D_mul _ _).mpr ⟨he, hr, by simp [E, readout]⟩,
      by simp [E, readout]⟩
  obtain ⟨p, hprep⟩ := native_existence true (.mul E (.mul E r)) ⟨hbase, by simp⟩
  obtain ⟨u, v, hne, hu, hv⟩ := opposite_slots (z 0) (z 1) r
  refine ⟨p ++ u, p ++ v, ?_, ?_, ?_⟩
  · exact fun h => hne (List.append_cancel_left h)
  · rw [hp]
    exact run_append hprep hu
  · rw [hp]
    exact run_append hprep hv

private theorem prefix_run (s t : Source) (p q : List Call)
    (h : run s (p ++ q) = some t) : ∃ u, run s p = some u := by
  induction p generalizing s with
  | nil => exact ⟨s, rfl⟩
  | cons e p ih =>
      simp only [List.cons_append] at h
      cases e with
      | promote a =>
          unfold run at h
          split at h <;> try contradiction
          next hg =>
            obtain ⟨u, hu⟩ := ih _ h
            exact ⟨u, by simpa [run, hg] using hu⟩
      | split a =>
          unfold run at h
          split at h <;> try contradiction
          next hg =>
            obtain ⟨u, hu⟩ := ih _ h
            exact ⟨u, by simpa [run, hg] using hu⟩

/-- On the full promised family the bare endpoint determines the labelled
causal order and its exact successful histories, while opposite complete slot
insertion orders give different successful serial words at that same endpoint. -/
theorem result (N : ℕ) (hN : 4 ≤ N) (z : Fin (15 * N) → Bool) :
    D (promise N z) ∧
    (∀ w : List Call, run (.of true) w = some (promise N z) ↔
      ∃ l : List (Event true (promise N z)), l.map Subtype.val = w ∧
        D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity.ExtensionList
          ∅ Set.univ l) ∧
    (∀ p q : List Call, run (.of true) (p ++ q) = some (promise N z) →
      ∃ u, run (.of true) p = some u) ∧
    (∀ c d : Event true (promise N z),
      Relation.TransGen (NativeEndpointCausalOrder.Edge true (promise N z)) c.1 d.1 ↔ c < d) ∧
    (∃ w v : List Call, w ≠ v ∧
      run (.of true) w = some (promise N z) ∧ run (.of true) v = some (promise N z)) := by
  have hd := domain_comb (15 * N) z
  exact ⟨hd, all_histories (promise N z) hd,
    fun p q h => prefix_run _ _ p q h,
    NativeEndpointCausalOrder.result true (promise N z),
    two_slot_histories (15 * N) (by omega) z⟩

end D5.S3.Arith.FibonacciAtomic.Geometry.NativePromiseCausalBoundary
