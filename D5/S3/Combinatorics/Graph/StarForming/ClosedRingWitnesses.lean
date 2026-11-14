/- GID: D5/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/ClosedRingWitnesses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual local selections and deletion witnesses for the closed-high modules. -/

import D5.S3.Combinatorics.Graph.StarForming.ClosedModule

/-! The original uniform selections in CLOSED_HIGH_CYCLE_COMPENSATION,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. This is finite local certificate data; the all-size ring
claims require symbolic assembly and actual finite fiber counts. -/

namespace D5.S3.Combinatorics.Graph.StarForming.ClosedRingWitnesses
open StarFormingDissociationRefutation ClosedModule

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def forming (v : Fin 62) : Prop := v.val<12 ∨
  (20≤v.val ∧ Cubic.fanoSelected ⟨(v.val-20)%14,by omega⟩)
instance (v : Fin 62) : Decidable (forming v) := inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

def failure (v : Fin 62) : Fin 62 :=
  if h0 : v.val<6 then ⟨12+v.val,by omega⟩ else
  if h1 : v.val<12 then ⟨6+v.val,by omega⟩ else
  if h2 : 20≤v.val then
    ⟨20+14*((v.val-20)/14)+(Cubic.fanoFailure ⟨(v.val-20)%14,by omega⟩).val,by
      have := (Cubic.fanoFailure ⟨(v.val-20)%14,by omega⟩).isLt
      have := v.isLt
      omega⟩
  else 0

def independent (v : Fin 62) : Prop :=
  (v.val<6 ∧ v.val%2=1) ∨ (6≤v.val ∧ v.val<12) ∨
  (12≤v.val ∧ v.val<18 ∧ v.val%2=0) ∨ (20≤v.val ∧ (v.val-20)%14<7)
instance (v : Fin 62) : Decidable (independent v) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _ ∧ _) ∨ (_ ∧ _)))

private theorem forms : Regular.Forms graph.Adj forming := by
  unfold Regular.Forms Regular.TwoAt
  decide +kernel

private theorem failures : ∀ d : Fin 62, forming d →
    ¬ (forming (failure d) ∧ failure d≠d) ∧
    ¬ Regular.TwoAt graph.Adj (fun v => forming v ∧ v≠d) (failure d) := by
  unfold Regular.TwoAt
  decide +kernel

/-- The original thirty-six-set is minimal, with explicit actual failures. -/
theorem forming_certificates : Regular.Minimal graph.Adj forming ∧
    (Finset.univ.filter forming).card=36 := by
  exact ⟨Subcubic.minimal_of_deletion_failures _ _ forms
    (fun d hd => ⟨failure d,failures d hd⟩),by decide +kernel⟩

/-- The original twelve-plus-three-seven witness is a dissociation thirty-three-set. -/
theorem independent_certificates :
    DissociationCover.Dissociates graph.Adj independent ∧
    (Finset.univ.filter independent).card=33 := by
  constructor
  · unfold DissociationCover.Dissociates
    decide +kernel
  · decide +kernel

def color (v : Fin 62) : Fin 2 :=
  if v.val<6 then ⟨v.val%2,by omega⟩ else
  if v.val<12 then ⟨(v.val+1)%2,by omega⟩ else
  if v.val<20 then ⟨v.val%2,by omega⟩ else
  if (v.val-20)%14<7 then 0 else 1

/-- The source bipartition and all local neighbor lists are checked exactly. -/
theorem local_class :
    (∀ v w : Fin 62, graph.Adj v w → color v≠color w) ∧
    (∀ v : Fin 62, (neighbors v).Nodup) ∧
    (∀ v : Fin 62, (neighbors v).length=if v=12 ∨ v=17 then 2 else 3) := by
  decide +kernel

/-- Both open interface vertices are omitted by the forming witness; the
independence witness selects only the even one. -/
theorem interface_states : ¬ forming 12 ∧ ¬ forming 17 ∧
    independent 12 ∧ ¬ independent 17 ∧ color 12=0 ∧ color 17=1 := by
  decide +kernel

end D5.S3.Combinatorics.Graph.StarForming.ClosedRingWitnesses
