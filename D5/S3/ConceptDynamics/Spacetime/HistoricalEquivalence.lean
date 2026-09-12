/- GID: D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/HistoricalEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.encoded_equality_converse_claim; result=D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.encoded_equality_converse_refuted; claim=D5/S3/ConceptDynamics/Spacetime/HistoricalEquivalence.encoded_equality_converse_claim
   digest: Historical isomorphism preserves all archive data and the signed readout. -/

import D5.S0.History.Spacetime.ArchiveCarrier
import D5.S0.History.Spacetime.ArchiveEncoding
import D5.S3.ConceptDynamics.Spacetime.ComplementCharge
import Mathlib.Data.Finset.BooleanAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Spacetime.HistoricalEquivalence

open D5.S0.History.Spacetime
open HFEncoding ArchiveCarrier ArchiveEncoding ComplementCharge

noncomputable section
local instance : DecidableEq HF := Classical.decEq _

structure HistoricalIsoData {d : Nat} (x y : Rich d)
    extends ArchiveEmbedding x.1.archive y.1.archive where
  onto : Function.Surjective eventMap
  current_image : Finset.map eventMap x.1.current = y.1.current
  selection_image : Finset.map eventMap x.2.val = y.2.val

def HistoricalIsoData.eventEquiv {d : Nat} {x y : Rich d} (h : HistoricalIsoData x y) :
    x.1.archive.Event ≃ y.1.archive.Event :=
  Equiv.ofBijective h.eventMap ⟨h.eventMap.injective, h.onto⟩

def HistoricalIso {d : Nat} (x y : Rich d) : Prop := Nonempty (HistoricalIsoData x y)

/- The parallel-versus-temporal nonisomorphism is reserved for the B2 worked-history
   specialization, where the two causal relations are available. -/

theorem historical_iso_refl {d : Nat} (x : Rich d) : HistoricalIso x x := by
  refine ⟨HistoricalIsoData.mk (ArchiveEmbedding.refl _) ?_ ?_ ?_⟩
  · exact Function.surjective_id
  · simp [ArchiveEmbedding.refl]
  · simp [ArchiveEmbedding.refl]

theorem historical_iso_symm {d : Nat} {x y : Rich d}
    (h : HistoricalIso x y) : HistoricalIso y x := by
  rcases h with ⟨h⟩
  let e := h.eventEquiv
  let a : ArchiveEmbedding y.1.archive x.1.archive :=
    { eventMap := e.symm.toEmbedding
      attributes_eq := by
        intro u
        have ha := h.attributes_eq (e.symm u)
        change y.1.archive.attributes (e (e.symm u)) = _ at ha
        simpa using ha.symm
      causal_iff := by
        intro u v
        have hc := h.causal_iff (e.symm u) (e.symm v)
        change y.1.archive.causal (e (e.symm u)) (e (e.symm v)) ↔ _ at hc
        simpa using hc.symm }
  refine ⟨HistoricalIsoData.mk a e.symm.surjective ?_ ?_⟩
  · change Finset.map e.symm.toEmbedding y.1.current = x.1.current
    have hc : Finset.map e.toEmbedding x.1.current = y.1.current := h.current_image
    rw [← hc, Finset.map_map]
    simp
  · change Finset.map e.symm.toEmbedding y.2.val = x.2.val
    have hs : Finset.map e.toEmbedding x.2.val = y.2.val := h.selection_image
    rw [← hs, Finset.map_map]
    simp

theorem historical_iso_trans {d : Nat} {x y z : Rich d}
    (h : HistoricalIso x y) (k : HistoricalIso y z) : HistoricalIso x z := by
  rcases h with ⟨h⟩
  rcases k with ⟨k⟩
  refine ⟨HistoricalIsoData.mk
    (ArchiveEmbedding.comp h.toArchiveEmbedding k.toArchiveEmbedding)
    (k.onto.comp h.onto) ?_ ?_⟩
  · change Finset.map (h.eventMap.trans k.eventMap) x.1.current = z.1.current
    rw [← Finset.map_map, h.current_image, k.current_image]
  · change Finset.map (h.eventMap.trans k.eventMap) x.2.val = z.2.val
    rw [← Finset.map_map, h.selection_image, k.selection_image]

theorem encoded_equality_implies_historical {d : Nat} {x y : Rich d}
    (h : richCode x = richCode y) : HistoricalIso x y := by
  have hxy : x = y := richCode_injective h
  subst y
  exact historical_iso_refl x

theorem historical_iso_readout_eq {d : Nat} {x y : Rich d}
    (h : HistoricalIso x y) : q x = q y := by
  rcases h with ⟨h⟩
  change (∑ e ∈ x.2.val, contribution x.1 e) =
    ∑ e ∈ y.2.val, contribution y.1 e
  calc
    (∑ e ∈ x.2.val, contribution x.1 e) =
        ∑ e ∈ x.2.val, contribution y.1 (h.eventMap e) := by
      apply Finset.sum_congr rfl
      intro e he
      simp [contribution, h.attributes_eq]
    _ = ∑ e ∈ y.2.val, contribution y.1 e := by
      rw [← h.selection_image, Finset.sum_map]

def encoded_equality_converse_claim : Prop :=
  ∀ {x y : Rich 3}, HistoricalIso x y → richCode x = richCode y

def singletonHistory (d : Nat) (e : HF) : Rich d :=
  let a : Archive d := {
    events := {e}
    attributes := fun _ =>
      { time := 0, position := fun _ => 0, positive := true, source := FreeMagma.of 0 }
    causal := fun _ _ => False
    irrefl := by simp
    trans := by simp
    time_lt := by simp }
  let c : Context d := { archive := a, current := Finset.univ }
  ⟨c, ⟨∅, Finset.empty_subset _⟩⟩

theorem singletonRenaming (d : Nat) (e f : HF) :
    HistoricalIso (singletonHistory d e) (singletonHistory d f) := by
  let ev : (singletonHistory d e).1.archive.Event ≃
      (singletonHistory d f).1.archive.Event :=
    { toFun := fun _ => ⟨f, by simp [singletonHistory]⟩
      invFun := fun _ => ⟨e, by simp [singletonHistory]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact (Finset.mem_singleton.mp x.property).symm
      right_inv := by
        intro x
        apply Subtype.ext
        exact (Finset.mem_singleton.mp x.property).symm }
  let a : ArchiveEmbedding (singletonHistory d e).1.archive (singletonHistory d f).1.archive :=
    { eventMap := ev.toEmbedding
      attributes_eq := by simp [singletonHistory]
      causal_iff := by simp [singletonHistory] }
  refine ⟨HistoricalIsoData.mk a ev.surjective ?_ ?_⟩
  · change Finset.map ev.toEmbedding Finset.univ = Finset.univ
    exact Finset.map_univ_equiv ev
  · change Finset.map ev.toEmbedding ∅ = ∅
    exact Finset.map_empty _

theorem singleton_codes_differ (d : Nat) :
    richCode (singletonHistory d (natCode 0)) ≠ richCode (singletonHistory d (natCode 1)) := by
  intro h
  have hxy := richCode_injective h
  have he := congrArg (fun z : Rich d => z.1.archive.events) hxy
  have h01 : natCode 0 = natCode 1 := by simpa [singletonHistory] using he
  exact (by decide : (0 : Nat) ≠ 1) (natCode_inj.mp h01)

theorem historical_iso_is_not_code_equality (d : Nat) :
    HistoricalIso (singletonHistory d (natCode 0)) (singletonHistory d (natCode 1)) ∧
      richCode (singletonHistory d (natCode 0)) ≠ richCode (singletonHistory d (natCode 1)) :=
  ⟨singletonRenaming d _ _, singleton_codes_differ d⟩

theorem encoded_equality_converse_refuted : ¬ encoded_equality_converse_claim := by
  intro h
  obtain ⟨hiso, hcode⟩ := historical_iso_is_not_code_equality 3
  exact hcode (h hiso)

end
end D5.S3.ConceptDynamics.Spacetime.HistoricalEquivalence
