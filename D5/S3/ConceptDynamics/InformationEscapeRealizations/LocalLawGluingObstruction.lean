/- GID: D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three pulled-back local laws realize the gluing obstruction with four kernel classes. -/

import D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction

/- Library-search audit trail (2026-09-04): the source relations, frozen theorem,
   Boolean ADMIT bridge, and typed bundle compiler are exact repository hits and
   reused. No existing legacy realization or gluing partition certificate was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction

open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction

/-- The three pair laws pulled back along the projections of a global-state attempt. -/
def localLawGluingRealization : PrimitiveRealization localLawGluingSignature where
  readout
    | .admit01 => fun state => decide (state.1 = state.2.1)
    | .admit12 => fun state => decide (state.2.1 = state.2.2)
    | .admit02 => fun state => decide (state.1 ≠ state.2.2)
  anchor := fun i => Fin.elim0 i

/-- The frozen gluing statement is equivalent to its object-bound ADMIT law. -/
theorem compatible_local_laws_can_lack_global_state_realization :
    LegacyPrimitiveRealization localLawGluingArena LocalLawGluingStatement
      localLawGluingRealization := by
  refine ⟨?_⟩
  have h01_snd (b : Bool) :
      (∃ state : Bool × Bool × Bool,
        localLawGluingRealization.readout .admit01 state = true /\ state.2.1 = b) ↔
        b ∈ Prod.snd '' sameLaw := by
    constructor
    · rintro ⟨state, h01, rfl⟩
      refine ⟨(state.1, state.2.1), ?_, rfl⟩
      exact (admit_readout_eq_true_iff
        (fun s : Bool × Bool × Bool => s.1 = s.2.1) state).1 h01
    · rintro ⟨pair, hpair, rfl⟩
      refine ⟨(pair.1, pair.2, false), ?_, rfl⟩
      exact (admit_readout_eq_true_iff
        (fun s : Bool × Bool × Bool => s.1 = s.2.1)
        (pair.1, pair.2, false)).2 hpair
  have h01_fst (b : Bool) :
      (∃ state : Bool × Bool × Bool,
        localLawGluingRealization.readout .admit01 state = true /\ state.1 = b) ↔
        b ∈ Prod.fst '' sameLaw := by
    constructor
    · rintro ⟨state, h01, rfl⟩
      refine ⟨(state.1, state.2.1), ?_, rfl⟩
      exact (admit_readout_eq_true_iff
        (fun s : Bool × Bool × Bool => s.1 = s.2.1) state).1 h01
    · rintro ⟨pair, hpair, rfl⟩
      refine ⟨(pair.1, pair.2, false), ?_, rfl⟩
      exact (admit_readout_eq_true_iff
        (fun s : Bool × Bool × Bool => s.1 = s.2.1)
        (pair.1, pair.2, false)).2 hpair
  have h12_fst (b : Bool) :
      (∃ state : Bool × Bool × Bool,
        localLawGluingRealization.readout .admit12 state = true /\ state.2.1 = b) ↔
        b ∈ Prod.fst '' sameLaw := by
    constructor
    · rintro ⟨state, h12, rfl⟩
      refine ⟨(state.2.1, state.2.2), ?_, rfl⟩
      exact (admit_readout_eq_true_iff
        (fun s : Bool × Bool × Bool => s.2.1 = s.2.2) state).1 h12
    · rintro ⟨pair, hpair, rfl⟩
      refine ⟨(false, pair.1, pair.2), ?_, rfl⟩
      exact (admit_readout_eq_true_iff
        (fun s : Bool × Bool × Bool => s.2.1 = s.2.2)
        (false, pair.1, pair.2)).2 hpair
  have h12_snd (b : Bool) :
      (∃ state : Bool × Bool × Bool,
        localLawGluingRealization.readout .admit12 state = true /\ state.2.2 = b) ↔
        b ∈ Prod.snd '' sameLaw := by
    constructor
    · rintro ⟨state, h12, rfl⟩
      refine ⟨(state.2.1, state.2.2), ?_, rfl⟩
      exact (admit_readout_eq_true_iff
        (fun s : Bool × Bool × Bool => s.2.1 = s.2.2) state).1 h12
    · rintro ⟨pair, hpair, rfl⟩
      refine ⟨(false, pair.1, pair.2), ?_, rfl⟩
      exact (admit_readout_eq_true_iff
        (fun s : Bool × Bool × Bool => s.2.1 = s.2.2)
        (false, pair.1, pair.2)).2 hpair
  have h02_fst (b : Bool) :
      (∃ state : Bool × Bool × Bool,
        localLawGluingRealization.readout .admit02 state = true /\ state.1 = b) ↔
        b ∈ Prod.fst '' differentLaw := by
    constructor
    · rintro ⟨state, h02, rfl⟩
      refine ⟨(state.1, state.2.2), ?_, rfl⟩
      exact (admit_readout_eq_true_iff
        (fun s : Bool × Bool × Bool => s.1 ≠ s.2.2) state).1 h02
    · rintro ⟨pair, hpair, rfl⟩
      refine ⟨(pair.1, false, pair.2), ?_, rfl⟩
      exact (admit_readout_eq_true_iff
        (fun s : Bool × Bool × Bool => s.1 ≠ s.2.2)
        (pair.1, false, pair.2)).2 hpair
  have h02_snd (b : Bool) :
      (∃ state : Bool × Bool × Bool,
        localLawGluingRealization.readout .admit02 state = true /\ state.2.2 = b) ↔
        b ∈ Prod.snd '' differentLaw := by
    constructor
    · rintro ⟨state, h02, rfl⟩
      refine ⟨(state.1, state.2.2), ?_, rfl⟩
      exact (admit_readout_eq_true_iff
        (fun s : Bool × Bool × Bool => s.1 ≠ s.2.2) state).1 h02
    · rintro ⟨pair, hpair, rfl⟩
      refine ⟨(pair.1, false, pair.2), ?_, rfl⟩
      exact (admit_readout_eq_true_iff
        (fun s : Bool × Bool × Bool => s.1 ≠ s.2.2)
        (pair.1, false, pair.2)).2 hpair
  constructor
  · rintro ⟨⟨hSndSame, hFstOuter, hSndOuter⟩, hNoGlobal⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b
      calc
        _ ↔ b ∈ Prod.snd '' sameLaw := h01_snd b
        _ ↔ b ∈ Prod.fst '' sameLaw := by rw [hSndSame]
        _ ↔ _ := (h12_fst b).symm
    · intro b
      calc
        _ ↔ b ∈ Prod.fst '' sameLaw := h01_fst b
        _ ↔ b ∈ Prod.fst '' differentLaw := by rw [hFstOuter]
        _ ↔ _ := (h02_fst b).symm
    · intro b
      calc
        _ ↔ b ∈ Prod.snd '' sameLaw := h12_snd b
        _ ↔ b ∈ Prod.snd '' differentLaw := by rw [hSndOuter]
        _ ↔ _ := (h02_snd b).symm
    · rintro ⟨state, h01, h12, h02⟩
      apply hNoGlobal
      refine ⟨state, ?_, ?_, ?_⟩
      · exact (admit_readout_eq_true_iff
          (fun s : Bool × Bool × Bool => s.1 = s.2.1) state).1 h01
      · exact (admit_readout_eq_true_iff
          (fun s : Bool × Bool × Bool => s.2.1 = s.2.2) state).1 h12
      · exact (admit_readout_eq_true_iff
          (fun s : Bool × Bool × Bool => s.1 ≠ s.2.2) state).1 h02
  · intro hLaw
    constructor
    · refine ⟨Set.ext ?_, Set.ext ?_, Set.ext ?_⟩
      · intro b
        exact (h01_snd b).symm.trans (hLaw.1 b) |>.trans (h12_fst b)
      · intro b
        exact (h01_fst b).symm.trans (hLaw.2.1 b) |>.trans (h02_fst b)
      · intro b
        exact (h12_snd b).symm.trans (hLaw.2.2.1 b) |>.trans (h02_snd b)
    · rintro ⟨state, h01, h12, h02⟩
      apply hLaw.2.2.2
      refine ⟨state, ?_, ?_, ?_⟩
      · simpa [localLawGluingRealization] using
          (admit_readout_eq_true_iff
            (fun s : Bool × Bool × Bool => s.1 = s.2.1) state).2 h01
      · simpa [localLawGluingRealization] using
          (admit_readout_eq_true_iff
            (fun s : Bool × Bool × Bool => s.2.1 = s.2.2) state).2 h12
      · simpa [localLawGluingRealization] using
          (admit_readout_eq_true_iff
            (fun s : Bool × Bool × Bool => s.1 ≠ s.2.2) state).2 h02

/-- The three ADMIT bits induce exactly the four census kernel classes. -/
theorem compatible_local_laws_can_lack_global_state_partition_count :
    (Finset.univ.image (fun state : Bool × Bool × Bool =>
      (localLawGluingRealization.readout .admit01 state,
        localLawGluingRealization.readout .admit12 state,
        localLawGluingRealization.readout .admit02 state))).card = 4 := by
  decide

/-- The private census pair `000,001` is separated by the outer ADMIT slot. -/
theorem compatible_local_laws_can_lack_global_state_private_pair :
    ¬ localLawGluingRealization.toPrimitiveBundle.agrees
      (false, false, false) (false, false, true) := by
  decide

example : localLawGluingArena.toArena.Nondegenerate := by decide

end D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
