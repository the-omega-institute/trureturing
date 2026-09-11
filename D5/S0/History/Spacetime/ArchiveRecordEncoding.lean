/- GID: D5/S0/History/Spacetime/ArchiveRecordEncoding
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/ArchiveRecordEncoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Legal finite graph records reconstruct exact causal archives with reflected time constraints. -/

import D5.S0.History.Spacetime.CoordinateEncoding
import D5.S0.History.Spacetime.FiniteGraphEncoding

set_option autoImplicit false

namespace D5.S0.History.Spacetime.ArchiveRecordEncoding

open HFEncoding ArchiveCarrier CoordinateEncoding FiniteGraphEncoding
noncomputable section

/-- The four attribute functions are bundled pointwise into one tuple-valued graph. -/
@[ext] structure Record where
  events : Finset HF
  attributes : HF
  causal : HF

/-- Legality is checked on graph members and uniquely decoded attribute tuples.
It is independent of the archive encoder and does not assert that an archive exists. -/
structure Legal (d : Nat) (r : Record) : Prop where
  graph : IsFunctionGraph r.events (IsAttributesCode d) r.attributes
  endpoints : IsRelationCode r.events r.causal
  irrefl : ∀ e : r.events, ¬ mem (pair e.val e.val) r.causal
  trans : ∀ e f g : r.events, mem (pair e.val f.val) r.causal →
    mem (pair f.val g.val) r.causal → mem (pair e.val g.val) r.causal
  time_lt : ∀ e f : r.events, mem (pair e.val f.val) r.causal →
    (decodeGraph (attributes_code_equiv d) r.attributes graph e).time <
    (decodeGraph (attributes_code_equiv d) r.attributes graph f).time

def archiveRecord {d : Nat} (a : Archive d) : Record :=
  ⟨a.events, graphCode a.events (attributes_code_equiv d) a.attributes,
    relationCode a.events a.causal⟩

theorem archiveRecord_legal {d : Nat} (a : Archive d) : Legal d (archiveRecord a) where
  graph := graphCode_valid a.events (attributes_code_equiv d) a.attributes
  endpoints := relationCode_valid a.events a.causal
  irrefl e he := a.irrefl e ((pair_mem_relationCode a.events a.causal e e).mp he)
  trans e f g hef hfg := (pair_mem_relationCode a.events a.causal e g).mpr
    (a.trans e f g ((pair_mem_relationCode a.events a.causal e f).mp hef)
      ((pair_mem_relationCode a.events a.causal f g).mp hfg))
  time_lt e f hef := by
    have ht := a.time_lt e f ((pair_mem_relationCode a.events a.causal e f).mp hef)
    simpa only [archiveRecord, decodeGraph_encode] using ht

def reconstructArchive {d : Nat} (r : Record) (h : Legal d r) : Archive d where
  events := r.events
  attributes := decodeGraph (attributes_code_equiv d) r.attributes h.graph
  causal := decodeRelation r.events r.causal
  irrefl := h.irrefl
  trans := h.trans
  time_lt := h.time_lt

/-- The entire dependent functions are restored, not merely their scalar readout. -/
@[simp] theorem reconstructArchive_encode {d : Nat} (a : Archive d) :
    reconstructArchive (archiveRecord a) (archiveRecord_legal a) = a := by
  apply Archive.ext
  · rfl
  · exact heq_of_eq (decodeGraph_encode a.events (attributes_code_equiv d) a.attributes)
  · exact heq_of_eq (decodeRelation_encode a.events a.causal)

/-- Structural graph legality excludes both missing fields and unobservable extra entries. -/
@[simp] theorem encode_reconstructArchive {d : Nat} (r : Record) (h : Legal d r) :
    archiveRecord (reconstructArchive r h) = r := by
  apply Record.ext
  · rfl
  · exact encode_decodeGraph r.events (attributes_code_equiv d) r.attributes h.graph
  · exact encode_decodeRelation r.events r.causal h.endpoints

def archive_record_equiv (d : Nat) : Archive d ≃ {r // Legal d r} where
  toFun a := ⟨archiveRecord a, archiveRecord_legal a⟩
  invFun r := reconstructArchive r.val r.property
  left_inv := reconstructArchive_encode
  right_inv r := Subtype.ext (encode_reconstructArchive r.val r.property)

/-- A literal tuple consisting of the event set, the attribute graph and the causal graph. -/
def recordCode (r : Record) : HF := pair (setCode r.events) (pair r.attributes r.causal)

theorem recordCode_injective : Function.Injective recordCode := by
  intro r s h
  obtain ⟨he, hf, hr⟩ : setCode r.events = setCode s.events ∧
      r.attributes = s.attributes ∧ r.causal = s.causal := by
    simpa [recordCode] using h
  exact Record.ext (finite_set_equiv.injective he) hf hr

/-- The archive grammar is a structural tuple with legal graphs over its actual event set. -/
def IsArchiveCode (d : Nat) (c : HF) : Prop :=
  ∃ E F R, c = pair E (pair F R) ∧ Legal d ⟨members E, F, R⟩

theorem recordCode_valid {d : Nat} (r : Record) (h : Legal d r) :
    IsArchiveCode d (recordCode r) := by
  refine ⟨setCode r.events, r.attributes, r.causal, rfl, ?_⟩
  simpa using h

def legal_record_code_equiv (d : Nat) : {r // Legal d r} ≃ {c // IsArchiveCode d c} :=
  Equiv.ofBijective (fun r => ⟨recordCode r.val, recordCode_valid r.val r.property⟩) ⟨by
    intro r s h
    exact Subtype.ext (recordCode_injective (congrArg Subtype.val h)), by
    rintro ⟨c, E, F, R, rfl, h⟩
    refine ⟨⟨⟨members E, F, R⟩, h⟩, Subtype.ext ?_⟩
    simp [recordCode]⟩

def archive_code_equiv (d : Nat) : Archive d ≃ {c // IsArchiveCode d c} :=
  (archive_record_equiv d).trans (legal_record_code_equiv d)

def archiveCode {d : Nat} (a : Archive d) : HF := (archive_code_equiv d a).val

theorem archiveCode_valid {d : Nat} (a : Archive d) : IsArchiveCode d (archiveCode a) :=
  (archive_code_equiv d a).property

def decodeArchive {d : Nat} (c : HF) (h : IsArchiveCode d c) : Archive d :=
  (archive_code_equiv d).symm ⟨c, h⟩

@[simp] theorem decodeArchive_encode {d : Nat} (a : Archive d) :
    decodeArchive (archiveCode a) (archiveCode_valid a) = a :=
  (archive_code_equiv d).symm_apply_apply a

@[simp] theorem encode_decodeArchive {d : Nat} (c : HF) (h : IsArchiveCode d c) :
    archiveCode (decodeArchive c h) = c :=
  congrArg Subtype.val ((archive_code_equiv d).apply_symm_apply ⟨c, h⟩)

@[simp] theorem archiveCode_inj {d : Nat} {a b : Archive d} :
    archiveCode a = archiveCode b ↔ a = b :=
  ⟨fun h => (archive_code_equiv d).injective (Subtype.ext h), congrArg archiveCode⟩

end
end D5.S0.History.Spacetime.ArchiveRecordEncoding
