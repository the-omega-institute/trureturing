/- GID: D5/S0/History/Spacetime/ArchiveCarrier
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/ArchiveCarrier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite causal archives with exact event attributes and separate current regions and selections. -/

import D5.S0.History.Spacetime.SourceTreeEncoding

set_option autoImplicit false

namespace D5.S0.History.Spacetime.ArchiveCarrier

open HFEncoding SourceTreeEncoding

/-- The four attributes of one event; the dimension is any fixed finite d. -/
@[ext] structure Attributes (d : Nat) where
  time : Int
  position : Fin d → Int
  positive : Bool
  source : SourceTree

/-- All attributes and the strict relation have exactly the archived event domain. -/
structure Archive (d : Nat) where
  events : Finset HF
  attributes : events → Attributes d
  causal : events → events → Prop
  irrefl : ∀ e, ¬ causal e e
  trans : ∀ e f g, causal e f → causal f g → causal e g
  time_lt : ∀ e f, causal e f → (attributes e).time < (attributes f).time

abbrev Archive.Event {d : Nat} (a : Archive d) := ↥a.events

/-- Extensional equality includes the complete dependent attribute functions. -/
theorem Archive.ext {d : Nat} {a b : Archive d} (he : a.events = b.events)
    (ha : HEq a.attributes b.attributes) (hr : HEq a.causal b.causal) : a = b := by
  cases a; cases b; cases he; cases ha; cases hr; rfl

structure Context (d : Nat) where
  archive : Archive d
  current : Finset archive.Event

abbrev Context.Event {d : Nat} (c : Context d) := c.archive.Event

/-- Every subset is permitted; no downward-closure requirement is imposed. -/
def Selection {d : Nat} (c : Context d) := {s : Finset c.Event // s ⊆ c.current}

/-- A rich representation retains its entire context as well as its selected subset. -/
def Rich (d : Nat) := (c : Context d) × Selection c

/-- This embedding concerns archives alone. Current regions do not occur in its type. -/
structure ArchiveEmbedding {d : Nat} (a b : Archive d) where
  eventMap : a.Event ↪ b.Event
  attributes_eq : ∀ e, b.attributes (eventMap e) = a.attributes e
  causal_iff : ∀ e f, b.causal (eventMap e) (eventMap f) ↔ a.causal e f

def ArchiveEmbedding.refl {d : Nat} (a : Archive d) : ArchiveEmbedding a a where
  eventMap := Function.Embedding.refl _
  attributes_eq _ := rfl
  causal_iff _ _ := Iff.rfl

def ArchiveEmbedding.comp {d : Nat} {a b c : Archive d}
    (f : ArchiveEmbedding a b) (g : ArchiveEmbedding b c) : ArchiveEmbedding a c where
  eventMap := f.eventMap.trans g.eventMap
  attributes_eq e := (g.attributes_eq (f.eventMap e)).trans (f.attributes_eq e)
  causal_iff e f' := (g.causal_iff _ _).trans (f.causal_iff e f')

end D5.S0.History.Spacetime.ArchiveCarrier
