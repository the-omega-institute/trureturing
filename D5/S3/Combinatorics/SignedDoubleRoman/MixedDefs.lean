/- GID: D5/S3/Combinatorics/SignedDoubleRoman/MixedDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/MixedDefs
   mirror-E: none(waiver:mixed-packing-foundation)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Two-relation admissibility and finite live-carrier packing hypotheses. -/

import Mathlib.Combinatorics.SimpleGraph.Clique

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.MixedDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every closed domination neighbourhood contains at most two selected vertices. -/
def TwoLimited (D : SimpleGraph V) [DecidableRel D.Adj] (X : Finset V) : Prop :=
  ∀ v, ((insert v (D.neighborFinset v)) ∩ X).card ≤ 2

/-- A selection satisfies colour independence and closed domination capacity. -/
def MixedAdmissible (C D : SimpleGraph V) [DecidableRel D.Adj] (X : Finset V) : Prop :=
  C.IsIndepSet (X : Set V) ∧ TwoLimited D X

/-- Both relations have all edge endpoints in the live carrier. -/
def Supported (C D : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v⦄, C.Adj u v ∨ D.Adj u v → u ∈ S ∧ v ∈ S

/-- Parallel colour and domination edges count separately toward degree three. -/
def DegreeBound (C D : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel D.Adj]
    (S : Finset V) : Prop :=
  ∀ v ∈ S, C.degree v + D.degree v ≤ 3

end D5.S3.Combinatorics.SignedDoubleRoman.MixedDefs
