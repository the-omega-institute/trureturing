/- GID: D5/S0/Diagonal/Naturality/CoordinateRestrictionNaturality
   generality: G
   mirror-B: D5/B/S0/Diagonal/Naturality/CoordinateRestrictionNaturality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Coordinate restriction preserves twisted diagonals for compatible value maps. -/

import D5.S0.Diagonal.EscapeCount
import Mathlib.Logic.Function.Conjugate

/- Library-search audit trail (2026-08-15):
   * Loogle found `Function.semiconj_iff_comp_eq` for the exact
     intertwining hypothesis; this theorem is imported and applied below.
   * LeanSearch returned the same equivalence and related restriction results,
     but no full-statement match for coordinate-restricted diagonalization.
   * Repository and digestion-record searches found no duplicate theorem. -/

namespace D5.S0.Diagonal.Naturality.CoordinateRestrictionNaturality

universe ui uj vi vj

variable {Ai : Type ui} {Aj : Type uj} {Yi : Type vi} {Yj : Type vj}

/-- Restrict both table coordinates along an address embedding and map its values. -/
def restrictTable (iota : Ai ↪ Aj) (q : Yj → Yi)
    (E : Aj → Aj → Yj) : Ai → Ai → Yi :=
  fun a b => q (E (iota a) (iota b))

/-- Restrict a vector along an address embedding and map its values. -/
def restrictVector (iota : Ai ↪ Aj) (q : Yj → Yi)
    (u : Aj → Yj) : Ai → Yi :=
  fun a => q (u (iota a))

/-- Coordinate restriction commutes with twisted diagonalization when the value
map intertwines the two twists. -/
theorem coordinate_restriction_naturality
    (iota : Ai ↪ Aj) (q : Yj → Yi) (tauJ : Yj → Yj) (tauI : Yi → Yi)
    (hcomm : q ∘ tauJ = tauI ∘ q) (E : Aj → Aj → Yj) :
    restrictVector iota q (EscapeCount.diagonal tauJ E) =
      EscapeCount.diagonal tauI (restrictTable iota q E) := by
  have hsemiconj : Function.Semiconj q tauJ tauI :=
    Function.semiconj_iff_comp_eq.mpr hcomm
  funext a
  simpa [restrictVector, restrictTable, EscapeCount.diagonal] using
    hsemiconj.eq (E (iota a) (iota a))

-- A concrete inhabited instance witnesses that the domain and hypothesis are satisfiable.
example :
    restrictVector (Function.Embedding.refl Unit) (id : Unit → Unit)
        (EscapeCount.diagonal (id : Unit → Unit) (fun _ _ => ())) =
      EscapeCount.diagonal (id : Unit → Unit)
        (restrictTable (Function.Embedding.refl Unit) (id : Unit → Unit)
          (fun _ _ => ())) := by
  apply coordinate_restriction_naturality
  rfl

end D5.S0.Diagonal.Naturality.CoordinateRestrictionNaturality
