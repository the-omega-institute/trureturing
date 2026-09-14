/- GID: D5/S0/History/Spacetime/AllSetZeckendorfHereditaryFiniteness
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/AllSetZeckendorfHereditaryFiniteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recursive Zeckendorf encoding preserves and reflects hereditary finiteness in every universe. -/

import D5.S0.History.Spacetime.AllSetZeckendorfEncoding
import Mathlib.SetTheory.ZFC.VonNeumann
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Data.Set.Finite.Lattice

set_option autoImplicit false
universe u
namespace D5.S0.History.Spacetime.AllSetZeckendorfHereditaryFiniteness
noncomputable section
open D5.S0.History.Spacetime.AllSetZeckendorfEncoding
attribute [local instance] Classical.allZFSetDefinable Classical.propDecidable

/-- A set is hereditarily finite when its ordinal rank is less than omega. -/
def IsHF (x : ZFSet.{u}) : Prop := ZFSet.rank x < Ordinal.omega0

/-- A recursive Zeckendorf code is hereditarily finite exactly when its original set is. -/
theorem enc_isHF_iff (x : ZFSet.{u}) : IsHF (Enc x) ↔ IsHF x := by
  sorry

end
end D5.S0.History.Spacetime.AllSetZeckendorfHereditaryFiniteness
