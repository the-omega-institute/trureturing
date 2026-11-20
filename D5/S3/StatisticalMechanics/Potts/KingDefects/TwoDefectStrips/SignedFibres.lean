/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/SignedFibres
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/SignedFibres
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Constant fibres of the complementary-colour row map. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live paths of HardinA229750.result and HardinA229751.result)
sum_beta: proof_shape=bind-only;
consumers=Width3.ZeroTemperature.transition_counts,Width4.ZeroTemperature.proper_transition_counts
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip

/-! Each complementary-pair row has two independent sign choices in every column. -/

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.SignedFibres
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip (beta)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip (colourEquiv8)

theorem sum_beta {k : ℕ} (w : (Fin k → Fin 4) → ℤ) :
    (∑ c : Fin k → Fin 8, w (beta ∘ c)) = (2 : ℤ)^k * ∑ r, w r := by
  let E := (Equiv.piCongrRight (fun _ : Fin k => colourEquiv8)).trans
    (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Fin 4) (fun _ => Bool))
  have hf (x : Fin k → Fin 8) : (E x).1 = beta ∘ x := rfl
  calc
    (∑ c : Fin k → Fin 8, w (beta ∘ c)) = ∑ x :
        (Fin k → Fin 4) × (Fin k → Bool), w x.1 := by
      simpa only [hf] using E.sum_comp (fun x => w x.1)
    _ = (2 : ℤ)^k * ∑ r, w r := by
      simp [Fintype.sum_prod_type, Finset.mul_sum, mul_comm]

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.SignedFibres
