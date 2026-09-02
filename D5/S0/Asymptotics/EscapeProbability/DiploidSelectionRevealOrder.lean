/- GID: D5/S0/Asymptotics/EscapeProbability/DiploidSelectionRevealOrder
   generality: G
   mirror-B: D5/B/S0/Asymptotics/EscapeProbability/DiploidSelectionRevealOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reuse the frozen diploid theorem with source-exact reveal-order guards. -/

import D5.S0.Asymptotics.EscapeProbability.DiploidDominanceSelectionOrder

/- Library-search audit trail (2026-09-02):
   * The imported frozen module is the exact owner of the diploid mean-fitness,
     normalized-frequency, asymptotic, and analytic-order calculation.
   * Pinned Mathlib owns `analyticOrderAt` and `Asymptotics.IsBigO`; no result is
     reproved here. This wrapper retains the old atom's explicit `0 < h`
     remainder branch and its adjacent source's `h * s ≠ 0` order branch.
   * The public `let` formulas reproduce source lines 2042-2089. The nonzero
     selection premise and mean-fitness domain guard come from lines 2095-2096. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Asymptotics.EscapeProbability.DiploidSelectionRevealOrder

open _root_.Asymptotics Filter
open scoped Topology

open D5.S0.Asymptotics.EscapeProbability.DiploidDominanceSelectionOrder

/-- In the source's diploid selection model, complete recessivity exposes a
quadratic rare-allele signal, while a nonzero heterozygote effect exposes a
linear signal. The five result leaves correspond to the exact update,
recessive expansion, recessive order, positive-dominance expansion, and
nonzero-dominance order. -/
theorem diploid_selection_reveal_order
    (selection dominance : Real) (selectionNe : selection ≠ 0) :
    let meanFitness := fun (h x : Real) =>
      (1 - x) ^ 2 + 2 * (1 - x) * x * (1 - h * selection) +
        x ^ 2 * (1 - selection)
    let selectedAlleleMass := fun (h x : Real) =>
      x ^ 2 * (1 - selection) + (1 - x) * x * (1 - h * selection)
    let updatedFrequency := fun (h x : Real) =>
      selectedAlleleMass h x / meanFitness h x
    let selectionChange := fun (h x : Real) => updatedFrequency h x - x
    (∀ x, meanFitness 0 x ≠ 0 →
      selectionChange 0 x =
        -(selection * (1 - x) * x ^ 2) / (1 - selection * x ^ 2)) ∧
    (fun x => selectionChange 0 x - (-selection * x ^ 2))
      =O[𝓝 0] (fun x => x ^ 3) ∧
    analyticOrderAt (selectionChange 0) 0 = 2 ∧
    (0 < dominance →
      (fun x => selectionChange dominance x - (-(dominance * selection) * x))
        =O[𝓝 0] (fun x => x ^ 2)) ∧
    (dominance * selection ≠ 0 →
      analyticOrderAt (selectionChange dominance) 0 = 1) := by
  dsimp
  obtain ⟨exactChange, recessiveRemainder, recessiveOrder,
      exposedRemainder, exposedOrder⟩ :=
    diploid_dominance_selection_order selection dominance selectionNe
  refine ⟨exactChange, recessiveRemainder, recessiveOrder, ?_, ?_⟩
  · intro _
    exact exposedRemainder
  · exact exposedOrder

/- Positive-branch reverse probe for CAS-A5: the public result yields a
concrete nontrivial order-one selection signal at `s = h = 1`. -/
example :
    analyticOrderAt
      (fun x : Real =>
        (x ^ 2 * (1 - 1) + (1 - x) * x * (1 - 1 * 1)) /
            ((1 - x) ^ 2 + 2 * (1 - x) * x * (1 - 1 * 1) +
              x ^ 2 * (1 - 1)) - x)
      0 = 1 := by
  have result := diploid_selection_reveal_order (1 : Real) 1 (by norm_num)
  dsimp at result
  simpa using result.2.2.2.2 (by norm_num)

/- Negative-branch reverse probe for CAS-A5: `h * s ≠ 0` observes the source's
negative-dominance branch, which the former `0 < h` antecedent omitted. -/
example :
    analyticOrderAt
      (fun x : Real =>
        (x ^ 2 * (1 - 1) + (1 - x) * x * (1 - (-1) * 1)) /
            ((1 - x) ^ 2 + 2 * (1 - x) * x * (1 - (-1) * 1) +
              x ^ 2 * (1 - 1)) - x)
      0 = 1 := by
  have result := diploid_selection_reveal_order (1 : Real) (-1) (by norm_num)
  dsimp at result
  simpa using result.2.2.2.2 (by norm_num)

/- Trivialization probe for CAS-A3: at `s = 0` the selection change is the zero
function, so the sourced `s ≠ 0` premise is essential to the exact order. -/
example :
    (fun x : Real =>
      (x ^ 2 * (1 - 0) + (1 - x) * x * (1 - 0 * 0)) /
          ((1 - x) ^ 2 + 2 * (1 - x) * x * (1 - 0 * 0) +
            x ^ 2 * (1 - 0)) - x) = fun _ => 0 := by
  funext x
  ring

#print axioms diploid_selection_reveal_order

end D5.S0.Asymptotics.EscapeProbability.DiploidSelectionRevealOrder
