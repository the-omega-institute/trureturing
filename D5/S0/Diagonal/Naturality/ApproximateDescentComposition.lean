/- GID: D5/S0/Diagonal/Naturality/ApproximateDescentComposition
   generality: G
   mirror-B: D5/B/S0/Diagonal/Naturality/ApproximateDescentComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Uniform approximate-descent defects obey the Lipschitz composition budget. -/

import D5.S0.Diagonal.Naturality.NaturalityDefectComposition

/- Library-search audit trail (2026-08-21):
   * Exact repository hit `NaturalityDefectComposition.naturality_defect_comp_le`
     proves the required pointwise composition inequality and is applied directly.
   * That frozen module records the exact pinned-Mathlib hits `dist_triangle` and
     `LipschitzWith.dist_le_mul`, both used by the imported pointwise theorem.
   * Repository and digestion-receipt searches for the atom identifier and the
     uniform supremum statement found no equal-or-stronger deposited theorem. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Diagonal.Naturality.ApproximateDescentComposition

open D5.S0.Diagonal.Naturality.NaturalityDefectComposition

/-- The source's global defect is the supremum of its pointwise pseudometric
defects over all source states. -/
def uniformNaturalityDefect
    {A Am B Bm : Type*} [PseudoMetricSpace Bm]
    (projectA : A -> Am) (projectB : B -> Bm)
    (globalMap : A -> B) (localMap : Am -> Bm) : Real :=
  ⨆ x, naturalityDefect projectA projectB globalMap localMap x

/-- Uniform error budgets for two approximate descents compose additively,
with the inner budget amplified by the outer local map's Lipschitz constant. -/
theorem approximate_descent_comp_bound
    {X Xbar Y Ybar Z Zbar : Type*}
    [PseudoMetricSpace Ybar] [PseudoMetricSpace Zbar]
    (projectX : X -> Xbar) (projectY : Y -> Ybar) (projectZ : Z -> Zbar)
    (globalF : X -> Y) (localF : Xbar -> Ybar)
    (globalG : Y -> Z) (localG : Ybar -> Zbar)
    (hX : Nonempty X)
    (epsilonF epsilonG : Real) (L : NNReal)
    (hF : forall x,
      naturalityDefect projectX projectY globalF localF x <= epsilonF)
    (hG : forall y,
      naturalityDefect projectY projectZ globalG localG y <= epsilonG)
    (hL : LipschitzWith L localG) :
    uniformNaturalityDefect projectX projectZ
        (globalG ∘ globalF) (localG ∘ localF) <=
      epsilonG + L * epsilonF := by
  letI : Nonempty X := hX
  unfold uniformNaturalityDefect
  apply ciSup_le
  intro x
  exact (naturality_defect_comp_le
    projectX projectY projectZ globalG localG globalF localF L hL x).trans
      (add_le_add (hG (globalF x))
        (mul_le_mul_of_nonneg_left (hF x) L.coe_nonneg))

/- The hypotheses and source carrier are jointly inhabited, while the theorem
specializes to the exact zero-defect identity interface. -/
example :
    uniformNaturalityDefect (id : Real -> Real) (id : Real -> Real)
        (id : Real -> Real) (id : Real -> Real) <=
      (0 : Real) + (1 : NNReal) * 0 := by
  simpa [Function.comp_def] using
    (approximate_descent_comp_bound
      (projectX := (id : Real -> Real)) (projectY := (id : Real -> Real))
      (projectZ := (id : Real -> Real)) (globalF := (id : Real -> Real))
      (localF := (id : Real -> Real)) (globalG := (id : Real -> Real))
      (localG := (id : Real -> Real)) ⟨0⟩ (epsilonF := 0) (epsilonG := 0) (L := 1)
      (by intro x; simp [naturalityDefect])
      (by intro y; simp [naturalityDefect]) LipschitzWith.id)

#print axioms uniformNaturalityDefect
#print axioms approximate_descent_comp_bound

end D5.S0.Diagonal.Naturality.ApproximateDescentComposition
