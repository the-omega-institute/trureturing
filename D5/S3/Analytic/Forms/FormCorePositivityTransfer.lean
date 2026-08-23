/- GID: D5/S3/Analytic/Forms/FormCorePositivityTransfer
   generality: G
   mirror-B: D5/B/S3/Analytic/Forms/FormCorePositivityTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Abstractly, form-norm continuity replaces closed semiboundedness in this transfer. -/

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Order.OrderClosed

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'nonnegative_of_formCore' D5 Golden/Frozen/accepted` returned no matches.
   * Repository searches for `QuadraticForm`, `form core`, `semibounded`, and `closable`
     found no public or private theorem covering positivity transfer from a form core.
   * Pinned mathlib has algebraic `QuadraticForm` and closable unbounded operators. Searches
     through `ContinuousLinearMap` and `InnerProductSpace` found no closed semibounded
     quadratic-form domain or form-core framework.
   * Local declaration search found `Dense.induction` and `isClosed_Ici.preimage`; these
     supply the density and limit-order steps. NyxID discovery exposed no configured public
     Loogle or LeanSearch connector, and local smart searches returned no exact theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Forms.FormCorePositivityTransfer

/-- A subset is an abstract form core when it is dense for the norm carried by the domain. -/
def IsFormCore {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Submodule ℝ V) [NormedAddCommGroup D] [NormedSpace ℝ D] (C : Set D) : Prop :=
  Dense C

/-- A continuous real form nonnegative on a form-norm core is nonnegative on its domain. -/
theorem nonnegative_of_formCore {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Submodule ℝ V) [NormedAddCommGroup D] [NormedSpace ℝ D] (q : D → ℝ) (C : Set D)
    (hq : Continuous q) (hcore : IsFormCore D C) (hnonneg : ∀ f ∈ C, 0 ≤ q f) :
    ∀ f : D, 0 ≤ q f := by
  exact fun f ↦ hcore.induction hnonneg (isClosed_Ici.preimage hq) f

example : ∀ f : (⊤ : Submodule ℝ ℝ), 0 ≤ (f : ℝ) ^ 2 := by
  refine nonnegative_of_formCore (⊤ : Submodule ℝ ℝ) (fun f ↦ (f : ℝ) ^ 2)
    Set.univ ?_ ?_ ?_
  · exact continuous_subtype_val.pow 2
  · exact dense_univ
  · exact fun f _ ↦ sq_nonneg (f : ℝ)

#print axioms nonnegative_of_formCore

end D5.S3.Analytic.Forms.FormCorePositivityTransfer
