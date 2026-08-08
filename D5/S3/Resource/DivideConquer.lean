/- GID: D5/S3/Resource/DivideConquer
   generality: G
   mirror-B: D5/B/S3/Resource/DivideConquer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove subadditivity of infimum-defined tensor-closed resource functionals. -/

/- Library-search audit trail (2026-08-08):
   * Local pinned-mathlib grep terms: `iInf_add`, `add_iInf`, `iInf_add_iInf`,
     `le_iInf_add_iInf`, `le_iInf₂_add_iInf₂`, `ciInf_le`, and `iInf_le_of_le`.
   * `Mathlib.Data.ENNReal.Operations` provides `ENNReal.le_iInf_add_iInf`, which turns a
     bound valid for every pair of indices into a bound by the sum of their two infima.
   * The lemma is stated for arbitrary `Sort` indices and hence also covers empty feasible-strategy
     subtypes. Using `ℝ≥0∞` makes an empty infimum equal to infinity and removes real-valued
     boundedness side conditions. The proof below is the thin resource-theoretic wrapper: its
     pointwise premise is supplied exactly by tensor closure and additive product cost.
-/

import Mathlib

namespace D5.S3.Resource.DivideConquer

universe u v

/-- Data for a resource functional whose admissible strategies are closed under products and
whose product-strategy cost is additive. -/
structure ResourceTheory (Obj : Type u) (Strat : Type v) where
  tensorObj : Obj → Obj → Obj
  tensorStrat : Strat → Strat → Strat
  feasible : Strat → Obj → Prop
  cost : Strat → ENNReal
  feasible_tensor : ∀ {s₁ s₂ X Y}, feasible s₁ X → feasible s₂ Y →
    feasible (tensorStrat s₁ s₂) (tensorObj X Y)
  cost_tensor : ∀ s₁ s₂, cost (tensorStrat s₁ s₂) = cost s₁ + cost s₂

namespace ResourceTheory

/-- The optimal resource cost, defined as the infimum over all feasible strategies. -/
noncomputable def value {Obj : Type u} {Strat : Type v}
    (R : ResourceTheory Obj Strat) (X : Obj) : ENNReal :=
  ⨅ s : {s : Strat // R.feasible s X}, R.cost s.1

end ResourceTheory

/-- An infimum-defined resource functional is subadditive when product strategies are feasible
and have additive cost. -/
theorem resource_functional_subadditive {Obj : Type u} {Strat : Type v}
    (R : ResourceTheory Obj Strat) (X Y : Obj) :
    R.value (R.tensorObj X Y) ≤ R.value X + R.value Y := by
  unfold ResourceTheory.value
  apply ENNReal.le_iInf_add_iInf
  intro sX sY
  calc
    (⨅ s : {s : Strat // R.feasible s (R.tensorObj X Y)}, R.cost s.1) ≤
        R.cost (R.tensorStrat sX.1 sY.1) :=
      iInf_le
        (fun s : {s : Strat // R.feasible s (R.tensorObj X Y)} => R.cost s.1)
        ⟨R.tensorStrat sX.1 sY.1, R.feasible_tensor sX.2 sY.2⟩
    _ = R.cost sX.1 + R.cost sY.1 := R.cost_tensor sX.1 sY.1

end D5.S3.Resource.DivideConquer
