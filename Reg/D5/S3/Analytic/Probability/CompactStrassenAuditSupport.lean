import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Analytic.Probability.CompactStrassen
import Lean

/-! Dependent observation families for compact martingale transport audits. -/
open Lean Meta Elab Term
open MeasureTheory Set Econlib.Probability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/-- Reconstruct the complete original telescope with one typed observation varied. -/
elab "source_law% " target:ident " replacing " old:term " with " replacement:term : term => do
  let info ← getConstInfo target.getId
  let statement := info.type
  let oldExpr ← instantiateMVars (← elabTerm old none)
  let replacementExpr ← elabTermEnsuringType replacement (← inferType oldExpr)
  let oldExpr ← instantiateMVars oldExpr
  let replacementExpr ← instantiateMVars replacementExpr
  let hits ← IO.mkRef (0 : Nat)
  let result ← Meta.transform statement (post := fun e => do
    if e.getAppFn.isConst && oldExpr.getAppFn.isConst &&
        e.getAppFn.constName! == oldExpr.getAppFn.constName! &&
        e.getAppNumArgs >= oldExpr.getAppNumArgs then
      let args := e.getAppArgs
      let observedHead := mkAppN e.getAppFn (args.extract 0 oldExpr.getAppNumArgs)
      if ← isDefEq observedHead oldExpr then
        hits.modify (· + 1)
        return .done (mkAppN replacementExpr (args.extract oldExpr.getAppNumArgs args.size))
    return .done e)
  if (← hits.get) == 0 then
    throwError "No occurrence of the proposed typed observation in the original telescope of {target}."
  instantiateMVars result

namespace Reg.CompactStrassenAudit
noncomputable section

abbrev Quantile : Signature where
  Params := Measure ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def quantileActual : Realization Quantile :=
  realize Quantile (fun _ μ t => μ.quantile t) (fun e => nomatch e)

abbrev ToReal : Signature where
  Params := Unit
  State _ := ENNReal
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def toRealActual : Realization ToReal :=
  realize ToReal (fun _ _ x => x.toReal) (fun e => nomatch e)

abbrev StopLoss : Signature where
  Params := Measure ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def stopLossActual : Realization StopLoss :=
  realize StopLoss (fun _ μ z => μ.stopLoss z) (fun e => nomatch e)

abbrev Max : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def maxActual : Realization Max :=
  realize Max (fun _ x y => max x y) (fun e => nomatch e)

abbrev Interval : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def intervalActual : Realization Interval :=
  realize Interval (fun _ a b => Ico a b) (fun e => nomatch e)

abbrev Convex : Signature where
  Params := Unit
  State _ := ℝ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def convexActual : Realization Convex :=
  realize Convex (fun _ _ f => ConvexOn ℝ Set.univ f) (fun e => nomatch e)

abbrev Support : Signature where
  Params := ProbDist ℝ
  State _ := Set ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def supportActual : Realization Support :=
  realize Support (fun _ μ s => μ.supportsOn s) (fun e => nomatch e)

universe u v
structure MapParams where
  α : Type u
  β : Type v
  mα : MeasurableSpace α
  mβ : MeasurableSpace β

abbrev MapFamily : Signature where
  Params := MapParams.{u,v}
  State p := letI := p.mα; letI := p.mβ
    Σ (d : ProbDist p.α), Σ (f : p.α → p.β), PLift (Measurable f)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := @ProbDist p.β p.mβ
  Anchor := Empty
  finiteAnchor := inferInstance

def mapActual : Realization MapFamily.{u,v} :=
  realize MapFamily (fun _ p x => @ProbDist.map p.α p.β p.mα p.mβ x.1 x.2.1 x.2.2.down)
    (fun e => nomatch e)

abbrev Coupling : Signature where
  Params := ProbDist ℝ × ProbDist ℝ
  State _ := ProbDist (ℝ × ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def couplingActual : Realization Coupling :=
  realize Coupling (fun _ p π => IsCoupling p.1 p.2 π) (fun e => nomatch e)

def martingaleActual : Realization Coupling :=
  realize Coupling (fun _ p π => IsMartingaleCoupling p.1 p.2 π) (fun e => nomatch e)

abbrev FiniteLaw : Signature where
  Params := Unit
  State _ := DiscreteLaw
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ProbDist ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def finiteLawActual : Realization FiniteLaw :=
  realize FiniteLaw (fun _ _ p => p.toProbDist) (fun e => nomatch e)

abbrev Mean : Signature where
  Params := Unit
  State _ := DiscreteLaw
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def meanActual : Realization Mean :=
  realize Mean (fun _ _ p => p.mean) (fun e => nomatch e)

abbrev Atom : Signature where
  Params := Σ (_μ : ProbDist ℝ), Σ (n : ℕ), PLift (0 < n)
  State p := Fin p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def atomActual : Realization Atom :=
  realize Atom (fun _ p k => DiscreteLaw.condMeanAtom p.1 p.2.1 p.2.2.down k)
    (fun e => nomatch e)

abbrev Atomization : Signature where
  Params := ProbDist ℝ
  State _ := {n : ℕ // 0 < n}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := DiscreteLaw
  Anchor := Empty
  finiteAnchor := inferInstance

def atomizationActual : Realization Atomization :=
  realize Atomization (fun _ μ n => DiscreteLaw.condMeanAtomize μ n.1 n.2)
    (fun e => nomatch e)

abbrev ScalarMeasure : Signature where
  Params := Unit
  State _ := ProbDist ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Measure ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def scalarMeasureActual : Realization ScalarMeasure :=
  realize ScalarMeasure (fun _ _ μ => μ.toMeasure) (fun e => nomatch e)

abbrev JointMeasure : Signature where
  Params := Unit
  State _ := ProbDist (ℝ × ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Measure (ℝ × ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def jointMeasureActual : Realization JointMeasure :=
  realize JointMeasure (fun _ _ π => π.toMeasure) (fun e => nomatch e)

end
end Reg.CompactStrassenAudit
