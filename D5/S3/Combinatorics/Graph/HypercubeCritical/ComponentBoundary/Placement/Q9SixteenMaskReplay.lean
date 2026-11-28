import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ThreeMaskCutClauses
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesReplay

/-! Replay contact refutations whose clauses include three-mask companions. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option Elab.async false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SixteenMaskReplay

open Lean Elab Term
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9ContactMaskCut (cutMasks)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9TenMaskSixAxisReplay (Recipe)
open Q9FifteenMaskLargeAxesReplay (recipe)
open Q9ThreeMaskCutClauses (companionLeftClause companionRightClause)
open private valuation checkCertificate replayCertificate from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskSixAxisReplay
open private proveRow from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesReplay

open Classical in
/-- Cubic placement with exact masks, including the signs used in the cut rows. -/
structure Inputs (r : Recipe) (C D : Finset (Q 9)) : Prop where
  core : Q9FifteenMaskLargeAxesReplay.Inputs r C D
  leftRegular : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3
  rightRegular : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3
  leftBalanced : IsBalanced C
  rightBalanced : IsBalanced D

private theorem family_eq {r : Recipe} {C D : Finset (Q 9)} (h : Inputs r C D)
    (hrequired : r.required = r.family) : minimumDisplacements C D false 2 = r.family :=
  Finset.Subset.antisymm h.core.core.allowed (hrequired ▸ h.core.core.realized)

private def numeral (value : Json) : TermElabM NumLit :=
  return Syntax.mkNumLit (toString (← Lean.ofExcept value.getNat?))

private def justifyRow (recipeTerm : Term) (C D h : Ident) (spec : Json) : TermElabM Term := do
  let row ← Lean.ofExcept spec.getArr?
  let tag ← Lean.ofExcept row[0]!.getStr?
  if tag != "cut-companion" then
    let core := mkIdent `replayInputs
    let proof ← proveRow recipeTerm C D core spec
    return ← `(let $core := Inputs.core $h; $proof)
  let side ← Lean.ofExcept row[1]!.getNat?
  let x ← numeral row[2]!
  let shore ← (← Lean.ofExcept row[3]!.getArr?).mapM numeral
  let pairTerm (item : Json) : TermElabM Term := do
    let axes ← Lean.ofExcept item.getArr?
    let i ← numeral axes[0]!
    let j ← numeral axes[1]!
    `(($i, $j))
  let p ← pairTerm row[4]!
  let q ← pairTerm row[5]!
  let r ← pairTerm row[6]!
  let common ← `((Inputs.core $h).core.geometry.separated)
  let tactic ← `(by unfold cutMasks; rw [family_eq $h rfl]; decide +kernel)
  if side == 0 then
    `(companionLeftClause (recipe := $recipeTerm) (A := ([$shore,*]).toFinset)
      $common (Inputs.leftRegular $h) (Inputs.leftBalanced $h) $x $p $q $r
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) $tactic)
  else
    unless side == 1 do throwError "Invalid companion clause side"
    `(companionRightClause (recipe := $recipeTerm) (A := ([$shore,*]).toFinset)
      $common (Inputs.rightRegular $h) (Inputs.rightBalanced $h) $x $p $q $r
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) $tactic)

elab "replay_sixteen_masks " impossible:ident masks:term " fingerprint " digest:num
    " certificate " data:term : command => Lean.Elab.Command.liftTermElabM do
  let contents ← checkCertificate digest.getNat data
  let name := (← getCurrNamespace) ++ impossible.getId
  let recipeTerm ← `(recipe $masks)
  let r ← elabTermEnsuringType recipeTerm (mkConst ``Recipe)
  synthesizeSyntheticMVarsNoPostponing
  let r ← instantiateMVars r
  replayCertificate name contents (mkApp (mkConst ``Inputs) r)
    (mkApp (mkConst ``valuation) r) (justifyRow recipeTerm)

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SixteenMaskReplay
