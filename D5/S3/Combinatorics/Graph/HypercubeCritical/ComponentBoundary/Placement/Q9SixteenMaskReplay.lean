import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ThreeMaskCutClauses
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesReplay

/-! Replay contact refutations with three-mask cut clauses.

Use `replay_sixteen_masks_semantic` for certificates with translation or
forbidden-square rows. It uses the same recipe, fingerprint, CNF, and LRAT
format as `replay_sixteen_masks`. Given `y = x XOR p`, the cut labels and clauses
are as follows, in the order emitted by `sixteen-mask-cubic-screen.py`.
Every row starts with `-L(x), -R(y)`. In the last column `p, q, r` denote XOR masks.

| JSON label shape | Remaining literals |
| --- | --- |
| `["cut-translate",0,x,shore,p,q,r]` | `+L(x XOR q XOR r)` |
| `["cut-translate",1,x,shore,p,q,r]` | `+R(y XOR q XOR r)` |
| `["cut-companion",0,x,shore,p,q,r]` | `+L(y XOR q), +L(y XOR r)` |
| `["cut-companion",1,x,shore,p,q,r]` | `+R(x XOR q), +R(x XOR r)` |
| `["cut-square",0,x,shore,p,q,r]` | `-L(y XOR q), -R(x XOR q)` |
| `["cut-square",1,x,shore,p,q,r]` | `-L(y XOR r), -R(x XOR r)` |

`x` is an even 9-bit word encoded as an integer in 0–511. `shore` is a JSON
array of axes in 0–8 whose crossing masks in the exact family are `p, q, r`.
Each pair in the label is a two-element array with the in-shore axis first.
The new command produces `∀ C D : Finset (Q 9), SemanticInputs (recipe masks) C D → False`.
-/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option Elab.async false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SixteenMaskReplay

open scoped Matrix
open Lean Elab Term
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9ContactMaskCut (cutMasks)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9TenMaskSixAxisReplay (Recipe)
open Q9FifteenMaskLargeAxesReplay (recipe)
open Q9ThreeMaskCutClauses
  (companionLeftClause companionRightClause translationClause forbiddenSquareClause)
open Q9WeightedSaturation (defect signedBiadjacency)
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

open Classical in
/-- The weighted cut rows also require connectedness and weighted defect
singularity for the normalized right support `D`. -/
structure SemanticInputs (r : Recipe) (C D : Finset (Q 9)) : Prop where
  base : Inputs r C D
  rightConnected : ((hypercube 9).induce (D : Set (Q 9))).Connected
  rightDefectSingular : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0

private theorem family_eq {r : Recipe} {C D : Finset (Q 9)} (h : Inputs r C D)
    (hrequired : r.required = r.family) : minimumDisplacements C D false 2 = r.family :=
  Finset.Subset.antisymm h.core.core.allowed (hrequired ▸ h.core.core.realized)

private def numeral (value : Json) : TermElabM NumLit :=
  return Syntax.mkNumLit (toString (← Lean.ofExcept value.getNat?))

private def justifyRow (recipeTerm : Term) (semantic : Bool) (C D h : Ident) (spec : Json) :
    TermElabM Term := do
  let row ← Lean.ofExcept spec.getArr?
  let tag ← Lean.ofExcept row[0]!.getStr?
  let base ← if semantic then `(SemanticInputs.base $h) else `($h)
  if tag != "cut-companion" && tag != "cut-translate" && tag != "cut-square" then
    let core := mkIdent `replayInputs
    let proof ← proveRow recipeTerm C D core spec
    return ← `(let $core := Inputs.core $base; $proof)
  unless semantic || tag == "cut-companion" do
    throwError "Cut row {tag} requires replay_sixteen_masks_semantic"
  let side ← Lean.ofExcept row[1]!.getNat?
  unless side ≤ 1 do throwError "Invalid selector in cut row {tag}"
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
  let common ← `((Inputs.core $base).core.geometry.separated)
  let cut ← `(by unfold cutMasks; rw [family_eq $base rfl]; decide +kernel)
  if tag == "cut-translate" then
    let s ← if side == 0 then `(false) else `(true)
    return ← `(translationClause (recipe := $recipeTerm) (A := ([$shore,*]).toFinset)
      $common (Inputs.leftRegular $base) (Inputs.rightRegular $base)
      (SemanticInputs.rightConnected $h) (Inputs.leftBalanced $base)
      (Inputs.rightBalanced $base) (SemanticInputs.rightDefectSingular $h) $s $x $p $q $r
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) $cut)
  if tag == "cut-square" then
    let (selected, other) := if side == 0 then (q, r) else (r, q)
    return ← `(forbiddenSquareClause (recipe := $recipeTerm) (A := ([$shore,*]).toFinset)
      $common (Inputs.rightRegular $base) (SemanticInputs.rightConnected $h)
      (Inputs.rightBalanced $base) (SemanticInputs.rightDefectSingular $h) $x $p $selected $other
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) $cut)
  if side == 0 then
    `(companionLeftClause (recipe := $recipeTerm) (A := ([$shore,*]).toFinset)
      $common (Inputs.leftRegular $base) (Inputs.leftBalanced $base) $x $p $q $r
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) $cut)
  else
    `(companionRightClause (recipe := $recipeTerm) (A := ([$shore,*]).toFinset)
      $common (Inputs.rightRegular $base) (Inputs.rightBalanced $base) $x $p $q $r
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) $cut)

private def replaySixteenMasks (semantic : Bool) (result : Name) (masks : Term)
    (digest : Nat) (data : Term) : TermElabM Unit := do
  let contents ← checkCertificate digest data
  let name := (← getCurrNamespace) ++ result
  let recipeTerm ← `(recipe $masks)
  let r ← elabTermEnsuringType recipeTerm (mkConst ``Recipe)
  synthesizeSyntheticMVarsNoPostponing
  let r ← instantiateMVars r
  let inputs := if semantic then ``SemanticInputs else ``Inputs
  replayCertificate name contents (mkApp (mkConst inputs) r)
    (mkApp (mkConst ``valuation) r) (justifyRow recipeTerm semantic)

elab "replay_sixteen_masks " impossible:ident masks:term " fingerprint " digest:num
    " certificate " data:term : command => Lean.Elab.Command.liftTermElabM do
  replaySixteenMasks false impossible.getId masks digest.getNat data

elab "replay_sixteen_masks_semantic " impossible:ident masks:term " fingerprint " digest:num
    " certificate " data:term : command => Lean.Elab.Command.liftTermElabM do
  replaySixteenMasks true impossible.getId masks digest.getNat data

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SixteenMaskReplay
