/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoReplay
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoReplay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Kernel-checked opposing-star refutations exclude six distance-two masks. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactGeometryReplay
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCNF

/-! Replay the two direct opposing-star refutations with geometric input proofs. -/

set_option autoImplicit false
set_option maxRecDepth 40000
set_option linter.style.longLine false
set_option Elab.async false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoReplay

open Lean Meta Elab Term
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9WeightedSaturation (defect signedBiadjacency)
open Q9TightDistanceTwoNormalized (DirectGeometry exists_direct_geometry_of_signed_defect)
open Q9TightDistanceTwoCNF
open Q9SharedContactCNF (Axis)
open private certificateFingerprint satisfies_one satisfies_and from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactGeometryReplay

private def clauseProof (C D h : Ident) (spec : Json) : TermElabM Term := do
  let row ← Lean.ofExcept spec.getArr?
  let kind ← Lean.ofExcept row[0]!.getStr?
  let number (i : Nat) := Lean.ofExcept (row[i]!.getNat?)
  let lit (i : Nat) : TermElabM NumLit := return Syntax.mkNumLit (toString (← number i))
  if kind = "separation" then
    let u ← lit 1
    let v ← lit 2
    let mask := (← number 1) ^^^ (← number 2)
    let axes := (List.range 9).filter (fun i => mask.testBit i)
    if let [i, j] := axes then
      let a := Syntax.mkNumLit (toString i)
      let b := Syntax.mkNumLit (toString j)
      return ← `(oddExteriorPairClause $h $u $a $b (by decide +kernel) (by decide) (by decide +kernel))
    return ← `(separationClause $h $u $v (by decide +kernel))
  let s ← if (← number 1) = 0 then `(false) else `(true)
  let w ← lit 2
  if kind = "base" then
    return ← `(baseClause $h $s $w)
  if kind = "center" then
    let i := Syntax.mkNumLit (toString ((← number 2) - 4))
    return ← `(exteriorClause $h $s $i)
  let rules ← if (← number 1) = 0 then `(DirectGeometry.left_rules $h) else `(DirectGeometry.right_rules $h)
  if kind = "upper" || kind = "lower" then
    let axes ← Lean.ofExcept row[3]!.getArr?
    let axes ← axes.mapM fun axis => do
      let i := Syntax.mkNumLit (toString (← Lean.ofExcept axis.getNat?))
      `(($i : Axis))
    if kind = "upper" then
      return ← `(upperClause (S := support $C $D) $s $rules $w [$axes,*] (by decide))
    return ← `(lowerClause (S := support $C $D) $s $rules $w [$axes,*] (by decide))
  if kind = "square" then
    let i ← lit 3
    let j ← lit 4
    return ← `(squareClause (S := support $C $D) $s $rules $w $i $j (by decide))
  if kind = "parity" then
    let i := Syntax.mkNumLit (toString ((← number 3) - 1))
    let sign ← lit 4
    return ← `(parityClause (S := support $C $D) $s $rules $w $i $sign)
  throwError "Unknown opposing-star clause kind {kind}"

private partial def justify (C D h : Ident) (v formula : Expr) (labels : Array Json)
    (start stop : Nat) : TermElabM Expr := do
  let width := stop - start
  if width = 1 then
    let clause := formula.appArg!
    let term ← clauseProof C D h labels[start]!
    let expected := mkApp2 (mkConst ``Sat.Valuation.satisfies) v clause
    let proof ← withRef term <| elabTermEnsuringType term expected
    synthesizeSyntheticMVarsNoPostponing
    return mkApp3 (mkConst ``satisfies_one) v clause (← instantiateMVars proof)
  if width = 0 then throwError "Empty opposing-star formula"
  let a := formula.appFn!.appArg!
  let b := formula.appArg!
  let middle := start + width / 2
  let ha ← justify C D h v a labels start middle
  let hb ← justify C D h v b labels middle stop
  return mkApp5 (mkConst ``satisfies_and) v a b ha hb

elab "replay_tight_stars " name:ident missing:num fingerprint:num certificate:term : command => do
  Lean.Elab.Command.liftTermElabM do
    let .lit (.strVal contents) ← elabTermEnsuringType certificate (mkConst ``String)
      | throwError "Expected literal certificate data"
    unless certificateFingerprint contents == fingerprint.getNat.toUInt64 do
      throwErrorAt certificate "Certificate bytes differ from the fingerprint pinned in Lean source"
    let data ← Lean.ofExcept (Json.parse contents)
    let input ← Lean.ofExcept ((data.getObjVal? "cnf").bind Json.getStr?)
    let trace ← Lean.ofExcept ((data.getObjVal? "lrat").bind Json.getStr?)
    let labels ← Lean.ofExcept ((data.getObjVal? "labels").bind Json.getArr?)
    let (_, _, formula, replay) ← Mathlib.Tactic.Sat.fromLRATAux input trace name.getId
    let dimension := mkNatLit 9
    let supportType := mkApp (mkConst ``Finset [Level.zero]) (mkApp (mkConst ``Q) dimension)
    let axisType := mkApp (mkConst ``Fin) dimension
    let m ← elabTermEnsuringType missing axisType
    synthesizeSyntheticMVarsNoPostponing
    let m ← instantiateMVars m
    withLocalDeclD `C supportType fun C =>
    withLocalDeclD `D supportType fun D =>
    withLocalDeclD `h (mkApp3 (mkConst ``DirectGeometry) C D m) fun h => do
      let S := mkApp2 (mkConst ``support) C D
      let v := mkApp (mkConst ``valuation) S
      let follows ← justify (mkIdent `C) (mkIdent `D) (mkIdent `h) v formula labels 0 labels.size
      let value ← mkLambdaFVars #[C, D, h] (mkApp2 replay v follows)
      let type ← mkForallFVars #[C, D, h] (mkConst ``False)
      let value ← instantiateMVars value
      let type ← instantiateMVars type
      addDecl <| .thmDecl {name := name.getId, levelParams := [], type, value}

set_option maxHeartbeats 0 in
-- The two checked certificates have thousands of geometric inputs.
replay_tight_stars distinctMissing 5 9121598861613958949
  (include_str "../../../../../../../Evidence/D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightOpposingStars1.result.json")

set_option maxHeartbeats 0 in
replay_tight_stars sameMissing 4 8968751942829982907
  (include_str "../../../../../../../Evidence/D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightOpposingStars0.result.json")

open Classical in
/-- The six-mask case at distance two is impossible for two separated connected
balanced cubic nine-cube supports with universally singular signed defects. -/
theorem minimum_displacements_card_ne_six
    {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0) :
    (minimumDisplacements C D b 2).card ≠ 6 := by
  intro htight
  obtain ⟨_, _, _, h⟩ :=
    exists_direct_geometry_of_signed_defect hsep hrC hrD hcC hcD hbC hbD hdetC hdetD htight
  rcases h.right_missing with he | he
  · cases he
    exact sameMissing _ _ h
  · cases he
    exact distinctMissing _ _ h

#print axioms minimum_displacements_card_ne_six

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoReplay
