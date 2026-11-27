/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisReplay
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisReplay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Every selected input is proved from the same signed normalized geometry. Resolution hints then derive the empty clause in the Lean kernel. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisInputClauses
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33ReplayBatches
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactGeometryReplay

/-! Kernel replay of the five-axis contact orbit refutations. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option Elab.async false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisReplay

open Lean Meta Elab Term
open BalancedCriticalSpectrum (Q)
open Q9FiveAxisValuation (valuation)
open Q9FiveAxisInputClauses
open Q9SharedContactCNF (Axis)
open private certificateFingerprint satisfies_one satisfies_and from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactGeometryReplay

private def clauseProof (h : Ident) (spec : Json) : TermElabM Term := do
  let row ← Lean.ofExcept spec.getArr?
  let kind ← Lean.ofExcept row[0]!.getStr?
  let number (i : Nat) := Lean.ofExcept row[i]!.getNat?
  let lit (i : Nat) : TermElabM NumLit := return Syntax.mkNumLit (toString (← number i))
  let bool (i : Nat) : TermElabM Term := do
    if (← number i) = 0 then `(false) else `(true)
  match kind with
  | "close" =>
    let x ← lit 1
    let y ← lit 2
    `(close_clause $h $x $y (by decide +kernel))
  | "mask" =>
    let x ← lit 1
    let y ← lit 2
    `(forbidden_mask_clause $h $x $y (by decide +kernel) (by decide +kernel) (by decide +kernel))
  | "translate" =>
    let w ← lit 1
    let i ← lit 2
    let j ← lit 3
    let p ← lit 4
    let q ← lit 5
    let s ← bool 6
    `(translated_clause $h $w $i $j $p $q $s (by decide +kernel) (by decide +kernel) (by decide +kernel))
  | _ =>
    let s ← bool 1
    if kind = "root" then return ← `(root_clause $h $s)
    if kind == "witness" then
      let m ← lit 1
      let i ← lit 2
      let b ← bool 3
      return ← `(witness_clause $m $i $b)
    if kind == "realized" then
      let m ← lit 1
      return ← `(realized_clause $h $m)
    let w ← lit 2
    match kind with
    | "upper" | "lower" =>
      let axes ← Lean.ofExcept row[3]!.getArr?
      let a ← axes.mapM fun x => do
        let i := Syntax.mkNumLit (toString (← Lean.ofExcept x.getNat?))
        `(($i : Axis))
      if kind == "upper" then
        `(degree_upper_clause $h $s $w [$a,*] (by decide) (by decide))
      else
        `(degree_lower_clause $h $s $w [$a,*] (by decide) (by decide))
    | "parity" =>
      let i ← lit 3
      let p ← lit 4
      `(degree_parity_clause $h $s $w $i $p (by decide))
    | "edge" =>
      let i ← lit 3
      let b ← bool 4
      `(edge_clause $h $s $w $i $b)
    | "polarity" =>
      let p ← bool 3
      let v ← lit 4
      `(polarity_clause $h $s $w $p $v)
    | "opposite" =>
      let i ← lit 3
      let p ← bool 4
      `(opposite_clause $h $s $w $i $p)
    | "mid_lower" =>
      let j ← lit 3
      let i ← lit 4
      `(midpoint_lower_clause $h $s $w $j $i (by decide +kernel))
    | "mid_upper" =>
      let j ← lit 3
      let axes ← Lean.ofExcept row[4]!.getArr?
      let nums ← axes.mapM fun v => do
        return Syntax.mkNumLit (toString (← Lean.ofExcept v.getNat?))
      let a := nums[0]!
      let b := nums[1]!
      let c := nums[2]!
      `(midpoint_upper_clause $h $s $w $j $a $b $c (by decide +kernel) (by decide) (by decide))
    | "three" | "four_occupancy" =>
      let low ← lit 3
      let axes ← Lean.ofExcept row[4]!.getArr?
      let nums ← axes.mapM fun v => do
        return Syntax.mkNumLit (toString (← Lean.ofExcept v.getNat?))
      if kind == "three" then
        let a ← nums.mapM fun i => `(($i : Axis))
        `(three_clause $h $s $w $low [$a,*] (by decide) (by decide +kernel) (by decide))
      else
        let a := nums[0]!
        let b := nums[1]!
        `(four_occupancy_clause $h $s $w $low $a $b (by decide) (by decide +kernel) (by decide))
    | "four_sign" =>
      let low ← lit 3
      let a ← lit 4
      let p ← if (← number 5) = 0 then `(true) else `(false)
      `(four_sign_clause $h $s $w $low $a $p (by decide) (by decide +kernel) (by decide))
    | "orbit" =>
      let p ← bool 3
      `(orbit_clause $h $s $w (by decide +kernel) $p (by decide +kernel))
    | _ => throwError "Unknown five-axis input label {kind}"

private def justify (h : Ident) (v formula : Expr) (labels : Array Json)
    (start stop : Nat) : TermElabM Expr := do
  let width := stop - start
  if width = 1 then
    unless formula.isAppOfArity ``Sat.Fmla.one 1 do
      throwError "Rectangle labels do not match row {start + 1}"
    let clause := formula.appArg!
    let term ← clauseProof h labels[start]!
    let expected := mkApp2 (mkConst ``Sat.Valuation.satisfies) v clause
    let proof ← withRef term <| withoutErrToSorry do
      let proof ← elabTermEnsuringType term expected
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars proof
    return mkApp3 (mkConst ``satisfies_one) v clause proof
  if hsplit : 1 < stop - start then
    unless formula.isAppOfArity ``Sat.Fmla.and 2 do
      throwError "Rectangle labels do not match rows {start + 1} through {stop}"
    let a := formula.appFn!.appArg!
    let b := formula.appArg!
    let middle := start + (stop - start) / 2
    let ha ← justify h v a labels start middle
    let hb ← justify h v b labels middle stop
    return mkApp5 (mkConst ``satisfies_and) v a b ha hb
  else
    throwError "Rectangle labels do not match rows {start + 1} through {stop}"
termination_by stop - start
decreasing_by all_goals omega

elab "replay_five_axis_case " orbit:num satisfied:ident impossible:ident fingerprint:num certificate:term : command => do
  Lean.Elab.Command.liftTermElabM do
    let .lit (.strVal contents) ← elabTermEnsuringType certificate (mkConst ``String)
      | throwError "Expected literal five-axis case certificate data"
    unless certificateFingerprint contents == fingerprint.getNat.toUInt64 do
      throwErrorAt certificate "Rectangle certificate fingerprint mismatch"
    let data ← Lean.ofExcept (Json.parse contents)
    let input ← Lean.ofExcept ((data.getObjVal? "cnf").bind Json.getStr?)
    let trace ← Lean.ofExcept ((data.getObjVal? "lrat").bind Json.getStr?)
    let labels ← Lean.ofExcept ((data.getObjVal? "labels").bind Json.getArr?)
    let ns ← getCurrNamespace
    let satisfiedName := ns ++ satisfied.getId
    let impossibleName := ns ++ impossible.getId
    let Std.Internal.Parsec.ParseResult.success _ (_, rows) :=
      Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_, input.startPos⟩
      | throwError "Could not parse the five-axis case CNF"
    unless rows.size == labels.size do
      throwError "Rectangle input and labels have different lengths"
    let formula := Mathlib.Tactic.Sat.buildConj rows 0 rows.size
    let ctxName ← mkAuxDeclName (impossibleName ++ `ctx)
    addDecl <| .defnDecl {
      name := ctxName
      levelParams := []
      type := mkConst ``Sat.Fmla
      value := formula
      hints := .regular 0
      safety := .safe
    }
    let ctx := Lean.mkConst ctxName
    let q9 := mkApp (mkConst ``Q) (mkNatLit 9)
    let supportType := mkApp (mkConst ``Finset [Level.zero]) q9
    let signType ← mkArrow (mkConst ``Bool) (← mkArrow q9 (mkConst ``Int))
    let idx := Syntax.mkNumLit (toString orbit.getNat)
    let reps ← elabTerm (← `(Q9FiveAxisOrbitCover.representatives[$idx]!)) none
    synthesizeSyntheticMVarsNoPostponing
    let reps ← instantiateMVars reps
    withLocalDeclD `C supportType fun C =>
    withLocalDeclD `D supportType fun D =>
    withLocalDeclD `f signType fun f =>
    withLocalDeclD `h (mkAppN (mkConst ``Inputs) #[C, D, f, reps]) fun h => do
      let vars := #[C, D, f, h]
      let v := mkAppN (mkConst ``valuation) #[C, D, f]
      let follows ← justify (mkIdent `h) v formula labels 0 labels.size
      let type ← mkForallFVars vars (mkApp2 (mkConst ``Sat.Valuation.satisfies_fmla) v ctx)
      let type ← instantiateMVars type
      let value ← instantiateMVars (← mkLambdaFVars vars follows)
      addDecl <| .thmDecl {name := satisfiedName, levelParams := [], type, value}
      let Std.Internal.Parsec.ParseResult.success _ steps :=
        Mathlib.Tactic.Sat.Parser.parseLRAT ⟨_, trace.startPos⟩
        | throwError "Could not parse the five-axis case LRAT certificate"
      let replay ← Q9K33ReplayBatches.replay impossibleName ctx formula rows steps
      let type ← mkForallFVars vars (mkConst ``False)
      let value ← mkLambdaFVars vars (mkApp2 replay v (mkAppN (mkConst satisfiedName) vars))
      addDecl <| .thmDecl {name := impossibleName, levelParams := [], type, value}

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisReplay
