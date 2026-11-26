/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMaskReplay
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMaskReplay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A checked refutation excludes exactly eight distance-two masks. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskGraph
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactGeometryReplay

/-! Replay the compact LRAT refutation of the normalized eight-mask family. -/

set_option autoImplicit false
set_option maxRecDepth 40000
set_option linter.style.longLine false
set_option Elab.async false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskReplay

open Lean Meta Elab Term
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9WeightedSaturation (defect signedBiadjacency)
open Q9FiveAxisMissingContact (Geometry exists_normalized_eight_mask_contact)
open Q9SharedContactCNF (Axis)
open Q9TightDistanceTwoCNF (support)
open Q9EightMaskClauses
open private witnessMasks from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses
open private certificateFingerprint satisfies_one satisfies_and from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactGeometryReplay
open private exists_both_parity_supported_of_signed_defect_singular from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ActualMinimumDisplacements
open private minimum_displacements_three_extensions mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

private def clauseProof (C D h family : Ident) (spec : Json) : TermElabM Term := do
  let row ← Lean.ofExcept spec.getArr?
  let kind ← Lean.ofExcept row[0]!.getStr?
  let number (i : Nat) := Lean.ofExcept row[i]!.getNat?
  let numeral (n : Nat) := Syntax.mkNumLit (toString n)
  let lit (i : Nat) : TermElabM NumLit := return numeral (← number i)
  if kind = "separation" then
    let x ← lit 1
    let y ← lit 2
    let mask := (← number 1) ^^^ (← number 2)
    let axes := (List.range 9).filter (fun i => mask.testBit i)
    if axes.length ≤ 1 then
      return ← `(closeClause $h $x $y (by decide +kernel))
    return ← `(absentMaskClause $family $x $y
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
  if kind = "witness-left" || kind = "witness-right" || kind = "realized" then
    let mask ← number 1
    let some m := (List.finRange 8).find? (fun m => (witnessMasks m).toNat == mask)
      | throwError "Unknown eight-mask witness mask {mask}"
    let m := numeral m.val
    if kind = "realized" then
      return ← `(normalizedRealizedClause $family $m)
    let i := numeral ((← number 2) / 2)
    if kind = "witness-left" then
      return ← `(witnesses_imply_left (C := $C) (D := $D) $m $i)
    return ← `(witnesses_imply_right (C := $C) (D := $D) $m $i)
  let side ← number 1
  let s ← if side = 0 then `(false) else `(true)
  if kind = "root" then
    return ← `(rootClause $h $s)
  let w ← lit 2
  let rules ← if side = 0 then `(Geometry.left_rules $h) else `(Geometry.right_rules $h)
  if kind = "upper" || kind = "lower" then
    let axes ← Lean.ofExcept row[3]!.getArr?
    let axes ← axes.mapM fun axis => do
      let i := numeral (← Lean.ofExcept axis.getNat?)
      `(($i : Axis))
    if kind = "upper" then
      return ← `(ordinaryClause (C := $C) (D := $D)
        (Q9TightDistanceTwoCNF.upperClause (S := support $C $D) $s $rules $w [$axes,*]
          (by decide)) (by decide))
    return ← `(ordinaryClause (C := $C) (D := $D)
      (Q9TightDistanceTwoCNF.lowerClause (S := support $C $D) $s $rules $w [$axes,*]
        (by decide)) (by decide))
  if kind = "parity" then
    let step := numeral ((← number 3) - 1)
    let polarity ← lit 4
    return ← `(ordinaryClause (C := $C) (D := $D)
      (Q9TightDistanceTwoCNF.parityClause (S := support $C $D) $s $rules $w $step $polarity)
      (by decide))
  throwError "Unknown eight-mask clause kind {kind}"

private partial def justify (C D h family : Ident) (v formula : Expr) (labels : Array Json)
    (start stop : Nat) : TermElabM Expr := do
  let width := stop - start
  if width = 1 then
    unless formula.isAppOfArity ``Sat.Fmla.one 1 do
      throwError "Eight-mask labels do not match the CNF at row {start + 1}"
    let clause := formula.appArg!
    let term ← clauseProof C D h family labels[start]!
    let expected := mkApp2 (mkConst ``Sat.Valuation.satisfies) v clause
    let proof ← withRef term <| withoutErrToSorry do
      let proof ← elabTermEnsuringType term expected
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars proof
    return mkApp3 (mkConst ``satisfies_one) v clause proof
  unless width > 1 && formula.isAppOfArity ``Sat.Fmla.and 2 do
    throwError "Eight-mask labels do not match the CNF at rows {start + 1} through {stop}"
  let a := formula.appFn!.appArg!
  let b := formula.appArg!
  let middle := start + width / 2
  let ha ← justify C D h family v a labels start middle
  let hb ← justify C D h family v b labels middle stop
  return mkApp5 (mkConst ``satisfies_and) v a b ha hb

elab "replay_eight_masks " satisfied:ident impossible:ident fingerprint:num certificate:term : command => do
  Lean.Elab.Command.liftTermElabM do
    let .lit (.strVal contents) ← elabTermEnsuringType certificate (mkConst ``String)
      | throwError "Expected literal eight-mask certificate data"
    unless certificateFingerprint contents == fingerprint.getNat.toUInt64 do
      throwErrorAt certificate "Certificate bytes differ from the fingerprint pinned in Lean source"
    let data ← Lean.ofExcept (Json.parse contents)
    let input ← Lean.ofExcept ((data.getObjVal? "cnf").bind Json.getStr?)
    let trace ← Lean.ofExcept ((data.getObjVal? "lrat").bind Json.getStr?)
    let labels ← Lean.ofExcept ((data.getObjVal? "labels").bind Json.getArr?)
    let ns ← getCurrNamespace
    let satisfiedName := ns ++ satisfied.getId
    let impossibleName := ns ++ impossible.getId
    let (_, ctx, formula, replay) ← Mathlib.Tactic.Sat.fromLRATAux input trace impossibleName
    let supportType := mkApp (mkConst ``Finset [Level.zero]) (mkApp (mkConst ``Q) (mkNatLit 9))
    withLocalDeclD `C supportType fun C =>
    withLocalDeclD `D supportType fun D =>
    withLocalDeclD `h (mkApp2 (mkConst ``Geometry) C D) fun h => do
      let masks := mkApp4 (mkConst ``minimumDisplacements) C D (mkConst ``Bool.false) (mkNatLit 2)
      let familyType ← mkEq masks (mkConst ``normalizedFamily)
      withLocalDeclD `family familyType fun family => do
        let vars := #[C, D, h, family]
        let v := mkApp2 (mkConst ``witnessValuation) C D
        let follows ← justify (mkIdent `C) (mkIdent `D) (mkIdent `h) (mkIdent `family)
          v formula labels 0 labels.size
        let type ← mkForallFVars vars (mkApp2 (mkConst ``Sat.Valuation.satisfies_fmla) v ctx)
        let value ← mkLambdaFVars vars follows
        addDecl <| .thmDecl {name := satisfiedName, levelParams := [], type, value}
        let type ← mkForallFVars vars (mkConst ``False)
        let value ← mkLambdaFVars vars (mkApp2 replay v (mkAppN (mkConst satisfiedName) vars))
        addDecl <| .thmDecl {name := impossibleName, levelParams := [], type, value}

set_option maxHeartbeats 0 in
replay_eight_masks normalizedInputSatisfied normalizedImpossible 12479109254839190949
  (include_str "../../../../../../../Evidence/D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9EightMasks.result.json")

open Classical in
/-- The eight-mask case at distance two is impossible for two separated connected
balanced cubic nine-cube supports with universally singular signed defects. -/
theorem minimum_displacements_card_ne_eight
    {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0) :
    (minimumDisplacements C D b 2).card ≠ 8 := by
  intro hcard
  let F := minimumDisplacements C D b 2
  have hsize (T : Finset (Fin 9)) (hT : T ∈ F) : T.card = 2 := by
    obtain ⟨x, _, y, _, _, hd, rfl⟩ := mem_minimumDisplacements.mp hT
    exact hd
  have hthree := minimum_displacements_three_extensions C D b 2 hsep
    (fun i => by
      let w : Fin 9 → ℝ := fun k => if k = i then 2 else 1
      have hw (k : Fin 9) : 0 < w k := by
        dsimp only [w]
        split <;> norm_num
      exact exists_both_parity_supported_of_signed_defect_singular C hrC hcC hbC w hw (hdetC w) b)
    (fun c => exists_both_parity_supported_of_signed_defect_singular D hrD hcD hbD
      (fun _ => 1) (fun _ => by norm_num) (hdetD fun _ => 1) c)
  obtain ⟨A, P, R, hA, hP, hR, hPR, hfamily⟩ :=
    Q9EightMaskGraph.eight_edge_family_eq_delete_two F hcard hsize hthree
  obtain ⟨_, _, h, hnormalized⟩ :=
    exists_normalized_eight_mask_contact hA hP hR hPR hfamily hsep hrC hrD hbC hbD
  exact normalizedImpossible _ _ h hnormalized

#print axioms minimum_displacements_card_ne_eight

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskReplay
