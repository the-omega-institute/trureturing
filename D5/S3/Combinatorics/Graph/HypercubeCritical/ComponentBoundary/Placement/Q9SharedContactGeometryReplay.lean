/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactGeometryReplay
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactGeometryReplay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Kernel-checked refutations exclude all three normalized shared distance-three contacts. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactCNF

/-! Replay the three shared-contact refutations with inputs justified by the cube model. -/

set_option autoImplicit false
set_option maxRecDepth 20000
set_option linter.style.longLine false
set_option Elab.async false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactGeometryReplay

open Lean Meta Elab Term
open Q9SharedContactCNF

private theorem satisfies_one (v : Sat.Valuation) (c : Sat.Clause) (h : v.satisfies c) :
    v.satisfies_fmla (Sat.Fmla.one c) :=
  ⟨fun _ hc => (List.mem_singleton.mp hc).symm ▸ h⟩

private theorem satisfies_and (v : Sat.Valuation) (a b : Sat.Fmla)
    (ha : v.satisfies_fmla a) (hb : v.satisfies_fmla b) :
    v.satisfies_fmla (Sat.Fmla.and a b) :=
  ⟨fun c hc => (List.mem_append.mp hc).elim (ha.prop c) (hb.prop c)⟩

private def specTerm (model : Ident) (spec : Json) : TermElabM Term := do
  let row ← Lean.ofExcept spec.getArr?
  let kind ← Lean.ofExcept row[0]!.getStr?
  let natural (n : Nat) : TermElabM NumLit :=
    return Syntax.mkNumLit (toString (← Lean.ofExcept row[n]!.getNat?))
  let side : TermElabM Term := do
    let n ← Lean.ofExcept row[1]!.getNat?
    if n = 0 then `(false) else `(true)
  if kind = "upper" || kind = "lower" then
    let s ← side
    let vertex ← natural 2
    let axes ← Lean.ofExcept row[3]!.getArr?
    let axes ← axes.mapM fun (a : Json) => do
      let n ← Lean.ofExcept a.getNat?
      let literal := Syntax.mkNumLit (toString n)
      `(($literal : Axis))
    if kind = "upper" then `(upperClause $model $s $vertex [$axes,*] (by decide))
    else `(lowerClause $model $s $vertex [$axes,*] (by decide))
  else if kind = "square" then
    let s ← side
    let w ← natural 2
    let i ← natural 3
    let j ← natural 4
    `(squareClause $model $s $w $i $j (by decide))
  else if kind = "separation" then
    let u ← natural 1
    let v ← natural 2
    `(separationClause $model $u $v (by decide))
  else if kind = "parity" then
    let s ← side
    let w ← natural 2
    let i ← Lean.ofExcept row[3]!.getNat?
    let step := Syntax.mkNumLit (toString (i - 1))
    let sign ← natural 4
    `(parityClause $model $s $w $step $sign)
  else if kind = "root" then
    let s ← Lean.ofExcept row[1]!.getNat?
    if s = 0 then `(leftRootClause $model) else `(rightRootClause $model)
  else if kind = "left-direction" then
    let i ← natural 1
    `(leftDirectionClause $model $i (by decide))
  else if kind = "right-direction" then
    let i ← natural 1
    `(rightDirectionClause $model $i (by decide))
  else throwError "Unknown clause kind {kind}"

private partial def justifyFormula (model : Ident) (v ctx : Expr) (specs : Array Json)
    (start stop : Nat) : TermElabM Expr := do
  let width := stop - start
  if width = 1 then
    let clause := ctx.appArg!
    let term ← specTerm model specs[start]!
    let expected := mkApp2 (mkConst ``Sat.Valuation.satisfies) v clause
    let proof ← withRef term <| elabTermEnsuringType term expected
    synthesizeSyntheticMVarsNoPostponing
    return mkApp3 (mkConst ``satisfies_one) v clause (← instantiateMVars proof)
  if width = 0 then throwError "Empty geometry formula"
  let a := ctx.appFn!.appArg!
  let b := ctx.appArg!
  let middle := start + width / 2
  let ha ← justifyFormula model v a specs start middle
  let hb ← justifyFormula model v b specs middle stop
  return mkApp5 (mkConst ``satisfies_and) v a b ha hb

-- Pin the external input in Lean source because include_str is read during elaboration.
-- Update the corresponding fingerprint whenever a certificate is regenerated.
private def certificateFingerprint (text : String) : UInt64 :=
  text.toUTF8.foldl (fun digest byte => (digest ^^^ byte.toUInt64) * 1099511628211)
    14695981039346656037

elab "replay_geometry " name:ident index:num fingerprint:num certificate:term : command => do
  Lean.Elab.Command.liftTermElabM do
    let .lit (.strVal contents) ← elabTermEnsuringType certificate (mkConst ``String)
      | throwError "Expected literal certificate data"
    unless certificateFingerprint contents == fingerprint.getNat.toUInt64 do
      throwErrorAt certificate "Certificate bytes differ from the fingerprint pinned in Lean source"
    let data ← Lean.ofExcept (Json.parse contents)
    let input ← Lean.ofExcept ((data.getObjVal? "cnf").bind Json.getStr?)
    let trace ← Lean.ofExcept ((data.getObjVal? "lrat").bind Json.getStr?)
    let specs ← Lean.ofExcept ((data.getObjVal? "labels").bind Json.getArr?)
    let (_, _, formula, replay) ← Mathlib.Tactic.Sat.fromLRATAux input trace name.getId
    let indexTerm ← elabTermEnsuringType index (mkApp (mkConst ``Fin) (mkNatLit 3))
    let modelType := mkApp (mkConst ``Model) indexTerm
    let modelName := `model
    withLocalDeclD modelName modelType fun m => do
      let v := mkApp2 (mkConst ``valuation) indexTerm m
      let follows ← justifyFormula (mkIdent modelName) v formula specs 0 specs.size
      let value ← mkLambdaFVars #[m] (mkApp2 replay v follows)
      let type ← mkForallFVars #[m] (mkConst ``False)
      addDecl <| .thmDecl {name := name.getId, levelParams := [], type, value}

set_option maxHeartbeats 0 in
-- Elaborating the full list of geometric clause proofs needs a larger budget.
replay_geometry sharedCase3 2 8169083809360750239
  (include_str "../../../../../../../Evidence/D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactOverlap3.result.json")

#print axioms sharedCase3

set_option maxHeartbeats 0 in
-- Elaborating the full list of geometric clause proofs needs a larger budget.
replay_geometry sharedCase2 1 9104730146278566203
  (include_str "../../../../../../../Evidence/D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactOverlap2.result.json")

#print axioms sharedCase2

set_option maxHeartbeats 0 in
-- Elaborating the full list of geometric clause proofs needs a larger budget.
replay_geometry sharedCase1 0 16453404429952119345
  (include_str "../../../../../../../Evidence/D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactOverlap1.result.json")

#print axioms sharedCase1

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip IsBalanced)
open BalancedCubeComponentBoundary (directions)
open Q9SharedContactAxisOrbits (canonicalDifference canonicalLeft canonicalRight)
open Q9SharedContactNormalized (LocalRules exists_normalized_shared_contact)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization (origin)

open Classical in
/-- A distance-three contact between two three-separated balanced cubic
nine-cube supports cannot have a shared occupied direction. -/
theorem no_shared_distance_three
    {C D : Finset (Q 9)}
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 3 ≤ hammingDist x y)
    {x y : Q 9} (hx : x ∈ C) (hy : y ∈ D) (hd : hammingDist x y = 3)
    (hshare : (directions C x ∩ directions D y).Nonempty) : False := by
  obtain ⟨k, A, B, hA, hB, hdist, hxA, hyB, hdirsA, hdirsB⟩ :=
    exists_normalized_shared_contact hrC hrD hbC hbD hsep hx hy hd hshare
  let S : Bool → Finset (Q 9) := fun b => if b then B else A
  have hs (b : Bool) : LocalRules (S b) := by
    cases b
    · exact hA
    · exact hB
  let M : Model k := ⟨S, hs, hdist, hxA, hyB, hdirsA, hdirsB⟩
  fin_cases k
  · exact sharedCase1 M
  · exact sharedCase2 M
  · exact sharedCase3 M

#print axioms no_shared_distance_three

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactGeometryReplay
