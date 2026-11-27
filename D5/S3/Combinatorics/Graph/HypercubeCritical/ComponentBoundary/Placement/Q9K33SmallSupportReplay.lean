/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportReplay
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportReplay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The six-axis contact rectangles force a component smaller than sixty. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33SmallSupportClauses
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33NormalizedRectangle
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33CompletionInputs
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33ReplayBatches
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactGeometryReplay

/-! The rectangle and direction-pair constraints leave one component of size at most 54. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option linter.style.longLine false
set_option Elab.async false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33SmallSupportReplay

open Lean Meta Elab Term
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization (normalize)
open BalancedCriticalSpectrum (Q flip IsBalanced)
open BalancedCubeComponentBoundary (regular_directions exterior_even)
open BalancedCubeGirth (no_selected_square)
open Q9IsotropicHuang (parity)
open Q9SharedContactCNF (Axis Word Variable pos neg)
open Q9SharedContactNormalized (LocalRules)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9SquareMaskGraph (activeAxes)
open Q9K33SmallSupportClauses
open Q9K33CompletionInputs (exists_corner_for_each_direction_pair sixty_le_actual_component)
open Q9K33NormalizedRectangle (normalization_of_nine_masks_on_six_axes)
open Q9WeightedSaturation (defect signedBiadjacency)
open Q9ComponentSaturation (componentDefect)
open TwoBalancedComponents (componentFinset)
open Translation.Q9ActualAperiodicity (signed_defect_det_eq_component)
open private component_connected from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TranslationAperiodicity
open private evenGrid oddGrid rowMaskAxis colMaskAxis from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33NormalizedRectangle
open private differingAxes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private normalize_local_rules normalize_hammingDist from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactNormalized
open private normalize_flip_axis from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized
open private certificateFingerprint satisfies_one satisfies_and from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactGeometryReplay

structure Geometry (S : Bool → Finset (Q 9)) : Prop where
  local_rules : ∀ s, LocalRules (S s)
  separate : ∀ x ∈ S false, ∀ y ∈ S true, 2 ≤ hammingDist x y
  contact_mask : ∀ x ∈ S false, ∀ y ∈ S true, parity x = false → hammingDist x y = 2 →
    ∃ i j : Fin 3, differingAxes x y = {rowMaskAxis i, colMaskAxis j}
  grid : ∀ (s : Bool) (w : Word), w ∈ (if s then oddGrid else evenGrid) → cubeBitVec 9 w ∈ S s
  corner : ∀ (s : Bool) (i j : Axis), i ≠ j →
    ∃ x ∈ S s, flip x i ∈ S s ∧ flip x j ∈ S s
  size : ∀ s, 60 ≤ (S s).card

private theorem gridClause {S : Bool → Finset (Q 9)} (h : Geometry S) (s : Bool) (w : Word)
    (hw : w ∈ (if s then oddGrid else evenGrid)) :
    (witnessValuation S).satisfies [pos (Variable.occupied s w)] := by
  intro hn
  exact hn ((occupied_value S s w).mpr (h.grid s w hw))

private theorem closeClause {S : Bool → Finset (Q 9)} (h : Geometry S) (x y : Word)
    (hd : hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) ≤ 1) :
    (witnessValuation S).satisfies [neg (Variable.occupied false x), neg (Variable.occupied true y)] := by
  intro hx hy
  have hsep := h.separate _ ((occupied_value S false x).mp hx) _ ((occupied_value S true y).mp hy)
  omega

private theorem absentMaskClause {S : Bool → Finset (Q 9)} (h : Geometry S) (x y : Word)
    (hp : parity (cubeBitVec 9 x) = false)
    (hd : hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 2)
    (hbad : ∀ i j : Fin 3, differingAxes (cubeBitVec 9 x) (cubeBitVec 9 y) ≠
      {rowMaskAxis i, colMaskAxis j}) :
    (witnessValuation S).satisfies [neg (Variable.occupied false x), neg (Variable.occupied true y)] := by
  intro hx hy
  obtain ⟨i, j, hm⟩ := h.contact_mask _ ((occupied_value S false x).mp hx)
    _ ((occupied_value S true y).mp hy) hp hd
  exact hbad i j hm

private def clauseProof (S h : Ident) (spec : Json) : TermElabM Term := do
  let row ← Lean.ofExcept spec.getArr?
  let kind ← Lean.ofExcept row[0]!.getStr?
  let number (i : Nat) := Lean.ofExcept row[i]!.getNat?
  let lit (i : Nat) : TermElabM NumLit := return Syntax.mkNumLit (toString (← number i))
  if kind = "separation" then
    let x ← lit 1
    let y ← lit 2
    let mask := (← number 1) ^^^ (← number 2)
    if ((List.range 9).filter (fun i => mask.testBit i)).length ≤ 1 then
      return ← `(closeClause $h $x $y (by decide +kernel))
    return ← `(absentMaskClause $h $x $y (by decide +kernel) (by decide +kernel) (by decide +kernel))
  if kind = "size" then
    let b ← lit 1
    return ← `(obstructionClause $b (Geometry.size $h (sizeBlock $b).1))
  let s ← if (← number 1) = 0 then `(false) else `(true)
  if kind = "realized" then
    let p ← lit 2
    return ← `(pairClause $s $p (Geometry.corner $h $s))
  if kind = "witness" then
    let p ← lit 2
    let w ← lit 3
    match ← number 4 with
    | 0 => return ← `(witnesses_imply_center (S := $S) $s $p $w)
    | 1 => return ← `(witnesses_imply_first (S := $S) $s $p $w)
    | 2 => return ← `(witnesses_imply_second (S := $S) $s $p $w)
    | _ => throwError "Unknown corner witness projection"
  let w ← lit 2
  if kind = "grid" then
    return ← `(gridClause $h $s $w (by decide +kernel))
  let rules ← `(Geometry.local_rules $h $s)
  if kind = "upper" || kind = "lower" then
    let axes ← Lean.ofExcept row[3]!.getArr?
    let axes ← axes.mapM fun axis => do
      let i := Syntax.mkNumLit (toString (← Lean.ofExcept axis.getNat?))
      `(($i : Axis))
    if kind = "upper" then
      return ← `(ordinaryClause (S := $S)
        (Q9TightDistanceTwoCNF.upperClause $s $rules $w [$axes,*] (by decide)) (by decide))
    return ← `(ordinaryClause (S := $S)
      (Q9TightDistanceTwoCNF.lowerClause $s $rules $w [$axes,*] (by decide)) (by decide))
  if kind = "parity" then
    let step := Syntax.mkNumLit (toString ((← number 3) - 1))
    let sign ← lit 4
    return ← `(ordinaryClause (S := $S)
      (Q9TightDistanceTwoCNF.parityClause $s $rules $w $step $sign) (by decide))
  throwError "Unknown rectangle clause kind {kind}"

private partial def justify (S h : Ident) (v formula : Expr) (labels : Array Json)
    (start stop : Nat) : TermElabM Expr := do
  let width := stop - start
  if width = 1 then
    unless formula.isAppOfArity ``Sat.Fmla.one 1 do
      throwError "Rectangle labels do not match row {start + 1}"
    let clause := formula.appArg!
    let term ← clauseProof S h labels[start]!
    let expected := mkApp2 (mkConst ``Sat.Valuation.satisfies) v clause
    let proof ← withRef term <| withoutErrToSorry do
      let proof ← elabTermEnsuringType term expected
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars proof
    return mkApp3 (mkConst ``satisfies_one) v clause proof
  unless width > 1 && formula.isAppOfArity ``Sat.Fmla.and 2 do
    throwError "Rectangle labels do not match rows {start + 1} through {stop}"
  let a := formula.appFn!.appArg!
  let b := formula.appArg!
  let middle := start + width / 2
  let ha ← justify S h v a labels start middle
  let hb ← justify S h v b labels middle stop
  return mkApp5 (mkConst ``satisfies_and) v a b ha hb

elab "replay_six_axis_rectangle " satisfied:ident impossible:ident fingerprint:num certificate:term : command => do
  Lean.Elab.Command.liftTermElabM do
    let .lit (.strVal contents) ← elabTermEnsuringType certificate (mkConst ``String)
      | throwError "Expected literal rectangle certificate data"
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
      | throwError "Could not parse the rectangle CNF"
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
    let supportType := mkArrow (mkConst ``Bool)
      (mkApp (mkConst ``Finset [Level.zero]) (mkApp (mkConst ``Q) (mkNatLit 9)))
    withLocalDeclD `S (← supportType) fun S =>
    withLocalDeclD `h (mkApp (mkConst ``Geometry) S) fun h => do
      let vars := #[S, h]
      let v := mkApp (mkConst ``witnessValuation) S
      let follows ← justify (mkIdent `S) (mkIdent `h) v formula labels 0 labels.size
      let type ← mkForallFVars vars (mkApp2 (mkConst ``Sat.Valuation.satisfies_fmla) v ctx)
      let value ← mkLambdaFVars vars follows
      addDecl <| .thmDecl {name := satisfiedName, levelParams := [], type, value}
      let Std.Internal.Parsec.ParseResult.success _ steps :=
        Mathlib.Tactic.Sat.Parser.parseLRAT ⟨_, trace.startPos⟩
        | throwError "Could not parse the rectangle LRAT certificate"
      let replay ← Q9K33ReplayBatches.replay impossibleName ctx formula rows steps
      let type ← mkForallFVars vars (mkConst ``False)
      let value ← mkLambdaFVars vars (mkApp2 replay v (mkAppN (mkConst satisfiedName) vars))
      addDecl <| .thmDecl {name := impossibleName, levelParams := [], type, value}

set_option maxHeartbeats 0 in
replay_six_axis_rectangle normalizedInputSatisfied normalizedImpossible 2063002516818150078
  (include_str "../../../../../../../Evidence/D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupport.result.json")

open Classical in
private theorem local_rules {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) : LocalRules C where
  occupied_degree := fun _ hx => regular_directions C hr hx
  exterior_degree := exterior_even C hr hb
  no_square := fun _ _ _ hne hx hi hj => no_selected_square hb hne hx hi hj

open Classical in
/-- In a 258-vertex subcubic subset, an actual separated balanced cubic
component pair with singular weighted defects cannot have nine masks
supported on only six axes on a starting parity. -/
theorem no_nine_masks_on_six_axes_in_actual_pair
    {U : Finset (Q 9)} (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (K L : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent)
    {b : Bool}
    (hsep : ∀ x ∈ componentFinset U K, ∀ y ∈ componentFinset U L, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (componentFinset U K : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (componentFinset U L : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced (componentFinset U K)) (hbD : IsBalanced (componentFinset U L))
    (hdetC : ∀ w : Fin 9 → ℝ, (componentDefect w U false K).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (componentDefect w U false L).det = 0)
    (haxes : (activeAxes (minimumDisplacements (componentFinset U K) (componentFinset U L) b 2)).card = 6) :
    (minimumDisplacements (componentFinset U K) (componentFinset U L) b 2).card ≠ 9 := by
  intro hmask
  obtain ⟨π, o, hleft, hright, hmask'⟩ := normalization_of_nine_masks_on_six_axes
    hsep hrC hrD (component_connected U K) (component_connected U L) hbC hbD
    (fun w => (signed_defect_det_eq_component w U false K).trans (hdetC w))
    (fun w => (signed_defect_det_eq_component w U false L).trans (hdetD w)) haxes hmask
  let T (K' : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent) :=
    (componentFinset U K').map (normalize π o).toEmbedding
  let S := Q9TightDistanceTwoCNF.support (T K) (T L)
  have hcorner (J : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent)
      (hdet : ∀ w : Fin 9 → ℝ, (componentDefect w U false J).det = 0) (i j : Axis) (hne : i ≠ j) :
      ∃ x ∈ T J, flip x i ∈ T J ∧ flip x j ∈ T J := by
    obtain ⟨x, hx, hi, hj⟩ := exists_corner_for_each_direction_pair hdet
      (show π i ≠ π j from fun h => hne (π.injective h))
    refine ⟨normalize π o x, mem_map.mpr ⟨x, hx, rfl⟩, ?_, ?_⟩
    · rw [← normalize_flip_axis]
      exact mem_map.mpr ⟨_, hi, rfl⟩
    · rw [← normalize_flip_axis]
      exact mem_map.mpr ⟨_, hj, rfl⟩
  apply normalizedImpossible S
  refine ⟨?_, ?_, hmask', ?_, ?_, ?_⟩
  · intro s
    cases s
    · exact normalize_local_rules π o _ (local_rules hrC hbC)
    · exact normalize_local_rules π o _ (local_rules hrD hbD)
  · intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hy
    change 2 ≤ hammingDist (normalize π o u) (normalize π o v)
    rw [normalize_hammingDist]
    exact hsep u hu v hv
  · intro s
    cases s
    · exact hleft
    · exact hright
  · intro s
    cases s
    · exact hcorner K hdetC
    · exact hcorner L hdetD
  · intro s
    cases s
    · change 60 ≤ (T K).card
      simpa [T] using sixty_le_actual_component hU hdeg K hrC hbC
    · change 60 ≤ (T L).card
      simpa [T] using sixty_le_actual_component hU hdeg L hrD hbD

#print axioms no_nine_masks_on_six_axes_in_actual_pair

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33SmallSupportReplay
