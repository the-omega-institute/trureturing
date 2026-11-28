import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33ReplayBatches
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactGeometryReplay

/-! The unsigned RUP refutations for the two rooted six-axis ten-mask families. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option Elab.async false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskSixAxisReplay

open Lean Meta Elab Term
open BalancedCriticalSpectrum (Q)
open Q9IsotropicHuang (parity)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9FiveAxisMissingContact (Geometry)
open Q9SharedContactCNF (Word Axis Variable pos neg)
open Q9TightDistanceTwoCNF (support)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open private evenWord evenWord_index indexOfWord variable_index_lt literalIndex positive_list
  rootWord rootWord_cube axesOf xor_mask from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses
open private mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private certificateFingerprint satisfies_one satisfies_and from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactGeometryReplay

inductive Shape where
  | wheel
  | bipartitePlus

-- The DIMACS witness blocks follow the sorted masks after the root mask 3.
private def witnessMask : Shape → Fin 9 → Word
  | .wheel => ![6, 12, 17, 24, 33, 34, 36, 40, 48]
  | .bipartitePlus => ![6, 9, 12, 18, 20, 24, 33, 36, 48]

/-- All allowed even distance-two masks in the labels of the rooted probe. -/
def Shape.family (shape : Shape) : Finset (Finset Axis) :=
  insert (axesOf (3 : Word)) ((List.finRange 9).map fun m => axesOf (witnessMask shape m)).toFinset

/-- The nonroot masks whose realization is used by the unsigned certificates. -/
def Shape.required : Shape → Finset (Finset Axis)
  | .wheel => {axesOf (12 : Word), axesOf (40 : Word)}
  | .bipartitePlus => {axesOf (20 : Word)}

/-- Roots at words 0 and 3, local cubic rules, separation, and the retained mask conditions. -/
structure Inputs (shape : Shape) (C D : Finset (Q 9)) : Prop where
  geometry : Geometry C D
  allowed : minimumDisplacements C D false 2 ⊆ shape.family
  realized : shape.required ⊆ minimumDisplacements C D false 2

/-- A permitted mask family, its required masks, and nonroot witness blocks in DIMACS order. -/
structure Recipe where
  {witnessCount : Nat}
  witnessMask : Fin witnessCount → Word
  family : Finset (Finset Axis)
  required : Finset (Finset Axis)

structure Recipe.Inputs (recipe : Recipe) (C D : Finset (Q 9)) : Prop where
  geometry : Geometry C D
  allowed : minimumDisplacements C D false 2 ⊆ recipe.family
  realized : recipe.required ⊆ minimumDisplacements C D false 2

private abbrev Shape.recipe (shape : Shape) : Recipe :=
  ⟨witnessMask shape, shape.family, shape.required⟩

private theorem Inputs.toRecipeInputs {shape : Shape} {C D : Finset (Q 9)}
    (h : Inputs shape C D) : Recipe.Inputs shape.recipe C D :=
  ⟨h.geometry, h.allowed, h.realized⟩

private abbrev occ := Variable.occupied

-- The first witness variable has SAT index 10240 and DIMACS number 10241.
private def witnessIndex {n : Nat} (m : Fin n) (i : Fin 256) : Nat :=
  10240 + 256 * m.val + i.val

private noncomputable def valuation (recipe : Recipe) (C D : Finset (Q 9)) :
    Sat.Valuation := fun n =>
  if hn : 10240 ≤ n ∧ n < 10240 + 256 * recipe.witnessCount then
    let k := n - 10240
    let m : Fin recipe.witnessCount := ⟨k / 256, by omega⟩
    let i : Fin 256 := ⟨k % 256, Nat.mod_lt _ (by decide)⟩
    cubeBitVec 9 (evenWord i) ∈ C ∧ cubeBitVec 9 (evenWord i ^^^ recipe.witnessMask m) ∈ D
  else Q9TightDistanceTwoCNF.valuation (support C D) n

private theorem witness_value (recipe : Recipe) (C D : Finset (Q 9))
    (m : Fin recipe.witnessCount) (i : Fin 256) :
    valuation recipe C D (witnessIndex m i) ↔
      cubeBitVec 9 (evenWord i) ∈ C ∧ cubeBitVec 9 (evenWord i ^^^ recipe.witnessMask m) ∈ D := by
  have hm := m.isLt
  have hi := i.isLt
  have hn : 10240 ≤ witnessIndex m i ∧
      witnessIndex m i < 10240 + 256 * recipe.witnessCount := by
    unfold witnessIndex
    omega
  have hdiv : (witnessIndex m i - 10240) / 256 = m.val := by
    unfold witnessIndex
    omega
  have hmod : (witnessIndex m i - 10240) % 256 = i.val := by
    unfold witnessIndex
    omega
  have hM (h : ((witnessIndex m i - 10240) / 256) < recipe.witnessCount) :
      (⟨(witnessIndex m i - 10240) / 256, h⟩ : Fin recipe.witnessCount) = m := Fin.ext hdiv
  have hI (h : ((witnessIndex m i - 10240) % 256) < 256) :
      (⟨(witnessIndex m i - 10240) % 256, h⟩ : Fin 256) = i := Fin.ext hmod
  simp only [valuation, dite_eq_left hn, hM, hI]

private theorem ordinary_value (recipe : Recipe) (C D : Finset (Q 9)) (n : Nat)
    (hn : n < 10240) :
    valuation recipe C D n = Q9TightDistanceTwoCNF.valuation (support C D) n := by
  have hout : ¬ (10240 ≤ n ∧ n < 10240 + 256 * recipe.witnessCount) :=
    fun h => (Nat.not_le_of_lt hn) h.1
  simp only [valuation, dite_eq_right hout]

private theorem ordinaryClause {recipe : Recipe} {C D : Finset (Q 9)} {c : Sat.Clause}
    (h : (Q9TightDistanceTwoCNF.valuation (support C D)).satisfies c)
    (hsmall : List.all c (fun l => decide (literalIndex l < 10240)) = true) :
    (valuation recipe C D).satisfies c := by
  change List Sat.Literal at c
  induction c with
  | nil => exact h
  | cons x xs ih =>
    rw [List.all_cons, Bool.and_eq_true] at hsmall
    have he := ordinary_value recipe C D (literalIndex x) (of_decide_eq_true hsmall.1)
    intro hx
    refine ih (h ?_) hsmall.2
    cases x <;> simp only [literalIndex] at he <;>
      simpa only [Sat.Valuation.neg, ← he] using hx

private theorem occupied_value (recipe : Recipe) (C D : Finset (Q 9)) (s : Bool) (x : Word) :
    valuation recipe C D (occ s x).index ↔ cubeBitVec 9 x ∈ support C D s := by
  rw [ordinary_value recipe C D _ (variable_index_lt _)]
  exact Q9TightDistanceTwoCNF.valuation_occupied _ _ _

private theorem rootClause {recipe : Recipe} {C D : Finset (Q 9)} (h : Recipe.Inputs recipe C D)
    (s : Bool) : (valuation recipe C D).satisfies [pos (occ s (rootWord s))] := by
  intro hn
  apply hn
  apply (occupied_value recipe C D s (rootWord s)).mpr
  cases s
  · simpa [rootWord_cube, support] using h.geometry.left_root
  · simpa [rootWord_cube, support] using h.geometry.right_root

private theorem closeClause {recipe : Recipe} {C D : Finset (Q 9)} (h : Recipe.Inputs recipe C D)
    (x y : Word) (hd : hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) ≤ 1) :
    (valuation recipe C D).satisfies [neg (occ false x), neg (occ true y)] := by
  intro hx hy
  exact h.geometry.forbidden_close ((occupied_value recipe C D false x).mp hx) hd
    ((occupied_value recipe C D true y).mp hy)

private theorem absentMaskClause {recipe : Recipe} {C D : Finset (Q 9)} (h : Recipe.Inputs recipe C D)
    (x y : Word) (hp : parity (cubeBitVec 9 x) = false)
    (hd : hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 2)
    (hbad : axesOf (x ^^^ y) ∉ recipe.family) :
    (valuation recipe C D).satisfies [neg (occ false x), neg (occ true y)] := by
  intro hx hy
  apply hbad
  rw [← xor_mask]
  exact h.allowed (mem_minimumDisplacements.mpr
    ⟨_, (occupied_value recipe C D false x).mp hx,
      _, (occupied_value recipe C D true y).mp hy, hp, hd, rfl⟩)

private theorem witnessLeft {recipe : Recipe} {C D : Finset (Q 9)}
    (m : Fin recipe.witnessCount) (i : Fin 256) :
    (valuation recipe C D).satisfies
      [.neg (witnessIndex m i), pos (occ false (evenWord i))] := by
  intro hw hx
  exact hx ((occupied_value recipe C D false (evenWord i)).mpr
    ((witness_value recipe C D m i).mp hw).1)

private theorem witnessRight {recipe : Recipe} {C D : Finset (Q 9)}
    (m : Fin recipe.witnessCount) (i : Fin 256) :
    (valuation recipe C D).satisfies
      [.neg (witnessIndex m i), pos (occ true (evenWord i ^^^ recipe.witnessMask m))] := by
  intro hw hy
  exact hy ((occupied_value recipe C D true (evenWord i ^^^ recipe.witnessMask m)).mpr
    ((witness_value recipe C D m i).mp hw).2)

private theorem realizedClause {recipe : Recipe} {C D : Finset (Q 9)} (h : Recipe.Inputs recipe C D)
    (m : Fin recipe.witnessCount) (hm : axesOf (recipe.witnessMask m) ∈ recipe.required) :
    (valuation recipe C D).satisfies
      ((List.finRange 256).map (fun i => Sat.Literal.pos (witnessIndex m i))) := by
  obtain ⟨x, hx, y, hy, hp, _, hmask⟩ := mem_minimumDisplacements.mp (h.realized hm)
  obtain ⟨u, rfl⟩ := (cubeBitVec 9).surjective x
  obtain ⟨v, rfl⟩ := (cubeBitVec 9).surjective y
  have hax : axesOf (u ^^^ v) = axesOf (recipe.witnessMask m) := xor_mask.symm.trans hmask
  have he : u ^^^ v = recipe.witnessMask m := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hj' := Finset.ext_iff.mp hax ⟨j, hj⟩
    simp only [axesOf, Finset.mem_filter, Finset.mem_univ, true_and] at hj'
    exact Bool.eq_iff_iff.mpr hj'
  have hv : u ^^^ recipe.witnessMask m = v := by
    rw [← he, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  have hw := (witness_value recipe C D m (indexOfWord u)).mpr
    (by rw [evenWord_index u hp, hv]; exact ⟨hx, hy⟩)
  have hmem : witnessIndex m (indexOfWord u) ∈ (List.finRange 256).map (witnessIndex m) :=
    List.mem_map.mpr ⟨indexOfWord u, List.mem_finRange (indexOfWord u), rfl⟩
  have hs := positive_list (v := valuation recipe C D) ⟨_, hmem, hw⟩
  rw [List.map_map] at hs
  exact hs

private def clauseProof (recipe : Term) (C D : Ident) (h : Term) (spec : Json) : TermElabM Term := do
  let row ← Lean.ofExcept spec.getArr?
  let kind ← Lean.ofExcept row[0]!.getStr?
  let numeral (i : Nat) : TermElabM NumLit :=
    return Syntax.mkNumLit (toString (← Lean.ofExcept row[i]!.getNat?))
  match kind with
  | "close" =>
    let x ← numeral 1
    let y ← numeral 2
    `(closeClause $h $x $y (by decide +kernel))
  | "mask" =>
    let x ← numeral 1
    let y ← numeral 2
    `(absentMaskClause $h $x $y (by decide +kernel) (by decide +kernel) (by decide +kernel))
  | "realized" =>
    let m ← numeral 1
    `(realizedClause (recipe := $recipe) $h ⟨$m, by decide⟩ (by decide +kernel))
  | "witness-left" | "witness-right" =>
    let m ← numeral 1
    let i ← numeral 2
    if kind == "witness-left" then
      `(witnessLeft (recipe := $recipe) (C := $C) (D := $D) ⟨$m, by decide⟩ $i)
    else
      `(witnessRight (recipe := $recipe) (C := $C) (D := $D) ⟨$m, by decide⟩ $i)
  | _ =>
    let side ← Lean.ofExcept row[1]!.getNat?
    unless side ≤ 1 do throwError "Invalid unsigned six-axis side {side}"
    let s ← if side == 0 then `(false) else `(true)
    if kind == "root" then return ← `(rootClause $h $s)
    let w ← numeral 2
    let rules ← if side == 0 then `(Geometry.left_rules (Recipe.Inputs.geometry $h))
      else `(Geometry.right_rules (Recipe.Inputs.geometry $h))
    match kind with
    | "upper" | "lower" =>
      let axes ← Lean.ofExcept row[3]!.getArr?
      let axes ← axes.mapM fun axis => do
        let i := Syntax.mkNumLit (toString (← Lean.ofExcept axis.getNat?))
        `(($i : Axis))
      if kind == "upper" then
        `(ordinaryClause (recipe := $recipe) (C := $C) (D := $D)
          (Q9TightDistanceTwoCNF.upperClause (S := support $C $D)
            $s $rules $w [$axes,*] (by decide)) (by decide))
      else
        `(ordinaryClause (recipe := $recipe) (C := $C) (D := $D)
          (Q9TightDistanceTwoCNF.lowerClause (S := support $C $D)
            $s $rules $w [$axes,*] (by decide)) (by decide))
    | "no-square" =>
      let i ← numeral 3
      let j ← numeral 4
      `(ordinaryClause (recipe := $recipe) (C := $C) (D := $D)
        (Q9TightDistanceTwoCNF.squareClause (S := support $C $D)
          $s $rules $w $i $j (by decide)) (by decide))
    | "parity" =>
      let step ← numeral 3
      let signs ← numeral 4
      `(ordinaryClause (recipe := $recipe) (C := $C) (D := $D)
        (Q9TightDistanceTwoCNF.parityClause (S := support $C $D)
          $s $rules $w $step $signs) (by decide))
    | _ => throwError "Unknown unsigned six-axis input label {kind}"

-- As in Q9EightMaskReplay, the CNF leaf itself determines the expected proof type.
private def justify (proveRow : Json → TermElabM Term) (v formula : Expr) (labels : Array Json)
    (start stop : Nat) : TermElabM Expr := do
  let width := stop - start
  if width = 1 then
    unless formula.isAppOfArity ``Sat.Fmla.one 1 do
      throwError "Expected one CNF clause at row {start + 1}"
    let clause := formula.appArg!
    let term ← proveRow labels[start]!
    let expected := mkApp2 (Lean.mkConst ``Sat.Valuation.satisfies) v clause
    let proof ← withRef term <| withoutErrToSorry do
      try
        let proof ← elabTerm term none
        synthesizeSyntheticMVarsNoPostponing
        let proof ← instantiateMVars proof
        let actual ← inferType proof
        unless ← isDefEq actual expected do
          throwError "Expected {expected}, but obtained {actual}"
        pure proof
      catch error =>
        throwError "Unsigned CNF row {start + 1}: {error.toMessageData}"
    return mkApp3 (Lean.mkConst ``satisfies_one) v clause proof
  if hsplit : 1 < stop - start then
    unless formula.isAppOfArity ``Sat.Fmla.and 2 do
      throwError "Expected CNF conjunction at rows {start + 1} through {stop}"
    let a := formula.appFn!.appArg!
    let b := formula.appArg!
    let mid := start + (stop - start) / 2
    let ha ← justify proveRow v a labels start mid
    let hb ← justify proveRow v b labels mid stop
    return mkApp5 (Lean.mkConst ``satisfies_and) v a b ha hb
  else
    throwError "Expected CNF conjunction at rows {start + 1} through {stop}"
termination_by stop - start
decreasing_by all_goals omega

private def checkCertificate (fingerprint : Nat) (certificate : Term) :
    TermElabM String := do
  let .lit (.strVal contents) ← elabTermEnsuringType certificate (Lean.mkConst ``String)
    | throwError "Expected literal unsigned certificate data"
  unless certificateFingerprint contents == fingerprint.toUInt64 do
    throwErrorAt certificate "Unsigned six-axis certificate fingerprint mismatch"
  return contents

private def replayCertificate (name : Name) (contents : String) (inputs valueAt : Expr)
    (proveRow : Ident → Ident → Ident → Json → TermElabM Term) : TermElabM Unit := do
  let data ← Lean.ofExcept (Json.parse contents)
  let input ← Lean.ofExcept ((data.getObjVal? "cnf").bind Json.getStr?)
  let trace ← Lean.ofExcept ((data.getObjVal? "lrat").bind Json.getStr?)
  let labels ← Lean.ofExcept ((data.getObjVal? "labels").bind Json.getArr?)
  let Std.Internal.Parsec.ParseResult.success _ (_, rows) :=
    Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_, input.startPos⟩
    | throwError "Could not parse the unsigned CNF"
  unless !rows.isEmpty && rows.size == labels.size do
    throwError "Unsigned six-axis CNF has no rows or differs in length from its labels"
  let Std.Internal.Parsec.ParseResult.success _ steps :=
    Mathlib.Tactic.Sat.Parser.parseLRAT ⟨_, trace.startPos⟩
    | throwError "Could not parse the unsigned LRAT"
  let formula := Mathlib.Tactic.Sat.buildConj rows 0 rows.size
  let ctxName ← mkAuxDeclName (name ++ `ctx)
  addDecl <| .defnDecl {
    name := ctxName, levelParams := [], type := Lean.mkConst ``Sat.Fmla, value := formula
    hints := .regular 0, safety := .safe
  }
  let ctx := Lean.mkConst ctxName
  let supportType := mkApp (Lean.mkConst ``Finset [Level.zero]) (mkApp (Lean.mkConst ``Q) (mkNatLit 9))
  let inputName ← mkAuxDeclName (name ++ `inputSatisfied)
  withLocalDeclD `C supportType fun C =>
  withLocalDeclD `D supportType fun D =>
  withLocalDeclD `h (mkApp2 inputs C D) fun h => do
    let vars := #[C, D, h]
    let v := mkApp2 valueAt C D
    let follows ← justify (proveRow (mkIdent `C) (mkIdent `D) (mkIdent `h))
      v formula labels 0 labels.size
    let type ← mkForallFVars vars (mkApp2 (Lean.mkConst ``Sat.Valuation.satisfies_fmla) v ctx)
    let value ← mkLambdaFVars vars follows
    addDecl <| .thmDecl {name := inputName, levelParams := [], type, value}
    let replay ← Q9K33ReplayBatches.replay name ctx formula rows steps
    let type ← mkForallFVars vars (Lean.mkConst ``False)
    let value ← mkLambdaFVars vars (mkApp2 replay v (mkAppN (Lean.mkConst inputName) vars))
    addDecl <| .thmDecl {name, levelParams := [], type, value}

elab "replay_unsigned_six_axis " impossible:ident shape:ident fingerprint:num certificate:term :
    command => Lean.Elab.Command.liftTermElabM do
  let contents ← checkCertificate fingerprint.getNat certificate
  let name := (← getCurrNamespace) ++ impossible.getId
  let shapeExpr ← elabTermEnsuringType shape (Lean.mkConst ``Shape)
  let recipe := mkApp (Lean.mkConst ``Shape.recipe) shapeExpr
  let valueAt := mkApp (Lean.mkConst ``valuation) recipe
  let recipeSyntax ← `(Shape.recipe $shape)
  replayCertificate name contents (mkApp (Lean.mkConst ``Inputs) shapeExpr) valueAt
    (fun C D h row => do
      let core ← `(Inputs.toRecipeInputs $h)
      clauseProof recipeSyntax C D core row)

elab "replay_unsigned_recipe " impossible:ident recipe:ident fingerprint:num certificate:term :
    command => Lean.Elab.Command.liftTermElabM do
  let contents ← checkCertificate fingerprint.getNat certificate
  let name := (← getCurrNamespace) ++ impossible.getId
  let recipeExpr ← elabTermEnsuringType recipe (Lean.mkConst ``Recipe)
  let inputs := mkApp (Lean.mkConst ``Recipe.Inputs) recipeExpr
  let valueAt := mkApp (Lean.mkConst ``valuation) recipeExpr
  let recipeSyntax : Term := ⟨recipe.raw⟩
  replayCertificate name contents inputs valueAt
    (fun C D h => clauseProof recipeSyntax C D h)

set_option maxHeartbeats 0 in
replay_unsigned_six_axis wheelImpossible Shape.wheel 8674790127115018758
  (include_str "../../../../../../../Evidence/D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TenMaskSixAxis-wheel.result.json")

set_option maxHeartbeats 0 in
replay_unsigned_six_axis bipartitePlusImpossible Shape.bipartitePlus 8618536180954689640
  (include_str "../../../../../../../Evidence/D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TenMaskSixAxis-bipartite-plus.result.json")

/-- An exact wheel family at the chosen rim contact contradicts the unsigned constraints. -/
theorem wheel_family_impossible {C D : Finset (Q 9)} (h : Geometry C D)
    (hfamily : minimumDisplacements C D false 2 = Shape.wheel.family) : False := by
  apply wheelImpossible C D
  refine ⟨h, ?_, ?_⟩
  · simpa only [hfamily] using Finset.Subset.refl Shape.wheel.family
  · rw [hfamily]
    decide +kernel

/-- An exact bipartite-plus family at the chosen cross contact contradicts the unsigned constraints. -/
theorem bipartite_plus_family_impossible {C D : Finset (Q 9)} (h : Geometry C D)
    (hfamily : minimumDisplacements C D false 2 = Shape.bipartitePlus.family) : False := by
  apply bipartitePlusImpossible C D
  refine ⟨h, ?_, ?_⟩
  · simpa only [hfamily] using Finset.Subset.refl Shape.bipartitePlus.family
  · rw [hfamily]
    decide +kernel

#print axioms wheel_family_impossible
#print axioms bipartite_plus_family_impossible

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskSixAxisReplay
