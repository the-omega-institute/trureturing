import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CliqueSixAxisReplay
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9GenericRootAction
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactFibreSmallObstructions
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ExteriorCycleClauses

/-! Typed refutations using descending root actions, shared exterior rows, and weighted cycles. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option Elab.async false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesReplay

open Lean Elab Term
open Finset
open BalancedCriticalSpectrum (Q)
open BalancedCubeComponentBoundary (directions mem_directions)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open Q9FiveAxisMissingContact (rightRoot)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization (origin)
open Q9IsotropicHuang (parity)
open Q9SharedContactCNF (Axis Word Variable pos neg)
open Q9TenMaskSixAxisReplay (Recipe)
open Q9TightDistanceTwoCNF (support)
open Q9ExteriorTransport (GainConsistent)
open Q9ExteriorCycleClauses (Row cycleClause)
open Q9DenseSixRootNormalization (tripleAxes triple triple_card triple_injective)

open Q9GenericRootAction (Canonical Related pairKey)
open private adjacentWord adjacentWord_spec satisfies_negative_list satisfies_positive_list from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactCNF
open private axesOf rootWord rootWord_cube from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses
open private translateWord from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactFibreSmallObstructions
open private valuation occupied_value ordinaryClause clauseProof checkCertificate replayCertificate from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskSixAxisReplay

def recipe (masks : List Word) : Recipe where
  witnessCount := masks.length
  witnessMask := fun i => masks.get i
  family := insert (axesOf (3 : Word)) (masks.map axesOf).toFinset
  required := insert (axesOf (3 : Word)) (masks.map axesOf).toFinset

private def axisPerm (f g : Axis → Axis)
    (h₁ : ∀ i, g (f i) = i) (h₂ : ∀ i, f (g i) = i) : Equiv.Perm Axis where
  toFun := f
  invFun := g
  left_inv := h₁
  right_inv := h₂

structure Inputs (r : Recipe) (C D : Finset (Q 9)) : Prop where
  core : Recipe.Inputs r C D
  fibre : Q9ContactFibreSmallObstructions.Inputs r.family C D
  canonical : Canonical r.family C D
  gains : ∀ s, GainConsistent (support C D s)
  size : ∀ s, 60 ≤ (support C D s).card

private abbrev occ := Variable.occupied

private theorem translationClause {r : Recipe} {C D : Finset (Q 9)} (h : Inputs r C D)
    (s : Bool) (x : Word) (i j p q : Axis) (hx : parity (cubeBitVec 9 x) = false)
    (hij : i ≠ j) (hpq : p ≠ q)
    (hcap : ∀ a : Axis, ({i,a} : Finset Axis) ∈ r.family → a = j ∨ a = p ∨ a = q) :
    let y := adjacentWord (adjacentWord x i) j
    let u := adjacentWord (adjacentWord x p) q
    let v := adjacentWord (adjacentWord u i) j
    (valuation r C D).satisfies [neg (occ false x), neg (occ true y), pos (occ s (if s then v else u))] := by
  intro y u v hC hD hn
  have hshift := translateWord h.fibre x i j p q hx hij hpq hcap
    ((occupied_value r C D false x).mp hC) ((occupied_value r C D true y).mp hD)
  apply hn
  apply (occupied_value r C D s _).mpr
  cases s
  · simpa [support] using hshift.1
  · simpa [support] using hshift.2

private def rootNeighbor (s : Bool) (i : Axis) : Variable :=
  .occupied s (adjacentWord (rootWord s) i)

private theorem rootNeighbor_value (r : Recipe) (C D : Finset (Q 9)) (s : Bool) (i : Axis) :
    valuation r C D (rootNeighbor s i).index ↔
      i ∈ directions (support C D s) (if s then rightRoot else origin) := by
  rw [rootNeighbor, occupied_value, mem_directions, adjacentWord_spec, rootWord_cube]

private theorem rootPairClause {r : Recipe} {C D : Finset (Q 9)} (h : Inputs r C D)
    (a b c d : Fin 35) (hrel : Related r.family (a,b) (c,d))
    (hbad : pairKey (c,d) < pairKey (a,b)) :
    (valuation r C D).satisfies
      ((((tripleAxes a).map (rootNeighbor false)) ++
        ((tripleAxes b).map (rootNeighbor true))).map neg) := by
  apply satisfies_negative_list
  intro hall
  obtain ⟨⟨i,j⟩, hleft, hright, hmin⟩ := h.canonical
  have ha : triple a ⊆ triple i := by
    intro x hx
    have hm : rootNeighbor false x ∈ (tripleAxes a).map (rootNeighbor false) :=
      List.mem_map.mpr ⟨x, List.mem_toFinset.mp hx, rfl⟩
    rw [← hleft]
    exact (rootNeighbor_value r C D false x).mp (hall _ (List.mem_append_left _ hm))
  have hb : triple b ⊆ triple j := by
    intro x hx
    have hm : rootNeighbor true x ∈ (tripleAxes b).map (rootNeighbor true) :=
      List.mem_map.mpr ⟨x, List.mem_toFinset.mp hx, rfl⟩
    rw [← hright]
    exact (rootNeighbor_value r C D true x).mp (hall _ (List.mem_append_right _ hm))
  have hi := triple_injective (eq_of_subset_of_card_le ha (by rw [triple_card, triple_card]))
  have hj := triple_injective (eq_of_subset_of_card_le hb (by rw [triple_card, triple_card]))
  subst i
  subst j
  exact (not_lt_of_ge (hmin (c,d) hrel)) hbad

private def sizeRow (s : Bool) (inside : List Word) : Sat.Clause :=
  (((List.finRange 512).filter (fun i => decide (BitVec.ofFin i ∉ inside))).map
    (fun i => occ s (BitVec.ofFin i))).map pos

private theorem sizeClause {r : Recipe} {C D : Finset (Q 9)} (h : Inputs r C D)
    (s : Bool) (inside : List Word) (hinside : inside.toFinset.card < 60) :
    (valuation r C D).satisfies (sizeRow s inside) := by
  unfold sizeRow
  apply satisfies_positive_list
  intro hall
  have hsub : support C D s ⊆ inside.toFinset.image (cubeBitVec 9) := by
    intro x hx
    obtain ⟨w, rfl⟩ := (cubeBitVec 9).surjective x
    by_cases hw : w ∈ inside
    · exact Finset.mem_image.mpr ⟨w, List.mem_toFinset.mpr hw, rfl⟩
    · exfalso
      have hf : w.toFin ∈ (List.finRange 512).filter
          (fun i => decide (BitVec.ofFin i ∉ inside)) := by
        exact List.mem_filter.mpr
          ⟨List.mem_finRange _, by simpa only [decide_eq_true_eq, BitVec.ofFin_toFin] using hw⟩
      apply hall (occ s w) (List.mem_map.mpr ⟨w.toFin, hf, by rw [BitVec.ofFin_toFin]⟩)
      exact (occupied_value r C D s w).mpr hx
  have hbound := (Finset.card_le_card hsub).trans Finset.card_image_le
  have hsize := h.size s
  omega

private def numeral (n : Json) : TermElabM NumLit :=
  return Syntax.mkNumLit (toString (← Lean.ofExcept n.getNat?))

private def integer (n : Json) : TermElabM Term := do
  let k ← Lean.ofExcept n.getInt?
  let a := Syntax.mkNumLit (toString k.natAbs)
  if k < 0 then `(-$a) else `($a)

private def proveRow (r : Term) (C D h : Ident) (spec : Json) : TermElabM Term := do
  let row ← Lean.ofExcept spec.getArr?
  let tag ← Lean.ofExcept row[0]!.getStr?
  if tag == "root-descent" then
    let a ← numeral row[1]!
    let b ← numeral row[2]!
    let permData ← Lean.ofExcept row[3]!.getArr?
    let forward ← permData.mapM numeral
    let inverse ← (Array.range 9).mapM fun i => do
      let some j := (List.range 9).find? (fun j => permData[j]!.getNat?.toOption == some i)
        | throwError "Nonbijective axis action"
      return Syntax.mkNumLit (toString j)
    let swap ← Lean.ofExcept row[4]!.getNat?
    let t ← if swap == 0 then `(false) else `(true)
    let c ← numeral row[5]!
    let d ← numeral row[6]!
    let p ← `(axisPerm ![$forward,*] ![$inverse,*] (by decide +kernel) (by decide +kernel))
    return ← `(rootPairClause $h $a $b $c $d
      ⟨$p, $t, by unfold Q9GenericRootAction.Preserves; decide +kernel,
        by decide +kernel, by decide +kernel⟩ (by decide +kernel))
  if tag == "size" then
    let s ← if (← Lean.ofExcept row[1]!.getNat?) == 0 then `(false) else `(true)
    let inside ← (← Lean.ofExcept row[2]!.getArr?).mapM numeral
    return ← `(sizeClause $h $s [$inside,*] (by decide +kernel))
  if tag == "translate" || tag == "weighted-cycle" then
    let side ← Lean.ofExcept row[1]!.getNat?
    unless side ≤ 1 do throwError "Invalid contact side"
    let s ← if side == 0 then `(false) else `(true)
    if tag == "translate" then
      let x ← numeral row[2]!
      let i ← numeral row[3]!
      let j ← numeral row[4]!
      let p ← numeral row[5]!
      let q ← numeral row[6]!
      return ← `(translationClause $h $s $x $i $j $p $q
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    let root ← numeral row[2]!
    let steps ← Lean.ofExcept row[3]!.getArr?
    let some first := steps[0]? | throwError "Empty exterior cycle"
    let rowTerm (data : Json) : TermElabM Term := do
      let values ← Lean.ofExcept data.getArr?
      let z ← numeral values[0]!
      let a ← numeral values[1]!
      let b ← numeral values[2]!
      `((⟨$z, $a, $b⟩ : Row))
    let first ← rowTerm first
    let rest ← (steps.extract 1 steps.size).mapM rowTerm
    let gain ← Lean.ofExcept row[4]!.getArr?
    let some k := (List.range gain.size).find? (fun k => gain[k]!.getInt?.toOption.any (· ≠ 0))
      | throwError "Exterior cycle has zero gain"
    let ka := Syntax.mkNumLit (toString k)
    let gk ← integer gain[k]!
    let gain ← gain.mapM integer
    let lits ← (← Lean.ofExcept row[5]!.getArr?).mapM integer
    return ← `(ordinaryClause (recipe := $r) (C := $C) (D := $D)
      (cycleClause (support $C $D) $s (Inputs.gains $h $s) $first [$rest,*] ![$gain,*]
        (by intro he; exact (by decide +kernel : ($gk : ℤ) ≠ 0) (congrFun he ($ka : Fin 9)))
        (by
          change Q9ExteriorCycleClauses.follow ($root : Word) 0 ($first :: [$rest,*]) =
            some (($root : Word), ![$gain,*])
          decide +kernel)
        (([$lits,*] : List Int).map Sat.Literal.ofInt) (by decide +kernel)) (by decide +kernel))
  let core ← `(Inputs.core $h)
  clauseProof r C D core spec

elab "replay_fifteen_masks " impossible:ident masks:term " fingerprint " fingerprint:num " certificate " certificate:term :
    command => Lean.Elab.Command.liftTermElabM do
  let contents ← checkCertificate fingerprint.getNat certificate
  let name := (← getCurrNamespace) ++ impossible.getId
  let recipeTerm ← `(recipe $masks)
  let r ← elabTermEnsuringType recipeTerm (mkConst ``Recipe)
  synthesizeSyntheticMVarsNoPostponing
  let r ← instantiateMVars r
  replayCertificate name contents (mkApp (mkConst ``Inputs) r)
    (mkApp (mkConst ``valuation) r) (proveRow recipeTerm)

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesReplay
