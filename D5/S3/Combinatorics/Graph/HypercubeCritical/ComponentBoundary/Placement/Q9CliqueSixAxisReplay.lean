import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DenseSixRootNormalization
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ExteriorCycleClauses

/-! The clique contact family, with the actual sixty-vertex component lower bound. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option Elab.async false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CliqueSixAxisReplay

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
open Q9DenseSixRootNormalization (triple)
open private adjacentWord adjacentWord_spec satisfies_positive_list from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactCNF
open private axesOf rootWord rootWord_cube from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses
open private valuation occupied_value ordinaryClause clauseProof checkCertificate replayCertificate from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskSixAxisReplay

def mask : Fin 14 → Word := ![5, 6, 9, 10, 12, 17, 18, 20, 24, 33, 34, 36, 40, 48]

def family : Finset (Finset Axis) :=
  insert (axesOf (3 : Word)) ((List.finRange 14).map (axesOf ∘ mask)).toFinset

def recipe : Recipe where
  witnessMask := mask
  family := family
  required := family

structure BaseInputs (C D : Finset (Q 9)) : Prop where
  core : Recipe.Inputs recipe C D
  gains : ∀ s, GainConsistent (support C D s)
  size : ∀ s, 60 ≤ (support C D s).card

structure RootInputs (a b : Fin 35) (C D : Finset (Q 9)) : Prop extends BaseInputs C D where
  left : directions C origin = triple a
  right : directions D rightRoot = triple b

structure InactiveInputs (C D : Finset (Q 9)) : Prop extends BaseInputs C D where
  vertical : ∀ x ∈ C, ∀ y ∈ D, parity x = false → hammingDist x y = 2 →
    ∀ s : Bool, directions (support C D s) (if s then y else x) = {6, 7, 8}

private abbrev occ := Variable.occupied

private theorem root_neighbor {a b : Fin 35} {C D : Finset (Q 9)}
    (h : RootInputs a b C D) (s : Bool) (i : Axis) :
    valuation recipe C D (occ s (adjacentWord (rootWord s) i)).index ↔
      i ∈ triple (if s then b else a) := by
  rw [occupied_value, adjacentWord_spec, rootWord_cube, ← mem_directions]
  cases s
  · exact congrArg (fun S : Finset Axis => i ∈ S) h.left |> Iff.of_eq
  · exact congrArg (fun S : Finset Axis => i ∈ S) h.right |> Iff.of_eq

private theorem rootClausePositive {a b : Fin 35} {C D : Finset (Q 9)}
    (h : RootInputs a b C D) (s : Bool) (i : Axis) (hi : i ∈ triple (if s then b else a)) :
    (valuation recipe C D).satisfies [pos (occ s (adjacentWord (rootWord s) i))] := by
  intro hn
  exact hn ((root_neighbor h s i).mpr hi)

private theorem rootClauseNegative {a b : Fin 35} {C D : Finset (Q 9)}
    (h : RootInputs a b C D) (s : Bool) (i : Axis) (hi : i ∉ triple (if s then b else a)) :
    (valuation recipe C D).satisfies [neg (occ s (adjacentWord (rootWord s) i))] := by
  intro hn
  exact hi ((root_neighbor h s i).mp hn)

private def sizeRow (s : Bool) (inside : List Word) : Sat.Clause :=
  (((List.finRange 512).filter (fun i => decide (BitVec.ofFin i ∉ inside))).map
    (fun i => occ s (BitVec.ofFin i))).map pos

private theorem sizeClause {C D : Finset (Q 9)} (h : BaseInputs C D)
    (s : Bool) (inside : List Word) (hinside : inside.toFinset.card < 60) :
    (valuation recipe C D).satisfies (sizeRow s inside) := by
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
      exact (occupied_value recipe C D s w).mpr hx
  have hbound := (Finset.card_le_card hsub).trans Finset.card_image_le
  have hsize := h.size s
  omega

private theorem inactive_neighbor {C D : Finset (Q 9)} (h : InactiveInputs C D)
    (s : Bool) (x y : Word) (i : Axis)
    (hx : parity (cubeBitVec 9 x) = false) (hd : hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 2)
    (hC : cubeBitVec 9 x ∈ C) (hD : cubeBitVec 9 y ∈ D) :
    valuation recipe C D (occ s (adjacentWord (if s then y else x) i)).index ↔
      i ∈ ({6, 7, 8} : Finset Axis) := by
  rw [occupied_value, adjacentWord_spec, ← mem_directions]
  cases s
  · change i ∈ directions C (cubeBitVec 9 x) ↔ _
    have hv := h.vertical _ hC _ hD hx hd false
    change directions C (cubeBitVec 9 x) = _ at hv
    rw [hv]
  · change i ∈ directions D (cubeBitVec 9 y) ↔ _
    have hv := h.vertical _ hC _ hD hx hd true
    change directions D (cubeBitVec 9 y) = _ at hv
    rw [hv]

private theorem inactivePositive {C D : Finset (Q 9)} (h : InactiveInputs C D)
    (s : Bool) (x y : Word) (i : Axis)
    (hx : parity (cubeBitVec 9 x) = false) (hd : hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 2)
    (hi : i ∈ ({6, 7, 8} : Finset Axis)) :
    (valuation recipe C D).satisfies [neg (occ false x), neg (occ true y),
      pos (occ s (adjacentWord (if s then y else x) i))] := by
  intro hC hD hn
  exact hn ((inactive_neighbor h s x y i hx hd
    ((occupied_value recipe C D false x).mp hC)
    ((occupied_value recipe C D true y).mp hD)).mpr hi)

private theorem inactiveNegative {C D : Finset (Q 9)} (h : InactiveInputs C D)
    (s : Bool) (x y : Word) (i : Axis)
    (hx : parity (cubeBitVec 9 x) = false) (hd : hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 2)
    (hi : i ∉ ({6, 7, 8} : Finset Axis)) :
    (valuation recipe C D).satisfies [neg (occ false x), neg (occ true y),
      neg (occ s (adjacentWord (if s then y else x) i))] := by
  intro hC hD hn
  exact hi ((inactive_neighbor h s x y i hx hd
    ((occupied_value recipe C D false x).mp hC)
    ((occupied_value recipe C D true y).mp hD)).mp hn)

private def numeral (n : Json) : TermElabM NumLit := do
  return Syntax.mkNumLit (toString (← Lean.ofExcept n.getNat?))

private def integer (n : Json) : TermElabM Term := do
  let k ← Lean.ofExcept n.getInt?
  let a := Syntax.mkNumLit (toString k.natAbs)
  if k < 0 then `(-$a) else `($a)

private def proveBaseRow (C D : Ident) (h : Term) (spec : Json) : TermElabM Term := do
  let row ← Lean.ofExcept spec.getArr?
  let tag ← Lean.ofExcept row[0]!.getStr?
  let r ← `(recipe)
  if tag == "size" then
    let s ← if (← Lean.ofExcept row[1]!.getNat?) == 0 then `(false) else `(true)
    let inside ← (← Lean.ofExcept row[2]!.getArr?).mapM numeral
    return ← `(sizeClause $h $s [$inside,*] (by decide +kernel))
  if tag == "weighted-cycle" then
    let s ← if (← Lean.ofExcept row[1]!.getNat?) == 0 then `(false) else `(true)
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
      (cycleClause (support $C $D) $s (BaseInputs.gains $h $s) $first [$rest,*] ![$gain,*]
        (by intro he; exact (by decide +kernel : ($gk : ℤ) ≠ 0) (congrFun he ($ka : Fin 9)))
        (by
          change Q9ExteriorCycleClauses.follow ($root : Word) 0 ($first :: [$rest,*]) =
            some (($root : Word), ![$gain,*])
          decide +kernel)
        (([$lits,*] : List Int).map Sat.Literal.ofInt) (by decide +kernel)) (by decide +kernel))
  let core ← `(BaseInputs.core $h)
  clauseProof r C D core spec

private def proveRootRow (C D h : Ident) (spec : Json) : TermElabM Term := do
  let row ← Lean.ofExcept spec.getArr?
  let tag ← Lean.ofExcept row[0]!.getStr?
  if tag == "root-neighbor" then
    let s ← if (← Lean.ofExcept row[1]!.getNat?) == 0 then `(false) else `(true)
    let i ← numeral row[2]!
    if (← Lean.ofExcept row[3]!.getNat?) == 1 then
      return ← `(rootClausePositive $h $s $i (by decide +kernel))
    return ← `(rootClauseNegative $h $s $i (by decide +kernel))
  proveBaseRow C D (← `(RootInputs.toBaseInputs $h)) spec

private def proveInactiveRow (C D h : Ident) (spec : Json) : TermElabM Term := do
  let row ← Lean.ofExcept spec.getArr?
  let tag ← Lean.ofExcept row[0]!.getStr?
  if tag == "inactive-contact" then
    let s ← if (← Lean.ofExcept row[1]!.getNat?) == 0 then `(false) else `(true)
    let x ← numeral row[2]!
    let y ← numeral row[3]!
    let i ← numeral row[4]!
    if (← Lean.ofExcept row[5]!.getNat?) == 1 then
      return ← `(inactivePositive $h $s $x $y $i (by decide +kernel) (by decide +kernel) (by decide +kernel))
    return ← `(inactiveNegative $h $s $x $y $i (by decide +kernel) (by decide +kernel) (by decide +kernel))
  proveBaseRow C D (← `(InactiveInputs.toBaseInputs $h)) spec

elab "replay_clique_root " impossible:ident a:num b:num fingerprint:num certificate:term :
    command => Lean.Elab.Command.liftTermElabM do
  let contents ← checkCertificate fingerprint.getNat certificate
  let name := (← getCurrNamespace) ++ impossible.getId
  let aExpr ← elabTerm (← `(($a : Fin 35))) none
  let bExpr ← elabTerm (← `(($b : Fin 35))) none
  replayCertificate name contents (mkApp2 (mkConst ``RootInputs) aExpr bExpr)
    (mkApp (mkConst ``valuation) (mkConst ``recipe)) proveRootRow

elab "replay_clique_inactive " impossible:ident fingerprint:num certificate:term :
    command => Lean.Elab.Command.liftTermElabM do
  let contents ← checkCertificate fingerprint.getNat certificate
  let name := (← getCurrNamespace) ++ impossible.getId
  replayCertificate name contents (mkConst ``InactiveInputs)
    (mkApp (mkConst ``valuation) (mkConst ``recipe)) proveInactiveRow

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CliqueSixAxisReplay
