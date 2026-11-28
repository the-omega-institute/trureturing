import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskSixAxisReplay

/-! Typed replay of opposing-star refutations for a four-axis clique
with three closed axes. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option Elab.async false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PendantK4StarsReplay

open Lean Meta Elab Term
open Finset
open BalancedCriticalSpectrum (Q flip)
open Q9IsotropicHuang (parity)
open Q9SharedContactCNF (Axis Word)
open Q9SharedContactNormalized (LocalRules)
open Q9TightDistanceTwoCNF (support valuation_occupied)
open Q9TightDistanceTwoNormalized (DirectStar baseAxes rightCenter exteriorShell_eq_zero_iff)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization (origin)
open private adjacentWord adjacentWord_spec from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactCNF
open private root cube_rootWord baseWord baseWord_shell baseRequired exteriorAxis missingAxis
  baseRow exteriorRow crossRow satisfies_signed_unit from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCNF
open private checkCertificate replayCertificate from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskSixAxisReplay

/-- Only mixed odd contact masks are forbidden. Contacts on two exterior axes
are permitted. The two stars have centres at words zero and fifteen. -/
structure Inputs (m : Axis) (C D : Finset (Q 9)) : Prop where
  left_star : DirectStar C origin 4
  right_star : DirectStar D rightCenter m
  left_rules : LocalRules C
  right_rules : LocalRules D
  separated : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y
  odd_mixed : ∀ x ∈ C, parity x = true → ∀ i : Axis, i.val < 3 → ∀ j ∉ baseAxes,
    flip (flip x i) j ∉ D

private noncomputable def starValuation (C D : Finset (Q 9)) : Sat.Valuation :=
  Q9TightDistanceTwoCNF.valuation (support C D)

private theorem baseClause {C D : Finset (Q 9)} {m : Axis} (h : Inputs m C D)
    (s : Bool) (v : Fin 16) : (starValuation C D).satisfies (baseRow s v) := by
  apply satisfies_signed_unit
  have hzero := (exteriorShell_eq_zero_iff _).mp (baseWord_shell v)
  have hbase : cubeBitVec 9 (baseWord v) ∈ support C D s ↔
      ∃ i ∈ baseAxes, flip (root s) i = cubeBitVec 9 (baseWord v) := by
    cases s
    · exact h.left_star.base _ hzero
    · apply h.right_star.base
      intro i hi
      simpa [rightCenter, hi] using hzero i hi
  rw [hbase]
  simp only [baseRequired, List.any_eq_true, List.mem_finRange, true_and, beq_iff_eq]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨⟨i.val, by omega⟩, Finset.mem_filter.mpr ⟨mem_univ _, i.isLt⟩, ?_⟩
    simpa only [adjacentWord_spec, cube_rootWord] using congrArg (cubeBitVec 9) hi
  · rintro ⟨i, hi, he⟩
    have hilt : i.val < 4 := (Finset.mem_filter.mp hi).2
    refine ⟨⟨i.val, hilt⟩, (cubeBitVec 9).injective ?_⟩
    simpa only [adjacentWord_spec, cube_rootWord] using he

private theorem exteriorClause {C D : Finset (Q 9)} {m : Axis} (h : Inputs m C D)
    (s : Bool) (i : Fin 5) : (starValuation C D).satisfies (exteriorRow m s i) := by
  have hstar : DirectStar (support C D s) (root s) (missingAxis m s) := by
    cases s
    · exact h.left_star
    · exact h.right_star
  apply satisfies_signed_unit
  rw [decide_eq_true_eq, adjacentWord_spec, cube_rootWord]
  exact (hstar.external_neighbor (exteriorAxis i)).symm

private theorem closeClause {C D : Finset (Q 9)} {m : Axis} (h : Inputs m C D)
    (u v : Word) (hd : hammingDist (cubeBitVec 9 u) (cubeBitVec 9 v) ≤ 1) :
    (starValuation C D).satisfies (crossRow u v) := by
  intro hu hv
  have hsep := h.separated _ ((valuation_occupied (support C D) false u).mp hu)
    _ ((valuation_occupied (support C D) true v).mp hv)
  omega

private theorem oddMixedClause {C D : Finset (Q 9)} {m : Axis} (h : Inputs m C D)
    (w : Word) (i j : Axis) (hp : parity (cubeBitVec 9 w) = true)
    (hi : i.val < 3) (hj : j ∉ baseAxes) :
    (starValuation C D).satisfies (crossRow w (adjacentWord (adjacentWord w i) j)) := by
  intro hu hv
  apply h.odd_mixed _ ((valuation_occupied (support C D) false w).mp hu) hp i hi j hj
  simpa [adjacentWord_spec, support] using
    (valuation_occupied (support C D) true (adjacentWord (adjacentWord w i) j)).mp hv

private def clauseProof (C D h : Ident) (spec : Json) : TermElabM Term := do
  let row ← Lean.ofExcept spec.getArr?
  let kind ← Lean.ofExcept row[0]!.getStr?
  let number (i : Nat) := Lean.ofExcept row[i]!.getNat?
  let numeral (n : Nat) := Syntax.mkNumLit (toString n)
  let lit (i : Nat) : TermElabM NumLit := return numeral (← number i)
  if kind == "close" then
    let u ← lit 1
    let v ← lit 2
    return ← `(closeClause $h $u $v (by decide +kernel))
  if kind == "odd-mixed" then
    let w ← lit 1
    let i ← lit 2
    let j ← lit 3
    return ← `(oddMixedClause $h $w $i $j (by decide +kernel) (by decide +kernel) (by decide +kernel))
  let side ← number 1
  unless side ≤ 1 do throwError "Invalid pendant-star side {side}"
  let s ← if side == 0 then `(false) else `(true)
  if kind == "base" then
    let v ← lit 2
    return ← `(baseClause $h $s $v)
  if kind == "center" then
    let axis ← number 2
    unless 4 ≤ axis ∧ axis < 9 do throwError "Invalid exterior axis {axis}"
    let i := numeral (axis - 4)
    return ← `(exteriorClause $h $s $i)
  let w ← lit 2
  let rules ← if side == 0 then `(Inputs.left_rules $h) else `(Inputs.right_rules $h)
  if kind == "upper" || kind == "lower" then
    let axes ← Lean.ofExcept row[3]!.getArr?
    let axes ← axes.mapM fun axis => do
      let i := numeral (← Lean.ofExcept axis.getNat?)
      `(($i : Axis))
    if kind == "upper" then
      return ← `(Q9TightDistanceTwoCNF.upperClause (S := support $C $D)
        $s $rules $w [$axes,*] (by decide))
    return ← `(Q9TightDistanceTwoCNF.lowerClause (S := support $C $D)
      $s $rules $w [$axes,*] (by decide))
  if kind == "square" then
    let i ← lit 3
    let j ← lit 4
    return ← `(Q9TightDistanceTwoCNF.squareClause (S := support $C $D)
      $s $rules $w $i $j (by decide))
  if kind == "parity" then
    let i := numeral ((← number 3) - 1)
    let signs ← lit 4
    return ← `(Q9TightDistanceTwoCNF.parityClause (S := support $C $D) $s $rules $w $i $signs)
  throwError "Unknown pendant-star input label {kind}"

elab "replay_pendant_k4_stars " impossible:ident missing:num fingerprint:num certificate:term :
    command => Lean.Elab.Command.liftTermElabM do
  let contents ← checkCertificate fingerprint.getNat certificate
  let name := (← getCurrNamespace) ++ impossible.getId
  let m ← elabTermEnsuringType missing (mkApp (mkConst ``Fin) (mkNatLit 9))
  synthesizeSyntheticMVarsNoPostponing
  let m ← instantiateMVars m
  replayCertificate name contents (mkApp (mkConst ``Inputs) m) (mkConst ``starValuation) clauseProof

set_option maxHeartbeats 0 in
replay_pendant_k4_stars pendantK4Stars4 4 17656598958759531573
  (include_str "../../../../../../../Evidence/D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9PendantK4Stars-4.result.json")

set_option maxHeartbeats 0 in
replay_pendant_k4_stars pendantK4Stars5 5 13791332759129151483
  (include_str "../../../../../../../Evidence/D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9PendantK4Stars-5.result.json")

/-- Normalized opposing stars with an four-axis clique with three closed axes cannot occur. -/
theorem pendant_k4_stars_excluded {C D : Finset (Q 9)} {m : Axis}
    (hm : m = 4 ∨ m = 5) (h : Inputs m C D) : False := by
  rcases hm with hm | hm
  · subst m
    exact pendantK4Stars4 C D h
  · subst m
    exact pendantK4Stars5 C D h

#print axioms pendant_k4_stars_excluded

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PendantK4StarsReplay
