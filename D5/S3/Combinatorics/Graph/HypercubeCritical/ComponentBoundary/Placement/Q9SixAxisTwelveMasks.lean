import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ExteriorCycleClauses
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9NormalizedContactTranslations
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskSixAxisReplay

/-! The four rooted six-axis twelve-mask recipes and their typed clause semantics. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option Elab.async false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
namespace Q9SixAxisTwelveMasks

open Lean Meta Elab Term
open Finset
open BalancedCriticalSpectrum (Q IsBalanced IsSwitching flip flip_adj)
open BalancedCubeGirth (adjacent_exists_flip)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
  (normalize)
open Q9ExteriorCycleClauses (Row cycleClause)
open Q9ExteriorTransport (GainConsistent gain_eq_of_endpoints normalize_gain_consistent)
open Q9FiveAxisMissingContact (Geometry)
open Q9IsotropicHuang (parity flipSign)
open Q9MinimumDistanceOperator (minimumDisplacements RidgeContact)
open Q9NormalizedContactTranslations (normalized_contact_translation)
open Q9SharedContactCNF (Axis Word Variable pos neg)
open Q9TenMaskSixAxisReplay (Recipe)
open Q9TightDistanceTwoCNF (support)
open Q9WeightedSaturation (defect signedBiadjacency)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
open private adjacentWord adjacentWord_spec from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactCNF
open private axesOf xor_mask literalIndex from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses
open private differingAxes_right_inj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactComplement
open private diff_pair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar
open private normalize_flip_axis mem_normalize_map from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized
open private valuation ordinaryClause occupied_value clauseProof checkCertificate replayCertificate from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskSixAxisReplay

-- Template order: missing matching, triangle, four-vertex path, three-vertex path plus edge.
private def masks (kind : Fin 4) : Fin 11 → Word :=
  ![![5, 6, 10, 12, 17, 20, 24, 33, 34, 40, 48],
    ![5, 6, 9, 10, 12, 17, 20, 24, 33, 36, 40],
    ![5, 6, 10, 12, 18, 24, 33, 34, 36, 40, 48],
    ![5, 6, 9, 12, 17, 20, 24, 33, 34, 40, 48]] kind

private def requiredMasks (kind : Fin 4) : List Word :=
  ![[5, 6, 10, 12, 20, 24, 33, 34, 40, 48],
    [5, 9, 12, 17, 20, 24, 33, 36, 40],
    [10, 12, 18, 24, 40, 48],
    [5, 9, 12, 17, 24, 33, 40, 48]] kind

/-- The full mask family and the witness blocks retained in the corresponding refutation. -/
def recipe (kind : Fin 4) : Recipe where
  witnessMask := masks kind
  family := insert (axesOf (3 : Word)) ((List.finRange 11).map (axesOf ∘ masks kind)).toFinset
  required := ((requiredMasks kind).map axesOf).toFinset

private structure Translation where
  cubic : Axis
  partner : Axis
  first : Axis
  second : Axis

private def translations (kind : Fin 4) : List Translation :=
  ![[],
    [⟨1, 0, 2, 3⟩, ⟨4, 0, 2, 3⟩, ⟨5, 0, 2, 3⟩, ⟨1, 2, 0, 3⟩, ⟨1, 3, 0, 2⟩,
      ⟨4, 2, 0, 3⟩, ⟨5, 2, 0, 3⟩, ⟨4, 3, 0, 2⟩, ⟨5, 3, 0, 2⟩],
    [⟨0, 1, 2, 5⟩, ⟨0, 2, 1, 5⟩, ⟨0, 5, 1, 2⟩, ⟨4, 1, 3, 5⟩, ⟨4, 3, 1, 5⟩, ⟨4, 5, 1, 3⟩],
    [⟨1, 0, 2, 5⟩, ⟨1, 2, 0, 5⟩, ⟨1, 5, 0, 2⟩]] kind

private def axisBit (i : Axis) : Word := BitVec.ofNat 9 (2 ^ i.val)

private def Translation.mask (a : Translation) : Word := axisBit a.cubic ^^^ axisBit a.partner
private def Translation.shift (a : Translation) : Word := axisBit a.first ^^^ axisBit a.second

private def translationPairs (kind : Fin 4) : List (Word × Word) :=
  (translations kind).map fun a => (a.mask, a.shift)

private def Translation.Valid (a : Translation) (r : Recipe) : Prop :=
  a.cubic ≠ a.partner ∧ a.first ≠ a.second ∧
    axesOf a.mask = {a.cubic, a.partner} ∧ axesOf a.mask ∈ r.family ∧
    ∀ i, ({a.cubic, i} : Finset Axis) ∈ r.family →
      i = a.partner ∨ i = a.first ∨ i = a.second

private instance (a : Translation) (r : Recipe) : Decidable (a.Valid r) := by
  unfold Translation.Valid
  infer_instance

private theorem translations_ok (kind : Fin 4) :
    (translations kind).all (fun a => decide (a.Valid (recipe kind))) = true := by
  fin_cases kind <;> decide +kernel

private theorem required_subset (kind : Fin 4) : (recipe kind).required ⊆ (recipe kind).family := by
  fin_cases kind <;> decide +kernel

/-- The normalized geometric rows, cubic translations, and the extra triangle inputs. -/
structure Inputs (kind : Fin 4) (C D : Finset (Q 9)) : Prop where
  core : Recipe.Inputs (recipe kind) C D
  translates : ∀ x y shift : Word, parity (cubeBitVec 9 x) = false →
    (x ^^^ y, shift) ∈ translationPairs kind → cubeBitVec 9 x ∈ C → cubeBitVec 9 y ∈ D →
    cubeBitVec 9 (x ^^^ shift) ∈ C ∧ cubeBitVec 9 (y ^^^ shift) ∈ D
  gains : kind = 1 → ∀ s, GainConsistent (support C D s)
  balance : kind = 1 → IsBalanced C

private theorem bitFlipCube (word : Word) (i : Axis) :
    cubeBitVec 9 (word ^^^ axisBit i) = flip (cubeBitVec 9 word) i :=
  adjacentWord_spec word i

open Classical in
private theorem normalize_balanced {C : Finset (Q 9)}
    (σ : Equiv.Perm (Fin 9)) (o : Q 9) (hC : IsBalanced C) :
    IsBalanced (C.map (normalize σ o).toEmbedding) := by
  let e := normalize σ o
  have hflip (x : Q 9) (i : Fin 9) : e (flip x i) = flip (e x) (σ.symm i) := by
    simpa only [Equiv.apply_symm_apply] using normalize_flip_axis σ o x (σ.symm i)
  obtain ⟨θ, hθ, hedge, _⟩ := HuangCubeCovariance.exists_signed_covariance e σ.symm hflip
  obtain ⟨f, hf⟩ := hC
  refine ⟨fun x => θ (e.symm x) * f (e.symm x), ?_, ?_⟩
  · intro x hx
    obtain ⟨u, rfl⟩ := e.surjective x
    have hu : u ∈ C := (mem_normalize_map σ o C u).mp hx
    rcases hθ u with ht | ht <;> rcases hf.1 u hu with hs | hs <;>
      simp [Equiv.symm_apply_apply, ht, hs]
  · intro x hx y hy hxy
    obtain ⟨u, rfl⟩ := e.surjective x
    obtain ⟨j, hj⟩ := adjacent_exists_flip hxy
    have hj' : y = e (flip u (σ j)) := by
      simpa only [hflip, Equiv.symm_apply_apply] using hj
    rw [hj'] at hy ⊢
    have hu : u ∈ C := (mem_normalize_map σ o C u).mp hx
    have hv : flip u (σ j) ∈ C := (mem_normalize_map σ o C _).mp hy
    rw [hedge u (σ j), hf.2 u hu _ hv (flip_adj u (σ j))]
    simp only [Equiv.symm_apply_apply]
    ring

open Classical in
/-- A rooted normalization of the actual pair supplies every clause of its recipe. -/
theorem inputs_of_normalized_pair (kind : Fin 4) {C D : Finset (Q 9)}
    (σ : Equiv.Perm (Fin 9)) (o : Q 9)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0) :
    let e := normalize σ o
    let X := C.map e.toEmbedding
    let Y := D.map e.toEmbedding
    Geometry X Y → minimumDisplacements X Y false 2 = (recipe kind).family → Inputs kind X Y := by
  let e := normalize σ o
  let X := C.map e.toEmbedding
  let Y := D.map e.toEmbedding
  change Geometry X Y → minimumDisplacements X Y false 2 = (recipe kind).family → Inputs kind X Y
  intro geom hfamily
  refine ⟨⟨geom, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hfamily]
  · rw [hfamily]
    exact required_subset kind
  · intro x y shift hpar hmask hx hy
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hmask
    have hcode : x ^^^ y = a.mask := (congrArg Prod.fst he).symm
    have hshift : shift = a.shift := (congrArg Prod.snd he).symm
    obtain ⟨hij, hpq, hax, _, hpartners⟩ :=
      of_decide_eq_true ((List.all_eq_true.mp (translations_ok kind)) a ha)
    have hf : cubeBitVec 9 y = flip (flip (cubeBitVec 9 x) a.cubic) a.partner :=
      differingAxes_right_inj (by rw [diff_pair _ hij, xor_mask, hcode]; exact hax)
    have hcontact : RidgeContact X Y false [a.cubic] a.partner (cubeBitVec 9 x) :=
      ⟨by simpa using hij.symm, hx, hpar, hf ▸ hy⟩
    have htranslated :=
      normalized_contact_translation σ o hsep hrC hrD hcC hcD hbC hbD hdetC hdetD
        hpq (by rw [hfamily]; exact hpartners) hcontact
    have step_word (w : Word) : cubeBitVec 9 (w ^^^ shift) =
        flip (flip (cubeBitVec 9 w) a.first) a.second := by
      rw [hshift, Translation.shift, ← BitVec.xor_assoc, bitFlipCube, bitFlipCube]
    refine ⟨?_, ?_⟩
    · rw [step_word]
      exact htranslated.2.1
    · rw [step_word, hf]
      simpa only [List.foldl_cons, List.foldl_nil, BalancedCubeGirth.flip_comm] using htranslated.2.2.2
  · intro _ s
    cases s
    · exact normalize_gain_consistent (C := C) (by
        intro x y g h hx p q
        exact gain_eq_of_endpoints hrC hcC hbC hdetC hx p q) σ o
    · exact normalize_gain_consistent (C := D) (by
        intro x y g h hx p q
        exact gain_eq_of_endpoints hrD hcD hbD hdetD hx p q) σ o
  · exact fun _ => normalize_balanced σ o hbC

private abbrev occ := Variable.occupied

private theorem translateClause {kind : Fin 4} {C D : Finset (Q 9)} (h : Inputs kind C D)
    (s : Bool) (x y target : Word) (hx : parity (cubeBitVec 9 x) = false)
    (hm : (x ^^^ y, (if s then y else x) ^^^ target) ∈ translationPairs kind) :
    (valuation (recipe kind) C D).satisfies [neg (occ false x), neg (occ true y), pos (occ s target)] := by
  intro hC hD he
  have hpair := h.translates x y _ hx hm
    ((occupied_value (recipe kind) C D false x).mp hC)
    ((occupied_value (recipe kind) C D true y).mp hD)
  apply he
  apply (occupied_value (recipe kind) C D s target).mpr
  cases s
  · have hleft := hpair.1
    change cubeBitVec 9 (x ^^^ (x ^^^ target)) ∈ C at hleft
    simpa only [support, Bool.false_eq_true, ite_false, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using hleft
  · have hright := hpair.2
    change cubeBitVec 9 (y ^^^ (y ^^^ target)) ∈ D at hright
    simpa only [support, ite_true, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using hright

open Classical in
private noncomputable def switching (C : Finset (Q 9)) : Q 9 → ℝ :=
  if h : IsBalanced C then Classical.choose h else fun _ => 1

open Classical in
private theorem switching_spec {C : Finset (Q 9)} (h : IsBalanced C) :
    IsSwitching C (switching C) := by
  simpa only [switching, dif_pos h] using Classical.choose_spec h

-- The eight retained switching rows use only the left support's sign variables.
private noncomputable def signedValuation (r : Recipe) (C D : Finset (Q 9)) : Sat.Valuation :=
  fun n => if n < 9216 ∨ 9728 ≤ n then valuation r C D n
    else switching C (cubeBitVec 9 (BitVec.ofNat 9 (n - 9216))) = 1

private theorem keepUnsigned {r : Recipe} {C D : Finset (Q 9)} {c : Sat.Clause}
    (h : (valuation r C D).satisfies c)
    (hout : List.all c (fun l => decide (literalIndex l < 9216 ∨ 9728 ≤ literalIndex l)) = true) :
    (signedValuation r C D).satisfies c := by
  change List Sat.Literal at c
  induction c with
  | nil => exact h
  | cons l ls ih =>
    rw [List.all_cons, Bool.and_eq_true] at hout
    have he : signedValuation r C D (literalIndex l) = valuation r C D (literalIndex l) := by
      exact if_pos (of_decide_eq_true hout.1)
    intro hl
    refine ih (h ?_) hout.2
    cases l <;> simp only [literalIndex] at he <;>
      simpa only [Sat.Valuation.neg, ← he] using hl

private def signIndex (x : Word) : Nat := 9216 + x.toNat
private def signLiteral (p : Bool) (x : Word) : Sat.Literal :=
  if p then .pos (signIndex x) else .neg (signIndex x)

private theorem sign_value (r : Recipe) (C D : Finset (Q 9)) (x : Word) :
    signedValuation r C D (signIndex x) = (switching C (cubeBitVec 9 x) = 1) := by
  have hx : x.toNat < 2 ^ 9 := x.isLt
  have h : ¬ (signIndex x < 9216 ∨ 9728 ≤ signIndex x) := by
    dsimp [signIndex]
    omega
  rw [signedValuation, if_neg h]
  have hword : BitVec.ofNat 9 (signIndex x - 9216) = x := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, show signIndex x - 9216 = x.toNat by simp [signIndex],
      Nat.mod_eq_of_lt hx]
  rw [hword]

private theorem signed_occupied_left (r : Recipe) (C D : Finset (Q 9)) (x : Word) :
    signedValuation r C D (occ false x).index ↔ cubeBitVec 9 x ∈ C := by
  have hx : x.toNat < 2 ^ 9 := x.isLt
  have hi : (occ false x).index < 9216 := by
    simp [Variable.index, Q9SharedContactCNF.wordIndex]
    omega
  rw [signedValuation, if_pos (Or.inl hi)]
  simpa [support] using occupied_value r C D false x

private theorem edgeSignClause {C D : Finset (Q 9)} (h : Inputs 1 C D)
    (x : Word) (i : Axis) (p same : Bool)
    (hsign : flipSign i (cubeBitVec 9 x) = if same then 1 else -1) :
    (signedValuation (recipe 1) C D).satisfies
      [neg (occ false x), neg (occ false (adjacentWord x i)), signLiteral p x,
        signLiteral (p != same) (adjacentWord x i)] := by
  intro hx hy
  let u := cubeBitVec 9 x
  let v := cubeBitVec 9 (adjacentWord x i)
  have hv : v = flip u i := adjacentWord_spec x i
  have huC : u ∈ C := (signed_occupied_left _ _ _ x).mp hx
  have hvC : v ∈ C := (signed_occupied_left _ _ _ _).mp hy
  have hs := switching_spec (h.balance rfl)
  have hadj : (hypercube 9).Adj u v := by
    rw [hv]
    exact flip_adj u i
  have hedge := hs.2 u huC v hvC hadj
  have hmatrix : huangMatrix 9 u v = (flipSign i (cubeBitVec 9 x) : ℝ) := by
    rw [hv, ← flipSign_cast]
  have hcast : (flipSign i (cubeBitVec 9 x) : ℝ) =
      if same then 1 else -1 := by
    rw [hsign]
    cases same <;> norm_num
  have hmul : (if same then (1 : ℝ) else -1) =
      switching C u * switching C v :=
    hcast.symm.trans (hmatrix.symm.trans hedge)
  have hleft := hs.1 u huC
  have hright := hs.1 v hvC
  change switching C (cubeBitVec 9 x) = 1 ∨ switching C (cubeBitVec 9 x) = -1 at hleft
  change switching C (cubeBitVec 9 (adjacentWord x i)) = 1 ∨
    switching C (cubeBitVec 9 (adjacentWord x i)) = -1 at hright
  change (if same then (1 : ℝ) else -1) =
    switching C (cubeBitVec 9 x) * switching C (cubeBitVec 9 (adjacentWord x i)) at hmul
  cases same <;> cases p <;>
    rcases hleft with hleft | hleft <;> rcases hright with hright | hright <;>
    norm_num [hleft, hright] at hmul <;>
    norm_num [Sat.Valuation.satisfies, Sat.Valuation.neg, signLiteral, sign_value, hleft, hright]

deriving instance DecidableEq for Row, Sat.Literal

private def numeral (n : Json) : TermElabM NumLit :=
  return Syntax.mkNumLit (toString (← Lean.ofExcept n.getNat?))

private def integer (n : Json) : TermElabM Term := do
  let k ← Lean.ofExcept n.getInt?
  let a := Syntax.mkNumLit (toString k.natAbs)
  if k < 0 then `(-$a) else `($a)

private def boolTerm (b : Bool) : TermElabM Term :=
  if b then `(true) else `(false)

private def proveRow (kind : Nat) (r : Term) (C D h : Ident) (spec : Json) : TermElabM Term := do
  let row ← Lean.ofExcept spec.getArr?
  let tag ← Lean.ofExcept row[0]!.getStr?
  if tag == "edge-sign" then
    unless kind == 1 && row[1]!.getNat?.toOption == some 0 do
      throwError "Unexpected edge-sign row"
    let x ← Lean.ofExcept row[2]!.getNat?
    let i ← Lean.ofExcept row[3]!.getNat?
    let p ← Lean.ofExcept row[4]!.getNat?
    unless x < 512 && i < 9 && p < 2 do throwError "Invalid edge-sign row"
    let same ← boolTerm (!((List.range i).foldl (fun b k => b != x.testBit k) false))
    let w := Syntax.mkNumLit (toString x)
    let a := Syntax.mkNumLit (toString i)
    let polarity ← boolTerm (p == 1)
    return ← `(edgeSignClause $h $w $a $polarity $same (by decide +kernel))
  let ordinary ← match tag with
    | "translate" =>
      let side ← Lean.ofExcept row[1]!.getNat?
      unless side ≤ 1 do throwError "Invalid translation side"
      let s ← boolTerm (side == 1)
      let x ← numeral row[2]!
      let y ← numeral row[3]!
      let target ← numeral row[4]!
      `(translateClause $h $s $x $y $target (by decide +kernel) (by decide +kernel))
    | "weighted-cycle" =>
      unless kind == 1 do throwError "Unexpected weighted exterior cycle"
      let side ← Lean.ofExcept row[1]!.getNat?
      unless side ≤ 1 do throwError "Invalid exterior-cycle side"
      let s ← boolTerm (side == 1)
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
      let labels ← Lean.ofExcept row[5]!.getArr?
      let lits ← labels.mapM integer
      `(ordinaryClause (recipe := $r) (C := $C) (D := $D)
        (cycleClause (support $C $D) $s (Inputs.gains $h (by rfl) $s)
          $first [$rest,*]
          ![$gain,*]
          (by intro he; exact (by decide +kernel : ($gk : ℤ) ≠ 0) (congrFun he ($ka : Fin 9)))
          (by
            change Q9ExteriorCycleClauses.follow ($root : Word) 0 ($first :: [$rest,*]) =
              some (($root : Word), ![$gain,*])
            decide +kernel)
          (([$lits,*] : List Int).map Sat.Literal.ofInt) (by decide +kernel))
        (by decide +kernel))
    | _ =>
      let core ← `(Inputs.core $h)
      clauseProof r C D core spec
  if kind == 1 then
    `(keepUnsigned (r := $r) (C := $C) (D := $D) $ordinary (by decide +kernel))
  else
    return ordinary

/-- Replay a pinned six-axis certificate with its associated typed input recipe. -/
elab "replay_six_axis_twelve " impossible:ident index:num fingerprint:num certificate:term :
    command => Lean.Elab.Command.liftTermElabM do
  let kind := index.getNat
  unless kind < 4 do throwErrorAt index "Unknown six-axis template"
  let contents ← checkCertificate fingerprint.getNat certificate
  let name := (← getCurrNamespace) ++ impossible.getId
  let kindTerm ← `(($index : Fin 4))
  let r ← `(recipe $kindTerm)
  let k ← elabTerm kindTerm none
  let recipeExpr := mkApp (mkConst ``recipe) k
  let inputs := mkApp (mkConst ``Inputs) k
  let valueAt := mkApp (if kind == 1 then mkConst ``signedValuation else mkConst ``valuation) recipeExpr
  replayCertificate name contents inputs valueAt (proveRow kind r)

end Q9SixAxisTwelveMasks
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
