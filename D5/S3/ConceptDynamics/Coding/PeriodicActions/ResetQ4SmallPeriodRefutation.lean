/- GID: D5/S3/ConceptDynamics/Coding/PeriodicActions/ResetQ4SmallPeriodRefutation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PeriodicActions/ResetQ4SmallPeriodRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.GroupTheory.QuotientGroup.Basic]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/ConceptDynamics/Coding/PeriodicActions/ResetQ4SmallPeriodRefutation.claim; result=D5/S3/ConceptDynamics/Coding/PeriodicActions/ResetQ4SmallPeriodRefutation.result; claim=D5/S3/ConceptDynamics/Coding/PeriodicActions/ResetQ4SmallPeriodRefutation.claim
   digest: Whole actions on periods one through five do not determine the quartic native cubic character. -/
import D5.S3.ConceptDynamics.Coding.ResetAlternatingHistories
import D5.S3.ConceptDynamics.Coding.TwistedPeriodicHistories
import D5.S3.ConceptDynamics.Coding.ResetStandardBeamGeometry
import D5.S3.ConceptDynamics.Coding.ResetQ4OriginalLocalizedCubes
import D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option Elab.async false

universe u

noncomputable section

namespace D5.S3.ConceptDynamics.Coding.ResetAlternatingSquareExecution

open ResetNumberedHistories
open ResetNumberedHistories.Alternating
open EssentialWordRealization
open FiniteWindowTableCriterion
open FixedBlockRigidity
open CountedGroupOverlap (Edge)

/-- Construct the existing, uniquely specified square on a compatible input.
This is a dependent pair, so the executable output carries its original
Square proof. There is no selected finite-action table in the definition. -/
private def leftSquareLegal {q : ℕ} (hq : 0 < q) (x : B q) (s : R q)
    (hc : targetB hq x = sourceR s) :
    {out : R q × B q // Square hq out.1 x out.2 s} := by
  cases x with
  | f i h =>
      cases s with
      | d j g =>
          have hv := congrArg Prod.fst hc
          have hg := congrArg Prod.snd hc
          dsimp only [targetB, sourceR] at hv hg
          cases hv
          cases hg
          by_cases he : i.val + 1 < q ∧ i.val % 2 = 0
          · exact ⟨(.a i h he.1, .f (next i he.1) h), .fdSwap i h he.1 he.2⟩
          · exact ⟨(.d i h, .f i h), .fdFix i h he⟩
      | f j g =>
          have hv := congrArg Prod.fst hc
          have hg := congrArg Prod.snd hc
          dsimp only [targetB, sourceR] at hv hg
          cases hv
          cases hg
          exact ⟨(.f i h, .f (zero hq) (flipSign h)), .ff i h⟩
      | a j g hj =>
          have hv := congrArg Prod.fst hc
          have hg := congrArg Prod.snd hc
          dsimp only [targetB, sourceR] at hv hg
          cases hv
          cases hg
          exact ⟨(.f i h, .a (zero hq) (flipSign h) hj),
            .fa i h (by simpa only [zero, Fin.val_mk, Nat.zero_add] using hj)⟩
  | a i h hi =>
      cases s with
      | d j g =>
          have hv := congrArg Prod.fst hc
          have hg := congrArg Prod.snd hc
          dsimp only [targetB, sourceR] at hv hg
          cases hv
          cases hg
          exact ⟨(.d i h, .a i h hi), .ad i h hi⟩
      | f j g =>
          have hv := congrArg Prod.fst hc
          have hg := congrArg Prod.snd hc
          dsimp only [targetB, sourceR] at hv hg
          cases hv
          cases hg
          by_cases he : i.val % 2 = 0
          · exact ⟨(.d i h, .f i h), .afSwap i h hi he⟩
          · exact ⟨(.a i h hi, .f (next i hi) h), .afFix i h hi he⟩
      | a j g hj =>
          have hv := congrArg Prod.fst hc
          have hg := congrArg Prod.snd hc
          dsimp only [targetB, sourceR] at hv hg
          cases hv
          cases hg
          exact ⟨(.a i h hi, .a (next i hi) h hj),
            .aa i h hi (by simpa only [next, Fin.val_mk, Nat.add_assoc] using hj)⟩

/-- Total executable realization, including the original incompatible-input
fallback. Keeping that branch makes the equality below unconditional. -/
private def leftSquareExec {q : ℕ} (hq : 0 < q) (x : B q) (s : R q) : R q × B q :=
  if hc : targetB hq x = sourceR s then (leftSquareLegal hq x s hc).val
  else (identityR (sourceB x), x)

/-- Uniqueness in the original relation identifies the executable square
with the original choice. No assumption asserts equality of table outputs. -/
private theorem leftSquareExec_eq {q : ℕ} (hq : 0 < q) (x : B q) (s : R q) :
    leftSquareExec hq x s = leftSquare hq x s := by
  by_cases hc : targetB hq x = sourceR s
  · rw [leftSquareExec, dif_pos hc]
    have hu := square_left_unique (leftSquareLegal hq x s hc).property
      (leftSquare_spec hq x s hc) rfl rfl
    exact Prod.ext hu.1 hu.2
  · simp only [leftSquareExec, leftSquare, dif_neg hc]

/-- Right-to-left execution on an arbitrary finite list of the ACTUAL typed
numbered reset edges. No path or evenness premise is omitted. -/
private def sweepLeftExec {q : ℕ} (hq : 0 < q) : List (B q) → R q → R q × List (B q)
  | [], s => (s, [])
  | x :: xs, s =>
      let tail := sweepLeftExec hq xs s
      let sq := leftSquareExec hq x tail.1
      (sq.1, sq.2 :: tail.2)

private theorem sweepLeftExec_eq {q : ℕ} (hq : 0 < q) (xs : List (B q)) (s : R q) :
    sweepLeftExec hq xs s = sweepLeft hq xs s := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [sweepLeftExec, sweepLeft, ih, leftSquareExec_eq]

/-- Executable local output on the original q+1-edge legal window.
The edge number and the absolute group coordinate are retained by
originalEdge; no sign word, necklace or orbit quotient is introduced. -/
private def forwardExec {q : ℕ} (hq : 0 < q)
    (w : LegalWord (expandedGraph (resetMatrix q)) (0 + q + 1)) :
    Edge (resetMatrix q) × Sign :=
  originalEdge hq (pick hq
    (sweepLeftExec hq (List.ofFn (fun j : Fin (q + 1) =>
        typedEdge (w.edge ⟨j.val, by omega⟩)))
      (identityR ((expandedGraph (resetMatrix q)).target (w.edge ⟨q, by omega⟩)))).2 0)

/-- Exact identification with the original forward table. The proof unfolds
the public table projection only far enough to expose its existing sweep;
it does not edit or reproduce the private forwardTable definition. -/
private theorem forwardExec_eq {q : ℕ} (hq : 0 < q)
    (w : LegalWord (expandedGraph (resetMatrix q)) (0 + q + 1)) :
    forwardExec hq w = (resetAlternatingTablePair q hq).f w := by
  change originalEdge hq (pick hq
    (sweepLeftExec hq (List.ofFn (fun j : Fin (q + 1) =>
        typedEdge (w.edge ⟨j.val, by omega⟩)))
      (identityR ((expandedGraph (resetMatrix q)).target (w.edge ⟨q, by omega⟩)))).2 0) =
    originalEdge hq (pick hq
    (sweepLeft hq (List.ofFn (fun j : Fin (q + 1) =>
        typedEdge (w.edge ⟨j.val, by omega⟩)))
      (identityR ((expandedGraph (resetMatrix q)).target (w.edge ⟨q, by omega⟩)))).2 0)
  rw [sweepLeftExec_eq]

end D5.S3.ConceptDynamics.Coding.ResetAlternatingSquareExecution

-- Resolve the existing private suppliers uniquely; no proof body is duplicated.
run_cmd do
  let mut env ← Lean.getEnv
  for userName in #[
    `D5.S3.ConceptDynamics.Coding.ResetQ4OriginalLocalizedCubes.originalScalar,
    `D5.S3.ConceptDynamics.Coding.ResetQ4OriginalLocalizedCubes.originalScalar_action,
    `D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.Common4,
    `D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.Plus4,
    `D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.cK,
    `D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.cK_a,
    `D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.cK_b,
    `D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.aUnit,
    `D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.bUnit,
    `D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.beta_val,
    `D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.Bminus_val,
    `D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.alpha_val,
    `D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.plusCharacterK,
    `D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes.plus_alpha_residue] do
    let candidates := env.constants.toList.filter fun (name, _) =>
      Lean.isPrivateName name && Lean.privateToUserName name == userName
    match candidates with
    | [(name, _)] => env := Lean.addAlias env userName name
    | _ => throwError "Expected one original private declaration for {userName}"
  Lean.setEnv env

open D5.S3.ConceptDynamics.Coding
open EssentialWordRealization
open FiniteWindowTableCriterion
open FixedBlockRigidity
open ResetNumberedHistories
open ResetNumberedHistories.Alternating
open ResetStandardBeamGeometry
open StandardBeamHomeomorphisms
open TwistedPeriodicHistories
open ResetAlternatingSquareExecution
open ResetFullStandardBeamRepresentation
open ResetNativeIntegerChart
open ResetNativeIntegralDefect
open ResetNativeUnitNormalForm
open ResetHistoryKernel
open ResetSignIntegerCyclic
open ResetIntegralGluing
open ResetQ4OriginalLocalizedCubes (originalScalar originalScalar_action)
open ResetQ4UnitCubes (cK cK_a cK_b aUnit bUnit beta Bminus beta_val Bminus_val)
open CountedGroupOverlap (Edge)

local instance nativeIntModule (q : ℕ) : Module ℤ (Native q) :=
  AddCommGroup.toIntModule _

namespace D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes
private def residueQuotientCharacter (a : Common4ˣ) (ha : a = aUnit) :
    Additive (Common4ˣ ⧸ Subgroup.zpowers a) →+ ZMod 3 := by
  exact (QuotientGroup.lift (Subgroup.zpowers a) cK.toMultiplicativeRight
    (by
      apply Subgroup.zpowers_le.mpr
      change cK (Additive.ofMul a) = 0
      rw [ha]
      exact cK_a)).toAdditiveLeft

private theorem residueQuotientCharacter_plus (a : Common4ˣ) (ha : a = aUnit) (u : Plus4ˣ) :
    residueQuotientCharacter a ha (Additive.ofMul
      (QuotientGroup.mk' (Subgroup.zpowers a)
        (Units.map (rplus 4).toMonoidHom u))) =
      plusCharacterK (Additive.ofMul u) := by
  rfl

end D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes

namespace D5.S3.ConceptDynamics.Coding.ResetQ4OriginalLocalizedCubes
open ResetQ4UnitCubes
open Polynomial
private theorem original_time_residue :
    Units.map (rplus 4).toMonoidHom
      (Units.map (plus 4).toMonoidHom
        (scalarUnit 4 (by decide)
          (rho 4 (by decide) (StandardBeamHomeomorphisms.unitShift (ResetGraph 4)))
          (rho_time 4 (by decide)
            (StandardBeamHomeomorphisms.unitShift (ResetGraph 4))))) = aUnit := by
  let t := StandardBeamHomeomorphisms.unitShift (ResetGraph 4)
  have hs : (originalScalar t : QF 4) = fp 4 X := by
    apply (nativeIntEquiv 4 (by decide)).injective
    have he := originalScalar_action t 1
    rw [mul_one] at he
    have ht := LinearMap.congr_fun (rho_unitShift 4 (by decide))
      (nativeIntEquiv 4 (by decide) 1)
    change rho 4 (by decide) t (nativeIntEquiv 4 (by decide) 1) =
      resetTheta 4 (nativeIntEquiv 4 (by decide) 1) at ht
    rw [ht, ← (native_presentation 4 (by decide)).2.1, mul_one] at he
    exact he
  have hp : Units.map (plus 4).toMonoidHom (originalScalar t) = alpha := by
    apply Units.ext
    change plus 4 (originalScalar t : QF 4) = plus 4 (fp 4 X)
    exact congrArg (plus 4) hs
  change Units.map (rplus 4).toMonoidHom
    (Units.map (plus 4).toMonoidHom (originalScalar t)) = aUnit
  rw [hp, plus_alpha_residue]

end D5.S3.ConceptDynamics.Coding.ResetQ4OriginalLocalizedCubes

namespace D5.S3.ConceptDynamics.Coding.ResetQ4SmallPeriodRefutation

private abbrev C := resetMatrix 4

private abbrev G := ResetGraph 4
private theorem even4 : Even 4 := ⟨2, rfl⟩

private def J : ResetFullAut 4 := evenAut 4 (by decide) even4 * unitShift G

-- Enumerate ACTUAL numbered base edges: four F_i and three A_i.
-- The zero edge number is supplied by originalEdge, not assumed for e.

private def baseAt (k : Fin 7) : Edge C :=
  if hk : k.val < 4 then
    (originalEdge (by decide : 0 < 4) (.f ⟨k.val, hk⟩ 1)).1
  else
    (originalEdge (by decide : 0 < 4)
      (.a ⟨k.val - 4, by omega⟩ 1 (by dsimp; omega))).1

private theorem baseAt_surjective : Function.Surjective baseAt := by
  intro e
  have he := congrArg Prod.fst
    (original_typed (by decide : 0 < 4) (e, (1 : Sign)))
  cases ht : typedEdge (e, (1 : Sign)) with
  | f i s =>
      refine ⟨⟨i.val, by omega⟩, ?_⟩
      have hi : i.val < 4 := i.isLt
      have hbase : baseAt ⟨i.val, by omega⟩ =
          (originalEdge (by decide : 0 < 4) (.f i s)).1 := by
        simp [baseAt, hi, originalEdge]
      exact hbase.trans (by simpa only [ht] using he)
  | a i s hi =>
      refine ⟨⟨4 + i.val, by omega⟩, ?_⟩
      have hk : ¬ 4 + i.val < 4 := by omega
      have hbase : baseAt ⟨4 + i.val, by omega⟩ =
          (originalEdge (by decide : 0 < 4) (.a i s hi)).1 := by
        dsimp only [baseAt]
        rw [dif_neg hk]
        apply numbered_ext
        · apply Fin.ext
          simp [originalEdge]
        · apply Fin.ext
          simp [originalEdge, next]
        · rfl
        · rfl
      exact hbase.trans (by simpa only [ht] using he)
-- ofSurjective enumerates by finite image, without invFun or choice.
-- This local instance replaces the noncomputable default edge enumeration.
local instance baseEdges : Fintype (Edge C) := Fintype.ofSurjective baseAt baseAt_surjective

private def f : LegalWord G 5 → Edge C × Sign := forwardExec (by decide : 0 < 4)

private theorem f_eq : f = (resetAlternatingTablePair 4 (by decide)).f := by
  funext w
  exact forwardExec_eq (by decide : 0 < 4) w

private theorem hf : Seam G G f := by
  rw [f_eq]
  exact (reset_alternating_tables_local 4 (by decide) even4).seamG
-- J=H*T: shift first, then the literal FORWARD table.

private def F : ResetHistory 4 → ResetHistory 4 :=
  fun x => applyTable G G (a := 0) (b := 4) f hf (shift G x)

private theorem F_commutes : Function.Commute F (shift G) := by
  intro x
  exact applyTable_shift G G (a := 0) (b := 4) f hf (shift G x)
private theorem fullAut_mul_apply (g h : ResetFullAut 4) (x : ResetHistory 4) :
    (g*h).val x = g.val (h.val x) := rfl

private theorem J_definition :
    J = evenAut 4 (by decide) even4 * unitShift G := rfl

private theorem evenAut_value :
    (evenAut 4 (by decide) even4).val =
      resetAlternatingWholeRayHomeomorph 4 (by decide) even4 := rfl

private theorem square_homeomorph_apply
    (S : SameCutWholeRayBridge.Squares G G (R := Edge (1 + C) × Sign))
    (K : SameCutWholeRayBridge.FiniteForgetting S 4) (x : ResetHistory 4) :
    S.historyHomeomorph K x = S.H K x := rfl

private theorem evenAut_apply (x : ResetHistory 4) :
    (evenAut 4 (by decide) even4).val x =
      (resetNumberedData 4 (by decide)).squares.H
        (resetFiniteForgetting 4 (by decide) even4) x := by
  exact (congrArg (fun h : ResetHistory 4 ≃ₜ ResetHistory 4 => h x)
    evenAut_value).trans
      (square_homeomorph_apply (resetNumberedData 4 (by decide)).squares
        (resetFiniteForgetting 4 (by decide) even4) x)

private theorem shift_apply (x : ResetHistory 4) : (unitShift G).val x = shift G x := rfl

set_option maxHeartbeats 2000000 in
-- Check the original homeomorphism projections without expanding its global lift.
private theorem actual_J (x : ResetHistory 4) : J.val x = F x := by
  calc
    J.val x = (evenAut 4 (by decide) even4).val ((unitShift G).val x) :=
      (congrArg (fun h : ResetFullAut 4 => h.val x) J_definition).trans
        (fullAut_mul_apply _ _ x)
    _ = (resetNumberedData 4 (by decide)).squares.H
        (resetFiniteForgetting 4 (by decide) even4) ((unitShift G).val x) :=
      evenAut_apply ((unitShift G).val x)
    _ = (resetNumberedData 4 (by decide)).squares.H
        (resetFiniteForgetting 4 (by decide) even4) (shift G x) :=
      congrArg ((resetNumberedData 4 (by decide)).squares.H
        (resetFiniteForgetting 4 (by decide) even4)) (shift_apply x)
    _ = applyTable G G (a := 0) (b := 4) (resetAlternatingTablePair 4 (by decide)).f
        (reset_alternating_tables_local 4 (by decide) even4).seamG (shift G x) :=
      reset_generic_H_eq_applyTable 4 (by decide) even4 (shift G x)
    _ = F x := by
      apply Subtype.ext
      funext k
      change (resetAlternatingTablePair 4 (by decide)).f
          (historyWindow G (shift G x) (k - (0 : ℤ)) 5) =
        f (historyWindow G (shift G x) (k - (0 : ℤ)) 5)
      exact (congrFun f_eq (historyWindow G (shift G x) (k - (0 : ℤ)) 5)).symm

private theorem group_one (x : ResetHistory 4) : groupHistory C 1 x = x := by
  apply Subtype.ext
  funext t
  apply Prod.ext
  · rfl
  · exact one_mul _

-- Restrict F to the actual periodic histories using its original unit-time
-- commutation. This proof works for every d, even d=0; only the subsequent
-- finite-word equivalence requires d>0.

private def periodicF (d : ℕ) (x : TwistedPeriod C 1 d) : TwistedPeriod C 1 d :=
  ⟨F x.val, by
    calc
      (shift G)^[d] (F x.val) = F ((shift G)^[d] x.val) :=
        (F_commutes.iterate_right d x.val).symm
      _ = F (groupHistory C 1 x.val) := congrArg F x.property
      _ = F x.val := congrArg F (group_one x.val)
      _ = groupHistory C 1 (F x.val) := (group_one (F x.val)).symm⟩

private def e (d : ℕ) (hd : 0 < d) := twistedPeriodEquiv C 1 hd

private def step (d : ℕ) (hd : 0 < d) : SeamWords C 1 hd → SeamWords C 1 hd :=
  fun p => e d hd (periodicF d ((e d hd).symm p))

private theorem amplify (d : ℕ) (hd : 0 < d) (k m : ℕ)
    (h : ∀ p : SeamWords C 1 hd, (step d hd)^[k] p = p) :
    ∀ p : SeamWords C 1 hd, (step d hd)^[k * m] p = p := by
  intro p
  rw [Function.iterate_mul]
  exact Function.iterate_fixed (h p) m

private def seamKey (d : ℕ) (hd : 0 < d) (p : SeamWords C 1 hd) :
    Fin 4 × Sign × (Fin d → Edge C) :=
  (p.1, p.2.1, p.2.2.val.edge)

private theorem seamKey_injective (d : ℕ) (hd : 0 < d) :
    Function.Injective (seamKey d hd) := by
  rintro ⟨i,z,⟨w,hw⟩⟩ ⟨j,t,⟨v,hv⟩⟩ h
  simp only [seamKey, Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,he⟩
  have hword : w = v := legalWord_ext he
  subst v
  rfl

local instance seamDecidableEq (d : ℕ) (hd : 0 < d) :
    DecidableEq (SeamWords C 1 hd) :=
  Function.Injective.decidableEq (seamKey_injective d hd)

private theorem certificate1 :
    ∀ p : SeamWords C 1 (by decide : 0 < 1),
      (step 1 (by decide))^[1] p = p := by
  decide

private theorem certificate2 :
    ∀ p : SeamWords C 1 (by decide : 0 < 2),
      (step 2 (by decide))^[1] p = p := by
  decide

private theorem certificate3 :
    ∀ p : SeamWords C 1 (by decide : 0 < 3),
      (step 3 (by decide))^[2] p = p := by
  decide

private def normalizedEdges {d : ℕ} (w : LegalWord (baseGraph C) d) :
    Fin d → Edge C := fun j =>
  (List.ofFn w.edge)[j.val]'(by simpa using j.isLt)

private theorem normalizedEdges_eq {d : ℕ} (w : LegalWord (baseGraph C) d) :
    normalizedEdges w = w.edge := by
  funext j
  simp [normalizedEdges]

private def normalizeWord {d : ℕ} (w : LegalWord (baseGraph C) d) :
    LegalWord (baseGraph C) d where
  edge := normalizedEdges w
  legal := by
    rw [normalizedEdges_eq]
    exact w.legal

private theorem normalizeWord_eq {d : ℕ} (w : LegalWord (baseGraph C) d) :
    normalizeWord w = w := by
  apply legalWord_ext
  exact normalizedEdges_eq w

private def normalizeSeam (d : ℕ) (hd : 0 < d) (p : SeamWords C 1 hd) :
    SeamWords C 1 hd :=
  ⟨p.1,p.2.1,⟨normalizeWord p.2.2.val,by
    rw [normalizeWord_eq]
    exact p.2.2.property⟩⟩

private theorem normalizeSeam_eq (d : ℕ) (hd : 0 < d) (p : SeamWords C 1 hd) :
    normalizeSeam d hd p = p := by
  rcases p with ⟨i,z,⟨w,hw⟩⟩
  simp only [normalizeSeam, normalizeWord_eq]

private def materializedStep (d : ℕ) (hd : 0 < d) :
    SeamWords C 1 hd → SeamWords C 1 hd :=
  fun p => normalizeSeam d hd (step d hd p)

private theorem materializedStep_eq (d : ℕ) (hd : 0 < d) :
    materializedStep d hd = step d hd := by
  funext p
  exact normalizeSeam_eq d hd (step d hd p)

set_option maxHeartbeats 20000000 in
-- Exhaustive kernel reduction on the complete materialized finite fiber.
private theorem certificate4 :
    ∀ p : SeamWords C 1 (by decide : 0 < 4),
      (step 4 (by decide))^[4] p = p := by
  rw [← materializedStep_eq 4 (by decide)]
  rintro ⟨i,z,w⟩
  fin_cases i <;> cases z <;> revert w <;> decide +kernel

set_option maxHeartbeats 20000000 in
-- Exhaustive kernel reduction on the complete materialized finite fiber.
private theorem certificate5 :
    ∀ p : SeamWords C 1 (by decide : 0 < 5),
      (step 5 (by decide))^[10] p = p := by
  rw [← materializedStep_eq 5 (by decide)]
  rintro ⟨i,z,w⟩
  fin_cases i <;> cases z <;> revert w <;> decide +kernel

-- Every input is an actual finite numbered word with its actual absolute
-- sign anchor. SeamWords includes all legal words and the exact loop seam.
-- Repeated extension/restriction uses the existing proven equivalence.
-- Check exponents 1,1,2,4,10 directly on the WHOLE period-d fibres,
-- then use iterate_fixed to reach 20. These are not claims about the
-- least-period orbit counts. No claim of minimal order is needed.

private theorem certificate : ∀ d : ℕ, ∀ hd : 0 < d, d ≤ 5 →
    ∀ p : SeamWords C 1 hd, (step d hd)^[20] p = p := by
  intro d hd hle
  interval_cases d
  · exact amplify 1 hd 1 20 certificate1
  · exact amplify 2 hd 1 20 certificate2
  · exact amplify 3 hd 2 10 certificate3
  · exact amplify 4 hd 4 5 certificate4
  · exact amplify 5 hd 10 2 certificate5

private theorem finite_semiconj (d : ℕ) (hd : 0 < d) :
    Function.Semiconj (fun p : SeamWords C 1 hd => ((e d hd).symm p).val)
      (step d hd) F := by
  intro p
  exact congrArg Subtype.val
    ((e d hd).symm_apply_apply (periodicF d ((e d hd).symm p)))

private theorem actual_power (k : ℕ) (x : ResetHistory 4) :
    (J ^ k).val x = F^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ']
      simp only [Subgroup.coe_mul, Homeomorph.mul_apply]
      rw [ih, actual_J]
      exact (Function.iterate_succ_apply' F k x).symm

private theorem fixes : ∀ d : ℕ, 1 ≤ d → d ≤ 5 → ∀ x : ResetHistory 4,
    (shift G)^[d] x = x → (J ^ 20).val x = x := by
  intro d hd hle x hx
  have hd' : 0 < d := by omega
  let xp : TwistedPeriod C 1 d :=
    ⟨x, hx.trans (group_one x).symm⟩
  have hh := (finite_semiconj d hd').iterate_right 20 (e d hd' xp)
  rw [certificate d hd' hle] at hh
  have hxp : ((e d hd').symm (e d hd' xp)).val = x :=
    congrArg Subtype.val ((e d hd').symm_apply_apply xp)
  have hh' : x = F^[20] x :=
    hxp.symm.trans (hh.trans (congrArg (F^[20]) hxp))
  rw [actual_power]
  exact hh'.symm

private theorem descent (ι : Type u) (period : ι → ℕ)
    (hpos : ∀ i, 1 ≤ period i) (hle : ∀ i, period i ≤ 5)
    (χ : ResetFullAut 4 → ZMod 3)
    (hfactor : χ.FactorsThrough
      (fun h : ResetFullAut 4 => fun i : ι =>
        fun x : {x : ResetHistory 4 // (shift G)^[period i] x = x} => h.val x.val)) :
    χ (J ^ 20) = χ 1 := by
  apply hfactor
  funext i
  funext x
  exact fixes (period i) (hpos i) (hle i) x.val x.property

-- The native scalar is the EXISTING originalScalar, not a new chart.
-- Its existing originalScalar_action proof, at 1 and at the actual scalar
-- of h, transports the already proved rho homomorphism to scalar units.
-- The aliases refer to the existing private declarations.

private abbrev E := nativeIntEquiv 4 (by decide)

private theorem scalar_at_one (h : ResetFullAut 4) :
    E (originalScalar h : QF 4) = rho 4 (by decide) h (E 1) := by
  simpa only [mul_one] using originalScalar_action h 1

private def scalar : ResetFullAut 4 →* (QF 4)ˣ := {
  toFun := originalScalar
  map_one' := by
    apply Units.ext
    apply E.injective
    rw [scalar_at_one, (rho 4 (by decide)).map_one]
    rfl
  map_mul' := by
    intro g h
    apply Units.ext
    apply E.injective
    calc
      E (originalScalar (g * h) : QF 4) =
          rho 4 (by decide) (g * h) (E 1) := scalar_at_one (g * h)
      _ = rho 4 (by decide) g (rho 4 (by decide) h (E 1)) := by
        rw [(rho 4 (by decide)).map_mul]
        rfl
      _ = rho 4 (by decide) g (E (originalScalar h : QF 4)) := by
        rw [scalar_at_one h]
      _ = E ((originalScalar g : QF 4) * (originalScalar h : QF 4)) :=
        (originalScalar_action g (originalScalar h : QF 4)).symm }

private def T : ResetFullAut 4 := unitShift G

private def H : ResetFullAut 4 := evenAut 4 (by decide) (by decide)

private theorem scalar_T : (scalar T : QF 4) = fp 4 Polynomial.X := by
  apply E.injective
  calc
    E (scalar T : QF 4) = rho 4 (by decide) T (E 1) := scalar_at_one T
    _ = resetTheta 4 (E 1) := LinearMap.congr_fun (rho_unitShift 4 (by decide)) (E 1)
    _ = E (fp 4 Polynomial.X) := by
      simpa only [mul_one] using ((native_presentation 4 (by decide)).2.1 1).symm

private theorem scalar_H : (scalar H : QF 4) = 1 + fp 4 Polynomial.X := by
  apply E.injective
  calc
    E (scalar H : QF 4) = rho 4 (by decide) H (E 1) := scalar_at_one H
    _ = E 1 + resetTheta 4 (E 1) :=
      LinearMap.congr_fun (rho_even 4 (by decide) (by decide)) (E 1)
    _ = E 1 + E (fp 4 Polynomial.X) := by
      rw [← (native_presentation 4 (by decide)).2.1 1, mul_one]
    _ = E (1 + fp 4 Polynomial.X) := (E.map_add _ _).symm

private theorem minus_T : Units.map (minus 4).toMonoidHom (scalar T) = beta := by
  apply Units.ext
  change minus 4 (scalar T : QF 4) = (beta.val : Minus 4)
  rw [scalar_T, beta_val]
  rfl

private theorem minus_H : Units.map (minus 4).toMonoidHom (scalar H) = Bminus := by
  apply Units.ext
  change minus 4 (scalar H : QF 4) = (Bminus.val : Minus 4)
  rw [scalar_H, map_add, map_one, Bminus_val]
  rfl

private def residues := (Units.map (rminus 4).toMonoidHom).comp
  ((Units.map (minus 4).toMonoidHom).comp scalar)

private def χ : Additive (ResetFullAut 4) →+ ZMod 3 := cK.comp residues.toAdditive

private theorem residue_T : residues T = aUnit := by
  change Units.map (rminus 4).toMonoidHom
    (Units.map (minus 4).toMonoidHom (scalar T)) = aUnit
  rw [minus_T]
  rfl

private theorem residue_H : residues H = bUnit := by
  change Units.map (rminus 4).toMonoidHom
    (Units.map (minus 4).toMonoidHom (scalar H)) = bUnit
  rw [minus_H]
  rfl

private theorem chi_T : χ (Additive.ofMul T) = 0 := by
  change cK (Additive.ofMul (residues T)) = 0
  rw [residue_T]
  exact cK_a

private theorem chi_H : χ (Additive.ofMul H) = 1 := by
  change cK (Additive.ofMul (residues H)) = 1
  rw [residue_H]
  exact cK_b

private theorem chi_J : χ (Additive.ofMul J) = 1 := by
  change χ (Additive.ofMul (H * T)) = 1
  rw [ofMul_mul, map_add, chi_H, chi_T, add_zero]

private theorem chi_power : χ (Additive.ofMul (J ^ 20)) = 2 := by
  rw [ofMul_pow, map_nsmul, chi_J]
  decide

private theorem two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide
-- The auxiliary character gives the arbitrary-family contradiction.

private theorem chi_minus : ∀ h : ResetFullAut 4, χ (Additive.ofMul h) =
    cK (Additive.ofMul (Units.map (rminus 4).toMonoidHom
      (Units.map (minus 4).toMonoidHom (originalScalar h)))) := by
  intro h
  rfl

private theorem chi_nonfactorization :
    ∀ (ι : Type u) (period : ι → ℕ),
    (∀ i, 1 ≤ period i) → (∀ i, period i ≤ 5) →
    ¬ (fun h : ResetFullAut 4 => χ (Additive.ofMul h)).FactorsThrough
      (fun h : ResetFullAut 4 => fun i : ι =>
        fun x : {x : ResetHistory 4 //
          (shift G)^[period i] x = x} => h.val x.val) := by
  intro ι period hpos hle hfactor
  have bad := descent ι period hpos hle
    (fun h : ResetFullAut 4 => χ (Additive.ofMul h)) hfactor
  have chi_one : χ (Additive.ofMul (1 : ResetFullAut 4)) = 0 := χ.map_zero
  apply two_ne_zero
  exact chi_power.symm.trans (bad.trans chi_one)

-- These two definitions preserve the supplied exact original-root readout.
-- originalScalar is definitionally its exact scalarUnit.

private def psi := fun f : ResetFullAut 4 =>
  Units.map (ResetIntegralGluing.rplus 4).toMonoidHom
    (Units.map (ResetIntegralGluing.plus 4).toMonoidHom
      (ResetNativeUnitNormalForm.scalarUnit 4 (by decide)
        (ResetFullStandardBeamRepresentation.rho 4 (by decide) f)
        (ResetHistoryKernel.rho_time 4 (by decide) f)))

private def chi_add : ResetFullAut 4 → ZMod 3 := fun f =>
  ResetQ4UnitCubes.residueQuotientCharacter
    (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4)))
    ResetQ4OriginalLocalizedCubes.original_time_residue (Additive.ofMul
      (QuotientGroup.mk'
        (Subgroup.zpowers (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4))))
        (psi f)))

-- Public Compatible membership gives the ring equality. Units.ext lifts
-- it to BOTH iterated unit residues for an arbitrary integral native unit.
-- No access to the private compatible_image theorem is required.

private theorem unit_residues (u : (QF 4)ˣ) :
    Units.map (rplus 4).toMonoidHom
      (Units.map (plus 4).toMonoidHom u) =
    Units.map (rminus 4).toMonoidHom
      (Units.map (minus 4).toMonoidHom u) := by
  apply Units.ext
  change rplus 4 (plus 4 (u : QF 4)) = rminus 4 (minus 4 (u : QF 4))
  exact (toCompatible 4 (u : QF 4)).property

-- Reduce the exact root quotient readout, with its actual forward-time
-- generator and original_time_residue proof, to the SAME oriented cK.

private theorem abstract_readout
    (a : ResetQ4UnitCubes.Common4ˣ) (ha : a = aUnit)
    (u : ResetQ4UnitCubes.Plus4ˣ) :
    ResetQ4UnitCubes.residueQuotientCharacter a ha (Additive.ofMul
      (QuotientGroup.mk' (Subgroup.zpowers a)
        (Units.map (rplus 4).toMonoidHom u))) =
      cK (Additive.ofMul (Units.map (rplus 4).toMonoidHom u)) := by
  exact ResetQ4UnitCubes.residueQuotientCharacter_plus a ha u

private theorem psi_originalScalar (h : ResetFullAut 4) :
    psi h = Units.map (rplus 4).toMonoidHom
      (Units.map (plus 4).toMonoidHom (originalScalar h)) := by
  rfl

private theorem native_readout (h : ResetFullAut 4) :
    chi_add h = cK (Additive.ofMul (Units.map (rplus 4).toMonoidHom
      (Units.map (plus 4).toMonoidHom (originalScalar h)))) := by
  have h1 := psi_originalScalar h
  have h2 := abstract_readout
    (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4)))
    ResetQ4OriginalLocalizedCubes.original_time_residue
    (Units.map (plus 4).toMonoidHom (originalScalar h))
  have h3 := congrArg (fun z : ResetQ4UnitCubes.Common4ˣ =>
    ResetQ4UnitCubes.residueQuotientCharacter
      (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4)))
      ResetQ4OriginalLocalizedCubes.original_time_residue (Additive.ofMul
        (QuotientGroup.mk'
          (Subgroup.zpowers (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4)))) z))) h1
  exact h3.trans h2

private theorem same_native_character (h : ResetFullAut 4) :
    χ (Additive.ofMul h) = chi_add h := by
  have hresidue := congrArg (fun r => cK (Additive.ofMul r))
    (unit_residues (originalScalar h))
  exact (chi_minus h).trans (hresidue.symm.trans (native_readout h).symm)

private theorem native_nonfactorization :
    ∀ (ι : Type u) (period : ι → ℕ),
    (∀ i, 1 ≤ period i) → (∀ i, period i ≤ 5) →
    ¬ chi_add.FactorsThrough
      (fun h : ResetFullAut 4 => fun i : ι =>
        fun x : {x : ResetHistory 4 //
          (shift G)^[period i] x = x} => h.val x.val) := by
  intro ι period hpos hle
  have hcharacter : (fun h : ResetFullAut 4 => χ (Additive.ofMul h)) = chi_add :=
    funext same_native_character
  rw [← hcharacter]
  exact chi_nonfactorization ι period hpos hle

/-- Determination of the exact native character by all five whole period actions. -/
def claim : Prop :=
  chi_add.FactorsThrough
    (fun h : ResetFullAut 4 => fun i : Fin 5 =>
      fun x : {x : ResetHistory 4 //
        (shift (ResetGraph 4))^[i.val + 1] x = x} => h.val x.val)

/-- The original pair ((H * forward T)^20, 1) separates this character
while agreeing on every original history of each period from one to five. -/
theorem result : ¬ claim := by
  exact native_nonfactorization (Fin 5) (fun i => i.val + 1)
    (fun i => by omega) (fun i => by have hi := i.isLt; omega)

#print axioms result

end D5.S3.ConceptDynamics.Coding.ResetQ4SmallPeriodRefutation
