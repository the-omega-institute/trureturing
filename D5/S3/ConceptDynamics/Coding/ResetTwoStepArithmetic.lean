/- GID: D5/S3/ConceptDynamics/Coding/ResetTwoStepArithmetic
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetTwoStepArithmetic
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Actual two-step path squares and strict ranks realize two unit times on native histories. -/

import D5.S3.ConceptDynamics.Coding.ResetFullStandardBeamRepresentation
import D5.S3.ConceptDynamics.Coding.ResetTwoStepCarrier
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetNumberedHistories

open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap (GroupMat)
open Multiplicative
open scoped BigOperators Matrix

namespace TwoStep

open Alternating (Vertex B zero next flipSign sourceB targetB actualEdgeEquiv
  actual_source actual_target typedEdge originalEdge typed_original original_typed numbered_ext)
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap (Edge)
open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity (expandedGraph)
open D5.S3.ConceptDynamics.Coding.SameCutWholeRayBridge
open D5.S3.ConceptDynamics.Coding.NumberedSameCutWholeRay

def next2 {q : ℕ} (i : Fin q) (hi : i.val + 2 < q) : Fin q := ⟨i.val + 2, hi⟩
def active {q : ℕ} (i : Fin q) : Prop := i.val % 4 = 0 ∨ i.val % 4 = 1
instance {q : ℕ} (i : Fin q) : Decidable (active i) := inferInstanceAs (Decidable (_ ∨ _))

private theorem active_legal {q : ℕ} (h4 : 4 ∣ q) (i : Fin q) (ha : active i) :
    i.val + 2 < q := by
  have hmod := Nat.mod_eq_zero_of_dvd h4
  unfold active at ha
  omega

/-- Identity versus the four legal two-edge words, retaining absolute sign. -/
inductive R (q : ℕ) where
  | d (i : Fin q) (g : Sign)
  | aa (i : Fin q) (g : Sign) (hi : i.val + 2 < q)
  | af (i : Fin q) (g : Sign) (hi : i.val + 1 < q)
  | fa (i : Fin q) (g : Sign) (h1 : 1 < q)
  | ff (i : Fin q) (g : Sign)
  deriving DecidableEq

def source {q : ℕ} : R q → Vertex q
  | .d i g | .aa i g _ | .af i g _ | .fa i g _ | .ff i g => (i, g)
def target {q : ℕ} (hq : 0 < q) : R q → Vertex q
  | .d i g => (i, g)
  | .aa i g hi => (next2 i hi, g)
  | .af _ g _ => (zero hq, flipSign g)
  | .fa _ g h1 => (⟨1, h1⟩, flipSign g)
  | .ff _ g => (zero hq, g)

/-- Each nonidentity boundary stores an actual composable two-edge path. -/
def path {q : ℕ} (hq : 0 < q) : R q → Sum (Vertex q)
    {p : B q × B q // targetB hq p.1 = sourceB p.2}
  | .d i g => .inl (i, g)
  | .aa i g hi => .inr ⟨(.a i g (by omega), .a (next i (by omega)) g hi), rfl⟩
  | .af i g hi => .inr ⟨(.a i g hi, .f (next i hi) g), rfl⟩
  | .fa i g h1 => .inr ⟨(.f i g, .a (zero hq) (flipSign g) h1), rfl⟩
  | .ff i g => .inr ⟨(.f i g, .f (zero hq) (flipSign g)), rfl⟩

private def decodePath {q : ℕ} (hq : 0 < q) : Sum (Vertex q)
    {p : B q × B q // targetB hq p.1 = sourceB p.2} → R q
  | .inl v => .d v.1 v.2
  | .inr ⟨(.f i g, .f _ _), _⟩ => .ff i g
  | .inr ⟨(.f i g, .a _ _ hj), hc⟩ => .fa i g (by
      simp only [targetB, sourceB, Prod.mk.injEq] at hc
      have := congrArg Fin.val hc.1
      simp only [zero] at this
      omega)
  | .inr ⟨(.a i g hi, .f _ _), _⟩ => .af i g hi
  | .inr ⟨(.a i g hi, .a j _ hj), hc⟩ => .aa i g (by
      simp only [targetB, sourceB, Prod.mk.injEq] at hc
      have := congrArg Fin.val hc.1
      simp only [next] at this
      omega)

def pathEquiv {q : ℕ} (hq : 0 < q) : R q ≃ Sum (Vertex q)
    {p : B q × B q // targetB hq p.1 = sourceB p.2} where
  toFun := path hq
  invFun := decodePath hq
  left_inv r := by cases r <;> rfl
  right_inv p := by
    cases p with
    | inl v => rfl
    | inr p =>
        rcases p with ⟨⟨x, y⟩, hc⟩
        cases x <;> cases y <;>
          simp only [targetB, sourceB, Prod.mk.injEq] at hc <;>
          rcases hc with ⟨rfl, rfl⟩ <;> rfl

/-- The only exchange is the legal F versus AAF pair at active source age. -/
inductive Square {q : ℕ} (hq : 0 < q) : R q → B q → B q → R q → Prop
  | fdSwap (i : Fin q) (g : Sign) (hi : i.val + 2 < q) (ha : active i) :
      Square hq (.aa i g hi) (.f i g) (.f (next2 i hi) g) (.d (zero hq) (flipSign g))
  | fdFix (i : Fin q) (g : Sign) (ha : ¬ active i) :
      Square hq (.d i g) (.f i g) (.f i g) (.d (zero hq) (flipSign g))
  | aafSwap (i : Fin q) (g : Sign) (hi : i.val + 2 < q) (ha : active i) :
      Square hq (.d i g) (.a i g (by omega)) (.f i g)
        (.af (next i (by omega)) g hi)
  | aafFix (i : Fin q) (g : Sign) (hi : i.val + 2 < q) (ha : ¬ active i) :
      Square hq (.aa i g hi) (.a i g (by omega)) (.f (next2 i hi) g)
        (.af (next i (by omega)) g hi)
  | faa (i : Fin q) (g : Sign) (h2 : 2 < q) :
      Square hq (.fa i g (by omega)) (.f i g)
        (.a (⟨1, by omega⟩) (flipSign g) h2) (.aa (zero hq) (flipSign g) h2)
  | faf (i : Fin q) (g : Sign) (h1 : 1 < q) :
      Square hq (.fa i g h1) (.f i g) (.f (⟨1, h1⟩) (flipSign g))
        (.af (zero hq) (flipSign g) h1)
  | ffa (i : Fin q) (g : Sign) (h1 : 1 < q) :
      Square hq (.ff i g) (.f i g) (.a (zero hq) g h1)
        (.fa (zero hq) (flipSign g) h1)
  | fff (i : Fin q) (g : Sign) :
      Square hq (.ff i g) (.f i g) (.f (zero hq) g)
        (.ff (zero hq) (flipSign g))
  | ad (i : Fin q) (g : Sign) (hi : i.val + 1 < q) :
      Square hq (.d i g) (.a i g hi) (.a i g hi) (.d (next i hi) g)
  | aaa (i : Fin q) (g : Sign) (hi : i.val + 3 < q) :
      Square hq (.aa i g (by omega)) (.a i g (by omega))
        (.a (next2 i (by omega)) g hi) (.aa (next i (by omega)) g hi)
  | afa (i : Fin q) (g : Sign) (hi : i.val + 1 < q) (h1 : 1 < q) :
      Square hq (.af i g hi) (.a i g hi) (.a (zero hq) (flipSign g) h1)
        (.fa (next i hi) g h1)
  | aff (i : Fin q) (g : Sign) (hi : i.val + 1 < q) :
      Square hq (.af i g hi) (.a i g hi) (.f (zero hq) (flipSign g))
        (.ff (next i hi) g)

private theorem square_initial {q : ℕ} {hq : 0 < q} {r s : R q} {x y : B q}
    (hs : Square hq r x y s) :
    source r = sourceB x ∧ target hq r = sourceB y ∧ targetB hq x = source s := by
  cases hs <;> simp [source, target, sourceB, targetB, next, next2, zero, flipSign]

private theorem back_exists {q : ℕ} (hq : 0 < q) (h4 : 4 ∣ q)
    (x : B q) (s : R q) (hc : targetB hq x = source s) :
    ∃ r y, Square hq r x y s := by
  cases x with
  | f i g =>
      cases s with
      | d j h =>
          simp only [targetB, source, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          by_cases ha : active i
          · exact ⟨_, _, .fdSwap i g (active_legal h4 i ha) ha⟩
          · exact ⟨_, _, .fdFix i g ha⟩
      | aa j h hj =>
          simp only [targetB, source, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .faa i g hj⟩
      | af j h hj =>
          simp only [targetB, source, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .faf i g hj⟩
      | fa j h hj =>
          simp only [targetB, source, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          simpa [flipSign] using (show ∃ r y, Square hq r (.f i g) y
            (.fa (zero hq) (flipSign g) hj) from ⟨_, _, .ffa i g hj⟩)
      | ff j h =>
          simp only [targetB, source, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .fff i g⟩
  | a i g hi =>
      cases s with
      | d j h =>
          simp only [targetB, source, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .ad i g hi⟩
      | aa j h hj =>
          simp only [targetB, source, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .aaa i g hj⟩
      | af j h hj =>
          simp only [targetB, source, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          by_cases ha : active i
          · exact ⟨_, _, .aafSwap i g hj ha⟩
          · exact ⟨_, _, .aafFix i g hj ha⟩
      | fa j h hj =>
          simp only [targetB, source, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .afa i g hi hj⟩
      | ff j h =>
          simp only [targetB, source, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .aff i g hi⟩

private theorem forth_exists {q : ℕ} (hq : 0 < q) (h4 : 4 ∣ q)
    (r : R q) (y : B q) (hc : target hq r = sourceB y) :
    ∃ x s, Square hq r x y s := by
  cases r with
  | d i g =>
      cases y with
      | f j h =>
          simp only [target, sourceB, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          by_cases ha : active i
          · exact ⟨_, _, .aafSwap i g (active_legal h4 i ha) ha⟩
          · exact ⟨_, _, .fdFix i g ha⟩
      | a j h hj =>
          simp only [target, sourceB, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .ad i g hj⟩
  | aa i g hi =>
      cases y with
      | f j h =>
          simp only [target, sourceB, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          by_cases ha : active i
          · exact ⟨_, _, .fdSwap i g hi ha⟩
          · exact ⟨_, _, .aafFix i g hi ha⟩
      | a j h hj =>
          simp only [target, sourceB, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .aaa i g hj⟩
  | af i g hi =>
      cases y with
      | f j h =>
          simp only [target, sourceB, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .aff i g hi⟩
      | a j h hj =>
          simp only [target, sourceB, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .afa i g hi hj⟩
  | fa i g h1 =>
      cases y with
      | f j h =>
          simp only [target, sourceB, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .faf i g h1⟩
      | a j h hj =>
          simp only [target, sourceB, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .faa i g hj⟩
  | ff i g =>
      cases y with
      | f j h =>
          simp only [target, sourceB, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          simpa [flipSign] using (show ∃ x s, Square hq (.ff i g) x
            (.f (zero hq) g) s from ⟨_, _, .fff i g⟩)
      | a j h hj =>
          simp only [target, sourceB, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, _, .ffa i g hj⟩


abbrev Word (q : ℕ) := Sum (B q) (B q × B q × B q)

/-- A literal involution on tagged one/three-edge words. On legal words the
    exchanged pair has the same exact source, target and absolute sign. -/
def exchange {q : ℕ} (h4 : 4 ∣ q) : Word q → Word q
  | .inl (.f i g) => if ha : active i then
      .inr (.a i g (by have := active_legal h4 i ha; omega),
        .a (next i (by have := active_legal h4 i ha; omega)) g (active_legal h4 i ha),
        .f (next2 i (active_legal h4 i ha)) g)
      else .inl (.f i g)
  | .inl (.a i g hi) => .inl (.a i g hi)
  | .inr p => match p.1 with
      | .f _ _ => .inr p
      | .a i g hi => if ha : active i then
          if p.2.1 = .a (next i hi) g (active_legal h4 i ha) ∧
              p.2.2 = .f (next2 i (active_legal h4 i ha)) g then .inl (.f i g)
          else .inr p
          else .inr p

theorem exchange_involutive {q : ℕ} (h4 : 4 ∣ q) : Function.Involutive (exchange h4) := by
  intro w
  cases w with
  | inl x =>
      cases x with
      | f i g => by_cases ha : active i <;> simp [exchange, ha]
      | a i g hi => rfl
  | inr p =>
      rcases p with ⟨x,y,z⟩
      cases x with
      | f i g => rfl
      | a i g hi =>
          by_cases ha : active i
          · by_cases hh : y = .a (next i hi) g (active_legal h4 i ha) ∧
                z = .f (next2 i (active_legal h4 i ha)) g
            · rcases hh with ⟨rfl,rfl⟩; simp [exchange, ha]
            · simp [exchange, ha, hh]
          · simp [exchange, ha]

def leftWord {q : ℕ} (hq : 0 < q) (x : B q) (s : R q) : Word q :=
  match path hq s with
  | .inl _ => .inl x
  | .inr p => .inr (x, p.val.1, p.val.2)
def rightWord {q : ℕ} (hq : 0 < q) (r : R q) (y : B q) : Word q :=
  match path hq r with
  | .inl _ => .inl y
  | .inr p => .inr (p.val.1, p.val.2, y)

private theorem square_exchange {q : ℕ} {hq : 0 < q} (h4 : 4 ∣ q)
    {r s : R q} {x y : B q} (hs : Square hq r x y s) :
    exchange h4 (leftWord hq x s) = rightWord hq r y := by
  cases hs <;> simp_all [exchange, leftWord, rightWord, path, next, next2, zero, active, flipSign,
    mul_assoc, show (ofAdd true : Sign) * ofAdd true = 1 by decide]

private theorem square_endpoints {q : ℕ} {hq : 0 < q} (h4 : 4 ∣ q)
    {r s : R q} {x y : B q} (hs : Square hq r x y s) :
    source r = sourceB x ∧ target hq r = sourceB y ∧
      targetB hq x = source s ∧ target hq s = targetB hq y := by
  have hi := square_initial hs
  refine ⟨hi.1, hi.2.1, hi.2.2, ?_⟩
  cases hs <;> simp [target, targetB, next, next2, zero, flipSign, mul_assoc,
    show (ofAdd true : Sign) * ofAdd true = 1 by decide]

private theorem rightWord_unique {q : ℕ} {hq : 0 < q}
    {r r' : R q} {y y' : B q}
    (hc : target hq r = sourceB y) (hc' : target hq r' = sourceB y')
    (hw : rightWord hq r y = rightWord hq r' y') : r = r' ∧ y = y' := by
  cases r <;> cases r' <;> cases y <;> cases y' <;> simp_all [rightWord, path, target, sourceB,
    next, next2, zero, Fin.ext_iff] <;> omega

private theorem leftWord_unique {q : ℕ} {hq : 0 < q}
    {s s' : R q} {x x' : B q}
    (hc : targetB hq x = source s) (hc' : targetB hq x' = source s')
    (hw : leftWord hq x s = leftWord hq x' s') : x = x' ∧ s = s' := by
  cases s <;> cases s' <;> simp_all [leftWord, path, targetB, source,
    next, next2, zero, Fin.ext_iff] <;> omega

private theorem square_back_unique {q : ℕ} {hq : 0 < q} (h4 : 4 ∣ q)
    {r r' s : R q} {x y y' : B q}
    (hs : Square hq r x y s) (hs' : Square hq r' x y' s) : r = r' ∧ y = y' := by
  exact rightWord_unique (square_endpoints h4 hs).2.1 (square_endpoints h4 hs').2.1
    ((square_exchange h4 hs).symm.trans (square_exchange h4 hs'))

private theorem square_forth_unique {q : ℕ} {hq : 0 < q} (h4 : 4 ∣ q)
    {r s s' : R q} {x x' y : B q}
    (hs : Square hq r x y s) (hs' : Square hq r x' y s') : x = x' ∧ s = s' := by
  have hw := (square_exchange h4 hs).trans (square_exchange h4 hs').symm
  have hinj := (exchange_involutive h4).injective hw
  exact leftWord_unique (square_endpoints h4 hs).2.2.1 (square_endpoints h4 hs').2.2.1 hinj

def leftRank {q : ℕ} (r r' : R q) : ℕ :=
  if r = r' then 0 else
  match r, r' with
  | .d i _, .aa _ _ _ | .aa i _ _, .d _ _ => i.val + 3
  | .d i _, .af _ _ _ | .af i _ _, .d _ _ =>
      if i.val % 4 = 0 ∨ i.val % 4 = 3 then i.val + 3 else 1
  | .d i _, .fa _ _ _ | .fa i _ _, .d _ _
  | .d i _, .ff _ _ | .ff i _, .d _ _ =>
      if i.val % 4 = 0 ∨ i.val % 4 = 1 then i.val + 3 else 2
  | .aa i _ _, .af _ _ _ | .af i _ _, .aa _ _ _ =>
      if i.val % 4 = 1 ∨ i.val % 4 = 2 then i.val + 3 else 1
  | .aa i _ _, .fa _ _ _ | .fa i _ _, .aa _ _ _
  | .aa i _ _, .ff _ _ | .ff i _, .aa _ _ _ =>
      if i.val % 4 = 2 ∨ i.val % 4 = 3 then i.val + 3 else 2
  | .af i _ _, .fa _ _ _ | .fa i _ _, .af _ _ _
  | .af i _ _, .ff _ _ | .ff i _, .af _ _ _ =>
      if i.val % 4 = 1 ∨ i.val % 4 = 3 then i.val + 3 else 2
  | .fa _ _ _, .ff _ _ | .ff _ _, .fa _ _ _ => 1
  | _, _ => 0

def lastEdge {q : ℕ} (hq : 0 < q) : R q → Option (B q)
  | .d _ _ => none
  | .aa i g hi => some (.a (next i (by omega)) g hi)
  | .af i g hi => some (.f (next i hi) g)
  | .fa _ g h1 => some (.a (zero hq) (flipSign g) h1)
  | .ff _ g => some (.f (zero hq) (flipSign g))

def rightRank {q : ℕ} (hq : 0 < q) (r r' : R q) : ℕ :=
  if r = r' then 0 else
  match r, r' with
  | .d _ _, .d _ _ => 0
  | .d i _, _ => q - i.val
  | _, .d i _ => q - i.val
  | _, _ => if lastEdge hq r = lastEdge hq r' then 1 else 2

private theorem leftRank_positive {q : ℕ} {r r' : R q}
    (hc : source r = source r') (hn : r ≠ r') : 0 < leftRank r r' := by
  cases r <;> cases r' <;> simp_all [source, leftRank, Fin.ext_iff] <;>
    (try split_ifs) <;> omega

private theorem leftRank_le {q : ℕ} (hq : 0 < q) (h4 : 4 ∣ q) {r r' : R q}
    (hc : source r = source r') : leftRank r r' ≤ q := by
  have hm := Nat.mod_eq_zero_of_dvd h4
  cases r <;> cases r' <;> simp_all [source, leftRank, Fin.ext_iff] <;>
    (try split_ifs) <;> omega

private theorem rightRank_positive {q : ℕ} (hq : 0 < q) {r r' : R q}
    (hc : target hq r = target hq r') (hn : r ≠ r') : 0 < rightRank hq r r' := by
  have hb := (target hq r).1.isLt
  have hb' := (target hq r').1.isLt
  cases r <;> cases r' <;> simp_all [target, rightRank, next2, zero, Fin.ext_iff] <;>
    (try split_ifs) <;> (try simp_all [target, next2, zero, Fin.ext_iff]) <;> omega

private theorem rightRank_le {q : ℕ} (hq : 0 < q) (h4 : 4 ∣ q) (r r' : R q) :
    rightRank hq r r' ≤ q := by
  have hm := Nat.mod_eq_zero_of_dvd h4
  cases r <;> cases r' <;> simp_all [rightRank] <;> (try split_ifs) <;> omega

private theorem leftRank_step {q : ℕ} {hq : 0 < q} (h4 : 4 ∣ q)
    {r r' s s' : R q} {x x' y y' : B q}
    (hs : Square hq r x y s) (hs' : Square hq r' x' y' s')
    (hx : x = x') (hn : r ≠ r') : leftRank r r' < leftRank s s' := by
  have hm := Nat.mod_eq_zero_of_dvd h4
  cases hs <;> cases hs' <;>
    simp_all [leftRank, next, next2, zero, active, Fin.ext_iff] <;>
    (try split_ifs) <;> (try simp_all) <;> omega


private theorem flipSign_inj (g h : Sign) : flipSign g = flipSign h ↔ g = h :=
  mul_right_cancel_iff

private def lastKey {q : ℕ} : R q → Option (Bool × ℕ)
  | .d _ _ => none
  | .aa i _ _ => some (true, i.val + 1)
  | .af i _ _ => some (false, i.val + 1)
  | .fa _ _ _ => some (true, 0)
  | .ff _ _ => some (false, 0)

private theorem same_last_iff {q : ℕ} (hq : 0 < q) {r r' : R q}
    (hc : target hq r = target hq r') :
    (lastEdge hq r = lastEdge hq r') ↔ (lastKey r = lastKey r') := by
  cases r <;> cases r' <;>
    simp_all [target, lastEdge, lastKey, next, next2, zero, flipSign, Fin.ext_iff] <;> omega

private theorem rightRank_step {q : ℕ} {hq : 0 < q} (h4 : 4 ∣ q)
    {r r' s s' : R q} {x x' y y' : B q}
    (hs : Square hq r x y s) (hs' : Square hq r' x' y' s')
    (hy : y = y') (hn : s ≠ s') : rightRank hq s s' < rightRank hq r r' := by
  have hnr : r ≠ r' := by
    intro hr
    subst r'
    subst y'
    exact hn (square_forth_unique h4 hs hs').2
  have hr := (square_endpoints h4 hs).2.1.trans
    ((congrArg sourceB hy).trans (square_endpoints h4 hs').2.1.symm)
  have ht := (square_endpoints h4 hs).2.2.2.trans
    ((congrArg (targetB hq) hy).trans (square_endpoints h4 hs').2.2.2.symm)
  have hlr := same_last_iff hq hr
  have hls := same_last_iff hq ht
  have hm := Nat.mod_eq_zero_of_dvd h4
  simp only [rightRank, if_neg hn, if_neg hnr, hlr, hls]
  clear hlr hls hr ht
  cases hs <;> cases hs'
  case fff.fdFix i g j h ha =>
    have hyy := hy
    simp only [B.f.injEq] at hyy
    have hj : zero hq = j := hyy.1
    have hac : active j := by rw [← hj]; exact Or.inl rfl
    exact (ha hac).elim
  case aff.fdFix i g hi j h ha =>
    have hyy := hy
    simp only [B.f.injEq] at hyy
    have hj : zero hq = j := hyy.1
    have hac : active j := by rw [← hj]; exact Or.inl rfl
    exact (ha hac).elim
  all_goals simp_all [lastKey, target, next, next2, zero, active, Fin.ext_iff, flipSign_inj] <;>
    (try split_ifs) <;> omega

abbrev Pair (q : ℕ) (hq : 0 < q) :=
  {p : B q × B q // targetB hq p.1 = sourceB p.2}


open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap (split join split_join join_split)

private theorem product_target {q : ℕ} (a b : Edge (resetMatrix q)) (hc : a.target = b.source) :
    (join (resetMatrix q) (resetMatrix q) a b hc).target = b.target := rfl

private theorem product_label {q : ℕ} (a b : Edge (resetMatrix q)) (hc : a.target = b.source) :
    (join (resetMatrix q) (resetMatrix q) a b hc).label = a.label * b.label := rfl

def pairNumber {q : ℕ} (hq : 0 < q) (p : Pair q hq) : Edge (twoStepMatrix q) × Sign :=
  let a := originalEdge hq p.val.1
  let b := originalEdge hq p.val.2
  (join (resetMatrix q) (resetMatrix q) a.1 b.1 (by
    have h := (actual_target hq p.val.1).trans
      (p.property.trans (actual_source hq p.val.2).symm)
    have ht : a.1.target = b.1.source := congrArg Prod.fst h
    exact ht), a.2)

private def pairDecode {q : ℕ} (hq : 0 < q) (e : Edge (twoStepMatrix q) × Sign) :
    Pair q hq :=
  let p := split (resetMatrix q) (resetMatrix q) e.1
  ⟨(typedEdge (p.1, e.2), typedEdge (p.2, e.2 * p.1.label)), by
    rw [Alternating.target_typed hq, Alternating.source_typed hq]
    rfl⟩

private theorem pair_number_decode {q : ℕ} (hq : 0 < q)
    (e : Edge (twoStepMatrix q) × Sign) : pairNumber hq (pairDecode hq e) = e := by
  simp only [pairNumber, pairDecode, original_typed]
  exact Prod.ext (join_split (resetMatrix q) (resetMatrix q) e.1) rfl

private theorem pair_decode_number {q : ℕ} (hq : 0 < q) (p : Pair q hq) :
    pairDecode hq (pairNumber hq p) = p := by
  apply Subtype.ext
  have hc := p.property
  have he := (actual_target hq p.val.1).trans (hc.trans (actual_source hq p.val.2).symm)
  have hg := congrArg Prod.snd he
  dsimp only [pairDecode, pairNumber]
  rw [split_join]
  dsimp only
  change (originalEdge hq p.val.1).2 * (originalEdge hq p.val.1).1.label =
    (originalEdge hq p.val.2).2 at hg
  apply Prod.ext
  · exact typed_original hq p.val.1
  · rw [hg]
    exact typed_original hq p.val.2

def pairNumberEquiv {q : ℕ} (hq : 0 < q) : Pair q hq ≃ Edge (twoStepMatrix q) × Sign where
  toFun := pairNumber hq
  invFun := pairDecode hq
  left_inv := pair_decode_number hq
  right_inv := pair_number_decode hq

private def genericBoundaryEquiv {q : ℕ} (hq : 0 < q) : R q ≃ Edge (twoStepCarrier q) × Sign :=
  (pathEquiv hq).trans
    ((Equiv.sumCongr (Alternating.identityExpandedEquiv q) (pairNumberEquiv hq)).trans
      (Alternating.expandedAddEquiv (1 : GroupMat Sign q q) (twoStepMatrix q)))

private theorem generic_source {q : ℕ} (hq : 0 < q) (r : R q) :
    (expandedGraph (twoStepCarrier q)).source (genericBoundaryEquiv hq r) = source r := by
  cases r <;> rfl

private theorem generic_target {q : ℕ} (hq : 0 < q) (r : R q) :
    (expandedGraph (twoStepCarrier q)).target (genericBoundaryEquiv hq r) = target hq r := by
  cases r <;> simp [genericBoundaryEquiv, pathEquiv, path,
    Alternating.expandedAddEquiv, Alternating.addLeft, Alternating.addRight,
    Alternating.identityExpandedEquiv, Alternating.identityEdge,
    pairNumberEquiv, pairNumber, product_label, product_target, actualEdgeEquiv, originalEdge,
    expandedGraph, target, next2, next, zero, flipSign, mul_assoc,
    show (ofAdd true : Sign) * ofAdd true = 1 by decide]

/-- The equal-endpoint identity and FF boundaries retain numbers zero and one. -/
private theorem generic_origin_numbering {q : ℕ} (hq : 0 < q) (g : Sign) :
    (genericBoundaryEquiv hq (.d (zero hq) g)).1.number.val = 0 ∧
      (genericBoundaryEquiv hq (.ff (zero hq) g)).1.number.val = 1 := by
  constructor
  · rfl
  · let e := pairNumber hq
      (⟨(.f (zero hq) g, .f (zero hq) (flipSign g)), rfl⟩ : Pair q hq)
    have hs : e.1.source = origin hq := rfl
    have ht : e.1.target = origin hq := rfl
    have hl : e.1.label = 1 := by
      change (ofAdd true : Sign) * ofAdd true = 1
      decide
    have hc : ((twoStepMatrix q) e.1.source e.1.target).coeff e.1.label = 1 := by
      rw [hs, ht, hl, twoStep_origin_square_coeff q hq]
    have hn : e.1.number.val < 1 := lt_of_lt_of_le e.1.number.isLt (le_of_eq hc)
    have hz : e.1.number.val = 0 := by omega
    change ((1 : GroupMat Sign q q) (origin hq) (origin hq)).coeff (1 : Sign) +
      e.1.number.val = 1
    rw [Alternating.identity_coefficient, hz]
    simp


private def numberedBoundary {q : ℕ} (hq : 0 < q) : R q → Edge (twoStepCarrier q) × Sign
  | .ff i g => if hi : i = zero hq then
      (⟨i, zero hq, 1, ⟨1, by
        subst i
        have hc := twoStep_origin_coeff q hq
        change 1 < ((twoStepCarrier q) (origin hq) (origin hq)).coeff (1 : Sign)
        omega⟩⟩, g)
      else genericBoundaryEquiv hq (.ff i g)
  | r => genericBoundaryEquiv hq r

private theorem numbered_boundary_eq {q : ℕ} (hq : 0 < q) (r : R q) :
    numberedBoundary hq r = genericBoundaryEquiv hq r := by
  cases r with
  | ff i g =>
      by_cases hi : i = zero hq
      · subst i
        simp only [numberedBoundary, dif_pos rfl]
        apply Prod.ext
        · apply numbered_ext
          · rfl
          · rfl
          · simp [genericBoundaryEquiv, pathEquiv, path, pairNumberEquiv, pairNumber,
              Alternating.expandedAddEquiv, Alternating.addRight, product_label, originalEdge,
              show (ofAdd true : Sign) * ofAdd true = 1 by decide]
          · exact (generic_origin_numbering hq g).2.symm
        · rfl
      · simp only [numberedBoundary, dif_neg hi]
  | d i g => rfl
  | aa i g hi => rfl
  | af i g hi => rfl
  | fa i g h1 => rfl

def numberedBoundaryEquiv {q : ℕ} (hq : 0 < q) : R q ≃ Edge (twoStepCarrier q) × Sign where
  toFun := numberedBoundary hq
  invFun := (genericBoundaryEquiv hq).symm
  left_inv r := by rw [numbered_boundary_eq]; exact (genericBoundaryEquiv hq).symm_apply_apply r
  right_inv r := by rw [numbered_boundary_eq]; exact (genericBoundaryEquiv hq).apply_symm_apply r

private theorem numbered_source {q : ℕ} (hq : 0 < q) (r : R q) :
    (expandedGraph (twoStepCarrier q)).source (numberedBoundaryEquiv hq r) = source r := by
  change (expandedGraph (twoStepCarrier q)).source (numberedBoundary hq r) = _
  rw [numbered_boundary_eq]
  exact generic_source hq r
private theorem numbered_target {q : ℕ} (hq : 0 < q) (r : R q) :
    (expandedGraph (twoStepCarrier q)).target (numberedBoundaryEquiv hq r) = target hq r := by
  change (expandedGraph (twoStepCarrier q)).target (numberedBoundary hq r) = _
  rw [numbered_boundary_eq]
  exact generic_target hq r

private def backChoice {q : ℕ} (hq : 0 < q) (h4 : 4 ∣ q) (x : B q) (s : R q) : R q × B q :=
  if hc : targetB hq x = source s then
    let r := Classical.choose (back_exists hq h4 x s hc)
    (r, Classical.choose (Classical.choose_spec (back_exists hq h4 x s hc)))
  else (.d (sourceB x).1 (sourceB x).2, x)
private theorem backChoice_spec {q : ℕ} (hq : 0 < q) (h4 : 4 ∣ q) (x : B q) (s : R q)
    (hc : targetB hq x = source s) : Square hq (backChoice hq h4 x s).1 x (backChoice hq h4 x s).2 s := by
  simp only [backChoice, dif_pos hc]
  exact Classical.choose_spec (Classical.choose_spec (back_exists hq h4 x s hc))
private def forthChoice {q : ℕ} (hq : 0 < q) (h4 : 4 ∣ q) (r : R q) (y : B q) : B q × R q :=
  if hc : target hq r = sourceB y then
    let x := Classical.choose (forth_exists hq h4 r y hc)
    (x, Classical.choose (Classical.choose_spec (forth_exists hq h4 r y hc)))
  else (y, .d (targetB hq y).1 (targetB hq y).2)
private theorem forthChoice_spec {q : ℕ} (hq : 0 < q) (h4 : 4 ∣ q) (r : R q) (y : B q)
    (hc : target hq r = sourceB y) : Square hq r (forthChoice hq h4 r y).1 y (forthChoice hq h4 r y).2 := by
  simp only [forthChoice, dif_pos hc]
  exact Classical.choose_spec (Classical.choose_spec (forth_exists hq h4 r y hc))

abbrev BRFiber {q : ℕ} (hq : 0 < q) (v z : Vertex q) :=
  {p : B q × R q // sourceB p.1 = v ∧ targetB hq p.1 = source p.2 ∧ target hq p.2 = z}
abbrev RBFiber {q : ℕ} (hq : 0 < q) (v z : Vertex q) :=
  {p : R q × B q // source p.1 = v ∧ target hq p.1 = sourceB p.2 ∧ targetB hq p.2 = z}

/-- The actual BR2/R2B bijection on each exact expanded endpoint fiber. -/
def endpointSquare {q : ℕ} (hq : 0 < q) (h4 : 4 ∣ q) (v z : Vertex q) :
    BRFiber hq v z ≃ RBFiber hq v z where
  toFun p := ⟨backChoice hq h4 p.val.1 p.val.2, by
    have he := square_endpoints h4 (backChoice_spec hq h4 p.val.1 p.val.2 p.property.2.1)
    exact ⟨he.1.trans p.property.1, he.2.1, he.2.2.2.symm.trans p.property.2.2⟩⟩
  invFun p := ⟨forthChoice hq h4 p.val.1 p.val.2, by
    have he := square_endpoints h4 (forthChoice_spec hq h4 p.val.1 p.val.2 p.property.2.1)
    exact ⟨he.1.symm.trans p.property.1, he.2.2.1, he.2.2.2.trans p.property.2.2⟩⟩
  left_inv p := by
    apply Subtype.ext
    have hs := backChoice_spec hq h4 p.val.1 p.val.2 p.property.2.1
    have ht := forthChoice_spec hq h4 (backChoice hq h4 p.val.1 p.val.2).1
      (backChoice hq h4 p.val.1 p.val.2).2 (square_endpoints h4 hs).2.1
    have hu := square_forth_unique h4 hs ht
    exact (Prod.ext hu.1 hu.2).symm
  right_inv p := by
    apply Subtype.ext
    have hs := forthChoice_spec hq h4 p.val.1 p.val.2 p.property.2.1
    have ht := backChoice_spec hq h4 (forthChoice hq h4 p.val.1 p.val.2).1
      (forthChoice hq h4 p.val.1 p.val.2).2 (square_endpoints h4 hs).2.2.1
    have hu := square_back_unique h4 hs ht
    exact (Prod.ext hu.1 hu.2).symm

private def back {q : ℕ} (hq : 0 < q) (h4 : 4 ∣ q) (x : B q) (s : R q) : R q × B q :=
  if hc : targetB hq x = source s then
    ((endpointSquare hq h4 (sourceB x) (target hq s)) ⟨(x,s),rfl,hc,rfl⟩).val
  else (.d (sourceB x).1 (sourceB x).2, x)
private theorem back_spec {q : ℕ} (hq : 0 < q) (h4 : 4 ∣ q) (x : B q) (s : R q)
    (hc : targetB hq x = source s) : Square hq (back hq h4 x s).1 x (back hq h4 x s).2 s := by
  simp only [back, dif_pos hc]
  exact backChoice_spec hq h4 x s hc
private def forth {q : ℕ} (hq : 0 < q) (h4 : 4 ∣ q) (r : R q) (y : B q) : B q × R q :=
  if hc : target hq r = sourceB y then
    ((endpointSquare hq h4 (source r) (targetB hq y)).symm ⟨(r,y),rfl,hc,rfl⟩).val
  else (y, .d (targetB hq y).1 (targetB hq y).2)
private theorem forth_spec {q : ℕ} (hq : 0 < q) (h4 : 4 ∣ q) (r : R q) (y : B q)
    (hc : target hq r = sourceB y) : Square hq r (forth hq h4 r y).1 y (forth hq h4 r y).2 := by
  simp only [forth, dif_pos hc]
  exact forthChoice_spec hq h4 r y hc

private theorem decoded_source {q : ℕ} (hq : 0 < q) (r : Edge (twoStepCarrier q) × Sign) :
    source ((numberedBoundaryEquiv hq).symm r) = (expandedGraph (twoStepCarrier q)).source r := by
  rw [← numbered_source hq, Equiv.apply_symm_apply]
private theorem decoded_target {q : ℕ} (hq : 0 < q) (r : Edge (twoStepCarrier q) × Sign) :
    target hq ((numberedBoundaryEquiv hq).symm r) = (expandedGraph (twoStepCarrier q)).target r := by
  rw [← numbered_target hq, Equiv.apply_symm_apply]

def numberedData (q : ℕ) (hq : 0 < q) (h4 : 4 ∣ q) :
    NumberedData (resetMatrix q) (resetMatrix q) (twoStepCarrier q) where
  squares := {
    source := (expandedGraph (twoStepCarrier q)).source
    target := (expandedGraph (twoStepCarrier q)).target
    sq := fun r x y s => Square hq ((numberedBoundaryEquiv hq).symm r)
      (typedEdge x) (typedEdge y) ((numberedBoundaryEquiv hq).symm s)
    endpoints := by
      intro r x y s hs
      have he := square_endpoints h4 hs
      exact ⟨(decoded_source hq r).symm.trans (he.1.trans (Alternating.source_typed hq x)),
        (decoded_target hq r).symm.trans (he.2.1.trans (Alternating.source_typed hq y)),
        (decoded_source hq s).symm.trans (he.2.2.1.symm.trans (Alternating.target_typed hq x)),
        (decoded_target hq s).symm.trans (he.2.2.2.trans (Alternating.target_typed hq y))⟩
    back := fun x s =>
      let p := back hq h4 (typedEdge x) ((numberedBoundaryEquiv hq).symm s)
      (numberedBoundaryEquiv hq p.1, actualEdgeEquiv hq p.2)
    back_spec := by
      intro x s hc
      have ht : targetB hq (typedEdge x) = source ((numberedBoundaryEquiv hq).symm s) :=
        (Alternating.target_typed hq x).trans (hc.trans (decoded_source hq s).symm)
      simpa only [Equiv.symm_apply_apply, actualEdgeEquiv, Equiv.coe_fn_mk, typed_original] using
        back_spec hq h4 (typedEdge x) ((numberedBoundaryEquiv hq).symm s) ht
    forth := fun r y =>
      let p := forth hq h4 ((numberedBoundaryEquiv hq).symm r) (typedEdge y)
      (actualEdgeEquiv hq p.1, numberedBoundaryEquiv hq p.2)
    forth_spec := by
      intro r y hc
      have ht : target hq ((numberedBoundaryEquiv hq).symm r) = sourceB (typedEdge y) :=
        (decoded_target hq r).trans (hc.trans (Alternating.source_typed hq y).symm)
      simpa only [Equiv.symm_apply_apply, actualEdgeEquiv, Equiv.coe_fn_mk, typed_original] using
        forth_spec hq h4 ((numberedBoundaryEquiv hq).symm r) (typedEdge y) ht
    back_unique := by
      intro r r' s x y y' hs hs'
      have hu := square_back_unique h4 hs hs'
      exact ⟨(numberedBoundaryEquiv hq).symm.injective hu.1,
        (actualEdgeEquiv hq).symm.injective hu.2⟩
    forth_unique := by
      intro r s s' x x' y hs hs'
      have hu := square_forth_unique h4 hs hs'
      exact ⟨(actualEdgeEquiv hq).symm.injective hu.1,
        (numberedBoundaryEquiv hq).symm.injective hu.2⟩
    outgoing := fun v => ⟨numberedBoundaryEquiv hq (.d v.1 v.2), numbered_source hq _⟩
    incoming := fun v => ⟨numberedBoundaryEquiv hq (.d v.1 v.2), numbered_target hq _⟩ }
  source_exact _ := rfl
  target_exact _ := rfl

/-- q strict integer steps contradict ranks in [1,q], including the last cut. -/
theorem finiteForgetting (q : ℕ) (hq : 0 < q) (h4 : 4 ∣ q) :
    FiniteForgetting (numberedData q hq h4).squares q where
  positive := hq
  left := by
    intro x y y' r r' hs hs'
    let b := fun i => (numberedBoundaryEquiv hq).symm (r i)
    let b' := fun i => (numberedBoundaryEquiv hq).symm (r' i)
    change ∀ i, i < q → Square hq (b i) (typedEdge (x i)) (typedEdge (y i)) (b (i+1)) at hs
    change ∀ i, i < q → Square hq (b' i) (typedEdge (x i)) (typedEdge (y' i)) (b' (i+1)) at hs'
    apply (numberedBoundaryEquiv hq).symm.injective
    change b 0 = b' 0
    by_contra hn
    have grow : ∀ n, n ≤ q → b n ≠ b' n ∧ leftRank (b 0) (b' 0) + n ≤ leftRank (b n) (b' n) := by
      intro n
      induction n with
      | zero => exact fun _ => ⟨hn, by omega⟩
      | succ n ih =>
          intro hle
          have hp := ih (by omega)
          have ha := hs n (by omega)
          have hb := hs' n (by omega)
          have hne : b (n+1) ≠ b' (n+1) := by
            intro hh
            exact hp.1 (square_back_unique h4 ha (hh.symm ▸ hb)).1
          have hstep := leftRank_step h4 ha hb rfl hp.1
          exact ⟨hne, by omega⟩
    have he := square_endpoints h4 (hs 0 hq)
    have he' := square_endpoints h4 (hs' 0 hq)
    have hp := leftRank_positive (he.1.trans he'.1.symm) hn
    have ht := square_endpoints h4 (hs (q-1) (by omega))
    have ht' := square_endpoints h4 (hs' (q-1) (by omega))
    have hsrc : source (b q) = source (b' q) := by
      have hh := ht.2.2.1.symm.trans ht'.2.2.1
      simpa [b, b', show q-1+1=q by omega] using hh
    have hbound := leftRank_le hq h4 hsrc
    have h := (grow q le_rfl).2
    omega
  right := by
    intro x x' y r r' hs hs'
    let b := fun i => (numberedBoundaryEquiv hq).symm (r i)
    let b' := fun i => (numberedBoundaryEquiv hq).symm (r' i)
    change ∀ i, i < q → Square hq (b i) (typedEdge (x i)) (typedEdge (y i)) (b (i+1)) at hs
    change ∀ i, i < q → Square hq (b' i) (typedEdge (x' i)) (typedEdge (y i)) (b' (i+1)) at hs'
    apply (numberedBoundaryEquiv hq).symm.injective
    change b q = b' q
    by_contra hn
    have neq : ∀ i, i ≤ q → b i ≠ b' i := by
      intro i hi hh
      have propagate : ∀ j, i ≤ j → j ≤ q → b j = b' j := by
        intro j
        induction j with
        | zero =>
            intro hij _
            have hz : i = 0 := by omega
            simpa only [hz] using hh
        | succ j ih =>
            intro hij hjq
            by_cases heq : i = j+1
            · simpa [heq] using hh
            · have hj := ih (by omega) (by omega)
              exact (square_forth_unique h4 (hs j (by omega)) (hj.symm ▸ hs' j (by omega))).2
      exact hn (propagate q hi le_rfl)
    have shrink : ∀ n, n ≤ q → rightRank hq (b n) (b' n) + n ≤ rightRank hq (b 0) (b' 0) := by
      intro n
      induction n with
      | zero => intro _; omega
      | succ n ih =>
          intro hle
          have hp := ih (by omega)
          have hd := rightRank_step h4 (hs n (by omega)) (hs' n (by omega)) rfl
            (neq (n+1) hle)
          omega
    have ht := square_endpoints h4 (hs (q-1) (by omega))
    have ht' := square_endpoints h4 (hs' (q-1) (by omega))
    have htgt : target hq (b q) = target hq (b' q) := by
      have hh := ht.2.2.2.trans ht'.2.2.2.symm
      simpa [b, b', show q-1+1=q by omega] using hh
    have hp := rightRank_positive hq htgt hn
    have hb := rightRank_le hq h4 (b 0) (b' 0)
    have hd := shrink q le_rfl
    omega

open D5.S3.ConceptDynamics.Coding.ResetStandardBeamGeometry
open D5.S3.ConceptDynamics.Coding.ResetFullStandardBeamRepresentation (rho rho_beam_image)
open D5.S3.ConceptDynamics.Coding.StandardBeamGeometry
open D5.S3.ConceptDynamics.Coding.StandardBeamEndpointRows
open D5.S3.ConceptDynamics.Coding.StandardBeamCoordinates
open D5.S3.ConceptDynamics.Coding.StandardBeamColimitCuts
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy (DimensionGroup VertexModule transition vertex vertexBasis)
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization (History)

local instance originalNativeIntModule (q : ℕ) : Module ℤ (DimensionGroup (resetMatrix q)) :=
  AddCommGroup.toIntModule _

/-- Original histories, original product topology and original unit time. -/
def aut (q : ℕ) (hq : 0 < q) (h4 : 4 ∣ q) : ResetFullAut q :=
  ⟨(numberedData q hq h4).squares.historyHomeomorph (finiteForgetting q hq h4),
    (numberedData q hq h4).squares.H_shift (finiteForgetting q hq h4)⟩

private theorem image_atCut (q : ℕ) (hq : 0 < q) (h4 : 4 ∣ q)
    (alpha : ResetHistory q) (n : ℤ) :
    AtCut (ResetGraph q) ((aut q hq h4).val '' ray (ResetGraph q) alpha n) n := by
  let T := numberedData q hq h4
  let K := finiteForgetting q hq h4
  have hu := T.numbered_same_cut_whole_ray_image K (Alternating.reset_expanded_essential q hq) alpha n
  change AtCut (ResetGraph q) (T.squares.H K '' T.Cleft alpha n) n
  rw [hu]
  exact atCut_iUnion (ResetGraph q) _ n (fun r =>
    ray_atCut (ResetGraph q) (Alternating.reset_expanded_essential q hq) (T.beta
      (Alternating.reset_expanded_essential q hq) alpha n r) n)

/-- Every full numbered C edge contributes its endpoint, with arbitrary
    future histories and both origin copies still present. -/
theorem image_endpointRow (q : ℕ) (hq : 0 < q) (h4 : 4 ∣ q)
    (alpha : ResetHistory q) (n : ℤ) :
    letI : Finite (Parts (ResetGraph q)
      ((aut q hq h4).val '' ray (ResetGraph q) alpha n) n) := (image_atCut q hq h4 alpha n).1
    endpointRow (ResetGraph q) ((aut q hq h4).val '' ray (ResetGraph q) alpha n) n =
      (Pi.single (endpoint (ResetGraph q) alpha n) 1) ᵥ*
        NativeIntegralRowTransport.expansionMatrix (twoStepCarrier q) := by
  classical
  let T := numberedData q hq h4
  let K := finiteForgetting q hq h4
  let hG := Alternating.reset_expanded_essential q hq
  have hu : (aut q hq h4).val '' ray (ResetGraph q) alpha n =
      ⋃ r : T.ActualOut alpha n, ray (ResetGraph q) (T.beta hG alpha n r) n :=
    T.numbered_same_cut_whole_ray_image K hG alpha n
  letI : Finite (Parts (ResetGraph q)
    ((aut q hq h4).val '' ray (ResetGraph q) alpha n) n) := (image_atCut q hq h4 alpha n).1
  letI : Finite (Parts (ResetGraph q)
    (⋃ r : T.ActualOut alpha n, ray (ResetGraph q) (T.beta hG alpha n r) n) n) :=
    (atCut_iUnion (ResetGraph q) _ n (fun r => ray_atCut (ResetGraph q) hG _ n)).1
  rw [ResetStandardBeamGeometry.endpointRow_set_congr (ResetGraph q) n hu]
  rw [endpointRow_disjointUnion (ResetGraph q) hG
    (fun r : T.ActualOut alpha n => T.beta hG alpha n r) n
      (fun r s hrs => T.numbered_components_disjoint K hG alpha n hrs)]
  rw [← expanded_adjacency_eq, Matrix.single_vecMul]
  simp only [one_smul, Matrix.row, adjacency]
  apply Finset.sum_congr rfl
  intro r _
  exact congrArg (fun p : Fin q × Sign => (Pi.single p (1 : ℤ) : Fin q × Sign → ℤ))
    (T.numbered_beta_endpoint hG alpha n r)

private theorem transition_square (q : ℕ) (z : VertexModule Sign q) :
    transition (twoStepMatrix q) z = transition (resetMatrix q) (transition (resetMatrix q) z) := by
  change z ᵥ* InertGroupBlockConjugacy.integerMatrix (resetMatrix q * resetMatrix q) =
    (z ᵥ* InertGroupBlockConjugacy.integerMatrix (resetMatrix q)) ᵥ*
      InertGroupBlockConjugacy.integerMatrix (resetMatrix q)
  rw [map_mul, Matrix.vecMul_vecMul]

private theorem image_coordinate (q : ℕ) (hq : 0 < q) (h4 : 4 ∣ q)
    (alpha : ResetHistory q) (N : ℕ) :
    resetBeamCoordinate q (resetImageBeam q hq (aut q hq h4) (resetRayBeam q hq alpha (N : ℤ))) =
      ((LinearMap.id : Module.End ℤ (DimensionGroup (resetMatrix q))) + (resetTheta q)^2)
        (stage (transition (resetMatrix q)) N
          (vertex (endpoint (ResetGraph q) alpha (N : ℤ)).1
            (endpoint (ResetGraph q) alpha (N : ℤ)).2)) := by
  let hG := Alternating.reset_expanded_essential q hq
  let p := endpoint (ResetGraph q) alpha (N : ℤ)
  unfold resetBeamCoordinate
  rw [beamCoordinate_at (ResetGraph q) hG _ (N : ℤ) (image_atCut q hq h4 alpha (N : ℤ))]
  unfold coordinateAt
  rw [resetRowLimitEquiv_intStage, intStage_nat]
  letI : Finite (Parts (ResetGraph q) ((aut q hq h4).val '' ray (ResetGraph q) alpha (N : ℤ)) (N : ℤ)) :=
    (image_atCut q hq h4 alpha (N : ℤ)).1
  change stage (transition (resetMatrix q)) N (NativeIntegralRowTransport.basisEquiv q
    (endpointRow (ResetGraph q) ((aut q hq h4).val '' ray (ResetGraph q) alpha (N : ℤ)) (N : ℤ))) = _
  rw [image_endpointRow]
  change stage (transition (resetMatrix q)) N
    (NativeIntegralRowTransport.basisEquiv q
      (NativeIntegralRowTransport.rowTransition (twoStepCarrier q)
        (NativeIntegralRowTransport.rowVertex p.1 p.2))) = _
  rw [NativeIntegralRowTransport.transport_transition]
  have hv : NativeIntegralRowTransport.basisEquiv q
      (NativeIntegralRowTransport.rowVertex p.1 p.2) = vertex p.1 p.2 := by
    rw [← NativeIntegralRowTransport.decode_vertex]
    exact NativeIntegralRowTransport.encode_decode _
  rw [hv, native_transition_one_add, transition_square, map_add]
  change stage (transition (resetMatrix q)) N (vertex p.1 p.2) +
    stage (transition (resetMatrix q)) N (transition (resetMatrix q)
      (transition (resetMatrix q) (vertex p.1 p.2))) =
    stage (transition (resetMatrix q)) N (vertex p.1 p.2) +
      ((resetTheta q)^2) (stage (transition (resetMatrix q)) N (vertex p.1 p.2))
  rw [pow_two, Module.End.mul_apply]
  change _ = _ + Theta (transition (resetMatrix q))
    (Theta (transition (resetMatrix q)) (stage (transition (resetMatrix q)) N (vertex p.1 p.2)))
  rw [Theta_stage, Theta_stage]

/-- The actual set-image representation on the entire original integer
    two-coefficient colimit equals identity plus two genuine unit times. -/
theorem rho_eq (q : ℕ) (hq : 0 < q) (h4 : 4 ∣ q) :
    (rho q hq (aut q hq h4)).toLinearMap = LinearMap.id + (resetTheta q)^2 := by
  apply ResetFullStandardBeamRepresentation.native_hom_ext q
  intro N
  apply (vertexBasis (H := Sign) (n := q)).ext
  intro p
  rcases p with ⟨i,g⟩
  simp only [LinearMap.comp_apply, ResetFullStandardBeamRepresentation.nativeStage_apply,
    LinearEquiv.coe_toLinearMap, vertexBasis, Pi.basis_apply, MonoidAlgebra.basis_apply]
  let alpha := resetBasisHistory q hq (i,g) (N : ℤ)
  have hray : resetBeamCoordinate q (resetRayBeam q hq alpha (N : ℤ)) =
      stage (transition (resetMatrix q)) N (vertex i g) := by
    rw [resetBeamCoordinate_ray, intStage_nat]
    simp [alpha, resetBasisHistory]
  have him := image_coordinate q hq h4 alpha N
  simp only [alpha, resetBasisHistory, vertexHistory_endpoint] at him
  have he := (rho_beam_image q hq (aut q hq h4) (resetRayBeam q hq alpha (N : ℤ))).trans him
  rw [hray] at he
  exact he

end TwoStep
end D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
