/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeEffectiveAtomicGuard
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Executable affine guards for exact atomic observations of guarded completed systems. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeAffineImageSaturation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveAtomicGuard

open NativeCompletionPrefixLifting CompletionHomogeneousFixedPoints
open NativeGuardedFreeExtension NativeGuardedImageSaturation NativeAffineImageSaturation
open NativeGuardedAtomicReplacement
open GenealogicalFiberTransport (Source substitution)
open PresburgerArithmetic

/-- A finite syntactic Boolean constant. -/
def constant (b : Bool) : Formula := .qf (if b then .truth else .falsity)

private theorem constant_holds (b : Bool) (xs : List Int) :
    (constant b).holds xs ↔ b = true := by cases b <;> simp [constant, Formula.holds, QF.eval]

/-- Equality of an original affine index plus a fixed offset to a fixed rank. -/
def rankEquals (a : Affine) (c j : Nat) : Formula :=
  .qf (.and (.atom (.le (a.add (.const ((c : Int) - j)))))
    (.atom (.le (a.neg.add (.const ((j : Int) - c))))))

private theorem rankEquals_holds (a : Affine) (c j : Nat) (xs : List Int)
    (legal : 0 ≤ a.eval xs) :
    (rankEquals a c j).holds xs ↔ (a.eval xs).toNat + c = j := by
  have cast := Int.toNat_of_nonneg legal
  simp only [rankEquals, Formula.holds, QF.eval, Atom.eval, Bool.and_eq_true,
    decide_eq_true_eq, Affine.eval_add, Affine.eval_const, Affine.eval_neg]
  omega

/-- The ground test uses equality of finite native trees, not completed equality. -/
def groundEquals (g : Source) (j : Nat) : Formula :=
  constant (decide (g = substitution^[j] (.of true)))

private theorem groundEquals_holds (g : Source) (j : Nat) (xs : List Int) :
    (groundEquals g j).holds xs ↔ embed g = atomic j := by
  rw [groundEquals, constant_holds, decide_eq_true_eq]
  rw [atomic, show leaf true = embed (.of true) from rfl, iterate_embed]
  exact NativeCompletionSupportClosure.embed_injective.eq_iff.symm

def tokenEquals {n k m : Nat} (I : Input n k m) (j : Fin (k+1)) (c r : Nat) : Formula :=
  Fin.lastCases (constant false) (fun i => rankEquals (I.indices i) c r) j

private theorem tokenEquals_holds {n k m : Nat} (I : Input n k m) (p : Fin n → Nat)
    (legal : Legal I p) (v : Fin m → CompletionTree) (j : Fin (k+1)) (c r : Nat) :
    (tokenEquals I j c r).holds (environment p) ↔
      evaluate (ranks I p) v (.token j c) = atomic r := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [tokenEquals, Fin.lastCases_last, constant_holds, Bool.false_eq_true]
    change False ↔ Omega = atomic r
    exact ⟨False.elim, fun h => CompletionPositiveDriftRegion.omega_not_finite
      (h.symm ▸ CompletionPositiveDriftRegion.atomic_finite r)⟩
  · simp only [tokenEquals, Fin.lastCases_castSucc]
    rw [rankEquals_holds _ _ _ _ (legal.2 i)]
    change ranks I p i + c = r ↔ atomic (ranks I p i + c) = atomic r
    exact CompletionPositiveDriftRegion.atomic_injective.eq_iff.symm

/-- Compare finite expression syntax with a fixed atomic rank. The supplied
state formulas are used only at ranks no larger than the requested one. -/
def expressionAtom {n k m : Nat} (I : Input n k m) (states : Nat → Fin m → Formula) :
    Expression k m → Nat → Formula
  | .ground g, j => groundEquals g j
  | .token i c, j => tokenEquals I i c j
  | .var a i, j => if a ≤ j then states (j-a) i else constant false
  | .pair A B, j => if 2 ≤ j then
      .and (expressionAtom I states A (j-1)) (expressionAtom I states B (j-2))
    else constant false

private theorem expressionAtom_holds {n k m : Nat} (I : Input n k m)
    (p : Fin n → Nat) (legal : Legal I p) (v : Fin m → CompletionTree)
    (states : Nat → Fin m → Formula) (E : Expression k m) (j : Nat)
    (correct : ∀ r, r ≤ j → ∀ i,
      (states r i).holds (environment p) ↔ v i = atomic r) :
    (expressionAtom I states E j).holds (environment p) ↔
      evaluate (ranks I p) v E = atomic j := by
  induction E generalizing j with
  | ground g => exact groundEquals_holds g j _
  | token i c => exact tokenEquals_holds I p legal v i c j
  | var a i =>
    simp only [expressionAtom]
    by_cases h : a ≤ j
    · rw [if_pos h, correct (j-a) (by omega)]
      change v i = atomic (j-a) ↔ rho^[a] (v i) = atomic j
      constructor
      · intro eq
        rw [eq, atomic, ← Function.iterate_add_apply]
        congr 1
        omega
      · intro eq
        obtain ⟨r, rank, value⟩ := atomic_predecessor a j (v i) eq
        have : r = j-a := by omega
        exact this ▸ value
    · rw [if_neg h, constant_holds]
      change False ↔ rho^[a] (v i) = atomic j
      constructor
      · exact False.elim
      · intro eq
        obtain ⟨r, rank, _⟩ := atomic_predecessor a j (v i) eq
        omega
  | pair A B ihA ihB =>
    simp only [expressionAtom]
    by_cases h : 2 ≤ j
    · rw [if_pos h]
      change (_ ∧ _) ↔ node _ _ = atomic j
      rw [ihA (j-1) (fun r hr => correct r (by omega)),
        ihB (j-2) (fun r hr => correct r (by omega))]
      constructor
      · rintro ⟨ha, hb⟩
        rw [ha, hb]
        have rank : j = (j-2)+2 := by omega
        rw [rank, atomic_pair]
        congr 2 <;> omega
      · intro eq
        obtain ⟨r, rank, ha, hb⟩ := pair_atomic eq
        have h1 : r+1 = j-1 := by omega
        have h2 : r = j-2 := by omega
        exact ⟨h1 ▸ ha, h2 ▸ hb⟩
    · rw [if_neg h, constant_holds]
      change False ↔ node _ _ = atomic j
      constructor
      · exact False.elim
      · intro eq
        obtain ⟨r, rank, _, _⟩ := pair_atomic eq
        omega

/-- One state step unfolds only a pair-guarded right side. -/
def stateStep {n k m s : Nat} (I : Input n k m) (mode : Mode s m)
    (lower : Nat → Fin m → Formula) (j : Nat) (i : Fin m) : Formula :=
  match I.equations i with
  | none => match mode i with
    | none => constant false
    | some r => constant (decide (r.val = j))
  | some E => expressionAtom I lower E j

/-- Strong recursion on the requested atomic rank constructs total finite
syntax. Pair roots decrease that rank before any recursive state call. -/
def stateAtom {n k m s : Nat} (I : Input n k m) (mode : Mode s m) (j : Nat) :
    Fin m → Formula :=
  Nat.strongRecOn j fun j rec =>
    stateStep I mode (fun r => if h : r < j then rec r h else fun _ => constant false) j

/-- The complete exact atomic observation formula; it never chooses a
semantic normal form or enumerates the original parameter values. -/
def atomicGuard {n k m s : Nat} (I : Input n k m) (mode : Mode s m)
    (E : Expression k m) (j : Nat) : Formula := expressionAtom I (stateAtom I mode) E j

private theorem stateAtom_holds {n k m s : Nat} (I : Input n k m)
    (guarded : Guarded I.equations) (mode : Mode s m) (p : Fin n → Nat)
    (legal : Legal I p) (v : Fin m → CompletionTree)
    (sat : Satisfies I.equations (ranks I p) v)
    (free : Extends I.equations (canonicalFree mode) v) :
    ∀ j i, (stateAtom I mode j i).holds (environment p) ↔ v i = atomic j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro i
    rw [stateAtom, Nat.strongRecOn_eq]
    change (stateStep I mode _ j i).holds _ ↔ _
    cases eq : I.equations i with
    | none =>
      simp only [stateStep, eq]
      rw [free i eq]
      cases hm : mode i with
      | none =>
        simp only [constant_holds, Bool.false_eq_true, canonicalFree, hm]
        exact ⟨False.elim, fun h => CompletionPositiveDriftRegion.omega_not_finite
          (h.symm ▸ CompletionPositiveDriftRegion.atomic_finite j)⟩
      | some r =>
        simp only [constant_holds, decide_eq_true_eq, canonicalFree, hm]
        exact CompletionPositiveDriftRegion.atomic_injective.eq_iff.symm
    | some E =>
      simp only [stateStep, eq]
      rw [sat i E eq]
      cases E with
      | ground g => exact groundEquals_holds g j _
      | token t c => exact tokenEquals_holds I p legal v t c j
      | var a t => exact (guarded i a t eq).elim
      | pair A B =>
        simp only [expressionAtom]
        by_cases h : 2 ≤ j
        · rw [if_pos h]
          have correct (r : Nat) (hr : r ≤ j-1) (i : Fin m) :
              ((if h : r < j then stateAtom I mode r else fun _ => constant false) i).holds
                (environment p) ↔ v i = atomic r := by
            rw [dif_pos (by omega : r < j)]
            exact ih r (by omega) i
          rw [Formula.holds,
            expressionAtom_holds I p legal v _ A (j-1) correct,
            expressionAtom_holds I p legal v _ B (j-2)
              (fun r hr => correct r (by omega))]
          change (_ ∧ _) ↔ node _ _ = atomic j
          constructor
          · rintro ⟨ha, hb⟩
            rw [ha, hb]
            have rank : j = (j-2)+2 := by omega
            rw [rank, atomic_pair]
            congr 2 <;> omega
          · intro same
            obtain ⟨r, rank, ha, hb⟩ := pair_atomic same
            have h1 : r+1 = j-1 := by omega
            have h2 : r = j-2 := by omega
            exact ⟨h1 ▸ ha, h2 ▸ hb⟩
        · rw [if_neg h, constant_holds]
          change False ↔ node _ _ = atomic j
          constructor
          · exact False.elim
          · intro same
            obtain ⟨r, rank, _, _⟩ := pair_atomic same
            omega

/-- Exact finite Presburger syntax for atomic terminal observations of every
canonical completed output, with the one original affine parameter tuple. -/
theorem atomic_guard_correct {n k m s : Nat} (I : Input n k m)
    (guarded : Guarded I.equations) (mode : Mode s m) (p : Fin n → Nat)
    (legal : Legal I p) (E : Expression k m) (j : Nat) :
    (atomicGuard I mode E j).holds (environment p) ↔
      evaluate (ranks I p) (canonical I.equations (ranks I p) guarded mode) E = atomic j := by
  have law := (normalized_saturation I.equations (ranks I p) guarded []
    (fun _ => none))
  have canonicalLaw := Classical.choose_spec
    (guarded_extension I.equations (ranks I p) guarded (canonicalFree mode)).exists
  exact expressionAtom_holds I p legal _ _ E j
    (fun r _ => stateAtom_holds I guarded mode p legal _ canonicalLaw.1 canonicalLaw.2 r)

end D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveAtomicGuard
