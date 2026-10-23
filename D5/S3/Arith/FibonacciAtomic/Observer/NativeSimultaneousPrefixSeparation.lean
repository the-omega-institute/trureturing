/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeSimultaneousPrefixSeparation
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: One independent finite frontier filling preserves every listed native nonidentity. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation

open GenealogicalFiberTransport (Source substitution)
open NativePrefixIdentityReflection
open NativeUniformResidualRealization
open NativeDepthPatterns (Pattern Frontier fill decompose depthEquiv)
open scoped BigOperators

/-- Push an interpreted native substitution through the actual expression. -/
def shift {ι : Type} (a : Nat) : MixedExpr ι → MixedExpr ι
  | .ground g => .ground (substitution^[a] g)
  | .residual b i => .residual (a + b) i
  | .pair A B => .pair (shift a A) (shift a B)

/-- Every occurrence of one original name reuses the same context. -/
def bind {ι κ : Type} (contexts : ι → MixedExpr κ) : MixedExpr ι → MixedExpr κ
  | .ground g => .ground g
  | .residual a i => shift a (contexts i)
  | .pair A B => .pair (bind contexts A) (bind contexts B)

theorem eval_shift {ι : Type} (a : Nat) (z : ι → Source) (E : MixedExpr ι) :
    eval z (shift a E) = substitution^[a] (eval z E) := by
  induction E with
  | ground g => rfl
  | residual b i => exact Function.iterate_add_apply substitution a b (z i)
  | pair A B ihA ihB =>
      change FreeMagma.mul _ _ = _
      rw [ihA,ihB]
      exact (Function.Semiconj₂.iterate
        (fun s t => substitution.map_mul s t) a (eval z A) (eval z B)).symm

theorem eval_bind {ι κ : Type} (contexts : ι → MixedExpr κ)
    (z : κ → Source) (E : MixedExpr ι) :
    eval z (bind contexts E) = eval (fun i => eval z (contexts i)) E := by
  induction E with
  | ground g => rfl
  | residual a i => exact eval_shift a z (contexts i)
  | pair A B ihA ihB => exact congrArg₂ FreeMagma.mul ihA ihB

/-- The number of reached holes, with no holes below early terminal leaves. -/
def holeCount : {d : Nat} → Pattern d → Nat
  | 0, _ => 1
  | _ + 1, .inl _ => 0
  | _ + 1, .inr p => holeCount p.1 + holeCount p.2

/-- Recursive executable hole numbering uses left holes before right holes. -/
def holeEquiv : {d : Nat} → (p : Pattern d) → Frontier p ≃ Fin (holeCount p)
  | 0, _ => {
      toFun := fun _ => ⟨0,by change 0 < 1; decide⟩
      invFun := fun _ => ()
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by
        apply Fin.ext
        have hx := x.isLt
        change x.val < 1 at hx
        simp only
        omega }
  | _ + 1, .inl _ => {
      toFun := fun x => nomatch x
      invFun := fun x => nomatch x
      left_inv := fun x => nomatch x
      right_inv := fun x => nomatch x }
  | _ + 1, .inr p => (Equiv.sumCongr (holeEquiv p.1) (holeEquiv p.2)).trans finSumFinEquiv

/-- Sum over original coordinates; zero coordinates and zero holes are included. -/
def totalHoles {m : Nat} (d : Fin m → Nat) (p : (i : Fin m) → Pattern (d i)) : Nat :=
  ∑ i, holeCount (p i)

/-- Separate coordinates and their separate reached holes have separate names. -/
def holeNumbering {m : Nat} (d : Fin m → Nat) (p : (i : Fin m) → Pattern (d i)) :
    ((i : Fin m) × Frontier (p i)) ≃ Fin (totalHoles d p) :=
  (Equiv.sigmaCongrRight (fun i => holeEquiv (p i))).trans finSigmaFinEquiv

/-- A native context contains concrete early leaves and one residual per hole. -/
def patternExpr {ι : Type} : {d : Nat} → (p : Pattern d) →
    (Frontier p → ι) → MixedExpr ι
  | 0, _, names => .residual 0 (names ())
  | _ + 1, .inl b, _ => .ground (.of b)
  | _ + 1, .inr p, names => .pair
      (patternExpr p.1 (fun x => names (.inl x)))
      (patternExpr p.2 (fun x => names (.inr x)))

private theorem eval_patternExpr {ι : Type} {d : Nat} (p : Pattern d)
    (names : Frontier p → ι) (z : ι → Source) :
    eval z (patternExpr p names) = fill p (fun x => z (names x)) := by
  induction d with
  | zero => rfl
  | succ d ih => cases p with
    | inl b => rfl
    | inr p => exact congrArg₂ FreeMagma.mul (ih p.1 _) (ih p.2 _)

/-- Finite residual coordinates are fixed while all other coordinates vary. -/
def fixedEval {k r m : Nat} (n : Fin k → Nat) (f : Fin r → Source)
    (z : Fin m → Source) (E : RankedExpr k (r + m)) : Source :=
  rankedEval n (Sum.elim f z ∘ finSumFinEquiv.symm) E

/-- Instantiate fixed ranks and finite coordinates, preserving every decoration. -/
def fixedExpr {k r m : Nat} (n : Fin k → Nat) (f : Fin r → Source)
    (E : RankedExpr k (r + m)) : MixedExpr (Fin m) :=
  bind (fun i => match finSumFinEquiv.symm i with
    | .inl j => .ground (f j)
    | .inr j => .residual 0 j) (instantiate n E)

private theorem eval_fixedExpr {k r m : Nat} (n : Fin k → Nat) (f : Fin r → Source)
    (z : Fin m → Source) (E : RankedExpr k (r + m)) :
    eval z (fixedExpr n f E) = fixedEval n f z E := by
  rw [fixedExpr,eval_bind]
  have valuation : (fun i : Fin (r + m) => eval z (match finSumFinEquiv.symm i with
      | .inl j => .ground (f j)
      | .inr j => .residual 0 j)) = Sum.elim f z ∘ finSumFinEquiv.symm := by
    funext i
    cases h : (finSumFinEquiv.symm i : Fin r ⊕ Fin m) <;>
      simp [eval,h,Function.comp_def]
  rw [valuation]
  exact instantiate_eval n (Sum.elim f z ∘ finSumFinEquiv.symm) E

/-- Substitute all original live coordinates by their independent native patterns. -/
def expanded {k r m : Nat} (n : Fin k → Nat) (f : Fin r → Source)
    (d : Fin m → Nat) (p : (i : Fin m) → Pattern (d i))
    (E : RankedExpr k (r + m)) : RankedExpr 0 (totalHoles d p) :=
  bind (fun i => patternExpr (p i) (fun x => Sum.inr (holeNumbering d p ⟨i,x⟩)))
    (fixedExpr n f E)

private theorem expanded_eval {k r m : Nat} (n : Fin k → Nat) (f : Fin r → Source)
    (d : Fin m → Nat) (p : (i : Fin m) → Pattern (d i))
    (E : RankedExpr k (r + m)) (w : Fin (totalHoles d p) → Source) :
    rankedEval (fun x : Fin 0 => nomatch x) w (expanded n f d p E) =
      fixedEval n f (fun i => fill (p i) (fun x => w (holeNumbering d p ⟨i,x⟩))) E := by
  unfold rankedEval expanded
  rw [eval_bind]
  simp only [eval_patternExpr,Sum.elim_inr]
  exact eval_fixedExpr n f _ E

/-- The entire list is expanded together; duplicates are not removed. -/
def expandedList {k r m : Nat} (n : Fin k → Nat) (f : Fin r → Source)
    (d : Fin m → Nat) (p : (i : Fin m) → Pattern (d i))
    (pairs : List (RankedExpr k (r + m) × RankedExpr k (r + m))) :
    List (RankedExpr 0 (totalHoles d p) × RankedExpr 0 (totalHoles d p)) :=
  pairs.map (fun e => (expanded n f d p e.1,expanded n f d p e.2))

/-- One computable tuple fills every coordinate using the same separator list. -/
def prefixTuple {k r m : Nat} (n : Fin k → Nat) (f : Fin r → Source)
    (d : Fin m → Nat) (p : (i : Fin m) → Pattern (d i))
    (pairs : List (RankedExpr k (r + m) × RankedExpr k (r + m))) (i : Fin m) : Source :=
  fill (p i) (fun x => uniformSeparator (expandedList n f d p pairs) (holeNumbering d p ⟨i,x⟩))

/-- The independent live-pattern construction keeps fixed coordinates and an
arbitrary rank policy, and avoids a whole finite list with one common filling. -/
theorem simultaneous_prefix_separation (k r m : Nat)
    (pairs : List (RankedExpr k (r + m) × RankedExpr k (r + m)))
    (P : (Fin k → Nat) → Prop) (n : Fin k → Nat) (f : Fin r → Source)
    (d : Fin m → Nat) (p : (i : Fin m) → Pattern (d i))
    (live : ∀ i, Nonempty (Frontier (p i))) :
    (∃ z : Fin m → Source, P n ∧ ∀ e ∈ pairs,
      fixedEval n f z e.1 ≠ fixedEval n f z e.2) ↔
    P n ∧ (∀ i, (decompose (d i) (prefixTuple n f d p pairs i)).1 = p i) ∧
      ∀ e ∈ pairs, fixedEval n f (prefixTuple n f d p pairs) e.1 ≠
        fixedEval n f (prefixTuple n f d p pairs) e.2 := by
  classical
  constructor
  · rintro ⟨z,policy,negatives⟩
    have nonidentities : ∀ e ∈ pairs,
        ∃ w : Fin (totalHoles d p) → Source,
          rankedEval (fun x : Fin 0 => nomatch x) w (expanded n f d p e.1) ≠
            rankedEval (fun x : Fin 0 => nomatch x) w (expanded n f d p e.2) := by
      intro e he
      by_contra hn
      have universal : ∀ w : Fin (totalHoles d p) → Source,
          rankedEval (fun x : Fin 0 => nomatch x) w (expanded n f d p e.1) =
            rankedEval (fun x : Fin 0 => nomatch x) w (expanded n f d p e.2) := by
        simpa only [not_exists,not_not] using hn
      have cylinder : ∀ w : (i : Fin m) → Frontier (p i) → Source,
          eval (fun i => fill (p i) (w i)) (fixedExpr n f e.1) =
            eval (fun i => fill (p i) (w i)) (fixedExpr n f e.2) := by
        intro w
        have eq := universal (fun x =>
          w ((holeNumbering d p).symm x).1 ((holeNumbering d p).symm x).2)
        simp only [expanded_eval] at eq
        have recovered : (fun i => fill (p i) (fun x =>
            w ((holeNumbering d p).symm ((holeNumbering d p) ⟨i,x⟩)).1
              ((holeNumbering d p).symm ((holeNumbering d p) ⟨i,x⟩)).2)) =
            (fun i => fill (p i) (w i)) := by
          funext i
          congr 1
          funext x
          exact congrArg (fun y : (j : Fin m) × Frontier (p j) => w y.1 y.2)
            ((holeNumbering d p).symm_apply_apply ⟨i,x⟩)
        rw [recovered] at eq
        simpa only [eval_fixedExpr] using eq
      have global := prefix_identity_reflection m d p live (fixedExpr n f e.1)
        (fixedExpr n f e.2) cylinder z
      exact negatives e he (by simpa only [eval_fixedExpr] using global)
    have each : ∀ q ∈ expandedList n f d p pairs,
        ∃ w : Fin (totalHoles d p) → Source,
          rankedEval (fun x : Fin 0 => nomatch x) w q.1 ≠
            rankedEval (fun x : Fin 0 => nomatch x) w q.2 := by
      intro q hq
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hq
      exact nonidentities e he
    have simultaneous := (simultaneous_completion 0 (totalHoles d p)
      (expandedList n f d p pairs) (fun x => nomatch x)).mp each
    refine ⟨policy,?_,?_⟩
    · intro i
      have back := (depthEquiv (d i)).apply_symm_apply
        (⟨p i,fun x => uniformSeparator (expandedList n f d p pairs) (holeNumbering d p ⟨i,x⟩)⟩)
      exact congrArg Sigma.fst back
    · intro e he
      have member : (expanded n f d p e.1,expanded n f d p e.2) ∈ expandedList n f d p pairs :=
        List.mem_map.mpr ⟨e,he,rfl⟩
      change fixedEval n f (fun i => fill (p i) (fun x =>
        uniformSeparator (expandedList n f d p pairs) (holeNumbering d p ⟨i,x⟩))) e.1 ≠
        fixedEval n f (fun i => fill (p i) (fun x =>
        uniformSeparator (expandedList n f d p pairs) (holeNumbering d p ⟨i,x⟩))) e.2
      simpa only [expanded_eval] using simultaneous _ member
  · rintro ⟨policy,_,negatives⟩
    exact ⟨prefixTuple n f d p pairs,policy,negatives⟩

#print axioms simultaneous_prefix_separation

end D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation
