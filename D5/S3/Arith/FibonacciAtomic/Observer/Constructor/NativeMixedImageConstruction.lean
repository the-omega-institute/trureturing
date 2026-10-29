/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Concrete expression naming and unrestricted mixed ambient-code assembly. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativePositiveBranchReduction
import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeMixedImageConstruction

open GenealogicalFiberTransport (Source substitution)
open NativePrefixIdentityReflection (MixedExpr eval)
open NativeUniformResidualRealization (RankedExpr rankedEval)
open NativeFiniteNormalInversion (Code expand encode shiftCode)
open NativePositiveBranchReduction (Equation BranchEquation)

variable {X : Type}

/-- Inputs and expression names occupy disjoint namespaces. -/
abbrev Name (X : Type) := X ⊕ MixedExpr X

def root (e : MixedExpr X) : Name X := .inr e

/-- Ground trees are expanded into their actual finite native constructors. -/
def groundDefinitions : Source → List (Equation (Name X))
  | .of true => [.primitive (root (.ground (.of true))) 0]
  | .of false => [.primitive (root (.ground (.of false))) 1]
  | .mul l r => groundDefinitions l ++ groundDefinitions r ++
      [.pair (root (.ground (.mul l r))) (root (.ground l)) (root (.ground r))]

/-- Every occurrence of the same expression reuses the same name. -/
def definitions : MixedExpr X → List (Equation (Name X))
  | .ground g => groundDefinitions g
  | .residual a x => [.shift (root (.residual a x)) a (.inl x)]
  | .pair l r => definitions l ++ definitions r ++
      [.pair (root (.pair l r)) (root l) (root r)]

def flatten (E : List (MixedExpr X × MixedExpr X)) : List (Equation (Name X)) :=
  E.flatMap fun e => definitions e.1 ++ definitions e.2 ++ [.same (root e.1) (root e.2)]

def extend (v : X → Source) : Name X → Source := Sum.elim v (eval v)

private theorem ground_value (w : Name X → Source) (g : Source)
    (h : ∀ e ∈ groundDefinitions g, e.Holds w) : w (root (.ground g)) = g := by
  induction g with
  | of b => cases b <;> exact h _ (by simp [groundDefinitions])
  | mul l r hl hr =>
      have left := hl (fun e he => h e (by simp [groundDefinitions, he]))
      have right := hr (fun e he => h e (by simp [groundDefinitions, he]))
      have head := h (.pair (root (.ground (.mul l r))) (root (.ground l))
        (root (.ground r))) (by simp [groundDefinitions])
      change w (root (.ground (.mul l r))) = .mul _ _ at head
      simpa only [left, right] using head

private theorem definition_value (w : Name X → Source) (e : MixedExpr X)
    (h : ∀ q ∈ definitions e, q.Holds w) :
    w (root e) = eval (fun x => w (.inl x)) e := by
  induction e with
  | ground g => exact ground_value w g h
  | residual a x => exact h _ (by simp [definitions])
  | pair l r hl hr =>
      have left := hl (fun q hq => h q (by simp [definitions, hq]))
      have right := hr (fun q hq => h q (by simp [definitions, hq]))
      have head := h (.pair (root (.pair l r)) (root l) (root r))
        (by simp [definitions])
      change w (root (.pair l r)) = .mul _ _ at head
      simpa only [left, right, eval] using head

private theorem ground_definitions_hold (v : X → Source) (g : Source) :
    ∀ q ∈ groundDefinitions g, q.Holds (extend v) := by
  induction g with
  | of b => cases b <;> simp [groundDefinitions, Equation.Holds, extend, root, eval, expand,
      GenealogicalFiberTransport.substitution]
  | mul l r hl hr =>
      intro q hq
      simp only [groundDefinitions, List.mem_append, List.mem_singleton] at hq
      rcases hq with (hq | hq) | rfl
      · exact hl q hq
      · exact hr q hq
      · rfl

private theorem definitions_hold (v : X → Source) (e : MixedExpr X) :
    ∀ q ∈ definitions e, q.Holds (extend v) := by
  induction e with
  | ground g => exact ground_definitions_hold v g
  | residual a x => intro q hq; simpa only [definitions, List.mem_singleton] using hq ▸ (rfl : Equation.Holds (extend v) (.shift (root (.residual a x)) a (.inl x)))
  | pair l r hl hr =>
      intro q hq
      simp only [definitions, List.mem_append, List.mem_singleton] at hq
      rcases hq with (hq | hq) | rfl
      · exact hl q hq
      · exact hr q hq
      · rfl

/-- Lowering preserves the same original assignment, including unused inputs. -/
theorem flatten_exact (E : List (MixedExpr X × MixedExpr X)) (v : X → Source) :
    (∀ e ∈ E, eval v e.1 = eval v e.2) ↔
      ∀ q ∈ flatten E, q.Holds (extend v) := by
  constructor
  · intro h q hq
    obtain ⟨e, he, hq⟩ := List.mem_flatMap.mp hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with (hq | hq) | rfl
    · exact definitions_hold v e.1 q hq
    · exact definitions_hold v e.2 q hq
    · exact h e he
  · intro h e he
    exact h (.same (root e.1) (root e.2))
      (List.mem_flatMap.mpr ⟨e, he, by simp⟩)

private theorem flatten_sound (E : List (MixedExpr X × MixedExpr X))
    (w : Name X → Source) (h : ∀ q ∈ flatten E, q.Holds w) :
    ∀ e ∈ E, eval (fun x => w (.inl x)) e.1 = eval (fun x => w (.inl x)) e.2 := by
  intro e he
  have sub (q : Equation (Name X)) (hq : q ∈ definitions e.1 ++ definitions e.2 ++
      [.same (root e.1) (root e.2)]) := h q (List.mem_flatMap.mpr ⟨e, he, hq⟩)
  have left := definition_value w e.1 (fun q hq => sub q (by simp [hq]))
  have right := definition_value w e.2 (fun q hq => sub q (by simp [hq]))
  have eq := sub (.same (root e.1) (root e.2)) (by simp)
  exact left.symm.trans (eq.trans right)

private theorem origins (E : List (Equation X)) (B : List (BranchEquation X))
    (h : B ∈ NativePositiveBranchReduction.branches E) : B.map BranchEquation.origin = E := by
  induction E generalizing B with
  | nil => simpa only [NativePositiveBranchReduction.branches, List.mem_singleton] using h
  | cons e E ih =>
      obtain ⟨b, hb, rest⟩ := List.mem_flatMap.mp h
      obtain ⟨B, hB, rfl⟩ := List.mem_map.mp rest
      simp only [List.map_cons, NativePositiveBranchReduction.choices_origin e b hb, ih B hB]

/-- Arbitrary ambient branch solutions expand to solutions of the original expressions.
There is no normality, shape separation, injectivity, or size hypothesis. -/
theorem flatten_expansion_sound (E : List (MixedExpr X × MixedExpr X))
    (B : List (BranchEquation (Name X)))
    (hB : B ∈ NativePositiveBranchReduction.branches (flatten E))
    (u : Name X → Code) (hu : ∀ b ∈ B, b.Holds u) :
    ∀ e ∈ E, eval (fun x => expand (u (.inl x))) e.1 =
      eval (fun x => expand (u (.inl x))) e.2 := by
  apply flatten_sound E (fun x => expand (u x))
  intro q hq
  rw [← origins _ _ hB] at hq
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
  exact NativePositiveBranchReduction.branch_sound u b (hu b hb)

/-- Finite affine rank atoms; all coefficients are integral. -/
inductive Scalar (k : Nat) where
  | constant : Nat → Scalar k
  | parameter : Fin k → Nat → Scalar k

def Scalar.value {k : Nat} (n : Fin k → Nat) : Scalar k → Nat
  | .constant c => c
  | .parameter i a => n i + a

/-- A block is an unrestricted native parameter with a fixed natural offset. -/
inductive Pattern (k m : Nat) where
  | scalar : Scalar k → Pattern k m
  | block : Fin m → Nat → Pattern k m
  | pair : Pattern k m → Pattern k m → Pattern k m

def Pattern.code {k m : Nat} (n : Fin k → Nat) (z : Fin m → Source) : Pattern k m → Code
  | .scalar r => .of (r.value n)
  | .block i a => shiftCode a (encode (z i))
  | .pair l r => .mul (l.code n z) (r.code n z)

def Pattern.template {k m : Nat} : Pattern k m → RankedExpr k m
  | .scalar (.constant c) => .ground (expand (.of c))
  | .scalar (.parameter i a) => .residual a (.inl i)
  | .block i a => .residual a (.inr i)
  | .pair l r => .pair l.template r.template

private theorem pattern_expansion {k m : Nat} (n : Fin k → Nat) (z : Fin m → Source)
    (t : Pattern k m) : expand (t.code n z) = rankedEval n z t.template := by
  induction t with
  | scalar r =>
      cases r with
      | constant c => rfl
      | parameter i a =>
          change substitution^[n i + a] (.of true) = substitution^[a] (substitution^[n i] (.of true))
          rw [Nat.add_comm (n i) a, Function.iterate_add_apply]
  | block i a =>
      change expand (shiftCode a (encode (z i))) = substitution^[a] (z i)
      rw [NativeFiniteNormalInversion.shift_expand, (NativeFiniteNormalInversion.encode_law _).2]
  | pair l r hl hr => exact congrArg₂ FreeMagma.mul hl hr

/-- Each successful guard is a conjunction of affine integer equalities in n alone. -/
abbrev Guard (k : Nat) := List (Scalar k × Scalar k)

def Guard.Holds {k : Nat} (g : Guard k) (n : Fin k → Nat) : Prop :=
  ∀ e ∈ g, (e.1.value n : Int) = (e.2.value n : Int)

/-- Compare finite decorated shapes; distinct sorts remain independent. -/
def compare {k m : Nat} : Pattern k m → Pattern k m → Option (Guard k)
  | .scalar r, .scalar s => some [(r,s)]
  | .block i a, .block j b => if i = j ∧ a = b then some [] else none
  | .pair l r, .pair s t => do
      let a ← compare l s
      let b ← compare r t
      pure (a ++ b)
  | _, _ => none

private theorem compare_sound {k m : Nat} (A C : Pattern k m) (g : Guard k)
    (hg : compare A C = some g) (n : Fin k → Nat) (hn : g.Holds n)
    (z : Fin m → Source) : A.code n z = C.code n z := by
  induction A generalizing C g with
  | scalar a =>
      cases C with
      | scalar c =>
          have eq : [(a,c)] = g := Option.some.inj hg
          subst g
          have h := hn (a,c) (by simp)
          exact congrArg FreeMagma.of (Int.ofNat_inj.mp h)
      | block i b => cases hg
      | pair l r => cases hg
  | block i a =>
      cases C with
      | scalar c => cases hg
      | pair l r => cases hg
      | block j b =>
          simp only [compare] at hg
          split_ifs at hg with h
          · rcases h with ⟨rfl,rfl⟩; rfl
          · cases hg
  | pair l r hl hr =>
      cases C with
      | scalar c => cases hg
      | block j b => cases hg
      | pair s t =>
          simp only [compare, Option.bind_eq_some_iff, Option.pure_def] at hg
          obtain ⟨a, ha, b, hb, eq⟩ := hg
          have eq : a ++ b = g := Option.some.inj eq
          subst g
          exact congrArg₂ FreeMagma.mul
            (hl s a ha (fun e he => hn e (List.mem_append_left _ he)))
            (hr t b hb (fun e he => hn e (List.mem_append_right _ he)))

end D5.S3.Arith.FibonacciAtomic.Observer.NativeMixedImageConstruction
