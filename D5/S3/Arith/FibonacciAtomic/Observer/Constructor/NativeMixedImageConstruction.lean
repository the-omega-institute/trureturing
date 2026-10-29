/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Concrete expression naming and unrestricted mixed ambient-code assembly. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativePositiveBranchReduction
import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization

/-! Native expression lowering and unrestricted ambient template comparison. -/

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
  | of b =>
      cases b with
      | false => exact h (.primitive (root (.ground (.of false))) 1) (by simp [groundDefinitions])
      | true => exact h (.primitive (root (.ground (.of true))) 0) (by simp [groundDefinitions])
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
  | residual a x => exact h (.shift (root (.residual a x)) a (.inl x)) (by simp [definitions])
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
  | residual a x =>
      intro q hq
      simp only [definitions, List.mem_singleton] at hq
      subst q
      rfl
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

/-- The actual finite branch list is constructed directly from the original expression list. -/
theorem expression_branch_exact (E : List (MixedExpr X × MixedExpr X)) (v : X → Source) :
    (∀ e ∈ E, eval v e.1 = eval v e.2) ↔
      ∃ B ∈ NativePositiveBranchReduction.branches (flatten E),
        ∀ b ∈ B, b.Holds (fun x => encode (extend v x)) := by
  rw [flatten_exact E v]
  exact NativePositiveBranchReduction.branches_exact (flatten E) (extend v)

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
  | nil =>
      simp only [NativePositiveBranchReduction.branches, List.mem_singleton] at h
      subst B
      rfl
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

/-- The decoration has exactly the leaves of the supplied free shape.
An explicit leaf carries a scalar; a residual occurrence carries its native sort and offset. -/
def Decoration (k m : Nat) : NativeTermUnification.Term X → Type
  | .of (.inl _) => Scalar k
  | .of (.inr _) => Fin m × Nat
  | .mul l r => Decoration k m l × Decoration k m r

/-- Assemble every original and auxiliary name by recursion on its actual free-shape term. -/
def assemble {k m : Nat} : (s : NativeTermUnification.Term X) → Decoration k m s → Pattern k m
  | .of (.inl _), r => .scalar r
  | .of (.inr _), b => .block b.1 b.2
  | .mul l r, d => .pair (assemble l d.1) (assemble r d.2)

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
          change substitution^[n i + a] (.of true) =
            substitution^[a] (substitution^[n i] (.of true))
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
          by_cases h : i = j ∧ a = b
          · rcases h with ⟨rfl,rfl⟩; rfl
          · simp [compare, h] at hg
  | pair l r hl hr =>
      cases C with
      | scalar c => cases hg
      | block j b => cases hg
      | pair s t =>
          change ((compare l s).bind fun a =>
            (compare r t).bind fun b => some (a ++ b)) = some g at hg
          simp only [Option.bind_eq_some_iff, Option.some.injEq] at hg
          obtain ⟨a, ha, b, hb, eq⟩ := hg
          subst g
          exact congrArg₂ FreeMagma.mul
            (hl s a ha (fun e he => hn e (List.mem_append_left _ he)))
            (hr t b hb (fun e he => hn e (List.mem_append_right _ he)))

/-- Translation is performed on the finite syntax, before native parameters are filled. -/
def Scalar.shift {k : Nat} (a : Nat) : Scalar k → Scalar k
  | .constant c => .constant (c + a)
  | .parameter i c => .parameter i (c + a)

def Pattern.shift {k m : Nat} (a : Nat) : Pattern k m → Pattern k m
  | .scalar r => .scalar (r.shift a)
  | .block i b => .block i (a + b)
  | .pair l r => .pair (l.shift a) (r.shift a)

private theorem shift_code {k m : Nat} (a : Nat) (t : Pattern k m)
    (n : Fin k → Nat) (z : Fin m → Source) :
    (t.shift a).code n z = shiftCode a (t.code n z) := by
  induction t with
  | scalar r => cases r <;> simp [Pattern.shift, Scalar.shift, Pattern.code,
      Scalar.value, shiftCode, Nat.add_assoc]
  | block i b =>
      exact (NativePositiveBranchReduction.shift_add a b (encode (z i))).symm
  | pair l r hl hr => exact congrArg₂ FreeMagma.mul hl hr

/-- Collapse ranks are explicit natural parameters, shared across its three comparisons. -/
def branchComparisons {k m : Nat} (t : X → Pattern k m)
    (c : BranchEquation X → Scalar k) (b : BranchEquation X) :
    List (Pattern k m × Pattern k m) :=
  match b with
  | .primitive x a => [(t x, .scalar (.constant a))]
  | .shift x a y => [(t x, (t y).shift a)]
  | .ordinary x y z => [(t x, .pair (t y) (t z))]
  | .same x y => [(t x, t y)]
  | .collapse x y z =>
      [(t y, .scalar ((c b).shift 1)),
       (t z, .scalar (c b)),
       (t x, .scalar ((c b).shift 2))]

def collect {k m : Nat} : List (Pattern k m × Pattern k m) → Option (Guard k)
  | [] => some []
  | (a,b) :: rest => do
      let g ← compare a b
      let h ← collect rest
      pure (g ++ h)

private theorem collect_sound {k m : Nat} (L : List (Pattern k m × Pattern k m))
    (g : Guard k) (hg : collect L = some g) (n : Fin k → Nat) (hn : g.Holds n)
    (z : Fin m → Source) : ∀ p ∈ L, p.1.code n z = p.2.code n z := by
  induction L generalizing g with
  | nil => intro p hp; cases hp
  | cons p L ih =>
      change ((compare p.1 p.2).bind fun a =>
        (collect L).bind fun b => some (a ++ b)) = some g at hg
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact compare_sound q.1 q.2 a ha n
          (fun e he => hn e (List.mem_append_left _ he)) z
      · exact ih b hb (fun e he => hn e (List.mem_append_right _ he)) q hq

private theorem comparisons_branch {k m : Nat} (t : X → Pattern k m)
    (c : BranchEquation X → Scalar k) (b : BranchEquation X)
    (n : Fin k → Nat) (z : Fin m → Source)
    (h : ∀ p ∈ branchComparisons t c b, p.1.code n z = p.2.code n z) :
    b.Holds (fun x => (t x).code n z) := by
  cases b with
  | primitive x a => exact h _ (List.mem_singleton_self _)
  | shift x a y =>
      have eq := h _ (List.mem_singleton_self _)
      exact eq.trans (shift_code a (t y) n z)
  | ordinary x y z => exact h _ (List.mem_singleton_self _)
  | same x y => exact h _ (List.mem_singleton_self _)
  | collapse x y w =>
      have scalar_shift (r : Scalar k) (a : Nat) :
          (r.shift a).value n = r.value n + a := by
        cases r <;> simp [Scalar.shift, Scalar.value, Nat.add_assoc]
      refine ⟨(c (.collapse x y w)).value n, ?_, ?_, ?_⟩
      · simpa only [Pattern.code, scalar_shift] using
          h (t y, .scalar ((c (.collapse x y w)).shift 1)) (by simp [branchComparisons])
      · exact h (t w, .scalar (c (.collapse x y w))) (by simp [branchComparisons])
      · simpa only [Pattern.code, scalar_shift] using
          h (t x, .scalar ((c (.collapse x y w)).shift 2)) (by simp [branchComparisons])

/-- Successful finite comparison extraction yields an image sound for every native filling.
The arithmetic domain depends only on natural scalar parameters. -/
theorem guarded_mixed_sound {k m : Nat} (E : List (MixedExpr X × MixedExpr X))
    (B : List (BranchEquation (Name X)))
    (hB : B ∈ NativePositiveBranchReduction.branches (flatten E))
    (s : Name X → NativeTermUnification.Term (Name X))
    (d : ∀ x, Decoration k m (s x)) (c : BranchEquation (Name X) → Scalar k)
    (g : Guard k)
    (hg : collect (B.flatMap (branchComparisons (fun x => assemble (s x) (d x)) c)) = some g)
    (n : Fin k → Nat) (hn : g.Holds n) (z : Fin m → Source) :
    ∀ e ∈ E, eval (fun x => rankedEval n z (assemble (s (.inl x)) (d (.inl x))).template) e.1 =
      eval (fun x => rankedEval n z (assemble (s (.inl x)) (d (.inl x))).template) e.2 := by
  let t : Name X → Pattern k m := fun x => assemble (s x) (d x)
  have comparisons := collect_sound _ g hg n hn z
  have branch : ∀ b ∈ B, b.Holds (fun x => (t x).code n z) := by
    intro b hb
    apply comparisons_branch t c b n z
    intro p hp
    exact comparisons p (List.mem_flatMap.mpr ⟨b,hb,hp⟩)
  have sound := flatten_expansion_sound E B hB (fun x => (t x).code n z) branch
  simpa only [pattern_expansion] using sound

end D5.S3.Arith.FibonacciAtomic.Observer.NativeMixedImageConstruction
