/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeGuardedFreeExtension
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Unique simultaneous guarded extension of arbitrary completed free values. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalEffectivePrefix

/-! Constants and parameter atoms are evaluated in the actual native completion.
The last token denotes Omega. Free states have arbitrary completed values;
no finiteness or rationality condition is imposed on their assignment. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedFreeExtension

open NativeCompletionPrefixLifting CompletionHomogeneousFixedPoints
open NativeFunctionalObstruction
open NativeSymbolicFiniteForcing (specialize nativeSystem specialize_value)

/-- The first k tokens are finite parameter atoms with natural offsets;
the last token is Omega. State occurrences retain their natural decorators. -/
abbrev Expression (k m : Nat) := CompletionPositiveDriftRegion.Expr (k + 1) m

abbrev System (k m : Nat) := Fin m → Option (Expression k m)

def tokenKind (k : Nat) : Fin (k + 1) → Bool := Fin.lastCases false (fun _ => true)

def tokenRank {k : Nat} (p : Fin k → Nat) : Fin (k + 1) → Nat := Fin.lastCases 0 p

def evaluate {k m : Nat} (p : Fin k → Nat) (v : Fin m → CompletionTree)
    (E : Expression k m) : CompletionTree :=
  CompletionPositiveDriftRegion.value (tokenKind k) (tokenRank p) v E

def Satisfies {k m : Nat} (S : System k m) (p : Fin k → Nat)
    (v : Fin m → CompletionTree) : Prop :=
  ∀ i E, S i = some E → v i = evaluate p v E

/-- Root links have been eliminated; a state-dependent right side has an
explicit ordered pair at the root. Constants need no recursive guard. -/
def Guarded {k m : Nat} (S : System k m) : Prop :=
  ∀ i a j, S i ≠ some (.var a j)

/-- Only undefined states are prescribed by the free assignment. -/
def Extends {k m : Nat} (S : System k m) (f v : Fin m → CompletionTree) : Prop :=
  ∀ i, S i = none → v i = f i

private theorem extension_exists {k m : Nat} (S : System k m) (p : Fin k → Nat)
    (f : Fin m → CompletionTree) :
    ∃ v, Satisfies S p v ∧ Extends S f v := by
  classical
  let N := nativeSystem S (tokenKind k) (tokenRank p)
  let B : Fin (m + 1) → Prop := Fin.lastCases True (fun i => S i = none)
  let boundary : Fin (m + 1) → CompletionTree := Fin.lastCases Omega f
  have empty : ∀ i, B i → N i = none := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro _; rfl
    · intro h
      change S j = none at h
      simp only [N, nativeSystem, Fin.lastCases_castSucc, h, Option.map_none]
  obtain ⟨w, sat, same⟩ := whole_system_boundary_extension N B boundary
    (by intro i E hi eq; rw [empty i hi] at eq; cases eq)
    (by intro i E hi eq; rw [empty i hi] at eq; cases eq)
  refine ⟨fun i => w i.castSucc, ?_, ?_⟩
  · intro i E eq
    have law := sat i.castSucc (specialize (tokenKind k) (tokenRank p) E)
      (by simp only [N, nativeSystem, Fin.lastCases_castSucc, eq, Option.map_some])
    exact law.trans (specialize_value _ _ w
      (by exact same (Fin.last m) trivial) E)
  · intro i hi
    exact same i.castSucc hi

private theorem evaluate_cutoff_congr {k m : Nat} (d : Nat) (p : Fin k → Nat)
    {v w : Fin m → CompletionTree} (same : ∀ i, cutoff d (v i) = cutoff d (w i))
    (E : Expression k m) : cutoff d (evaluate p v E) = cutoff d (evaluate p w E) := by
  let v' : Fin (m + 1) → CompletionTree := Fin.lastCases Omega v
  let w' : Fin (m + 1) → CompletionTree := Fin.lastCases Omega w
  have hv := specialize_value (tokenKind k) (tokenRank p) v' rfl E
  have hw := specialize_value (tokenKind k) (tokenRank p) w' rfl E
  change cutoff d (CompletionPositiveDriftRegion.value _ _ v E) =
    cutoff d (CompletionPositiveDriftRegion.value _ _ w E)
  rw [← hv, ← hw, ← NativeFunctionalEffectivePrefix.eval_cutoff,
    ← NativeFunctionalEffectivePrefix.eval_cutoff]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rfl
  · exact same j

/-- Every arbitrary assignment on the undefined states has exactly one
simultaneous extension through the pair-guarded definitions. -/
theorem guarded_extension {k m : Nat} (S : System k m) (p : Fin k → Nat)
    (guarded : Guarded S) (f : Fin m → CompletionTree) :
    ∃! v, Satisfies S p v ∧ Extends S f v := by
  obtain ⟨v, sat, free⟩ := extension_exists S p f
  refine ⟨v, ⟨sat, free⟩, ?_⟩
  intro w hw
  have prefixes : ∀ d i, cutoff d (w i) = cutoff d (v i) := by
    intro d
    induction d with
    | zero => intro i; rfl
    | succ d ih =>
      intro i
      cases eq : S i with
      | none => rw [hw.2 i eq, free i eq]
      | some E =>
        rw [hw.1 i E eq, sat i E eq]
        cases E with
        | ground t => rfl
        | token j c => rfl
        | var a j => exact (guarded i a j eq).elim
        | pair A B =>
          exact congrArg Sum.inr (congrArg₂ Prod.mk
            (evaluate_cutoff_congr d p ih A) (evaluate_cutoff_congr d p ih B))
  funext i
  apply readout_ext
  intro a
  exact (cutoff_readout (a.length + 1) (w i) (v i)).mp
    (prefixes _ i) a (by omega)

end D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedFreeExtension
