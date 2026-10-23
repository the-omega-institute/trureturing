/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleCompiler
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleCompiler
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact complete-stratum compilation and finite whole-table feasibility. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSimultaneousPrefixSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleCompiler

open GenealogicalFiberTransport (Source substitution)
open NativeFiveHoleFiber
open NativePrefixIdentityReflection (MixedExpr eval)
open NativeUniformResidualRealization (RankedExpr rankedEval uniformSeparator uniform_residual_reflection)
open NativeSimultaneousPrefixSeparation (shift eval_shift)

abbrev Expr := RankedExpr 0 2
def ranks : Fin 0 → Nat := fun i => nomatch i
def tuple (y z : Source) : Fin 2 → Source := ![y,z]
def Y : Expr := .residual 0 (.inr 0)
def Z : Expr := .residual 0 (.inr 1)
def FY : Expr := .pair (.ground (.of true)) (.residual 1 (.inr 0))
def FZ : Expr := .pair (.ground (.of true)) (.residual 1 (.inr 1))
def holes (side : Bool) : Fin 5 → Expr := ![if side then FY else Y,Y,Z,FY,FZ]

/-- The original ordered class representatives, without redundant-negative deletion. -/
def four (side : Bool) : Fin 4 → Expr :=
  if side then ![FY,Y,Z,FZ] else ![Y,Z,FY,FZ]

def six (E : Fin 4 → Expr) : List (Expr × Expr) :=
  [(E 0,E 1),(E 0,E 2),(E 0,E 3),(E 1,E 2),(E 1,E 3),(E 2,E 3)]

/-- Every history occurrence follows the six class comparisons, in supplied order. -/
def table (side : Bool) (H : History) : List (Expr × Expr) :=
  six (four side) ++ (indexedHistory H).val.map (fun e =>
    (shift e.1 (holes side e.2.1), shift e.2.2.1 (holes side e.2.2.2)))

def Negatives (side : Bool) (H : History) (t : Fin 2 → Source) : Prop :=
  ∀ e ∈ table side H, rankedEval ranks t e.1 ≠ rankedEval ranks t e.2

instance negativesDecidable (side : Bool) (H : History) (t : Fin 2 → Source) :
    Decidable (Negatives side H t) :=
  inferInstanceAs (Decidable (∀ e ∈ table side H,
    rankedEval ranks t e.1 ≠ rankedEval ranks t e.2))

private theorem tuple_eta (t : Fin 2 → Source) : tuple (t 0) (t 1) = t := by
  funext i
  fin_cases i <;> rfl

private theorem evaluate_hole (side : Bool) (y z : Source) (i : Fin 5) :
    rankedEval ranks (tuple y z) (holes side i) =
      hole (if side then F y else y) y z i := by
  fin_cases i <;> cases side <;>
    simp [rankedEval,eval,holes,Y,Z,FY,FZ,tuple,hole,F]

private theorem evaluate_shift (a : Nat) (t : Fin 2 → Source) (E : Expr) :
    rankedEval ranks t (shift a E) = substitution^[a] (rankedEval ranks t E) :=
  eval_shift a (Sum.elim (fun j => substitution^[ranks j] (.of true)) t) E

private theorem table_iff (side : Bool) (H : History) (y z : Source) :
    Negatives side H (tuple y z) ↔ Distinct y z ∧ Protected H (source side y z) := by
  have histories : (∀ e ∈ (indexedHistory H).val,
      rankedEval ranks (tuple y z) (shift e.1 (holes side e.2.1)) ≠
        rankedEval ranks (tuple y z) (shift e.2.2.1 (holes side e.2.2.2))) ↔
      Protected H (source side y z) := by
    simp only [evaluate_shift,evaluate_hole]
    unfold Protected
    conv_rhs => rw [← (indexedHistory H).property]
    simp only [List.forall_mem_map,originalRecord,source,Negative,epoch_hole,
      Option.isSome_some,true_and,ne_eq,Option.some.injEq]
  unfold Negatives table
  simp only [List.forall_mem_append,List.forall_mem_map]
  rw [histories]
  apply and_congr ?_ Iff.rfl
  cases side
  · simp [six,four,rankedEval,eval,Y,Z,FY,FZ,tuple,Distinct,F]
  · simp only [six,four,if_true,List.forall_mem_cons,List.forall_mem_singleton,
      rankedEval,eval,Y,Z,FY,FZ,tuple,Matrix.cons_val_zero,Matrix.cons_val_one,
      Sum.elim_inr,Function.iterate_zero,Function.iterate_one,Distinct,F]
    constructor
    · rintro ⟨a,b,c,d,e,f,_⟩
      exact ⟨d,Ne.symm a,e,Ne.symm b,f,c⟩
    · rintro ⟨a,b,c,d,e,f⟩
      refine ⟨Ne.symm b,Ne.symm d,f,a,c,e,?_⟩
      intro q hq
      cases hq

/-- Both directions concern the original full guarded source carrier. -/
theorem stratum_compile_iff (side : Bool) (H : History) (u : Source) :
    Stratum side H u ↔ ∃ t : Fin 2 → Source,
      u = source side (t 0) (t 1) ∧ Negatives side H t := by
  rw [raw_stratum_iff]
  constructor
  · rintro ⟨y,z,eq,d,hist⟩
    exact ⟨tuple y z,eq,(table_iff side H y z).mpr ⟨d,hist⟩⟩
  · rintro ⟨t,eq,neg⟩
    have both := (table_iff side H (t 0) (t 1)).mp (by rwa [tuple_eta])
    exact ⟨t 0,t 1,eq,both⟩

/-- Failure of the test excludes every tuple, rather than only the separator. -/
theorem separator_exact (side : Bool) (H : History) :
    Negatives side H (uniformSeparator (table side H)) ↔
      ∃ t : Fin 2 → Source, Negatives side H t := by
  constructor
  · intro h; exact ⟨uniformSeparator (table side H),h⟩
  · rintro ⟨t,neg⟩ e he eq
    exact neg e he ((uniform_residual_reflection 0 2 (table side H) ranks e he).mp eq t)

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleCompiler
