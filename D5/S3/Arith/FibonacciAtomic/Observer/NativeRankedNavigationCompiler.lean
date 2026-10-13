/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedNavigationCompiler
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Guarded native suffix navigation and joint rank-only Presburger records. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedEqualityCompiler
import D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedNavigationCompiler

open GenealogicalFiberTransport (Source substitution)
open ActualLeafHistoryRigidity (subtree)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativePrefixIdentityReflection (MixedExpr eval kappa kappa_iterate)
open NativeUniformResidualRealization (RankedExpr rankedEval)
open NativeRankedEqualityCompiler (equalityFormula ranked_equality_compilation)
open FirstOrder.Language

/-- Left edges cost one rank and right edges cost two. -/
def pathCost : Address → Nat
  | [] => 0
  | b :: p => (if b then 2 else 1) + pathCost p

/-- Every edge requires a branch, including a final left edge. -/
def pathThreshold : Address → Nat
  | [] => 0
  | b :: p => max 2 ((if b then 2 else 1) + pathThreshold p)

theorem atomic_navigation (p : Address) (t : Nat) (u : Source) :
    subtree p (substitution^[t] (.of true)) = some u ↔
      ∃ r : Nat, pathThreshold p ≤ t ∧ t = r + pathCost p ∧
        substitution^[r] (.of true) = u := by
  induction p generalizing t with
  | nil => simp [subtree, pathThreshold, pathCost, eq_comm]
  | cons b p ih =>
      cases t with
      | zero => simp [subtree, pathThreshold, pathCost]
      | succ t => cases t with
        | zero =>
            change subtree (b :: p) (.of false) = some u ↔ _
            simp only [subtree, reduceCtorEq, false_iff, not_exists, not_and]
            intro r h; simp only [pathThreshold] at h; omega
        | succ t =>
            have children : substitution^[t+2] (.of true) =
                .mul (substitution^[t+1] (.of true)) (substitution^[t] (.of true)) := by
              have h := ((ranked_equality_compilation 1 0 Fin.elim0
                (.residual 2 (.inl 0))
                (.pair (.residual 1 (.inl 0)) (.residual 0 (.inl 0)))).2
                  (fun _ => t)).mp (by
                    simp [equalityFormula, NativeRankedEqualityCompiler.compileEquality,
                      NativeRankedEqualityCompiler.normalize,
                      NativeRankedEqualityCompiler.equalityConditions,
                      NativeRankedEqualityCompiler.atomicConditions,
                      NativeRankedEqualityCompiler.clock, NativeRankedEqualityCompiler.addOffset,
                      NativeRankedEqualityCompiler.conditionsFormula,
                      NativeRankedEqualityCompiler.offsetTerm, Formula.Realize,
                      BoundedFormula.realize_bdEqual])
              simpa only [rankedEval, eval, Sum.elim_inl, Function.iterate_zero_apply,
                ← Function.iterate_add_apply, Nat.add_comm, Nat.add_zero] using h
            rw [show t+1+1 = t+2 by omega, children]
            cases b <;> simp only [subtree, ih, pathThreshold, pathCost, Bool.false_eq_true,
              if_false, if_true, Nat.max_le]
            all_goals
              constructor
              · rintro ⟨r, h, e, v⟩
                exact ⟨r, ⟨by omega, by omega⟩, by omega, v⟩
              · rintro ⟨r, ⟨_,h⟩, e, v⟩
                exact ⟨r, by omega, by omega, v⟩

/-- Push a fixed epoch through the finite pair skeleton. -/
def atEpoch {k : Nat} (e : Nat) : RankedExpr k 0 → RankedExpr k 0
  | .ground g => .ground (substitution^[e] g)
  | .residual a i => .residual (e+a) i
  | .pair A B => .pair (atEpoch e A) (atEpoch e B)

private theorem epoch_value {k : Nat} (e : Nat) (n : Fin k → Nat)
    (E : RankedExpr k 0) :
    rankedEval n Fin.elim0 (atEpoch e E) = substitution^[e] (rankedEval n Fin.elim0 E) := by
  induction E with
  | ground g => rfl
  | residual a i => simp only [atEpoch, rankedEval, eval, Function.iterate_add_apply]
  | pair A B ihA ihB =>
      change .mul _ _ = substitution^[e] (.mul _ _)
      rw [Function.Semiconj₂.iterate
        (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
          fun A B => substitution.map_mul A B)]
      exact congrArg₂ FreeMagma.mul ihA ihB

/-- Navigation stops at a whole expression or at an atomic suffix, or is absent. -/
inductive Navigation (k : Nat) where
  | missing
  | whole : RankedExpr k 0 → Navigation k
  | atomic : Fin k → Nat → Address → Navigation k

/-- Follow the finite syntax skeleton; finite grounds are navigated literally. -/
def navigate {k : Nat} : RankedExpr k 0 → Address → Navigation k
  | E, [] => .whole E
  | .ground g, b :: p =>
      match subtree (b :: p) g with
      | none => .missing
      | some u => .whole (.ground u)
  | .residual a (.inl j), b :: p => .atomic j a (b :: p)
  | .residual _ (.inr i), _ :: _ => Fin.elim0 i
  | .pair A B, b :: p => navigate (if b then B else A) p

/-- This interpretation uses actual native subtree navigation. -/
def navigationValue {k : Nat} (n : Fin k → Nat) : Navigation k → Option Source
  | .missing => none
  | .whole E => some (rankedEval n Fin.elim0 E)
  | .atomic j a p => subtree p (substitution^[n j+a] (.of true))

theorem navigate_value {k : Nat} (n : Fin k → Nat) (E : RankedExpr k 0)
    (p : Address) : navigationValue n (navigate E p) = subtree p (rankedEval n Fin.elim0 E) := by
  induction p generalizing E with
  | nil => rfl
  | cons b p ih => cases E with
    | ground g =>
        simp only [navigate]
        cases h : subtree (b :: p) g <;> simp [navigationValue, rankedEval, eval, h]
    | residual a i => cases i with
      | inl j =>
          change subtree (b :: p) (substitution^[n j+a] (.of true)) =
            subtree (b :: p) (substitution^[a] (substitution^[n j] (.of true)))
          rw [Nat.add_comm, Function.iterate_add_apply]
      | inr i => exact Fin.elim0 i
    | pair A B => cases b <;> simpa [navigate, rankedEval, eval, subtree] using ih _

/-- Reserve two fresh natural coordinates while preserving every original name. -/
def liftExpr {k : Nat} : RankedExpr k 0 → RankedExpr (k+2) 0
  | .ground g => .ground g
  | .residual a (.inl j) => .residual a (.inl (Fin.castAdd 2 j))
  | .residual _ (.inr i) => Fin.elim0 i
  | .pair A B => .pair (liftExpr A) (liftExpr B)

private theorem lift_value {k : Nat} (n : Fin k → Nat) (w : Fin 2 → Nat)
    (E : RankedExpr k 0) :
    rankedEval (Fin.addCases n w) Fin.elim0 (liftExpr E) = rankedEval n Fin.elim0 E := by
  induction E with
  | ground g => rfl
  | residual a i => cases i with
    | inl j => simp [liftExpr, rankedEval, eval]
    | inr i => exact Fin.elim0 i
  | pair A B ihA ihB => exact congrArg₂ FreeMagma.mul ihA ihB

/-- The reached whole expression, with a selected fresh coordinate for atomic suffixes. -/
def reachedExpr {k : Nat} (s : Navigation k) (i : Fin 2) : RankedExpr (k+2) 0 :=
  match s with
  | .missing => .ground (.of true)
  | .whole E => liftExpr E
  | .atomic _ _ _ => .residual 0 (.inl (Fin.natAdd k i))

/-- Finite lower bounds are expressed by excluding all smaller fixed indices. -/
def lowerFormula {k : Nat} (j : Fin k) (a h : Nat) : presburger.Formula (Fin k) :=
  ((List.range h).map fun c =>
    (equalityFormula Fin.elim0 (.residual a (.inl j))
      (.ground (substitution^[c] (.of true)))).not).foldr (· ⊓ ·) ⊤

private theorem lower_realize {k : Nat} (v : Fin k → Nat) (j : Fin k) (a h : Nat) :
    (lowerFormula j a h).Realize v ↔ h ≤ v j+a := by
  simp only [lowerFormula, Formula.Realize, BoundedFormula.realize_foldr_inf,
    List.forall_mem_map, BoundedFormula.realize_not]
  have eqs : ∀ c : Nat,
      (equalityFormula Fin.elim0 (.residual a (.inl j))
        (.ground (substitution^[c] (.of true)))).Realize v ↔ v j+a = c := by
    intro c
    rw [(ranked_equality_compilation k 0 Fin.elim0 _ _).2 v]
    change substitution^[a] (substitution^[v j] (.of true)) = substitution^[c] (.of true) ↔ _
    rw [← Function.iterate_add_apply, Nat.add_comm a]
    constructor
    · intro he
      have hc := congrArg kappa he
      simpa only [kappa_iterate, kappa, Nat.zero_add] using hc
    · intro he; rw [he]
  simp only [Formula.Realize] at eqs
  simp only [eqs, List.mem_range]
  constructor
  · intro hnot; by_contra hlt; exact hnot _ (by omega) rfl
  · intro hle c hc he; omega

/-- Reachedness includes the complete atomic suffix guard and the endpoint index equation. -/
def guardFormula {k : Nat} (s : Navigation k) (i : Fin 2) : presburger.Formula (Fin (k+2)) :=
  match s with
  | .missing => ⊥
  | .whole _ => ⊤
  | .atomic j a p =>
      lowerFormula (Fin.castAdd 2 j) a (pathThreshold p) ⊓
        equalityFormula Fin.elim0 (.residual a (.inl (Fin.castAdd 2 j)))
          (.residual (pathCost p) (.inl (Fin.natAdd k i)))

theorem guard_realize {k : Nat} (n : Fin k → Nat) (w : Fin 2 → Nat)
    (s : Navigation k) (i : Fin 2) :
    (guardFormula s i).Realize (Fin.addCases n w) ↔
      navigationValue n s = some (rankedEval (Fin.addCases n w) Fin.elim0 (reachedExpr s i)) := by
  cases s with
  | missing => simp [guardFormula, navigationValue]
  | whole E => simp [guardFormula, navigationValue, reachedExpr, lift_value]
  | atomic j a p =>
      rw [guardFormula, Formula.realize_inf, lower_realize,
        (ranked_equality_compilation (k+2) 0 Fin.elim0 _ _).2 (Fin.addCases n w)]
      simp only [Fin.addCases_left, Fin.addCases_right, navigationValue, reachedExpr,
        rankedEval, eval, Sum.elim_inl, Function.iterate_zero_apply]
      have eqs : substitution^[a] (substitution^[n j] (.of true)) =
          substitution^[pathCost p] (substitution^[w i] (.of true)) ↔
          n j+a = w i+pathCost p := by
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
        constructor
        · intro he
          have hc := congrArg kappa he
          simp only [kappa_iterate, kappa, Nat.zero_add] at hc
          omega
        · intro he
          congr 1; omega
      rw [eqs, atomic_navigation]
      constructor
      · rintro ⟨h,e⟩; exact ⟨w i,h,e,rfl⟩
      · rintro ⟨r,h,e,he⟩
        have hc := congrArg kappa he
        simp only [kappa_iterate, kappa, Nat.zero_add] at hc
        exact ⟨h, by omega⟩

/-- Existentially bind just the two fresh endpoint coordinates. -/
def closeFormula {k : Nat} (f : presburger.Formula (Fin (k + 2))) :
    presburger.Formula (Fin k) :=
  (BoundedFormula.relabel (finSumFinEquiv.symm : Fin (k+2) → Fin k ⊕ Fin 2) f).exs

private theorem close_realize {k : Nat} (f : presburger.Formula (Fin (k + 2)))
    (n : Fin k → Nat) :
    (closeFormula f).Realize n ↔ ∃ w : Fin 2 → Nat, f.Realize (Fin.addCases n w) := by
  simp only [closeFormula, BoundedFormula.realize_exs, BoundedFormula.realize_relabel]
  apply exists_congr
  intro w
  have hv : Sum.elim n (w ∘ Fin.castAdd 0) ∘
      (finSumFinEquiv.symm : Fin (k+2) → Fin k ⊕ Fin 2) = Fin.addCases n w := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp
  rw [hv]
  have hzero : w ∘ Fin.natAdd 2 = (default : Fin 0 → Nat) := funext (fun i => Fin.elim0 i)
  rw [hzero]
  unfold Formula.Realize
  apply Iff.of_eq
  apply congrArg (BoundedFormula.Realize f (Fin.addCases n w))
  exact Subsingleton.elim _ _

theorem navigation_witness {k : Nat} (n : Fin k → Nat) (s : Navigation k)
    (i : Fin 2) (u : Source) (hu : navigationValue n s = some u) :
    ∃ r : Nat, ∀ w : Fin 2 → Nat, w i = r →
      (guardFormula s i).Realize (Fin.addCases n w) ∧
        rankedEval (Fin.addCases n w) Fin.elim0 (reachedExpr s i) = u := by
  cases s with
  | missing => cases hu
  | whole E =>
      refine ⟨0, fun w _ => ?_⟩
      have he : rankedEval n Fin.elim0 E = u := Option.some.inj hu
      have hv : rankedEval (Fin.addCases n w) Fin.elim0 (reachedExpr (.whole E) i) = u :=
        (lift_value n w E).trans he
      exact ⟨(guard_realize n w (.whole E) i).mpr (hu.trans (congrArg some hv.symm)), hv⟩
  | atomic j a p =>
      obtain ⟨r,_,_,he⟩ := (atomic_navigation p (n j+a) u).mp hu
      refine ⟨r, fun w hw => ?_⟩
      have hv : rankedEval (Fin.addCases n w) Fin.elim0
          (reachedExpr (.atomic j a p) i) = u := by
        simpa [reachedExpr, rankedEval, eval, hw] using he
      exact ⟨(guard_realize n w (.atomic j a p) i).mpr
        (hu.trans (congrArg some hv.symm)), hv⟩

/-- Exact classification of the root of a reached expression. -/
def rootFormula {k : Nat} (E : RankedExpr k 0) : Reply → presburger.Formula (Fin k)
  | .alpha => equalityFormula Fin.elim0 E (.ground (.of true))
  | .beta => equalityFormula Fin.elim0 E (.ground (.of false))
  | .branch => (equalityFormula Fin.elim0 E (.ground (.of true))).not ⊓
      (equalityFormula Fin.elim0 E (.ground (.of false))).not
  | .absent => ⊥

private theorem root_realize {k : Nat} (E : RankedExpr k 0) (y : Reply) (v : Fin k → Nat) :
    (rootFormula E y).Realize v ↔ readout [] (rankedEval v Fin.elim0 E) = y := by
  have ha := (ranked_equality_compilation k 0 Fin.elim0 E (.ground (.of true))).2 v
  have hb := (ranked_equality_compilation k 0 Fin.elim0 E (.ground (.of false))).2 v
  cases y <;> simp only [rootFormula, Formula.realize_inf, Formula.realize_not,
    Formula.realize_bot, ha, hb, rankedEval, eval]
  all_goals
    cases h : eval (Sum.elim (fun j => substitution^[v j] (.of true)) Fin.elim0) E with
    | of b => cases b <;> simp only [readout, reduceCtorEq, iff_false, not_true_eq_false,
          and_false, false_and]
          <;> (intro he; cases he)
    | mul A B => simp [readout]

/-- Absence negates reachedness; other replies classify a genuinely reached subtree. -/
def literalFormula {k : Nat} (s : Navigation k) (y : Reply) : presburger.Formula (Fin k) :=
  match y with
  | .absent => (closeFormula (guardFormula s 0)).not
  | _ => closeFormula (guardFormula s 0 ⊓ rootFormula (reachedExpr s 0) y)

private theorem root_not_absent (u : Source) : readout [] u ≠ Reply.absent := by
  cases u with
  | of b => cases b <;> simp [readout]
  | mul A B => simp [readout]

private theorem literal_realize {k : Nat} (s : Navigation k) (y : Reply) (n : Fin k → Nat) :
    (literalFormula s y).Realize n ↔
      (match navigationValue n s with | none => Reply.absent | some u => readout [] u) = y := by
  have reach : (closeFormula (guardFormula s 0)).Realize n ↔
      ∃ u : Source, navigationValue n s = some u := by
    rw [close_realize]
    constructor
    · rintro ⟨w,hw⟩
      exact ⟨_,(guard_realize n w s 0).mp hw⟩
    · rintro ⟨u,hu⟩
      obtain ⟨r,hr⟩ := navigation_witness n s 0 u hu
      exact ⟨fun _ => r,(hr _ rfl).1⟩
  cases y with
  | absent =>
      simp only [literalFormula, Formula.realize_not, reach]
      cases hv : navigationValue n s with
      | none => simp
      | some u => simp [root_not_absent]
  | alpha | beta | branch =>
      simp only [literalFormula]
      rw [close_realize]
      simp only [Formula.realize_inf, root_realize]
      constructor
      · rintro ⟨w,hw,hy⟩
        rw [(guard_realize n w s 0).mp hw]
        exact hy
      · intro hy
        cases hv : navigationValue n s with
        | none => simp [hv] at hy
        | some u =>
            simp only [hv] at hy
            obtain ⟨r,hr⟩ := navigation_witness n s 0 u hv
            refine ⟨fun _ => r,(hr _ rfl).1,?_⟩
            rw [(hr _ rfl).2]
            exact hy

/-- One shared rank tuple evaluates an endpoint at its fixed epoch and suffix. -/
structure Endpoint (k : Nat) where
  expression : RankedExpr k 0
  epoch : Nat
  address : Address

/-- Endpoint navigation is an effective finite construction. -/
def endpointNavigation {k : Nat} (a : Endpoint k) : Navigation k :=
  navigate (atEpoch a.epoch a.expression) a.address

/-- Literal replies and positive whole-subtree links share all original rank coordinates. -/
inductive Record (k : Nat) where
  | literal : Endpoint k → Reply → Record k
  | link : Endpoint k → Endpoint k → Record k

/-- The specification is stated directly on actual native trees and readouts. -/
def RecordHolds {k : Nat} (n : Fin k → Nat) : Record k → Prop
  | .literal a y => readout a.address
      (substitution^[a.epoch] (rankedEval n Fin.elim0 a.expression)) = y
  | .link a b => ∃ u v : Source,
      subtree a.address (substitution^[a.epoch] (rankedEval n Fin.elim0 a.expression)) = some u ∧
      subtree b.address (substitution^[b.epoch] (rankedEval n Fin.elim0 b.expression)) =
        some v ∧ u = v

/-- Both endpoint guards precede whole native equality in a positive link. -/
def linkFormula {k : Nat} (s t : Navigation k) : presburger.Formula (Fin k) :=
  closeFormula (guardFormula s 0 ⊓ (guardFormula t 1 ⊓
    equalityFormula Fin.elim0 (reachedExpr s 0) (reachedExpr t 1)))

private theorem link_realize {k : Nat} (s t : Navigation k) (n : Fin k → Nat) :
    (linkFormula s t).Realize n ↔ ∃ u v : Source,
      navigationValue n s = some u ∧ navigationValue n t = some v ∧ u = v := by
  rw [linkFormula, close_realize]
  simp only [Formula.realize_inf]
  constructor
  · rintro ⟨w,hs,ht,he⟩
    exact ⟨_,_,(guard_realize n w s 0).mp hs,(guard_realize n w t 1).mp ht,
      ((ranked_equality_compilation (k+2) 0 Fin.elim0 _ _).2 (Fin.addCases n w)).mp he⟩
  · rintro ⟨u,v,hs,ht,he⟩
    obtain ⟨r,hr⟩ := navigation_witness n s 0 u hs
    obtain ⟨q,hq⟩ := navigation_witness n t 1 v ht
    let w : Fin 2 → Nat := ![r,q]
    obtain ⟨hsg,hsu⟩ := hr w (by simp [w])
    obtain ⟨htg,htv⟩ := hq w (by simp [w])
    exact ⟨w,hsg,htg,
      ((ranked_equality_compilation (k+2) 0 Fin.elim0 _ _).2 (Fin.addCases n w)).mpr
        (hsu.trans (he.trans htv.symm))⟩

/-- The exact formula for each native record. -/
def recordFormula {k : Nat} : Record k → presburger.Formula (Fin k)
  | .literal a y => literalFormula (endpointNavigation a) y
  | .link a b => linkFormula (endpointNavigation a) (endpointNavigation b)

private theorem endpoint_value {k : Nat} (n : Fin k → Nat) (a : Endpoint k) :
    navigationValue n (endpointNavigation a) =
      subtree a.address (substitution^[a.epoch] (rankedEval n Fin.elim0 a.expression)) := by
  rw [endpointNavigation, navigate_value, epoch_value]

private theorem record_realize {k : Nat} (r : Record k) (n : Fin k → Nat) :
    (recordFormula r).Realize n ↔ RecordHolds n r := by
  cases r with
  | literal a y =>
      rw [recordFormula, literal_realize, endpoint_value]
      have reply := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        a.address [] (substitution^[a.epoch] (rankedEval n Fin.elim0 a.expression))
      simp only [List.append_nil] at reply
      change _ ↔ readout a.address _ = y
      rw [reply]
      rfl
  | link a b =>
      simp only [recordFormula, link_realize, endpoint_value, RecordHolds]

/-- Finite conjunction; the empty refinement list produces top. -/
def refinementFormula {k : Nat} (records : List (Record k)) : presburger.Formula (Fin k) :=
  (records.map recordFormula).foldr (· ⊓ ·) ⊤

/-- Effective first-order Presburger compilation for every original unbounded rank tuple. -/
theorem rank_only_refinement_compilation (k : Nat) (records : List (Record k)) :
    ∀ n : Fin k → Nat, (refinementFormula records).Realize n ↔
      ∀ r ∈ records, RecordHolds n r := by
  intro n
  simp only [refinementFormula, Formula.Realize, BoundedFormula.realize_foldr_inf,
    List.forall_mem_map]
  exact forall_congr' fun r => forall_congr' fun _ => record_realize r n

#print axioms rank_only_refinement_compilation
end D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedNavigationCompiler
