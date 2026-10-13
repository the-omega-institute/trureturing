/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Positive context histories recover unrestricted repeated-role valuations. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativePayloadHistoryInstallation
import D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativePositiveContextFiber

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address readout)
open ActualLeafHistoryRigidity (subtree)
open ActualCutPartitionRecovery
open ActualCutPartitionDecoder (HoleExterior cutExterior nameExterior)
open NativeCutFibers (labels Classes extend rowAt_evaluate)
open NativePrefixIdentityReflection (MixedExpr eval)
open NativePayloadHistoryInstallation (compile Holds Record)
open NativeFiveHoleFiber (GuardedEqual)

/-- Every displayed hole carries its original address; displayed concrete
nodes lie outside the cut. -/
def WellAddressed (P : CutSet) : Address → HoleExterior → Prop
  | a, .of (.inl _) => a ∉ P
  | a, .of (.inr p) => a = p ∧ a ∈ P
  | a, .mul l r => a ∉ P ∧ WellAddressed P (a ++ [false]) l ∧
      WellAddressed P (a ++ [true]) r

/-- An ordinary role context is a zero-decoration mixed expression. -/
def expression : LiteralRow → MixedExpr Nat
  | .of (.inl b) => .ground (.of b)
  | .of (.inr n) => .residual 0 n
  | .mul l r => .pair (expression l) (expression r)

/-- The concrete exterior and prescribed positive equalities are independent
of the compiler and impose no different-role disequality. -/
def PositiveContext (P : CutSet) (X : HoleExterior) (label : Address → Nat)
    (U : Source) : Prop :=
  cutExterior P [] U = X ∧ ∀ (p q : Address) (n : Nat),
    rowAt p (nameExterior label X) = some (.of (.inr n)) →
    rowAt q (nameExterior label X) = some (.of (.inr n)) →
    subtree p U = subtree q U

private def Star (U : Source) (rep : Nat → Address) (a : Address)
    (C : LiteralRow) : Prop :=
  ∀ (p : Address) (n : Nat), rowAt p C = some (.of (.inr n)) →
    GuardedEqual 0 (a ++ p) 0 (rep n) U

private theorem star_ground (U : Source) (rep : Nat → Address) (a : Address) (b : Bool) :
    Star U rep a (.of (.inl b)) := by
  intro p n h
  cases p <;> simp [rowAt] at h
  cases h

private theorem star_role (U : Source) (rep : Nat → Address) (a : Address) (n : Nat) :
    Star U rep a (.of (.inr n)) ↔ GuardedEqual 0 a 0 (rep n) U := by
  constructor
  · intro h; simpa using h [] n rfl
  · intro h p m hp
    cases p with
    | nil =>
        have eq : n = m := by
          injection hp with he
          injection he with he
          exact Sum.inr.inj he
        subst m; simpa using h
    | cons b p => simp [rowAt] at hp

private theorem star_pair (U : Source) (rep : Nat → Address) (a : Address)
    (l r : LiteralRow) : Star U rep a (.mul l r) ↔
      Star U rep (a ++ [false]) l ∧ Star U rep (a ++ [true]) r := by
  constructor
  · intro h
    constructor
    · intro p n hp; simpa [List.append_assoc] using h (false :: p) n hp
    · intro p n hp; simpa [List.append_assoc] using h (true :: p) n hp
  · rintro ⟨hl,hr⟩ p n hp
    cases p with
    | nil => simp [rowAt] at hp
    | cons b p =>
        cases b
        · simpa [List.append_assoc] using hl p n hp
        · simpa [List.append_assoc] using hr p n hp

private theorem compiled_exterior (P : CutSet) (label : Address → Nat)
    (rep : Nat → Address) (U : Source) (X : HoleExterior) (a : Address) (T : Source)
    (well : WellAddressed P a X) (present : subtree a U = some T) :
    Holds U (compile rep a (expression (nameExterior label X))) ↔
      cutExterior P a T = X ∧ Star U rep a (nameExterior label X) := by
  induction X generalizing a T with
  | of v => cases v with
    | inl b =>
        have h := NativePayloadHistoryInstallation.payload_history_exact
          (.ground (.of b) : MixedExpr Nat) rep a U (fun _ => .of true)
          (by simp [NativePayloadHistoryInstallation.names])
        have no : a ∉ P := well
        have star := star_ground U rep a b
        simp only [nameExterior, FreeMagma.lift_of, Sum.map_inl, id_eq, expression]
        rw [h]
        simp only [eval, present, Option.some.injEq]
        cases T <;> simp [cutExterior, no, star]
        constructor <;> intro he <;> cases he <;> rfl
    | inr p =>
        obtain ⟨rfl,mem⟩ := well
        cases T <;> simp [nameExterior, expression, compile, Holds, Record.Holds, cutExterior,
          mem, star_role]
  | mul l r ihl ihr =>
      obtain ⟨no,wl,wr⟩ := well
      have read := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a [] U
      have readAt : readout a U = readout [] T := by
        simpa only [List.append_nil, present] using read
      have app := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simp only [nameExterior, FreeMagma.mul_eq, map_mul, expression, compile,
        Holds, List.forall_mem_cons, List.forall_mem_append, Record.Holds,
        Function.iterate_zero, id_eq]
      change (readout a U = .branch ∧
        Holds U (compile rep (a ++ [false]) (expression (nameExterior label l))) ∧
        Holds U (compile rep (a ++ [true]) (expression (nameExterior label r)))) ↔ _
      rw [readAt]
      cases T with
      | of b => cases b <;> simp [readout, cutExterior, no]
      | mul tl tr =>
          have al : subtree (a ++ [false]) U = some tl := by rw [app, present]; rfl
          have ar : subtree (a ++ [true]) U = some tr := by rw [app, present]; rfl
          rw [ihl _ _ wl al, ihr _ _ wr ar]
          simp only [readout, true_and, cutExterior, no, ↓reduceIte]
          change (_ ∧ _) ∧ _ ∧ _ ↔
            FreeMagma.mul (cutExterior P (a ++ [false]) tl)
              (cutExterior P (a ++ [true]) tr) = FreeMagma.mul l r ∧
            Star U rep a (.mul (nameExterior label l) (nameExterior label r))
          rw [star_pair]
          constructor
          · rintro ⟨⟨hl,sl⟩,hr,sr⟩
            exact ⟨congrArg₂ FreeMagma.mul hl hr,sl,sr⟩
          · rintro ⟨he,sl,sr⟩
            injection he with hl hr
            exact ⟨⟨hl,sl⟩,hr,sr⟩

private theorem occurrence_label (C : LiteralRow) (p : Address) (n : Nat)
    (occ : rowAt p C = some (.of (.inr n))) : n ∈ labels C := by
  induction p generalizing C with
  | nil =>
      have same : C = .of (.inr n) := Option.some.inj occ
      subst C; simp [labels]
  | cons b p ih =>
      cases C with
      | of c => simp [rowAt] at occ
      | mul l r =>
          cases b
          · exact Finset.mem_union_left _ (ih l occ)
          · exact Finset.mem_union_right _ (ih r occ)

private theorem cut_role_present (P : CutSet) (label : Address → Nat)
    (T : Source) (a p : Address) (n : Nat)
    (occ : rowAt p (nameExterior label (cutExterior P a T)) = some (.of (.inr n))) :
    (subtree p T).isSome := by
  induction p generalizing a T with
  | nil => simp [subtree]
  | cons b p ih =>
      by_cases mem : a ∈ P
      · cases T <;> simp [cutExterior, mem, nameExterior, rowAt] at occ
      · cases T with
        | of c => simp [cutExterior, mem, nameExterior, rowAt] at occ
        | mul l r =>
            cases b
            · exact ih l (a ++ [false]) (by simpa [cutExterior, mem, nameExterior, rowAt] using occ)
            · exact ih r (a ++ [true]) (by simpa [cutExterior, mem, nameExterior, rowAt] using occ)

/-- The independent original exterior and all within-role equalities agree
exactly with the finite root history. Distinct roles need not have distinct values. -/
theorem positive_context_history_exact (P : CutSet) (X : HoleExterior)
    (label : Address → Nat) (rep : Nat → Address)
    (well : WellAddressed P [] X)
    (representatives : ∀ n ∈ labels (nameExterior label X),
      rowAt (rep n) (nameExterior label X) = some (.of (.inr n))) (U : Source) :
    PositiveContext P X label U ↔
      Holds U (compile rep [] (expression (nameExterior label X))) := by
  have bridge := compiled_exterior P label rep U X [] U well rfl
  constructor
  · rintro ⟨exterior,eqs⟩
    apply bridge.mpr
    refine ⟨exterior,?_⟩
    intro p n occ
    have rocc := representatives n (occurrence_label _ p n occ)
    have hp := cut_role_present P label U [] p n (by simpa only [exterior] using occ)
    have hr := cut_role_present P label U [] (rep n) n (by simpa only [exterior] using rocc)
    exact ⟨hp,hr,eqs p (rep n) n occ rocc⟩
  · intro h
    obtain ⟨exterior,links⟩ := bridge.mp h
    refine ⟨exterior,?_⟩
    intro p q n hp hq
    exact (links p n hp).2.2.trans (links q n hq).2.2.symm


/-- Read the value at the designated occurrence of each supported role.
The default is irrelevant on positive contexts, where every representative is reached. -/
def recoverRoles (C : LiteralRow) (rep : Nat → Address) (U : Source) :
    Classes C → Source :=
  fun b => (subtree (rep b.val) U).getD (.of true)

private theorem eval_expression (C : LiteralRow) (v : Nat → Source) :
    eval v (expression C) = evaluateRow v C := by
  induction C with
  | of c => cases c <;> rfl
  | mul l r hl hr =>
      change FreeMagma.mul (eval v (expression l)) (eval v (expression r)) =
        FreeMagma.mul (evaluateRow v l) (evaluateRow v r)
      exact congrArg₂ FreeMagma.mul hl hr

private theorem names_expression (C : LiteralRow) (n : Nat) :
    n ∈ NativePayloadHistoryInstallation.names (expression C) ↔ n ∈ labels C := by
  induction C with
  | of c => cases c <;> simp [expression, NativePayloadHistoryInstallation.names, labels]
  | mul l r hl hr => simp [expression, NativePayloadHistoryInstallation.names, labels, hl, hr]

private theorem filled_positive (P : CutSet) (X : HoleExterior)
    (label : Address → Nat) (rep : Nat → Address)
    (well : WellAddressed P [] X)
    (representatives : ∀ n ∈ labels (nameExterior label X),
      rowAt (rep n) (nameExterior label X) = some (.of (.inr n)))
    (v : Classes (nameExterior label X) → Source) :
    PositiveContext P X label
      (evaluateRow (extend (nameExterior label X) v) (nameExterior label X)) := by
  apply (positive_context_history_exact P X label rep well representatives _).mpr
  apply (NativePayloadHistoryInstallation.payload_history_exact
    (expression (nameExterior label X)) rep [] _ (extend (nameExterior label X) v) ?_).mpr
  · simp only [subtree, eval_expression]
  · intro n hn
    simpa only [evaluateRow, FreeMagma.lift_of, Sum.elim_inr] using
      rowAt_evaluate (nameExterior label X) (extend (nameExterior label X) v) (rep n) _
        (representatives n ((names_expression _ n).mp hn))

private theorem recover_fill (C : LiteralRow) (rep : Nat → Address)
    (representatives : ∀ n ∈ labels C, rowAt (rep n) C = some (.of (.inr n)))
    (v : Classes C → Source) :
    recoverRoles C rep (evaluateRow (extend C v) C) = v := by
  funext b
  have h := rowAt_evaluate C (extend C v) (rep b.val) _
    (representatives b.val b.property)
  change (subtree (rep b.val) (evaluateRow (extend C v) C)).getD (.of true) = v b
  rw [h]
  simp only [Option.getD_some, evaluateRow, FreeMagma.lift_of,
    Sum.elim_inr, extend, b.property, ↓reduceDIte]

private theorem fill_recover (P : CutSet) (X : HoleExterior)
    (label : Address → Nat) (rep : Nat → Address)
    (well : WellAddressed P [] X)
    (representatives : ∀ n ∈ labels (nameExterior label X),
      rowAt (rep n) (nameExterior label X) = some (.of (.inr n)))
    (U : Source) (positive : PositiveContext P X label U) :
    evaluateRow (extend (nameExterior label X) (recoverRoles (nameExterior label X) rep U))
      (nameExterior label X) = U := by
  have located : ∀ n ∈ NativePayloadHistoryInstallation.names (expression (nameExterior label X)),
      subtree (rep n) U =
        some (extend (nameExterior label X) (recoverRoles (nameExterior label X) rep U) n) := by
    intro n hn
    have mem := (names_expression _ n).mp hn
    have occ := representatives n mem
    have present := cut_role_present P label U [] (rep n) n
      (by simpa only [positive.1] using occ)
    obtain ⟨T,hT⟩ := Option.isSome_iff_exists.mp present
    simp only [extend, mem, ↓reduceDIte, recoverRoles, hT, Option.getD_some]
  have h := (NativePayloadHistoryInstallation.payload_history_exact
    (expression (nameExterior label X)) rep [] U
    (extend (nameExterior label X) (recoverRoles (nameExterior label X) rep U)) located).mp
      ((positive_context_history_exact P X label rep well representatives U).mp positive)
  have same : U = evaluateRow
      (extend (nameExterior label X) (recoverRoles (nameExterior label X) rep U)) (nameExterior label X) := by
    simpa only [subtree, eval_expression, Option.some.injEq] using h
  exact same.symm

/-- Every unrestricted supported-role valuation gives exactly one source in the
positive context, and reading its representatives recovers that valuation. -/
def positiveContextEquiv (P : CutSet) (X : HoleExterior)
    (label : Address → Nat) (rep : Nat → Address)
    (well : WellAddressed P [] X)
    (representatives : ∀ n ∈ labels (nameExterior label X),
      rowAt (rep n) (nameExterior label X) = some (.of (.inr n))) :
    (Classes (nameExterior label X) → Source) ≃ {U : Source // PositiveContext P X label U} where
  toFun v := ⟨evaluateRow (extend (nameExterior label X) v) (nameExterior label X),
    filled_positive P X label rep well representatives v⟩
  invFun U := recoverRoles (nameExterior label X) rep U.val
  left_inv := recover_fill (nameExterior label X) rep representatives
  right_inv U := Subtype.ext (fill_recover P X label rep well representatives U.val U.property)

end D5.S3.Arith.FibonacciAtomic.Observer.NativePositiveContextFiber
