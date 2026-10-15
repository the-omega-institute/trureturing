/- GID: D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore.finite_literal_synthesis; instance=D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore.rightHoleInput
   digest: Literal submission budgets on the full actual stationary Moore fiber. -/

import D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeSharedMooreSynthesis
import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.MinMax

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeLiteralMoore

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open ActualCutPartitionRecovery
open NativeCutFibers
open NativeClassRootImage
open NativeClassRootPadding
open NativeClassRootSimulation (Chart firstClass classReply firstClass_reply)
open NativeFullRootFeasibility (target actual_type native_full_root_feasibility)
open NativeFiniteRootMinimax (chartList computedTarget finite_root_minimax)
open NativeSixSourceMoore (Controller Run)
open NativeSharedMooreSynthesis
open NativeWholeRowService (labels_witness)
open ActualObserverAbsorbingNormalization (skip_exact skip_retained skip_removed)

universe u v

/-- Physical occurrences keep the original numeric class identity. -/
def occurrences (C : LiteralRow) (d : Classes C) : List Address :=
  (holeAddresses [] C).filter (fun p => holeLabel p C == some d.val)

/-- The order is length first, then the original lexicographic address order. -/
def shortest (C : LiteralRow) (d : Classes C) : Address :=
  ((occurrences C d).argmin (fun p => toLex (p.length,p))).getD []

def price (C : LiteralRow) (d : Classes C) : Nat := (shortest C d).length

def nativeCost {Q : Type u} {H : Type v} (M : Controller Q H) (tr : List Q) : Nat :=
  (tr.map (fun s => (M.addr s).length)).sum

def rootCost {C : LiteralRow} {Q : Type u} {H : Type v}
    (T : RootTable C Q H) (tr : List Q) : Nat :=
  (tr.map (fun s => price C (T.coord s))).sum

private theorem shortest_spec (C : LiteralRow) (d : Classes C) :
    shortest C d ∈ occurrences C d ∧
    ∀ p ∈ occurrences C d,
      (shortest C d).length ≤ p.length ∧
      ((shortest C d).length = p.length → shortest C d ≤ p) := by
  obtain ⟨p,hp,he⟩ := labels_witness C d.val d.property []
  have mem : p ∈ occurrences C d := by simpa [occurrences,he] using hp
  have ne : occurrences C d ≠ [] := List.ne_nil_of_mem mem
  have found : ∃ a, (occurrences C d).argmin (fun p => toLex (p.length,p)) = some a := by
    cases h : (occurrences C d).argmin (fun p => toLex (p.length,p)) with
    | none => exact (ne (List.argmin_eq_none.mp h)).elim
    | some a => exact ⟨a,rfl⟩
  obtain ⟨a,ha⟩ := found
  have hm : a ∈ (occurrences C d).argmin (fun p => toLex (p.length,p)) := ha
  simp only [shortest,ha,Option.getD_some]
  refine ⟨List.argmin_mem hm,?_⟩
  intro p hp
  exact Prod.Lex.toLex_le_toLex'.mp (List.le_of_mem_argmin hp hm)

private theorem hole_prefix (C : LiteralRow) (a : Address) :
    holeAddresses a C = (holeAddresses [] C).map (a ++ ·) := by
  induction C generalizing a with
  | of z => cases z <;> simp [holeAddresses]
  | mul l r ihl ihr =>
      change holeAddresses (a ++ [false]) l ++ holeAddresses (a ++ [true]) r =
        (holeAddresses [false] l ++ holeAddresses [true] r).map (a ++ ·)
      rw [ihl (a ++ [false]),ihr (a ++ [true]),ihl [false],ihr [true]]
      simp only [List.map_append,List.map_map]
      simp only [List.append_assoc,Function.comp_def]

/-- Exterior traversal either fixes the raw reply for every filling, or
identifies an actual physical prefix with its unchanged class name. -/
private theorem literal_geometry (C : LiteralRow) (a : Address) :
    (∀ z, firstClass C a = .inl z → ∀ f : Nat → Source,
      readout a (evaluateRow f C) = z) ∧
    (∀ d below, firstClass C a = .inr (d,below) →
      ∃ p w, a = p ++ w ∧ p ∈ occurrences C d ∧
        below = !w.isEmpty ∧ rowAt p C = some (.of (.inr d.val))) := by
  induction C generalizing a with
  | of z =>
      cases z with
      | inl b =>
          constructor
          · intro z hz f
            change readout a (.of b) = z
            exact Sum.inl.inj hz
          · intro d below hz; simp [firstClass] at hz
      | inr n =>
          constructor
          · intro z hz; simp [firstClass] at hz
          · intro d below hz
            have eq : (⟨n,by simp [labels]⟩ : Classes (.of (.inr n))) = d ∧
                (!a.isEmpty) = below := by simpa [firstClass] using hz
            refine ⟨[],a,rfl,?_,eq.2.symm,?_⟩
            · simp [occurrences,holeAddresses,holeLabel,rowAt,←eq.1]
            · simp [rowAt,←eq.1]
  | mul l r ihl ihr =>
      cases a with
      | nil =>
          constructor
          · intro z hz f
            simpa [firstClass,evaluateRow,readout] using hz
          · intro d below hz; simp [firstClass] at hz
      | cons b a =>
          cases b
          · constructor
            · intro z hz f
              cases hc : firstClass l a with
              | inl y =>
                  have yz : y = z := by simpa [firstClass,hc] using hz
                  subst z
                  exact (ihl a).1 y hc f
              | inr p => simp [firstClass,hc] at hz
            · intro d below hz
              cases hc : firstClass l a with
              | inl y => simp [firstClass,hc] at hz
              | inr p =>
                  have eq : (⟨p.1.val,Finset.mem_union_left _ p.1.property⟩ :
                      Classes (.mul l r)) = d ∧ p.2 = below := by
                    simpa [firstClass,hc] using hz
                  obtain ⟨v,w,hw,hv,hbelow,hat⟩ := (ihl a).2 p.1 p.2 hc
                  refine ⟨false::v,w,by simp [hw],?_,eq.2.symm.trans hbelow,?_⟩
                  · have hv' := (List.mem_filter.mp hv).1
                    have label := (List.mem_filter.mp hv).2
                    apply List.mem_filter.mpr
                    refine ⟨?_,?_⟩
                    · change false::v ∈ holeAddresses [false] l ++ holeAddresses [true] r
                      apply List.mem_append_left
                      rw [hole_prefix]
                      exact List.mem_map.mpr ⟨v,hv',rfl⟩
                    · simpa [holeLabel,rowAt,hat,←eq.1]
                  · simpa [rowAt,←eq.1] using hat
          · constructor
            · intro z hz f
              cases hc : firstClass r a with
              | inl y =>
                  have yz : y = z := by simpa [firstClass,hc] using hz
                  subst z
                  exact (ihr a).1 y hc f
              | inr p => simp [firstClass,hc] at hz
            · intro d below hz
              cases hc : firstClass r a with
              | inl y => simp [firstClass,hc] at hz
              | inr p =>
                  have eq : (⟨p.1.val,Finset.mem_union_right _ p.1.property⟩ :
                      Classes (.mul l r)) = d ∧ p.2 = below := by
                    simpa [firstClass,hc] using hz
                  obtain ⟨v,w,hw,hv,hbelow,hat⟩ := (ihr a).2 p.1 p.2 hc
                  refine ⟨true::v,w,by simp [hw],?_,eq.2.symm.trans hbelow,?_⟩
                  · have hv' := (List.mem_filter.mp hv).1
                    apply List.mem_filter.mpr
                    refine ⟨?_,?_⟩
                    · change true::v ∈ holeAddresses [false] l ++ holeAddresses [true] r
                      apply List.mem_append_right
                      rw [hole_prefix]
                      exact List.mem_map.mpr ⟨v,hv',rfl⟩
                    · simpa [holeLabel,rowAt,hat,←eq.1]
                  · simpa [rowAt,←eq.1] using hat

private theorem shortest_read (C : LiteralRow) (d : Classes C) (v : Classes C → Source) :
    subtree (shortest C d) (evaluateRow (extend C v) C) = some (v d) := by
  have label : holeLabel (shortest C d) C = some d.val := by
    simpa only [beq_iff_eq] using (List.mem_filter.mp (shortest_spec C d).1).2
  have hat : rowAt (shortest C d) C = some (.of (.inr d.val)) := by
    cases ht : rowAt (shortest C d) C with
    | none => simp [holeLabel,ht] at label
    | some t => cases t with
      | mul l r => simp [holeLabel,ht] at label
      | of z => cases z with
        | inl b => simp [holeLabel,ht] at label
        | inr n =>
            have eq : n = d.val := by simpa [holeLabel,ht] using label
            simpa [eq] using ht
  simpa [evaluateRow,extend,d.property] using rowAt_evaluate C (extend C v) _ _ hat


/-- Exactly the words which enter a physical hole survive. -/
def enters (C : LiteralRow) (a : Address) : Bool :=
  match firstClass C a with | .inl _ => false | .inr _ => true

abbrev Surviving {Q : Type u} {H : Type v} (C : LiteralRow) (M : Controller Q H) :=
  {s : Q // enters C (M.addr s) = true}

private def kept {Q : Type u} {H : Type v} (C : LiteralRow) (M : Controller Q H) :
    Q ⊕ H → Bool
  | .inl s => enters C (M.addr s)
  | .inr _ => true

/-- This adapter is used only by the finite first-exit proof. Its address
labels encode a predicate and are never installed in the native table. -/
private def exitAdapter {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (C : LiteralRow) (M : Controller Q H) (z₀ : H) :
    ActualFiniteObserverAbsentElimination.Observer (Q ⊕ H) where
  e0 := .inr z₀
  action k := match k with
    | .inl s => .inl (if enters C (M.addr s) then [] else [false])
    | .inr _ => .inr false
  transition k z := match k with
    | .inl s => match firstClass C (M.addr s) with
      | .inl y => M.next s y
      | .inr _ => M.next s z
    | .inr h => .inr h
  decoder := fun _ => []
  decoded_nodup := fun _ => List.nodup_nil

private theorem adapter_retained {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (C : LiteralRow) (M : Controller Q H) (z₀ : H) (k : Q ⊕ H) :
    ActualObserverAbsorbingNormalization.retained 1 (exitAdapter C M z₀) k = kept C M k := by
  cases k with
  | inr h => rfl
  | inl s => cases hc : firstClass C (M.addr s) <;>
      simp [ActualObserverAbsorbingNormalization.retained,exitAdapter,kept,enters,hc]

private def lower {Q : Type u} {H : Type v} (C : LiteralRow) (M : Controller Q H)
    (k : Q ⊕ H) (hk : kept C M k = true) : Surviving C M ⊕ H :=
  match k with
  | .inl s => .inl ⟨s,hk⟩
  | .inr h => .inr h

private theorem exit_kept {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (C : LiteralRow) (M : Controller Q H) (z₀ : H) {k s : Q ⊕ H}
    (hs : ActualObserverAbsorbingNormalization.skip 1 (exitAdapter C M z₀) k = some s) :
    kept C M s = true := by
  rw [← adapter_retained C M z₀ s]
  exact ((skip_exact 1 (exitAdapter C M z₀) k).2 s hs).choose_spec.2.2.1

/-- One static map on every installed state. A missing first exit maps to
one original halt, including every state in the same nonexiting basin. -/
def contractCode {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (C : LiteralRow) (M : Controller Q H) (z₀ : H) (k : Q ⊕ H) :
    Surviving C M ⊕ H :=
  match hs : ActualObserverAbsorbingNormalization.skip 1 (exitAdapter C M z₀) k with
  | none => .inr z₀
  | some s => lower C M s (exit_kept C M z₀ hs)

private theorem contract_kept {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (C : LiteralRow) (M : Controller Q H) (z₀ : H) (k : Q ⊕ H)
    (hk : kept C M k = true) : contractCode C M z₀ k = lower C M k hk := by
  have hit := skip_retained 1 (exitAdapter C M z₀)
    ((adapter_retained C M z₀ k).trans hk)
  unfold contractCode
  split <;> rename_i hs
  · rw [hit] at hs; contradiction
  · have e := Option.some.inj (hit.symm.trans hs)
    subst e
    rfl

private theorem contract_removed {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (C : LiteralRow) (M : Controller Q H) (z₀ : H) (s : Q) (z : Reply)
    (hc : firstClass C (M.addr s) = .inl z) :
    contractCode C M z₀ (.inl s) = contractCode C M z₀ (M.next s z) := by
  have rem : ActualObserverAbsorbingNormalization.retained 1 (exitAdapter C M z₀)
      (.inl s) ≠ true := by rw [adapter_retained]; simp [kept,enters,hc]
  have eq := skip_removed 1 (exitAdapter C M z₀) rem
  have step : (exitAdapter C M z₀).transition (.inl s) .absent = M.next s z := by
    simp [exitAdapter,hc]
  rw [step] at eq
  unfold contractCode
  split
  · rename_i hs
    split
    · rfl
    · rename_i t ht
      rw [eq,ht] at hs
      contradiction
  · rename_i t hs
    split
    · rename_i ht
      rw [eq,ht] at hs
      contradiction
    · rename_i t' ht
      have same := Option.some.inj (hs.symm.trans (eq.trans ht))
      subst t'
      rfl

/-- The installed table has the surviving subtype and every original halt.
The initial code is contractCode applied before entry. -/
def contract {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (C : LiteralRow) (M : Controller Q H) (z₀ : H) : Controller (Surviving C M) H where
  addr s := M.addr s.val
  next s z := contractCode C M z₀ (M.next s.val z)
  out := M.out

def survivingTrace {Q : Type u} {H : Type v} (C : LiteralRow) (M : Controller Q H)
    (tr : List Q) : List (Surviving C M) :=
  tr.filterMap (fun s => if h : enters C (M.addr s) = true then some ⟨s,h⟩ else none)

private theorem run_exit {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (C : LiteralRow) (M : Controller Q H) (z₀ : H) (f : Nat → Source)
    {k : Q ⊕ H} {tr : List Q} {h : H}
    (run : Run M (evaluateRow f C) k tr h) :
    ∃ s, ActualObserverAbsorbingNormalization.skip 1 (exitAdapter C M z₀) k = some s := by
  induction run with
  | halt h => exact ⟨_,skip_retained 1 _ ((adapter_retained C M z₀ (.inr h)).trans rfl)⟩
  | @read s tr h tail ih =>
      cases hc : firstClass C (M.addr s) with
      | inr p =>
          exact ⟨_,skip_retained 1 _ (by rw [adapter_retained]; simp [kept,enters,hc])⟩
      | inl z =>
          have reply := (literal_geometry C (M.addr s)).1 z hc f
          have rem : ActualObserverAbsorbingNormalization.retained 1 (exitAdapter C M z₀)
              (.inl s) ≠ true := by rw [adapter_retained]; simp [kept,enters,hc]
          rw [skip_removed 1 _ rem]
          simpa only [exitAdapter,hc,reply] using ih

/-- On each terminating filled-row run, static contraction produces exactly
its filtered running-state list and the identical original halt. Nonexiting
forced basins are absent even when the initial code is removed. -/
private theorem contract_run {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (C : LiteralRow) (M : Controller Q H) (z₀ : H) (f : Nat → Source)
    {k : Q ⊕ H} {tr : List Q} {h : H}
    (run : Run M (evaluateRow f C) k tr h) :
    Run (contract C M z₀) (evaluateRow f C) (contractCode C M z₀ k)
      (survivingTrace C M tr) h ∧
    (∃ s, ActualObserverAbsorbingNormalization.skip 1 (exitAdapter C M z₀) k = some s) := by
  refine ⟨?_,run_exit C M z₀ f run⟩
  induction run with
  | halt h =>
      rw [contract_kept C M z₀ (.inr h) rfl]
      exact .halt h
  | @read s tr h tail ih =>
      cases hc : firstClass C (M.addr s) with
      | inl z =>
          have reply := (literal_geometry C (M.addr s)).1 z hc f
          rw [contract_removed C M z₀ s z hc]
          simpa [survivingTrace,enters,hc,reply] using ih
      | inr p =>
          have hk : enters C (M.addr s) = true := by simp [enters,hc]
          rw [contract_kept C M z₀ (.inl s) hk]
          change Run (contract C M z₀) _ (.inl (⟨s,hk⟩ : Surviving C M)) _ _
          have trace : survivingTrace C M (s::tr) = ⟨s,hk⟩ :: survivingTrace C M tr := by
            simp [survivingTrace,hk]
          rw [trace]
          exact Run.read (⟨s,hk⟩ : Surviving C M) ih

private theorem filtered_resources {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (C : LiteralRow) (M : Controller Q H) (z₀ : H) (tr : List Q) :
    (survivingTrace C M tr).length ≤ tr.length ∧
    nativeCost (contract C M z₀) (survivingTrace C M tr) ≤ nativeCost M tr := by
  refine ⟨List.length_filterMap_le _ _,?_⟩
  induction tr with
  | nil => exact le_rfl
  | cons s tr ih =>
      by_cases hk : enters C (M.addr s) = true
      · simpa [survivingTrace,hk,nativeCost,contract] using Nat.add_le_add_left ih (M.addr s).length
      · simpa [survivingTrace,hk,nativeCost] using ih.trans (Nat.le_add_left _ _)


/-- The original full actual domain and normalized export, with a bound on
the same trace's actual submitted lengths. -/
def NativeLiteralFeasible (P : CutSet) (C : LiteralRow) (r K q ell : Nat) : Prop :=
  ∃ (Q H : Type) (_ : Fintype Q) (_ : Fintype H) (M : Controller Q H)
    (code : ImageValues C → Q ⊕ H),
    (Set.range code).ncard ≤ r ∧ Fintype.card (Q ⊕ H) ≤ K ∧
    ∀ (v : ImageValues C) (u : OriginFiber P C),
      substitution u.val = evaluateRow (extend C v.val.val) C →
      ∃ h tr, Run M (substitution u.val) (code v) tr h ∧
        M.out h = canonicalRow P u.val ∧ tr.length ≤ q ∧ nativeCost M tr ≤ ell

/-- Root prices are paid on every running visit of the existing evaluator. -/
def RootLiteralFeasible (C : LiteralRow) (r K q ell : Nat) : Prop :=
  ∃ (Q H : Type) (_ : Fintype Q) (_ : Fintype H) (T : RootTable C Q H)
    (c : Chart C → Q ⊕ H),
    (Set.range c).ncard ≤ r ∧ Fintype.card (Q ⊕ H) ≤ K ∧
    ∀ θ, ∃ h tr, evaluate (rootStep T θ.val) q (c θ) = some (h,tr) ∧
      T.out h = target C θ.val ∧ rootCost T tr ≤ ell

/-- Only the physical representative changes; classes, carriers, transitions
and whole outputs are the original root table's fields. -/
def installShortest {C : LiteralRow} {Q : Type u} {H : Type v}
    (T : RootTable C Q H) : Controller Q H where
  addr s := shortest C (T.coord s)
  next := T.next
  out := T.out

private theorem shortest_paths {Q : Type u} {H : Type v}
    (P : CutSet) (hP : CutPrefixFree P) (u₀ : Source)
    (T : RootTable (canonicalRow P (substitution u₀)) Q H)
    (v : ImageValues (canonicalRow P (substitution u₀)))
    (u : OriginFiber P (canonicalRow P (substitution u₀)))
    (image : substitution u.val = evaluateRow
      (extend (canonicalRow P (substitution u₀)) v.val.val) (canonicalRow P (substitution u₀))) (n : Nat) (k : Q ⊕ H) :
    evaluate (fun s => (installShortest T).next s
      (readout ((installShortest T).addr s) (substitution u.val))) n k =
      evaluate (rootStep T (types _ v.val.val)) n k := by
  have steps : (fun s => (installShortest T).next s
      (readout ((installShortest T).addr s) (substitution u.val))) =
      rootStep T (types _ v.val.val) := by
    funext s
    change T.next s (readout (shortest _ (T.coord s)) (substitution u.val)) = _
    apply congrArg (T.next s)
    rw [image]
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,readAt,_⟩ :=
      ActualLeafHistoryRigidity.actual_address_geometry
    have h := readAt (shortest (canonicalRow P (substitution u₀)) (T.coord s)) []
      (evaluateRow (extend (canonicalRow P (substitution u₀)) v.val.val)
        (canonicalRow P (substitution u₀)))
    rw [List.append_nil,shortest_read] at h
    rw [h]
    change readout [] (v.val.val (T.coord s)) = rootReply (rootType (v.val.val (T.coord s)))
    cases v.val.val (T.coord s) with
    | of b => cases b <;> rfl
    | mul l r => rfl
  rw [steps]

private theorem root_literal_sufficient (P : CutSet) (hP : CutPrefixFree P)
    (u₀ : Source) (r K q ell : Nat)
    (feasible : RootLiteralFeasible (canonicalRow P (substitution u₀)) r K q ell) :
    NativeLiteralFeasible P (canonicalRow P (substitution u₀)) r K q ell := by
  rcases feasible with ⟨Q,H,fQ,fH,T,c,cap,states,correct⟩
  let _ := fQ
  let _ := fH
  have bridge := install_full_fiber P hP u₀ T c
  refine ⟨Q,H,fQ,fH,installShortest T,exportCode hP u₀ c,?_,states,?_⟩
  · rw [bridge.1]; exact cap
  · intro v u image
    let θ : Chart _ := ⟨types _ v.val.val,actual_type P hP (substitution u₀) v⟩
    obtain ⟨h,tr,ev,out,cost⟩ := correct θ
    rw [← shortest_paths P hP u₀ T v u image q (c θ)] at ev
    obtain ⟨run,calls⟩ := (native_evaluate_iff _ _ _ _ _ _).mp ev
    exact ⟨h,tr,run,out.trans (bridge.2 v u image).1,calls,cost⟩

private theorem paid_price_le {Q : Type u} {H : Type v}
    (C : LiteralRow) (d₀ : Classes C) (M : Controller Q H)
    (all : ∀ s, enters C (M.addr s) = true) (tr : List Q) :
    rootCost (paidTable C d₀ M) tr ≤ nativeCost M tr := by
  have per (s : Q) : price C ((paidTable C d₀ M).coord s) ≤ (M.addr s).length := by
    cases hc : firstClass C (M.addr s) with
    | inl z => have no := all s; simp [enters,hc] at no
    | inr p =>
        obtain ⟨a,w,word,occ,_,_⟩ := (literal_geometry C (M.addr s)).2 p.1 p.2 hc
        change price C (paidCoord C d₀ (M.addr s)) ≤ _
        simp only [paidCoord,hc]
        exact ((shortest_spec C p.1).2 a occ).1.trans (by simp [word])
  induction tr with
  | nil => exact le_rfl
  | cons s tr ih =>
      simpa only [rootCost,nativeCost,List.map_cons,List.sum_cons] using Nat.add_le_add (per s) ih


/-- Exact joint upper-budget transfer on every original nonempty actual
fiber. Necessity contracts first, then compares one truthful selected origin
per type. Sufficiency installs shortest physical words on every origin. -/
theorem literal_moore_feasibility (P : CutSet) (hP : CutPrefixFree P)
    (u₀ : Source) (r K q ell : Nat) (hr : 1 ≤ r) (hK : 1 ≤ K) :
    NativeLiteralFeasible P (canonicalRow P (substitution u₀)) r K q ell ↔
      RootLiteralFeasible (canonicalRow P (substitution u₀)) r K q ell := by
  classical
  constructor
  · intro feasible
    let C := canonicalRow P (substitution u₀)
    by_cases hd : Nonempty (Classes C)
    · obtain ⟨d₀⟩ := hd
      rcases feasible with ⟨Q,H,fQ,fH,M,code,cap,states,correct⟩
      let _ := fQ
      let _ := fH
      have refImage : substitution u₀ = evaluateRow (extend C (referenceValues P hP u₀).val.val) C :=
        (recover_fill P hP C ⟨substitution u₀,rfl⟩).symm
      obtain ⟨z₀,_,_,_,_,_⟩ := correct (referenceValues P hP u₀) ⟨u₀,rfl⟩ refImage
      let M' := contract C M z₀
      let code' : ImageValues C → Surviving C M ⊕ H := fun v => contractCode C M z₀ (code v)
      obtain ⟨values,origins,truth,paths⟩ := paid_native_recode P hP u₀ d₀ M'
      let c : Chart C → Surviving C M ⊕ H := fun θ => code' (values θ)
      have cap' : (Set.range code').ncard ≤ (Set.range code).ncard := by
        have eq : Set.range code' = contractCode C M z₀ '' Set.range code := by
          exact Set.range_comp (contractCode C M z₀) code
        rw [eq]
        exact Set.ncard_image_le
      refine ⟨Surviving C M,H,inferInstance,fH,paidTable C d₀ M',c,?_,?_,?_⟩
      · exact (Set.ncard_le_ncard (by rintro s ⟨θ,rfl⟩; exact ⟨values θ,rfl⟩)).trans (cap'.trans cap)
      · have sub : Fintype.card (Surviving C M) ≤ Fintype.card Q := Fintype.card_subtype_le _
        simp only [Fintype.card_sum] at states ⊢
        omega
      · intro θ
        obtain ⟨h,tr,run,out,calls,cost⟩ := correct (values θ) (origins θ) (truth θ).1
        have fillRun : Run M (evaluateRow (extend C (values θ).val.val) C) (code (values θ)) tr h :=
          (truth θ).1 ▸ run
        have reduced := (contract_run C M z₀ _ fillRun).1
        rw [← (truth θ).1] at reduced
        have bounds := filtered_resources C M z₀ tr
        refine ⟨h,survivingTrace C M tr,?_,out.trans (truth θ).2.2.2.symm,?_⟩
        · rw [paths]
          exact (native_evaluate_iff M' _ q _ _ _).mpr ⟨reduced,bounds.1.trans calls⟩
        · exact (paid_price_le C d₀ M' (fun s => s.property) _).trans (bounds.2.trans cost)
    · have empty : IsEmpty (Classes C) := ⟨fun d => hd ⟨d⟩⟩
      let _ := empty
      have old : NativeFeasible P C r K q := by
        rcases feasible with ⟨Q,H,fQ,fH,M,code,cap,states,correct⟩
        refine ⟨Q,H,fQ,fH,M,code,cap,states,?_⟩
        intro v u image
        obtain ⟨h,tr,run,out,calls,_⟩ := correct v u image
        exact ⟨h,tr,run,out,calls⟩
      obtain ⟨Q,H,fQ,fH,T,c,cap,states,correct⟩ :=
        (shared_moore_feasibility P hP u₀ r K q hr hK).mp old
      refine ⟨Q,H,fQ,fH,T,c,cap,states,?_⟩
      intro θ
      obtain ⟨h,tr,ev,out⟩ := correct θ
      refine ⟨h,tr,ev,out,?_⟩
      have no : IsEmpty Q := ⟨fun s => isEmptyElim (T.coord s)⟩
      have nil : tr = [] := List.eq_nil_iff_forall_not_mem.mpr (fun s _ => no.false s)
      simp [rootCost,nil]
  · exact root_literal_sufficient P hP u₀ r K q ell



/-- A finite per-input charge check on the original shared candidate universe. -/
def literalCheck {C : LiteralRow} {a b : Nat} (A : Candidate C a b)
    (r q ell : Nat) : Bool :=
  check A r q && (chartList C).all (fun θ =>
    match evaluate (rootStep A.table θ.val) q (A.color θ) with
    | none => false
    | some p => decide (rootCost A.table p.2 ≤ ell))

private theorem literalCheck_spec {C : LiteralRow} {a b : Nat}
    (A : Candidate C a b) (r q ell : Nat) :
    literalCheck A r q ell = true ↔
      (Set.range A.color).ncard ≤ r ∧ ∀ θ, ∃ h tr,
        evaluate (rootStep A.table θ.val) q (A.color θ) = some (h,tr) ∧
        A.table.out h = target C θ.val ∧ rootCost A.table tr ≤ ell := by
  rw [literalCheck,Bool.and_eq_true,check_spec,List.all_eq_true]
  constructor
  · rintro ⟨⟨cap,good⟩,cost⟩
    refine ⟨cap,fun θ => ?_⟩
    obtain ⟨h,tr,ev,out⟩ := good θ
    have bound := cost θ ((finite_root_minimax C []).2.2.2.2.1 θ)
    simp only [ev,decide_eq_true_eq] at bound
    exact ⟨h,tr,ev,out,bound⟩
  · rintro ⟨cap,good⟩
    refine ⟨⟨cap,fun θ => ?_⟩,fun θ _ => ?_⟩
    · obtain ⟨h,tr,ev,out,_⟩ := good θ
      exact ⟨h,tr,ev,out⟩
    · obtain ⟨h,tr,ev,_,bound⟩ := good θ
      simpa only [ev,decide_eq_true_eq] using bound

/-- Additional price certification uses exactly the existing finite universe. -/
def synthesizeLiteral (C : LiteralRow) (r K q ell : Nat) :=
  (boundedCandidates C K).find? (fun A => literalCheck A.2.2 r q ell)

private theorem weighted_carrier_complete {C : LiteralRow} (θ₀ : Chart C)
    {Q H : Type} [Fintype Q] [Fintype H]
    (T : RootTable C Q H) (c : Chart C → Q ⊕ H) (r q ell : Nat)
    (cap : (Set.range c).ncard ≤ r)
    (correct : ∀ θ, ∃ h tr, evaluate (rootStep T θ.val) q (c θ) = some (h,tr) ∧
      T.out h = target C θ.val ∧ rootCost T tr ≤ ell) :
    ∃ A ∈ candidates C (Fintype.card Q) (Fintype.card H),
      literalCheck A r q ell = true := by
  classical
  let e := Fintype.equivFin Q
  let f := Fintype.equivFin H
  let out (h : H) := if T.out h ∈ outputList C then T.out h else computedTarget C θ₀.val
  have outmem (h : H) : out h ∈ outputList C := by
    dsimp only [out]
    split_ifs with hh
    · exact hh
    · exact List.mem_map.mpr ⟨θ₀,(finite_root_minimax C []).2.2.2.2.1 θ₀,rfl⟩
  let T' : RootTable C (Fin (Fintype.card Q)) (Fin (Fintype.card H)) :=
    ⟨fun s => T.coord (e.symm s),
     fun s z => Sum.map e f (T.next (e.symm s) z),fun h => out (f.symm h)⟩
  let c' : Chart C → Fin (Fintype.card Q) ⊕ Fin (Fintype.card H) := fun θ => Sum.map e f (c θ)
  let A : Candidate C (Fintype.card Q) (Fintype.card H) := ⟨T',c'⟩
  refine ⟨A,candidate_complete T' c' (fun h => outmem _),
    (literalCheck_spec A r q ell).mpr ⟨?_,?_⟩⟩
  · have eq : Set.range c' = Sum.map e f '' Set.range c := Set.range_comp (Sum.map e f) c
    change (Set.range c').ncard ≤ r
    rw [eq]
    exact (Set.ncard_image_le (f := Sum.map e f) (s := Set.range c)).trans cap
  · intro θ
    obtain ⟨h,tr,ev,output,cost⟩ := correct θ
    have mapped := evaluate_reindex e f (rootStep T θ.val) (rootStep T' θ.val)
      (by intro s; simp [rootStep,T']) q (c θ)
    refine ⟨f h,tr.map e,?_,?_,?_⟩
    · simpa only [ev,Option.map_some] using mapped
    · change out (f.symm (f h)) = target C θ.val
      rw [f.symm_apply_apply]
      have hm : T.out h ∈ outputList C := List.mem_map.mpr
        ⟨θ,(finite_root_minimax C []).2.2.2.2.1 θ,
          ((finite_root_minimax C []).2.2.2.2.2 θ.val).trans output.symm⟩
      simp only [out,if_pos hm,output]
    · change rootCost T' (tr.map e) ≤ ell
      simpa [rootCost,T',List.map_map,Function.comp_def] using cost

/-- The checked table itself installs shortest physical words and genuine
acquired initial codes on every original actual origin. -/
theorem literal_candidate_sound (P : CutSet) (hP : CutPrefixFree P) (u₀ : Source)
    (r K q ell a b : Nat)
    (A : Candidate (canonicalRow P (substitution u₀)) a b)
    (size : a+b ≤ K) (accepted : literalCheck A r q ell = true) :
    (Set.range (exportCode hP u₀ A.color)).ncard ≤ r ∧
    Fintype.card (Fin a ⊕ Fin b) ≤ K ∧
    ∀ (v : ImageValues (canonicalRow P (substitution u₀)))
      (u : OriginFiber P (canonicalRow P (substitution u₀))),
      substitution u.val = evaluateRow (extend (canonicalRow P (substitution u₀)) v.val.val)
        (canonicalRow P (substitution u₀)) →
      ∃ h tr, Run (installShortest A.table) (substitution u.val)
        (exportCode hP u₀ A.color v) tr h ∧
        A.table.out h = canonicalRow P u.val ∧ tr.length ≤ q ∧
        nativeCost (installShortest A.table) tr ≤ ell := by
  have checked := (literalCheck_spec A r q ell).mp accepted
  have bridge := install_full_fiber P hP u₀ A.table A.color
  refine ⟨?_,by simpa using size,?_⟩
  · rw [bridge.1]; exact checked.1
  · intro v u image
    let θ : Chart _ := ⟨types _ v.val.val,actual_type P hP (substitution u₀) v⟩
    obtain ⟨h,tr,ev,out,cost⟩ := checked.2 θ
    rw [← shortest_paths P hP u₀ A.table v u image q (A.color θ)] at ev
    obtain ⟨run,calls⟩ := (native_evaluate_iff _ _ _ _ _ _).mp ev
    exact ⟨h,tr,run,out.trans (bridge.2 v u image).1,calls,cost⟩

/-- Finite synthesis is equivalent to the original four-budget full-fiber
problem. No state-union acyclicity or original source-size bound is required. -/
theorem finite_literal_synthesis (P : CutSet) (hP : CutPrefixFree P)
    (u₀ : Source) (r K q ell : Nat) (hr : 1 ≤ r) (hK : 1 ≤ K) :
    (synthesizeLiteral (canonicalRow P (substitution u₀)) r K q ell).isSome = true ↔
      NativeLiteralFeasible P (canonicalRow P (substitution u₀)) r K q ell := by
  classical
  constructor
  · intro hs
    obtain ⟨⟨a,b,A⟩,hA⟩ := Option.isSome_iff_exists.mp hs
    have accepted := List.find?_some hA
    have size := (bounded_size (List.mem_of_find?_eq_some hA)).2
    exact ⟨Fin a,Fin b,inferInstance,inferInstance,installShortest A.table,
      exportCode hP u₀ A.color,literal_candidate_sound P hP u₀ r K q ell a b A size accepted⟩
  · intro feasible
    rcases (literal_moore_feasibility P hP u₀ r K q ell hr hK).mp feasible with
      ⟨Q,H,fQ,fH,T,c,cap,states,correct⟩
    let _ := fQ
    let _ := fH
    let θ₀ := referenceType P hP u₀
    obtain ⟨A,mem,accepted⟩ := weighted_carrier_complete θ₀ T c r q ell cap correct
    have pos : 1 ≤ Fintype.card Q + Fintype.card H := by
      have nonempty : Nonempty (Q ⊕ H) := ⟨c θ₀⟩
      let _ := nonempty
      have hp := Fintype.card_pos (α := Q ⊕ H)
      simp only [Fintype.card_sum] at hp
      omega
    have bound : Fintype.card Q+Fintype.card H ≤ K := by simpa using states
    have inList := bounded_mem pos bound mem
    by_contra no
    have none : synthesizeLiteral (canonicalRow P (substitution u₀)) r K q ell = none := by
      cases h : synthesizeLiteral (canonicalRow P (substitution u₀)) r K q ell <;> simp_all
    exact (List.find?_eq_none.mp none _ inList) accepted



theorem zero_call_literal (C : LiteralRow) (r K q ell : Nat)
    (old : RootFeasible C r K 0) : RootLiteralFeasible C r K q ell := by
  rcases old with ⟨Q,H,fQ,fH,T,c,cap,states,correct⟩
  refine ⟨Q,H,fQ,fH,T,c,cap,states,?_⟩
  intro θ
  obtain ⟨h,tr,ev,out⟩ := correct θ
  cases hc : c θ with
  | inl s => simp [hc,evaluate] at ev
  | inr z =>
      rw [hc,evaluate_halt] at ev
      cases Option.some.inj ev
      exact ⟨h,[],by rw [evaluate_halt],out,Nat.zero_le _⟩

private theorem zero_price_empty {C : LiteralRow} {Q H : Type}
    (T : RootTable C Q H) (positive : ∀ d, 0 < price C d)
    (tr : List Q) (cost : rootCost T tr ≤ 0) : tr = [] := by
  cases tr with
  | nil => rfl
  | cons s tr =>
      have pos := positive (T.coord s)
      simp only [rootCost,List.map_cons,List.sum_cons] at cost
      omega

/-- Both zero-budget endpoints on the unchanged full fiber, including root,
empty and blocked cuts. The unused upper budget remains arbitrary. -/
theorem zero_budget_endpoint (P : CutSet) (hP : CutPrefixFree P) (u₀ : Source)
    (r K q ell : Nat) (hr : 1 ≤ r) (hK : 1 ≤ K) (zero : q = 0 ∨ ell = 0) :
    NativeLiteralFeasible P (canonicalRow P (substitution u₀)) r K q ell ↔
      targetCount (canonicalRow P (substitution u₀)) ≤ r ∧
      targetCount (canonicalRow P (substitution u₀)) ≤ K := by
  rw [literal_moore_feasibility P hP u₀ r K q ell hr hK]
  constructor
  · intro feasible
    by_cases root : [] ∈ P
    · have cut : P = {[]} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        exact ⟨root,fun a ha => (hP root ha (by simp)).symm⟩
      have row : canonicalRow P (substitution u₀) = .of (.inr 0) := by
        subst P
        cases ht : substitution u₀ <;>
          simp [canonicalRow,literalRow,classOrdinal,firstEqIndex,orderedHoles,
            reachedHoles,subtree]
      have count : targetCount (canonicalRow P (substitution u₀)) = 1 := by
        rw [row]; decide +kernel
      simpa only [count] using And.intro hr hK
    · rcases feasible with ⟨Q,H,fQ,fH,T,c,cap,states,correct⟩
      let _ := fQ
      let _ := fH
      apply (zero_call_endpoint _ r K).mp
      refine ⟨Q,H,fQ,fH,T,c,cap,states,?_⟩
      intro θ
      obtain ⟨h,tr,ev,out,cost⟩ := correct θ
      rcases zero with hq | he
      · subst q
        exact ⟨h,tr,ev,out⟩
      · have positive (d : Classes (canonicalRow P (substitution u₀))) :
            0 < price (canonicalRow P (substitution u₀)) d := by
          have mem := (List.mem_filter.mp (shortest_spec _ d).1).1
          have cut := ((canonicalRow_reached P hP (substitution u₀) _).mp mem).1
          change 0 < (shortest _ d).length
          by_contra hn
          have nil : shortest _ d = [] := List.length_eq_zero_iff.mp (by omega)
          exact root (nil ▸ cut)
        have nil := zero_price_empty T positive tr (he ▸ cost)
        subst tr
        exact ⟨h,[],evaluate_exact _ ev,out⟩
  · intro bounds
    exact zero_call_literal _ r K q ell ((zero_call_endpoint _ r K).mpr bounds)

/-- Original right-hole input: one running state and two complete-output
halts. This is the first input to the literal checker, not a second model. -/
def rightHoleInput : Candidate (.mul (.of (.inl false)) (.of (.inr 0))) 1 2 where
  table := {
    coord := fun _ => ⟨0,by simp [labels]⟩
    next := fun _ z => if z = .alpha then .inr 0 else .inr 1
    out := fun h => if h = 0 then .of (.inl false)
      else .mul (.of (.inl true)) (.of (.inr 0)) }
  color := fun _ => .inl 0

/-- The four-state native table includes the initial empty-word query. -/
def emptyThenRight : Controller (Fin 2) (Fin 2) where
  addr s := if s = 0 then [] else [true]
  next s z := if s = 0 then .inl 1 else if z = .alpha then .inr 0 else .inr 1
  out := rightHoleInput.table.out

#print axioms zero_budget_endpoint
#print axioms finite_literal_synthesis
#print axioms literal_candidate_sound
#print axioms literal_geometry
#print axioms contract_run
#print axioms literal_moore_feasibility

end D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeLiteralMoore
