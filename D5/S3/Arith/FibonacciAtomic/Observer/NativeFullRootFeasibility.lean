/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Whole actual-fiber predecessor feasibility is exactly finite class-root feasibility at the same capacity and call budget. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootSimulation
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSharpPredecessorFiber
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open ActualCutPartitionRecovery
open NativeCutFibers
open NativeClassRootImage
open NativeClassRootSimulation
open NativePassiveServiceRealization (Dialogue)
open NativeSerialMachine (Op Event Trace Run Replay answers reads)
open NativePredecessorRowRecovery (H back)

/-- No update occurs in an actual stationary run. The controller and all
unreachable behavior are unrestricted. -/
def Stationary (t : Trace) : Prop := ∀ n, Event.update n ∉ t

/-- A finite local segment is selected only when replay reaches a boundary.
The default imposes no termination condition on any unreachable computation. -/
private def next {K : Type} (δ : K → Op K LiteralRow) (fallback : LiteralRow)
    (c : K) : Op K LiteralRow := by
  classical
  exact if h : ∃ s b, Replay δ c 0 [] s b then δ h.choose_spec.choose.1
  else .stop fallback

private theorem next_replay {K : Type} (δ : K → Op K LiteralRow)
    (fallback : LiteralRow) {c : K} {s : Trace} {b : NativeSerialMachine.Boundary K LiteralRow}
    (p : Replay δ c 0 [] s b) : next δ fallback c = δ b.1 := by
  classical
  have h : ∃ s b, Replay δ c 0 [] s b := ⟨s,b,p⟩
  rw [next, dif_pos h]
  have eq := (NativeSerialMachine.replay_deterministic h.choose_spec.choose_spec p).2
  exact congrArg (fun b => δ b.1) eq

private theorem next_local {K : Type} (δ : K → Op K LiteralRow)
    (fallback : LiteralRow) {c c' : K} (step : δ c = .localStep c')
    {r : Source} {t : Trace} {o : LiteralRow} (run : Run δ c' 0 r t o) :
    next δ fallback c = next δ fallback c' := by
  obtain ⟨s,b,p,_,_,_⟩ := NativeSerialMachine.reached_prefix_replay run [] List.nil_prefix
  exact (next_replay δ fallback (Replay.localStep step p)).trans
    (next_replay δ fallback p).symm

/-- Bounded unrolling keeps Stop at depth zero and replaces further reads by
an arbitrary common halt. Local work is replayed without charging a query. -/
private def normalize {K : Type} (δ : K → Op K LiteralRow) (fallback : LiteralRow) :
    Nat → K → Dialogue LiteralRow
  | 0, c => match next δ fallback c with
      | .stop o => .stop o
      | _ => .stop fallback
  | n+1, c => match next δ fallback c with
      | .stop o => .stop o
      | .read a k => .read a (normalize δ fallback n (k .alpha))
          (normalize δ fallback n (k .beta)) (normalize δ fallback n (k .branch))
          (normalize δ fallback n (k .absent))
      | _ => .stop fallback

private theorem normalize_depth {K : Type} (δ : K → Op K LiteralRow)
    (fallback : LiteralRow) (n : Nat) (c : K) : nativeDepth (normalize δ fallback n c) ≤ n := by
  induction n generalizing c with
  | zero => cases hn : next δ fallback c <;> simp [normalize,hn,nativeDepth]
  | succ n ih =>
      cases hn : next δ fallback c <;> simp only [normalize,hn,nativeDepth]
      all_goals first | omega | exact Nat.add_le_add_right (max_le (max_le (ih _) (ih _)) (max_le (ih _) (ih _))) 1

private theorem normalize_run {K : Type} (δ : K → Op K LiteralRow)
    (fallback : LiteralRow) {c : K} {r : Source} {t : Trace} {o : LiteralRow}
    (run : Run δ c 0 r t o) (stationary : Stationary t) (n : Nat)
    (budget : (answers t).length ≤ n) :
    nativeRun (fun a => readout a r) (normalize δ fallback n c) = (o,(answers t).length) := by
  have aux : ∀ {e : Nat} {c : K} {r : Source} {t : Trace} {o : LiteralRow},
      Run δ c e r t o → e = 0 → Stationary t → ∀ n, (answers t).length ≤ n →
      nativeRun (fun a => readout a r) (normalize δ fallback n c) = (o,(answers t).length) := by
    intro e c r t o run
    induction run with
    | @stop c e r o step =>
        intro he _ n _
        subst e
        have hn := (next_replay δ fallback (Replay.stop step)).trans step
        cases n <;> simp [normalize,hn,nativeRun,answers,reads]
    | @localStep c c' e r t o step run ih =>
        intro he hs n hb
        subst e
        have tail : Stationary _ := fun m hm => hs m (List.mem_cons_of_mem _ hm)
        have hn := next_local δ fallback step run
        have eq : normalize δ fallback n c = normalize δ fallback n c' := by
          cases n <;> simp only [normalize,hn]
        rw [eq]
        exact ih rfl tail n hb
    | update step run ih =>
        intro _ hs _ _
        exact False.elim (hs _ List.mem_cons_self)
    | @read c e r a k y t o step hy run ih =>
        intro he hs n hb
        subst e
        have tail : Stationary t := fun m hm => hs m (List.mem_cons_of_mem _ hm)
        have hn := (next_replay δ fallback (Replay.await step)).trans step
        cases n with
        | zero => simp [answers,reads] at hb
        | succ n =>
            have hb' : (answers t).length ≤ n := by simpa [answers,reads] using hb
            have ht := ih rfl tail n hb'
            cases y <;> simpa [normalize,hn,nativeRun,hy,answers,reads] using
              congrArg (fun out : LiteralRow × Nat => (out.1,out.2+1)) ht
  exact aux run rfl stationary n budget

/-- Alpha at a visible exterior root is a concrete alpha or the alpha class.
A pair never counts as a literal leaf. -/
def VisibleAlpha (C : LiteralRow) (θ : Classes C → Option Bool) (a : Address) : Prop :=
  ∃ e, rowAt a C = some e ∧ lit (typeExtend C θ) true e

/-- Repair is occurrence-sensitive: two occurrences sharing a class can have
different old/new status. The root occurrence is always old. -/
def oldMask (C : LiteralRow) (θ : Classes C → Option Bool) : CutSet := by
  classical
  exact (holeAddresses [] C).toFinset.filter fun p =>
    ¬ ∃ q d, p = q ++ [d] ∧ VisibleAlpha C θ (q ++ [true])

/-- The complete target is the existing occurrence-repair decoder, with a
fallback that is never used on the admissible chart. -/
def target (C : LiteralRow) (θ : Classes C → Option Bool) : LiteralRow :=
  (back C (oldMask C θ)).getD (.of (.inl true))

private theorem visible_alpha (P : CutSet) (hP : CutPrefixFree P) (t₀ : Source)
    (v : ImageValues (canonicalRow P t₀)) (u : OriginFiber P (canonicalRow P t₀))
    (image : substitution u.val = evaluateRow (extend (canonicalRow P t₀) v.val.val) (canonicalRow P t₀))
    (a : Address) (avoid : ∀ s : Address, s.IsPrefix a → s ≠ a → s ∉ P) :
    VisibleAlpha (canonicalRow P t₀) (types (canonicalRow P t₀) v.val.val) a ↔
      subtree a (substitution u.val) = some (.of true) := by
  let C := canonicalRow P t₀
  have roots := root_extend C v.val.val
  constructor
  · rintro ⟨e,he,ha⟩
    have ev : evaluateRow (extend C v.val.val) e = .of true :=
      (evaluate_leaf e _ true).mpr (by rwa [roots])
    rw [image, rowAt_evaluate C _ a e he, ev]
  · intro ha
    have loc := literalRow_at P (substitution u.val) [] a (substitution u.val)
      (by simpa using avoid)
    have atrow : rowAt a (canonicalRow P (substitution u.val)) =
        some (literalRow P (substitution u.val) a (.of true)) := by
      simpa [canonicalRow,ha] using loc
    have located : rowAt a C = some (literalRow P (substitution u.val) a (.of true)) := by
      simpa only [u.property] using atrow
    refine ⟨_,located,?_⟩
    have ev := rowAt_evaluate C (extend C v.val.val) a _ located
    rw [← image, ha] at ev
    have leaf : evaluateRow (extend C v.val.val)
        (literalRow P (substitution u.val) a (.of true)) = .of true :=
      (Option.some.inj ev).symm
    rw [← roots]
    exact (evaluate_leaf _ _ true).mp leaf

private theorem sibling_avoid (P : CutSet) (hP : CutPrefixFree P)
    (q : Address) (d : Bool) (hp : q ++ [d] ∈ P) :
    ∀ s : Address, s.IsPrefix (q ++ [true]) → s ≠ q ++ [true] → s ∉ P := by
  intro s hs hn hm
  have sl : s.length ≤ q.length := by
    have le := hs.length_le
    have ne : s.length ≠ (q ++ [true]).length := fun h => hn (hs.eq_of_length h)
    simp only [List.length_append,List.length_singleton] at le ne
    omega
  have sq : s.IsPrefix q :=
    List.prefix_of_prefix_length_le hs (List.prefix_append q [true]) sl
  have sp : s.IsPrefix (q ++ [d]) := sq.trans (List.prefix_append q [d])
  have eq := hP hm hp sp
  have len := congrArg List.length eq
  simp only [List.length_append,List.length_singleton] at len
  omega

private theorem children_present (q : Address) (v : Source) (d : Bool) :
    (subtree (q ++ [d]) v).isSome = (subtree (q ++ [true]) v).isSome := by
  have app := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [app,app]
  cases h : subtree q v with
  | none => rfl
  | some t => cases t with
    | of b => cases d <;> rfl
    | mul l r => cases d <;> rfl

private theorem mask_correct (P : CutSet) (hP : CutPrefixFree P) (t₀ : Source)
    (v : ImageValues (canonicalRow P t₀)) (u : OriginFiber P (canonicalRow P t₀))
    (image : substitution u.val = evaluateRow (extend (canonicalRow P t₀) v.val.val) (canonicalRow P t₀)) :
    oldMask (canonicalRow P t₀) (types (canonicalRow P t₀) v.val.val) = H P u.val := by
  classical
  have support (p : Address) : p ∈ H P u.val ↔ p ∈ P ∧ (subtree p u.val).isSome :=
    by simpa [H] using canonicalRow_reached P hP u.val p
  have current (p : Address) : p ∈ (holeAddresses [] (canonicalRow P t₀)).toFinset ↔
      p ∈ P ∧ (subtree p (substitution u.val)).isSome := by
    simpa only [u.property,List.mem_toFinset] using canonicalRow_reached P hP (substitution u.val) p
  ext p
  simp only [oldMask,Finset.mem_filter]
  constructor
  · rintro ⟨hp,hn⟩
    have hc := (current p).mp hp
    apply (support p).mpr
    refine ⟨hc.1,?_⟩
    induction p using List.reverseRecOn with
    | nil => simp [subtree]
    | append_singleton q d ih =>
        have pr : (subtree (q ++ [true]) (substitution u.val)).isSome := by
          simpa [children_present q (substitution u.val) d] using hc.2
        have nb : ¬ subtree (q ++ [true]) u.val = none := by
          intro h
          have alpha := (NativeSharpPredecessorFiber.right_birth q u.val pr).mp h
          exact hn ⟨q,d,rfl,(visible_alpha P hP t₀ v u image _
            (sibling_avoid P hP q d hc.1)).mpr alpha⟩
        have old : (subtree (q ++ [true]) u.val).isSome := by
          cases h : subtree (q ++ [true]) u.val <;> simp_all
        simpa [children_present q u.val d] using old
  · intro hp
    have old := (support p).mp hp
    obtain ⟨t,ht⟩ := Option.isSome_iff_exists.mp old.2
    have transport : subtree p (substitution u.val) = some (substitution t) := by
      simpa using NativeDepthPatterns.original_present_transport 1 p u.val t ht
    refine ⟨(current p).mpr ⟨old.1,by simp [transport]⟩,?_⟩
    rintro ⟨q,d,eq,alpha⟩
    subst p
    have pr : (subtree (q ++ [true]) (substitution u.val)).isSome := by
      rw [← children_present q (substitution u.val) d]
      simp [transport]
    have new := (NativeSharpPredecessorFiber.right_birth q u.val pr).mpr
      ((visible_alpha P hP t₀ v u image _ (sibling_avoid P hP q d old.1)).mp alpha)
    have same := children_present q u.val d
    rw [new] at same
    simpa using same.symm.trans old.2

private theorem factorization (P : CutSet) (hP : CutPrefixFree P) (t₀ : Source)
    (v : ImageValues (canonicalRow P t₀)) (u : OriginFiber P (canonicalRow P t₀))
    (image : substitution u.val = evaluateRow (extend (canonicalRow P t₀) v.val.val) (canonicalRow P t₀)) :
    back (canonicalRow P t₀) (oldMask (canonicalRow P t₀) (types (canonicalRow P t₀) v.val.val)) =
      some (canonicalRow P u.val) ∧
    target (canonicalRow P t₀) (types (canonicalRow P t₀) v.val.val) = canonicalRow P u.val := by
  have mask := mask_correct P hP t₀ v u image
  have decode := (NativePredecessorRowRecovery.native_predecessor_row_recovery P hP).1 u.val
  rw [u.property,← mask] at decode
  exact ⟨decode,by simp [target,decode]⟩

private theorem origin_values (P : CutSet) (hP : CutPrefixFree P) (t₀ : Source)
    (u : OriginFiber P (canonicalRow P t₀)) :
    ∃ v : ImageValues (canonicalRow P t₀),
      substitution u.val = evaluateRow (extend (canonicalRow P t₀) v.val.val) (canonicalRow P t₀) := by
  let v := recover P hP (canonicalRow P t₀) ⟨substitution u.val,u.property⟩
  have fill := recover_fill P hP (canonicalRow P t₀) ⟨substitution u.val,u.property⟩
  exact ⟨⟨v,⟨u.val,fill.symm⟩⟩,fill.symm⟩

theorem actual_type (P : CutSet) (hP : CutPrefixFree P) (t₀ : Source)
    (v : ImageValues (canonicalRow P t₀)) : Admissible (canonicalRow P t₀) (types (canonicalRow P t₀) v.val.val) := by
  obtain ⟨u,hu⟩ := v.property
  have row : canonicalRow P (substitution u) = canonicalRow P t₀ := by
    rw [hu]
    exact legal_values_row P hP t₀ v.val
  apply (class_root_chart P hP t₀ _).mpr
  refine ⟨⟨u,row⟩,?_⟩
  have fill := recover_fill P hP (canonicalRow P t₀) ⟨substitution u,row⟩
  have eq := (rowFiberEquiv P hP t₀).injective
    (Subtype.ext (fill.trans hu))
  have val : (recover P hP (canonicalRow P t₀) ⟨substitution u,row⟩).val = v.val.val :=
    congrArg Subtype.val eq
  rw [val]

/-- Joint existence permits an arbitrary ambient payload type. Its actual
complete range must be finite as well as cardinally bounded. Entry is a
function of that complete value and the fixed common data alone. -/
def InvFeas (P : CutSet) (C : LiteralRow) (r q : Nat) : Prop :=
  ∃ (S K : Type) (σ : ImageValues C → S) (entry : S → K) (δ : K → Op K LiteralRow),
    (Set.range σ).Finite ∧ (Set.range σ).ncard ≤ r ∧
    ∀ (v : ImageValues C) (u : OriginFiber P C),
      substitution u.val = evaluateRow (extend C v.val.val) C →
      ∃ t, Run δ (entry (σ v)) 0 (substitution u.val) t (canonicalRow P u.val) ∧
        Stationary t ∧ (answers t).length ≤ q

/-- Only used colors require a depth bound. Edges that no admissible input
reaches are still finite tree edges and may have arbitrary outputs. -/
def RootFeas (C : LiteralRow) (r q : Nat) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (c : Chart C → S) (E : S → RootTree C LiteralRow),
    1 ≤ Fintype.card S ∧ Fintype.card S ≤ r ∧
    ∀ θ, (rootRun θ.val (E (c θ))).1 = target C θ.val ∧ rootDepth (E (c θ)) ≤ q

/-- Each experiment really invokes the native port at the row-determined
representative. The fourth, unreachable absent edge halts immediately. -/
def install (C : LiteralRow) (fallback : LiteralRow) : RootTree C LiteralRow → Dialogue LiteralRow
  | .stop o => .stop o
  | .ask d A B E => .read (NativeWholeRowService.representative C d)
      (install C fallback A) (install C fallback B) (install C fallback E) (.stop fallback)

/-- A native dialogue supplies a deterministic common controller. -/
def controller : Dialogue LiteralRow → Op (Dialogue LiteralRow) LiteralRow
  | .stop o => .stop o
  | .read a A B E D => .read a (fun y => match y with
      | .alpha => A | .beta => B | .branch => E | .absent => D)

private theorem representative_reply (C : LiteralRow) (v : Classes C → Source)
    (d : Classes C) :
    readout (NativeWholeRowService.representative C d) (evaluateRow (extend C v) C) =
      NativeClassRootPadding.rootReply (types C v d) := by
  have app := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have loc := NativeWholeRowService.representative_subtree C v d
  rw [← List.append_nil (NativeWholeRowService.representative C d),app,loc]
  change readout [] (v d) = NativeClassRootPadding.rootReply (rootType (v d))
  cases v d with
  | of b => cases b <;> rfl
  | mul l r => rfl

theorem install_correct (C : LiteralRow) (fallback : LiteralRow)
    (T : RootTree C LiteralRow) (v : Classes C → Source) :
    nativeRun (fun a => readout a (evaluateRow (extend C v) C)) (install C fallback T) =
      rootRun (types C v) T ∧ nativeDepth (install C fallback T) = rootDepth T := by
  induction T with
  | stop o => exact ⟨rfl,rfl⟩
  | ask d A B E ihA ihB ihE =>
      refine ⟨?_,?_⟩
      · simp only [install,nativeRun,representative_reply,rootRun]
        cases h : types C v d with
        | none => simpa [NativeClassRootPadding.rootReply,h] using
            congrArg (fun out : LiteralRow × Nat => (out.1,out.2+1)) ihE.1
        | some b => cases b <;> simp only [NativeClassRootPadding.rootReply] <;>
            first
            | exact congrArg (fun out : LiteralRow × Nat => (out.1,out.2+1)) ihA.1
            | exact congrArg (fun out : LiteralRow × Nat => (out.1,out.2+1)) ihB.1
      · simp [install,nativeDepth,rootDepth,ihA.2,ihB.2,ihE.2]

theorem dialogue_run (T : Dialogue LiteralRow) (t : Source) :
    ∃ tr, Run controller T 0 t tr (nativeRun (fun a => readout a t) T).1 ∧
      Stationary tr ∧ (answers tr).length = (nativeRun (fun a => readout a t) T).2 := by
  induction T with
  | stop o => exact ⟨[],Run.stop rfl,by simp [Stationary],rfl⟩
  | read a A B E D ihA ihB ihE ihD =>
      have tail : ∃ tr, Run controller (match readout a t with
          | .alpha => A | .beta => B | .branch => E | .absent => D) 0 t tr
          (nativeRun (fun a => readout a t) (match readout a t with
            | .alpha => A | .beta => B | .branch => E | .absent => D)).1 ∧
        Stationary tr ∧ (answers tr).length =
          (nativeRun (fun a => readout a t) (match readout a t with
            | .alpha => A | .beta => B | .branch => E | .absent => D)).2 := by
        cases readout a t
        · exact ihA
        · exact ihB
        · exact ihE
        · exact ihD
      obtain ⟨tr,run,hs,hc⟩ := tail
      refine ⟨Event.read 0 a (readout a t)::tr,?_,?_,?_⟩
      · have rr := Run.read (c := Dialogue.read a A B E D) (δ := controller)
          (k := fun y => match y with
            | .alpha => A | .beta => B | .branch => E | .absent => D) rfl rfl run
        cases hy : readout a t <;> simpa [nativeRun,hy] using rr
      · intro n
        simp only [List.mem_cons,reduceCtorEq,false_or]
        exact hs n
      · cases hy : readout a t <;> simpa [nativeRun,answers,reads,hy] using
          congrArg (fun n : Nat => n+1) hc

theorem native_calls (T : Dialogue LiteralRow) (t : Source) :
    (nativeRun (fun a => readout a t) T).2 ≤ nativeDepth T := by
  induction T with
  | stop o => exact Nat.le_refl 0
  | read a A B E D ihA ihB ihE ihD =>
      cases hy : readout a t <;> simp only [nativeRun,hy,nativeDepth] <;> omega

private theorem coloring_range (P : CutSet) (hP : CutPrefixFree P) (t₀ : Source)
    (S : Type) (c : Chart (canonicalRow P t₀) → S) :
    Set.range (fun v : ImageValues (canonicalRow P t₀) =>
      c ⟨types (canonicalRow P t₀) v.val.val,actual_type P hP t₀ v⟩) = Set.range c := by
  ext s
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨_,rfl⟩
  · rintro ⟨θ,rfl⟩
    obtain ⟨v,u,image,ht,_,_⟩ := NativeClassRootPadding.padded_native_query_chart
      P hP t₀ 0 θ.val θ.property
    refine ⟨v,?_⟩
    exact congrArg c (Subtype.ext ht)

private theorem sufficient (P : CutSet) (hP : CutPrefixFree P) (t₀ : Source)
    (r q : Nat) (feasible : RootFeas (canonicalRow P t₀) r q) :
    InvFeas P (canonicalRow P t₀) r q := by
  classical
  rcases feasible with ⟨S,fs,c,E,_,cap,correct⟩
  let _ := fs
  let C := canonicalRow P t₀
  let fallback : LiteralRow := .of (.inl true)
  let θ (v : ImageValues C) : Chart C := ⟨types C v.val.val,actual_type P hP t₀ v⟩
  let σ (v : ImageValues C) : S := c (θ v)
  let entry (s : S) : Dialogue LiteralRow := install C fallback (E s)
  refine ⟨S,Dialogue LiteralRow,σ,entry,controller,Set.toFinite _,?_,?_⟩
  · have range := coloring_range P hP t₀ S c
    change Set.range σ = Set.range c at range
    rw [range]
    exact (Set.ncard_le_card _).trans (by simpa only [Nat.card_eq_fintype_card] using cap)
  · intro v u image
    have sim := install_correct C fallback (E (σ v)) v.val.val
    have same : nativeRun (fun a => readout a (substitution u.val)) (entry (σ v)) =
        rootRun (θ v).val (E (c (θ v))) := by
      simpa only [image] using sim.1
    have output : (nativeRun (fun a => readout a (substitution u.val)) (entry (σ v))).1 =
        canonicalRow P u.val :=
      (congrArg Prod.fst same).trans ((correct (θ v)).1.trans
        (factorization P hP t₀ v u image).2)
    obtain ⟨tr,run,stationary,calls⟩ := dialogue_run (entry (σ v)) (substitution u.val)
    refine ⟨tr,?_,stationary,?_⟩
    · simpa only [output] using run
    · rw [calls]
      apply (native_calls (entry (σ v)) (substitution u.val)).trans
      change nativeDepth (install C fallback (E (σ v))) ≤ q
      rw [sim.2]
      exact (correct (θ v)).2

private theorem necessary (P : CutSet) (hP : CutPrefixFree P) (u₀ : Source)
    (r q : Nat) (feasible : InvFeas P (canonicalRow P (substitution u₀)) r q) :
    RootFeas (canonicalRow P (substitution u₀)) r q := by
  classical
  let C := canonicalRow P (substitution u₀)
  rcases feasible with ⟨S,K,σ,entry,δ,finite,cap,correct⟩
  let Used := Set.range σ
  let _ : Fintype Used := finite.fintype
  let σ' (v : ImageValues C) : Used := ⟨σ v,⟨v,rfl⟩⟩
  let fallback : LiteralRow := .of (.inl true)
  let E (s : Used) : Dialogue LiteralRow := normalize δ fallback q (entry s.val)
  have budget (s : Used) : nativeDepth (E s) ≤ q := normalize_depth δ fallback q (entry s.val)
  have normalized : ∀ (v : ImageValues C) (u : OriginFiber P C),
      substitution u.val = evaluateRow (extend C v.val.val) C →
      (nativeRun (fun a => readout a (substitution u.val)) (E (σ' v))).1 = canonicalRow P u.val := by
    intro v u image
    obtain ⟨tr,run,stationary,calls⟩ := correct v u image
    exact congrArg Prod.fst (normalize_run δ fallback run stationary q calls)
  obtain ⟨v,u,c,sim⟩ := truthful_joint_root_simulation P hP (substitution u₀)
    Used σ' E q budget normalized
  obtain ⟨v₀,_⟩ := origin_values P hP (substitution u₀) ⟨u₀,rfl⟩
  let _ : Nonempty Used := ⟨σ' v₀⟩
  refine ⟨Used,inferInstance,c,fun s => compileRoot C (E s),?_,?_,?_⟩
  · exact Fintype.card_pos
  · simpa only [Set.fintypeCard_eq_ncard] using cap
  · intro θ
    have h := sim θ
    have factor := (factorization P hP (substitution u₀) (v θ) (u θ) h.1).2
    rw [h.2.1] at factor
    exact ⟨h.2.2.2.1.trans factor.symm,h.2.2.2.2.2⟩

/-- Complete full-fiber same-r,q reduction. A reference origin merely specifies
an arbitrary nonempty complete current row. The common reader entry depends
only on the complete truthful payload and fixed common data. Acquisition,
export and lawful installation are external paid premises. -/
theorem native_full_root_feasibility (P : CutSet) (hP : CutPrefixFree P)
    (u₀ : Source) (r q : Nat) (hr : 1 ≤ r) :
    let C := canonicalRow P (substitution u₀)
    (∀ (v : ImageValues C) (u : OriginFiber P C),
      substitution u.val = evaluateRow (extend C v.val.val) C →
      oldMask C (types C v.val.val) = H P u.val ∧
      back C (oldMask C (types C v.val.val)) = some (canonicalRow P u.val) ∧
      target C (types C v.val.val) = canonicalRow P u.val) ∧
    (∀ θ : Chart C, ∃ row : LiteralRow, back C (oldMask C θ.val) = some row) ∧
    (∀ (v : ImageValues C) (d : Classes C),
      subtree (NativeWholeRowService.representative C d) (evaluateRow (extend C v.val.val) C) =
        some (v.val.val d) ∧
      readout (NativeWholeRowService.representative C d) (evaluateRow (extend C v.val.val) C) =
        NativeClassRootPadding.rootReply (types C v.val.val d)) ∧
    (InvFeas P C r q ↔ RootFeas C r q) := by
  dsimp only
  refine ⟨?_,?_,?_,⟨necessary P hP u₀ r q,sufficient P hP (substitution u₀) r q⟩⟩
  · intro v u image
    exact ⟨mask_correct P hP (substitution u₀) v u image,
      factorization P hP (substitution u₀) v u image⟩
  · intro θ
    obtain ⟨v,u,image,ht,_,_⟩ := NativeClassRootPadding.padded_native_query_chart
      P hP (substitution u₀) 0 θ.val θ.property
    refine ⟨canonicalRow P u.val,?_⟩
    have decode := (factorization P hP (substitution u₀) v u image).1
    rwa [ht] at decode
  · intro v d
    exact ⟨NativeWholeRowService.representative_subtree _ v.val.val d,
      representative_reply _ v.val.val d⟩

#print axioms native_full_root_feasibility
end D5.S3.Arith.FibonacciAtomic.Observer.NativeFullRootFeasibility
