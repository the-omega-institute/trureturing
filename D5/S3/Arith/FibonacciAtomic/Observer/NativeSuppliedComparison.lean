/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedComparison
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedComparison
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Fixed original skeletons force distinct installed queries at actual epochs and static entry-window covers. -/

import D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciStaticScan
import D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedComparison

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualCutPartitionRecovery (LiteralRow evaluateRow rowAt)
open NativeActiveParityExecution (chartOf numbered locator source labels bit)
open CombLiteralInstallationBounds (Controller Run IsQuery literal queries halts queryCone)
open scoped BigOperators

/-- All original labels, with no shape quantification or supplied actual lag. -/
def Correct {E : Type} (M : Controller E) (S : Source) (T : Nat) : Prop :=
  ∀ x : Fin S.length → Bool, ∀ t, t ≤ T →
    (∃ qs updates f b, Run M (source (chartOf S) x) M.initial t qs updates f b) ∧
    (∀ qs updates f b, Run M (source (chartOf S) x) M.initial t qs updates f b →
      b = NativeActiveParityExecution.parity (labels x) S.length)

/-- Zero Updates on promised successful runs; unused Update rows are allowed. -/
def Static {E : Type} (M : Controller E) (S : Source) (T : Nat) : Prop :=
  ∀ x : Fin S.length → Bool, ∀ t, t ≤ T →
    ∀ qs updates f b, Run M (source (chartOf S) x) M.initial t qs updates f b → updates = 0

private theorem parity_eq {h : Nat} (x : Fin h → Bool) :
    NativeActiveParityExecution.parity (labels x) h = SparseLiteralParityReadLowerBound.parity x := by
  rw [NativeFibonacciStaticScan.parity_sum]
  unfold SparseLiteralParityReadLowerBound.parity
  congr 2
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [labels, i.isLt, bit, Bool.toNat]

/-- Only leaf cones reached by the literal can affect its raw reply. This
retains each original leaf's own literal address and permits absent replies. -/
private theorem numbered_agreement (S : Source) (offset t : Nat) (a : Address)
    (f g : Nat → Source)
    (same : ∀ i : Fin S.length, (locator S i).IsPrefix a →
      f (offset+i.val) = g (offset+i.val)) :
    readout a (substitution^[t] (evaluateRow f (numbered S offset))) =
      readout a (substitution^[t] (evaluateRow g (numbered S offset))) := by
  induction S generalizing offset a with
  | of b =>
      have eq := same ⟨0,by change 0 < 1; omega⟩ (by simp [locator])
      simpa [numbered, evaluateRow] using congrArg (fun z => readout a (substitution^[t] z)) eq
  | mul l r ihl ihr =>
      have pair (f : Nat → Source) :
          substitution^[t] (evaluateRow f (numbered (.mul l r) offset)) =
            .mul (substitution^[t] (evaluateRow f (numbered l offset)))
              (substitution^[t] (evaluateRow f (numbered r (offset+l.length)))) :=
        Function.Semiconj₂.iterate (fun x y => substitution.map_mul x y) t _ _
      rw [pair, pair]
      cases a with
      | nil => rfl
      | cons d a =>
          cases d with
          | false =>
              apply ihl offset a
              intro i hi
              exact same ⟨i.val,by change i.val < l.length+r.length; omega⟩
                (by simpa [locator, i.isLt] using hi)
          | true =>
              apply ihr (offset+l.length) a
              intro i hi
              have bound : l.length+i.val < (.mul l r : Source).length := by
                change l.length+i.val < l.length+r.length
                omega
              have eq := same ⟨l.length+i.val,bound⟩
                (by simpa [locator, Nat.not_lt.mpr (Nat.le_add_right _ _)] using hi)
              simpa [Nat.add_assoc] using eq

private theorem cone_unique (S : Source) (i j : Fin S.length) (a : Address)
    (hi : ((chartOf S).address i).IsPrefix a)
    (hj : ((chartOf S).address j).IsPrefix a) : i = j := by
  let C := chartOf S
  let u := evaluateRow (fun _ => (.of true : Source)) C.row
  have located (k : Fin S.length) :
      ActualLeafHistoryRigidity.subtree (C.address k) u = some (.of true) :=
    NativeCutFibers.rowAt_evaluate C.row _ (C.address k) _ (C.located k)
  have rigid := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.1
  have addr : C.address i = C.address j := by
    rcases List.prefix_or_prefix_of_prefix hi hj with h | h
    · exact (rigid u _ _ true true (located i) (located j) h).1
    · exact (rigid u _ _ true true (located j) (located i) h).1.symm
  have eq := C.located i
  rw [addr,C.located j] at eq
  apply Fin.ext
  have val := congrArg (fun r : LiteralRow => match r with
    | .of (.inr n) => n | _ => 0) (Option.some.inj eq)
  exact val.symm

private theorem flip_outside (S : Source) (x : Fin S.length → Bool) (i : Fin S.length)
    (t : Nat) (a : Address) (outside : ¬ ((chartOf S).address i).IsPrefix a) :
    readout a (substitution^[t] (source (chartOf S) x)) =
      readout a (substitution^[t] (source (chartOf S) (Function.update x i (!(x i))))) := by
  apply numbered_agreement S 0 t a
  intro j hj
  have ne : j ≠ i := by intro eq; subst j; exact outside hj
  simp [labels, j.isLt, Function.update_of_ne ne]

private theorem separating_read {E : Type} {M : Controller E} {S : Source} {T : Nat}
    (correct : Correct M S T) (x y : Fin S.length → Bool)
    (different : NativeActiveParityExecution.parity (labels x) S.length ≠
      NativeActiveParityExecution.parity (labels y) S.length)
    {t : Nat} (ht : t ≤ T) {qs : List (E × Nat)} {updates : Nat} {f : E} {b : Bool}
    (run : Run M (source (chartOf S) x) M.initial t qs updates f b) :
    ∃ z ∈ qs, readout (literal M z.1) (substitution^[z.2] (source (chartOf S) x)) ≠
      readout (literal M z.1) (substitution^[z.2] (source (chartOf S) y)) := by
  by_contra! same
  exact different (((correct x t ht).2 qs updates f b run).symm.trans
    ((correct y t ht).2 qs updates f b (CombLiteralInstallationBounds.run_replay run same)))

/-- On each actual terminating run, the separating queries for the original
coordinates are different installed words, even when words recur at new epochs. -/
theorem same_run_distinct_queries {E : Type} {M : Controller E} {S : Source} {T : Nat}
    (correct : Correct M S T) (x : Fin S.length → Bool)
    {t : Nat} (ht : t ≤ T) {qs : List (E × Nat)} {updates : Nat} {f : E} {b : Bool}
    (run : Run M (source (chartOf S) x) M.initial t qs updates f b) :
    ∃ pick : Fin S.length → E, Function.Injective pick ∧
      ∀ i, ∃ epoch, (pick i,epoch) ∈ qs ∧
        ((chartOf S).address i).IsPrefix (literal M (pick i)) ∧
        readout (literal M (pick i)) (substitution^[epoch] (source (chartOf S) x)) ≠
          readout (literal M (pick i)) (substitution^[epoch]
            (source (chartOf S) (Function.update x i (!(x i))))) := by
  classical
  have need (i : Fin S.length) : ∃ z ∈ qs,
      ((chartOf S).address i).IsPrefix (literal M z.1) ∧
      readout (literal M z.1) (substitution^[z.2] (source (chartOf S) x)) ≠
        readout (literal M z.1) (substitution^[z.2]
          (source (chartOf S) (Function.update x i (!(x i))))) := by
    have diff : NativeActiveParityExecution.parity (labels x) S.length ≠
        NativeActiveParityExecution.parity (labels (Function.update x i (!(x i)))) S.length := by
      rw [parity_eq, parity_eq]
      exact Ne.symm (SparseLiteralParityReadLowerBound.parity_flip x i)
    obtain ⟨z,hz,sep⟩ := separating_read correct x _ diff ht run
    exact ⟨z,hz,by by_contra h; exact sep (flip_outside S x i z.2 _ h),sep⟩
  choose pick mem cone sep using need
  refine ⟨fun i => (pick i).1, ?_, fun i => ⟨(pick i).2, mem i, cone i, sep i⟩⟩
  intro i j eq
  have hi := cone i
  change (pick i).1 = (pick j).1 at eq
  rw [eq] at hi
  exact cone_unique S i j (literal M (pick j).1) hi (cone j)

private theorem two_halts {E : Type} [Fintype E] {M : Controller E} {S : Source} {T : Nat}
    (correct : Correct M S T) : 2 ≤ (halts M).card := by
  classical
  let x : Fin S.length → Bool := fun _ => false
  let i : Fin S.length := ⟨0,S.length_pos⟩
  let y := Function.update x i true
  obtain ⟨qa,ua,ea,ba,ra⟩ := (correct x 0 (by omega)).1
  obtain ⟨qb,ub,eb,bb,rb⟩ := (correct y 0 (by omega)).1
  have oa := (correct x 0 (by omega)).2 qa ua ea ba ra
  have ob := (correct y 0 (by omega)).2 qb ub eb bb rb
  have neOut : ba ≠ bb := by
    rw [oa, ob, parity_eq, parity_eq]
    exact Ne.symm (SparseLiteralParityReadLowerBound.parity_flip x i)
  have ha := CombLiteralInstallationBounds.run_halt ra
  have hb := CombLiteralInstallationBounds.run_halt rb
  have ne : ea ≠ eb := by intro eq; subst eb; exact neOut (NativeSerialMachine.Op.stop.inj (ha.symm.trans hb))
  have sub : {ea,eb} ⊆ halts M := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · simp [halts,ha]
    · have eq := Finset.mem_singleton.mp he
      subst e
      simp [halts,hb]
  simpa [ne] using Finset.card_le_card sub

/-- Fixed-shape correctness forces h query words and both output words among
all installed states, including unreachable states. -/
theorem installed_lower_bound {E : Type} [Fintype E] {M : Controller E}
    {S : Source} {T : Nat} (correct : Correct M S T) :
    S.length ≤ (queries M).card ∧ 2 ≤ (halts M).card ∧ S.length+2 ≤ Fintype.card E := by
  classical
  obtain ⟨qs,updates,f,b,run⟩ := (correct (fun _ => false) 0 (by omega)).1
  obtain ⟨pick,inj,sep⟩ := same_run_distinct_queries correct _ (by omega) run
  let select (i : Fin S.length) : queries M :=
    ⟨pick i, by
      obtain ⟨epoch,mem,_⟩ := sep i
      simpa [queries] using CombLiteralInstallationBounds.run_queries run (pick i,epoch) mem⟩
  have inj' : Function.Injective select := fun i j eq => inj (congrArg Subtype.val eq)
  have lower := Fintype.card_le_of_injective select inj'
  simp only [Fintype.card_fin,Fintype.card_coe] at lower
  have halt := two_halts correct
  have total := CombLiteralInstallationBounds.query_halt_card M
  exact ⟨lower,halt,by omega⟩

/-- Every original cone covers every allowed static entry comparison. -/
private theorem static_separates {E : Type} [Fintype E] {M : Controller E}
    {S : Source} {T : Nat} (correct : Correct M S T) (static : Static M S T)
    (i : Fin S.length) (t : Nat) (ht : t ≤ T) :
    ∃ e ∈ queryCone M ((chartOf S).address i),
      readout ((literal M e).drop ((chartOf S).address i).length)
        (NativeActiveParityExecution.atom t) ≠
      readout ((literal M e).drop ((chartOf S).address i).length)
        (NativeActiveParityExecution.atom (t+1)) := by
  let x : Fin S.length → Bool := fun _ => false
  obtain ⟨qs,updates,f,b,run⟩ := (correct x t ht).1
  obtain ⟨pick,_,sep⟩ := same_run_distinct_queries correct x ht run
  obtain ⟨epoch,mem,cone,diff⟩ := sep i
  have ep := CombLiteralInstallationBounds.static_epochs run
    (static x t ht qs updates f b run) (pick i,epoch) mem
  change epoch = t at ep
  have split : (chartOf S).address i ++
      (literal M (pick i)).drop ((chartOf S).address i).length = literal M (pick i) := by
    have take := (List.prefix_iff_eq_take.mp cone).symm
    calc
      _ = (literal M (pick i)).take ((chartOf S).address i).length ++
          (literal M (pick i)).drop ((chartOf S).address i).length :=
        congrArg (fun p => p ++ (literal M (pick i)).drop ((chartOf S).address i).length) take.symm
      _ = _ := List.take_append_drop _ _
  have law (y : Fin S.length → Bool) :
      readout (literal M (pick i)) (substitution^[epoch] (source (chartOf S) y)) =
        readout ((literal M (pick i)).drop ((chartOf S).address i).length)
          (NativeActiveParityExecution.atom (epoch+bit (y i))) := by
    have c := NativeActiveParityExecution.cone_read (chartOf S) y 0 epoch i
      ((literal M (pick i)).drop ((chartOf S).address i).length)
    simpa [NativeActiveParityExecution.observations,NativePollingAlignment.observations,split] using c
  refine ⟨pick i,?_,?_⟩
  · simp only [queryCone,Finset.mem_filter]
    exact ⟨by simpa [queries] using CombLiteralInstallationBounds.run_queries run _ mem,cone⟩
  · rw [law,law,ep] at diff
    simpa [x,bit] using diff

private theorem static_cone_bound {E : Type} [Fintype E] {M : Controller E}
    {S : Source} {T : Nat} (correct : Correct M S T) (static : Static M S T)
    (i : Fin S.length) :
    (T+3)/3 ≤ (queryCone M ((chartOf S).address i)).card := by
  classical
  let cone := queryCone M ((chartOf S).address i)
  let w (e : E) := CombLiteralInstallationBounds.weight
    ((literal M e).drop ((chartOf S).address i).length)
  have need (t : Fin (T+1)) : ∃ e : cone, w e.val ≤ t.val+1 ∧ t.val ≤ w e.val+1 := by
    obtain ⟨e,he,sep⟩ := static_separates correct static i t.val (by omega)
    exact ⟨⟨e,he⟩,CombLiteralInstallationBounds.adjacent_window _ _ sep⟩
  choose pick bounds using need
  let code (t : Fin (T+1)) : cone × Fin 3 :=
    (pick t,⟨t.val+1-w (pick t).val,by have h := bounds t; omega⟩)
  have inj : Function.Injective code := by
    intro t s eq
    have same := congrArg Prod.fst eq
    change pick t = pick s at same
    have off := congrArg (fun z : cone × Fin 3 => z.2.val) eq
    change t.val+1-w (pick t).val = s.val+1-w (pick s).val at off
    have bt := bounds t
    have bs := bounds s
    rw [same] at off bt
    apply Fin.ext
    omega
  have count := Fintype.card_le_of_injective code inj
  simp only [Fintype.card_fin,Fintype.card_prod,Fintype.card_coe] at count
  change (T+3)/3 ≤ cone.card
  omega

/-- The static bound counts the installed union over all entries, separately
in each original cone, without a per-run Read bound or a bound on literal depth. -/
theorem static_installed_lower_bound {E : Type} [Fintype E] {M : Controller E}
    {S : Source} {T : Nat} (correct : Correct M S T) (static : Static M S T) :
    S.length*((T+3)/3) ≤ (queries M).card ∧
      S.length*((T+3)/3)+2 ≤ Fintype.card E := by
  classical
  have disjoint : ∀ i ∈ (Finset.univ : Finset (Fin S.length)),
      ∀ j ∈ (Finset.univ : Finset (Fin S.length)), i ≠ j →
        Disjoint (queryCone M ((chartOf S).address i)) (queryCone M ((chartOf S).address j)) := by
    intro i _ j _ ne
    apply Finset.disjoint_left.mpr
    intro e hi hj
    exact ne (cone_unique S i j (literal M e) (Finset.mem_filter.mp hi).2
      (Finset.mem_filter.mp hj).2)
  have sum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => static_cone_bound correct static i)
  have bound : (∑ i : Fin S.length, (queryCone M ((chartOf S).address i)).card) ≤
      (queries M).card := by
    rw [← Finset.card_biUnion disjoint]
    apply Finset.card_le_card
    intro e he
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp hi).1
  have lower : S.length*((T+3)/3) ≤ (queries M).card := by
    simpa using sum.trans bound
  have halt := two_halts correct
  have count := CombLiteralInstallationBounds.query_halt_card M
  exact ⟨lower,by omega⟩

#print axioms same_run_distinct_queries
#print axioms installed_lower_bound
#print axioms static_installed_lower_bound

end D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedComparison
