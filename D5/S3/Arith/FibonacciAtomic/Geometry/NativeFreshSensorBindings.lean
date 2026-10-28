/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorBindings
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact raw binding projection of guarded native fresh-sensor execution. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth

/-! Raw table projection and inherited-label framing for original-leaf growth. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorBindings

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address)
open ActualLeafHistoryRigidity (subtree)
open NativeMaterialRootRecognition (terminals)
open NativeGuardedLeafRepair (RawMap Value Call nativeRun promotedMap splitMap)
open NativeFreshSensorGrowth (calls)

/-- Projection of one existing native call onto its actual table and next integer. -/
private def tableStep (s : RawMap × ℤ) : Call → RawMap × ℤ
  | .promote p => (promotedMap s.1 p, s.2)
  | .split p => (splitMap s.1 s.2 p, s.2 + 1)

private def table (t : Source) (p : Address) (s : RawMap × ℤ) : RawMap × ℤ :=
  ((calls t).map (Call.shift p)).foldl tableStep s

private theorem projection {t u : Source} {labels labels' : RawMap}
    {next next' : ℤ} {x y : Value} {w : List Call}
    (h : nativeRun t labels next x w = some (u, labels', next', y)) :
    w.foldl tableStep (labels,next) = (labels',next') := by
  induction w generalizing t labels next x with
  | nil => simpa [nativeRun] using congrArg (Option.map (fun s => (s.2.1,s.2.2.1))) h
  | cons c w ih =>
      cases c with
      | promote p =>
          unfold nativeRun at h
          split at h <;> try contradiction
          exact ih h
      | split p =>
          unfold nativeRun at h
          split at h <;> try contradiction
          exact ih h

private theorem shift_shift (p q : Address) (c : Call) :
    Call.shift p (Call.shift q c) = Call.shift (p ++ q) c := by
  cases c <;> simp [Call.shift, List.append_assoc]

private theorem table_mul (l r : Source) (p : Address) (s : RawMap × ℤ) :
    table (.mul l r) p s = table r (p ++ [true]) (table l (p ++ [false]) s) := by
  simp only [table, calls, List.map_append, List.foldl_append, List.map_map]
  have hf (b : Bool) : Call.shift p ∘ Call.shift [b] = Call.shift (p ++ [b]) :=
    funext (shift_shift p [b])
  rw [hf false, hf true]

private theorem next_mono (w : List Call) (s : RawMap × ℤ) :
    s.2 ≤ (w.foldl tableStep s).2 := by
  induction w generalizing s with
  | nil => exact le_rfl
  | cons c w ih =>
      cases c with
      | promote p => exact ih (tableStep s (.promote p))
      | split p => exact le_trans (by simp [tableStep]) (ih (tableStep s (.split p)))

private theorem frame (w : List Call) (p q : Address) (b : Bool)
    (s : RawMap × ℤ) (i : ℤ) (hi : i < s.2) (hs : s.1 i = p ++ ((!b) :: q)) :
    (((w.map (Call.shift (p ++ [b]))).foldl tableStep s).1 i) = s.1 i := by
  induction w generalizing s with
  | nil => rfl
  | cons c w ih =>
      have step : (tableStep s (Call.shift (p ++ [b]) c)).1 i = s.1 i := by
        cases c with
        | promote r =>
            cases b <;> simp [tableStep, Call.shift, promotedMap, hs, List.append_assoc]
        | split r =>
            have hn : i ≠ s.2 := ne_of_lt hi
            cases b <;> simp [tableStep, Call.shift, splitMap, hn, hs, List.append_assoc]
      have hnext : s.2 ≤ (tableStep s (Call.shift (p ++ [b]) c)).2 := by
        cases c <;> simp [tableStep, Call.shift]
      simpa only [List.map_cons, List.foldl_cons, step] using
        ih (tableStep s (Call.shift (p ++ [b]) c)) (lt_of_lt_of_le hi hnext) (step.trans hs)

/-- Destination of an original terminal after that original leaf's two guarded calls. -/
def inherited : Source → Address → Address
  | .of true, _ => [false,false]
  | .of false, _ => [false,false,false]
  | .mul _ _, [] => []
  | .mul l _, false :: q => false :: inherited l q
  | .mul _ r, true :: q => true :: inherited r q

/-- Fresh labels in allocation order; beta contributes its outer R then its designated LR. -/
def fresh : Source → List Address
  | .of true => [[true]]
  | .of false => [[true], [false,true]]
  | .mul l r => (fresh l).map (false :: ·) ++ (fresh r).map (true :: ·)

private theorem inherited_table (t : Source) (p q : Address) (hq : q ∈ terminals t)
    (s : RawMap × ℤ) (i : ℤ) (hi : i < s.2) (hs : s.1 i = p ++ q) :
    (table t p s).1 i = p ++ inherited t q := by
  induction t generalizing p q s with
  | of b =>
      cases b
      · have he : q = [false] := by simpa [terminals] using hq
        subst q
        have hn : i ≠ s.2 := ne_of_lt hi
        have hn' : i ≠ s.2 + 1 := by omega
        simp [table, calls, tableStep, Call.shift, splitMap, inherited, hn, hn', hs,
          List.append_assoc]
      · have he : q = [] := by simpa [terminals] using hq
        subst q
        have hn : i ≠ s.2 := ne_of_lt hi
        simp [table, calls, tableStep, Call.shift, promotedMap, splitMap, inherited,
          hn, hs, List.append_assoc]
  | mul l r il ir =>
      rw [table_mul]
      simp only [terminals, List.mem_append, List.mem_map] at hq
      rcases hq with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
      · have hl := il (p ++ [false]) q hq s hi (by simpa [List.append_assoc] using hs)
        have hn : i < (table l (p ++ [false]) s).2 :=
          lt_of_lt_of_le hi (next_mono _ s)
        have hf := frame (calls r) p (inherited l q) true
          (table l (p ++ [false]) s) i hn (by simpa [List.append_assoc] using hl)
        exact hf.trans (by simpa [inherited, List.append_assoc] using hl)
      · have hf := frame (calls l) p q false s i hi (by simpa [List.append_assoc] using hs)
        have hn : i < (table l (p ++ [false]) s).2 :=
          lt_of_lt_of_le hi (next_mono _ s)
        have hr := ir (p ++ [true]) q hq (table l (p ++ [false]) s) hn
          (by simpa [table, List.append_assoc, hf] using hs)
        simpa [inherited, List.append_assoc] using hr

/-- All original integer labels below the next fresh integer follow their actual native moves. -/
theorem inherited_bindings {t u : Source} {labels labels' : RawMap} {next next' : ℤ}
    {x y : Value} (h : nativeRun t labels next x (calls t) = some (u,labels',next',y)) :
    ∀ i, i < next → labels i ∈ terminals t → labels' i = inherited t (labels i) := by
  intro i hi hm
  have hp := projection h
  have ht : table t [] (labels,next) = (labels',next') := by
    have hs : Call.shift [] = id := by funext c; cases c <;> rfl
    simpa only [table, hs, List.map_id] using hp
  have hh := inherited_table t [] (labels i) hm (labels,next) i hi (by simp)
  simpa [ht] using hh

end D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorBindings
