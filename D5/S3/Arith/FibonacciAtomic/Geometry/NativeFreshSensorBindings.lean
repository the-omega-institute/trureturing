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

private theorem table_next (t : Source) (p : Address) (s : RawMap × ℤ) :
    (table t p s).2 = s.2 + (fresh t).length := by
  induction t generalizing p s with
  | of b => cases b <;> simp [table, calls, tableStep, Call.shift, fresh] <;> omega
  | mul l r il ir =>
      rw [table_mul, ir, il]
      simp [fresh, Nat.cast_add, add_assoc]

private theorem fresh_table (t : Source) (p : Address) (s : RawMap × ℤ)
    (j : ℕ) (hj : j < (fresh t).length) :
    (table t p s).1 (s.2 + j) = p ++ (fresh t)[j] := by
  induction t generalizing p s j with
  | of b =>
      cases b
      · have hcases : j = 0 ∨ j = 1 := by
          have hh : j < 2 := by simpa [fresh] using hj
          omega
        rcases hcases with rfl | rfl <;>
          simp [table, calls, tableStep, Call.shift, splitMap, fresh, List.append_assoc]
      · have he : j = 0 := by
          have hh : j < 1 := by simpa [fresh] using hj
          omega
        subst j
        simp [table, calls, tableStep, Call.shift, promotedMap, splitMap, fresh]
  | mul l r il ir =>
      rw [table_mul]
      have hn := table_next l (p ++ [false]) s
      by_cases hl : j < (fresh l).length
      · have hb := il (p ++ [false]) s j hl
        have hlt : s.2 + (j : ℤ) < (table l (p ++ [false]) s).2 := by
          rw [hn]
          have hh : (j : ℤ) < ((fresh l).length : ℤ) := by exact_mod_cast hl
          omega
        have hf := frame (calls r) p (fresh l)[j] true
          (table l (p ++ [false]) s) (s.2 + j) hlt
          (by simpa [List.append_assoc] using hb)
        apply hf.trans
        simpa [fresh, List.getElem_append_left, hl, List.append_assoc] using hb
      · have hj' : j - (fresh l).length < (fresh r).length := by
          simp only [fresh, List.length_append, List.length_map] at hj
          omega
        have hi : (table l (p ++ [false]) s).2 + ((j - (fresh l).length : ℕ) : ℤ) =
            s.2 + j := by rw [hn]; omega
        have hr := ir (p ++ [true]) (table l (p ++ [false]) s) (j - (fresh l).length) hj'
        rw [hi] at hr
        have hge : ((fresh l).map (false :: ·)).length ≤ j := by simpa using Nat.le_of_not_gt hl
        simpa only [fresh, List.getElem_append_right hge, List.getElem_map,
          List.length_map, List.append_assoc, List.singleton_append] using hr

private theorem table_actual {t u : Source} {labels labels' : RawMap} {next next' : ℤ}
    {x y : Value} (h : nativeRun t labels next x (calls t) = some (u,labels',next',y)) :
    table t [] (labels,next) = (labels',next') := by
  have hs : Call.shift [] = id := by funext c; cases c <;> rfl
  simpa only [table, hs, List.map_id] using projection h

/-- Exact inherited and allocated label destinations of the same successful native execution. -/
theorem raw_bindings {t u : Source} {labels labels' : RawMap} {next next' : ℤ}
    {x y : Value} (h : nativeRun t labels next x (calls t) = some (u,labels',next',y)) :
    next' = next + (fresh t).length ∧
    (∀ i, i < next → labels i ∈ terminals t → labels' i = inherited t (labels i)) ∧
    (∀ j (hj : j < (fresh t).length), labels' (next + j) = (fresh t)[j]) := by
  have ht := table_actual h
  refine ⟨?_, ?_, ?_⟩
  · simpa [ht] using table_next t [] (labels,next)
  · intro i hi hm
    simpa [ht] using inherited_table t [] (labels i) hm (labels,next) i hi (by simp)
  · intro j hj
    simpa [ht] using fresh_table t [] (labels,next) j hj

end D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorBindings
