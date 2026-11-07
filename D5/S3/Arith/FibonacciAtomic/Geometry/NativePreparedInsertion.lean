/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativePreparedInsertion
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/NativePreparedInsertion
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual guarded preparation and distinct-slot two-event insertion in native combs. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth
import D5.S3.Arith.FibonacciAtomic.FourExitRawEndpointSpectrum

/-! Source-relative preparation and literal slot insertion on the existing native runner. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativePreparedInsertion

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address)
open ActualLeafHistoryRigidity (OutputContext subtree)
open ActualImageAddressCertificate (replace)
open NativeGuardedLeafRepair (Call run)
open FourExitRawEndpointSpectrum (comb)

def C : Source := .mul (.of false) (.of true)

def D (b : Bool) : Source := if b then .mul C (.of false) else .mul (.of false) C

def M : Source := .mul (.mul C (.of true)) (.of true)

def preparation : ℕ → List Call
  | 0 => [.promote [], .split [], .split [false], .split [false, false]]
  | k + 1 => [.promote [], .split [], .split [false]] ++
      (preparation k).map (Call.shift [true])

def localInsertion (b : Bool) : List Call :=
  if b then [.split [false], .promote [true]]
  else [.promote [true], .split [true]]

def slotAddress (j : ℕ) : Address := List.replicate j true ++ [false]

def insertion {k : ℕ} (x : Fin k → Bool) (j : Fin k) : List Call :=
  (localInsertion (x j)).map (Call.shift (slotAddress j.val))

def endpoint (k : ℕ) (x : Fin k → Bool) (active : List (Fin k)) : Source :=
  comb k (fun j => if j ∈ active then D (x j) else C) M

private theorem shift_shift (p q : Address) (c : Call) :
    Call.shift p (Call.shift q c) = Call.shift (p ++ q) c := by
  cases c <;> simp [Call.shift, List.append_assoc]

private theorem comb_run : ∀ (k : ℕ) (f : Fin k → Source) (tail u : Source)
    (j : Fin k) (w : List Call), run (f j) w = some u →
    run (comb k f tail) (w.map (Call.shift (slotAddress j.val))) =
      some (comb k (Function.update f j u) tail) := by
  intro k
  induction k with
  | zero => intro f tail u j; exact Fin.elim0 j
  | succ k ih =>
      intro f tail u j
      refine Fin.cases ?_ (fun i => ?_) j
      · intro w hw
        have h := NativeGuardedLeafRepair.context_run
          (.left .hole (comb k (fun i => f i.succ) tail)) hw
        simpa [comb, slotAddress, OutputContext.plug, OutputContext.holeAddress,
          Function.update, Fin.succ_ne_zero] using h
      · intro w hw
        have h := ih (fun i => f i.succ) tail u i w hw
        have hu : Function.update (fun i => f i.succ) i u =
            (fun a => if a = i then u else f a.succ) :=
          funext (fun a => Function.update_apply _ _ _ a)
        rw [hu] at h
        have h' := NativeGuardedLeafRepair.context_run (.right (f 0) .hole) h
        simpa [comb, slotAddress, OutputContext.plug, OutputContext.holeAddress,
          List.map_map, Function.comp_def, shift_shift, List.replicate_succ,
          Function.update, Fin.succ_inj, Ne.symm (Fin.succ_ne_zero i)] using h'

/-- The source-relative preparation executes every native guard and ends in the prepared comb. -/
theorem prepares (k : ℕ) :
    run (.of true) (preparation k) = some (comb k (fun _ => C) M) ∧
    (preparation k).length = 3 * k + 4 := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      constructor
      · have h := NativeGuardedLeafRepair.context_run (.right C .hole) ih.1
        simpa [preparation, run, subtree, replace, C, comb,
          OutputContext.plug, OutputContext.holeAddress] using h
      · simp only [preparation, List.length_append, List.length_cons,
          List.length_nil, List.length_map]
        omega

private theorem insert_one (k : ℕ) (x : Fin k → Bool) (active : List (Fin k))
    (j : Fin k) (hj : j ∉ active) :
    run (endpoint k x active) (insertion x j) = some (endpoint k x (j :: active)) := by
  have local_run : run C (localInsertion (x j)) = some (D (x j)) := by
    cases x j <;> rfl
  have h := comb_run k (fun i => if i ∈ active then D (x i) else C) M
      (D (x j)) j (localInsertion (x j)) (by simpa [hj] using local_run)
  have update_eq :
      Function.update (fun i => if i ∈ active then D (x i) else C) j (D (x j)) =
      (fun i => if i ∈ j :: active then D (x i) else C) := by
    funext i
    by_cases hi : i = j
    · subst i; simp
    · simp [Function.update, hi]
  simpa [endpoint, insertion, update_eq] using h

private theorem inserts_from (k : ℕ) (x : Fin k → Bool) (todo : List (Fin k))
    (hn : todo.Nodup) (active : List (Fin k))
    (hf : ∀ j ∈ todo, j ∉ active) :
    run (endpoint k x active) (todo.flatMap (insertion x)) =
      some (endpoint k x (todo ++ active)) := by
  induction todo generalizing active with
  | nil => rfl
  | cons j todo ih =>
      have hj := insert_one k x active j (hf j (by simp))
      have ht := ih hn.tail (j :: active) (by
        intro i hi
        simp only [List.mem_cons, not_or]
        exact ⟨fun he => (List.nodup_cons.mp hn).1 (he ▸ hi), hf i (by simp [hi])⟩)
      have joined : run (endpoint k x active)
          (insertion x j ++ todo.flatMap (insertion x)) =
          some (endpoint k x (todo ++ j :: active)) := by
        exact NativeFreshSensorGrowth.run_append hj ht
      have he : endpoint k x (todo ++ j :: active) =
          endpoint k x ((j :: todo) ++ active) := by
        unfold endpoint
        congr 1
        funext i
        simp only [List.mem_append, List.mem_cons]
        congr 1
        exact propext (by tauto)
      simpa only [List.flatMap_cons, he] using joined

/-- Any order of distinct labels gives the literal slotwise endpoint on the actual runner. -/
theorem prepared_insertion (k : ℕ) (x : Fin k → Bool) (order : List (Fin k))
    (hn : order.Nodup) :
    run (.of true) (preparation k ++ order.flatMap (insertion x)) =
      some (endpoint k x order) ∧
    (preparation k ++ order.flatMap (insertion x)).length =
      3 * k + 4 + 2 * order.length := by
  have h := inserts_from k x order hn [] (by simp)
  have h0 : endpoint k x [] = comb k (fun _ => C) M := by simp [endpoint]
  rw [h0, List.append_nil] at h
  constructor
  · have hp := (prepares k).1
    exact NativeFreshSensorGrowth.run_append hp h
  · have hi (j : Fin k) : (insertion x j).length = 2 := by
      simp only [insertion, List.length_map]
      cases x j <;> rfl
    have ht (l : List (Fin k)) : (l.flatMap (insertion x)).length = 2 * l.length := by
      induction l with
      | nil => rfl
      | cons j order ih =>
          simp only [List.flatMap_cons, List.length_append, hi,
            List.length_cons, ih]
          omega
    rw [List.length_append, (prepares k).2, ht order]

end D5.S3.Arith.FibonacciAtomic.Geometry.NativePreparedInsertion
