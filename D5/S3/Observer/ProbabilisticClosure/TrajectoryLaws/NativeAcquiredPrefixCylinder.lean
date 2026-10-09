/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixCylinder
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixCylinder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native stream histories have exact paid-prefix fibers and unread-tail restart. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixCylinder

open FourthSegmentStoppedLaw (Letter Stream Prefix readPrefix)
open NativeAcquiredPrefixState

/-- Erase only Stop: rejected pairs, returns and partial Reads retain their order. -/
def readLetters : List Operation → List Letter
  | [] => []
  | .read x :: h => x :: readLetters h
  | .stop _ :: h => readLetters h

def readCost : Operation → ℕ
  | .read _ => 1
  | .stop _ => 0

/-- The unread raw source after exactly k paid Reads. -/
def rawTail (ω : Stream) (k : ℕ) : Stream := fun i => ω (i + k)

/-- Scheduling depends only on native control and the next raw letter. -/
def nextOperation (c : AcquiredNativeState) (ω : Stream) : Option Operation :=
  match c.source.finiteFields.control with
  | .seed _ | .early _ _ | .fourth (.active _) => some (.read (ω 0))
  | .fourth (.pending b) => some (.stop b)
  | .fourth .delivered => none

/-- Every scheduled event performs the original native transaction. -/
def nextNative (c : AcquiredNativeState) (ω : Stream) :
    Option (Operation × AcquiredNativeState) :=
  (nextOperation c ω).bind fun op => (nativeStep c op).map fun d => (op, d)

/-- The bound counts events. Only Read advances the raw source and paid cursor.
    The emitted history is an output, never an input to scheduling. -/
def nativeDrive (c : AcquiredNativeState) (ω : Stream) :
    ℕ → Option (List Operation × AcquiredNativeState × ℕ)
  | 0 => some ([], c, 0)
  | n + 1 => (nextNative c ω).bind fun step =>
      (nativeDrive step.2 (rawTail ω (readCost step.1)) n).map fun result =>
        (step.1 :: result.1, result.2.1, readCost step.1 + result.2.2)

private theorem next_native_spec (c d : AcquiredNativeState) (ω : Stream) (op : Operation) :
    nextNative c ω = some (op, d) ↔
      nativeStep c op = some d ∧
        (match op with | .read x => ω 0 = x | .stop _ => True) := by
  rcases c with ⟨⟨⟨control, r⟩, s⟩, counts⟩
  cases op <;> cases control with
  | seed first =>
      cases first <;>
        simp [nextNative, nextOperation, nativeStep, nativeRead, finiteRead,
          nativeStop, finiteStop, and_comm] <;> aesop
  | early t phase =>
      simp [nextNative, nextOperation, nativeStep, nativeRead, finiteRead,
        nativeStop, finiteStop, and_comm] <;> aesop
  | fourth control =>
      cases control <;>
        simp [nextNative, nextOperation, nativeStep, nativeRead, finiteRead,
          nativeStop, finiteStop, and_comm] <;> aesop

private theorem prefix_cons (ω : Stream) (x : Letter) (w : List Letter) :
    Prefix ω (x :: w) ↔ ω 0 = x ∧ Prefix (rawTail ω 1) w := by
  simp [Prefix, readPrefix, List.ofFn_succ, rawTail]

private theorem raw_tail_add (ω : Stream) (a b : ℕ) :
    rawTail (rawTail ω a) b = rawTail ω (a + b) := by
  funext i
  simp [rawTail, Nat.add_comm, Nat.add_left_comm]

private theorem drive_append (c : AcquiredNativeState) (ω : Stream) (n m : ℕ) :
    nativeDrive c ω (n + m) = (nativeDrive c ω n).bind fun r =>
      (nativeDrive r.2.1 (rawTail ω r.2.2) m).map fun s =>
        (r.1 ++ s.1, s.2.1, r.2.2 + s.2.2) := by
  induction n generalizing c ω with
  | zero => simp [nativeDrive, show rawTail ω 0 = ω from rfl]
  | succ n ih =>
      simp only [Nat.succ_add, nativeDrive, ih, Option.bind_assoc,
        Option.map_bind, Option.bind_map, Option.map_map, Function.comp_def]
      congr 1
      funext step
      congr 1
      funext r
      rw [raw_tail_add]
      simp [Nat.add_assoc]

private theorem drive_spec (n : ℕ) (c d : AcquiredNativeState)
    (ω : Stream) (h : List Operation) (k : ℕ) :
    nativeDrive c ω n = some (h, d, k) ↔
      h.length = n ∧ execute c h = some d ∧
        Prefix ω (readLetters h) ∧ k = (readLetters h).length := by
  induction n generalizing c d ω h k with
  | zero =>
      cases h <;> simp [nativeDrive, execute, readLetters, Prefix, readPrefix,
        eq_comm, and_left_comm, and_comm]
  | succ n ih =>
      cases h with
      | nil => simp [nativeDrive, Option.bind_eq_some_iff]
      | cons op h =>
          simp only [nativeDrive, Option.bind_eq_some_iff, Option.map_eq_some_iff,
            Prod.mk.injEq]
          constructor
          · rintro ⟨⟨a, e⟩, hs, ⟨⟨v, f, j⟩, ht, hh, hd, hk⟩⟩
            dsimp only at ht hh hd hk
            obtain ⟨ha, hv⟩ := List.cons.inj hh
            subst a
            subst v
            subst f
            obtain ⟨hstep, hletter⟩ := (next_native_spec c e ω op).mp hs
            obtain ⟨hlen, hex, hp, hj⟩ := (ih e d _ h j).mp ht
            refine ⟨by simp [hlen], ?_, ?_, ?_⟩
            · simp [execute, hstep, hex]
            · cases op with
              | read x => exact (prefix_cons ω x _).mpr ⟨hletter, hp⟩
              | stop b => exact hp
            · cases op <;> simp_all [readLetters, readCost, Nat.add_comm]
          · rintro ⟨hlen, hex, hp, hk⟩
            obtain ⟨e, hs, ht⟩ := Option.bind_eq_some_iff.mp hex
            have hl : h.length = n := by simpa using hlen
            have hp' : Prefix (rawTail ω (readCost op)) (readLetters h) := by
              cases op with
              | read x => exact ((prefix_cons ω x _).mp hp).2
              | stop b => exact hp
            have hs' : nextNative c ω = some (op, e) := by
              apply (next_native_spec c e ω op).mpr
              refine ⟨hs, ?_⟩
              cases op with
              | read x => exact ((prefix_cons ω x _).mp hp).1
              | stop b => trivial
            refine ⟨(op, e), hs', (h, d, (readLetters h).length),
              (ih e d _ h _).mpr ⟨hl, ht, hp', rfl⟩, rfl, rfl, ?_⟩
            cases op <;> simp_all [readLetters, readCost, Nat.add_comm]

/-- Every finite emitted history is exactly its legal raw-prefix cylinder;
    the full returned state is the original run state and k counts only Read. -/
theorem native_acquired_prefix_cylinder (h : List Operation) (c : AcquiredNativeState)
    (ω : Stream) (k : ℕ) :
    nativeDrive initial ω h.length = some (h, c, k) ↔
      run h = some c ∧ Prefix ω (readLetters h) ∧ k = (readLetters h).length := by
  simpa only [run, true_and] using drive_spec h.length initial c ω h k

/-- After an emitted prefix, every further finite execution restarts at the exact
    unread tail with the full original state. Its form earns all native fields. -/
theorem native_acquired_prefix_resumption (h : List Operation) (c : AcquiredNativeState)
    (ω : Stream) (k : ℕ)
    (event : nativeDrive initial ω h.length = some (h, c, k)) (n : ℕ) :
    k = (readLetters h).length ∧
    nativeDrive initial ω (h.length + n) =
      (nativeDrive c (rawTail ω k) n).map (fun r =>
        (h ++ r.1, r.2.1, k + r.2.2)) ∧
    ∃ nf : PrefixForm, render nf = h ∧ c = reconstruct nf ∧ PrefixFacts nf c := by
  obtain ⟨hrun, _, hk⟩ := (native_acquired_prefix_cylinder h c ω k).mp event
  refine ⟨hk, ?_, ?_⟩
  · rw [drive_append, event]
    rfl
  · obtain ⟨nf, hf, _⟩ := (native_acquired_prefix_reconstruction h).1.mp ⟨c, hrun⟩
    obtain ⟨hr, facts, _⟩ := (native_acquired_prefix_reconstruction h).2 nf hf
    have hc : c = reconstruct nf := Option.some.inj (hrun.symm.trans hr)
    exact ⟨nf, hf, hc, hc.symm ▸ facts⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixCylinder
