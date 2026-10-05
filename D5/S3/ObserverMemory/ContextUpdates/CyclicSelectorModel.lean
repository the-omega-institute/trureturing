/- GID: D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorModel
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/ContextUpdates/CyclicSelectorModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Original cyclic selector source, observation and recovery model. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Max
import D5.S3.ObserverMemory.RefinementClosure.FiniteHorizonKernelRecurrence
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.GroupTheory.Index
import D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality

namespace D5.S3.ObserverMemory.ContextUpdates.CyclicSelectorRecovery

open scoped BigOperators
set_option autoImplicit false

/-- The original binary-character group and its kernel-valued clock offset. -/
abbrev Group (m : ℕ) := ZMod 2 × ZMod m

/-- Receiver, labelled senders 2 through r, and the second coordinate of h in H. -/
abbrev Source (m r : ℕ) := (Group m × (Fin (r-1) → Group m)) × ZMod m

def total {m r : ℕ} (s : Source m r) : Group m := s.1.1 + ∑ i, s.1.2 i

def clock {m r : ℕ} (s : Source m r) : Group m := total s + (0,s.2)

def selector (m : ℕ) (b : ZMod 2) : Group m :=
  (1, if b = 0 then 0 else (m/2 : ℕ))

/-- Coefficients use their binary values; the projection retains its H coordinate. -/
def project {m : ℕ} (c x : Group m) : Group m :=
  x - if x.1 = 0 then 0 else c

def observe {m r : ℕ} (f : ZMod m → ZMod 2) (s : Source m r) :
    Group m × Group m × (Fin (r-1) → Group m) :=
  (s.1.1,clock s,fun i => project (selector m (f s.1.1.2)) (s.1.2 i))

/-- j nonnegative repetitions of the sole unit action, with sender 2 translated back. -/
def advance {m r : ℕ} (j : ℕ) (s : Source m r) : Source m r :=
  ((s.1.1 + (0,(j : ZMod m)),fun i =>
    s.1.2 i - if i.val = 0 then (0,(j : ZMod m)) else 0),s.2)

def trace {m r : ℕ} (f : ZMod m → ZMod 2) (n : ℕ) (s : Source m r) :=
  fun j : Fin (n+1) => observe f (advance j.val s)

abbrev Snapshot (m r : ℕ) := Group m × Group m × (Fin (r-1) → Group m)

/-- Two known-time observations of one source are normalized before bit decisions. -/
def recover {m r : ℕ} (f : ZMod m → ZMod 2) (p q : ℕ)
    (A B : Snapshot m r) : Source m r :=
  let a := A.1 - (0,(p : ZMod m))
  let u := fun (j : ℕ) (E : Snapshot m r) (i : Fin (r-1)) =>
    E.2.2 i + if i.val = 0 then (0,(j : ZMod m)) else 0
  let c := selector m (f A.1.2)
  let x := fun i => u p A i + if u q B i - u p A i = 0 then 0 else c
  ((a,x),(A.2.1-(a+∑ i, x i)).2)

/-- A fixed endpoint arithmetic schedule. Each sender normalizes both replies
(two additions and two index comparisons), subtracts them (one subtraction),
compares the difference with zero (one comparison), reconstructs its coordinate
(one addition), and contributes to the sum (one addition). Fixed work is the
receiver correction, adding the receiver to the sum, and subtracting from t;
selector selection costs one comparison. The two time residue conversions and
one public f evaluation are outside the group/comparison ledger. -/
def recoverArithmetic {m r : ℕ} (f : ZMod m → ZMod 2) (p q : ℕ)
    (A B : Snapshot m r) : Source m r × ℕ × ℕ :=
  let a := A.1 - (0,(p : ZMod m))
  let c := selector m (f A.1.2)
  let sender := fun i : Fin (r-1) =>
    let normalized : (Group m × Group m) × ℕ × ℕ :=
      ((A.2.2 i + if i.val = 0 then (0,(p : ZMod m)) else 0,
        B.2.2 i + if i.val = 0 then (0,(q : ZMod m)) else 0),2,2)
    let difference := (normalized.1.2 - normalized.1.1,normalized.2.1+1,normalized.2.2)
    let zeroTest := (difference.1 = 0,difference.2.1,difference.2.2+1)
    (normalized.1.1 + if zeroTest.1 then 0 else c,zeroTest.2.1+1,zeroTest.2.2)
  let x := fun i => (sender i).1
  (((a,x),(A.2.1-(a+∑ i, x i)).2),
    3+∑ i, ((sender i).2.1+1),1+∑ i, (sender i).2.2)

/-- A source with receiver (0,z), zero senders and zero offset. -/
def baseSource (m r : ℕ) (z : ZMod m) : Source m r := (((0,z),fun _ => 0),0)

/-- The same receiver and offset, with exactly senders 2 and 3 flipped. -/
def flipSource (m r : ℕ) (hr : 3 ≤ r) (f : ZMod m → ZMod 2)
    (z : ZMod m) : Source m r :=
  let c := selector m (f z)
  let i0 : Fin (r-1) := ⟨0,by omega⟩
  let i1 : Fin (r-1) := ⟨1,by omega⟩
  (((0,z),Pi.single i0 c + Pi.single i1 c),0)

/-- Direct realization of a proposed snapshot by a parity-compatible bitstring. -/
def fiberSource {m r : ℕ} (f : ZMod m → ZMod 2) (a t : Group m)
    (u : Fin (r-1) → ZMod m) (bits : Fin (r-1) → ZMod 2) : Source m r :=
  let c := selector m (f a.2)
  let x := fun i => ((0,u i) : Group m) + if bits i = 0 then 0 else c
  ((a,x),(t-(a+∑ i, x i)).2)

/-- The zero value is reserved for absence of any positive change. -/
noncomputable def delta {m : ℕ} (f : ZMod m → ZMod 2) (z : ZMod m) : ℕ := by
  classical
  exact if h : ∃ j : ℕ, 0 < j ∧ f (z + (j : ZMod m)) ≠ f z then Nat.find h else 0

noncomputable def beta {m : ℕ} (f : ZMod m → ZMod 2) (z : ZMod m) : ℕ := by
  classical
  exact if h : ∃ j : ℕ, 0 < j ∧ f (z - (j : ZMod m)) ≠ f z then Nat.find h else 0

abbrev RunStart {m : ℕ} (f : ZMod m → ZMod 2) :=
  {s : ZMod m // f (s-1) ≠ f s}

abbrev RunPosition {m : ℕ} (f : ZMod m → ZMod 2) :=
  (s : RunStart f) × Fin (delta f s.val)

/-- H-valued snapshot coordinates, rather than all ambient group-valued replies. -/
abbrev HSnapshot (m r : ℕ) := Group m × Group m × (Fin (r-1) → ZMod m)

def constantWindow {m : ℕ} (f : ZMod m → ZMod 2) (n : ℕ) (z : ZMod m) : Prop :=
  ∀ j : ℕ, j ≤ n → f (z+(j : ZMod m)) = f z

noncomputable def windowCount {m : ℕ} (f : ZMod m → ZMod 2) (n : ℕ) : ℕ :=
  Nat.card {z : ZMod m // constantWindow f n z}

noncomputable def traceClassCount {m r : ℕ} (f : ZMod m → ZMod 2) (n : ℕ) : ℕ :=
  Nat.card (Quotient (Setoid.ker (trace (r := r) f n)))

end D5.S3.ObserverMemory.ContextUpdates.CyclicSelectorRecovery
