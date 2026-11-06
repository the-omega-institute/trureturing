/- GID: D5/S3/Quantum/Dynamics/NativeProtocolGraft
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/NativeProtocolGraft
   mirror-E: none(waiver:content-registration-pending)
   anchors: []
   utility: none
   digest: Original native grafts retain paths, matrix products and expanded call costs. -/

import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.NumberTheory.Niven
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import D5.S3.Arith.Lattices.GoldenIntegerRing
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Analysis.InnerProductSpace.PiL2
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

/-! Native protocol composition on the full sixteen-bit carrier. -/

noncomputable section
open scoped BigOperators Matrix
namespace D5.S3.Quantum.Dynamics.NativeProtocolGraft

/-- Positions 0,...,15 represent the original sites -1,...,14. -/
abbrev Basis := Fin 16 → Bool
abbrev Mat := Matrix Basis Basis ℂ
abbrev Address := Fin 14

def phi : ℝ := (1 + Real.sqrt 5) / 2
def t : ℂ := ((phi⁻¹ : ℝ) : ℂ)
def beta : ℂ := ((Real.sqrt (phi⁻¹) : ℝ) : ℂ)
def zeta : ℂ := Complex.exp ((3 * Real.pi / 5 : ℝ) * Complex.I)

def number (p : Fin 16) : Mat := Matrix.diagonal (fun b => if b p then 1 else 0)
def flip (p : Fin 16) (b : Basis) : Basis := Function.update b p (!(b p))
def bitX (p : Fin 16) : Mat := fun b c => if b = flip p c then 1 else 0

def center (j : Address) : Fin 16 := ⟨j.val + 1, by omega⟩
def left (j : Address) : Fin 16 := ⟨j.val, by omega⟩
def right (j : Address) : Fin 16 := ⟨j.val + 2, by omega⟩
def goldenQ (j : Address) : Mat :=
  t • (1 - number (center j)) + t^2 • number (center j) + beta^3 • bitX (center j)
def goldenP (j : Address) : Mat :=
  number (left j) * number (right j) +
    ((1 - number (left j)) * (1 - number (right j))) * goldenQ j
/-- The actual full-carrier matrix (23.2), at every original address. -/
def gate (j : Address) : Mat := zeta • (1 + (zeta - 1) • goldenP j)

def rootWord : Basis := fun i => decide (i.val = 0 ∨ i.val = 4 ∨ i.val = 8)
def omega0 : Basis → ℂ := fun b => if b = rootWord then 1 else 0

inductive Direction where
  | forward | inverse
  deriving DecidableEq

def callMatrix (j : Address) : Direction → Mat
  | .forward => gate j
  | .inverse => gate j ^ 9

def callCost : Direction → ℕ
  | .forward => 1
  | .inverse => 9

/-- A selector presents a complete diagonal zero-one decomposition. It need not
be surjective: every unused outcome and its complete subtree remain present. -/
def projector {n : ℕ} (select : Basis → Fin n) (o : Fin n) : Mat :=
  Matrix.diagonal (fun b => if select b = o then 1 else 0)

inductive Tree (L : Type) : Type
  | leaf (label : L)
  | call (address : Address) (direction : Direction) (next : Tree L)
  | measure (outcomes : ℕ) (select : Basis → Fin outcomes)
      (next : Fin outcomes → Tree L)

namespace Tree
variable {L M : Type}

def Path : Tree L → Type
  | .leaf _ => Unit
  | .call _ _ U => Path U
  | .measure n _ U => (o : Fin n) × Path (U o)

instance pathFinite : (T : Tree L) → Fintype (Path T)
  | .leaf _ => inferInstanceAs (Fintype Unit)
  | .call _ _ U => pathFinite U
  | .measure _ _ U =>
      letI := fun o => pathFinite (U o)
      inferInstanceAs (Fintype (Sigma (fun o => Path (U o))))

instance pathNonempty : (T : Tree L) → Nonempty (Path T)
  | .leaf _ => ⟨()⟩
  | .call _ _ U => pathNonempty U
  | .measure _ select U =>
      let o := select rootWord
      letI := pathNonempty (U o)
      ⟨⟨o, Classical.choice inferInstance⟩⟩

def label : (T : Tree L) → Path T → L
  | .leaf l, _ => l
  | .call _ _ U, p => label U p
  | .measure _ _ U, p => label (U p.1) p.2

inductive Entry where
  | call (address : Address) (direction : Direction)
  | report (outcomes : ℕ) (outcome : Fin outcomes)

def archive : (T : Tree L) → Path T → List Entry
  | .leaf _, _ => []
  | .call j d U, p => .call j d :: archive U p
  | .measure n _ U, p => .report n p.1 :: archive (U p.1) p.2

/-- Chronological operations multiply from the left. -/
def operator : (T : Tree L) → Path T → Mat
  | .leaf _, _ => 1
  | .call j d U, p => operator U p * callMatrix j d
  | .measure _ select U, p => operator (U p.1) p.2 * projector select p.1

def calls : (T : Tree L) → Path T → ℕ
  | .leaf _, _ => 0
  | .call _ d U, p => callCost d + calls U p
  | .measure _ _ U, p => calls (U p.1) p.2

def maxCalls (T : Tree L) : ℕ := Finset.univ.sup (calls T)

/-- Continuation depends on the entire actual prefix path, not merely its
terminal label. No branch is filtered by its mass. -/
def graft : (T : Tree L) → (Path T → Tree M) → Tree M
  | .leaf _, C => C ()
  | .call j d U, C => .call j d (graft U C)
  | .measure n select U, C =>
      .measure n select (fun o => graft (U o) (fun p => C ⟨o,p⟩))

def attach : (T : Tree L) → (C : Path T → Tree M) →
    (p : Path T) → Path (C p) → Path (graft T C)
  | .leaf _, _, _, q => q
  | .call _ _ U, C, p, q => attach U C p q
  | .measure _ _ U, C, p, q => ⟨p.1, attach (U p.1) (fun r => C ⟨p.1,r⟩) p.2 q⟩

def split : (T : Tree L) → (C : Path T → Tree M) →
    Path (graft T C) → (p : Path T) × Path (C p)
  | .leaf _, _, q => ⟨(),q⟩
  | .call _ _ U, C, q => split U C q
  | .measure _ _ U, C, q =>
      let r := split (U q.1) (fun p => C ⟨q.1,p⟩) q.2
      ⟨⟨q.1,r.1⟩,r.2⟩

private theorem split_attach (T : Tree L) (C : Path T → Tree M)
    (p : Path T) (q : Path (C p)) : split T C (attach T C p q) = ⟨p,q⟩ := by
  induction T with
  | leaf l => cases p; rfl
  | call j d U ih => exact ih C p q
  | measure n select U ih =>
    rcases p with ⟨o,p⟩
    dsimp only [attach, split]
    rw [ih o (fun r => C ⟨o,r⟩) p q]

private theorem attach_split (T : Tree L) (C : Path T → Tree M)
    (r : Path (graft T C)) :
    attach T C (split T C r).1 (split T C r).2 = r := by
  induction T with
  | leaf l => rfl
  | call j d U ih => exact ih C r
  | measure n select U ih =>
    rcases r with ⟨o,r⟩
    simp only [split, attach, ih]
    rfl

def pathEquiv (T : Tree L) (C : Path T → Tree M) :
    Path (graft T C) ≃ ((p : Path T) × Path (C p)) where
  toFun := split T C
  invFun := fun r => attach T C r.1 r.2
  left_inv := attach_split T C
  right_inv := fun r => split_attach T C r.1 r.2

private theorem operator_attach (T : Tree L) (C : Path T → Tree M)
    (p : Path T) (q : Path (C p)) :
    operator (graft T C) (attach T C p q) = operator (C p) q * operator T p := by
  induction T with
  | leaf l => cases p; simp [graft, attach, operator]
  | call j d U ih =>
    simpa only [graft, attach, operator, Matrix.mul_assoc] using
      congrArg (fun A => A * callMatrix j d) (ih C p q)
  | measure n select U ih =>
    rcases p with ⟨o,p⟩
    simpa only [graft, attach, operator, Matrix.mul_assoc] using
      congrArg (fun A => A * projector select o) (ih o (fun r => C ⟨o,r⟩) p q)

private theorem archive_attach (T : Tree L) (C : Path T → Tree M)
    (p : Path T) (q : Path (C p)) :
    archive (graft T C) (attach T C p q) = archive T p ++ archive (C p) q := by
  induction T with
  | leaf l => cases p; rfl
  | call j d U ih => simpa [graft, attach, archive] using congrArg (List.cons (.call j d)) (ih C p q)
  | measure n select U ih =>
    rcases p with ⟨o,p⟩
    simpa [graft, attach, archive] using
      congrArg (List.cons (.report n o)) (ih o (fun r => C ⟨o,r⟩) p q)

private theorem calls_attach (T : Tree L) (C : Path T → Tree M)
    (p : Path T) (q : Path (C p)) :
    calls (graft T C) (attach T C p q) = calls T p + calls (C p) q := by
  induction T with
  | leaf l => cases p; simp [graft, attach, calls]
  | call j d U ih => simpa [graft, attach, calls, Nat.add_assoc] using congrArg (callCost d + ·) (ih C p q)
  | measure n select U ih =>
    rcases p with ⟨o,p⟩
    exact ih o (fun r => C ⟨o,r⟩) p q

/-- Raw terminal Born mass from the same fixed original root. -/
def mass (T : Tree L) (p : Path T) (z : Basis) : ℝ :=
  Complex.normSq ((operator T p).mulVec omega0 z)

/-- Exact ordered-product, archive and syntactic resource semantics of every
native graft path, including zero outcomes and stopped labels. -/
private theorem native_graft_semantics (T : Tree L) (C : Path T → Tree M)
    (p : Path T) (q : Path (C p)) :
    operator (graft T C) (attach T C p q) = operator (C p) q * operator T p ∧
    archive (graft T C) (attach T C p q) = archive T p ++ archive (C p) q ∧
    calls (graft T C) (attach T C p q) = calls T p + calls (C p) q :=
  ⟨operator_attach T C p q, archive_attach T C p q, calls_attach T C p q⟩

private theorem label_attach (T : Tree L) (C : Path T → Tree M)
    (p : Path T) (q : Path (C p)) :
    label (graft T C) (attach T C p q) = label (C p) q := by
  induction T with
  | leaf l => rfl
  | call j d U ih => exact ih C p q
  | measure n select U ih =>
    rcases p with ⟨o,p⟩
    exact ih o (fun r => C ⟨o,r⟩) p q

/-- A raw event on the full terminal record and the full terminal basis word. -/
def eventMass (T : Tree L) (event : Path T → Basis → Bool) : ℝ :=
  ∑ p, ∑ z, if event p z then mass T p z else 0

/-! A history event is lifted to the complete terminal basis record without
discarding any terminal word. -/
def historyEvent {L : Type} {T : Tree L} (event : Path T → Bool) :
    Path T → Basis → Bool := fun p _ => event p

private theorem graft_event (T : Tree L) (C : Path T → Tree M)
    (event : (p : Path T) → Path (C p) → Basis → Bool) :
    eventMass (graft T C) (fun r z =>
      event (split T C r).1 (split T C r).2 z) =
      ∑ p, ∑ q, ∑ z, if event p q z then
        Complex.normSq (((operator (C p) q * operator T p).mulVec omega0) z) else 0 := by
  classical
  unfold eventMass
  rw [← (pathEquiv T C).symm.sum_comp]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro z _
  change (if event (split T C (attach T C p q)).1
    (split T C (attach T C p q)).2 z then
      mass (graft T C) (attach T C p q) z else 0) = _
  rw [split_attach]
  simp only [mass, (native_graft_semantics T C p q).1]

private theorem graft_maxCalls (T : Tree L) (C : Path T → Tree M) :
    maxCalls (graft T C) =
      Finset.univ.sup (fun p => calls T p + maxCalls (C p)) := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro r _
    have hr := attach_split T C r
    have hs := Finset.le_sup (f := fun p => calls T p + maxCalls (C p))
      (Finset.mem_univ (split T C r).1)
    rw [← hr, calls_attach]
    exact le_trans (Nat.add_le_add_left
      (Finset.le_sup (Finset.mem_univ (split T C r).2)) _) hs
  · apply Finset.sup_le
    intro p _
    have hn : (Finset.univ : Finset (Path (C p))).Nonempty := Finset.univ_nonempty
    obtain ⟨q,_,hq⟩ := Finset.exists_mem_eq_sup Finset.univ hn (calls (C p))
    rw [maxCalls, hq]
    rw [← calls_attach T C p q]
    exact Finset.le_sup (Finset.mem_univ _)

end Tree
open _root_.D5.S3.Quantum.Dynamics.NativeProtocolGraft.Tree

inductive StopKind where
  | failure | refusal | early | normal
  deriving DecidableEq

/-- The code retains distinct original terminal labels of the same kind.
Only finitely many codes occur in each finite tree. -/
structure Stop where
  kind : StopKind
  code : ℕ
  deriving DecidableEq

inductive Cut where
  | active | absorbed (stop : Stop)
  deriving DecidableEq

/-- Original site b1 has shifted index 2. -/
def readBit (i : Fin 16) (b : Basis) : Fin 2 := if b i then 1 else 0

def extensionAt : Cut → (Fin 2 → Tree Stop) → Tree Stop
  | .active, C => .measure 2 (readBit 2) C
  | .absorbed s, _ => .leaf s

def readTag : (cut : Cut) → (C : Fin 2 → Tree Stop) →
    Path (extensionAt cut C) → Option (Fin 2)
  | .active, _, q => some q.1
  | .absorbed _, _, _ => none

def extension (T : Tree Cut) (C : Path T → Fin 2 → Tree Stop)
    (p : Path T) : Tree Stop := extensionAt (label T p) (C p)

/-- The projection keeps the original program, full original path, original
read and final stop. Only the added continuation path is forgotten. -/
def projectRecord (T : Tree Cut) (C : Path T → Fin 2 → Tree Stop) (program : ℕ)
    (r : Path (graft T (extension T C))) :
    ℕ × Path T × Option (Fin 2) × Stop :=
  let pq := split T (extension T C) r
  (program,pq.1,readTag (label T pq.1) (C pq.1) pq.2,
    label (extension T C pq.1) pq.2)

/-- Per-original-record law, without conditioning, relabeling, or discarding
zero, failed or stopped continuation positions. -/
def projectedMass (T : Tree Cut) (C : Path T → Fin 2 → Tree Stop)
    (program : ℕ) (event : (ℕ × Path T × Option (Fin 2) × Stop) → Basis → Bool) : ℝ :=
  eventMass (graft T (extension T C)) (fun r z => event (projectRecord T C program r) z)

/-- Complete suffix law at a cut. In the absorbed case it explicitly has no
read label, no new archive and the identity operator. -/
def CutLaw (cut : Cut) (C : Fin 2 → Tree Stop) : Prop :=
  match cut with
  | .active => ∀ (j : Fin 2) (q : Path (C j)),
      readTag .active C ⟨j,q⟩ = some j ∧
      operator (extensionAt .active C) ⟨j,q⟩ = operator (C j) q * projector (readBit 2) j ∧
      calls (extensionAt .active C) ⟨j,q⟩ = calls (C j) q ∧
      archive (extensionAt .active C) ⟨j,q⟩ = .report 2 j :: archive (C j) q ∧
      label (extensionAt .active C) ⟨j,q⟩ = label (C j) q
  | .absorbed s => ∀ q : Path (extensionAt (.absorbed s) C),
      readTag (.absorbed s) C q = none ∧ operator (extensionAt (.absorbed s) C) q = 1 ∧
      archive (extensionAt (.absorbed s) C) q = [] ∧
      calls (extensionAt (.absorbed s) C) q = 0 ∧ label (extensionAt (.absorbed s) C) q = s

/-- Every original native prefix has an exact all-menu, stop-aware graft with
the same root, an exact original-record pushforward and the whole syntax cost.
This is a semantic composition result, not a Petz implementation assertion. -/
theorem original_native_projection (T : Tree Cut) (C : Path T → Fin 2 → Tree Stop)
    (program : ℕ) (event : (ℕ × Path T × Option (Fin 2) × Stop) → Basis → Bool) :
    projectedMass T C program event =
      (∑ p, ∑ q : Path (extension T C p), ∑ z,
        if event (program,p,readTag (label T p) (C p) q,label (extension T C p) q) z then
          Complex.normSq (((operator (extension T C p) q * operator T p).mulVec omega0) z)
        else 0) ∧
    maxCalls (graft T (extension T C)) =
      Finset.univ.sup (fun p => calls T p + maxCalls (extension T C p)) ∧
    (∀ p, CutLaw (label T p) (C p)) ∧
    (∀ (p : Path T) (q : Path (extension T C p)),
      operator (graft T (extension T C)) (attach T (extension T C) p q) =
        operator (extension T C p) q * operator T p ∧
      archive (graft T (extension T C)) (attach T (extension T C) p q) =
        archive T p ++ archive (extension T C p) q ∧
      calls (graft T (extension T C)) (attach T (extension T C) p q) =
        calls T p + calls (extension T C p) q ∧
      label (graft T (extension T C)) (attach T (extension T C) p q) =
        label (extension T C p) q) := by
  refine ⟨?_, Tree.graft_maxCalls T (extension T C), ?_, ?_⟩
  · exact Tree.graft_event T (extension T C) (fun p q z =>
      event (program,p,readTag (label T p) (C p) q,label (extension T C p) q) z)
  · intro p
    cases label T p <;> simp [CutLaw, extensionAt, readTag, operator, calls, archive, label]
  · intro p q
    obtain ⟨ho,ha,hc⟩ := Tree.native_graft_semantics T (extension T C) p q
    exact ⟨ho,ha,hc,Tree.label_attach T (extension T C) p q⟩


#print axioms original_native_projection

end D5.S3.Quantum.Dynamics.NativeProtocolGraft
