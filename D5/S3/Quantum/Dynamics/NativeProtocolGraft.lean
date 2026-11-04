/- GID: D5/S3/Quantum/Dynamics/NativeProtocolGraft
   generality: G
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


/-- The inverse golden ratio is an algebraic integer before any conditioning. -/
private theorem t_integral : IsIntegral ℤ t := by
  have hcos : 2 * Real.cos ((2 / 5 : ℚ) * Real.pi) = phi⁻¹ := by
    rw [show ((2 / 5 : ℚ) : ℝ) * Real.pi = 2 * (Real.pi / 5) by norm_num; ring,
      Real.cos_two_mul, Real.cos_pi_div_five]
    change _ = Real.goldenRatio⁻¹
    rw [Real.inv_goldenRatio]
    dsimp [Real.goldenConj]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have ht : IsIntegral ℤ (phi⁻¹ : ℝ) :=
    hcos ▸ Real.isIntegral_two_mul_cos_rat_mul_pi (2 / 5)
  exact (isIntegral_algebraMap_iff (B := ℂ)).mpr ht

private theorem beta_integral : IsIntegral ℤ beta := by
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  have hb : beta ^ 2 = t := by
    dsimp [beta, t]
    rw [← Complex.ofReal_pow, Real.sq_sqrt]
    exact inv_nonneg.mpr (by dsimp [phi]; positivity)
  rw [hb]
  exact t_integral

private theorem zeta_integral : IsIntegral ℤ zeta := by
  unfold zeta
  convert Complex.isIntegral_exp_rat_mul_pi_mul_I (3 / 5) using 1 <;>
    push_cast <;> congr 1 <;> ring

private theorem number_integral (i : Fin 16) (b c : Basis) :
    IsIntegral ℤ (number i b c) := by
  classical
  simp only [number, Matrix.diagonal_apply]
  split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero

private theorem gate_integral (j : Address) (b c : Basis) :
    IsIntegral ℤ (gate j b c) := by
  classical
  have hid (b c : Basis) : IsIntegral ℤ ((1 : Mat) b c) := by
    simp only [Matrix.one_apply]
    split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
  have hx (b c : Basis) : IsIntegral ℤ (bitX (center j) b c) := by
    simp only [bitX]
    split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
  have hq (b c : Basis) : IsIntegral ℤ (goldenQ j b c) := by
    exact ((t_integral.mul ((hid b c).sub (number_integral _ b c))).add
      ((t_integral.pow 2).mul (number_integral _ b c))).add
      ((beta_integral.pow 3).mul (hx b c))
  have hmul (A B : Mat) (hA : ∀ b c, IsIntegral ℤ (A b c))
      (hB : ∀ b c, IsIntegral ℤ (B b c)) (b c : Basis) : IsIntegral ℤ ((A * B) b c) := by
    rw [Matrix.mul_apply]
    exact IsIntegral.sum _ (fun k _ => (hA b k).mul (hB k c))
  have hp : IsIntegral ℤ (goldenP j b c) := by
    apply IsIntegral.add
    · exact hmul _ _ (number_integral _) (number_integral _) b c
    · exact hmul _ _ (fun b c => hmul _ _
        (fun b c => (hid b c).sub (number_integral _ b c))
        (fun b c => (hid b c).sub (number_integral _ b c)) b c) hq b c
  exact zeta_integral.mul ((hid b c).add ((zeta_integral.sub isIntegral_one).mul hp))

private theorem call_integral (j : Address) (d : Direction) (b c : Basis) :
    IsIntegral ℤ (callMatrix j d b c) := by
  classical
  have hp (n : ℕ) : ∀ b c, IsIntegral ℤ ((gate j ^ n) b c) := by
    induction n with
    | zero =>
      intro b c
      simp only [pow_zero, Matrix.one_apply]
      split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
    | succ n ih =>
      intro b c
      rw [pow_succ, Matrix.mul_apply]
      exact IsIntegral.sum _ (fun k _ => (ih b k).mul (gate_integral j k c))
  cases d
  · exact gate_integral j b c
  · exact hp 9 b c

private theorem projector_integral {n : ℕ} (select : Basis → Fin n) (o : Fin n)
    (b c : Basis) : IsIntegral ℤ (projector select o b c) := by
  classical
  simp only [projector, Matrix.diagonal_apply]
  split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero

private theorem operator_integral {L : Type} (T : Tree L) (p : Path T) (b c : Basis) :
    IsIntegral ℤ (operator T p b c) := by
  classical
  induction T generalizing b c with
  | leaf l =>
    simp only [operator, Matrix.one_apply]
    split_ifs <;> first | exact isIntegral_one | exact isIntegral_zero
  | call j d U ih =>
    simp only [operator, Matrix.mul_apply]
    exact IsIntegral.sum _ (fun k _ => (ih p b k).mul (call_integral j d k c))
  | measure n select U ih =>
    simp only [operator, Matrix.mul_apply]
    exact IsIntegral.sum _ (fun k _ =>
      (ih p.1 p.2 b k).mul (projector_integral select p.1 k c))

/-- Every raw finite event of the original full-menu tree is an algebraic
integer. The statement includes all terminal records, with arbitrary feedback,
inverse calls expanded to nine forward calls and the original fixed root. -/
private theorem original_event_integral {L : Type} (T : Tree L)
    (event : Path T → Basis → Bool) : IsIntegral ℤ (eventMass T event) := by
  classical
  have hv (p : Path T) (z : Basis) :
      IsIntegral ℤ ((operator T p).mulVec omega0 z) := by
    simp only [Matrix.mulVec, dotProduct]
    exact IsIntegral.sum _ (fun b _ => (operator_integral T p z b).mul
      (by simp only [omega0]; split_ifs <;>
        first | exact isIntegral_one | exact isIntegral_zero))
  have hm (p : Path T) (z : Basis) : IsIntegral ℤ (mass T p z) := by
    apply (isIntegral_algebraMap_iff (B := ℂ)).mp
    change IsIntegral ℤ ((Complex.normSq ((operator T p).mulVec omega0 z) : ℝ) : ℂ)
    rw [Complex.normSq_eq_conj_mul_self]
    exact ((hv p z).map (Complex.conjAe : ℂ →ₐ[ℝ] ℂ)).mul (hv p z)
  unfold eventMass
  apply IsIntegral.sum
  intro p _
  apply IsIntegral.sum
  intro z _
  split_ifs
  · exact hm p z
  · exact isIntegral_zero

/-- The two scalar masses occurring in the original reference comparison. -/
def emptyTarget : ℝ := (13 - 5 * Real.sqrt 5) / 22
def referenceTarget : ℝ := (9 * Real.sqrt 5 - 19) / 22

private abbrev GoldenField :=
  D5.S3.Arith.Lattices.GoldenIntegerRing.GoldenNumberField

private def goldenEmbedding : GoldenField →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨Real.goldenRatio, by
    simpa only [Rat.smul_def, Rat.cast_one, one_mul, smul_eq_mul, mul_one,
      ← pow_two, one_pow, add_comm] using Real.goldenRatio_sq⟩

private theorem target_nonintegral :
    ¬ IsIntegral ℤ emptyTarget ∧ ¬ IsIntegral ℤ referenceTarget := by
  have norm_obstruction (a : GoldenField) (n : ℚ)
      (hn : Algebra.norm ℚ a = n) (hni : ¬ IsIntegral ℤ n) :
      ¬ IsIntegral ℤ (goldenEmbedding a) := by
    intro h
    have ha : IsIntegral ℤ a :=
      (isIntegral_algHom_iff (goldenEmbedding.restrictScalars ℤ)
        goldenEmbedding.injective).mp h
    exact hni (hn ▸ Algebra.isIntegral_norm ℚ ha)
  have he : goldenEmbedding (⟨9/11,-5/11⟩ : GoldenField) = emptyTarget := by
    simp [goldenEmbedding, QuadraticAlgebra.lift, emptyTarget, Real.goldenRatio, Rat.smul_def]
    ring
  have hr : goldenEmbedding (⟨-14/11,9/11⟩ : GoldenField) = referenceTarget := by
    simp [goldenEmbedding, QuadraticAlgebra.lift, referenceTarget, Real.goldenRatio, Rat.smul_def]
    ring
  constructor
  · rw [← he]
    apply norm_obstruction _ (1/11)
    · change (DistribSMul.toLinearMap ℚ GoldenField
        (⟨9/11,-5/11⟩ : GoldenField)).det = 1/11
      rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
      norm_num [QuadraticAlgebra.norm]
    · intro h
      obtain ⟨z,hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ)).mp h
      change (z : ℚ) = 1 / 11 at hz
      have hh : (11 : ℚ) * (z : ℚ) = 1 := by rw [hz]; norm_num
      have hh' : 11 * z = 1 := by exact_mod_cast hh
      omega
  · rw [← hr]
    apply norm_obstruction _ (-1/11)
    · change (DistribSMul.toLinearMap ℚ GoldenField
        (⟨-14/11,9/11⟩ : GoldenField)).det = -1/11
      rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
      norm_num [QuadraticAlgebra.norm]
    · intro h
      obtain ⟨z,hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ)).mp h
      change (z : ℚ) = -1 / 11 at hz
      have hh : (11 : ℚ) * (z : ℚ) = -1 := by rw [hz]; norm_num
      have hh' : 11 * z = -1 := by exact_mod_cast hh
      omega

/-- Raw events in any original native tree are algebraic integers and hence
cannot equal either of the two nonintegral reference-comparison masses. -/
theorem original_event_arithmetic {L : Type} (T : Tree L)
    (event : Path T → Basis → Bool) :
    IsIntegral ℤ (eventMass T event) ∧ eventMass T event ≠ emptyTarget ∧
      eventMass T event ≠ referenceTarget := by
  have h := original_event_integral T event
  exact ⟨h, fun he => target_nonintegral.1 (he ▸ h),
    fun he => target_nonintegral.2 (he ▸ h)⟩

#print axioms original_event_arithmetic

#print axioms original_native_projection

namespace Coeff
open scoped QuadraticAlgebra
private theorem mod_two : (2 : ZMod 2) = 0 := by decide

/-- Integer coordinates in the original inverse-golden basis. -/
abbrev O := QuadraticAlgebra ℤ 1 (-1)
def tau : O := QuadraticAlgebra.omega
/-- The two cyclotomic coordinates, each itself an integer pair. -/
abbrev S := QuadraticAlgebra O (-1) (-tau)
def eta : S := QuadraticAlgebra.omega
def inc : O →+* S := algebraMap O S

private theorem t_sq : t ^ 2 = 1 - t := by
  have ht : (phi⁻¹ : ℝ) ^ 2 = 1 - phi⁻¹ := by
    change Real.goldenRatio⁻¹ ^ 2 = 1 - Real.goldenRatio⁻¹
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  unfold t
  exact_mod_cast ht

private theorem beta_sq : beta ^ 2 = t := by
  dsimp [beta, t]
  rw [← Complex.ofReal_pow, Real.sq_sqrt]
  exact inv_nonneg.mpr (by dsimp [phi]; positivity)

private theorem zeta_sum : zeta + star zeta = -t := by
  have hcos : 2 * Real.cos (3 * Real.pi / 5) = -phi⁻¹ := by
    rw [show 3 * Real.pi / 5 = Real.pi - 2 * (Real.pi / 5) by ring,
      Real.cos_pi_sub, Real.cos_two_mul, Real.cos_pi_div_five]
    change _ = -Real.goldenRatio⁻¹
    rw [Real.inv_goldenRatio]
    dsimp [Real.goldenConj]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)]
  have hz : zeta.re = Real.cos (3 * Real.pi / 5) := by
    simp [zeta, Complex.exp_re]
  apply Complex.ext
  · simpa [t, hz, two_mul] using hcos
  · simp [t]

private theorem zeta_norm : zeta * star zeta = 1 := by
  change zeta * (starRingEnd ℂ) zeta = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp [zeta, Complex.norm_exp]

private theorem zeta_sq : zeta ^ 2 = -1 - t * zeta := by
  have h := congrArg (fun x : ℂ => zeta * x) zeta_sum
  rw [mul_add, zeta_norm] at h
  linear_combination h

/-- Evaluation laws follow from the two defining quadratic equations. -/
def evalO {R : Type*} [CommRing R] (u : R) (hu : u ^ 2 = 1 - u) : O →+* R where
  toFun x := (x.re : R) + (x.im : R) * u
  map_zero' := by simp
  map_one' := by
    simp only [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, Int.cast_one,
      Int.cast_zero, zero_mul, add_zero]
  map_add' x y := by
    change (((x+y).re : R) + ((x+y).im : R) * u) = _
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, Int.cast_add]
    ring
  map_mul' x y := by
    change (((x*y).re : R) + ((x*y).im : R) * u) = _
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    push_cast
    linear_combination -(x.im : R) * (y.im : R) * hu

@[simp] private theorem evalO_tau {R : Type*} [CommRing R] (u : R) (hu : u ^ 2 = 1 - u) :
    evalO u hu tau = u := by simp [evalO, tau, QuadraticAlgebra.omega]

def evalS (u v : ℂ) (hu : u ^ 2 = 1 - u) (hv : v ^ 2 = -1 - u*v) : S →+* ℂ where
  toFun x := evalO u hu x.re + evalO u hu x.im * v
  map_zero' := by simp
  map_one' := by change evalO u hu 1 + evalO u hu 0 * v = 1; simp
  map_add' x y := by
    change evalO u hu (x+y).re + evalO u hu (x+y).im * v = _
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]
    ring
  map_mul' x y := by
    change evalO u hu (x*y).re + evalO u hu (x*y).im * v = _
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      map_add, map_mul, map_neg, map_one, evalO_tau]
    linear_combination -(evalO u hu x.im) * (evalO u hu y.im) * hv

def physical : S →+* ℂ := evalS t zeta t_sq zeta_sq

@[simp] private theorem evalS_inc (u v : ℂ) (hu hv) (x : O) :
    evalS u v hu hv (inc x) = evalO u hu x := by
  simp [evalS, inc]
@[simp] private theorem evalS_eta (u v : ℂ) (hu hv) :
    evalS u v hu hv eta = v := by simp [evalS, eta, QuadraticAlgebra.omega]

/-- Relative bit parity on the entire sixteen-bit carrier. -/
def parity (b : Basis) : ZMod 2 :=
  (∑ i : Fin 16, if b i then 1 else 0) -
    ∑ i : Fin 16, if rootWord i then 1 else 0

def exponent (b : Basis) : ℕ := if parity b = 0 then 0 else 1

private theorem parity_root : parity rootWord = 0 := by simp [parity]
private theorem flip_flip (i : Fin 16) (b : Basis) : flip i (flip i b) = b := by
  funext k
  by_cases hk : k = i
  · subst k; simp [flip]
  · simp [flip, Function.update_of_ne hk, hk]

private theorem parity_flip (i : Fin 16) (b : Basis) :
    parity (flip i b) = parity b + 1 := by
  classical
  have hsplit (f : Fin 16 → ZMod 2) :
      ∑ k, f k = (∑ k ∈ Finset.univ.erase i, f k) + f i :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  unfold parity
  rw [hsplit (fun k => if flip i b k then 1 else 0),
    hsplit (fun k => if b k then 1 else 0)]
  have he : (∑ k ∈ Finset.univ.erase i, if flip i b k then (1:ZMod 2) else 0) =
      ∑ k ∈ Finset.univ.erase i, if b k then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [flip, Function.update_of_ne (Finset.mem_erase.mp hk).1]
  rw [he]
  cases hb : b i <;> simp [flip, hb] <;> ring_nf <;> simp only [mod_two, zero_add]

private theorem exponent_flip (i : Fin 16) (b : Basis) :
    exponent (flip i b) = 1 - exponent b := by
  have hcases : parity b = 0 ∨ parity b = 1 := by
    have hv := (parity b).val_lt
    have hr := ZMod.natCast_zmod_val (parity b)
    interval_cases (parity b).val <;> simp_all
  rcases hcases with h | h <;> norm_num [exponent, parity_flip, h] <;> exact mod_two


private theorem number_action (i : Fin 16) (w : Basis → ℂ) (z : Basis) :
    (number i).mulVec w z = if z i then w z else 0 := by
  classical
  simp [number, Matrix.mulVec_diagonal]

private theorem complement_action (i : Fin 16) (w : Basis → ℂ) (z : Basis) :
    (1 - number i : Mat).mulVec w z = if z i then 0 else w z := by
  rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec, number_action]
  cases z i <;> simp

private theorem flip_action (i : Fin 16) (w : Basis → ℂ) (z : Basis) :
    (bitX i).mulVec w z = w (flip i z) := by
  classical
  have he (b : Basis) : z = flip i b ↔ b = flip i z := by
    constructor
    · intro h; rw [h, flip_flip]
    · intro h; rw [h, flip_flip]
  simp [Matrix.mulVec, dotProduct, bitX, he]

private theorem q_action (j : Address) (w : Basis → ℂ) (z : Basis) :
    (goldenQ j).mulVec w z =
      (if z (center j) then t^2 else t) * w z + beta^3 * w (flip (center j) z) := by
  simp only [goldenQ, Matrix.add_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, number_action, complement_action]
  rw [flip_action]
  cases z (center j) <;> simp

def diagonal (j : Address) (z : Basis) : O :=
  if z (left j) then (if z (right j) then 1 else 0)
  else if z (right j) then 0 else if z (center j) then tau^2 else tau

def active (j : Address) (z : Basis) : Bool := !(z (left j)) && !(z (right j))

def diagStep (j : Address) (z : Basis) : S :=
  eta * (1 + (eta - 1) * inc (diagonal j z))
def offStep (j : Address) (z : Basis) : S :=
  if active j z then inc tau * eta * (eta - 1) else 0

/-- A forward call transports four integer coefficients per basis word. -/
def step (j : Address) (h : Basis → S) (z : Basis) : S :=
  diagStep j z * h z +
    offStep j z * inc (tau ^ (1 - exponent z)) * h (flip (center j) z)

def amplitude (h : Basis → S) (z : Basis) : ℂ :=
  beta ^ exponent z * physical (h z)

private theorem p_action (j : Address) (w : Basis → ℂ) (z : Basis) :
    (goldenP j).mulVec w z = evalO t t_sq (diagonal j z) * w z +
      (if active j z then beta^3 * w (flip (center j) z) else 0) := by
  simp only [goldenP, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Pi.add_apply]
  rw [number_action, complement_action]
  cases hl : z (left j) <;> cases hr : z (right j) <;>
    simp [diagonal, active, hl, hr, number_action, complement_action, q_action]
  cases z (center j) <;> simp

private theorem step_physical (j : Address) (h : Basis → S) :
    amplitude (step j h) = (gate j).mulVec (amplitude h) := by
  funext z
  have he : exponent z = 0 ∨ exponent z = 1 := by
    unfold exponent; split_ifs <;> simp
  have hpow := exponent_flip (center j) z
  simp only [gate, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul, p_action]
  unfold amplitude step diagStep offStep physical
  simp only [map_add, map_mul, map_sub, map_one, evalS_eta, evalS_inc, map_pow,
    evalO_tau, map_zero]
  rw [hpow]
  rcases he with he | he <;> rw [he] <;>
    cases ha : active j z <;> simp [ha, beta_sq] <;> ring_nf <;>
    try simp only [show beta^4 = t^2 by rw [show beta^4 = (beta^2)^2 by ring, beta_sq],
      show beta^3 = beta*t by rw [pow_succ, beta_sq]; ring]
  all_goals ring

/-- Complete finite branch transport, with nine steps at inverse syntax. -/
def branch {L : Type} : (T : Tree L) → Path T → (Basis → S) → Basis → S
  | .leaf _, _, h => h
  | .call j d U, p, h => branch U p ((step j)^[callCost d] h)
  | .measure _ select U, p, h =>
      branch (U p.1) p.2 (fun z => if select z = p.1 then h z else 0)

def initial : Basis → S := fun z => if z = rootWord then 1 else 0

private theorem initial_physical : amplitude initial = omega0 := by
  funext z
  by_cases hz : z = rootWord
  · subst z
    simp [amplitude, initial, omega0, exponent, parity_root]
  · simp [amplitude, initial, omega0, hz]

private theorem iterate_physical (j : Address) (n : ℕ) (h : Basis → S) :
    amplitude ((step j)^[n] h) = (gate j ^ n).mulVec (amplitude h) := by
  induction n generalizing h with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, step_physical,
      Matrix.mulVec_mulVec, ← pow_succ]

private theorem branch_physical {L : Type} (T : Tree L) (p : Path T) (h : Basis → S) :
    amplitude (branch T p h) = (operator T p).mulVec (amplitude h) := by
  induction T generalizing h with
  | leaf l => simp [branch, operator]
  | call j d U ih =>
    change amplitude (branch U p ((step j)^[callCost d] h)) =
      (operator U p * callMatrix j d).mulVec (amplitude h)
    rw [ih p, iterate_physical, Matrix.mulVec_mulVec]
    cases d <;> simp [operator, callMatrix, callCost]
  | measure n select U ih =>
    change amplitude (branch (U p.1) p.2 _) =
      (operator (U p.1) p.2 * projector select p.1).mulVec (amplitude h)
    rw [ih p.1 p.2]
    simp only [← Matrix.mulVec_mulVec]
    congr 1
    funext z
    simp [amplitude, projector, Matrix.mulVec_diagonal]
    split_ifs <;> simp


private theorem real_t_sq : (phi⁻¹ : ℝ)^2 = 1 - phi⁻¹ := by
  change Real.goldenRatio⁻¹ ^ 2 = 1 - Real.goldenRatio⁻¹
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

private theorem neg_phi_sq : (-phi)^2 = 1 - (-phi) := by
  change (-Real.goldenRatio)^2 = 1 - (-Real.goldenRatio)
  nlinarith [Real.goldenRatio_sq]

private theorem complex_neg_phi_sq : (-(phi : ℂ))^2 = 1 - (-(phi : ℂ)) := by
  exact_mod_cast neg_phi_sq

def realPhysical : O →+* ℝ := evalO phi⁻¹ real_t_sq
def realConjugate : O →+* ℝ := evalO (-phi) neg_phi_sq

def conjugateZeta : ℂ := Complex.exp ((Real.pi / 5 : ℝ) * Complex.I)
def conjugateBeta : ℂ := (Real.sqrt phi : ℂ) * Complex.I

private theorem conjugateZeta_re : 2 * conjugateZeta.re = phi := by
  simp [conjugateZeta, Complex.exp_re, Real.cos_pi_div_five, phi]
  ring

private theorem conjugateZeta_norm : Complex.normSq conjugateZeta = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  simp [conjugateZeta, Complex.norm_exp]

private theorem conjugateZeta_sq : conjugateZeta^2 = -1 - (-(phi : ℂ))*conjugateZeta := by
  have hs : conjugateZeta + star conjugateZeta = (phi : ℂ) := by
    apply Complex.ext
    · simpa [two_mul] using conjugateZeta_re
    · simp
  have hn : conjugateZeta * star conjugateZeta = 1 := by
    change conjugateZeta * (starRingEnd ℂ) conjugateZeta = 1
    rw [Complex.mul_conj, conjugateZeta_norm]; rfl
  have h := congrArg (fun x : ℂ => conjugateZeta*x) hs
  rw [mul_add, hn] at h
  linear_combination h

private theorem conjugateBeta_sq : conjugateBeta^2 = -(phi : ℂ) := by
  have hp : 0 ≤ phi := by dsimp [phi]; positivity
  simp [conjugateBeta, mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt hp]

private theorem conjugateBeta_norm : Complex.normSq conjugateBeta = phi := by
  have hp : 0 ≤ phi := by dsimp [phi]; positivity
  simp only [conjugateBeta, map_mul, Complex.normSq_I, Complex.normSq_ofReal]
  rw [← pow_two, Real.sq_sqrt hp, mul_one]

def nonphysical : S →+* ℂ :=
  evalS (-(phi : ℂ)) conjugateZeta complex_neg_phi_sq conjugateZeta_sq

def conjugateAmplitude (h : Basis → S) (z : Basis) : ℂ :=
  conjugateBeta ^ exponent z * nonphysical (h z)

private theorem evalO_real (u : ℝ) (hu : u^2 = 1-u) (x : O) :
    evalO (u : ℂ) (by exact_mod_cast hu) x = (evalO u hu x : ℂ) := by
  simp [evalO]

private theorem norm_evaluation (u : ℝ) (v : ℂ) (hu : u^2 = 1-u)
    (hv : v^2 = -1 - (u : ℂ)*v) (hr : 2*v.re = -u)
    (hn : Complex.normSq v = 1) (x : S) :
    evalO u hu (QuadraticAlgebra.norm x) =
      Complex.normSq (evalS (u : ℂ) v (by exact_mod_cast hu) hv x) := by
  simp only [QuadraticAlgebra.norm_def, map_sub, map_add, map_mul, map_neg,
    map_one, evalO_tau]
  change _ = Complex.normSq ((evalO (u : ℂ) _ x.re) +
    (evalO (u : ℂ) _ x.im)*v)
  rw [evalO_real u hu x.re, evalO_real u hu x.im]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    zero_add, add_zero]
  rw [Complex.normSq_apply] at hn
  linear_combination -(evalO u hu x.im)^2 * hn -
    evalO u hu x.re * evalO u hu x.im * hr

/-- Integer coordinates of the raw event, computed from the same branch products. -/
def coordinates {L : Type} (T : Tree L) (event : Path T → Basis → Bool) : O :=
  ∑ p, ∑ z, if event p z then
    tau ^ exponent z * QuadraticAlgebra.norm (branch T p initial z) else 0

private theorem physical_coordinate (h : Basis → S) (z : Basis) :
    realPhysical (tau^exponent z * QuadraticAlgebra.norm (h z)) =
      Complex.normSq (amplitude h z) := by
  have hr : 2*zeta.re = -phi⁻¹ := by
    have hh := congrArg Complex.re zeta_sum
    simpa [t, two_mul] using hh
  have hn : Complex.normSq zeta = 1 := by
    have hh := zeta_norm
    change zeta * (starRingEnd ℂ) zeta = 1 at hh
    rw [Complex.mul_conj] at hh
    exact_mod_cast hh
  have hb : Complex.normSq beta = phi⁻¹ := by
    simp only [beta, Complex.normSq_ofReal]
    rw [← pow_two, Real.sq_sqrt]
    exact inv_nonneg.mpr (by dsimp [phi]; positivity)
  simp only [realPhysical, map_mul, map_pow, evalO_tau, amplitude,
    map_mul, map_pow, hb, physical]
  rw [norm_evaluation phi⁻¹ zeta real_t_sq (by simpa [t] using zeta_sq) hr hn]
  rfl

private theorem conjugate_coordinate (h : Basis → S) (z : Basis) :
    realConjugate (tau^exponent z * QuadraticAlgebra.norm (h z)) =
      (-1 : ℝ)^exponent z * Complex.normSq (conjugateAmplitude h z) := by
  simp only [realConjugate, map_mul, map_pow, evalO_tau, conjugateAmplitude,
    map_mul, map_pow, conjugateBeta_norm, nonphysical]
  rw [norm_evaluation (-phi) conjugateZeta neg_phi_sq
    (by simpa using conjugateZeta_sq) (by simpa using conjugateZeta_re) conjugateZeta_norm]
  by_cases he : exponent z = 0
  · simp [he]
  · have he' : exponent z = 1 := by simpa [exponent] using he
    simp [he', mul_assoc]

private theorem coordinates_physical {L : Type} (T : Tree L)
    (event : Path T → Basis → Bool) :
    realPhysical (coordinates T event) = eventMass T event := by
  classical
  simp only [coordinates, map_sum, eventMass]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro z _
  split_ifs with h
  · rw [physical_coordinate, branch_physical, initial_physical]
    rfl
  · exact map_zero _

private theorem coordinates_conjugate {L : Type} (T : Tree L)
    (event : Path T → Basis → Bool) :
    realConjugate (coordinates T event) = ∑ p, ∑ z, if event p z then
      (-1 : ℝ)^exponent z * Complex.normSq (conjugateAmplitude (branch T p initial) z)
      else 0 := by
  classical
  simp only [coordinates, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro z _
  split_ifs
  · exact conjugate_coordinate _ _
  · exact map_zero _


/-- The actual embedded projection row, derived from the same coefficient transport. -/
def conjugateP (j : Address) (w : Basis → ℂ) (z : Basis) : ℂ :=
  (realConjugate (diagonal j z) : ℂ) * w z +
    if active j z then conjugateBeta^3 * w (flip (center j) z) else 0

private theorem conjugate_step (j : Address) (h : Basis → S) (z : Basis) :
    conjugateAmplitude (step j h) z = conjugateZeta *
      (conjugateAmplitude h z + (conjugateZeta - 1) *
        conjugateP j (conjugateAmplitude h) z) := by
  have he : exponent z = 0 ∨ exponent z = 1 := by
    unfold exponent; split_ifs <;> simp
  have hpow := exponent_flip (center j) z
  unfold conjugateAmplitude step diagStep offStep nonphysical conjugateP
  simp only [map_add, map_mul, map_sub, map_one, evalS_eta, evalS_inc, map_pow,
    evalO_tau]
  rw [hpow]
  have hd : evalO (-(phi : ℂ)) complex_neg_phi_sq (diagonal j z) =
      (realConjugate (diagonal j z) : ℂ) := by
    simpa [realConjugate] using evalO_real (-phi) neg_phi_sq (diagonal j z)
  rw [hd]
  rcases he with he | he <;> rw [he] <;>
    cases ha : active j z <;> simp [ha] <;> ring_nf <;>
    try simp only [show conjugateBeta^4 = (-(phi : ℂ))^2 by
      rw [show conjugateBeta^4 = (conjugateBeta^2)^2 by ring, conjugateBeta_sq],
      show conjugateBeta^3 = conjugateBeta * (-(phi : ℂ)) by
        rw [pow_succ, conjugateBeta_sq]; ring]
  all_goals ring

def energy (w : Basis → ℂ) : ℝ := ∑ z, Complex.normSq (w z)
def l2 (w : Basis → ℂ) : EuclideanSpace ℂ Basis := WithLp.toLp 2 w

private theorem energy_nonneg (w : Basis → ℂ) : 0 ≤ energy w :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

private theorem energy_norm (w : Basis → ℂ) : energy w = ‖l2 w‖^2 := by
  simp [energy, l2, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]

private theorem cauchy_two (a b x y : ℂ) :
    Complex.normSq (a*x+b*y) ≤
      (Complex.normSq a+Complex.normSq b)*(Complex.normSq x+Complex.normSq y) := by
  have h := norm_add_le (a*x) (b*y)
  rw [norm_mul, norm_mul] at h
  have hs := sq_nonneg (‖a‖*‖y‖ - ‖b‖*‖x‖)
  simp only [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (a*x+b*y), norm_nonneg a, norm_nonneg b,
    norm_nonneg x, norm_nonneg y]

private theorem flip_sum (i : Fin 16) (f : Basis → ℝ) :
    ∑ z, f (flip i z) = ∑ z, f z := by
  let e : Basis ≃ Basis := ⟨flip i, flip i, flip_flip i, flip_flip i⟩
  exact e.sum_comp f

private theorem phi_positive : 0 < phi := by dsimp [phi]; positivity
private theorem phi_cubic : phi^3 = phi + phi^2 := by
  have h : phi^2 = phi+1 := Real.goldenRatio_sq
  nlinarith

private theorem active_flip (j : Address) (z : Basis) :
    active j (flip (center j) z) = active j z := by
  have hl : left j ≠ center j := by
    intro h; have hh := congrArg Fin.val h; simp [left, center] at hh
  have hr : right j ≠ center j := by
    intro h; have hh := congrArg Fin.val h; simp [right, center] at hh
  simp [active, flip, Function.update_of_ne hl, Function.update_of_ne hr, hl, hr]

/-- Squared row weight on a nonphysical active two-dimensional block. -/
def rowWeight (j : Address) (z : Basis) : ℝ :=
  if z (center j) then phi^2 else phi

private theorem rowWeight_pair (j : Address) (z : Basis) :
    rowWeight j z + rowWeight j (flip (center j) z) = phi^3 := by
  cases hc : z (center j) <;> simp [rowWeight, flip, hc, phi_cubic] <;> ring

private theorem active_row_bound (j : Address) (w : Basis → ℂ) (z : Basis)
    (ha : active j z = true) :
    Complex.normSq (conjugateP j w z) ≤
      phi^3 * rowWeight j z *
        (Complex.normSq (w z) + Complex.normSq (w (flip (center j) z))) := by
  have hd : realConjugate (diagonal j z) =
      if z (center j) then phi^2 else -phi := by
    unfold active at ha
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha
    cases hz : z (center j) <;> simp [diagonal, ha.1, ha.2, realConjugate, hz]
  have hc := cauchy_two (realConjugate (diagonal j z) : ℂ)
    (conjugateBeta^3) (w z) (w (flip (center j) z))
  simp only [conjugateP, ha, if_true]
  refine le_trans hc ?_
  apply mul_le_mul_of_nonneg_right _ (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
  rw [hd]
  simp only [map_pow, conjugateBeta_norm, Complex.normSq_ofReal]
  have hp : phi^2 = phi+1 := Real.goldenRatio_sq
  apply le_of_eq
  cases hz : z (center j) <;> simp only [rowWeight, hz, Bool.false_eq_true,
    ite_false, ite_true, neg_mul_neg, neg_pow, even_two, Even.neg_pow]
  · linear_combination -phi^2 * hp
  · linear_combination -phi^3 * hp

private theorem projection_energy (j : Address) (w : Basis → ℂ) :
    energy (conjugateP j w) ≤ (phi^3)^2 * energy w := by
  classical
  let a : Basis → ℝ := fun z => if active j z then Complex.normSq (w z) else 0
  let b : Basis → ℝ := fun z =>
    if z (left j) && z (right j) then Complex.normSq (w z) else 0
  have hpoint (z : Basis) : Complex.normSq (conjugateP j w z) ≤
      phi^3 * rowWeight j z * (a z + a (flip (center j) z)) + b z := by
    by_cases ha : active j z = true
    · have hh : z (left j) = false ∧ z (right j) = false := by
        simpa [active] using ha
      have hb : b z = 0 := by simp [b, hh.1, hh.2]
      simpa only [a, ha, active_flip, ite_true, hb, add_zero] using
        active_row_bound j w z ha
    · have hzero : active j z = false := Bool.eq_false_iff.mpr ha
      simp only [a, active_flip, hzero, ite_false, add_zero, zero_add, mul_zero]
      cases hl : z (left j) <;> cases hr : z (right j) <;>
        simp [active, hl, hr] at ha
      all_goals simp [b, conjugateP, hzero, diagonal, realConjugate, hl, hr]
  have hreindex :
      (∑ z, rowWeight j z * a (flip (center j) z)) =
        ∑ z, rowWeight j (flip (center j) z) * a z := by
    simpa only [flip_flip] using
      flip_sum (center j) (fun z => rowWeight j (flip (center j) z) * a z)
  have hsum : (∑ z, rowWeight j z * (a z + a (flip (center j) z))) =
      phi^3 * ∑ z, a z := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, hreindex, ← Finset.sum_add_distrib]
    simp_rw [← add_mul, rowWeight_pair]
    rw [Finset.mul_sum]
  have htotal := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset Basis)) => hpoint z)
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at htotal
  rw [hsum] at htotal
  refine le_trans htotal ?_
  rw [← mul_assoc, ← pow_two]
  have hphi : 1 ≤ (phi^3)^2 := by
    have hp : 1 ≤ phi := by
      change 1 ≤ Real.goldenRatio
      exact Real.one_lt_goldenRatio.le
    exact one_le_pow₀ (one_le_pow₀ hp)
  have hbn : 0 ≤ ∑ z, b z := by
    apply Finset.sum_nonneg
    intro z _; dsimp [b]; split_ifs
    · exact Complex.normSq_nonneg _
    · norm_num
  have hmass : (∑ z, a z) + (∑ z, b z) ≤ energy w := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z _
    cases hl : z (left j) <;> cases hr : z (right j) <;>
      simp [a, b, active, hl, hr, Complex.normSq_nonneg]
  nlinarith [mul_le_mul_of_nonneg_left hmass (sq_nonneg (phi^3)),
    mul_le_mul_of_nonneg_right hphi hbn]


def kappa : ℝ := 1 + 2*phi^3

private theorem kappa_one : 1 ≤ kappa := by
  have hp := pow_nonneg phi_positive.le 3
  dsimp [kappa]
  linarith

private theorem step_energy (j : Address) (h : Basis → S) :
    energy (conjugateAmplitude (step j h)) ≤
      kappa^2 * energy (conjugateAmplitude h) := by
  let w := conjugateAmplitude h
  have hp : ‖l2 (conjugateP j w)‖ ≤ phi^3 * ‖l2 w‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (pow_nonneg phi_positive.le _) (norm_nonneg _))).mp
    have hb := projection_energy j w
    rw [energy_norm, energy_norm] at hb
    nlinarith [hb]
  have hv : l2 (conjugateAmplitude (step j h)) =
      conjugateZeta • (l2 w + (conjugateZeta-1) • l2 (conjugateP j w)) := by
    ext z
    exact conjugate_step j h z
  have hz : ‖conjugateZeta‖ = 1 := by
    have hn := conjugateZeta_norm
    rw [Complex.normSq_eq_norm_sq] at hn
    nlinarith [norm_nonneg conjugateZeta]
  have hd : ‖conjugateZeta-1‖ ≤ 2 := by
    have hn := norm_sub_le conjugateZeta (1 : ℂ)
    norm_num only [hz, norm_one] at hn
    exact hn
  have htri := norm_add_le (l2 w) ((conjugateZeta-1) • l2 (conjugateP j w))
  rw [norm_smul] at htri
  have hm := mul_le_mul hd hp (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  have hnorm : ‖l2 (conjugateAmplitude (step j h))‖ ≤ kappa * ‖l2 w‖ := by
    rw [hv, norm_smul, hz, one_mul]
    dsimp [kappa]
    nlinarith [hm]
  rw [energy_norm, energy_norm]
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (le_trans zero_le_one kappa_one) (norm_nonneg _))).mpr hnorm
  simpa [mul_pow] using hs

private theorem iterate_energy (j : Address) (n : ℕ) (h : Basis → S) :
    energy (conjugateAmplitude ((step j)^[n] h)) ≤
      kappa^(2*n) * energy (conjugateAmplitude h) := by
  induction n generalizing h with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have h1 := ih (step j h)
    have h2 := mul_le_mul_of_nonneg_left (step_energy j h)
      (pow_nonneg (le_trans zero_le_one kappa_one) (2*n))
    refine le_trans h1 (le_trans h2 (le_of_eq ?_))
    rw [← mul_assoc, ← pow_add]
    congr 2 <;> omega

def masked {n : ℕ} (select : Basis → Fin n) (o : Fin n) (h : Basis → S) : Basis → S :=
  fun z => if select z = o then h z else 0

private theorem measurement_energy {n : ℕ} (select : Basis → Fin n) (h : Basis → S) :
    (∑ o, energy (conjugateAmplitude (masked select o h))) =
      energy (conjugateAmplitude h) := by
  classical
  unfold energy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp [masked, conjugateAmplitude, apply_ite]

private theorem call_max {L : Type} (j : Address) (d : Direction) (U : Tree L) :
    callCost d + maxCalls U ≤ maxCalls (.call j d U) := by
  classical
  obtain ⟨p,_,hp⟩ := Finset.exists_mem_eq_sup Finset.univ
    (Finset.univ_nonempty : (Finset.univ : Finset (Path U)).Nonempty) (calls U)
  change callCost d + (Finset.univ.sup (calls U)) ≤ _
  rw [hp]
  exact Finset.le_sup (f := calls (.call j d U)) (Finset.mem_univ p)

private theorem measure_max {L : Type} {n : ℕ} (select : Basis → Fin n)
    (U : Fin n → Tree L) (o : Fin n) :
    maxCalls (U o) ≤ maxCalls (.measure n select U) := by
  classical
  apply Finset.sup_le
  intro p _
  exact Finset.le_sup (f := calls (.measure n select U)) (Finset.mem_univ (⟨o,p⟩))

/-- Sum over all syntactic paths, without pruning unused outcomes. -/
def treeEnergy {L : Type} (T : Tree L) (h : Basis → S) : ℝ :=
  ∑ p : Path T, energy (conjugateAmplitude (branch T p h))

private theorem whole_tree_energy {L : Type} (T : Tree L) (h : Basis → S) :
    treeEnergy T h ≤ kappa^(2*maxCalls T) * energy (conjugateAmplitude h) := by
  classical
  induction T generalizing h with
  | leaf l =>
    change (∑ _p : Unit, energy (conjugateAmplitude h)) ≤
      kappa^(2 * ((Finset.univ : Finset Unit).sup (fun _ => 0))) *
        energy (conjugateAmplitude h)
    simp
  | call j d U ih =>
    change treeEnergy U ((step j)^[callCost d] h) ≤ _
    have h1 := ih ((step j)^[callCost d] h)
    have h2 := mul_le_mul_of_nonneg_left (iterate_energy j (callCost d) h)
      (pow_nonneg (le_trans zero_le_one kappa_one) (2*maxCalls U))
    refine le_trans h1 (le_trans h2 ?_)
    rw [← mul_assoc, ← pow_add]
    apply mul_le_mul_of_nonneg_right _ (energy_nonneg _)
    apply pow_le_pow_right₀ kappa_one
    have hm := call_max j d U
    omega
  | measure n select U ih =>
    change (∑ p : (o : Fin n) × Path (U o),
      energy (conjugateAmplitude (branch (U p.1) p.2 (masked select p.1 h)))) ≤ _
    rw [Fintype.sum_sigma]
    calc
      _ ≤ ∑ o, kappa^(2*maxCalls (U o)) *
          energy (conjugateAmplitude (masked select o h)) :=
        Finset.sum_le_sum (fun o _ => ih o (masked select o h))
      _ ≤ ∑ o, kappa^(2*maxCalls (.measure n select U)) *
          energy (conjugateAmplitude (masked select o h)) := by
        apply Finset.sum_le_sum
        intro o _
        apply mul_le_mul_of_nonneg_right _ (energy_nonneg _)
        exact pow_le_pow_right₀ kappa_one (Nat.mul_le_mul_left 2 (measure_max select U o))
      _ = _ := by rw [← Finset.mul_sum, measurement_energy]

private theorem initial_energy : energy (conjugateAmplitude initial) = 1 := by
  classical
  simp [energy, conjugateAmplitude, initial, exponent, parity_root, apply_ite]

private theorem event_conjugate_bound {L : Type} (T : Tree L)
    (event : Path T → Basis → Bool) :
    |realConjugate (coordinates T event)| ≤ kappa^(2*maxCalls T) := by
  rw [coordinates_conjugate]
  calc
    _ ≤ ∑ p : Path T, ∑ z : Basis, |if event p z then
        (-1 : ℝ)^exponent z * Complex.normSq (conjugateAmplitude (branch T p initial) z)
        else 0| := le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum
          (fun p _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ treeEnergy T initial := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro z _
      split_ifs <;> simp [abs_mul, abs_pow, abs_of_nonneg (Complex.normSq_nonneg _),
        Complex.normSq_nonneg]
    _ ≤ _ := by simpa [initial_energy] using whole_tree_energy T initial



end Coeff

/-- Recursively computed integer coordinates of the actual original event,
its parity-signed nonphysical evaluation and its whole-tree resource bound. -/
theorem original_event_coordinates_and_bound {L : Type} (T : Tree L)
    (event : Path T → Basis → Bool) :
    eventMass T event = Coeff.realPhysical (Coeff.coordinates T event) ∧
    Coeff.realConjugate (Coeff.coordinates T event) =
      (∑ p, ∑ z, if event p z then (-1 : ℝ)^Coeff.exponent z *
        Complex.normSq (Coeff.conjugateAmplitude (Coeff.branch T p Coeff.initial) z)
        else 0) ∧
    |Coeff.realConjugate (Coeff.coordinates T event)| ≤
      Coeff.kappa^(2*maxCalls T) :=
  ⟨(Coeff.coordinates_physical T event).symm, Coeff.coordinates_conjugate T event,
    Coeff.event_conjugate_bound T event⟩

namespace Coeff


private theorem norm_product (x : O) :
    realPhysical x * realConjugate x = ((QuadraticAlgebra.norm x : ℤ) : ℝ) := by
  have hi : phi⁻¹ = phi-1 := by
    change Real.goldenRatio⁻¹ = Real.goldenRatio-1
    rw [Real.inv_goldenRatio]
    dsimp [Real.goldenConj, Real.goldenRatio]
    ring
  have hp : phi^2 = phi+1 := Real.goldenRatio_sq
  change ((x.re : ℝ)+(x.im : ℝ)*phi⁻¹) *
    ((x.re : ℝ)+(x.im : ℝ)*(-phi)) = _
  rw [hi, QuadraticAlgebra.norm_def]
  push_cast
  linear_combination -(x.im : ℝ)^2 * hp

private theorem norm_zero (x : O) (hn : QuadraticAlgebra.norm x = 0) : x = 0 := by
  let g : D5.S0.Carrier.GoldenInt := ⟨x.re-x.im,x.im⟩
  have hg : D5.S0.Carrier.norm g = 0 := by
    dsimp [D5.S0.Carrier.norm, g]
    rw [QuadraticAlgebra.norm_def] at hn
    nlinarith
  have hz := (D5.S0.Carrier.norm_eq_zero_iff g).mp hg
  have ha := congrArg D5.S0.Carrier.GoldenInt.a hz
  have hb := congrArg D5.S0.Carrier.GoldenInt.b hz
  dsimp [g] at ha hb
  ext <;> simp only [QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero] <;> omega

private theorem int_abs_lower (n : ℤ) (hn : n ≠ 0) : (1 : ℝ) ≤ |(n : ℝ)| := by
  have hh : (1 : ℤ) ≤ |n| := by
    by_cases hp : 0 ≤ n
    · rw [abs_of_nonneg hp]; omega
    · rw [abs_of_neg (lt_of_not_ge hp)]; omega
  exact_mod_cast hh

private theorem norm_div11 (x u : O)
    (hu : QuadraticAlgebra.norm u = 11 ∨ QuadraticAlgebra.norm u = -11) :
    11 ∣ QuadraticAlgebra.norm (11*x-u) := by
  let c := 2*x.re*u.re-x.re*u.im-x.im*u.re-2*x.im*u.im
  have he : QuadraticAlgebra.norm (11*x-u) =
      121*QuadraticAlgebra.norm x-11*c+QuadraticAlgebra.norm u := by
    simp only [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_sub,
      QuadraticAlgebra.im_sub, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
    dsimp [c]
    ring
  rw [he]
  rcases hu with hu | hu
  · refine ⟨11*QuadraticAlgebra.norm x-c+1,?_⟩
    rw [hu]; ring
  · refine ⟨11*QuadraticAlgebra.norm x-c-1,?_⟩
    rw [hu]; ring

private theorem discrepancy (x u : O) (a K C : ℝ)
    (hu : realPhysical u = 11*a)
    (hc : |realConjugate u| = 11*C)
    (hn : QuadraticAlgebra.norm u = 11 ∨ QuadraticAlgebra.norm u = -11)
    (hne : realPhysical x ≠ a) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hb : |realConjugate x| ≤ K) :
    1/(11*(K+C)) ≤ |realPhysical x-a| := by
  let y : O := 11*x-u
  have hny : QuadraticAlgebra.norm y ≠ 0 := by
    intro he
    have hy := norm_zero y he
    have hh := congrArg realPhysical hy
    simp only [y, map_sub, map_mul, map_ofNat, map_zero, hu] at hh
    apply hne
    linarith
  obtain ⟨k,hk⟩ := norm_div11 x u hn
  have hk0 : k ≠ 0 := by
    intro he
    apply hny
    change QuadraticAlgebra.norm (11*x-u) = 0
    simp [hk, he]
  have hlow : (11 : ℝ) ≤ |((QuadraticAlgebra.norm y : ℤ) : ℝ)| := by
    have hka := int_abs_lower k hk0
    dsimp [y]
    rw [hk, Int.cast_mul, Int.cast_ofNat, abs_mul]
    norm_num only
    linarith
  have hpy : realPhysical y = 11*(realPhysical x-a) := by
    dsimp [y]
    rw [map_sub, map_mul, map_ofNat, hu]
    ring
  have hcy : |realConjugate y| ≤ 11*(K+C) := by
    dsimp [y]
    simp only [map_sub, map_mul, map_ofNat]
    have ht := abs_sub (11*realConjugate x) (realConjugate u)
    rw [abs_mul, hc] at ht
    norm_num only at ht
    nlinarith
  rw [← norm_product, abs_mul, hpy, abs_mul] at hlow
  norm_num only at hlow
  have hh := mul_le_mul_of_nonneg_left hcy (mul_nonneg (by norm_num : (0:ℝ) ≤ 11) (abs_nonneg (realPhysical x-a)))
  have hden : 0 < 11*(K+C) := by linarith
  rw [div_le_iff₀ hden]
  nlinarith [hh, abs_nonneg (realPhysical x-a)]

private theorem positive_lower (x : O) (K : ℝ) (hK : 0 < K)
    (hp : 0 < realPhysical x) (hb : |realConjugate x| ≤ K) :
    K⁻¹ ≤ realPhysical x := by
  have hn : QuadraticAlgebra.norm x ≠ 0 := by
    intro he
    have hz := norm_zero x he
    rw [hz, map_zero] at hp
    linarith
  have hlow := int_abs_lower (QuadraticAlgebra.norm x) hn
  rw [← norm_product, abs_mul, abs_of_pos hp] at hlow
  rw [inv_le_iff_one_le_mul₀ hK]
  nlinarith [mul_le_mul_of_nonneg_left hb hp.le]

end Coeff

/-- Arithmetic resource bounds for every computed original raw event. The
reference-state and record-law realization obligations are separate. -/
theorem original_event_resource_bounds {L : Type} (T : Tree L)
    (event : Path T → Basis → Bool) :
    (0 < eventMass T event →
      (Coeff.kappa^(2*maxCalls T))⁻¹ ≤ eventMass T event) ∧
    1/(11*(Coeff.kappa^(2*maxCalls T)+(13+5*Real.sqrt 5)/22)) ≤
      |eventMass T event-emptyTarget| ∧
    1/(11*(Coeff.kappa^(2*maxCalls T)+(19+9*Real.sqrt 5)/22)) ≤
      |eventMass T event-referenceTarget| := by
  let x := Coeff.coordinates T event
  have hm := (original_event_coordinates_and_bound T event).1
  have hb := (original_event_coordinates_and_bound T event).2.2
  have hK : 1 ≤ Coeff.kappa^(2*maxCalls T) := one_le_pow₀ Coeff.kappa_one
  have hi : phi⁻¹ = phi-1 := by
    change Real.goldenRatio⁻¹ = Real.goldenRatio-1
    rw [Real.inv_goldenRatio]
    dsimp [Real.goldenConj, Real.goldenRatio]; ring
  refine ⟨?_,?_,?_⟩
  · intro hp
    rw [hm] at hp ⊢
    exact Coeff.positive_lower x _ (lt_of_lt_of_le zero_lt_one hK) hp hb
  · rw [hm]
    apply Coeff.discrepancy x (⟨4,-5⟩ : Coeff.O) emptyTarget _
      ((13+5*Real.sqrt 5)/22)
    · simp only [Coeff.realPhysical, Coeff.evalO, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk]
      norm_num only [Int.cast_ofNat, Int.cast_neg]
      rw [hi]; dsimp [phi, emptyTarget]; ring
    · simp only [Coeff.realConjugate, Coeff.evalO, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk]
      norm_num only [Int.cast_ofNat, Int.cast_neg]
      rw [abs_of_nonneg (by have hp := Coeff.phi_positive; nlinarith)]
      dsimp [phi]; ring
    · left; norm_num [QuadraticAlgebra.norm_def]
    · rw [← hm]
      exact (original_event_arithmetic T event).2.1
    · exact hK
    · positivity
    · exact hb
  · rw [hm]
    apply Coeff.discrepancy x (⟨-5,9⟩ : Coeff.O) referenceTarget _
      ((19+9*Real.sqrt 5)/22)
    · simp only [Coeff.realPhysical, Coeff.evalO, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk]
      norm_num only [Int.cast_ofNat, Int.cast_neg]
      rw [hi]; dsimp [phi, referenceTarget]; ring
    · simp only [Coeff.realConjugate, Coeff.evalO, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk]
      norm_num only [Int.cast_ofNat, Int.cast_neg]
      rw [abs_of_nonpos (by dsimp [phi]; nlinarith [Real.sqrt_nonneg (5:ℝ)])]
      dsimp [phi]; ring
    · right; norm_num [QuadraticAlgebra.norm_def]
    · rw [← hm]
      exact (original_event_arithmetic T event).2.2
    · exact hK
    · positivity
    · exact hb

#print axioms original_event_coordinates_and_bound
#print axioms original_event_resource_bounds

namespace Actual
open scoped ComplexOrder MatrixOrder

/-- A computational vector on the complete original carrier. -/
def ket (b : Basis) : Basis → ℂ := fun z => if z = b then 1 else 0

private theorem flip_ne (i : Fin 16) (b : Basis) : flip i b ≠ b := by
  intro h
  have hi := congrFun h i
  cases hb : b i <;> simpa [flip, hb] using hi

private theorem flip_eq (i : Fin 16) (z b : Basis) :
    flip i z = b ↔ z = flip i b := by
  constructor <;> intro h
  · rw [← h, Coeff.flip_flip]
  · rw [h, Coeff.flip_flip]

private theorem gate_ket (j : Address) (b : Basis) :
    (gate j).mulVec (ket b) =
      (zeta * (1 + (zeta - 1) * Coeff.evalO t Coeff.t_sq (Coeff.diagonal j b))) • ket b +
      (if Coeff.active j b then zeta * (zeta - 1) * beta^3 else 0) •
        ket (flip (center j) b) := by
  funext z
  simp only [gate, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul, Coeff.p_action, ket]
  by_cases hz : z = b
  · subst z
    simp [flip_ne, Ne.symm (flip_ne (center j) b)] <;> ring
  · by_cases hf : z = flip (center j) b
    · subst z
      simp only [Coeff.flip_flip, if_pos rfl, hz, if_false, mul_zero,
        mul_one, zero_add, Coeff.active_flip]
      split_ifs <;> ring
    · have hfb : flip (center j) z ≠ b := by
        exact fun h => hf ((flip_eq (center j) z b).mp h)
      simp [hz, hf, hfb]

/-- Source sites b1,b2,b3 are shifted positions 2,3,4; all other bits
remain the original root bits. -/
def sourceWord (x y z : Bool) : Basis :=
  Function.update (Function.update (Function.update rootWord 2 x) 3 y) 4 z

def a : ℂ := zeta * (1 + (zeta - 1) * t)
def b : ℂ := zeta * (zeta - 1) * beta^3
def c : ℂ := zeta * (1 + (zeta - 1) * t^2)

/-- The original three forward source calls, in chronological order. -/
def sourceTree : Tree Cut :=
  .call 3 .forward (.call 2 .forward (.call 1 .forward (.leaf .active)))

def sourceVector : Basis → ℂ :=
  (gate 1).mulVec ((gate 2).mulVec ((gate 3).mulVec omega0))

def fiveTermVector : Basis → ℂ :=
  (a^2*b) • ket (sourceWord false false false) +
  (a*b^2) • ket (sourceWord true false false) +
  (zeta*a*c) • ket (sourceWord false false true) +
  (zeta*b*c) • ket (sourceWord true false true) +
  (zeta*b^2) • ket (sourceWord false true false)

private theorem source_start : omega0 = ket (sourceWord false false true) := by
  have h : rootWord = sourceWord false false true := by decide
  change ket rootWord = ket (sourceWord false false true)
  exact congrArg ket h

private theorem source_steps :
    sourceVector = fiveTermVector := by
  have h3 : (gate 3).mulVec (ket (sourceWord false false true)) =
      b • ket (sourceWord false false false) +
      c • ket (sourceWord false false true) := by
    rw [gate_ket]
    have hf : flip (center 3) (sourceWord false false true) =
        sourceWord false false false := by decide
    rw [hf, show Coeff.diagonal 3 (sourceWord false false true) = Coeff.tau^2 by rfl,
      show Coeff.active 3 (sourceWord false false true) = true by rfl]
    simp only [Bool.true_eq, if_true, map_pow, Coeff.evalO_tau]
    change c • _ + b • _ = _
    abel
  have h20 : (gate 2).mulVec (ket (sourceWord false false false)) =
      a • ket (sourceWord false false false) +
      b • ket (sourceWord false true false) := by
    rw [gate_ket]
    have hf : flip (center 2) (sourceWord false false false) =
        sourceWord false true false := by decide
    rw [hf, show Coeff.diagonal 2 (sourceWord false false false) = Coeff.tau by rfl,
      show Coeff.active 2 (sourceWord false false false) = true by rfl]
    simp only [Bool.true_eq, if_true, Coeff.evalO_tau]
    rfl
  have h21 : (gate 2).mulVec (ket (sourceWord false false true)) =
      zeta • ket (sourceWord false false true) := by
    rw [gate_ket, show Coeff.diagonal 2 (sourceWord false false true) = 0 by rfl,
      show Coeff.active 2 (sourceWord false false true) = false by rfl]
    simp
  have h10 : (gate 1).mulVec (ket (sourceWord false false false)) =
      a • ket (sourceWord false false false) +
      b • ket (sourceWord true false false) := by
    rw [gate_ket]
    have hf : flip (center 1) (sourceWord false false false) =
        sourceWord true false false := by decide
    rw [hf, show Coeff.diagonal 1 (sourceWord false false false) = Coeff.tau by rfl,
      show Coeff.active 1 (sourceWord false false false) = true by rfl]
    simp only [Bool.true_eq, if_true, Coeff.evalO_tau]
    rfl
  have h11 : (gate 1).mulVec (ket (sourceWord false false true)) =
      a • ket (sourceWord false false true) +
      b • ket (sourceWord true false true) := by
    rw [gate_ket]
    have hf : flip (center 1) (sourceWord false false true) =
        sourceWord true false true := by decide
    rw [hf, show Coeff.diagonal 1 (sourceWord false false true) = Coeff.tau by rfl,
      show Coeff.active 1 (sourceWord false false true) = true by rfl]
    simp only [Bool.true_eq, if_true, Coeff.evalO_tau]
    rfl
  have h12 : (gate 1).mulVec (ket (sourceWord false true false)) =
      zeta • ket (sourceWord false true false) := by
    rw [gate_ket, show Coeff.diagonal 1 (sourceWord false true false) = 0 by rfl,
      show Coeff.active 1 (sourceWord false true false) = false by rfl]
    simp
  rw [sourceVector, source_start, h3]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, h20, h21, h10, h11, h12]
  dsimp only [fiveTermVector]
  module

/-- Exact sparse action of the actual original full matrices on the fixed root. -/
private theorem original_source_vector :
    (operator sourceTree ()).mulVec omega0 = fiveTermVector ∧
    calls sourceTree () = 3 := by
  constructor
  · simpa [sourceTree, operator, callMatrix, sourceVector, Matrix.mulVec_mulVec, Matrix.mul_assoc] using source_steps
  · rfl


/-- The original complement contains all fifteen other native bits. -/
abbrev Rest := {i : Fin 16 // i ≠ 2} → Bool
def cut : Basis ≃ Fin 2 × Rest :=
  (Equiv.funSplitAt 2 Bool).trans (Equiv.prodCongr finTwoEquiv.symm (Equiv.refl Rest))
abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ
local instance : NormedAddCommGroup Qubit := Matrix.instL2OpNormedAddCommGroup
local instance : NormedSpace ℂ Qubit := Matrix.instL2OpNormedSpace
local instance : NormedRing Qubit := Matrix.instL2OpNormedRing
local instance : NormedAlgebra ℂ Qubit := Matrix.instL2OpNormedAlgebra

/-- Mathematical reduction at original site b1. Original records remain
outside this operation; it asserts no physical deletion or fresh preparation. -/
def cross (v w : Basis → ℂ) : Qubit :=
  D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight
    (Matrix.vecMulVec (v ∘ cut.symm) (star (w ∘ cut.symm)))

def reduced (v : Basis → ℂ) : Qubit := cross v v

private theorem ket_cut (x : Basis) (i : Fin 2) (e : Rest) :
    ket x (cut.symm (i,e)) =
      if i = (cut x).1 then if e = (cut x).2 then 1 else 0 else 0 := by
  have h : cut.symm (i,e) = x ↔ i = (cut x).1 ∧ e = (cut x).2 := by
    rw [Equiv.symm_apply_eq, Prod.ext_iff]
  simp only [ket, h]
  split_ifs <;> simp_all

private theorem source_rest (x y z x' y' z' : Bool) :
    (cut (sourceWord x y z)).2 = (cut (sourceWord x' y' z')).2 ↔
      y = y' ∧ z = z' := by
  cases x <;> cases y <;> cases z <;>
    cases x' <;> cases y' <;> cases z' <;> decide

/-- The lawful reduction is positive on every actual full-carrier vector. -/
private theorem reduced_positive (v : Basis → ℂ) : (reduced v).PosSemidef :=
  D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight_posSemidef
    (Matrix.posSemidef_vecMulVec_self_star (v ∘ cut.symm))


private theorem cut_source_bit (x y z : Bool) :
    (cut (sourceWord x y z)).1 = if x then 1 else 0 := by
  cases x <;> rfl

open D5.S3.Quantum.Information.PartialTraceMutualInformation

private theorem cross_add_left (u v w : Basis → ℂ) :
    cross (u+v) w = cross u w + cross v w := by
  unfold cross
  change partialTraceRight
    (Matrix.vecMulVec ((u ∘ cut.symm)+(v ∘ cut.symm)) (star (w ∘ cut.symm))) = _
  rw [Matrix.add_vecMulVec, partialTraceRight_add]

private theorem cross_add_right (u v w : Basis → ℂ) :
    cross u (v+w) = cross u v + cross u w := by
  unfold cross
  change partialTraceRight
    (Matrix.vecMulVec (u ∘ cut.symm) (star ((v ∘ cut.symm)+(w ∘ cut.symm)))) = _
  rw [star_add, Matrix.vecMulVec_add, partialTraceRight_add]

private theorem cross_ket_smul (a b : ℂ) (x y : Basis) (i j : Fin 2) :
    cross (a • ket x) (b • ket y) i j =
      if i = (cut x).1 ∧ j = (cut y).1 ∧ (cut x).2 = (cut y).2
      then a * star b else 0 := by
  classical
  simp only [cross, partialTraceRight, Matrix.vecMulVec_apply,
    Function.comp_apply, Pi.star_apply, Pi.smul_apply, smul_eq_mul, map_mul, ket_cut]
  by_cases hi : i = (cut x).1 <;> by_cases hj : j = (cut y).1 <;>
    simp [hi, hj, mul_ite, ite_mul, apply_ite (starRingEnd ℂ), eq_comm]

def sourceLocal (i : Fin 2) : ℂ := if i = 0 then a else b
def p0 : Qubit := fun i j => if i = 0 ∧ j = 0 then 1 else 0
def sourceMixture : Qubit := fun i j =>
  (a * star a * b * star b + c * star c) * sourceLocal i * star (sourceLocal j) +
  (b * star b)^2 * p0 i j

private theorem source_reduction : reduced sourceVector = sourceMixture := by
  change cross sourceVector sourceVector = _
  rw [source_steps]
  simp only [fiveTermVector, cross_add_left, cross_add_right]
  ext i j
  simp only [Matrix.add_apply, cross_ket_smul, cut_source_bit, source_rest]
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceMixture, sourceLocal, p0, Matrix.vecMulVec_apply,
      Pi.star_apply]
  all_goals simp only [starRingEnd_apply, star_mul, star_pow]
  · linear_combination
      (a * star a * c * star c + b^2 * (star b)^2) * Coeff.zeta_norm
  · linear_combination (a * star b * c * star c) * Coeff.zeta_norm
  · linear_combination (b * star a * c * star c) * Coeff.zeta_norm
  · linear_combination (b * star b * c * star c) * Coeff.zeta_norm

private theorem zeta_cube : zeta^3 = t-t*zeta := by
  calc
    zeta^3 = zeta*zeta^2 := by ring
    _ = zeta*(-1-t*zeta) := by rw [Coeff.zeta_sq]
    _ = -zeta-t*zeta^2 := by ring
    _ = -zeta-t*(-1-t*zeta) := by rw [Coeff.zeta_sq]
    _ = t+(t^2-1)*zeta := by ring
    _ = t-t*zeta := by rw [Coeff.t_sq]; ring

private theorem zeta_four : zeta^4 = t+zeta := by
  calc
    zeta^4 = zeta^3*zeta := by ring
    _ = (t-t*zeta)*zeta := by rw [zeta_cube]
    _ = t*zeta-t*zeta^2 := by ring
    _ = t*zeta-t*(-1-t*zeta) := by rw [Coeff.zeta_sq]
    _ = t+(t+t^2)*zeta := by ring
    _ = t+zeta := by rw [Coeff.t_sq]; ring

private theorem a_value : a = -t := by
  unfold a
  calc
    _ = zeta+(zeta^2-zeta)*t := by ring
    _ = zeta+(-1-t*zeta-zeta)*t := by rw [Coeff.zeta_sq]
    _ = -t := by linear_combination -zeta * Coeff.t_sq

private theorem b_value : b = -beta*zeta^4 := by
  have hb : beta^3 = beta*t := by rw [pow_succ, Coeff.beta_sq]; ring
  unfold b
  rw [hb, zeta_four]
  calc
    _ = (zeta^2-zeta)*beta*t := by ring
    _ = (-1-t*zeta-zeta)*beta*t := by rw [Coeff.zeta_sq]
    _ = -beta*(t+zeta) := by linear_combination -(beta*zeta) * Coeff.t_sq

private theorem c_value : c = -t*zeta^3 := by
  unfold c
  rw [Coeff.t_sq, zeta_cube]
  calc
    _ = zeta^2-(zeta+(zeta^2-zeta)*t)+zeta := by ring
    _ = -1-t*zeta-(-t)+zeta := by
      rw [show zeta+(zeta^2-zeta)*t = a by unfold a; ring,
        a_value, Coeff.zeta_sq]
    _ = -t*(t-t*zeta) := by linear_combination (1-zeta)*Coeff.t_sq

private theorem star_t : star t = t := by simp [t]
private theorem star_beta : star beta = beta := by simp [beta]
private theorem phase_norm (n : ℕ) : zeta^n * star (zeta^n) = 1 := by
  rw [star_pow, ← mul_pow, Coeff.zeta_norm, one_pow]

private theorem a_norm : a * star a = t^2 := by
  rw [a_value, star_neg, star_t]; ring
private theorem b_norm : b * star b = t := by
  rw [b_value, star_mul, star_neg, star_beta]
  calc
    _ = beta^2 * (zeta^4*star (zeta^4)) := by ring
    _ = t := by rw [phase_norm, Coeff.beta_sq, mul_one]
private theorem c_norm : c * star c = t^2 := by
  rw [c_value, star_mul, star_neg, star_t]
  calc
    _ = t^2*(zeta^3*star (zeta^3)) := by ring
    _ = t^2 := by rw [phase_norm, mul_one]

def gamma : ℂ := t^2 * beta * star (zeta^4)
def chi : Qubit := !![t,gamma;star gamma,t^2]

private theorem mixture_chi : sourceMixture = chi := by
  have hw : a * star a * b * star b + c * star c = t := by
    rw [show a * star a * b * star b = (a*star a)*(b*star b) by ring,
      a_norm, b_norm, c_norm]
    linear_combination t * Coeff.t_sq
  ext i j
  simp only [sourceMixture, hw, b_norm]
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceLocal, p0, chi, Matrix.vecMulVec_apply, Pi.star_apply]
  all_goals try simp only [starRingEnd_apply]
  · rw [show t*a*star a = t*(a*star a) by ring, a_norm]
    linear_combination t*Coeff.t_sq
  · rw [a_value, b_value, star_mul, star_neg, star_beta]
    unfold gamma
    ring
  · rw [a_value, b_value, star_neg, star_t]
    simp only [gamma, star_mul, star_pow, star_t, star_beta, star_star, starRingEnd_apply]
    ring
  · rw [show t*b*star b = t*(b*star b) by ring, b_norm]
    ring

/-- The full-carrier source calls give exactly the same native marginal chi. -/
private theorem original_source_calibration :
    reduced ((operator sourceTree ()).mulVec omega0) = chi ∧ chi.PosSemidef := by
  have hv := original_source_vector.1
  have hc : reduced ((operator sourceTree ()).mulVec omega0) = chi := by
    rw [hv, ← source_steps, source_reduction, mixture_chi]
  exact ⟨hc, hc ▸ reduced_positive _⟩



private theorem t_nonzero : t ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (inv_ne_zero Coeff.phi_positive.ne')

private theorem gamma_norm : gamma * star gamma = t^5 := by
  simp only [gamma, star_mul, star_pow, star_t, star_beta, star_star]
  calc
    _ = t^4 * beta^2 * (zeta^4 * star (zeta^4)) := by rw [star_pow]; ring
    _ = t^5 := by rw [phase_norm, Coeff.beta_sq]; ring

private theorem chi_det : chi.det = t^4 := by
  rw [Matrix.det_fin_two]
  change t * t^2 - gamma * star gamma = t^4
  rw [gamma_norm]
  linear_combination -(t^3)*Coeff.t_sq

private theorem chi_trace : chi.trace = 1 := by
  simp only [chi, Matrix.trace, Fin.sum_univ_two]
  norm_num
  linear_combination Coeff.t_sq

private theorem chi_faithful : chi.PosDef :=
  original_source_calibration.2.posDef_iff_det_ne_zero.mpr
    (chi_det ▸ pow_ne_zero 4 t_nonzero)

private theorem empty_reduction : reduced omega0 = p0 := by
  rw [source_start]
  change cross (ket (sourceWord false false true))
    (ket (sourceWord false false true)) = _
  rw [← one_smul ℂ (ket (sourceWord false false true))]
  ext i j
  rw [cross_ket_smul, cut_source_bit]
  fin_cases i <;> fin_cases j <;> norm_num [p0]

def rootScale : ℝ := Real.sqrt (1+2*(phi⁻¹)^2)
def chiRoot : Qubit := (rootScale : ℂ)⁻¹ • (chi + t^2 • (1 : Qubit))

private theorem rootScale_pos : 0 < rootScale := by
  dsimp [rootScale]
  positivity

private theorem rootScale_sq : (rootScale : ℂ)^2 = 1+2*t^2 := by
  dsimp [rootScale, t]
  norm_cast
  exact Real.sq_sqrt (by positivity)

private theorem chi_square : chi*chi = chi-t^4 • (1 : Qubit) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chi, Matrix.mul_apply, Fin.sum_univ_two,
      Pi.smul_apply, smul_eq_mul, star_t, star_pow]
  all_goals try simp only [starRingEnd_apply]
  · rw [gamma_norm]
    linear_combination (t^3+t)*Coeff.t_sq
  · linear_combination gamma*Coeff.t_sq
  · linear_combination (star gamma)*Coeff.t_sq
  · rw [mul_comm (star gamma) gamma, gamma_norm]
    linear_combination (t^3+t^2)*Coeff.t_sq

private theorem chiRoot_square : chiRoot*chiRoot = chi := by
  have hn : (rootScale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr rootScale_pos.ne'
  have hnum : (chi+t^2 • (1 : Qubit)) * (chi+t^2 • (1 : Qubit)) =
      (1+2*t^2) • chi := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, chi_square]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one,
      smul_smul]
    module
  rw [chiRoot, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hnum, smul_smul]
  have hc : (rootScale : ℂ)⁻¹*(rootScale : ℂ)⁻¹*(1+2*t^2) = 1 := by
    rw [← rootScale_sq]
    field_simp
  rw [hc, one_smul]

private theorem chiRoot_positive : chiRoot.PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact original_source_calibration.2.add
      (Matrix.PosSemidef.one.smul (by
        simp only [t, ← Complex.ofReal_pow, Complex.nonneg_iff, Complex.ofReal_re,
          Complex.ofReal_im, and_true]
        positivity))
  · exact_mod_cast (inv_nonneg.mpr rootScale_pos.le : 0 ≤ rootScale⁻¹)

private theorem chi_sqrt : cfc Real.sqrt chi = chiRoot := by
  have h : CFC.sqrt chi = chiRoot :=
    CFC.sqrt_unique chiRoot_square chiRoot_positive.nonneg
  rwa [CFC.sqrt_eq_real_sqrt _ original_source_calibration.2.nonneg,
    cfcₙ_eq_cfc] at h


/-- The same original b1 instrument, after summing its retained read. -/
def delta (X : Qubit) : Qubit := Matrix.diagonal (fun i => X i i)

private theorem read_cut (i : Fin 2) (e : Rest) :
    readBit 2 (cut.symm (i,e)) = i := by
  fin_cases i <;> rfl

private theorem projected_cut (v : Basis → ℂ) (j i : Fin 2) (e : Rest) :
    ((projector (readBit 2) j).mulVec v) (cut.symm (i,e)) =
      if i = j then v (cut.symm (i,e)) else 0 := by
  simp [projector, Matrix.mulVec_diagonal, read_cut]

private theorem reduced_projector (v : Basis → ℂ) (o : Fin 2) :
    reduced ((projector (readBit 2) o).mulVec v) =
      fun i j => if i = o ∧ j = o then reduced v i j else 0 := by
  ext i j
  simp only [reduced, cross, partialTraceRight, Matrix.vecMulVec_apply,
    Function.comp_apply, Pi.star_apply, projected_cut]
  by_cases hi : i = o <;> by_cases hj : j = o <;>
    simp [hi, hj, apply_ite (starRingEnd ℂ)]

private theorem native_delta (v : Basis → ℂ) :
    (∑ j : Fin 2, reduced ((projector (readBit 2) j).mulVec v)) =
      delta (reduced v) := by
  rw [Fin.sum_univ_two, reduced_projector, reduced_projector]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [delta]

private theorem read_empty (j : Fin 2) :
    (projector (readBit 2) j).mulVec omega0 =
      if j = 0 then omega0 else 0 := by
  funext z
  simp only [projector, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply]
  by_cases hz : z = rootWord
  · subst z
    fin_cases j <;> norm_num [omega0, readBit, rootWord]
  · simp [omega0, hz]

def inverseRoot : Qubit := Matrix.diagonal ![beta⁻¹,t⁻¹]

private theorem h_diagonal :
    delta chi = Matrix.diagonal (fun i => ((![(phi⁻¹),(phi⁻¹)^2] : Fin 2 → ℝ) i : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [delta, chi, t]

private theorem inverse_root :
    cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (delta chi) = inverseRoot := by
  rw [h_diagonal,
    D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverseRoot, beta, t, Real.sqrt_sq (inv_nonneg.mpr Coeff.phi_positive.le),
      Real.sqrt_sq Coeff.phi_positive.le]

/-- The fixed mathematical Petz formula. This definition adds no native gate. -/
def petz (Y : Qubit) : Qubit :=
  cfc Real.sqrt chi *
    delta (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (delta chi) * Y *
      cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (delta chi)) *
    cfc Real.sqrt chi

private theorem petz_empty_entry :
    petz p0 1 1 = t^4/(1+2*t^2) := by
  have hb : beta ≠ 0 := by
    intro h
    have hs := Coeff.beta_sq
    rw [h, zero_pow (by decide)] at hs
    exact t_nonzero hs.symm
  have hr : (rootScale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr rootScale_pos.ne'
  have hd : 1+2*t^2 ≠ 0 := by rw [← rootScale_sq]; exact pow_ne_zero 2 hr
  rw [petz, chi_sqrt, inverse_root]
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, chiRoot, inverseRoot,
    delta, p0, chi, Pi.smul_apply, smul_eq_mul]
  simp only [starRingEnd_apply]
  have hg : star gamma * gamma = t^5 := by rw [mul_comm, gamma_norm]
  calc
    _ = (star gamma * gamma) / ((rootScale : ℂ)^2 * beta^2) := by field_simp <;> ring
    _ = t^4/(1+2*t^2) := by
      rw [hg, rootScale_sq, Coeff.beta_sq]
      field_simp <;> ring

private theorem empty_target_value :
    ((emptyTarget : ℝ) : ℂ) = t^4/(1+2*t^2) := by
  have hi : phi⁻¹ = phi-1 := by
    change Real.goldenRatio⁻¹ = Real.goldenRatio-1
    rw [Real.inv_goldenRatio]
    dsimp [Real.goldenConj, Real.goldenRatio]
    ring
  have he : ((emptyTarget : ℝ) : ℂ) = (4-5*t)/11 := by
    simp only [t, emptyTarget, Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [hi]
    push_cast
    dsimp [phi]
    push_cast
    ring
  rw [he]
  have hd : 1+2*t^2 ≠ 0 := by
    rw [← rootScale_sq]
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr rootScale_pos.ne')
  apply (eq_div_iff hd).2
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff (by norm_num : (11 : ℂ) ≠ 0)).2
  linear_combination -(11*t^2-t+4)*Coeff.t_sq

/-- The actual three-call calibration, native read and fixed Petz empty-input
event are linked to every complete original continuation's raw discrepancy.
The separate five-call retained-history and full-record targets remain open. -/
theorem original_empty_petz_consumer :
    reduced ((operator sourceTree ()).mulVec omega0) = chi ∧
    calls sourceTree () = 3 ∧ chi.PosDef ∧ chi.trace = 1 ∧ chi.det = t^4 ∧
    cfc Real.sqrt chi = chiRoot ∧
    (∀ v : Basis → ℂ,
      (∑ j : Fin 2, reduced ((projector (readBit 2) j).mulVec v)) =
        delta (reduced v)) ∧
    reduced omega0 = p0 ∧
    (∀ j : Fin 2, (projector (readBit 2) j).mulVec omega0 =
      if j = 0 then omega0 else 0) ∧
    petz (reduced omega0) 1 1 = ((emptyTarget : ℝ) : ℂ) ∧
    (∀ C : Fin 2 → Tree Stop,
      let T := extensionAt .active C
      eventMass T (fun _ z => z 2) ≠ (petz (reduced omega0) 1 1).re ∧
      1/(11*(Coeff.kappa^(2*maxCalls T)+(13+5*Real.sqrt 5)/22)) ≤
        |eventMass T (fun _ z => z 2) - (petz (reduced omega0) 1 1).re|) := by
  have hp : petz (reduced omega0) 1 1 = ((emptyTarget : ℝ) : ℂ) := by
    rw [empty_reduction, petz_empty_entry, empty_target_value]
  refine ⟨original_source_calibration.1, original_source_vector.2,
    chi_faithful, chi_trace, chi_det, chi_sqrt, native_delta, empty_reduction,
    read_empty, hp, ?_⟩
  intro C
  dsimp only
  rw [hp, Complex.ofReal_re]
  exact ⟨(original_event_arithmetic _ _).2.1,
    (original_event_resource_bounds _ _).2.1⟩

#print axioms original_empty_petz_consumer

end Actual

end D5.S3.Quantum.Dynamics.NativeProtocolGraft
