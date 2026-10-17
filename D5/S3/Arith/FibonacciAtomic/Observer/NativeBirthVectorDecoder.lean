/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeBirthVectorDecoder
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Complete-level native birth vectors decode exactly the finite original prefix pattern. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
import D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedNavigationCompiler
import Mathlib.Logic.Equiv.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeBirthVectorDecoder

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open NativeDepthPatterns (Pattern depthEquiv decompose)
open NativeRankedNavigationCompiler (pathThreshold)

abbrev LevelAddress (d : Nat) := {a : Address // a.length = d}
abbrev LevelVector (d : Nat) := LevelAddress d → Nat

/-- The atomic code is the path threshold for alpha and its natural-number
predecessor for beta. -/
def atomicBirth (b : Bool) (a : Address) : Nat :=
  if b then pathThreshold a else pathThreshold a - 1

/-- The recursive address code: the root has code zero, an atomic source uses
`atomicBirth`, and a pair selects a child without an epoch shift. The results
below concern this code; they do not establish its interpretation as the least
epoch of actual presence for the full source/address family. -/
def birthAt : Address → Source → Nat
  | [], _ => 0
  | a, .of b => atomicBirth b a
  | false :: a, .mul l _ => birthAt a l
  | true :: a, .mul _ r => birthAt a r

/-- Collect the recursively defined `birthAt` code at every address of one
complete depth. -/
def birthVector (d : Nat) (u : Source) : LevelVector d :=
  fun a => birthAt a.1 u

def alphaVector (d : Nat) : LevelVector (d + 1) :=
  fun a => pathThreshold a.1

def betaVector (d : Nat) : LevelVector (d + 1) :=
  fun a => pathThreshold a.1 - 1

def leftBlock {d : Nat} (x : LevelVector (d + 1)) : LevelVector d :=
  fun a => x ⟨false :: a.1, by simp [a.2]⟩

def rightBlock {d : Nat} (x : LevelVector (d + 1)) : LevelVector d :=
  fun a => x ⟨true :: a.1, by simp [a.2]⟩

def tailAddress {d : Nat} (a : LevelAddress (d + 1)) : LevelAddress d :=
  ⟨a.1.tail, by
    cases h : a.1 with
    | nil =>
        have hz : 0 = d + 1 := by simpa [h] using a.2
        omega
    | cons b t => simpa [h] using a.2⟩

/-- A total recursive decoder, proved correct on `patternVector` images by
`decodeBirth_patternVector`. At depth zero it returns `some ()` for every input;
at positive depth it tests the rightmost sentinel and otherwise recurses on the
two blocks. Acceptance does not certify that an arbitrary input is an image
vector. -/
def decodeBirth : (d : Nat) → LevelVector d → Option (Pattern d)
  | 0, _ => some ()
  | d + 1, x =>
      let right := x ⟨List.replicate (d + 1) true, by simp⟩
      if right = 2 * (d + 1) then some (.inl true)
      else if right = 2 * (d + 1) - 1 then some (.inl false)
      else
        match decodeBirth d (leftBlock x), decodeBirth d (rightBlock x) with
        | some l, some r => some (.inr (l, r))
        | _, _ => none

/-- The vector code carried by a finite original prefix pattern. -/
def patternVector : (d : Nat) → Pattern d → LevelVector d
  | 0, _ => fun _ => 0
  | d + 1, .inl b => fun a => atomicBirth b a.1
  | d + 1, .inr (l, r) =>
      fun a => if h : a.1.head? = some false then
        patternVector d l (tailAddress a)
      else
        patternVector d r (tailAddress a)

theorem pathThreshold_bound : ∀ a : Address, pathThreshold a ≤ 2 * a.length := by
  intro a
  induction a with
  | nil => rfl
  | cons b a ih => cases b <;> simp [pathThreshold, List.length_cons] at * <;> omega

/-- Every complete-depth code is bounded by twice the depth. -/
theorem patternVector_bound :
    ∀ d (p : Pattern d) (a : LevelAddress d), patternVector d p a ≤ 2 * d := by
  intro d
  induction d with
  | zero => intro p a; simp [patternVector]
  | succ d ih =>
      intro p a
      cases p with
      | inl b =>
          rw [patternVector]
          by_cases hb : b
          · simp [atomicBirth, hb]
            have ht := pathThreshold_bound a.1
            omega
          · simp [atomicBirth, hb]
            have ht := pathThreshold_bound a.1
            omega
      | inr p =>
          by_cases h : a.1.head? = some false
          · have hh := ih p.1 (tailAddress a)
            simp [patternVector, h]
            omega
          · have hh := ih p.2 (tailAddress a)
            simp [patternVector, h]
            omega

theorem birthVector_decompose (d : Nat) (u : Source) :
    birthVector d u = patternVector d (decompose d u).1 := by
  induction d generalizing u with
  | zero =>
      funext a
      have hz : a.1 = [] := by
        cases h : a.1 with
        | nil => rfl
        | cons b t =>
            have : False := by simpa [h] using a.2
            exact this.elim
      simp [birthVector, patternVector, birthAt, hz]
  | succ d ih =>
      cases u with
      | of b =>
          funext a
          rcases a with ⟨a, ha⟩
          cases a with
          | nil => simp at ha
          | cons c t =>
              simp [birthVector, birthAt, patternVector, decompose, atomicBirth]
      | mul l r =>
          funext a
          rcases a with ⟨a, ha⟩
          cases a with
          | nil => simp at ha
          | cons b a =>
              cases b with
              | false =>
                  have ha' : a.length = d := by simpa using ha
                  change birthAt a l =
                    patternVector d (decompose d l).1 ⟨a, ha'⟩
                  simpa [birthVector] using congrFun (ih l) ⟨a, ha'⟩
              | true =>
                  have ha' : a.length = d := by simpa using ha
                  change birthAt a r =
                    patternVector d (decompose d r).1 ⟨a, ha'⟩
                  simpa [birthVector] using congrFun (ih r) ⟨a, ha'⟩

theorem pathThreshold_allTrue (d : Nat) :
    pathThreshold (List.replicate d true) = 2 * d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [List.replicate_succ, pathThreshold, ih]; omega

theorem leftBlock_patternVector (d : Nat) (l r : Pattern d) :
    leftBlock (patternVector (d + 1) (.inr (l, r))) = patternVector d l := by
  funext a
  simp [leftBlock, patternVector, tailAddress]

theorem rightBlock_patternVector (d : Nat) (l r : Pattern d) :
    rightBlock (patternVector (d + 1) (.inr (l, r))) = patternVector d r := by
  funext a
  simp [rightBlock, patternVector, tailAddress]

theorem patternVector_rightmost_pair (d : Nat) (l r : Pattern d) :
    patternVector (d + 1) (.inr (l, r))
        ⟨List.replicate (d + 1) true, by simp⟩ =
      patternVector d r ⟨List.replicate d true, by simp⟩ := by
  simp [patternVector, tailAddress, List.replicate_succ]

theorem decodeBirth_patternVector :
    ∀ d (p : Pattern d), decodeBirth d (patternVector d p) = some p := by
  intro d
  induction d with
  | zero => intro p; cases p; rfl
  | succ d ih =>
      intro p
      cases p with
      | inl b =>
          by_cases hb : b
          · simp [decodeBirth, patternVector, atomicBirth, hb,
              pathThreshold_allTrue]
          · simp [decodeBirth, patternVector, atomicBirth, hb,
              pathThreshold_allTrue]
            omega
      | inr p =>
          have bound : patternVector d p.2
              ⟨List.replicate d true, by simp⟩ ≤ 2 * d :=
            patternVector_bound d p.2 ⟨List.replicate d true, by simp⟩
          rw [decodeBirth]
          rw [patternVector_rightmost_pair d p.1 p.2]
          have hs : 2 * d < 2 * (d + 1) - 1 := by omega
          have hlt : patternVector d p.2
              ⟨List.replicate d true, by simp⟩ < 2 * (d + 1) - 1 :=
            lt_of_le_of_lt bound hs
          have hne1 : patternVector d p.2
              ⟨List.replicate d true, by simp⟩ ≠ 2 * (d + 1) := by omega
          have hne2 : patternVector d p.2
              ⟨List.replicate d true, by simp⟩ ≠ 2 * (d + 1) - 1 := by omega
          rw [if_neg hne1, if_neg hne2]
          rw [leftBlock_patternVector d p.1 p.2,
            rightBlock_patternVector d p.1 p.2]
          simp [ih]

end D5.S3.Arith.FibonacciAtomic.Observer.NativeBirthVectorDecoder
