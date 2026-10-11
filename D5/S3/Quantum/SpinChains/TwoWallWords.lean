/- GID: D5/S3/Quantum/SpinChains/TwoWallWords
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/TwoWallWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal two-wall cyclic words carry the eclectic bond action and translation. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Data.Fin.VecNotation

open scoped BigOperators

namespace D5.S3.Quantum.SpinChains.TwoWallWords

/-- The three letters, with the wall represented by the third letter. -/
abbrev Letter := Fin 3

def one : Letter := 0
def two : Letter := 1
def wall : Letter := 2

/-- Cyclic sites; the length is always at least two. -/
abbrev Pos (a b : ℕ) := ZMod (a + b + 2)

instance lengthNeZero (a b : ℕ) : NeZero (a + b + 2) := ⟨by omega⟩

/-- Number of occurrences of a letter. -/
def count {a b : ℕ} (c : Letter) (w : Pos a b → Letter) : ℕ :=
  ∑ p, if w p = c then 1 else 0

/-- Literal words, retaining the positions and both walls. -/
abbrev Word (a b : ℕ) :=
  {w : Pos a b → Letter // count one w = a ∧ count two w = b ∧ count wall w = 2}

instance wordFintype (a b : ℕ) : Fintype (Word a b) := inferInstance

/-- Push a word forward along a permutation of its sites. -/
def permute {a b : ℕ} (e : Equiv.Perm (Pos a b)) : Equiv.Perm (Word a b) where
  toFun w := ⟨fun p => w.1 (e.symm p), by
    have h (c : Letter) : count c (fun p => w.1 (e.symm p)) = count c w.1 :=
      e.symm.sum_comp (fun p => if w.1 p = c then 1 else 0)
    simpa only [h] using w.2⟩
  invFun w := ⟨fun p => w.1 (e p), by
    have h (c : Letter) : count c (fun p => w.1 (e p)) = count c w.1 :=
      Equiv.sum_comp e (fun p => if w.1 p = c then 1 else 0)
    simpa only [h] using w.2⟩
  left_inv w := by apply Subtype.ext; funext p; simp
  right_inv w := by apply Subtype.ext; funext p; simp

/-- Right translation: the letter at p comes from p−t. -/
def rotate {a b : ℕ} (t : Pos a b) : Equiv.Perm (Word a b) :=
  permute (Equiv.addRight t)

/-- Exchange the ordered bond's two sites. -/
def swapWord {a b : ℕ} (p : Pos a b) : Equiv.Perm (Word a b) :=
  permute (Equiv.swap p (p + 1))

/-- Input pairs for F1, F2 and F3, in that order. -/
def inputPair : Fin 3 → Letter × Letter := ![(wall, two), (one, wall), (two, one)]

/-- The oriented input test, before the swap. -/
def Allowed {a b : ℕ} (i : Fin 3) (w : Word a b) (p : Pos a b) : Prop :=
  w.1 p = (inputPair i).1 ∧ w.1 (p + 1) = (inputPair i).2

instance allowedDecidable {a b : ℕ} (i : Fin 3) (w : Word a b) (p : Pos a b) :
    Decidable (Allowed i w p) := inferInstanceAs (Decidable (_ ∧ _))

/-- Finite linear combinations of the literal words. -/
abbrev Space (K : Type*) [Zero K] (a b : ℕ) := Word a b →₀ K

/-- The delta basis vector. -/
noncomputable def delta (K : Type*) [Field K] {a b : ℕ} (w : Word a b) : Space K a b :=
  Finsupp.single w 1

/-- One local transition; disallowed input pairs are annihilated. -/
noncomputable def bond (K : Type*) [Field K] {a b : ℕ}
    (i : Fin 3) (p : Pos a b) (w : Word a b) : Space K a b :=
  if Allowed i w p then delta K (swapWord p w) else 0

/-- Sum over every bond, retaining repeated resulting words with their multiplicities. -/
noncomputable def F (K : Type*) [Field K] (a b : ℕ) (i : Fin 3) :
    Module.End K (Space K a b) :=
  Finsupp.linearCombination K (fun w => ∑ p, bond K i p w)

noncomputable def F1 (K : Type*) [Field K] (a b : ℕ) := F K a b 0
noncomputable def F2 (K : Type*) [Field K] (a b : ℕ) := F K a b 1
noncomputable def F3 (K : Type*) [Field K] (a b : ℕ) := F K a b 2

/-- The eclectic coupling operator. -/
noncomputable def T (K : Type*) [Field K] (a b : ℕ) (ξ : Fin 3 → K) :
    Module.End K (Space K a b) := ∑ i, ξ i • F K a b i

/-- Linear right translation by t sites. -/
noncomputable def translation (K : Type*) [Field K] {a b : ℕ} (t : Pos a b) :
    Module.End K (Space K a b) := Finsupp.lmapDomain K K (rotate t)

/-- The source's one-site right shift. -/
noncomputable def U (K : Type*) [Field K] (a b : ℕ) : Module.End K (Space K a b) :=
  translation K 1

end D5.S3.Quantum.SpinChains.TwoWallWords
