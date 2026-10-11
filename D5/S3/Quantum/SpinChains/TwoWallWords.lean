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
import Mathlib.Tactic.Abel

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
    Module.End K (Space K a b) :=
  ξ 0 • F1 K a b + ξ 1 • F2 K a b + ξ 2 • F3 K a b

/-- Linear right translation by t sites. -/
noncomputable def translation (K : Type*) [Field K] {a b : ℕ} (t : Pos a b) :
    Module.End K (Space K a b) := Finsupp.lmapDomain K K (rotate t)

/-- The source's one-site right shift. -/
noncomputable def U (K : Type*) [Field K] (a b : ℕ) : Module.End K (Space K a b) :=
  translation K 1

/-- Count preservation, delta action, periodicity and translation symmetry of the bond sums. -/
theorem cyclic_action (K : Type*) [Field K] (a b : ℕ) :
    (∀ (c : Letter) (p : Pos a b) (w : Pos a b → Letter),
      count c (fun q => w (Equiv.swap p (p + 1) q)) = count c w) ∧
    (∀ (t : Pos a b) (w : Word a b),
      translation K t (delta K w) = delta K (rotate t w)) ∧
    (∀ (i : Fin 3) (w : Word a b),
      F K a b i (delta K w) = ∑ p, bond K i p w) ∧
    U K a b ^ (a + b + 2) = 1 ∧
    (∀ i : Fin 3, Commute (U K a b) (F K a b i)) ∧
    (∀ ξ : Fin 3 → K, Commute (U K a b) (T K a b ξ)) := by
  classical
  have hcount (c : Letter) (p : Pos a b) (w : Pos a b → Letter) :
      count c (fun q => w (Equiv.swap p (p + 1) q)) = count c w := by
    exact Equiv.sum_comp (Equiv.swap p (p + 1))
      (fun q => if w q = c then 1 else 0)
  have ht (t : Pos a b) (w : Word a b) (z : K) :
      translation K t (Finsupp.single w z) = Finsupp.single (rotate t w) z := by
    simp [translation]
  have hf (i : Fin 3) (w : Word a b) (z : K) :
      F K a b i (Finsupp.single w z) = z • ∑ p, bond K i p w := by
    simp [F]
  have hr (t s : Pos a b) (w : Word a b) :
      rotate t (rotate s w) = rotate (t + s) w := by
    apply Subtype.ext
    funext p
    change w.1 ((p + -t) + -s) = w.1 (p + -(t + s))
    abel_nf
  have hz (w : Word a b) : rotate (0 : Pos a b) w = w := by
    apply Subtype.ext
    funext p
    change w.1 (p + -0) = w.1 p
    simp
  have hmul (t s : Pos a b) :
      translation K t * translation K s = translation K (t + s) := by
    apply Finsupp.lhom_ext
    intro w z
    simp only [Module.End.mul_apply, ht, hr]
  have hzero : translation K (0 : Pos a b) = 1 := by
    apply Finsupp.lhom_ext
    intro w z
    simp [ht, hz]
  have hpow (n : ℕ) : U K a b ^ n = translation K (n : Pos a b) := by
    induction n with
    | zero => simpa using hzero.symm
    | succ n ih => rw [pow_succ, ih]; simpa [U] using hmul (n : Pos a b) 1
  have hswap (t p : Pos a b) (w : Word a b) :
      rotate t (swapWord p w) = swapWord (p + t) (rotate t w) := by
    apply Subtype.ext
    funext q
    change w.1 (Equiv.swap p (p + 1) (q + -t)) =
      w.1 (Equiv.swap (p + t) (p + t + 1) q + -t)
    have h := (Equiv.addRight (-t)).injective.swap_apply (p + t) (p + t + 1) q
    simp only [Equiv.coe_addRight, ← sub_eq_add_neg] at h
    have hp : p + t + 1 - t = p + 1 := by abel_nf
    simpa only [← sub_eq_add_neg, add_sub_cancel_right, hp] using congrArg w.1 h
  have ha (i : Fin 3) (t p : Pos a b) (w : Word a b) :
      Allowed i (rotate t w) (p + t) ↔ Allowed i w p := by
    change (w.1 (p + t + -t) = (inputPair i).1 ∧
      w.1 (p + t + 1 + -t) = (inputPair i).2) ↔ Allowed i w p
    have hp : p + t + 1 + -t = p + 1 := by abel_nf
    simp only [add_neg_cancel_right, hp, Allowed]
  have hb (i : Fin 3) (t p : Pos a b) (w : Word a b) :
      translation K t (bond K i p w) = bond K i (p + t) (rotate t w) := by
    have hat : Allowed i (rotate t w) (p + t) ↔ Allowed i w p := ha i t p w
    by_cases h : Allowed i w p
    · simp [bond, h, hat.mpr h, delta, ht, hswap]
    · have hn : ¬ Allowed i (rotate t w) (p + t) := fun h' => h (hat.mp h')
      simp [bond, h, hn]
  have hc (i : Fin 3) (t : Pos a b) :
      Commute (translation K t) (F K a b i) := by
    change translation K t * F K a b i = F K a b i * translation K t
    apply Finsupp.lhom_ext
    intro w z
    simp only [Module.End.mul_apply, hf, ht, map_smul, map_sum, hb]
    exact congrArg (fun v => z • v)
      (Equiv.sum_comp (Equiv.addRight t) (fun p => bond K i p (rotate t w)))
  refine ⟨hcount, ?_, ?_, ?_, (fun i => hc i 1), ?_⟩
  · intro t w
    exact ht t w 1
  · intro i w
    simpa [delta] using hf i w 1
  · rw [hpow, ZMod.natCast_self, hzero]
  · intro ξ
    change U K a b * T K a b ξ = T K a b ξ * U K a b
    simp only [T, F1, F2, F3, U, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    rw [(hc 0 1).eq, (hc 1 1).eq, (hc 2 1).eq]

end D5.S3.Quantum.SpinChains.TwoWallWords
