/- GID: D5/S3/StatisticalMechanics/CellularAutomata/KleinFourInvariant
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/KleinFourInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A structural merger invariant for binary Klein-four cellular automata. -/

/-
MIT License

Copyright (c) 2026 Edgar Alcalá-Arroyo, Alonso Castillo-Ramirez, Haobo Ma, Wenlin Zhang

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Public source: https://github.com/the-omega-institute/klein-four-lazy-ca-supplement
Version v1.1.0, commit fae47ad9dbbd4cbc1462a058dffe6ad4c2e416f1.
DOI: 10.5281/zenodo.23280244. Adapted structural proof; fixed counts excluded.
-/

import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.CellularAutomata.KleinFourInvariant

abbrev G := Bool × Bool

def gm (g h : G) : G := (xor g.1 h.1, xor g.2 h.2)
def e : G := (false, false)

theorem gm_comm : ∀ a b : G, gm a b = gm b a := by decide
theorem e_gm : ∀ a : G, gm e a = a := by decide

def character (s : Fin 3) (g : G) : Bool :=
  if s = 0 then g.1 else if s = 1 then g.2 else xor g.1 g.2

def shift (s : Fin 3) (b : Bool) : G :=
  if s = 1 then (false, b) else (b, false)


inductive X
  | c : Bool → X
  | p : Fin 3 → Bool → X
  | f : Bool → G → X
  deriving DecidableEq, Fintype

def act (g : G) : X → X
  | .c b => .c b
  | .p s b => .p s (xor b (character s g))
  | .f b h => .f b (gm h g)

theorem act_e : ∀ x, act e x = x := by decide
theorem act_act : ∀ g h x, act g (act h x) = act (gm g h) x := by decide

abbrev Bits := G → Bool

/-- The constants, three complementary pairs, and weight-one/weight-three orbits. -/
def encode : X → Bits
  | .c b => fun _ => b
  | .p s b => fun h => xor b (character s h)
  | .f b g => fun h => xor b (decide (h = g))

def bitNumber (x : Bits) : Nat :=
  (x (false, false)).toNat + 2 * (x (true, false)).toNat +
    4 * (x (false, true)).toNat + 8 * (x (true, true)).toNat

/-- Explicit inverse, so local-rule and lazy-map computations remain reducible. -/
def decode (x : Bits) : X :=
  match bitNumber x with
  | 0 => .c false
  | 15 => .c true
  | 1 => .f false (false, false)
  | 2 => .f false (true, false)
  | 4 => .f false (false, true)
  | 8 => .f false (true, true)
  | 14 => .f true (false, false)
  | 13 => .f true (true, false)
  | 11 => .f true (false, true)
  | 7 => .f true (true, true)
  | 10 => .p 0 false
  | 5 => .p 0 true
  | 12 => .p 1 false
  | 3 => .p 1 true
  | 6 => .p 2 false
  | _ => .p 2 true

theorem decode_encode : ∀ x, decode (encode x) = x := by decide
theorem encode_decode : ∀ x, encode (decode x) = x := by decide

def configurations : X ≃ Bits :=
  { toFun := encode, invFun := decode, left_inv := decode_encode, right_inv := encode_decode }

theorem encode_act : ∀ g x h, encode (act g x) h = encode x (gm h g) := by decide

def Equivariant (T : X → X) : Prop := ∀ g x, T (act g x) = act g (T x)

def equivariantSubmonoid : Submonoid (Function.End X) where
  carrier := {T | Equivariant T}
  one_mem' := by intro g x; rfl
  mul_mem' := by
    intro A B hA hB g x
    change A (B (act g x)) = act g (A (B x))
    rw [hB, hA]

abbrev CA := equivariantSubmonoid

instance : CoeFun CA (fun _ => X → X) := ⟨fun T => T.val⟩

@[ext] theorem CA.ext {A B : CA} (h : ∀ x, A x = B x) : A = B :=
  Subtype.ext (funext h)

theorem equiv (T : CA) (g : G) (x : X) : T (act g x) = act g (T x) := T.property g x

@[simp] theorem mul_apply (A B : CA) (x : X) : (A * B) x = A (B x) := rfl

/-- §2: every local rule gives a cellular automaton. -/
def ofRule (r : X → Bool) : CA :=
  ⟨fun x => decode (fun g => r (act g x)), by
    intro g x
    apply configurations.injective
    funext h
    simp only [configurations, Equiv.coe_fn_mk, encode_decode, encode_act]
    rw [act_act, gm_comm]⟩

/-- Definition 2.1: identity except at occurrences of one pattern on a
neighborhood containing the identity; there the binary central symbol flips. -/
def lazyMap (S : Finset G) (p : Bits) : CA :=
  ofRule (fun x => if ∀ h ∈ S, encode x h = p h then !(encode x e) else encode x e)

def ICA : Set CA := {T | Function.Bijective T}
def L : Set CA := {T | ∃ S p, e ∈ S ∧ T = lazyMap S p}
def M : Submonoid CA := Submonoid.closure (ICA ∪ L)

def freeOrbit : X → Option Bool
  | .f b _ => some b
  | _ => none

/-- Equation (2.3): the two free orbits have the same free image. -/
def Merges (T : X → X) : Prop :=
  ∃ b, freeOrbit (T (.f false e)) = some b ∧ freeOrbit (T (.f true e)) = some b

/-- Equation (3.2), Theorem 1.1: constants and one pair share a constant image. -/
def Witness (T : X → X) : Prop :=
  ∃ s b, T (.c false) = .c b ∧ T (.c true) = .c b ∧
    T (.p s false) = .c b ∧ T (.p s true) = .c b

def Criterion (T : X → X) : Prop := Merges T → Witness T

instance (T : X → X) : Decidable (Merges T) := inferInstanceAs (Decidable (∃ b, _))
instance (T : X → X) : Decidable (Witness T) := inferInstanceAs (Decidable (∃ s b, _))
instance (T : X → X) : Decidable (Criterion T) := inferInstanceAs (Decidable (_ → _))

abbrev Small := Bool × Bool

def smallRun (s : Fin 3) (d : Small) (b : Bool) : X :=
  if d.1 then .p s (xor d.2 b) else .c d.2

theorem smallRun_equiv : ∀ s d b g,
    smallRun s d (xor b (character s g)) = act g (smallRun s d b) := by decide

structure Lower where
  c : Bool → Bool
  p : Fin 3 → Small
  deriving DecidableEq, Fintype

abbrev Free := Bool → X

structure Table where
  lower : Lower
  free : Free
  deriving DecidableEq, Fintype

def Table.run (t : Table) : X → X
  | .c b => .c (t.lower.c b)
  | .p s b => smallRun s (t.lower.p s) b
  | .f b g => act g (t.free b)

def Table.ca (t : Table) : CA := ⟨t.run, by
  intro g x
  cases x with
  | c b => rfl
  | p s b => exact smallRun_equiv s (t.lower.p s) b g
  | f b h =>
    change act (gm h g) (t.free b) = act g (act h (t.free b))
    rw [act_act, gm_comm]⟩

theorem fixed_iff_constant : ∀ y : X, (∀ g, act g y = y) ↔ ∃ b, y = .c b := by decide

theorem fixed_character_iff : ∀ s y,
    (∀ g, character s g = false → act g y = y) ↔ ∃ d, y = smallRun s d false := by decide

theorem constant_image (T : CA) (b : Bool) : ∃ a, T (.c b) = .c a := by
  apply (fixed_iff_constant _).mp
  intro g
  symm
  exact equiv T g (.c b)

theorem pair_image (T : CA) (s : Fin 3) : ∃ d, T (.p s false) = smallRun s d false := by
  apply (fixed_character_iff _ _).mp
  intro g hg
  rw [← equiv]
  simp [act, hg]

def constantValue : X → Bool
  | .c b => b
  | _ => false

def pairValue : X → Small
  | .c b => (false, b)
  | .p _ b => (true, b)
  | _ => (false, false)

def tableOf (T : CA) : Table :=
  { lower := { c := fun b => constantValue (T (.c b)),
               p := fun s => pairValue (T (.p s false)) },
    free := fun b => T (.f b e) }

theorem pair_rep : ∀ s b, act (shift s b) (.p s false) = .p s b := by decide
theorem free_rep : ∀ b g, act g (.f b e) = .f b g := by decide
theorem smallRun_shift : ∀ s d b,
    act (shift s b) (smallRun s d false) = smallRun s d b := by decide
theorem smallRun_pairValue : ∀ s d, pairValue (smallRun s d false) = d := by decide

theorem ca_tableOf (T : CA) : (tableOf T).ca = T := by
  ext x
  cases x with
  | c b =>
    obtain ⟨a, ha⟩ := constant_image T b
    change X.c (constantValue (T (.c b))) = T (.c b)
    rw [ha]; rfl
  | p s b =>
    obtain ⟨d, hd⟩ := pair_image T s
    change smallRun s (pairValue (T (.p s false))) b = T (.p s b)
    rw [hd, smallRun_pairValue]
    rw [← pair_rep s b, equiv, hd, smallRun_shift]
  | f b g =>
    change act g (T (.f b e)) = T (.f b g)
    rw [← free_rep b g, equiv]

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem freeOrbit_act : ∀ g x, freeOrbit (act g x) = freeOrbit x := by decide

theorem lower_no_free (T : CA) (x : X) (hx : freeOrbit x = none) : freeOrbit (T x) = none := by
  rw [← ca_tableOf T]
  cases x with
  | c b => rfl
  | p s b =>
    change freeOrbit (smallRun s ((tableOf T).lower.p s) b) = none
    exact (by decide : ∀ s d b, freeOrbit (smallRun s d b) = none) s _ b
  | f b g => simp [freeOrbit] at hx

theorem image_free_source (T : CA) (x : X) (b : Bool)
    (h : freeOrbit (T x) = some b) : ∃ j g, x = .f j g := by
  cases x with
  | c a => have := lower_no_free T (.c a) rfl; rw [h] at this; contradiction
  | p s a => have := lower_no_free T (.p s a) rfl; rw [h] at this; contradiction
  | f j g => exact ⟨j, g, rfl⟩

theorem same_free_translate : ∀ x y b,
    freeOrbit x = some b → freeOrbit y = some b → ∃ g, act g x = y := by decide

/-- Units do not merge free orbits, as used in Lemma 3.2. -/
theorem invertible_not_merges (T : CA) (hT : T ∈ ICA) : ¬ Merges T := by
  rintro ⟨b, h0, h1⟩
  obtain ⟨g, hg⟩ := same_free_translate _ _ b h0 h1
  have h := hT.1 ((equiv T g (.f false e)).trans hg)
  have : ∀ g, act g (.f false e) ≠ X.f true e := by decide
  exact this g h

theorem invertible_criterion (T : CA) (hT : T ∈ ICA) : Criterion T :=
  fun h => False.elim (invertible_not_merges T hT h)

/-- Lemma 3.1: check the finite neighborhood/pattern family, not all automata. -/
theorem lazy_criterion_check : ∀ (S : Finset G) (p : Bits),
    e ∈ S → Criterion (lazyMap S p) := by
  dsimp only [Criterion, Merges, Witness, lazyMap, ofRule]
  decide

theorem witness_postcompose (A B : CA) (hB : Witness B) : Witness (A * B) := by
  obtain ⟨s, b, h0, h1, hp0, hp1⟩ := hB
  obtain ⟨a, ha⟩ := constant_image A b
  exact ⟨s, a, by simp [h0, ha], by simp [h1, ha], by simp [hp0, ha], by simp [hp1, ha]⟩

theorem witness_precompose (A B : CA) (hA : Witness A) : Witness (A * B) := by
  obtain ⟨s, b, h0, h1, hp0, hp1⟩ := hA
  have hc : ∀ a, A (.c a) = .c b := by intro a; cases a <;> assumption
  have hp : ∀ a, A (.p s a) = .c b := by intro a; cases a <;> assumption
  have eval : ∀ d a, A (smallRun s d a) = .c b := by
    intro d a
    unfold smallRun
    split
    · exact hp _
    · exact hc _
  obtain ⟨a0, ha0⟩ := constant_image B false
  obtain ⟨a1, ha1⟩ := constant_image B true
  obtain ⟨d, hd⟩ := pair_image B s
  refine ⟨s, b, ?_, ?_, ?_, ?_⟩
  · simp [ha0, hc]
  · simp [ha1, hc]
  · simp [hd, eval]
  · rw [mul_apply, ← pair_rep s true, equiv, hd, smallRun_shift, eval]

/-- Structural composition argument from Lemma 3.2. -/
theorem criterion_mul (A B : CA) (hA : Criterion A) (hB : Criterion B) : Criterion (A * B) := by
  rintro ⟨b, h0, h1⟩
  simp only [mul_apply] at h0 h1
  obtain ⟨j0, g0, hj0⟩ := image_free_source A (B (.f false e)) b h0
  obtain ⟨j1, g1, hj1⟩ := image_free_source A (B (.f true e)) b h1
  by_cases h : j0 = j1
  · apply witness_postcompose
    apply hB
    exact ⟨j0, by simp [hj0, freeOrbit], by simp [hj1, h, freeOrbit]⟩
  · apply witness_precompose
    apply hA
    have h0' : freeOrbit (A (.f j0 e)) = some b := by
      rw [hj0, ← free_rep j0 g0, equiv, freeOrbit_act] at h0
      exact h0
    have h1' : freeOrbit (A (.f j1 e)) = some b := by
      rw [hj1, ← free_rep j1 g1, equiv, freeOrbit_act] at h1
      exact h1
    cases j0 <;> cases j1 <;> simp_all [Merges]

def criterionSubmonoid : Submonoid CA where
  carrier := {T | Criterion T}
  one_mem' := by decide
  mul_mem' := fun hA hB => criterion_mul _ _ hA hB

theorem membership_implies_criterion (T : CA) (hT : T ∈ M) : Criterion T := by
  have hle : M ≤ criterionSubmonoid := Submonoid.closure_le.mpr (by
    intro A hA
    rcases hA with hA | ⟨S, p, hS, rfl⟩
    · exact invertible_criterion A hA
    · exact lazy_criterion_check S p hS)
  exact hle hT


end D5.S3.StatisticalMechanics.CellularAutomata.KleinFourInvariant
