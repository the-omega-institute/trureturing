/- GID: D5/S3/Arith/Congruence/ConditionalComparison/Cylinders
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Prefix cylinders. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/Cylinders.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic

/-!
# Prefix cylinders

This is the finite CRT-normal form of a covering system.  A block is a finite
word, a cylinder fixes an initial segment in each block, and distinct moduli
become injectivity of depth vectors.
-/

namespace Erdos7

/-- A word of length `a` over an alphabet of size `q`. -/
abbrev Word (q a : ℕ) := Fin a → Fin q

/-- A prefix of length `d` over an alphabet of size `q`. -/
abbrev Prefix (q d : ℕ) := Fin d → Fin q

/-- A word begins with a prescribed prefix. -/
def HasPrefix {q a d : ℕ} (w : Word q a) (u : Prefix q d) (hd : d ≤ a) : Prop :=
  ∀ i : Fin d, w ⟨i, Nat.lt_of_lt_of_le i.isLt hd⟩ = u i

instance instDecidableHasPrefix {q a d : ℕ} (w : Word q a)
    (u : Prefix q d) (hd : d ≤ a) : Decidable (HasPrefix w u hd) := by
  unfold HasPrefix
  infer_instance

/-- Prefix cylinder data over finitely many blocks. -/
structure Cylinder (r : ℕ) (arity height : Fin r → ℕ) where
  depth : (j : Fin r) → Fin (height j + 1)
  digits : (j : Fin r) → Prefix (arity j) (depth j : ℕ)

namespace Cylinder

variable {r : ℕ} {arity height : Fin r → ℕ}

/-- The ambient product of block words. -/
abbrev Point (r : ℕ) (arity height : Fin r → ℕ) :=
  (j : Fin r) → Word (arity j) (height j)

/-- Membership in a prefix cylinder. -/
def Contains (C : Cylinder r arity height) (x : Point r arity height) : Prop :=
  ∀ j, HasPrefix (x j) (C.digits j) (Nat.le_of_lt_succ (C.depth j).isLt)

/-- The depth vector is nonzero. -/
def Nontrivial (C : Cylinder r arity height) : Prop :=
  ∃ j, (C.depth j : ℕ) ≠ 0

/-- The set of blocks in which a cylinder has positive depth. -/
def support (C : Cylinder r arity height) : Finset (Fin r) :=
  Finset.univ.filter fun j ↦ (C.depth j : ℕ) ≠ 0

/-- A pure cylinder fixes digits in exactly one block. -/
def Pure (C : Cylinder r arity height) : Prop := C.support.card = 1

@[simp] theorem mem_support (C : Cylinder r arity height) (j : Fin r) :
    j ∈ C.support ↔ (C.depth j : ℕ) ≠ 0 := by
  simp [support]

/-- A pure cylinder with positive depth in block `j` is supported exactly
there. -/
theorem support_eq_singleton_of_pure_of_depth_ne_zero
    (C : Cylinder r arity height) {j : Fin r} (hPure : C.Pure)
    (hj : (C.depth j : ℕ) ≠ 0) : C.support = {j} := by
  unfold Pure at hPure
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hPure
  have hjmem : j ∈ C.support := (C.mem_support j).2 hj
  have hjb : j = b := by simpa [hb] using hjmem
  simpa [hjb] using hb

/-- Every other block of a pure cylinder has depth zero. -/
theorem depth_eq_zero_of_pure_of_ne
    (C : Cylinder r arity height) {j b : Fin r} (hPure : C.Pure)
    (hj : (C.depth j : ℕ) ≠ 0) (hb : b ≠ j) :
    (C.depth b : ℕ) = 0 := by
  have hs := C.support_eq_singleton_of_pure_of_depth_ne_zero hPure hj
  have hbnot : b ∉ C.support := by simp [hs, hb]
  simpa [C.mem_support b] using hbnot

/-- Two pure cylinders having the same positive depth in one block have the
same full depth vector. -/
theorem depth_eq_of_pure_of_same_positive
    (C D : Cylinder r arity height) {j : Fin r}
    (hCPure : C.Pure) (hDPure : D.Pure)
    (hj : (C.depth j : ℕ) ≠ 0) (hdepth : C.depth j = D.depth j) :
    C.depth = D.depth := by
  funext b
  by_cases hb : b = j
  · subst b
    exact hdepth
  · apply Fin.ext
    rw [C.depth_eq_zero_of_pure_of_ne hCPure hj hb]
    have hjD : (D.depth j : ℕ) ≠ 0 := by simpa [← hdepth] using hj
    rw [D.depth_eq_zero_of_pure_of_ne hDPure hjD hb]

/-- A family covers the entire finite product. -/
def Covers {κ : Type*} (C : κ → Cylinder r arity height) : Prop :=
  ∀ x : Point r arity height, ∃ k, (C k).Contains x

/-- Full-vector uniqueness, the CRT translation of distinct moduli. -/
def DepthInjective {κ : Type*} (C : κ → Cylinder r arity height) : Prop :=
  Function.Injective fun k ↦ (C k).depth

/-- Transport a cylinder along an equality of ambient heights. -/
def castHeight {height' : Fin r → ℕ} (h : height = height')
    (C : Cylinder r arity height) : Cylinder r arity height' :=
  h ▸ C

/-- Transport an ambient point along an equality of heights. -/
def castPoint {height' : Fin r → ℕ} (h : height = height')
    (x : Point r arity height) : Point r arity height' :=
  h ▸ x

@[simp] theorem castHeight_depth {height' : Fin r → ℕ}
    (h : height = height') (C : Cylinder r arity height) (j : Fin r) :
    (castHeight h C).depth j = h ▸ C.depth j := by
  subst height'
  rfl

theorem castHeight_nontrivial {height' : Fin r → ℕ}
    (h : height = height') (C : Cylinder r arity height) :
    (castHeight h C).Nontrivial ↔ C.Nontrivial := by
  subst height'
  rfl

theorem castHeight_contains {height' : Fin r → ℕ}
    (h : height = height') (C : Cylinder r arity height)
    (x : Point r arity height) :
    (castHeight h C).Contains (castPoint h x) ↔ C.Contains x := by
  subst height'
  rfl

theorem covers_castHeight {height' : Fin r → ℕ} {L : ℕ}
    (h : height = height') (C : Fin L → Cylinder r arity height) :
    Covers (fun k ↦ castHeight h (C k)) ↔ Covers C := by
  subst height'
  rfl

theorem depthInjective_castHeight {height' : Fin r → ℕ} {L : ℕ}
    (h : height = height') (C : Fin L → Cylinder r arity height) :
    DepthInjective (fun k ↦ castHeight h (C k)) ↔ DepthInjective C := by
  subst height'
  rfl

/-- In a depth-injective family, a pure cylinder at a prescribed positive
block-depth is unique. -/
theorem eq_of_pure_of_same_positive {κ : Type*}
    (C : κ → Cylinder r arity height) (hInj : DepthInjective C)
    {k l : κ} {j : Fin r} (hkPure : (C k).Pure)
    (hlPure : (C l).Pure) (hj : ((C k).depth j : ℕ) ≠ 0)
    (hdepth : (C k).depth j = (C l).depth j) : k = l := by
  apply hInj
  exact depth_eq_of_pure_of_same_positive (C k) (C l)
    hkPure hlPure hj hdepth

/-- Embed a predecessor coordinate `Fin j` into the full block set. -/
def predecessorIndex (j : Fin r) (i : Fin (j : ℕ)) : Fin r :=
  ⟨i, Nat.lt_of_lt_of_le i.isLt (Nat.le_of_lt j.isLt)⟩

/--
Ending-only uniqueness.  If every label in `S` has the same positive current
depth, zero future depths, bounded predecessor depths, and a nonzero
predecessor vector, then there are at most
`∏ᵢ (Dᵢ+1) - 1` labels.

The proof deliberately reconstructs the *full* depth vector before invoking
injectivity; this is the formal guard against the invalid projected-prefix
count that appeared in the rank-eight attempt.
-/
theorem ending_count_le_box_sub_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (C : κ → Cylinder r arity height) (hInj : DepthInjective C)
    (j : Fin r) (e : ℕ) (S : Finset κ) (D : Fin (j : ℕ) → ℕ)
    (hcurrent : ∀ k ∈ S, ((C k).depth j : ℕ) = e)
    (hfuture : ∀ k ∈ S, ∀ i : Fin r, (j : ℕ) < i →
      ((C k).depth i : ℕ) = 0)
    (hbound : ∀ k ∈ S, ∀ i : Fin (j : ℕ),
      ((C k).depth (predecessorIndex j i) : ℕ) ≤ D i)
    (hpred : ∀ k ∈ S, ∃ i : Fin (j : ℕ),
      ((C k).depth (predecessorIndex j i) : ℕ) ≠ 0) :
    S.card ≤ (∏ i, (D i + 1)) - 1 := by
  classical
  let Box := (i : Fin (j : ℕ)) → Fin (D i + 1)
  let encode : {k // k ∈ S} → Box := fun k i ↦
    ⟨((C k.1).depth (predecessorIndex j i) : ℕ),
      Nat.lt_succ_of_le (hbound k.1 k.2 i)⟩
  let zeroBox : Box := fun i ↦ ⟨0, Nat.zero_lt_succ (D i)⟩
  have hencode : Function.Injective encode := by
    intro k l hkl
    apply Subtype.ext
    apply hInj
    funext i
    apply Fin.ext
    by_cases hij : (i : ℕ) < (j : ℕ)
    · let i' : Fin (j : ℕ) := ⟨i, hij⟩
      have hv := congrFun hkl i'
      have hvval := congrArg Fin.val hv
      simpa [encode, i', predecessorIndex] using hvval
    · by_cases hji : (j : ℕ) < (i : ℕ)
      · rw [hfuture k.1 k.2 i hji, hfuture l.1 l.2 i hji]
      · have hijEq : i = j := Fin.ext (by omega)
        subst i
        exact (hcurrent k.1 k.2).trans (hcurrent l.1 l.2).symm
  have hnonzero : ∀ k : {k // k ∈ S}, encode k ≠ zeroBox := by
    intro k hk
    obtain ⟨i, hi⟩ := hpred k.1 k.2
    apply hi
    have hv := congrFun hk i
    exact congrArg Fin.val hv
  let enlarged : Sum {k // k ∈ S} Unit → Box
    | Sum.inl k => encode k
    | Sum.inr _ => zeroBox
  have henlarged : Function.Injective enlarged := by
    intro x y hxy
    cases x with
    | inl k =>
        cases y with
        | inl l => exact congrArg Sum.inl (hencode hxy)
        | inr u => exact (hnonzero k hxy).elim
    | inr u =>
        cases y with
        | inl l => exact (hnonzero l hxy.symm).elim
        | inr v => simp
  have hcard := Fintype.card_le_of_injective enlarged henlarged
  have hbox : Fintype.card Box = ∏ i, (D i + 1) := by
    simp [Box]
  have hsum : Fintype.card (Sum {k // k ∈ S} Unit) = S.card + 1 := by
    simp
  rw [hbox, hsum] at hcard
  omega

end Cylinder
end Erdos7
