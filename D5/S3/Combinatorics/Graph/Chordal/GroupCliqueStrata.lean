/- GID: D5/S3/Combinatorics/Graph/Chordal/GroupCliqueStrata
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Group gain bounds for chordal graphs at clique numbers four and five. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.EliminationForest
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Fin.VecNotation

compile_only_with_mathlib

/-! # Noncommutative clique-stratum certificates

All powers below are pointwise set powers. Triangle hypotheses concern ordered
triangle holonomies, with the displayed multiplication order retained.
-/

open scoped Pointwise

namespace SimpleGraph.GroupCliqueStrata

universe u v
variable {H : Type v} [Group H] {U : Set H}

/-- The algebraic hypotheses on the allowed triangle holonomies. -/
structure NormalSet (U : Set H) : Prop where
  one_mem : 1 ∈ U
  inv_mem : ∀ ⦃x⦄, x ∈ U → x⁻¹ ∈ U
  conj_mem : ∀ a, ∀ ⦃x⦄, x ∈ U → a * x * a⁻¹ ∈ U

namespace NormalSet

theorem mul_two (_hU : NormalSet U) {a b : H} (ha : a ∈ U) (hb : b ∈ U) :
    a * b ∈ U ^ 2 := by
  simpa only [pow_two] using Set.mul_mem_mul ha hb

theorem mul_three (hU : NormalSet U) {a b c : H}
    (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U) : a * b * c ∈ U ^ 3 := by
  simpa only [pow_succ, pow_two, pow_one] using
    Set.mul_mem_mul (hU.mul_two ha hb) hc

theorem mem_two (hU : NormalSet U) {a : H} (ha : a ∈ U) : a ∈ U ^ 2 := by
  simpa using hU.mul_two ha hU.one_mem

theorem two_three (hU : NormalSet U) {a : H} (ha : a ∈ U ^ 2) : a ∈ U ^ 3 := by
  simpa only [pow_succ, pow_one, mul_one] using Set.mul_mem_mul ha hU.one_mem

theorem inv_two (hU : NormalSet U) {a : H} (ha : a ∈ U ^ 2) : a⁻¹ ∈ U ^ 2 := by
  rw [pow_two, Set.mem_mul] at ha
  obtain ⟨x, hx, y, hy, rfl⟩ := ha
  simpa only [mul_inv_rev] using hU.mul_two (hU.inv_mem hy) (hU.inv_mem hx)

theorem inv_three (hU : NormalSet U) {a : H} (ha : a ∈ U ^ 3) : a⁻¹ ∈ U ^ 3 := by
  rw [pow_succ, Set.mem_mul] at ha
  obtain ⟨x, hx, y, hy, rfl⟩ := ha
  rw [pow_two, Set.mem_mul] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  simpa only [mul_inv_rev, mul_assoc] using
    hU.mul_three (hU.inv_mem hy) (hU.inv_mem hb) (hU.inv_mem ha)

theorem one_two_mul (_hU : NormalSet U) {a b : H} (ha : a ∈ U) (hb : b ∈ U ^ 2) :
    a * b ∈ U ^ 3 := by
  simpa only [pow_succ', pow_one] using Set.mul_mem_mul ha hb

theorem two_one_mul (_hU : NormalSet U) {a b : H} (ha : a ∈ U ^ 2) (hb : b ∈ U) :
    a * b ∈ U ^ 3 := by
  simpa only [pow_succ, pow_one] using Set.mul_mem_mul ha hb

theorem conj_two (hU : NormalSet U) (a : H) {x : H} (hx : x ∈ U ^ 2) :
    a * x * a⁻¹ ∈ U ^ 2 := by
  rw [pow_two, Set.mem_mul] at hx
  obtain ⟨b, hb, c, hc, rfl⟩ := hx
  convert hU.mul_two (hU.conj_mem a hb) (hU.conj_mem a hc) using 1; group

end NormalSet

/-- Residuals in the convention used in the two source proofs. -/
def residual {V : Type u} (g : V → V → H) (φ : V → H) (a b : V) : H :=
  φ a * g a b * (φ b)⁻¹

theorem residual_reverse {V : Type u} {g : V → V → H} (φ : V → H) {a b : V}
    (hab : g b a = (g a b)⁻¹) :
    residual g φ b a = (residual g φ a b)⁻¹ := by
  simp only [residual, hab, mul_inv_rev, inv_inv, mul_assoc]

theorem residual_triangle {V : Type u} {g : V → V → H} (φ : V → H) {a b c : V}
    (hU : NormalSet U) (ht : g a b * g b c * (g a c)⁻¹ ∈ U) :
    residual g φ a b * residual g φ b c * (residual g φ a c)⁻¹ ∈ U := by
  convert hU.conj_mem (φ a) ht using 1; simp [residual, mul_assoc]

/-- An admissible ordered triangle. -/
def GoodTriangle {I : Type*} (U : Set H) (e : I → I → H) (a b c : I) : Prop :=
  e a b ∈ U ∧ (e a b)⁻¹ * e a c ∈ U

/-- The closed ordered-four-clique prefix invariant, with budgets `(1,2,1)`. -/
def GoodFour {I : Type*} (U : Set H) (e : I → I → H) (a b c d : I) : Prop :=
  e a b ∈ U ∧ e a b * e b c ∈ U ^ 2 ∧ e a b * e b c * e c d ∈ U

section TriangleExtension

variable {I : Type*} {e : I → I → H} {a b c v : I}

/-- The three-neighbor extension, including all three child-triangle certificates.
The closing equation is realized by `triangle_extension_gauge` below. -/
theorem triangle_extension (hU : NormalSet U)
    (hr : ∀ i j, e j i = (e i j)⁻¹)
    (ht : ∀ i j k, e i j * e j k * (e i k)⁻¹ ∈ U)
    (hgood : GoodTriangle U e a b c)
    (hclose : e c v = ((e a b)⁻¹ * e a c)⁻¹) :
    e a v ∈ U ^ 2 ∧ e b v ∈ U ^ 2 ∧ e c v ∈ U ^ 2 ∧
      GoodTriangle U e a b v ∧ GoodTriangle U e c v a ∧ GoodTriangle U e c v b := by
  let X := e a b
  let C := X⁻¹ * e a c
  let p := e a b * e b v * (e a v)⁻¹
  let q := e a c * e c v * (e a v)⁻¹
  have hX : X ∈ U := hgood.1
  have hC : C ∈ U := hgood.2
  have hp : p ∈ U := ht a b v
  have hq : q ∈ U := ht a c v
  have hav : e a v = q⁻¹ * X := by dsimp [q, X]; rw [hclose]; group
  have hbv : e b v = X⁻¹ * p * q⁻¹ * X := by
    dsimp [p, q, X]; rw [hclose]; group
  have hcv : e c v ∈ U := by rw [hclose]; exact hU.inv_mem hC
  have hD : e b c * C⁻¹ ∈ U := by
    convert hU.conj_mem X⁻¹ (ht a b c) using 1; dsimp [X, C]; group
  refine ⟨?_, ?_, hU.mem_two hcv, ⟨hX, ?_⟩, ⟨hcv, ?_⟩, ⟨hcv, ?_⟩⟩
  · rw [hav]; exact hU.mul_two (hU.inv_mem hq) hX
  · rw [hbv]
    convert hU.conj_two X⁻¹ (hU.mul_two hp (hU.inv_mem hq)) using 1; group
  · rw [hav]
    simpa only [mul_assoc, inv_inv] using hU.conj_mem X⁻¹ (hU.inv_mem hq)
  · rw [hclose, hr a c]
    convert hU.inv_mem hX using 1; dsimp [C, X]; group
  · rw [hclose, hr b c]
    convert hU.inv_mem hD using 1; dsimp [C, X]; group

/-- The actual gauge choice giving the closing equation in `triangle_extension`. -/
theorem triangle_extension_gauge {V : Type u} (g : V → V → H) (φ : V → H)
    {a b c v : V} (hba : g b a = (g a b)⁻¹)
    (hv : φ v = φ b * g b a * g a c * g c v) :
    residual g φ c v =
      ((residual g φ a b)⁻¹ * residual g φ a c)⁻¹ := by
  simp only [residual, hv, hba]
  group

/-- The two-neighbor extension splits an existing two-factor edge certificate.
Its new triangle is admissible in the order `(a,v,b)`. -/
theorem two_neighbor_extension (hU : NormalSet U)
    (ht : e a b * e b v * (e a v)⁻¹ ∈ U)
    {A B : H} (hA : A ∈ U) (hB : B ∈ U)
    (hab : e a b = A * B) (hav : e a v = A) :
    e a v ∈ U ^ 2 ∧ e b v ∈ U ^ 2 ∧ GoodTriangle U e a v b := by
  have hbv : e b v = B⁻¹ * (A⁻¹ * (e a b * e b v * (e a v)⁻¹) * A) := by
    rw [hab, hav]; group
  refine ⟨hav ▸ hU.mem_two hA, ?_, ?_⟩
  · rw [hbv]
    exact hU.mul_two (hU.inv_mem hB)
      (by simpa only [inv_inv] using hU.conj_mem A⁻¹ ht)
  · constructor
    · simpa only [hav] using hA
    · simpa only [hav, hab, inv_mul_cancel_left] using hB

end TriangleExtension

section FourExtension

variable {I : Type*} {e : I → I → H} {a b c d v : I}

/-- Every edge of an ordered four-clique with prefix budgets `(1,2,1)`
has a three-factor certificate. -/
theorem four_edges (hU : NormalSet U)
    (ht : ∀ i j k, e i j * e j k * (e i k)⁻¹ ∈ U)
    (hg : GoodFour U e a b c d) :
    e a b ∈ U ^ 3 ∧ e b c ∈ U ^ 3 ∧ e c d ∈ U ^ 3 ∧
      e a c ∈ U ^ 3 ∧ e b d ∈ U ^ 3 ∧ e a d ∈ U ^ 3 := by
  obtain ⟨hA, hQ, hP⟩ := hg
  have hbc : e b c = (e a b)⁻¹ * (e a b * e b c) := by group
  have hcd : e c d = (e a b * e b c)⁻¹ * (e a b * e b c * e c d) := by group
  have hac : e a c = (e a b * e b c * (e a c)⁻¹)⁻¹ * (e a b * e b c) := by group
  have hbd : e b d = (e b c * e c d * (e b d)⁻¹)⁻¹ *
      (e a b)⁻¹ * (e a b * e b c * e c d) := by group
  have had : e a d = (e a c * e c d * (e a d)⁻¹)⁻¹ *
      (e a b * e b c * (e a c)⁻¹)⁻¹ * (e a b * e b c * e c d) := by group
  refine ⟨hU.two_three (hU.mem_two hA), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbc]; exact hU.one_two_mul (hU.inv_mem hA) hQ
  · rw [hcd]; exact hU.two_one_mul (hU.inv_two hQ) hP
  · rw [hac]; exact hU.one_two_mul (hU.inv_mem (ht a b c)) hQ
  · rw [hbd]; exact hU.mul_three (hU.inv_mem (ht b c d)) (hU.inv_mem hA) hP
  · rw [had]; exact hU.mul_three (hU.inv_mem (ht a c d))
      (hU.inv_mem (ht a b c)) hP

/-- The four-neighbor extension and its complete child-face closure table.
No compatibility of different faces' stored orders is assumed. -/
theorem four_extension (hU : NormalSet U)
    (hr : ∀ i j, e j i = (e i j)⁻¹)
    (ht : ∀ i j k, e i j * e j k * (e i k)⁻¹ ∈ U)
    (hg : GoodFour U e a b c d)
    (hclose : e d v = (e a b * e b c * e c d)⁻¹) :
    (e a v ∈ U ^ 3 ∧ e b v ∈ U ^ 3 ∧ e c v ∈ U ^ 3 ∧ e d v ∈ U ^ 3) ∧
      GoodFour U e v d c b ∧ GoodFour U e v d c a ∧
      GoodFour U e a b d v ∧ GoodFour U e a b c v := by
  let A := e a b
  let Q := e a b * e b c
  let P := e a b * e b c * e c d
  let t₁ := e a b * e b c * (e a c)⁻¹
  let t₂ := e b c * e c d * (e b d)⁻¹
  let t₃ := e a c * e c d * (e a d)⁻¹
  let s₁ := e c d * e d v * (e c v)⁻¹
  let s₂ := e b d * e d v * (e b v)⁻¹
  let s₃ := e a d * e d v * (e a v)⁻¹
  obtain ⟨hA, hQ, hP⟩ := hg
  have ht₁ : t₁ ∈ U := ht a b c
  have ht₂ : t₂ ∈ U := ht b c d
  have ht₃ : t₃ ∈ U := ht a c d
  have hs₁ : s₁ ∈ U := ht c d v
  have hs₂ : s₂ ∈ U := ht b d v
  have hs₃ : s₃ ∈ U := ht a d v
  have hcv : e c v = s₁⁻¹ * Q⁻¹ := by dsimp [s₁, Q]; rw [hclose]; group
  have hbv : e b v = s₂⁻¹ * t₂⁻¹ * A⁻¹ := by
    dsimp [s₂, t₂, A]; rw [hclose]; group
  have hav : e a v = s₃⁻¹ * t₃⁻¹ * t₁⁻¹ := by
    dsimp [s₃, t₃, t₁]; rw [hclose]; group
  have hvd : e v d = P := by rw [hr d v, hclose, inv_inv]
  have hvdc : e v d * e d c = Q := by rw [hvd, hr c d]; dsimp [P, Q]; group
  have hvdcb : e v d * e d c * e c b = A := by
    rw [hvdc, hr b c]; dsimp [Q, A]; group
  have hvdca : e v d * e d c * e c a = t₁ := by
    rw [hvdc, hr a c]
  have habd : e a b * e b d = (A * t₂⁻¹ * A⁻¹) * P := by
    dsimp [A, t₂, P]; group
  have habdv : e a b * e b d * e d v = A * t₂⁻¹ * A⁻¹ := by
    rw [habd, hclose]; dsimp [P]; group
  have habcv : e a b * e b c * e c v = Q * s₁⁻¹ * Q⁻¹ := by
    rw [hcv]; exact (mul_assoc Q s₁⁻¹ Q⁻¹).symm
  have hconj₂ : A * t₂⁻¹ * A⁻¹ ∈ U := hU.conj_mem A (hU.inv_mem ht₂)
  have hconj₁ : Q * s₁⁻¹ * Q⁻¹ ∈ U := hU.conj_mem Q (hU.inv_mem hs₁)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ⟨hA, ?_, ?_⟩, ⟨hA, hQ, ?_⟩⟩
  · rw [hav]; exact hU.mul_three (hU.inv_mem hs₃) (hU.inv_mem ht₃) (hU.inv_mem ht₁)
  · rw [hbv]; exact hU.mul_three (hU.inv_mem hs₂) (hU.inv_mem ht₂) (hU.inv_mem hA)
  · rw [hcv]; exact hU.one_two_mul (hU.inv_mem hs₁) (hU.inv_two hQ)
  · rw [hclose]; exact hU.two_three (hU.mem_two (hU.inv_mem hP))
  · rwa [hvd]
  · rwa [hvdc]
  · rwa [hvdcb]
  · rwa [hvd]
  · rwa [hvdc]
  · rwa [hvdca]
  · rw [habd]; exact hU.mul_two hconj₂ hP
  · rwa [habdv]
  · rwa [habcv]

/-- The gauge choice giving the closing equation for the four-neighbor step. -/
theorem four_extension_gauge {V : Type u} (g : V → V → H) (φ : V → H)
    {a b c d v : V} (hv : φ v = φ a * g a b * g b c * g c d * g d v) :
    residual g φ d v =
      (residual g φ a b * residual g φ b c * residual g φ c d)⁻¹ := by
  simp only [residual, hv]
  group

end FourExtension

/-! A finite frame construction handles separators of every size. Auxiliary
points carry their own gauges; several points may have the same graph vertex.
Replacing an auxiliary point by a clone is therefore a purely local operation,
and does not require adding vertices to the graph or changing existing gauges. -/

noncomputable section Frames

variable {V : Type u} {G : SimpleGraph V} {g : V → V → H}

local instance : DecidableEq (V × H) := Classical.decEq _

def Near (G : SimpleGraph V) (x y : V) : Prop := x = y ∨ G.Adj x y

theorem Near.symm {x y : V} (h : Near G x y) : Near G y x :=
  h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

def pointEdge (g : V → V → H) (p q : V × H) : H := p.2 * g p.1 q.1 * q.2⁻¹

def tupleBag {n : ℕ} {A : Type*} (f : Fin n → A) : Multiset A :=
  Finset.univ.val.map f

theorem mem_tupleBag {n : ℕ} {A : Type*} (f : Fin n → A) (a : A) :
    a ∈ tupleBag f ↔ ∃ i, f i = a := by simp [tupleBag]

theorem tupleBag_erase_mem {n : ℕ} {A : Type*} [DecidableEq A]
    (f : Fin n → A) {i d : Fin n} (h : i ≠ d) :
    f i ∈ (tupleBag f).erase (f d) := by
  have hi : i ∈ (Finset.univ : Finset (Fin n)).val.erase d :=
    (Multiset.mem_erase_of_ne h).mpr (Finset.mem_val.mpr (Finset.mem_univ i))
  have hm : f i ∈ ((Finset.univ : Finset (Fin n)).val.erase d).map f :=
    Multiset.mem_map.mpr ⟨i, hi, rfl⟩
  simpa only [tupleBag, Multiset.map_erase_of_mem f Finset.univ.val (by simp)] using hm

theorem tupleBag_three {A : Type*} (f : Fin 3 → A) :
    tupleBag f = f 0 ::ₘ f 1 ::ₘ f 2 ::ₘ 0 := by
  simp [tupleBag, Fin.univ_succ]

theorem tupleBag_four {A : Type*} (f : Fin 4 → A) :
    tupleBag f = f 0 ::ₘ f 1 ::ₘ f 2 ::ₘ f 3 ::ₘ 0 := by
  simp [tupleBag, Fin.univ_succ]

def TupleClique {n : ℕ} (f : Fin n → V × H) : Prop :=
  ∀ i j, Near G (f i).1 (f j).1

/-- A frame extension supplies one common new gauge for all deleted-slot faces. -/
structure FrameScheme (G : SimpleGraph V) (g : V → V → H) (U : Set H)
    (n r : ℕ) where
  positive : 0 < n
  good : (Fin n → V × H) → Prop
  constant : ∀ x p, good (fun _ => (x, p))
  inverse : ∀ ⦃x : H⦄, x ∈ U ^ r → x⁻¹ ∈ U ^ r
  extend : ∀ f, TupleClique (G := G) f → good f → ∀ v,
    (∀ i, Near G (f i).1 v) → ∃ q : H,
      (∀ i, pointEdge g (f i) (v, q) ∈ U ^ r) ∧
      ∀ d : Fin n, ∃ f' : Fin n → V × H,
        good f' ∧ tupleBag f' = (v, q) ::ₘ (tupleBag f).erase (f d)

variable {n r : ℕ} (C : FrameScheme G g U n r)

def Covers (f : Fin n → V × H) (S : Finset V) (φ : V → H) : Prop :=
  ∀ x ∈ S, ∃ i, f i = (x, φ x)

def HasFrame (S : Finset V) (φ : V → H) : Prop :=
  ∃ f : Fin n → V × H, TupleClique (G := G) f ∧ C.good f ∧ Covers f S φ

omit [Group H] in
theorem replacement_clique {f f' : Fin n → V × H} {v : V} {q : H} {d : Fin n}
    (hc : TupleClique (G := G) f) (hv : ∀ i, Near G (f i).1 v)
    (he : tupleBag f' = (v, q) ::ₘ (tupleBag f).erase (f d)) :
    TupleClique (G := G) f' := by
  have mem (i : Fin n) : f' i = (v, q) ∨ ∃ j, f j = f' i := by
    have hi : f' i ∈ tupleBag f' := (mem_tupleBag _ _).mpr ⟨i, rfl⟩
    rw [he, Multiset.mem_cons] at hi
    exact hi.imp_right fun h => (mem_tupleBag _ _).mp (Multiset.mem_of_mem_erase h)
  intro i j
  rcases mem i with hi | ⟨i', hi⟩ <;> rcases mem j with hj | ⟨j', hj⟩
  · rw [hi, hj]; exact Or.inl rfl
  · rw [hi, ← hj]; exact (hv j').symm
  · rw [← hi, hj]; exact hv i'
  · rw [← hi, ← hj]; exact hc i' j'

/-- Cloning removes every frame point outside a prescribed nonempty clique,
while preserving the actual gauges of that clique. -/
theorem localize_frame {S : Finset V} {φ : V → H} (hS : S.Nonempty)
    (hf : HasFrame C S φ) :
    ∃ f : Fin n → V × H, TupleClique (G := G) f ∧ C.good f ∧ Covers f S φ ∧
      ∀ i, (f i).1 ∈ S := by
  classical
  obtain ⟨f, hc, hg, hcov⟩ := hf
  let bad (f : Fin n → V × H) := ((tupleBag f).filter (fun p => p.1 ∉ S)).card
  suffices ∀ k (f : Fin n → V × H), bad f = k → TupleClique (G := G) f →
      C.good f → Covers f S φ →
      ∃ f' : Fin n → V × H, TupleClique (G := G) f' ∧ C.good f' ∧ Covers f' S φ ∧
        ∀ i, (f' i).1 ∈ S from this _ f rfl hc hg hcov
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro f hk hc hg hcov
    by_cases hall : ∀ i, (f i).1 ∈ S
    · exact ⟨f, hc, hg, hcov, hall⟩
    obtain ⟨d, hd⟩ := not_forall.mp hall
    obtain ⟨x, hx⟩ := hS
    obtain ⟨ix, hix⟩ := hcov x hx
    have hv : ∀ i, Near G (f i).1 x := by
      intro i
      simpa only [hix] using hc i ix
    obtain ⟨q, _, hfaces⟩ := C.extend f hc hg x hv
    obtain ⟨f', hg', he⟩ := hfaces d
    have hc' := replacement_clique hc hv he
    have hcov' : Covers f' S φ := by
      intro y hy
      obtain ⟨i, hi⟩ := hcov y hy
      apply (mem_tupleBag f' _).mp
      rw [he]
      apply Multiset.mem_cons.mpr ∘ Or.inr
      apply (Multiset.mem_erase_of_ne (a := (y, φ y)) (b := f d) ?_).mpr
      · rw [← hi]; exact (mem_tupleBag _ _).mpr ⟨i, rfl⟩
      · intro h; exact hd (by simpa only [← h] using hy)
    have hlt : bad f' < k := by
      have hm : f d ∈ tupleBag f := (mem_tupleBag _ _).mpr ⟨d, rfl⟩
      have hb : tupleBag f = f d ::ₘ (tupleBag f).erase (f d) :=
        (Multiset.cons_erase hm).symm
      have h₁ : bad f' = (((tupleBag f).erase (f d)).filter (fun p => p.1 ∉ S)).card := by
        dsimp [bad]; rw [he]; simp [hx]
      have h₂ : bad f = (((tupleBag f).erase (f d)).filter (fun p => p.1 ∉ S)).card + 1 := by
        dsimp [bad]; conv_lhs => rw [hb]; simp [hd]
      omega
    exact ih _ hlt f' rfl hc' hg' hcov'

theorem pointEdge_reverse (hr : ∀ x y, Near G x y → g y x = (g x y)⁻¹)
    {p q : V × H} (hpq : Near G p.1 q.1) :
    pointEdge g q p = (pointEdge g p q)⁻¹ := by
  simp only [pointEdge, hr _ _ hpq, mul_inv_rev, inv_inv, mul_assoc]

theorem pointEdge_triangle (hU : NormalSet U)
    (ht : ∀ x y z, Near G x y → Near G y z → Near G x z →
      g x y * g y z * (g x z)⁻¹ ∈ U)
    {p q s : V × H} (hpq : Near G p.1 q.1) (hqs : Near G q.1 s.1)
    (hps : Near G p.1 s.1) :
    pointEdge g p q * pointEdge g q s * (pointEdge g p s)⁻¹ ∈ U := by
  convert hU.conj_mem p.2 (ht _ _ _ hpq hqs hps) using 1;
    simp [pointEdge, mul_assoc]

def augmented (f : Fin n → V × H) (v : V) (q : H) : Option (Fin n) → V × H
  | none => (v, q)
  | some i => f i

omit [Group H] in
theorem augmented_clique {f : Fin n → V × H} (hc : TupleClique (G := G) f)
    {v : V} (hv : ∀ i, Near G (f i).1 v) (q : H) :
    ∀ i j, Near G (augmented f v q i).1 (augmented f v q j).1 := by
  intro i j
  cases i with
  | none => cases j with
    | none => exact Or.inl rfl
    | some j => exact (hv j).symm
  | some i => cases j with
    | none => exact hv i
    | some j => exact hc i j

/-- The triangle table gives a complete three-slot extension scheme. -/
def triangleScheme (hU : NormalSet U) (h₁ : ∀ x, g x x = 1)
    (hr : ∀ x y, Near G x y → g y x = (g x y)⁻¹)
    (ht : ∀ x y z, Near G x y → Near G y z → Near G x z →
      g x y * g y z * (g x z)⁻¹ ∈ U) : FrameScheme G g U 3 2 where
  positive := by decide
  good f := GoodTriangle U (pointEdge g) (f 0) (f 1) (f 2)
  constant x p := by simpa [GoodTriangle, pointEdge, h₁] using And.intro hU.one_mem hU.one_mem
  inverse := fun {_} hx => hU.inv_two hx
  extend f hc hg v hv := by
    let q := (f 1).2 * g (f 1).1 (f 0).1 * g (f 0).1 (f 2).1 * g (f 2).1 v
    let F := augmented f v q
    let e (i j : Option (Fin 3)) := pointEdge g (F i) (F j)
    have hF := augmented_clique hc hv q
    have her : ∀ i j, e j i = (e i j)⁻¹ := fun i j => pointEdge_reverse hr (hF i j)
    have het : ∀ i j k, e i j * e j k * (e i k)⁻¹ ∈ U :=
      fun i j k => pointEdge_triangle hU ht (hF i j) (hF j k) (hF i k)
    have hec : e (some 2) none = ((e (some 0) (some 1))⁻¹ * e (some 0) (some 2))⁻¹ := by
      dsimp [e, F, augmented, pointEdge, q]
      rw [hr _ _ (hc 0 1)]
      group
    have h := triangle_extension hU her het (a := some 0) (b := some 1) (c := some 2) hg hec
    refine ⟨q, ?_, ?_⟩
    · intro i; fin_cases i
      · exact h.1
      · exact h.2.1
      · exact h.2.2.1
    · intro d; fin_cases d
      · refine ⟨![f 2, (v, q), f 1], h.2.2.2.2.2, ?_⟩
        change tupleBag ![f 2, (v, q), f 1] = (v, q) ::ₘ (tupleBag f).erase (f 0)
        rw [tupleBag_three f, Multiset.erase_cons_head]
        simp [tupleBag_three, ← Multiset.singleton_add, add_comm, add_left_comm, add_assoc]
      · refine ⟨![f 2, (v, q), f 0], h.2.2.2.2.1, ?_⟩
        change tupleBag ![f 2, (v, q), f 0] = (v, q) ::ₘ (tupleBag f).erase (f 1)
        have he : tupleBag f = f 1 ::ₘ f 0 ::ₘ f 2 ::ₘ 0 := by
          rw [tupleBag_three]; exact Multiset.cons_swap _ _ _
        rw [he, Multiset.erase_cons_head]
        simp [tupleBag_three, ← Multiset.singleton_add, add_comm, add_left_comm, add_assoc]
      · refine ⟨![f 0, f 1, (v, q)], h.2.2.2.1, ?_⟩
        change tupleBag ![f 0, f 1, (v, q)] = (v, q) ::ₘ (tupleBag f).erase (f 2)
        have he : tupleBag f = f 2 ::ₘ f 0 ::ₘ f 1 ::ₘ 0 := by
          rw [tupleBag_three]; simp only [← Multiset.singleton_add]; ac_rfl
        rw [he, Multiset.erase_cons_head]
        simp [tupleBag_three, ← Multiset.singleton_add, add_comm, add_assoc]

/-- The four-clique table gives a complete four-slot extension scheme. -/
def fourScheme (hU : NormalSet U) (h₁ : ∀ x, g x x = 1)
    (hr : ∀ x y, Near G x y → g y x = (g x y)⁻¹)
    (ht : ∀ x y z, Near G x y → Near G y z → Near G x z →
      g x y * g y z * (g x z)⁻¹ ∈ U) : FrameScheme G g U 4 3 where
  positive := by decide
  good f := GoodFour U (pointEdge g) (f 0) (f 1) (f 2) (f 3)
  constant x p := by
    simpa [GoodFour, pointEdge, h₁] using
      And.intro hU.one_mem (And.intro (Set.one_mem_pow hU.one_mem) hU.one_mem)
  inverse := fun {_} hx => hU.inv_three hx
  extend f hc hg v hv := by
    let q := (f 0).2 * g (f 0).1 (f 1).1 * g (f 1).1 (f 2).1 *
      g (f 2).1 (f 3).1 * g (f 3).1 v
    let F := augmented f v q
    let e (i j : Option (Fin 4)) := pointEdge g (F i) (F j)
    have hF := augmented_clique hc hv q
    have her : ∀ i j, e j i = (e i j)⁻¹ := fun i j => pointEdge_reverse hr (hF i j)
    have het : ∀ i j k, e i j * e j k * (e i k)⁻¹ ∈ U :=
      fun i j k => pointEdge_triangle hU ht (hF i j) (hF j k) (hF i k)
    have hec : e (some 3) none =
        (e (some 0) (some 1) * e (some 1) (some 2) * e (some 2) (some 3))⁻¹ := by
      dsimp [e, F, augmented, pointEdge, q]; group
    have h := four_extension hU her het (a := some 0) (b := some 1)
      (c := some 2) (d := some 3) hg hec
    refine ⟨q, ?_, ?_⟩
    · intro i; fin_cases i
      · exact h.1.1
      · exact h.1.2.1
      · exact h.1.2.2.1
      · exact h.1.2.2.2
    · intro d; fin_cases d
      · refine ⟨![(v, q), f 3, f 2, f 1], h.2.1, ?_⟩
        change tupleBag ![(v, q), f 3, f 2, f 1] = (v, q) ::ₘ (tupleBag f).erase (f 0)
        rw [tupleBag_four f, Multiset.erase_cons_head]
        simp [tupleBag_four, ← Multiset.singleton_add, add_comm, add_assoc]
      · refine ⟨![(v, q), f 3, f 2, f 0], h.2.2.1, ?_⟩
        change tupleBag ![(v, q), f 3, f 2, f 0] = (v, q) ::ₘ (tupleBag f).erase (f 1)
        have he : tupleBag f = f 1 ::ₘ f 0 ::ₘ f 2 ::ₘ f 3 ::ₘ 0 := by
          rw [tupleBag_four]; exact Multiset.cons_swap _ _ _
        rw [he, Multiset.erase_cons_head]
        simp [tupleBag_four, ← Multiset.singleton_add, add_comm, add_assoc]
      · refine ⟨![f 0, f 1, f 3, (v, q)], h.2.2.2.1, ?_⟩
        change tupleBag ![f 0, f 1, f 3, (v, q)] = (v, q) ::ₘ (tupleBag f).erase (f 2)
        have he : tupleBag f = f 2 ::ₘ f 0 ::ₘ f 1 ::ₘ f 3 ::ₘ 0 := by
          rw [tupleBag_four]; simp only [← Multiset.singleton_add]; ac_rfl
        rw [he, Multiset.erase_cons_head]
        simp [tupleBag_four, ← Multiset.singleton_add, add_comm, add_assoc]
      · refine ⟨![f 0, f 1, f 2, (v, q)], h.2.2.2.2, ?_⟩
        change tupleBag ![f 0, f 1, f 2, (v, q)] = (v, q) ::ₘ (tupleBag f).erase (f 3)
        have he : tupleBag f = f 3 ::ₘ f 0 ::ₘ f 1 ::ₘ f 2 ::ₘ 0 := by
          rw [tupleBag_four]; simp only [← Multiset.singleton_add]; ac_rfl
        rw [he, Multiset.erase_cons_head]
        simp [tupleBag_four, ← Multiset.singleton_add, add_comm, add_assoc]

/-- Finite simplicial elimination for a frame scheme. The invariant stores a
frame for every nonempty clique of size at most `n`, including small separators. -/
theorem FrameScheme.finite_potential (C : FrameScheme G g U n r)
    (hG : G.IsChordal)
    (hb : ∀ t : Finset V, G.IsClique (t : Set V) → t.card ≤ n + 1)
    (hr : ∀ x y, Near G x y → g y x = (g x y)⁻¹) (S : Finset V) :
    ∃ φ : V → H,
      (∀ x ∈ S, ∀ y ∈ S, G.Adj x y → residual g φ x y ∈ U ^ r) ∧
      ∀ t : Finset V, t ⊆ S → t.Nonempty → G.IsClique (t : Set V) → t.card ≤ n →
        HasFrame C t φ := by
  classical
  suffices ∀ k (S : Finset V), S.card = k →
      ∃ φ : V → H,
        (∀ x ∈ S, ∀ y ∈ S, G.Adj x y → residual g φ x y ∈ U ^ r) ∧
        ∀ t : Finset V, t ⊆ S → t.Nonempty → G.IsClique (t : Set V) → t.card ≤ n →
          HasFrame C t φ from this S.card S rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro S hk
    by_cases hS : S.Nonempty
    · obtain ⟨z, hz, hsimp⟩ := hG.exists_simplicial_in_finset S hS
      obtain ⟨φ, he, hf⟩ := ih (S.erase z).card
        (by have := Finset.card_erase_lt_of_mem hz; omega) (S.erase z) rfl
      let N := (S.erase z).filter (G.Adj z)
      have memN (x : V) : x ∈ N ↔ x ∈ S ∧ x ≠ z ∧ G.Adj z x := by
        simp [N, and_assoc, and_left_comm]
      have hNS : N ⊆ S.erase z := Finset.filter_subset _ _
      have hcN : G.IsClique (N : Set V) := by
        intro a ha b hb hab
        exact hsimp a ((memN a).mp ha).1 b ((memN b).mp hb).1
          ((memN a).mp ha).2.2 ((memN b).mp hb).2.2 hab
      have hzN : z ∉ N := by simp [N]
      have hbN : N.card ≤ n := by
        have hc : G.IsClique ((insert z N : Finset V) : Set V) := by
          rw [Finset.coe_insert]
          exact hcN.insert (fun x hx _ => ((memN x).mp hx).2.2)
        have h := hb (insert z N) hc
        rw [Finset.card_insert_of_notMem hzN] at h
        omega
      have hframe : ∃ f : Fin n → V × H, TupleClique (G := G) f ∧ C.good f ∧
          Covers f N φ ∧ ∀ i, Near G (f i).1 z := by
        by_cases hN : N.Nonempty
        · obtain ⟨f, hc, hg, hcov, himg⟩ := localize_frame C hN (hf N hNS hN hcN hbN)
          refine ⟨f, hc, hg, hcov, fun i => Or.inr ?_⟩
          exact ((memN _).mp (himg i)).2.2.symm
        · refine ⟨fun _ => (z, 1), fun _ _ => Or.inl rfl, C.constant z 1, ?_,
            fun _ => Or.inl rfl⟩
          intro x hx; exact (hN ⟨x, hx⟩).elim
      obtain ⟨f, hc, hg, hcov, hv⟩ := hframe
      obtain ⟨q, hnew, hfaces⟩ := C.extend f hc hg z hv
      let φ' : V → H := fun x => if x = z then q else φ x
      have hφz : φ' z = q := by simp [φ']
      have hφ {x : V} (hx : x ≠ z) : φ' x = φ x := by simp [φ', hx]
      have newedge (x : V) (hx : x ∈ N) : residual g φ' x z ∈ U ^ r := by
        obtain ⟨i, hi⟩ := hcov x hx
        have h := hnew i
        rw [hi] at h
        simpa only [residual, pointEdge, hφ ((memN x).mp hx).2.1, hφz] using h
      refine ⟨φ', ?_, ?_⟩
      · intro x hx y hy hxy
        by_cases hxz : x = z
        · subst x
          have hyN := (memN y).mpr ⟨hy, hxy.ne.symm, hxy⟩
          rw [residual_reverse φ' (hr y z (Or.inr hxy.symm))]
          exact C.inverse (newedge y hyN)
        · by_cases hyz : y = z
          · subst y
            exact newedge x ((memN x).mpr ⟨hx, hxz, hxy.symm⟩)
          · simpa only [residual, hφ hxz, hφ hyz] using
              he x (Finset.mem_erase.mpr ⟨hxz, hx⟩) y (Finset.mem_erase.mpr ⟨hyz, hy⟩) hxy
      · intro t ht htn htc htnum
        by_cases hzt : z ∈ t
        · have htN : t.erase z ⊆ N := by
            intro x hx
            have hx' := Finset.mem_erase.mp hx
            exact (memN x).mpr ⟨ht hx'.2, hx'.1, htc hzt hx'.2 hx'.1.symm⟩
          let idx : (t.erase z) → Fin n := fun x => (hcov x (htN x.property)).choose
          have idxspec (x : t.erase z) : f (idx x) = ((x : V), φ x) :=
            (hcov x (htN x.property)).choose_spec
          have hcard : Fintype.card (t.erase z) < Fintype.card (Fin n) := by
            simpa only [Fintype.card_coe, Fintype.card_fin] using
              (Finset.card_erase_lt_of_mem hzt).trans_le htnum
          have hns : ¬ Function.Surjective idx := fun hs =>
            (not_le_of_gt hcard) (Fintype.card_le_of_surjective idx hs)
          have hex : ∃ d, ∀ x, idx x ≠ d := by
            simpa only [Function.Surjective, not_forall, not_exists] using hns
          obtain ⟨d, hd⟩ := hex
          obtain ⟨f', hg', hbag⟩ := hfaces d
          refine ⟨f', replacement_clique hc hv hbag, hg', ?_⟩
          intro x hx
          apply (mem_tupleBag f' _).mp
          rw [hbag]
          by_cases hxz : x = z
          · subst x; simp [hφz]
          · have hxt : x ∈ t.erase z := Finset.mem_erase.mpr ⟨hxz, hx⟩
            have hi := tupleBag_erase_mem f (hd ⟨x, hxt⟩)
            rw [idxspec ⟨x, hxt⟩] at hi
            rw [hφ hxz]
            exact Multiset.mem_cons.mpr (Or.inr hi)
        · obtain ⟨f', hc', hg', hcov'⟩ := hf t
            (fun x hx => Finset.mem_erase.mpr ⟨fun h => hzt (h ▸ hx), ht hx⟩)
            htn htc htnum
          refine ⟨f', hc', hg', ?_⟩
          intro x hx
          rw [hφ (fun h => hzt (h ▸ hx))]
          exact hcov' x hx
    · refine ⟨fun _ => 1, ?_, ?_⟩
      · intro x hx; exact (hS ⟨x, hx⟩).elim
      · intro t ht htn
        obtain ⟨x, hx⟩ := htn
        exact (hS ⟨x, ht hx⟩).elim

end Frames

section Universal

variable {V : Type u} {G : SimpleGraph V} {g : V → V → H}

def normalizedGain [DecidableEq V] (g : V → V → H) (x y : V) : H :=
  if x = y then 1 else g x y

theorem normalizedGain_adj [DecidableEq V] {x y : V} (h : G.Adj x y) :
    normalizedGain g x y = g x y := ite_eq_right h.ne

theorem normalizedGain_reverse [DecidableEq V]
    (hr : ∀ x y, G.Adj x y → g y x = (g x y)⁻¹)
    {x y : V} (h : Near G x y) :
    normalizedGain g y x = (normalizedGain g x y)⁻¹ := by
  rcases h with rfl | h
  · simp [normalizedGain]
  · simp only [normalizedGain_adj h, normalizedGain_adj h.symm, hr _ _ h]

theorem normalizedGain_triangle [DecidableEq V] (hU : NormalSet U)
    (hr : ∀ x y, G.Adj x y → g y x = (g x y)⁻¹)
    (ht : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z →
      g x y * g y z * (g x z)⁻¹ ∈ U)
    {x y z : V} (hxy : Near G x y) (hyz : Near G y z) (hxz : Near G x z) :
    normalizedGain g x y * normalizedGain g y z * (normalizedGain g x z)⁻¹ ∈ U := by
  rcases hxy with rfl | hxy
  · simpa [normalizedGain] using hU.one_mem
  rcases hyz with rfl | hyz
  · simpa [normalizedGain] using hU.one_mem
  rcases hxz with rfl | hxz
  · simpa [normalizedGain, hxy.ne, hxy.ne.symm, hr _ _ hxy] using hU.one_mem
  simpa only [normalizedGain_adj hxy, normalizedGain_adj hyz, normalizedGain_adj hxz] using
    ht x y z hxy hyz hxz

/-- Universal nonabelian upper bound at clique number at most four.
This includes empty and disconnected graphs, and assumes no metric on `H`. -/
theorem exists_potential_clique_le_four [Finite V] (hG : G.IsChordal)
    (hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ 4)
    (hU : NormalSet U) (g : V → V → H)
    (hrev : ∀ x y, G.Adj x y → g y x = (g x y)⁻¹)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z →
      g x y * g y z * (g x z)⁻¹ ∈ U) :
    ∃ φ : V → H, ∀ x y, G.Adj x y → residual g φ x y ∈ U ^ 2 := by
  classical
  let := Fintype.ofFinite V
  let γ := normalizedGain g
  have h₁ : ∀ x, γ x x = 1 := by intro x; simp [γ, normalizedGain]
  have hr : ∀ x y, Near G x y → γ y x = (γ x y)⁻¹ :=
    fun _ _ h => normalizedGain_reverse hrev h
  have ht : ∀ x y z, Near G x y → Near G y z → Near G x z →
      γ x y * γ y z * (γ x z)⁻¹ ∈ U :=
    fun _ _ _ hxy hyz hxz => normalizedGain_triangle hU hrev htri hxy hyz hxz
  let C := triangleScheme hU h₁ hr ht
  obtain ⟨φ, hφ, _⟩ := C.finite_potential hG hclique hr Finset.univ
  refine ⟨φ, fun x y hxy => ?_⟩
  simpa only [residual, γ, normalizedGain_adj hxy] using
    hφ x (Finset.mem_univ _) y (Finset.mem_univ _) hxy

/-- Universal nonabelian upper bound at clique number at most five.
The frame construction supplies the smaller-separator cases unconditionally. -/
theorem exists_potential_clique_le_five [Finite V] (hG : G.IsChordal)
    (hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ 5)
    (hU : NormalSet U) (g : V → V → H)
    (hrev : ∀ x y, G.Adj x y → g y x = (g x y)⁻¹)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z →
      g x y * g y z * (g x z)⁻¹ ∈ U) :
    ∃ φ : V → H, ∀ x y, G.Adj x y → residual g φ x y ∈ U ^ 3 := by
  classical
  let := Fintype.ofFinite V
  let γ := normalizedGain g
  have h₁ : ∀ x, γ x x = 1 := by intro x; simp [γ, normalizedGain]
  have hr : ∀ x y, Near G x y → γ y x = (γ x y)⁻¹ :=
    fun _ _ h => normalizedGain_reverse hrev h
  have ht : ∀ x y z, Near G x y → Near G y z → Near G x z →
      γ x y * γ y z * (γ x z)⁻¹ ∈ U :=
    fun _ _ _ hxy hyz hxz => normalizedGain_triangle hU hrev htri hxy hyz hxz
  let C := fourScheme hU h₁ hr ht
  obtain ⟨φ, hφ, _⟩ := C.finite_potential hG hclique hr Finset.univ
  refine ⟨φ, fun x y hxy => ?_⟩
  simpa only [residual, γ, normalizedGain_adj hxy] using
    hφ x (Finset.mem_univ _) y (Finset.mem_univ _) hxy

end Universal

end SimpleGraph.GroupCliqueStrata
