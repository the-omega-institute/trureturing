/- GID: D5/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/EilenbergZilber/DerivedOperators
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formal integer-linear simplicial operators and their realizations. -/

/-
Copyright (c) 2026 Jeffrey Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey Li

Source: LeanPool/EilenbergZilber, revision 8bbde3a6de815108d41922c9362ebbe38422663a.
Original source: jeffrey-dot-li/lean-homology, revision
40c5aae235b0f499ebfc1e68ce574a62b531203c; author release
fd0147a1ffe4f3c14c247574e148893d7cdf8cf6 (LeanPool PR 588).
Modifications: receiving namespace and imports, module boundaries, exposure of
consumed private interfaces, canonical identifier spellings, and omission of unused
companion, reflexive binding, and frontal material.
-/

module

public import D5.S3.HomologicalAlgebra.EilenbergZilber.Bisimplicial
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# Eilenberg–Mac Lane derived-operator API for the normalized Eilenberg–Zilber homotopy

This file builds the **tiny, local derived-operator API** needed to formalize Eilenberg–Mac Lane's
*recursive* construction of the Eilenberg–Zilber homotopy `Φ` (Eilenberg–Mac Lane II, Thm 2.1a,
the identity `∂Φ + Φ∂ = ∇f − i` modulo norms). It is the input to
`eilenbergZilberNormalized` in `BisimplicialNormalized.lean`.

We deliberately **do not** use an explicit closed-form homotopy; the literature only ever proves
the contraction identity via the recursion + derived operators, so we follow EM directly.

## Design

EM's "natural operators" `M : (K×L)_s → (K×L)_q` (their (2.10)) are, on a bisimplicial object `X`,
exactly finite `ℤ`-linear combinations of **letters**: a pair of `SimplexCategory` maps
`(β, γ) : ⟦q⟧ ⟶ ⟦s⟧` acting on the diagonal `FTwo.obj X = diag X` by

`(X.obj ⟦s⟧).map γ.op ≫ (X.map β.op).app ⟦q⟧ : X_{s,s} ⟶ X_{q,q}`.

* `OpLetter s q` — one such pair, `DerivedOp s q := OpLetter s q →₀ ℤ` — a formal `ℤ`-combination.
* `DerivedOp.realize X` — realize a formal operator as an actual degreewise hom on `FTwo.obj X`.
* `DerivedOp.prime` — EM's derived operator `M ↦ M'` (prepend the 0-th coface `δ⁰` to each letter).

"Modulo norms" is represented (per the project's `PInfty` strategy) by postcomposing with
`retractionNTwo X = PInftyToNormalizedMooreComplex (diag X)`: a term is a *norm* iff it dies after
`≫ retractionNTwo`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicTopology AlgebraicTopology.DoldKan CategoryTheory.Limits
open scoped Simplicial

namespace D5.S3.HomologicalAlgebra.EilenbergZilber

namespace BisimplicialObject

variable {C : Type*} [Category C] [Abelian C]

/-! ### Operators as formal `ℤ`-combinations of letters -/

/-- A **letter**: a pair of `SimplexCategory` maps `⟦q⟧ ⟶ ⟦s⟧`. The `fst` map acts on the
horizontal (first / `K`) simplicial variable and `snd` on the vertical (second / `L`) one.
Realized on a bisimplicial object it gives a single summand `X_{s,s} ⟶ X_{q,q}` of an EM
natural operator (their (2.10)). -/
structure OpLetter (s q : ℕ) where
  /-- Horizontal (`K`-side) `SimplexCategory` map. -/
  fst : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌
  /-- Vertical (`L`-side) `SimplexCategory` map. -/
  snd : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌

noncomputable instance (s q : ℕ) : DecidableEq (OpLetter s q) := Classical.decEq _

/-- An EM natural operator `(K×L)_s → (K×L)_q` (their (2.10)): a finite `ℤ`-linear combination of
letters, with uniqueness of representation supplied by carrying the representation as data. -/
abbrev DerivedOp (s q : ℕ) := OpLetter s q →₀ ℤ

/-- Realize a single letter as a degreewise hom on the diagonal complex `FTwo.obj X`. -/
noncomputable def OpLetter.realizeLetter {s q : ℕ} (X : BisimplicialObject C) (l : OpLetter s q) :
    (FTwo.obj X).X s ⟶ (FTwo.obj X).X q :=
  (X.obj (Opposite.op ⦋s⦌)).map l.snd.op ≫ (X.map l.fst.op).app (Opposite.op ⦋q⦌)

/-- Realize a formal operator as a degreewise hom on `FTwo.obj X` (`ℤ`-linear extension of
`OpLetter.realizeLetter`). -/
noncomputable def DerivedOp.realize {s q : ℕ} (X : BisimplicialObject C) (M : DerivedOp s q) :
    (FTwo.obj X).X s ⟶ (FTwo.obj X).X q :=
  M.sum fun l c => c • l.realizeLetter X

/-! ### The derived operator `M ↦ M'` (EM (2.10)) -/

/-- The 0-th-coface shift of a monotone map: `0 ↦ 0`, `j+1 ↦ θ(j)+1`. This is EM's `δ⁰`
prepending used to define the derived operator. -/
def primeHom {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    (⦋q + 1⦌ : SimplexCategory) ⟶ ⦋s + 1⦌ :=
  SimplexCategory.mkHom
    { toFun := fun j =>
        ⟨min (if (j : ℕ) = 0 then 0
              else (SimplexCategory.Hom.toOrderHom θ
                ⟨(j : ℕ) - 1, (by have := j.isLt; omega : (j : ℕ) - 1 < q + 1)⟩ : ℕ) + 1) (s + 1),
          by omega⟩
      monotone' := by
        intro a b hab
        have hab' : (a : ℕ) ≤ (b : ℕ) := hab
        simp only [Fin.mk_le_mk]
        split_ifs with ha hb hb
        · omega
        · omega
        · omega
        · have hmono : (SimplexCategory.Hom.toOrderHom θ
              ⟨(a : ℕ) - 1, (by have := a.isLt; omega : (a : ℕ) - 1 < q + 1)⟩ : ℕ) ≤
              (SimplexCategory.Hom.toOrderHom θ
              ⟨(b : ℕ) - 1, (by have := b.isLt; omega : (b : ℕ) - 1 < q + 1)⟩ : ℕ) :=
            (SimplexCategory.Hom.toOrderHom θ).monotone (by simp only [Fin.mk_le_mk]; omega)
          omega }

/-- The derived operator on a single letter: prime both `SimplexCategory` maps. -/
def OpLetter.primeLetter {s q : ℕ} (l : OpLetter s q) : OpLetter (s + 1) (q + 1) :=
  ⟨primeHom l.fst, primeHom l.snd⟩

/-- EM's **derived operator** `M ↦ M'` (their (2.10)): prime every letter, `ℤ`-linearly. -/
noncomputable def DerivedOp.prime {s q : ℕ} (M : DerivedOp s q) : DerivedOp (s + 1) (q + 1) :=
  Finsupp.mapDomain OpLetter.primeLetter M

/-! ### Composition of operators (vertical, on the diagonal) -/

/-- Composition of letters: `comp l₂ l₁` realizes to `realize l₁ ≫ realize l₂` (apply `l₁` then
`l₂`). Horizontal and vertical maps compose independently. -/
def OpLetter.compLetter {s q r : ℕ} (l₂ : OpLetter q r) (l₁ : OpLetter s q) : OpLetter s r :=
  ⟨l₂.fst ≫ l₁.fst, l₂.snd ≫ l₁.snd⟩

/-- `ℤ`-bilinear composition of operators (apply `MOne` then `MTwo`). -/
noncomputable def DerivedOp.comp {s q r : ℕ} (MTwo : DerivedOp q r) (MOne : DerivedOp s q) :
    DerivedOp s r :=
  MOne.sum fun l₁ c₁ => MTwo.sum fun l₂ c₂ => Finsupp.single (l₂.compLetter l₁) (c₁ * c₂)

/-! ### Functoriality / `ℤ`-linearity of `realize`

These let the abstract operator identities (`prime_comp_truncBoundary`, `lastFace_comp_prime`,
`boundary_comp_D0`, …) be pushed to genuine hom identities on `FTwo.obj X`, so the EM induction can
run at the operator level and only be realized at the end. -/

@[simp] lemma realize_zero {s q : ℕ} (X : BisimplicialObject C) :
    (0 : DerivedOp s q).realize X = 0 := by
  simp [DerivedOp.realize]

@[simp] lemma realize_single {s q : ℕ} (X : BisimplicialObject C) (l : OpLetter s q) (c : ℤ) :
    DerivedOp.realize X (Finsupp.single l c) = c • l.realizeLetter X := by
  simp [DerivedOp.realize, Finsupp.sum_single_index]

lemma realize_add {s q : ℕ} (X : BisimplicialObject C) (M N : DerivedOp s q) :
    (M + N).realize X = M.realize X + N.realize X := by
  simp [DerivedOp.realize, Finsupp.sum_add_index', zero_smul, add_smul]

lemma realize_neg {s q : ℕ} (X : BisimplicialObject C) (M : DerivedOp s q) :
    (-M).realize X = -(M.realize X) := by
  simp [DerivedOp.realize, Finsupp.sum_neg_index, neg_smul]

lemma realize_sub {s q : ℕ} (X : BisimplicialObject C) (M N : DerivedOp s q) :
    (M - N).realize X = M.realize X - N.realize X := by
  simp [sub_eq_add_neg, realize_add, realize_neg]

noncomputable def realizeAddMonoidHom {s q : ℕ} (X : BisimplicialObject C) :
    DerivedOp s q →+ ((FTwo.obj X).X s ⟶ (FTwo.obj X).X q) where
  toFun M := M.realize X
  map_zero' := realize_zero X
  map_add' := realize_add X

lemma realize_zsmul {s q : ℕ} (X : BisimplicialObject C) (c : ℤ) (M : DerivedOp s q) :
    (c • M).realize X = c • M.realize X :=
  map_zsmul (realizeAddMonoidHom X) c M

/-- A single composed letter realizes to the composition of the realizations (the Pattern-5
bifunctor merge: interleave the horizontal/vertical legs via naturality of `X.map _`). -/
private lemma OpLetter.realizeLetter_compLetter {s q r : ℕ} (X : BisimplicialObject C) (l₂ : OpLetter q r)
    (l₁ : OpLetter s q) :
    (l₂.compLetter l₁).realizeLetter X = l₁.realizeLetter X ≫ l₂.realizeLetter X := by
  change (X.obj (Opposite.op ⦋s⦌)).map (l₂.snd ≫ l₁.snd).op ≫
      (X.map (l₂.fst ≫ l₁.fst).op).app (Opposite.op ⦋r⦌) =
    ((X.obj (Opposite.op ⦋s⦌)).map l₁.snd.op ≫ (X.map l₁.fst.op).app (Opposite.op ⦋q⦌)) ≫
      ((X.obj (Opposite.op ⦋q⦌)).map l₂.snd.op ≫ (X.map l₂.fst.op).app (Opposite.op ⦋r⦌))
  simp only [op_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% ((X.map l₁.fst.op).naturality l₂.snd.op)]

/-- `comp` is additive in its right argument. -/
lemma DerivedOp.comp_add_right {s q r : ℕ} (MTwo : DerivedOp q r) (M N : DerivedOp s q) :
    MTwo.comp (M + N) = MTwo.comp M + MTwo.comp N := by
  simp only [DerivedOp.comp]
  rw [Finsupp.sum_add_index']
  · intro a; simp
  · intro a b₁ b₂; simp only [add_mul, Finsupp.single_add]; rw [Finsupp.sum_add]

/-- `comp` is additive in its left argument. -/
lemma DerivedOp.add_comp {s q r : ℕ} (M N : DerivedOp q r) (K : DerivedOp s q) :
    (M + N).comp K = M.comp K + N.comp K := by
  simp only [DerivedOp.comp]
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro l₁ _
  rw [Finsupp.sum_add_index']
  · intro a; simp
  · intro a b₁ b₂; simp only [mul_add, Finsupp.single_add]

/-- `comp` on a right `single`. -/
lemma DerivedOp.comp_single_right {s q r : ℕ} (MTwo : DerivedOp q r) (l₁ : OpLetter s q)
    (c : ℤ) :
    MTwo.comp (Finsupp.single l₁ c) = MTwo.sum fun l₂ c₂ => Finsupp.single (l₂.compLetter l₁) (c * c₂) := by
  rw [DerivedOp.comp, Finsupp.sum_single_index (by simp)]

/-- `comp` of two `single`s. -/
lemma DerivedOp.single_comp_single {s q r : ℕ} (l₂ : OpLetter q r) (l₁ : OpLetter s q)
    (c₂ c₁ : ℤ) :
    DerivedOp.comp (Finsupp.single l₂ c₂) (Finsupp.single l₁ c₁) =
      Finsupp.single (l₂.compLetter l₁) (c₁ * c₂) := by
  rw [DerivedOp.comp_single_right, Finsupp.sum_single_index (by simp)]

/-- `realize` turns operator composition into hom composition (contravariantly: apply `MOne` then
`MTwo`). The functoriality fact that drives the operator-level induction. Proved by reducing to the
single-single case (`OpLetter.realizeLetter_compLetter`) via bilinearity of `comp` and additivity of
`realize`. -/
lemma realize_comp {s q r : ℕ} (X : BisimplicialObject C) (MTwo : DerivedOp q r)
    (MOne : DerivedOp s q) :
    (MTwo.comp MOne).realize X = MOne.realize X ≫ MTwo.realize X := by
  induction MOne using Finsupp.induction with
  | zero => simp [DerivedOp.comp]
  | single_add l₁ c₁ f _ _ ih =>
    rw [DerivedOp.comp_add_right, realize_add, ih, realize_add, Preadditive.add_comp]
    congr 1
    clear ih
    induction MTwo using Finsupp.induction with
    | zero => simp [DerivedOp.comp]
    | single_add l₂ c₂ g _ _ ih₂ =>
      rw [DerivedOp.add_comp, realize_add, ih₂, realize_add, Preadditive.comp_add]
      congr 1
      simp only [DerivedOp.single_comp_single, realize_single, OpLetter.realizeLetter_compLetter,
        Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul]
      rw [mul_comm c₂ c₁]

/-- The identity letter realizes to the identity hom. -/
lemma realize_single_id {q : ℕ} (X : BisimplicialObject C) :
    DerivedOp.realize X (Finsupp.single ⟨𝟙 _, 𝟙 _⟩ 1 : DerivedOp q q) = 𝟙 ((FTwo.obj X).X q) := by
  rw [realize_single, one_smul]
  change (X.obj (Opposite.op ⦋q⦌)).map (𝟙 _).op ≫ (X.map (𝟙 _).op).app (Opposite.op ⦋q⦌) =
    𝟙 ((X.obj (Opposite.op ⦋q⦌)).obj (Opposite.op ⦋q⦌))
  simp

/-! ### Distinguished operators: degeneracy `D₀`, faces, boundaries -/

/-- The 0-th degeneracy operator `D₀ = s₀ × s₀ : (K×L)_q → (K×L)_{q+1}` of EM (2.13). -/
noncomputable def D0op (q : ℕ) : DerivedOp q (q + 1) :=
  Finsupp.single ⟨SimplexCategory.σ 0, SimplexCategory.σ 0⟩ 1

/-- The `i`-th face operator `F_i = δ_i × δ_i : (K×L)_{q+1} → (K×L)_q`. -/
noncomputable def faceOp (q : ℕ) (i : Fin (q + 2)) : DerivedOp (q + 1) q :=
  Finsupp.single ⟨SimplexCategory.δ i, SimplexCategory.δ i⟩ 1

/-- The **last face** `F₀` in EM's `∂ = F₀ − ∂'` decomposition — here the 0-th face `F_0`. -/
noncomputable def lastFaceOp (q : ℕ) : DerivedOp (q + 1) q :=
  faceOp q 0

/-- The **truncated boundary** `∂' = Σ_{i≥1} (-1)^{i-1} F_i` (the part of the boundary omitting the
0-th face), so that the full boundary is `∂ = F₀ − ∂'`. -/
noncomputable def truncBoundaryOp (q : ℕ) : DerivedOp (q + 1) q :=
  ∑ i : Fin (q + 1), ((-1 : ℤ) ^ (i : ℕ)) • faceOp q i.succ

/-- The full simplicial boundary operator `∂ = Σ_i (-1)^i F_i : (K×L)_{q+1} → (K×L)_q`. -/
noncomputable def boundaryOp (q : ℕ) : DerivedOp (q + 1) q :=
  ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • faceOp q i

/-! ### The realized operators agree with the chain-complex data

These tie the formal operators to the actual differentials / maps on `FTwo.obj X`, so the abstract
operator identities below can be transported to statements about `Homotopy.comm`. -/

/-- The realized `i`-th face is the `i`-th face of the diagonal simplicial object: the
horizontal/vertical legs of `⟨δ i, δ i⟩` reassemble into `(diag X).δ i` via naturality of
`X.map (δ i).op`. -/
lemma realize_faceOp (X : BisimplicialObject C) (q : ℕ) (i : Fin (q + 2)) :
    (faceOp q i).realize X = (diag.obj X).δ i := by
  rw [faceOp, realize_single, one_smul, OpLetter.realizeLetter, SimplicialObject.δ, diag_obj_map]
  exact (X.map (SimplexCategory.δ i).op).naturality (SimplexCategory.δ i).op

/-- The realized boundary operator is the differential of `FTwo.obj X`. -/
lemma realize_boundaryOp (X : BisimplicialObject C) (q : ℕ) :
    (boundaryOp q).realize X = (FTwo.obj X).d (q + 1) q := by
  rw [show (FTwo.obj X).d (q + 1) q
      = (AlternatingFaceMapComplex.obj (diag.obj X)).d (q + 1) q from rfl,
    AlternatingFaceMapComplex.obj_d_eq,
    show (boundaryOp q).realize X = realizeAddMonoidHom X (boundaryOp q) from rfl,
    boundaryOp, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, show realizeAddMonoidHom X (faceOp q i) = (faceOp q i).realize X from rfl,
    realize_faceOp]

/-- `∂ = F₀ − ∂'` (EM, just above (2.13)): the full boundary splits as the 0-th face minus the
truncated boundary. -/
lemma boundaryOp_eq (q : ℕ) :
    boundaryOp q = lastFaceOp q - truncBoundaryOp q := by
  rw [boundaryOp, Fin.sum_univ_succ, lastFaceOp, truncBoundaryOp, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_succ, pow_succ, mul_neg, mul_one, neg_zsmul]

/-! ### Algebra of the derived operator `prime`

`prime` is additive and **multiplicative** (`(β∘γ)' = β'∘γ'`), and on faces it shifts the index
(`prime(δ_i) = δ_{i+1}`). Consequently EM's truncated boundary is *literally* the derived operator
of the boundary: `∂' = prime(∂)` (`prime_boundaryOp`). These are exactly what make EM's family
identity `∂'M' = M'∂'` hold — it is just `prime` applied (via `prime_comp`) to the chain-map
condition `∂M = M∂`, with no ad-hoc index juggling. This is why we no longer state a separate
(mis-indexed) `prime_comp_truncBoundary`. -/

@[simp] lemma prime_zero {s q : ℕ} : (0 : DerivedOp s q).prime = 0 := by
  simp [DerivedOp.prime]

lemma prime_add {s q : ℕ} (M N : DerivedOp s q) : (M + N).prime = M.prime + N.prime := by
  simp [DerivedOp.prime, Finsupp.mapDomain_add]

/-- The 0-th coface shift is **multiplicative**: `(g ≫ f)' = g' ≫ f'`. The combinatorial core of
`prime`-multiplicativity (a `SimplexCategory` identity, no `Finsupp`). -/
lemma primeHom_comp {s q r : ℕ} (g : (⦋r⦌ : SimplexCategory) ⟶ ⦋q⦌)
    (f : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    primeHom (g ≫ f) = primeHom g ≫ primeHom f := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply,
    SimplexCategory.len_mk]
  apply Fin.ext
  by_cases hj : (j : ℕ) = 0
  · simp [hj]
  · generalize_proofs h1 h2 h3
    simp only [ite_eq_right hj]
    have hbq : ((SimplexCategory.Hom.toOrderHom g) ⟨(j : ℕ) - 1, h1⟩ : ℕ) < q + 1 := Fin.isLt _
    rw [ite_eq_right (by omega)]
    congr 2
    congr 1
    congr 1
    apply Fin.ext
    set t : ℕ := ↑((SimplexCategory.Hom.toOrderHom g) ⟨(j : ℕ) - 1, h1⟩)
    have ht : t < q + 1 := by simpa [t] using hbq
    have hmin : min (t + 1) (q + 1) = t + 1 := Nat.min_eq_left (Nat.succ_le_of_lt ht)
    simp [t, hmin]

/-- Letter-level multiplicativity of `prime`: `(l₂ ∘ l₁)' = l₂' ∘ l₁'`. -/
lemma OpLetter.primeLetter_compLetter {s q r : ℕ} (l₂ : OpLetter q r) (l₁ : OpLetter s q) :
    (l₂.compLetter l₁).primeLetter = l₂.primeLetter.compLetter l₁.primeLetter := by
  simp only [OpLetter.primeLetter, OpLetter.compLetter, primeHom_comp]

/-- **`prime` is multiplicative** (`(β∘γ)' = β'∘γ'`), so `(MTwo ∘ MOne)' = MTwo' ∘ MOne'`. The key fact
behind EM's `∂'M' = M'∂'`. Reduced to the single–single case `OpLetter.primeLetter_compLetter` by bilinearity
of `comp` and additivity of `prime`. -/
lemma prime_comp {s q r : ℕ} (MTwo : DerivedOp q r) (MOne : DerivedOp s q) :
    (MTwo.comp MOne).prime = MTwo.prime.comp MOne.prime := by
  induction MOne using Finsupp.induction with
  | zero => simp [DerivedOp.comp, DerivedOp.prime]
  | single_add l₁ c₁ f _ _ ih =>
    rw [DerivedOp.comp_add_right, prime_add, ih, prime_add, DerivedOp.comp_add_right]
    congr 1
    clear ih
    induction MTwo using Finsupp.induction with
    | zero => simp [DerivedOp.comp, DerivedOp.prime]
    | single_add l₂ c₂ g _ _ ih₂ =>
      rw [DerivedOp.add_comp, prime_add, ih₂, prime_add, DerivedOp.add_comp]
      congr 1
      simp only [DerivedOp.single_comp_single, DerivedOp.prime, Finsupp.mapDomain_single,
        OpLetter.primeLetter_compLetter]

/-- `primeHom` shifts the face map index: `prime(δ_i) = δ_{i+1}`. The combinatorial core of
`prime_faceOp`. -/
lemma primeHom_δ {q : ℕ} (i : Fin (q + 2)) :
    primeHom (SimplexCategory.δ i) = SimplexCategory.δ i.succ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    SimplexCategory.len_mk]
  simp only [SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  have hj := j.isLt
  simp only [SimplexCategory.len_mk] at hj
  split_ifs <;>
    (try simp_all only [Fin.val_castSucc, Fin.val_succ]) <;> omega

/-- **`prime` shifts faces**: `prime(δ_i) = δ_{i+1}` (prepending the `0`-th vertex pushes the
omitted vertex up by one). -/
lemma prime_faceOp (q : ℕ) (i : Fin (q + 2)) :
    (faceOp q i).prime = faceOp (q + 1) i.succ := by
  simp only [faceOp, DerivedOp.prime, Finsupp.mapDomain_single, OpLetter.primeLetter, primeHom_δ]

/-- `primeHom` shifts the degeneracy map index: `prime(σ_i) = σ_{i+1}` (prepending the `0`-th vertex
pushes the doubled vertex up by one). The degeneracy analog of `primeHom_δ`. -/
lemma primeHom_σ {q : ℕ} (i : Fin (q + 1)) :
    primeHom (SimplexCategory.σ i) = SimplexCategory.σ i.succ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    SimplexCategory.len_mk]
  simp only [SimplexCategory.σ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    Fin.predAboveOrderHom, OrderHom.coe_mk, Fin.predAbove]
  have hj := j.isLt
  simp only [SimplexCategory.len_mk] at hj
  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all only [Fin.val_pred, Fin.coe_castPred] <;> omega

/-- `prime` bundled as an additive hom, so it distributes over `Finset.sum` (`map_sum`) and
`zsmul` (`map_zsmul`). -/
noncomputable def primeAddHom {s q : ℕ} :
    DerivedOp s q →+ DerivedOp (s + 1) (q + 1) where
  toFun := DerivedOp.prime
  map_zero' := prime_zero
  map_add' := prime_add

/-- **`∂' = prime(∂)`** (EM): the truncated boundary is the derived operator of the full boundary.
Note the degree shift — `prime` of the degree-`q` boundary is the truncated boundary at degree
`q+1` (this is the index offset that the literal EM transcription hides). -/
lemma prime_boundaryOp (q : ℕ) :
    (boundaryOp q).prime = truncBoundaryOp (q + 1) := by
  simp only [boundaryOp, truncBoundaryOp]
  rw [show (∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • faceOp q i).prime
      = primeAddHom (∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • faceOp q i) from rfl,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, show primeAddHom (faceOp q i) = (faceOp q i).prime from rfl, prime_faceOp]

/-! ### Core derived-operator identities (EM I.3, used in the (2.13) induction) -/

/-- The 0-th face "eats" the prepended vertex: `δ 0 ≫ primeHom θ = θ ≫ δ 0`. The combinatorial
core of `lastFace_comp_prime`. -/
lemma faceZero_comp_primeHom {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    SimplexCategory.δ (0 : Fin (q + 2)) ≫ primeHom θ
      = θ ≫ SimplexCategory.δ (0 : Fin (s + 2)) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  simp only [primeHom, SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply,
    SimplexCategory.len_mk]
  -- Unfold the two `δ 0` cofaces to `Fin.succAbove 0 = Fin.succ`, then `simp` evaluates the
  -- `primeHom` `if`/`min` (both legs send `j ↦ θ(j) + 1`); the leftover `↑(θ j) ≤ s` is `isLt`.
  dsimp only [SimplexCategory.δ, Fin.succAboveOrderEmb, OrderEmbedding.coe_ofStrictMono,
    Function.Embedding.coeFn_mk]
  simp only [SimplexCategory.mkHom, Fin.succAbove_zero, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, OrderEmbedding.coe_ofStrictMono, Fin.val_succ,
    Nat.add_eq_zero_iff, Fin.val_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    add_tsub_cancel_right, Fin.eta, Nat.add_min_add_right, Nat.add_right_cancel_iff, inf_eq_left]
  have hj := (SimplexCategory.Hom.toOrderHom θ j).isLt
  simp only [SimplexCategory.len_mk] at hj
  omega

/-- **`F₀ M' = M F₀`** (EM, Lemma I.3.3): dropping the bottom face commutes with priming. The one
derived-operator/boundary identity that is *not* a consequence of multiplicativity, since the
outer `F₀` is unprimed. -/
lemma lastFace_comp_prime {s q : ℕ} (M : DerivedOp s q) :
    (lastFaceOp q).comp (M.prime) = M.comp (lastFaceOp s) := by
  induction M using Finsupp.induction with
  | zero => simp [DerivedOp.prime, DerivedOp.comp]
  | single_add l c f _ _ ih =>
    rw [prime_add, DerivedOp.comp_add_right, ih, DerivedOp.add_comp]
    congr 1
    rw [DerivedOp.prime, Finsupp.mapDomain_single, lastFaceOp, faceOp, lastFaceOp, faceOp,
      DerivedOp.single_comp_single, DerivedOp.single_comp_single, mul_one, one_mul]
    congr 1
    simp only [OpLetter.compLetter, OpLetter.primeLetter, faceZero_comp_primeHom]

/-- Post-composition with `D₀` on the right, bundled additively so `map_sum`/`map_zsmul` distribute
it over the boundary sum. -/
private noncomputable def compRightD0 (q : ℕ) :
    DerivedOp (q + 2) (q + 1) →+ DerivedOp (q + 1) (q + 1) where
  toFun M := M.comp (D0op (q + 1))
  map_zero' := by simp [DerivedOp.comp]
  map_add' M N := DerivedOp.add_comp M N _

/-- Pre-composition with `D₀` on the left, bundled additively. -/
private noncomputable def compLeftD0 (q : ℕ) :
    DerivedOp (q + 1) q →+ DerivedOp (q + 1) (q + 1) where
  toFun M := (D0op q).comp M
  map_zero' := by simp [DerivedOp.comp]
  map_add' M N := DerivedOp.comp_add_right (D0op q) M N

/-- The `i ≥ 2` simplicial identity `F_{k+2} D₀ = D₀ F_{k+1}` at the operator level
(`δ_{k+2} ≫ σ_0 = σ_0 ≫ δ_{k+1}`). -/
private lemma faceSuccSucc_comp_D0 (q : ℕ) (k : Fin (q + 1)) :
    (faceOp (q + 1) k.succ.succ).comp (D0op (q + 1))
      = (D0op q).comp (faceOp q k.succ) := by
  rw [faceOp, D0op, D0op, faceOp, DerivedOp.single_comp_single,
    DerivedOp.single_comp_single, mul_one]
  congr 1
  simp only [OpLetter.compLetter]
  congr 1 <;>
    exact SimplexCategory.δ_comp_σ_of_gt (i := k.succ) (j := 0) (by simp [Fin.lt_def])

/-- The two unit faces `F_0 D₀ = F_1 D₀ = 1` (`δ_0 ≫ σ_0 = δ_1 ≫ σ_0 = 𝟙`); used to cancel the
first two terms of `∂ D₀`. -/
lemma face_zero_comp_D0 (q : ℕ) :
    (faceOp (q + 1) (0 : Fin (q + 3))).comp (D0op (q + 1))
      = (Finsupp.single ⟨𝟙 _, 𝟙 _⟩ 1 : DerivedOp (q + 1) (q + 1)) := by
  rw [faceOp, D0op, DerivedOp.single_comp_single, mul_one]
  congr 1

private lemma face_one_comp_D0 (q : ℕ) :
    (faceOp (q + 1) (0 : Fin (q + 2)).succ).comp (D0op (q + 1))
      = (Finsupp.single ⟨𝟙 _, 𝟙 _⟩ 1 : DerivedOp (q + 1) (q + 1)) := by
  rw [faceOp, D0op, DerivedOp.single_comp_single, mul_one]
  congr 1
  simp only [OpLetter.compLetter]
  congr 1 <;> exact SimplexCategory.δ_comp_σ_succ

/-- Simplicial identity `∂ D₀ = D₀ ∂'` at the operator level.

Writing `∂ = F₀ - ∂'`, the terms `F₀ D₀` and `F₁ D₀` both equal the identity, so the remaining
faces assemble to `D₀ ∂'`. -/
lemma boundary_comp_D0 (q : ℕ) :
    (boundaryOp (q + 1)).comp (D0op (q + 1)) =
      (D0op q).comp (truncBoundaryOp q) := by
  have hL : (boundaryOp (q + 1)).comp (D0op (q + 1))
      = ∑ i : Fin (q + 3), ((-1 : ℤ) ^ (i : ℕ)) • (faceOp (q + 1) i).comp (D0op (q + 1)) := by
    rw [boundaryOp,
      show (∑ i : Fin (q + 3), ((-1 : ℤ) ^ (i : ℕ)) • faceOp (q + 1) i).comp (D0op (q + 1))
        = compRightD0 q (∑ i : Fin (q + 3), ((-1 : ℤ) ^ (i : ℕ)) • faceOp (q + 1) i) from rfl,
      map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul (compRightD0 q) _ _
  have hR : (D0op q).comp (truncBoundaryOp q)
      = ∑ k : Fin (q + 1), ((-1 : ℤ) ^ (k : ℕ)) • (D0op q).comp (faceOp q k.succ) := by
    rw [truncBoundaryOp,
      show (D0op q).comp (∑ k : Fin (q + 1), ((-1 : ℤ) ^ (k : ℕ)) • faceOp q k.succ)
        = compLeftD0 q (∑ k : Fin (q + 1), ((-1 : ℤ) ^ (k : ℕ)) • faceOp q k.succ) from rfl,
      map_sum]
    exact Finset.sum_congr rfl fun k _ => map_zsmul (compLeftD0 q) _ _
  rw [hL, hR, Fin.sum_univ_succ, Fin.sum_univ_succ, face_zero_comp_D0, face_one_comp_D0]
  simp only [Fin.val_zero, Fin.val_succ, Nat.zero_add, pow_zero, pow_one, one_smul,
    neg_one_zsmul]
  rw [add_neg_cancel_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [faceSuccSucc_comp_D0]
  congr 1
  rw [pow_succ, pow_succ]
  ring

/-! ### Killing norms with `PInfty`

For the homotopy identity, the relevant norms are the **diagonal** degenerate terms in `D(K×L)`.
They are detected by postcomposing with
`retractionNTwo = PInftyToNormalizedMooreComplex (diag X)`, which kills diagonal degeneracies of the
diagonal simplicial object.

The lemmas in this section package that kill mechanism in the forms used later by the EM
induction. -/

/-- The realization of a **diagonal letter** `⟨θ, θ⟩` is the diagonal map `(diag X).map θ.op`
(`realize_faceOp` generalized off the face case): the horizontal/vertical legs reassemble by
naturality of `X.map θ.op`. -/
lemma realize_diagLetter (X : BisimplicialObject C) {s q : ℕ}
    (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    DerivedOp.realize X (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) = (diag.obj X).map θ.op := by
  rw [realize_single, one_smul, OpLetter.realizeLetter, diag_obj_map]
  exact (X.map θ.op).naturality θ.op

/-- A diagonal degeneracy `⟨θ, θ⟩` with `θ` non-monic is killed by `retractionNTwo`.

Its realization is the diagonal map `(diag X).map θ.op`, and a non-monic `θ` is a simplicial
degeneracy, so `degeneracy_comp_PInfty` applies after factoring `PInfty` through the Moore
inclusion. -/
lemma realize_diagLetter_comp_retractionNTwo_eq_zero_of_not_mono {s q : ℕ} (X : BisimplicialObject C)
    (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) (hθ : ¬ Mono θ) :
    DerivedOp.realize X (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) ≫ (retractionNTwo X).f q = 0 := by
  rw [realize_diagLetter]
  -- `(diag X).map θ.op` is a degeneracy of `diag X` (θ non-mono); factor `PInfty = retr ≫ incl`
  -- and cancel the mono Moore inclusion (Pattern 1).
  have : Mono ((inclusionOfMooreComplexMap (diag.obj X)).f q) := by
    rw [inclusionOfMooreComplexMap_f]; exact Subobject.arrow_mono _
  refine zero_of_comp_mono ((inclusionOfMooreComplexMap (diag.obj X)).f q) ?_
  exact (Category.assoc _ _ _).trans <|
    (congrArg ((diag.obj X).map θ.op ≫ ·)
      ((HomologicalComplex.comp_f _ _ q).symm.trans
        (congrArg (fun φ => HomologicalComplex.Hom.f φ q)
          (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap (diag.obj X))))).trans
      (degeneracy_comp_PInfty (diag.obj X) q θ hθ)

/-- A diagonal degeneracy on the output side kills any composite after `retractionNTwo`.

If `M = ⟨θ, θ⟩ ∘ N` with `θ` non-monic, then `realize M ≫ retractionNTwo = 0`. This is the form
used later, where the norm term is expressed as a diagonal degeneracy postcomposed with an
arbitrary operator. -/
lemma realize_comp_diagLetter_not_mono_comp_retractionNTwo {r s q : ℕ} (X : BisimplicialObject C)
    (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) (hθ : ¬ Mono θ) (N : DerivedOp r s) :
    DerivedOp.realize X (DerivedOp.comp (Finsupp.single (⟨θ, θ⟩ : OpLetter s q) 1) N) ≫
        (retractionNTwo X).f q = 0 := by
  rw [realize_comp, Category.assoc,
    realize_diagLetter_comp_retractionNTwo_eq_zero_of_not_mono X θ hθ, Limits.comp_zero]


end BisimplicialObject

end D5.S3.HomologicalAlgebra.EilenbergZilber
