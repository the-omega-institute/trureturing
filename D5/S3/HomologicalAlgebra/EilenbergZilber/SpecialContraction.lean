/- GID: D5/S3/HomologicalAlgebra/EilenbergZilber/SpecialContraction
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/EilenbergZilber/SpecialContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Structural cancellation for the recursive normalized Eilenberg–Mac Lane homotopy. -/

/-
Copyright (c) 2026 Jeffrey Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey Li

The frontal and norm algebra declarations below are from
LeanPool/EilenbergZilber/BisimplicialDerivedOp.lean, author release
fd0147a1ffe4f3c14c247574e148893d7cdf8cf6 (LeanPool PR 588).
The legal chain is recorded in Library/HomologicalAlgebra/li2026bisimplicialeilenbergzilber.md.
Retire the transplanted closure when the pinned upstream library supplies equivalent declarations.
-/

import D5.S3.HomologicalAlgebra.EilenbergZilber.BisimplicialNormalized
import D5.S3.HomologicalAlgebra.EilenbergZilber.SpecialContractionShuffle

/-! # Special contractions of the bisimplicial Eilenberg–Zilber homotopy -/

noncomputable section

open CategoryTheory
open AlgebraicTopology AlgebraicTopology.DoldKan CategoryTheory.Limits
open scoped Simplicial

namespace D5.S3.HomologicalAlgebra.EilenbergZilber
namespace BisimplicialObject

/-- An operator is **frontal** (EM) if every letter in its support is frontal in both variables.
This is the property of **derived (primed) operators** — `primeHom` fixes `0`, so any `M.prime` is
frontal in this strong sense (`prime_frontal`). It is what the homotopy identity (2.3) consumes
(via `prime_comp_D0_of_frontal`). -/
private def DerivedOp.Frontal {s q : ℕ} (M : DerivedOp s q) : Prop :=
  ∀ l ∈ M.support, IsFrontalHom l.fst ∧ IsFrontalHom l.snd

/-- The derived operator preserves frontality (EM: `M'` is always frontal, since `primeHom` fixes
`0`). -/
private lemma prime_frontal {s q : ℕ} (M : DerivedOp s q) : (M.prime).Frontal := by
  intro l hl
  have hl' := Finsupp.mapDomain_support hl
  rw [Finset.mem_image] at hl'
  obtain ⟨l', _, rfl⟩ := hl'
  exact ⟨primeHom_frontal _, primeHom_frontal _⟩

/-- **Frontal ⟹ priming commutes with `D₀`** (EM, from Lemma I.3.3: `(β')^* D₀ = D₀ β^*`).
For a frontal operator, `M' ∘ D₀ = D₀ ∘ M`. -/
private lemma prime_comp_D0_of_frontal {s q : ℕ} (M : DerivedOp s q) (hM : M.Frontal) :
    (M.prime).comp (D0op s) = (D0op q).comp M := by
  induction M using Finsupp.induction with
  | zero => simp [DerivedOp.prime, DerivedOp.comp]
  | single_add l c f hlf hc ih =>
    have hl := hM l (by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.notMem_support_iff.mp hlf, add_zero]
      exact hc)
    have hf : DerivedOp.Frontal f := fun l' hl' => hM l' (by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply,
        Finsupp.single_eq_of_ne (by rintro rfl; exact hlf hl'), zero_add,
        ← Finsupp.mem_support_iff]
      exact hl')
    rw [prime_add, DerivedOp.add_comp, DerivedOp.comp_add_right, ih hf]
    congr 1
    rw [DerivedOp.prime, Finsupp.mapDomain_single, D0op, D0op,
      DerivedOp.single_comp_single, DerivedOp.single_comp_single, one_mul, mul_one]
    congr 1
    simp only [OpLetter.compLetter, OpLetter.primeLetter, primeHom_comp_degenZero l.fst hl.1,
      primeHom_comp_degenZero l.snd hl.2]

/-- Composition of frontal `SimplexCategory` maps is frontal (`0 ↦ 0 ↦ 0`). -/
private lemma IsFrontalHom.comp {a b c : ℕ} {f : (⦋a⦌ : SimplexCategory) ⟶ ⦋b⦌}
    {g : (⦋b⦌ : SimplexCategory) ⟶ ⦋c⦌} (hf : IsFrontalHom f) (hg : IsFrontalHom g) :
    IsFrontalHom (f ≫ g) := by
  simp only [IsFrontalHom, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply] at *
  rw [hf, hg]

/-- The zero operator is (vacuously) frontal. -/
private lemma DerivedOp.Frontal.zero {s q : ℕ} : (0 : DerivedOp s q).Frontal := by
  intro l hl
  simp only [Finsupp.support_zero, Finset.notMem_empty] at hl

/-- A single frontal letter gives a frontal operator. -/
private lemma DerivedOp.Frontal.single {s q : ℕ} (l : OpLetter s q) (c : ℤ)
    (hl : IsFrontalHom l.fst ∧ IsFrontalHom l.snd) :
    DerivedOp.Frontal (Finsupp.single l c) := by
  intro l' hl'
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hl')]
  exact hl

/-- Frontality is preserved by negation (same support). -/
private lemma DerivedOp.Frontal.neg {s q : ℕ} {M : DerivedOp s q} (hM : M.Frontal) : (-M).Frontal :=
  fun l hl => hM l (by simpa using hl)

/-- Frontality is preserved by addition (support ⊆ union). -/
private lemma DerivedOp.Frontal.add {s q : ℕ} {M N : DerivedOp s q} (hM : M.Frontal)
    (hN : N.Frontal) :
    (M + N).Frontal := by
  intro l hl
  rcases Finset.mem_union.mp (Finsupp.support_add hl) with h | h
  · exact hM l h
  · exact hN l h

/-- Frontality is preserved by right composition with a single frontal letter. -/
private lemma DerivedOp.Frontal.comp_single {s q r : ℕ} {M : DerivedOp q r} (hM : M.Frontal)
    (l₁ : OpLetter s q) (c₁ : ℤ) (hl₁ : IsFrontalHom l₁.fst ∧ IsFrontalHom l₁.snd) :
    (M.comp (Finsupp.single l₁ c₁)).Frontal := by
  induction M using Finsupp.induction with
  | zero =>
      rw [show DerivedOp.comp (0 : DerivedOp q r) (Finsupp.single l₁ c₁) = 0 from by
        simp [DerivedOp.comp]]
      exact DerivedOp.Frontal.zero
  | single_add l₂ c₂ g hlg hc₂ ih =>
      have hl₂ := hM l₂ (by
        rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same,
          Finsupp.notMem_support_iff.mp hlg, add_zero]
        exact hc₂)
      have hg : DerivedOp.Frontal g := fun l' hl' => hM l' (by
        rw [Finsupp.mem_support_iff, Finsupp.add_apply,
          Finsupp.single_eq_of_ne (by rintro rfl; exact hlg hl'), zero_add,
          ← Finsupp.mem_support_iff]
        exact hl')
      rw [DerivedOp.add_comp, DerivedOp.single_comp_single]
      exact (DerivedOp.Frontal.single (l₂.compLetter l₁) (c₁ * c₂)
        ⟨hl₂.1.comp hl₁.1, hl₂.2.comp hl₁.2⟩).add (ih hg)

/-- `Φ` is frontal: `Φ₀ = 0` is vacuously frontal; the step `Φ_{q+1} = −Φ'_q + h'_{q+1} D₀` is a
sum of a primed operator (frontal by `prime_frontal`, no induction hypothesis needed) and a primed
operator composed with the frontal degeneracy `D₀ = ⟨σ₀,σ₀⟩`. -/
private lemma phiOp_frontal (q : ℕ) : (phiOp q).Frontal := by
  cases q with
  | zero => exact DerivedOp.Frontal.zero
  | succ q =>
      have hσ : IsFrontalHom (SimplexCategory.σ (0 : Fin (q + 1 + 1))) := by
        simp [IsFrontalHom, SimplexCategory.σ, Fin.predAbove]
      rw [phiOp, D0op]
      exact ((prime_frontal _).neg).add ((prime_frontal _).comp_single _ 1 ⟨hσ, hσ⟩)

/-- A `subtraction` convenience: `IsNorm M → IsNorm N → IsNorm (M - N)`. -/
private lemma IsNorm.sub {s q : ℕ} {M N : DerivedOp s q} (hM : IsNorm M) (hN : IsNorm N) :
    IsNorm (M - N) := by rw [sub_eq_add_neg]; exact hM.add hN.neg

/-- A norm absorbs arbitrary right composition (the degeneracy stays on the output side). -/
private lemma IsNorm.comp_right {s s' q : ℕ} {M : DerivedOp s q} (hM : IsNorm M)
    (N : DerivedOp s' s) :
    IsNorm (M.comp N) := by
  induction hM generalizing s' with
  | zero => rw [DerivedOp.zero_comp]; exact IsNorm.zero
  | add _ _ ihM ihN => rw [DerivedOp.add_comp]; exact (ihM N).add (ihN N)
  | neg _ ihM => rw [DerivedOp.neg_comp]; exact (ihM N).neg
  | diagDegen θ hθ N₀ => rw [DerivedOp.comp_assoc]; exact IsNorm.diagDegen θ hθ _

private noncomputable def diagOp (n : ℕ) (i : Fin (n + 1)) : DerivedOp n (n + 1) :=
  Finsupp.single (diagLetter i) 1

private lemma prime_diagOp (n : ℕ) (i : Fin (n + 1)) :
    (diagOp n i).prime = diagOp (n + 1) i.succ := by
  simp only [diagOp, DerivedOp.prime, Finsupp.mapDomain_single, diagLetter,
    OpLetter.primeLetter, primeHom_σ]

private lemma D0_comp_diagOp (n : ℕ) (i : Fin (n + 1)) :
    (D0op (n + 1)).comp (diagOp n i) = (diagOp n i).prime.comp (D0op n) := by
  rw [prime_diagOp, D0op, D0op, diagOp, diagOp, DerivedOp.single_comp_single,
    DerivedOp.single_comp_single]
  have hs := SimplexCategory.σ_comp_σ (Fin.zero_le i)
  have hz : (0 : Fin (n + 1)).castSucc = 0 := Fin.ext rfl
  rw [hz] at hs
  simp only [diagLetter, OpLetter.compLetter, hs]

private lemma hOp_diagOp_isNorm (n : ℕ) (i : Fin (n + 1)) :
    IsNorm ((hOp (n + 1)).comp (diagOp n i)) :=
  hOp_comp_ordered_repeat (diagLetter i) 1 i i le_rfl (repeats_sigma n i) (repeats_sigma n i)

private lemma phiOp_diagOp_isNorm (n : ℕ) (i : Fin (n + 1)) :
    IsNorm ((phiOp (n + 1)).comp (diagOp n i)) := by
  have expand (n : ℕ) (i : Fin (n + 1)) :
      (phiOp (n + 1)).comp (diagOp n i) =
        -((phiOp n).prime.comp (diagOp n i)) +
          (((hOp (n + 1)).comp (diagOp n i)).prime).comp (D0op n) := by
    rw [phiOp, DerivedOp.add_comp, DerivedOp.neg_comp, DerivedOp.comp_assoc,
      D0_comp_diagOp, ← DerivedOp.comp_assoc, ← prime_comp]
  have first (n : ℕ) : IsNorm ((phiOp n).prime.comp (diagOp n 0)) := by
    change IsNorm ((phiOp n).prime.comp (D0op n))
    rw [prime_comp_D0_of_frontal _ (phiOp_frontal n)]
    exact IsNorm.diagDegen _ (sigma_not_mono 0) _
  induction n with
  | zero =>
    rw [show i = 0 from Fin.ext (by have := i.isLt; omega), expand]
    exact (first 0).neg.add ((hOp_diagOp_isNorm 0 0).prime.comp_right _)
  | succ n ih =>
    rw [expand]
    refine IsNorm.add ?_ ((hOp_diagOp_isNorm (n + 1) i).prime.comp_right _)
    refine IsNorm.neg ?_
    refine Fin.cases (first (n + 1)) (fun j => ?_) i
    rw [← prime_diagOp, ← prime_comp]
    exact (ih j).prime

/-- Every monotone map from a longer simplex to a shorter one identifies an
adjacent pair, since otherwise strict monotonicity would give an injection. -/
private lemma exists_repeat_succ {n : ℕ} (f : (⦋n + 1⦌ : SimplexCategory) ⟶ ⦋n⦌) :
    ∃ i : Fin (n + 1), Repeats f i := by
  by_contra! h
  have hinj : Function.Injective f.toOrderHom :=
    (Fin.strictMono_iff_lt_succ.mpr fun i =>
      lt_of_le_of_ne (f.toOrderHom.monotone (Fin.castSucc_le_succ i)) (h i)).injective
  simpa only [SimplexCategory.len_mk, Fintype.card_fin, Nat.add_le_add_iff_right,
    Nat.not_succ_le_self] using Fintype.card_le_of_injective _ hinj

private def OrderedRepeats {s n : ℕ} (l : OpLetter s n) : Prop :=
  ∃ j k : Fin n, j ≤ k ∧ Repeats l.fst j ∧ Repeats l.snd k

private lemma phiOp_ordered_repeats (n : ℕ) :
    ∀ l ∈ (phiOp n).support, OrderedRepeats l := by
  induction n with
  | zero => simp [phiOp]
  | succ n ih =>
    intro l hl
    rw [phiOp] at hl
    rcases Finset.mem_union.mp (Finsupp.support_add hl) with h | h
    · rw [Finsupp.support_neg] at h
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support h)
      obtain ⟨j, k, hjk, hf, hg⟩ := ih a ha
      exact ⟨j.succ, k.succ, Fin.succ_le_succ_iff.mpr hjk, hf.prime, hg.prime⟩
    · rw [D0op, DerivedOp.comp_single_right] at h
      simp only [one_mul] at h
      change l ∈ (Finsupp.mapDomain (fun a => a.compLetter (diagLetter 0))
        ((hOp (n + 1)).prime)).support at h
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support h)
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
      have hf : Repeats ((b.primeLetter.compLetter (diagLetter 0)).fst) 0 := by
        change Repeats (primeHom b.fst ≫ SimplexCategory.σ 0) 0
        rw [primeHom_comp_degenZero b.fst (hOp_horizontal_frontal _ b hb)]
        exact (repeats_sigma (n + 1) 0).comp b.fst
      obtain ⟨k, hk⟩ := exists_repeat_succ ((b.primeLetter.compLetter (diagLetter 0)).snd)
      exact ⟨0, k, Fin.zero_le _, hf, hk⟩

private lemma hOp_comp_phiOp_isNorm (n : ℕ) : IsNorm ((hOp (n + 1)).comp (phiOp n)) := by
  have h (M : DerivedOp n (n + 1)) (hM : ∀ l ∈ M.support, OrderedRepeats l) :
      IsNorm ((hOp (n + 1)).comp M) := by
    induction M using Finsupp.induction with
    | zero => simpa [DerivedOp.comp] using (IsNorm.zero : IsNorm (0 : DerivedOp n (n + 1)))
    | single_add l c M hl hc ih =>
      have H : (Finsupp.single l c + M).support = insert l M.support := by
        rw [Finsupp.support_add_eq]
        · rw [Finsupp.support_single l hc, Finset.singleton_union]
        · simpa [Finsupp.support_single l hc] using hl
      rw [H] at hM
      obtain ⟨j, k, hjk, hj, hk⟩ := hM l (Finset.mem_insert_self _ _)
      rw [DerivedOp.comp_add_right]
      exact (hOp_comp_ordered_repeat l c j k hjk hj hk).add
        (ih (fun a ha => hM a (Finset.mem_insert_of_mem ha)))
  exact h _ (phiOp_ordered_repeats n)

private lemma phiOp_square_step (n : ℕ) :
    (phiOp (n + 2)).comp (phiOp (n + 1)) =
      ((phiOp (n + 1)).comp (phiOp n)).prime -
        (((phiOp (n + 1)).comp (hOp (n + 1))).prime).comp (D0op (n + 1)) +
        (((hOp (n + 2)).comp (phiOp (n + 1))).prime).comp (D0op (n + 1)) := by
  conv_lhs => rw [phiOp]
  rw [DerivedOp.add_comp, DerivedOp.neg_comp, DerivedOp.comp_assoc,
    ← prime_comp_D0_of_frontal _ (phiOp_frontal (n + 1)),
    ← DerivedOp.comp_assoc, ← prime_comp]
  congr 1
  conv_lhs => arg 1; arg 2; rw [phiOp]
  rw [DerivedOp.comp_add_right, DerivedOp.comp_neg, ← DerivedOp.comp_assoc, ← prime_comp,
    ← prime_comp, neg_add, neg_neg, sub_eq_add_neg]

private lemma phiOp_square_isNorm (n : ℕ) : IsNorm ((phiOp (n + 1)).comp (phiOp n)) := by
  induction n with
  | zero => simpa [phiOp, DerivedOp.comp] using (IsNorm.zero : IsNorm (0 : DerivedOp 0 2))
  | succ n ih =>
    rw [phiOp_square_step]
    exact (ih.prime.sub ((phiOp_comp_hOp_isNorm (n + 1)).prime.comp_right _)).add
      ((hOp_comp_phiOp_isNorm (n + 1)).prime.comp_right _)


universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma vanishes_of_diagOp (X : BisimplicialObject C) {n m : ℕ}
    (M : DerivedOp (n + 1) m) (h : ∀ i : Fin (n + 1), IsNorm (M.comp (diagOp n i))) :
    DegeneraciesVanish (X := diag.obj X) (M.realize X ≫ (retractionNTwo X).f m) := by
  intro i
  have h' := (h i).kill X
  rw [realize_comp, Category.assoc, diagOp, diagLetter,
    realize_diagLetter X (SimplexCategory.σ i)] at h'
  exact h'

private lemma absorb_projector (X : BisimplicialObject C) {n m : ℕ}
    (M : DerivedOp n m)
    (h : DegeneraciesVanish (X := diag.obj X) (M.realize X ≫ (retractionNTwo X).f m)) :
    (retractionNTwo X).f n ≫ (inclusionNTwo X).f n ≫
      M.realize X ≫ (retractionNTwo X).f m = M.realize X ≫ (retractionNTwo X).f m := by
  have hp := congrArg (fun f => f.f n)
    (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap (diag.obj X))
  change ((retractionNTwo X ≫ inclusionNTwo X).f n) = (PInfty (X := diag.obj X)).f n at hp
  rw [HomologicalComplex.comp_f] at hp
  rw [← Category.assoc ((retractionNTwo X).f n), hp]
  have hq := (degeneraciesVanish_iff_QInfty_f_comp _).mp h
  have key := congrArg (fun f => f ≫ M.realize X ≫ (retractionNTwo X).f m)
    (PInfty_f_add_QInfty_f (X := diag.obj X) n)
  rwa [Preadditive.add_comp, hq, add_zero, Category.id_comp] at key

private lemma absorb_phi (X : BisimplicialObject C) (n : ℕ) :
    (retractionNTwo X).f n ≫ (inclusionNTwo X).f n ≫
      (phiOp n).realize X ≫ (retractionNTwo X).f (n + 1) =
      (phiOp n).realize X ≫ (retractionNTwo X).f (n + 1) := by
  apply absorb_projector
  cases n with
  | zero => trivial
  | succ n => exact vanishes_of_diagOp X _ (phiOp_diagOp_isNorm n)

private lemma absorb_h (X : BisimplicialObject C) (n : ℕ) :
    (retractionNTwo X).f n ≫ (inclusionNTwo X).f n ≫
      (hOp n).realize X ≫ (retractionNTwo X).f n =
      (hOp n).realize X ≫ (retractionNTwo X).f n := by
  apply absorb_projector
  cases n with
  | zero => trivial
  | succ n => exact vanishes_of_diagOp X _ (hOp_diagOp_isNorm n)

private lemma phiHomNorm_step (X : BisimplicialObject C) (n : ℕ) :
    phiHomNorm X n (n + 1) = (inclusionNTwo X).f n ≫
      (phiOp n).realize X ≫ (retractionNTwo X).f (n + 1) := by
  rw [phiHomNorm, dif_pos rfl, eqToHom_refl, Category.id_comp]

private lemma normalizedAW_shuffle_f (X : BisimplicialObject C) (n : ℕ) :
    (normalizedAlexanderWhitney X ≫ normalizedShuffleMap X).f n =
      (inclusionNTwo X).f n ≫ (hOp n).realize X ≫ (retractionNTwo X).f n := by
  rw [normalizedAW_shuffle_eq, HomologicalComplex.comp_f, HomologicalComplex.comp_f, realize_hOp]

/-- The recursive normalized Eilenberg–Mac Lane homotopy used in the
bisimplicial Eilenberg–Zilber equivalence satisfies the three side conditions
of a special contraction, in every degree. -/
theorem normalized_special_contraction (X : BisimplicialObject C) (n : ℕ) :
    (normalizedShuffleMap X).f n ≫ phiHomNorm X n (n + 1) = 0 ∧
      phiHomNorm X n (n + 1) ≫ (normalizedAlexanderWhitney X).f (n + 1) = 0 ∧
      phiHomNorm X n (n + 1) ≫ phiHomNorm X (n + 1) (n + 2) = 0 := by
  let S := normalizedShuffleMap X
  let A := normalizedAlexanderWhitney X
  let K := A ≫ S
  have side₁ : K.f n ≫ phiHomNorm X n (n + 1) = 0 := by
    rw [show K.f n = (A ≫ S).f n from rfl, normalizedAW_shuffle_f, phiHomNorm_step]
    simp only [Category.assoc, absorb_phi]
    rw [← Category.assoc ((hOp n).realize X), ← realize_comp,
      (phiOp_comp_hOp_isNorm n).kill X, comp_zero]
  have side₂ : phiHomNorm X n (n + 1) ≫ K.f (n + 1) = 0 := by
    rw [show K.f (n + 1) = (A ≫ S).f (n + 1) from rfl, normalizedAW_shuffle_f, phiHomNorm_step]
    simp only [Category.assoc, absorb_h]
    rw [← Category.assoc ((phiOp n).realize X), ← realize_comp,
      (hOp_comp_phiOp_isNorm n).kill X, comp_zero]
  have sa (k : ℕ) : S.f k ≫ A.f k = 𝟙 _ := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun f => f.f k) (normalizedShuffle_alexanderWhitney X)
  have sk : S.f n ≫ K.f n = S.f n := by
    change S.f n ≫ (A ≫ S).f n = S.f n
    rw [HomologicalComplex.comp_f, ← Category.assoc, sa, Category.id_comp]
  have ka : K.f (n + 1) ≫ A.f (n + 1) = A.f (n + 1) := by
    change (A ≫ S).f (n + 1) ≫ A.f (n + 1) = A.f (n + 1)
    rw [HomologicalComplex.comp_f, Category.assoc, sa, Category.comp_id]
  change S.f n ≫ phiHomNorm X n (n + 1) = 0 ∧
    phiHomNorm X n (n + 1) ≫ A.f (n + 1) = 0 ∧
    phiHomNorm X n (n + 1) ≫ phiHomNorm X (n + 1) (n + 2) = 0
  refine ⟨?_, ?_, ?_⟩
  · rw [← sk, Category.assoc, side₁, comp_zero]
  · rw [← ka, ← Category.assoc, side₂, zero_comp]
  · rw [phiHomNorm_step, phiHomNorm_step]
    simp only [Category.assoc, absorb_phi]
    rw [← Category.assoc ((phiOp n).realize X), ← realize_comp,
      (phiOp_square_isNorm n).kill X, comp_zero]

end BisimplicialObject
end D5.S3.HomologicalAlgebra.EilenbergZilber
