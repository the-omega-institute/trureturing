/- GID: D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal
   generality: I
   mirror-B: D5/B/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A punctured even set refutes Nathanson's sumset intersection assertion. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#20722; Refuted)
  Direct frozen dependencies: none.
stage_sdiff_infinite: proof_shape: bind-only; consumer: result.
not_basis_of_subset_even: proof_shape: bind-only; consumers: punctured_even_not_maximal, result.
punctured_even_not_maximal: proof_shape: bind-only; consumer: result.
stage_odd_infinite: proof_shape: bind-only; consumer: result.
odd_mem_stage_sumset: proof_shape: bind-only; consumer: result.
Every helper has escape_witness: none and Direct frozen dependencies: none.
The public result has utility: none and is an escape-audit target.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27767.
The four public definitions retain the expressions in issue #20722.
The maximal-nonbasis condition is inlined literally in claim; the proof reuses Mathlib Maximal
through Set.maximal_iff_forall_ssuperset instead of declaring a duplicate predicate.
The sumset is defined over semigroups, including those without an identity, and its zero case is
empty; Mathlib's monoid pointwise natural scalar action has a different zero case.
The positive-index integer family in NathansonProblem12AffineInvariance does not define this
predicate for arbitrary semigroups. No D5 declaration is imported.
Utility kind=none: arbitrary infinite families and unbounded integers; no finite enumeration,
numerical reduction or computational certificate establishes the conclusion.
The proof uses Finite.exists_le, antitone_nat_of_succ_le, Set.Infinite.sdiff,
Set.Infinite.exists_notMem_finite, Set.mem_add and integer parity from pinned Mathlib.
Only the instance S = ℤ, h = 2, A = {n | Even n ∧ n ≠ 2} is needed for the refutation.
-/

import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Fintype.Order
import Mathlib.Order.Minimal
import Mathlib.Algebra.Group.Pointwise.Set.Basic

set_option autoImplicit false

namespace D5.S3.Arith.Additive.NathansonSumsetIntersectionNonmaximal

open scoped Pointwise

variable {S : Type*} [AddCommSemigroup S]

/-- The `h`-fold sumset `hA = {a₁ + ⋯ + a_h : aᵢ ∈ A}` for `h ≥ 1` (`sumset A 0 = ∅` is never used). -/
def sumset (A : Set S) : ℕ → Set S
  | 0 => ∅
  | 1 => A
  | h + 2 => sumset A (h + 1) + A

/-- `A` is a basis of order `h` for `S`: `hA = S`. -/
def IsBasis (h : ℕ) (A : Set S) : Prop := sumset A h = Set.univ

/-- `(A_q)` is decreasing and `A_q ≠ A_{q+1}` for infinitely many `q`. -/
def AsymptoticallyStrictlyDecreasing (A : ℕ → Set S) : Prop :=
  (∀ q, A (q + 1) ⊆ A q) ∧ ∀ N, ∃ q, N ≤ q ∧ A q ≠ A (q + 1)

/-- Problem 2, as a universal assertion over infinite abelian semigroups and orders `h ≥ 1`. -/
def claim : Prop :=
  ∀ (S : Type) [AddCommSemigroup S] [Infinite S] (h : ℕ) (A : Set S), 1 ≤ h →
    ¬ IsBasis h A → ¬ (¬ IsBasis h A ∧ ∀ B : Set S, A ⊂ B → IsBasis h B) →
      ∃ Aq : ℕ → Set S, AsymptoticallyStrictlyDecreasing Aq ∧ (⋂ q, Aq q) = A ∧
        (⋂ q, sumset (Aq q) h) = sumset A h

private def puncturedEven : Set ℤ := {n : ℤ | Even n ∧ n ≠ 2}

private theorem stage_sdiff_infinite {T : Type*} (Aq : ℕ → Set T) (A : Set T)
    (hdec : ∀ q, Aq (q + 1) ⊆ Aq q)
    (hstrict : ∀ N, ∃ q, N ≤ q ∧ Aq q ≠ Aq (q + 1))
    (hinter : (⋂ q, Aq q) = A) (q : ℕ) : (Aq q \ A).Infinite := by
  classical
  intro hfin
  have hanti : Antitone Aq := antitone_nat_of_succ_le hdec
  have hsub : ∀ m, A ⊆ Aq m := by
    intro m x hx
    exact Set.mem_iInter.mp (hinter.symm.subset hx) m
  have hgone : ∀ x : ↥(Aq q \ A), ∃ r, x.val ∉ Aq r := by
    intro x
    by_contra! h
    exact x.property.2 (hinter.subset (Set.mem_iInter.mpr h))
  let r : ↥(Aq q \ A) → ℕ := fun x => Classical.choose (hgone x)
  have hr (x : ↥(Aq q \ A)) : x.val ∉ Aq (r x) := Classical.choose_spec (hgone x)
  have : Finite ↥(Aq q \ A) := hfin.to_subtype
  obtain ⟨M, hM⟩ := Finite.exists_le r
  have heq : ∀ m, max q M ≤ m → Aq m = A := by
    intro m hm
    apply Set.Subset.antisymm
    · intro x hx
      by_contra hxA
      have hxq : x ∈ Aq q := hanti (le_trans (le_max_left q M) hm) hx
      let y : ↥(Aq q \ A) := ⟨x, hxq, hxA⟩
      exact hr y (hanti (le_trans (hM y) (le_trans (le_max_right q M) hm)) hx)
    · exact hsub m
  obtain ⟨m, hm, hne⟩ := hstrict (max q M)
  exact hne ((heq m hm).trans (heq (m + 1) (le_trans hm (Nat.le_succ m))).symm)

private theorem not_basis_of_subset_even {B : Set ℤ} (hB : B ⊆ {n | Even n}) :
    ¬ IsBasis 2 B := by
  intro h
  have h1 : (1 : ℤ) ∈ B + B := by
    change (1 : ℤ) ∈ sumset B 2
    rw [h]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp h1
  have heven : Even (1 : ℤ) := hab ▸ (hB ha).add (hB hb)
  exact Int.not_even_one heven

private theorem punctured_even_not_maximal :
    ¬ Maximal (fun B : Set ℤ => ¬ IsBasis 2 B) puncturedEven := by
  intro h
  have h := Set.maximal_iff_forall_ssuperset.mp h
  apply not_basis_of_subset_even (B := {n : ℤ | Even n}) (fun _ hx => hx)
  apply Classical.not_not.mp (h.2 ?_)
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro hback
  have h2 := hback (show (2 : ℤ) ∈ {n : ℤ | Even n} from even_two)
  exact h2.2 rfl

private theorem stage_odd_infinite (B : Set ℤ) (h : (B \ puncturedEven).Infinite) :
    {n ∈ B | Odd n}.Infinite := by
  apply (h.sdiff (Set.finite_singleton 2)).mono
  rintro n ⟨⟨hnB, hnA⟩, hn2⟩
  refine ⟨hnB, Int.not_even_iff_odd.mp ?_⟩
  intro hn
  exact hnA ⟨hn, by simpa using hn2⟩

private theorem odd_mem_stage_sumset (B : Set ℤ) (hsub : puncturedEven ⊆ B)
    (hodd : {n ∈ B | Odd n}.Infinite) (n : ℤ) (hn : Odd n) : n ∈ sumset B 2 := by
  obtain ⟨b, hb, hbavoid⟩ := hodd.exists_notMem_finite (Set.finite_singleton (n - 2))
  have hne : n - b ≠ 2 := by
    intro heq
    apply hbavoid
    change b = n - 2
    omega
  have heven : Even (n - b) := Int.even_sub'.mpr (by simp [hn, hb.2])
  exact Set.mem_add.mpr ⟨n - b, hsub ⟨heven, hne⟩, b, hb.1, sub_add_cancel n b⟩

theorem result : ¬ claim := by
  intro hclaim
  obtain ⟨Aq, hseq, hinter, hsum⟩ := hclaim ℤ 2 puncturedEven (by decide)
    (not_basis_of_subset_even (fun _ hx => hx.1)) (by
      intro h
      apply punctured_even_not_maximal
      exact Set.maximal_iff_forall_ssuperset.mpr
        ⟨h.1, fun _ hsub => not_not.mpr (h.2 _ hsub)⟩)
  have h1 : (1 : ℤ) ∈ ⋂ q, sumset (Aq q) 2 := by
    apply Set.mem_iInter.mpr
    intro q
    apply odd_mem_stage_sumset (Aq q)
    · intro x hx
      exact Set.mem_iInter.mp (hinter.symm ▸ hx) q
    · exact stage_odd_infinite (Aq q) (stage_sdiff_infinite Aq puncturedEven hseq.1 hseq.2 hinter q)
    · exact odd_one
  have hnot : (1 : ℤ) ∉ sumset puncturedEven 2 := by
    intro hmem
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hmem
    exact Int.not_even_one (hab ▸ ha.1.add hb.1)
  exact hnot (hsum ▸ h1)

end D5.S3.Arith.Additive.NathansonSumsetIntersectionNonmaximal
