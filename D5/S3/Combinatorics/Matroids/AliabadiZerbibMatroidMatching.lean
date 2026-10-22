/- GID: D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: none
   digest: A sparse paving integer matroid need not be matched to itself. -/

/- admission_basis: open-problem-resolution (#19681; Refuted)
   utility: none; the delivered content is the symbolic family for all n,s >= 2.
   Module escape_witness: allowed_exchange and extend_avoiding construct punctured;
   family_sparse_paving supplies its sparse-paving property for all n,s >= 2.
   These facts are consumed by result and survive the binding-only bypass test.
   Direct frozen dependencies: none (all imports are pinned Mathlib).
   The source predicates and claim use the expressions fixed by #19681.
   Interval sets and their increasing enumeration use Mathlib expressions directly.
   The four-slot escape audit for result is unfinished under
   https://github.com/the-omega-institute/trureturing/issues/20096.
   result declaration statement_id:
   sha256:08172161640aab569dd7cc5be8f2d63f95a2c9b71e810ef46d1678fc3434f726.
   Missing: source-realization bridge, enrolled lawful readout, whole-family
   variation/sensitivity and observational-dependence evidence, continuation record.
   No declared_validated registration is claimed. The issue also inventories
   IsPaving, IsSparsePaving, BasesMatched, IsMatchedTo and claim as source definitions.
   The proof-shape table expands same-delivery helpers; generated proof auxiliaries
   inherit their authored owner's classification. Predicate definitions are marked
   bind-only because they encode source conditions rather than assert new facts.
   Consumer edges come from compiled values with generated auxiliaries expanded.
   Ground/base projections, ranks, interval arithmetic and the matching obstruction
   have binding/normalization bypasses; their mere use of punctured does not
   provide an escape witness. Each content row identifies its live mathematical fact.

| module | declaration | proof_shape | escape_witness | consumers | direct frozen dependencies | registration status |
| --- | --- | --- | --- | --- | --- | --- |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.IsPaving | bind-only | none (binding/normalization) | IsSparsePaving, family_sparse_paving | none | not a theorem |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.IsSparsePaving | bind-only | none (binding/normalization) | claim | none | not a theorem |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.BasesMatched | bind-only | none (binding/normalization) | IsMatchedTo, family_not_matched, no_matching_basis | none | not a theorem |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.IsMatchedTo | bind-only | none (binding/normalization) | claim, family_not_matched, result | none | not a theorem |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.claim | bind-only | none (binding/normalization) | result | none | not a theorem |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.allowed_exchange | content | allowed_exchange: the n-subsets other than H satisfy basis exchange | punctured | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.extend_avoiding | content | extend_avoiding: every smaller ground subset extends to an allowed n-base | punctured, punctured_dual_small_indep, punctured_small_indep | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured | content | allowed_exchange and extend_avoiding: construction of the one-deleted-base matroid | family_finite, family_not_matched, family_sparse_paving, family_zero, initial_base, no_matching_basis, punctured_base, punctured_dual_base, punctured_dual_paving, punctured_dual_rank, punctured_dual_small_indep, punctured_ground, punctured_loopless, punctured_paving, punctured_rank, punctured_small_indep, result | none | not a theorem |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_ground | bind-only | none (binding/normalization) | family_zero, punctured_dual_base | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_base | bind-only | none (binding/normalization) | family_base, punctured_dual_base, punctured_rank | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_small_indep | content | extend_avoiding: every smaller ground subset extends to an allowed n-base | punctured_loopless, punctured_paving | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_rank | bind-only | none (binding/normalization) | family_rank, punctured_paving | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_paving | content | extend_avoiding: every smaller ground subset extends to an allowed n-base | family_sparse_paving | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_dual_base | bind-only | none (binding/normalization) | punctured_dual_rank, punctured_dual_small_indep | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_dual_small_indep | content | extend_avoiding: every smaller ground subset extends to an allowed n-base | punctured_dual_paving | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_dual_rank | bind-only | none (binding/normalization) | punctured_dual_paving | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_dual_paving | content | extend_avoiding: every smaller ground subset extends to an allowed n-base | family_sparse_paving | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_loopless | content | extend_avoiding: every smaller ground subset extends to an allowed n-base | family_loopless | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.ground_card | bind-only | none (binding/normalization) | family_base, family_finite, family_loopless, family_not_matched, family_rank, family_sparse_paving, family_zero, initial_base, no_matching_basis | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.hole_card | bind-only | none (binding/normalization) | family_base, family_finite, family_loopless, family_not_matched, family_rank, family_sparse_paving, family_zero, initial_base, no_matching_basis, result | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.hole_subset | bind-only | none (binding/normalization) | family_base, family_finite, family_loopless, family_not_matched, family_rank, family_sparse_paving, family_zero, initial_base, no_matching_basis, result | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.family_base | bind-only | none (binding/normalization) | initial_base, no_matching_basis | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.family_finite | bind-only | none (binding/normalization) | result | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.family_loopless | content | extend_avoiding: every smaller ground subset extends to an allowed n-base | result | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.family_rank | bind-only | none (binding/normalization) | result | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.family_sparse_paving | content | extend_avoiding: every smaller ground subset extends to an allowed n-base | result | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.initial_injective | bind-only | none (binding/normalization) | family_not_matched | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.initial_range | bind-only | none (binding/normalization) | initial_base, no_matching_basis | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.initial_base | bind-only | none (binding/normalization) | family_not_matched | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.forced_target | bind-only | none (binding/normalization) | no_matching_basis | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.no_matching_basis | bind-only | none (binding/normalization) | family_not_matched | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.family_not_matched | bind-only | none (binding/normalization) | result | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.family_zero | bind-only | none (binding/normalization) | result | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.result | content | allowed_exchange and extend_avoiding in punctured, together with family_sparse_paving for all n,s >= 2 | settlement | none | unfinished #20096 |

   The one-deleted-base construction is a finite specialization of tightening;
   no novelty is claimed for the construction. The broader apnelson1/Matroid
   constructors at rev 8ece6307a54854484c9b5fa40b9ed3c5ccc8e42b use different
   Lean and Mathlib pins, so they cannot be imported at the local pins.
-/

import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Set.Card
import Mathlib.Tactic.NormNum
import Mathlib.Order.SuccPred.Int
import Mathlib.Order.Interval.Set.Fin
import Mathlib.Data.Nat.Cast.SetInterval
import Mathlib.Algebra.Order.Interval.Set.Monoid
import Mathlib.Algebra.Order.Interval.Set.SuccPred

/-! Binding conventions for M. Aliabadi and S. Zerbib, "Matchings in matroids over abelian groups", arXiv:2202.07719v3
(J. Algebraic Combin. 2024): matroids over an abelian group `G` (ground set a subset of `G`), paving and sparse paving
matroids, matchings of ordered bases and of matroids (Definition 1.3), and Question 2.7: "Let G be an abelian
torsion-free group. Let M be a matroid over G and N be a sparse paving matroid over G, both of the same rank n, so that
|E(M)| = |E(N)| − 1 or |E(M)| = |E(N)|. If 0 ∉ E(N), is M matched to N?" -/

namespace D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching

variable {G : Type*} [AddCommGroup G]

/-- A matroid of rank `n` is paving if every `(n − 1)`-subset of its ground set is independent. -/
def IsPaving (M : Matroid G) : Prop :=
  ∀ X ⊆ M.E, X.encard + 1 = M.eRank → M.Indep X

/-- `M` is sparse paving if `M` and its dual `M✶` are both paving. -/
def IsSparsePaving (M : Matroid G) : Prop :=
  IsPaving M ∧ IsPaving M✶

/-- Definition 1.3 (1): ordered bases `(a₁, …, aₙ)` of `M` and `(b₁, …, bₙ)` of `N` are matched if
`aᵢ + bᵢ ∉ E(M)` for all `i`. -/
def BasesMatched (M : Matroid G) {n : ℕ} (a b : Fin n → G) : Prop :=
  ∀ i, a i + b i ∉ M.E

/-- Definition 1.3 (2): `M` is matched to `N` if for every ordered basis of `M` there is an ordered basis of `N`
matched to it. -/
def IsMatchedTo (M N : Matroid G) : Prop :=
  ∀ n : ℕ, ∀ a : Fin n → G, Function.Injective a → M.IsBase (Set.range a) →
    ∃ b : Fin n → G, Function.Injective b ∧ N.IsBase (Set.range b) ∧ BasesMatched M a b

/-- Question 2.7, as a statement whose truth is asked: for every torsion-free abelian group `G` and finite loopless
matroids `M`, `N` over `G` of the same positive rank, with `N` sparse paving, `|E(M)| = |E(N)| − 1` or
`|E(M)| = |E(N)|`, and `0 ∉ E(N)`, `M` is matched to `N`. -/
def claim : Prop :=
  ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (M N : Matroid G), M.Finite → N.Finite →
    M.Loopless → N.Loopless → 0 < M.eRank → M.eRank = N.eRank → IsSparsePaving N →
    (M.E.ncard + 1 = N.E.ncard ∨ M.E.ncard = N.E.ncard) → (0 : G) ∉ N.E → IsMatchedTo M N

open Set
section Generic
variable {α : Type*} {E H B C I : Set α} {n : ℕ}

/- The deleted-base construction is a specialization of tightening. The broader third-party
   construction is Matroid.tighten / Matroid.finiteRankSparsePavingOn in apnelson1/Matroid,
   rev 8ece6307a54854484c9b5fa40b9ed3c5ccc8e42b. Its toolchain and Mathlib pin differ
   from the local environment. No novelty is claimed for this matroid construction. -/
private lemma allowed_exchange (hE : E.Finite) (hH : H.ncard = n) :
    Matroid.ExchangeProperty (fun B : Set α => B ⊆ E ∧ B.ncard = n ∧ B ≠ H) := by
  intro B C hB hC e he
  have hBfin := hE.subset hB.1
  have hCB : ¬ C ⊆ B := by
    intro h
    have heq : C = B := Set.eq_of_subset_of_ncard_le h (by omega) hBfin
    exact he.2 (heq ▸ he.1)
  obtain ⟨f, hfC, hfB⟩ := Set.not_subset.mp hCB
  have hc : (insert f (B \ {e})).ncard = n := by
    rw [Set.ncard_exchange hfB he.1, hB.2.1]
  by_cases hswap : insert f (B \ {e}) = H
  · have hCH : ¬ C ⊆ H := by
      intro h
      exact hC.2.2 (Set.eq_of_subset_of_ncard_le h (by omega) (hE.subset (by
        rw [← hswap]; exact insert_subset (hC.1 hfC) (sdiff_subset.trans hB.1))))
    obtain ⟨g, hgC, hgH⟩ := Set.not_subset.mp hCH
    have hgB : g ∉ B := by
      intro hg
      have hge : g ≠ e := ne_of_mem_of_not_mem hgC he.2
      exact hgH (hswap ▸ (mem_insert_of_mem f ⟨hg, hge⟩))
    refine ⟨g, ⟨hgC, hgB⟩, insert_subset (hC.1 hgC) (sdiff_subset.trans hB.1), ?_, ?_⟩
    · rw [Set.ncard_exchange hgB he.1, hB.2.1]
    · intro hh; exact hgH (hh ▸ mem_insert g _)
  · exact ⟨f, ⟨hfC, hfB⟩, insert_subset (hC.1 hfC) (sdiff_subset.trans hB.1), hc, hswap⟩

/- Finite cardinal form of the one-exchange extension argument used by
   Matroid.IsLawfulTightening.exists_notMem_between in the same upstream source. -/
private lemma extend_avoiding (hE : E.Finite) (hH : H ⊆ E) (hcH : H.ncard = n)
    (hn : n < E.ncard) (hI : I ⊆ E) (hcI : I.ncard < n) :
    ∃ B, I ⊆ B ∧ B ⊆ E ∧ B.ncard = n ∧ B ≠ H := by
  obtain ⟨B, hIB, hBE, hcB⟩ := Set.exists_subsuperset_card_eq hI hcI.le hn.le
  by_cases hBH : B = H
  · subst B
    obtain ⟨e, heE, heH⟩ := Set.sdiff_nonempty_of_ncard_lt_ncard (lt_of_eq_of_lt hcH hn) (hE.subset hH)
    obtain ⟨f, hfH, hfI⟩ := Set.sdiff_nonempty_of_ncard_lt_ncard (Nat.lt_of_lt_of_eq hcI hcH.symm) (hE.subset hI)
    refine ⟨insert e (H \ {f}), ?_, insert_subset heE (sdiff_subset.trans hH), ?_, ?_⟩
    · intro x hx; exact mem_insert_of_mem e ⟨hIB hx, by rintro rfl; exact hfI hx⟩
    · rw [Set.ncard_exchange heH hfH, hcH]
    · intro hh; exact heH (hh ▸ mem_insert e _)
  · exact ⟨B, hIB, hBE, hcB, hBH⟩

private noncomputable def punctured (E H : Set α) (n : ℕ) (hE : E.Finite)
    (hH : H ⊆ E) (hcH : H.ncard = n) (hn : 0 < n) (hEn : n < E.ncard) : Matroid α :=
  Matroid.ofExistsFiniteIsBase E (fun B => B ⊆ E ∧ B.ncard = n ∧ B ≠ H)
    (by
      obtain ⟨B, -, hBE, hcB, hBH⟩ := extend_avoiding hE hH hcH hEn
        (Set.empty_subset E) (by simpa using hn)
      exact ⟨B, ⟨hBE, hcB, hBH⟩, hE.subset hBE⟩)
    (allowed_exchange hE hcH) (fun _ h => h.1)

variable (hE : E.Finite) (hH : H ⊆ E) (hcH : H.ncard = n)
    (hn : 0 < n) (hEn : n < E.ncard)

@[simp] private lemma punctured_ground : (punctured E H n hE hH hcH hn hEn).E = E := by rfl

@[simp] private lemma punctured_base (B : Set α) :
    (punctured E H n hE hH hcH hn hEn).IsBase B ↔ B ⊆ E ∧ B.ncard = n ∧ B ≠ H := by rfl

private lemma punctured_small_indep (hI : I ⊆ E) (hcI : I.ncard < n) :
    (punctured E H n hE hH hcH hn hEn).Indep I := by
  obtain ⟨B, hIB, hBE, hcB, hBH⟩ := extend_avoiding hE hH hcH hEn hI hcI
  exact Matroid.indep_iff.mpr ⟨B, ⟨hBE, hcB, hBH⟩, hIB⟩

private lemma punctured_rank : (punctured E H n hE hH hcH hn hEn).eRank = n := by
  obtain ⟨B, hB⟩ := (punctured E H n hE hH hcH hn hEn).exists_isBase
  have hb := (punctured_base hE hH hcH hn hEn B).mp hB
  rw [← hB.encard_eq_eRank, ← (hE.subset hb.1).cast_ncard_eq, hb.2.1]

private lemma punctured_paving :
    IsPaving (punctured E H n hE hH hcH hn hEn) := by
  intro X hX hcard
  have hXfin := hE.subset hX
  rw [punctured_rank hE hH hcH hn hEn, ← hXfin.cast_ncard_eq] at hcard
  have hc : X.ncard < n := by
    have : X.ncard + 1 = n := by exact ENat.natCast_inj.mp hcard
    exact Nat.lt_of_succ_le this.le
  exact punctured_small_indep hE hH hcH hn hEn hX hc

private lemma punctured_dual_base {s : ℕ} (hEs : E.ncard = n+s) (B : Set α) :
    (punctured E H n hE hH hcH hn hEn)✶.IsBase B ↔
      B ⊆ E ∧ B.ncard = s ∧ B ≠ E \ H := by
  simp only [Matroid.dual_isBase_iff', punctured_base, punctured_ground]
  constructor
  · rintro ⟨⟨hsub, hcard, hneq⟩, hBE⟩
    refine ⟨hBE, ?_, ?_⟩
    · have := Set.ncard_sdiff_add_ncard_of_subset hBE hE
      omega
    · intro hh
      apply hneq
      rw [hh, Set.sdiff_sdiff_cancel_left hH]
  · rintro ⟨hBE, hcard, hneq⟩
    refine ⟨⟨sdiff_subset, ?_, ?_⟩, hBE⟩
    · have := Set.ncard_sdiff_add_ncard_of_subset hBE hE
      omega
    · intro hh
      apply hneq
      rw [← hh, Set.sdiff_sdiff_cancel_left hBE]

private lemma punctured_dual_small_indep {s : ℕ} (hEs : E.ncard = n+s)
    (hI : I ⊆ E) (hcI : I.ncard < s) :
    (punctured E H n hE hH hcH hn hEn)✶.Indep I := by
  have hK : (E \ H).ncard = s := by
    have := Set.ncard_sdiff_add_ncard_of_subset hH hE
    omega
  obtain ⟨B, hIB, hBE, hcB, hBH⟩ := extend_avoiding hE sdiff_subset hK
    (by omega : s < E.ncard) hI hcI
  exact Matroid.indep_iff.mpr ⟨B,
    (punctured_dual_base hE hH hcH hn hEn hEs B).mpr ⟨hBE, hcB, hBH⟩, hIB⟩

private lemma punctured_dual_rank {s : ℕ} (hEs : E.ncard = n+s) :
    (punctured E H n hE hH hcH hn hEn)✶.eRank = s := by
  obtain ⟨B, hB⟩ := (punctured E H n hE hH hcH hn hEn)✶.exists_isBase
  have hb := (punctured_dual_base hE hH hcH hn hEn hEs B).mp hB
  rw [← hB.encard_eq_eRank, ← (hE.subset hb.1).cast_ncard_eq, hb.2.1]

private lemma punctured_dual_paving {s : ℕ} (hEs : E.ncard = n+s) :
    IsPaving (punctured E H n hE hH hcH hn hEn)✶ := by
  intro X hX hcard
  have hXE : X ⊆ E := hX
  have hXfin := hE.subset hXE
  rw [punctured_dual_rank hE hH hcH hn hEn hEs, ← hXfin.cast_ncard_eq] at hcard
  have hc : X.ncard < s := by
    have : X.ncard + 1 = s := by exact ENat.natCast_inj.mp hcard
    exact Nat.lt_of_succ_le this.le
  exact punctured_dual_small_indep hE hH hcH hn hEn hEs hXE hc

private lemma punctured_loopless (hn2 : 2 ≤ n) :
    (punctured E H n hE hH hcH hn hEn).Loopless := by
  rw [Matroid.loopless_iff_forall_isNonloop]
  intro e he
  rw [← Matroid.indep_singleton]
  apply punctured_small_indep hE hH hcH hn hEn (Set.singleton_subset_iff.mpr he)
  simp only [Set.ncard_singleton]
  omega

end Generic

private lemma ground_card (n s : ℕ) : ((Set.Icc 1 ((n:ℤ)+s))).ncard = n+s := by
  rw [Set.ncard_Icc, Int.card_Icc]
  omega

private lemma hole_card (n s : ℕ) : ((Set.Icc ((s:ℤ)+1) ((s:ℤ)+n))).ncard = n := by
  rw [Set.ncard_Icc, Int.card_Icc]
  have : (s:ℤ) + n + 1 - ((s:ℤ)+1) = n := by
    rw [add_sub_add_right_eq_sub, add_sub_cancel_left]
  rw [this]; simp

private lemma hole_subset (n s : ℕ) : (Set.Icc ((s:ℤ)+1) ((s:ℤ)+n)) ⊆ (Set.Icc 1 ((n:ℤ)+s)) := by
  exact Set.Icc_subset_Icc (by omega) (by omega)

@[simp] private lemma family_base (n s : ℕ) (hn : 2 ≤ n) (hs : 2 ≤ s) (B : Set ℤ) :
    (punctured (Set.Icc 1 ((n:ℤ)+s)) (Set.Icc ((s:ℤ)+1) ((s:ℤ)+n)) n (Set.finite_Icc _ _) (hole_subset n s) (hole_card n s) (by omega) (by rw [ground_card]; omega)).IsBase B ↔ B ⊆ (Set.Icc 1 ((n:ℤ)+s)) ∧ B.ncard = n ∧ B ≠ (Set.Icc ((s:ℤ)+1) ((s:ℤ)+n)) := by
  exact punctured_base _ _ _ _ _ B

private lemma family_finite (n s : ℕ) (hn : 2 ≤ n) (hs : 2 ≤ s) :
    (punctured (Set.Icc 1 ((n:ℤ)+s)) (Set.Icc ((s:ℤ)+1) ((s:ℤ)+n)) n (Set.finite_Icc _ _) (hole_subset n s) (hole_card n s) (by omega) (by rw [ground_card]; omega)).Finite := by
  exact ⟨Set.finite_Icc _ _⟩

private lemma family_loopless (n s : ℕ) (hn : 2 ≤ n) (hs : 2 ≤ s) :
    (punctured (Set.Icc 1 ((n:ℤ)+s)) (Set.Icc ((s:ℤ)+1) ((s:ℤ)+n)) n (Set.finite_Icc _ _) (hole_subset n s) (hole_card n s) (by omega) (by rw [ground_card]; omega)).Loopless := by
  exact punctured_loopless _ _ _ _ _ hn

private lemma family_rank (n s : ℕ) (hn : 2 ≤ n) (hs : 2 ≤ s) :
    (punctured (Set.Icc 1 ((n:ℤ)+s)) (Set.Icc ((s:ℤ)+1) ((s:ℤ)+n)) n (Set.finite_Icc _ _) (hole_subset n s) (hole_card n s) (by omega) (by rw [ground_card]; omega)).eRank = n := by
  exact punctured_rank _ _ _ _ _

private lemma family_sparse_paving (n s : ℕ) (hn : 2 ≤ n) (hs : 2 ≤ s) :
    IsSparsePaving (punctured (Set.Icc 1 ((n:ℤ)+s)) (Set.Icc ((s:ℤ)+1) ((s:ℤ)+n)) n (Set.finite_Icc _ _) (hole_subset n s) (hole_card n s) (by omega) (by rw [ground_card]; omega)) := by
  exact ⟨punctured_paving _ _ _ _ _,
      punctured_dual_paving _ _ _ _ _ (ground_card n s)⟩

private lemma initial_injective (n : ℕ) : Function.Injective ((fun i : Fin n => (i.val:ℤ)+1)) := by
  exact (add_left_injective (1 : ℤ)).comp (Nat.cast_injective.comp Fin.val_injective)

private lemma initial_range (n : ℕ) : Set.range ((fun i : Fin n => (i.val:ℤ)+1)) = Set.Icc 1 (n:ℤ) := by
  change Set.range ((fun x : ℤ => x + 1) ∘ ((Nat.cast : ℕ → ℤ) ∘ (Fin.val : Fin n → ℕ))) = _
  rw [Set.range_comp, Set.range_comp, Fin.range_val, Nat.image_cast_int_Iio, Set.image_add_const_Ico]
  exact Set.Ico_add_one_right_eq_Icc 1 (n : ℤ)

private lemma initial_base (n s : ℕ) (hn : 2 ≤ n) (hs : 2 ≤ s) :
    (punctured (Set.Icc 1 ((n:ℤ)+s)) (Set.Icc ((s:ℤ)+1) ((s:ℤ)+n)) n (Set.finite_Icc _ _) (hole_subset n s) (hole_card n s) (by omega) (by rw [ground_card]; omega)).IsBase (Set.range ((fun i : Fin n => (i.val:ℤ)+1))) := by
  rw [family_base n s hn hs, initial_range]
  refine ⟨?_, ?_, ?_⟩
  · exact Set.Icc_subset_Icc_right (by omega)
  · simpa only [Nat.cast_zero, add_zero, Nat.add_zero] using ground_card n 0
  · intro hh
    have h1 : (1:ℤ) ∈ Set.Icc 1 (n:ℤ) := by exact Set.left_mem_Icc.mpr (by omega)
    rw [hh] at h1
    simp only [Set.mem_Icc] at h1
    omega

private lemma forced_target (n s : ℕ) (a b : ℤ) (ha : a ∈ Set.Icc 1 (n:ℤ))
    (hb : b ∈ (Set.Icc 1 ((n:ℤ)+s))) (hab : a+b ∉ (Set.Icc 1 ((n:ℤ)+s))) : b ∈ (Set.Icc ((s:ℤ)+1) ((s:ℤ)+n)) := by
  simp only [Set.mem_Icc] at *
  omega

private lemma no_matching_basis (n s : ℕ) (hn : 2 ≤ n) (hs : 2 ≤ s)
    (b : Fin n → ℤ) (hbinj : Function.Injective b)
    (hbase : (punctured (Set.Icc 1 ((n:ℤ)+s)) (Set.Icc ((s:ℤ)+1) ((s:ℤ)+n)) n (Set.finite_Icc _ _) (hole_subset n s) (hole_card n s) (by omega) (by rw [ground_card]; omega)).IsBase (Set.range b)) :
    ¬ BasesMatched (punctured (Set.Icc 1 ((n:ℤ)+s)) (Set.Icc ((s:ℤ)+1) ((s:ℤ)+n)) n (Set.finite_Icc _ _) (hole_subset n s) (hole_card n s) (by omega) (by rw [ground_card]; omega)) ((fun i : Fin n => (i.val:ℤ)+1)) b := by
  intro hmatch
  have hrange : Set.range b ⊆ (Set.Icc ((s:ℤ)+1) ((s:ℤ)+n)) := by
    refine Set.range_subset_iff.mpr ?_
    intro i
    apply forced_target n s ((fun i : Fin n => (i.val:ℤ)+1) i) (b i)
    · rw [← initial_range]; exact Set.mem_range_self i
    · exact hbase.subset_ground (Set.mem_range_self i)
    · exact hmatch i
  have hc : (Set.range b).ncard = n := by
    rw [Set.ncard_range_of_injective hbinj, Nat.card_fin]
  have heq : Set.range b = (Set.Icc ((s:ℤ)+1) ((s:ℤ)+n)) :=
    Set.eq_of_subset_of_ncard_le hrange (by rw [hole_card, hc]) (Set.finite_Icc _ _)
  exact ((family_base n s hn hs _).mp hbase).2.2 heq

private lemma family_not_matched (n s : ℕ) (hn : 2 ≤ n) (hs : 2 ≤ s) :
    ¬ IsMatchedTo (punctured (Set.Icc 1 ((n:ℤ)+s)) (Set.Icc ((s:ℤ)+1) ((s:ℤ)+n)) n (Set.finite_Icc _ _) (hole_subset n s) (hole_card n s) (by omega) (by rw [ground_card]; omega)) (punctured (Set.Icc 1 ((n:ℤ)+s)) (Set.Icc ((s:ℤ)+1) ((s:ℤ)+n)) n (Set.finite_Icc _ _) (hole_subset n s) (hole_card n s) (by omega) (by rw [ground_card]; omega)) := by
  intro hm
  obtain ⟨b,hbinj,hbase,hmatch⟩ := hm n ((fun i : Fin n => (i.val:ℤ)+1)) (initial_injective n) (initial_base n s hn hs)
  exact no_matching_basis n s hn hs b hbinj hbase hmatch

private lemma family_zero (n s : ℕ) (hn : 2 ≤ n) (hs : 2 ≤ s) :
    (0:ℤ) ∉ (punctured (Set.Icc 1 ((n:ℤ)+s)) (Set.Icc ((s:ℤ)+1) ((s:ℤ)+n)) n (Set.finite_Icc _ _) (hole_subset n s) (hole_card n s) (by omega) (by rw [ground_card]; omega)).E := by
  rw [punctured_ground]
  exact Set.notMem_Icc_of_lt (by decide)

theorem result : ¬ claim := by
  intro h
  let N := (punctured (Set.Icc 1 ((2:ℤ)+2)) (Set.Icc ((2:ℤ)+1) ((2:ℤ)+2)) 2 (Set.finite_Icc _ _) (hole_subset 2 2) (hole_card 2 2) (by decide) (by norm_num [Set.ncard_Icc, Int.card_Icc]))
  have hrank : N.eRank = 2 := family_rank 2 2 (by decide) (by decide)
  have hm : IsMatchedTo N N := h ℤ N N
    (family_finite 2 2 (by decide) (by decide)) (family_finite 2 2 (by decide) (by decide))
    (family_loopless 2 2 (by decide) (by decide)) (family_loopless 2 2 (by decide) (by decide))
    (by rw [hrank]; decide) rfl
    (family_sparse_paving 2 2 (by decide) (by decide)) (Or.inr rfl) (family_zero 2 2 (by decide) (by decide))
  exact family_not_matched 2 2 (by decide) (by decide) hm

end D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching
