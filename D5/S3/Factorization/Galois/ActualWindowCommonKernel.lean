/- GID: D5/S3/Factorization/Galois/ActualWindowCommonKernel
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/ActualWindowCommonKernel
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Conditional hyperplane partition rank and rigidity of actual embedding constraints. -/

import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Order.Partition.Finpartition
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor

/-!
The declarations below develop the deterministic general-position implication in
Raz--Wigderson, arXiv:1901.09423v1, Definition 5.1, Theorem 5.2 and Lemma 5.3.
Genericity (Theorem 7.1) is a separate obligation.

For R5 (31.5)--(31.7), V(sigma) is the direct sum of the block-supported
embedding rows and phi is the ONE common hyperplane functional. Class splitting
below is the recursive independence step of the partition-rank proof, not a
rank-nullity assertion about the original window kernel.
-/

noncomputable section

open scoped Classical

namespace D5.S3.Factorization.Galois.ActualWindowCommonKernel.HyperplaneRank

open Module

variable {K E ι : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- Span of a finite subfamily before cutting. -/
def familySpan (V : ι → Submodule K E) (s : Finset ι) : Submodule K E :=
  s.sup V

/-- Cut each member by the same hyperplane, then span the cuts. -/
def cutSpan (V : ι → Submodule K E) (φ : E →ₗ[K] K) (s : Finset ι) :
    Submodule K E :=
  s.sup fun i => V i ⊓ LinearMap.ker φ

/-- The finite, source-local form of Definition 5.1. The second clause includes
the empty middle family, as required in the base case of Lemma 5.3. -/
def InGeneralPosition (V : ι → Submodule K E) (φ : E →ₗ[K] K) (s : Finset ι) : Prop :=
  (∀ i ∈ s, ¬ V i ≤ LinearMap.ker φ) ∧
    ∀ A ⊆ s, ∀ B ⊆ s, ∀ C ⊆ s,
      (cutSpan V φ A ⊔ familySpan V B) ⊓
          (cutSpan V φ A ⊔ familySpan V C) ≤ LinearMap.ker φ →
      (cutSpan V φ A ⊔ familySpan V B) ⊓
          (cutSpan V φ A ⊔ familySpan V C) = cutSpan V φ A

private theorem cutSpan_le_ker (V : ι → Submodule K E) (φ : E →ₗ[K] K)
    (s : Finset ι) : cutSpan V φ s ≤ LinearMap.ker φ :=
  Finset.sup_le fun _ _ => inf_le_right

private theorem cutSpan_le_span (V : ι → Submodule K E) (φ : E →ₗ[K] K)
    (s : Finset ι) : cutSpan V φ s ≤ familySpan V s :=
  Finset.sup_mono_fun fun _ _ => inf_le_left

private theorem generalPosition_mono {V : ι → Submodule K E} {φ : E →ₗ[K] K}
    {s t : Finset ι} (h : InGeneralPosition V φ s) (ht : t ⊆ s) :
    InGeneralPosition V φ t :=
  ⟨fun i hi => h.1 i (ht hi),
    fun A hA B hB C hC => h.2 A (hA.trans ht) B (hB.trans ht) C (hC.trans ht)⟩

private theorem cutSpan_sup_parts (V : ι → Submodule K E) (φ : E →ₗ[K] K)
    {s : Finset ι} (P : Finpartition s) :
    P.parts.sup (cutSpan V φ) = cutSpan V φ s := by
  classical
  apply P.sup_parts_apply
  · intro A B
    exact Finset.sup_union
  · exact Finset.sup_empty

private theorem finrank_sup_of_supIndep [FiniteDimensional K E]
    {α : Type*} (s : Finset α) (V : α → Submodule K E) (h : s.SupIndep V) :
    finrank K (s.sup V : Submodule K E) = ∑ i ∈ s, finrank K (V i) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => intro h; simp
  | @insert i s hi ih =>
      intro h
      have hs : s ⊆ insert i s := Finset.subset_insert _ _
      have hd := h hs (Finset.mem_insert_self i s) hi
      have hr := Submodule.finrank_sup_add_finrank_inf_eq (V i) (s.sup V)
      rw [hd.eq_bot, finrank_bot, add_zero] at hr
      rw [Finset.sup_insert, Finset.sum_insert hi, hr, ih (h.subset hs)]

private theorem finrank_inf_ker_add_one [FiniteDimensional K E]
    (φ : E →ₗ[K] K) (P : Submodule K E) (hP : ¬ P ≤ LinearMap.ker φ) :
    finrank K (P ⊓ LinearMap.ker φ : Submodule K E) + 1 = finrank K P := by
  have hn : φ.domRestrict P ≠ 0 := by
    intro hz
    apply hP
    intro x hx
    have h := LinearMap.congr_fun hz (⟨x, hx⟩ : P)
    exact LinearMap.mem_ker.mpr (by simpa using h)
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  have heq : LinearMap.ker (φ.domRestrict P) =
      (P ⊓ LinearMap.ker φ : Submodule K E).comap P.subtype := by
    ext x
    simp
  rw [heq, (Submodule.comapSubtypeEquivOfLe
    (show (P ⊓ LinearMap.ker φ : Submodule K E) ≤ P from inf_le_left)).finrank_eq] at hdim
  exact hdim

private theorem extension_finrank [FiniteDimensional K E]
    (V : ι → Submodule K E) (φ : E →ₗ[K] K) {s : Finset ι} {i : ι}
    (hi : i ∈ s) (hout : ¬ V i ≤ LinearMap.ker φ) :
    finrank K (cutSpan V φ s ⊔ V i : Submodule K E) =
      finrank K (cutSpan V φ s) + 1 := by
  have hinter : cutSpan V φ s ⊓ V i = V i ⊓ LinearMap.ker φ := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans (cutSpan_le_ker V φ s))
    · exact le_inf (Finset.le_sup (f := fun j => V j ⊓ LinearMap.ker φ) hi) inf_le_left
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (cutSpan V φ s) (V i)
  rw [hinter] at hd
  have hcut := finrank_inf_ker_add_one φ (V i) hout
  omega

private theorem equal_rank_extensions_inf [FiniteDimensional K E]
    {T P Q : Submodule K E} (hTP : T ≤ P) (hTQ : T ≤ Q)
    (hP : finrank K P = finrank K T + 1)
    (hQ : finrank K Q = finrank K T + 1) (hne : P ≠ Q) : P ⊓ Q = T := by
  have hT : T ≤ P ⊓ Q := le_inf hTP hTQ
  apply le_antisymm _ hT
  by_contra hnot
  have hlt : T < P ⊓ Q := lt_of_le_not_ge hT hnot
  have hdlt := Submodule.finrank_lt_finrank_of_lt hlt
  have hdle := Submodule.finrank_mono (show P ⊓ Q ≤ P from inf_le_left)
  have heq : P ⊓ Q = P := Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
  have hPQ : P ≤ Q := heq.symm.le.trans inf_le_right
  exact hne (Submodule.eq_of_le_of_finrank_eq hPQ (hP.trans hQ.symm))

private def extensionPartition (V : ι → Submodule K E) (φ : E →ₗ[K] K)
    (s : Finset ι) : Finpartition s := by
  classical
  exact Finpartition.ofSetSetoid
    (Setoid.ker fun i => cutSpan V φ s ⊔ V i) s

private theorem extensionPart_repr (V : ι → Submodule K E) (φ : E →ₗ[K] K)
    {s B : Finset ι} (hB : B ∈ (extensionPartition V φ s).parts) :
    ∃ i ∈ s, B = s.filter (fun j => cutSpan V φ s ⊔ V i = cutSpan V φ s ⊔ V j) := by
  classical
  change B ∈ s.image (fun i => s.filter
    (fun j => cutSpan V φ s ⊔ V i = cutSpan V φ s ⊔ V j)) at hB
  obtain ⟨i, hi, hBi⟩ := Finset.mem_image.mp hB
  exact ⟨i, hi, hBi.symm⟩

private theorem extensionPart_sup (V : ι → Submodule K E) (φ : E →ₗ[K] K)
    {s B : Finset ι} {i : ι} (hi : i ∈ s)
    (hB : B = s.filter (fun j => cutSpan V φ s ⊔ V i = cutSpan V φ s ⊔ V j)) :
    cutSpan V φ s ⊔ familySpan V B = cutSpan V φ s ⊔ V i := by
  classical
  apply le_antisymm
  · refine sup_le le_sup_left (Finset.sup_le fun j hj => ?_)
    have hij := (Finset.mem_filter.mp (hB ▸ hj)).2
    exact hij.symm ▸ (show V j ≤ cutSpan V φ s ⊔ V j from le_sup_right)
  · refine sup_le le_sup_left ?_
    exact (Finset.le_sup (f := V)
      (hB.symm ▸ Finset.mem_filter.mpr ⟨hi, rfl⟩)).trans le_sup_right

private theorem extensionPart_separated [FiniteDimensional K E]
    {V : ι → Submodule K E} {φ : E →ₗ[K] K} {s : Finset ι}
    (h : InGeneralPosition V φ s) {B C : Finset ι}
    (hB : B ∈ (extensionPartition V φ s).parts)
    (hC : C ∈ (extensionPartition V φ s).parts) (hne : B ≠ C) :
    (cutSpan V φ s ⊔ familySpan V B) ⊓
      (cutSpan V φ s ⊔ familySpan V C) ≤ LinearMap.ker φ := by
  classical
  obtain ⟨i, hi, hBi⟩ := extensionPart_repr V φ hB
  obtain ⟨j, hj, hCj⟩ := extensionPart_repr V φ hC
  rw [extensionPart_sup V φ hi hBi, extensionPart_sup V φ hj hCj]
  have hneq : cutSpan V φ s ⊔ V i ≠ cutSpan V φ s ⊔ V j := by
    intro heq
    apply hne
    rw [hBi, hCj, heq]
  rw [equal_rank_extensions_inf le_sup_left le_sup_left
    (extension_finrank V φ hi (h.1 i hi))
    (extension_finrank V φ hj (h.1 j hj)) hneq]
  exact cutSpan_le_ker V φ s

/-- The recursive direct-sum step of Lemma 5.3. Separation is tested on the
uncut blocks extended by the total cut span; pairwise disjointness of cuts
alone would not imply this conclusion. -/
private theorem cut_parts_supIndep
    {V : ι → Submodule K E} {φ : E →ₗ[K] K} {s : Finset ι}
    (h : InGeneralPosition V φ s) (P : Finpartition s)
    (hsep : ∀ B ∈ P.parts, ∀ C ∈ P.parts, B ≠ C →
      (cutSpan V φ s ⊔ familySpan V B) ⊓
        (cutSpan V φ s ⊔ familySpan V C) ≤ LinearMap.ker φ) :
    P.parts.SupIndep (cutSpan V φ) := by
  classical
  intro q hq B hB hBq
  revert hq hBq
  induction q using Finset.induction_on with
  | empty => intro hq hBq; simp
  | @insert C q hCq ih =>
      intro hq hBq
      have hC : C ∈ P.parts := hq (Finset.mem_insert_self _ _)
      have hqP : q ⊆ P.parts := (Finset.subset_insert _ _).trans hq
      have hBC : B ≠ C := by
        intro heq
        exact hBq (Finset.mem_insert.mpr (Or.inl heq))
      have hBq' : B ∉ q := fun hb => hBq (Finset.mem_insert_of_mem hb)
      have hdq := ih hqP hBq'
      let A := q.biUnion id
      have hAs : A ⊆ s := by
        intro i hi
        obtain ⟨D, hD, hiD⟩ := Finset.mem_biUnion.mp hi
        exact P.le (hqP hD) hiD
      have hcutA : cutSpan V φ A = q.sup (cutSpan V φ) := by
        dsimp [A, cutSpan]
        rw [Finset.sup_biUnion]
        rfl
      have hAT : cutSpan V φ A ≤ cutSpan V φ s := Finset.sup_mono hAs
      have hcross : (cutSpan V φ A ⊔ familySpan V C) ⊓
          (cutSpan V φ A ⊔ familySpan V B) ≤ LinearMap.ker φ :=
        (inf_le_inf (sup_le_sup_right hAT _) (sup_le_sup_right hAT _)).trans
          (hsep C hC B hB hBC.symm)
      have hmiddle := h.2 A hAs C (P.le hC) B (P.le hB) hcross
      apply Submodule.disjoint_def.mpr
      intro x hxB hxq
      rw [Finset.sup_insert] at hxq
      have hxL : x ∈ cutSpan V φ A ⊔ familySpan V C := by
        have hle : cutSpan V φ C ⊔ q.sup (cutSpan V φ) ≤
            cutSpan V φ A ⊔ familySpan V C := by
          rw [hcutA]
          exact sup_le ((cutSpan_le_span V φ C).trans le_sup_right) le_sup_left
        exact hle hxq
      have hxR : x ∈ cutSpan V φ A ⊔ familySpan V B :=
        (le_sup_right : familySpan V B ≤ cutSpan V φ A ⊔ familySpan V B)
          ((cutSpan_le_span V φ B) hxB)
      have hxA : x ∈ q.sup (cutSpan V φ) := by
        rw [← hcutA, ← hmiddle]
        exact ⟨hxL, hxR⟩
      exact Submodule.disjoint_def.mp hdq x hxB hxA

private theorem rank_le_partition_cost [FiniteDimensional K E]
    {V : ι → Submodule K E} {φ : E →ₗ[K] K} {s : Finset ι}
    (h : InGeneralPosition V φ s) (P : Finpartition s) :
    finrank K (cutSpan V φ s) ≤
      ∑ B ∈ P.parts, (finrank K (familySpan V B) - 1) := by
  classical
  rw [← cutSpan_sup_parts V φ P]
  refine (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor.finrank_sup_le_sum
    (cutSpan V φ) P.parts).trans ?_
  apply Finset.sum_le_sum
  intro B hB
  obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts hB
  have hout : ¬ familySpan V B ≤ LinearMap.ker φ := by
    intro hBker
    exact h.1 i (P.le hB hi) ((Finset.le_sup hi).trans hBker)
  have hdim := finrank_inf_ker_add_one φ (familySpan V B) hout
  have hle := Submodule.finrank_mono
    (le_inf (cutSpan_le_span V φ B) (cutSpan_le_ker V φ B))
  omega

private theorem exists_tight_partition [FiniteDimensional K E]
    (V : ι → Submodule K E) (φ : E →ₗ[K] K) (s : Finset ι) :
    InGeneralPosition V φ s →
      ∃ P : Finpartition s, finrank K (cutSpan V φ s) =
        ∑ B ∈ P.parts, (finrank K (familySpan V B) - 1) := by
  classical
  refine Finset.strongInductionOn s ?_
  intro s ih
  intro gp
  by_cases hs : s = ∅
  · subst s
    refine ⟨Finpartition.empty (Finset ι), ?_⟩
    change finrank K (cutSpan V φ ∅) = 0
    rw [cutSpan, Finset.sup_empty, finrank_bot]
  by_cases hall : ∀ i ∈ s, ∀ j ∈ s,
      cutSpan V φ s ⊔ V i = cutSpan V φ s ⊔ V j
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hspan : familySpan V s = cutSpan V φ s ⊔ V i := by
      apply le_antisymm
      · apply Finset.sup_le
        intro j hj
        rw [hall i hi j hj]
        exact le_sup_right
      · exact sup_le (cutSpan_le_span V φ s) (Finset.le_sup hi)
    have hdim := extension_finrank V φ hi (gp.1 i hi)
    rw [← hspan] at hdim
    refine ⟨Finpartition.indiscrete hs, ?_⟩
    simp only [Finpartition.indiscrete_parts, Finset.sum_singleton]
    omega
  · let P := extensionPartition V φ s
    have hproper : ∀ B ∈ P.parts, B ⊂ s := by
      intro B hB
      refine Finset.ssubset_iff_subset_ne.mpr ⟨P.le hB, ?_⟩
      intro hBs
      obtain ⟨i, hi, hBi⟩ := extensionPart_repr V φ hB
      have hsame : ∀ j ∈ s, cutSpan V φ s ⊔ V i = cutSpan V φ s ⊔ V j := by
        intro j hj
        have hjB : j ∈ B := hBs.symm ▸ hj
        have hjfilter : j ∈ s.filter
            (fun l => cutSpan V φ s ⊔ V i = cutSpan V φ s ⊔ V l) := hBi ▸ hjB
        exact (Finset.mem_filter.mp hjfilter).2
      exact hall fun j hj k hk => (hsame j hj).symm.trans (hsame k hk)
    have hrec : ∀ B ∈ P.parts, ∃ Q : Finpartition B,
        finrank K (cutSpan V φ B) =
          ∑ C ∈ Q.parts, (finrank K (familySpan V C) - 1) := by
      intro B hB
      exact ih B (hproper B hB) (generalPosition_mono gp (P.le hB))
    let Q : ∀ B ∈ P.parts, Finpartition B := fun B hB => (hrec B hB).choose
    have hQ : ∀ B (hB : B ∈ P.parts), finrank K (cutSpan V φ B) =
        ∑ C ∈ (Q B hB).parts, (finrank K (familySpan V C) - 1) := by
      intro B hB
      exact (hrec B hB).choose_spec
    have hind : P.parts.SupIndep (cutSpan V φ) :=
      cut_parts_supIndep gp P (fun B hB C hC => extensionPart_separated gp hB hC)
    refine ⟨P.bind Q, ?_⟩
    calc
      finrank K (cutSpan V φ s) =
          ∑ B ∈ P.parts, finrank K (cutSpan V φ B) := by
        rw [← cutSpan_sup_parts V φ P]
        exact finrank_sup_of_supIndep P.parts (cutSpan V φ) hind
      _ = ∑ B ∈ P.parts.attach,
          ∑ C ∈ (Q B.1 B.2).parts, (finrank K (familySpan V C) - 1) := by
        rw [← Finset.sum_attach]
        exact Finset.sum_congr rfl (fun B _ => hQ B.1 B.2)
      _ = ∑ C ∈ (P.bind Q).parts, (finrank K (familySpan V C) - 1) := by
        simpa only [Finpartition.bind, Finpartition.copy_parts] using
          (Finpartition.sum_combine (fun B : P.parts => Q B.1 B.2)
            P.supIndep.attach (fun C => finrank K (familySpan V C) - 1)).symm

/-- Deterministic Lovasz partition-rank implication, with its actual attaining
partition. This does not assert that an algebraically independent normal is in
general position; that is the separate genericity input in R5 (31.7). -/
theorem hyperplane_partition_rank [FiniteDimensional K E]
    (V : ι → Submodule K E) (φ : E →ₗ[K] K) (s : Finset ι)
    (h : InGeneralPosition V φ s) :
    ∃ P : Finpartition s,
      finrank K (cutSpan V φ s) =
        ∑ B ∈ P.parts, (finrank K (familySpan V B) - 1) ∧
      ∀ Q : Finpartition s, finrank K (cutSpan V φ s) ≤
        ∑ B ∈ Q.parts, (finrank K (familySpan V B) - 1) := by
  obtain ⟨P, hP⟩ := exists_tight_partition V φ s h
  exact ⟨P, hP, rank_le_partition_cost h⟩

/-- Row space of the SAME constraint for every member of a finite family.
The distinguished row is zero; all other rows use that one distinguished
coefficient, rather than independently chosen pairwise parameters. -/
def commonRowSpan {β : Type*} (b : ι → β → E) (φ : E →ₗ[K] K)
    (k : β) (s : Finset ι) : Submodule K E :=
  s.sup fun σ => Submodule.span K
    (Set.range fun i => φ (b σ k) • b σ i - φ (b σ i) • b σ k)

private def cutProjection (φ : E →ₗ[K] K) (v : E) : E →ₗ[K] E :=
  φ v • LinearMap.id - φ.smulRight v

theorem span_common_rows_eq_cut {β : Type*} (b : β → E)
    (φ : E →ₗ[K] K) (k : β) (hk : φ (b k) ≠ 0) :
    Submodule.span K (Set.range fun i => φ (b k) • b i - φ (b i) • b k) =
      Submodule.span K (Set.range b) ⊓ LinearMap.ker φ := by
  let P := Submodule.span K (Set.range b)
  let π := cutProjection φ (b k)
  have hbk : b k ∈ P := Submodule.subset_span (Set.mem_range_self k)
  have hmap : P.map π = P ⊓ LinearMap.ker φ := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      refine ⟨P.sub_mem (P.smul_mem _ hy) (P.smul_mem _ hbk), ?_⟩
      apply LinearMap.mem_ker.mpr
      change φ (φ (b k) • y - φ y • b k) = 0
      simp [mul_comm]
    · intro x hx
      refine ⟨(φ (b k))⁻¹ • x, P.smul_mem _ hx.1, ?_⟩
      have hxφ : φ x = 0 := LinearMap.mem_ker.mp hx.2
      change φ (b k) • ((φ (b k))⁻¹ • x) - φ ((φ (b k))⁻¹ • x) • b k = x
      simp [hxφ, smul_smul, hk]
  have himage : π '' Set.range b =
      Set.range (fun i => φ (b k) • b i - φ (b i) • b k) := by
    exact (Set.range_comp π b).symm
  rw [show P = Submodule.span K (Set.range b) from rfl,
    Submodule.map_span, himage] at hmap
  exact hmap

/-- The (31.6) common-constraint rows consume the partition-rank theorem.
The spans here are the actual rows in one common ambient vector space.
In the source, b(sigma,i) is the block-supported embedding row and phi is the
normal z. Identifying that algebraically independent normal as general-position
is NOT included in the hypothesis discharge of this source draft. -/
private theorem common_rows_partition_rank [FiniteDimensional K E] {β : Type*}
    (b : ι → β → E) (φ : E →ₗ[K] K) (k : β) (s : Finset ι)
    (hk : ∀ σ ∈ s, φ (b σ k) ≠ 0)
    (h : InGeneralPosition (fun σ => Submodule.span K (Set.range (b σ))) φ s) :
    ∃ P : Finpartition s,
      finrank K (commonRowSpan b φ k s) =
        ∑ B ∈ P.parts,
          (finrank K (familySpan (fun σ => Submodule.span K (Set.range (b σ))) B) - 1) ∧
      ∀ Q : Finpartition s, finrank K (commonRowSpan b φ k s) ≤
        ∑ B ∈ Q.parts,
          (finrank K (familySpan (fun σ => Submodule.span K (Set.range (b σ))) B) - 1) := by
  have hrows : commonRowSpan b φ k s =
      cutSpan (fun σ => Submodule.span K (Set.range (b σ))) φ s := by
    apply Finset.sup_congr rfl
    intro σ hσ
    exact span_common_rows_eq_cut (b σ) φ k (hk σ hσ)
  rw [hrows]
  exact hyperplane_partition_rank _ φ s h

section BlockRows

variable {β : Type*} {κ : β → Type*} [Fintype β] [∀ i, Fintype (κ i)]

/-- The i-th row is placed in its own coordinate block, exactly as in (31.5). -/
def blockRows (b : ∀ i, ι → κ i → K) (σ : ι) (i : β) : (j : β) → κ j → K := by
  classical
  exact Pi.single i (b i σ)

/-- Rank contribution q_i(B) of a nonempty embedding block; the definition also
permits the empty subfamily, whose span has dimension zero. -/
def blockSpan (b : ∀ i, ι → κ i → K) (B : Finset ι) (i : β) :
    Submodule K (κ i → K) :=
  Submodule.span K (b i '' (B : Set ι))

private def piSubtypeEquiv (p : (i : β) → Submodule K (κ i → K)) :
    Submodule.pi Set.univ p ≃ₗ[K] ((i : β) → p i) where
  toFun x i := ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
  invFun x := ⟨fun i => x i, fun i _ => (x i).2⟩
  left_inv x := by ext i j; rfl
  right_inv x := by ext i j; rfl
  map_add' x y := by ext i j; rfl
  map_smul' c x := by ext i j; rfl

private theorem familySpan_blockRows (b : ∀ i, ι → κ i → K) (B : Finset ι) :
    familySpan (fun σ => Submodule.span K (Set.range (blockRows b σ))) B =
      Submodule.pi Set.univ (blockSpan b B) := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro σ hσ
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa [blockRows, blockSpan] using
        (Submodule.subset_span (show b i σ ∈ b i '' (B : Set ι) from ⟨σ, hσ, rfl⟩))
    · simpa [blockRows, Pi.single_eq_of_ne hji] using (blockSpan b B j).zero_mem
  · intro x hx
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro i hi
    have hmap : (blockSpan b B i).map
        (LinearMap.single K (fun j => κ j → K) i) ≤
        familySpan (fun σ => Submodule.span K (Set.range (blockRows b σ))) B := by
      rw [blockSpan, Submodule.map_span_le]
      rintro _ ⟨σ, hσ, rfl⟩
      exact (Finset.le_sup (f := fun τ => Submodule.span K (Set.range (blockRows b τ))) hσ)
        (Submodule.subset_span (Set.mem_range_self i))
    exact hmap (Submodule.mem_map_of_mem (hx i (Set.mem_univ i)))

private theorem familySpan_blockRows_finrank (b : ∀ i, ι → κ i → K) (B : Finset ι) :
    finrank K (familySpan (fun σ => Submodule.span K (Set.range (blockRows b σ))) B) =
      ∑ i, finrank K (blockSpan b B i) := by
  rw [familySpan_blockRows, (piSubtypeEquiv (blockSpan b B)).finrank_eq,
    Module.finrank_pi_fintype]

/-- The actual common-constraint row interface of (31.5)--(31.7), conditional
only on the explicitly exposed deterministic general-position premise.
No generic partition rank, field descent or original-field specialization is
assumed as an atomic rank fact. All blocks use the same phi and the same k. -/
theorem block_common_rows_partition_rank
    (b : ∀ i, ι → κ i → K) (φ : ((i : β) → κ i → K) →ₗ[K] K)
    (k : β) (s : Finset ι)
    (hk : ∀ σ ∈ s, φ (blockRows b σ k) ≠ 0)
    (h : InGeneralPosition
      (fun σ => Submodule.span K (Set.range (blockRows b σ))) φ s) :
    ∃ P : Finpartition s,
      finrank K (commonRowSpan (blockRows b) φ k s) =
        ∑ B ∈ P.parts, ((∑ i, finrank K (blockSpan b B i)) - 1) ∧
      ∀ Q : Finpartition s, finrank K (commonRowSpan (blockRows b) φ k s) ≤
        ∑ B ∈ Q.parts, ((∑ i, finrank K (blockSpan b B i)) - 1) := by
  obtain ⟨P, hP, hbound⟩ := common_rows_partition_rank (blockRows b) φ k s hk h
  refine ⟨P, ?_, ?_⟩
  · simpa only [familySpan_blockRows_finrank] using hP
  · intro Q
    simpa only [familySpan_blockRows_finrank] using hbound Q


/-- The common normal in coefficient coordinates. The flattened index is the
source pair (i,j); commutativity identifies this with sum z(i,j)v(i,j). -/
def coefficientNormal (z : (Σ i, κ i) → K) : ((i : β) → κ i → K) →ₗ[K] K where
  toFun v := ∑ a, v a.1 a.2 * z a
  map_add' v w := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c v := by simp [mul_assoc, Finset.mul_sum]

/-- Matrix of the simultaneous constraint in embedding output coordinates.
The row (sigma,i) is exactly the row of (31.6), including the zero k-row. -/
def commonConstraintMatrix [Fintype ι] (b : ∀ i, ι → κ i → K)
    (φ : ((i : β) → κ i → K) →ₗ[K] K) (k : β) :
    Matrix (ι × β) (Σ i, κ i) K :=
  fun r a => φ (blockRows b r.1 k) * blockRows b r.1 r.2 a.1 a.2 -
    φ (blockRows b r.1 r.2) * blockRows b r.1 k a.1 a.2

private theorem commonConstraintMatrix_rank [Fintype ι]
    (b : ∀ i, ι → κ i → K) (φ : ((i : β) → κ i → K) →ₗ[K] K) (k : β) :
    (commonConstraintMatrix b φ k).rank =
      finrank K (commonRowSpan (blockRows b) φ k Finset.univ) := by
  classical
  let e : ((i : β) → κ i → K) ≃ₗ[K] ((a : Σ i, κ i) → K) :=
    (LinearEquiv.piCurry K (fun _ _ => K)).symm
  have hspan : (commonRowSpan (blockRows b) φ k Finset.univ).map e.toLinearMap =
      Submodule.span K (Set.range (commonConstraintMatrix b φ k).row) := by
    apply le_antisymm
    · have hle : commonRowSpan (blockRows b) φ k Finset.univ ≤
          (Submodule.span K (Set.range (commonConstraintMatrix b φ k).row)).comap
            e.toLinearMap := by
        apply Finset.sup_le
        intro σ hσ
        apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨(σ, i), rfl⟩
      rintro y ⟨v, hv, rfl⟩
      exact hle hv
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨σ, i⟩, rfl⟩
      exact ⟨φ (blockRows b σ k) • blockRows b σ i -
          φ (blockRows b σ i) • blockRows b σ k,
        (Finset.le_sup (f := fun τ => Submodule.span K (Set.range fun j =>
          φ (blockRows b τ k) • blockRows b τ j - φ (blockRows b τ j) • blockRows b τ k))
          (Finset.mem_univ σ))
          (Submodule.subset_span (Set.mem_range_self i)), rfl⟩
  rw [Matrix.rank_eq_finrank_span_row, ← hspan, e.finrank_map_eq]

variable {F D : Type*} [Field F] [Field D] [Algebra F D] [Algebra F K]

/-- Actual embedding rows of bases of the original normalized windows X_i.
The scalar field K may already include the parameter extension K_0(z). -/
def embeddingRows (emb : ι → D →ₐ[F] K) (X : β → Submodule F D)
    (x : ∀ i, Basis (κ i) F (X i)) : ∀ i, ι → κ i → K :=
  fun i σ j => emb σ (x i j : D)

/-- A source-mathematics consumer of partition rank: the actual simultaneous
embedding constraints have only the shared coefficient direction as solutions
iff every partition cost is at least M-1. This is a rigidity statement about
vectors in the kernel, not a renamed row-rank formula.

For (31.5)--(31.7), F is the original field, D the ratio field, K is K_0(z),
emb lists Hom_F(D,K_0) followed by K_0 -> K_0(z), X and x are the source
normalized windows and their F-bases, k=1, and z is the SAME coefficient tuple
in all output embeddings. The conclusion concerns this scalar-extended
embedding-coordinate system only; it proves neither genericity nor descent
nor specialization of the polynomial constraint over F. -/
theorem embedding_common_kernel_rigidity [Fintype ι]
    (emb : ι → D →ₐ[F] K) (X : β → Submodule F D)
    (x : ∀ i, Basis (κ i) F (X i)) (z : (Σ i, κ i) → K) (k : β)
    (hz : z ≠ 0)
    (hk : ∀ σ, coefficientNormal z (blockRows (embeddingRows emb X x) σ k) ≠ 0)
    (gp : InGeneralPosition
      (fun σ => Submodule.span K (Set.range (blockRows (embeddingRows emb X x) σ)))
      (coefficientNormal z) Finset.univ) :
    LinearMap.ker
        (commonConstraintMatrix (embeddingRows emb X x) (coefficientNormal z) k).mulVecLin =
      K ∙ z ↔
    ∀ P : Finpartition (Finset.univ : Finset ι),
      (∑ i, Fintype.card (κ i)) - 1 ≤
        ∑ B ∈ P.parts, ((∑ i, finrank K (blockSpan (embeddingRows emb X x) B i)) - 1) := by
  classical
  let b := embeddingRows emb X x
  let A := commonConstraintMatrix b (coefficientNormal z) k
  change LinearMap.ker A.mulVecLin = K ∙ z ↔
    ∀ P : Finpartition (Finset.univ : Finset ι),
      (∑ i, Fintype.card (κ i)) - 1 ≤
        ∑ B ∈ P.parts, ((∑ i, finrank K (blockSpan b B i)) - 1)
  obtain ⟨P, hP, hbound⟩ := block_common_rows_partition_rank b (coefficientNormal z)
    k Finset.univ (fun σ _ => hk σ) gp
  have hrank : A.rank = finrank K (commonRowSpan (blockRows b)
      (coefficientNormal z) k Finset.univ) := commonConstraintMatrix_rank b _ k
  have hnull := A.mulVecLin.finrank_range_add_finrank_ker
  change A.rank + finrank K (LinearMap.ker A.mulVecLin) =
    finrank K ((Σ i, κ i) → K) at hnull
  rw [Module.finrank_pi, Fintype.card_sigma] at hnull
  have hzker : z ∈ LinearMap.ker A.mulVecLin := by
    apply LinearMap.mem_ker.mpr
    ext ⟨σ, i⟩
    change coefficientNormal z ((coefficientNormal z (blockRows b σ k)) •
      blockRows b σ i - (coefficientNormal z (blockRows b σ i)) • blockRows b σ k) = 0
    simp [mul_comm]
  have hline : K ∙ z ≤ LinearMap.ker A.mulVecLin :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hzker
  have hline_dim : finrank K (K ∙ z) = 1 := finrank_span_singleton hz
  have hpos : 1 ≤ finrank K (LinearMap.ker A.mulVecLin) := by
    simpa only [hline_dim] using Submodule.finrank_mono hline
  constructor
  · intro heq Q
    have hdim : finrank K (LinearMap.ker A.mulVecLin) = 1 := by
      rw [heq, hline_dim]
    have hle := hbound Q
    rw [← hrank] at hle
    omega
  · intro hc
    have hcost := hc P
    have hrP := hrank.trans hP
    have hdim : finrank K (LinearMap.ker A.mulVecLin) = 1 := by omega
    exact (Submodule.eq_of_le_of_finrank_eq hline (hline_dim.trans hdim.symm)).symm

#print axioms hyperplane_partition_rank
#print axioms block_common_rows_partition_rank
#print axioms embedding_common_kernel_rigidity

end BlockRows

end D5.S3.Factorization.Galois.ActualWindowCommonKernel.HyperplaneRank
