/- GID: D5/S3/Factorization/Galois/ActualWindowCommonKernel
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/ActualWindowCommonKernel
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Actual common kernels identify simultaneous window intersections and rank minimizers. -/

import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic

/-!
The common constraint uses one tuple in the original extension field. Its
distinguished output coordinate is zero; retaining that coordinate also covers
a singleton family without a separate codomain convention.

For a nonzero label r, inverse multiplication describes the actual scaled
window r W. No passage to an abstract degree lattice or to independent pairwise
minimizers occurs. The kernel construction is the linear-algebraic interface
for the original-label return from a common constraint matrix.
-/

noncomputable section

namespace D5.S3.Factorization.Galois.ActualWindowCommonKernel

open Module

variable {F L ι : Type*} [Field F] [Field L] [Algebra F L]

/-- The actual intersection of the windows scaled by nonzero labels. -/
def intersection (W : ι → Submodule F L) (r : ι → L) : Submodule F L :=
  ⨅ i, (W i).comap (LinearMap.mulLeft F (r i)⁻¹)

/-- All coordinates are constrained against the same distinguished coordinate. -/
def constraint (W : ι → Submodule F L) (k : ι) (p : ι → L) :
    (∀ i, W i) →ₗ[F] (ι → L) where
  toFun v i := p k * (v i : L) - p i * (v k : L)
  map_add' v w := by
    ext i
    simp only [Pi.add_apply, Submodule.coe_add]
    ring
  map_smul' a v := by
    ext i
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, Algebra.smul_def]
    ring

private theorem kernel_coordinate (W : ι → Submodule F L) (k : ι)
    (p : ι → L) (hp : p k ≠ 0) (v : LinearMap.ker (constraint W k p)) (i : ι) :
    p i / p k * (v.1 k : L) = (v.1 i : L) := by
  have h := congrFun (LinearMap.mem_ker.mp v.2) i
  change p k * (v.1 i : L) - p i * (v.1 k : L) = 0 at h
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hp).mpr
  simpa only [mul_comm] using (sub_eq_zero.mp h).symm

/-- Projection to one coordinate, with the simultaneous inverse reconstructed
inside the original windows. -/
private def kernelEquiv (W : ι → Submodule F L) (k : ι)
    (p : ι → L) (hp : ∀ i, p i ≠ 0) :
    LinearMap.ker (constraint W k p) ≃ₗ[F]
      intersection W (fun i => p k / p i) := by
  let project : LinearMap.ker (constraint W k p) →ₗ[F]
      intersection W (fun i => p k / p i) :=
    { toFun := fun v => ⟨(v.1 k : L), by
        simp only [intersection, Submodule.mem_iInf, Submodule.mem_comap,
          LinearMap.mulLeft_apply]
        intro i
        rw [inv_div, kernel_coordinate W k p (hp k) v i]
        exact (v.1 i).2⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  refine LinearEquiv.ofBijective project ⟨?_, ?_⟩
  · intro v w h
    have hcoord := congrArg (fun x : intersection W (fun i => p k / p i) => (x : L)) h
    change (v.1 k : L) = (w.1 k : L) at hcoord
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rw [← kernel_coordinate W k p (hp k) v i,
      ← kernel_coordinate W k p (hp k) w i, hcoord]
  · intro x
    let v : ∀ i, W i := fun i => ⟨p i / p k * (x : L), by
      have hx := (Submodule.mem_iInf _).mp x.2 i
      change (p k / p i)⁻¹ * (x : L) ∈ W i at hx
      simpa only [inv_div] using hx⟩
    have hv : v ∈ LinearMap.ker (constraint W k p) := by
      apply LinearMap.mem_ker.mpr
      ext i
      change p k * (p i / p k * (x : L)) -
        p i * (p k / p k * (x : L)) = 0
      field_simp [hp k]
      <;> ring
    refine ⟨⟨v, hv⟩, Subtype.ext ?_⟩
    change p k / p k * (x : L) = (x : L)
    rw [div_self (hp k), one_mul]

private theorem ratio_mem (W : ι → Submodule F L) (k : ι)
    (p : ∀ i, W i) (hp : ∀ i, (p i : L) ≠ 0) :
    (p k : L) ∈ intersection W (fun i => (p k : L) / (p i : L)) := by
  simp only [intersection, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.mulLeft_apply]
  intro i
  rw [inv_div, div_mul_cancel₀ _ (hp k)]
  exact (p i).2

/-- Rank-nullity for the common constraint gives the dimension of the actual
original-label intersection. The same tuple witnesses positive intersection. -/
theorem common_kernel_rank_identity [Fintype ι] [FiniteDimensional F L]
    (W : ι → Submodule F L) (k : ι) (p : ∀ i, W i)
    (hp : ∀ i, (p i : L) ≠ 0) :
    finrank F (LinearMap.range (constraint W k (fun i => (p i : L)))) +
        finrank F (intersection W (fun i => (p k : L) / (p i : L))) =
      ∑ i, finrank F (W i) ∧
    0 < finrank F (intersection W (fun i => (p k : L) / (p i : L))) := by
  constructor
  · have h := (constraint W k (fun i => (p i : L))).finrank_range_add_finrank_ker
    rw [(kernelEquiv W k (fun i => (p i : L)) hp).finrank_eq,
      Module.finrank_pi_fintype] at h
    exact h
  · apply Submodule.one_le_finrank_iff.mpr
    intro hbot
    have hm := ratio_mem W k p hp
    rw [hbot, Submodule.mem_bot] at hm
    exact hp k hm

private theorem original_tuple (W : ι → Submodule F L) (k : ι)
    (r : ι → L) (hr : ∀ i, r i ≠ 0) (hk : r k = 1)
    (hI : intersection W r ≠ ⊥) :
    ∃ p : ∀ i, W i, (∀ i, (p i : L) ≠ 0) ∧
      (fun i => (p k : L) / (p i : L)) = r := by
  obtain ⟨w, hw, hne⟩ := (intersection W r).ne_bot_iff.mp hI
  let p : ∀ i, W i := fun i => ⟨(r i)⁻¹ * w, by
    exact (Submodule.mem_iInf _).mp hw i⟩
  have hp : ∀ i, (p i : L) ≠ 0 := fun i => mul_ne_zero (inv_ne_zero (hr i)) hne
  refine ⟨p, hp, ?_⟩
  funext i
  change ((r k)⁻¹ * w) / ((r i)⁻¹ * w) = r i
  rw [hk]
  field_simp [hne, hr i]

/-- One tuple in the original windows simultaneously maximizes common-constraint
rank and attains the minimum positive dimension over all original labels. -/
theorem exists_joint_rank_minimizer [Finite ι] [FiniteDimensional F L]
    (W : ι → Submodule F L) (k : ι) (hW : ∀ i, W i ≠ ⊥) :
    ∃ p : ∀ i, W i, (∀ i, (p i : L) ≠ 0) ∧
      (∀ (q : ∀ i, W i), (∀ i, (q i : L) ≠ 0) →
        finrank F (LinearMap.range (constraint W k (fun i => (q i : L)))) ≤
          finrank F (LinearMap.range (constraint W k (fun i => (p i : L))))) ∧
      (∀ r : ι → L, (∀ i, r i ≠ 0) → r k = 1 →
        0 < finrank F (intersection W r) →
        finrank F (intersection W (fun i => (p k : L) / (p i : L))) ≤
          finrank F (intersection W r)) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hex (i : ι) : ∃ x : W i, (x : L) ≠ 0 := by
    obtain ⟨x, hx, hn⟩ := (W i).ne_bot_iff.mp (hW i)
    exact ⟨⟨x, hx⟩, hn⟩
  choose q hq using hex
  let S : Set ℕ := {n | ∃ p : ∀ i, W i, (∀ i, (p i : L) ≠ 0) ∧
    finrank F (intersection W (fun i => (p k : L) / (p i : L))) = n}
  have hS : S.Nonempty := ⟨_, q, hq, rfl⟩
  obtain ⟨p, hp, hd⟩ := Nat.sInf_mem hS
  have hmin (q : ∀ i, W i) (hq : ∀ i, (q i : L) ≠ 0) :
      finrank F (intersection W (fun i => (p k : L) / (p i : L))) ≤
        finrank F (intersection W (fun i => (q k : L) / (q i : L))) := by
    rw [hd]
    exact Nat.sInf_le (show _ ∈ S from ⟨q, hq, rfl⟩)
  refine ⟨p, hp, ?_, ?_⟩
  · intro q hq
    have hpdim := (common_kernel_rank_identity W k p hp).1
    have hqdim := (common_kernel_rank_identity W k q hq).1
    have hle := hmin q hq
    omega
  · intro r hr hk hpos
    have hI : intersection W r ≠ ⊥ := Submodule.one_le_finrank_iff.mp hpos
    obtain ⟨q, hq, heq⟩ := original_tuple W k r hr hk hI
    rw [← heq]
    exact hmin q hq

#print axioms common_kernel_rank_identity
#print axioms exists_joint_rank_minimizer

end D5.S3.Factorization.Galois.ActualWindowCommonKernel

/-!
UNVERIFIED source draft. The declarations below have no current compilation,
axiom-closure, mirror or registration evidence. They develop the deterministic
general-position implication in Raz--Wigderson, arXiv:1901.09423v1, Definition
5.1, Theorem 5.2 and Lemma 5.3. Genericity (Theorem 7.1) is a separate obligation.

For R5 (31.5)--(31.7), V(sigma) is the direct sum of the block-supported
embedding rows and phi is the ONE common hyperplane functional. Class splitting
below is the recursive independence step of the partition-rank proof, not a
rank-nullity assertion about the original window kernel.
-/

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

private theorem finrank_sup_le_sum [FiniteDimensional K E]
    {α : Type*} (s : Finset α) (V : α → Submodule K E) :
    finrank K (s.sup V) ≤ ∑ i ∈ s, finrank K (V i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sup_insert, Finset.sum_insert hi]
      exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
        (Nat.add_le_add_left ih _)

private theorem finrank_sup_of_supIndep [FiniteDimensional K E]
    {α : Type*} (s : Finset α) (V : α → Submodule K E) (h : s.SupIndep V) :
    finrank K (s.sup V) = ∑ i ∈ s, finrank K (V i) := by
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
    · exact le_inf (Finset.le_sup hi) inf_le_left
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
    exact (Finset.le_sup (hB.symm ▸ Finset.mem_filter.mpr ⟨hi, rfl⟩)).trans le_sup_right

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
        le_sup_right ((cutSpan_le_span V φ B) hxB)
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
  refine (finrank_sup_le_sum P.parts (cutSpan V φ)).trans ?_
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
  induction s using Finset.strongInductionOn with
  | h s ih =>
      intro gp
      by_cases hs : s = ∅
      · subst s
        exact ⟨Finpartition.empty (Finset ι), by simp [cutSpan]⟩
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
            exact (Finset.mem_filter.mp (hBi ▸ hjB)).2
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

private theorem span_common_rows_eq_cut {β : Type*} (b : β → E)
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
    rw [Set.image_range]
    rfl
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
      simpa [blockRows] using
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
      exact (Finset.le_sup hσ)
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

end BlockRows

end D5.S3.Factorization.Galois.ActualWindowCommonKernel.HyperplaneRank
