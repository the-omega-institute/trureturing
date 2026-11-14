/- GID: D5/S3/VertexAlgebra/Sectors/VBKMWeightIdeal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/VBKMWeightIdeal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Virasoro and Borcherds presentation, action, and ideal structure. -/

/-
admission_basis: escape-witness
proof_shape: ASSUMED-UNVERIFIED until the port is compiled and classified.
escape_witness: ASSUMED-UNVERIFIED until the port is compiled and classified.
Direct frozen dependencies: none.
-/


import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finsupp.Interval
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Common
import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Ideal
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Eigenspace.Basic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
attribute [local instance] LieRing.ofAssociativeRing
universe u v
namespace D5.S3.VertexAlgebra.Sectors.VBKMWeightIdeal

variable {A N P : Type*} [LieRing A] [LieAlgebra ℂ A]

private noncomputable def wordAction (neg : N → A) (v : A) : List N → A
  | [] => v
  | n::ns => ⁅neg n, wordAction neg v ns⁆

private noncomputable def negativeSpan (neg : N → A) (v : A) : Submodule ℂ A :=
  Submodule.span ℂ (Set.range (wordAction neg v))

private theorem seed_mem (neg : N → A) (v : A) : v ∈ negativeSpan neg v :=
  Submodule.subset_span ⟨[],rfl⟩

private theorem negative_stable (neg : N → A) (v : A) (n : N) (x : A)
    (hx : x ∈ negativeSpan neg v) : ⁅neg n,x⁆ ∈ negativeSpan neg v := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨ns,rfl⟩ := hy
    exact Submodule.subset_span ⟨n::ns,rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [lie_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [lie_smul] using Submodule.smul_mem _ a ih

private theorem negative_linear_stable (neg : N → A) (v : A) (x y : A)
    (hx : x ∈ Submodule.span ℂ (Set.range neg)) (hy : y ∈ negativeSpan neg v) :
    ⁅x,y⁆ ∈ negativeSpan neg v := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨n,rfl⟩ := hx; exact negative_stable neg v n y hy
  | zero => simp
  | add x x' hx hx' ih ih' => simpa only [add_lie] using Submodule.add_mem _ ih ih'
  | smul a x hx ih => simpa only [smul_lie] using Submodule.smul_mem _ a ih

private theorem cartan_stable (neg : N → A) (v : A) (C : Set A)
    (hCN : ∀ c ∈ C, ∀ n, ⁅c,neg n⁆ ∈ Submodule.span ℂ (Set.range neg))
    (hCv : ∀ c ∈ C, ⁅c,v⁆ ∈ Submodule.span ℂ ({v} : Set A))
    (c : A) (hc : c ∈ C) (x : A) (hx : x ∈ negativeSpan neg v) :
    ⁅c,x⁆ ∈ negativeSpan neg v := by
  have hword (ns : List N) : ⁅c,wordAction neg v ns⁆ ∈ negativeSpan neg v := by
    induction ns with
    | nil =>
      have hle : Submodule.span ℂ ({v} : Set A) ≤ negativeSpan neg v := by
        apply Submodule.span_le.mpr
        intro y hy
        have hy' : y = v := Set.mem_singleton_iff.mp hy
        subst y
        exact seed_mem neg v
      exact hle (hCv c hc)
    | cons n ns ih =>
      rw [wordAction,leibniz_lie]
      exact Submodule.add_mem _
        (negative_linear_stable neg v _ _ (hCN c hc n) (Submodule.subset_span ⟨ns,rfl⟩))
        (negative_stable neg v n _ ih)
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨ns,rfl⟩ := hx; exact hword ns
  | zero => simp
  | add x y hx hy ih ih' => simpa only [lie_add] using Submodule.add_mem _ ih ih'
  | smul a x hx ih => simpa only [lie_smul] using Submodule.smul_mem _ a ih

private theorem positive_stable (neg : N → A) (pos : P → A) (v : A) (C : Set A)
    (hCN : ∀ c ∈ C, ∀ n, ⁅c,neg n⁆ ∈ Submodule.span ℂ (Set.range neg))
    (hCv : ∀ c ∈ C, ⁅c,v⁆ ∈ Submodule.span ℂ ({v} : Set A))
    (hPN : ∀ p n, ⁅pos p,neg n⁆ ∈
      Submodule.span ℂ (Set.range neg) ⊔ Submodule.span ℂ C ⊔ Submodule.span ℂ (Set.range pos))
    (hPv : ∀ p, ⁅pos p,v⁆ = 0)
    (p : P) (x : A) (hx : x ∈ negativeSpan neg v) :
    ⁅pos p,x⁆ ∈ negativeSpan neg v := by
  have hword (ns : List N) : ∀ p, ⁅pos p,wordAction neg v ns⁆ ∈ negativeSpan neg v := by
    induction ns with
    | nil => intro p; simp [wordAction,hPv]
    | cons n ns ih =>
      intro p
      let Br : A →ₗ[ℂ] A := {
        toFun := fun z => ⁅z,wordAction neg v ns⁆
        map_add' := fun z z' => add_lie z z' _
        map_smul' := fun a z => smul_lie a z _ }
      have hne : Submodule.span ℂ (Set.range neg) ≤ (negativeSpan neg v).comap Br := by
        apply Submodule.span_le.mpr
        rintro z ⟨n,rfl⟩
        exact negative_stable neg v n _ (Submodule.subset_span ⟨ns,rfl⟩)
      have hca : Submodule.span ℂ C ≤ (negativeSpan neg v).comap Br := by
        apply Submodule.span_le.mpr
        intro c hc
        exact cartan_stable neg v C hCN hCv c hc _ (Submodule.subset_span ⟨ns,rfl⟩)
      have hpo : Submodule.span ℂ (Set.range pos) ≤ (negativeSpan neg v).comap Br := by
        apply Submodule.span_le.mpr
        rintro z ⟨q,rfl⟩
        exact ih q
      have hbr : ⁅⁅pos p,neg n⁆,wordAction neg v ns⁆ ∈ negativeSpan neg v :=
        (sup_le (sup_le hne hca) hpo) (hPN p n)
      rw [wordAction,leibniz_lie]
      exact Submodule.add_mem _ hbr (negative_stable neg v n _ (ih p))
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨ns,rfl⟩ := hx; exact hword ns p
  | zero => simp
  | add x y hx hy ih ih' => simpa only [lie_add] using Submodule.add_mem _ ih ih'
  | smul a x hx ih => simpa only [lie_smul] using Submodule.smul_mem _ a ih

private theorem stable_of_generates (G : Set A) (hG : LieSubalgebra.lieSpan ℂ A G = ⊤)
    (W : Submodule ℂ A) (hW : ∀ g ∈ G, ∀ x ∈ W, ⁅g,x⁆ ∈ W)
    (a x : A) (hx : x ∈ W) : ⁅a,x⁆ ∈ W := by
  have ha : a ∈ LieSubalgebra.lieSpan ℂ A G := by rw [hG]; trivial
  have hall : ∀ x ∈ W, ⁅a,x⁆ ∈ W := by
    induction ha using LieSubalgebra.lieSpan_induction with
    | mem a ha => exact hW a ha
    | zero => intro x hx; simp
    | add a b ha hb ih ih' =>
      intro x hx
      simpa only [add_lie] using W.add_mem (ih x hx) (ih' x hx)
    | smul c a ha ih =>
      intro x hx
      simpa only [smul_lie] using W.smul_mem c (ih x hx)
    | lie a b ha hb ih ih' =>
      intro x hx
      rw [lie_lie]
      exact W.sub_mem (ih _ (ih' x hx)) (ih' _ (ih x hx))
  exact hall x hx

private theorem negative_span_isIdeal (neg : N → A) (pos : P → A) (v : A) (C : Set A)
    (hCN : ∀ c ∈ C, ∀ n, ⁅c,neg n⁆ ∈ Submodule.span ℂ (Set.range neg))
    (hCv : ∀ c ∈ C, ⁅c,v⁆ ∈ Submodule.span ℂ ({v} : Set A))
    (hPN : ∀ p n, ⁅pos p,neg n⁆ ∈
      Submodule.span ℂ (Set.range neg) ⊔ Submodule.span ℂ C ⊔ Submodule.span ℂ (Set.range pos))
    (hPv : ∀ p, ⁅pos p,v⁆ = 0)
    (hgen : LieSubalgebra.lieSpan ℂ A (C ∪ Set.range neg ∪ Set.range pos) = ⊤) :
    ∃ K : LieIdeal ℂ A, K.toSubmodule = negativeSpan neg v := by
  refine ⟨{ negativeSpan neg v with lie_mem := ?_ },rfl⟩
  intro a x hx
  apply stable_of_generates _ hgen _ ?_ a x hx
  intro g hg y hy
  rcases hg with (hc | hn) | hp
  · exact cartan_stable neg v C hCN hCv g hc y hy
  · obtain ⟨n,rfl⟩ := hn
    exact negative_stable neg v n y hy
  · obtain ⟨p,rfl⟩ := hp
    exact positive_stable neg pos v C hCN hCv hPN hPv p y hy


private noncomputable def spectralWeight (α : N → ℂ) (μ : ℂ) : List N → ℂ
  | [] => μ
  | n::ns => spectralWeight α μ ns - α n

private theorem word_eigen (neg : N → A) (v H : A) (α : N → ℂ) (μ : ℂ)
    (hHN : ∀ n, ⁅H,neg n⁆ = (-α n) • neg n) (hHv : ⁅H,v⁆ = μ • v)
    (ns : List N) :
    ⁅H,wordAction neg v ns⁆ = spectralWeight α μ ns • wordAction neg v ns := by
  induction ns with
  | nil => exact hHv
  | cons n ns ih =>
    simp only [wordAction,spectralWeight,leibniz_lie,hHN,ih,smul_lie,lie_smul]
    module

private theorem spectralWeight_negative (α : N → ℂ) (μ : ℂ)
    (hα : ∀ n, 0 < (α n).re) (hμ : μ.re < 0) (ns : List N) :
    (spectralWeight α μ ns).re < 0 := by
  induction ns with
  | nil => exact hμ
  | cons n ns ih =>
    simp only [spectralWeight,Complex.sub_re]
    have := hα n
    linarith

private theorem negative_span_disjoint_cartan (neg : N → A) (v H : A) (α : N → ℂ) (μ : ℂ)
    (hHN : ∀ n, ⁅H,neg n⁆ = (-α n) • neg n) (hHv : ⁅H,v⁆ = μ • v)
    (hα : ∀ n, 0 < (α n).re) (hμ : μ.re < 0)
    (C : Set A) (hHC : ∀ c ∈ C, ⁅H,c⁆ = 0) :
    negativeSpan neg v ⊓ Submodule.span ℂ C = ⊥ := by
  let E : Module.End ℂ A := LieModule.toEnd ℂ A A H
  let S : Set ℂ := {z | z.re < 0}
  let Q : Submodule ℂ A := ⨆ z ∈ S, E.eigenspace z
  have hW : negativeSpan neg v ≤ Q := by
    apply Submodule.span_le.mpr
    rintro x ⟨ns,rfl⟩
    have heig : wordAction neg v ns ∈ E.eigenspace (spectralWeight α μ ns) :=
      Module.End.mem_eigenspace_iff.mpr (word_eigen neg v H α μ hHN hHv ns)
    have hneg : spectralWeight α μ ns ∈ S := spectralWeight_negative α μ hα hμ ns
    have hle : E.eigenspace (spectralWeight α μ ns) ≤ Q :=
      le_iSup_of_le (spectralWeight α μ ns) (le_iSup_of_le hneg le_rfl)
    exact hle heig
  have hC : Submodule.span ℂ C ≤ E.eigenspace 0 := by
    apply Submodule.span_le.mpr
    intro c hc
    apply Module.End.mem_eigenspace_iff.mpr
    simpa [E] using hHC c hc
  have hnot : (0 : ℂ) ∉ S := by simp [S]
  have hdisj : Disjoint (E.eigenspace 0) Q := E.eigenspaces_iSupIndep.disjoint_biSup hnot
  exact disjoint_iff.mp ((hdisj.mono hC hW).symm)

theorem nonzero_disjoint_ideal (neg : N → A) (pos : P → A) (v H : A) (C : Set A)
    (hCN : ∀ c ∈ C, ∀ n, ⁅c,neg n⁆ ∈ Submodule.span ℂ (Set.range neg))
    (hCv : ∀ c ∈ C, ⁅c,v⁆ ∈ Submodule.span ℂ ({v} : Set A))
    (hPN : ∀ p n, ⁅pos p,neg n⁆ ∈
      Submodule.span ℂ (Set.range neg) ⊔ Submodule.span ℂ C ⊔ Submodule.span ℂ (Set.range pos))
    (hPv : ∀ p, ⁅pos p,v⁆ = 0)
    (hgen : LieSubalgebra.lieSpan ℂ A (C ∪ Set.range neg ∪ Set.range pos) = ⊤)
    (α : N → ℂ) (μ : ℂ)
    (hHN : ∀ n, ⁅H,neg n⁆ = (-α n) • neg n) (hHv : ⁅H,v⁆ = μ • v)
    (hα : ∀ n, 0 < (α n).re) (hμ : μ.re < 0)
    (hHC : ∀ c ∈ C, ⁅H,c⁆ = 0) (hv : v ≠ 0) :
    ∃ K : LieIdeal ℂ A, K ≠ ⊥ ∧ K.toSubmodule ⊓ Submodule.span ℂ C = ⊥ := by
  obtain ⟨K,hK⟩ := negative_span_isIdeal neg pos v C hCN hCv hPN hPv hgen
  refine ⟨K, ?_, ?_⟩
  · intro hz
    have hmem : v ∈ K := by change v ∈ K.toSubmodule; rw [hK]; exact seed_mem neg v
    rw [hz] at hmem
    exact hv hmem
  · rw [hK]
    exact negative_span_disjoint_cartan neg v H α μ hHN hHv hα hμ C hHC


end D5.S3.VertexAlgebra.Sectors.VBKMWeightIdeal
