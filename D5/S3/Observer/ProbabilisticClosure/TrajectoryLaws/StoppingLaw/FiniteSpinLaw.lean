/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteSpinLaw
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteSpinLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Bernoulli configurations have positive weights and exact cylinder masses. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.StoppingMass
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace FiniteSpinLaw

variable {ι : Type*} [Fintype ι]

def weight (β : Bias) (σ : ι → Bool) : ℝ := ∏ i, β.π (σ i)

def mass (β : Bias) (E : Set (ι → Bool)) : ℝ :=
  ∑ σ, if σ ∈ E then weight β σ else 0

theorem weight_pos (β : Bias) (σ : ι → Bool) : 0 < weight β σ :=
  Finset.prod_pos fun _ _ => β.π_pos _

theorem weight_sum (β : Bias) : ∑ σ : ι → Bool, weight β σ = 1 := by
  rw [show (∑ σ : ι → Bool, weight β σ) = ∏ _ : ι, ∑ s : Bool, β.π s from
    (Fintype.prod_sum (fun (_ : ι) (s : Bool) => β.π s)).symm]
  simp [Fintype.sum_bool, Bias.π]

theorem mass_nonneg (β : Bias) (E : Set (ι → Bool)) : 0 ≤ mass β E := by
  apply Finset.sum_nonneg
  intro σ _
  split_ifs
  · exact (weight_pos β σ).le
  · exact le_rfl

@[simp] theorem mass_univ (β : Bias) : mass (ι := ι) β Set.univ = 1 := by
  simpa [mass] using weight_sum (ι := ι) β

@[simp] theorem mass_empty (β : Bias) : mass (ι := ι) β ∅ = 0 := by simp [mass]

theorem mass_mono (β : Bias) {E F : Set (ι → Bool)} (h : E ⊆ F) :
    mass β E ≤ mass β F := by
  apply Finset.sum_le_sum
  intro σ _
  by_cases he : σ ∈ E
  · simp [he, h he]
  · simp only [he, ↓reduceIte]
    split_ifs
    · exact (weight_pos β σ).le
    · exact le_rfl

theorem mass_union (β : Bias) {E F : Set (ι → Bool)} (h : Disjoint E F) :
    mass β (E ∪ F) = mass β E + mass β F := by
  rw [mass, mass, mass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  have hn : ¬(σ ∈ E ∧ σ ∈ F) := fun hh => Set.disjoint_left.mp h hh.1 hh.2
  by_cases he : σ ∈ E <;> by_cases hf : σ ∈ F <;> simp_all

theorem mass_diff (β : Bias) {E F : Set (ι → Bool)} (h : F ⊆ E) :
    mass β (E \ F) = mass β E - mass β F := by
  have hu : E = (E \ F) ∪ F := by ext σ; simp only [Set.mem_union, Set.mem_diff]; tauto
  have hd : Disjoint (E \ F) F := Set.disjoint_sdiff_left
  have he := mass_union β hd
  rw [← hu] at he
  linarith

theorem mass_pos_iff (β : Bias) (E : Set (ι → Bool)) :
    0 < mass β E ↔ E.Nonempty := by
  constructor
  · intro hp
    by_contra hn
    have he : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [he] at hp
  · rintro ⟨σ, hσ⟩
    have hle : weight β σ ≤ mass β E := by
      calc
        weight β σ = if σ ∈ E then weight β σ else 0 := by simp [hσ]
        _ ≤ ∑ τ : ι → Bool, if τ ∈ E then weight β τ else 0 :=
          Finset.single_le_sum (f := fun τ : ι → Bool => if τ ∈ E then weight β τ else 0) (fun τ _ => by
            split_ifs
            · exact (weight_pos β τ).le
            · exact le_rfl) (Finset.mem_univ σ)
    exact (weight_pos β σ).trans_le hle

/-- A finite probability-one assertion holds at every configuration. -/
theorem mass_one_iff (β : Bias) (E : Set (ι → Bool)) :
    mass β E = 1 ↔ E = Set.univ := by
  constructor
  · intro he
    have hdiff := mass_diff β (show E ⊆ Set.univ from Set.subset_univ E)
    rw [mass_univ, he, sub_self] at hdiff
    by_contra hn
    have hnon : (Set.univ \ E).Nonempty := by
      by_contra h
      have : Set.univ ⊆ E := by
        intro σ _
        by_contra hx
        exact h ⟨σ, trivial, hx⟩
      exact hn (Set.Subset.antisymm (Set.subset_univ E) this)
    have hp := (mass_pos_iff β _).2 hnon
    linarith
  · rintro rfl; exact mass_univ β

/-- Arbitrary coordinatewise constraints factor as a finite product. -/
theorem mass_pi (β : Bias) (A : ι → Set Bool) :
    mass β {σ | ∀ i, σ i ∈ A i} =
      ∏ i, ∑ s : Bool, if s ∈ A i then β.π s else 0 := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simpa only [mass, weight, Set.mem_setOf_eq] using
    (Fintype.prod_ite_zero (p := fun i => σ i ∈ A i) (f := fun i => β.π (σ i))).symm

/-- Prescribing a finite set of coordinates leaves every other spin unrestricted. -/
theorem prescribed_mass (β : Bias) (A : Finset ι) (v : ι → Bool) :
    mass β {σ | ∀ i ∈ A, σ i = v i} = ∏ i ∈ A, β.π (v i) := by
  have hs : {σ : ι → Bool | ∀ i ∈ A, σ i = v i} =
      {σ | ∀ i, σ i ∈ (if i ∈ A then {v i} else Set.univ : Set Bool)} := by
    ext σ
    constructor
    · intro h i
      by_cases hi : i ∈ A
      · simpa [hi] using h i hi
      · simp [hi]
    · intro h i hi; simpa [hi] using h i
  rw [hs, mass_pi]
  have hcoord (i : ι) :
      (∑ s : Bool, if s ∈ (if i ∈ A then {v i} else Set.univ : Set Bool)
        then β.π s else 0) = if i ∈ A then β.π (v i) else 1 := by
    by_cases hi : i ∈ A
    · simp [hi, Fintype.sum_bool]
    · simp [hi, Fintype.sum_bool, Bias.π]
  simp_rw [hcoord]
  exact Finset.prod_ite_mem_eq A (fun i => β.π (v i))

theorem constant_mass (β : Bias) (A : Finset ι) (s : Bool) :
    mass β {σ | ∀ i ∈ A, σ i = s} = (β.π s)^A.card := by
  rw [prescribed_mass]
  simp

/-- Nonempty monochromatic blocks split into two disjoint constant-spin cylinders. -/
theorem monochromatic_mass (β : Bias) (A : Finset ι) (ha : A.Nonempty) :
    mass β {σ | (∀ i ∈ A, σ i = false) ∨ (∀ i ∈ A, σ i = true)} = β.T A.card := by
  have hd : Disjoint {σ : ι → Bool | ∀ i ∈ A, σ i = false}
      {σ | ∀ i ∈ A, σ i = true} := by
    apply Set.disjoint_left.mpr
    intro σ h0 h1
    rcases ha with ⟨i, hi⟩
    have := (h0 i hi).symm.trans (h1 i hi)
    cases this
  change mass β ({σ | ∀ i ∈ A, σ i = false} ∪ {σ | ∀ i ∈ A, σ i = true}) = _
  rw [mass_union β hd, constant_mass, constant_mass]
  rfl

end FiniteSpinLaw
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
