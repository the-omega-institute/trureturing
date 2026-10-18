/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteMarginals
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteMarginals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Bernoulli marginals preserve arbitrary events under coordinate restriction. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteSpinLaw
import Mathlib.Logic.Equiv.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace FiniteSpinLaw

variable {ι : Type*} [Fintype ι]

def restrict (A : Finset ι) (σ : ι → Bool) : A → Bool := fun i => σ i

theorem restriction_fiber_mass (β : Bias) (A : Finset ι) (τ : A → Bool) :
    mass β {σ : ι → Bool | restrict A σ = τ} = weight β τ := by
  let v : ι → Bool := fun i => if h : i ∈ A then τ ⟨i, h⟩ else false
  have he : {σ : ι → Bool | restrict A σ = τ} = {σ | ∀ i ∈ A, σ i = v i} := by
    ext σ
    constructor
    · intro h i hi
      have hh := congrFun h ⟨i, hi⟩
      simpa [restrict, v, hi] using hh
    · intro h
      funext i
      simpa [restrict, v, i.property] using h i i.property
  rw [he, prescribed_mass]
  have hp : (∏ i ∈ A, β.π (v i)) = ∏ i : A, β.π (v i) :=
    (Finset.prod_coe_sort A (fun i => β.π (v i))).symm
  rw [hp]
  simp only [v, dif_pos (Subtype.property _), weight]

/-- Marginalization is proved for every event, not just constant-spin cylinders. -/
theorem restriction_mass (β : Bias) (A : Finset ι) (E : Set (A → Bool)) :
    mass β {σ : ι → Bool | restrict A σ ∈ E} = mass β E := by
  have hsingle (σ : ι → Bool) :
      (if restrict A σ ∈ E then weight β σ else 0) =
      ∑ τ : A → Bool, if τ ∈ E then
        (if restrict A σ = τ then weight β σ else 0) else 0 := by
    rw [Finset.sum_eq_single (restrict A σ)]
    · by_cases he : restrict A σ ∈ E <;> simp [he]
    · intro τ _ hτ
      have hn : restrict A σ ≠ τ := Ne.symm hτ
      simp [hn]
    · simp
  unfold mass
  simp only [Set.mem_setOf_eq]
  simp_rw [hsingle]
  rw [Finset.sum_comm]
  refine Finset.sum_congr (by ext; simp) ?_
  intro τ _
  by_cases he : τ ∈ E
  · simp only [he, ↓reduceIte]
    have hf := restriction_fiber_mass β A τ
    unfold mass at hf
    calc
      _ = _ := Finset.sum_congr (by ext; simp) (by intro σ _; simp)
      _ = _ := hf
  · simp [he]

/-- An arbitrary coordinate partition has independent product marginals. -/
theorem partition_mass (β : Bias) (p : ι → Prop) [DecidablePred p]
    (E : Set ({i // p i} → Bool)) (F : Set ({i // ¬p i} → Bool)) :
    mass β {σ : ι → Bool | (fun i : {i // p i} => σ i) ∈ E ∧
      (fun i : {i // ¬p i} => σ i) ∈ F} = mass β E * mass β F := by
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => Bool)
  have hw (σ : ι → Bool) : weight β σ = weight β (e σ).1 * weight β (e σ).2 := by
    exact (Fintype.prod_subtype_mul_prod_subtype p (fun i => β.π (σ i))).symm
  unfold mass
  simp only [Set.mem_setOf_eq]
  rw [show (∑ σ : ι → Bool, if
      (fun i : {i // p i} => σ i) ∈ E ∧ (fun i : {i // ¬p i} => σ i) ∈ F
      then weight β σ else 0) =
      ∑ z : ({i // p i} → Bool) × ({i // ¬p i} → Bool),
        if z.1 ∈ E ∧ z.2 ∈ F then weight β z.1 * weight β z.2 else 0 from
    Fintype.sum_equiv e _ _ (fun σ => by rw [hw]; rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr (by ext; simp) ?_
  intro σ _
  refine Finset.sum_congr (by ext; simp) ?_
  intro τ _
  by_cases he : σ ∈ E <;> by_cases hf : τ ∈ F <;> simp [he, hf]

/-- Reindexing a finite coordinate carrier preserves every event mass. -/
theorem reindex_mass {κ : Type*} [Fintype κ] (β : Bias) (e : ι ≃ κ)
    (E : Set (κ → Bool)) :
    mass β {σ : ι → Bool | (fun i => σ (e.symm i)) ∈ E} = mass β E := by
  let q : (ι → Bool) ≃ (κ → Bool) :=
    { toFun := fun σ i => σ (e.symm i)
      invFun := fun τ i => τ (e i)
      left_inv := by intro σ; funext i; simp
      right_inv := by intro σ; funext i; simp }
  have hw (σ : ι → Bool) : weight β σ = weight β (q σ) := by
    apply Fintype.prod_equiv e
    intro i
    simp [q]
  unfold mass
  simp only [Set.mem_setOf_eq]
  exact Fintype.sum_equiv q _ _ (fun σ => by rw [hw]; rfl)

/-- Events depending on disjoint coordinate sets are independent. -/
theorem disjoint_event_mass (β : Bias) (A B : Finset ι) (hd : Disjoint A B)
    (E F : Set (ι → Bool))
    (hE : ∀ σ τ : ι → Bool, (∀ i ∈ A, σ i = τ i) → (σ ∈ E ↔ τ ∈ E))
    (hF : ∀ σ τ : ι → Bool, (∀ i ∈ B, σ i = τ i) → (σ ∈ F ↔ τ ∈ F)) :
    mass β (E ∩ F) = mass β E * mass β F := by
  let E' : Set ({i // i ∈ A} → Bool) :=
    {σ | (fun i => if hi : i ∈ A then σ ⟨i, hi⟩ else false) ∈ E}
  let F' : Set ({i // i ∉ A} → Bool) :=
    {σ | (fun i => if hi : i ∉ A then σ ⟨i, hi⟩ else false) ∈ F}
  have he (σ : ι → Bool) : σ ∈ E ↔ (fun i : {i // i ∈ A} => σ i) ∈ E' := by
    apply hE
    intro i hi
    simp [hi]
  have hf (σ : ι → Bool) : σ ∈ F ↔ (fun i : {i // i ∉ A} => σ i) ∈ F' := by
    apply hF
    intro i hi
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    simp [hn]
  have heq : E ∩ F = {σ | (fun i : {i // i ∈ A} => σ i) ∈ E' ∧
      (fun i : {i // i ∉ A} => σ i) ∈ F'} := by ext σ; exact and_congr (he σ) (hf σ)
  have heqE : E = {σ | (fun i : {i // i ∈ A} => σ i) ∈ E'} := by ext σ; exact he σ
  have heqF : F = {σ | (fun i : {i // i ∉ A} => σ i) ∈ F'} := by ext σ; exact hf σ
  rw [heq, partition_mass]
  have hmE := partition_mass β (fun i : ι => i ∈ A) E' Set.univ
  have hmF := partition_mass β (fun i : ι => i ∈ A) Set.univ F'
  simp only [Set.mem_univ, and_true, true_and, mass_univ, mul_one, one_mul] at hmE hmF
  rw [heqE, heqF, hmE, hmF]

end FiniteSpinLaw
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
