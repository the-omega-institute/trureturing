/- GID: D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy
   mirror-E: none(waiver:symbolic-insertion-energy-identity)
   anchors: []
   utility: none
   digest: A finite erasure-closed product law gives every joint occupation insertion energy. -/

/-
proof_shape: monomial_dirichlet: content
escape_witness: occupied-endpoint reindexing of the joint monomial
  insertion increments on an arbitrary finite erasure-closed family.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only).
Private helpers organize the live reindexing and Boolean increment proof.
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.StatisticalMechanics.HardCore.MonomialInsertionEnergy

open scoped BigOperators
variable {α K : Type*} [DecidableEq α] [Field K]

/-- The original finite product-activity law, with total field division. -/
def mass (Ω : Finset (Finset α)) (activity : α → K) (s : Finset α) : K :=
  (∏ i ∈ s, activity i) / (∑ t ∈ Ω, ∏ i ∈ t, activity i)

/-- A joint occupation is one exactly when its marked sites are all occupied. -/
def monomial (I s : Finset α) : K := if I ⊆ s then 1 else 0

/-- A moment of the same original law, including the empty marked set. -/
def moment (Ω : Finset (Finset α)) (activity : α → K) (I : Finset α) : K :=
  ∑ s ∈ Ω, mass Ω activity s * monomial I s

/-- Empty endpoints of the actual legal insertion edges at one site. -/
def insertionStates (Ω : Finset (Finset α)) (i : α) : Finset (Finset α) :=
  Ω.filter fun s => i ∉ s ∧ insert i s ∈ Ω

/-- The bilinear heat-bath form counts each permitted insertion edge once. -/
def dirichlet (Ω : Finset (Finset α)) (V : Finset α) (activity w : α → K)
    (f g : Finset α → K) : K :=
  ∑ i ∈ V, ∑ s ∈ insertionStates Ω i,
    mass Ω activity s * w i * (activity i / (1 + activity i)) *
      (f (insert i s) - f s) * (g (insert i s) - g s)

private theorem mass_insert (Ω : Finset (Finset α)) (activity : α → K)
    (s : Finset α) (i : α) (hi : i ∉ s) :
    mass Ω activity (insert i s) = activity i * mass Ω activity s := by
  simp only [mass, Finset.prod_insert hi]
  ring

private theorem monomial_increment (I s : Finset α) (i : α) (hi : i ∉ s) :
    monomial (K := K) I (insert i s) - monomial I s =
      if i ∈ I then monomial I (insert i s) else 0 := by
  by_cases hiI : i ∈ I
  · have hnot : ¬ I ⊆ s := fun h => hi (h hiI)
    simp [hiI, monomial, hnot]
  · have he : I ⊆ insert i s ↔ I ⊆ s := by
      constructor
      · intro h j hj
        rcases Finset.mem_insert.mp (h hj) with he | hs
        · subst j
          exact False.elim (hiI hj)
        · exact hs
      · exact fun h => h.trans (Finset.subset_insert i s)
    simp [hiI, monomial, he]

private theorem monomial_mul (I J s : Finset α) :
    monomial (K := K) I s * monomial J s = monomial (I ∪ J) s := by
  by_cases hI : I ⊆ s <;> by_cases hJ : J ⊆ s <;>
    simp [monomial, Finset.union_subset_iff, hI, hJ]

private theorem occupied_reindex (Ω : Finset (Finset α))
    (hΩ : ∀ s ∈ Ω, ∀ i ∈ s, s.erase i ∈ Ω)
    (activity : α → K) (I : Finset α) (i : α) (hiI : i ∈ I) :
    (∑ s ∈ insertionStates Ω i,
      mass Ω activity (insert i s) * monomial I (insert i s)) = moment Ω activity I := by
  have hfilter :
      (Ω.filter (fun t => i ∈ t)).filter (fun t => I ⊆ t) =
        Ω.filter (fun t => I ⊆ t) := by
    ext t
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 hiI⟩, h.2⟩⟩
  calc
    _ = ∑ t ∈ Ω.filter (fun t => i ∈ t), mass Ω activity t * monomial I t := by
      apply Finset.sum_bij (fun s _ => insert i s)
      · intro s hs
        have hs' := Finset.mem_filter.mp hs
        exact Finset.mem_filter.mpr ⟨hs'.2.2, Finset.mem_insert_self i s⟩
      · intro s hs t ht he
        have hsi := (Finset.mem_filter.mp hs).2.1
        have hti := (Finset.mem_filter.mp ht).2.1
        have he' := congrArg (fun u : Finset α => u.erase i) he
        simpa [hsi, hti] using he'
      · intro t ht
        obtain ⟨htΩ, hit⟩ := Finset.mem_filter.mp ht
        refine ⟨t.erase i, ?_, Finset.insert_erase hit⟩
        exact Finset.mem_filter.mpr
          ⟨hΩ t htΩ i hit, Finset.notMem_erase i t,
            (Finset.insert_erase hit).symm ▸ htΩ⟩
      · intro s _
        rfl
    _ = ∑ t ∈ Ω.filter (fun t => I ⊆ t), mass Ω activity t := by
      simp only [monomial, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, hfilter]
    _ = moment Ω activity I := by
      simp only [moment, monomial, mul_ite, mul_one, mul_zero, Finset.sum_filter]

private theorem site_energy (Ω : Finset (Finset α))
    (hΩ : ∀ s ∈ Ω, ∀ i ∈ s, s.erase i ∈ Ω)
    (activity w : α → K) (I J : Finset α) (i : α) :
    (∑ s ∈ insertionStates Ω i,
      mass Ω activity s * w i * (activity i / (1 + activity i)) *
        (monomial I (insert i s) - monomial I s) *
        (monomial J (insert i s) - monomial J s)) =
    moment Ω activity (I ∪ J) *
      (if i ∈ I ∩ J then w i / (1 + activity i) else 0) := by
  by_cases hi : i ∈ I ∩ J
  · obtain ⟨hiI, hiJ⟩ := Finset.mem_inter.mp hi
    simp only [hi, ite_true]
    calc
      _ = ∑ s ∈ insertionStates Ω i,
          (mass Ω activity (insert i s) * monomial (I ∪ J) (insert i s)) *
            (w i / (1 + activity i)) := by
        apply Finset.sum_congr rfl
        intro s hs
        have hsi := (Finset.mem_filter.mp hs).2.1
        rw [monomial_increment I s i hsi, monomial_increment J s i hsi]
        simp only [hiI, hiJ, ite_true]
        rw [mass_insert Ω activity s i hsi, ← monomial_mul]
        ring
      _ = _ := by
        rw [← Finset.sum_mul,
          occupied_reindex Ω hΩ activity (I ∪ J) i (Finset.mem_union_left J hiI)]
  · simp only [hi, ite_false, mul_zero]
    apply Finset.sum_eq_zero
    intro s hs
    have hsi := (Finset.mem_filter.mp hs).2.1
    rw [monomial_increment I s i hsi, monomial_increment J s i hsi]
    by_cases hiI : i ∈ I
    · have hiJ : i ∉ J := fun h => hi (Finset.mem_inter.mpr ⟨hiI, h⟩)
      simp [hiI, hiJ]
    · simp [hiI]

/-- All joint occupation energies use the same original law and edges.
No positivity or nonzero denominator is needed for this field identity;
the probability interpretation additionally requires positive activities. -/
theorem monomial_dirichlet (Ω : Finset (Finset α))
    (hΩ : ∀ s ∈ Ω, ∀ i ∈ s, s.erase i ∈ Ω)
    (V : Finset α) (activity w : α → K) (I J : Finset α) :
    dirichlet Ω V activity w (monomial I) (monomial J) =
      moment Ω activity (I ∪ J) *
        ∑ i ∈ V.filter (fun i => i ∈ I ∩ J), w i / (1 + activity i) := by
  unfold dirichlet
  simp_rw [site_energy Ω hΩ activity w I J]
  rw [← Finset.mul_sum, Finset.sum_filter]

#print axioms monomial_dirichlet

end D5.S3.StatisticalMechanics.HardCore.MonomialInsertionEnergy
