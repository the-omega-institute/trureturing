/- GID: D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion
   mirror-E: none(waiver:symbolic-weighted-partition-identity)
   anchors: []
   digest: Actual independent sets give a weighted deletion identity without nonzero premises. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

open scoped BigOperators

variable {α R T : Type*} [DecidableEq α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

/-- All independent subsets of the actual finite vertex domain, using Mathlib's
independence predicate. The ambient vertex type need not be finite. -/
def configurations (V : Finset α) : Finset (Finset α) :=
  V.powerset.filter fun S => G.IsIndepSet (S : Set α)

/-- The multivariate hard-core partition sum over actual independent subsets. -/
def partition [CommSemiring R] (V : Finset α) (w : α → R) : R :=
  ∑ S ∈ configurations G V, ∏ v ∈ S, w v

/-- Delete the root and all its neighbors within the finite vertex domain. -/
def closedComplement (V : Finset α) (v : α) : Finset α :=
  (V.erase v).filter fun u => ¬ G.Adj v u

private theorem mem_configurations (V S : Finset α) :
    S ∈ configurations G V ↔ S ⊆ V ∧ G.IsIndepSet (S : Set α) := by
  simp [configurations]

private theorem mem_closedComplement (V : Finset α) (v u : α) :
    u ∈ closedComplement G V v ↔ u ∈ V ∧ u ≠ v ∧ ¬ G.Adj v u := by
  simp only [closedComplement, Finset.mem_filter, Finset.mem_erase]
  tauto

private theorem root_absent (V S : Finset α) (v : α)
    (hS : S ∈ configurations G (closedComplement G V v)) : v ∉ S := by
  intro hv
  have hm := (mem_configurations G _ _).mp hS
  exact ((mem_closedComplement G V v v).mp (hm.1 hv)).2.1 rfl

private theorem insert_configuration (V S : Finset α) (v : α) (hv : v ∈ V)
    (hS : S ∈ configurations G (closedComplement G V v)) :
    insert v S ∈ configurations G V := by
  obtain ⟨hsub, hind⟩ := (mem_configurations G _ _).mp hS
  apply (mem_configurations G _ _).mpr
  constructor
  · intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hv
    · exact ((mem_closedComplement G V v u).mp (hsub hu)).1
  · intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with hxv | hx
    · subst x
      rcases Finset.mem_insert.mp hy with hyv | hy
      · subst y
        exact False.elim (hxy rfl)
      · exact ((mem_closedComplement G V v y).mp (hsub hy)).2.2
    · rcases Finset.mem_insert.mp hy with hyv | hy
      · subst y
        intro hadj
        exact ((mem_closedComplement G V v x).mp (hsub hx)).2.2 (G.adj_symm hadj)
      · exact hind hx hy hxy

private theorem erase_configuration (V S : Finset α) (v : α)
    (hS : S ∈ configurations G V) (hv : v ∈ S) :
    S.erase v ∈ configurations G (closedComplement G V v) := by
  obtain ⟨hsub, hind⟩ := (mem_configurations G _ _).mp hS
  apply (mem_configurations G _ _).mpr
  constructor
  · intro u hu
    obtain ⟨hne, huS⟩ := Finset.mem_erase.mp hu
    exact (mem_closedComplement G V v u).mpr
      ⟨hsub huS, hne, hind hv huS hne.symm⟩
  · intro x hx y hy hxy
    exact hind (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) hxy

private theorem configuration_split (V : Finset α) (v : α) (hv : v ∈ V) :
    configurations G V = configurations G (V.erase v) ∪
      (configurations G (closedComplement G V v)).image (insert v) := by
  ext S
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · intro hS
    obtain ⟨hsub, hind⟩ := (mem_configurations G _ _).mp hS
    by_cases hvS : v ∈ S
    · exact Or.inr ⟨S.erase v, erase_configuration G V S v hS hvS,
        Finset.insert_erase hvS⟩
    · left
      apply (mem_configurations G _ _).mpr
      refine ⟨?_, hind⟩
      intro u hu
      refine Finset.mem_erase.mpr ⟨?_, hsub hu⟩
      intro he
      subst u
      exact hvS hu
  · rintro (hS | ⟨S, hS, rfl⟩)
    · obtain ⟨hsub, hind⟩ := (mem_configurations G _ _).mp hS
      exact (mem_configurations G _ _).mpr
        ⟨fun _ hu => Finset.mem_of_mem_erase (hsub hu), hind⟩
    · exact insert_configuration G V S v hv hS

private theorem configuration_split_disjoint (V : Finset α) (v : α) :
    Disjoint (configurations G (V.erase v))
      ((configurations G (closedComplement G V v)).image (insert v)) := by
  apply Finset.disjoint_left.mpr
  intro S hS himage
  obtain ⟨U, hU, he⟩ := Finset.mem_image.mp himage
  have hvS : v ∈ S := he ▸ Finset.mem_insert_self v U
  have hvErase := ((mem_configurations G _ _).mp hS).1 hvS
  exact Finset.notMem_erase v V hvErase

/-- Partition the actual independent configurations by root occupancy.
The identity holds over every commutative semiring, including polynomial rings,
and has no division, positivity, or nonvanishing assumption. -/
theorem partition_delete [CommSemiring R] (V : Finset α) (v : α)
    (hv : v ∈ V) (w : α → R) :
    partition G V w = partition G (V.erase v) w +
      w v * partition G (closedComplement G V v) w := by
  unfold partition
  rw [configuration_split G V v hv,
    Finset.sum_union (configuration_split_disjoint G V v)]
  congr 1
  calc
    _ = ∑ S ∈ configurations G (closedComplement G V v),
        ∏ u ∈ insert v S, w u := by
      apply Finset.sum_image
      intro S hS U hU he
      have he' := congrArg (fun F : Finset α => F.erase v) he
      simpa [root_absent G V S v hS, root_absent G V U v hU] using he'
    _ = ∑ S ∈ configurations G (closedComplement G V v),
        w v * ∏ u ∈ S, w u := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.prod_insert (root_absent G V S v hS)]
    _ = _ := by rw [Finset.mul_sum]

/-- The empty configuration gives the empty domain partition value one. -/
theorem partition_empty [CommSemiring R] (w : α → R) :
    partition G ∅ w = 1 := by
  simp [partition, configurations, Finset.filter_singleton, SimpleGraph.IsIndepSet,
    Set.Pairwise]

/-- A scalar homomorphism evaluates the same independent-set sum, so an
algebraic identity is transported without changing its configuration semantics. -/
theorem map_partition [CommSemiring R] [CommSemiring T]
    (f : R →+* T) (V : Finset α) (w : α → R) :
    f (partition G V w) = partition G V (fun v => f (w v)) := by
  simp [partition]

/-- The ordinary independence polynomial on the same finite induced domain. -/
noncomputable def independencePolynomial (V : Finset α) : Polynomial ℤ :=
  partition G V (fun _ => Polynomial.X)

/-- Complex evaluation is exactly the hard-core sum used by the deletion
identity. No recursively defined surrogate polynomial is substituted. -/
theorem independencePolynomial_eval (V : Finset α) (z : ℂ) :
    Polynomial.eval₂ (Int.castRingHom ℂ) z (independencePolynomial G V) =
      partition G V (fun _ => z) := by
  simpa [independencePolynomial] using
    map_partition G (Polynomial.eval₂RingHom (Int.castRingHom ℂ) z) V
      (fun _ => (Polynomial.X : Polynomial ℤ))

/-- For nonnegative real activities every finite-domain partition is at least
one, witnessed by the empty independent configuration. -/
theorem one_le_partition (V : Finset α) (w : α → ℝ) (hw : ∀ v ∈ V, 0 ≤ w v) :
    1 ≤ partition G V w := by
  have hempty : (∅ : Finset α) ∈ configurations G V := by
    simp [configurations, SimpleGraph.IsIndepSet, Set.Pairwise]
  have hnonneg (S : Finset α) (hS : S ∈ configurations G V) :
      0 ≤ ∏ v ∈ S, w v := by
    apply Finset.prod_nonneg
    intro v hv
    exact hw v (((mem_configurations G V S).mp hS).1 hv)
  simpa [partition] using Finset.single_le_sum hnonneg hempty

#print axioms partition_delete
#print axioms partition_empty
#print axioms map_partition
#print axioms independencePolynomial_eval
#print axioms one_le_partition

end D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
