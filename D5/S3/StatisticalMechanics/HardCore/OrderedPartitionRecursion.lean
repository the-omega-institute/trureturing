/- GID: D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion
   mirror-E: none(waiver:symbolic-exact-neighbor-elimination)
   anchors: []
   digest: Ordered actual-subgraph factors telescope and propagate local nonvanishing. -/

import D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.OrderedPartitionRecursion

open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

variable {α R K : Type*} [DecidableEq α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

/-- The actual domain remaining after the listed vertex deletions. -/
def afterErases (V : Finset α) : List α → Finset α
  | [] => V
  | v :: l => afterErases (V.erase v) l

/-- Product of the vacant numerators along the successive actual domains. -/
def numeratorProduct [CommSemiring R] (w : α → R) (V : Finset α) : List α → R
  | [] => 1
  | v :: l => partition G (V.erase v) w * numeratorProduct w (V.erase v) l

/-- Product of the corresponding pre-deletion partitions. -/
def denominatorProduct [CommSemiring R] (w : α → R) (V : Finset α) : List α → R
  | [] => 1
  | v :: l => partition G V w * denominatorProduct w (V.erase v) l

/-- The actual product of vacancy ratios, retaining the ordered intermediate
subgraphs. The field inverse is only used with nonzero denominators downstream. -/
def vacancyProduct [Field K] (w : α → K) (V : Finset α) : List α → K
  | [] => 1
  | v :: l => (partition G (V.erase v) w / partition G V w) *
      vacancyProduct w (V.erase v) l

/-- The final deleted set depends on the listed vertices, while intermediate
subgraphs and individual vacancy ratios may depend on their order. -/
theorem afterErases_eq_sdiff (V : Finset α) (l : List α) :
    afterErases V l = V \ l.toFinset := by
  induction l generalizing V with
  | nil => simp [afterErases]
  | cons v l ih =>
      rw [afterErases, ih]
      ext u
      simp only [List.toFinset_cons, Finset.mem_sdiff, Finset.mem_erase,
        Finset.mem_insert]
      tauto

/-- Cross multiplication makes the telescoping identity valid at zeros too.
No partition function is assumed nonzero. -/
theorem telescoping_cross [CommSemiring R] (w : α → R) (V : Finset α) (l : List α) :
    partition G V w * numeratorProduct G w V l =
      partition G (afterErases V l) w * denominatorProduct G w V l := by
  induction l generalizing V with
  | nil => simp [numeratorProduct, denominatorProduct, afterErases]
  | cons v l ih =>
      simp only [numeratorProduct, denominatorProduct, afterErases]
      rw [ih (V.erase v)]
      ring

/-- Listing all neighbors identifies the final domain with the actual closed
neighborhood deletion. Repeated entries cause no problem for this identity. -/
theorem afterErases_neighbors (V : Finset α) (v : α) (l : List α)
    (hl : l.toFinset = V.filter (G.Adj v)) :
    afterErases (V.erase v) l = closedComplement G V v := by
  rw [afterErases_eq_sdiff, hl]
  ext u
  simp only [closedComplement, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_erase]
  tauto

/-- Exact ordered hard-core recurrence in denominator-cleared form. It is a
polynomial identity over any commutative semiring and remains valid at every
complex activity, including zeros of the intermediate partitions. -/
theorem ordered_partition_cross [CommSemiring R] (w : α → R)
    (V : Finset α) (v : α) (hv : v ∈ V) (l : List α)
    (hl : l.toFinset = V.filter (G.Adj v)) :
    partition G V w * denominatorProduct G w (V.erase v) l =
      partition G (V.erase v) w *
        (denominatorProduct G w (V.erase v) l +
          w v * numeratorProduct G w (V.erase v) l) := by
  have ht := telescoping_cross G w (V.erase v) l
  rw [afterErases_neighbors G V v l hl] at ht
  calc
    _ = (partition G (V.erase v) w + w v * partition G (closedComplement G V v) w) *
        denominatorProduct G w (V.erase v) l := by rw [partition_delete G V v hv w]
    _ = partition G (V.erase v) w * denominatorProduct G w (V.erase v) l +
        w v * (partition G (closedComplement G V v) w *
          denominatorProduct G w (V.erase v) l) := by ring
    _ = partition G (V.erase v) w * denominatorProduct G w (V.erase v) l +
        w v * (partition G (V.erase v) w * numeratorProduct G w (V.erase v) l) := by
      rw [← ht]
    _ = _ := by ring

private theorem denominator_nonzero [Field K] (w : α → K)
    (V : Finset α) (l : List α)
    (hV : ∀ U : Finset α, U ⊆ V → partition G U w ≠ 0) :
    denominatorProduct G w V l ≠ 0 := by
  induction l generalizing V with
  | nil => simp [denominatorProduct]
  | cons v l ih =>
      apply mul_ne_zero (hV V (by intro x hx; exact hx))
      apply ih
      intro U hU
      apply hV U
      intro x hx
      exact Finset.mem_of_mem_erase (hU hx)

private theorem vacancyProduct_eq_quotient [Field K] (w : α → K)
    (V : Finset α) (l : List α) :
    vacancyProduct G w V l =
      numeratorProduct G w V l / denominatorProduct G w V l := by
  induction l generalizing V with
  | nil => simp [vacancyProduct, numeratorProduct, denominatorProduct]
  | cons v l ih =>
      simp only [vacancyProduct, numeratorProduct, denominatorProduct]
      rw [ih]
      exact div_mul_div_comm _ _ _ _

/-- Genuine vacancy ratios on proper domains give the ordered recursion.
Only partitions of subsets of V minus the root are required nonzero: the root
partition being proved nonzero is never included among these hypotheses. -/
theorem partition_ordered_recursion [Field K] (w : α → K)
    (V : Finset α) (v : α) (hv : v ∈ V) (l : List α)
    (hl : l.toFinset = V.filter (G.Adj v))
    (hproper : ∀ U : Finset α, U ⊆ V.erase v → partition G U w ≠ 0) :
    partition G V w = partition G (V.erase v) w *
      (1 + w v * vacancyProduct G w (V.erase v) l) := by
  have hD := denominator_nonzero G w (V.erase v) l hproper
  rw [vacancyProduct_eq_quotient]
  apply mul_right_cancel₀ hD
  calc
    _ = partition G (V.erase v) w *
        (denominatorProduct G w (V.erase v) l +
          w v * numeratorProduct G w (V.erase v) l) :=
      ordered_partition_cross G w V v hv l hl
    _ = _ := by field_simp [hD]

/-- The exact induction step needed by zero-freeness: smaller-domain
nonvanishing and a nonzero local recursion denominator imply nonvanishing of
the original independent-set partition. -/
theorem partition_nonzero_of_local_denominator [Field K] (w : α → K)
    (V : Finset α) (v : α) (hv : v ∈ V) (l : List α)
    (hl : l.toFinset = V.filter (G.Adj v))
    (hproper : ∀ U : Finset α, U ⊆ V.erase v → partition G U w ≠ 0)
    (hlocal : 1 + w v * vacancyProduct G w (V.erase v) l ≠ 0) :
    partition G V w ≠ 0 := by
  rw [partition_ordered_recursion G w V v hv l hl hproper]
  exact mul_ne_zero (hproper (V.erase v) (by intro x hx; exact hx)) hlocal

#print axioms afterErases_eq_sdiff
#print axioms telescoping_cross
#print axioms afterErases_neighbors
#print axioms ordered_partition_cross
#print axioms partition_ordered_recursion
#print axioms partition_nonzero_of_local_denominator

end D5.S3.StatisticalMechanics.HardCore.OrderedPartitionRecursion
