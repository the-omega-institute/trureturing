/- GID: D5/S3/HardCoreHolomorphic/FiniteGridZeroFree
   generality: G
   mirror-B: D5/B/S3/HardCoreHolomorphic/FiniteGridZeroFree
   mirror-E: none(waiver:simultaneous-actual-finite-grid-induction)
   anchors: []
   digest: Every finite induced square grid has a quantitative nonzero partition on the common activity tube. -/

import D5.S3.HardCoreHolomorphic.ActualGraphLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.HardCoreHolomorphic.FiniteGridZeroFree

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.StatisticalMechanics.HardCore.PartitionRelabeling
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
open D5.S3.StatisticalMechanics.HardCore.SquareGridMessages
open D5.S3.StatisticalMechanics.HardCore.SquareGridRootMessages
open D5.S3.StatisticalMechanics.HardCore.AdaptiveRadiusFourCertificates
open D5.S3.HardCoreHolomorphic.TubeEstimates
open D5.S3.HardCoreHolomorphic.AdaptiveComplexNeighborhood
open D5.S3.HardCoreHolomorphic.ActualGraphLift

private theorem erase_card_lt (V : Finset Point) (v : Point) (hv : v ∈ V) :
    (V.erase v).card < V.card := by
  have he := Finset.card_erase_of_mem hv
  have hp : 0 < V.card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

private theorem shifted_origin (V : Finset Point) (v : Point) (hv : v ∈ V) :
    (0, 0) ∈ V.image (shiftTo v) := by
  refine Finset.mem_image.mpr ⟨v, hv, ?_⟩
  ext <;> simp [shiftTo]

private theorem partition_shift (V : Finset Point) (v : Point) (z : ℂ) :
    gridPartition (V.image (shiftTo v)) z = gridPartition V z :=
  partition_relabel squareGrid squareGrid (shiftTo v) (shift_adj_iff v) V (fun _ => z)

/-- Simultaneous strong induction on actual vertex cardinality. The first
component bounds every untyped graph partition away from zero. The second
represents every compatible nonroot graph vacancy in its genuine type tube.
All recursive calls have strictly fewer vertices; no same-size conclusion is
used to prove itself. Holomorphic and geometric facts are actual dependencies. -/
theorem finite_grid_partition_control (z : ℂ) (hz : z ∈ ActivityTube)
    (V : Finset Point) :
    (1 / 2 : ℝ) ^ V.card ≤ ‖gridPartition V z‖ ∧
      (∀ i : Fin 881, (0, 0) ∈ V → Disjoint V (radiusFourMask i) →
        ∃ m : ℂ, m ∈ Omega i ∧ decode i m = gridVacancy V (0, 0) z) := by
  suffices hall : ∀ n : ℕ, ∀ W : Finset Point, W.card = n →
      (1 / 2 : ℝ) ^ W.card ≤ ‖gridPartition W z‖ ∧
        (∀ i : Fin 881, (0, 0) ∈ W → Disjoint W (radiusFourMask i) →
          ∃ m : ℂ, m ∈ Omega i ∧ decode i m = gridVacancy W (0, 0) z) by
    exact hall V.card V rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro W hW
      have nonzeroSmaller (U : Finset Point) (hU : U.card < n) : gridPartition U z ≠ 0 := by
        apply norm_pos_iff.mp
        exact lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) U.card)
          (ih U.card hU U rfl).1
      by_cases hempty : W = ∅
      · subst W
        constructor
        · simp [gridPartition, partition_empty]
        · intro i h0
          exact False.elim (Finset.notMem_empty (0, 0) h0)
      · constructor
        · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
          let U := W.image (shiftTo v)
          have hcard : U.card = W.card :=
            Finset.card_image_of_injective W (shiftTo v).injective
          have hUn : U.card = n := hcard.trans hW
          have h0 : (0, 0) ∈ U := shifted_origin W v hv
          have hdel : (U.erase (0, 0)).card < n := by
            rw [← hUn]
            exact erase_card_lt U (0, 0) h0
          have hproper : ∀ T : Finset Point, T ⊆ U.erase (0, 0) → gridPartition T z ≠ 0 := by
            intro T hT
            exact nonzeroSmaller T ((Finset.card_le_card hT).trans_lt hdel)
          have hchildren : ∀ e : Fin 4, rootDirection e ∈ U → ∃ m : ℂ,
              m ∈ Omega 0 ∧ decode 0 m = gridVacancy (rootDomain U e) (0, 0) z := by
            intro e he
            obtain ⟨hroot, hcompat, hlt⟩ := root_child_context U h0 e he
            have hn : (rootDomain U e).card < n := by omega
            exact (ih _ hn (rootDomain U e) rfl).2 0 hroot hcompat
          obtain ⟨D, hD, hrec⟩ := root_graph_step U h0 z hz hproper hchildren
          have hDn : (1 / 2 : ℝ) ≤ ‖D‖ := hD.trans (Complex.re_le_norm D)
          have hsmall := (ih _ hdel (U.erase (0, 0)) rfl).1
          have hsize : (U.erase (0, 0)).card + 1 = U.card := by
            have he := Finset.card_erase_of_mem h0
            have hp : 0 < U.card := Finset.card_pos.mpr ⟨(0, 0), h0⟩
            omega
          have hbound : (1 / 2 : ℝ) ^ U.card ≤ ‖gridPartition U z‖ := by
            calc
              _ = (1 / 2 : ℝ) ^ (U.erase (0, 0)).card * (1 / 2) := by
                rw [← hsize, pow_succ]
              _ ≤ ‖gridPartition (U.erase (0, 0)) z‖ * ‖D‖ :=
                mul_le_mul hsmall hDn (by norm_num) (norm_nonneg _)
              _ = _ := by rw [hrec, norm_mul]
          have hpartition : gridPartition U z = gridPartition W z := partition_shift W v z
          simpa only [hcard, hpartition] using hbound
        · intro i h0 hdis
          have hdel : (W.erase (0, 0)).card < n := by
            rw [← hW]
            exact erase_card_lt W (0, 0) h0
          have hproper : ∀ T : Finset Point, T ⊆ W.erase (0, 0) → gridPartition T z ≠ 0 := by
            intro T hT
            exact nonzeroSmaller T ((Finset.card_le_card hT).trans_lt hdel)
          have hchildren : ∀ d ∈ availableDirections W, ∃ m : ℂ,
              m ∈ Omega (childType i d) ∧
              decode (childType i d) m = childVacancy W (radiusFourChoice i) d z := by
            intro d hd
            have hv : direction d ∈ W := (Finset.mem_filter.mp hd).2
            obtain ⟨j, hj, hroot, hcompat, hlt⟩ := typed_child_context W i h0 hdis d hv
            have hn : (advance W (radiusFourChoice i) d).card < n := by omega
            have htype : childType i d = j := by simp [childType, hj]
            obtain ⟨m, hm, he⟩ := (ih _ hn (advance W (radiusFourChoice i) d) rfl).2 j hroot hcompat
            refine ⟨m, ?_, ?_⟩
            · simpa only [htype] using hm
            · simpa only [htype, childVacancy] using he
          exact (typed_graph_step W i h0 hdis z hz hproper hchildren).2

/-- A quantitative common lower modulus for every actual finite induced grid.
The exponential volume factor is explicit and includes the empty graph. -/
theorem finite_grid_partition_lower (V : Finset Point) (z : ℂ) (hz : z ∈ ActivityTube) :
    (1 / 2 : ℝ) ^ V.card ≤ ‖gridPartition V z‖ :=
  (finite_grid_partition_control z hz V).1

/-- Unconditional finite-grid nonvanishing on the constructed common activity
neighborhood. There is no supplied nonvanishing, contraction, typing or graph-size hypothesis. -/
theorem finite_grid_zero_free (V : Finset Point) (z : ℂ) (hz : z ∈ ActivityTube) :
    gridPartition V z ≠ 0 := by
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) V.card)
    (finite_grid_partition_lower V z hz)

/-- The explicit interval and width are in the theorem statement, for all
finite vertex domains at once. This is the actual independent-set sum. -/
theorem finite_grid_zero_free_explicit (V : Finset Point) (z : ℂ)
    (hz : ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 51 / 20 ∧
      ‖z - (lam : ℂ)‖ < 1 / (10 : ℝ) ^ 30) :
    gridPartition V z ≠ 0 := by
  apply finite_grid_zero_free V z
  obtain ⟨lam, hl0, hl1, hd⟩ := hz
  exact ⟨lam, ⟨hl0, hl1⟩, by simpa only [epsilon] using hd⟩

/-- The same result for the existing integer-coefficient independence
polynomial, via its proved actual-configuration evaluation identity. -/
theorem finite_grid_independencePolynomial_zero_free (V : Finset Point) (z : ℂ)
    (hz : ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 51 / 20 ∧
      ‖z - (lam : ℂ)‖ < 1 / (10 : ℝ) ^ 30) :
    Polynomial.eval₂ (Int.castRingHom ℂ) z (independencePolynomial squareGrid V) ≠ 0 := by
  rw [independencePolynomial_eval]
  exact finite_grid_zero_free_explicit V z hz

/-- The local partition increment for every present origin remains in a
common right half-plane. The derived bound supports stable ordered logarithms. -/
theorem finite_grid_origin_increment (V : Finset Point) (h0 : (0, 0) ∈ V)
    (z : ℂ) (hz : z ∈ ActivityTube) :
    (1 / 2 : ℝ) ≤ (gridPartition V z / gridPartition (V.erase (0, 0)) z).re := by
  have hproper := fun (U : Finset Point) (_ : U ⊆ V.erase (0, 0)) => finite_grid_zero_free U z hz
  have hchildren : ∀ e : Fin 4, rootDirection e ∈ V → ∃ m : ℂ,
      m ∈ Omega 0 ∧ decode 0 m = gridVacancy (rootDomain V e) (0, 0) z := by
    intro e he
    obtain ⟨hroot, hcompat, _⟩ := root_child_context V h0 e he
    exact (finite_grid_partition_control z hz (rootDomain V e)).2 0 hroot hcompat
  obtain ⟨D, hD, hrec⟩ := root_graph_step V h0 z hz hproper hchildren
  have hn := finite_grid_zero_free (V.erase (0, 0)) z hz
  have heq : gridPartition V z / gridPartition (V.erase (0, 0)) z = D := by
    rw [hrec]
    field_simp [hn]
  rwa [heq]

/-- Every actual marked vacancy, even at a boundary vertex or an absent
vertex, has modulus at most two on the same complex neighborhood. -/
theorem finite_grid_vacancy_bound (V : Finset Point) (v : Point)
    (z : ℂ) (hz : z ∈ ActivityTube) : ‖gridVacancy V v z‖ ≤ 2 := by
  by_cases hv : v ∈ V
  · let W := V.image (shiftTo v)
    have h0 : (0, 0) ∈ W := shifted_origin V v hv
    have h := finite_grid_origin_increment W h0 z hz
    let D := gridPartition W z / gridPartition (W.erase (0, 0)) z
    have hd : (1 / 2 : ℝ) ≤ ‖D‖ := h.trans (Complex.re_le_norm D)
    have hp : 0 < ‖D‖ := lt_of_lt_of_le (by norm_num) hd
    rw [← vacancy_shift V v z]
    have heq : gridVacancy W (0, 0) z = D⁻¹ := by simp only [gridVacancy, D, inv_div]
    change ‖gridVacancy W (0, 0) z‖ ≤ 2
    rw [heq, norm_inv, inv_eq_one_div]
    apply (div_le_iff₀ hp).mpr
    linarith
  · simp only [gridVacancy, Finset.erase_eq_of_notMem hv,
      div_self (finite_grid_zero_free V z hz), norm_one]
    norm_num

#print axioms finite_grid_partition_control
#print axioms finite_grid_partition_lower
#print axioms finite_grid_zero_free
#print axioms finite_grid_zero_free_explicit
#print axioms finite_grid_independencePolynomial_zero_free
#print axioms finite_grid_origin_increment
#print axioms finite_grid_vacancy_bound

end D5.S3.HardCoreHolomorphic.FiniteGridZeroFree
