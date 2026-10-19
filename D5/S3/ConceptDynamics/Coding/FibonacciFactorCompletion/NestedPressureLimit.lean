/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Anchored compact cylinders stabilize actual languages and their weighted pressure zeros. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge

set_option autoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
open Filter Topology

/-- The word is fixed at coordinate zero, independently of its original occurrence. -/
def anchoredCylinder (w : List CuLetter) : Set (ℤ → CuLetter) :=
  {ω | ∀ k : Fin w.length, ω (k : ℕ) = w[k]}

private theorem cylinder_closed (w : List CuLetter) : IsClosed (anchoredCylinder w) := by
  have h := isClosed_iInter (fun k : Fin w.length =>
    (isClosed_singleton : IsClosed ({w[k]} : Set CuLetter)).preimage
      (continuous_apply ((k : ℕ) : ℤ) :
        Continuous (fun ω : ℤ → CuLetter => ω ((k : ℕ) : ℤ))))
  convert h using 1
  ext ω
  simp [anchoredCylinder]

/-- A word that persists in all the languages has one common realization in
 their intersection. Its occurrence positions may vary arbitrarily. -/
theorem persistent_word_intersection (Y : ℕ → Set (ℤ → CuLetter))
    (compact : ∀ j, IsCompact (Y j)) (decreasing : Antitone Y)
    (shift : ∀ j (ω : ℤ → CuLetter), ω ∈ Y j → ∀ a : ℤ,
      (fun i => ω (i + a)) ∈ Y j)
    (w : List CuLetter) (persistent : ∀ j, ∃ ω ∈ Y j, Occurs ω w) :
    ∃ ω ∈ ⋂ j, Y j, ω ∈ anchoredCylinder w := by
  let t : ℕ → Set (ℤ → CuLetter) := fun j => Y j ∩ anchoredCylinder w
  have occupied (j : ℕ) : (t j).Nonempty := by
    obtain ⟨ω, hω, a, occurs⟩ := persistent j
    refine ⟨fun i => ω (i + a), shift j ω hω a, ?_⟩
    intro k
    simpa [add_comm] using occurs k
  obtain ⟨ω, hω⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t
    (fun j => Set.inter_subset_inter_left _ (decreasing (Nat.le_succ j))) occupied
    ((compact 0).inter_right (cylinder_closed w))
    (fun j => (compact j).isClosed.inter (cylinder_closed w))
  refine ⟨ω, Set.mem_iInter.mpr (fun j => (Set.mem_iInter.mp hω j).1),
    (Set.mem_iInter.mp hω 0).2⟩

/-- Each fixed finite language eventually equals the actual intersection
 language. The single index covers all binary words of that length, also zero. -/
theorem nested_language_stabilization (Y : ℕ → Set (ℤ → CuLetter))
    (compact : ∀ j, IsCompact (Y j)) (decreasing : Antitone Y)
    (shift : ∀ j (ω : ℤ → CuLetter), ω ∈ Y j → ∀ a : ℤ,
      (fun i => ω (i + a)) ∈ Y j) (k : ℕ) :
    ∃ J : ℕ, ∀ j ≥ J, ∀ w : List CuLetter, w.length = k →
      ((∃ ω ∈ Y j, Occurs ω w) ↔ (∃ ω ∈ ⋂ m, Y m, Occurs ω w)) := by
  classical
  have each (w : List CuLetter) : ∃ J : ℕ, ∀ j ≥ J,
      ((∃ ω ∈ Y j, Occurs ω w) ↔ (∃ ω ∈ ⋂ m, Y m, Occurs ω w)) := by
    by_cases h : ∀ j, ∃ ω ∈ Y j, Occurs ω w
    · obtain ⟨ω, hω, hw⟩ := persistent_word_intersection Y compact decreasing shift w h
      refine ⟨0, fun j _ => ⟨fun _ => ⟨ω, hω, 0, ?_⟩,
        fun ⟨ν, hν, hv⟩ => ⟨ν, Set.mem_iInter.mp hν j, hv⟩⟩⟩
      simpa [anchoredCylinder] using hw
    · obtain ⟨J, hJ⟩ := not_forall.mp h
      refine ⟨J, fun j hj => ⟨fun ⟨ω, hω, hw⟩ => False.elim (hJ
        ⟨ω, decreasing hj hω, hw⟩), fun ⟨ω, hω, hw⟩ =>
        ⟨ω, Set.mem_iInter.mp hω j, hw⟩⟩⟩
  let words : Finset (Fin k → CuLetter) := Finset.univ
  choose index eventual using fun v : Fin k → CuLetter => each (List.ofFn v)
  refine ⟨words.sup index, ?_⟩
  intro j hj w hw
  let v : Fin k → CuLetter := fun i => w[i.val]'(by simpa [hw] using i.isLt)
  have recover : List.ofFn v = w := by
    apply List.ext_getElem
    · simpa using hw.symm
    · intro i hi hj
      simp [v]
  have bound : index v ≤ words.sup index := Finset.le_sup (Finset.mem_univ v)
  simpa only [recover] using eventual v j (bound.trans hj)

private theorem partition_mono {X Y : Set (ℤ → CuLetter)} (incl : X ⊆ Y)
    (k : ℕ) (θ : ℝ) : partitionSum X k θ ≤ partitionSum Y k θ := by
  classical
  let f : LengthDictionary X k → LengthDictionary Y k := fun w =>
    ⟨w.val, by rcases w.property.1 with ⟨ω, hω, hw⟩; exact ⟨ω, incl hω, hw⟩,
      w.property.2⟩
  have inj : Function.Injective f := fun _ _ h => Subtype.ext (congrArg (fun w : LengthDictionary Y k => w.val) h)
  unfold partitionSum
  rw [← Finset.sum_image (f := fun w : LengthDictionary Y k => wordTerm θ w.val)
    (fun _ _ _ _ h => inj h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun w _ _ => (pow_pos (Real.rpow_pos_of_pos (by norm_num) _) _).le)

private theorem partition_language_eq (X Y : Set (ℤ → CuLetter)) (k : ℕ) (θ : ℝ)
    (same : ∀ w : List CuLetter, w.length = k →
      ((∃ ω ∈ X, Occurs ω w) ↔ (∃ ω ∈ Y, Occurs ω w))) :
    partitionSum X k θ = partitionSum Y k θ := by
  classical
  let e : LengthDictionary X k ≃ LengthDictionary Y k :=
    { toFun := fun w => ⟨w.val, (same w.val w.property.2).mp w.property.1, w.property.2⟩
      invFun := fun w => ⟨w.val, (same w.val w.property.2).mpr w.property.1, w.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- Inclusion compares pressure at every real exponent, without an entropy
 assumption or a sign restriction on the exponent. -/
theorem pressure_mono {X Y : Set (ℤ → CuLetter)} (occupiedX : X.Nonempty)
    (occupiedY : Y.Nonempty) (incl : X ⊆ Y) (θ : ℝ) : pressure X θ ≤ pressure Y θ := by
  apply le_of_tendsto_of_tendsto (pressure_tendsto X occupiedX θ)
    (pressure_tendsto Y occupiedY θ)
  filter_upwards [] with k
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
  exact Real.logb_le_logb_of_le (by norm_num) (partition_positive X occupiedX k θ)
    (partition_mono incl k θ)


private theorem pressure_eq_ciInf (X : Set (ℤ → CuLetter)) (θ : ℝ) :
    pressure X θ = ⨅ k : {k : ℕ // 1 ≤ k}, logPartition X θ k.val / (k.val : ℝ) := by
  unfold pressure iInf
  congr 1
  ext z
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, k.property, rfl⟩

/-- The decreasing pressures have exactly the intersection pressure as their
 infimum and limit for every real exponent. The common lower bound is explicit. -/
theorem nested_pressure_limit (Y : ℕ → Set (ℤ → CuLetter))
    (compact : ∀ j, IsCompact (Y j)) (occupied : ∀ j, (Y j).Nonempty)
    (decreasing : Antitone Y)
    (shift : ∀ j (ω : ℤ → CuLetter), ω ∈ Y j → ∀ a : ℤ,
      (fun i => ω (i + a)) ∈ Y j) (θ : ℝ) :
    (⋂ j, Y j).Nonempty ∧
    Antitone (fun j => pressure (Y j) θ) ∧
    (⨅ j, pressure (Y j) θ) = pressure (⋂ j, Y j) θ ∧
    Tendsto (fun j => pressure (Y j) θ) atTop (𝓝 (pressure (⋂ j, Y j) θ)) := by
  letI : Nonempty {k : ℕ // 1 ≤ k} := ⟨⟨1, le_rfl⟩⟩
  have occ : (⋂ j, Y j).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Y
      (fun j => decreasing (Nat.le_succ j)) occupied (compact 0)
      (fun j => (compact j).isClosed)
  have pm : Antitone (fun j => pressure (Y j) θ) :=
    fun i j hij => pressure_mono (occupied j) (occupied i) (decreasing hij) θ
  let q (j : ℕ) (k : {k : ℕ // 1 ≤ k}) : ℝ :=
    logPartition (Y j) θ k.val / (k.val : ℝ)
  let r (k : {k : ℕ // 1 ≤ k}) : ℝ :=
    logPartition (⋂ j, Y j) θ k.val / (k.val : ℝ)
  have qb (j : ℕ) (k : {k : ℕ // 1 ≤ k}) : -20 * |θ| ≤ q j k :=
    log_quotient_lower_bound (Y j) (occupied j) θ k.val
  have rowBound (k : {k : ℕ // 1 ≤ k}) : BddBelow (Set.range (fun j => q j k)) :=
    ⟨-20 * |θ|, by rintro _ ⟨j, rfl⟩; exact qb j k⟩
  have fixed (k : {k : ℕ // 1 ≤ k}) : (⨅ j, q j k) = r k := by
    obtain ⟨J, hJ⟩ := nested_language_stabilization Y compact decreasing shift k.val
    apply le_antisymm
    · apply ciInf_le_of_le (rowBound k) J
      have same := partition_language_eq (Y J) (⋂ j, Y j) k.val θ (hJ J le_rfl)
      exact le_of_eq (by dsimp [q, r, logPartition]; rw [same])
    · apply le_ciInf
      intro j
      dsimp [r, q]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Real.logb_le_logb_of_le (by norm_num)
        (partition_positive _ occ _ θ)
        (partition_mono (Set.iInter_subset Y j) _ θ)
  have joint : BddBelow (Set.range (fun p : ℕ × {k : ℕ // 1 ≤ k} => q p.1 p.2)) :=
    ⟨-20 * |θ|, by rintro _ ⟨⟨j,k⟩,rfl⟩; exact qb j k⟩
  have swapped : BddBelow (Set.range (fun p : {k : ℕ // 1 ≤ k} × ℕ => q p.2 p.1)) :=
    ⟨-20 * |θ|, by rintro _ ⟨⟨k,j⟩,rfl⟩; exact qb j k⟩
  have commute : (⨅ j, ⨅ k, q j k) = ⨅ k, ⨅ j, q j k := by
    rw [← ciInf_prod joint, ← ciInf_prod swapped]
    unfold iInf
    congr 1
    ext z
    constructor
    · rintro ⟨⟨j,k⟩,rfl⟩; exact ⟨(k,j),rfl⟩
    · rintro ⟨⟨k,j⟩,rfl⟩; exact ⟨(j,k),rfl⟩
  have infimum : (⨅ j, pressure (Y j) θ) = pressure (⋂ j, Y j) θ := by
    simp_rw [pressure_eq_ciInf]
    exact commute.trans (congrArg (fun f : {k : ℕ // 1 ≤ k} → ℝ => ⨅ k, f k)
      (funext fixed))
  have bound : BddBelow (Set.range (fun j => pressure (Y j) θ)) := by
    refine ⟨-20 * |θ|, ?_⟩
    rintro _ ⟨j,rfl⟩
    change -20 * |θ| ≤ pressure (Y j) θ
    rw [pressure_eq_ciInf]
    exact le_ciInf (qb j)
  refine ⟨occ, pm, infimum, ?_⟩
  rw [← infimum]
  exact tendsto_atTop_ciInf pm bound

/-- The weighted factor rates converge even when the intersection has zero
 entropy. The negative test pressure uses the literal slope six. -/
theorem nested_rate_limit (Y : ℕ → Set (ℤ → CuLetter))
    (compact : ∀ j, IsCompact (Y j)) (occupied : ∀ j, (Y j).Nonempty)
    (decreasing : Antitone Y)
    (shift : ∀ j (ω : ℤ → CuLetter), ω ∈ Y j → ∀ a : ℤ,
      (fun i => ω (i + a)) ∈ Y j) :
    Antitone (fun j => weightedFactorRate (Y j)) ∧
    Tendsto (fun j => weightedFactorRate (Y j)) atTop
      (𝓝 (weightedFactorRate (⋂ j, Y j))) := by
  have occ := (nested_pressure_limit Y compact occupied decreasing shift 0).1
  have zero (X : Set (ℤ → CuLetter)) (hX : X.Nonempty) :
      pressure X (weightedFactorRate X) = 0 :=
    (pressure_zero_iff_rate X hX _).mpr rfl
  have compare (X Z : Set (ℤ → CuLetter)) (hX : X.Nonempty) (hZ : Z.Nonempty)
      (incl : X ⊆ Z) : weightedFactorRate X ≤ weightedFactorRate Z := by
    by_contra h
    have lt := pressure_strictAnti X hX (lt_of_not_ge h)
    have mono := pressure_mono hX hZ incl (weightedFactorRate Z)
    rw [zero X hX, zero Z hZ] at *
    linarith
  have lower (j : ℕ) : weightedFactorRate (⋂ m, Y m) ≤ weightedFactorRate (Y j) :=
    compare _ _ occ (occupied j) (Set.iInter_subset Y j)
  refine ⟨fun i j hij => compare _ _ (occupied j) (occupied i) (decreasing hij), ?_⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun j => ha.trans_le (lower j))
  · intro b hb
    let η := weightedFactorRate (⋂ j, Y j)
    have negative : pressure (⋂ j, Y j) b < 0 := by
      have slope := (pressure_shift_bounds _ occ η (b-η) (by dsimp [η]; linarith)).2
      rw [add_sub_cancel, zero _ occ] at slope
      dsimp [η] at slope
      linarith
    have limit := (nested_pressure_limit Y compact occupied decreasing shift b).2.2.2
    have eventually := (tendsto_order.mp limit).2 0 negative
    filter_upwards [eventually] with j hj
    by_contra h
    have mono := (pressure_strictAnti (Y j) (occupied j)).antitone (le_of_not_gt h)
    rw [zero _ (occupied j)] at mono
    linarith


private theorem finite_past_shift (ω : ℤ → CuLetter) (i a : ℤ) (n : ℕ) (z : ℝ) :
    finitePast (fun q => ω (q+a)) i n z = finitePast ω (i+a) n z := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [finitePast, ih]
    have index : i-1+a = i+a-1 := by ring
    rw [index]

/-- The literal upper window constraints define a nonempty compact closed
 bilateral subshift. Equality in the high guard is included. -/
theorem upper_memory_subshift (n K : ℕ) (d : ℝ) (positive : 1 ≤ K) :
    (MemoryLanguage .upper n K d).Nonempty ∧
    IsClosed (MemoryLanguage .upper n K d) ∧
    IsCompact (MemoryLanguage .upper n K d) ∧
    (∀ (ω : ℤ → CuLetter), ω ∈ MemoryLanguage .upper n K d → ∀ a : ℤ,
      (fun i => ω (i+a)) ∈ MemoryLanguage .upper n K d) := by
  have pastContinuous (i : ℤ) :
      Continuous (fun ω : ℤ → CuLetter => finitePast ω i n (hSide .high)) := by
    have window : Continuous (fun ω : ℤ → CuLetter => memoryWindow n ω i) :=
      continuous_pi (fun k => continuous_apply (i-1-(k : ℕ)))
    have value : Continuous (fun v : MemoryVertex n => memoryValue v (hSide .high)) :=
      continuous_of_discreteTopology
    simpa only [Function.comp_def, window_value] using value.comp window
  have runOpen (position : ℕ → ℤ) (m : ℕ) :
      IsOpen {ω : ℤ → CuLetter | ∀ k : Fin m, ω (position k) = .c} := by
    have h := isOpen_iInter_of_finite (fun k : Fin m =>
      (isOpen_discrete ({CuLetter.c} : Set CuLetter)).preimage
        (continuous_apply (position k) : Continuous (fun ω : ℤ → CuLetter => ω (position k))))
    convert h using 1
    ext ω
    simp
  have closed : IsClosed (MemoryLanguage .upper n K d) := by
    have noRun (i : ℤ) : IsClosed {ω : ℤ → CuLetter |
        ¬ ∀ k : Fin (K+1), ω (i+(k : ℕ)) = .c} :=
      (runOpen (fun k => i+(k : ℤ)) (K+1)).isClosed_compl
    have guard (i : ℤ) : IsClosed {ω : ℤ → CuLetter |
        (∀ k : Fin K, ω (i-(k : ℕ)) = .c) →
          chi^(K-1)*d ≤ finitePast ω i n (hSide .high)} := by
      have h := (runOpen (fun k => i-(k : ℤ)) K).isClosed_compl.union
        (isClosed_le (continuous_const :
          Continuous (fun _ : ℤ → CuLetter => chi^(K-1)*d)) (pastContinuous i))
      convert h using 1
      ext ω
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq]
      tauto
    convert (isClosed_iInter noRun).inter (isClosed_iInter guard) using 1
    ext ω
    simp [MemoryLanguage, UpperMemoryLanguage]
  have occupied : (MemoryLanguage .upper n K d).Nonempty := by
    refine ⟨fun _ => .u, ?_, ?_⟩
    · intro i run
      have h := run ⟨0, by omega⟩
      cases h
    · intro i run
      have h := run ⟨0, by omega⟩
      cases h
  refine ⟨occupied, closed, closed.isCompact, ?_⟩
  intro ω hω a
  change (∀ i : ℤ, ¬ ∀ k : Fin (K+1), ω (i+(k : ℕ)+a)=.c) ∧ _
  constructor
  · intro i run
    apply hω.1 (i+a)
    intro k
    convert run k using 1 <;> congr 1 <;> ring
  · intro i run
    have actual : ∀ k : Fin K, ω (i+a-(k : ℕ))=.c := by
      intro k
      convert run k using 1 <;> congr 1 <;> ring
    simpa only [finite_past_shift] using hω.2 (i+a) actual

/-- Every original upper-memory rate decreases to the rate of the same
 auxiliary language. The sequence includes every n at least K. -/
theorem original_upper_rate_limit (K : ℕ) (d : ℝ) (positive : 1 ≤ K) :
    Antitone (fun n => weightedFactorRate (MemoryLanguage .upper n K d)) ∧
    Tendsto (fun n => weightedFactorRate (MemoryLanguage .upper n K d)) atTop
      (𝓝 (weightedFactorRate (AuxiliaryLanguage K d))) := by
  let Y : ℕ → Set (ℤ → CuLetter) := fun j => MemoryLanguage .upper (K+j) K d
  have compact (j : ℕ) : IsCompact (Y j) := (upper_memory_subshift (K+j) K d positive).2.2.1
  have occupied (j : ℕ) : (Y j).Nonempty := (upper_memory_subshift (K+j) K d positive).1
  have dec : Antitone Y := by
    apply antitone_nat_of_succ_le
    intro j
    simpa only [Y, Nat.add_assoc] using (original_memory_language_nesting (K+j) K d).2.2.2
  have shift : ∀ j (ω : ℤ → CuLetter), ω ∈ Y j → ∀ a : ℤ,
      (fun i => ω (i+a)) ∈ Y j :=
    fun j => (upper_memory_subshift (K+j) K d positive).2.2.2
  have intersection : (⋂ j, Y j) = AuxiliaryLanguage K d := by
    rw [← original_upper_memory_intersection K d]
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Y]
    constructor
    · intro h n hn
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
      exact h j
    · intro h j
      exact h (K+j) (Nat.le_add_right K j)
  have limit := (nested_rate_limit Y compact occupied dec shift).2
  rw [intersection] at limit
  have unshifted : Tendsto (fun n => weightedFactorRate (MemoryLanguage .upper n K d))
      atTop (𝓝 (weightedFactorRate (AuxiliaryLanguage K d))) := by
    apply (tendsto_add_atTop_iff_nat K).mp
    simpa [Y, Nat.add_comm] using limit
  exact ⟨antitone_nat_of_succ_le (fun n => (original_memory_rate_nesting n K d).2.2.2),
    unshifted⟩

/-- The original spectral roots give the upper rate limit at the actual source
 budget, with the same eta_b for both starts and both guard contracts. -/
theorem original_upper_root_limit (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g^2 * chi^K * hSide .high < b)
    (hbp : b < lam - g^2 * chi^K * (aSide .high / (1-rho*chi^K))) :
    ∃ roots : MemorySide → ℕ → ℝ,
      (∀ side n, K ≤ n → 0 < roots side n ∧ roots side n < 1 ∧
        weightedRadius side n K ((lam-b)/g^2/chi^K) (roots side n) = 1 ∧
        weightedFactorRate (MemoryLanguage side n K ((lam-b)/g^2/chi^K)) =
          -Real.logb 2 (roots side n)) ∧
      (∀ n, K ≤ n → -Real.logb 2 (roots .lower n) ≤ eta_b K b ∧
        eta_b K b ≤ -Real.logb 2 (roots .upper n)) ∧
      MonotoneOn (fun n => -Real.logb 2 (roots .lower n)) (Set.Ici K) ∧
      AntitoneOn (fun n => -Real.logb 2 (roots .upper n)) (Set.Ici K) ∧
      Tendsto (fun n => -Real.logb 2 (roots .upper n)) atTop (𝓝 (eta_b K b)) ∧
      (∀ model strict, actualRate model K ((lam-b)/g^2/chi^K) strict = eta_b K b) := by
  let d := (lam-b)/g^2/chi^K
  obtain ⟨roots, properties, sandwich, lower, upper⟩ := original_root_rate_families K d hK
  have bridge : eta_b K b = weightedFactorRate (AuxiliaryLanguage K d) :=
    actual_auxiliary_rate_bridge o b K hK hqb hbp .original false
  have rateLimit := (original_upper_rate_limit K d (by omega)).2
  rw [← bridge] at rateLimit
  refine ⟨roots, properties, ?_, lower, upper, ?_, ?_⟩
  · intro n hn
    rw [bridge]
    exact sandwich n hn
  · apply rateLimit.congr'
    filter_upwards [eventually_ge_atTop K] with n hn
    exact (properties .upper n hn).2.2.2
  · intro model strict
    exact (actual_auxiliary_rate_bridge o b K hK hqb hbp model strict).trans bridge.symm

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
