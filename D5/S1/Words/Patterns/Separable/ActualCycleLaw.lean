/- GID: D5/S1/Words/Patterns/Separable/ActualCycleLaw
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/ActualCycleLaw
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Probability.ProductMeasure]
   utility: none
   digest: Actual marked cycles have normalized count weights and common stream prefixes. -/

import D5.S1.Words.Patterns.Separable.ActualCycles
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

namespace D5.S1.Words.Patterns.Separable.ActualCycleLaw

open D5.S1.Words.Patterns.Separable.ActualCycles
open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S1.Words.Patterns.Separable.MinimumCutKernel
open D5.S1.Words.Patterns.Separable.OccupiedComparison
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

/-- Nonempty actual shapes removed from the right. -/
abbrev Removal := Σ n : ℕ, Avoider (n + 1)

/-- Exactly r right removals, followed by an actual terminal shape. -/
def Fixed : Bool → ℕ → Type
  | sign, 0 => Σ n : ℕ, Indecomposable sign (n + 1)
  | sign, r + 1 => Removal × Fixed (!sign) r

namespace Fixed

def size {sign} : {r : ℕ} → Fixed sign r → ℕ
  | 0, terminal => terminal.1 + 1
  | _ + 1, pair => pair.1.1 + 1 + size pair.2

def decode {sign} : {r : ℕ} → Fixed sign r → UnboundedCycle sign
  | 0, terminal => .terminal terminal.1 terminal.2
  | _ + 1, pair => .discard pair.1.1 pair.1.2 (decode pair.2)

private theorem decode_size {sign r} (c : Fixed sign r) :
    c.decode.size = c.size := by
  induction r generalizing sign with
  | zero => rfl
  | succ r ih => simp only [decode, UnboundedCycle.size, size, ih]

instance (sign : Bool) (r : ℕ) : Countable (Fixed sign r) := by
  induction r generalizing sign with
  | zero => exact inferInstanceAs (Countable (Σ n : ℕ, Indecomposable sign (n + 1)))
  | succ r ih =>
    let := ih (!sign)
    exact inferInstanceAs (Countable (Removal × Fixed (!sign) r))

end Fixed

private def encode {sign} : UnboundedCycle sign → Σ r : ℕ, Fixed sign r
  | .terminal n shape => ⟨0, ⟨n, shape⟩⟩
  | .discard n shape tail =>
      let next := encode tail
      ⟨next.1 + 1, (⟨n, shape⟩, next.2)⟩

private theorem decode_encode {sign} (c : UnboundedCycle sign) :
    (encode c).2.decode = c := by
  induction c with
  | terminal n shape => rfl
  | discard n shape tail ih =>
    change UnboundedCycle.discard n shape (encode tail).2.decode = _
    rw [ih]

private theorem encode_decode {sign r} (c : Fixed sign r) :
    encode c.decode = ⟨r, c⟩ := by
  induction r generalizing sign with
  | zero => rfl
  | succ r ih =>
    rcases c with ⟨⟨n, shape⟩, tail⟩
    change (let next := encode tail.decode;
      (⟨next.1 + 1, (⟨n, shape⟩, next.2)⟩ : Σ r : ℕ, Fixed sign r)) = _
    rw [ih]

/-- A size-preserving enumeration retains every actual shape and the alternating signs. -/
def enumeration (sign : Bool) : UnboundedCycle sign ≃ Σ r : ℕ, Fixed sign r where
  toFun := encode
  invFun := fun c => c.2.decode
  left_inv := decode_encode
  right_inv := fun c => encode_decode c.2

instance (sign : Bool) : Countable (UnboundedCycle sign) :=
  Countable.of_equiv _ (enumeration sign).symm

/-- The mark includes the initial cut sign and the complete actual cycle. -/
abbrev MarkedCycle := Σ sign : Bool, UnboundedCycle sign

private theorem parameter_bounds : 0 < b ∧ b < 1 ∧ 0 ≤ rho ∧ 0 ≤ ceiling ∧
    ceiling * (1 - b)⁻¹ = (1 / 2 : ℝ) := by
  have sq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have nonneg := Real.sqrt_nonneg (2 : ℝ)
  have low : 1 < Real.sqrt (2 : ℝ) := by nlinarith
  have high : Real.sqrt (2 : ℝ) < 2 := by nlinarith
  have bounds : 0 < b ∧ b < 1 := by dsimp [b]; constructor <;> linarith
  refine ⟨bounds.1, bounds.2, sq_nonneg _, ?_, ?_⟩
  · dsimp [ceiling, a]; linarith [bounds.2]
  · dsimp [ceiling, a]
    field_simp [ne_of_gt (sub_pos.mpr bounds.2)]

private theorem removal_mass :
    (∑' c : Removal, ENNReal.ofReal (rho ^ (c.1 + 1))) = ENNReal.ofReal b := by
  classical
  rw [ENNReal.tsum_sigma']
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  have cast (n : ℕ) : (Nat.card (Avoider (n + 1)) : ℝ≥0∞) *
      ENNReal.ofReal (rho ^ (n + 1)) = ENNReal.ofReal (shapeWeight n) := by
    rw [shapeWeight, ENNReal.ofReal_mul (pow_nonneg parameter_bounds.2.2.1 _)]
    simp only [ENNReal.ofReal_natCast, mul_comm]
  simp_rw [cast]
  have nonneg (n : ℕ) : 0 ≤ shapeWeight n :=
    mul_nonneg (pow_nonneg parameter_bounds.2.2.1 _) (Nat.cast_nonneg _)
  rw [← ENNReal.ofReal_tsum_of_nonneg nonneg critical_shape_masses.1,
    critical_shape_masses.2.1]

private theorem terminal_mass (sign : Bool) :
    (∑' c : Σ n : ℕ, Indecomposable sign (n + 1),
      ENNReal.ofReal (rho ^ (c.1 + 1))) = ENNReal.ofReal ceiling := by
  classical
  rw [ENNReal.tsum_sigma']
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  have counts := D5.S1.Words.Patterns.Separable.ActualCardinality.actual_schroder_cardinality.2.2.1
  simp_rw [counts sign, ← counts false]
  have cast (n : ℕ) : (Nat.card (Indecomposable false (n + 1)) : ℝ≥0∞) *
      ENNReal.ofReal (rho ^ (n + 1)) = ENNReal.ofReal
        (rho ^ (n + 1) * (Nat.card (Indecomposable false (n + 1)) : ℝ)) := by
    rw [ENNReal.ofReal_mul (pow_nonneg parameter_bounds.2.2.1 _)]
    simp only [ENNReal.ofReal_natCast, mul_comm]
  simp_rw [cast]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n =>
    mul_nonneg (pow_nonneg parameter_bounds.2.2.1 _) (Nat.cast_nonneg _))
    critical_shape_masses.2.2.2.2.1, critical_shape_masses.2.2.2.2.2.1]

private theorem fixed_mass (sign : Bool) (r : ℕ) :
    (∑' c : Fixed sign r, ENNReal.ofReal (rho ^ c.size)) =
      ENNReal.ofReal (ceiling * b ^ r) := by
  induction r generalizing sign with
  | zero =>
    change (∑' c : Σ n : ℕ, Indecomposable sign (n + 1),
      ENNReal.ofReal (rho ^ (c.1 + 1))) = _
    simpa only [pow_zero, mul_one] using terminal_mass sign
  | succ r ih =>
    change (∑' c : Removal × Fixed (!sign) r,
      ENNReal.ofReal (rho ^ (c.1.1 + 1 + c.2.size))) = _
    have split (c : Removal × Fixed (!sign) r) :
        ENNReal.ofReal (rho ^ (c.1.1 + 1 + c.2.size)) =
          ENNReal.ofReal (rho ^ (c.1.1 + 1)) * ENNReal.ofReal (rho ^ c.2.size) := by
      rw [pow_add, ENNReal.ofReal_mul (pow_nonneg parameter_bounds.2.2.1 _)]
    simp_rw [split]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left, ih]
    rw [ENNReal.tsum_mul_right, removal_mass,
      ← ENNReal.ofReal_mul parameter_bounds.1.le]
    congr 1
    ring

private theorem signed_mass (sign : Bool) :
    (∑' c : UnboundedCycle sign, ENNReal.ofReal (rho ^ c.size)) =
      ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [← (enumeration sign).symm.tsum_eq]
  simp only [enumeration, Equiv.coe_fn_symm_mk, Fixed.decode_size]
  rw [ENNReal.tsum_sigma']
  simp_rw [fixed_mass]
  have summable : Summable (fun r : ℕ => ceiling * b ^ r) :=
    (summable_geometric_of_lt_one parameter_bounds.1.le parameter_bounds.2.1).mul_left ceiling
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun r =>
    mul_nonneg parameter_bounds.2.2.2.1 (pow_nonneg parameter_bounds.1.le r)) summable]
  rw [tsum_mul_left, tsum_geometric_of_lt_one parameter_bounds.1.le parameter_bounds.2.1,
    parameter_bounds.2.2.2.2]

private theorem total_mass :
    (∑' c : MarkedCycle, ENNReal.ofReal (rho ^ c.2.size)) = 1 := by
  rw [ENNReal.tsum_sigma']
  simp_rw [signed_mass]
  norm_num [tsum_fintype, ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num)]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- Its weights are the limits of actual minimum-cut tuple probabilities. -/
noncomputable def cyclePMF : PMF MarkedCycle :=
  ⟨fun c => ENNReal.ofReal (rho ^ c.2.size), by
    rw [← total_mass]
    exact ENNReal.summable.hasSum⟩

instance : MeasurableSpace MarkedCycle := ⊤
instance : MeasurableSingletonClass MarkedCycle := ⟨fun _ => trivial⟩

/-- A common realization of all complete marked-cycle prefixes. -/
abbrev Stream := ℕ → MarkedCycle

noncomputable def streamMeasure : Measure Stream :=
  Measure.infinitePi (fun _ : ℕ => cyclePMF.toMeasure)

instance : IsProbabilityMeasure streamMeasure :=
  inferInstanceAs (IsProbabilityMeasure
    (Measure.infinitePi (fun _ : ℕ => cyclePMF.toMeasure)))

namespace Prefix

/-- The actual marked cycles at the first k coordinates. -/
def nth : {k : ℕ} → UnboundedTuple k → Fin k → MarkedCycle
  | 0, _, i => Fin.elim0 i
  | _ + 1, pair, i => Fin.cases pair.1 (fun j => nth pair.2 j) i

/-- Recursive tuples and finite coordinate observations describe the same marks. -/
def coordinates : (k : ℕ) → UnboundedTuple k ≃ (Fin k → MarkedCycle)
  | 0 => (show Unit ≃ (Fin 0 → MarkedCycle) from Equiv.ofUnique _ _)
  | k + 1 => (Equiv.prodCongr (Equiv.refl MarkedCycle) (coordinates k)).trans
      (Fin.consEquiv (fun _ => MarkedCycle))

private theorem coordinates_apply {k : ℕ} (tuple : UnboundedTuple k) :
    coordinates k tuple = nth tuple := by
  induction k with
  | zero => funext i; exact Fin.elim0 i
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change coordinates k tuple.2 j = nth tuple.2 j
      rw [ih]

/-- All later cycles remain unrestricted. -/
def cylinder {k : ℕ} (tuple : UnboundedTuple k) : Set Stream :=
  {ω | ∀ i : Fin k, ω i.val = nth tuple i}

private theorem box {k : ℕ} (tuple : UnboundedTuple k) :
    cylinder tuple = Set.pi (Finset.range k : Set ℕ)
      (fun i => {c | ∀ h : i < k, c = nth tuple ⟨i, h⟩}) := by
  ext ω
  simp only [cylinder, Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
  constructor
  · intro h i hi
    exact fun _ => h ⟨i, hi⟩
  · intro h i
    exact h i.val i.isLt i.isLt

private theorem measurable {k : ℕ} (tuple : UnboundedTuple k) :
    MeasurableSet (cylinder tuple) := by
  rw [box]
  exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => trivial)

private theorem product_mass {k : ℕ} (tuple : UnboundedTuple k) :
    (∏ i : Fin k, cyclePMF (nth tuple i)) = ENNReal.ofReal (rho ^ tuple.size) := by
  induction k with
  | zero => simp [UnboundedTuple.size]
  | succ k ih =>
    rw [Fin.prod_univ_succ]
    simp only [nth, Fin.cases_zero, Fin.cases_succ]
    rw [ih]
    change ENNReal.ofReal (rho ^ tuple.1.2.size) *
      ENNReal.ofReal (rho ^ tuple.2.size) = _
    rw [← ENNReal.ofReal_mul (pow_nonneg parameter_bounds.2.2.1 _), ← pow_add]
    rfl

private theorem mass {k : ℕ} (tuple : UnboundedTuple k) :
    streamMeasure (cylinder tuple) = ENNReal.ofReal (rho ^ tuple.size) := by
  classical
  rw [box]
  change (Measure.infinitePi (fun _ : ℕ => cyclePMF.toMeasure)) _ = _
  rw [Measure.infinitePi_pi (fun _ : ℕ => cyclePMF.toMeasure) (fun _ _ => trivial)]
  have values (i : ℕ) (hi : i < k) :
      cyclePMF.toMeasure {c | ∀ h : i < k, c = nth tuple ⟨i, h⟩} =
        cyclePMF (nth tuple ⟨i, hi⟩) := by
    have eq : {c | ∀ h : i < k, c = nth tuple ⟨i, h⟩} = {nth tuple ⟨i, hi⟩} := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨fun h => h hi, fun h _ => h⟩
    rw [eq, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  let f (i : ℕ) : ℝ≥0∞ :=
    if hi : i < k then cyclePMF (nth tuple ⟨i, hi⟩) else 1
  calc
    (∏ i ∈ Finset.range k, cyclePMF.toMeasure
      {c | ∀ h : i < k, c = nth tuple ⟨i, h⟩}) = ∏ i ∈ Finset.range k, f i := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [values i (Finset.mem_range.mp hi)]
        simp only [f, dif_pos (Finset.mem_range.mp hi)]
    _ = ∏ i : Fin k, f i.val := (Fin.prod_univ_eq_prod_range f k).symm
    _ = ∏ i : Fin k, cyclePMF (nth tuple i) := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [f, dif_pos i.isLt]
    _ = _ := product_mass tuple

end Prefix

/-- Actual count weights normalize before the stream is constructed. Every finite
marked prefix has its actual permutation probability limit on this common stream. -/
theorem actual_countable_cycle_law :
    Countable MarkedCycle ∧
    IsProbabilityMeasure streamMeasure ∧
    (∀ k, Function.Bijective (Prefix.nth (k := k))) ∧
    (∀ sign r, (∑' c : Fixed sign r, ENNReal.ofReal (rho ^ c.size)) =
      ENNReal.ofReal (ceiling * b ^ r)) ∧
    (∑' c : MarkedCycle, ENNReal.ofReal (rho ^ c.2.size)) = 1 ∧
    (∀ k (tuple : UnboundedTuple k), MeasurableSet (Prefix.cylinder tuple) ∧
      streamMeasure (Prefix.cylinder tuple) = ENNReal.ofReal (rho ^ tuple.size)) ∧
    (∀ k (tuple : UnboundedTuple k),
      ∃ K H : ℕ, ∃ bounded : Tuple K H k, bounded.erase = tuple ∧
        Tendsto bounded.probability atTop
          (𝓝 ((streamMeasure (Prefix.cylinder tuple)).toReal))) ∧
    ProbabilityTheory.iIndepFun (fun (j : ℕ) (ω : Stream) => ω j) streamMeasure ∧
    (∀ I : Finset ℕ, streamMeasure.map I.restrict =
      Measure.pi (fun _ : I => cyclePMF.toMeasure)) := by
  refine ⟨inferInstance, inferInstance, ?_, fixed_mass, total_mass,
    fun _ tuple => ⟨Prefix.measurable tuple,
    Prefix.mass tuple⟩, ?_, ?_, ?_⟩
  · intro k
    have same : (Prefix.coordinates k : UnboundedTuple k → Fin k → MarkedCycle) =
        Prefix.nth := funext Prefix.coordinates_apply
    rw [← same]
    exact (Prefix.coordinates k).bijective
  · intro k tuple
    obtain ⟨K, H, bounded, erased, limit⟩ :=
      actual_complete_cycles.2.2.2.2.2.2.2.1 k tuple
    refine ⟨K, H, bounded, erased, ?_⟩
    rw [Prefix.mass, ENNReal.toReal_ofReal (pow_nonneg parameter_bounds.2.2.1 _)]
    exact limit
  · exact ProbabilityTheory.iIndepFun_infinitePi (fun _ => measurable_id)
  · exact fun _ => Measure.infinitePi_map_restrict (fun _ : ℕ => cyclePMF.toMeasure)

#print axioms actual_countable_cycle_law

end D5.S1.Words.Patterns.Separable.ActualCycleLaw
