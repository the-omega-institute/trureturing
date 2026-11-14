/- GID: D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation
   generality: I
   mirror-B: D5/B/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.claim; result=D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.result; claim=D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.claim
   digest: Actual support tuples and a finite atomic Bochner barycenter for the accumulated-error assertion. -/

import D5.S3.QuadraticForms.AccumulatedSparseRefutation
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
Ekene E., MathOverflow 509794, revision 2,
https://mathoverflow.net/revisions/509794/2, CC BY-SA 4.0.
The dictionary in the source assertion is the topological support of a
probability on the closed unit ball, and the sum is an ordinary HasSum.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal Topology
open MeasureTheory Finset Matrix

namespace D5.S3.HilbertOperators.Approximation.AccumulatedSupportRefutation

abbrev UnitBall (H : Type) [NormedAddCommGroup H] := {a : H // ‖a‖ ≤ 1}

def errorSet {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] (μ : Measure (UnitBall H)) (d : ℕ) : Set ℝ :=
  {r | ∃ (a : Fin d → UnitBall H) (c : Fin d → ℝ),
    (∀ j, a j ∈ μ.support) ∧
    r = ‖(∫ b : UnitBall H, (b : H) ∂μ) - ∑ j, c j • (a j : H)‖ ^ 2}

def sigmaSq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] (μ : Measure (UnitBall H)) (d : ℕ) : ℝ :=
  sInf (errorSet μ d)

/-- The full Hilbert assertion, using arbitrary real coefficients, repetitions,
the actual support, and existence of an ordinary bounded series total. -/
def claim : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H], ∀ (μ : Measure (UnitBall H)),
    IsProbabilityMeasure μ →
    ∃ T : ℝ, HasSum (fun n : ℕ => sigmaSq μ (n + 1)) T ∧ T ≤ 1

abbrev Space := EuclideanSpace ℝ (Option (Fin 64))

instance space_measurable : MeasurableSpace Space := borel Space

instance space_borel : BorelSpace Space := ⟨rfl⟩

def atom (i : Fin 64) : Space :=
  WithLp.toLp 2 (fun j => if j = none ∨ j = some i then 1 / Real.sqrt 2 else 0)

private theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private theorem atom_norm (i : Fin 64) : ‖atom i‖ = 1 := by
  have h : ‖atom i‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [atom, Fintype.sum_option, div_pow, sqrt_two_sq]
  nlinarith [norm_nonneg (atom i)]

def ballAtom (i : Fin 64) : UnitBall Space := ⟨atom i, (atom_norm i).le⟩

def measure : Measure (UnitBall Space) :=
  (1 / 64 : ℝ≥0∞) • ∑ i : Fin 64, Measure.dirac (ballAtom i)

instance measure_probability : IsProbabilityMeasure measure := by
  constructor
  norm_num [measure, Measure.smul_apply, Measure.finsetSum_apply]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem barycenter_integrable : Integrable (fun b : UnitBall Space => (b : Space)) measure := by
  apply Integrable.smul_measure _ (by norm_num)
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact integrable_dirac (by simp)

theorem barycenter_eq : (∫ b : UnitBall Space, (b : Space) ∂measure) =
    (1 / 64 : ℝ) • ∑ i : Fin 64, atom i := by
  have hi := (integrable_smul_measure (by norm_num : (1 / 64 : ℝ≥0∞) ≠ 0)
    (by norm_num : (1 / 64 : ℝ≥0∞) ≠ ∞)).mp barycenter_integrable
  rw [measure, integral_smul_measure]
  rw [integral_finsetSum_measure]
  · simp [ballAtom]
  · exact integrable_finsetSum_measure.mp hi

theorem support_eq : measure.support = Set.range ballAtom := by
  ext b
  constructor
  · intro hb
    by_contra hn
    have hclosed : IsClosed (Set.range ballAtom) := Set.finite_range ballAtom |>.isClosed
    have hnhds : (Set.range ballAtom)ᶜ ∈ nhds b :=
      hclosed.isOpen_compl.mem_nhds hn
    have hp := (Measure.mem_support_iff_forall b).mp hb _ hnhds
    have hz : measure (Set.range ballAtom)ᶜ = 0 := by
      simp [measure, Measure.smul_apply, Measure.finsetSum_apply, hclosed.measurableSet.compl,
        Measure.dirac_apply']
    rw [hz] at hp
    exact (lt_irrefl _ hp)
  · rintro ⟨i, rfl⟩
    rw [Measure.mem_support_iff_forall]
    intro U hU
    have hmem : ballAtom i ∈ U := mem_of_mem_nhds hU
    have hiU : Measure.dirac (ballAtom i) U ≤
        ∑ j : Fin 64, Measure.dirac (ballAtom j) U :=
      Finset.single_le_sum (f := fun j : Fin 64 => Measure.dirac (ballAtom j) U)
        (fun _ _ => bot_le) (mem_univ i)
    rw [Measure.dirac_apply_of_mem hmem] at hiU
    have hp : 0 < (∑ j : Fin 64, Measure.dirac (ballAtom j)) U := by
      rw [Measure.finsetSum_apply]
      exact lt_of_lt_of_le zero_lt_one hiU
    simpa only [measure, Measure.smul_apply, smul_eq_mul] using
      ENNReal.mul_pos_iff.mpr ⟨(by norm_num : (0 : ℝ≥0∞) < 1 / 64), hp⟩

def combination (c : Fin 64 → ℝ) : Space := ∑ i, c i • atom i

private theorem combination_none (c : Fin 64 → ℝ) :
    combination c none = (∑ i, c i) / Real.sqrt 2 := by
  simp [combination, atom, WithLp.ofLp_sum, Finset.sum_apply,
    div_eq_mul_inv, ← sum_mul]

private theorem combination_some (c : Fin 64 → ℝ) (i : Fin 64) :
    combination c (some i) = c i / Real.sqrt 2 := by
  classical
  simp [combination, atom, WithLp.ofLp_sum, Finset.sum_apply, eq_comm, div_eq_mul_inv]

private theorem barycenter_none : (∫ b : UnitBall Space, (b : Space) ∂measure) none =
    1 / Real.sqrt 2 := by
  rw [barycenter_eq]
  simp [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, atom]

private theorem barycenter_some (i : Fin 64) :
    (∫ b : UnitBall Space, (b : Space) ∂measure) (some i) =
      1 / (64 * Real.sqrt 2) := by
  classical
  rw [barycenter_eq]
  simp [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, atom, eq_comm]
  ring

theorem error_bridge (c : Fin 64 → ℝ) :
    ‖(∫ b : UnitBall Space, (b : Space) ∂measure) - combination c‖ ^ 2 =
      (D5.S3.QuadraticForms.AccumulatedSparseRefutation.vector - (fun i => 8 * c i)) ⬝ᵥ
        (D5.S3.QuadraticForms.AccumulatedSparseRefutation.matrix *ᵥ
          (D5.S3.QuadraticForms.AccumulatedSparseRefutation.vector - (fun i => 8 * c i))) := by
  rw [EuclideanSpace.real_norm_sq_eq,
    D5.S3.QuadraticForms.AccumulatedSparseRefutation.quadratic]
  simp only [Fintype.sum_option, PiLp.sub_apply, barycenter_none, barycenter_some,
    combination_none, combination_some, Pi.sub_apply,
    D5.S3.QuadraticForms.AccumulatedSparseRefutation.vector]
  have hs : (∑ i : Fin 64, (1 / 8 - 8 * c i)) = 8 - 8 * ∑ i, c i := by
    norm_num [sum_sub_distrib, ← mul_sum]
  have hq : (∑ i : Fin 64, (1 / 8 - 8 * c i) ^ 2) =
      1 - 2 * (∑ i, c i) + 64 * ∑ i, c i ^ 2 := by
    simp_rw [show ∀ t : ℝ, (1 / 8 - 8 * t) ^ 2 = 1 / 64 - 2 * t + 64 * t ^ 2 by
      intro t; ring]
    simp [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  have hq' : (∑ i : Fin 64, (1 / (64 * Real.sqrt 2) - c i / Real.sqrt 2) ^ 2) =
      ((1 / 64) - (1 / 32) * (∑ i, c i) + ∑ i, c i ^ 2) / 2 := by
    have h (t : ℝ) : (1 / (64 * Real.sqrt 2) - t / Real.sqrt 2) ^ 2 =
        (1 / 4096 - t / 32 + t ^ 2) / 2 := by
      calc
        _ = ((1 / 64 - t) / Real.sqrt 2) ^ 2 := by congr 1; ring
        _ = (1 / 64 - t) ^ 2 / 2 := by rw [div_pow, sqrt_two_sq]
        _ = _ := by ring
    simp_rw [h]
    simp [← sum_div, sum_add_distrib, sum_sub_distrib]
    ring
  rw [hs, hq, hq']
  rw [← sub_div, div_pow, sqrt_two_sq]
  ring

/-- Consolidation includes repeated atoms, negative coefficients and cancellations. -/
theorem tuple_to_coefficients (d : ℕ) (a : Fin d → UnitBall Space) (r : Fin d → ℝ)
    (ha : ∀ j, a j ∈ measure.support) :
    ∃ c : Fin 64 → ℝ, (univ.filter fun i => c i ≠ 0).card ≤ d ∧
      (∑ j, r j • (a j : Space)) = combination c := by
  classical
  have hex : ∀ j, ∃ i, ballAtom i = a j := by
    intro j
    simpa only [support_eq, Set.mem_range] using ha j
  choose f hf using hex
  let c : Fin 64 → ℝ := fun i => ∑ j, if f j = i then r j else 0
  refine ⟨c, ?_, ?_⟩
  · have hsub : (univ.filter fun i => c i ≠ 0) ⊆ univ.image f := by
      intro i hi
      by_contra hn
      have hz : c i = 0 := by
        apply sum_eq_zero
        intro j _
        simp only [ite_eq_right_iff]
        intro hji
        exact (hn (mem_image.mpr ⟨j, mem_univ _, hji⟩)).elim
      exact (mem_filter.mp hi).2 hz
    exact (card_le_card hsub).trans ((card_image_le).trans (by simp))
  · rw [combination]
    simp_rw [c, sum_smul, ite_smul, zero_smul]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    rw [← hf j]
    simp [ballAtom]

/-- Enumeration and zero padding realize every sparse real coefficient vector
as a source tuple of exactly d support points. -/
theorem coefficients_to_tuple (d : ℕ) (c : Fin 64 → ℝ)
    (hc : (univ.filter fun i => c i ≠ 0).card ≤ d) :
    ∃ (a : Fin d → UnitBall Space) (r : Fin d → ℝ),
      (∀ j, a j ∈ measure.support) ∧
      (∑ j, r j • (a j : Space)) = combination c := by
  classical
  let S := univ.filter fun i => c i ≠ 0
  let eS := S.equivFin
  let e : Fin d ≃ Fin S.card ⊕ Fin (d - S.card) :=
    (finCongr (Nat.add_sub_of_le hc).symm).trans finSumFinEquiv.symm
  let a : Fin d → UnitBall Space := fun j =>
    Sum.elim (fun i => ballAtom (eS.symm i).val) (fun _ => ballAtom 0) (e j)
  let r : Fin d → ℝ := fun j =>
    Sum.elim (fun i => c (eS.symm i).val) (fun _ => 0) (e j)
  refine ⟨a, r, ?_, ?_⟩
  · intro j
    rw [support_eq]
    dsimp [a]
    cases e j with
    | inl i => exact ⟨_, rfl⟩
    | inr i => exact ⟨_, rfl⟩
  · calc
      (∑ j, r j • (a j : Space)) =
          ∑ q : Fin S.card ⊕ Fin (d - S.card),
            Sum.elim (fun i => c (eS.symm i).val • atom (eS.symm i).val)
              (fun _ => 0) q := by
        convert e.sum_comp
          (Sum.elim (fun i => c (eS.symm i).val • atom (eS.symm i).val)
            (fun _ : Fin (d - S.card) => (0 : Space))) using 1
        apply sum_congr rfl
        intro j _
        dsimp [r, a]
        cases e j <;> simp [ballAtom]
      _ = ∑ i : Fin S.card, c (eS.symm i).val • atom (eS.symm i).val := by
        simp [Fintype.sum_sum_type]
      _ = ∑ i : S, c i.val • atom i.val :=
        eS.symm.sum_comp (fun i : S => c i.val • atom i.val)
      _ = ∑ i ∈ S, c i • atom i :=
        (sum_subtype S (fun _ => Iff.rfl) (fun i => c i • atom i)).symm
      _ = combination c := by
        apply sum_subset (filter_subset _ _)
        intro i hi hn
        have : c i = 0 := by simpa [S] using hn
        simp [this]

theorem errorSet_eq (d : ℕ) : errorSet measure d =
    D5.S3.QuadraticForms.AccumulatedSparseRefutation.errorSet
      D5.S3.QuadraticForms.AccumulatedSparseRefutation.matrix
      D5.S3.QuadraticForms.AccumulatedSparseRefutation.vector d := by
  classical
  ext s
  constructor
  · rintro ⟨a, r, ha, rfl⟩
    obtain ⟨c, hc, he⟩ := tuple_to_coefficients d a r ha
    refine ⟨fun i => 8 * c i, ?_, ?_⟩
    · simpa using hc
    · rw [he, error_bridge]
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨a, r, ha, he⟩ := coefficients_to_tuple d (fun i => z i / 8) (by simpa using hz)
    refine ⟨a, r, ha, ?_⟩
    rw [he, error_bridge]
    congr 2 <;> ext i <;> ring

theorem errors_exact (d : ℕ) (hd : 1 ≤ d) (h64 : d ≤ 64) :
    IsLeast (errorSet measure d)
      (D5.S3.QuadraticForms.AccumulatedSparseRefutation.optimum d) := by
  rw [errorSet_eq]
  exact D5.S3.QuadraticForms.AccumulatedSparseRefutation.sparse_minimum d hd h64

theorem errors_zero (d : ℕ) (hd : 64 ≤ d) : IsLeast (errorSet measure d) 0 := by
  classical
  rw [errorSet_eq]
  constructor
  · refine ⟨D5.S3.QuadraticForms.AccumulatedSparseRefutation.vector, ?_, ?_⟩
    · exact (card_le_card (filter_subset _ _)).trans (by simpa using hd)
    · simp
  · rintro s ⟨z, _, rfl⟩
    rw [D5.S3.QuadraticForms.AccumulatedSparseRefutation.quadratic]
    positivity

theorem ordinary_sum : HasSum (fun n : ℕ => sigmaSq measure (n + 1))
    D5.S3.QuadraticForms.AccumulatedSparseRefutation.total := by
  have hz : ∀ n ∉ range 63, sigmaSq measure (n + 1) = 0 := by
    intro n hn
    exact (errors_zero _ (by simp only [mem_range] at hn; omega)).csInf_eq
  have hs : HasSum (fun n : ℕ => sigmaSq measure (n + 1))
      (∑ n ∈ range 63, sigmaSq measure (n + 1)) := hasSum_sum_of_ne_finset_zero hz
  convert hs using 1
  unfold D5.S3.QuadraticForms.AccumulatedSparseRefutation.total
  calc
    _ = ∑ d ∈ Ico 1 64, sigmaSq measure d := by
      apply sum_congr (by decide)
      intro d hd
      exact (errors_exact d (by simp only [mem_Ico] at hd; omega)
        (by simp only [mem_Ico] at hd; omega)).csInf_eq.symm
    _ = _ := by
      simpa only [Nat.reduceSub, Nat.add_comm] using
        sum_Ico_eq_sum_range (fun d => sigmaSq measure d) 1 64

theorem result : ¬ claim := by
  intro h
  obtain ⟨T, hT, hle⟩ := h Space measure inferInstance
  have he := hT.unique ordinary_sum
  rw [he] at hle
  exact (not_le.mpr D5.S3.QuadraticForms.AccumulatedSparseRefutation.accumulation_gt_one) hle

end D5.S3.HilbertOperators.Approximation.AccumulatedSupportRefutation
