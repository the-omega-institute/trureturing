/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.NumberTheory.Real.GoldenRatio]
   utility: none
   digest: All-occurrence descendant masses of the original Fibonacci sources. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedNavigationCompiler
import D5.S3.Arith.FibonacciAtomic.Observer.ActualCompletionHorizon
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.NativeRotationDepthGap
import Mathlib.NumberTheory.Real.GoldenRatio
import D5.S0.Diagonal.Probability.EquivariantEscape

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceMass

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply nodes readout)
open ActualLeafHistoryRigidity (subtree)
open AncestorAreaInstability (T)
open Observer.NativeRankedNavigationCompiler (pathCost pathThreshold atomic_navigation)
open D5.S0.Diagonal.Probability.EquivariantEscape
  (uniformPmf uniformPmf_toOuterMeasure_apply)
open MeasureTheory
open scoped BigOperators ENNReal

/-- Every original occurrence, including the root and both terminal labels. -/
def vertices (n : ℕ) : Finset Address := (nodes (T n)).toFinset

/-- Actual node cardinality. -/
def N (n : ℕ) : ℕ := (vertices n).card

/-- The actual occurrence type for one source. -/
abbrev Node (n : ℕ) := ↥(vertices n)

instance (n : ℕ) : MeasurableSpace (Node n) := ⊤
instance (n : ℕ) : DiscreteMeasurableSpace (Node n) := ⟨fun _ => trivial⟩

theorem root_mem (n : ℕ) : [] ∈ vertices n := by
  unfold vertices
  cases T n <;> simp [nodes]

instance (n : ℕ) : Nonempty (Node n) := ⟨⟨[], root_mem n⟩⟩

/-- Uniform probability on all actual nodes of this source. -/
def μ (n : ℕ) : Measure (Node n) := (uniformPmf (Node n)).toMeasure

instance (n : ℕ) : IsProbabilityMeasure (μ n) := by unfold μ; infer_instance

/-- Actual reached descendants, with absent prefixes contributing the empty set. -/
def descendants (n : ℕ) (p : Address) : Finset Address :=
  (vertices n).filter (p.IsPrefix ·)

/-- All-occurrence descendant mass, computed with the actual node cardinality. -/
def mass (n : ℕ) (p : Address) : ℝ := (descendants n p).card / (N n : ℝ)

/-- The reciprocal golden ratio. -/
abbrev a : ℝ := Real.goldenRatio⁻¹

theorem cardinality (n : ℕ) : N n = 2 * Nat.fib (n+1) - 1 := by
  rw [N, vertices, List.toFinset_card_of_nodup
    (Observer.ActualPureAcquisitionCompiler.nodes_nodup _),
    Observer.ActualCompletionHorizon.nodes_count]
  have h := SourceCoordinates.NativeRotationDepthGap.iterate_length (.of true) n
  simpa [T, GenealogicalFiberTransport.composition] using congrArg (fun k => 2*k-1) h

theorem N_pos (n : ℕ) : 0 < N n :=
  Finset.card_pos.mpr ⟨[], root_mem n⟩

theorem node_iff (S : Source) (x : Address) :
    x ∈ nodes S ↔ ∃ U, subtree x S = some U := by
  induction S generalizing x with
  | of b => cases x <;> simp [nodes, subtree]
  | mul S U ihS ihU =>
    cases x with
    | nil => simp [nodes, subtree]
    | cons b x => cases b <;> simp [nodes, subtree, ihS, ihU]

private theorem append_subtree (p q : Address) (S : Source) :
    subtree (p ++ q) S = (subtree p S).bind (subtree q) :=
  ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 p q S

private theorem descendants_subtree (n : ℕ) (p : Address) (U : Source)
    (hp : subtree p (T n) = some U) :
    descendants n p = (nodes U).toFinset.image (p ++ ·) := by
  classical
  ext x
  simp only [descendants, vertices, Finset.mem_filter, List.mem_toFinset,
    Finset.mem_image]
  constructor
  · rintro ⟨hx, ⟨q, rfl⟩⟩
    obtain ⟨V, hV⟩ := (node_iff _ _).mp hx
    rw [append_subtree, hp] at hV
    exact ⟨q, (node_iff _ _).mpr ⟨V, hV⟩, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨V, hV⟩ := (node_iff _ _).mp hq
    exact ⟨(node_iff _ _).mpr ⟨V, by rw [append_subtree, hp]; exact hV⟩,
      ⟨q, rfl⟩⟩

private theorem descendants_absent (n : ℕ) (p : Address)
    (hp : subtree p (T n) = none) : descendants n p = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hx, q, rfl⟩ := Finset.mem_filter.mp hx
  obtain ⟨V, hV⟩ := (node_iff _ _).mp (List.mem_toFinset.mp hx)
  simp [append_subtree, hp] at hV

theorem cost_length (p : Address) : p.length ≤ pathCost p := by
  induction p with
  | nil => rfl
  | cons b p ih => cases b <;> simp [pathCost, List.length_cons] at * <;> omega

private theorem threshold_last (p : Address) (hp : p ≠ []) :
    pathThreshold p = max (pathCost p) (pathCost p.dropLast + 2) := by
  induction p with
  | nil => exact False.elim (hp rfl)
  | cons b p ih =>
    cases p with
    | nil => cases b <;> decide
    | cons c p =>
      have hh := ih (by simp)
      cases b <;> simp only [pathThreshold, pathCost, List.dropLast_cons_cons] at * <;>
        omega

private theorem count_bounds (n : ℕ) :
    Real.goldenRatio^n / Real.goldenRatio ≤ (N n : ℝ) ∧
    (N n : ℝ)+1 ≤ 2 * Real.goldenRatio^n := by
  have hp := Real.goldenRatio_pos
  have h1 := Real.one_lt_goldenRatio
  have countRec (j : ℕ) : (N (j+2) : ℝ) + 1 = (N (j+1) : ℝ)+1 + ((N j : ℝ)+1) := by
    have hfj : 1 ≤ Nat.fib (j+1) := Nat.succ_le_iff.mpr
      (Nat.fib_pos.mpr (by omega))
    have hfk : 1 ≤ Nat.fib (j+2) := Nat.succ_le_iff.mpr
      (Nat.fib_pos.mpr (by omega))
    have hn : N (j+2)+1 = (N (j+1)+1)+(N j+1) := by
      simp only [cardinality]
      change 2*Nat.fib (j+3)-1+1 =
        (2*Nat.fib (j+2)-1+1)+(2*Nat.fib (j+1)-1+1)
      rw [show j+3 = (j+1)+2 by omega, Nat.fib_add_two]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      omega
    exact_mod_cast hn
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [show N 0 = 1 by rw [cardinality]; decide, pow_zero]
    norm_num only [Nat.cast_one]
    constructor
    · exact (div_le_iff₀ hp).mpr (by simpa using h1.le)
    · norm_num
  | one =>
    constructor
    · rw [show N 1 = 1 by rw [cardinality]; decide, pow_one]
      simpa only [Nat.cast_one] using (div_self Real.goldenRatio_ne_zero).le
    · rw [show N 1 = 1 by rw [cardinality]; decide, pow_one]
      norm_num only [Nat.cast_one]
      linarith
  | more n ih ih' =>
    have he := Real.goldenRatio_pow_sub_goldenRatio_pow n
    have hr := countRec n
    rcases ih with ⟨hl, hu⟩
    rcases ih' with ⟨hl', hu'⟩
    constructor
    · rw [div_le_iff₀ hp] at hl hl' ⊢
      nlinarith [mul_pos hp (by norm_num : (0:ℝ)<1)]
    · linarith

private theorem point_mass (n : ℕ) (x : Node n) :
    μ n {x} = (N n : ℝ≥0∞)⁻¹ := by
  classical
  rw [μ, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (measurableSet_singleton x),
    uniformPmf_toOuterMeasure_apply]
  simp [Node, N]

private theorem measure_mass (n : ℕ) (p : Address) :
    (μ n {x | p.IsPrefix x.val}).toReal = mass n p := by
  classical
  let e : {x : Node n // p.IsPrefix x.val} ≃ ↥(descendants n p) := {
    toFun := fun x => ⟨x.val.val, Finset.mem_filter.mpr ⟨x.val.property, x.property⟩⟩
    invFun := fun x => ⟨⟨x.val, (Finset.mem_filter.mp x.property).1⟩,
      (Finset.mem_filter.mp x.property).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hc := Fintype.card_congr e
  rw [μ, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (by measurability),
    uniformPmf_toOuterMeasure_apply]
  simp only [Fintype.card_coe, ENNReal.toReal_div, ENNReal.toReal_natCast]
  change (Fintype.card {x : Node n // p.IsPrefix x.val} : ℝ) /
    (vertices n).card = mass n p
  rw [hc, Fintype.card_coe]
  rfl

private theorem root_label (n : ℕ) : readout [] (T n) =
    if n = 0 then Reply.alpha else if n = 1 then Reply.beta else Reply.branch := by
  cases n with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n =>
      have hr := (SourceTransportCentralizer.source_transport_centralizer.1 (T n)).mpr
        ⟨n, rfl⟩
      have ht : T (n+2) = .mul (T (n+1)) (T n) := by
        simpa only [T, Function.iterate_succ_apply', Nat.add_assoc] using hr
      rw [show n+1+1 = n+2 by omega, ht]
      simp [readout]

private theorem read_subtree (p : Address) (S U : Source)
    (hp : subtree p S = some U) : readout p S = readout [] U := by
  have h := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1 p [] S
  simpa [hp] using h

/-- Native reached-address geometry and the uniform all-occurrence mass envelope. -/
theorem finite_source_masses :
    (∀ (n : ℕ) (p : Address), p ≠ [] →
      ((∃ U, subtree p (T n) = some U) ↔
        pathCost p ≤ n ∧ pathCost p.dropLast + 2 ≤ n)) ∧
    (∀ (n : ℕ) (p : Address), p ≠ [] →
      pathCost p ≤ n → pathCost p.dropLast + 2 ≤ n →
      subtree p (T n) = some (T (n-pathCost p)) ∧
      mass n p = (N (n-pathCost p) : ℝ) / (N n : ℝ)) ∧
    (∀ (n : ℕ) (p : Address), subtree p (T n) = none → mass n p = 0) ∧
    (∀ (n : ℕ) (p : Address), mass n p ≤ 2*Real.goldenRatio*a^p.length) ∧
    (∀ (n : ℕ) (p : Address), (μ n {x | p.IsPrefix x.val}).toReal = mass n p) ∧
    (∀ (n : ℕ) (x : Node n), μ n {x} = (N n : ℝ≥0∞)⁻¹) ∧
    (∀ (n : ℕ) (p : Address), subtree p (T n) = some (T (n-pathCost p)) →
      readout p (T n) = if n-pathCost p = 0 then Reply.alpha
        else if n-pathCost p = 1 then Reply.beta else Reply.branch) ∧
    (∀ (n : ℕ) (p : Address) (b : Bool), subtree p (T n) = some (.of b) →
      ∀ q : Address, q ≠ [] → subtree (p ++ q) (T n) = none) ∧
    (∀ n : ℕ, mass n [] = 1 ∧ readout [] (T n) =
      if n = 0 then Reply.alpha else if n = 1 then Reply.beta else Reply.branch) := by
  classical
  have reached (n : ℕ) (p : Address) :
      (∃ U, subtree p (T n) = some U) ↔ pathThreshold p ≤ n := by
    constructor
    · rintro ⟨U, hU⟩
      exact ((atomic_navigation p n U).mp hU).choose_spec.1
    · intro h
      refine ⟨T (n-pathCost p), (atomic_navigation p n _).mpr
        ⟨n-pathCost p, h, ?_, rfl⟩⟩
      have hc : pathCost p ≤ pathThreshold p := by
        induction p with
        | nil => rfl
        | cons b p ih => cases b <;> simp [pathCost, pathThreshold] at * <;> omega
      omega
  have exactTree (n : ℕ) (p : Address) (h : pathThreshold p ≤ n) :
      subtree p (T n) = some (T (n-pathCost p)) := by
    obtain ⟨U, hU⟩ := (reached n p).mpr h
    obtain ⟨r, _, he, hu⟩ := (atomic_navigation p n U).mp hU
    have hr : r = n-pathCost p := by omega
    subst r
    simpa [T] using hU.trans (congrArg some hu.symm)
  have ratio (n : ℕ) (p : Address) (h : pathThreshold p ≤ n) :
      mass n p = (N (n-pathCost p) : ℝ) / (N n : ℝ) := by
    rw [mass, descendants_subtree n p _ (exactTree n p h),
      Finset.card_image_of_injective _ (List.append_right_injective _)]
    rfl
  refine ⟨?_, ?_, ?_, ?_, measure_mass, point_mass, ?_, ?_, ?_⟩
  · intro n p hp
    rw [reached, threshold_last p hp, max_le_iff]
  · intro n p hp hc hb
    have ht : pathThreshold p ≤ n := by rw [threshold_last p hp]; exact max_le hc hb
    exact ⟨exactTree n p ht, ratio n p ht⟩
  · intro n p hp
    simp [mass, descendants_absent n p hp]
  · intro n p
    by_cases ht : pathThreshold p ≤ n
    · rw [ratio n p ht]
      have hc : pathCost p ≤ n := by
        obtain ⟨U, hu⟩ := (reached n p).mpr ht
        obtain ⟨r, _, he, _⟩ := (atomic_navigation p n U).mp hu
        omega
      have hlo := (count_bounds n).1
      have hup := (count_bounds (n-pathCost p)).2
      have hn : 0 < (N n : ℝ) := by exact_mod_cast N_pos n
      have hpow : Real.goldenRatio^n =
          Real.goldenRatio^(n-pathCost p) * Real.goldenRatio^(pathCost p) := by
        rw [← pow_add, Nat.sub_add_cancel hc]
      have he : (N (n-pathCost p) : ℝ) / (N n : ℝ) ≤
          2*Real.goldenRatio*a^(pathCost p) := by
        apply (div_le_iff₀ hn).mpr
        have hp := Real.goldenRatio_pos
        have hpos : 0 < Real.goldenRatio^(pathCost p) := pow_pos hp _
        rw [div_le_iff₀ hp, hpow] at hlo
        simp only [a, inv_pow]
        rw [show 2*Real.goldenRatio*(Real.goldenRatio^pathCost p)⁻¹*(N n : ℝ) =
          (2*Real.goldenRatio*(N n : ℝ))/(Real.goldenRatio^pathCost p) by ring]
        apply (le_div_iff₀ hpos).mpr
        nlinarith
      apply he.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_of_le_one (inv_nonneg.mpr Real.goldenRatio_pos.le)
        (inv_le_one_of_one_le₀ Real.one_lt_goldenRatio.le) (cost_length p)
    · have hab : subtree p (T n) = none := by
        cases hs : subtree p (T n) with
        | none => rfl
        | some U => exact False.elim (ht ((reached n p).mp ⟨U, hs⟩))
      rw [mass, descendants_absent n p hab]
      simp only [Finset.card_empty, Nat.cast_zero, zero_div]
      positivity
  · intro n p hp
    rw [read_subtree p _ _ hp, root_label]
  · intro n p b hp q hq
    rw [append_subtree, hp]
    cases q with
    | nil => exact False.elim (hq rfl)
    | cons c q => rfl
  · intro n
    refine ⟨?_, root_label n⟩
    simp [mass, descendants, N, Finset.ne_empty_of_mem (root_mem n)]

end D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceMass
