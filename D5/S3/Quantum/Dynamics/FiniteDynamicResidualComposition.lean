/- GID: D5/S3/Quantum/Dynamics/FiniteDynamicResidualComposition
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/FiniteDynamicResidualComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite CPTP dynamic residuals compose with the rescaled second time window. -/

/- proof_shape: content
   admission_basis: escape-witness
   escape_witness: result
   The estimate combines a common amplified input, rectangular CPTP contraction,
   and transport of the second error to the window [0,a*T].
   window_bdd, residual_nonneg and pointwise_le_residual are consumed bind-only
   helpers; they organize the two bounded real suprema in result.
   utility: none describes general inequalities, with no finite search,
   numerical reduction, checker or certified-instance content.
   Escape audit unfinished:
   https://github.com/the-omega-institute/trureturing/issues/17928
   The full dynamicResidual source family has no completed whole-family
   variation, sensitivity, actual observational-dependence or source-selection
   evidence. No declared_validated registration is asserted. -/

import D5.S3.QuantumChannels.SchurChannelMixedUnitaryDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.FiniteDynamicResidualComposition

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.QuantumChannels.SchurChannelMixedUnitaryDistance

variable {A B C : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- One half of the supremum of the unhalved stabilized channel discrepancy
on the closed time window. The zero element also defines empty windows. -/
def dynamicResidual (channel : QuantumChannel A B)
    (PA : ℝ → QuantumChannel A A) (PB : ℝ → QuantumChannel B B)
    (a T : ℝ) : ℝ :=
  sSup ({0} ∪ {x : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) T,
    x = diamondDistance (channel.comp (PA t)) ((PB (a * t)).comp channel)}) / 2

private theorem window_bdd (channel : QuantumChannel A B)
    (PA : ℝ → QuantumChannel A A) (PB : ℝ → QuantumChannel B B)
    (a T : ℝ) :
    BddAbove ({0} ∪ {x : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) T,
      x = diamondDistance (channel.comp (PA t)) ((PB (a * t)).comp channel)}) := by
  refine ⟨2, ?_⟩
  rintro x (hx | ⟨t, ht, rfl⟩)
  · have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    rw [hx0]; norm_num
  · exact (diamond_bounds _ _).2

private theorem residual_nonneg (channel : QuantumChannel A B)
    (PA : ℝ → QuantumChannel A A) (PB : ℝ → QuantumChannel B B)
    (a T : ℝ) : 0 ≤ dynamicResidual channel PA PB a T := by
  exact div_nonneg (le_csSup (window_bdd channel PA PB a T) (Or.inl (by simp)))
    (by norm_num)

private theorem pointwise_le_residual (channel : QuantumChannel A B)
    (PA : ℝ → QuantumChannel A A) (PB : ℝ → QuantumChannel B B)
    (a T t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    diamondDistance (channel.comp (PA t)) ((PB (a * t)).comp channel) ≤
      2 * dynamicResidual channel PA PB a T := by
  have h := le_csSup (window_bdd channel PA PB a T) (Or.inr ⟨t, ht, rfl⟩)
  unfold dynamicResidual
  linarith

/-- Dynamic residual composition for independent finite system dimensions.
The second residual is evaluated on the time window of length `a * T`. -/
theorem result (C1 : QuantumChannel A B) (C2 : QuantumChannel B C)
    (PA : ℝ → QuantumChannel A A) (PB : ℝ → QuantumChannel B B)
    (PC : ℝ → QuantumChannel C C) (a b T : ℝ)
    (ha : 0 < a) (_hb : 0 < b) (_hT : 0 ≤ T) :
    dynamicResidual (C2.comp C1) PA PC (a * b) T ≤
      dynamicResidual C1 PA PB a T + dynamicResidual C2 PB PC b (a * T) := by
  have hbound : sSup ({0} ∪ {x : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) T,
      x = diamondDistance ((C2.comp C1).comp (PA t))
        ((PC ((a * b) * t)).comp (C2.comp C1))}) ≤
      2 * dynamicResidual C1 PA PB a T +
        2 * dynamicResidual C2 PB PC b (a * T) := by
    apply csSup_le (show ({0} ∪ {x : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) T,
        x = diamondDistance ((C2.comp C1).comp (PA t))
          ((PC ((a * b) * t)).comp (C2.comp C1))}).Nonempty from
      ⟨0, Or.inl (by simp)⟩)
    rintro x (hx | ⟨t, ht, rfl⟩)
    · have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      rw [hx0]
      nlinarith [residual_nonneg C1 PA PB a T,
        residual_nonneg C2 PB PC b (a * T)]
    · have hat : a * t ∈ Set.Icc (0 : ℝ) (a * T) :=
        ⟨mul_nonneg ha.le ht.1, mul_le_mul_of_nonneg_left ht.2 ha.le⟩
      have hfirst := pointwise_le_residual C1 PA PB a T t ht
      have hsecond := pointwise_le_residual C2 PB PC b (a * T) (a * t) hat
      have hstep : diamondDistance ((C2.comp C1).comp (PA t))
          ((PC ((a * b) * t)).comp (C2.comp C1)) ≤
          diamondDistance (C1.comp (PA t)) ((PB (a * t)).comp C1) +
            diamondDistance (C2.comp (PB (a * t))) ((PC (b * (a * t))).comp C2) := by
        -- Split at C2 PB(at) C1, retaining the common reference input.
        apply csSup_le (show ({0} ∪ {y : ℝ | ∃ n : ℕ,
            ∃ ρ : DensityState (Fin n × A),
              y = referenceError ((C2.comp C1).comp (PA t))
                ((PC ((a * b) * t)).comp (C2.comp C1)) ρ}).Nonempty from
          ⟨0, Or.inl (by simp)⟩)
        rintro y (hy | ⟨n, ρ, rfl⟩)
        · have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
          rw [hy0]
          exact add_nonneg (diamond_bounds _ _).1 (diamond_bounds _ _).1
        · have htri := traceDistance_triangle
            (referenceState ((C2.comp C1).comp (PA t)) ρ)
            (referenceState ((C2.comp (PB (a * t))).comp C1) ρ)
            (referenceState ((PC ((a * b) * t)).comp (C2.comp C1)) ρ)
          have hc := trace_contract_rectangular (referenceChannel C2)
            (referenceState (C1.comp (PA t)) ρ)
            (referenceState ((PB (a * t)).comp C1) ρ)
          have hleft := reference_error_le_diamond
            (C1.comp (PA t)) ((PB (a * t)).comp C1) ρ
          have hright := reference_error_le_diamond
            (C2.comp (PB (a * t))) ((PC (b * (a * t))).comp C2)
            (referenceState C1 ρ)
          have htime : (a * b) * t = b * (a * t) := by ring
          rw [htime] at htri
          change referenceError ((C2.comp C1).comp (PA t))
              ((PC (b * (a * t))).comp (C2.comp C1)) ρ / 2 ≤
            traceDistance
              ((referenceChannel C2).mapState (referenceState (C1.comp (PA t)) ρ))
              ((referenceChannel C2).mapState (referenceState ((PB (a * t)).comp C1) ρ)) +
            referenceError (C2.comp (PB (a * t))) ((PC (b * (a * t))).comp C2)
              (referenceState C1 ρ) / 2 at htri
          change _ ≤ referenceError (C1.comp (PA t)) ((PB (a * t)).comp C1) ρ / 2 at hc
          rw [htime]
          linarith
      linarith
  unfold dynamicResidual at hbound ⊢
  linarith

#print axioms result

end D5.S3.Quantum.Dynamics.FiniteDynamicResidualComposition
