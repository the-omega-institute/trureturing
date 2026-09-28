/- GID: D5/S3/Quantum/Thermal/ClassicalProductRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Thermal/ClassicalProductRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Genuine measure-level KL recovery, finite-defect accounting, unique minimum, and reversible invariance. -/

import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Tactic

/-!
Uses Mathlib's ENNReal-valued KL divergence, including its absolute-continuity
and integrability conditions. No arbitrary divergence function is postulated.
For standard Borel hidden spaces the conditional kernel is constructed by
Mathlib from an arbitrary joint law. The pointwise conditional-KL integral,
Gaussian density calculation, and metaplectic quantization are not established
by this module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Thermal.ClassicalProductRecovery

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def thermalLift (ν : Measure X) (γh : Measure Y) : Measure (X × Y) :=
  ν ⊗ₘ Kernel.const X γh

@[simp]
theorem thermalLift_eq_prod (ν : Measure X) (γh : Measure Y)
    [IsFiniteMeasure ν] [IsProbabilityMeasure γh] :
    thermalLift ν γh = ν.prod γh := by
  simp [thermalLift]

@[simp]
theorem thermalLift_fst (ν : Measure X) (γh : Measure Y)
    [IsFiniteMeasure ν] [IsProbabilityMeasure γh] :
    (thermalLift ν γh).fst = ν := by
  unfold thermalLift
  exact Measure.fst_compProd ν (Kernel.const X γh)

/-- Product thermal recovery is an actual chain rule on measures. -/
theorem product_recovery_chain (ν γr : Measure X) (γh : Measure Y)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure γr] [IsProbabilityMeasure γh]
    (κ : Kernel X Y) [IsMarkovKernel κ] :
    klDiv (ν ⊗ₘ κ) (γr.prod γh) =
      klDiv ν γr + klDiv (ν ⊗ₘ κ) (ν.prod γh) := by
  simpa only [Measure.compProd_const] using
    klDiv_compProd_eq_add ν γr κ (Kernel.const X γh)

/-- Finite total KL implies both terms are finite, before taking real parts. -/
theorem recovery_terms_finite (ν γr : Measure X) (γh : Measure Y)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure γr] [IsProbabilityMeasure γh]
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (h : klDiv (ν ⊗ₘ κ) (γr.prod γh) ≠ ⊤) :
    klDiv ν γr ≠ ⊤ ∧ klDiv (ν ⊗ₘ κ) (ν.prod γh) ≠ ⊤ := by
  constructor
  · intro hm
    apply h
    simp [product_recovery_chain ν γr γh κ, hm]
  · intro hr
    apply h
    simp [product_recovery_chain ν γr γh κ, hr]

theorem recovery_defect_real (ν γr : Measure X) (γh : Measure Y)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure γr] [IsProbabilityMeasure γh]
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (h : klDiv (ν ⊗ₘ κ) (γr.prod γh) ≠ ⊤) :
    (klDiv (ν ⊗ₘ κ) (γr.prod γh)).toReal - (klDiv ν γr).toReal =
      (klDiv (ν ⊗ₘ κ) (ν.prod γh)).toReal := by
  obtain ⟨hm, hr⟩ := recovery_terms_finite ν γr γh κ h
  rw [product_recovery_chain ν γr γh κ, ENNReal.toReal_add hm hr]
  ring

/-- The minimum is attained by the constructed product law, not a supplied optimizer. -/
theorem thermalLift_minimizes (ν γr : Measure X) (γh : Measure Y)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure γr] [IsProbabilityMeasure γh]
    (κ : Kernel X Y) [IsMarkovKernel κ] :
    klDiv (ν.prod γh) (γr.prod γh) = klDiv ν γr ∧
      klDiv (ν.prod γh) (γr.prod γh) ≤ klDiv (ν ⊗ₘ κ) (γr.prod γh) := by
  have he : klDiv (ν.prod γh) (γr.prod γh) = klDiv ν γr := by
    simpa only [Measure.compProd_const] using
      klDiv_compProd_left ν γr (Kernel.const X γh)
  refine ⟨he, ?_⟩
  rw [he, product_recovery_chain ν γr γh κ]
  calc
    klDiv ν γr = klDiv ν γr + 0 := by rw [add_zero]
    _ ≤ klDiv ν γr + klDiv (ν ⊗ₘ κ) (ν.prod γh) :=
      add_le_add_left (zero_le _) _

/-- Finiteness of the marginal value is essential: infinity cannot be cancelled. -/
theorem thermalLift_unique_minimum (ν γr : Measure X) (γh : Measure Y)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure γr] [IsProbabilityMeasure γh]
    (κ : Kernel X Y) [IsMarkovKernel κ] (hfin : klDiv ν γr ≠ ⊤) :
    klDiv (ν ⊗ₘ κ) (γr.prod γh) = klDiv ν γr ↔ ν ⊗ₘ κ = ν.prod γh := by
  constructor
  · intro h
    rw [product_recovery_chain ν γr γh κ] at h
    have hz : klDiv (ν ⊗ₘ κ) (ν.prod γh) = 0 :=
      (ENNReal.add_right_inj hfin).mp (by simpa using h)
    exact klDiv_eq_zero_iff.mp hz
  · intro h
    rw [product_recovery_chain ν γr γh κ, h, klDiv_self, add_zero]

/-- Data processing in both directions proves invariance, including infinite KL. -/
theorem klDiv_measurableEquiv {Z : Type*} [MeasurableSpace Z]
    (μ π : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure π]
    (e : X ≃ᵐ Z) : klDiv (μ.map e) (π.map e) = klDiv μ π := by
  apply le_antisymm (klDiv_map_le μ π e.measurable)
  have h := klDiv_map_le (μ.map e) (π.map e) e.symm.measurable
  simpa only [Measure.map_map e.symm.measurable e.measurable,
    Function.comp_def, MeasurableEquiv.symm_apply_apply, Measure.map_id] using h

theorem klDiv_reference_preserving (μ π : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure π]
    (e : X ≃ᵐ X) (hπ : π.map e = π) :
    klDiv (μ.map e) π = klDiv μ π := by
  simpa only [hπ] using klDiv_measurableEquiv μ π e

/-- The full and observed distinguishabilities are separately conserved by an
intertwining reversible evolution preserving both reference measures. -/
theorem predictive_defect_invariant (μ π : Measure X) (γ : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure π] [IsFiniteMeasure γ]
    (observe : X → Y) (ho : Measurable observe)
    (e : X ≃ᵐ X) (f : Y ≃ᵐ Y)
    (hπ : π.map e = π) (hγ : γ.map f = γ)
    (he : ∀ x, observe (e x) = f (observe x)) :
    (klDiv (μ.map e) π, klDiv ((μ.map e).map observe) γ) =
      (klDiv μ π, klDiv (μ.map observe) γ) := by
  have hm : (μ.map e).map observe = (μ.map observe).map f := by
    rw [Measure.map_map ho e.measurable, Measure.map_map f.measurable ho]
    congr 1
    funext x
    exact he x
  rw [hm, klDiv_reference_preserving μ π e hπ,
    klDiv_reference_preserving (μ.map observe) γ f hγ]


section StandardBorel

variable [StandardBorelSpace Y] [Nonempty Y]

/-- No disintegration is assumed here: the kernel is constructed from μ. -/
theorem arbitrary_joint_recovery_chain (μ : Measure (X × Y))
    (γr : Measure X) (γh : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γr] [IsProbabilityMeasure γh] :
    klDiv μ (γr.prod γh) = klDiv μ.fst γr + klDiv μ (μ.fst.prod γh) := by
  have hd : μ.fst ⊗ₘ μ.condKernel = μ := μ.disintegrate μ.condKernel
  simpa only [hd] using product_recovery_chain μ.fst γr γh μ.condKernel

/-- Finite physical deficit equals the KL to the constructed thermal lift. -/
theorem arbitrary_joint_recovery_defect (μ : Measure (X × Y))
    (γr : Measure X) (γh : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γr] [IsProbabilityMeasure γh]
    (hfin : klDiv μ (γr.prod γh) ≠ ⊤) :
    (klDiv μ (γr.prod γh)).toReal - (klDiv μ.fst γr).toReal =
      (klDiv μ (μ.fst.prod γh)).toReal := by
  have hd : μ.fst ⊗ₘ μ.condKernel = μ := μ.disintegrate μ.condKernel
  have hf : klDiv (μ.fst ⊗ₘ μ.condKernel) (γr.prod γh) ≠ ⊤ := by
    simpa only [hd] using hfin
  simpa only [hd] using recovery_defect_real μ.fst γr γh μ.condKernel hf

/-- Unique optimum over every joint probability law with the prescribed marginal. -/
theorem all_joint_laws_unique_minimum (ν γr : Measure X) (γh : Measure Y)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure γr] [IsProbabilityMeasure γh]
    (hfin : klDiv ν γr ≠ ⊤) (μ : Measure (X × Y)) [IsProbabilityMeasure μ]
    (hmarg : μ.fst = ν) :
    klDiv ν γr ≤ klDiv μ (γr.prod γh) ∧
      (klDiv μ (γr.prod γh) = klDiv ν γr ↔ μ = ν.prod γh) := by
  have hd : μ.fst ⊗ₘ μ.condKernel = μ := μ.disintegrate μ.condKernel
  have hle := (thermalLift_minimizes μ.fst γr γh μ.condKernel).2
  have he := (thermalLift_minimizes μ.fst γr γh μ.condKernel).1
  rw [he, hd, hmarg] at hle
  have hf : klDiv μ.fst γr ≠ ⊤ := by simpa only [hmarg] using hfin
  have hu := thermalLift_unique_minimum μ.fst γr γh μ.condKernel hf
  exact ⟨hle, by simpa only [hd, hmarg] using hu⟩

/-- Equality of the actual measures, rather than equality of formal scalar symbols. -/
theorem zero_recovery_iff_product (μ : Measure (X × Y)) (γh : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γh] :
    klDiv μ (μ.fst.prod γh) = 0 ↔ μ = μ.fst.prod γh := klDiv_eq_zero_iff

end StandardBorel

#print axioms recovery_defect_real
#print axioms thermalLift_unique_minimum
#print axioms predictive_defect_invariant
#print axioms arbitrary_joint_recovery_defect
#print axioms all_joint_laws_unique_minimum

end D5.S3.Quantum.Thermal.ClassicalProductRecovery
