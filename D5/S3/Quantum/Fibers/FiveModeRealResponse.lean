/- GID: D5/S3/Quantum/Fibers/FiveModeRealResponse
   generality: I
   mirror-B: D5/B/S3/Quantum/Fibers/FiveModeRealResponse
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual five-mode nonnegative waits separate precisely the real parts of Hermitian inputs. -/

import D5.S3.Quantum.QuantumChannels.RealPartPositiveObstruction
import D5.S3.Quantum.Fibers.FiveModeRealWaitSpan
import D5.S3.Quantum.Fibers.RankOneFeedbackProtocol
import D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence
import Mathlib.LinearAlgebra.Dimension.Finrank
import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix MatrixOrder ComplexOrder
open NormedSpace
namespace D5.S3.Quantum.Fibers.FiveModeRealResponse
open D5.S3.Quantum.Fibers.NonnegativeConjugationSpan
open D5.S3.Quantum.Fibers.FiveModeRealWaitSpan
open D5.S3.Quantum.Fibers.RankOneFeedbackProtocol
open D5.S3.Quantum.QuantumChannels.RealPartPositiveObstruction
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

section RealWaitRealization
open scoped Matrix.Norms.Operator

/-- Entrywise real coordinates, without adjoining imaginary measurements. -/
def realEntries (X : Matrix (Fin 5) (Fin 5) ℂ) : Matrix (Fin 5) (Fin 5) ℝ := X.map Complex.re

/-- The actual real orthogonal wait embedded in the complex five-mode algebra. -/
def walk (t : NNReal) : Matrix (Fin 5) (Fin 5) ℂ :=
  (exp ((t : ℝ) • generator)).map Complex.ofReal

private theorem real_transpose_wait (t : ℝ) :
    (exp (t • generator)).transpose = exp (t • (-generator)) := by
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, generator_skew]

private theorem walk_zero : walk 0 = 1 := by simp [walk]
private theorem walk_add (t u : NNReal) : walk (t+u) = walk u * walk t := by
  have hc := ((Commute.refl generator).smul_left (u : ℝ)).smul_right (t : ℝ)
  simp only [walk, NNReal.coe_add, add_smul]
  rw [add_comm, Matrix.exp_add_of_commute _ _ hc]
  exact Matrix.map_mul (f := Complex.ofRealHom)

private theorem walk_conj (t : NNReal) :
    (walk t)ᴴ = (exp ((t : ℝ) • (-generator))).map Complex.ofReal := by
  have ht := real_transpose_wait (t : ℝ)
  ext i j
  have he := congrArg Complex.ofReal (congrFun (congrFun ht i) j)
  simpa [walk] using he

private theorem walk_unitary (t : NNReal) : (walk t)ᴴ * walk t = 1 := by
  have he : exp ((t : ℝ) • (-generator)) * exp ((t : ℝ) • generator) = 1 := by
    rw [smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl _)),
      neg_add_cancel, exp_zero]
  rw [walk_conj, walk]
  change (exp ((t : ℝ) • (-generator))).map Complex.ofRealHom *
    (exp ((t : ℝ) • generator)).map Complex.ofRealHom = 1
  rw [← Matrix.map_mul, he]
  simp

/-- The fixed menu uses exactly these waits, complete rank-one reads, and Stop. -/
def menu : Menu (Fin 5) := unitaryMenu walk walk_zero walk_add walk_unitary

private theorem first_effect_real (t : NNReal) (s : Fin 5) :
    firstEffect walk t s =
      (conjugate generator (Matrix.single s s 1) t).map Complex.ofReal := by
  rw [firstEffect, walk_conj, walk]
  change (exp ((t : ℝ) • (-generator))).map Complex.ofRealHom *
    projector s * (exp ((t : ℝ) • generator)).map Complex.ofRealHom =
    (exp ((t : ℝ) • (-generator)) * Matrix.single s s 1 *
      exp ((t : ℝ) • generator)).map Complex.ofRealHom
  simp only [Matrix.map_mul, Matrix.map_single, map_one, projector]

private theorem real_trace_pairing (E : Matrix (Fin 5) (Fin 5) ℝ)
    (X : Matrix (Fin 5) (Fin 5) ℂ) :
    (Matrix.trace (E.map Complex.ofReal * X)).re = Matrix.trace (E * realEntries X) := by
  simp [Matrix.trace, Matrix.mul_apply, realEntries, Complex.mul_re]

private theorem realEntries_symmetric (X : Matrix (Fin 5) (Fin 5) ℂ)
    (hX : X.IsHermitian) : (realEntries X).transpose = realEntries X := by
  ext i j
  have h := congrArg Complex.re (congrFun (congrFun hX i) j)
  simpa [realEntries] using h

private theorem waits_separate_real (X Y : Matrix (Fin 5) (Fin 5) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (h : ∀ t : NNReal, ∀ s : Fin 5,
      (Matrix.trace (firstEffect walk t s * X)).re =
        (Matrix.trace (firstEffect walk t s * Y)).re) : realEntries X = realEntries Y := by
  let D := realEntries X - realEntries Y
  have hd : D.transpose = D := by
    simp [D, Matrix.transpose_sub, realEntries_symmetric X hX, realEntries_symmetric Y hY]
  let pairing : Matrix (Fin 5) (Fin 5) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun E => Matrix.trace (E * D)
      map_add' := by intro E F; simp [Matrix.add_mul, Matrix.trace_add]
      map_smul' := by intro c E; simp }
  have hp : ∀ E ∈ waitSpan, pairing E = 0 := by
    intro E hE
    induction hE using Submodule.span_induction with
    | mem E hE =>
      obtain ⟨⟨t,s⟩, rfl⟩ := hE
      have hs := h t s
      simp only [first_effect_real, real_trace_pairing] at hs
      simpa [pairing, D, Matrix.mul_sub, Matrix.trace_sub, sub_eq_zero] using hs
    | zero => simp
    | add E F _ _ he hf => simp [map_add, he, hf]
    | smul c E _ he => simp [map_smul, he]
  have hall : ∀ E, E.transpose = E → Matrix.trace (E * D) = 0 := by
    intro E hE
    exact hp E (by rw [five_mode_nonnegative_wait_span]; exact hE)
  have hz (i j : Fin 5) : D i j = 0 := by
    have hs : (Matrix.single i j (1 : ℝ) + Matrix.single j i 1).transpose =
        Matrix.single i j 1 + Matrix.single j i 1 := by simp [Matrix.transpose_add, add_comm]
    have hh := hall _ hs
    have hij : D j i = D i j := congrFun (congrFun hd i) j
    simp [Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, hij] at hh
    linarith
  ext i j
  exact sub_eq_zero.mp (hz i j)

private abbrev Upper := {p : Fin 5 × Fin 5 // p.1 ≤ p.2}
private def upperEquiv : symmetricSpace ≃ₗ[ℝ] (Upper → ℝ) where
  toFun X p := X.1 p.1.1 p.1.2
  invFun f := ⟨fun i j => if h : i ≤ j then f ⟨(i,j),h⟩ else f ⟨(j,i), le_of_not_ge h⟩, by
    ext i j
    by_cases h : i ≤ j
    · by_cases h' : j ≤ i
      · have he := le_antisymm h h'; subst j; simp
      · simp [h,h']
    · simp [h, le_of_not_ge h]⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    by_cases h : i ≤ j
    · simp [h]
    · simp only [h, dite_false]
      exact congrFun (congrFun X.2 i) j
  right_inv f := by funext p; simp [p.2]
  map_add' X Y := rfl
  map_smul' c X := rfl

/-- Real matrices embedded entrywise in the complex matrix algebra. -/
def realMatrixEmbedding : Matrix (Fin 5) (Fin 5) ℝ →ₗ[ℝ] Matrix (Fin 5) (Fin 5) ℂ where
  toFun E := E.map Complex.ofReal
  map_add' E F := by ext i j; simp
  map_smul' c E := by ext i j; simp [Matrix.smul_apply]

/-- The symmetric real effects as a real subspace of the actual complex algebra. -/
def symmetricEffectSpace : Submodule ℝ (Matrix (Fin 5) (Fin 5) ℂ) :=
  symmetricSpace.map realMatrixEmbedding

private theorem actual_effect_span_eq :
    Submodule.span ℝ (Set.range (fun p : (P : Protocol (Fin 5)) × Record P =>
      recordEffect walk p.1 p.2)) = symmetricEffectSpace := by
  rw [(actual_protocol_effect_correspondence walk walk_zero walk_add walk_unitary).1]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro E (rfl | ⟨⟨t,s⟩, rfl⟩)
    · exact Submodule.mem_map.mpr ⟨1, by simp [symmetricSpace], by
        ext i j; by_cases hij : i = j <;> simp [realMatrixEmbedding, Matrix.one_apply, hij]⟩
    · refine Submodule.mem_map.mpr ⟨conjugate generator (Matrix.single s s 1) t, ?_, ?_⟩
      · rw [← five_mode_nonnegative_wait_span]
        exact Submodule.subset_span ⟨(t,s),rfl⟩
      · exact (first_effect_real t s).symm
  · rintro E ⟨S,hS,rfl⟩
    rw [← five_mode_nonnegative_wait_span] at hS
    induction hS using Submodule.span_induction with
    | mem S hS =>
      obtain ⟨⟨t,s⟩,rfl⟩ := hS
      change (conjugate generator (Matrix.single s s 1) t).map Complex.ofReal ∈ _
      rw [← first_effect_real]
      exact Submodule.subset_span (Set.mem_insert_of_mem 1 ⟨(t,s),rfl⟩)
    | zero => exact (firstEffectSpan walk).zero_mem
    | add E F _ _ he hf => simpa only [map_add] using (firstEffectSpan walk).add_mem he hf
    | smul c E _ he => simpa only [map_smul] using (firstEffectSpan walk).smul_mem c he

private theorem finite_actual_effect_supplier :
    ∃ effects : Finset (Matrix (Fin 5) (Fin 5) ℂ),
      (↑effects : Set _) ⊆ Set.range (fun p : (P : Protocol (Fin 5)) × Record P =>
        recordEffect walk p.1 p.2) ∧
      Submodule.span ℝ (effects : Set _) = symmetricEffectSpace := by
  classical
  let S := Set.range (fun p : (P : Protocol (Fin 5)) × Record P =>
    recordEffect walk p.1 p.2)
  obtain ⟨t,ht⟩ := (Submodule.fg_iff_finiteDimensional (Submodule.span ℝ S)).mpr
    (inferInstance : FiniteDimensional ℝ (Submodule.span ℝ S))
  obtain ⟨T,hT,hspan⟩ := Submodule.subset_span_finite_of_subset_span
    (R := ℝ) (t := t) (s := S) (by rw [← ht]; exact Submodule.subset_span)
  refine ⟨T,hT, ?_⟩
  have he : Submodule.span ℝ (T : Set _) = Submodule.span ℝ S := by
    apply le_antisymm (Submodule.span_mono hT)
    rw [← ht]
    exact Submodule.span_le.mpr hspan
  exact he.trans actual_effect_span_eq

/-- Integrated finite-history event weights under an input-independent seed measure.
For probability measures and measurable event probabilities this is the actual event probability.
The equality below also holds for the total Bochner integrals against arbitrary measures. -/
def randomEventProbability {Seed : Type*} [MeasurableSpace Seed]
    (μ : MeasureTheory.Measure Seed) (strategy : Seed → Protocol (Fin 5))
    (event : ∀ c, Finset (Record (strategy c))) (X : Matrix (Fin 5) (Fin 5) ℂ) : ℝ :=
  ∫ c, ∑ h ∈ event c, ludersLaw menu (strategy c) X h ∂μ

/-- Full finite protocol response fibers equal entrywise real-part fibers.
The fifteen-dimensional effect span is an actual nonnegative-time supplier. -/
private theorem deterministic_response_fiber (X Y : Matrix (Fin 5) (Fin 5) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    ((∀ (P : Protocol (Fin 5)) (h : Record P), ludersLaw menu P X h = ludersLaw menu P Y h)
      ↔ realEntries X = realEntries Y) ∧ Module.finrank ℝ waitSpan = 15 := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro h
      apply waits_separate_real X Y hX hY
      intro t s
      have hc := (actual_protocol_effect_correspondence walk walk_zero walk_add walk_unitary).2.1
      have he : recordEffect walk (.wait t (.read fun _ => .stop)) ⟨s,PUnit.unit⟩ =
          firstEffect walk t s := by
        simp [recordEffect, firstEffect, projector, Matrix.single_mul_single_same]
      simpa only [menu, ← hc, he] using h (.wait t (.read fun _ => .stop)) ⟨s,PUnit.unit⟩
    · intro h P r
      have hc := actual_protocol_effect_correspondence walk walk_zero walk_add walk_unitary
      have hm : recordEffect walk P r ∈ firstEffectSpan walk := by
        rw [← hc.1]
        exact Submodule.subset_span ⟨⟨P,r⟩, rfl⟩
      have hp : ∀ E ∈ firstEffectSpan walk,
          (Matrix.trace (E * X)).re = (Matrix.trace (E * Y)).re := by
        intro E hE
        induction hE using Submodule.span_induction with
        | mem E hE =>
          obtain rfl | ⟨⟨t,s⟩, rfl⟩ := hE
          · simpa [Matrix.trace, realEntries] using congrArg Matrix.trace h
          · simp only [first_effect_real, real_trace_pairing, h]
        | zero => simp
        | add E F _ _ he hf => simp [Matrix.add_mul, Matrix.trace_add, he, hf]
        | smul c E _ he => simpa using congrArg (fun z : ℝ => c * z) he
      simpa only [menu, hc.2.1] using hp _ hm
  · rw [five_mode_nonnegative_wait_span, upperEquiv.finrank_eq]
    calc
      Module.finrank ℝ (Upper → ℝ) = Fintype.card Upper := Module.finrank_fintype_fun_eq_card ℝ
      _ = 15 := by decide

end RealWaitRealization

section OrthogonalReadout

open D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence
open D5.S3.Quantum.Algebra.FutureWordOrthogonalResidual

local instance matrixNormedAddCommGroup : NormedAddCommGroup (Matrix (Fin 5) (Fin 5) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one
local instance matrixInnerProductSpace : InnerProductSpace ℂ (Matrix (Fin 5) (Fin 5) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one
local instance matrixUniformSpace : UniformSpace (Matrix (Fin 5) (Fin 5) ℂ) :=
  matrixNormedAddCommGroup.toUniformSpace
local instance matrixTopologicalSpace : TopologicalSpace (Matrix (Fin 5) (Fin 5) ℂ) :=
  matrixUniformSpace.toTopologicalSpace
local instance (priority := 2000) (K : Submodule ℂ (Matrix (Fin 5) (Fin 5) ℂ)) :
    K.HasOrthogonalProjection := by
  letI : IsUniformAddGroup K := K.toAddSubgroup.isUniformAddGroup
  have hcomplete : CompleteSpace K := FiniteDimensional.complete ℂ K
  exact @Submodule.HasOrthogonalProjection.ofCompleteSpace ℂ
    (Matrix (Fin 5) (Fin 5) ℂ) _ matrixNormedAddCommGroup matrixInnerProductSpace K hcomplete

/-- A finite bounded family of actual history effects with the same full-menu fibers,
real span, invisible residual, and visible orthogonal projection. -/
def finiteOrthogonalReadout
    (response : Matrix (Fin 5) (Fin 5) ℂ → (P : Protocol (Fin 5)) → Record P → ℝ) : Prop :=
  ∃ (m : ℕ) (effects : Fin (m + 1) → Matrix (Fin 5) (Fin 5) ℂ),
    (∀ i, effects i ∈ Set.range (fun p : (P : Protocol (Fin 5)) × Record P =>
      recordEffect walk p.1 p.2)) ∧
    Submodule.span ℝ (Set.range effects) = symmetricEffectSpace ∧
    (∀ i, (effects i).PosSemidef ∧ (1 - effects i).PosSemidef) ∧
    ∀ rho sigma : Matrix (Fin 5) (Fin 5) ℂ,
      rho.PosSemidef ∧ Matrix.trace rho = 1 →
      sigma.PosSemidef ∧ Matrix.trace sigma = 1 →
      (response rho = response sigma ↔ finiteTraceReadout effects rho = finiteTraceReadout effects sigma) ∧
      (finiteTraceReadout effects rho = finiteTraceReadout effects sigma ↔
        centeredState rho - centeredState sigma ∈
          futureResidual (𝕜 := ℂ) (fun i => centeredEffect (effects i))) ∧
      (centeredState rho - centeredState sigma ∈
          futureResidual (𝕜 := ℂ) (fun i => centeredEffect (effects i)) ↔
        (visibleEffectSubspace (𝕜 := ℂ) (fun i => centeredEffect (effects i))).starProjection
            (centeredState rho) =
          (visibleEffectSubspace (𝕜 := ℂ) (fun i => centeredEffect (effects i))).starProjection
            (centeredState sigma))

private theorem actual_finite_orthogonal_readout :
    finiteOrthogonalReadout (fun X P h => ludersLaw menu P X h) := by
  classical
  obtain ⟨T,hT,hspan⟩ := finite_actual_effect_supplier
  let effects : Fin (T.card + 1) → Matrix (Fin 5) (Fin 5) ℂ :=
    Fin.cases 1 (fun i => (T.equivFin.symm i).val)
  have hactual (i) : effects i ∈ Set.range (fun p : (P : Protocol (Fin 5)) × Record P =>
      recordEffect walk p.1 p.2) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨⟨.stop,PUnit.unit⟩, rfl⟩
    · exact hT (T.equivFin.symm j).property
  have heffects : Submodule.span ℝ (Set.range effects) = symmetricEffectSpace := by
    apply le_antisymm
    · rw [← actual_effect_span_eq]
      exact Submodule.span_mono (by rintro E ⟨i,rfl⟩; exact hactual i)
    · rw [← hspan]
      apply Submodule.span_le.mpr
      intro E hE
      apply Submodule.subset_span
      refine ⟨(T.equivFin ⟨E,hE⟩).succ, ?_⟩
      simp [effects]
  have hbounds (i) : (effects i).PosSemidef ∧ (1 - effects i).PosSemidef := by
    obtain ⟨⟨P,h⟩,he⟩ := hactual i
    rw [← he]
    exact (actual_protocol_effect_correspondence walk walk_zero walk_add walk_unitary).2.2 P h
  refine ⟨T.card,effects,hactual,heffects,hbounds, ?_⟩
  intro rho sigma hrho hsigma
  have hcanonical := readout_fiber_orthogonal_equivalence effects rho sigma hrho hsigma hbounds
  refine ⟨?_,hcanonical.1.trans hcanonical.2.1,hcanonical.2.2⟩
  constructor
  · intro hresponse
    have hreal := (deterministic_response_fiber rho sigma hrho.1.isHermitian hsigma.1.isHermitian).1.mp
      (fun P h => congrFun (congrFun hresponse P) h)
    have hR := real_part_readout_obstruction (0 : Fin 5) 1 (by decide)
    have hs : symmetrize rho = symmetrize sigma := by
      ext i j
      rw [hR.2.2.1 rho hrho.1.isHermitian, hR.2.2.1 sigma hsigma.1.isHermitian]
      exact congrArg Complex.ofReal (congrFun (congrFun hreal i) j)
    funext i
    have hm : effects i ∈ symmetricEffectSpace := by
      rw [← heffects]
      exact Submodule.subset_span ⟨i,rfl⟩
    obtain ⟨E,hE,he⟩ := hm
    have ht : (effects i).transpose = effects i := by
      rw [← he]
      ext a b
      exact congrArg Complex.ofReal (congrFun (congrFun hE a) b)
    change Matrix.trace (rho * effects i) = Matrix.trace (sigma * effects i)
    rw [Matrix.trace_mul_comm rho, Matrix.trace_mul_comm sigma,
      ← hR.2.2.2.1 (effects i) rho ht, ← hR.2.2.2.1 (effects i) sigma ht, hs]
  · intro hreadout
    let pairing : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℝ] ℂ :=
      { toFun := fun E => Matrix.trace (E * (rho - sigma))
        map_add' := by intro E F; simp [Matrix.add_mul, Matrix.trace_add]
        map_smul' := by intro c E; simp }
    have hp : ∀ E ∈ Submodule.span ℝ (Set.range effects), pairing E = 0 := by
      intro E hE
      induction hE using Submodule.span_induction with
      | mem E hE =>
        obtain ⟨i,rfl⟩ := hE
        have hi := congrFun hreadout i
        change Matrix.trace (effects i * (rho - sigma)) = 0
        rw [Matrix.mul_sub, Matrix.trace_sub, sub_eq_zero,
          Matrix.trace_mul_comm (effects i) rho, Matrix.trace_mul_comm (effects i) sigma]
        exact hi
      | zero => simp
      | add E F _ _ hE hF => simp [map_add,hE,hF]
      | smul c E _ hE => simp [map_smul,hE]
    funext P h
    have hm : recordEffect walk P h ∈ Submodule.span ℝ (Set.range effects) := by
      rw [heffects, ← actual_effect_span_eq]
      exact Submodule.subset_span ⟨⟨P,h⟩,rfl⟩
    have he := hp _ hm
    have hprob := (actual_protocol_effect_correspondence walk walk_zero walk_add walk_unitary).2.1
    have heq : Matrix.trace (recordEffect walk P h * rho) =
        Matrix.trace (recordEffect walk P h * sigma) := by
      simpa [pairing, Matrix.mul_sub, Matrix.trace_sub, sub_eq_zero] using he
    simpa only [hprob, menu] using congrArg Complex.re heq

end OrthogonalReadout

/-- Full finite protocol response fibers equal real-part fibers and persist under arbitrary
input-independent random control and measurable recorded events. -/
theorem five_mode_real_response_fiber (X Y : Matrix (Fin 5) (Fin 5) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    ((∀ (P : Protocol (Fin 5)) (h : Record P), ludersLaw menu P X h = ludersLaw menu P Y h)
      ↔ realEntries X = realEntries Y) ∧ Module.finrank ℝ waitSpan = 15 ∧
    Submodule.span ℝ (Set.range (fun p : (P : Protocol (Fin 5)) × Record P =>
      recordEffect walk p.1 p.2)) = symmetricEffectSpace ∧
    (∃ effects : Finset (Matrix (Fin 5) (Fin 5) ℂ),
      (↑effects : Set _) ⊆ Set.range (fun p : (P : Protocol (Fin 5)) × Record P =>
        recordEffect walk p.1 p.2) ∧
      Submodule.span ℝ (effects : Set _) = symmetricEffectSpace) ∧
    (∀ (Seed : Type) [MeasurableSpace Seed] (μ : MeasureTheory.Measure Seed)
      (strategy : Seed → Protocol (Fin 5)) (event : ∀ c, Finset (Record (strategy c))),
      realEntries X = realEntries Y →
        randomEventProbability μ strategy event X = randomEventProbability μ strategy event Y) ∧
    (∀ Z : Matrix (Fin 5) (Fin 5) ℂ, Z.PosSemidef →
      ∀ (P : Protocol (Fin 5)) (h : Record P),
        ludersLaw menu P (symmetrize Z) h = ludersLaw menu P Z h) ∧
    ¬ MatrixMap.IsCompletelyPositive (symmetrize (n := Fin 5)) ∧
    finiteOrthogonalReadout (fun Z P h => ludersLaw menu P Z h) := by
  have hc := deterministic_response_fiber X Y hX hY
  have hR := real_part_readout_obstruction (0 : Fin 5) 1 (by decide)
  refine ⟨hc.1, hc.2, actual_effect_span_eq, finite_actual_effect_supplier,
    ?_, ?_, hR.2.2.2.2.2.2, actual_finite_orthogonal_readout⟩
  · intro Seed measurable μ strategy event h
    unfold randomEventProbability
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun c => Finset.sum_congr rfl fun r _ =>
      hc.1.mpr h (strategy c) r
  · intro Z hZ
    apply (deterministic_response_fiber (symmetrize Z) Z
      (hR.1 Z hZ).isHermitian hZ.isHermitian).1.mpr
    ext i j
    simp only [realEntries, Matrix.map_apply, hR.2.2.1 Z hZ.isHermitian,
      Complex.ofReal_re]

open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition

/-- The actual response coordinate map on the real Hermitian input space. -/
def realCoordinateMap : HermitianSpace 5 →ₗ[ℝ] symmetricSpace where
  toFun X := ⟨realEntries X.1, realEntries_symmetric X.1 X.2⟩
  map_add' X Y := by apply Subtype.ext; ext i j; simp [realEntries]
  map_smul' c X := by apply Subtype.ext; ext i j; simp [realEntries, Matrix.smul_apply]

/-- The ten linear blind directions; physical locality is asserted below only at full rank. -/
def blindDirections : Submodule ℝ (HermitianSpace 5) := LinearMap.ker realCoordinateMap

private theorem realCoordinateMap_surjective : Function.Surjective realCoordinateMap := by
  intro S
  let H : HermitianSpace 5 := ⟨S.1.map Complex.ofReal, by
    change (S.1.map Complex.ofReal).IsHermitian
    ext i j
    have he := congrArg Complex.ofReal (congrFun (congrFun S.2 i) j)
    simpa using he⟩
  refine ⟨H, ?_⟩
  apply Subtype.ext
  ext i j
  simp [realCoordinateMap, realEntries, H]

private theorem blind_real_zero (D : blindDirections) : realEntries D.1.1 = 0 := by
  exact congrArg Subtype.val ((LinearMap.mem_ker).mp D.2)

private theorem blind_trace_zero (D : blindDirections) : Matrix.trace D.1.1 = 0 := by
  have hd (i : Fin 5) : D.1.1 i i = 0 := by
    have hH : D.1.1.IsHermitian := D.1.2
    have he : star (D.1.1 i i) = D.1.1 i i := congrFun (congrFun hH i) i
    have hr : (D.1.1 i i).re = 0 := congrFun (congrFun (blind_real_zero D) i) i
    rw [← Complex.conj_eq_iff_re.mp he, hr]
    rfl
  simp [Matrix.trace, hd]

/-- Variable real response directions after fixing trace. -/
def normalizedVisibleDirections : Submodule ℝ symmetricSpace :=
  LinearMap.ker ((Matrix.traceLinearMap (Fin 5) ℝ ℝ).comp symmetricSpace.subtype)

private theorem symmetric_finrank : Module.finrank ℝ symmetricSpace = 15 := by
  rw [upperEquiv.finrank_eq]
  calc
    Module.finrank ℝ (Upper → ℝ) = Fintype.card Upper := Module.finrank_fintype_fun_eq_card ℝ
    _ = 15 := by decide

private theorem normalized_visible_finrank : Module.finrank ℝ normalizedVisibleDirections = 14 := by
  let tr : symmetricSpace →ₗ[ℝ] ℝ :=
    (Matrix.traceLinearMap (Fin 5) ℝ ℝ).comp symmetricSpace.subtype
  have hn : tr ≠ 0 := by
    intro h
    let e : symmetricSpace := ⟨Matrix.single 0 0 1, by simp [symmetricSpace]⟩
    have he := LinearMap.congr_fun h e
    norm_num [tr, e, Matrix.traceLinearMap] at he
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  rw [symmetric_finrank] at hd
  change Module.finrank ℝ (LinearMap.ker tr) = 14
  omega

private theorem blind_finrank : Module.finrank ℝ blindDirections = 10 := by
  have h := LinearMap.finrank_range_add_finrank_ker realCoordinateMap
  rw [LinearMap.range_eq_top.mpr realCoordinateMap_surjective, finrank_top,
    hermitian_space_finrank] at h
  rw [symmetric_finrank] at h
  change Module.finrank ℝ (LinearMap.ker realCoordinateMap) = 10
  omega

/-- A full-rank density has a relative neighborhood of physical states in all ten blind
directions. The neighborhood radius is obtained from a strictly positive spectral lower bound. -/
theorem full_rank_blind_fiber_neighborhood (rho : Matrix (Fin 5) (Fin 5) ℂ)
    (hpositive : rho.PosDef) (htrace : Matrix.trace rho = 1) :
    Module.finrank ℝ blindDirections = 10 ∧
    Module.finrank ℝ normalizedVisibleDirections = 14 ∧
    Module.finrank ℝ (traceZeroHermitian 5) = 24 ∧
    ∃ r : ℝ, 0 < r ∧ ∀ D : blindDirections,
      ‖CStarMatrix.ofMatrix D.1.1‖ < r →
      (rho + D.1.1).PosSemidef ∧ Matrix.trace (rho + D.1.1) = 1 ∧
      ∀ (P : Protocol (Fin 5)) (h : Record P),
        ludersLaw menu P rho h = ludersLaw menu P (rho + D.1.1) h := by
  refine ⟨blind_finrank, normalized_visible_finrank, by simpa using trace_zero_hermitian_finrank 5, ?_⟩
  let c : Matrix (Fin 5) (Fin 5) ℂ ≃⋆ₐ[ℂ] CStarMatrix (Fin 5) (Fin 5) ℂ :=
    CStarMatrix.ofMatrixStarAlgEquiv
  have hp : 0 ≤ c rho := map_nonneg c hpositive.posSemidef.nonneg
  have hu : IsUnit (c rho) := hpositive.isUnit.map c
  have hs := hu.isStrictlyPositive hp
  obtain ⟨r,hr,hlower⟩ := (CFC.exists_pos_algebraMap_le_iff (c rho) hs.isSelfAdjoint).2
    (fun x hx => hs.spectrum_pos hx)
  refine ⟨r,hr, ?_⟩
  intro D hD
  have hd : IsSelfAdjoint (c D.1.1) := congrArg CStarMatrix.ofMatrix D.1.2
  have hb := IsSelfAdjoint.neg_algebraMap_norm_le_self (a := c D.1.1) (ha := hd)
  have hsmall : ‖c D.1.1‖ < r := hD
  have hbase : (0 : CStarMatrix (Fin 5) (Fin 5) ℂ) ≤
      algebraMap ℝ _ r + -(algebraMap ℝ _ ‖c D.1.1‖) := by
    rw [← map_neg, ← map_add]
    exact algebraMap_nonneg (β := CStarMatrix (Fin 5) (Fin 5) ℂ) (by linarith : 0 ≤ r + -‖c D.1.1‖)
  have hsum : 0 ≤ c (rho + D.1.1) := by
    simpa only [map_add] using hbase.trans (add_le_add hlower hb)
  have hm : (rho + D.1.1).PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    simpa only [StarAlgEquiv.symm_apply_apply] using map_nonneg c.symm hsum
  refine ⟨hm, by rw [Matrix.trace_add, htrace, blind_trace_zero, add_zero], ?_⟩
  apply (five_mode_real_response_fiber rho (rho + D.1.1)
    hpositive.isHermitian hm.isHermitian).1.mpr
  ext i j
  have hz : (D.1.1 i j).re = 0 := congrFun (congrFun (blind_real_zero D) i) j
  simp [realEntries, hz]

/-- The unnormalized vector on the two rays e_N plus or minus i e_2. -/
def pairKet (sign : ℝ) : Fin 5 → ℂ :=
  ![1, (sign : ℂ) * Complex.I, 0, 0, 0]

/-- Normalized rank-one states on the two rays; the ket has squared norm two. -/
def pairState (sign : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  (2 : ℂ)⁻¹ • Matrix.vecMulVec (pairKet sign) (star (pairKet sign))

/-- The orthogonal pure-state pair has identical responses for the entire actual menu. -/
theorem orthogonal_pair_same_actual_responses :
    (pairState 1).PosSemidef ∧ Matrix.trace (pairState 1) = 1 ∧
    (pairState (-1)).PosSemidef ∧ Matrix.trace (pairState (-1)) = 1 ∧
    pairState 1 * pairState (-1) = 0 ∧ pairState 1 ≠ pairState (-1) ∧
    (∀ (P : Protocol (Fin 5)) (h : Record P),
      ludersLaw menu P (pairState 1) h = ludersLaw menu P (pairState (-1)) h) := by
  have hpos (s : ℝ) : (pairState s).PosSemidef :=
    (Matrix.posSemidef_vecMulVec_self_star (pairKet s)).smul
      (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩)
  refine ⟨hpos 1, ?_, hpos (-1), ?_, ?_, ?_, ?_⟩
  · norm_num [pairState, pairKet, Matrix.trace, Matrix.vecMulVec,
      Pi.single_apply, Fin.sum_univ_succ, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  · norm_num [pairState, pairKet, Matrix.trace, Matrix.vecMulVec,
      Pi.single_apply, Fin.sum_univ_succ, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pairState, pairKet, Matrix.mul_apply, Matrix.vecMulVec,
        Pi.single_apply, Fin.sum_univ_succ, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] <;> ring_nf <;>
      norm_num [Complex.I_mul_I]
  · intro h
    have he := congrArg (fun X => (X 0 1).im) h
    norm_num [pairState, pairKet, Matrix.vecMulVec, Pi.single_apply] at he
  · apply (five_mode_real_response_fiber _ _ (hpos 1).isHermitian (hpos (-1)).isHermitian).1.mpr
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [realEntries, pairState, pairKet, Matrix.vecMulVec, Pi.single_apply]

end D5.S3.Quantum.Fibers.FiveModeRealResponse
