/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/UniformRankNormalization
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/UniformRankNormalization
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The trace-augmented raw readout and the derivative rank of the adjacent marginal. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCompactReadout
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteTraceBase
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The trace-augmented raw readout and the derivative rank of the adjacent marginal. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.UniformRankNormalization

open Function Filter Matrix
open scoped BigOperators Matrix Matrix.Norms.Elementwise ComplexConjugate Topology
open PeriodicMPSCompactReadout (Readout readout normalizedExchangeMarginals
  normalizedMarginal_mem eq_of_readout_of_trace_eq)
open PeriodicMPSUniformHardCoreLocalization (twoSiteObservation twoSiteObservation_projector
  twoSiteObservation_traceWord)
open PeriodicMPSUniformHardCoreMarginalWitness (Amplitudes pairGram mass_eq_trace)
open PeriodicMPSProjectiveCoordinates (projector mass mass_pos)
open SevenSiteTraceBase (wordPolynomial wordPolynomial_eq_trace differentiable_eval_polynomial)
open private form map_form from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteTraceBase
open UniformMPSExpectedDimensionRefutation (traceWord)
open TwoQubitMarginalReflection (Density Bits ExchangeSymmetric)

noncomputable section

/-- The second trace, the two determinants, and the mixed trace at first trace one. -/
abbrev Ordinary := ℂ × ℂ × ℂ × ℂ

/-- The ordinary amplitude with `m` sites traced out by the adjacent marginal. -/
def ordinaryAmplitude (m : ℕ) (p : Ordinary) : Amplitudes m :=
  fun w => wordPolynomial 1 p.1 p.2.1 p.2.2.1 p.2.2.2 (List.ofFn w)

private theorem differentiable_ordinaryAmplitude (m : ℕ) :
    Differentiable ℝ (ordinaryAmplitude m) := by
  apply differentiable_pi.mpr
  intro w
  let b : Fin 5 → Ordinary → ℂ :=
    ![(fun _ => 1), Prod.fst, (fun p => p.2.1), (fun p => p.2.2.1), (fun p => p.2.2.2)]
  have hb (i : Fin 5) : Differentiable ℝ (b i) := by
    fin_cases i
    · exact differentiable_const (1 : ℂ)
    · change Differentiable ℝ (fun p : Ordinary => p.1)
      fun_prop
    · change Differentiable ℝ (fun p : Ordinary => p.2.1)
      fun_prop
    · change Differentiable ℝ (fun p : Ordinary => p.2.2.1)
      fun_prop
    · change Differentiable ℝ (fun p : Ordinary => p.2.2.2)
      fun_prop
  let X : Fin 5 → MvPolynomial (Fin 5) ℂ := MvPolynomial.X
  let P := wordPolynomial (X 0) (X 1) (X 2) (X 3) (X 4) (List.ofFn w)
  have h (p : Ordinary) : MvPolynomial.eval (fun i => b i p) P = ordinaryAmplitude m p w := by
    let e := MvPolynomial.eval (fun i => b i p)
    change e P = _
    have hX (i : Fin 5) : e (X i) = b i p := MvPolynomial.eval_X (f := fun j => b j p) i
    have he : e P = wordPolynomial (e (X 0)) (e (X 1)) (e (X 2)) (e (X 3)) (e (X 4))
        (List.ofFn w) := by
      unfold P wordPolynomial
      rw [map_form e]
      rcases form (X 0) (X 1) (X 2) (X 3) (X 4) (List.ofFn w) with ⟨u, a, b', c⟩
      simp [map_ofNat]
    rw [he, hX 0, hX 1, hX 2, hX 3, hX 4]; rfl
  simpa only [h] using differentiable_eval_polynomial (𝕜 := ℝ) P b hb

private theorem exists_core_ordinary (m : ℕ) (p : Ordinary) :
    ∃ A : Fin 2 → PeriodicMPSParentIntersection.Bond,
      ordinaryAmplitude m p = traceWord 2 2 (2 + m) A := by
  obtain ⟨A, ht, hs, hd, he, hk⟩ :=
    PeriodicMPSFiveSiteCoordinates.exists_trace_coordinates 1 p.1 p.2.1 p.2.2.1 p.2.2.2
  refine ⟨A, funext fun w => ?_⟩
  simpa only [ordinaryAmplitude, ht, hs, hd, he, hk, SevenSiteTraceBase.wordProduct,
    traceWord] using wordPolynomial_eq_trace A w

def ordinaryRaw (m : ℕ) (p : Ordinary) : Density := pairGram (ordinaryAmplitude m p)

def ordinaryMass (m : ℕ) (p : Ordinary) : ℝ := (ordinaryRaw m p).trace.re

/-- The trace row followed by the nine independent Pauli readings. -/
def rawReadout (m : ℕ) (p : Ordinary) : ℝ × Readout :=
  (ordinaryMass m p, readout (ordinaryRaw m p))

/-- The actual adjacent marginal of the projectivized ordinary amplitude. -/
def ordinaryMarginal (m : ℕ) (p : Ordinary) : Density :=
  twoSiteObservation m (projector (ordinaryAmplitude m p))

private theorem projectiveMass_eq_ordinaryMass (m : ℕ) (p : Ordinary) :
    mass (ordinaryAmplitude m p) = ordinaryMass m p := by
  unfold ordinaryMass ordinaryRaw
  exact mass_eq_trace (m := m) (ordinaryAmplitude m p)

private theorem ordinaryMass_pos (m : ℕ) (p : Ordinary) (hp : ordinaryAmplitude m p ≠ 0) :
    0 < ordinaryMass m p := by
  rw [← projectiveMass_eq_ordinaryMass]
  exact mass_pos _ hp

private theorem ordinaryMarginal_eq_normalizedRaw (m : ℕ) (p : Ordinary) :
    ordinaryMarginal m p = (ordinaryMass m p)⁻¹ • ordinaryRaw m p := by
  rw [ordinaryMarginal, twoSiteObservation_projector (m := m),
    projectiveMass_eq_ordinaryMass, ordinaryRaw]

private theorem ordinaryMarginal_mem (m : ℕ) (p : Ordinary) (hp : ordinaryAmplitude m p ≠ 0) :
    ordinaryMarginal m p ∈ normalizedExchangeMarginals := by
  obtain ⟨A, hA⟩ := exists_core_ordinary m p
  rw [hA] at hp
  simpa only [ordinaryMarginal, hA, twoSiteObservation_traceWord] using normalizedMarginal_mem A hp

private theorem differentiable_ordinaryRaw (m : ℕ) : Differentiable ℝ (ordinaryRaw m) := by
  have hA := differentiable_ordinaryAmplitude m
  change Differentiable ℝ (fun p => pairGram (ordinaryAmplitude m p))
  apply differentiable_pi.mpr
  intro i
  apply differentiable_pi.mpr
  intro j
  unfold pairGram
  simp only [Complex.star_def, ← Complex.conjCLE_apply]
  fun_prop

private theorem differentiable_ordinaryMass (m : ℕ) : Differentiable ℝ (ordinaryMass m) := by
  have hR := differentiable_ordinaryRaw m
  unfold ordinaryMass Matrix.trace Matrix.diag
  change Differentiable ℝ (fun p => Complex.reCLM (∑ i, ordinaryRaw m p i i))
  fun_prop

private theorem differentiableAt_ordinaryMarginal (m : ℕ) (p : Ordinary)
    (hp : ordinaryAmplitude m p ≠ 0) : DifferentiableAt ℝ (ordinaryMarginal m) p := by
  rw [funext (ordinaryMarginal_eq_normalizedRaw m)]
  exact ((differentiable_ordinaryMass m p).inv (ordinaryMass_pos m p hp).ne').smul
    (differentiable_ordinaryRaw m p)

/-- The trace coordinate splits the augmented raw range into the normalized
derivative range and the line through the raw value. -/
private theorem finrank_augmented_normalization {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : E → ℝ) (v : E → Readout) (x : E)
    (hn : DifferentiableAt ℝ n x) (hv : DifferentiableAt ℝ v x) (hx : n x ≠ 0) :
    Module.finrank ℝ ↑(LinearMap.range (fderiv ℝ (fun y => (n y, v y)) x).toLinearMap ⊔
      Submodule.span ℝ {(n x, v x)} : Submodule ℝ (ℝ × Readout)) =
      Module.finrank ℝ (LinearMap.range (fderiv ℝ (fun y => (n y)⁻¹ • v y) x).toLinearMap :
        Submodule ℝ Readout) + 1 := by
  let g : E → Readout := fun y => (n y)⁻¹ • v y
  let dg : E →ₗ[ℝ] Readout := (fderiv ℝ g x).toLinearMap
  let draw : E →ₗ[ℝ] ℝ × Readout := (fderiv ℝ (fun y => (n y, v y)) x).toLinearMap
  let embed : Readout →ₗ[ℝ] ℝ × Readout := LinearMap.inr ℝ ℝ Readout
  let D : E →ₗ[ℝ] ℝ × Readout := embed.comp dg
  let z : ℝ × Readout := (n x, v x)
  let L : Submodule ℝ (ℝ × Readout) := Submodule.span ℝ {z}
  change Module.finrank ℝ ↑(LinearMap.range draw ⊔ L : Submodule ℝ (ℝ × Readout)) =
    Module.finrank ℝ (LinearMap.range dg) + 1
  have hg : DifferentiableAt ℝ g x := (hn.inv hx).smul hv
  have hval : (fun y => n y • g y) =ᶠ[𝓝 x] v :=
    (hn.continuousAt.eventually_ne hx).mono fun y hy => by
      simp only [g, smul_smul, mul_inv_cancel₀ hy, one_smul]
  have hderiv := hval.fderiv_eq (𝕜 := ℝ)
  -- Differentiate the product identity for the quotient on the nonzero-trace neighborhood.
  have hprod (a : E) : n x • dg a + fderiv ℝ n x a • g x = fderiv ℝ v x a := by
    rw [← hderiv, fderiv_fun_smul hn hg]; rfl
  have hraw := (hn.hasFDerivAt.prodMk hv.hasFDerivAt).fderiv
  have hsplit (a : E) : draw a = n x • D a + (fderiv ℝ n x a / n x) • z := by
    apply Prod.ext
    · change (fderiv ℝ (fun y => (n y, v y)) x a).1 = _
      rw [hraw]
      change fderiv ℝ n x a = n x * 0 + (fderiv ℝ n x a / n x) * n x
      rw [mul_zero, zero_add, div_mul_cancel₀ _ hx]
    · change (fderiv ℝ (fun y => (n y, v y)) x a).2 = n x • dg a + _
      rw [hraw]
      change fderiv ℝ v x a = n x • dg a + (fderiv ℝ n x a / n x) • v x
      simpa only [g, smul_smul, div_eq_mul_inv] using (hprod a).symm
  have hz : z ∈ L := Submodule.mem_span_singleton_self z
  have hspan : LinearMap.range draw ⊔ L = LinearMap.range D ⊔ L := by
    apply le_antisymm
    · refine sup_le ?_ le_sup_right
      rintro _ ⟨a, rfl⟩
      rw [hsplit]
      exact Submodule.add_mem_sup
        ((LinearMap.range D).smul_mem _ (D.mem_range_self a)) (L.smul_mem _ hz)
    · refine sup_le ?_ le_sup_right
      rintro _ ⟨a, rfl⟩
      have ha : draw a - (fderiv ℝ n x a / n x) • z ∈ LinearMap.range draw ⊔ L :=
        Submodule.sub_mem_sup (draw.mem_range_self a) (L.smul_mem _ hz)
      rw [hsplit, add_sub_cancel_right] at ha
      simpa only [smul_smul, inv_mul_cancel₀ hx, one_smul] using
        (LinearMap.range draw ⊔ L).smul_mem (n x)⁻¹ ha
  have hdis : Disjoint (LinearMap.range D) L := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨a, rfl⟩ ha
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
    have hzero : c * n x = 0 := congrArg Prod.fst hc
    rw [(mul_eq_zero.mp hzero).resolve_right hx, zero_smul] at hc
    exact hc.symm
  have hz_ne : z ≠ 0 := fun h => hx (congrArg Prod.fst h)
  have hline : Module.finrank ℝ L = 1 := finrank_span_singleton hz_ne
  have hrank : Module.finrank ℝ (LinearMap.range D) = Module.finrank ℝ (LinearMap.range dg) := by
    change Module.finrank ℝ (LinearMap.range (embed.comp dg)) = _
    rw [LinearMap.range_comp]
    have hinj : Function.Injective embed := LinearMap.inr_injective
    exact (Submodule.equivMapOfInjective embed hinj (LinearMap.range dg)).finrank_eq.symm
  rw [hspan]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range D) L
  have hzero : Module.finrank ℝ ↥(LinearMap.range D ⊓ L) = 0 := by
    rw [hdis.eq_bot, finrank_bot]
  rwa [hzero, add_zero, hrank, hline] at hdim

private theorem fderiv_constraint {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {m : ℕ} {p : Ordinary} (hp : ordinaryAmplitude m p ≠ 0)
    (L : Density →L[ℝ] Y) (c : Y) (h : ∀ M ∈ normalizedExchangeMarginals, L M = c)
    (u : Ordinary) : L (fderiv ℝ (ordinaryMarginal m) p u) = 0 := by
  have he : L ∘ ordinaryMarginal m =ᶠ[𝓝 p] (fun _ => c) :=
    ((differentiable_ordinaryAmplitude m).continuous.continuousAt.eventually_ne hp).mono
      fun q hq => h _ (ordinaryMarginal_mem m q hq)
  have hd : fderiv ℝ (L ∘ ordinaryMarginal m) p = L.comp (fderiv ℝ (ordinaryMarginal m) p) :=
    (L.hasFDerivAt.comp p (differentiableAt_ordinaryMarginal m p hp).hasFDerivAt).fderiv
  rw [he.fderiv_eq, fderiv_const_apply] at hd
  simpa only [ContinuousLinearMap.comp_apply, _root_.zero_apply] using
    (congrArg (fun T : Ordinary →L[ℝ] Y => T u) hd).symm

private theorem finrank_normalizedReadout (m : ℕ) (p : Ordinary)
    (hp : ordinaryAmplitude m p ≠ 0) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ (readout ∘ ordinaryMarginal m) p).toLinearMap :
      Submodule ℝ Readout) =
      Module.finrank ℝ (LinearMap.range (fderiv ℝ (ordinaryMarginal m) p).toLinearMap :
        Submodule ℝ Density) := by
  let D := fderiv ℝ (ordinaryMarginal m) p
  let entry (i j : Bits) : Density →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.proj i : Density →L[ℝ] (Bits → ℂ))
  have hD : fderiv ℝ (readout ∘ ordinaryMarginal m) p = readout.comp D :=
    (readout.hasFDerivAt.comp p (differentiableAt_ordinaryMarginal m p hp).hasFDerivAt).fderiv
  have hker : LinearMap.ker (readout.comp D).toLinearMap = LinearMap.ker D.toLinearMap := by
    ext u
    change readout (D u) = 0 ↔ D u = 0
    refine ⟨fun hu => ?_, fun h => by rw [h, map_zero]⟩
    have hHerm : (D u).IsHermitian := by
      change (D u)ᴴ = D u
      ext i j
      let L := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (entry j i) - entry i j
      have he := fderiv_constraint hp L 0
        (fun M hM => sub_eq_zero.mpr (congrArg (fun N : Density => N i j) hM.1.eq)) u
      exact sub_eq_zero.mp he
    have hSwap : ExchangeSymmetric (D u) := by
      intro i j
      let L := entry i.swap j.swap - entry i j
      exact sub_eq_zero.mp (fderiv_constraint hp L 0
        (fun M hM => sub_eq_zero.mpr (hM.2.1 i j)) u)
    let T : Density →L[ℝ] ℂ := ∑ i : Bits, entry i i
    have hT (M : Density) : T M = M.trace := by
      simp only [T, Matrix.trace, Matrix.diag, _root_.sum_apply]
      exact Finset.sum_congr rfl fun _ _ => rfl
    have htrace : (D u).trace = 0 := by
      simpa only [D, hT] using fderiv_constraint hp T 1
        (fun M hM => (hT M).trans hM.2.2) u
    exact eq_of_readout_of_trace_eq hHerm (by simp) hSwap (by intro i j; simp)
      (by simp [htrace]) (by simpa using hu)
  rw [hD]
  have hReadout := (readout.comp D).toLinearMap.finrank_range_add_finrank_ker
  have hMarginal := D.toLinearMap.finrank_range_add_finrank_ker
  rw [hker, ← hMarginal] at hReadout
  exact Nat.add_right_cancel hReadout

/-- The raw trace and Pauli derivative columns, together with the raw value,
have rank one more than the derivative of the actual normalized marginal.
The Pauli derivative of that marginal has the same rank. -/
theorem finrank_rawReadout_span (m : ℕ) (p : Ordinary) (hp : ordinaryAmplitude m p ≠ 0) :
    Module.finrank ℝ ↑(LinearMap.range (fderiv ℝ (rawReadout m) p).toLinearMap ⊔
      Submodule.span ℝ {rawReadout m p} : Submodule ℝ (ℝ × Readout)) =
      Module.finrank ℝ (LinearMap.range (fderiv ℝ (ordinaryMarginal m) p).toLinearMap :
        Submodule ℝ Density) + 1 ∧
    Module.finrank ℝ (LinearMap.range (fderiv ℝ (readout ∘ ordinaryMarginal m) p).toLinearMap :
      Submodule ℝ Readout) =
      Module.finrank ℝ (LinearMap.range (fderiv ℝ (ordinaryMarginal m) p).toLinearMap :
        Submodule ℝ Density) := by
  have hvalue : readout ∘ ordinaryMarginal m =
      fun q => (ordinaryMass m q)⁻¹ • (readout ∘ ordinaryRaw m) q := by
    funext q
    exact (congrArg readout (ordinaryMarginal_eq_normalizedRaw m q)).trans (map_smul readout _ _)
  have hrank := finrank_augmented_normalization (ordinaryMass m) (readout ∘ ordinaryRaw m) p
    (differentiable_ordinaryMass m p) (readout.differentiable.comp (differentiable_ordinaryRaw m) p)
    (ordinaryMass_pos m p hp).ne'
  have hreads := finrank_normalizedReadout m p hp
  refine ⟨?_, hreads⟩
  rw [← hreads, hvalue]
  exact hrank

#print axioms finrank_rawReadout_span

end

end D5.S3.Quantum.TensorNetworks.UniformRankNormalization
