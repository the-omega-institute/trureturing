/- GID: D5/S3/Quantum/Analysis/LinearGroups/ExponentialChart
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/LinearGroups/ExponentialChart
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exponential chart of a locally compact group injecting into a real unit group. -/

import D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Connected.Basic

/-!
# Exponential chart of a locally compact group in a finite-dimensional algebra

Let `A` be a finite-dimensional real normed algebra, `G` a locally compact topological group
and `ρ : G →* Aˣ` a continuous injective homomorphism, and let `L` be the Lie subalgebra of
one-parameter generators of `A` (`generatorSubalgebra`). For `X ∈ L` let `ε X` be the value at
time `1` of the continuous lift of `t ↦ exp (t • X)`; injectivity of `ρ` makes it the unique
element with `ρ (ε X) = exp X`.

* Path lemma: a compact neighbourhood `V` of `1` has a boundary whose image under `ρ` is
  compact and misses `1`, so a path in `G` from `1` whose image under `ρ` stays close to `1`
  never leaves `V`.
* Continuity of `ε` on all of `L`: near `X₁` the path `t ↦ ε (t • X₁)⁻¹ * ε (t • X)` on
  `[0, 1]` has image under `ρ` uniformly close to `1`, hence ends in any compact
  neighbourhood of `1`.
* Neighbourhoods (the main step): with a complement `C` of `L`, the map
  `(Y, B) ↦ exp Y * exp B` on `L × C` has derivative the sum map at `0`, so by the inverse
  function theorem every element of `A` near `1` is `exp Y * exp B` with `Y ∈ L`, `B ∈ C`
  small; if elements outside `ε '' V` accumulated at `1`, their `C`-coordinates `B` would be
  nonzero and, by the escape lemma, their directions would accumulate at a generator of norm
  one lying in `C`, which is impossible since `L ⊓ C = ⊥`.
* Open embedding: let `S` be a domain near `0` on which `exp` has a continuous local inverse
  `log`, and `W` the interior of `ε '' (L ∩ S)`, an open neighbourhood of `1` by the previous
  step. On `U = L ∩ S ∩ ε⁻¹ W` the map `ε` is injective, and for `O ⊆ U` open in `L` the image
  `ε '' O` is the set of `g ∈ W` with `log (ρ g) ∈ O`, which is open.

The main result is `exists_exp_chart`.
-/

namespace D5.S3.Quantum.Analysis.LinearGroups.ExponentialChart

open Filter Set
open scoped Topology
open D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators

variable {A : Type*} [NormedRing A] {G : Type*} [TopologicalSpace G] [Group G]

section Paths

/-- A compact set of `G` not containing `1` is mapped by `ρ` away from a neighbourhood of `1`. -/
private theorem exists_nhds_one_forall_notMem {ρ : G →* Aˣ} (hc : Continuous ρ)
    (hi : Function.Injective ρ) {K : Set G} (hK : IsCompact K) (h1 : (1 : G) ∉ K) :
    ∃ O ∈ 𝓝 (1 : A), ∀ g ∈ K, ((ρ g : Aˣ) : A) ∉ O := by
  have hcomp : IsCompact ((fun g => ((ρ g : Aˣ) : A)) '' K) :=
    hK.image (Units.continuous_val.comp hc)
  refine ⟨_, hcomp.isClosed.isOpen_compl.mem_nhds ?_, fun g hg hO => hO (mem_image_of_mem _ hg)⟩
  rintro ⟨g, hg, hg1⟩
  have : g = 1 := hi (Units.ext (hg1.trans (by rw [map_one, Units.val_one])))
  exact h1 (this ▸ hg)

/-- The path lemma: for a compact neighbourhood `V` of `1` there is a neighbourhood `O` of `1`
in `A` such that a path in `G` starting at `1` whose image under `ρ` stays in `O` stays in
`V`: it cannot cross the boundary of `V`, whose image under `ρ` is compact and misses `1`. -/
private theorem exists_nhds_one_path_mem [T2Space G] {ρ : G →* Aˣ} (hc : Continuous ρ)
    (hi : Function.Injective ρ) {V : Set G} (hV : IsCompact V) (hV1 : V ∈ 𝓝 (1 : G)) :
    ∃ O ∈ 𝓝 (1 : A), ∀ γ : ℝ → G, ContinuousOn γ (Icc 0 1) → γ 0 = 1 →
      (∀ t ∈ Icc (0 : ℝ) 1, ((ρ (γ t) : Aˣ) : A) ∈ O) → γ 1 ∈ V := by
  have h1 : (1 : G) ∈ interior V := mem_interior_iff_mem_nhds.2 hV1
  obtain ⟨O, hO, hKO⟩ := exists_nhds_one_forall_notMem hc hi (hV.diff isOpen_interior)
    (fun h => h.2 h1)
  refine ⟨O, hO, fun γ hγ hγ0 hγO => ?_⟩
  have hsub : γ '' Icc 0 1 ⊆ interior V := by
    refine (isPreconnected_Icc.image γ hγ).subset_left_of_subset_union isOpen_interior
      hV.isClosed.isOpen_compl (disjoint_compl_right.mono_left interior_subset) ?_
      ⟨1, ⟨0, left_mem_Icc.2 zero_le_one, hγ0⟩, h1⟩
    rintro _ ⟨t, ht, rfl⟩
    by_cases htV : γ t ∈ V
    · exact Or.inl (by_contra fun hint => hKO _ ⟨htV, hint⟩ (hγO t ht))
    · exact Or.inr htV
  exact interior_subset (hsub ⟨1, right_mem_Icc.2 zero_le_one, rfl⟩)

variable [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Continuity of the time-one value of a family of lifts: if `γ X` is a continuous lift of
`t ↦ exp (t • v X)` for every `X`, with `v` continuous, then `X ↦ γ X 1` is continuous. Near
`X₁` the path `t ↦ (γ X₁ t)⁻¹ * γ X t`, `t ∈ [0, 1]`, starts at `1` and its image under `ρ`
stays uniformly close to `1`, so by the path lemma it ends in any given compact
neighbourhood of `1`. -/
private theorem continuous_lift_one [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    {ρ : G →* Aˣ} (hc : Continuous ρ) (hi : Function.Injective ρ) {S : Type*} [TopologicalSpace S]
    {v : S → A} (hv : Continuous v) (γ : S → ℝ → G) (hγc : ∀ X, Continuous (γ X))
    (hγ : ∀ X t, ((ρ (γ X t) : Aˣ) : A) = NormedSpace.exp (t • v X)) :
    Continuous fun X => γ X 1 := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hγ0 : ∀ X, γ X 0 = 1 := fun X => hi (Units.ext (by
    rw [hγ, zero_smul, NormedSpace.exp_zero, map_one, Units.val_one]))
  refine continuous_iff_continuousAt.2 fun X₁ => ?_
  have key : Tendsto (fun X => (γ X₁ 1)⁻¹ * γ X 1) (𝓝 X₁) (𝓝 1) := by
    intro N hN
    rw [mem_map]
    obtain ⟨V, hV1, hVN, hV⟩ := local_compact_nhds hN
    obtain ⟨O, hO, hpath⟩ := exists_nhds_one_path_mem hc hi hV hV1
    have hF : Continuous fun p : A × ℝ =>
        NormedSpace.exp (-(p.2 • v X₁)) * NormedSpace.exp (p.2 • p.1) :=
      (NormedSpace.exp_continuous.comp (continuous_snd.smul continuous_const).neg).mul
        (NormedSpace.exp_continuous.comp (continuous_snd.smul continuous_fst))
    have htube : ∀ᶠ Y in 𝓝 (v X₁), ∀ t ∈ Icc (0 : ℝ) 1,
        NormedSpace.exp (-(t • v X₁)) * NormedSpace.exp (t • Y) ∈ O := by
      refine isCompact_Icc.eventually_forall_of_forall_eventually fun t _ => ?_
      refine hF.continuousAt.preimage_mem_nhds ?_
      rw [← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left, neg_add_cancel,
        NormedSpace.exp_zero]
      exact hO
    filter_upwards [(hv.tendsto X₁).eventually htube] with X hX
    refine hVN (hpath (fun t => (γ X₁ t)⁻¹ * γ X t) ((hγc X₁).inv.mul (hγc X)).continuousOn
      (by rw [hγ0, hγ0, inv_one, one_mul]) fun t ht => ?_)
    show ((ρ ((γ X₁ t)⁻¹ * γ X t) : Aˣ) : A) ∈ O
    rw [map_mul, map_inv, Units.val_mul, ← Ring.inverse_unit, hγ, Ring.inverse_exp, hγ]
    exact hX t ht
  have h := (tendsto_const_nhds (x := γ X₁ 1)).mul key
  rw [mul_one] at h
  exact h.congr fun X => mul_inv_cancel_left _ _

omit [CompleteSpace A] in
/-- Coordinates of the second kind: if `A = L ⊕ C`, every `a` near `1` factors as
`exp Y * exp B` with `Y ∈ L` and `B ∈ C`, where `Y` and `B` tend to `0` as `a` tends to `1`.
The map `Z ↦ exp (p_L Z) * exp (p_C Z)` has derivative `p_L + p_C = id` at `0`, so it has a
local inverse at `1` by the inverse function theorem. -/
private theorem exists_exp_mul_exp_eq [FiniteDimensional ℝ A] {L C : Submodule ℝ A}
    (h : IsCompl L C) :
    ∃ Y B : A → A, Tendsto Y (𝓝 1) (𝓝 0) ∧ Tendsto B (𝓝 1) (𝓝 0) ∧ (∀ a, Y a ∈ L) ∧
      (∀ a, B a ∈ C) ∧
      ∀ᶠ a in 𝓝 (1 : A), NormedSpace.exp (Y a) * NormedSpace.exp (B a) = a := by
  obtain ⟨pL, hpL⟩ : ∃ pL : A →L[ℝ] A, ∀ Z, pL Z = L.projection C h Z :=
    ⟨LinearMap.toContinuousLinearMap _, fun _ => rfl⟩
  obtain ⟨pC, hpC⟩ : ∃ pC : A →L[ℝ] A, ∀ Z, pC Z = C.projection L h.symm Z :=
    ⟨LinearMap.toContinuousLinearMap _, fun _ => rfl⟩
  have hsum : ∀ Z, pL Z + pC Z = Z := fun Z => by
    rw [hpL, hpC]
    exact Submodule.projection_add_projection_eq_self h Z
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : A → A,
      Ψ = fun Z => NormedSpace.exp (pL Z) * NormedSpace.exp (pC Z) := ⟨_, rfl⟩
  have hexp : ∀ p : A →L[ℝ] A, HasStrictFDerivAt (fun Z => NormedSpace.exp (p Z)) p 0 := by
    intro p
    have h0 : HasStrictFDerivAt NormedSpace.exp (1 : A →L[ℝ] A) (p 0) := by
      rw [map_zero]
      exact hasStrictFDerivAt_exp_zero
    convert h0.comp (0 : A) p.hasStrictFDerivAt using 1
    ext Z
    simp
  have hΨ :
      HasStrictFDerivAt Ψ ((ContinuousLinearEquiv.refl ℝ A : A ≃L[ℝ] A) : A →L[ℝ] A) 0 := by
    rw [hΨdef]
    convert (hexp pL).fun_mul' (hexp pC) using 1
    ext Z
    simp [add_comm (pC Z), hsum]
  have hΨ0 : Ψ 0 = 1 := by simp [hΨdef]
  set Φ := hΨ.localInverse Ψ _ 0
  have hΦ : Tendsto Φ (𝓝 1) (𝓝 0) := by
    have := hΨ.localInverse_continuousAt.tendsto
    rwa [hΨ.localInverse_apply_image, hΨ0] at this
  refine ⟨fun a => pL (Φ a), fun a => pC (Φ a), ?_, ?_, fun a => ?_, fun a => ?_, ?_⟩
  · have h' := (pL.continuous.tendsto 0).comp hΦ
    rw [map_zero] at h'
    exact h'
  · have h' := (pC.continuous.tendsto 0).comp hΦ
    rw [map_zero] at h'
    exact h'
  · show pL (Φ a) ∈ L
    rw [hpL]
    exact Submodule.projection_apply_mem h _
  · show pC (Φ a) ∈ C
    rw [hpC]
    exact Submodule.projection_apply_mem h.symm _
  · have hΨa : ∀ Z, Ψ Z = NormedSpace.exp (pL Z) * NormedSpace.exp (pC Z) := fun Z => by
      rw [hΨdef]
    have h' := hΨ.eventually_right_inverse
    rw [hΨ0] at h'
    filter_upwards [h'] with a ha
    exact (hΨa _).symm.trans ha

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
/-- The neighbourhood filter of `1` in a locally compact `G` is countably generated: on a
compact neighbourhood `V₀` of `1` it is the trace of the preimage under `ρ` of the
neighbourhood filter of `1` in `A`. -/
private theorem isCountablyGenerated_nhds_one [LocallyCompactSpace G] {ρ : G →* Aˣ}
    (hc : Continuous ρ) (hi : Function.Injective ρ) : (𝓝 (1 : G)).IsCountablyGenerated := by
  obtain ⟨V₀, hV₀, hV₀1⟩ := exists_compact_mem_nhds (1 : G)
  have heq : 𝓝 (1 : G) = comap (fun g => ((ρ g : Aˣ) : A)) (𝓝 1) ⊓ 𝓟 V₀ := by
    refine le_antisymm (le_inf ?_ (le_principal_iff.2 hV₀1)) fun N hN => ?_
    · have hρc : Continuous fun g : G => ((ρ g : Aˣ) : A) := Units.continuous_val.comp hc
      have h1 : Tendsto (fun g : G => ((ρ g : Aˣ) : A)) (𝓝 1) (𝓝 1) := by
        simpa using hρc.tendsto (1 : G)
      exact h1.le_comap
    · obtain ⟨V, hV1, hVN, -⟩ := local_compact_nhds hN
      obtain ⟨O, hO, hKO⟩ := exists_nhds_one_forall_notMem hc hi (hV₀.diff isOpen_interior)
        (fun h => h.2 (mem_interior_iff_mem_nhds.2 hV1))
      refine mem_inf_of_inter (preimage_mem_comap hO) (mem_principal_self V₀)
        fun g hg => hVN (interior_subset ?_)
      by_contra hint
      exact hKO g ⟨hg.2, hint⟩ hg.1
  rw [heq]
  infer_instance

end Paths

section Chart

attribute [local instance] LieRing.ofAssociativeRing

variable [NormedAlgebra ℝ A] [FiniteDimensional ℝ A] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- The image under a time-one map `ε` of a neighbourhood of `0` in the generator subalgebra
`L` is a neighbourhood of `1`. Write `A = L ⊕ C`; an element `g` near `1` has
`ρ g = exp Y * exp B` with `Y ∈ L`, `B ∈ C` small, and `h = (ε Y)⁻¹ * g` has `ρ h = exp B`.
If elements `g` outside the image accumulated at `1`, then `B ≠ 0` for them and, by the escape
lemma, the directions `‖B‖⁻¹ • B` would accumulate at a generator in `C` of norm one,
contradicting `L ⊓ C = ⊥`. -/
private theorem image_mem_nhds_one {ρ : G →* Aˣ} (hc : Continuous ρ)
    (hi : Function.Injective ρ) {ε : generatorSubalgebra ρ hc hi → G} (hε : ContinuousAt ε 0)
    (hρε : ∀ X, ((ρ (ε X) : Aˣ) : A) = NormedSpace.exp (X : A))
    {V : Set (generatorSubalgebra ρ hc hi)} (hV : V ∈ 𝓝 0) : ε '' V ∈ 𝓝 (1 : G) := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hρc : Continuous fun g : G => ((ρ g : Aˣ) : A) := Units.continuous_val.comp hc
  have hρ1 : Tendsto (fun g : G => ((ρ g : Aˣ) : A)) (𝓝 1) (𝓝 1) := by
    simpa using hρc.tendsto (1 : G)
  have hε0 : ε 0 = 1 := hi (Units.ext (by
    rw [hρε, ZeroMemClass.coe_zero, NormedSpace.exp_zero, map_one, Units.val_one]))
  obtain ⟨C, hLC⟩ := Submodule.exists_isCompl (generatorSubalgebra ρ hc hi).toSubmodule
  obtain ⟨Yf, Bf, hY0, hB0, hYL, hBC, hfac⟩ := exists_exp_mul_exp_eq hLC
  by_contra hnot
  have hW : ∀ N ∈ 𝓝 (1 : G), ∃ g ∈ N, g ∉ ε '' V ∧
      NormedSpace.exp (Yf ((ρ g : Aˣ) : A)) * NormedSpace.exp (Bf ((ρ g : Aˣ) : A)) =
        ((ρ g : Aˣ) : A) := by
    intro N hN
    by_contra hne
    apply hnot
    filter_upwards [hN, hρ1.eventually hfac] with g hgN hgT
    by_contra hgV
    exact hne ⟨g, hgN, hgV, hgT⟩
  have := isCountablyGenerated_nhds_one hc hi
  obtain ⟨s, hs⟩ := (𝓝 (1 : G)).exists_antitone_basis
  choose g hgs hgV hgf using fun k => hW (s k) (hs.mem k)
  have hg : Tendsto g atTop (𝓝 1) := hs.tendsto hgs
  have ha : Tendsto (fun k => ((ρ (g k) : Aˣ) : A)) atTop (𝓝 1) := hρ1.comp hg
  obtain ⟨y, hyv⟩ : ∃ y : ℕ → generatorSubalgebra ρ hc hi,
      ∀ k, (y k : A) = Yf ((ρ (g k) : Aˣ) : A) := ⟨fun k => ⟨_, hYL _⟩, fun _ => rfl⟩
  have hy : Tendsto y atTop (𝓝 0) := by
    refine tendsto_subtype_rng.2 ?_
    simp_rw [hyv]
    exact hY0.comp ha
  have hh : Tendsto (fun k => (ε (y k))⁻¹ * g k) atTop (𝓝 1) := by
    have h' := ((hε.tendsto.comp hy).inv).mul hg
    rwa [hε0, inv_one, one_mul] at h'
  have hρh : ∀ k, ((ρ ((ε (y k))⁻¹ * g k) : Aˣ) : A) =
      NormedSpace.exp (Bf ((ρ (g k) : Aˣ) : A)) := by
    intro k
    calc ((ρ ((ε (y k))⁻¹ * g k) : Aˣ) : A)
        = NormedSpace.exp (-Yf ((ρ (g k) : Aˣ) : A)) * ((ρ (g k) : Aˣ) : A) := by
          rw [map_mul, map_inv, Units.val_mul, ← Ring.inverse_unit, hρε, Ring.inverse_exp, hyv]
      _ = NormedSpace.exp (-Yf ((ρ (g k) : Aˣ) : A)) *
          (NormedSpace.exp (Yf ((ρ (g k) : Aˣ) : A)) *
            NormedSpace.exp (Bf ((ρ (g k) : Aˣ) : A))) := by rw [hgf k]
      _ = NormedSpace.exp (Bf ((ρ (g k) : Aˣ) : A)) := by
          rw [← mul_assoc, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left,
            neg_add_cancel, NormedSpace.exp_zero, one_mul]
  have hBne : ∀ᶠ k in atTop, Bf ((ρ (g k) : Aˣ) : A) ≠ 0 := by
    filter_upwards [hy hV] with k hk hBk
    refine hgV k ⟨y k, hk, hi (Units.ext ?_)⟩
    have h2 := hgf k
    rw [hBk, NormedSpace.exp_zero, mul_one] at h2
    rw [hρε, hyv]
    exact h2
  have hS : IsCompact ((C : Set A) ∩ Metric.sphere 0 1) :=
    (isCompact_sphere (0 : A) 1).inter_left C.closed_of_finiteDimensional
  have hDev : ∀ᶠ k in atTop, ‖Bf ((ρ (g k) : Aˣ) : A)‖⁻¹ • Bf ((ρ (g k) : Aˣ) : A) ∈
      (C : Set A) ∩ Metric.sphere 0 1 := by
    filter_upwards [hBne] with k hk
    refine ⟨C.smul_mem _ (hBC _), ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hk)]
  obtain ⟨D, hDS, hD⟩ := hS.exists_mapClusterPt_of_frequently hDev.frequently
  have hDgen : IsOneParameterGenerator ρ D :=
    isOneParameterGenerator_of_mapClusterPt ρ hc hi hh (hB0.comp ha) hρh hD
  have hD0 : D = 0 := Submodule.disjoint_def.1 hLC.disjoint D hDgen hDS.1
  have hD1 := hDS.2
  rw [hD0, mem_sphere_zero_iff_norm, norm_zero] at hD1
  exact zero_ne_one hD1

/-- Exponential chart of a locally compact group `G` with a continuous injective homomorphism
`ρ` into the units of a finite-dimensional real normed algebra `A`: there is a continuous map
`ε` from the Lie subalgebra of one-parameter generators to `G` with `ρ (ε X) = exp X`, whose
restriction to some open neighbourhood `U` of `0` is an open embedding. -/
theorem exists_exp_chart (ρ : G →* Aˣ) (hc : Continuous ρ) (hi : Function.Injective ρ) :
    ∃ ε : generatorSubalgebra ρ hc hi → G, Continuous ε ∧
      (∀ X, ((ρ (ε X) : Aˣ) : A) = NormedSpace.exp (X : A)) ∧
      ∃ U : Set (generatorSubalgebra ρ hc hi), IsOpen U ∧ (0 : generatorSubalgebra ρ hc hi) ∈ U ∧
        Topology.IsOpenEmbedding (U.domRestrict ε) := by
  have : T2Space G := T2Space.of_injective_continuous (f := fun g => ((ρ g : Aˣ) : A))
    (fun _ _ h => hi (Units.ext h)) (Units.continuous_val.comp hc)
  have hρc : Continuous fun g : G => ((ρ g : Aˣ) : A) := Units.continuous_val.comp hc
  choose γ hγc hγ using fun X : generatorSubalgebra ρ hc hi =>
    (X.2 : ∃ γ : ℝ → G, Continuous γ ∧
      ∀ t : ℝ, ((ρ (γ t) : Aˣ) : A) = NormedSpace.exp (t • (X : A)))
  obtain ⟨ε, hεdef⟩ : ∃ ε : generatorSubalgebra ρ hc hi → G, ε = fun X => γ X 1 := ⟨_, rfl⟩
  have hε : Continuous ε := hεdef ▸ continuous_lift_one hc hi continuous_subtype_val γ hγc hγ
  have hρε : ∀ X, ((ρ (ε X) : Aˣ) : A) = NormedSpace.exp (X : A) := fun X => by
    rw [hεdef, hγ, one_smul]
  have hε0 : ε 0 = 1 := hi (Units.ext (by
    rw [hρε, ZeroMemClass.coe_zero, NormedSpace.exp_zero, map_one, Units.val_one]))
  -- the local inverse of `exp` at `0`
  have hexp : HasStrictFDerivAt (NormedSpace.exp : A → A)
      ((ContinuousLinearEquiv.refl ℝ A : A ≃L[ℝ] A) : A →L[ℝ] A) 0 := by
    convert hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A) using 1
    ext
    simp
  obtain ⟨e, he⟩ : ∃ e : OpenPartialHomeomorph A A,
      e = hexp.toOpenPartialHomeomorph NormedSpace.exp := ⟨_, rfl⟩
  have he0 : (0 : A) ∈ e.source := he ▸ hexp.mem_toOpenPartialHomeomorph_source
  have heexp : ∀ x, e x = NormedSpace.exp x := fun x => by
    rw [he, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hS : Subtype.val ⁻¹' e.source ∈ 𝓝 (0 : generatorSubalgebra ρ hc hi) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds he0)
  have hinj : InjOn ε (Subtype.val ⁻¹' e.source) := fun X hX Y hY hXY =>
    Subtype.ext (e.injOn hX hY (by rw [heexp, heexp, ← hρε, ← hρε, hXY]))
  -- an open neighbourhood of `1` covered by the images of elements of the chart domain
  obtain ⟨W, hWdef⟩ : ∃ W : Set G, W = interior (ε '' (Subtype.val ⁻¹' e.source)) := ⟨_, rfl⟩
  have hW1 : (1 : G) ∈ W :=
    hWdef ▸ mem_interior_iff_mem_nhds.2 (image_mem_nhds_one hc hi hε.continuousAt hρε hS)
  have hWS : W ⊆ ε '' (Subtype.val ⁻¹' e.source) := hWdef ▸ interior_subset
  have hWo : IsOpen W := hWdef ▸ isOpen_interior
  obtain ⟨U, hUdef⟩ : ∃ U : Set (generatorSubalgebra ρ hc hi),
      U = Subtype.val ⁻¹' e.source ∩ ε ⁻¹' W := ⟨_, rfl⟩
  have hUo : IsOpen U := hUdef ▸ (e.open_source.preimage continuous_subtype_val).inter
    (hWo.preimage hε)
  -- on `U`, the image of an open set is the set of `g ∈ W` with `log (ρ g)` in it
  have hopen : ∀ O : Set (generatorSubalgebra ρ hc hi), IsOpen O → O ⊆ U → IsOpen (ε '' O) := by
    intro O hO hOU
    obtain ⟨O', hO', rfl⟩ := isOpen_induced_iff.1 hO
    have heq : ε '' (Subtype.val ⁻¹' O') =
        W ∩ (fun g : G => ((ρ g : Aˣ) : A)) ⁻¹' (e.target ∩ e.symm ⁻¹' O') := by
      ext g
      constructor
      · rintro ⟨X, hXO, rfl⟩
        have hXU := hOU hXO
        rw [hUdef] at hXU
        refine ⟨hXU.2, ?_, ?_⟩
        · show ((ρ (ε X) : Aˣ) : A) ∈ e.target
          rw [hρε, ← heexp]
          exact e.map_source hXU.1
        · show e.symm ((ρ (ε X) : Aˣ) : A) ∈ O'
          rw [hρε, ← heexp, e.left_inv hXU.1]
          exact hXO
      · rintro ⟨hgW, -, hgO⟩
        obtain ⟨Y, hYS, rfl⟩ := hWS hgW
        refine ⟨Y, ?_, rfl⟩
        have hgO' : e.symm ((ρ (ε Y) : Aˣ) : A) ∈ O' := hgO
        rw [hρε, ← heexp, e.left_inv hYS] at hgO'
        exact hgO'
    rw [heq]
    exact hWo.inter ((e.continuousOn_symm.isOpen_inter_preimage e.open_target hO').preimage hρc)
  refine ⟨ε, hε, hρε, U, hUo, ?_, ?_⟩
  · rw [hUdef]
    exact ⟨he0, by rw [mem_preimage, hε0]; exact hW1⟩
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hε.continuousOn.domRestrict
    (Set.injOn_iff_injective.1 (hinj.mono (hUdef ▸ inter_subset_left))) fun s hs => ?_
  rw [Set.domRestrict_eq, Set.image_comp]
  exact hopen _ (hUo.isOpenMap_subtype_val s hs) (Subtype.coe_image_subset U s)

end Chart

end D5.S3.Quantum.Analysis.LinearGroups.ExponentialChart
