/- GID: D5/S3/Topology/InverseLimit/SignedBallHistoryCapture
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedBallHistoryCapture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original signed births and proper-stage historical capture. -/

import D5.S3.Topology.InverseLimit.CountableSignedMeasureReflection
import D5.S3.Topology.InverseLimit.CountableContinuousReflection
import D5.S3.Topology.InverseLimit.SignedBirthEnumeration
import D5.S3.Topology.Measures.SignedSplitSuccessorOrdered
import D5.S3.Topology.Measures.SignedBallReduction

/-! Original whole-sequence labels and literal norm-preserving projected lifts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Set Function Filter MeasureTheory
open scoped Ordinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedBallHistoryCapture

open CountableClopenReflection SignedBirthEnumeration SignedProperLimit
open D5.S3.Topology.Measures
open NormPreservingLifts

universe u v w z

local instance (X : Profinite.{1}) : MeasurableSpace X := borel X
local instance (X : Profinite.{1}) : BorelSpace X := ⟨rfl⟩

namespace Historical

private theorem cofinite_principal_le_of_finite_sdiff {s t : Set ℕ}
    (h : (s \ t).Finite) : cofinite ⊓ 𝓟 s ≤ cofinite ⊓ 𝓟 t := by
  calc
    cofinite ⊓ 𝓟 s = cofinite ⊓ 𝓟 (s \ (s \ t)) :=
      (h.cofinite_inf_principal_sdiff (s := s)).symm
    _ ≤ cofinite ⊓ 𝓟 t := inf_le_inf_left _ (principal_mono.2 (by
      intro x hx
      by_contra hxt
      exact hx.2 ⟨hx.1, hxt⟩))

private theorem exists_free_extension {I : Type u} [Nonempty I]
    (J : I → Set ℕ)
    (hd : ∀ i j, ∃ k, (J k \ J i).Finite ∧ (J k \ J j).Finite)
    (N : Set ℕ) (hinf : ∀ i, (J i ∩ N).Infinite) :
    ∃ u : Ultrafilter ℕ, (u : Filter ℕ) ≤ cofinite ∧ N ∈ u ∧ ∀ i, J i ∈ u := by
  classical
  let F : I → Filter ℕ := fun i => cofinite ⊓ 𝓟 (J i ∩ N)
  have hmono {i k : I} (h : (J k \ J i).Finite) : F k ≤ F i := by
    apply cofinite_principal_le_of_finite_sdiff
    apply h.subset
    intro n hn
    refine ⟨hn.1.1, ?_⟩
    intro hni
    exact hn.2 ⟨hni, hn.1.2⟩
  have hdir : Directed (· ≥ ·) F := by
    intro i j
    obtain ⟨k, hki, hkj⟩ := hd i j
    exact ⟨k, hmono hki, hmono hkj⟩
  have hn : ∀ i, (F i).NeBot := fun i => cofinite_inf_principal_neBot_iff.2 (hinf i)
  let f : Filter ℕ := ⨅ i, F i
  have : f.NeBot := iInf_neBot_of_directed' hdir hn
  let u : Ultrafilter ℕ := Ultrafilter.of f
  have hu (i : I) : (u : Filter ℕ) ≤ F i :=
    (Ultrafilter.of_le f).trans (iInf_le F i)
  have hm (i : I) : J i ∩ N ∈ (u : Filter ℕ) :=
    le_principal_iff.1 ((hu i).trans inf_le_right)
  exact ⟨u, (hu (Classical.arbitrary I)).trans inf_le_left,
    mem_of_superset (hm (Classical.arbitrary I)) inter_subset_right,
    fun i => mem_of_superset (hm i) inter_subset_left⟩

/-- Two fixed distinct free ultrafilters contain every historical set and
respectively the two original reservoirs. The index type is arbitrary;
only pairwise downward directedness modulo finite sets is required. -/
private theorem exists_distinct_free_ultrafilters {I : Type u} [Nonempty I]
    (J : I → Set ℕ)
    (hd : ∀ i j, ∃ k, (J k \ J i).Finite ∧ (J k \ J j).Finite)
    (N₀ N₁ : Set ℕ) (hdis : Disjoint N₀ N₁)
    (hinf₀ : ∀ i, (J i ∩ N₀).Infinite) (hinf₁ : ∀ i, (J i ∩ N₁).Infinite) :
    ∃ u₀ u₁ : Ultrafilter ℕ,
      (u₀ : Filter ℕ) ≤ cofinite ∧ (u₁ : Filter ℕ) ≤ cofinite ∧
      N₀ ∈ u₀ ∧ N₁ ∈ u₁ ∧ (∀ i, J i ∈ u₀) ∧ (∀ i, J i ∈ u₁) ∧ u₀ ≠ u₁ := by
  obtain ⟨u₀, hf₀, hN₀, hJ₀⟩ := exists_free_extension J hd N₀ hinf₀
  obtain ⟨u₁, hf₁, hN₁, hJ₁⟩ := exists_free_extension J hd N₁ hinf₁
  refine ⟨u₀, u₁, hf₀, hf₁, hN₀, hN₁, hJ₀, hJ₁, ?_⟩
  intro heq
  have hN₁' : N₁ ∈ (u₀ : Filter ℕ) := heq.symm ▸ hN₁
  exact (Filter.NeBot.not_disjoint inferInstance hN₀ hN₁') hdis

/-- Any already chosen free pair containing the whole history collides
under a continuous map if separating continuous Hausdorff-valued
observables converge, each on its own historical set. No common stage
for the observables is assumed. -/
private theorem eq_of_historical_observables {I : Type u} (J : I → Set ℕ)
    (u₀ u₁ : Ultrafilter ℕ)
    (hf₀ : (u₀ : Filter ℕ) ≤ cofinite) (hf₁ : (u₁ : Filter ℕ) ≤ cofinite)
    (hJ₀ : ∀ i, J i ∈ u₀) (hJ₁ : ∀ i, J i ∈ u₁)
    {X : Type v} [TopologicalSpace X] (V : Ultrafilter ℕ → X) (hV : Continuous V)
    {A : Type w} {Y : A → Type z} [∀ a, TopologicalSpace (Y a)] [∀ a, T2Space (Y a)]
    (phi : ∀ a, X → Y a) (hphi : ∀ a, Continuous (phi a))
    (hsep : ∀ x y, (∀ a, phi a x = phi a y) → x = y)
    (hconv : ∀ a, ∃ i L, Tendsto (fun n => phi a (V (pure n)))
      (cofinite ⊓ 𝓟 (J i)) (𝓝 L)) : V u₀ = V u₁ := by
  apply hsep
  intro a
  obtain ⟨i, L, hi⟩ := hconv a
  have hle₀ : (u₀ : Filter ℕ) ≤ cofinite ⊓ 𝓟 (J i) :=
    le_inf hf₀ (le_principal_iff.2 (hJ₀ i))
  have hle₁ : (u₁ : Filter ℕ) ≤ cofinite ⊓ 𝓟 (J i) :=
    le_inf hf₁ (le_principal_iff.2 (hJ₁ i))
  have hlim₀ : Tendsto (fun n => phi a (V (pure n))) (u₀ : Filter ℕ)
      (𝓝 (phi a (V u₀))) :=
    ((hphi a).comp hV).tendsto u₀ |>.comp (Ultrafilter.tendsto_pure_self u₀)
  have hlim₁ : Tendsto (fun n => phi a (V (pure n))) (u₁ : Filter ℕ)
      (𝓝 (phi a (V u₁))) :=
    ((hphi a).comp hV).tendsto u₁ |>.comp (Ultrafilter.tendsto_pure_self u₁)
  exact (tendsto_nhds_unique hlim₀ (hi.mono_left hle₀)).trans
    (tendsto_nhds_unique hlim₁ (hi.mono_left hle₁)).symm


end Historical

/-- Enumerations are required only from omega onward. -/
def birthBase : CountableStage := ⟨ω, Ordinal.omega0_lt_omega_one⟩

abbrev BirthStage := {a : CountableStage // birthBase ≤ a}
abbrev Eligible (θ : BirthStage) (d : Label) := {c : CountableStage // max θ.1 d < c}

private def bond (F : CountableStageᵒᵖ ⥤ Profinite.{1})
    {b c : CountableStage} (h : b ≤ c) : C(F.obj (op c), F.obj (op b)) :=
  (F.map (homOfLE h).op).hom.hom

private def projection {F : CountableStageᵒᵖ ⥤ Profinite.{1}}
    (C : Cone F) (b : CountableStage) : C(C.pt, F.obj (op b)) :=
  (C.π.app (op b)).hom.hom

private theorem posPart_real_eq_of_mass {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y] (s : SignedMeasure X)
    (p : X → Y) (hp : Measurable p)
    (hmass : (SignedMeasure.totalVariation (s.map p)) univ = s.totalVariation univ) :
    (SignedMeasure.toJordanDecomposition (s.map p)).posPart.real univ =
      s.toJordanDecomposition.posPart.real univ := by
  have hsum : (SignedMeasure.toJordanDecomposition (s.map p)).posPart.real univ +
      (SignedMeasure.toJordanDecomposition (s.map p)).negPart.real univ =
      s.toJordanDecomposition.posPart.real univ +
      s.toJordanDecomposition.negPart.real univ := by
    have he : (SignedMeasure.totalVariation (s.map p)).real univ =
        s.totalVariation.real univ := by
      simpa only [Measure.real] using congrArg ENNReal.toReal hmass
    calc
      _ = (SignedMeasure.totalVariation (s.map p)).real univ := by
        symm
        exact measureReal_add_apply
      _ = s.totalVariation.real univ := he
      _ = _ := measureReal_add_apply
  have hwhole : (s.map p) univ = s univ := by
    rw [VectorMeasure.map_apply _ hp MeasurableSet.univ, preimage_univ]
  rw [SignedMeasure.apply_eq_posPart_real_sub_negPart_real _ MeasurableSet.univ,
    SignedMeasure.apply_eq_posPart_real_sub_negPart_real _ MeasurableSet.univ] at hwhole
  linarith

private theorem regular_map_of_mass {X : Type u} {Y : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (s : SignedMeasure X) (hs : s.totalVariation.Regular) (p : C(X, Y))
    (hmass : (SignedMeasure.totalVariation (s.map p)) univ = s.totalVariation univ) :
    (SignedMeasure.totalVariation (s.map p)).Regular := by
  rw [totalVariation_map_of_mass s p p.continuous.measurable hmass]
  letI : s.totalVariation.Regular := hs
  letI : (s.totalVariation.map p).InnerRegular :=
    Measure.InnerRegular.map_of_continuous p.continuous
  infer_instance

private theorem map_carry {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y] (s : SignedMeasure X)
    (p : X → Y) (hp : Measurable p) {V : Set Y} (hV : MeasurableSet V)
    (hnull : s.totalVariation (p ⁻¹' V)ᶜ = 0) :
    (SignedMeasure.totalVariation (s.map p)) Vᶜ = 0 := by
  apply le_antisymm ?_ bot_le
  calc
    _ ≤ s.totalVariation.map p Vᶜ := by
      simpa only [SignedMeasure.totalVariation_eq_variation] using
        (VectorMeasure.variation_map_le (μ := s) (φ := p)) Vᶜ
    _ = 0 := by rw [Measure.map_apply hp hV.compl, preimage_compl, hnull]

private theorem functional_map {X : Type u} {Y : Type v}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (s : SignedMeasure X) (p : C(X, Y)) (g : C(Y, ℝ)) :
    signedFunctional (s.map p) g = signedFunctional s (g.comp p) := by
  change (∫ᵛ y, g y ∂•s.map p) = ∫ᵛ x, g (p x) ∂•s
  apply VectorMeasure.integral_map p.continuous.measurable
    g.continuous.aestronglyMeasurable
  rw [VectorMeasure.Integrable, ← SignedMeasure.totalVariation_eq_variation]
  exact (g.comp p).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)


/-- The stored data used by capture. The domain restriction on U, V and nu
is part of the telescope: no birth enumeration is postulated below omega. -/
structure RawHistory (F : CountableStageᵒᵖ ⥤ Profinite.{1}) where
  U : (b : BirthStage) → Label → SupportFamily (F.obj (op b.1))
  U_onto : ∀ b, Surjective (U b)
  V : (θ : BirthStage) → SupportFamily (F.obj (op θ.1))
  nu : (θ : BirthStage) → Label → BornData (V θ)
  nu_onto : ∀ θ, Surjective (nu θ)
  launch : ∀ b i, ∃ θ : BirthStage, ∃ h : b.1 < θ.1,
    ∀ n, (V θ).clopen n =
      ⟨bond F h.le ⁻¹' ((U b i).clopen n : Set (F.obj (op b.1))),
        ((U b i).clopen n).isClopen.preimage (bond F h.le).continuous⟩
  N₀ : BirthStage → Label → Set ℕ
  N₁ : BirthStage → Label → Set ℕ
  reservoirs_disjoint : ∀ θ d, Disjoint (N₀ θ d) (N₁ θ d)
  J : (θ : BirthStage) → (d : Label) → Eligible θ d → Set ℕ
  infinite₀ : ∀ θ d c, (J θ d c ∩ N₀ θ d).Infinite
  infinite₁ : ∀ θ d c, (J θ d c ∩ N₁ θ d).Infinite
  directed : ∀ θ d (b c : Eligible θ d), b.1 ≤ c.1 → (J θ d c \ J θ d b).Finite
  properF : ∀ θ d (c : Eligible θ d) (s : ℕ → SignedMeasure (F.obj (op c.1))),
    (∀ n, (s n).totalVariation.Regular) →
    (∀ n, (s n).totalVariation univ = 1) →
    (∀ n, (s n).map (bond F ((le_max_left θ.1 d).trans c.2.le)) =
      ((nu θ d).1 n).1) →
    (∀ n, (s n).totalVariation
      (bond F ((le_max_left θ.1 d).trans c.2.le) ⁻¹' (V θ).clopen n)ᶜ = 0) →
    ∃ μ : SignedMeasure (F.obj (op c.1)), μ.totalVariation.Regular ∧
      μ.totalVariation univ ≤ 1 ∧ ∀ g : C(F.obj (op c.1), ℝ),
        Tendsto (fun n => signedFunctional (s n) g)
          (cofinite ⊓ 𝓟 (J θ d c)) (𝓝 (signedFunctional μ g))

private theorem projection_factor (F : CountableStageᵒᵖ ⥤ Profinite.{1})
    (C : Cone F) {b c : CountableStage} (h : b ≤ c) :
    (bond F h : F.obj (op c) → F.obj (op b)) ∘ projection C c =
      projection C b := by
  funext x
  exact ConcreteCategory.congr_hom (C.w (homOfLE h).op) x

theorem exists_original_birth (F : CountableStageᵒᵖ ⥤ Profinite.{1})
    (C : Cone F) (H : RawHistory F)
    (s : ℕ → SignedMeasure C.pt)
    (hsreg : ∀ n, (s n).totalVariation.Regular)
    (hsnorm : ∀ n, (s n).totalVariation univ = 1)
    (hshalf : ∀ n, (1 / 2 : ℝ) ≤ (s n).toJordanDecomposition.posPart.real univ)
    (b : BirthStage) (W : SupportFamily (F.obj (op b.1)))
    (hcarry : ∀ n, (s n).totalVariation (projection C b.1 ⁻¹' W.clopen n)ᶜ = 0)
    (hbmass : ∀ n, (SignedMeasure.totalVariation ((s n).map (projection C b.1))) univ = 1) :
    ∃ θ : BirthStage, b.1 < θ.1 ∧ ∃ d : Label,
      (∀ n, ((H.nu θ d).1 n).1 = (s n).map (projection C θ.1)) ∧
      (∀ n, (s n).totalVariation (projection C θ.1 ⁻¹' (H.V θ).clopen n)ᶜ = 0) := by
  obtain ⟨i, hi⟩ := H.U_onto b W
  obtain ⟨θ, hbθ, hlaunch⟩ := H.launch b i
  have hpre (n : ℕ) :
      projection C θ.1 ⁻¹' (H.V θ).clopen n =
        projection C b.1 ⁻¹' W.clopen n := by
    rw [hlaunch n, hi]
    change ((bond F hbθ.le : F.obj (op θ.1) → F.obj (op b.1)) ∘
      projection C θ.1) ⁻¹' W.clopen n = _
    rw [projection_factor F C hbθ.le]
  have hnorm (n : ℕ) : (SignedMeasure.totalVariation ((s n).map (projection C θ.1))) univ = 1 := by
    have h := SignedSplitSuccessor.map_mass_through_factor
      (projection C θ.1) (projection C θ.1).continuous.measurable
      (bond F hbθ.le) (bond F hbθ.le).continuous.measurable
      (s n) ((s n).map (projection C b.1))
      (by rw [projection_factor F C hbθ.le]) (by rw [hsnorm n, hbmass n])
    exact h.2.trans (hbmass n)
  have hreg (n : ℕ) : (SignedMeasure.totalVariation ((s n).map (projection C θ.1))).Regular :=
    regular_map_of_mass (s n) (hsreg n) (projection C θ.1)
      (by rw [hnorm n, hsnorm n])
  let B : BornData (H.V θ) := ⟨fun n => ⟨(s n).map (projection C θ.1), by
      letI := hreg n
      exact RegularSignedLift.regular_jordanParts_of_regular_totalVariation _⟩, fun n => by
    refine ⟨hnorm n, ?_, ?_⟩
    · apply map_carry _ _ (projection C θ.1).continuous.measurable
        ((H.V θ).clopen n).isClopen.isClosed.measurableSet
      rw [hpre n]
      exact hcarry n
    · have hh : (1 / 2 : ℝ) ≤
          (SignedMeasure.toJordanDecomposition ((s n).map (projection C θ.1))).posPart.real univ := by
        rw [posPart_real_eq_of_mass (s n) _
          (projection C θ.1).continuous.measurable
          (by rw [hnorm n, hsnorm n])]
        exact hshalf n
      exact (ENNReal.toReal_le_toReal (by norm_num) (by finiteness)).mp (by
        simpa only [Measure.real, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using hh)⟩
  obtain ⟨d, hd⟩ := H.nu_onto θ B
  refine ⟨θ, hbθ, d, ?_, ?_⟩
  · intro n
    exact congrArg (fun t : BornData (H.V θ) => ((t.1 n).1)) hd
  · intro n
    rw [hpre n]
    exact hcarry n

theorem projected_lift (F : CountableStageᵒᵖ ⥤ Profinite.{1})
    (C : Cone F) (H : RawHistory F) (s : ℕ → SignedMeasure C.pt)
    (hsreg : ∀ n, (s n).totalVariation.Regular)
    (hsnorm : ∀ n, (s n).totalVariation univ = 1)
    (θ : BirthStage) (d : Label)
    (hbirth : ∀ n, ((H.nu θ d).1 n).1 = (s n).map (projection C θ.1))
    (hcarry : ∀ n, (s n).totalVariation (projection C θ.1 ⁻¹' (H.V θ).clopen n)ᶜ = 0)
    (c : Eligible θ d) :
    (∀ n, (SignedMeasure.totalVariation ((s n).map (projection C c.1))).Regular) ∧
    (∀ n, (SignedMeasure.totalVariation ((s n).map (projection C c.1))) univ = 1) ∧
    (∀ n, ((s n).map (projection C c.1)).map
      (bond F ((le_max_left θ.1 d).trans c.2.le)) = ((H.nu θ d).1 n).1) ∧
    (∀ n, (SignedMeasure.totalVariation ((s n).map (projection C c.1)))
      (bond F ((le_max_left θ.1 d).trans c.2.le) ⁻¹' (H.V θ).clopen n)ᶜ = 0) := by
  let hθc : θ.1 ≤ c.1 := (le_max_left θ.1 d).trans c.2.le
  have hsand (n : ℕ) := SignedSplitSuccessor.map_mass_through_factor
    (projection C c.1) (projection C c.1).continuous.measurable
    (bond F hθc) (bond F hθc).continuous.measurable
    (s n) (((H.nu θ d).1 n).1)
    (by rw [projection_factor F C hθc, hbirth n])
    (by rw [hsnorm n, ((H.nu θ d).2 n).1])
  have hnorm (n : ℕ) : (SignedMeasure.totalVariation ((s n).map (projection C c.1))) univ = 1 :=
    (hsand n).2.trans (((H.nu θ d).2 n).1)
  refine ⟨fun n => regular_map_of_mass (s n) (hsreg n)
    (projection C c.1) (by rw [hnorm n, hsnorm n]),
    hnorm, fun n => (hsand n).1, ?_⟩
  intro n
  apply map_carry _ _ (projection C c.1).continuous.measurable
    (((H.V θ).clopen n).isClopen.preimage (bond F hθc).continuous).isClosed.measurableSet
  change (s n).totalVariation
    (((bond F hθc : F.obj (op c.1) → F.obj (op θ.1)) ∘ projection C c.1) ⁻¹'
      (H.V θ).clopen n)ᶜ = 0
  rw [projection_factor F C hθc]
  exact hcarry n

private theorem collision_of_original_birth (F : CountableStageᵒᵖ ⥤ Profinite.{1})
    [∀ j, Nonempty (F.obj j)] (C : Cone F) (hC : IsLimit C)
    (hs : ∀ {i j} (a : i ⟶ j), Surjective (F.map a)) (H : RawHistory F)
    (s : ℕ → SignedMeasure C.pt)
    (hsreg : ∀ n, (s n).totalVariation.Regular)
    (hsnorm : ∀ n, (s n).totalVariation univ = 1)
    (θ : BirthStage) (d : Label)
    (hbirth : ∀ n, ((H.nu θ d).1 n).1 = (s n).map (projection C θ.1))
    (hcarry : ∀ n, (s n).totalVariation (projection C θ.1 ⁻¹' (H.V θ).clopen n)ᶜ = 0) :
    ∃ p q : Ultrafilter ℕ, (p : Filter ℕ) ≤ cofinite ∧
      (q : Filter ℕ) ≤ cofinite ∧ p ≠ q ∧
      ∀ f : Ultrafilter ℕ → WeakDual ℝ C(C.pt, ℝ), Continuous f →
        (∀ n, f (pure n) = StrongDual.toWeakDual (signedFunctional (s n))) → f p = f q := by
  let c0 : CountableStage :=
    ⟨Order.succ (max θ.1.1 d.1),
      (Cardinal.isSuccLimit_omega 1).succ_lt (max_lt θ.1.2 d.2)⟩
  have hc0 : max θ.1 d < c0 := by
    change max θ.1.1 d.1 < Order.succ (max θ.1.1 d.1)
    exact Order.lt_succ _
  letI : Nonempty (Eligible θ d) := ⟨⟨c0, hc0⟩⟩
  have hdir (i j : Eligible θ d) :
      ∃ k : Eligible θ d, (H.J θ d k \ H.J θ d i).Finite ∧
        (H.J θ d k \ H.J θ d j).Finite := by
    let k : Eligible θ d := ⟨max i.1 j.1, i.2.trans_le (le_max_left _ _)⟩
    exact ⟨k, H.directed θ d i k (le_max_left _ _),
      H.directed θ d j k (le_max_right _ _)⟩
  obtain ⟨p, q, hp, hq, _, _, hpJ, hqJ, hpq⟩ :=
    Historical.exists_distinct_free_ultrafilters (H.J θ d) hdir
      (H.N₀ θ d) (H.N₁ θ d) (H.reservoirs_disjoint θ d)
      (H.infinite₀ θ d) (H.infinite₁ θ d)
  refine ⟨p, q, hp, hq, hpq, ?_⟩
  intro f hf hext
  apply Historical.eq_of_historical_observables (H.J θ d) p q hp hq hpJ hqJ f hf
    (fun g : C(C.pt, ℝ) => fun x : WeakDual ℝ C(C.pt, ℝ) => x g)
    (fun g => WeakDual.eval_continuous g)
    (fun x y h => by
      apply WeakDual.toStrongDual.injective
      exact ContinuousLinearMap.ext h)
  intro g
  obtain ⟨c, hbase, a, ha⟩ := CountableContinuousReflection.exists_stage F C hC hs c0 g
  let e : Eligible θ d := ⟨c, hc0.trans_le hbase⟩
  obtain ⟨hreg, hnorm, hmap, hsup⟩ := projected_lift F C H s hsreg hsnorm θ d hbirth hcarry e
  obtain ⟨μ, _, _, hconv⟩ := H.properF θ d e
    (fun n => (s n).map (projection C c)) hreg hnorm hmap hsup
  refine ⟨e, signedFunctional μ a, ?_⟩
  have htest : g = a.comp (projection C c) := by
    ext x
    exact ha x
  have heval (n : ℕ) : f (pure n) g =
      signedFunctional ((s n).map (projection C c)) a := by
    rw [hext n]
    change signedFunctional (s n) g = _
    rw [functional_map, ← htest]
  simpa only [heval] using hconv a

private theorem capture_reflected_sequence (F : CountableStageᵒᵖ ⥤ Profinite.{1})
    [∀ j, Nonempty (F.obj j)] (C : Cone F) (hC : IsLimit C)
    (hs : ∀ {i j} (a : i ⟶ j), Surjective (F.map a)) (H : RawHistory F)
    (s : ℕ → SignedMeasure C.pt)
    (hsreg : ∀ n, (s n).totalVariation.Regular)
    (hsnorm : ∀ n, (s n).totalVariation univ = 1)
    (hshalf : ∀ n, (1 / 2 : ℝ) ≤ (s n).toJordanDecomposition.posPart.real univ)
    (b : BirthStage) (W : SupportFamily (F.obj (op b.1)))
    (hcarry : ∀ n, (s n).totalVariation (projection C b.1 ⁻¹' W.clopen n)ᶜ = 0)
    (hbmass : ∀ n, (SignedMeasure.totalVariation ((s n).map (projection C b.1))) univ = 1) :
    ∃ p q : Ultrafilter ℕ, (p : Filter ℕ) ≤ cofinite ∧
      (q : Filter ℕ) ≤ cofinite ∧ p ≠ q ∧
      ∀ f : Ultrafilter ℕ → WeakDual ℝ C(C.pt, ℝ), Continuous f →
        (∀ n, f (pure n) = StrongDual.toWeakDual (signedFunctional (s n))) → f p = f q := by
  obtain ⟨θ, _, d, hbirth, hsup⟩ :=
    exists_original_birth F C H s hsreg hsnorm hshalf b W hcarry hbmass
  exact collision_of_original_birth F C hC hs H s hsreg hsnorm θ d hbirth hsup


theorem signed_clopen_collision (F : CountableStageᵒᵖ ⥤ Profinite.{1})
    [∀ j, Nonempty (F.obj j)] (C : Cone F) (hC : IsLimit C)
    (hs : ∀ {i j} (a : i ⟶ j), Surjective (F.map a)) (H : RawHistory F) :
    SignedBallReduction.SignedClopenCollision (K := C.pt) := by
  intro s W hsreg hsnorm hW hdis hcarry hhalf f hf hext
  letI : ∀ n, (s n).totalVariation.Regular := hsreg
  obtain ⟨b, hb, V, hV, hWV, hne, hdisV, hpres, _⟩ :=
    CountableSignedMeasureReflection.exists_common_stage F C hC hs birthBase s W
      (fun n => (hW n).1)
  let row : BirthStage := ⟨b, hb⟩
  let family : SupportFamily (F.obj (op b)) :=
    { clopen := fun n => ⟨V n, hV n⟩
      nonempty := fun n => (hne n).mpr (hW n).2
      disjoint := fun n m hnm => (hdisV n m).mpr (hdis hnm) }
  have hmass (n : ℕ) : (s n).totalVariation univ = 1 :=
    (ENNReal.toReal_eq_one_iff _).mp (by simpa only [Measure.real] using hsnorm n)
  have hbmass (n : ℕ) :
      (SignedMeasure.totalVariation ((s n).map (projection C row.1))) univ = 1 := by
    have h := ((hpres b le_rfl n).1).1
    change (SignedMeasure.totalVariation ((s n).map (projection C row.1))) univ =
      (s n).totalVariation univ at h
    exact h.trans (hmass n)
  have hsup (n : ℕ) :
      (s n).totalVariation (projection C row.1 ⁻¹' family.clopen n)ᶜ = 0 := by
    have h := hWV n
    change W n = projection C row.1 ⁻¹' family.clopen n at h
    rw [← h]
    exact hcarry n
  obtain ⟨p, q, hp, hq, hpq, hcollision⟩ :=
    capture_reflected_sequence F C hC hs H s hsreg hmass hhalf row family hsup hbmass
  exact ⟨p, q, hp, hq, hpq, hcollision f hf hext⟩

#check @signed_clopen_collision
#print axioms signed_clopen_collision


end D5.S3.Topology.InverseLimit.SignedBallHistoryCapture
