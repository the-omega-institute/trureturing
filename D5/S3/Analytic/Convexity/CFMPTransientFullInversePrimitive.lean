import D5.S3.Analytic.Convexity.CFMPTransientOpenImage
import D5.S3.Analytic.Convexity.CFMPTransientInverseAE
import D5.S3.Analytic.Convexity.CFMPTransientLocalWeakPoincare
import D5.S3.Analytic.Convexity.CFMPTransientGlobalPrimitive

/-!
Transient source assembly only. NOT elaborated, compiled, kernel checked, or admitted.
Target: Lean v4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
The four imports refer to the exact immutable files in the supplied manifest.
In particular, the independent B2 legacy-import recheck remains pending.
No replacement for its original private owner is introduced here.

The private binder below is shared by the core and the requested original-setting
consumer. It takes the already identified e and G; it chooses no other inverse.
All declarations in this file are transient, not proposed canonical wrappers.
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Classical Topology NNReal InnerProductSpace

namespace CFMP144Transient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The used B1 → B3 → B4 binder. No local/global primitive is assumed. -/
private theorem primitive_for_same_inverse
    {D Ω U : Set E} {F G : E → E} {K : ℝ≥0}
    (hΩ : IsOpen Ω) (hD : Convex ℝ D) (e : D ≃ₜ Ω)
    (hLip : LipschitzOnWith K G Ω) (hMaps : MapsTo G Ω D)
    (hInv : ∀ y ∈ Ω, G y + F (G y) = y)
    (hF : ∀ x ∈ U, ∃ A : E →L[ℝ] E,
      HasFDerivAt F A x ∧ ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    (hFinite : (F '' (D \ U)).Finite) :
    ∃ Q : E → ℝ, ∀ z ∈ Ω, HasFDerivAt Q (innerSL ℝ (G z)) z := by
  classical
  -- Canonical inner-product volume, on the original ambient E throughout.
  -- The OfBasis import supplies IsAddHaarMeasure for this very volume.
  have hAE : ∀ᵐ z ∂(volume : Measure E).restrict Ω,
      ∃ A : E →L[ℝ] E, HasFDerivAt G A z ∧
        ∀ u v, inner ℝ (A u) v = inner ℝ u (A v) :=
    CFMPInverseAE.ae_symmetric_derivative_of_finite_exceptional_values
      (volume : Measure E) hΩ hLip hMaps hInv hF hFinite
  have hlocal : ∀ a ∈ Ω, ∃ r > 0, ∃ q : E → ℝ,
      ball a r ⊆ Ω ∧
        ∀ z ∈ ball a r, HasFDerivAt q (innerSL ℝ (G z)) z := by
    intro a ha
    obtain ⟨r, hr, hball, q, _hq_normalized, hq⟩ :=
      LocalWeakPoincare.exists_local_normalized_primitive hΩ hLip hAE a ha
    -- B3: r, positive, containment, q, normalization, derivative.
    -- B4: r, positive, q, containment, derivative.
    exact ⟨r, hr, q, hball, hq⟩
  by_cases hempty : D = ∅
  · -- There is no choice of a point in either empty subtype.
    have hΩempty : Ω = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hmem : G z ∈ D := hMaps hz
      simpa only [hempty, Set.mem_empty_iff_false] using hmem
    refine ⟨fun _ => 0, ?_⟩
    intro z hz
    have hfalse : False := by
      simpa only [hΩempty, Set.mem_empty_iff_false] using hz
    exact hfalse.elim
  · have hne : D.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
    exact CFMP137Transient.exists_global_primitive_of_homeomorph
      (ω := fun z => innerSL ℝ (G z)) hΩ hD hne e hlocal

/-- Complete same-object target: the image, homeomorphism, ambient inverse, and
total primitive are outputs. There is no nonempty, nontrivial, PSD, open-U,
convex-image, inverse, or local-primitive premise. -/
theorem exists_full_inverse_primitive
    {D U : Set E} {F : E → E}
    (hDopen : IsOpen D) (hDconv : Convex ℝ D) (hFcont : ContinuousOn F D)
    (hMono : ∀ x ∈ D, ∀ y ∈ D, 0 ≤ inner ℝ (F x - F y) (x - y))
    (hF : ∀ x ∈ U, ∃ A : E →L[ℝ] E,
      HasFDerivAt F A x ∧ ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    (hFinite : (F '' (D \ U)).Finite) :
    let T : E → E := fun x => x + F x
    let Ω : Set E := T '' D
    IsOpen Ω ∧ ∃ e : D ≃ₜ Ω,
      (∀ x : D, (e x : E) = T (x : E)) ∧
      ∃ (G : E → E) (Q : E → ℝ),
        (G = fun z => if hz : z ∈ Ω then (e.symm ⟨z, hz⟩ : E) else 0) ∧
        (∀ y : Ω, G (y : E) = (e.symm y : E)) ∧
        (Ω.domRestrict G = (Subtype.val : D → E) ∘ e.symm) ∧
        MapsTo G Ω D ∧
        (∀ y ∈ Ω, G y + F (G y) = y) ∧
        LipschitzOnWith 1 G Ω ∧
        ∀ z ∈ Ω, HasFDerivAt Q (innerSL ℝ (G z)) z := by
  classical
  let T : E → E := fun x => x + F x
  let Ω : Set E := T '' D
  change IsOpen Ω ∧ ∃ e : D ≃ₜ Ω,
    (∀ x : D, (e x : E) = T (x : E)) ∧
    ∃ (G : E → E) (Q : E → ℝ),
      (G = fun z => if hz : z ∈ Ω then (e.symm ⟨z, hz⟩ : E) else 0) ∧
      (∀ y : Ω, G (y : E) = (e.symm y : E)) ∧
      (Ω.domRestrict G = (Subtype.val : D → E) ∘ e.symm) ∧
      MapsTo G Ω D ∧ (∀ y ∈ Ω, G y + F (G y) = y) ∧
      LipschitzOnWith 1 G Ω ∧
      ∀ z ∈ Ω, HasFDerivAt Q (innerSL ℝ (G z)) z
  -- Exactly the third projection; no audit projection wrapper or new choice.
  obtain ⟨hΩ, _hExpansion, _hInjective, e₀, he₀, _hInvNorm, hInvLip⟩ :=
    (CFMP133_SourceOnly.bridge (E := E)).2.2 D F hDopen hFcont hMono
  have hT : ContinuousOn T D := continuous_id.continuousOn.add hFcont
  have hTsub : Continuous (fun x : D => T (x : E)) := hT.domRestrict
  have he₀val : Continuous (fun x : D => (e₀ x : E)) :=
    hTsub.congr (fun x => (he₀ x).symm)
  have he₀cont : Continuous e₀ := by
    -- Subtype eta preserves the exact e₀ returned by B2.
    simpa only [Subtype.coe_eta] using
      he₀val.subtype_mk (fun x => (e₀ x).property)
  let e : D ≃ₜ Ω :=
    { toEquiv := e₀
      continuous_toFun := he₀cont
      continuous_invFun := hInvLip.continuous }
  have he : ∀ x : D, (e x : E) = T (x : E) := he₀
  have heInvLip : LipschitzWith 1 e.symm := hInvLip
  -- The only ambient inverse definition in the assembly.
  let G : E → E := fun z => if hz : z ∈ Ω then (e.symm ⟨z, hz⟩ : E) else 0
  have hG : ∀ y : Ω, G (y : E) = (e.symm y : E) := by
    intro y
    simp only [G, dif_pos y.property]
  have hRestrict : Ω.domRestrict G = (Subtype.val : D → E) ∘ e.symm := by
    funext y
    exact hG y
  have hMaps : MapsTo G Ω D := by
    intro y hy
    rw [hG ⟨y, hy⟩]
    exact (e.symm ⟨y, hy⟩).property
  have hInv : ∀ y ∈ Ω, G y + F (G y) = y := by
    intro y hy
    let yΩ : Ω := ⟨y, hy⟩
    calc
      G y + F (G y) = (e.symm yΩ : E) + F (e.symm yΩ : E) := by
        rw [hG yΩ]
      _ = (e (e.symm yΩ) : E) := (he (e.symm yΩ)).symm
      _ = y := congrArg (fun z : Ω => (z : E)) (e.apply_symm_apply yΩ)
  have hLip : LipschitzOnWith 1 G Ω := by
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    rw [hG ⟨y, hy⟩, hG ⟨z, hz⟩]
    simpa only [Subtype.dist_eq] using
      heInvLip.dist_le_mul (⟨y, hy⟩ : Ω) (⟨z, hz⟩ : Ω)
  obtain ⟨Q, hQ⟩ := primitive_for_same_inverse
    hΩ hDconv e hLip hMaps hInv hF hFinite
  exact ⟨hΩ, e, he, G, Q, rfl, hG, hRestrict, hMaps, hInv, hLip, hQ⟩

/-- Original homeomorphism-style consumer. Its extra original hypotheses are
retained here only; they are not premises of the core theorem. This consumer
uses the given e and G directly, without invoking B2 again or selecting another
inverse. PSD is dropped only in the application to the shared binder. -/
theorem original_homeomorph_primitive
    {D Ω U : Set E} {F G : E → E} {K : ℝ≥0}
    (_hDopen : IsOpen D) (hDconv : Convex ℝ D)
    (hΩ : IsOpen Ω) (_hFcont : ContinuousOn F D)
    (e : D ≃ₜ Ω)
    (he : ∀ x : D, (e x : E) = (x : E) + F (x : E))
    (hG : ∀ y : Ω, G (y : E) = (e.symm y : E))
    (hLip : LipschitzOnWith K G Ω)
    (_hUopen : IsOpen U) (_hUD : U ⊆ D)
    (hF : ∀ x ∈ U, ∃ A : E →L[ℝ] E,
      HasFDerivAt F A x ∧
      (∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) ∧
      ∀ v, 0 ≤ inner ℝ (A v) v)
    (hFinite : (F '' (D \ U)).Finite) :
    Ω = (fun x => x + F x) '' D ∧
      ∃ Q : E → ℝ, ∀ z ∈ Ω, HasFDerivAt Q (innerSL ℝ (G z)) z := by
  have hMaps : MapsTo G Ω D := by
    intro y hy
    rw [hG ⟨y, hy⟩]
    exact (e.symm ⟨y, hy⟩).property
  have hInv : ∀ y ∈ Ω, G y + F (G y) = y := by
    intro y hy
    let yΩ : Ω := ⟨y, hy⟩
    calc
      G y + F (G y) = (e.symm yΩ : E) + F (e.symm yΩ : E) := by
        rw [hG yΩ]
      _ = (e (e.symm yΩ) : E) := (he (e.symm yΩ)).symm
      _ = y := congrArg (fun z : Ω => (z : E)) (e.apply_symm_apply yΩ)
  refine ⟨?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro y hy
      exact ⟨G y, hMaps hy, hInv y hy⟩
    · rintro y ⟨x, hx, rfl⟩
      rw [← he ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
  · apply primitive_for_same_inverse hΩ hDconv e hLip hMaps hInv
    · intro x hx
      obtain ⟨A, hA, hSym, _hPSD⟩ := hF x hx
      exact ⟨A, hA, hSym⟩
    · exact hFinite

end CFMP144Transient

end
