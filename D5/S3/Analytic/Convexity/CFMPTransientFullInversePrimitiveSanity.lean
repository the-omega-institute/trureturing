import D5.S3.Analytic.Convexity.CFMPTransientFullInversePrimitive

/-!
Future sanity elaborations only; none has been run.
Lean v4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
These consume the actual assembly theorem, including its actual e and G.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped Classical NNReal InnerProductSpace

namespace CFMP144Transient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Arbitrary F on an empty D: no regularity, basepoint, or positive dimension
is needed. In particular the actual zero-totalized inverse is zero everywhere. -/
theorem sanity_emptyD (F : E → E) :
    let Ω : Set E := (fun x => x + F x) '' (∅ : Set E)
    IsOpen Ω ∧ Ω = ∅ ∧
      ∃ e : (∅ : Set E) ≃ₜ Ω,
        (∀ x : (∅ : Set E), (e x : E) = (x : E) + F (x : E)) ∧
        ∃ (G : E → E) (Q : E → ℝ),
          (∀ z, G z = 0) ∧
          (∀ y : Ω, G (y : E) = (e.symm y : E)) ∧
          LipschitzOnWith 1 G Ω ∧
          ∀ z ∈ Ω, HasFDerivAt Q (innerSL ℝ (G z)) z := by
  classical
  have hF : ∀ x ∈ (∅ : Set E), ∃ A : E →L[ℝ] E,
      HasFDerivAt F A x ∧ ∀ u v, inner ℝ (A u) v = inner ℝ u (A v) := by
    intro x hx
    exact False.elim hx
  obtain ⟨hΩ, e, he, G, Q, hGdef, hG, _hRestrict, _hMaps, _hInv, hLip, hQ⟩ :=
    exists_full_inverse_primitive (D := ∅) (U := ∅) (F := F)
      isOpen_empty convex_empty (continuousOn_empty F)
      (by intro x hx; exact False.elim hx) hF (by simp)
  refine ⟨hΩ, by simp, e, he, G, Q, ?_, hG, hLip, hQ⟩
  intro z
  rw [hGdef]
  simp

/-- Nonempty dimension-zero specialization. The core's nonempty branch uses
B4 with the homeomorphism produced by B2. No Nontrivial instance is installed. -/
theorem sanity_dimension0 :
    let E₀ := EuclideanSpace ℝ (Fin 0)
    let Ω : Set E₀ := (fun x => x + (0 : E₀)) '' (Set.univ : Set E₀)
    IsOpen Ω ∧ Ω = Set.univ ∧
      ∃ e : (Set.univ : Set E₀) ≃ₜ Ω,
        (∀ x : (Set.univ : Set E₀), (e x : E₀) = (x : E₀) + 0) ∧
        ∃ (G : E₀ → E₀) (Q : E₀ → ℝ),
          (∀ y : Ω, G (y : E₀) = (e.symm y : E₀)) ∧
          (∀ z, G z = z) ∧ LipschitzOnWith 1 G Ω ∧
          ∀ z, HasFDerivAt Q (innerSL ℝ (G z)) z := by
  classical
  let E₀ := EuclideanSpace ℝ (Fin 0)
  letI : MeasurableSpace E₀ := borel E₀
  letI : BorelSpace E₀ := ⟨rfl⟩
  let Ω : Set E₀ := (fun x => x + (0 : E₀)) '' (Set.univ : Set E₀)
  have hF : ∀ x ∈ (Set.univ : Set E₀), ∃ A : E₀ →L[ℝ] E₀,
      HasFDerivAt (fun _ : E₀ => (0 : E₀)) A x ∧
        ∀ u v, inner ℝ (A u) v = inner ℝ u (A v) := by
    intro x _hx
    exact ⟨0, hasFDerivAt_const (0 : E₀) x, by intro u v; simp⟩
  obtain ⟨hΩ, e, he, G, Q, _hGdef, hG, _hRestrict, _hMaps, hInv, hLip, hQ⟩ :=
    exists_full_inverse_primitive (D := Set.univ) (U := Set.univ)
      (F := fun _ : E₀ => (0 : E₀)) isOpen_univ convex_univ
      continuous_const.continuousOn (by intro x hx y hy; simp) hF (by simp)
  have hAll (z : E₀) : z ∈ Ω := ⟨z, Set.mem_univ z, by simp⟩
  have hΩuniv : Ω = Set.univ := Set.eq_univ_of_forall hAll
  refine ⟨hΩ, hΩuniv, e, he, G, Q, hG, ?_, hLip, ?_⟩
  · intro z
    simpa only [add_zero] using hInv z (hAll z)
  · intro z
    exact hQ z (hAll z)

/-- Original open-U/subset/PSD input used with the core. Dropping PSD happens
only in supplying its symmetric-derivative premise. The actual output e and G
then feed the original homeomorphism-style consumer, with no inverse re-choice.
The two total primitives need not agree or share a normalization. -/
theorem sanity_original_setting
    {D U : Set E} {F : E → E}
    (hDopen : IsOpen D) (hDconv : Convex ℝ D) (hFcont : ContinuousOn F D)
    (hMono : ∀ x ∈ D, ∀ y ∈ D, 0 ≤ inner ℝ (F x - F y) (x - y))
    (hUopen : IsOpen U) (hUD : U ⊆ D)
    (hF : ∀ x ∈ U, ∃ A : E →L[ℝ] E,
      HasFDerivAt F A x ∧
      (∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) ∧
      ∀ v, 0 ≤ inner ℝ (A v) v)
    (hFinite : (F '' (D \ U)).Finite) :
    let Ω : Set E := (fun x => x + F x) '' D
    IsOpen Ω ∧ ∃ e : D ≃ₜ Ω,
      (∀ x : D, (e x : E) = (x : E) + F (x : E)) ∧
      ∃ (G : E → E) (Q : E → ℝ),
        (∀ y : Ω, G (y : E) = (e.symm y : E)) ∧
        LipschitzOnWith 1 G Ω ∧
        ∀ z ∈ Ω, HasFDerivAt Q (innerSL ℝ (G z)) z := by
  have hSym : ∀ x ∈ U, ∃ A : E →L[ℝ] E,
      HasFDerivAt F A x ∧ ∀ u v, inner ℝ (A u) v = inner ℝ u (A v) := by
    intro x hx
    obtain ⟨A, hA, hASym, _hPSD⟩ := hF x hx
    exact ⟨A, hA, hASym⟩
  obtain ⟨hΩ, e, he, G, _Qcore, _hGdef, hG, _hRestrict, _hMaps, _hInv,
      hLip, _hQcore⟩ :=
    exists_full_inverse_primitive hDopen hDconv hFcont hMono hSym hFinite
  obtain ⟨_hImage, Q, hQ⟩ := original_homeomorph_primitive
    hDopen hDconv hΩ hFcont e he hG hLip hUopen hUD hF hFinite
  exact ⟨hΩ, e, he, G, Q, hG, hLip, hQ⟩

end CFMP144Transient

end
