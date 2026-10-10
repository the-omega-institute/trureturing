/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryTorusKernel
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryTorusKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryDiagonalSeparation
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryPoweredConjugation
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryTraceRootConjugation

/-! Actual determinant-one diagonals preserving the hyperbolic Hermitian form.
The pair labels are e_i,f_i; ordering f_i in reverse order makes this the standard
anti-diagonal form. The statements give literal matrices and all-target conjugation,
not an abstract torus action. Bounds concern the selected local block only. -/
namespace NikolovSegal.UnitaryField
open Matrix
variable {F : Type*} [Field F] [Finite F]

theorem regular_even_unitary_torus (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F)
    (m s : ℕ) (hs : 0 < s)
    (hQ : 2 * s * (m + 2)^2 + 2 < Nat.card (fixedField ι)) :
    ∃ u : Fˣ, ∃ D : SpecialLinearGroup (Fin (m + 2) ⊕ Fin (m + 2)) F,
      D.val = diagonal (fun i => (pairedEntries ι (evenWeight m) u i : F)) ∧
      adjoint ι D.val * hermitianForm (pairSwap (m + 2)) * D.val =
        hermitianForm (pairSwap (m + 2)) ∧
      (∀ i j : Fin (m + 2) ⊕ Fin (m + 2), i ≠ j →
        ((pairedEntries ι (evenWeight m) u i / pairedEntries ι (evenWeight m) u j)^s : Fˣ) ≠ 1) ∧
      (∀ A : SpecialLinearGroup (Fin (m + 2) ⊕ Fin (m + 2)) F, ∀ i j,
        ((D^s * A * (D^s)⁻¹).val) i j =
          (((pairedEntries ι (evenWeight m) u i / pairedEntries ι (evenWeight m) u j)^s : Fˣ) : F) *
            A.val i j) := by
  obtain ⟨u, hU, hsep⟩ := regular_even_diagonal ι hinv hne m s hs hQ
  refine ⟨u, evenDiagonal ι (evenWeight m) (evenWeight_sum m) u, rfl, hU, hsep, ?_⟩
  exact actual_powered_conjugation _ _ s

theorem regular_odd_unitary_torus (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F)
    (d s : ℕ) (hd : 0 < d) (hs : 0 < s)
    (hQ : 2 * s * (d + 1)^2 + 2 < Nat.card (fixedField ι)) :
    ∃ u : Fˣ, ∃ D : SpecialLinearGroup (Option (Fin d ⊕ Fin d)) F,
      D.val = diagonal (fun i => (oddEntries ι (positiveWeight d) u i : F)) ∧
      adjoint ι D.val * hermitianForm (oddSwap d) * D.val = hermitianForm (oddSwap d) ∧
      (((oddEntries ι (positiveWeight d) u none : Fˣ) : F) *
        ι ((oddEntries ι (positiveWeight d) u none : Fˣ) : F) = 1) ∧
      (∀ i j : Option (Fin d ⊕ Fin d), i ≠ j →
        ((oddEntries ι (positiveWeight d) u i / oddEntries ι (positiveWeight d) u j)^s : Fˣ) ≠ 1) ∧
      (∀ A : SpecialLinearGroup (Option (Fin d ⊕ Fin d)) F, ∀ i j,
        ((D^s * A * (D^s)⁻¹).val) i j =
          (((oddEntries ι (positiveWeight d) u i / oddEntries ι (positiveWeight d) u j)^s : Fˣ) : F) *
            A.val i j) := by
  obtain ⟨u, hU, hnorm, hsep⟩ := regular_odd_diagonal ι hinv hne d s hd hs hQ
  exact ⟨u, oddDiagonal ι (positiveWeight d) u, rfl, hU, hnorm, hsep,
    actual_powered_conjugation _ _ s⟩

/- Surjectivity of the actual norm coordinate of the four-dimensional torus.
The supplied norm is realized in an honest determinant-one Hermitian diagonal. -/
theorem prescribed_norm_even_torus (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F)
    (t : (fixedField ι)ˣ) :
    ∃ u : Fˣ, ∃ D : SpecialLinearGroup (Fin 2 ⊕ Fin 2) F,
      D.val = diagonal (fun i => (pairedEntries ι (evenWeight 0) u i : F)) ∧
      adjoint ι D.val * hermitianForm (pairSwap 2) * D.val = hermitianForm (pairSwap 2) ∧
      D.val (.inl 0) (.inl 0) * ι (D.val (.inl 0) (.inl 0)) = (t : fixedField ι) := by
  obtain ⟨u, hu⟩ := norm_units_surjective ι hinv hne t
  refine ⟨u, evenDiagonal ι (evenWeight 0) (evenWeight_sum 0) u,
    rfl, evenDiagonal_unitary ι hinv _ _ u, ?_⟩
  have he : evenWeight 0 (0 : Fin 2) = 1 := rfl
  simpa only [evenDiagonal, diagonalSL, diagonal_apply_eq, pairedEntries, he, zpow_one] using hu

end NikolovSegal.UnitaryField
