/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryAntidiagonalCoordinates
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryAntidiagonalCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryTorusKernel
import Mathlib.Data.Fin.Rev

namespace NikolovSegal.UnitaryField
open Matrix

def evenLabel (d : ℕ) : (Fin d ⊕ Fin d) ≃ Fin (2*d) :=
  ((Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans finSumFinEquiv).trans
    (finCongr (by omega))

theorem evenLabel_reflection (d : ℕ) (i : Fin d ⊕ Fin d) :
    evenLabel d (pairSwap d i) = (evenLabel d i).rev := by
  apply Fin.ext
  cases i <;> simp [evenLabel, pairSwap, Fin.revPerm, Fin.rev, finSumFinEquiv]
  all_goals omega

def oddLabelFn (d : ℕ) : Option (Fin d ⊕ Fin d) → Fin (2*d+1)
  | none => ⟨d, by omega⟩
  | some (.inl i) => ⟨i.val, by omega⟩
  | some (.inr i) => ⟨2*d-i.val, by omega⟩

theorem oddLabelFn_injective (d : ℕ) : Function.Injective (oddLabelFn d) := by
  intro i j h
  have hv := congrArg Fin.val h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => cases j <;> simp only [oddLabelFn] at hv <;> omega
  | some i =>
    cases j with
    | none => cases i <;> simp only [oddLabelFn] at hv <;> omega
    | some j =>
      cases i with
      | inl i =>
        cases j with
        | inl j => exact congrArg (fun z => some (Sum.inl z)) (Fin.ext hv)
        | inr j => simp only [oddLabelFn] at hv; omega
      | inr i =>
        cases j with
        | inl j => simp only [oddLabelFn] at hv; omega
        | inr j =>
          simp only [oddLabelFn] at hv
          have he : i.val = j.val := by omega
          exact congrArg (fun z => some (Sum.inr z)) (Fin.ext he)

noncomputable def oddLabel (d : ℕ) : Option (Fin d ⊕ Fin d) ≃ Fin (2*d+1) :=
  Equiv.ofBijective (oddLabelFn d) ((oddLabelFn_injective d).bijective_of_nat_card_le (by
    simp [Nat.card_eq_fintype_card]; omega))

theorem oddLabel_reflection (d : ℕ) (i : Option (Fin d ⊕ Fin d)) :
    oddLabel d (oddSwap d i) = (oddLabel d i).rev := by
  apply Fin.ext
  cases i with
  | none => simp [oddLabel, oddLabelFn, oddSwap, Fin.rev]; omega
  | some i => cases i <;> simp [oddLabel, oddLabelFn, oddSwap, pairSwap, Fin.rev] <;> omega

variable {F : Type*} [Field F] [Finite F]

/- Literal anti-diagonal form on the native Fin N coordinate space. -/
def antiDiagonal (N : ℕ) : Matrix (Fin N) (Fin N) F := hermitianForm Fin.revPerm

theorem transport_antidiagonal_torus {I : Type*} [Fintype I] [DecidableEq I]
    (N : ℕ) (e : I ≃ Fin N) (τ : I ≃ I)
    (href : ∀ i, e (τ i) = (e i).rev)
    (ι : F ≃+* F) (w : I → Fˣ) (hw : ∏ i, w i = 1)
    (hunit : ∀ i, involutionUnit ι (w i) * w (τ i) = 1)
    (s : ℕ) (hsep : ∀ i j, i ≠ j → ((w i / w j)^s : Fˣ) ≠ 1) :
    ∃ D : SpecialLinearGroup (Fin N) F,
      D.val = diagonal (fun j => (w (e.symm j) : F)) ∧
      adjoint ι D.val * antiDiagonal N * D.val = antiDiagonal N ∧
      (∀ i j : Fin N, i ≠ j → ((w (e.symm i) / w (e.symm j))^s : Fˣ) ≠ 1) ∧
      (∀ A : SpecialLinearGroup (Fin N) F, ∀ i j,
        (D^s * A * (D^s)⁻¹).val i j =
          (((w (e.symm i) / w (e.symm j))^s : Fˣ) : F) * A.val i j) := by
  have hp : ∏ j, w (e.symm j) = 1 := by rw [e.symm.prod_comp]; exact hw
  refine ⟨diagonalSL (fun j => w (e.symm j)) hp, rfl, ?_, ?_,
    actual_powered_conjugation _ _ s⟩
  · apply diagonal_hermitian
    intro j
    have he : e.symm (Fin.revPerm j) = τ (e.symm j) := by
      apply e.injective
      simpa using (href (e.symm j)).symm
    rw [he]
    exact hunit (e.symm j)
  · intro i j hij
    exact hsep _ _ (fun h => hij (e.symm.injective h))

theorem regular_even_antidiagonal_torus (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F)
    (m s : ℕ) (hs : 0 < s)
    (hQ : 2*s*(m+2)^2+2 < Nat.card (fixedField ι)) :
    ∃ u : Fˣ, ∃ D : SpecialLinearGroup (Fin (2*(m+2))) F,
      D.val = diagonal (fun j => (pairedEntries ι (evenWeight m) u ((evenLabel (m+2)).symm j) : F)) ∧
      adjoint ι D.val * antiDiagonal (2*(m+2)) * D.val = antiDiagonal (2*(m+2)) ∧
      (∀ i j : Fin (2*(m+2)), i ≠ j →
        ((pairedEntries ι (evenWeight m) u ((evenLabel (m+2)).symm i) /
          pairedEntries ι (evenWeight m) u ((evenLabel (m+2)).symm j))^s : Fˣ) ≠ 1) ∧
      (∀ A : SpecialLinearGroup (Fin (2*(m+2))) F, ∀ i j,
        (D^s * A * (D^s)⁻¹).val i j =
          (((pairedEntries ι (evenWeight m) u ((evenLabel (m+2)).symm i) /
            pairedEntries ι (evenWeight m) u ((evenLabel (m+2)).symm j))^s : Fˣ) : F) * A.val i j) := by
  obtain ⟨u, _, _, _, hsep, _⟩ := regular_even_unitary_torus ι hinv hne m s hs hQ
  exact ⟨u, transport_antidiagonal_torus _ (evenLabel _) (pairSwap _)
    (evenLabel_reflection _) ι _ (by rw [prod_pairedEntries, evenWeight_sum, zpow_zero])
    (pairedEntries_hermitian ι hinv _ u) s hsep⟩

theorem regular_odd_antidiagonal_torus (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F)
    (d s : ℕ) (hd : 0 < d) (hs : 0 < s)
    (hQ : 2*s*(d+1)^2+2 < Nat.card (fixedField ι)) :
    ∃ u : Fˣ, ∃ D : SpecialLinearGroup (Fin (2*d+1)) F,
      D.val = diagonal (fun j => (oddEntries ι (positiveWeight d) u ((oddLabel d).symm j) : F)) ∧
      adjoint ι D.val * antiDiagonal (2*d+1) * D.val = antiDiagonal (2*d+1) ∧
      (∀ i j : Fin (2*d+1), i ≠ j →
        ((oddEntries ι (positiveWeight d) u ((oddLabel d).symm i) /
          oddEntries ι (positiveWeight d) u ((oddLabel d).symm j))^s : Fˣ) ≠ 1) ∧
      (∀ A : SpecialLinearGroup (Fin (2*d+1)) F, ∀ i j,
        (D^s * A * (D^s)⁻¹).val i j =
          (((oddEntries ι (positiveWeight d) u ((oddLabel d).symm i) /
            oddEntries ι (positiveWeight d) u ((oddLabel d).symm j))^s : Fˣ) : F) * A.val i j) := by
  obtain ⟨u, _, _, _, _, hsep, _⟩ := regular_odd_unitary_torus ι hinv hne d s hd hs hQ
  exact ⟨u, transport_antidiagonal_torus _ (oddLabel _) (oddSwap _)
    (oddLabel_reflection _) ι _ (prod_oddEntries _ _ _)
    (oddEntries_hermitian ι hinv _ u) s hsep⟩

end NikolovSegal.UnitaryField
