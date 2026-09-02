/- GID: D5/S3/Weil/ZetaBridge/SymmetricConvergentOfZetaSummable
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/SymmetricConvergentOfZetaSummable
   mirror-E: none(waiver:analytic-extraction-only)
   anchors: []
   digest: Frozen zeta-zero summability gives symmetric convergence for every enumeration. -/

import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaExplicit.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable

open Filter
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula

noncomputable section

/-- Every supplied enumeration of the nontrivial zeta zeros is symmetrically convergent for
every Weil test function. This is a moderate extraction of the already-frozen heavy analytic
result: Riemann-von Mangoldt counts and Fourier-Laplace decay are proved inside
`Zeta23.WeilEF`. It makes the `hZero` premise of O-6 derivable without changing O-6's
statement. -/
theorem symmetricConvergent_of_zeroData
    (Z : ZeroData) (g : WeilTestFunction) : SymmetricConvergent Z g := by
  obtain ⟨hsummable, _hsum⟩ :=
    Zeta23.WeilEF.EF_lit_zetaZeroConfig (g : ℝ → ℂ)
      (g.contDiff.of_le (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top))
      g.hasCompactSupport
  let setSubtypeEquiv : {rho : ℂ // Zeta23.IsNontrivialZero rho} ≃
      ↥{rho : ℂ | Zeta23.IsNontrivialZero rho} :=
    { toFun := fun rho => ⟨rho, rho.property⟩
      invFun := fun rho => ⟨rho, rho.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e := (zeroEquiv Z).trans setSubtypeEquiv
  let f : ↥{rho : ℂ | Zeta23.IsNontrivialZero rho} → ℂ := fun rho =>
    (Zeta23.zeroMult rho : ℂ) * Zeta23.paperFT (g : ℝ → ℂ) (Zeta23.gammaOf rho)
  let a : ℕ → ℂ := fun n => zeroSummand Z g n
  have hterm : ∀ n, f (e n) = a n := by
    intro n
    change (Zeta23.zeroMult (Z.zero n) : ℂ) *
        Zeta23.paperFT (g : ℝ → ℂ) (Zeta23.gammaOf (Z.zero n)) =
      (Z.multiplicity n : ℂ) * fourierLaplace g (Z.gamma n)
    rw [← multiplicity_eq_zeroMult Z n, paperFT_eq_fourierLaplace,
      gammaOf_eq_spectralParameter]
    rfl
  have ha : HasSum a (∑' rho, f rho) := by
    have hf : HasSum (f ∘ e) (∑' rho, f rho) :=
      e.hasSum_iff.mpr hsummable.hasSum
    exact hf.congr_fun fun n => (hterm n).symm
  refine ⟨∑' rho, f rho, ?_⟩
  have hcutoff : Tendsto (fun T : ℝ => ∑ n ∈ Z.symmetricIndices T, a n)
      atTop (nhds (∑' rho, f rho)) :=
    ha.comp (tendsto_symmetricIndices Z)
  simpa [truncatedZeroSum, a] using hcutoff

-- There are no explicit hypotheses; the empty conjunction is witnessable for all binders.
example (_Z : ZeroData) (_g : WeilTestFunction) : True := True.intro

-- The supplied zero-data domain is inhabited independently of the conclusion.
example (Z : ZeroData) : Nonempty ZeroData := ⟨Z⟩

-- The test-function domain has a closed canonical inhabitant.
example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

#print axioms symmetricConvergent_of_zeroData

end


end D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
