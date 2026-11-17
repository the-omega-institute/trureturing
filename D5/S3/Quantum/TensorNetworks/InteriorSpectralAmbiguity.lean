/- GID: D5/S3/Quantum/TensorNetworks/InteriorSpectralAmbiguity
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/InteriorSpectralAmbiguity
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Nonzero canonical REAL13 exclusion with the genuine native actual ambiguity consumer. -/

import D5.S3.Quantum.TensorNetworks.InteriorSpectralWitness
import D5.S3.Quantum.TensorNetworks.InteriorSpectralEnvironments
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Canonical exclusion and its observed finite-product consumer in the literal actual image. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Quantum.TensorNetworks.InteriorSpectralAmbiguity
open Matrix MvPolynomial
open scoped Matrix
open InteriorSpectralCertificate InteriorSpectralWitness
open OpenBoundaryMPSSpectralExtraction

/-- The literal nonzero lengthwise exclusion certificate has an actual native ambiguity consumer.
Every root e is covered, hence both physical square-root branches. -/
theorem canonical_exclusion_actual_ambiguity (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    P p q ≠ 0 ∧ ∀ (x : Fin 13 → ℝ) (e : ℂ),
      0 < OpenBoundaryMPSQ2PolynomialFiber.sigma x → eval x (P p q) ≠ 0 →
      e^2 = D (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) →
      ∃ φ : PeriodicMPSParentIntersection.Word ((p+2)+q) → ℂ,
        φ ∈ OpenBoundaryMPSMarginalBirationality.openBoundaryMPS ((p+2)+q) ∧ φ ≠ 0 ∧
        OpenBoundaryMPSInteriorCommonCore.rawInterior p 2 q φ =
          OpenBoundaryMPSInteriorCommonCore.rawInterior p 2 q
            (OpenBoundaryMPSMarginalBirationality.mpsState ((p+2)+q)
              (A (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) 0)
              (A (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) 1)
              (L (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x))
              ((Real.sqrt (OpenBoundaryMPSQ2PolynomialFiber.sigma x) : ℂ) •
                ![1,OpenBoundaryMPSQ2PolynomialFiber.eta x])) ∧
        ¬ ∃ η : ℂ, ‖η‖ = 1 ∧ φ = η •
          OpenBoundaryMPSMarginalBirationality.mpsState ((p+2)+q)
            (A (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) 0)
            (A (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) 1)
            (L (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x))
            ((Real.sqrt (OpenBoundaryMPSQ2PolynomialFiber.sigma x) : ℂ) •
              ![1,OpenBoundaryMPSQ2PolynomialFiber.eta x]) := by
  refine ⟨P_nonzero p q hp hq,?_⟩
  intro x e hsigma hP he
  obtain ⟨hc,hs,hb⟩ := certificate_native p q x e hsigma hP he
  obtain ⟨hl,hr⟩ := InteriorSpectralEnvironments.certificate_positive_targets
    p q hp hq x e hsigma hP he
  exact canonical_actual_ambiguity_of_native p q hp hq x e
    ((Real.sqrt (OpenBoundaryMPSQ2PolynomialFiber.sigma x) : ℂ) •
      ![1,OpenBoundaryMPSQ2PolynomialFiber.eta x]) hc hs hl hr hb


open scoped BigOperators
open PeriodicMPSParentIntersection (Word)
open OpenBoundaryMPSQ2PolynomialFiber
open OpenBoundaryMPSIntrinsicQ2Fiber
open OpenBoundaryMPSInteriorGenericity
open OpenBoundaryMPSMarginalBirationality
open OpenBoundaryMPSDensityRecovery
open OpenBoundaryMPSDensityGenericity
open OpenBoundaryMPSQuotient hiding coreCoordinates
open OpenBoundaryMPSTwoSiteMinimality (state)
open OpenBoundaryMPSInteriorCommonCore (rawInterior)

set_option maxHeartbeats 1200000 in
/-- One literal observed polynomial serves every interior two-site window at each fixed
length. Genericity is relative to the entire actual image; only the target is restricted.
The nonzero nonphase competitor can depend on the window. -/
theorem observed_interior_ambiguity (m : ℕ) (hm : 1 ≤ m) :
    ∃ R : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ, R ≠ 0 ∧
      (actualPrincipalLocus m R).Nonempty ∧ IsOpen (actualPrincipalLocus m R) ∧
      Dense (actualPrincipalLocus m R) ∧
      (∀ (ψ : openBoundaryMPS (3 + m)) (z : ℂ), ‖z‖ = 1 →
        ∃ hz : z • (ψ : Word (3 + m) → ℂ) ∈ openBoundaryMPS (3 + m),
          (⟨z • (ψ : Word (3 + m) → ℂ), hz⟩ ∈ actualPrincipalLocus m R ↔
            ψ ∈ actualPrincipalLocus m R)) ∧
      ∀ ψ : openBoundaryMPS (3 + m), ψ ∈ actualPrincipalLocus m R →
        ∀ p q : ℕ, 1 ≤ p → 1 ≤ q → p + q = m + 1 →
          ∀ h : ((p + 2) + q) = 3 + m,
            ∃ φ : openBoundaryMPS (3 + m), (φ : Word (3 + m) → ℂ) ≠ 0 ∧
              rawInterior p 2 q (castState h φ) = rawInterior p 2 q (castState h ψ) ∧
              ¬ ∃ η : ℂ, ‖η‖ = 1 ∧
                (φ : Word (3 + m) → ℂ) = η • (ψ : Word (3 + m) → ℂ) := by
  let Pi : Fin m → RealPoly := fun i => P (i.val + 1) (m - i.val)
  have hPi : ∀ i, Pi i ≠ 0 := by
    intro i
    exact (canonical_exclusion_actual_ambiguity (i.val + 1) (m - i.val)
      (by omega) (by omega)).1
  choose H B hclear using fun i : Fin m =>
    clear_polynomial (Pi i) (quotientNumeratorFamily m) (quotientDenominatorFamily m)
  let Pprod : RealPoly := ∏ i : Fin m, Pi i
  have hPprod : Pprod ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hPi i)
  have hw : ∃ a : Coordinates, eval a Pprod ≠ 0 := by
    by_contra hn
    apply hPprod
    apply MvPolynomial.funext
    intro a
    simpa using not_not.mp (not_exists.mp hn a)
  obtain ⟨a, ha⟩ := hw
  obtain ⟨x, hxDom, hxP⟩ := (polynomial_nonzero_dense Pprod a ha).inter_open_nonempty _
    (quotientValidityDomain_open m) (quotientValidityDomain_nonempty m)
  change eval x Pprod ≠ 0 at hxP
  have hxPi : ∀ i, eval x (Pi i) ≠ 0 := by
    have hh : (∏ i : Fin m, eval x (Pi i)) ≠ 0 := by simpa [Pprod] using hxP
    exact fun i => Finset.prod_ne_zero_iff.mp hh i (Finset.mem_univ i)
  let Qx := quotientRawPrefix m x
  let ax := realCoordinates (fun ij : ObsIndex => Qx ij.1 ij.2)
  have hρx : eval ax (quotientLocusPolynomial m) ≠ 0 := hxDom.2.1
  have hratx : (fun j => eval ax (quotientNumeratorFamily m j) /
      eval ax (quotientDenominatorFamily m j)) = x := by
    change (fun j => eval ax (quotientRealNumerator m (quotientIndexEquiv.symm j)) /
      eval ax (quotientRealDenominator m (quotientIndexEquiv.symm j))) = x
    rw [funext (quotientCoordinate_ratio m Qx hρx)]
    exact quotientCoordinates_retraction_local m x hxDom.1 hρx
  have hHx : ∀ i, eval ax (H i) ≠ 0 := by
    intro i
    have hc := hclear i ax (quotient_denominators_nonzero m Qx hρx)
    rw [hratx] at hc
    intro hh
    exact hxPi i (by simpa [hh] using hc.2)
  let R := quotientLocusPolynomial m * ∏ i : Fin m, H i
  have hRx : eval ax R ≠ 0 := by
    simpa [R] using mul_ne_zero hρx
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hHx i))
  have hR : R ≠ 0 := by
    intro hh
    simp [hh] at hRx
  let ψx : openBoundaryMPS (3 + m) :=
    ⟨state (3 + m) (positiveRepresentative x), ⟨_, _, _, _, rfl⟩⟩
  have hgeneric := actual_principal_genericity m R ⟨ψx, hRx⟩
  refine ⟨R, hR, hgeneric.1, hgeneric.2.1, hgeneric.2.2, ?_, ?_⟩
  · intro ψ z hz
    exact ⟨actual_phase _ ψ z, locus_phase m R ψ z hz⟩
  · intro ψ hψ p q hp hq hpq h
    let Q := rawPrefix 3 m (ψ : Word (3 + m) → ℂ)
    let y := realCoordinates (fun ij : ObsIndex => Q ij.1 ij.2)
    have hparts : eval y (quotientLocusPolynomial m) ≠ 0 ∧
        (∏ i : Fin m, eval y (H i)) ≠ 0 := by
      simpa only [actualPrincipalLocus, Set.mem_ofPred_eq, R, map_mul, map_prod,
        mul_ne_zero_iff] using hψ
    have hρ := hparts.1
    let pθ := quotientCoordinates m Q
    let x := quotientCoordinates13 pθ
    let θ := positiveRepresentative x
    have hg := ((quotientLocus_eval m Q).mp hρ).1
    have h00 := (rational_quotient_inverse m Q hρ).2.2.2.2.2
    obtain ⟨hpσ, z₀, hz₀, hrep₀⟩ := actual_quotient_representative m ψ ψ.property hg h00
    have hσ : 0 < sigma x := by
      change 0 < quotientRealCoordinates pθ (quotientIndexEquiv.symm 10)
      have hi : quotientIndexEquiv.symm 10 = Sum.inr (Sum.inr 0) := by decide
      simpa [hi, quotientRealCoordinates] using hpσ
    have hθ := quotientCoordinates_positiveRepresentative pθ hpσ
    have hrep : (ψ : Word (3 + m) → ℂ) = z₀ • state (3 + m) θ := by
      dsimp [θ, x]
      rw [hθ]
      exact hrep₀
    let i : Fin m := ⟨p - 1, by omega⟩
    have hip : i.val + 1 = p := by dsimp [i]; omega
    have hiq : m - i.val = q := by dsimp [i]; omega
    have hrat : (fun j => eval y (quotientNumeratorFamily m j) /
        eval y (quotientDenominatorFamily m j)) = x :=
      funext (quotientCoordinate_ratio m Q hρ)
    have hc := hclear i y (quotient_denominators_nonzero m Q hρ)
    rw [hrat] at hc
    have hPx : eval x (P p q) ≠ 0 := by
      have hiH := Finset.prod_ne_zero_iff.mp hparts.2 i (Finset.mem_univ i)
      have hiP : eval x (Pi i) ≠ 0 := by rw [hc.2]; exact div_ne_zero hiH hc.1
      simpa only [Pi, hip, hiq] using hiP
    obtain ⟨e, he⟩ := IsAlgClosed.exists_pow_nat_eq (D (coreCoordinates x)) (by decide : 0 < 2)
    obtain ⟨χ, hχ, hχne, hraw, hnonphase⟩ :=
      (canonical_exclusion_actual_ambiguity p q hp hq).2 x e hσ hPx he
    have hstate : mpsState ((p + 2) + q) (A (coreCoordinates x) 0)
        (A (coreCoordinates x) 1) (L (coreCoordinates x))
        ((Real.sqrt (sigma x) : ℂ) • ![1, eta x]) =
        state ((p + 2) + q) θ := by
      congr 1
      ext j
      fin_cases j <;> simp [θ, positiveRepresentative, OpenBoundaryMPSTwoSiteMinimality.right]
    rw [hstate] at hraw hnonphase
    let χ' := castState h.symm χ
    have hχ' : χ' ∈ openBoundaryMPS (3 + m) := by
      obtain ⟨a, b, l, r, hr⟩ := hχ
      refine ⟨a, b, l, r, ?_⟩
      dsimp [χ']
      rw [hr, cast_mps]
    let χactual : openBoundaryMPS (3 + m) := ⟨χ', hχ'⟩
    let φ : openBoundaryMPS (3 + m) := ⟨z₀ • χ', actual_phase _ χactual z₀⟩
    have hz₀ne : z₀ ≠ 0 := by intro hz; simp [hz] at hz₀
    have hcast : castState h χ' = χ := by
      dsimp only [χ']
      funext w
      change χ (fun j => w (Fin.cast h.symm (Fin.cast h j))) = χ w
      apply congrArg χ
      funext j
      exact congrArg w (Fin.ext rfl)
    have hcaststate : castState h (state (3 + m) θ) = state ((p + 2) + q) θ :=
      cast_mps h _ _ _ _
    refine ⟨φ, ?_, ?_, ?_⟩
    · intro hzero
      have hzero' : z₀ • χ' = z₀ • (0 : Word (3 + m) → ℂ) := by simpa [φ] using hzero
      have hc0 : χ' = 0 := (smul_right_inj hz₀ne).mp hzero'
      apply hχne
      rw [← hcast, hc0]
      rfl
    · change rawInterior p 2 q (z₀ • castState h χ') = _
      rw [rawInterior_phase _ _ _ _ _ hz₀, hcast, hraw, hrep]
      change _ = rawInterior p 2 q (z₀ • castState h (state (3 + m) θ))
      rw [rawInterior_phase _ _ _ _ _ hz₀, hcaststate]
    · rintro ⟨η, hη, heq⟩
      apply hnonphase
      refine ⟨η, hη, ?_⟩
      have heq' : z₀ • χ' = z₀ • (η • state (3 + m) θ) := by
        change z₀ • χ' = η • (ψ : Word (3 + m) → ℂ) at heq
        rw [hrep, smul_comm] at heq
        exact heq
      have hχeq := (smul_right_inj hz₀ne).mp heq'
      have hh := congrArg (castState h) hχeq
      change castState h χ' = η • castState h (state (3 + m) θ) at hh
      rwa [hcast, hcaststate] at hh

end D5.S3.Quantum.TensorNetworks.InteriorSpectralAmbiguity
