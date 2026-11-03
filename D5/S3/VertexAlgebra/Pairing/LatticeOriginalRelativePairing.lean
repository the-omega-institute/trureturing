/- GID: D5/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Pairing/LatticeOriginalRelativePairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original all-charge relative tensor pairing with arbitrary complex transverse basis and signed-degree selection. -/

import D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian
import D5.S3.VertexAlgebra.Lattice.LatticeRealNullFrame
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration
import D5.S3.Quantum.Fermionic.BcGhostHermitian
import D5.S3.VertexAlgebra.Pairing.FiniteDegreePairing
import Mathlib.Tactic

/-! The original all-integral-charge Carrier tensor occupation Fock pairing.
The only reality hypotheses are on the two longitudinal vectors; the transverse
basis is an arbitrary complex basis of the actual orthogonal complement. The
source uses the canonical frame-free `OriginalMatterHermitian.Hm` and the
signed ghost Hermitian form, with the literal c0 insertion.

The full-telescope escape audit remains unfinished for the public declarations
in this source; issue https://github.com/the-omega-institute/trureturing/issues/25857
discloses the missing realization, exact reconstruction, lawful template,
whole-family variation, sensitivity and observational-dependence evidence.
This is not a validated registration. The full BRST/HPL/no-ghost programme
remains outside this result. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.LatticeOriginalRelativePairing

open LatticeGeneratingFieldLocality LatticeLightConeCoordinates
open LatticeLightConeCoordinates.NullFrame LatticeQuartetContraction
open LatticeBRSTModeFiltration LatticeInvolution MvPolynomial
open SourceBPZ.OriginalSourcePairing
open SourceBPZ.OriginalMatterHermitian
open LatticeRealNullFrame (conjugateVector conjugate_gram)
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostCharge (charge siteSign)
open private charge_erase from D5.S3.Quantum.Fermionic.BcGhostCharge
open D5.S3.Quantum.Fermionic.BcGhostHermitian
open private wick_constant_left from
  D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick
open private actualBasis_apply from
  D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
open private coordinateDerivative_X from
  D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates

variable {D : LatticeData}

def matterForm : Carrier D →ₗ⋆[ℂ] Carrier D →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun := Hm x
      map_add' := fun y z => Hm_add_right x y z
      map_smul' := fun a y => Hm_smul_right a x y }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact Hm_add_left x y z
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    exact Hm_smul_left a x y

@[simp] theorem matterForm_apply (x y : Carrier D) : matterForm x y = Hm x y := by rfl

theorem Hm_single (p q : Charge D) (P Q : Oscillator D) :
    Hm (Finsupp.single p P) (Finsupp.single q Q) =
      if p = q then integerWick D (sigma D (kappaOsc P)) Q else 0 := by
  unfold Hm
  change sourcePairing D (thetaLinear D (kappaCarrier (Finsupp.single p P)))
      (Finsupp.single q Q) = _
  rw [kappaCarrier_single, theta_single,
    sourcePairing_single_single]
  by_cases hpq : p = q <;> simp [hpq, eq_comm]

private theorem integerWick_one_left (Q : Oscillator D) :
    integerWick D 1 Q = Q.coeff 0 := by
  rw [integerWick_apply, map_one]
  change SignedOscillatorWick.wick D (C 1) Q = Q.coeff 0
  rw [wick_constant_left, one_mul]

/-- Every integral momentum has the same ground norm one, including p=0. -/
theorem Hm_ground (p q : Charge D) :
    Hm (Finsupp.single p (1 : Oscillator D)) (Finsupp.single q 1) =
      if p = q then 1 else 0 := by
  rw [Hm_single]
  split_ifs
  · simpa [kappaOsc, sigma] using (integerWick_one_left (D := D) (1 : Oscillator D))
  · simp

variable (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
variable (hPlus : conjugateVector F.ePlus = F.ePlus)
variable (hMinus : conjugateVector F.eMinus = F.eMinus)

include hPlus hMinus
/-- Reality is imposed on the longitudinal frame, never on B. -/
def conjugateK (v : F.K) : F.K :=
  ⟨conjugateVector (v : E D), by
    change g D F.ePlus (conjugateVector (v : E D)) = 0 ∧
      g D F.eMinus (conjugateVector (v : E D)) = 0
    have hp := conjugate_gram D F.ePlus (v : E D)
    have hm := conjugate_gram D F.eMinus (v : E D)
    rw [hPlus] at hp
    rw [hMinus] at hm
    have hvp : g D F.ePlus (v : E D) = 0 := v.property.1
    have hvm : g D F.eMinus (v : E D) = 0 := v.property.2
    have hp0 : star (g D F.ePlus (v : E D)) = 0 := by simp [hvp]
    have hm0 : star (g D F.eMinus (v : E D)) = 0 := by simp [hvm]
    exact ⟨by rw [← hp, hp0], by rw [← hm, hm0]⟩⟩

/-- Actual original-coordinate transport of conjugation in an arbitrary B. -/
theorem conjugateK_expansion (v : F.K) :
    conjugateVector (v : E D) =
      ∑ j : Fin t, B.repr (conjugateK F hPlus hMinus v) j • (B j : E D) := by
  change conjugateVector (v : E D) =
    ∑ j : Fin t, B.repr (conjugateK F hPlus hMinus v) j • (B j : E D)
  have hv : (conjugateK F hPlus hMinus v : E D) = conjugateVector (v : E D) := rfl
  rw [← hv]
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using
    (congrArg Subtype.val (B.sum_repr (conjugateK F hPlus hMinus v))).symm

omit hPlus hMinus

def direction (l : Label t) : E D := F.completeBasis B l

@[simp] theorem direction_plus : direction F B (plus t) = F.ePlus := by
  simp [direction]
@[simp] theorem direction_minus : direction F B (minus t) = F.eMinus := by
  simp [direction]
@[simp] theorem direction_transverse (j : Fin t) :
    direction F B (transverse t j) = (B j : E D) := by simp [direction]

@[simp] theorem direction_inl :
    direction F B (Sum.inl () : Label t) = F.ePlus := by
  simpa [plus] using (direction_plus F B)

@[simp] theorem direction_inr_inl :
    direction F B (Sum.inr (Sum.inl ()) : Label t) = F.eMinus := by
  simpa [minus] using (direction_minus F B)

@[simp] theorem direction_inr_inr (j : Fin t) :
    direction F B (Sum.inr (Sum.inr j) : Label t) = (B j : E D) := by
  simpa [transverse] using (direction_transverse F B j)

/-- The existing inverse coordinate equivalence, not a second substitution. -/
def phi : PolynomialCoordinates (Label t) →ₐ[ℂ] Oscillator D :=
  (F.coordinateEquiv B).symm.toAlgHom

@[simp] theorem phi_X (l : Label t) (r : ℕ) :
    phi F B (X (l,r)) = lin r (direction F B l) := by
  simp [phi, direction]

theorem kappa_lin (u : E D) (r : ℕ) :
    kappaOsc (lin r u) = lin r (conjugateVector u) := by
  simp [lin, kappaOsc, conjugateVector, map_sum, map_smul, smul_eq_C_mul]

theorem sigma_lin (u : E D) (r : ℕ) : sigma D (lin r u) = -lin r u := by
  simp [lin, map_sum, sigma_smul, Finset.sum_neg_distrib]

include hPlus hMinus
/-- This is generally a MIXTURE of transverse generators, not a fixed X_j. -/
theorem kappa_phi_transverse (j : Fin t) (r : ℕ) :
    kappaOsc (phi F B (X (transverse t j,r))) =
      ∑ k : Fin t, B.repr (conjugateK F hPlus hMinus (B j)) k •
        phi F B (X (transverse t k,r)) := by
  rw [phi_X, direction_transverse, kappa_lin,
    conjugateK_expansion F B hPlus hMinus (B j)]
  simp only [phi_X, direction_transverse, lin, Finset.sum_apply,
    Finset.sum_smul, Finset.smul_sum, smul_smul, map_sum, map_smul]

include hPlus hMinus
/-- Both longitudinal directions are fixed. The transverse case explicitly
uses the transported conjugation expansion above. -/
theorem kappa_phi_X (l : Label t) (r : ℕ) :
    kappaOsc (phi F B (X (l,r))) = lin r (conjugateVector (direction F B l)) := by
  rcases l with u | (u | j)
  · cases u
    rw [phi_X]
    simp [direction, plus, kappa_lin, hPlus]
  · cases u
    rw [phi_X]
    simp [direction, minus, kappa_lin, hMinus]
  · change kappaOsc (phi F B (X (transverse t j,r))) =
      lin r (conjugateVector (direction F B (transverse t j)))
    rw [kappa_phi_transverse F B hPlus hMinus]
    rw [direction_transverse, conjugateK_expansion F B hPlus hMinus (B j)]
    simp only [phi_X, direction_transverse, lin, Finset.sum_apply,
      Finset.sum_smul, Finset.smul_sum, smul_smul, map_sum, map_smul]

omit hPlus hMinus

theorem phi_constant (P : PolynomialCoordinates (Label t)) :
    (phi F B P).coeff 0 = P.coeff 0 := by
  change MvPolynomial.constantCoeff (phi F B P) = MvPolynomial.constantCoeff P
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P x hP =>
    rcases x with ⟨l,r⟩
    rw [map_mul, phi_X]
    simp [lin, MvPolynomial.coeff_mul_X']

/-- The original Gram directional derivative, before coordinate transport. -/
def originalDerivative (u : E D) (r : ℕ) : Derivation ℂ (Oscillator D) (Oscillator D) :=
  LatticeLightConeCoordinates.oldDerivative u r

/-- The same derivative in the actual complete basis. r is retained literally. -/
def coordinateDerivative (u : E D) (r : ℕ) :
    Derivation ℂ (PolynomialCoordinates (Label t)) (PolynomialCoordinates (Label t)) :=
  LatticeLightConeCoordinates.coordinateDerivative (F.completeBasis B) u r

theorem originalDerivative_apply (u : E D) (r : ℕ) (Q : Oscillator D) :
    originalDerivative u r Q = ∑ i : Fin D.rank,
      u i • LatticeActualAnnihilation.annihilate D i r Q := by
  change (Derivation.coeFnAddMonoidHom
    (∑ i : Fin D.rank, u i • LatticeActualAnnihilation.annihilationDerivation D i r)) Q = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
    Derivation.coe_smul, Pi.smul_apply, LatticeActualAnnihilation.annihilation_apply]

theorem coordinateDerivative_apply (u : E D) (r : ℕ)
    (Q : PolynomialCoordinates (Label t)) :
    coordinateDerivative F B u r Q = ∑ l : Label t,
      g D u (direction F B l) • pderiv (l,r) Q := by
  change (Derivation.coeFnAddMonoidHom
    (∑ l : Label t, g D u (F.completeBasis B l) • pderiv (l,r))) Q = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
    Derivation.coe_smul, Pi.smul_apply]
  rfl

theorem originalDerivative_lin (u v : E D) (r s : ℕ) :
    originalDerivative u r (lin s v) =
      if r = s then (g D u v) • (1 : Oscillator D) else 0 := by
  exact LatticeLightConeCoordinates.oldDerivative_lin u v r s

theorem derivative_transport (u : E D) (r : ℕ)
    (Q : PolynomialCoordinates (Label t)) :
    originalDerivative u r (phi F B Q) = phi F B (coordinateDerivative F B u r Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C c => simp [originalDerivative, coordinateDerivative]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X Q x hQ =>
    rcases x with ⟨l,s⟩
    have hx : originalDerivative u r (phi F B (X (l,s))) =
        phi F B (coordinateDerivative F B u r (X (l,s))) := by
      rw [phi_X, originalDerivative_lin]
      by_cases hrs : r = s
      · subst s
        rw [coordinateDerivative, coordinateDerivative_X]
        simp [phi, direction]
      · rw [coordinateDerivative, coordinateDerivative_X]
        simp [hrs, phi, direction]
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hQ, hx]

theorem integerWick_lin_creation (u : E D) (r : ℕ) (P Q : Oscillator D) :
    integerWick D (lin r u * P) Q =
      integerWick D P (-((r : ℂ)+1) • originalDerivative u r Q) := by
  classical
  change integerWick D ((∑ i : Fin D.rank, u i • X (i,r)) * P) Q = _
  rw [Finset.sum_mul, map_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_mul_assoc,
    map_smul, integerWick_creation, originalDerivative_apply,
    Finset.smul_sum, smul_smul]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]
  ring

def oscillatorForm (P Q : PolynomialCoordinates (Label t)) : ℂ :=
  integerWick D (sigma D (kappaOsc (phi F B P))) (phi F B Q)

/-- Contraction at frequency r+1, with the original Hermitian conjugation. -/
def contraction (x : Variables t) : Module.End ℂ (PolynomialCoordinates (Label t)) :=
  ((x.2 : ℂ)+1) •
    (coordinateDerivative F B (conjugateVector (direction F B x.1)) x.2).toLinearMap

include hPlus hMinus
/-- The reflection minus and the original signed Wick minus cancel. -/
theorem oscillator_creation (x : Variables t) (P Q : PolynomialCoordinates (Label t)) :
    oscillatorForm F B (X x * P) Q =
      oscillatorForm F B P (contraction F B x Q) := by
  rcases x with ⟨l,r⟩
  unfold oscillatorForm
  rw [map_mul, show kappaOsc (phi F B (X (l,r)) * phi F B P) =
      kappaOsc (phi F B (X (l,r))) * kappaOsc (phi F B P) by
    simp [kappaOsc, map_mul]]
  rw [kappa_phi_X F B hPlus hMinus, map_mul, sigma_lin,
    neg_mul, map_neg, LinearMap.neg_apply, integerWick_lin_creation]
  rw [derivative_transport F B]
  simp [contraction, map_smul] <;> ring

omit hPlus hMinus
theorem oscillator_one_left (Q : PolynomialCoordinates (Label t)) :
    oscillatorForm F B 1 Q = Q.coeff 0 := by
  unfold oscillatorForm
  have h1 : phi F B (1 : PolynomialCoordinates (Label t)) = 1 := by
    simp [phi]
  rw [h1, show kappaOsc (1 : Oscillator D) = 1 by simp [kappaOsc],
    show sigma D (1 : Oscillator D) = 1 by simp [sigma]]
  rw [integerWick_one_left]
  exact phi_constant F B Q

theorem oscillator_right_expansion (P Q : PolynomialCoordinates (Label t)) :
    oscillatorForm F B P Q = ∑ m ∈ Q.support,
      Q.coeff m * oscillatorForm F B P (monomial m 1) := by
  classical
  have hm (m : Exponents t) : monomial m (Q.coeff m) =
      Q.coeff m • monomial m (1 : ℂ) := by
    simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      using (Eq.refl (monomial m (Q.coeff m)))
  conv_lhs => rw [Q.as_sum]
  simp [oscillatorForm, hm, map_sum, map_smul]

include hPlus hMinus
/-- Exact same-frequency one-particle contraction from the original recursion. -/
theorem oscillator_X_X (l k : Label t) (r s : ℕ) :
    oscillatorForm F B (X (l,r)) (X (k,s)) =
      if r = s then ((r : ℂ)+1) *
        g D (conjugateVector (direction F B l)) (direction F B k) else 0 := by
  have he := oscillator_creation F B hPlus hMinus (l,r) 1 (X (k,s))
  simp only [mul_one] at he
  rw [he, oscillator_one_left]
  by_cases hrs : r = s
  · subst s
    simp [contraction, coordinateDerivative, coordinateDerivative_X,
      MvPolynomial.pderiv_X, direction]
  · simp [contraction, coordinateDerivative, coordinateDerivative_X, hrs,
      MvPolynomial.pderiv_X, direction]

include hPlus hMinus
/-- The complete Gram sparsity needed by the Wick induction. In the transverse
case conjugation is proved to remain in K and is expanded through B. -/
theorem gram_weight_selection (l k : Label t) (r s : ℕ)
    (hbad : variableWeight (l,r) + variableWeight (k,s) ≠ 0) :
    g D (conjugateVector (direction F B l)) (direction F B k) = 0 := by
  have hK (j : Fin t) :
      g D (conjugateVector (B j : E D)) F.ePlus = 0 ∧
      g D (conjugateVector (B j : E D)) F.eMinus = 0 := by
    have hk := (conjugateK F hPlus hMinus (B j)).property
    exact ⟨(g_symm D _ _).trans hk.1, (g_symm D _ _).trans hk.2⟩
  rcases l with u | (u | j)
  · cases u
    simp only [direction_inl]
    rcases k with v | (v | k)
    · cases v
      simp only [direction_inl]
      change g D (conjugateVector F.ePlus) F.ePlus = 0
      rw [hPlus]
      exact F.plus_null
    · cases v
      simp only [direction_inr_inl]
      exact False.elim (hbad (by simp [variableWeight, plus, minus, transverse]))
    · simp only [direction_inr_inr]
      change g D (conjugateVector F.ePlus) (B k : E D) = 0
      rw [hPlus]
      exact (B k).property.1
  · cases u
    simp only [direction_inr_inl]
    rcases k with v | (v | k)
    · cases v
      simp only [direction_inl]
      exact False.elim (hbad (by simp [variableWeight, plus, minus, transverse]))
    · cases v
      simp only [direction_inr_inl]
      change g D (conjugateVector F.eMinus) F.eMinus = 0
      rw [hMinus]
      exact F.minus_null
    · simp only [direction_inr_inr]
      change g D (conjugateVector F.eMinus) (B k : E D) = 0
      rw [hMinus]
      exact (B k).property.2
  · simp only [direction_inr_inr]
    rcases k with v | (v | k)
    · cases v
      simp only [direction_inl]
      change g D (conjugateVector (B j : E D)) F.ePlus = 0
      exact (hK j).1
    · cases v
      simp only [direction_inr_inl]
      change g D (conjugateVector (B j : E D)) F.eMinus = 0
      exact (hK j).2
    · simp only [direction_inr_inr]
      exact False.elim (hbad (by simp [variableWeight, plus, minus, transverse]))

/-- Extract a real derivative contribution from the finite coordinate sum. -/
theorem contraction_support (x : Variables t) (m n : Exponents t)
    (hc : (contraction F B x (monomial m 1)).coeff n ≠ 0) :
    exponentDegree n = exponentDegree m + variableWeight x := by
  classical
  have hs : (∑ l : Label t,
      (((x.2 : ℂ)+1) * g D (conjugateVector (direction F B x.1)) (direction F B l)) *
        (pderiv (l,x.2) (monomial m (1 : ℂ))).coeff n) ≠ 0 := by
    simpa [contraction, coordinateDerivative_apply,
      Finset.mul_sum, mul_assoc] using hc
  obtain ⟨l, hl, hcon⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  have hg : g D (conjugateVector (direction F B x.1)) (direction F B l) ≠ 0 := by
    intro hz
    apply hcon
    rw [hz]
    simp
  have hd : (pderiv (l,x.2) (monomial m (1 : ℂ))).coeff n ≠ 0 := by
    intro hz
    apply hcon
    rw [hz]
    simp
  have hw : variableWeight x + variableWeight (l,x.2) = 0 := by
    by_contra hw
    exact hg (gram_weight_selection F B hPlus hMinus x.1 l x.2 x.2 hw)
  have he := derivative_support_degree (l,x.2) m n hd
  omega

/-- Wick induction on EVERY exponent, including all transverse occupations.
No monomial-pairing premise is supplied. -/
theorem oscillator_monomial_selection (m n : Exponents t)
    (hmn : exponentDegree m + exponentDegree n ≠ 0) :
    oscillatorForm F B (monomial m 1) (monomial n 1) = 0 := by
  classical
  have step (m : Exponents t)
      (ih : ∀ n, exponentDegree m + exponentDegree n ≠ 0 →
        oscillatorForm F B (monomial m 1) (monomial n 1) = 0)
      (x : Variables t) :
      ∀ n, exponentDegree (Finsupp.single x 1 + m) + exponentDegree n ≠ 0 →
        oscillatorForm F B (monomial (Finsupp.single x 1 + m) 1) (monomial n 1) = 0 := by
    intro n hn
    rw [← X_mul_monomial x m (1 : ℂ), oscillator_creation F B hPlus hMinus,
      oscillator_right_expansion]
    apply Finset.sum_eq_zero
    intro k hk
    have hdeg := contraction_support F B hPlus hMinus x n k
      (MvPolynomial.mem_support_iff.mp hk)
    have hmk : exponentDegree m + exponentDegree k ≠ 0 := by
      norm_num [exponentDegree_add, exponentDegree_single] at hn
      omega
    rw [ih k hmk, mul_zero]
  have all : ∀ m : Exponents t, ∀ n,
      exponentDegree m + exponentDegree n ≠ 0 →
        oscillatorForm F B (monomial m 1) (monomial n 1) = 0 := by
    intro m
    refine m.induction ?_ ?_
    · intro n hn
      rw [show monomial (0 : Exponents t) (1 : ℂ) = 1 by simp,
        oscillator_one_left]
      have hn0 : n ≠ 0 := by
        intro hz
        subst n
        exact hn (by simp [exponentDegree])
      simp [coeff_monomial, hn0, Ne.symm hn0]
    · intro x k m hx hk hm
      have hp : ∀ a : ℕ, ∀ n,
          exponentDegree (Finsupp.single x a + m) + exponentDegree n ≠ 0 →
            oscillatorForm F B (monomial (Finsupp.single x a + m) 1) (monomial n 1) = 0 := by
        intro a
        induction a with
        | zero => simpa using hm
        | succ a ha =>
          simpa [Finsupp.single_add, add_assoc, add_comm, add_left_comm] using
            step (Finsupp.single x a + m) ha x
      simpa [add_comm, add_left_comm, add_assoc] using hp k
  exact all m n hmn

theorem matter_basis_selection (p q : Charge D) (m n : Exponents t)
    (hmn : exponentDegree m + exponentDegree n ≠ 0) :
    Hm (Finsupp.single p (phi F B (monomial m 1)))
      (Finsupp.single q (phi F B (monomial n 1))) = 0 := by
  rw [Hm_single]
  split_ifs
  · exact oscillator_monomial_selection F B hPlus hMinus m n hmn
  · rfl

omit hPlus hMinus

/- The original signed ghost form. No positive occupation dot product. -/
def ghostForm : Fock →ₗ⋆[ℂ] Fock →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun := Hg x
      map_add' := D5.S3.Quantum.Fermionic.BcGhostHermitian.Hg_add_right x
      map_smul' := fun a y => D5.S3.Quantum.Fermionic.BcGhostHermitian.Hg_smul_right a x y }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact D5.S3.Quantum.Fermionic.BcGhostHermitian.Hg_add_left x y z
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    exact D5.S3.Quantum.Fermionic.BcGhostHermitian.Hg_smul_left a x y

/-- The original row sign and the c0 Jordan--Wigner phase are both retained. -/
theorem ghost_relative_signed (S T : Finset ℕ) :
    Hg (ket S) (c 0 (ket T)) =
      D5.S3.Quantum.Fermionic.BcGhostHermitian.eps S *
        if 3 ∈ D5.S3.Quantum.Fermionic.BcGhostHermitian.partner S then
          phase 3 (D5.S3.Quantum.Fermionic.BcGhostHermitian.partner S) *
            if T = (D5.S3.Quantum.Fermionic.BcGhostHermitian.partner S).erase 3 then 1 else 0
        else 0 := by
  classical
  rw [D5.S3.Quantum.Fermionic.BcGhostHermitian.Hg_ket_coefficient,
    D5.S3.Quantum.Fermionic.BcGhostHermitian.c_zero,
    D5.S3.Quantum.Fermionic.BcGhostHermitian.create_coefficient]
  simp [ket, Finsupp.single_apply]

/-- Derive ghost charge sum TWO from the literal signed coefficient and c0.
This even holds on the ambient occupation basis, before restricting ker b0. -/
theorem ghost_relative_nonzero (S T : Finset ℕ)
    (hST : Hg (ket S) (c 0 (ket T)) ≠ 0) : charge S + charge T = 2 := by
  classical
  let U := D5.S3.Quantum.Fermionic.BcGhostHermitian.partner S
  rw [ghost_relative_signed] at hST
  have h3 : 3 ∈ U := by
    by_contra h3
    dsimp only [U] at h3
    exact hST (by simp [h3])
  have hTU : T = U.erase 3 := by
    by_contra he
    dsimp only [U] at h3 he
    exact hST (by simp [h3, he])
  have hp := D5.S3.Quantum.Fermionic.BcGhostHermitian.charge_partner S
  have he := charge_erase 3 U h3
  dsimp only [U] at he
  rw [hTU]
  change charge S + charge ((partner S).erase 3) = 2
  rw [he]
  have hs3 : siteSign 3 = 1 := by norm_num [siteSign]
  rw [hs3]
  omega

private def rightTensor (x : Carrier D) (s : Fock) : State D →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    { toFun := fun y => (matterForm x y) • ghostForm s
      map_add' := by intro y z; simp only [map_add, add_smul]
      map_smul' := by
        intro a y
        simp only [map_smul, smul_smul, smul_eq_mul]
        simp only [RingHom.id_apply] }

@[simp] private theorem rightTensor_tmul (x y : Carrier D) (s t : Fock) :
    rightTensor x s (y ⊗ₜ[ℂ] t) = matterForm x y * ghostForm s t := by
  simp [rightTensor]

/-- Constructed by the tensor universal property from the ORIGINAL Hm and Hg. -/
def totalForm : State D →ₗ⋆[ℂ] State D →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun s => rightTensor x s
          map_add' := by
            intro s t
            apply LinearMap.ext
            intro z
            induction z using TensorProduct.induction_on with
            | zero => simp
            | tmul y v => simp [rightTensor_tmul, map_add, add_mul] <;> ring
            | add z w hz hw => simp [map_add, hz, hw] <;> ring
          map_smul' := by
            intro a s
            apply LinearMap.ext
            intro z
            induction z using TensorProduct.induction_on with
            | zero => simp
            | tmul y v => simp [rightTensor_tmul, Hg_smul_right, smul_eq_mul] <;> ring
            | add z w hz hw => simp [map_add, hz, hw] <;> ring }
      map_add' := by
        intro x z
        apply LinearMap.ext
        intro s
        apply LinearMap.ext
        intro v
        induction v using TensorProduct.induction_on with
        | zero => simp
        | tmul y w => simp [rightTensor_tmul, map_add, add_mul] <;> ring
        | add v w hv hw =>
          simp only [map_add]
          rw [hv, hw]
      map_smul' := by
        intro a x
        apply LinearMap.ext
        intro s
        apply LinearMap.ext
        intro v
        induction v using TensorProduct.induction_on with
        | zero => simp
        | tmul y w =>
          simp [rightTensor_tmul, Hm_smul_left, matterForm_apply, smul_eq_mul] <;> ring
        | add v w hv hw =>
          simp only [map_add]
          rw [hv, hw]
          }

@[simp] theorem totalForm_tmul (x y : Carrier D) (s t : Fock) :
    totalForm (x ⊗ₜ[ℂ] s) (y ⊗ₜ[ℂ] t) = Hm x y * Hg s t := by
  simp [totalForm, rightTensor, ghostForm]

/-- Literal c0 insertion on the original tensor factor. -/
def relativeForm : State D →ₗ⋆[ℂ] State D →ₗ[ℂ] ℂ where
  toFun x := (totalForm x).comp (tp 1 (c 0))
  map_add' x y := by ext z; simp
  map_smul' a x := by ext y; simp

@[simp] theorem relativeForm_tmul (x y : Carrier D) (s t : Fock) :
    relativeForm (x ⊗ₜ[ℂ] s) (y ⊗ₜ[ℂ] t) = Hm x y * Hg s (c 0 t) := by
  simp [relativeForm]

/-- Native actualBasis compatibility, retaining p, every r+1 and every S. -/
theorem relativeForm_actualBasis (p q : Charge D) (m n : Exponents t)
    (S T : Finset ℕ) :
    relativeForm (actualBasis F B (⟨p,m⟩,S)) (actualBasis F B (⟨q,n⟩,T)) =
      (if p = q then oscillatorForm F B (monomial m 1) (monomial n 1) else 0) *
        Hg (ket S) (c 0 (ket T)) := by
  rw [actualBasis_apply, actualBasis_apply]
  simp only [sector, relativeForm_tmul, Hm_single, phi, oscillatorForm]
  rfl

include hPlus hMinus
/-- Opposite degree is DERIVED on the original basis, not an input interface. -/
theorem actual_opposite_degree (i j : StateIndex D t) (hij : degree i + degree j ≠ 0) :
    relativeForm (actualBasis F B i) (actualBasis F B j) = 0 := by
  rcases i with ⟨⟨p,m⟩,S⟩
  rcases j with ⟨⟨q,n⟩,T⟩
  rw [relativeForm_actualBasis]
  by_cases hgh : Hg (ket S) (c 0 (ket T)) = 0
  · rw [hgh, mul_zero]
  · have hg := ghost_relative_nonzero S T hgh
    have hm : exponentDegree m + exponentDegree n ≠ 0 := by
      dsimp only [degree] at hij
      omega
    have hmat := matter_basis_selection F B hPlus hMinus p q m n hm
    rw [Hm_single] at hmat
    change (if p = q then oscillatorForm F B (monomial m 1) (monomial n 1) else 0) = 0 at hmat
    rw [hmat, zero_mul]

/-- All finite polynomial/occupation combinations, with no homogeneity
assumption on x or y when their supports are separated in this sense. -/
theorem actual_support_orthogonal (x y : State D)
    (hxy : ∀ i j, (actualBasis F B).repr x i ≠ 0 →
      (actualBasis F B).repr y j ≠ 0 → degree i + degree j ≠ 0) :
    relativeForm x y = 0 := by
  apply FiniteDegreePairing.supported_orthogonal (actualBasis F B) relativeForm
    (P := fun i => (actualBasis F B).repr x i ≠ 0)
    (Q := fun j => (actualBasis F B).repr y j ≠ 0) (fun _ h => h) (fun _ h => h)
  intro i j hi hj
  exact actual_opposite_degree F B hPlus hMinus i j (hxy i j hi hj)

end D5.S3.VertexAlgebra.LatticeOriginalRelativePairing
