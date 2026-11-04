/- GID: D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original lattice light-cone coordinates and charge-dependent null frames. -/

/- The original integral Charge, complex bilinear Gram form and oscillator
carrier are preserved. No positivity or operator-transport certificate is
assumed. The coordinate input and null-frame input were fallible uncompiled
drafts; this implementation repairs them against the current native API.
Classical setting: Bakalov--Kac, arXiv math/0402315v1, section 4.1.
The claims are algebraic tools, with no BRST or no-ghost conclusion.
proof_shape: content
admission_basis: escape-witness
escape_witness: Explicit inverse substitutions, Gram directional derivatives,
and isotropic-vector normalization are proved on the original carrier.
-/
import D5.S3.VertexAlgebra.LatticeSugawaraCurrents
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! Explicit light-cone coordinates on the original lattice oscillator carrier. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeLightConeCoordinates

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents MvPolynomial
open scoped BigOperators

abbrev E (D : LatticeData) := Fin D.rank → ℂ

/-- The actual complex bilinear Gram pairing; there is no conjugation. -/
def g (D : LatticeData) (u v : E D) : ℂ :=
  ∑ i, ∑ j, u i * (D.G i j : ℂ) * v j

theorem g_symm (D : LatticeData) (u v : E D) : g D u v = g D v u := by
  unfold g
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [D.symmetric j i]
  ring

@[simp] theorem g_zero_right (D : LatticeData) (u : E D) : g D u 0 = 0 := by
  simp [g]

@[simp] theorem g_add_right (D : LatticeData) (u v w : E D) :
    g D u (v + w) = g D u v + g D u w := by
  simp [g, mul_add, Finset.sum_add_distrib]

@[simp] private theorem g_sub_right (D : LatticeData) (u v w : E D) :
    g D u (v - w) = g D u v - g D u w := by
  simp [g, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem g_smul_right (D : LatticeData) (u v : E D) (c : ℂ) :
    g D u (c • v) = c * g D u v := by
  simp only [g, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

@[simp] theorem g_add_left (D : LatticeData) (u v w : E D) :
    g D (u + v) w = g D u w + g D v w := by
  rw [g_symm, g_add_right, g_symm D w u, g_symm D w v]

@[simp] theorem g_smul_left (D : LatticeData) (u v : E D) (c : ℂ) :
    g D (c • u) v = c * g D u v := by
  rw [g_symm, g_smul_right, g_symm]

def pairing (D : LatticeData) (u : E D) : E D →ₗ[ℂ] ℂ where
  toFun := g D u
  map_add' := g_add_right D u
  map_smul' c v := g_smul_right D u v c

/-- Only the three geometric equations, rather than a proposed splitting. -/
structure NullFrame (D : LatticeData) where
  ePlus : E D
  eMinus : E D
  plus_null : g D ePlus ePlus = 0
  minus_null : g D eMinus eMinus = 0
  plus_minus : g D ePlus eMinus = 1

namespace NullFrame

variable {D : LatticeData} (F : NullFrame D)

@[simp] theorem minus_plus : g D F.eMinus F.ePlus = 1 := by
  rw [g_symm, F.plus_minus]

/-- The actual simultaneous orthogonal complement inside E. -/
def K : Submodule ℂ (E D) :=
  (pairing D F.ePlus).ker ⊓ (pairing D F.eMinus).ker

@[simp] theorem plus_K (k : F.K) : g D F.ePlus (k : E D) = 0 := k.property.1
@[simp] theorem minus_K (k : F.K) : g D F.eMinus (k : E D) = 0 := k.property.2
@[simp] theorem K_plus (k : F.K) : g D (k : E D) F.ePlus = 0 := by
  rw [g_symm, F.plus_K]
@[simp] theorem K_minus (k : F.K) : g D (k : E D) F.eMinus = 0 := by
  rw [g_symm, F.minus_K]

def projVector : E D →ₗ[ℂ] E D :=
  LinearMap.id - (pairing D F.eMinus).smulRight F.ePlus -
    (pairing D F.ePlus).smulRight F.eMinus

@[simp] theorem projVector_apply (v : E D) :
    F.projVector v = v - g D F.eMinus v • F.ePlus - g D F.ePlus v • F.eMinus := rfl

def projK : E D →ₗ[ℂ] F.K :=
  F.projVector.codRestrict F.K (by
    intro v
    constructor <;>
      simp [pairing, projVector_apply, F.plus_null, F.minus_null, F.plus_minus])

@[simp] theorem coe_projK (v : E D) :
    (F.projK v : E D) = v - g D F.eMinus v • F.ePlus -
      g D F.ePlus v • F.eMinus := rfl

@[simp] theorem projK_coe (k : F.K) : F.projK (k : E D) = k := by
  apply Subtype.ext
  simp

/-- Explicit splitting, proved from the null equations and Gram symmetry. -/
def frameEquiv : E D ≃ₗ[ℂ] ℂ × ℂ × F.K where
  toFun v := (g D F.eMinus v, g D F.ePlus v, F.projK v)
  invFun x := x.1 • F.ePlus + x.2.1 • F.eMinus + (x.2.2 : E D)
  left_inv v := by
    change g D F.eMinus v • F.ePlus + g D F.ePlus v • F.eMinus +
      (v - g D F.eMinus v • F.ePlus - g D F.ePlus v • F.eMinus) = v
    abel
  right_inv x := by
    rcases x with ⟨a, b, k⟩
    have hp : g D F.ePlus (a • F.ePlus + b • F.eMinus + (k : E D)) = b := by
      simp [F.plus_null, F.plus_minus]
    have hm : g D F.eMinus (a • F.ePlus + b • F.eMinus + (k : E D)) = a := by
      simp [F.minus_null]
    apply Prod.ext hm
    apply Prod.ext hp
    apply Subtype.ext
    change a • F.ePlus + b • F.eMinus + (k : E D) -
      g D F.eMinus (a • F.ePlus + b • F.eMinus + (k : E D)) • F.ePlus -
      g D F.ePlus (a • F.ePlus + b • F.eMinus + (k : E D)) • F.eMinus = _
    rw [hp, hm]
    abel
  map_add' v w := by simp [g_add_right, map_add]
  map_smul' c v := by simp [g_smul_right, map_smul, smul_eq_mul]

/-- Finite index for a genuine transverse basis; t is NOT asserted to be rank-2. -/
abbrev Label (t : ℕ) := Unit ⊕ (Unit ⊕ Fin t)

def plus (t : ℕ) : Label t := .inl ()
def minus (t : ℕ) : Label t := .inr (.inl ())
def transverse (t : ℕ) (j : Fin t) : Label t := .inr (.inr j)

/-- A supplied basis of the actual K gives a basis of ALL of the original E. -/
def completeBasis {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K) :
    Module.Basis (Label t) ℂ (E D) :=
  ((Module.Basis.singleton Unit ℂ).prod
    ((Module.Basis.singleton Unit ℂ).prod B)).map F.frameEquiv.symm

@[simp] private theorem completeBasis_plus {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K) :
    F.completeBasis B (plus t) = F.ePlus := by
  simp [completeBasis, plus, Module.Basis.prod_apply, frameEquiv]

@[simp] private theorem completeBasis_minus {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K) :
    F.completeBasis B (minus t) = F.eMinus := by
  simp [completeBasis, minus, Module.Basis.prod_apply, frameEquiv]

@[simp] private theorem completeBasis_transverse {t : ℕ}
    (B : Module.Basis (Fin t) ℂ F.K) (j : Fin t) :
    F.completeBasis B (transverse t j) = (B j : E D) := by
  simp [completeBasis, transverse, Module.Basis.prod_apply, frameEquiv]

@[simp] private theorem repr_plus {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K) (v : E D) :
    (F.completeBasis B).repr v (plus t) = g D F.eMinus v := by
  change ((Module.Basis.singleton Unit ℂ).prod
    ((Module.Basis.singleton Unit ℂ).prod B)).repr (F.frameEquiv v) (.inl ()) = _
  simp [frameEquiv]

@[simp] private theorem repr_minus {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K) (v : E D) :
    (F.completeBasis B).repr v (minus t) = g D F.ePlus v := by
  change ((Module.Basis.singleton Unit ℂ).prod
    ((Module.Basis.singleton Unit ℂ).prod B)).repr (F.frameEquiv v) (.inr (.inl ())) = _
  simp [frameEquiv]

@[simp] private theorem repr_transverse {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
    (v : E D) (j : Fin t) :
    (F.completeBasis B).repr v (transverse t j) = B.repr (F.projK v) j := by
  change ((Module.Basis.singleton Unit ℂ).prod
    ((Module.Basis.singleton Unit ℂ).prod B)).repr (F.frameEquiv v) (.inr (.inr j)) = _
  rfl

end NullFrame

/- The frequencywise construction works for any genuine finite basis of E.
   Applying it to completeBasis below supplies the required null coordinates. -/

abbrev PolynomialCoordinates (ι : Type*) := MvPolynomial (ι × ℕ) ℂ

/-- Vector-valued creation polynomial at exactly one frequency. -/
def lin {ι : Type*} [Fintype ι] (r : ℕ) :
    (ι → ℂ) →ₗ[ℂ] PolynomialCoordinates ι := by
  classical
  exact
    { toFun := fun v => ∑ i, v i • X (i,r)
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum, smul_smul] }

@[simp] private theorem lin_single {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (i : ι) :
    lin r (Pi.single i (1 : ℂ)) = (X (i,r) : PolynomialCoordinates ι) := by
  classical
  simp [lin, Pi.single_apply]

abbrev standardBasis (D : LatticeData) : Module.Basis (Fin D.rank) ℂ (E D) :=
  Pi.basisFun ℂ (Fin D.rank)

section BasisSubstitution

variable {D : LatticeData} {ι : Type*} [Fintype ι]
variable (b : Module.Basis ι ℂ (E D))

/-- Explicit original-variable substitution: coordinates of each original unit vector. -/
private def forwardHom : Oscillator D →ₐ[ℂ] PolynomialCoordinates ι :=
  MvPolynomial.aeval (fun x : Index D => lin x.2 (b.equivFun (standardBasis D x.1)))

/-- Explicit inverse substitution: the actual vector b(c) in original variables. -/
private def backwardHom : PolynomialCoordinates ι →ₐ[ℂ] Oscillator D :=
  MvPolynomial.aeval (fun x : ι × ℕ => lin x.2 (b x.1))

private theorem forward_lin (r : ℕ) (v : E D) :
    forwardHom b (lin r v) = lin r (b.equivFun v) := by
  have h : (forwardHom b).toLinearMap.comp (lin r) =
      (lin r).comp b.equivFun.toLinearMap := by
    apply (standardBasis D).ext
    intro i
    simp [forwardHom, standardBasis]
  exact LinearMap.congr_fun h v

private theorem backward_lin (r : ℕ) (v : ι → ℂ) :
    backwardHom b (lin r v) = lin r (b.equivFun.symm v) := by
  classical
  have h : (backwardHom b).toLinearMap.comp (lin r) =
      (lin r).comp b.equivFun.symm.toLinearMap := by
    apply (Pi.basisFun ℂ ι).ext
    intro i
    simp [backwardHom, Module.Basis.equivFun_symm_apply, Pi.single_apply]
  exact LinearMap.congr_fun h v

private theorem backward_forward (P : Oscillator D) :
    backwardHom b (forwardHom b P) = P := by
  have h : (backwardHom b).comp (forwardHom b) = AlgHom.id ℂ (Oscillator D) := by
    apply MvPolynomial.algHom_ext
    intro x
    rcases x with ⟨i,r⟩
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [show forwardHom b (X (i,r)) = lin r (b.equivFun (standardBasis D i)) from
      MvPolynomial.aeval_X _ _]
    rw [backward_lin, LinearEquiv.symm_apply_apply]
    simp [standardBasis]
  exact DFunLike.congr_fun h P

private theorem forward_backward (P : PolynomialCoordinates ι) :
    forwardHom b (backwardHom b P) = P := by
  classical
  classical
  have h : (forwardHom b).comp (backwardHom b) =
      AlgHom.id ℂ (PolynomialCoordinates ι) := by
    apply MvPolynomial.algHom_ext
    intro x
    rcases x with ⟨c,r⟩
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [show backwardHom b (X (c,r)) = lin r (b c) from MvPolynomial.aeval_X _ _]
    rw [forward_lin]
    simp [Module.Basis.equivFun_self, lin, Finsupp.single_apply]
  exact DFunLike.congr_fun h P

/-- No change-of-representation hypothesis: both inverse laws were proved on variables. -/
def polynomialEquiv : Oscillator D ≃ₐ[ℂ] PolynomialCoordinates ι where
  toFun := forwardHom b
  invFun := backwardHom b
  left_inv := backward_forward b
  right_inv := forward_backward b
  map_mul' := (forwardHom b).map_mul
  map_add' := (forwardHom b).map_add
  commutes' := (forwardHom b).commutes

@[simp] private theorem polynomialEquiv_symm_X (c : ι) (r : ℕ) :
    (polynomialEquiv b).symm (X (c,r)) = lin r (b c) :=
  MvPolynomial.aeval_X _ _

private theorem polynomialEquiv_lin (r : ℕ) (v : E D) :
    polynomialEquiv b (lin r v) = lin r (b.equivFun v) := forward_lin b r v

end BasisSubstitution

/-- Integral charge labels are never transformed. -/
def chargeVector {D : LatticeData} (p : Charge D) : E D := fun i => (p i : ℂ)

private theorem g_charge (D : LatticeData) (u : E D) (p : Charge D) :
    g D u (chargeVector p) =
      ∑ i, u i * (bilinear D (unitCharge D i) p : ℂ) := by
  classical
  simp [g, chargeVector, bilinear, unitCharge, Int.cast_sum, Int.cast_mul,
    Finset.mul_sum, mul_assoc]

/-- Complex linear extension of the ORIGINAL sector currents. -/
def polynomialCurrent {D : LatticeData} (u : E D) (p : Charge D) (m : ℤ) :
    Module.End ℂ (Oscillator D) :=
  ∑ i, u i • neutralPolynomialMode D i p m

/-- Complex linear extension of the ORIGINAL all-charge modes (the a(u,m) notation). -/
def a {D : LatticeData} (u : E D) (m : ℤ) : Module.End ℂ (Carrier D) :=
  ∑ i, u i • neutralMode D i m

theorem a_single {D : LatticeData} (u : E D) (m : ℤ) (p : Charge D)
    (P : Oscillator D) :
    a u m (Finsupp.single p P) = Finsupp.single p (polynomialCurrent u p m P) := by
  classical
  simp only [a, polynomialCurrent, LinearMap.sum_apply, LinearMap.smul_apply]
  change (∑ i, u i • neutralMode D i m (Finsupp.single p P)) =
    (Finsupp.lsingle p : Oscillator D →ₗ[ℂ] Carrier D)
      (∑ i, u i • neutralPolynomialMode D i p m P)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [map_smul, Finsupp.lsingle_apply, neutralMode_single, Finsupp.smul_single]

/-- Actual positive-mode directional derivation. -/
def oldDerivative {D : LatticeData} (u : E D) (r : ℕ) :
    Derivation ℂ (Oscillator D) (Oscillator D) :=
  ∑ i, u i • ∑ j, (D.G i j : ℂ) • pderiv (j,r)

theorem polynomialCurrent_negative {D : LatticeData} (u : E D) (p : Charge D)
    (r : ℕ) (P : Oscillator D) :
    polynomialCurrent u p (-(r : ℤ)-1) P = lin r u * P := by
  simp [polynomialCurrent, neutralPolynomialMode_negative, lin,
    Finset.sum_mul, smul_mul_assoc]

theorem polynomialCurrent_zero {D : LatticeData} (u : E D) (p : Charge D)
    (P : Oscillator D) :
    polynomialCurrent u p 0 P = g D u (chargeVector p) • P := by
  rw [g_charge]
  simp [polynomialCurrent, neutralPolynomialMode, smul_smul, Finset.sum_smul]

theorem polynomialCurrent_positive {D : LatticeData} (u : E D) (p : Charge D)
    (r : ℕ) (P : Oscillator D) :
    polynomialCurrent u p ((r : ℤ)+1) P = (r+1 : ℂ) • oldDerivative u r P := by
  classical
  simp [polynomialCurrent, neutralPolynomialMode_positive, weightedPartial,
    oldDerivative, Finset.smul_sum, smul_smul, mul_comm, mul_left_comm]

private theorem oldDerivative_X {D : LatticeData} (u : E D) (r s : ℕ) (j : Fin D.rank) :
    oldDerivative u r (X (j,s)) =
      if r = s then g D u (standardBasis D j) • (1 : Oscillator D) else 0 := by
  classical
  by_cases hrs : r = s
  · subst s
    simp [oldDerivative, pderiv_X, Pi.single_apply, Prod.mk.injEq,
      g, standardBasis, smul_smul, Finset.sum_smul]
  · simp [oldDerivative, pderiv_X, Pi.single_apply, Prod.mk.injEq, hrs]

private theorem g_expand_right (D : LatticeData) (u v : E D) :
    (∑ j, v j * g D u (standardBasis D j)) = g D u v := by
  have h := congrArg (pairing D u) ((standardBasis D).sum_repr v)
  simpa [pairing] using h

theorem oldDerivative_lin {D : LatticeData} (u v : E D) (r s : ℕ) :
    oldDerivative u r (lin s v) =
      if r = s then g D u v • (1 : Oscillator D) else 0 := by
  classical
  change oldDerivative u r (∑ j, v j • X (j,s)) = _
  simp only [map_sum, Derivation.map_smul, oldDerivative_X]
  by_cases hrs : r = s
  · simp only [hrs, if_true, smul_smul, ← Finset.sum_smul]
    rw [g_expand_right]
  · simp [hrs]

section DerivativeTransport

variable {D : LatticeData} {ι : Type*} [Fintype ι]
variable (b : Module.Basis ι ℂ (E D))

/-- The coefficients are the actual Gram pairings with the newly derived basis. -/
def coordinateDerivative (u : E D) (r : ℕ) :
    Derivation ℂ (PolynomialCoordinates ι) (PolynomialCoordinates ι) :=
  ∑ c, g D u (b c) • pderiv (c,r)

private theorem coordinateDerivative_X (u : E D) (r s : ℕ) (c : ι) :
    coordinateDerivative b u r (X (c,s)) =
      if r = s then g D u (b c) • (1 : PolynomialCoordinates ι) else 0 := by
  classical
  by_cases hrs : r = s
  · subst s
    simp [coordinateDerivative, pderiv_X, Pi.single_apply, Prod.mk.injEq]
  · simp [coordinateDerivative, pderiv_X, Pi.single_apply, Prod.mk.injEq, hrs]

/-- Chain rule proved on the actual inverse substitutions, then on every polynomial. -/
private theorem derivative_backward (u : E D) (r : ℕ) (Q : PolynomialCoordinates ι) :
    oldDerivative u r (backwardHom b Q) =
      backwardHom b (coordinateDerivative b u r Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C c => simp [backwardHom]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X Q x hQ =>
    rcases x with ⟨c,s⟩
    have hx : oldDerivative u r (backwardHom b (X (c,s))) =
        backwardHom b (coordinateDerivative b u r (X (c,s))) := by
      rw [show backwardHom b (X (c,s)) = lin s (b c) from MvPolynomial.aeval_X _ _,
        oldDerivative_lin, coordinateDerivative_X]
      split_ifs <;> simp
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hQ, hx]

private theorem derivative_transport (u : E D) (r : ℕ) (P : Oscillator D) :
    polynomialEquiv b (oldDerivative u r P) =
      coordinateDerivative b u r (polynomialEquiv b P) := by
  apply (polynomialEquiv b).symm.injective
  change backwardHom b (forwardHom b (oldDerivative u r P)) =
    backwardHom b (coordinateDerivative b u r (forwardHom b P))
  rw [← derivative_backward, backward_forward, backward_forward]

/-- Explicit target formula, including the unchanged original integral charge. -/
def coordinatePolynomialMode (u : E D) (p : Charge D) (m : ℤ) :
    Module.End ℂ (PolynomialCoordinates ι) :=
  if m < 0 then LinearMap.mulLeft ℂ (lin (-m-1).toNat (b.equivFun u))
  else if m = 0 then g D u (chargeVector p) • LinearMap.id
  else (m : ℂ) • (coordinateDerivative b u (m-1).toNat).toLinearMap

/-- Every original polynomial, every original charge, every integer mode. -/
private theorem fixed_charge_transport (u : E D) (p : Charge D) (m : ℤ)
    (P : Oscillator D) :
    polynomialEquiv b (polynomialCurrent u p m P) =
      coordinatePolynomialMode b u p m (polynomialEquiv b P) := by
  cases m with
  | ofNat n =>
    cases n with
    | zero => simp [polynomialCurrent_zero, coordinatePolynomialMode]
    | succ r =>
      rw [show (Int.ofNat (r+1)) = (r : ℤ)+1 by simp, polynomialCurrent_positive]
      simp only [map_smul, derivative_transport]
      simp [coordinatePolynomialMode, show ¬ (r : ℤ)+1 < 0 by omega,
        show (r : ℤ)+1 ≠ 0 by omega]
  | negSucc r =>
    rw [show Int.negSucc r = -(r : ℤ)-1 by omega, polynomialCurrent_negative,
      map_mul, polynomialEquiv_lin]
    simp [coordinatePolynomialMode, show -(r : ℤ)-1 < 0 by omega,
      show -(-(r : ℤ)-1)-1 = (r : ℤ) by omega]

/-- Value substitution only, with exactly the original Charge D as the support index. -/
def carrierEquiv : Carrier D ≃ₗ[ℂ] (Charge D →₀ PolynomialCoordinates ι) :=
  Finsupp.mapRange.linearEquiv (polynomialEquiv b).toLinearEquiv

@[simp] theorem carrierEquiv_apply (v : Carrier D) (p : Charge D) :
    carrierEquiv b v p = polynomialEquiv b (v p) := rfl

@[simp] theorem carrierEquiv_single (p : Charge D) (P : Oscillator D) :
    carrierEquiv b (Finsupp.single p P) = Finsupp.single p (polynomialEquiv b P) := by
  classical
  ext q
  by_cases h : p = q
  · subst q; simp
  · simp [Finsupp.single_apply, h]

/-- A concrete chargewise endomorphism, not an assumed conjugation law. -/
def coordinateMode (u : E D) (m : ℤ) :
    Module.End ℂ (Charge D →₀ PolynomialCoordinates ι) :=
  Finsupp.lsum ℂ (fun p =>
    (Finsupp.lsingle p).comp (coordinatePolynomialMode b u p m))

@[simp] theorem coordinateMode_single (u : E D) (m : ℤ) (p : Charge D)
    (P : PolynomialCoordinates ι) :
    coordinateMode b u m (Finsupp.single p P) =
      Finsupp.single p (coordinatePolynomialMode b u p m P) := by
  simp [coordinateMode]

/-- The actual all-charge operator transport, preserving every integral charge label. -/
theorem all_charge_transport (u : E D) (m : ℤ) (v : Carrier D) :
    carrierEquiv b (a u m v) = coordinateMode b u m (carrierEquiv b v) := by
  have h : (carrierEquiv b).toLinearMap.comp (a u m) =
      (coordinateMode b u m).comp (carrierEquiv b).toLinearMap := by
    apply Finsupp.lhom_ext'
    intro p
    apply LinearMap.ext
    intro P
    change carrierEquiv b (a u m (Finsupp.single p P)) =
      coordinateMode b u m (carrierEquiv b (Finsupp.single p P))
    rw [a_single, carrierEquiv_single, carrierEquiv_single,
      coordinateMode_single, fixed_charge_transport]
  exact LinearMap.congr_fun h v


end DerivativeTransport

namespace NullFrame

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
variable (B : Module.Basis (Fin t) ℂ F.K)

abbrev coordinateEquiv := polynomialEquiv (F.completeBasis B)
abbrev allChargeEquiv := carrierEquiv (F.completeBasis B)

def pPlus (p : Charge D) : ℂ := g D F.ePlus (chargeVector p)
def pMinus (p : Charge D) : ℂ := g D F.eMinus (chargeVector p)

theorem vector_substitution (v : E D) (r : ℕ) :
    F.coordinateEquiv B (lin r v) =
      g D F.eMinus v • X (plus t,r) + g D F.ePlus v • X (minus t,r) +
        ∑ j : Fin t, B.repr (F.projK v) j • X (transverse t j,r) := by
  rw [polynomialEquiv_lin]
  simp only [lin, Fintype.sum_sum_type, Fintype.sum_unique, Module.Basis.equivFun_apply]
  change (F.completeBasis B).repr v (plus t) • X (plus t,r) +
    ((F.completeBasis B).repr v (minus t) • X (minus t,r) +
      ∑ j : Fin t, (F.completeBasis B).repr v (transverse t j) •
        X (transverse t j,r)) = _
  simp only [F.repr_plus, F.repr_minus, F.repr_transverse, add_assoc]

private theorem coordinateDerivative_minus (r : ℕ) :
    coordinateDerivative (F.completeBasis B) F.eMinus r = pderiv (plus t,r) := by
  classical
  have hc (c : Label t) : g D F.eMinus (F.completeBasis B c) =
      if c = plus t then 1 else 0 := by
    rcases c with u | (u | j)
    · cases u
      change g D F.eMinus (F.completeBasis B (plus t)) = _
      rw [F.completeBasis_plus, F.minus_plus]
      simp [plus]
    · cases u
      change g D F.eMinus (F.completeBasis B (minus t)) = _
      rw [F.completeBasis_minus]
      simp [minus, plus, F.minus_null]
    · change g D F.eMinus (F.completeBasis B (transverse t j)) = _
      rw [F.completeBasis_transverse]
      simp [plus, transverse]
  simp only [coordinateDerivative, hc]
  simp

private theorem coordinateDerivative_plus (r : ℕ) :
    coordinateDerivative (F.completeBasis B) F.ePlus r = pderiv (minus t,r) := by
  classical
  have hc (c : Label t) : g D F.ePlus (F.completeBasis B c) =
      if c = minus t then 1 else 0 := by
    rcases c with u | (u | j)
    · cases u
      change g D F.ePlus (F.completeBasis B (plus t)) = _
      rw [F.completeBasis_plus]
      simp [minus, plus, F.plus_null]
    · cases u
      change g D F.ePlus (F.completeBasis B (minus t)) = _
      rw [F.completeBasis_minus, F.plus_minus]
      simp [minus]
    · change g D F.ePlus (F.completeBasis B (transverse t j)) = _
      rw [F.completeBasis_transverse]
      simp [minus, transverse]
  simp only [coordinateDerivative, hc]
  simp

private theorem coordinateDerivative_K (k : F.K) (r : ℕ) :
    coordinateDerivative (F.completeBasis B) (k : E D) r =
      ∑ j : Fin t, g D (k : E D) (B j : E D) • pderiv (transverse t j,r) := by
  classical
  simp only [coordinateDerivative, Fintype.sum_sum_type, Fintype.sum_unique]
  change g D (k : E D) (F.completeBasis B (plus t)) • pderiv (plus t,r) +
    (g D (k : E D) (F.completeBasis B (minus t)) • pderiv (minus t,r) +
      ∑ j : Fin t, g D (k : E D) (F.completeBasis B (transverse t j)) •
        pderiv (transverse t j,r)) = _
  simp only [F.completeBasis_plus, F.completeBasis_minus, F.completeBasis_transverse,
    F.K_plus, F.K_minus, zero_smul, zero_add]

theorem creation_plus (p : Charge D) (r : ℕ) (P : Oscillator D) :
    F.coordinateEquiv B (polynomialCurrent F.ePlus p (-(r : ℤ)-1) P) =
      X (plus t,r) * F.coordinateEquiv B P := by
  rw [polynomialCurrent_negative, map_mul]
  have hx : F.coordinateEquiv B (lin r F.ePlus) = X (plus t,r) := by
    apply (F.coordinateEquiv B).symm.injective
    simp only [AlgEquiv.symm_apply_apply, polynomialEquiv_symm_X, F.completeBasis_plus]
  rw [hx]

theorem creation_minus (p : Charge D) (r : ℕ) (P : Oscillator D) :
    F.coordinateEquiv B (polynomialCurrent F.eMinus p (-(r : ℤ)-1) P) =
      X (minus t,r) * F.coordinateEquiv B P := by
  rw [polynomialCurrent_negative, map_mul]
  have hx : F.coordinateEquiv B (lin r F.eMinus) = X (minus t,r) := by
    apply (F.coordinateEquiv B).symm.injective
    simp only [AlgEquiv.symm_apply_apply, polynomialEquiv_symm_X, F.completeBasis_minus]
  rw [hx]

theorem annihilation_minus (p : Charge D) (r : ℕ) (P : Oscillator D) :
    F.coordinateEquiv B (polynomialCurrent F.eMinus p ((r : ℤ)+1) P) =
      (r+1 : ℂ) • pderiv (plus t,r) (F.coordinateEquiv B P) := by
  rw [polynomialCurrent_positive, map_smul, derivative_transport,
    F.coordinateDerivative_minus B]

theorem annihilation_plus (p : Charge D) (r : ℕ) (P : Oscillator D) :
    F.coordinateEquiv B (polynomialCurrent F.ePlus p ((r : ℤ)+1) P) =
      (r+1 : ℂ) • pderiv (minus t,r) (F.coordinateEquiv B P) := by
  rw [polynomialCurrent_positive, map_smul, derivative_transport,
    F.coordinateDerivative_plus B]

theorem creation_K (k : F.K) (p : Charge D) (r : ℕ) (P : Oscillator D) :
    F.coordinateEquiv B (polynomialCurrent (k : E D) p (-(r : ℤ)-1) P) =
      (∑ j : Fin t, B.repr k j • X (transverse t j,r)) * F.coordinateEquiv B P := by
  rw [polynomialCurrent_negative, map_mul, F.vector_substitution B]
  simp

theorem annihilation_K (k : F.K) (p : Charge D) (r : ℕ) (P : Oscillator D) :
    F.coordinateEquiv B (polynomialCurrent (k : E D) p ((r : ℤ)+1) P) =
      (r+1 : ℂ) • ∑ j : Fin t, g D (k : E D) (B j : E D) •
        pderiv (transverse t j,r) (F.coordinateEquiv B P) := by
  rw [polynomialCurrent_positive, map_smul, derivative_transport,
    F.coordinateDerivative_K B]
  simp

theorem original_carrier_all_charges (u : E D) (m : ℤ) (v : Carrier D) :
    F.allChargeEquiv B (a u m v) =
      coordinateMode (F.completeBasis B) u m (F.allChargeEquiv B v) :=
  all_charge_transport (F.completeBasis B) u m v

end NullFrame

/- Frequency grading. We prove preservation in both directions, for every
   polynomial, using weighted-homogeneous monomial induction. -/

def frequencyWeight {ι : Type*} (x : ι × ℕ) : ℕ := x.2 + 1

private theorem homogeneous_substitution {σ τ : Type*} (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ ℂ)
    (hf : ∀ i, IsWeightedHomogeneous v (f i) (w i))
    {P : MvPolynomial σ ℂ} {n : ℕ} (hP : IsWeightedHomogeneous w P n) :
    IsWeightedHomogeneous v (MvPolynomial.aeval f P) n := by
  classical
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa using MvPolynomial.isWeightedHomogeneous_zero ℂ v n
  | add P Q hP hQ ihP ihQ => simpa only [map_add] using ihP.add ihQ
  | monomial d c hd =>
    rw [MvPolynomial.aeval_monomial]
    change IsWeightedHomogeneous v (C c * ∏ i ∈ d.support, f i ^ d i) n
    have h := MvPolynomial.IsWeightedHomogeneous.prod d.support
      (fun i => f i ^ d i) (fun i => d i • w i) (fun i hi => (hf i).pow (d i))
    have hw : (∑ i ∈ d.support, d i • w i) = n := by
      simpa only [Finsupp.weight_apply, Finsupp.sum] using hd
    rw [hw] at h
    exact h.C_mul c

theorem lin_homogeneous {ι : Type*} [Fintype ι] (r : ℕ) (v : ι → ℂ) :
    IsWeightedHomogeneous frequencyWeight (lin r v) (r+1) := by
  classical
  change IsWeightedHomogeneous frequencyWeight
    (∑ i, v i • (X (i,r) : PolynomialCoordinates ι)) (r+1)
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro i hi
  exact (MvPolynomial.weightedHomogeneousSubmodule ℂ frequencyWeight (r+1)).smul_mem
    _ (MvPolynomial.isWeightedHomogeneous_X ℂ frequencyWeight (i,r))

private theorem polynomialEquiv_homogeneous {D : LatticeData} {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (E D)) (P : Oscillator D) (n : ℕ) :
    IsWeightedHomogeneous frequencyWeight (polynomialEquiv b P) n ↔
      IsWeightedHomogeneous (oscillatorWeight D) P n := by
  constructor
  · intro h
    have h' : IsWeightedHomogeneous (oscillatorWeight D)
        (backwardHom b (polynomialEquiv b P)) n :=
      homogeneous_substitution frequencyWeight (oscillatorWeight D)
        (fun x : ι × ℕ => lin x.2 (b x.1))
        (fun x => lin_homogeneous x.2 (b x.1)) h
    change IsWeightedHomogeneous (oscillatorWeight D)
      ((polynomialEquiv b).symm (polynomialEquiv b P)) n at h'
    simpa only [AlgEquiv.symm_apply_apply] using h'
  · intro h
    exact homogeneous_substitution (oscillatorWeight D) frequencyWeight
      (fun x : Index D => lin x.2 (b.equivFun (standardBasis D x.1)))
      (fun x => lin_homogeneous x.2 _) h

/-- Required grading theorem for the actual null-frame substitution. -/
theorem NullFrame.frequency_grading {D : LatticeData} (F : NullFrame D) {t : ℕ}
    (B : Module.Basis (Fin t) ℂ F.K) (P : Oscillator D) (n : ℕ) :
    IsWeightedHomogeneous frequencyWeight (F.coordinateEquiv B P) n ↔
      IsWeightedHomogeneous (oscillatorWeight D) P n :=
  polynomialEquiv_homogeneous (F.completeBasis B) P n

end D5.S3.VertexAlgebra.LatticeLightConeCoordinates
