/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Signed support degrees of the original lattice tensor occupation-ghost modes. -/

import D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
import D5.S3.Quantum.Fermionic.BcGhostCubic
import D5.S3.Quantum.Fermionic.BcGhostCharge
import Mathlib.Tactic

/-! Signed degree on the original integral-charge matter tensor occupation bc carrier.
The coordinate basis is transported from the accepted original carrier. Its degree
is the plus count minus the minus count plus ghost charge minus one. Positive
minus currents differentiate PLUS variables; zero currents are scalar degree zero.
The original locally finite quartet and cubic operators are used without assumed
support certificates. This module does not identify or transfer the full BRST differential.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.LatticeBRSTModeFiltration

open LatticeGeneratingFieldLocality
open D5.S3.HomologicalAlgebra
open LatticeLightConeCoordinates LatticeLightConeCoordinates.NullFrame
open LatticeQuartetContraction
open private sector_current sector_add sector_smul from D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostCharge
open MvPolynomial
open private fixed_charge_transport g_expand_right from D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
open private charge_insert charge_erase from D5.S3.Quantum.Fermionic.BcGhostCharge
open private cubic_eq from D5.S3.Quantum.Fermionic.BcGhostCubic

/- Signed weights use integers, independently of any Gram positivity. -/
def variableWeight {t : ℕ} (x : Variables t) : ℤ :=
  if x.1 = plus t then 1 else if x.1 = minus t then -1 else 0

def exponentDegree {t : ℕ} (m : Exponents t) : ℤ :=
  m.sum (fun x n => (n : ℤ) * variableWeight x)

@[simp] theorem weight_plus (t r : ℕ) : variableWeight (plus t,r) = 1 := by
  simp [variableWeight]
@[simp] theorem weight_minus (t r : ℕ) : variableWeight (minus t,r) = -1 := by
  simp [variableWeight, plus, minus]
@[simp] theorem weight_transverse {t : ℕ} (j : Fin t) (r : ℕ) :
    variableWeight (transverse t j,r) = 0 := by
  simp [variableWeight, plus, minus, transverse]

theorem exponentDegree_add {t : ℕ} (m n : Exponents t) :
    exponentDegree (m+n) = exponentDegree m + exponentDegree n := by
  classical
  unfold exponentDegree
  rw [Finsupp.sum_add_index]
  · intro x; simp
  · intro x a b; simp [Nat.cast_add, add_mul]

@[simp] theorem exponentDegree_single {t : ℕ} (x : Variables t) (k : ℕ) :
    exponentDegree (Finsupp.single x k) = (k : ℤ) * variableWeight x := by
  classical
  simp [exponentDegree]

def degree {D : LatticeData} {t : ℕ} (i : StateIndex D t) : ℤ :=
  exponentDegree i.1.2 + charge i.2 - 1

/- Elementary polynomial actions, proved before discussing any BRST operator. -/
theorem X_mul_monomial {t : ℕ} (x : Variables t) (m : Exponents t) (z : ℂ) :
    X x * monomial m z = monomial (Finsupp.single x 1 + m) z := by
  change monomial (Finsupp.single x 1) (1 : ℂ) * monomial m z = _
  rw [monomial_mul, one_mul]

theorem single_add_sub {t : ℕ} (x : Variables t) (m : Exponents t)
    (hx : m x ≠ 0) : Finsupp.single x 1 + (m-Finsupp.single x 1) = m := by
  classical
  ext y
  by_cases hy : y=x
  · subst y
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.tsub_apply]
    omega
  · simp [Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm hy]

/-- Actual derivative, including the zero-exponent case and the scalar multiplicity. -/
theorem derivative_monomial {t : ℕ} (x : Variables t) (m : Exponents t) :
    pderiv x (monomial m (1 : ℂ)) =
      (m x : ℂ) • monomial (m-Finsupp.single x 1) 1 := by
  classical
  apply mul_left_cancel₀ (show (X x : PolynomialCoordinates (Label t)) ≠ 0 by simp)
  rw [X_mul_pderiv_monomial]
  by_cases hx : m x = 0
  · simp [hx]
  · rw [mul_smul_comm, X_mul_monomial, single_add_sub x m hx]
    simp only [Nat.cast_smul_eq_nsmul]

/-- Literal coefficient of the original multiplication formula in the derived coordinates. -/
theorem multiply_coefficient {t : ℕ} (x : Variables t) (m n : Exponents t) :
    (X x * monomial m (1 : ℂ)).coeff n =
      if Finsupp.single x 1 + m = n then 1 else 0 := by
  classical
  rw [X_mul_monomial]
  by_cases h : Finsupp.single x 1+m=n <;> simp [coeff_monomial, h, eq_comm]

/-- Literal coefficient of the derivative; no support or degree premise. -/
theorem derivative_coefficient {t : ℕ} (x : Variables t) (m n : Exponents t) :
    (pderiv x (monomial m (1 : ℂ))).coeff n =
      if m-Finsupp.single x 1 = n then (m x : ℂ) else 0 := by
  classical
  rw [derivative_monomial]
  by_cases h : m-Finsupp.single x 1 = n <;> simp [h, coeff_monomial, eq_comm]

theorem multiply_support_degree {t : ℕ} (x : Variables t) (m n : Exponents t)
    (h : (X x * monomial m (1 : ℂ)).coeff n ≠ 0) :
    exponentDegree n = exponentDegree m + variableWeight x := by
  classical
  have hn : Finsupp.single x 1+m=n := by
    by_contra hn
    exact h (by simp [multiply_coefficient, hn])
  rw [← hn, exponentDegree_add, exponentDegree_single]
  ring

theorem derivative_support_degree {t : ℕ} (x : Variables t) (m n : Exponents t)
    (h : (pderiv x (monomial m (1 : ℂ))).coeff n ≠ 0) :
    exponentDegree n = exponentDegree m - variableWeight x := by
  classical
  have hx : m x ≠ 0 := by
    intro hx
    exact h (by simp [derivative_coefficient, hx])
  have hn : m-Finsupp.single x 1=n := by
    by_contra hn
    exact h (by simp [derivative_coefficient, hn])
  have he := congrArg exponentDegree (single_add_sub x m hx)
  rw [exponentDegree_add, exponentDegree_single, Nat.cast_one, one_mul, hn] at he
  omega

/- Primitive occupation coefficients with the actual Jordan--Wigner phase. -/
theorem create_coefficient (j : ℕ) (S T : Finset ℕ) :
    (create j (ket S)) T =
      if j ∈ S then 0 else if insert j S = T then phase j S else 0 := by
  classical
  rw [create_ket]
  by_cases hj : j ∈ S
  · simp only [if_pos hj, Finsupp.zero_apply]
  · simp only [if_neg hj, Finsupp.smul_apply, ket, Finsupp.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem annihilate_coefficient (j : ℕ) (S T : Finset ℕ) :
    (annihilate j (ket S)) T =
      if j ∈ S then (if S.erase j = T then phase j S else 0) else 0 := by
  classical
  rw [annihilate_ket]
  by_cases hj : j ∈ S
  · simp only [if_pos hj, Finsupp.smul_apply, ket, Finsupp.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
  · simp only [if_neg hj, Finsupp.zero_apply]

theorem create_support_charge (j : ℕ) (S T : Finset ℕ)
    (h : (create j (ket S)) T ≠ 0) : charge T=charge S+siteSign j := by
  classical
  have hj : j ∉ S := by intro hj; exact h (by simp [create_coefficient, hj])
  have he : insert j S=T := by
    by_contra he
    exact h (by simp only [create_coefficient, if_neg hj, if_neg he])
  rw [← he, charge_insert j S hj]

theorem annihilate_support_charge (j : ℕ) (S T : Finset ℕ)
    (h : (annihilate j (ket S)) T ≠ 0) : charge T=charge S-siteSign j := by
  classical
  have hj : j ∈ S := by
    by_contra hj
    exact h (by simp [annihilate_coefficient, hj])
  have he : S.erase j=T := by
    by_contra he
    exact h (by simp only [annihilate_coefficient, if_pos hj, if_neg he])
  rw [← he, charge_erase j S hj]

/-- Every integer b mode, including b(-1) and b0. -/
theorem b_support_charge (n : ℤ) (S T : Finset ℕ)
    (h : (b n (ket S)) T ≠ 0) : charge T=charge S-1 := by
  by_cases hn : n ≤ -2
  · have hh := create_support_charge (2*(-n-2).toNat) S T (by simpa [b, hn] using h)
    simpa [siteSign, sub_eq_add_neg] using hh
  · have hh := annihilate_support_charge (2*(n+1).toNat+1) S T (by simpa [b, hn] using h)
    simpa [siteSign, sub_eq_add_neg] using hh

/-- Every integer c mode, including c1 and c0. -/
theorem c_support_charge (n : ℤ) (S T : Finset ℕ)
    (h : (c n (ket S)) T ≠ 0) : charge T=charge S+1 := by
  by_cases hn : n ≤ 1
  · have hh := create_support_charge (2*(1-n).toNat+1) S T (by simpa [c, hn] using h)
    simpa [siteSign, sub_eq_add_neg] using hh
  · have hh := annihilate_support_charge (2*(n-2).toNat) S T (by simpa [c, hn] using h)
    simpa [siteSign, sub_eq_add_neg] using hh

section CoefficientCalculus
variable {V I : Type*} [AddCommGroup V] [Module ℂ V]
variable (bas : Module.Basis I ℂ V) (w : I → ℤ)

def Shift (A : Module.End ℂ V) (k : ℤ) : Prop :=
  ∀ i j, bas.repr (A (bas i)) j ≠ 0 → w j=w i+k

theorem basis_expand (v : V) :
    (∑ i ∈ (bas.repr v).support, bas.repr v i • bas i)=v := by
  simpa [Finsupp.linearCombination_apply, Finsupp.sum] using bas.linearCombination_repr v

theorem shift_zero (k : ℤ) : Shift bas w 0 k := by
  intro i j h
  exact False.elim (h (by simp))

theorem shift_one : Shift bas w (1 : Module.End ℂ V) 0 := by
  classical
  intro i j h
  have he : i=j := by
    by_contra he
    exact h (by simp [Module.Basis.repr_self, Finsupp.single_apply, he])
  subst j
  omega

theorem shift_smul {A : Module.End ℂ V} {k : ℤ} (z : ℂ)
    (hA : Shift bas w A k) : Shift bas w (z • A) k := by
  intro i j h
  apply hA i j
  intro hz
  apply h
  simp [hz]

theorem shift_add {A C : Module.End ℂ V} {k : ℤ}
    (hA : Shift bas w A k) (hC : Shift bas w C k) : Shift bas w (A+C) k := by
  intro i j h
  by_cases ha : bas.repr (A (bas i)) j=0
  · apply hC i j
    intro hc
    exact h (by simp [ha, hc])
  · exact hA i j ha

theorem shift_mul {A C : Module.End ℂ V} {a c : ℤ}
    (hA : Shift bas w A a) (hC : Shift bas w C c) : Shift bas w (A*C) (a+c) := by
  classical
  intro i j h
  by_contra hw
  apply h
  change (bas.coord j) (A (C (bas i)))=0
  rw [← basis_expand bas (C (bas i))]
  simp only [map_sum, map_smul, Module.Basis.coord_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro l hl
  by_cases hc : bas.repr (C (bas i)) l=0
  · simp [hc]
  · by_cases ha : bas.repr (A (bas l)) j=0
    · simp [ha]
    · have h1 := hC i l hc
      have h2 := hA l j ha
      exact False.elim (hw (by omega))

theorem shift_sum {J : Type*} (s : Finset J) (A : J → Module.End ℂ V) (k : ℤ)
    (hA : ∀ j ∈ s, Shift bas w (A j) k) : Shift bas w (∑ j ∈ s, A j) k := by
  classical
  revert hA
  induction s using Finset.induction_on with
  | empty => intro hA; simpa using shift_zero bas w k
  | @insert j s hj ih =>
    intro hA
    rw [Finset.sum_insert hj]
    exact shift_add bas w (hA j (by simp)) (ih (fun l hl => hA l (by simp [hl])))

def StrictRaises (A : Module.End ℂ V) : Prop :=
  ∀ i j, bas.repr (A (bas i)) j ≠ 0 → w i+1≤w j

theorem strictRaises_of_shift {A : Module.End ℂ V} {k : ℤ}
    (hA : Shift bas w A k) (hk : 1≤k) : StrictRaises bas w A := by
  intro i j h
  have hh := hA i j h
  omega

theorem strictRaises_smul {A : Module.End ℂ V} (z : ℂ)
    (hA : StrictRaises bas w A) : StrictRaises bas w (z • A) := by
  intro i j h
  apply hA i j
  intro hz
  exact h (by simp [hz])

theorem strictRaises_add {A C : Module.End ℂ V}
    (hA : StrictRaises bas w A) (hC : StrictRaises bas w C) :
    StrictRaises bas w (A+C) := by
  intro i j h
  by_cases ha : bas.repr (A (bas i)) j=0
  · apply hC i j
    intro hc
    exact h (by simp [ha, hc])
  · exact hA i j ha

theorem shift_diagonal (f : I → ℂ) :
    Shift bas w (FiniteSupportEndomorphismCalculus.diagonal bas f) 0 := by
  classical
  intro i j h
  rw [FiniteSupportEndomorphismCalculus.diagonal_basis] at h
  have he : i=j := by
    by_contra he
    exact h (by simp [Module.Basis.repr_self, Finsupp.single_apply, he])
  subst j
  omega

end CoefficientCalculus

abbrev polynomialBasis (t : ℕ) := MvPolynomial.basisMonomials (Variables t) ℂ
abbrev occupationBasis : Module.Basis (Finset ℕ) ℂ Fock := Finsupp.basisSingleOne

theorem multiply_shift {t : ℕ} (x : Variables t) :
    Shift (polynomialBasis t) exponentDegree (LinearMap.mulLeft ℂ (X x)) (variableWeight x) := by
  intro m n h
  exact multiply_support_degree x m n h

theorem derivative_shift {t : ℕ} (x : Variables t) :
    Shift (polynomialBasis t) exponentDegree (pderiv x).toLinearMap (-variableWeight x) := by
  intro m n h
  simpa [sub_eq_add_neg] using derivative_support_degree x m n h

theorem b_shift (n : ℤ) : Shift occupationBasis charge (b n) (-1) := by
  intro S T h
  simpa [sub_eq_add_neg] using b_support_charge n S T h

theorem c_shift (n : ℤ) : Shift occupationBasis charge (c n) 1 := by
  intro S T h
  exact c_support_charge n S T h

/-- Both actual normal-ordering branches have charge degree +1. -/
theorem cubic_shift (p q : ℤ) : Shift occupationBasis charge
    (D5.S3.Quantum.Fermionic.BcGhostBRST.cubic p q) 1 := by
  rw [cubic_eq]
  split_ifs
  · simpa using shift_mul occupationBasis charge
      (shift_mul occupationBasis charge (b_shift (-p-q)) (c_shift p)) (c_shift q)
  · simpa using shift_mul occupationBasis charge
      (shift_mul occupationBasis charge (c_shift p) (c_shift q)) (b_shift (-p-q))

theorem cubicTerm_shift (pq : ℤ × ℤ) : Shift occupationBasis charge
    (D5.S3.Quantum.Fermionic.BcGhostBRST.cubicTerm pq) 1 := by
  unfold D5.S3.Quantum.Fermionic.BcGhostBRST.cubicTerm
  exact shift_smul occupationBasis charge _ (cubic_shift pq.1 pq.2)

/-- Actual locally finite cubic: coefficient extraction commutes with its finite sum.
    This proof uses neither nilpotence nor a ghost-number commutator witness. -/
theorem Qg_shift : Shift occupationBasis charge
    D5.S3.Quantum.Fermionic.BcGhostBRST.Qg 1 := by
  intro S T h
  by_contra hw
  apply h
  change (Finsupp.lapply T : Fock →ₗ[ℂ] ℂ)
    (∑ᶠ pq : ℤ × ℤ, D5.S3.Quantum.Fermionic.BcGhostBRST.cubicTerm pq (ket S))=0
  rw [map_finsum (Finsupp.lapply T)
    (D5.S3.Quantum.Fermionic.BcGhostBRST.cubicTerm_finite (ket S))]
  apply finsum_eq_zero_of_forall_eq_zero
  intro pq
  by_contra hc
  exact hw (cubicTerm_shift pq S T hc)

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
variable (B : Module.Basis (Fin t) ℂ F.K)

/-- Coordinate modes are transported ORIGINAL polynomial operators. -/
abbrev cm (u : E D) (p : Charge D) (n : ℤ) :=
  coordinatePolynomialMode (F.completeBasis B) u p n

theorem cm_plus_negative (p : Charge D) (r : ℕ) (Q : PolynomialCoordinates (Label t)) :
    cm F B F.ePlus p (-(r : ℤ)-1) Q=X (plus t,r)*Q := by
  have h := F.creation_plus B p r ((F.coordinateEquiv B).symm Q)
  rw [fixed_charge_transport, AlgEquiv.apply_symm_apply] at h
  simpa only [AlgEquiv.apply_symm_apply] using h

theorem cm_minus_negative (p : Charge D) (r : ℕ) (Q : PolynomialCoordinates (Label t)) :
    cm F B F.eMinus p (-(r : ℤ)-1) Q=X (minus t,r)*Q := by
  have h := F.creation_minus B p r ((F.coordinateEquiv B).symm Q)
  rw [fixed_charge_transport, AlgEquiv.apply_symm_apply] at h
  simpa only [AlgEquiv.apply_symm_apply] using h

theorem cm_plus_positive (p : Charge D) (r : ℕ) (Q : PolynomialCoordinates (Label t)) :
    cm F B F.ePlus p ((r : ℤ)+1) Q=(r+1 : ℂ) • pderiv (minus t,r) Q := by
  have h := F.annihilation_plus B p r ((F.coordinateEquiv B).symm Q)
  rw [fixed_charge_transport, AlgEquiv.apply_symm_apply] at h
  simpa only [AlgEquiv.apply_symm_apply] using h

theorem cm_minus_positive (p : Charge D) (r : ℕ) (Q : PolynomialCoordinates (Label t)) :
    cm F B F.eMinus p ((r : ℤ)+1) Q=(r+1 : ℂ) • pderiv (plus t,r) Q := by
  have h := F.annihilation_minus B p r ((F.coordinateEquiv B).symm Q)
  rw [fixed_charge_transport, AlgEquiv.apply_symm_apply] at h
  simpa only [AlgEquiv.apply_symm_apply] using h

theorem cm_plus_shift (p : Charge D) (n : ℤ) (hn : n≠0) :
    Shift (polynomialBasis t) exponentDegree (cm F B F.ePlus p n) 1 := by
  cases n with
  | negSucc r =>
    have he : cm F B F.ePlus p (Int.negSucc r)=LinearMap.mulLeft ℂ (X (plus t,r)) := by
      apply LinearMap.ext
      intro Q
      rw [show Int.negSucc r=-(r : ℤ)-1 by omega]
      exact cm_plus_negative F B p r Q
    rw [he]
    simpa using multiply_shift (plus t,r)
  | ofNat k =>
    cases k with
    | zero => exact False.elim (hn rfl)
    | succ r =>
      have he : cm F B F.ePlus p (Int.ofNat (r+1))=
          (r+1 : ℂ) • (pderiv (minus t,r)).toLinearMap := by
        apply LinearMap.ext
        intro Q
        rw [show Int.ofNat (r+1)=(r : ℤ)+1 by simp]
        exact cm_plus_positive F B p r Q
      rw [he]
      exact shift_smul _ _ _ (by simpa using derivative_shift (minus t,r))

theorem cm_minus_shift (p : Charge D) (n : ℤ) (hn : n≠0) :
    Shift (polynomialBasis t) exponentDegree (cm F B F.eMinus p n) (-1) := by
  cases n with
  | negSucc r =>
    have he : cm F B F.eMinus p (Int.negSucc r)=LinearMap.mulLeft ℂ (X (minus t,r)) := by
      apply LinearMap.ext
      intro Q
      rw [show Int.negSucc r=-(r : ℤ)-1 by omega]
      exact cm_minus_negative F B p r Q
    rw [he]
    simpa using multiply_shift (minus t,r)
  | ofNat k =>
    cases k with
    | zero => exact False.elim (hn rfl)
    | succ r =>
      have he : cm F B F.eMinus p (Int.ofNat (r+1))=
          (r+1 : ℂ) • (pderiv (plus t,r)).toLinearMap := by
        apply LinearMap.ext
        intro Q
        rw [show Int.ofNat (r+1)=(r : ℤ)+1 by simp]
        exact cm_minus_positive F B p r Q
      rw [he]
      exact shift_smul _ _ _ (by simpa using derivative_shift (plus t,r))

/-- Zero modes have scalar degree zero, for every original charge, including p=0. -/
theorem cm_zero_shift (u : E D) (p : Charge D) :
    Shift (polynomialBasis t) exponentDegree (cm F B u p 0) 0 := by
  have he : cm F B u p 0 = g D u (chargeVector p) • (1 : Module.End ℂ _) := by
    rfl
  rw [he]
  exact shift_smul _ _ _ (shift_one (polynomialBasis t) exponentDegree)

theorem cm_transverse_shift (u : F.K) (p : Charge D) (n : ℤ) :
    Shift (polynomialBasis t) exponentDegree (cm F B (u : E D) p n) 0 := by
  classical
  cases n with
  | negSucc r =>
    have he : cm F B (u : E D) p (Int.negSucc r)=
        ∑ j : Fin t, B.repr u j • LinearMap.mulLeft ℂ (X (transverse t j,r)) := by
      apply LinearMap.ext
      intro Q
      rw [show Int.negSucc r=-(r : ℤ)-1 by omega]
      have h := F.creation_K B u p r ((F.coordinateEquiv B).symm Q)
      rw [fixed_charge_transport, AlgEquiv.apply_symm_apply] at h
      simpa [Finset.sum_mul, smul_mul_assoc] using h
    rw [he]
    apply shift_sum
    intro j hj
    exact shift_smul _ _ _ (by simpa using multiply_shift (transverse t j,r))
  | ofNat k =>
    cases k with
    | zero => exact cm_zero_shift F B (u : E D) p
    | succ r =>
      have he : cm F B (u : E D) p (Int.ofNat (r+1))=
          (r+1 : ℂ) • ∑ j : Fin t,
            g D (u : E D) (B j : E D) • (pderiv (transverse t j,r)).toLinearMap := by
        apply LinearMap.ext
        intro Q
        rw [show Int.ofNat (r+1)=(r : ℤ)+1 by simp]
        have h := F.annihilation_K B u p r ((F.coordinateEquiv B).symm Q)
        rw [fixed_charge_transport, AlgEquiv.apply_symm_apply] at h
        simpa using h
      rw [he]
      apply shift_smul
      apply shift_sum
      intro j hj
      exact shift_smul _ _ _ (by simpa using derivative_shift (transverse t j,r))

/-- Read actual tensor-basis coefficients, not coefficients in a replacement carrier. -/
theorem sector_coefficient (p : Charge D) (Q : PolynomialCoordinates (Label t))
    (w : Fock) (i : StateIndex D t) :
    (actualBasis F B).repr (sector F B p Q w) i =
      if p=i.1.1 then Q.coeff i.1.2 * w i.2 else 0 := by
  classical
  change ((coordinateMatterBasis (D := D) (t := t)).tensorProduct occupationBasis).repr
    (tensorCoordinates F B (sector F B p Q w)) i = _
  have ht : tensorCoordinates F B (sector F B p Q w) = Finsupp.single p Q ⊗ₜ[ℂ] w := by
    change carrierEquiv (F.completeBasis B)
      (Finsupp.single p ((F.coordinateEquiv B).symm Q)) ⊗ₜ[ℂ] w = _
    rw [carrierEquiv_single]
    simp only [AlgEquiv.apply_symm_apply]
  rw [ht, Module.Basis.tensorProduct_repr_tmul_apply]
  change w i.2 * ((Finsupp.single p Q) i.1.1).coeff i.1.2 = _
  by_cases hp : p=i.1.1 <;> simp [Finsupp.single_apply, hp, mul_comm]

theorem tensor_current_shift (u : E D) (n : ℤ) (G : Module.End ℂ Fock) (a c : ℤ)
    (ha : ∀ p : Charge D, Shift (polynomialBasis t) exponentDegree (cm F B u p n) a)
    (hc : Shift occupationBasis charge G c) :
    Shift (actualBasis F B) degree (tp (D := D) (LatticeLightConeCoordinates.a u n) G) (a+c) := by
  intro i j h
  rcases i with ⟨⟨p,m⟩,S⟩
  rw [actualBasis_apply, sector_current, fixed_charge_transport,
    AlgEquiv.apply_symm_apply, sector_coefficient] at h
  have hp : p=j.1.1 := by
    by_contra hp
    exact h (by simp [hp])
  rw [if_pos hp] at h
  have hm : (cm F B u p n (monomial m 1)).coeff j.1.2 ≠ 0 := (mul_ne_zero_iff.mp h).1
  have hg : (G (ket S)) j.2 ≠ 0 := (mul_ne_zero_iff.mp h).2
  have h1 := ha p m j.1.2 hm
  have h2 := hc S j.2 hg
  dsimp [degree]
  omega

theorem original_plus_c_shift (n k : ℤ) (hn : n≠0) :
    Shift (actualBasis F B) degree (tp (a F.ePlus n) (c k)) 2 := by
  simpa using tensor_current_shift F B F.ePlus n (c k) 1 1
    (fun p => cm_plus_shift F B p n hn) (c_shift k)

theorem original_minus_c_shift (n k : ℤ) (hn : n≠0) :
    Shift (actualBasis F B) degree (tp (a F.eMinus n) (c k)) 0 := by
  simpa using tensor_current_shift F B F.eMinus n (c k) (-1) 1
    (fun p => cm_minus_shift F B p n hn) (c_shift k)

theorem original_plus_b_shift (n k : ℤ) (hn : n≠0) :
    Shift (actualBasis F B) degree (tp (a F.ePlus n) (b k)) 0 := by
  simpa using tensor_current_shift F B F.ePlus n (b k) 1 (-1)
    (fun p => cm_plus_shift F B p n hn) (b_shift k)

theorem original_transverse_c_shift (u : F.K) (n k : ℤ) :
    Shift (actualBasis F B) degree (tp (a (u : E D) n) (c k)) 1 := by
  simpa using tensor_current_shift F B (u : E D) n (c k) 0 1
    (fun p => cm_transverse_shift F B u p n) (c_shift k)

theorem original_plus_matter_shift (n : ℤ) (hn : n≠0) :
    Shift (actualBasis F B) degree (tp (a F.ePlus n) 1) 1 := by
  simpa using tensor_current_shift F B F.ePlus n 1 1 0
    (fun p => cm_plus_shift F B p n hn) (shift_one occupationBasis charge)

theorem original_minus_matter_shift (n : ℤ) (hn : n≠0) :
    Shift (actualBasis F B) degree (tp (a F.eMinus n) 1) (-1) := by
  simpa using tensor_current_shift F B F.eMinus n 1 (-1) 0
    (fun p => cm_minus_shift F B p n hn) (shift_one occupationBasis charge)

theorem original_transverse_matter_shift (u : F.K) (n : ℤ) :
    Shift (actualBasis F B) degree (tp (a (u : E D) n) 1) 0 := by
  simpa using tensor_current_shift F B (u : E D) n 1 0 0
    (fun p => cm_transverse_shift F B u p n) (shift_one occupationBasis charge)

theorem tensor_ghost_shift (G : Module.End ℂ Fock) (k : ℤ)
    (hG : Shift occupationBasis charge G k) :
    Shift (actualBasis F B) degree (tp (1 : Module.End ℂ (Carrier D)) G) k := by
  intro i j h
  rcases i with ⟨⟨p,m⟩,S⟩
  rw [actualBasis_apply, ghost_sector, sector_coefficient] at h
  have hp : p=j.1.1 := by
    by_contra hp
    exact h (by simp [hp])
  rw [if_pos hp] at h
  have hm : m=j.1.2 := by
    by_contra hm
    exact h (by simp [coeff_monomial, hm])
  have hg : (G (ket S)) j.2 ≠ 0 := by
    intro hg
    exact h (by simp [hg])
  have hh := hG S j.2 hg
  dsimp [degree]
  rw [← hm]
  omega

/-- The literal cubic tensor lift has degree +1; no extra c0 is added. -/
theorem original_ghost_cubic_shift : Shift (actualBasis F B) degree
    (tp (1 : Module.End ℂ (Carrier D)) D5.S3.Quantum.Fermionic.BcGhostBRST.Qg) 1 :=
  tensor_ghost_shift F B _ 1 Qg_shift

/-- Each nonzero/nonzero longitudinal cross term in the quadratic matter sum
    has degree +1 after multiplication by the literal c mode. -/
theorem original_cross_c_shift (m n k : ℤ) (hm : m≠0) (hn : n≠0) :
    Shift (actualBasis F B) degree (tp (a F.ePlus m * a F.eMinus n) (c k)) 1 := by
  have he : tp (a F.ePlus m * a F.eMinus n) (c k)=
      tp (a F.ePlus m) 1 * tp (a F.eMinus n) (c k) := by
    simp only [tp, ← TensorProduct.map_mul, one_mul]
  rw [he]
  simpa using shift_mul (actualBasis F B) degree
    (original_plus_matter_shift F B m hm) (original_minus_c_shift F B n k hn)

/-- The other literal normal-ordering order has the same degree. -/
theorem original_reverse_cross_c_shift (m n k : ℤ) (hm : m≠0) (hn : n≠0) :
    Shift (actualBasis F B) degree (tp (a F.eMinus m * a F.ePlus n) (c k)) 1 := by
  have he : tp (a F.eMinus m * a F.ePlus n) (c k)=
      tp (a F.eMinus m) 1 * tp (a F.ePlus n) (c k) := by
    simp only [tp, ← TensorProduct.map_mul, one_mul]
  rw [he]
  simpa using shift_mul (actualBasis F B) degree
    (original_minus_matter_shift F B m hm) (original_plus_c_shift F B n k hn)

theorem original_transverse_pair_c_shift (u v : F.K) (m n k : ℤ) :
    Shift (actualBasis F B) degree
      (tp (a (u : E D) m * a (v : E D) n) (c k)) 1 := by
  have he : tp (a (u : E D) m * a (v : E D) n) (c k)=
      tp (a (u : E D) m) 1 * tp (a (v : E D) n) (c k) := by
    simp only [tp, ← TensorProduct.map_mul, one_mul]
  rw [he]
  simpa using shift_mul (actualBasis F B) degree
    (original_transverse_matter_shift F B u m) (original_transverse_c_shift F B v n k)

/- The real quartet operators are statewise finite sums, not formal infinite sums. -/
theorem family_total_shift {V I : Type*} [AddCommGroup V] [Module ℂ V]
    (bas : Module.Basis I ℂ V) (w : I → ℤ)
    (A : FiniteSupportEndomorphismCalculus.Family V) (k : ℤ)
    (hA : ∀ r, Shift bas w (A.term r) k) : Shift bas w A.total k := by
  classical
  intro i j h
  by_contra hw
  apply h
  change (bas.coord j) (A.total (bas i))=0
  rw [A.total_eq_sum (bas i) (A.bound (bas i)) le_rfl]
  simp only [map_sum, Module.Basis.coord_apply]
  apply Finset.sum_eq_zero
  intro r hr
  by_contra hc
  exact hw (hA r i j hc)

theorem dTerm_shift (r : ℕ) : Shift (actualBasis F B) degree (dTerm F r) 0 := by
  apply shift_add
  · exact original_minus_c_shift F B _ _ (by omega)
  · exact original_minus_c_shift F B _ _ (by omega)

theorem rTerm_shift (r : ℕ) : Shift (actualBasis F B) degree (rTerm F r) 0 := by
  apply shift_smul
  apply shift_add
  · exact original_plus_b_shift F B _ _ (by omega)
  · exact original_plus_b_shift F B _ _ (by omega)

theorem d0_shift (p : Charge D) : Shift (actualBasis F B) degree (d0 F p) 0 := by
  apply shift_smul
  exact family_total_shift _ _ (dFamily F) 0 (dTerm_shift F B)

/-- This support statement needs no inverse-pPlus hypothesis, even though a
    contraction identity does. The zero scalar inverse at pPlus=0 proves no contraction. -/
theorem R_shift (p : Charge D) : Shift (actualBasis F B) degree (R F p) 0 := by
  apply shift_smul
  exact family_total_shift _ _ (rFamily F) 0 (rTerm_shift F B)

theorem invM_shift : Shift (actualBasis F B) degree (invM F B) 0 :=
  shift_diagonal (actualBasis F B) degree _

/-- Genuine original h=R*invM has degree zero, by its finite modes and diagonal inverse. -/
theorem h_shift (p : Charge D) : Shift (actualBasis F B) degree (h F B p) 0 := by
  simpa only [h, add_zero] using shift_mul (actualBasis F B) degree
    (R_shift F B p) (invM_shift F B)

theorem a_add_vectors (u v : E D) (n : ℤ) : a (u+v) n=a u n+a v n := by
  classical
  simp [a, add_smul, Finset.sum_add_distrib]

theorem a_smul_vector (z : ℂ) (u : E D) (n : ℤ) : a (z • u) n=z • a u n := by
  classical
  simp [a, smul_smul, Finset.smul_sum]

/- Actual finite inverse-Gram contractions. These are coefficients of the
   coordinate substitution of the quadratic matter form, before normal-order
   regrouping. The mode regrouping is proved in the companion NullFrame module. -/
def inverseGramPair (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (u v : E D) : ℂ :=
  ∑ i, ∑ j, H i j * g D u (standardBasis D i) * g D v (standardBasis D j)

theorem inverse_covector (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D=1) (v : E D) (i : Fin D.rank) :
    (∑ j, H i j * g D v (standardBasis D j))=v i := by
  classical
  have hg (j : Fin D.rank) :
      g D v (standardBasis D j)=∑ k, (D.G j k : ℂ)*v k := by
    rw [g_symm]
    simp [g, standardBasis, Pi.single_apply]
  have hi (k : Fin D.rank) :
      (∑ j, H i j * (D.G j k : ℂ))=if i=k then 1 else 0 := by
    simpa [Matrix.mul_apply, LatticeSugawaraCurrents.gramComplex, Matrix.one_apply]
      using congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M i k) hHG
  calc
    _ = ∑ k, (∑ j, H i j * (D.G j k : ℂ))*v k := by
      simp_rw [hg, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [← mul_assoc, ← Finset.sum_mul]
    _ = v i := by simp_rw [hi]; simp

theorem inverseGramPair_eq (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D=1) (u v : E D) :
    inverseGramPair H u v=g D u v := by
  classical
  calc
    _ = ∑ i, g D u (standardBasis D i) *
        (∑ j, H i j * g D v (standardBasis D j)) := by
      unfold inverseGramPair
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, g D u (standardBasis D i)*v i := by simp_rw [inverse_covector H hHG]
    _ = g D u v := by simpa only [mul_comm] using g_expand_right D u v

/-- Thus the bad same-sign terms really have zero coefficient in the
    inverse-Gram quadratic form, whereas both longitudinal cross coefficients are one. -/
theorem inverseGram_longitudinal_coefficients
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D=1) :
    inverseGramPair H F.ePlus F.ePlus=0 ∧
    inverseGramPair H F.eMinus F.eMinus=0 ∧
    inverseGramPair H F.ePlus F.eMinus=1 ∧
    inverseGramPair H F.eMinus F.ePlus=1 := by
  simp [inverseGramPair_eq H hHG, F.plus_null, F.minus_null, F.plus_minus]

theorem momentum_current_decomposition (p : Charge D) (n : ℤ) :
    a (chargeVector p) n = F.pMinus p • a F.ePlus n +
      F.pPlus p • a F.eMinus n + a (F.projK (chargeVector p) : E D) n := by
  have hd : chargeVector p = F.pMinus p • F.ePlus +
      F.pPlus p • F.eMinus + (F.projK (chargeVector p) : E D) := by
    rw [coe_projK]
    unfold pPlus pMinus
    abel
  conv_lhs => rw [hd]
  simp only [a_add_vectors, a_smul_vector]

/-- Subtract only the actual pPlus*aMinus*c leading summand. This is a
    component of the desired full remainder, not a new definition of full Q. -/
def momentumRemainder (p : Charge D) (n : ℤ) : Module.End ℂ (State D) :=
  tp (a (chargeVector p) n) (c (-n)) - F.pPlus p • tp (a F.eMinus n) (c (-n))

theorem momentumRemainder_formula (p : Charge D) (n : ℤ) :
    momentumRemainder F p n = F.pMinus p • tp (a F.ePlus n) (c (-n)) +
      tp (a (F.projK (chargeVector p) : E D) n) (c (-n)) := by
  unfold momentumRemainder
  rw [momentum_current_decomposition F p n]
  simp only [tp, TensorProduct.map_add_left, TensorProduct.map_smul_left]
  abel

/-- Actual support raising for the nonzero-mode linear momentum remainder. -/
theorem momentumRemainder_strictRaises (p : Charge D) (n : ℤ) (hn : n≠0) :
    StrictRaises (actualBasis F B) degree (momentumRemainder F p n) := by
  rw [momentumRemainder_formula]
  apply strictRaises_add
  · apply strictRaises_smul
    exact strictRaises_of_shift _ _ (original_plus_c_shift F B n (-n) hn) (by omega)
  · exact strictRaises_of_shift _ _
      (original_transverse_c_shift F B (F.projK (chargeVector p)) n (-n)) (by omega)

/- The companion NullFrame and Endpoints modules prove the finite original
Sugawara regrouping and both endpoint cases. They also prove strict raising for
arbitrary finite endpoint-subtracted matter mode sums plus the original ghost
cubic, and for their product with h, on the indicated fixed-charge inputs.

Still required for original HPL: identify the full locally finite BRST remainder
with those terms; establish actual matter-plus-ghost zero-mode cancellation on
ker b0 and ker totalL0; prove d0, h and delta preserve that literal shell; transport
its actual coefficient bounds to this basis; derive the h delta nilpotence bound;
and supply actual rank-26 Q squared zero and the transverse target maps. No full
delta, full h delta support, transfer, cohomology or no-ghost claim is made here.
The contraction needs pPlus nonzero, whereas these support statements do not.
-/

end D5.S3.VertexAlgebra.LatticeBRSTModeFiltration
