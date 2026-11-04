/- GID: D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeQuartetContraction
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Actual all-frequency tensor quartet contraction by its inverse count. -/

import D5.S3.VertexAlgebra.Lattice.LatticeQuartetOperators

/-! The full quartet zero-count projector and its actual inverse-count homotopy. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.VertexAlgebra.LatticeQuartetContraction
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeLightConeCoordinates
open NullFrame MvPolynomial
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
open scoped BigOperators TensorProduct
variable {D : LatticeData} (F : NullFrame D)

abbrev Variables (t : ℕ) := Label t × ℕ
abbrev Exponents (t : ℕ) := Variables t →₀ ℕ
abbrev CoordinateCarrier (D : LatticeData) (t : ℕ) :=
  Charge D →₀ PolynomialCoordinates (Label t)
abbrev StateIndex (D : LatticeData) (t : ℕ) :=
  (Σ _ : Charge D, Exponents t) × Finset ℕ

variable {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)

/-- Constructed tensor equivalence; integral charge and original ghost factor are unchanged. -/
def tensorCoordinates : State D ≃ₗ[ℂ] (CoordinateCarrier D t ⊗[ℂ] Fock) :=
  TensorProduct.congr (F.allChargeEquiv B) (LinearEquiv.refl ℂ Fock)

def sector (p : Charge D) (Q : PolynomialCoordinates (Label t)) (w : Fock) : State D :=
  Finsupp.single p ((F.coordinateEquiv B).symm Q) ⊗ₜ[ℂ] w

private theorem sector_current (p : Charge D) (Q : PolynomialCoordinates (Label t))
    (w : Fock) (u : E D) (n : ℤ) (G : Module.End ℂ Fock) :
    tp (a u n) G (sector F B p Q w) =
      sector F B p
        (F.coordinateEquiv B (polynomialCurrent u p n ((F.coordinateEquiv B).symm Q))) (G w) := by
  simp only [sector, tp_tmul, a_single, AlgEquiv.symm_apply_apply]

private theorem sector_add (p : Charge D) (Q T : PolynomialCoordinates (Label t)) (w : Fock) :
    sector F B p (Q+T) w = sector F B p Q w + sector F B p T w := by
  simp [sector, TensorProduct.add_tmul]
private theorem sector_smul (p : Charge D) (z : ℂ) (Q : PolynomialCoordinates (Label t)) (w : Fock) :
    sector F B p (z • Q) w = z • sector F B p Q w := by
  simp only [sector, map_smul, ← Finsupp.smul_single, ← TensorProduct.smul_tmul']
theorem sector_smul_right (p : Charge D) (z : ℂ) (Q : PolynomialCoordinates (Label t)) (w : Fock) :
    sector F B p Q (z • w) = z • sector F B p Q w := by
  simp [sector, TensorProduct.tmul_smul]

/-- The displayed x,y derivative and multiplication formulas act on ORIGINAL states. -/
private theorem grouped_coordinate_d (p : Charge D) (r : ℕ)
    (Q : PolynomialCoordinates (Label t)) (w : Fock) :
    dTerm F r (sector F B p Q w) =
      (r+1 : ℂ) • sector F B p (pderiv (plus t,r) Q) (c (-((r : ℤ)+1)) w) +
      sector F B p (X (minus t,r) * Q) (c ((r : ℤ)+1) w) := by
  simp only [dTerm, dm, LinearMap.add_apply, sector_current]
  simp only [F.annihilation_minus B, show -((r : ℤ)+1) = -(r : ℤ)-1 by ring,
    F.creation_minus B, AlgEquiv.apply_symm_apply, sector_smul]
  simp only [neg_sub, sub_neg_eq_add, add_comm]

private theorem grouped_coordinate_R (p : Charge D) (r : ℕ)
    (Q : PolynomialCoordinates (Label t)) (w : Fock) :
    rTerm F r (sector F B p Q w) =
      (r+1 : ℂ)⁻¹ • sector F B p (X (plus t,r) * Q) (b ((r : ℤ)+1) w) +
      sector F B p (pderiv (minus t,r) Q) (b (-((r : ℤ)+1)) w) := by
  have hz : (r+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  simp only [rTerm, rr, LinearMap.smul_apply, LinearMap.add_apply, sector_current]
  simp only [neg_neg]
  simp only [show -((r : ℤ)+1) = -(r : ℤ)-1 by ring,
    show -(-(r : ℤ)-1) = (r : ℤ)+1 by ring,
    F.creation_plus B, F.annihilation_plus B, AlgEquiv.apply_symm_apply, sector_smul,
    smul_add, smul_smul, inv_mul_cancel₀ hz, one_smul]

def coordinateMatterBasis : Module.Basis (Σ _ : Charge D, Exponents t) ℂ
    (CoordinateCarrier D t) :=
  Finsupp.basis (fun _ => MvPolynomial.basisMonomials (Variables t) ℂ)

/-- A genuine basis obtained using the constructed polynomial and tensor equivalences. -/
def actualBasis : Module.Basis (StateIndex D t) ℂ (State D) :=
  ((coordinateMatterBasis (D := D) (t := t)).tensorProduct
    (Finsupp.basisSingleOne : Module.Basis (Finset ℕ) ℂ Fock)).map
      (tensorCoordinates F B).symm

@[simp] theorem actualBasis_apply (p : Charge D) (m : Exponents t) (S : Finset ℕ) :
    actualBasis F B (⟨p,m⟩,S) = sector F B p (monomial m 1) (ket S) := by
  simp [actualBasis, coordinateMatterBasis, Finsupp.coe_basis,
    MvPolynomial.coe_basisMonomials, tensorCoordinates, sector, ket,
    carrierEquiv, Finsupp.mapRange.linearEquiv]
  congr 1
  exact Finsupp.mapRange_single

private theorem basis_expansion (v : State D) :
    (∑ i ∈ ((actualBasis F B).repr v).support,
      (actualBasis F B).repr v i • actualBasis F B i) = v := by
  simpa [Finsupp.linearCombination_apply, Finsupp.sum] using
    (actualBasis F B).linearCombination_repr v

def localDegree (m : Exponents t) (r : ℕ) : ℕ := m (plus t,r) + m (minus t,r)
def frequencies (m : Exponents t) : Finset ℕ := m.support.image Prod.snd
def longitudinalCount (m : Exponents t) : ℕ := ∑ r ∈ frequencies m, localDegree m r
def totalCount (i : StateIndex D t) : ℕ := longitudinalCount i.1.2 + GC.count i.2

private theorem localDegree_zero_outside (m : Exponents t) (r : ℕ) (hr : r ∉ frequencies m) :
    localDegree m r = 0 := by
  have h1 : (plus t,r) ∉ m.support := fun h => hr (Finset.mem_image.mpr ⟨_,h,rfl⟩)
  have h2 : (minus t,r) ∉ m.support := fun h => hr (Finset.mem_image.mpr ⟨_,h,rfl⟩)
  simp [localDegree, Finsupp.notMem_support_iff.mp h1, Finsupp.notMem_support_iff.mp h2]

private theorem sum_localDegree (m : Exponents t) (N : ℕ)
    (hN : ∀ r ∈ frequencies m, r < N) :
    (∑ r ∈ Finset.range N, localDegree m r) = longitudinalCount m := by
  symm
  apply Finset.sum_subset (fun r hr => Finset.mem_range.mpr (hN r hr))
  intro r hr hnot
  exact localDegree_zero_outside m r hnot

private theorem numberTerm_coordinate (p : Charge D) (r : ℕ)
    (Q : PolynomialCoordinates (Label t)) (w : Fock) :
    numberTerm F r (sector F B p Q w) =
      sector F B p (X (plus t,r) * pderiv (plus t,r) Q +
        X (minus t,r) * pderiv (minus t,r) Q) w + sector F B p Q (GC.U (r+1) w) := by
  have hz : (r+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  have ht (A C : Module.End ℂ (Carrier D)) : tp (A*C) (1 : Module.End ℂ Fock) =
      tp A 1 * tp C 1 := by
    simpa [tp] using TensorProduct.map_mul A C (1 : Module.End ℂ Fock) 1
  have hc1 : tp (a F.ePlus (-((r : ℤ)+1)) * a F.eMinus ((r : ℤ)+1)) 1
      (sector F B p Q w) =
      (r+1 : ℂ) • sector F B p (X (plus t,r) * pderiv (plus t,r) Q) w := by
    rw [ht, Module.End.mul_apply, sector_current, F.annihilation_minus B,
      AlgEquiv.apply_symm_apply, sector_smul, map_smul, sector_current,
      show -((r : ℤ)+1) = -(r : ℤ)-1 by ring, F.creation_plus B,
      AlgEquiv.apply_symm_apply]
    rfl
  have hc2 : tp (a F.eMinus (-((r : ℤ)+1)) * a F.ePlus ((r : ℤ)+1)) 1
      (sector F B p Q w) =
      (r+1 : ℂ) • sector F B p (X (minus t,r) * pderiv (minus t,r) Q) w := by
    rw [ht, Module.End.mul_apply, sector_current, F.annihilation_plus B,
      AlgEquiv.apply_symm_apply, sector_smul, map_smul, sector_current,
      show -((r : ℤ)+1) = -(r : ℤ)-1 by ring, F.creation_minus B,
      AlgEquiv.apply_symm_apply]
    rfl
  simp only [tp] at hc1 hc2
  simp only [numberTerm, tp, TensorProduct.map_add_left, LinearMap.add_apply,
    LinearMap.smul_apply]
  change (r+1 : ℂ)⁻¹ • (_ + _) + _ = _
  rw [hc1, hc2, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hz, one_smul, one_smul]
  simp only [sector_add]
  rfl

private theorem numberTerm_basis (r : ℕ) (i : StateIndex D t) :
    numberTerm F r (actualBasis F B i) =
      (localDegree i.1.2 r + GC.localCount (r+1) i.2 : ℕ) • actualBasis F B i := by
  rcases i with ⟨⟨p,m⟩,S⟩
  simp only [actualBasis_apply]
  rw [numberTerm_coordinate, X_mul_pderiv_monomial,
    X_mul_pderiv_monomial, GC.U_ket]
  simp only [← Nat.cast_smul_eq_nsmul ℂ, sector_add, sector_smul,
    sector_smul_right, localDegree, Nat.cast_add, add_smul]

/-- Derived diagonal spectrum, with transverse exponents absent and site-1 holes present. -/
theorem M_basis (i : StateIndex D t) :
    M F (actualBasis F B i) = (totalCount i : ℂ) • actualBasis F B i := by
  classical
  let v := actualBasis F B i
  let N := max (modeBound F v)
    (max ((frequencies i.1.2).sup id + 1) (i.2.sup id + 3))
  have hb : modeBound F v ≤ N := le_max_left _ _
  have hf : ∀ r ∈ frequencies i.1.2, r < N := by
    intro r hr
    have hh : r ≤ (frequencies i.1.2).sup id := Finset.le_sup (f := id) hr
    dsimp [N]
    omega
  have hN3 : 3 ≤ N+1 := by dsimp [N]; omega
  have hS : ∀ j ∈ i.2, j+3 ≤ N+1 := by
    intro j hj
    have hh : j ≤ i.2.sup id := Finset.le_sup (f := id) hj
    dsimp [N]
    omega
  have hg : (∑ r ∈ Finset.range N, GC.localCount (r+1) i.2) = GC.count i.2 := by
    have h := GC.sum_localCount i.2 (N+1) hN3 hS
    rw [Finset.sum_range_succ'] at h
    have hzero : GC.localCount 0 i.2 = 0 := by simp [GC.localCount]
    simpa only [hzero, zero_add, add_zero] using h
  rw [M, (numberFamily F).total_eq_sum v N hb]
  dsimp only [v]
  simp only [numberFamily, numberTerm_basis, ← Nat.cast_smul_eq_nsmul ℂ,
    Nat.cast_add, ← Finset.sum_smul, ← Nat.cast_sum, Finset.sum_add_distrib,
    sum_localDegree i.1.2 N hf, hg]
  simp only [totalCount, Nat.cast_add]

theorem M_eq_number : M F = number (actualBasis F B) totalCount := by
  apply (actualBasis F B).ext
  intro i
  rw [M_basis, number, diagonal_basis]

def P0 : Module.End ℂ (State D) := projectZero (actualBasis F B) totalCount
def invM : Module.End ℂ (State D) := inverseNumber (actualBasis F B) totalCount
def h (p : Charge D) : Module.End ℂ (State D) := R F p * invM F B

theorem spectral_projection_inverse :
    M F * invM F B = 1 - P0 F B ∧ invM F B * M F = 1 - P0 F B ∧
    P0 F B * P0 F B = P0 F B ∧ M F * P0 F B = 0 ∧ invM F B * P0 F B = 0 := by
  simp only [M_eq_number F B]
  exact spectral_identities (actualBasis F B) totalCount

private theorem invM_commutes_d0 (p : Charge D) : invM F B * d0 F p = d0 F p * invM F B := by
  exact commutes_function (actualBasis F B) totalCount (d0 F p)
    (by simpa only [M_eq_number F B] using M_commutes_d0 F p) (fun n => if n = 0 then 0 else (n : ℂ)⁻¹)

private theorem invM_commutes_R (p : Charge D) : invM F B * R F p = R F p * invM F B := by
  exact commutes_function (actualBasis F B) totalCount (R F p)
    (by simpa only [M_eq_number F B] using M_commutes_R F p) (fun n => if n = 0 then 0 else (n : ℂ)⁻¹)

theorem homotopy_contraction (p : Charge D) (hp : F.pPlus p ≠ 0) :
    d0 F p * h F B p + h F B p * d0 F p = 1 - P0 F B := by
  calc
    _ = (d0 F p * R F p + R F p * d0 F p) * invM F B := by
      simp only [h, add_mul, mul_assoc, invM_commutes_d0 F B p]
    _ = M F * invM F B := by rw [original_contraction F p hp]
    _ = _ := (spectral_projection_inverse F B).1

theorem homotopy_square (p : Charge D) : h F B p * h F B p = 0 := by
  calc
    _ = R F p * (invM F B * R F p) * invM F B := by rw [h]; noncomm_ring
    _ = (R F p * R F p) * (invM F B * invM F B) := by
      rw [invM_commutes_R F B p]; noncomm_ring
    _ = 0 := by rw [R_square, zero_mul]

def NoLongitudinal (m : Exponents t) : Prop := ∀ r, m (plus t,r) = 0 ∧ m (minus t,r) = 0

private theorem longitudinalCount_zero_iff (m : Exponents t) :
    longitudinalCount m = 0 ↔ NoLongitudinal m := by
  classical
  constructor
  · intro hm r
    have hd : localDegree m r = 0 := by
      by_cases hr : r ∈ frequencies m
      · have hl := Finset.single_le_sum (fun s (_ : s ∈ frequencies m) =>
          Nat.zero_le (localDegree m s)) hr
        change localDegree m r ≤ longitudinalCount m at hl
        omega
      · exact localDegree_zero_outside m r hr
    exact Nat.add_eq_zero_iff.mp hd
  · intro hm
    apply Finset.sum_eq_zero
    intro r hr
    simp [localDegree, (hm r).1, (hm r).2]

theorem totalCount_zero_iff (i : StateIndex D t) :
    totalCount i = 0 ↔ NoLongitudinal i.1.2 ∧ (i.2 = {1} ∨ i.2 = {1,3}) := by
  simp only [totalCount, Nat.add_eq_zero_iff, longitudinalCount_zero_iff, GC.count_zero_iff]

def transverseVariable (x : Fin t × ℕ) : Variables t := (transverse t x.1,x.2)

theorem transverseVariable_injective : Function.Injective (transverseVariable (t := t)) := by
  intro x y h
  rcases x with ⟨i,r⟩
  rcases y with ⟨j,s⟩
  simpa [transverseVariable, transverse] using h

private theorem noLongitudinal_mapDomain (d : (Fin t × ℕ) →₀ ℕ) :
    NoLongitudinal (d.mapDomain transverseVariable) := by
  intro r
  constructor
  · apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨⟨j,s⟩,h⟩
    simp [transverseVariable, transverse, plus] at h
  · apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨⟨j,s⟩,h⟩
    simp [transverseVariable, transverse, minus] at h

private theorem noLongitudinal_support (m : Exponents t) (hm : NoLongitudinal m) :
    (m.support : Set (Variables t)) ⊆ Set.range transverseVariable := by
  intro x hx
  rcases x with ⟨l,r⟩
  rcases l with u | (u | j)
  · cases u
    exact False.elim ((Finsupp.mem_support_iff.mp hx) (hm r).1)
  · cases u
    exact False.elim ((Finsupp.mem_support_iff.mp hx) (hm r).2)
  · exact ⟨(j,r),rfl⟩

/-- Surjectivity onto precisely the polynomials with no longitudinal variables is constructed. -/
private theorem transverse_monomial_preimage (m : Exponents t) (hm : NoLongitudinal m) :
    ∃ Q : MvPolynomial (Fin t × ℕ) ℂ,
      rename transverseVariable Q = monomial m 1 := by
  refine ⟨monomial (m.comapDomain transverseVariable transverseVariable_injective.injOn) 1, ?_⟩
  rw [rename_monomial, Finsupp.mapDomain_comapDomain transverseVariable
    transverseVariable_injective m (noLongitudinal_support m hm)]

/-- Actual polynomial in the supplied basis of the actual K, inside the original oscillator. -/
def transverseOriginal : MvPolynomial (Fin t × ℕ) ℂ →ₐ[ℂ] Oscillator D :=
  (F.coordinateEquiv B).symm.toAlgHom.comp (rename transverseVariable)

def ghostB0 : Module.End ℂ (State D) := tp 1 (b 0)
def chargeMatter (p : Charge D) : Module.End ℂ (Carrier D) :=
  (Finsupp.lsingle p).comp (Finsupp.lapply p)
def chargeProject (p : Charge D) : Module.End ℂ (State D) := tp (chargeMatter p) 1

theorem ghost_sector (p : Charge D) (Q : PolynomialCoordinates (Label t))
    (w : Fock) (G : Module.End ℂ Fock) :
    tp (1 : Module.End ℂ (Carrier D)) G (sector F B p Q w) = sector F B p Q (G w) := by
  simp [sector]

private theorem chargeProject_basis (p : Charge D) (i : StateIndex D t) :
    chargeProject p (actualBasis F B i) =
      (if i.1.1 = p then (1 : ℂ) else 0) • actualBasis F B i := by
  rcases i with ⟨⟨q,m⟩,S⟩
  simp only [actualBasis_apply]
  by_cases h : q = p
  · subst q
    simp [chargeProject, chargeMatter, sector]
  · simp [chargeProject, chargeMatter, sector, h, Ne.symm h]

theorem chargeProject_diagonal (p : Charge D) : chargeProject (D := D) p =
    diagonal (actualBasis F B) (fun i => if i.1.1 = p then 1 else 0) := by
  apply (actualBasis F B).ext
  intro i
  rw [chargeProject_basis, diagonal_basis]

private theorem fixed_charge_coefficients (p : Charge D) (v : State D) :
    chargeProject p v = v ↔ ∀ i : StateIndex D t, i.1.1 ≠ p → (actualBasis F B).repr v i = 0 := by
  rw [chargeProject_diagonal F B]
  constructor
  · intro h i hi
    have hh := congrArg (fun w => (actualBasis F B).repr w i) h
    simpa [diagonal_coefficient, hi] using hh.symm
  · intro h
    apply (actualBasis F B).repr.injective
    ext i
    by_cases hi : i.1.1 = p
    · simp [diagonal_coefficient, hi]
    · simp [diagonal_coefficient, hi, h i hi]

/-- The literal original b0 kernel is detected, without imposing a physical mass shell. -/
theorem b0_coefficients (v : State D) : ghostB0 v = 0 ↔
    ∀ i : StateIndex D t, 3 ∈ i.2 → (actualBasis F B).repr v i = 0 := by
  classical
  let J : Module.End ℂ (State D) := tp 1 (create 3 * annihilate 3)
  have hJ : J = diagonal (actualBasis F B) (fun i => if 3 ∈ i.2 then 1 else 0) := by
    apply (actualBasis F B).ext
    rintro ⟨⟨p,m⟩,S⟩
    rw [diagonal_basis, actualBasis_apply]
    change tp 1 (create 3 * annihilate 3) (sector F B p (monomial m 1) (ket S)) = _
    rw [ghost_sector,
      D5.S3.Quantum.Fermionic.BcGhostQuartetCount.create_annihilate_ket]
    by_cases h3 : 3 ∈ S <;> simp [h3, sector]
  have hfac : J = tp 1 (create 3) * ghostB0 := by
    simpa [J, ghostB0, GC.b_zero, tp] using
      TensorProduct.map_mul (1 : Module.End ℂ (Carrier D)) 1 (create 3) (annihilate 3)
  constructor
  · intro hb i hi
    have hz : J v = 0 := by rw [hfac, Module.End.mul_apply, hb, map_zero]
    have hh := congrArg (fun w => (actualBasis F B).repr w i) hz
    rw [hJ, diagonal_coefficient] at hh
    simpa [hi] using hh
  · intro hv
    rw [← basis_expansion F B v]
    simp only [map_sum, map_smul]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases h3 : 3 ∈ i.2
    · rw [hv i h3, zero_smul]
    · rcases i with ⟨⟨p,m⟩,S⟩
      rw [actualBasis_apply]
      simp [ghostB0, ghost_sector, GC.b_zero, annihilate_ket, h3, sector]

def groundMap (p : Charge D) : MvPolynomial (Fin t × ℕ) ℂ →ₗ[ℂ] State D :=
  ((TensorProduct.mk ℂ (Carrier D) Fock).flip
    D5.S3.Quantum.Fermionic.BcGhostQuartetCount.c1vac).comp
      ((Finsupp.lsingle p).comp (transverseOriginal F B).toLinearMap)

theorem groundMap_apply (p : Charge D) (Q : MvPolynomial (Fin t × ℕ) ℂ) :
    groundMap F B p Q = Finsupp.single p (transverseOriginal F B Q) ⊗ₜ[ℂ]
      D5.S3.Quantum.Fermionic.BcGhostQuartetCount.c1vac := rfl

theorem groundMap_sector (p : Charge D) (Q : MvPolynomial (Fin t × ℕ) ℂ) :
    groundMap F B p Q = sector F B p (rename transverseVariable Q) (ket {1}) := by
  rw [groundMap_apply, D5.S3.Quantum.Fermionic.BcGhostQuartetCount.c1vac_eq]
  rfl

theorem groundMap_monomial (p : Charge D) (d : (Fin t × ℕ) →₀ ℕ) :
    groundMap F B p (monomial d 1) = actualBasis F B
      (⟨p,d.mapDomain transverseVariable⟩,{1}) := by
  rw [groundMap_sector, rename_monomial, actualBasis_apply]

theorem groundMap_identities (p : Charge D) :
    (M F).comp (groundMap F B p) = 0 ∧ ghostB0.comp (groundMap F B p) = 0 ∧
    (chargeProject p).comp (groundMap F B p) = groundMap F B p := by
  have hq (d : (Fin t × ℕ) →₀ ℕ) : totalCount (D := D)
      (⟨p,d.mapDomain transverseVariable⟩,{1}) = 0 := by
    apply (totalCount_zero_iff _).mpr
    exact ⟨noLongitudinal_mapDomain d, Or.inl rfl⟩
  repeat' constructor
  all_goals
    apply (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ).ext
    intro d
    simp only [MvPolynomial.coe_basisMonomials, LinearMap.comp_apply, groundMap_monomial]
  · rw [M_basis, hq]; simp
  · rw [actualBasis_apply]
    simp [ghostB0, ghost_sector, GC.b_zero, annihilate_ket, sector]
  · rw [chargeProject_basis]
    simp only [if_pos rfl, if_true, one_smul]

/-- Full ghost zero count has two states, before b0 is imposed. -/
private theorem full_zero_count_coefficients (v : State D) : M F v = 0 ↔
    ∀ i ∈ ((actualBasis F B).repr v).support,
      NoLongitudinal i.1.2 ∧ (i.2 = {1} ∨ i.2 = {1,3}) := by
  rw [M_eq_number F B, kernel_number_iff]
  constructor
  · intro h i hi
    apply (totalCount_zero_iff i).mp
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hi) (h i hn)
  · intro h i hn
    by_contra hc
    exact hn ((totalCount_zero_iff i).mpr (h i (Finsupp.mem_support_iff.mpr hc)))

/-- Exact fixed-integral-charge, literal-kerb0 ground; Q is an arbitrary polynomial
in the actual supplied transverse basis. This is not a claim about the physical
relative BRST complex, which additionally needs totalL0 and the actual remainder. -/
theorem literal_relative_ground (p : Charge D) (v : State D) :
    (M F v = 0 ∧ ghostB0 v = 0 ∧ chargeProject p v = v) ↔
      ∃ Q : MvPolynomial (Fin t × ℕ) ℂ,
        v = Finsupp.single p (transverseOriginal F B Q) ⊗ₜ[ℂ]
          D5.S3.Quantum.Fermionic.BcGhostQuartetCount.c1vac := by
  classical
  constructor
  · rintro ⟨hm,hb,hp⟩
    have hground : v ∈ LinearMap.range (groundMap F B p) := by
      rw [← basis_expansion F B v]
      apply Submodule.sum_mem
      intro i hi
      have hm' := (full_zero_count_coefficients F B v).mp hm i hi
      have hb' := (b0_coefficients F B v).mp hb
      have hp' := (fixed_charge_coefficients F B p v).mp hp
      have hcharge : i.1.1 = p := by
        by_contra hn
        exact (Finsupp.mem_support_iff.mp hi) (hp' i hn)
      have hket : i.2 = {1} := by
        rcases hm'.2 with h | h
        · exact h
        · exact False.elim ((Finsupp.mem_support_iff.mp hi) (hb' i (by simp [h])))
      obtain ⟨Q,hQ⟩ := transverse_monomial_preimage i.1.2 hm'.1
      apply Submodule.smul_mem
      refine ⟨Q, ?_⟩
      rw [groundMap_sector, hQ]
      rcases i with ⟨⟨q,m⟩,S⟩
      dsimp at hcharge hket
      subst q
      subst S
      exact (actualBasis_apply F B p m {1}).symm
    obtain ⟨Q,hQ⟩ := hground
    exact ⟨Q, hQ.symm.trans (groundMap_apply F B p Q)⟩
  · rintro ⟨Q,rfl⟩
    change M F (groundMap F B p Q) = 0 ∧ ghostB0 (groundMap F B p Q) = 0 ∧
      chargeProject p (groundMap F B p Q) = groundMap F B p Q
    exact ⟨LinearMap.congr_fun (groundMap_identities F B p).1 Q,
      LinearMap.congr_fun (groundMap_identities F B p).2.1 Q,
      LinearMap.congr_fun (groundMap_identities F B p).2.2 Q⟩

private theorem b0_dm (n : ℤ) (hn : n ≠ 0) : ac (ghostB0 (D := D)) (dm F n) = 0 := by
  have hc : b 0 * c (-n) + c (-n) * b 0 = 0 := by
    simpa [hn] using ghost_mixed_car 0 (-n)
  rw [ghostB0, dm, tp_ac]
  simp only [one_mul, mul_one, sub_self, tp, TensorProduct.map_zero_left, TensorProduct.map_zero_right, hc, add_zero]

private theorem b0_rr (n : ℤ) : ac (ghostB0 (D := D)) (rr F n) = 0 := by
  rw [ghostB0, rr, tp_ac]
  simp only [one_mul, mul_one, sub_self, tp, TensorProduct.map_zero_left, TensorProduct.map_zero_right, ghost_b_car, add_zero]

private theorem b0_unscaledD : ac (ghostB0 (D := D)) (unscaledD F) = 0 := by
  apply Family.total_ac_fixed
  intro r
  simp only [dFamily, dTerm, ac_add_right, b0_dm F _ (by omega : (r : ℤ)+1 ≠ 0), b0_dm F _ (by omega : -((r : ℤ)+1) ≠ 0), add_zero]

private theorem b0_unscaledR : ac (ghostB0 (D := D)) (unscaledR F) = 0 := by
  apply Family.total_ac_fixed
  intro r
  simp [rFamily, rTerm, ac_smul_right, ac_add_right, b0_rr]

theorem b0_d0 (p : Charge D) : ac (ghostB0 (D := D)) (d0 F p) = 0 := by
  rw [d0, ac_smul_right, b0_unscaledD, smul_zero]
private theorem b0_R (p : Charge D) : ac (ghostB0 (D := D)) (R F p) = 0 := by
  rw [R, ac_smul_right, b0_unscaledR, smul_zero]

private theorem odd_even_commutes {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T A C : Module.End ℂ V) (hA : ac T A = 0) (hC : ac T C = 0) :
    T * ac A C = ac A C * T := by
  have hTA : T*A = -(A*T) := eq_neg_iff_add_eq_zero.mpr hA
  have hTC : T*C = -(C*T) := eq_neg_iff_add_eq_zero.mpr hC
  calc
    _ = (T*A)*C + (T*C)*A := by unfold ac; noncomm_ring
    _ = -(A*T)*C + -(C*T)*A := by rw [hTA,hTC]
    _ = -(A*(T*C)) - C*(T*A) := by noncomm_ring
    _ = _ := by rw [hTC,hTA]; unfold ac; noncomm_ring

private theorem M_commutes_b0 : M F * ghostB0 = ghostB0 * M F := by
  simp only [← unscaled_contraction F]
  exact (odd_even_commutes ghostB0 (unscaledD F) (unscaledR F)
    (b0_unscaledD F) (b0_unscaledR F)).symm

private theorem invM_commutes_b0 : invM F B * ghostB0 = ghostB0 * invM F B := by
  exact commutes_function (actualBasis F B) totalCount ghostB0
    (by simpa only [M_eq_number F B] using M_commutes_b0 F) (fun n => if n = 0 then 0 else (n : ℂ)⁻¹)
theorem P0_commutes_b0 : P0 F B * ghostB0 = ghostB0 * P0 F B := by
  exact commutes_function (actualBasis F B) totalCount ghostB0
    (by simpa only [M_eq_number F B] using M_commutes_b0 F) (fun n => if n = 0 then 1 else 0)

private theorem chargeMatter_a (p : Charge D) (u : E D) (n : ℤ) :
    chargeMatter p * a u n = a u n * chargeMatter p := by
  apply Finsupp.lhom_ext
  intro q P
  by_cases hq : q=p
  · subst q
    simp [Module.End.mul_apply, chargeMatter, a_single]
  · simp [Module.End.mul_apply, chargeMatter, a_single, hq, Ne.symm hq]

private theorem chargeProject_current (p : Charge D) (u : E D) (n : ℤ) (G : Module.End ℂ Fock) :
    chargeProject p * tp (a u n) G = tp (a u n) G * chargeProject p := by
  simp only [chargeProject, tp, ← TensorProduct.map_mul, one_mul, mul_one, chargeMatter_a]

theorem chargeProject_d0 (p q : Charge D) :
    chargeProject p * d0 F q = d0 F q * chargeProject p := by
  have hu : chargeProject p * unscaledD F = unscaledD F * chargeProject p := by
    apply Family.total_commutes_fixed
    intro r
    simp [dFamily, dTerm, dm, mul_add, add_mul, chargeProject_current]
  simp only [d0, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hu]

theorem chargeProject_R (p q : Charge D) :
    chargeProject p * R F q = R F q * chargeProject p := by
  have hu : chargeProject p * unscaledR F = unscaledR F * chargeProject p := by
    apply Family.total_commutes_fixed
    intro r
    simp [rFamily, rTerm, rr, mul_add, add_mul, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, chargeProject_current]
  simp only [R, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hu]

private theorem spectral_remaining_identities : P0 F B * M F = 0 ∧
    P0 F B * invM F B = 0 ∧ invM F B * P0 F B = 0 := by
  rw [M_eq_number F B]
  repeat' constructor
  all_goals
    apply (actualBasis F B).ext
    intro i
    by_cases hi : totalCount i=0
    · simp [P0, invM, number, inverseNumber, projectZero, Module.End.mul_apply, hi]
    · simp [P0, invM, number, inverseNumber, projectZero, Module.End.mul_apply, hi]

theorem P0_basis (i : StateIndex D t) : P0 F B (actualBasis F B i) =
    (if totalCount i=0 then (1 : ℂ) else 0) • actualBasis F B i := by
  simp [P0, projectZero]

private theorem P0_commutes_R (p : Charge D) : P0 F B * R F p = R F p * P0 F B := by
  exact commutes_function (actualBasis F B) totalCount (R F p)
    (by simpa only [M_eq_number F B] using M_commutes_R F p) (fun n => if n = 0 then 1 else 0)

theorem h_mul_P0 (p : Charge D) : h F B p * P0 F B = 0 := by
  rw [h, mul_assoc, (spectral_remaining_identities F B).2.2, mul_zero]

theorem P0_mul_h (p : Charge D) : P0 F B * h F B p = 0 := by
  rw [h, ← mul_assoc, P0_commutes_R, mul_assoc,
    (spectral_remaining_identities F B).2.1, mul_zero]

private theorem dTerm_zero_count (r : ℕ) (i : StateIndex D t)
    (hi : totalCount i = 0) : dTerm F r (actualBasis F B i) = 0 := by
  classical
  obtain ⟨hm,hS⟩ := (totalCount_zero_iff i).mp hi
  rcases i with ⟨⟨p,m⟩,S⟩
  have hd : pderiv (plus t,r) (monomial m (1 : ℂ)) = 0 := by
    simp [pderiv_monomial, (hm r).1]
  have hc : c ((r : ℤ)+1) (ket S) = 0 := by
    rcases hS with rfl | rfl
    all_goals
      by_cases hr : r = 0
      · subst r
        simp [GC.c_positive_one]
      · have hr2 : 2 ≤ r+1 := by omega
        have he1 : 2*(r+1-2) ≠ 1 := by omega
        have he3 : 2*(r+1-2) ≠ 3 := by omega
        have hh := GC.c_positive_ge_two (r+1) hr2
        simp only [Nat.cast_add, Nat.cast_one] at hh
        rw [hh]
        simp only [annihilate_ket, Finset.mem_insert, Finset.mem_singleton, he1, he3, or_self, if_false]
  rw [actualBasis_apply, grouped_coordinate_d, hd, hc]
  simp [sector]

theorem d0_mul_P0 (p : Charge D) : d0 F p * P0 F B = 0 := by
  apply (actualBasis F B).ext
  intro i
  change d0 F p (P0 F B (actualBasis F B i)) = 0
  rw [P0_basis]
  by_cases hi : totalCount i = 0
  · simp only [hi, if_pos rfl, if_true, one_smul]
    change F.pPlus p • (dFamily F).total (actualBasis F B i) = 0
    rw [(dFamily F).total_eq_sum _ (modeBound F (actualBasis F B i)) le_rfl]
    simp only [dFamily, dTerm_zero_count F B _ i hi, Finset.sum_const_zero, smul_zero]
  · simp only [if_neg hi, zero_smul, map_zero]

theorem P0_mul_d0 (p : Charge D) : P0 F B * d0 F p = 0 := by
  have hc : P0 F B * d0 F p = d0 F p * P0 F B :=
    commutes_function (actualBasis F B) totalCount (d0 F p)
      (by simpa only [M_eq_number F B] using M_commutes_d0 F p)
      (fun n => if n = 0 then 1 else 0)
  exact hc.trans (d0_mul_P0 F B p)

/-- The actual inverse-count homotopy preserves the literal b0 kernel. -/
theorem b0_h (p : Charge D) : ac (ghostB0 (D := D)) (h F B p) = 0 := by
  change ghostB0 * (R F p * invM F B) + (R F p * invM F B) * ghostB0 = 0
  rw [mul_assoc (R F p) (invM F B) ghostB0, invM_commutes_b0 F B]
  calc
    _ = (ghostB0 * R F p + R F p * ghostB0) * invM F B := by noncomm_ring
    _ = 0 := by rw [← ac, b0_R, zero_mul]

end D5.S3.VertexAlgebra.LatticeQuartetContraction
