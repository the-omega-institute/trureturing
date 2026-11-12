import D5.S3.VertexAlgebra.Lattice.LatticeBRSTPhysicalPairing
import D5.S3.VertexAlgebra.Lattice.LatticeRealNullFrame
import D5.S3.VertexAlgebra.SourceBPZ.TransverseHermitian
import Batteries.Tactic.OpenPrivate

/-!
Initially prepared as a source-only candidate. Ordinary-pairing lemmas for
LatticeBRSTPhysicalTransverseRealization. The argument uses the ORIGINAL
Hm tensor ordinary Hg. Longitudinal boosts are skew-adjoint because BOTH
actual null vectors are real. The degree selection is proved from current
creation/annihilation formulas; it is not a norm-recovery assumption.

Classical attribution: light-cone no-ghost argument of Goddard--Thorn and
Brower, BRST realization of Kato--Ogawa and Lian--Zuckerman. The saved
OriginalQEnergyInclusionPairing suggests the two-slot finite-tail expansion
only; its rotated F and its negative normalization are not used. Current
source-pairing, ghost, real-geometry and Mathlib license notices are retained
in their pinned suppliers. No historical module is imported.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct

open private fixed_charge_transport from
  D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
open private Hm_finset_sum_left Hm_finset_sum_right from
  D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian
open private N_actual_coefficient from
  D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTCohomology

namespace D5.S3.VertexAlgebra.LatticeBRSTInsertedTailOrthogonality

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeLightConeCoordinates
open LatticeLightConeCoordinates.NullFrame LatticeQuartetContraction
open LatticeBRSTModeFiltration LatticeMatterGhostHermitian LatticeBRSTPhysicalPairing
open SourceBPZ.OriginalMatterHermitian
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostHermitian
open D5.S3.Quantum.Fermionic.BcGhostCharge (charge)
open LatticeRelativeBRSTCohomology.Number (N)

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
variable (B : Module.Basis (Fin t) ℂ F.K)

private def matter (p : Charge D) :
    PolynomialCoordinates (Label t) →ₗ[ℂ] Carrier D :=
  (Finsupp.lsingle p).comp (F.coordinateEquiv B).symm.toLinearMap

private theorem matter_current (u : E D) (p : Charge D) (n : ℤ)
    (Q : PolynomialCoordinates (Label t)) :
    a u n (matter F B p Q) = matter F B p (cm F B u p n Q) := by
  rw [show matter F B p Q = Finsupp.single p ((F.coordinateEquiv B).symm Q) from rfl,
    a_single]
  change Finsupp.single p _ = Finsupp.single p _
  congr 1
  apply (F.coordinateEquiv B).injective
  rw [fixed_charge_transport, AlgEquiv.apply_symm_apply]
  change (cm F B u p n) Q =
    (F.coordinateEquiv B) ((F.coordinateEquiv B).symm ((cm F B u p n) Q))
  exact ((F.coordinateEquiv B).apply_symm_apply _).symm

private theorem Hm_real_current (u : E D) (hu : ∀ i, star (u i) = u i)
    (n : ℤ) (x y : Carrier D) : Hm (a u n x) y = Hm x (a u (-n) y) := by
  simp only [a, LinearMap.sum_apply, LinearMap.smul_apply,
    Hm_finset_sum_left, Hm_finset_sum_right, Hm_smul_left, Hm_smul_right,
    starRingEnd_apply, hu, Hm_neutralMode]

/-- A finite frequency boost on the literal original matter carrier. -/
private def boostTerm (r : ℕ) : Module.End ℂ (Carrier D) :=
  (r + 1 : ℂ)⁻¹ •
    (a F.ePlus (-(r : ℤ) - 1) * a F.eMinus ((r : ℤ) + 1) -
      a F.eMinus (-(r : ℤ) - 1) * a F.ePlus ((r : ℤ) + 1))

private theorem boostTerm_matter (p : Charge D) (r : ℕ)
    (Q : PolynomialCoordinates (Label t)) :
    boostTerm F r (matter F B p Q) =
      matter F B p (MvPolynomial.X (plus t, r) * MvPolynomial.pderiv (plus t, r) Q -
        MvPolynomial.X (minus t, r) * MvPolynomial.pderiv (minus t, r) Q) := by
  have hn : (r + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  simp only [boostTerm, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, matter_current, cm_minus_positive, cm_plus_negative,
    cm_plus_positive, cm_minus_negative, mul_smul_comm, map_smul,
    ← smul_sub, smul_smul, inv_mul_cancel₀ hn, one_smul, map_sub]

private theorem boostTerm_monomial (p : Charge D) (r : ℕ) (m : Exponents t) :
    boostTerm F r (matter F B p (MvPolynomial.monomial m 1)) =
      (((m (plus t, r) : ℤ) - m (minus t, r) : ℤ) : ℂ) •
        matter F B p (MvPolynomial.monomial m 1) := by
  rw [boostTerm_matter, MvPolynomial.X_mul_pderiv_monomial,
    MvPolynomial.X_mul_pderiv_monomial]
  simp only [map_sub, map_nsmul, Int.cast_sub, Int.cast_natCast,
    sub_smul, Nat.cast_smul_eq_nsmul]

/-- Ordinary Hm makes the longitudinal boost skew-adjoint, without a Wick
sign convention or any transverse positivity premise. -/
private theorem boostTerm_skew
    (plusReal : ∀ i, star (F.ePlus i) = F.ePlus i)
    (minusReal : ∀ i, star (F.eMinus i) = F.eMinus i)
    (r : ℕ) (x y : Carrier D) :
    Hm (boostTerm F r x) y = -Hm x (boostTerm F r y) := by
  simp only [boostTerm, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, Hm_smul_left, Hm_smul_right]
  have subleft (v w : Carrier D) : Hm (v - w) y = Hm v y - Hm w y := by
    have hn : Hm (-w) y = -Hm w y := by
      simpa only [neg_one_smul, map_neg, map_one, neg_one_mul] using
        Hm_smul_left (-1) w y
    rw [sub_eq_add_neg, Hm_add_left, hn, sub_eq_add_neg]
  have subright (v w : Carrier D) : Hm x (v - w) = Hm x v - Hm x w := by
    have hn : Hm x (-w) = -Hm x w := by
      simpa only [neg_one_smul, neg_one_mul] using Hm_smul_right (-1) x w
    rw [sub_eq_add_neg, Hm_add_right, hn, sub_eq_add_neg]
  rw [subleft, subright,
    Hm_real_current F.ePlus plusReal, Hm_real_current F.eMinus minusReal,
    Hm_real_current F.eMinus minusReal, Hm_real_current F.ePlus plusReal]
  simp only [show -(-(r : ℤ) - 1) = (r : ℤ) + 1 by ring,
    show -((r : ℤ) + 1) = -(r : ℤ) - 1 by ring, starRingEnd_apply, star_inv₀,
    star_add, star_natCast, star_one]
  ring

private theorem degree_frequency_sum (m : Exponents t) (s : Finset ℕ)
    (hs : ∀ x ∈ m.support, x.2 ∈ s) :
    exponentDegree m = ∑ r ∈ s, ((m (plus t, r) : ℤ) - m (minus t, r)) := by
  classical
  have he : exponentDegree m =
      ∑ x ∈ Finset.univ.product s, (m x : ℤ) * variableWeight x := by
    unfold exponentDegree Finsupp.sum
    apply Finset.sum_subset
    · intro x hx
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hs x hx⟩
    · intro x _ hx
      change (m x : ℤ) * variableWeight x = 0
      rw [Finsupp.notMem_support_iff.mp hx, Nat.cast_zero, zero_mul]
  rw [he, Finset.product_eq_sprod, Finset.sum_product Finset.univ s
    (fun x : Variables t => (m x : ℤ) * variableWeight x)]
  simp [variableWeight, plus, minus, Fintype.sum_sum_type,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]

private theorem boostSum_monomial (p : Charge D) (m : Exponents t) (s : Finset ℕ)
    (hs : ∀ x ∈ m.support, x.2 ∈ s) :
    (∑ r ∈ s, boostTerm F r) (matter F B p (MvPolynomial.monomial m 1)) =
      (exponentDegree m : ℂ) • matter F B p (MvPolynomial.monomial m 1) := by
  simp only [LinearMap.sum_apply, boostTerm_monomial, ← Finset.sum_smul]
  rw [degree_frequency_sum m s hs, Int.cast_sum]

/-- Current real-null coordinate selection for the original matter form.
Only a finite union of the two actual monomial frequency supports is used. -/
private theorem Hm_monomial_degree_selection
    (plusReal : ∀ i, star (F.ePlus i) = F.ePlus i)
    (minusReal : ∀ i, star (F.eMinus i) = F.eMinus i)
    (p q : Charge D) (m n : Exponents t)
    (hne : exponentDegree m + exponentDegree n ≠ 0) :
    Hm (matter F B p (MvPolynomial.monomial m 1))
      (matter F B q (MvPolynomial.monomial n 1)) = 0 := by
  classical
  let s := frequencies m ∪ frequencies n
  have hm : ∀ x ∈ m.support, x.2 ∈ s := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hn : ∀ x ∈ n.support, x.2 ∈ s := by
    intro x hx
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  let x := matter F B p (MvPolynomial.monomial m 1)
  let y := matter F B q (MvPolynomial.monomial n 1)
  have skew : Hm ((∑ r ∈ s, boostTerm F r) x) y =
      -Hm x ((∑ r ∈ s, boostTerm F r) y) := by
    simp only [LinearMap.sum_apply, Hm_finset_sum_left, Hm_finset_sum_right,
      boostTerm_skew F plusReal minusReal, Finset.sum_neg_distrib]
  dsimp only [x, y] at skew
  rw [boostSum_monomial F B p m s hm, boostSum_monomial F B q n s hn,
    Hm_smul_left, Hm_smul_right] at skew
  simp only [starRingEnd_apply, star_intCast] at skew
  have eq : (((exponentDegree m + exponentDegree n : ℤ) : ℂ)) * Hm x y = 0 := by
    push_cast
    linear_combination skew
  exact (mul_eq_zero.mp eq).resolve_left (by exact_mod_cast hne)

/-- Direct current ghost computation: the phase at site 3 is minus one. -/
theorem c0_down : c 0 (ket ({1} : Finset ℕ)) = -ket ({1, 3} : Finset ℕ) := by
  norm_num [c, create_ket, phase, lowerCount, Finset.filter_singleton,
    show ({3, 1} : Finset ℕ) = {1, 3} by ext j; simp [or_comm]]

/-- The ordinary Hg normalization is PLUS ONE. No rotated F is used. -/
theorem Hg_down_c0_down : Hg (ket ({1} : Finset ℕ)) (c 0 (ket {1})) = 1 := by
  rw [c0_down, Hg_ket_left, map_neg]
  norm_num [row, rowList, rho, dCreate, daggerMode, tau,
    D5.S3.Quantum.Fermionic.BcGhostHermitian.E,
    mode, create_ket, create, phase, lowerCount, ket, Finset.filter_insert,
    Finset.filter_singleton, Finsupp.lsum_single, LinearMap.smulRight_apply,
    LinearMap.id_apply, Finsupp.single_apply,
    show ({5, 1, 3} : Finset ℕ) = {1, 3, 5} by decide]

/-- Actual ground representatives use precisely the just-computed scalar. -/
theorem inserted_groundMap (p q : Charge D)
    (f g : MvPolynomial (Fin t × ℕ) ℂ) :
    inserted (groundMap F B p f) (groundMap F B q g) =
      Hm (Finsupp.single p (transverseOriginal F B f))
        (Finsupp.single q (transverseOriginal F B g)) := by
  simp only [groundMap_apply,
    D5.S3.Quantum.Fermionic.BcGhostQuartetCount.c1vac_eq,
    inserted, LatticeMatterGhostCoupling.ghostC,
    TensorProduct.map_tmul, LinearMap.id_apply]
  rw [Hmg_tmul, Hg_down_c0_down, mul_one]

private theorem native_one_support (x : State D) (hx : N D x = x)
    (i : StateIndex D t) (hi : (actualBasis F B).repr x i ≠ 0) : charge i.2 = 1 := by
  have he := congrArg (fun v => (actualBasis F B).repr v i) hx
  rw [N_actual_coefficient F B] at he
  have hc : (charge i.2 : ℂ) = 1 := mul_right_cancel₀ hi (he.trans (one_mul _).symm)
  exact_mod_cast hc

private theorem inserted_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → State D) (y : State D) :
    inserted (∑ i ∈ s, f i) y = ∑ i ∈ s, inserted (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, inserted_add_left, ih]

private theorem inserted_sum_right {ι : Type*} (s : Finset ι)
    (x : State D) (f : ι → State D) :
    inserted x (∑ i ∈ s, f i) = ∑ i ∈ s, inserted x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, inserted_add_right, ih]

/-- Both native-ghost-one slots: a strictly positive SUM of current signed
degrees is orthogonal for the ordinary inserted-c0 pairing. This is proved
by finite actual-basis expansions, not postulated for an inclusion. -/
theorem inserted_degree_orthogonal
    (plusReal : ∀ i, star (F.ePlus i) = F.ePlus i)
    (minusReal : ∀ i, star (F.eMinus i) = F.eMinus i)
    (x y : State D) (hx : N D x = x) (hy : N D y = y)
    (a b : ℤ) (hab : 0 < a + b)
    (hl : ∀ i, (actualBasis F B).repr x i ≠ 0 → a ≤ degree i)
    (hr : ∀ i, (actualBasis F B).repr y i ≠ 0 → b ≤ degree i) :
    inserted x y = 0 := by
  classical
  rw [← basis_expand (actualBasis F B) x, inserted_sum_left]
  apply Finset.sum_eq_zero
  intro i hi
  rw [inserted_smul_left]
  have hi' := Finsupp.mem_support_iff.mp hi
  have hil := hl i hi'
  have hci := native_one_support F B x hx i hi'
  suffices inserted (actualBasis F B i) y = 0 by rw [this, mul_zero]
  rw [← basis_expand (actualBasis F B) y, inserted_sum_right]
  apply Finset.sum_eq_zero
  intro j hj
  rw [inserted_smul_right]
  have hj' := Finsupp.mem_support_iff.mp hj
  have hjr := hr j hj'
  have hcj := native_one_support F B y hy j hj'
  have hne : exponentDegree i.1.2 + exponentDegree j.1.2 ≠ 0 := by
    simp only [degree, hci, hcj] at hil hjr
    omega
  have hm := Hm_monomial_degree_selection F B plusReal minusReal
    i.1.1 j.1.1 i.1.2 j.1.2 hne
  rcases i with ⟨⟨p,m⟩,S⟩
  rcases j with ⟨⟨q,n⟩,T⟩
  rw [actualBasis_apply, actualBasis_apply]
  simp only [inserted, sector, LatticeMatterGhostCoupling.ghostC,
    TensorProduct.map_tmul, LinearMap.id_apply, Hmg_tmul]
  change _ * (Hm (matter F B p (MvPolynomial.monomial m 1))
    (matter F B q (MvPolynomial.monomial n 1)) * _) = 0
  rw [hm, zero_mul, mul_zero]

theorem inserted_positive_tail_left
    (plusReal : ∀ i, star (F.ePlus i) = F.ePlus i)
    (minusReal : ∀ i, star (F.eMinus i) = F.eMinus i)
    (tail base : State D) (ht : N D tail = tail) (hb : N D base = base)
    (tl : ∀ i, (actualBasis F B).repr tail i ≠ 0 → 1 ≤ degree i)
    (bl : ∀ i, (actualBasis F B).repr base i ≠ 0 → 0 ≤ degree i) :
    inserted tail base = 0 :=
  inserted_degree_orthogonal F B plusReal minusReal tail base ht hb 1 0 (by norm_num) tl bl

theorem inserted_positive_tail_right
    (plusReal : ∀ i, star (F.ePlus i) = F.ePlus i)
    (minusReal : ∀ i, star (F.eMinus i) = F.eMinus i)
    (base tail : State D) (hb : N D base = base) (ht : N D tail = tail)
    (bl : ∀ i, (actualBasis F B).repr base i ≠ 0 → 0 ≤ degree i)
    (tl : ∀ i, (actualBasis F B).repr tail i ≠ 0 → 1 ≤ degree i) :
    inserted base tail = 0 :=
  inserted_degree_orthogonal F B plusReal minusReal base tail hb ht 0 1 (by norm_num) bl tl

end D5.S3.VertexAlgebra.LatticeBRSTInsertedTailOrthogonality
