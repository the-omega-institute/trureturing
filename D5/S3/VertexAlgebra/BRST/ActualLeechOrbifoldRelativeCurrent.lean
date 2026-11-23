/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeCurrent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeCurrent
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Native current closure and explicit relative BRST boundary primitives -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldModeSuperderivation
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCartanAction
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostNumberCovariance

/-! Native current closure and relative primitives for the original Leech BRST operator. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open ActualLeechOrbifoldCriticalMatter (Matter matter hyperbolicPlane)
open ActualLeechOrbifoldMatter (Orbifold)
open LatticeGeneratingFieldLocality (Charge Carrier)
open LatticeQuartetContraction (chargeProject chargeProject_diagonal actualBasis
  actualBasis_apply tp)
open LatticeMatterGhostCoupling (State ghostB)
open RelativeCohomology (GhostSpace GradedCycles GradedBoundaries GradedCohomology)
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock)
open BcGhostCharge (ghostNumber charge)
open private rightLift_tmul rightSlice_tmul rightSlices_expand rightSlice_chargeProject
  assocQ_preserves_momentum from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone
open private assocQ_reassoc assocN_eq rightSlice_assocN mem_ghostSpace gradedBoundaryMap
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
open private eq_zero_of_all_rightSlices
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightConeDegreeBounds
open private reassoc_ghostB reassoc_parity assocParity assocY_modes term_truncation
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes
open private b_parity from D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyBVSecondOrder
open private assoc_zero_mode_project
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCartanAction
open private charge_one_sign
  from D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostNumberCovariance
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup

abbrev B : Module.End ℂ ComplexState := VirasoroBRST.ghostB matter (-1)
abbrev T : Module.End ℂ ComplexState := VirasoroBRST.Ltotal matter (-1)
abbrev N : Module.End ℂ ComplexState := VirasoroBRST.N matter

/-- Literal descent by the original antighost and mode zero. -/
def current : ComplexState →ₗ[ℂ] Module.End ℂ ComplexState :=
  (originalMode 0).comp B

/-- Fixed points of the existing plane momentum projection. -/
def Momentum (p : Charge hyperbolicPlane) (x : ComplexState) : Prop :=
  rightLift (chargeProject p) (reassoc x) = reassoc x

abbrev Degree (g : ℤ) (x : ComplexState) : Prop := N x = (g : ℂ) • x

/-- The input-translation coefficient identity for the literal total L(-1). -/
abbrev TranslationModeLaw : Prop :=
  ∀ (n : ℤ) (x y : ComplexState),
    originalMode n (T x) y = -(n : ℂ) • originalMode (n - 1) x y

/-- Only the fixed-first Cartan slice of the tensor commutator is needed
for momentum. The two Cartan currents have the orbifold and ghost vacua. -/
abbrev CartanModeLaw : Prop :=
  ∀ (i : Fin 2) (n : ℤ) (x y : ComplexState),
    originalMode 0 (cartanCurrent i) (originalMode n x y) =
      originalMode n (originalMode 0 (cartanCurrent i) x) y +
        originalMode n x (originalMode 0 (cartanCurrent i) y)

private abbrev ghostLift := Module.End.lTensorAlgHom ℂ Fock Matter

private theorem ghost_car (m n : ℤ) (x : ComplexState) :
    VirasoroBRST.ghostB matter m (VirasoroBRST.ghostB matter n x) +
      VirasoroBRST.ghostB matter n (VirasoroBRST.ghostB matter m x) = 0 := by
  have h : ghostLift
      (BcGhostFock.b m * BcGhostFock.b n + BcGhostFock.b n * BcGhostFock.b m) = 0 := by
    rw [BcGhostFock.ghost_b_car, map_zero]
  change ghostLift (BcGhostFock.b m) (ghostLift (BcGhostFock.b n) x) +
    ghostLift (BcGhostFock.b n) (ghostLift (BcGhostFock.b m) x) = 0
  simpa only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.zero_apply] using LinearMap.congr_fun h x

private theorem ghost_square (m : ℤ) (x : ComplexState) :
    VirasoroBRST.ghostB matter m (VirasoroBRST.ghostB matter m x) = 0 := by
  have h : (2 : ℂ) • VirasoroBRST.ghostB matter m (VirasoroBRST.ghostB matter m x) = 0 := by
    simpa only [two_smul] using ghost_car m m x
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

private theorem ward (r : ℤ) (x : ComplexState) :
    Q (VirasoroBRST.ghostB matter r x) + VirasoroBRST.ghostB matter r (Q x) =
      VirasoroBRST.Ltotal matter r x :=
  LinearMap.congr_fun (VirasoroBRST.Q_ward_b matter r) x

private theorem Q_sq (x : ComplexState) : Q (Q x) = 0 := by
  simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun Q_squared x

private theorem Q_T (x : ComplexState) : Q (T x) = T (Q x) := by
  rw [← ward (-1) x, ← ward (-1) (Q x)]
  simp only [map_add, Q_sq, map_zero, zero_add, add_zero]

private theorem E_b (r : ℤ) (x : ComplexState) :
    E (VirasoroBRST.ghostB matter r x) =
      VirasoroBRST.ghostB matter r (E x) - (r : ℂ) • VirasoroBRST.ghostB matter r x := by
  have h (a : Matter) (w : Fock) :
      E (VirasoroBRST.ghostB matter r (a ⊗ₜ[ℂ] w)) -
        VirasoroBRST.ghostB matter r (E (a ⊗ₜ[ℂ] w)) =
        -(r : ℂ) • VirasoroBRST.ghostB matter r (a ⊗ₜ[ℂ] w) := by
    have hw := LinearMap.congr_fun (BcGhostVirasoro.ward_b 0 r) w
    have ht := congrArg (fun z : Fock => a ⊗ₜ[ℂ] z) hw
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      zero_sub, Int.cast_neg, zero_add, TensorProduct.tmul_sub, TensorProduct.tmul_smul] at ht
    simp only [E, VirasoroBRST.Ltotal, VirasoroBRST.matterMode, VirasoroBRST.ghostVirasoro,
      VirasoroBRST.ghostB, BcGhostChargeTensor.B, BcGhostChargeTensor.liftGhost,
      LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply, map_add]
    convert ht using 1
    abel
  have hl : E * VirasoroBRST.ghostB matter r - VirasoroBRST.ghostB matter r * E =
      -(r : ℂ) • VirasoroBRST.ghostB matter r := TensorProduct.ext' h
  have hx : E (VirasoroBRST.ghostB matter r x) - VirasoroBRST.ghostB matter r (E x) =
      -(r : ℂ) • VirasoroBRST.ghostB matter r x := LinearMap.congr_fun hl x
  rw [neg_smul] at hx
  rw [sub_eq_iff_eq_add, neg_add_eq_sub] at hx
  exact hx

private theorem E_T (x : ComplexState) : E (T x) = T (E x) + T x := by
  have commute : ∀ y : ComplexState, Q (E y) = E (Q y) := by
    intro y
    rw [← ward 0 y, ← ward 0 (Q y)]
    simp only [map_add, Q_sq, map_zero, zero_add, add_zero]
  have hB (y : ComplexState) : E (B y) = B (E y) + B y := by
    simpa only [Int.cast_neg, Int.cast_one, neg_smul, one_smul, sub_neg_eq_add]
      using E_b (-1) y
  calc
    E (T x) = E (Q (B x)) + E (B (Q x)) := by rw [← ward (-1), map_add]
    _ = Q (B (E x)) + B (Q (E x)) + (Q (B x) + B (Q x)) := by
      rw [← commute (B x), hB x, hB (Q x), ← commute x, map_add]
      abel
    _ = T (E x) + T x := by rw [ward (-1) (E x), ward (-1) x]

private theorem N_reassoc (x : ComplexState) :
    reassoc (N x) = RelativeCohomology.assocN (reassoc x) := by
  change _ = reassoc (N (reassoc.symm (reassoc x)))
  rw [reassoc.symm_apply_apply]

private theorem degree_b {g : ℤ} {x : ComplexState} (r : ℤ) (hx : Degree g x) :
    Degree (g - 1) (VirasoroBRST.ghostB matter r x) := by
  have h := congrArg ghostLift (BcGhostCharge.ghost_number_relations.2.1 r)
  simp only [map_sub, map_mul, map_neg] at h
  have h' : N (VirasoroBRST.ghostB matter r x) -
      VirasoroBRST.ghostB matter r (N x) = -VirasoroBRST.ghostB matter r x :=
    LinearMap.congr_fun h x
  rw [hx, map_smul] at h'
  unfold Degree
  rw [Int.cast_sub, Int.cast_one, sub_smul, one_smul]
  exact (sub_eq_iff_eq_add.mp h').trans (by abel)

private theorem degree_Q {g : ℤ} {x : ComplexState} (hx : Degree g x) :
    Degree (g + 1) (Q x) := by
  have h : N (Q x) - Q (N x) = Q x :=
    LinearMap.congr_fun (VirasoroBRST.N_Q matter) x
  rw [hx, map_smul] at h
  change N (Q x) = ((g + 1 : ℤ) : ℂ) • Q x
  rw [Int.cast_add, Int.cast_one, add_smul, one_smul, add_comm]
  exact sub_eq_iff_eq_add.mp h

private theorem degree_T {g : ℤ} {x : ComplexState} (hx : Degree g x) : Degree g (T x) := by
  have h₁ := degree_Q (degree_b (-1) hx)
  have h₂ := degree_b (-1) (degree_Q hx)
  rw [sub_add_cancel] at h₁
  rw [add_sub_cancel_right] at h₂
  rw [← ward (-1) x]
  change N (Q (B x)) = (g : ℂ) • Q (B x) at h₁
  change N (B (Q x)) = (g : ℂ) • B (Q x) at h₂
  simp only [Degree, map_add, h₁, h₂, smul_add]

/-- Native ghost number one determines bc parity on arbitrary orbifold tensors. -/
theorem odd_of_degree_one {x : ComplexState} (hx : Degree 1 x) :
    originalParity x = -x := by
  classical
  have hN : RelativeCohomology.assocN (reassoc x) = reassoc x := by
    rw [← N_reassoc, show N x = x by simpa only [Degree, Int.cast_one, one_smul] using hx]
  let sl := rightSlice planeFrame planeBasis
  have support_charge (i) (hi : sl i (reassoc x) ≠ 0) : charge i.2 = 1 := by
    have h := congrArg (sl i) hN
    rw [rightSlice_assocN planeFrame planeBasis] at h
    change (charge i.2 : ℂ) • sl i (reassoc x) = sl i (reassoc x) at h
    have he := smul_left_injective ℂ hi (h.trans (one_smul ℂ _).symm)
    exact_mod_cast he
  have basis_parity (i) :
      LatticeMatterGhostStateField.parity hyperbolicPlane (actualBasis planeFrame planeBasis i) =
        (-1 : ℂ)^i.2.card • actualBasis planeFrame planeBasis i := by
    rcases i with ⟨⟨p, m⟩, S⟩
    simp only [actualBasis_apply, LatticeQuartetContraction.sector,
      LatticeMatterGhostStateField.parity, TensorProduct.map_tmul, LinearMap.id_apply,
      parity_ket, TensorProduct.tmul_smul]
  apply reassoc.injective
  refine (reassoc_parity x).trans (Eq.trans ?_ (reassoc.map_neg x).symm)
  let z := reassoc x
  change assocParity z = -z
  let f := fun i => sl i z ⊗ₜ[ℂ] actualBasis planeFrame planeBasis i
  let indices := (rightSlices planeFrame planeBasis z).support
  have hz : z = ∑ i ∈ indices, f i := rightSlices_expand planeFrame planeBasis z
  calc
    assocParity z = ∑ i ∈ indices, assocParity (f i) := by
      exact (congrArg assocParity hz).trans (map_sum _ _ _)
    _ = ∑ i ∈ indices, -f i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hn : sl i z ≠ 0 := Finsupp.mem_support_iff.mp hi
      change rightLift _ (sl i z ⊗ₜ[ℂ] actualBasis planeFrame planeBasis i) = _
      rw [rightLift_tmul, basis_parity, charge_one_sign i.2 (support_charge i hn),
        neg_one_smul, TensorProduct.tmul_neg]
    _ = -z := (Finset.sum_neg_distrib _).trans (congrArg Neg.neg hz.symm)

/-- Applying the literal odd b mode to a degree-one state produces an even current. -/
theorem even_B_of_degree_one {x : ComplexState} (hx : Degree 1 x) :
    originalParity (B x) = B x := by
  apply reassoc.injective
  have hp : assocParity (reassoc x) = -reassoc x :=
    (reassoc_parity x).symm.trans
      ((congrArg reassoc (odd_of_degree_one hx)).trans (reassoc.map_neg x))
  rw [reassoc_parity, reassoc_ghostB]
  change rightLift (LatticeMatterGhostStateField.parity hyperbolicPlane)
      (rightLift (ghostB hyperbolicPlane (-1)) (reassoc x)) =
    rightLift (ghostB hyperbolicPlane (-1)) (reassoc x)
  have h : ∀ z : AssocState,
      assocParity (rightLift (ghostB hyperbolicPlane (-1)) z) =
        -rightLift (ghostB hyperbolicPlane (-1)) (assocParity z) := by
    intro z
    have hb : LatticeMatterGhostStateField.parity hyperbolicPlane * ghostB hyperbolicPlane (-1) =
        -(ghostB hyperbolicPlane (-1) * LatticeMatterGhostStateField.parity hyperbolicPlane) :=
      LinearMap.ext (b_parity hyperbolicPlane (-1))
    have hl := congrArg rightLift hb
    simpa only [map_mul, map_neg, LinearMap.neg_apply, Module.End.mul_apply] using
      LinearMap.congr_fun hl z
  exact (h _).trans (by rw [hp, map_neg, neg_neg])

private theorem momentum_b {p : Charge hyperbolicPlane} {x : ComplexState}
    (r : ℤ) (hx : Momentum p x) : Momentum p (VirasoroBRST.ghostB matter r x) := by
  have h : chargeProject p * ghostB hyperbolicPlane r =
      ghostB hyperbolicPlane r * chargeProject p := by
    apply TensorProduct.ext'
    intro a w
    rfl
  have hl := congrArg rightLift h
  simp only [map_mul] at hl
  unfold Momentum at hx ⊢
  rw [reassoc_ghostB]
  simpa only [Module.End.mul_apply, hx, reassoc_ghostB] using
    LinearMap.congr_fun hl (reassoc x)

private theorem momentum_Q {p : Charge hyperbolicPlane} {x : ComplexState}
    (hx : Momentum p x) : Momentum p (Q x) := by
  unfold Momentum at hx ⊢
  rw [← assocQ_reassoc]
  exact assocQ_preserves_momentum planeFrame planeBasis p hx

private theorem momentum_T {p : Charge hyperbolicPlane} {x : ComplexState}
    (hx : Momentum p x) : Momentum p (T x) := by
  have h₁ := momentum_Q (momentum_b (-1) hx)
  have h₂ := momentum_b (-1) (momentum_Q hx)
  rw [← ward (-1) x]
  simp only [Momentum, map_add] at h₁ h₂ ⊢
  rw [h₁, h₂]

private theorem cartan_scalar {p : Charge hyperbolicPlane} {x : ComplexState}
    (i : Fin 2) (hx : Momentum p x) :
    originalMode 0 (cartanCurrent i) x = cartanEigenvalue i p • x := by
  rw [← ghostB_minus_one_u]
  exact cartan_zero_mode_of_momentum i p x hx

private theorem momentum_of_cartan {p : Charge hyperbolicPlane} {x : ComplexState}
    (hx : ∀ i : Fin 2, originalMode 0 (cartanCurrent i) x = cartanEigenvalue i p • x) :
    Momentum p x := by
  classical
  let sl := rightSlice planeFrame planeBasis
  let z := reassoc x
  have eig (k : Fin 2) (i) :
      sl i (reassoc (originalMode 0 (cartanCurrent k) x)) =
        cartanEigenvalue k i.1.1 • sl i z := by
    have h : ∀ (y : AssocState),
        sl i (rightLift (tp (LatticeFiniteNegativeGeneration.neutralMode hyperbolicPlane k 0)
          LinearMap.id) y) = cartanEigenvalue k i.1.1 • sl i y := by
      intro y
      conv_lhs => rw [rightSlices_expand planeFrame planeBasis y]
      conv_rhs => rw [rightSlices_expand planeFrame planeBasis y]
      simp only [map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hpj : rightLift (chargeProject j.1.1)
          (sl j y ⊗ₜ[ℂ] actualBasis planeFrame planeBasis j) =
            sl j y ⊗ₜ[ℂ] actualBasis planeFrame planeBasis j := by
        rw [rightLift_tmul]
        have hh := LinearMap.congr_fun (chargeProject_diagonal planeFrame planeBasis j.1.1)
          (actualBasis planeFrame planeBasis j)
        rw [D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus.diagonal_basis,
          ite_eq_left rfl, one_smul] at hh
        rw [hh]
      have hj := LinearMap.congr_fun (assoc_zero_mode_project k j.1.1)
        (sl j y ⊗ₜ[ℂ] actualBasis planeFrame planeBasis j)
      simp only [Module.End.mul_apply, hpj, LinearMap.smul_apply] at hj
      rw [hj, map_smul, rightSlice_tmul, Module.Basis.repr_self_apply]
      by_cases hij : i = j
      · subst j
        rfl
      · simp [Ne.symm hij]
    rw [← originalAntighost_zero_u, reassoc_cartan_mode]
    exact h z
  unfold Momentum
  apply sub_eq_zero.mp
  apply eq_zero_of_all_rightSlices planeFrame planeBasis
  intro i
  rw [map_sub, rightSlice_chargeProject planeFrame planeBasis]
  by_cases hi : i.1.1 = p
  · simp [hi]
  · rw [ite_eq_right hi]
    have hz : sl i z = 0 := by
      by_contra hn
      apply hi
      have hc (k : Fin 2) : cartanEigenvalue k i.1.1 = cartanEigenvalue k p := by
        have h := eig k i
        rw [hx k, map_smul, map_smul] at h
        exact smul_left_injective ℂ hn h.symm
      have h0 := hc 0
      have h1 := hc 1
      rw [(cartanEigenvalue_coordinates _).1, (cartanEigenvalue_coordinates p).1] at h0
      rw [(cartanEigenvalue_coordinates _).2, (cartanEigenvalue_coordinates p).2] at h1
      funext k
      fin_cases k
      · exact_mod_cast h1
      · exact_mod_cast h0
    change 0 - sl i z = 0
    rw [hz, sub_zero]

private abbrev planeN := BcGhostChargeTensor.number (M := Carrier hyperbolicPlane)

private theorem plane_number_mode (n : ℤ) (x y : State hyperbolicPlane) :
    planeN (((LatticeMatterGhostStateField.Y hyperbolicPlane x)[[n]]) y) =
      ((LatticeMatterGhostStateField.Y hyperbolicPlane (planeN x))[[n]]) y +
        ((LatticeMatterGhostStateField.Y hyperbolicPlane x)[[n]]) (planeN y) :=
  Lattice.PhysicalLie.LatticeMatterGhostNumberCovariance.number_mode hyperbolicPlane x y n

open private term term_tmul term_finite
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes

section Cartan
open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldMatter (leechUnit)
open TwistedGround.Orbifold
open CountableOccupationFock (vacuum)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open LatticeMatterGhostSignedBorcherds (mu_D jacobiLeftTerm)
open private assoc_vacuum_left from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes

private abbrev planeCartan (i : Fin 2) : State hyperbolicPlane :=
  LatticeZeroMomentumBRST.current hyperbolicPlane i ⊗ₜ[ℂ] vacuum

private theorem plane_cartan_derivation (i : Fin 2) (n : ℤ) (x y : State hyperbolicPlane) :
    let a := planeCartan i
    let Y := LatticeMatterGhostStateField.Y hyperbolicPlane
    ((Y a)[[0]]) (((Y x)[[n]]) y) =
      ((Y (((Y a)[[0]]) x))[[n]]) y + ((Y x)[[n]]) (((Y a)[[0]]) y) := by
  let D := hyperbolicPlane
  let a := planeCartan i
  let P := LatticeMatterGhostStateField.parity D
  let m := LatticeBRSTCohomologyField.originalMode D
  change m 0 a (m n x y) = m n (m 0 a x) y + m n x (m 0 a y)
  have even : P a = a := by
    simp [P, a, planeCartan, LatticeMatterGhostStateField.parity,
      TensorProduct.map_tmul, CountableOccupationFock.vacuum, parity_ket]
  have h₀ : (2 : ℂ)⁻¹ • (a + P a) = a := by rw [even]; module
  have h₁ : (2 : ℂ)⁻¹ • (a - P a) = 0 := by rw [even, sub_self, smul_zero]
  have law := (LatticeMatterGhostBorcherds.borcherds D a x y 0 n 0).2.2.2.2
  dsimp only at law
  rw [h₀, h₁, finsum_eq_single _ 0, finsum_eq_single _ 0] at law
  · have h : m n (m 0 a x) y = m 0 a (m n x y) - m n x (m 0 a y) := by
      simpa [m, jacobiLeftTerm, mu_D, integerBinomial, epsilon,
        ← LatticeBRSTCohomologyField.originalMode_apply] using law
    exact (eq_sub_iff_add_eq.mp h).symm
  · intro j hj
    simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hj)]
  · intro j hj
    simp [jacobiLeftTerm, integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hj)]

private theorem assoc_cartan_derivation (i : Fin 2) (n : ℤ) (x y : AssocState) :
    let A := rightLift ((LatticeMatterGhostStateField.Y hyperbolicPlane (planeCartan i))[[0]])
    A (((assocY x)[[n]]) y) = ((assocY (A x))[[n]]) y + ((assocY x)[[n]]) (A y) := by
  let A := rightLift ((LatticeMatterGhostStateField.Y hyperbolicPlane (planeCartan i))[[0]])
  change A (((assocY x)[[n]]) y) = ((assocY (A x))[[n]]) y + ((assocY x)[[n]]) (A y)
  induction x using TensorProduct.inductionOn with
  | tmul u a =>
    induction y using TensorProduct.inductionOn with
    | tmul v b =>
      simp only [assocY_modes]
      rw [map_finsum A (term_finite (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b) n),
        ← finsum_add_distrib (term_finite (A (u ⊗ₜ[ℂ] a)) (v ⊗ₜ[ℂ] b) n)
          (term_finite (u ⊗ₜ[ℂ] a) (A (v ⊗ₜ[ℂ] b)) n)]
      apply finsum_congr
      intro k
      dsimp only [A]
      simp only [rightLift_tmul, term_tmul, plane_cartan_derivation, TensorProduct.tmul_add]
    | add x y hx hy =>
      simp only [map_add, hx, hy] <;> abel
  | add x z hx hz =>
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, hx, hz]
    abel

/-- A Cartan zero mode has vacuum on the orbifold factor. Its plane-ghost
commutator acts termwise through the actual finite tensor convolution. -/
theorem cartan_mode : CartanModeLaw := by
  intro i n x y
  have h (z : ComplexState) :
      reassoc (originalMode 0 (cartanCurrent i) z) =
        rightLift ((LatticeMatterGhostStateField.Y hyperbolicPlane (planeCartan i))[[0]])
          (reassoc z) := by
    rw [reassoc_originalMode]
    change ((assocY (OriginalOrbifoldField.vacuumState leechData leechUnit ⊗ₜ[ℂ]
      planeCartan i))[[0]]) (reassoc z) = _
    rw [assoc_vacuum_left]
  apply reassoc.injective
  rw [h, map_add, reassoc_originalMode n x y,
    reassoc_originalMode n (originalMode 0 (cartanCurrent i) x) y,
    reassoc_originalMode n x (originalMode 0 (cartanCurrent i) y), h x, h y]
  exact assoc_cartan_derivation i n (reassoc x) (reassoc y)

end Cartan

private theorem momentum_mode (n : ℤ)
    {p q : Charge hyperbolicPlane} {x y : ComplexState} (hx : Momentum p x) (hy : Momentum q y) :
    Momentum (p + q) (originalMode n x y) := by
  apply momentum_of_cartan
  intro i
  have hadd : cartanEigenvalue i (p + q) = cartanEigenvalue i p + cartanEigenvalue i q := by
    fin_cases i
    · change cartanEigenvalue 0 (p + q) = cartanEigenvalue 0 p + cartanEigenvalue 0 q
      simp only [(cartanEigenvalue_coordinates _).1, Pi.add_apply, Int.cast_add]
    · change cartanEigenvalue 1 (p + q) = cartanEigenvalue 1 p + cartanEigenvalue 1 q
      simp only [(cartanEigenvalue_coordinates _).2, Pi.add_apply, Int.cast_add]
  rw [cartan_mode, cartan_scalar i hx, cartan_scalar i hy, hadd]
  simp only [map_smul, LinearMap.smul_apply, add_smul]

private theorem assoc_number_mode (n : ℤ) (x y : AssocState) :
    rightLift planeN (((assocY x)[[n]]) y) =
      ((assocY (rightLift planeN x))[[n]]) y + ((assocY x)[[n]]) (rightLift planeN y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a u =>
    induction y using TensorProduct.inductionOn with
    | tmul b v =>
      simp only [assocY_modes]
      rw [map_finsum (rightLift planeN) (term_finite (a ⊗ₜ[ℂ] u) (b ⊗ₜ[ℂ] v) n),
        ← finsum_add_distrib (term_finite (rightLift planeN (a ⊗ₜ[ℂ] u)) (b ⊗ₜ[ℂ] v) n)
          (term_finite (a ⊗ₜ[ℂ] u) (rightLift planeN (b ⊗ₜ[ℂ] v)) n)]
      apply finsum_congr
      intro k
      simp only [rightLift_tmul, term_tmul, plane_number_mode, TensorProduct.tmul_add]
    | add y z hy hz =>
      simp only [map_add, hy, hz]
      abel
  | add x z hx hz =>
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, hx, hz]
    abel

private theorem degree_mode (n : ℤ) {g h : ℤ} {x y : ComplexState}
    (hx : Degree g x) (hy : Degree h y) : Degree (g + h) (originalMode n x y) := by
  have law : N (originalMode n x y) =
      originalMode n (N x) y + originalMode n x (N y) := by
    apply reassoc.injective
    have hN : RelativeCohomology.assocN = rightLift planeN := by
      rw [assocN_eq]
      rfl
    simpa only [N_reassoc, hN, reassoc_originalMode, map_add] using
      assoc_number_mode n (reassoc x) (reassoc y)
  rw [hx, hy] at law
  simpa only [Degree, Int.cast_add, add_smul, map_smul, LinearMap.smul_apply] using law

section Translation
open ActualLeechHyperbolic (leechData leech_spec)
open ActualLeechOrbifoldMatter (leechUnit leechPosDef)
open ActualLeechOrbifoldCriticalMatter (hyperbolicMatter)
open TwistedGround.Orbifold
open LatticeSugawaraCurrents (gramComplex)
open private stress_fixed_mode stress_twisted_mode
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTranslation
open private matter_mode_tmul
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone
open private plane_inverse
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCriticalMatter
open private translation_tmul
  from D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField
open private charge_parity from D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyField
open private parity_square from D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBRSTDerivation

private abbrev orbT := OriginalOrbifoldTranslation.T leechData leechUnit
private abbrev planeT := LatticeMatterGhostStateField.translation hyperbolicPlane
private abbrev orbY := OriginalOrbifoldField.Y leechData leechUnit leechPosDef
private abbrev planeY := LatticeMatterGhostStateField.Y hyperbolicPlane
private abbrev assocT :=
  orbT.rTensor (State hyperbolicPlane) + rightLift planeT

private theorem orb_translation_is_L :
    ActualLeechOrbifoldMatter.mode (-1) = orbT := by
  apply LinearMap.ext
  intro v
  rw [ActualLeechOrbifoldMatter.mode, show (-1 + 1 : ℤ) = 0 by norm_num]
  change ((orbY (ActualLeechOrbifoldMatter.omega.1, 0))[[0]]) v = orbT v
  rw [OriginalOrbifoldField.Y_fixed_ncoeff_apply, OriginalOrbifoldTranslation.T_apply,
    stress_fixed_mode, stress_twisted_mode]
  exact leechUnit

private theorem plane_translation_is_L :
    hyperbolicMatter.mode (-1) = LatticeSugawaraConformal.translation hyperbolicPlane :=
  LatticeSugawaraConformal.sugawaraMode_minus_one_eq_translation hyperbolicPlane _ plane_inverse
    plane_inverse

private theorem reassoc_T (x : ComplexState) : reassoc (T x) = assocT (reassoc x) := by
  have h : reassoc.toLinearMap.comp T = assocT.comp reassoc.toLinearMap := by
    apply TensorProduct.ext'
    intro z w
    induction z using TensorProduct.inductionOn with
    | tmul u a =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        VirasoroBRST.matterMode, VirasoroBRST.ghostVirasoro, LinearMap.add_apply,
        TensorProduct.map_tmul, LinearMap.id_apply, matter_mode_tmul, TensorProduct.add_tmul,
        map_add, reassoc, TensorProduct.assoc_tmul, LinearMap.rTensor_tmul, rightLift_tmul,
        translation_tmul, orb_translation_is_L, plane_translation_is_L, TensorProduct.tmul_add]
      abel
    | add u v hu hv =>
      simp only [TensorProduct.add_tmul, map_add, hu, hv]
  exact LinearMap.congr_fun h x

private theorem plane_translation_modes (n : ℤ) (x y : State hyperbolicPlane) :
    ((planeY (planeT x))[[n]]) y = -(n : ℂ) • ((planeY x)[[n - 1]]) y := by
  let D := hyperbolicPlane
  let H := gramComplex D
  let C := LatticeBRST.totalCharge D H
  let b := ghostB D (-1)
  let P := LatticeMatterGhostStateField.parity D
  let m := LatticeBRSTCohomologyField.originalMode D n
  have hB (s v : State D) : b (m s v) = m (b s) v + m (P s) (b v) :=
    Lattice.PhysicalLie.LatticeBRSTCurrentIdentities.b_minus_one_mode D s v n
  have hC (s v : State D) : C (m s v) = m (C s) v + m (P s) (C v) :=
    LatticeBRSTCohomologyField.charge_mode D H s v n
  have hW (s : State D) : planeT s = C (b s) + b (C s) :=
    LinearMap.congr_fun
      (LatticeBRSTCohomologyField.original_translation_eq_charge_b D H
        plane_inverse plane_inverse) s
  have hb (s : State D) : P (b s) = -b (P s) := b_parity D (-1) s
  have hc (s : State D) : C (P s) = -P (C s) := charge_parity D H s
  have hpp (s : State D) : P (P s) = s := parity_square D s
  have derivation : planeT (m x y) = m (planeT x) y + m x (planeT y) := by
    rw [hW (m x y), hB x y, hC x y, hW x, hW y]
    simp only [map_add, LinearMap.add_apply, hB, hC, hb, hc, hpp, map_neg,
      LinearMap.neg_apply]
    abel
  have cov := LinearMap.congr_fun
    (LatticeMatterGhostStateField.stateField_covariance D x n) y
  change planeT (m x y) - m x (planeT y) =
    -(n : ℂ) • ((planeY x)[[n - 1]]) y at cov
  rw [derivation, add_sub_cancel_right] at cov
  exact cov

private theorem assoc_translation_term (n k : ℤ) (x y : AssocState) :
    term n k (assocT x) y =
      -(k : ℂ) • term (n - 1) (k - 1) x y +
        -((n - 1 - k : ℤ) : ℂ) • term (n - 1) k x y := by
  induction x using TensorProduct.inductionOn with
  | tmul u a =>
    induction y using TensorProduct.inductionOn with
    | tmul v b =>
      simp only [LinearMap.add_apply, LinearMap.rTensor_tmul, rightLift_tmul, map_add,
        term_tmul]
      rw [OriginalOrbifoldTranslation.Y_translation leechData leechUnit leechPosDef leech_spec.1,
        LinearMap.smul_apply, plane_translation_modes,
        show n - 1 - 1 - (k - 1) = n - 1 - k by omega,
        show n - 1 - k - 1 = n - 1 - 1 - k by omega,
        TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    | add y z hy hz =>
      simp only [map_add, hy, hz, smul_add]
      abel
  | add x z hx hz =>
    have hT : assocT (x + z) = assocT x + assocT z := map_add assocT _ _
    rw [hT, (term n k).map_add, LinearMap.add_apply, hx, hz]
    simp only [map_add, LinearMap.add_apply, smul_add]
    abel

private theorem assoc_translation_modes (n : ℤ) (x y : AssocState) :
    ((assocY (assocT x))[[n]]) y = -(n : ℂ) • ((assocY x)[[n - 1]]) y := by
  let f : ℤ → AssocState := fun k => term (n - 1) k x y
  have hf : Function.HasFiniteSupport f := term_finite x y (n - 1)
  let e : ℤ ≃ ℤ := Equiv.subRight 1
  let left : ℤ → AssocState := fun k => -((k + 1 : ℤ) : ℂ) • f k
  let right : ℤ → AssocState := fun k => -((n - 1 - k : ℤ) : ℂ) • f k
  have hl : Function.HasFiniteSupport left := hf.smul_right (fun k : ℤ => -((k + 1 : ℤ) : ℂ))
  have hr : Function.HasFiniteSupport right := hf.smul_right (fun k : ℤ => -((n - 1 - k : ℤ) : ℂ))
  have hshift (k : ℤ) : left (e k) = -(k : ℂ) • f (k - 1) := by
    change -((k - 1 + 1 : ℤ) : ℂ) • f (k - 1) = _
    rw [sub_add_cancel]
  rw [assocY_modes, assocY_modes]
  change (∑ᶠ k : ℤ, term n k (assocT x) y) = -(n : ℂ) • ∑ᶠ k : ℤ, f k
  calc
    _ = ∑ᶠ k : ℤ, (left (e k) + right k) := by
      apply finsum_congr
      intro k
      rw [assoc_translation_term, hshift]
    _ = (∑ᶠ k : ℤ, left k) + ∑ᶠ k : ℤ, right k := by
      change (∑ᶠ k, ((left ∘ e) k + right k)) = _
      rw [finsum_add_distrib (hl.comp_of_injective e.injective) hr]
      exact congrArg (fun z => z + ∑ᶠ k : ℤ, right k) (finsum_comp_equiv e (f := left))
    _ = _ := by
      rw [← finsum_add_distrib hl hr, smul_finsum' _ hf]
      apply finsum_congr
      intro k
      change -((k + 1 : ℤ) : ℂ) • f k + -((n - 1 - k : ℤ) : ℂ) • f k = -(n : ℂ) • f k
      rw [← add_smul]
      congr 1
      push_cast
      ring

/-- The literal total L(-1) gives the actual translated coefficient, including mode zero. -/
theorem translation_mode : TranslationModeLaw := by
  intro n x y
  apply reassoc.injective
  rw [reassoc_originalMode, reassoc_T, map_smul, reassoc_originalMode]
  exact assoc_translation_modes n (reassoc x) (reassoc y)

end Translation

/-- The antighost kills the literal current of any two b0-closed states. -/
theorem current_b0 {x y : ComplexState} (hx : b0 x = 0) (hy : b0 y = 0) :
    b0 (current x y) = 0 := by
  have h : b0 (B x) = 0 := by
    simpa only [hx, map_zero, add_zero] using ghost_car 0 (-1) x
  change b0 (originalMode 0 (B x) y) = 0
  rw [actual_b0_mode, h, ghost_square (-1) x, hy]
  simp only [map_zero, LinearMap.zero_apply, add_zero]

private theorem current_Q (x y : ComplexState) :
    Q (current x y) = -current (Q x) y + originalMode 0 (originalParity (B x)) (Q y) := by
  change Q (originalMode 0 (B x) y) = _
  have h : Q (B x) = T x - B (Q x) := eq_sub_of_add_eq (ward (-1) x)
  rw [actualQ_mode_superderivation, h, map_sub, LinearMap.sub_apply, translation_mode 0]
  simp only [Int.cast_zero, neg_zero, zero_smul, zero_sub, current, LinearMap.comp_apply]

/-- The three constraints are precisely the pinned relative shell. -/
theorem relative_iff (p : Charge hyperbolicPlane) (x : ComplexState) :
    reassoc x ∈ relativeShell p ↔ Momentum p x ∧ b0 x = 0 ∧ E x = 0 := by
  rw [mem_relativeShell_iff]
  have hb : assocB0 (reassoc x) = reassoc (b0 x) := by
    change reassoc (b0 (reassoc.symm (reassoc x))) = _
    rw [reassoc.symm_apply_apply]
  have he : assocE (reassoc x) = reassoc (E x) := by
    change reassoc (E (reassoc.symm (reassoc x))) = _
    rw [reassoc.symm_apply_apply]
  rw [hb, he]
  change (Momentum p x ∧ _ ∧ _) ↔ _
  constructor
  · rintro ⟨hp, hb', he'⟩
    exact ⟨hp, reassoc.injective (hb'.trans reassoc.map_zero.symm),
      reassoc.injective (he'.trans reassoc.map_zero.symm)⟩
  · rintro ⟨hp, hb', he'⟩
    exact ⟨hp, (congrArg reassoc hb').trans reassoc.map_zero,
      (congrArg reassoc he').trans reassoc.map_zero⟩

private theorem b0_Q_of_relative {x : ComplexState} (hb : b0 x = 0) (he : E x = 0) :
    b0 (Q x) = 0 := by
  simpa only [hb, he, map_zero, zero_add] using ward 0 x

private theorem current_degree {g h : ℤ} {x y : ComplexState}
    (hx : Degree g x) (hy : Degree h y) :
    Degree (g - 1 + h) (current x y) :=
  degree_mode 0 (degree_b (-1) hx) hy

private theorem current_momentum
    {p q : Charge hyperbolicPlane} {x y : ComplexState}
    (hx : Momentum p x) (hy : Momentum q y) :
    Momentum (p + q) (current x y) := momentum_mode 0 (momentum_b (-1) hx) hy

/-- Closure on the pinned relative shell, in ghost degree one. -/
theorem current_closed
    {p q : Charge hyperbolicPlane} {u v : ComplexState}
    (hu : reassoc u ∈ relativeShell p) (hv : reassoc v ∈ relativeShell q)
    (du : Degree 1 u) (dv : Degree 1 v) (qu : Q u = 0) (qv : Q v = 0) :
    reassoc (current u v) ∈ relativeShell (p + q) ∧
      Degree 1 (current u v) ∧ Q (current u v) = 0 := by
  obtain ⟨pu, bu, _⟩ := (relative_iff p u).mp hu
  obtain ⟨pv, bv, _⟩ := (relative_iff q v).mp hv
  have hb := current_b0 bu bv
  have hq : Q (current u v) = 0 := by
    rw [current_Q, qu, qv]
    simp only [current, map_zero, LinearMap.zero_apply, neg_zero,
      zero_add]
  have he : E (current u v) = 0 := by
    simpa only [hb, hq, map_zero, add_zero] using (ward 0 (current u v)).symm
  exact ⟨(relative_iff _ _).mpr ⟨current_momentum pu pv, hb, he⟩,
    by simpa only [sub_self, zero_add] using current_degree du dv, hq⟩

/-- The first boundary is witnessed by the negative literal descent of its primitive. -/
theorem left_boundary
    {p q : Charge hyperbolicPlane} {a v : ComplexState}
    (ha : reassoc a ∈ relativeShell p) (hv : reassoc v ∈ relativeShell q)
    (da : Degree 0 a) (dv : Degree 1 v) (qv : Q v = 0) :
    reassoc (-current a v) ∈ relativeShell (p + q) ∧ Degree 0 (-current a v) ∧
      Q (-current a v) = current (Q a) v := by
  obtain ⟨pa, ba, ea⟩ := (relative_iff p a).mp ha
  obtain ⟨pv, bv, _⟩ := (relative_iff q v).mp hv
  have hq : Q (-current a v) = current (Q a) v := by
    rw [map_neg, current_Q, qv, map_zero, add_zero, neg_neg]
  have hb : b0 (-current a v) = 0 := by
    rw [map_neg, current_b0 ba bv, neg_zero]
  have he : E (-current a v) = 0 := by
    rw [← ward 0, hb, hq, current_b0 (b0_Q_of_relative ba ea) bv]
    simp only [map_zero, add_zero]
  refine ⟨(relative_iff _ _).mpr ⟨?_, hb, he⟩, ?_, hq⟩
  · have hp := current_momentum pa pv
    let f := rightLift (chargeProject (p + q))
    let z : ComplexState := current a v
    change f (reassoc (-z)) = reassoc (-z)
    exact (congrArg f (reassoc.map_neg z)).trans
      ((f.map_neg (reassoc z)).trans
        ((congrArg Neg.neg hp).trans (reassoc.map_neg z).symm))
  · have hd := current_degree da dv
    simpa only [Degree, show (0 - 1 + 1 : ℤ) = 0 by omega, map_neg, smul_neg, neg_inj] using hd

/-- For a boundary in the second slot the even extracted current gives the positive sign. -/
theorem right_boundary
    {p q : Charge hyperbolicPlane} {u a : ComplexState}
    (hu : reassoc u ∈ relativeShell p) (ha : reassoc a ∈ relativeShell q)
    (du : Degree 1 u) (da : Degree 0 a) (qu : Q u = 0) :
    reassoc (current u a) ∈ relativeShell (p + q) ∧ Degree 0 (current u a) ∧
      Q (current u a) = current u (Q a) := by
  obtain ⟨pu, bu, _⟩ := (relative_iff p u).mp hu
  obtain ⟨pa, ba, ea⟩ := (relative_iff q a).mp ha
  have hq : Q (current u a) = current u (Q a) := by
    rw [current_Q, qu, even_B_of_degree_one du]
    simp only [current, LinearMap.comp_apply, map_zero, LinearMap.zero_apply, neg_zero,
      zero_add]
  have hb := current_b0 bu ba
  have he : E (current u a) = 0 := by
    rw [← ward 0, hb, hq, current_b0 bu (b0_Q_of_relative ba ea)]
    simp only [map_zero, add_zero]
  exact ⟨(relative_iff _ _).mpr ⟨current_momentum pu pa, hb, he⟩,
    by simpa only [sub_self, zero_add] using current_degree du da, hq⟩

/-- The relative product defect is read directly by b0 at coefficient -1. -/
theorem b0_product {u v : ComplexState} (bu : b0 u = 0) (bv : b0 v = 0) :
    b0 (originalMode (-1) u v) = current u v := by
  rw [actual_b0_mode, bu, bv]
  simp only [map_zero, LinearMap.zero_apply, zero_add, add_zero, current,
    LinearMap.comp_apply, show (-1 + 1 : ℤ) = 0 by norm_num]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
