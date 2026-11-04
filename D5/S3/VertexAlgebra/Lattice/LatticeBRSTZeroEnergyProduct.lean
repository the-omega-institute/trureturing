/-
SOURCE-ONLY / UNCOMPILED implementation. No native or kernel acceptance.

This consumes, sequentially, the fixed completed P0/B0 source and raw antighost
source, the completed tensor Borcherds source, and the EXISTING full current
Cohomology/product source drafts. Their exact hashes are in hash-evidence.json.
They are implementation inputs, not independent votes. No active native writer
or canonical signed writer is an input to this file.

Attribution is retained: Bakalov--Kac for the lattice construction;
Scott Carnahan / vertexAlg (4453e34ec390e82a0c789c731ada8f9a6e86bdea) for
field/residue calculus; Kalle Kytölä for the Sugawara architecture; and the
original ghost and Mathlib authors under their suppliers' Apache-2.0 notices.
The mode-one finite-support reduction adapts OriginalTopologicalApplications
(SHA256 85302c4b23c6e4e0f271ca7aa794ba69c65fbef4af813ca5e0204940696d95ad,
lines 272--317), as ported by LatticeMatterGhostAntighostSecondOrder.
Here the public nonhomogeneous Borcherds theorem removes the second-state
homogeneity premise by using the actual even-first projections a0=a, a1=0.
Its four finite-support certificates are retained on specialization. All new
sum reductions below are pointwise support reductions; no unrestricted
map_finsum or exchange of infinite sums is used.

The endpoint uses the supplied full quotient, not a new quotient or BV record.
P0 need not be multiplicative on raw states. Delta remains the supplied
P0-reduced b0 operator, never raw b0 on arbitrary cycles. There is no new
second-order, bracket Jacobi/Leibniz, associativity or commutativity claim.
The parent scientific goal remains incomplete. Native API reconciliation and
elaboration of this exact source and its source-draft dependency closure remain
required; source inspection does not establish either.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTZeroEnergyReduction
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyProduct
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostAntighostSecondOrder
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.LatticeBRSTZeroEnergyProduct

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeSugawaraCurrents (gramComplex)
open LatticeMatterGhostCoupling (State matterMode ghostVirasoro ghostB)
open LatticeMatterGhostStateField
  (Y parity vacuum translation omega stateField_vacuum_creation
   stateField_covariance conformal_modes)
open LatticeMatterGhostSignedBorcherds (mu_D jacobiLeftTerm)
open LatticeMatterGhostAntighostSecondOrder (mu)
open LatticeBRST (totalCharge)
open LatticeBRSTCohomologyField (cycles Cohomology classOf cycleMode product product_classOf)
open LatticeBRSTZeroEnergyReduction
  (totalL0 P0 totalL0_P0 P0_fixed_iff cycleP0 classOf_P0
   B0_P0_cycle Delta Delta_classOf)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open D5.S3.Quantum.Fermionic
open private identity_modes from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open private p_zero_left from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostSignedBorcherds

noncomputable section

-- Every declaration has its complete parameter list; there are no hidden
-- section hypotheses. In particular the raw closure section has no h26.

private theorem translation_as_minus_two (D : LatticeData) (a : State D) :
    translation D a = ((Y D a)[[-2]]) (vacuum D) := by
  have law := LinearMap.congr_fun (stateField_covariance D a (-1)) (vacuum D)
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    (stateField_vacuum_creation D).2.1 a,
    (stateField_vacuum_creation D).2.2.2, map_zero, sub_zero,
    Int.cast_neg, Int.cast_one, neg_neg, one_smul,
    show (-1 : ℤ) - 1 = -2 by norm_num] using law

private theorem translation_zero_mode (D : LatticeData) (a c : State D) :
    ((Y D (translation D a))[[0]]) c = 0 := by
  have vacuumEven : parity D (vacuum D) = vacuum D := by
    simp [parity, vacuum, TensorProduct.map_tmul,
      CountableOccupationFock.vacuum, parity_ket]
  have vacuumMode (n : ℤ) (hn : n ≠ -1) : ((Y D (vacuum D))[[n]]) = 0 := by
    rw [(stateField_vacuum_creation D).1, identity_modes, if_neg hn]
  have raw := LatticeMatterGhostBorcherds.borcherds D a (vacuum D) c 0 0 (-2)
  dsimp only at raw
  obtain ⟨_finiteLeft, _finiteForward, _finiteReverse0, _finiteReverse1, law⟩ := raw
  change mu_D D (translation D a) 0 c = 0
  rw [translation_as_minus_two D a]
  change mu_D D (mu_D D a (-2) (vacuum D)) 0 c = 0
  rw [← p_zero_left D a (vacuum D) c 0 (-2), law]
  -- Both reverse families vanish, including the actual parity-vacuum family.
  -- Forward inner vacuum indices are i>=0; reverse outer indices are -2-i.
  apply finsum_eq_zero_of_forall_eq_zero
  intro i
  have positive := vacuumMode (i : ℤ) (by omega)
  have negative := vacuumMode (-2 - (i : ℤ)) (by omega)
  simp only [zero_add, vacuumEven, mu_D, positive, negative,
    LinearMap.zero_apply, map_zero, add_zero, sub_zero, smul_zero]

private theorem omega_even (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    parity D (omega D H) = omega D H := by
  have ghostVacuum : CountableOccupationFock.parity CountableOccupationFock.vacuum =
      CountableOccupationFock.vacuum := by
    simp [CountableOccupationFock.vacuum, parity_ket]
  have ghostOmega : CountableOccupationFock.parity BcGhostConformalBRSTState.Omega =
      BcGhostConformalBRSTState.Omega := by
    norm_num [BcGhostConformalBRSTState.Omega, parity_ket, map_add, map_smul]
  simp only [omega, map_add, parity, TensorProduct.map_tmul,
    LinearMap.id_apply, ghostVacuum, ghostOmega]

/-- The historical mode-one mechanism on an even first state and EVERY second
state. Its hypotheses do not impose parity on a or c. -/
private theorem even_first_one_mode (D : LatticeData) (u a c : State D)
    (hu : parity D u = u) :
    ((Y D u)[[1]]) (mu D a c) =
      mu D (((Y D u)[[1]]) a) c + mu D a (((Y D u)[[1]]) c) +
        ((Y D (((Y D u)[[0]]) a))[[0]]) c := by
  classical
  have evenProjection : (2 : ℂ)⁻¹ • (u + parity D u) = u := by
    rw [hu]
    module
  have oddProjection : (2 : ℂ)⁻¹ • (u - parity D u) = 0 := by
    rw [hu, sub_self, smul_zero]
  have raw := LatticeMatterGhostBorcherds.borcherds D u a c 1 (-1) 0
  dsimp only at raw
  obtain ⟨_finiteLeft, _finiteForward, _finiteReverse0, _finiteReverse1, law⟩ := raw
  rw [evenProjection, oddProjection] at law
  have leftValue : (∑ᶠ i : ℕ, jacobiLeftTerm D 1 (-1) 0 u a c i) =
      mu_D D (mu_D D u 0 a) 0 c + mu_D D (mu_D D u 1 a) (-1) c := by
    rw [finsum_eq_sum_of_support_subset (s := {0, 1})]
    · simp [jacobiLeftTerm, integerBinomial, Ring.choose_natCast]
    · intro i member
      by_contra outside
      have large : 1 < i := by
        change i ∉ ({0, 1} : Finset ℕ) at outside
        simp only [Finset.mem_insert, Finset.mem_singleton] at outside
        omega
      apply member
      have chooseZero : Ring.choose (1 : ℤ) i = 0 := by
        simpa only [Nat.cast_one, Nat.choose_eq_zero_of_lt large, Nat.cast_zero]
          using (Ring.choose_natCast (R := ℤ) 1 i)
      simp [jacobiLeftTerm, integerBinomial, chooseZero]
  let right (i : ℕ) : State D :=
    (((-1 : ℂ)^i) * integerBinomial 0 i) •
      (mu_D D u (1 + 0 - i) (mu_D D a (-1 + i) c) - epsilon 0 •
        (mu_D D a (-1 + 0 - i) (mu_D D u (1 + i) c) +
          mu_D D (parity D a) (-1 + 0 - i) (mu_D D 0 (1 + i) c)))
  have rightValue : (∑ᶠ i : ℕ, right i) = right 0 := by
    rw [finsum_eq_single _ 0]
    intro i different
    simp [right, integerBinomial,
      Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero different)]
  rw [leftValue] at law
  change mu_D D (mu_D D u 0 a) 0 c + mu_D D (mu_D D u 1 a) (-1) c =
    ∑ᶠ i : ℕ, right i at law
  rw [rightValue] at law
  have reduced : mu_D D (mu_D D u 0 a) 0 c +
      mu_D D (mu_D D u 1 a) (-1) c =
      mu_D D u 1 (mu_D D a (-1) c) - mu_D D a (-1) (mu_D D u 1 c) := by
    simpa [right, integerBinomial, epsilon, mu_D] using law
  exact (eq_sub_iff_add_eq.mp reduced).symm.trans (by
    dsimp only [mu_D, mu]
    abel)

private theorem omega_zero_mode (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    ((Y D (omega D H))[[0]]) = translation D := by
  have modes := conformal_modes D H (-1)
  change ((Y D (omega D H))[[0]]) =
    TensorProduct.map (LatticeSugawaraCurrents.sugawaraMode D H (-1)) LinearMap.id +
      TensorProduct.map LinearMap.id (BcGhostVirasoro.L (-1)) at modes
  rw [LatticeSugawaraConformal.sugawaraMode_minus_one_eq_translation D H hHG hGH]
    at modes
  exact modes

/-- Actual total L0 derives actual mode -1 on ALL original tensor states.
Only the two stated inverse-Gram equations are required. -/
theorem totalL0_mu (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a b : State D) :
    totalL0 D H (mu D a b) = mu D (totalL0 D H a) b + mu D a (totalL0 D H b) := by
  have law := even_first_one_mode D (omega D H) a b (omega_even D H)
  have modeOne : ((Y D (omega D H))[[1]]) = totalL0 D H := by
    simpa only [zero_add, totalL0] using conformal_modes D H 0
  rw [modeOne, omega_zero_mode D H hHG hGH, translation_zero_mode D a b,
    add_zero] at law
  exact law

/-- Closure of the actual zero-energy kernel, with no rank or sector restriction. -/
theorem zero_energy_mu (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a b : State D) (ha : totalL0 D H a = 0) (hb : totalL0 D H b = 0) :
    totalL0 D H (mu D a b) = 0 := by
  rw [totalL0_mu D H hHG hGH, ha, hb]
  simp [mu]

/-- P0 fixes the product of two already reduced states. This does NOT assert
P0(mu(a,b))=mu(P0(a),P0(b)) for arbitrary states. -/
theorem P0_mu_P0 (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a b : State D) :
    P0 D (mu D (P0 D a) (P0 D b)) = mu D (P0 D a) (P0 D b) :=
  (P0_fixed_iff D H hHG hGH _).mpr
    (zero_energy_mu D H hHG hGH _ _
      (totalL0_P0 D H hHG hGH a) (totalL0_P0 D H hHG hGH b))

/-- Existing cycle mode closure applied to existing P0-preserved cycles. -/
theorem reduced_mu_cycle (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x y : cycles D H) :
    totalCharge D H (mu D (P0 D (x : State D)) (P0 D (y : State D))) = 0 :=
  (cycleMode D H (-1) (cycleP0 D H h26 hHG hGH x)
    (cycleP0 D H h26 hHG hGH y)).property

/-- Congruence through the supplied classOf_P0 suffices on the full quotient. -/
theorem product_classOf_P0 (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x y : cycles D H) :
    product D H h26 hHG hGH (classOf D H h26 hHG hGH x) (classOf D H h26 hHG hGH y) =
      classOf D H h26 hHG hGH
        ⟨mu D (P0 D (x : State D)) (P0 D (y : State D)),
          reduced_mu_cycle D H h26 hHG hGH x y⟩ := by
  calc
    _ = product D H h26 hHG hGH
        (classOf D H h26 hHG hGH (cycleP0 D H h26 hHG hGH x))
        (classOf D H h26 hHG hGH (cycleP0 D H h26 hHG hGH y)) := by
      rw [classOf_P0 D H h26 hHG hGH x, classOf_P0 D H h26 hHG hGH y]
    _ = classOf D H h26 hHG hGH
        (cycleMode D H (-1) (cycleP0 D H h26 hHG hGH x)
          (cycleP0 D H h26 hHG hGH y)) :=
      product_classOf D H h26 hHG hGH _ _
    _ = _ := rfl

/-- The endpoint representative is an actual Q-cycle: apply supplied B0/P0
cycle preservation to the closed product, then use its proved P0 fixity. -/
theorem reduced_b0_mu_cycle (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x y : cycles D H) :
    totalCharge D H (ghostB D 0
      (mu D (P0 D (x : State D)) (P0 D (y : State D)))) = 0 := by
  have closed := B0_P0_cycle D H h26 hHG hGH
    (mu D (P0 D (x : State D)) (P0 D (y : State D)))
    (reduced_mu_cycle D H h26 hHG hGH x y)
  rw [P0_mu_P0 D H hHG hGH] at closed
  exact closed

/-- Delta of the existing product on the existing FULL current cohomology,
for every pair of actual cycles, with the literal physical b(0) representative. -/
theorem Delta_product_classOf (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x y : cycles D H) :
    Delta D H h26 hHG hGH
      (product D H h26 hHG hGH (classOf D H h26 hHG hGH x)
        (classOf D H h26 hHG hGH y)) =
      classOf D H h26 hHG hGH
        ⟨ghostB D 0 (mu D (P0 D (x : State D)) (P0 D (y : State D))),
          reduced_b0_mu_cycle D H h26 hHG hGH x y⟩ := by
  rw [product_classOf_P0 D H h26 hHG hGH x y, Delta_classOf]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  change ghostB D 0 (P0 D (mu D (P0 D (x : State D)) (P0 D (y : State D)))) =
    ghostB D 0 (mu D (P0 D (x : State D)) (P0 D (y : State D)))
  rw [P0_mu_P0 D H hHG hGH]

end
end D5.S3.VertexAlgebra.LatticeBRSTZeroEnergyProduct
