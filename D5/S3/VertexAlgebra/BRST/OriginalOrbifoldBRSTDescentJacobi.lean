/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTDescentJacobi
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTDescentJacobi
   mirror-E: none(waiver:algebraic-original-brst-descent-jacobi)
   anchors: []
   utility: none
   digest: The native descent Lie identities on the actual odd relative BRST quotient. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTZeroEnergy

/-!
The even zero-mode commutator uses the native super-Borcherds identity,
following the corresponding lattice argument in `LatticeBRSTCurrentIdentities`.
The odd representatives are selected inside the original relative complex.
The symmetric defect is a relative boundary obtained from the vacuum
coefficient of super-Borcherds and the native zero-energy projection.
-/

set_option autoImplicit false

open scoped TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTDescentJacobi

open OriginalOrbifoldCriticalMatter (Matter State Q b vacuum vacuum_closed)
open OriginalOrbifoldBRSTStateField (Y Y_truncation)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTFieldAxioms (homogeneous_mode_product translation
  translation_eq_total_mode translation_vacuum stateField_creation stateField_covariance)
open OriginalOrbifoldBRSTModeDerivation (Q_mode b_zero_mode)
open OriginalOrbifoldBRSTSuperJacobi (homogeneous_borcherds)
open OriginalOrbifoldBRSTDescent
open OriginalOrbifoldBRSTZeroEnergy (totalL0 P0 EInv P0_commutes P0_fixed_iff
  EInv_totalL0 totalL0_EInv totalL0_P0)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open D5.S3.HomologicalAlgebra.FinitePerturbation (boundaryMap)

open private b_parity Q_parity parity_square parity_mem_relativeStates cycle_closed
  b_square ward from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private theorem antighost_even (x : State) (hx : parity x = -x) :
    parity (b (-1) x) = b (-1) x := by
  rw [b_parity, hx, map_neg, neg_neg]

private theorem zero_binomial_sum (f : ℕ → State) :
    (∑ᶠ i : ℕ, integerBinomial 0 i • f i) = f 0 := by
  rw [finsum_eq_single _ 0]
  · simp [integerBinomial]
  · intro i hi
    simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

private theorem zero_signed_binomial_sum (f : ℕ → State) :
    (∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * integerBinomial 0 i) • f i) = f 0 := by
  rw [finsum_eq_single _ 0]
  · simp [integerBinomial]
  · intro i hi
    simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

/-- The native unsigned descent product satisfies left Leibniz for odd first and second inputs. -/
theorem descent_leftLeibniz (x y z : State) (hx : parity x = -x) (hy : parity y = -y) :
    descent x (descent y z) =
      descent (descent x y) z + descent y (descent x z) := by
  have h := (homogeneous_borcherds (b (-1) x) (b (-1) y) z 0 0
    (by simpa only [pow_zero, one_smul] using antighost_even x hx)
    (by simpa only [pow_zero, one_smul] using antighost_even y hy) 0 0 0).2.2.2
  dsimp only at h
  rw [zero_binomial_sum, zero_signed_binomial_sum, zero_signed_binomial_sum] at h
  simp only [Nat.cast_zero, add_zero, sub_zero, epsilon, zpow_zero, Nat.mul_zero,
    pow_zero, mul_one, one_smul] at h
  have hb : b (-1) (descent x y) = descent x (b (-1) y) := by
    rw [descent_b_minus_one, hx, map_neg, LinearMap.neg_apply, neg_neg]
  change (((Y (descent x (b (-1) y)))[[0]]) z) =
    descent x (descent y z) - descent y (descent x z) at h
  rw [← hb] at h
  exact (eq_sub_iff_add_eq.mp h).symm

private theorem descent_odd (x y : State) (hx : parity x = -x) (hy : parity y = -y) :
    parity (descent x y) = -descent x y := by
  change parity (((Y (b (-1) x))[[0]]) y) = -(((Y (b (-1) x))[[0]]) y)
  simpa only [Nat.zero_add, pow_one, neg_one_smul] using
    homogeneous_mode_product (b (-1) x) y 0 1 0
      (by simpa only [pow_zero, one_smul] using antighost_even x hx)
      (by simpa only [pow_one, neg_one_smul] using hy)

private def relativeParity : Module.End ℂ relativeStates :=
  parity.restrict parity_mem_relativeStates

private def cycleParity : Module.End ℂ relativeCycles :=
  relativeParity.restrict (by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change Q (parity (x : State)) = 0
    rw [Q_parity, cycle_closed ⟨x, hx⟩, map_zero, neg_zero])

/-- The native parity involution on the literal relative kernel/image quotient. -/
def cohomologyParity : Module.End ℂ RelativeCohomology :=
  relativeBoundaries.mapQ relativeBoundaries cycleParity (by
    intro x hx
    change ∃ z, boundaryMap relativeDifferential relativeDifferential_square z = x at hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨-relativeParity z, Subtype.ext (Subtype.ext ?_)⟩
    change Q (-parity (z : State)) = parity (Q (z : State))
    rw [Q.map_neg, Q_parity, neg_neg])

private theorem cohomologyParity_mk (x : relativeCycles) :
    cohomologyParity (relativeBoundaries.mkQ x) =
      relativeBoundaries.mkQ (cycleParity x) := rfl

/-- The descended parity squares to the identity on classes. -/
theorem cohomologyParity_involution (x : RelativeCohomology) :
    cohomologyParity (cohomologyParity x) = x := by
  refine Submodule.Quotient.induction_on _ x (fun u => ?_)
  change cohomologyParity (cohomologyParity (relativeBoundaries.mkQ u)) =
    relativeBoundaries.mkQ u
  rw [cohomologyParity_mk, cohomologyParity_mk]
  exact congrArg relativeBoundaries.mkQ (Subtype.ext (Subtype.ext (parity_square _)))

/-- The odd part of the literal native relative quotient. -/
def oddRelativeCohomology : Submodule ℂ RelativeCohomology :=
  LinearMap.ker (cohomologyParity + LinearMap.id)

private theorem oddRepresentative (x : RelativeCohomology) (hx : x ∈ oddRelativeCohomology) :
    ∃ u : relativeCycles, relativeBoundaries.mkQ u = x ∧ parity (u.1 : State) = -(u.1 : State) := by
  have hx' : cohomologyParity x = -x :=
    eq_neg_iff_add_eq_zero.mpr (LinearMap.mem_ker.mp hx)
  let cls : relativeCycles →ₗ[ℂ] RelativeCohomology := relativeBoundaries.mkQ
  obtain ⟨u, hu⟩ : ∃ u : relativeCycles, cls u = x :=
    relativeBoundaries.mkQ_surjective x
  refine ⟨(2 : ℂ)⁻¹ • (u - cycleParity u), ?_, ?_⟩
  · change cls ((2 : ℂ)⁻¹ • (u - cycleParity u)) = x
    have hp : cls (cycleParity u) = -x :=
      (cohomologyParity_mk u).symm.trans ((congrArg cohomologyParity hu).trans hx')
    calc
      _ = (2 : ℂ)⁻¹ • cls (u - cycleParity u) := cls.map_smul _ _
      _ = (2 : ℂ)⁻¹ • (x - (-x)) :=
        congrArg (fun z : RelativeCohomology => (2 : ℂ)⁻¹ • z)
          ((cls.map_sub u (cycleParity u)).trans (congrArg₂ Sub.sub hu hp))
      _ = x := by
        rw [sub_neg_eq_add, ← two_smul ℂ x, smul_smul]
        norm_num
  · change parity ((2 : ℂ)⁻¹ • ((u.1 : State) - parity (u.1 : State))) =
      -((2 : ℂ)⁻¹ • ((u.1 : State) - parity (u.1 : State)))
    rw [map_smul, map_sub, parity_square, ← smul_neg, neg_sub]

/-- Left Leibniz already holds on odd representatives inside the relative cycles. -/
theorem cycleDescent_leftLeibniz (x y z : relativeCycles)
    (hx : parity (x.1 : State) = -(x.1 : State))
    (hy : parity (y.1 : State) = -(y.1 : State)) :
    cycleDescent x (cycleDescent y z) =
      cycleDescent (cycleDescent x y) z + cycleDescent y (cycleDescent x z) :=
  Subtype.ext (Subtype.ext (descent_leftLeibniz _ _ _ hx hy))

/-- Left Leibniz on the original quotient with odd first and second classes. -/
theorem cohomologyDescent_leftLeibniz (x y z : RelativeCohomology)
    (hx : x ∈ oddRelativeCohomology) (hy : y ∈ oddRelativeCohomology) :
    cohomologyDescent x (cohomologyDescent y z) =
      cohomologyDescent (cohomologyDescent x y) z +
        cohomologyDescent y (cohomologyDescent x z) := by
  refine Exists.elim (oddRepresentative x hx) fun u hu => ?_
  refine Exists.elim (oddRepresentative y hy) fun v hv => ?_
  refine Exists.elim (relativeBoundaries.mkQ_surjective z) fun w hw => ?_
  have h := congrArg relativeBoundaries.mkQ (cycleDescent_leftLeibniz u v w hu.2 hv.2)
  rw [map_add] at h
  simpa only [← cohomologyDescent_mk, hu.1, hv.1, hw] using h

/-- The induced native bracket of two odd classes is odd. -/
theorem cohomologyDescent_mem_odd (x y : RelativeCohomology)
    (hx : x ∈ oddRelativeCohomology) (hy : y ∈ oddRelativeCohomology) :
    cohomologyDescent x y ∈ oddRelativeCohomology := by
  refine Exists.elim (oddRepresentative x hx) fun u hu => ?_
  refine Exists.elim (oddRepresentative y hy) fun v hv => ?_
  have hp : cycleParity (cycleDescent u v) = -cycleDescent u v :=
    Subtype.ext (Subtype.ext (descent_odd _ _ hu.2 hv.2))
  apply LinearMap.mem_ker.mpr
  change cohomologyParity (cohomologyDescent _ _) + cohomologyDescent _ _ = 0
  let cls : relativeCycles →ₗ[ℂ] RelativeCohomology := relativeBoundaries.mkQ
  have h : cohomologyParity (cls (cycleDescent u v)) = -cls (cycleDescent u v) :=
    (cohomologyParity_mk _).trans
      ((congrArg cls hp).trans (cls.map_neg (cycleDescent u v)))
  change cohomologyParity (relativeBoundaries.mkQ (cycleDescent u v)) =
    -relativeBoundaries.mkQ (cycleDescent u v) at h
  simp only [← cohomologyDescent_mk, hu.1, hv.1] at h
  exact eq_neg_iff_add_eq_zero.mp h

private abbrev mode (x : State) (n : ℤ) (y : State) : State := ((Y x)[[n]]) y

private theorem negOneMode_symm_translation (x y : State)
    (hx : parity x = -x) (hy : parity y = -y) (hQx : Q x = 0) (hQy : Q y = 0) :
    ∃ w : State, Q w = 0 ∧ mode x (-1) y + mode y (-1) x = translation w := by
  have h := (homogeneous_borcherds x y vacuum 1 1
    (by simpa only [pow_one, neg_one_smul] using hx)
    (by simpa only [pow_one, neg_one_smul] using hy) (-1) (-1) 0).2.2.2
  dsimp only at h
  rw [zero_signed_binomial_sum, zero_signed_binomial_sum] at h
  simp only [Nat.cast_zero, zero_add, add_zero, sub_zero, epsilon, zpow_zero,
    pow_one, one_mul, stateField_creation, neg_one_smul, sub_neg_eq_add] at h
  let f : ℕ → State := fun i =>
    (integerBinomial (-1) i / ((i : ℂ) + 1)) • mode (mode x i y) (-(i : ℤ) - 1) vacuum
  have hf : Function.HasFiniteSupport f := by
    obtain ⟨cutoff, vanish⟩ := Y_truncation x y
    refine (Finset.range cutoff.toNat).finite_toSet.subset ?_
    intro i hi
    apply Finset.mem_range.mpr
    by_contra! hlarge
    apply hi
    have hz : mode x i y = 0 := vanish _ (by omega)
    simp only [f, hz]
    change (integerBinomial (-1) i / ((i : ℂ) + 1)) •
      (((Y 0)[[-(i : ℤ) - 1]]) vacuum) = 0
    simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero]
  refine ⟨∑ᶠ i : ℕ, f i, ?_, ?_⟩
  · rw [map_finsum Q hf]
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    have hclosed : Q (mode x i y) = 0 := by
      unfold mode
      simp only [Q_mode, hQx, hQy, map_zero, Pi.zero_apply, LinearMap.zero_apply, add_zero]
    change Q ((integerBinomial (-1) i / ((i : ℂ) + 1)) •
      mode (mode x i y) (-(i : ℤ) - 1) vacuum) = 0
    simp only [mode, map_smul, Q_mode, hclosed, vacuum_closed, map_zero, Pi.zero_apply,
      LinearMap.zero_apply, add_zero, smul_zero]
  · rw [map_finsum translation hf, ← h]
    apply finsum_congr
    intro i
    have cov := LinearMap.congr_fun
      (stateField_covariance (mode x i y) (-(i : ℤ) - 1)) vacuum
    simp only [LinearMap.sub_apply, Module.End.mul_apply, translation_vacuum, map_zero,
      sub_zero, LinearMap.smul_apply] at cov
    have index : -(i : ℤ) - 1 - 1 = -1 + -1 - (i : ℤ) := by omega
    have scalar : -((-(i : ℤ) - 1 : ℤ) : ℂ) = (i : ℂ) + 1 := by push_cast; ring
    have hn : (i : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
    change _ = translation ((integerBinomial (-1) i / ((i : ℂ) + 1)) •
      mode (mode x i y) (-(i : ℤ) - 1) vacuum)
    rw [map_smul, cov, index, scalar, smul_smul, div_mul_cancel₀ _ hn]

private theorem b_zero_negOne_mode (x y : State) (hx : b 0 x = 0) (hy : b 0 y = 0) :
    b 0 (mode x (-1) y) = descent x y := by
  change b 0 (((Y x)[[-1]]) y) = (((Y (b (-1) x))[[0]]) y)
  simp only [b_zero_mode, hx, hy, neg_add_cancel, map_zero, Pi.zero_apply,
    LinearMap.zero_apply, zero_add, add_zero]

private theorem L0_b_zero (x : State) : totalL0 (b 0 x) = b 0 (totalL0 x) := by
  calc
    totalL0 (b 0 x) = Q (b 0 (b 0 x)) + b 0 (Q (b 0 x)) := (ward 0 _).symm
    _ = b 0 (Q (b 0 x) + b 0 (Q x)) := by
      rw [map_add, b_square, b_square, map_zero, zero_add, add_zero]
    _ = b 0 (totalL0 x) := congrArg (b 0) (ward 0 x)

private theorem P0_L0 (x : State) : P0 (totalL0 x) = 0 := by
  have h₁ : EInv (totalL0 x) = x - P0 x := LinearMap.congr_fun EInv_totalL0 x
  have h₂ : totalL0 (EInv (totalL0 x)) = totalL0 x - P0 (totalL0 x) :=
    LinearMap.congr_fun totalL0_EInv (totalL0 x)
  rw [h₁, map_sub, totalL0_P0, sub_zero] at h₂
  exact sub_eq_self.mp h₂.symm

private theorem P0_b_zero (x : State) : P0 (b 0 x) = b 0 (P0 x) := by
  have hsplit : totalL0 (EInv x) = x - P0 x := LinearMap.congr_fun totalL0_EInv x
  have hsplit' : b 0 x = b 0 (P0 x) + totalL0 (b 0 (EInv x)) := by
    rw [L0_b_zero, hsplit, map_sub]
    abel
  have hfix : P0 (b 0 (P0 x)) = b 0 (P0 x) :=
    (P0_fixed_iff _).mpr (by rw [L0_b_zero, totalL0_P0, map_zero])
  calc
    P0 (b 0 x) = P0 (b 0 (P0 x) + totalL0 (b 0 (EInv x))) := congrArg P0 hsplit'
    _ = b 0 (P0 x) := by rw [map_add, hfix, P0_L0, add_zero]

/-- The symmetric descent defect of two odd relative cycles has a relative primitive. -/
theorem descent_symm_boundary (x y : State) (hx : x ∈ relativeStates)
    (hy : y ∈ relativeStates) (hQx : Q x = 0) (hQy : Q y = 0)
    (hpx : parity x = -x) (hpy : parity y = -y) :
    ∃ u : relativeStates, Q (u : State) = descent x y + descent y x := by
  obtain ⟨w, hw, hT⟩ := negOneMode_symm_translation x y hpx hpy hQx hQy
  have hD : b 0 (translation w) = descent x y + descent y x := by
    rw [← hT, map_add, b_zero_negOne_mode x y hx.1 hy.1, b_zero_negOne_mode y x hy.1 hx.1]
  have hL : totalL0 (descent x y + descent y x) = 0 :=
    (relativeStates.add_mem (descent_mem_relativeStates x y hx hy)
      (descent_mem_relativeStates y x hy hx)).2
  have hQ : Q (b (-1) w) = translation w := by
    simpa only [hw, map_zero, add_zero, translation_eq_total_mode] using ward (-1) w
  let v := P0 (b (-1) w)
  have hv : totalL0 v = 0 := totalL0_P0 _
  refine ⟨⟨-b 0 v, ?_⟩, ?_⟩
  · change b 0 (-b 0 v) = 0 ∧ totalL0 (-b 0 v) = 0
    simp only [map_neg, b_square, L0_b_zero, hv, map_zero, neg_zero, and_self]
  · change Q (-b 0 v) = _
    have hvQ : Q (b 0 v) + b 0 (Q v) = 0 := (ward 0 v).trans hv
    have hc : Q v = P0 (Q (b (-1) w)) := (LinearMap.congr_fun P0_commutes _).symm
    rw [Q.map_neg, (eq_neg_iff_add_eq_zero.mpr hvQ), hc, hQ, ← P0_b_zero, hD,
      (P0_fixed_iff _).mpr hL, neg_neg]

/-- The native descent operation is skew on odd relative classes. -/
theorem cohomologyDescent_skew (x y : RelativeCohomology)
    (hx : x ∈ oddRelativeCohomology) (hy : y ∈ oddRelativeCohomology) :
    cohomologyDescent x y = -cohomologyDescent y x := by
  refine Exists.elim (oddRepresentative x hx) fun u hu => ?_
  refine Exists.elim (oddRepresentative y hy) fun v hv => ?_
  have h : relativeBoundaries.mkQ (cycleDescent u v + cycleDescent v u) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    obtain ⟨p, hp⟩ := descent_symm_boundary (u.1 : State) (v.1 : State)
      u.1.property v.1.property (cycle_closed u) (cycle_closed v) hu.2 hv.2
    exact ⟨p, Subtype.ext (Subtype.ext hp)⟩
  apply eq_neg_iff_add_eq_zero.mpr
  rw [map_add] at h
  simpa only [← cohomologyDescent_mk, hu.1, hv.1] using h

#print axioms descent_leftLeibniz
#print axioms cycleDescent_leftLeibniz
#print axioms cohomologyParity
#print axioms cohomologyParity_involution
#print axioms cohomologyDescent_leftLeibniz
#print axioms cohomologyDescent_mem_odd
#print axioms descent_symm_boundary
#print axioms cohomologyDescent_skew

end
end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTDescentJacobi
