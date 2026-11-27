/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qChargedResidueProduct
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Adjusted charged residues and their agreement with native ground-state products. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedResidueProduct.FiniteGroundSums

/-! Residue extraction from finite homogeneous slices of the charged radial products. -/

set_option autoImplicit false

open scoped BigOperators VertexOperator

noncomputable section
namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedResidueProduct

section Product

open P48qThirdTwistedField
open P48qTwistedChargeAction (lattice g g_cube g_isometry Momentum)
open NativeStandardThirdLift (standardLift standardLift_ground_single)
open LatticeGeneratingFieldLocality (Charge)
open P48qCurrentChargedIterate (chargedGround)
open P48qAllJetWickField (NativeStates nativeField)
open LatticeAllStateReconstruction (mu)
open P48qNativeCurrentLocality (InResidue nativeField_inResidue restoreResidue_coeff)
open P48qNativeResidueProduct (adjustedResidue clearedResidue binomialTail adjustedResidue_eq_iff
  clearedResidue_zero_of_locality)
open PowerSeries (binomialSeries)
open private liftProject liftProject_eigen from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality

open private strippedResidue_coverSlice coeff_diagonal_strip cleared_off_residue clear_radial_locality
  groundSum radialGroundSum radialGroundSum_coeff radialGroundSum_cleared_finite
  radialGroundSum_cleared_swap mu_groundSum groundMode_zero radialGroundSum_weakAssociativity from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedResidueProduct.FiniteGroundSums
local notation "Xc" => (coverMonomial 1 0 (1 : Fock))
local notation "Yc" => (coverMonomial 0 1 (1 : Fock))
local notation "ιF" => HahnSeries.ofPowerSeries ℤ Fock
local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

private theorem groundSums_adjustedResidue {I J : Type*} [Fintype I] [Fintype J]
    (a : I → Charge lattice) (b : J → Charge lattice) (u : I → ℂ) (w : J → ℂ)
    (s t : ℤ) (hs : InResidue s (nativeField (groundSum a u)))
    (ht : InResidue t (nativeField (groundSum b w)))
    (N : ℕ) (hN : ∀ i j, chargedLocalityOrder (a i) (b j) ≤ N) :
    ∀ n, adjustedResidue s t (nativeField (groundSum a u)) (nativeField (groundSum b w)) N n =
      nativeField (mu lattice (groundSum a u) n (groundSum b w)) := by
  let A := nativeField (groundSum a u)
  let B := nativeField (groundSum b w)
  let F (n : ℤ) := nativeField (mu lattice (groundSum a u) n (groundSum b w))
  let L := radialGroundSum a b u w
  let R := radialGroundSum b a w u
  let C (v : State) (q : Momentum) := (Xc ^ 3 - Yc ^ 3) ^ N * L v q
  have hL v q k l := radialGroundSum_coeff a b u w v q k l
  have hR v q (k l : ℤ) := radialGroundSum_coeff b a w u v q l k
  have hswap v q := radialGroundSum_cleared_swap a b u w v q N hN
  have hlocal := clear_radial_locality A B N L R hL hR hswap
  have hf n (hn : (N : ℤ) ≤ n) : F n = 0 := by
    dsimp only [F]
    rw [mu_groundSum]
    simp only [groundMode_zero _ _ _ (hN _ _) _ hn, smul_zero, Finset.sum_const_zero, map_zero]
  have hr n (hn : (N : ℤ) ≤ n) : clearedResidue s t A B n = 0 :=
    clearedResidue_zero_of_locality s t A B hs ht N hlocal n hn
  refine (adjustedResidue_eq_iff s t A B N F hf hr).2 ?_
  intro n h
  by_cases hn : (N : ℤ) ≤ n
  · simp [hr n hn, binomialTail, show ((N : ℤ) - n).toNat = 0 by omega]
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  let m := ((N : ℤ) - n - 1).toNat
  let h' := h + 3 * (N : ℤ) - 3
  have hm : (m : ℤ) = (N : ℤ) - n - 1 := Int.toNat_of_nonneg (by omega)
  have hoff (k l : ℤ) (hk : k % 3 ≠ s % 3 ∨ l % 3 ≠ t % 3) :
      ((C v q).coeff l).coeff k = 0 := by
    apply cleared_off_residue (L v q) s t _ N k l hk
    intro k l hkl
    rw [hL]
    rcases hkl with hkl | hkl
    · rw [hs k hkl]
      rfl
    · rw [ht l hkl, LinearMap.zero_apply, map_zero, Finsupp.zero_apply]
  have hc (j : ℕ) (hj : j ≤ m) :
      PowerSeries.coeff (m - j) (diagonalCoverReadout (C v q) h') =
        HVertexOperator.coeff (F (n + j)) (h + 3 * (n + j)) v q := by
    have hd : ((m - j : ℕ) : ℤ) = (N : ℤ) - (n + (j : ℤ)) - 1 := by omega
    rw [← HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ), hd]
    have he := radialGroundSum_weakAssociativity a b u w v q N hN h' (n + j)
    change (ιF (diagonalCoverReadout (C v q) h')).coeff _ = _ at he
    rw [he, show h' - 3 * ((N : ℤ) - (n + (j : ℤ)) - 1) = h + 3 * (n + (j : ℤ)) by
      dsimp [h']; ring]
  have hbin :
      PowerSeries.coeff m (binomialSeries Fock (-(s : ℂ) / 3) *
        diagonalCoverReadout (C v q) h') =
      (binomialTail (-(s : ℂ) / 3) N
        (fun p => HVertexOperator.coeff (F p) (h + 3 * p)) n) v q := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      binomialTail, show ((N : ℤ) - n).toNat = m + 1 by omega]
    simp only [LinearMap.sum_apply, Finset.sum_apply', LinearMap.smul_apply, Finsupp.smul_apply,
      PowerSeries.binomialSeries_coeff, Algebra.smul_mul_assoc, one_mul]
    exact Finset.sum_congr rfl fun j hj => by
      rw [hc j (by simpa using Finset.mem_range.mp hj)]
  rw [← hbin, clearedResidue, restoreResidue_coeff]
  split
  · rename_i hk
    let H := (h - (s + t)) / 3 - 1
    have hH : h' = 3 * (H + N) + s + t := by dsimp [h', H]; omega
    rw [hH, coeff_diagonal_strip (radialGroundSum_cleared_finite a b u w v q N hN)
      s t (H + N) m hoff]
    have hh := strippedResidue_coverSlice A B v q s t H N m (L v q) (R v q)
      (hL v q) (hR v q) (radialGroundSum_cleared_finite a b u w v q N hN) (hswap v q)
    rw [show (N : ℤ) - (m : ℤ) - 1 = n by omega,
      show H + (N : ℤ) - m = (h + 3 * n - (s + t)) / 3 by dsimp only [H]; omega] at hh
    exact hh
  · rename_i hk
    have hz : diagonalCoverReadout (C v q) h' = 0 := by
      unfold diagonalCoverReadout
      apply finsum_eq_zero_of_forall_eq_zero
      intro k
      have hne : k % 3 ≠ s % 3 ∨ (h' - k) % 3 ≠ t % 3 := by
        by_contra! hp
        dsimp [h'] at hp
        omega
      rw [hoff k _ hne, map_zero, zero_mul]
    rw [hz, mul_zero, map_zero]
    rfl

private def chargeOrbit (a : Charge lattice) : Fin 3 → Charge lattice :=
  ![a, g a, g (g a)]

private def projectedOrbitWeight (r : Fin 3) (a : Charge lattice) : Fin 3 → ℂ :=
  fun i => (3 : ℂ)⁻¹ * ![1, ζ ^ r.val * eta a, (ζ ^ r.val) ^ 2 * (eta a * eta (g a))] i
where
  eta (a : Charge lattice) := (ThirdTwistedChargeAction.nativeStandardEta lattice g a : ℂ)

private theorem liftProject_groundSum (r : Fin 3) (a : Charge lattice) :
    liftProject r (chargedGround a) = groundSum (chargeOrbit a) (projectedOrbitWeight r a) := by
  have hl (b : Charge lattice) :
      σ (chargedGround b) =
        (ThirdTwistedChargeAction.nativeStandardEta lattice g b : ℂ) • chargedGround (g b) :=
    standardLift_ground_single lattice g g_cube g_isometry b
  simp only [liftProject, hl, map_smul, groundSum, chargeOrbit, projectedOrbitWeight,
    projectedOrbitWeight.eta, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, smul_add, smul_smul, mul_one]
  rfl

set_option maxHeartbeats 1000000 in
-- Elaboration unfolds the native field types while aligning the two projections.
/-- Every integer product label for two lift-eigenprojected charged ground
states. The same clearing order works on all nine ordered orbit pairs. -/
theorem adjustedResidue_native_projected_chargedGround
    (a b : Charge lattice) (r p : Fin 3) (N : ℕ)
    (hN : ∀ i j, chargedLocalityOrder (chargeOrbit a i) (chargeOrbit b j) ≤ N) (n : ℤ) :
    adjustedResidue (2 * (r.val : ℤ)) (2 * (p.val : ℤ))
      (nativeField (liftProject r (chargedGround a)))
      (nativeField (liftProject p (chargedGround b)))
      N n = nativeField (mu lattice (liftProject r (chargedGround a)) n
        (liftProject p (chargedGround b))) := by
  have he (i : Fin 3) (x : Charge lattice) :
      σ (liftProject i (chargedGround x)) = ζ ^ (2 * (i.val : ℤ)) •
        liftProject i (chargedGround x) := by
    simpa only [show 2 * (i.val : ℤ) = ((i.val * 2 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, pow_mul] using liftProject_eigen i (chargedGround x)
  have ha := nativeField_inResidue _ _ (he r a)
  have hb := nativeField_inResidue _ _ (he p b)
  simp only [liftProject_groundSum] at ha hb ⊢
  exact groundSums_adjustedResidue (chargeOrbit a) (chargeOrbit b)
    (projectedOrbitWeight r a) (projectedOrbitWeight p b) _ _ ha hb N hN n

-- A common finite clearing order exists for every pair of projected grounds.
set_option maxHeartbeats 1000000 in
-- The conclusion specializes the projected ground theorem to a finite supremum.
theorem exists_adjustedResidue_native_projected_chargedGround
    (a b : Charge lattice) (r p : Fin 3) :
    ∃ N : ℕ, ∀ n : ℤ,
      adjustedResidue (2 * (r.val : ℤ)) (2 * (p.val : ℤ))
        (nativeField (liftProject r (chargedGround a)))
        (nativeField (liftProject p (chargedGround b))) N n =
      nativeField (mu lattice (liftProject r (chargedGround a)) n
        (liftProject p (chargedGround b))) := by
  let order (ij : Fin 3 × Fin 3) :=
    chargedLocalityOrder (chargeOrbit a ij.1) (chargeOrbit b ij.2)
  refine ⟨Finset.univ.sup order, fun n =>
    adjustedResidue_native_projected_chargedGround a b r p _ (fun i j => ?_) n⟩
  change order (i, j) ≤ Finset.univ.sup order
  exact Finset.le_sup (f := order) (Finset.mem_univ (i, j))

open P48qNativeCurrentLocality (Field stripResidue stripResidue_coeff)
open P48qTwistedHeisenberg (currentField)
open P48qNativeCurrentCommutator (nativeField_current_commutator)
open P48qCurrentChargedIterate (source_product_positive)
open ThirdTwistedIterate (currentAlong)
open ThirdEigenspacePairing (p48qAction)
open private strip_current_ncoeff from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentLocality
open private projectAt_on_residue from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCurrentChargedIterate

open private groundSpan chargeGround from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality

private theorem ground_current_positive (a : NativeStates) (ha : a ∈ groundSpan)
    (u : Cartan) (i : ℤ) (hi : 0 < i) :
    mu lattice (currentAlong lattice u) i a = 0 := by
  let L := (LatticeAllStateField.Y lattice (currentAlong lattice u))[[i]]
  change L a = 0
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b, rfl⟩ := ha
    exact source_product_positive b u i hi
  | zero => exact map_zero _
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

private theorem ground_current_zero_mem (a : NativeStates) (ha : a ∈ groundSpan)
    (u : Cartan) : mu lattice (currentAlong lattice u) 0 a ∈ groundSpan := by
  let L := (LatticeAllStateField.Y lattice (currentAlong lattice u))[[0]]
  change L a ∈ groundSpan
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b, rfl⟩ := ha
    change mu lattice (currentAlong lattice u) 0 (chargedGround b) ∈ groundSpan
    rw [P48qCurrentChargedIterate.source_product_zero]
    exact groundSpan.smul_mem _ (Submodule.subset_span ⟨b, rfl⟩)
  | zero => rw [map_zero]; exact groundSpan.zero_mem
  | add a b _ _ ha hb => rw [map_add]; exact groundSpan.add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact groundSpan.smul_mem c ha

set_option maxHeartbeats 1000000 in
-- Elaborating the bracket aligns the two stripped mode indices.
private theorem stripped_current_ground_commutator
    (u : Cartan) (r : ℕ) (hr : r < 3) (hu : p48qAction u = (ζ ^ r) ^ 2 • u)
    (a : NativeStates) (ha : a ∈ groundSpan) (s z j : ℤ) :
    ⁅(stripResidue (-(r : ℤ)) (currentField u))[[z]],
      (stripResidue s (nativeField a))[[j]]⁆ =
      (stripResidue (-(r : ℤ) + s)
        (nativeField (mu lattice (currentAlong lattice u) 0 a)))[[z + j]] := by
  let m : ℤ := 3 * z + r
  rw [strip_current_ncoeff, VertexOperator.ncoeff_apply, stripResidue_coeff,
    nativeField_current_commutator,
    projectAt_on_residue u r hr hu m (by dsimp [m]; omega)]
  rw [finsum_eq_single _ 0 (fun i hi => by
    rw [ground_current_positive a ha u i (by omega)]
    simp only [map_zero, Pi.zero_apply, smul_zero])]
  simp only [Ring.choose_zero_right, one_smul, Nat.cast_zero, mul_zero, add_zero,
    VertexOperator.ncoeff_apply, stripResidue_coeff]
  rw [show 3 * (-j - 1) + s - (3 * z + (r : ℤ)) =
    3 * (-(z + j) - 1) + (-(r : ℤ) + s) by omega]

open LatticeHalfFockGroundRightCurrentTransport (residueWeight)
open LatticeHalfFockGroundRightCurrentTransport.Calculus (R)
open SignedFieldResidueLocality (residueField residueCoefficient residueLeft residueRight)
open StateFieldResidueReconstruction (epsilon integerBinomial)
open private R_mode ext_modes from D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue
open private R_interchange from D5.S3.VertexAlgebra.GroundRightCurrentTransport.Interchange
-- Li, arXiv:q-alg/9504022, §3. The imported interchange is proved
-- by the finite double residue for a simple-pole commutator.

private theorem ordinaryResidue_eq_R {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : VertexOperator ℂ V) (n : ℤ) : (residueField 1 n A B).operator = R A B n := by
  apply ext_modes
  intro q
  apply LinearMap.ext
  intro x
  rw [(residueField 1 n A B).coefficient, R_mode]
  have hchoose (i : ℕ) : integerBinomial n i = Ring.choose (n : ℂ) i :=
    Ring.map_choose (Int.castRingHom ℂ) n i
  simp only [residueCoefficient, residueLeft, residueRight, residueWeight, epsilon,
    mul_one, hchoose, add_comm n q]

open LatticeHalfFockGroundRightCurrentTransport.Calculus (Z Valid)
open private R_sum R_smul R_Z R_zero from D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue
open private Z_mode from D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue
open private Z_smul Z_sum Z_Z Z_zero Z_sub from
  D5.S3.VertexAlgebra.GroundRightCurrentTransport.Interchange
open private finite_convolution from D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
open P48qNativeCurrentLocality (stripResidue_restoreResidue
  restoreResidue_stripResidue coverDelta_comm_eq_zero_iff)

private def integralAdjusted {V : Type*} [AddCommGroup V] [Module ℂ V]
    (c : ℂ) (A B : VertexOperator ℂ V) (N : ℕ) (n : ℤ) : VertexOperator ℂ V :=
  ∑ i ∈ Finset.range ((N : ℤ) - n).toNat, Ring.choose c i • Z i (R A B (n + i))

private theorem integralAdjusted_pad {V : Type*} [AddCommGroup V] [Module ℂ V]
    (c : ℂ) (A B : VertexOperator ℂ V) (N L : ℕ) (n : ℤ)
    (h : Valid A B N) (hlen : (N : ℤ) ≤ n + L) :
    integralAdjusted c A B N n =
      ∑ i ∈ Finset.range L, Ring.choose c i • Z i (R A B (n + i)) := by
  unfold integralAdjusted
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i _ hi
  rw [h _ (by simp only [Finset.mem_range, not_lt] at hi; omega), Z_zero, smul_zero]

private theorem integralAdjusted_interchange {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A J B A₀ : VertexOperator ℂ V) (c d : ℂ) (n m : ℤ)
    (I K I₀ O P : ℕ) (hI : Valid J B I) (hK : Valid A B K) (h₀ : Valid A₀ B I₀)
    (hO : Valid A (integralAdjusted d J B I m) O)
    (hP : Valid J (integralAdjusted c A B K n) P)
    (ward : ∀ z j : ℤ, J[[z]] * A[[j]] - A[[j]] * J[[z]] = A₀[[z + j]]) :
    integralAdjusted c A (integralAdjusted d J B I m) O n =
      integralAdjusted d J (integralAdjusted c A B K n) P m -
        integralAdjusted (c + d) A₀ B I₀ (n + m) := by
  let L := ((I : ℤ) - m).toNat + ((K : ℤ) - n).toNat + ((I₀ : ℤ) - (n + m)).toNat +
    ((O : ℤ) - n).toNat + ((P : ℤ) - m).toNat
  have hi : (I : ℤ) ≤ m + L := by dsimp [L]; omega
  have hk : (K : ℤ) ≤ n + L := by dsimp [L]; omega
  have h0 : (I₀ : ℤ) ≤ n + m + L := by dsimp [L]; omega
  have ho : (O : ℤ) ≤ n + L := by dsimp [L]; omega
  have hp : (P : ℤ) ≤ m + L := by dsimp [L]; omega
  rw [integralAdjusted_pad _ _ _ _ _ _ hO ho,
    integralAdjusted_pad _ _ _ _ _ _ hP hp,
    integralAdjusted_pad _ _ _ _ _ _ hI hi,
    integralAdjusted_pad _ _ _ _ _ _ hK hk,
    integralAdjusted_pad _ _ _ _ _ _ h₀ h0]
  simp only [R_sum, R_smul, R_Z, Z_sum, Z_smul, Z_Z]
  simp_rw [R_interchange A A₀ J B _ _ ward, Z_sub, smul_sub]
  simp_rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_sub_distrib]
  let F (i : ℕ) := Z i (R A₀ B (n + m + i))
  have hF (i : ℕ) (h : L ≤ i) : F i = 0 := by
    simp only [F, h₀ _ (by omega : (I₀ : ℤ) ≤ n + m + i), Z_zero]
  have hc := finite_convolution c d L F hF
  have hcorr :
      (∑ i ∈ Finset.range L, Ring.choose c i •
        ∑ j ∈ Finset.range L, Ring.choose d j •
          Z ((i : ℤ) + j) (R A₀ B (n + i + (m + j)))) =
        ∑ i ∈ Finset.range L, Ring.choose (c + d) i • Z i (R A₀ B (n + m + i)) := by
    simpa only [F, Nat.cast_add, show ∀ i j : ℕ,
      n + m + ((i : ℤ) + j) = n + i + (m + j) by intros; omega] using hc
  rw [hcorr]
  congr 1
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (Ring.choose c i), add_comm (i : ℤ)]

private theorem strip_adjusted (s t : ℤ) (A B : Field) (N : ℕ) (n : ℤ) :
    stripResidue (s + t) (adjustedResidue s t A B N n) =
      integralAdjusted ((s : ℂ) / 3) (stripResidue s A) (stripResidue t B) N n := by
  apply ext_modes
  intro q
  simp only [VertexOperator.ncoeff_apply, stripResidue_coeff, adjustedResidue,
    integralAdjusted, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [restoreResidue_coeff, ite_eq_left (by omega), VertexOperator.coeff_eq_ncoeff,
    VertexOperator.coeff_eq_ncoeff, Z_mode, ordinaryResidue_eq_R]
  rw [show -((3 * (-q - 1) + (s + t) - (s + t - 3 * (i : ℤ))) / 3) - 1 =
    (-(-q - 1) - 1) - i by omega]

private theorem valid_of_coverLocality (s t : ℤ) (A B : Field) (N : ℕ)
    (ha : InResidue s A) (hb : InResidue t B)
    (h : P48qNativeCurrentLocality.coverDelta^[N]
      (P48qNativeCurrentLocality.coverComm A B) = 0) :
    Valid (stripResidue s A) (stripResidue t B) N := by
  apply LatticeHalfFockGroundRightCurrentTransport.Calculus.valid_of_locality
  rw [Module.End.pow_apply]
  exact (coverDelta_comm_eq_zero_iff s t A B ha hb N).mp h

private theorem adjusted_inResidue (s t : ℤ) (A B : Field) (N : ℕ) (n : ℤ) :
    InResidue (s + t) (adjustedResidue s t A B N n) := by
  intro k hk
  simp only [adjustedResidue, map_sum, Finset.sum_apply, map_smul, Pi.smul_apply,
    restoreResidue_coeff, show ∀ j : ℕ, (s+t-3*(j:ℤ)) % 3 = (s+t) % 3 by intro; omega,
    ite_eq_right hk, smul_zero, Finset.sum_const_zero]

private theorem restore_sub (s : ℤ) (A B : Field) :
    P48qNativeCurrentLocality.restoreResidue s (A - B) =
      P48qNativeCurrentLocality.restoreResidue s A -
      P48qNativeCurrentLocality.restoreResidue s B := by
  apply HVertexOperator.coeff_inj
  funext k
  simp only [restoreResidue_coeff, map_sub, Pi.sub_apply]
  split_ifs <;> simp only [sub_zero]

private theorem adjusted_simplePole_interchange (s j t : ℤ) (A J B A₀ : Field)
    (n m : ℤ) (I K I₀ O P : ℕ)
    (hI : Valid (stripResidue j J) (stripResidue t B) I)
    (hK : Valid (stripResidue s A) (stripResidue t B) K)
    (h₀ : Valid (stripResidue (j + s) A₀) (stripResidue t B) I₀)
    (hO : Valid (stripResidue s A) (stripResidue (j + t) (adjustedResidue j t J B I m)) O)
    (hP : Valid (stripResidue j J) (stripResidue (s + t) (adjustedResidue s t A B K n)) P)
    (ward : ∀ z l : ℤ, (stripResidue j J)[[z]] * (stripResidue s A)[[l]] -
      (stripResidue s A)[[l]] * (stripResidue j J)[[z]] = (stripResidue (j + s) A₀)[[z + l]]) :
    adjustedResidue s (j + t) A (adjustedResidue j t J B I m) O n =
      adjustedResidue j (s + t) J (adjustedResidue s t A B K n) P m -
        adjustedResidue (j + s) t A₀ B I₀ (n + m) := by
  rw [strip_adjusted] at hO hP
  have h := integralAdjusted_interchange _ _ _ _ ((s : ℂ) / 3) ((j : ℂ) / 3) n m
    I K I₀ O P hI hK h₀ hO hP ward
  rw [show (s : ℂ) / 3 + (j : ℂ) / 3 = ((j + s : ℤ) : ℂ) / 3 by push_cast; ring] at h
  have hform (a b : ℤ) (X Y : Field) (N : ℕ) (q : ℤ) :
      adjustedResidue a b X Y N q =
        P48qNativeCurrentLocality.restoreResidue (a + b)
          (integralAdjusted ((a : ℂ) / 3) (stripResidue a X) (stripResidue b Y) N q) := by
    rw [← strip_adjusted a b X Y N q,
      restoreResidue_stripResidue _ _ (adjusted_inResidue a b X Y N q)]
  rw [hform s (j + t), hform j (s + t), hform (j + s) t,
    strip_adjusted, strip_adjusted, show s + (j + t) = j + (s + t) by omega,
    show j + s + t = j + (s + t) by omega, h, restore_sub]

open P48qNativeCurrentLocality (coverDelta coverComm)
open private lift_current currentStateLinear from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality
open P48qNativePairwiseLocality (nativeField_pairwise_locality)
open NativeStandardThirdLift (standardLift_compatible)

open P48qNativeCurrentLocality (CoverLocal)
open private coverLocal_iff localCoefficients strip_local restore_local from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentLocality
open private coverLocal_symm from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality

private theorem adjusted_coverLocal (s t c : ℤ) (A B C : Field) (N : ℕ) (n : ℤ)
    (hc : InResidue c C) (hAC : CoverLocal A C) (hBC : CoverLocal B C)
    (hAB : CoverLocal A B) : CoverLocal (adjustedResidue s t A B N n) C := by
  have ordinary (X Y : Field) :
      SignedFieldNormalProductLocality.signedComm (1 : ℂ) X Y =
        FieldNormalProductLocality.commutator X Y := by
    funext i j
    simp [SignedFieldNormalProductLocality.signedComm, FieldNormalProductLocality.commutator]
  apply (coverLocal_iff _ C).mpr
  simp only [adjustedResidue, map_sum, map_smul]
  apply (localCoefficients C).sum_mem
  intro i _
  apply (localCoefficients C).smul_mem
  apply (coverLocal_iff _ C).mp
  apply restore_local _ c _ C hc
  have h := SignedFieldResidueLocality.residue_locality 1 1 1
    (stripResidue s A) (stripResidue t B) (stripResidue c C)
  simp only [mul_one, ordinary] at h
  exact h (strip_local s c A C hAC) (strip_local t c B C hBC)
    (strip_local s t A B hAB) (n + i)

private theorem current_lift_eigen (u : Cartan) (r : ℕ)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) :
    σ (currentAlong lattice u) = ζ ^ (-(r : ℤ)) • currentAlong lattice u := by
  have hζ : IsPrimitiveRoot ζ 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive
  have hz : (ζ ^ r) ^ 3 = 1 := by rw [pow_right_comm, hζ.pow_eq_one, one_pow]
  have hp : ζ ^ (-(r : ℤ)) = (ζ ^ r) ^ 2 := by
    rw [zpow_neg, zpow_natCast]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', hz]
  rw [hp, lift_current, hu]
  exact currentStateLinear.map_smul _ _

private theorem mu_eigen (a b : NativeStates) (s t m : ℤ)
    (ha : σ a = ζ ^ s • a) (hb : σ b = ζ ^ t • b) :
    σ (mu lattice a m b) = ζ ^ (s + t) • mu lattice a m b := by
  unfold mu
  rw [(standardLift_compatible lattice g g_cube g_isometry).2.1, ha, hb,
    zpow_add₀ (Units.ne_zero ThirdTwistedChargeCocycle.zeta)]
  simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, smul_smul, mul_comm]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- The theorem aligns the actual eigenstates and five pairwise locality orders.
/-- The local-field commutator for a current and a lift eigenstate in the
charged ground span. The higher current products of the charged ground vanish,
so the zero product is the entire correction at all integer product labels. -/
theorem adjustedResidue_current_ground_interchange
    (u : Cartan) (r : ℕ) (hr : r < 3) (hu : p48qAction u = (ζ ^ r) ^ 2 • u)
    (a b : NativeStates) (s t n m : ℤ) (ha : a ∈ groundSpan)
    (hAe : σ a = ζ ^ s • a) (hb : σ b = ζ ^ t • b) :
    let j := -(r : ℤ)
    let A := nativeField a
    let J := nativeField (currentAlong lattice u)
    let B := nativeField b
    let A₀ := nativeField (mu lattice (currentAlong lattice u) 0 a)
    ∃ I K I₀ O P : ℕ,
      coverDelta^[I] (coverComm J B) = 0 ∧
      coverDelta^[K] (coverComm A B) = 0 ∧
      coverDelta^[I₀] (coverComm A₀ B) = 0 ∧
      coverDelta^[O] (coverComm A (adjustedResidue j t J B I m)) = 0 ∧
      coverDelta^[P] (coverComm J (adjustedResidue s t A B K n)) = 0 ∧
      adjustedResidue s (j + t) A (adjustedResidue j t J B I m) O n =
        adjustedResidue j (s + t) J (adjustedResidue s t A B K n) P m -
          adjustedResidue (j + s) t A₀ B I₀ (n + m) := by
  let j := -(r : ℤ)
  let h := currentAlong lattice u
  let a₀ := mu lattice h 0 a
  let A := nativeField a
  let J := nativeField h
  let B := nativeField b
  let A₀ := nativeField a₀
  have hJe := current_lift_eigen u r hu
  have hA₀e : σ a₀ = ζ ^ (j + s) • a₀ := mu_eigen h a j s 0 hJe hAe
  obtain ⟨I, hI⟩ := nativeField_pairwise_locality h b
  obtain ⟨K, hK⟩ := nativeField_pairwise_locality a b
  obtain ⟨I₀, hI₀⟩ := nativeField_pairwise_locality a₀ b
  have hs : InResidue s A := nativeField_inResidue _ _ hAe
  have hj : InResidue j J := nativeField_inResidue _ _ hJe
  have ht : InResidue t B := nativeField_inResidue _ _ hb
  have h0 : InResidue (j + s) A₀ := nativeField_inResidue _ _ hA₀e
  have hAJ := nativeField_pairwise_locality a h
  have hJA := nativeField_pairwise_locality h a
  obtain ⟨O, hO⟩ := coverLocal_symm
    (adjusted_coverLocal j t s J B A I m hs hJA (coverLocal_symm ⟨K, hK⟩) ⟨I, hI⟩)
  obtain ⟨P, hP⟩ := coverLocal_symm
    (adjusted_coverLocal s t j A B J K n hj hAJ (coverLocal_symm ⟨I, hI⟩) ⟨K, hK⟩)
  refine ⟨I, K, I₀, O, P, hI, hK, hI₀, hO, hP, ?_⟩
  refine adjusted_simplePole_interchange s j t A J B A₀ n m I K I₀ O P
    (valid_of_coverLocality _ _ _ _ _ hj ht hI) (valid_of_coverLocality _ _ _ _ _ hs ht hK)
    (valid_of_coverLocality _ _ _ _ _ h0 ht hI₀)
    (valid_of_coverLocality _ _ _ _ _ hs (adjusted_inResidue _ _ _ _ _ _) hO)
    (valid_of_coverLocality _ _ _ _ _ hj (adjusted_inResidue _ _ _ _ _ _) hP) ?_
  intro z l
  simpa only [A, J, h, j, A₀, a₀, P48qNativeMonodromy.nativeField_current,
    LieRing.of_associative_ring_bracket] using
    stripped_current_ground_commutator u r hr hu a ha s z l

#check adjustedResidue_current_ground_interchange
#print axioms adjustedResidue_current_ground_interchange


open LatticeSugawaraCurrents (vectorFrequencyBound)
open P48qNativeResidueProduct (adjustedResidue_coeff adjustedResidue_cutoff_mono
  adjustedResidue_native_current)
open private current_cleared_nonneg from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeResidueProduct
open private EigenWord prepend groundProject_mem from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality
open LatticeActualStateFieldCalculus (mode_commutator commutatorTerm)

private theorem adjusted_at_valid_cutoffs (s t : ℤ) (A B : Field) (N M : ℕ)
    (hN : ∀ q ≥ (N : ℤ), clearedResidue s t A B q = 0)
    (hM : ∀ q ≥ (M : ℤ), clearedResidue s t A B q = 0) (n : ℤ) :
    adjustedResidue s t A B N n = adjustedResidue s t A B M n :=
  (adjustedResidue_cutoff_mono s t A B N (max N M) (le_max_left _ _) hN n).trans
    (adjustedResidue_cutoff_mono s t A B M (max N M) (le_max_right _ _) hM n).symm

private theorem adjusted_current_at_locality (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (b : NativeStates) (t : ℤ)
    (he : σ b = ζ ^ t • b) (N : ℕ) (n : ℤ)
    (hN : coverDelta^[N] (coverComm (nativeField (currentAlong lattice u)) (nativeField b)) = 0) :
    adjustedResidue (-(r : ℤ)) t (nativeField (currentAlong lattice u)) (nativeField b) N n =
      nativeField (mu lattice (currentAlong lattice u) n b) := by
  have hb := nativeField_inResidue b t he
  have hc := nativeField_inResidue (currentAlong lattice u) _ (current_lift_eigen u r hu)
  refine (adjusted_at_valid_cutoffs _ _ _ _ N (vectorFrequencyBound lattice b + 1)
    (fun q hq => clearedResidue_zero_of_locality _ _ _ _ hc hb N hN q hq) ?_ n).trans
      (adjustedResidue_native_current u r hr hu b t hb n)
  intro p hp
  have hnonneg : 0 ≤ p := by omega
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hnonneg
  apply HVertexOperator.coeff_inj
  funext l
  let k := l - 3 * (q : ℤ)
  have hk : k + 3 * (q : ℤ) = l := by dsimp [k]; ring
  rw [P48qNativeMonodromy.nativeField_current, ← hk, current_cleared_nonneg u r hr hu b t hb]
  have hq : vectorFrequencyBound lattice b + 1 ≤ q := by exact_mod_cast hp
  simp [binomialTail, Nat.sub_eq_zero_of_le hq]

private theorem source_current_ground_commute (u : Cartan) (a b : NativeStates)
    (ha : a ∈ groundSpan) (m n : ℤ) :
    mu lattice a n (mu lattice (currentAlong lattice u) m b) =
      mu lattice (currentAlong lattice u) m (mu lattice a n b) -
        mu lattice (mu lattice (currentAlong lattice u) 0 a) (n + m) b := by
  let h := currentAlong lattice u
  have law := mode_commutator lattice h a m n
  rw [finsum_eq_single _ 0 (fun i hi => by
    unfold commutatorTerm
    rw [ground_current_positive a ha u i (by omega)]
    simp only [map_zero, Pi.zero_apply, smul_zero])] at law
  simp only [commutatorTerm, StateFieldResidueReconstruction.integerBinomial,
    Ring.choose_zero_right, Int.cast_one, one_smul, Nat.cast_zero, sub_zero] at law
  have at_b := LinearMap.congr_fun law b
  change mu lattice h m (mu lattice a n b) - mu lattice a n (mu lattice h m b) =
    mu lattice (mu lattice h 0 a) (m + n) b at at_b
  rw [add_comm m n] at at_b
  rw [← at_b]
  abel

private def GroundFirstCompatible (b : NativeStates) (t : ℤ) : Prop :=
  ∀ (a : NativeStates) (s : ℤ), a ∈ groundSpan → σ a = ζ ^ s • a →
    ∀ (N : ℕ), coverDelta^[N] (coverComm (nativeField a) (nativeField b)) = 0 →
      ∀ n, adjustedResidue s t (nativeField a) (nativeField b) N n =
        nativeField (mu lattice a n b)

private theorem groundSpan_sum (a : NativeStates) (ha : a ∈ groundSpan) :
    ∃ c : Charge lattice →₀ ℂ,
      groundSum (fun i : c.support => i.val) (fun i => c i.val) = a := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp ha
  refine ⟨c, ?_⟩
  rw [groundSum, c.support.sum_coe_sort (fun i => c i • chargedGround i)]
  exact hc

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- The cutoff is chosen over arbitrary finite indices and reused by both radial sums.
private theorem groundSums_adjusted_atLocality {I J : Type*} [Fintype I] [Fintype J]
    (a : I → Charge lattice) (b : J → Charge lattice) (u : I → ℂ) (v : J → ℂ)
    (s t : ℤ) (N : ℕ) (n : ℤ)
    (hs : InResidue s (nativeField (groundSum a u)))
    (ht : InResidue t (nativeField (groundSum b v)))
    (hN : coverDelta^[N]
      (coverComm (nativeField (groundSum a u)) (nativeField (groundSum b v))) = 0) :
    adjustedResidue s t (nativeField (groundSum a u)) (nativeField (groundSum b v)) N n =
      nativeField (mu lattice (groundSum a u) n (groundSum b v)) := by
  let order (ij : I × J) := chargedLocalityOrder (a ij.1) (b ij.2)
  let M := Finset.univ.sup order
  have hM (i : I) (j : J) : chargedLocalityOrder (a i) (b j) ≤ M := by
    change order (i, j) ≤ Finset.univ.sup order
    exact Finset.le_sup (f := order) (Finset.mem_univ (i, j))
  let A := nativeField (groundSum a u)
  let B := nativeField (groundSum b v)
  have hloc : coverDelta^[M] (coverComm A B) = 0 :=
    clear_radial_locality A B M (radialGroundSum a b u v) (radialGroundSum b a v u)
      (radialGroundSum_coeff a b u v)
      (fun x p k l => radialGroundSum_coeff b a v u x p l k)
      (fun x p => radialGroundSum_cleared_swap a b u v x p M hM)
  exact (adjusted_at_valid_cutoffs s t A B N M
    (fun q hq => clearedResidue_zero_of_locality s t A B hs ht N hN q hq)
    (fun q hq => clearedResidue_zero_of_locality s t A B hs ht M hloc q hq) n).trans
      (groundSums_adjustedResidue a b u v s t hs ht M hM n)

private theorem groundFirst_ground (b : NativeStates) (t : ℤ) (hb : b ∈ groundSpan)
    (hbe : σ b = ζ ^ t • b) : GroundFirstCompatible b t := by
  intro a s ha hae N hN n
  obtain ⟨c, hc⟩ := groundSpan_sum a ha
  obtain ⟨d, hd⟩ := groundSpan_sum b hb
  subst a
  subst b
  exact groundSums_adjusted_atLocality _ _ _ _ s t N n
    (nativeField_inResidue _ s hae) (nativeField_inResidue _ t hbe) hN

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- The two inner iterations carry different native inputs and locality orders.
private theorem groundFirst_current_step (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (b : NativeStates) (t m : ℤ)
    (hbe : σ b = ζ ^ t • b) (ih : GroundFirstCompatible b t) :
    GroundFirstCompatible (mu lattice (currentAlong lattice u) m b) (-(r : ℤ) + t) := by
  intro a s ha hae N hN n
  let h := currentAlong lattice u
  let a₀ := mu lattice h 0 a
  let j := -(r : ℤ)
  let b' := mu lattice h m b
  let w := mu lattice a n b
  have hhe := current_lift_eigen u r hu
  have hwe := mu_eigen a b s t n hae hbe
  have hbe' := mu_eigen h b j t m hhe hbe
  obtain ⟨I, K, I₀, O, P, hI, hK, hI₀, hO, hP, eq⟩ :=
    adjustedResidue_current_ground_interchange u r hr hu a b s t n m ha hae hbe
  have hinner := adjusted_current_at_locality u r hr hu b t hbe I m hI
  rw [hinner] at hO eq
  have hpair := ih a s ha hae K hK n
  rw [hpair] at hP eq
  rw [adjusted_current_at_locality u r hr hu w (s + t) hwe P m hP,
    ih a₀ (j + s) (ground_current_zero_mem a ha u)
      (mu_eigen h a j s 0 hhe hae) I₀ hI₀ (n + m), ← map_sub,
    ← source_current_ground_commute u a b ha m n] at eq
  have hs := nativeField_inResidue a s hae
  have ht := nativeField_inResidue b' (j + t) hbe'
  exact (adjusted_at_valid_cutoffs _ _ _ _ N O
    (fun q hq => clearedResidue_zero_of_locality _ _ _ _ hs ht N hN q hq)
    (fun q hq => clearedResidue_zero_of_locality _ _ _ _ hs ht O hO q hq) n).trans eq

/-- Charged-ground eigenstates act compatibly on every negative-current
eigenword, for every integer product label and every uniform locality order. -/
theorem adjustedResidue_ground_first_eigenWord {d : ℕ} {b : NativeStates}
    (hb : EigenWord d b) : ∃ t : ℤ, σ b = ζ ^ t • b ∧ GroundFirstCompatible b t := by
  induction hb with
  | ground a p =>
    have h : σ (liftProject p (chargeGround a)) =
        ζ ^ (((p.val * 2 : ℕ) : ℤ)) • liftProject p (chargeGround a) := by
      simpa only [zpow_natCast, pow_mul] using liftProject_eigen p (chargeGround a)
    exact ⟨_, h, groundFirst_ground _ _ (groundProject_mem a p) h⟩
  | @cons d b hb level u r hu ih =>
    obtain ⟨t, he, hc⟩ := ih
    exact ⟨-(r.val : ℤ) + t,
      mu_eigen _ _ _ _ _ (current_lift_eigen u r.val hu) he,
      groundFirst_current_step u r.val r.isLt hu b t (-((level : ℕ) : ℤ)) he hc⟩

#check adjustedResidue_ground_first_eigenWord
#print axioms adjustedResidue_ground_first_eigenWord

open private eigenWords eigenWordSpan eigenWordSpan_eq_top root_cube from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality
open private deltaCoverEnd coverOrder_mono from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentLocality
open P48qNativeResidueProduct
  (adjustedResidue_strip_left_add_three adjustedResidue_strip_right_add_three)
open P48qNativeCurrentLocality (restoreResidue)

private theorem zeta_zpow_eq_iff (s t : ℤ) : ζ ^ s = ζ ^ t ↔ s % 3 = t % 3 := by
  have hz : IsPrimitiveRoot ζ 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive
  have hne := Units.ne_zero ThirdTwistedChargeCocycle.zeta
  rw [← div_eq_one_iff_eq (zpow_ne_zero t hne), ← zpow_sub₀ hne, hz.zpow_eq_one_iff_dvd]
  change (3 : ℤ) ∣ s - t ↔ _
  omega

private theorem periodThree {D : Type*} {F : ℤ → D} (h : Function.Periodic F 3)
    (a b : ℤ) (hab : a % 3 = b % 3) : F a = F b := by
  have he : b + ((a - b) / 3) * 3 = a := by omega
  simpa only [Int.cast_id, he] using (h.int_mul ((a - b) / 3)) b

private theorem adjusted_strip_representatives (s s' t t' : ℤ) (A B : Field) (N : ℕ) (n : ℤ)
    (hs : s % 3 = s' % 3) (ht : t % 3 = t' % 3) (hA : InResidue s A) (hB : InResidue t B)
    (hN : coverDelta^[N] (coverComm A B) = 0) :
    adjustedResidue s t A B N n = adjustedResidue s' t' A B N n := by
  let left (k : ℤ) := if k % 3 = s % 3 then adjustedResidue k t A B N n else 0
  have hleft : Function.Periodic left 3 := by
    intro k
    have hmod : (k + 3) % 3 = k % 3 := by omega
    by_cases hk : k % 3 = s % 3
    · simp only [left, hmod, ite_eq_left hk]
      exact adjustedResidue_strip_left_add_three _ _ A B
        (fun l hl => hA l (by simpa only [hk] using hl)) hB N hN n
    · simp only [left, hmod, ite_eq_right hk]
  have hfirst : adjustedResidue s t A B N n = adjustedResidue s' t A B N n := by
    simpa only [left, ite_eq_left rfl, ite_eq_left hs.symm] using periodThree hleft s s' hs
  exact hfirst.trans (periodThree (F := fun k => adjustedResidue s' k A B N n)
    (fun k => adjustedResidue_strip_right_add_three s' k A B N n) t t' ht)

private theorem liftProject_eigenstate (r : Fin 3) (v : NativeStates) (t : ℤ)
    (hv : σ v = ζ ^ t • v) :
    liftProject r v = if ζ ^ t = (ζ ^ r.val) ^ 2 then v else 0 := by
  by_cases h : ζ ^ t = (ζ ^ r.val) ^ 2
  · rw [ite_eq_left h]
    have hv' := hv
    rw [h] at hv'
    have hc : (ζ ^ r.val) ^ 3 = 1 := root_cube _
    have hm : ζ ^ r.val * (ζ ^ r.val) ^ 2 = 1 := by rw [← pow_succ', hc]
    have hσ₂ : σ (σ v) = ((ζ ^ r.val) ^ 2) ^ 2 • v := by
      rw [hv', map_smul, hv', smul_smul, ← pow_two ((ζ ^ r.val) ^ 2)]
    have hm₂ : (ζ ^ r.val) ^ 2 * ((ζ ^ r.val) ^ 2) ^ 2 = 1 := by
      rw [← pow_succ', pow_right_comm, hc, one_pow]
    rw [liftProject, hσ₂, hv', smul_smul, hm, smul_smul, hm₂, one_smul]
    calc
      (3 : ℂ)⁻¹ • (v + v + v) = (3 : ℂ)⁻¹ • ((3 : ℂ) • v) := by module
      _ = v := by rw [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  · rw [ite_eq_right h]
    have hm : σ (liftProject r v) = ζ ^ t • liftProject r v := by
      have hσ₂ : σ (σ v) = (ζ ^ t * ζ ^ t) • v := by
        rw [hv, map_smul, hv, smul_smul]
      have hform : liftProject r v =
          ((3 : ℂ)⁻¹ * (1 + ζ ^ r.val * ζ ^ t + (ζ ^ r.val) ^ 2 * (ζ ^ t * ζ ^ t))) • v := by
        rw [liftProject, hσ₂, hv]
        simp only [mul_smul, add_smul, one_smul]
      rw [hform, map_smul, hv, smul_comm]
    have hzero : (ζ ^ t - (ζ ^ r.val) ^ 2) • liftProject r v = 0 := by
      rw [sub_smul, ← hm, ← liftProject_eigen, sub_self]
    exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr h)

private theorem liftProject_sum {I : Type*} (r : Fin 3) (S : Finset I)
    (c : I → ℂ) (v : I → NativeStates) :
    liftProject r (∑ i ∈ S, c i • v i) = ∑ i ∈ S, c i • liftProject r (v i) := by
  simp only [liftProject, map_sum, map_smul, Finset.smul_sum]
  simp_rw [← Finset.sum_add_distrib]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  module

private theorem adjustedResidue_right_sum {I : Type*} (S : Finset I)
    (c : I → ℂ) (B : I → Field) (s t : ℤ) (A : Field) (N : ℕ) (n : ℤ) :
    adjustedResidue s t A (∑ i ∈ S, c i • B i) N n =
      ∑ i ∈ S, c i • adjustedResidue s t A (B i) N n := by
  have strip_sum (k : ℤ) (F : I → Field) :
      stripResidue k (∑ i ∈ S, c i • F i) = ∑ i ∈ S, c i • stripResidue k (F i) := by
    apply HVertexOperator.coeff_inj
    funext l
    simp only [stripResidue_coeff, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  have hsum : InResidue (s + t) (∑ i ∈ S, c i • adjustedResidue s t A (B i) N n) := by
    intro k hk
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
      fun i => adjusted_inResidue s t A (B i) N n k hk, smul_zero, Finset.sum_const_zero]
  rw [← restoreResidue_stripResidue _ _ (adjusted_inResidue s t A _ N n),
    ← restoreResidue_stripResidue _ _ hsum]
  congr 1
  simp only [strip_sum, strip_adjusted, integralAdjusted, R_sum, R_smul, Z_sum, Z_smul]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [mul_comm]

set_option maxHeartbeats 1000000 in
-- Elaboration aligns the projected states, locality orders, and finite field sums.
/-- Charged-ground lift eigenstates act compatibly on every actual lift
eigenstate, at every integer product label and every cutoff for the cleared residues. -/
theorem adjustedResidue_ground_first_eigenstate (a b : NativeStates) (s t : ℤ)
    (ha : a ∈ groundSpan) (hae : σ a = ζ ^ s • a) (hbe : σ b = ζ ^ t • b)
    (N : ℕ) (hN : ∀ q ≥ (N : ℤ), clearedResidue s t (nativeField a) (nativeField b) q = 0)
    (n : ℤ) :
    adjustedResidue s t (nativeField a) (nativeField b) N n =
      nativeField (mu lattice a n b) := by
  classical
  let r : Fin 3 := ⟨((2 * t) % 3).toNat, by omega⟩
  have hr : ζ ^ t = (ζ ^ r.val) ^ 2 := by
    rw [← pow_mul, ← zpow_natCast, zeta_zpow_eq_iff]
    dsimp [r]
    omega
  have hmem : b ∈ Submodule.span ℂ eigenWords := by
    change b ∈ eigenWordSpan
    rw [eigenWordSpan_eq_top]
    trivial
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_iff_linearCombination ℂ eigenWords b).mp hmem
  rw [Finsupp.linearCombination_apply] at hc
  let v (i : eigenWords) := liftProject r i.val
  have hsum : (∑ i ∈ c.support, c i • v i) = b := by
    have hp := congrArg (liftProject r) hc
    rw [liftProject_eigenstate r b t hbe, ite_eq_left hr] at hp
    exact (liftProject_sum r c.support c Subtype.val).symm.trans hp
  have he (i : eigenWords) : σ (v i) = ζ ^ t • v i := by
    rw [hr]
    exact liftProject_eigen r i.val
  choose order horder using fun i : eigenWords => nativeField_pairwise_locality a (v i)
  let M := max N (c.support.sup order)
  have hM (i : eigenWords) (hi : i ∈ c.support) :
      coverDelta^[M] (coverComm (nativeField a) (nativeField (v i))) = 0 := by
    have horder' :
        (deltaCoverEnd ^ order i) (coverComm (nativeField a) (nativeField (v i))) = 0 := by
      rw [Module.End.pow_apply]
      exact horder i
    have hM' := coverOrder_mono (le_trans (Finset.le_sup (f := order) hi) (le_max_right N _))
      horder'
    rw [Module.End.pow_apply] at hM'
    exact hM'
  have term (i : eigenWords) (hi : i ∈ c.support) :
      adjustedResidue s t (nativeField a) (nativeField (v i)) M n =
        nativeField (mu lattice a n (v i)) := by
    obtain ⟨d, hd⟩ := i.property
    obtain ⟨t', he', hcomp⟩ := adjustedResidue_ground_first_eigenWord hd
    by_cases hm : ζ ^ t = ζ ^ t'
    · have hv : v i = i.val := by
        dsimp [v]
        rw [liftProject_eigenstate r i.val t' he', ite_eq_left (hm.symm.trans hr)]
      have ht' := (zeta_zpow_eq_iff t t').mp hm
      have hs := nativeField_inResidue a s hae
      have ht := nativeField_inResidue (v i) t (he i)
      have ha' : σ a = ζ ^ (s % 3) • a := by
        rw [hae, (zeta_zpow_eq_iff s (s % 3)).mpr (by omega)]
      calc
        _ = adjustedResidue (s % 3) t' (nativeField a) (nativeField (v i)) M n :=
          adjusted_strip_representatives s (s % 3) t t' _ _ M n (by omega) ht' hs ht (hM i hi)
        _ = _ := by
          simpa only [hv] using hcomp a (s % 3) ha ha' M (by simpa only [hv] using hM i hi) n
    · have hv : v i = 0 := by
        exact (liftProject_eigenstate r i.val t' he').trans
          (ite_eq_right (fun hh => hm (hr.trans hh.symm)))
      simp only [hv, mu, map_zero]
      simpa only [Finset.sum_empty] using adjustedResidue_right_sum
        (∅ : Finset Unit) (fun _ => 0) (fun _ => 0) s t (nativeField a) M n
  have hcut := adjustedResidue_cutoff_mono s t _ _ N M (le_max_left _ _) hN n
  rw [hcut, ← hsum]
  simp only [mu, map_sum, map_smul]
  rw [adjustedResidue_right_sum]
  exact Finset.sum_congr rfl fun i hi => congrArg (fun F : Field => c i • F) (term i hi)

#check adjustedResidue_ground_first_eigenstate
#print axioms adjustedResidue_ground_first_eigenstate

#check adjustedResidue_native_projected_chargedGround
#check exists_adjustedResidue_native_projected_chargedGround
#print axioms adjustedResidue_native_projected_chargedGround
#print axioms exists_adjustedResidue_native_projected_chargedGround

end Product

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedResidueProduct
