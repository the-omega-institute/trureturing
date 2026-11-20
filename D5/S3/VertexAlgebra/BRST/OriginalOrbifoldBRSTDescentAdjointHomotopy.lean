/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTDescentAdjointHomotopy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTDescentAdjointHomotopy
   mirror-E: none(waiver:algebraic-original-brst-descent-adjoint-homotopy)
   anchors: []
   utility: none
   digest: Native BRST homotopy for the positive Virasoro corrections to descent. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTL1Nilpotent

/-!
The two antighosts give a relative BRST homotopy for the finite positive-mode
descent corrections. Local nilpotence of the total positive mode provides a
common cutoff at which the terminal term vanishes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTDescentAdjointHomotopy

open D5.S3.Quantum.Fermionic
open OriginalOrbifoldCriticalMatter (Matter State Q b matterDatum mode vacuum Q_squared)
open OriginalOrbifoldBRSTDescent (relativeStates translation_zero_mode)
open OriginalOrbifoldBRSTL1Nilpotent (totalL1_lowers_energy totalL1_locally_nilpotent)
open OriginalOrbifoldBRSTStateField (Y Y_vacuum OmegaTotal conformal_modes)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTFieldAxioms (translation translation_eq_total_mode
  translation_eq_conformal_ncoeff stateField_creation)
open OriginalOrbifoldBRSTModeDerivation (Q_mode b_zero_mode)
open OriginalOrbifoldBRSTSuperJacobi (residueClosure homogeneous_borcherds)
open SignedFieldResidueLocality (residueField residueCoefficient residueLeft residueRight)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open private ward b_parity Q_parity parity_vacuum translation_creation b_car b_square from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent
open private of_parity_eigenspaces one_binomial_sum signed_zero_binomial_sum from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTModeDerivation
open private identity_ncoeff from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTStateField

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

local notation "E" => VirasoroBRST.Ltotal matterDatum 1
local notation "T" => VirasoroBRST.Ltotal matterDatum (-1)
local notation "L₀" => VirasoroBRST.Ltotal matterDatum 0

private theorem Q_E (x : State) : Q (E x) = E (Q x) := by
  have hQ : Q * Q = 0 := by simpa only [pow_two] using Q_squared
  have h : Q * E = E * Q := by
    have hE : E = Q * b 1 + b 1 * Q := (VirasoroBRST.Q_ward_b matterDatum 1).symm
    calc
      Q * E = Q * (Q * b 1 + b 1 * Q) := congrArg (Q * ·) hE
      _ = (Q * Q) * b 1 + (Q * b 1) * Q := by rw [mul_add, mul_assoc, mul_assoc]
      _ = (Q * b 1) * Q + b 1 * (Q * Q) := by
        simp only [hQ, zero_mul, mul_zero, zero_add, add_zero]
      _ = (Q * b 1 + b 1 * Q) * Q :=
        ((add_mul (Q * b 1) (b 1 * Q) Q).trans
          (congrArg ((Q * b 1) * Q + ·) (mul_assoc (b 1) Q Q))).symm
      _ = E * Q := congrArg (· * Q) hE.symm
  exact LinearMap.congr_fun h x

private theorem Q_E_pow (k : ℕ) (x : State) : Q ((E ^ k) x) = (E ^ k) (Q x) := by
  induction k with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ k ih => simp only [pow_succ', Module.End.mul_apply, Q_E, ih]

private theorem E_T (x : State) : E (T x) - T (E x) = (2 : ℂ) • L₀ x := by
  have h : E * T - T * E = (2 : ℂ) • L₀ := by
    apply TensorProduct.ext'
    intro v w
    have hm := LinearMap.congr_fun
      (OriginalOrbifoldCriticalMatter.mode_virasoro 1 (-1)) v
    have hg := LinearMap.congr_fun (BcGhostVirasoro.virasoro 1 (-1)) w
    norm_num [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.smul_apply] at hm hg
    change
      ((TensorProduct.map (mode 1) LinearMap.id +
          TensorProduct.map LinearMap.id (BcGhostVirasoro.L 1)) *
        (TensorProduct.map (mode (-1)) LinearMap.id +
          TensorProduct.map LinearMap.id (BcGhostVirasoro.L (-1))) -
        (TensorProduct.map (mode (-1)) LinearMap.id +
          TensorProduct.map LinearMap.id (BcGhostVirasoro.L (-1))) *
        (TensorProduct.map (mode 1) LinearMap.id +
          TensorProduct.map LinearMap.id (BcGhostVirasoro.L 1)) :
        Module.End ℂ State) (v ⊗ₜ[ℂ] w) =
      ((2 : ℂ) • (TensorProduct.map (mode 0) LinearMap.id +
        TensorProduct.map LinearMap.id (BcGhostVirasoro.L 0)) :
        Module.End ℂ State) (v ⊗ₜ[ℂ] w)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.mul_apply, map_add, TensorProduct.map_tmul, LinearMap.id_apply]
    calc
      _ = (mode 1 (mode (-1) v) - mode (-1) (mode 1 v)) ⊗ₜ[ℂ] w +
          v ⊗ₜ[ℂ] (BcGhostVirasoro.L 1 (BcGhostVirasoro.L (-1) w) -
            BcGhostVirasoro.L (-1) (BcGhostVirasoro.L 1 w)) := by
        simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
        abel
      _ = _ := by rw [hm, hg, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]
  exact LinearMap.congr_fun h x

private theorem total_b (m r : ℤ) (x : State) :
    VirasoroBRST.Ltotal matterDatum m (b r x) - b r (VirasoroBRST.Ltotal matterDatum m x) =
      ((m - r : ℤ) : ℂ) • b (m + r) x := by
  have h : VirasoroBRST.Ltotal matterDatum m * b r - b r * VirasoroBRST.Ltotal matterDatum m =
      ((m - r : ℤ) : ℂ) • b (m + r) := by
    apply TensorProduct.ext'
    intro v w
    have hg := LinearMap.congr_fun (BcGhostVirasoro.ward_b m r) w
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply] at hg
    simp only [b, VirasoroBRST.Ltotal, VirasoroBRST.matterMode, VirasoroBRST.ghostVirasoro,
      VirasoroBRST.ghostB, BcGhostChargeTensor.B, BcGhostChargeTensor.liftGhost,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
      map_add, TensorProduct.map_tmul, LinearMap.id_apply]
    rw [add_sub_add_left_eq_sub, ← TensorProduct.tmul_sub, hg, TensorProduct.tmul_smul]
  exact LinearMap.congr_fun h x

private theorem Q_double_antighost (u : State) (hb : b 0 u = 0) (hQ : Q u = 0) :
    Q (b 1 (b (-1) u)) = E (b (-1) u) - T (b 1 u) := by
  have ha : Q (b (-1) u) = T u := by
    simpa only [hQ, map_zero, add_zero] using ward (-1) u
  have ht : T (b 1 u) = b 1 (T u) := by
    apply sub_eq_zero.mp
    simpa only [show (-1 : ℤ) + 1 = 0 by norm_num, hb, smul_zero] using total_b (-1) 1 u
  apply eq_sub_of_add_eq
  rw [ht, ← ha]
  exact ward 1 (b (-1) u)

private theorem antighost_energy (u : State) (hu : L₀ u = 0) :
    L₀ (b 1 u) = -b 1 u := by
  simpa only [hu, map_zero, sub_zero, zero_sub, zero_add, Int.cast_neg, Int.cast_one,
    neg_one_smul] using total_b 0 1 u

private theorem E_pow_energy (x : State) (e : ℤ) (hx : L₀ x = (e : ℂ) • x) (k : ℕ) :
    L₀ ((E ^ k) x) = ((e : ℂ) - (k : ℂ)) • (E ^ k) x := by
  induction k with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero] using hx
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      have hk : L₀ ((E ^ k) x) = ((e - (k : ℤ) : ℤ) : ℂ) • (E ^ k) x := by
        simpa only [Int.cast_sub, Int.cast_natCast] using ih
      have h := totalL1_lowers_energy hk
      simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one] at h
      rw [Nat.cast_succ, show (e : ℂ) - ((k : ℂ) + 1) = (e : ℂ) - (k : ℂ) - 1 by ring]
      exact h

private theorem E_pow_T (x : State) (hx : L₀ x = -x) (k : ℕ) :
    (E ^ (k + 1)) (T x) =
      T ((E ^ (k + 1)) x) - (((k : ℂ) + 1) * ((k : ℂ) + 2)) • (E ^ k) x := by
  induction k with
  | zero =>
      simpa only [Nat.cast_zero, zero_add, one_mul, pow_zero, pow_one, Module.End.one_apply,
        hx, smul_neg, sub_eq_add_neg] using
        (sub_eq_iff_eq_add.mp (E_T x)).trans (add_comm _ _)
  | succ k ih =>
      have hc := sub_eq_iff_eq_add.mp (E_T ((E ^ (k + 1)) x))
      have he := E_pow_energy x (-1)
        (by simpa only [Int.cast_neg, Int.cast_one, neg_one_smul] using hx) (k + 1)
      rw [Int.cast_neg, Int.cast_one, Nat.cast_succ,
        show -(1 : ℂ) - ((k : ℂ) + 1) = -((k : ℂ) + 2) by ring] at he
      rw [he] at hc
      have hstep : (E ^ (k + 1 + 1)) (T x) =
          E ((E ^ (k + 1)) (T x)) := by rw [pow_succ', Module.End.mul_apply]
      have hxstep : (E ^ (k + 1 + 1)) x = E ((E ^ (k + 1)) x) := by
        rw [pow_succ', Module.End.mul_apply]
      have hxprev : E ((E ^ k) x) = (E ^ (k + 1)) x := by
        rw [pow_succ', Module.End.mul_apply]
      rw [hstep, hxstep, ih, map_sub, map_smul, hc, hxprev, Nat.cast_succ]
      module

/-- The Ward homotopy on a relative cycle, with the correction zero at order zero. -/
theorem Q_descent_iterate (u : State) (hu : u ∈ relativeStates) (hQ : Q u = 0) (k : ℕ) :
    Q ((E ^ k) (b 1 (b (-1) u))) =
      (E ^ (k + 1)) (b (-1) u) - T ((E ^ k) (b 1 u)) +
        ((k : ℂ) * ((k : ℂ) + 1)) • (E ^ (k - 1)) (b 1 u) := by
  change b 0 u = 0 ∧ L₀ u = 0 at hu
  rw [Q_E_pow, Q_double_antighost u hu.1 hQ, map_sub, pow_succ, Module.End.mul_apply]
  cases k with
  | zero => simp only [pow_zero, Module.End.one_apply, Nat.cast_zero, zero_mul, zero_smul, add_zero]
  | succ k =>
      rw [show k.succ - 1 = k by omega, Nat.cast_succ, E_pow_T _ (antighost_energy u hu.2)]
      rw [show (k : ℂ) + 1 + 1 = (k : ℂ) + 2 by ring]
      abel

private abbrev modeValue (s : State) (n : ℤ) (v : State) : State := ((Y s)[[n]]) v

private def modeValueMap (n : ℤ) (v : State) : Module.End ℂ State :=
  (LinearMap.applyₗ (R := ℂ) v).comp ((LinearMap.proj n).comp (VertexOperator.ncoeff.comp Y))

private theorem minus_two_weight (i : ℕ) :
    (-1 : ℂ) ^ i * integerBinomial (-2) i = (i : ℂ) + 1 := by
  have h : integerBinomial (-2) i = (-1 : ℂ) ^ i * ((i : ℂ) + 1) := by
    unfold integerBinomial
    rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, Ring.choose_neg,
      show (2 : ℤ) + i - 1 = ((i + 1 : ℕ) : ℤ) by omega,
      Ring.choose_natCast, Nat.choose_succ_self_right]
    simp only [Units.smul_def, smul_eq_mul, Int.cast_mul, Int.cast_negOnePow_natCast,
      Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_natCast, Int.cast_one]
  have hSquare : (-1 : ℂ) ^ i * (-1 : ℂ) ^ i = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [h, ← mul_assoc, hSquare, one_mul]

private theorem T_negative_mode (s v : State) (k : ℕ) :
    modeValue (T s) (-(k : ℤ) - 1) v =
      ((k : ℂ) + 1) • modeValue s (-(k : ℤ) - 2) v := by
  apply of_parity_eigenspaces (fun a =>
    modeValue (T a) (-(k : ℤ) - 1) v =
      ((k : ℂ) + 1) • modeValue a (-(k : ℤ) - 2) v) _ _ s
  · intro a c ha hc
    let A := modeValueMap (-(k : ℤ) - 1) v
    let B := modeValueMap (-(k : ℤ) - 2) v
    change A (T a) = ((k : ℂ) + 1) • B a at ha
    change A (T c) = ((k : ℂ) + 1) • B c at hc
    change A (T (a + c)) = ((k : ℂ) + 1) • B (a + c)
    rw [(T : Module.End ℂ State).map_add, A.map_add, B.map_add, ha, hc, smul_add]
  · intro a p ha
    have h := residueClosure a vacuum p 0 ha parity_vacuum (-2)
    rw [translation_creation, Y_vacuum] at h
    change ((Y (T a))[[-(k : ℤ) - 1]]) v =
      ((k : ℂ) + 1) • ((Y a)[[-(k : ℤ) - 2]]) v
    rw [← translation_eq_total_mode, h, (residueField _ _ _ _).coefficient, residueCoefficient]
    have hRight : residueRight (-2) (-(k : ℤ) - 1) (Y a) FieldNormalProduct.identityField v =
        0 := by
      unfold residueRight
      apply finsum_eq_zero_of_forall_eq_zero
      intro i
      simp only [identity_ncoeff, ite_eq_right (show (-2 : ℤ) + (-(k : ℤ) - 1) - i ≠ -1 by omega),
        LinearMap.zero_apply, smul_zero]
    rw [hRight, smul_zero, sub_zero]
    unfold residueLeft
    rw [finsum_eq_single _ k]
    · simp only [identity_ncoeff, show -(k : ℤ) - 1 + (k : ℤ) = -1 by omega,
        ite_true, LinearMap.id_apply, minus_two_weight,
        show (-2 : ℤ) - (k : ℤ) = -(k : ℤ) - 2 by omega]
    · intro i hi
      simp only [identity_ncoeff, ite_eq_right (show -(k : ℤ) - 1 + (i : ℤ) ≠ -1 by omega),
        LinearMap.zero_apply, map_zero, smul_zero]

private theorem parity_total (m : ℤ) (s : State) :
    parity (VirasoroBRST.Ltotal matterDatum m s) =
      VirasoroBRST.Ltotal matterDatum m (parity s) := by
  have parity_Q (x : State) : parity (Q x) = -Q (parity x) := by
    rw [Q_parity, neg_neg]
  rw [← ward m s, ← ward m (parity s), map_add]
  simp only [parity_Q, b_parity, map_neg, neg_neg]

private theorem parity_homotopy_iterate (u : State) (hu : parity u = -u) (k : ℕ) :
    parity ((E ^ k) (b 1 (b (-1) u))) = -(E ^ k) (b 1 (b (-1) u)) := by
  induction k with
  | zero =>
      simp only [pow_zero, Module.End.one_apply, b_parity, hu, map_neg, neg_neg]
  | succ k ih =>
      simp only [pow_succ', Module.End.mul_apply, parity_total, ih, map_neg]

private theorem omega_even : parity OmegaTotal = (-1 : ℂ) ^ 0 • OmegaTotal := by
  have hMode : ((Y OmegaTotal)[[-1]]) = VirasoroBRST.Ltotal matterDatum (-2) := by
    simpa only [show (-2 : ℤ) + 1 = -1 by norm_num] using conformal_modes (-2)
  have h := stateField_creation OmegaTotal
  rw [hMode] at h
  have hVac : parity vacuum = vacuum := by
    simpa only [pow_zero, one_smul] using parity_vacuum
  rw [pow_zero, one_smul, ← h, parity_total (-2) vacuum, hVac]

private theorem T_shifted_negative_mode (s v : State) (k : ℕ) :
    modeValue (T s) (1 + (-(k : ℤ) - 1)) v = (k : ℂ) • modeValue s (-(k : ℤ) - 1) v := by
  cases k with
  | zero =>
      rw [show (1 : ℤ) + (-((0 : ℕ) : ℤ) - 1) = 0 by norm_num,
        Nat.cast_zero, zero_smul, ← translation_eq_total_mode]
      exact translation_zero_mode s v
  | succ k =>
      rw [show 1 + (-(k.succ : ℤ) - 1) = -(k : ℤ) - 1 by omega,
        show -(k.succ : ℤ) - 1 = -(k : ℤ) - 2 by omega, Nat.cast_succ]
      exact T_negative_mode s v k

private theorem L0_negative_mode (s v : State) (k : ℕ) (hs : parity s = -s) :
    L₀ (modeValue s (-(k : ℤ) - 1) v) =
      modeValue (L₀ s) (-(k : ℤ) - 1) v +
      (k : ℂ) • modeValue s (-(k : ℤ) - 1) v +
      modeValue s (-(k : ℤ) - 1) (L₀ v) := by
  let n : ℤ := -(k : ℤ) - 1
  have h := (homogeneous_borcherds OmegaTotal s v 0 1 omega_even
    (by simpa only [pow_one, neg_one_smul] using hs) 1 n 0).2.2.2
  dsimp only at h
  simp only [one_binomial_sum, signed_zero_binomial_sum, Nat.cast_zero, Nat.cast_one,
    zero_add, add_zero, sub_zero, epsilon, zpow_zero, pow_zero,
    mul_one, one_smul, show 1 + n - 1 = n by omega] at h
  have hMode : ((Y OmegaTotal)[[1]]) = L₀ := by
    simpa only [zero_add] using conformal_modes 0
  rw [hMode, ← translation_eq_conformal_ncoeff, translation_eq_total_mode] at h
  change modeValue (T s) (1 + n) v + modeValue (L₀ s) n v =
    L₀ (modeValue s n v) - modeValue s n (L₀ v) at h
  rw [T_shifted_negative_mode s v k, add_comm ((k : ℂ) • modeValue s n v)] at h
  exact (eq_sub_iff_add_eq.mp h).symm

private theorem homotopy_iterate_antighosts (u : State) (hu : b 0 u = 0) (k : ℕ) :
    b 1 ((E ^ k) (b 1 (b (-1) u))) = 0 ∧
      b 0 ((E ^ k) (b 1 (b (-1) u))) = 0 ∧
      b (-1) ((E ^ k) (b 1 (b (-1) u))) = 0 := by
  induction k with
  | zero =>
      simp only [pow_zero, Module.End.one_apply]
      have ha : b 0 (b (-1) u) = 0 := by
        simpa only [hu, map_zero, add_zero] using b_car 0 (-1) u
      exact ⟨b_square 1 (b (-1) u),
        by simpa only [ha, map_zero, add_zero] using b_car 0 1 (b (-1) u),
        by simpa only [b_square, map_zero, add_zero] using b_car (-1) 1 (b (-1) u)⟩
  | succ k ih =>
      let s : State := (E ^ k) (b 1 (b (-1) u))
      change b 1 s = 0 ∧ b 0 s = 0 ∧ b (-1) s = 0 at ih
      rw [pow_succ', Module.End.mul_apply]
      have kill (r : ℤ) (hr : b r s = 0) (hc : ((1 - r : ℤ) : ℂ) • b (1 + r) s = 0) :
          b r (E s) = 0 := by
        have h := total_b 1 r s
        rw [hr, hc, map_zero, zero_sub, neg_eq_zero] at h
        exact h
      exact ⟨kill 1 ih.1 (by simp only [sub_self, Int.cast_zero, zero_smul]),
        kill 0 ih.2.1 (by simp only [add_zero, ih.1, smul_zero]),
        kill (-1) ih.2.2 (by
          simp only [show (1 : ℤ) + -1 = 0 by norm_num, ih.2.1, smul_zero])⟩

private theorem homotopy_iterate_energy (u : State) (hu : L₀ u = 0) (k : ℕ) :
    L₀ ((E ^ k) (b 1 (b (-1) u))) = -(k : ℂ) • (E ^ k) (b 1 (b (-1) u)) := by
  have ha : L₀ (b (-1) u) = b (-1) u := by
    simpa only [hu, map_zero, sub_zero, zero_sub, zero_add, neg_neg, Int.cast_one, one_smul]
      using total_b 0 (-1) u
  have hτ : L₀ (b 1 (b (-1) u)) = (0 : ℂ) • b 1 (b (-1) u) := by
    have h := sub_eq_iff_eq_add.mp (total_b 0 1 (b (-1) u))
    simpa only [ha, zero_sub, zero_add, Int.cast_neg, Int.cast_one, neg_one_smul,
      neg_add_cancel, add_neg_cancel, zero_smul] using h
  have h := E_pow_energy (b 1 (b (-1) u)) 0 (by simpa only [Int.cast_zero] using hτ) k
  simpa only [Int.cast_zero, zero_sub] using h

private theorem inv_factorial_succ_mul (k : ℕ) :
    (((k + 1).factorial : ℂ)⁻¹) * ((k : ℂ) + 1) = (k.factorial : ℂ)⁻¹ := by
  have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hs : (k : ℂ) + 1 ≠ 0 := by
    rw [← Nat.cast_succ]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp [hk, hs]

private def homotopyTerm (u v : State) (k : ℕ) : State :=
  ((k + 1).factorial : ℂ)⁻¹ • modeValue ((E ^ k) (b 1 (b (-1) u))) (-(k : ℤ) - 1) v

private def correctionTerm (u v : State) (k : ℕ) : State :=
  ((k + 1).factorial : ℂ)⁻¹ • modeValue ((E ^ (k + 1)) (b (-1) u)) (-(k : ℤ) - 1) v

private def tailTerm (u v : State) (k : ℕ) : State :=
  (k.factorial : ℂ)⁻¹ • modeValue ((E ^ k) (b 1 u)) (-(k : ℤ) - 2) v

/-- The first `N` positive-order terms of the weight-one descent adjoint formula. -/
def descentAdjointCorrection (N : ℕ) (u v : State) : State :=
  ∑ k ∈ Finset.range N, correctionTerm u v k

/-- The finite BRST primitive obtained from the two antighosts. -/
def descentAdjointHomotopy (N : ℕ) (u v : State) : State :=
  ∑ k ∈ Finset.range N, homotopyTerm u v k

/-- Every partial homotopy sum is a relative state on relative inputs with odd source. -/
theorem descentAdjointHomotopy_mem_relativeStates (u v : State) (hu : u ∈ relativeStates)
    (hp : parity u = -u) (hv : v ∈ relativeStates) (N : ℕ) :
    descentAdjointHomotopy N u v ∈ relativeStates := by
  change b 0 u = 0 ∧ L₀ u = 0 at hu
  change b 0 v = 0 ∧ L₀ v = 0 at hv
  unfold descentAdjointHomotopy
  apply Submodule.sum_mem
  intro k _
  unfold homotopyTerm
  apply Submodule.smul_mem
  let s : State := (E ^ k) (b 1 (b (-1) u))
  let n : ℤ := -(k : ℤ) - 1
  change b 0 (modeValue s n v) = 0 ∧ L₀ (modeValue s n v) = 0
  have hb := homotopy_iterate_antighosts u hu.1 k
  change b 1 s = 0 ∧ b 0 s = 0 ∧ b (-1) s = 0 at hb
  have he := homotopy_iterate_energy u hu.2 k
  change L₀ s = -(k : ℂ) • s at he
  constructor
  · dsimp only [modeValue]
    rw [b_zero_mode, hb.2.1, hb.2.2, hv.1]
    simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply, add_zero]
  · have h := L0_negative_mode s v k (parity_homotopy_iterate u hp k)
    change L₀ (modeValue s n v) =
      modeValueMap n v (L₀ s) + (k : ℂ) • modeValue s n v + ((Y s)[[n]]) (L₀ v) at h
    rw [he, hv.2, (modeValueMap n v).map_smul, ((Y s)[[n]]).map_zero] at h
    change L₀ (modeValue s n v) =
      -(k : ℂ) • modeValue s n v + (k : ℂ) • modeValue s n v + 0 at h
    simpa only [neg_smul, neg_add_cancel, add_zero] using h

private theorem Q_homotopy_term (u v : State) (hu : u ∈ relativeStates) (hQ : Q u = 0)
    (hp : parity u = -u) (k : ℕ) :
    Q (homotopyTerm u v k) + homotopyTerm u (Q v) k =
      correctionTerm u v k - tailTerm u v k + (if k = 0 then 0 else tailTerm u v (k - 1)) := by
  calc
    _ = ((k + 1).factorial : ℂ)⁻¹ •
        modeValue (Q ((E ^ k) (b 1 (b (-1) u)))) (-(k : ℤ) - 1) v := by
      simp only [homotopyTerm, modeValue, map_smul, Q_mode, parity_homotopy_iterate u hp k,
        map_neg, Pi.neg_apply, LinearMap.neg_apply, smul_add, smul_neg]
      abel
    _ = _ := by
      have hCoeff : ((k + 1).factorial : ℂ)⁻¹ * ((k : ℂ) * ((k : ℂ) + 1)) =
          (k.factorial : ℂ)⁻¹ * (k : ℂ) := by
        calc
          _ = (((k + 1).factorial : ℂ)⁻¹ * ((k : ℂ) + 1)) * (k : ℂ) := by ring
          _ = _ := by rw [inv_factorial_succ_mul]
      have hPrev : ((k.factorial : ℂ)⁻¹ * (k : ℂ)) •
          modeValue ((E ^ (k - 1)) (b 1 u)) (-(k : ℤ) - 1) v =
          if k = 0 then 0 else tailTerm u v (k - 1) := by
        cases k with
        | zero => simp only [Nat.cast_zero, mul_zero, zero_smul, ite_true]
        | succ k =>
            rw [ite_eq_right (Nat.succ_ne_zero k), show k.succ - 1 = k by omega, Nat.cast_succ,
              inv_factorial_succ_mul]
            unfold tailTerm
            rw [show -(k.succ : ℤ) - 1 = -(k : ℤ) - 2 by omega]
      let A := modeValueMap (-(k : ℤ) - 1) v
      change ((k + 1).factorial : ℂ)⁻¹ • A (Q ((E ^ k) (b 1 (b (-1) u)))) = _
      rw [Q_descent_iterate u hu hQ k, A.map_add, A.map_sub, A.map_smul]
      change ((k + 1).factorial : ℂ)⁻¹ •
        (modeValue ((E ^ (k + 1)) (b (-1) u)) (-(k : ℤ) - 1) v -
          modeValue (T ((E ^ k) (b 1 u))) (-(k : ℤ) - 1) v +
          ((k : ℂ) * ((k : ℂ) + 1)) • modeValue ((E ^ (k - 1)) (b 1 u)) (-(k : ℤ) - 1) v) = _
      rw [T_negative_mode]
      simp only [smul_add, smul_sub, smul_smul, inv_factorial_succ_mul, hCoeff]
      change correctionTerm u v k - tailTerm u v k +
        ((k.factorial : ℂ)⁻¹ * (k : ℂ)) • modeValue ((E ^ (k - 1)) (b 1 u)) (-(k : ℤ) - 1) v = _
      rw [hPrev]

/-- The finite sum telescopes to one terminal mode of `E^N b(1) u`. -/
private theorem Q_homotopy_sum (u v : State) (hu : u ∈ relativeStates) (hQ : Q u = 0)
    (hp : parity u = -u) (N : ℕ) :
    Q (descentAdjointHomotopy (N + 1) u v) + descentAdjointHomotopy (N + 1) u (Q v) =
      descentAdjointCorrection (N + 1) u v - tailTerm u v N := by
  induction N with
  | zero =>
      change Q (∑ k ∈ Finset.range 1, homotopyTerm u v k) +
        (∑ k ∈ Finset.range 1, homotopyTerm u (Q v) k) =
        (∑ k ∈ Finset.range 1, correctionTerm u v k) - tailTerm u v 0
      simpa only [Finset.sum_range_one, ite_true, add_zero] using Q_homotopy_term u v hu hQ hp 0
  | succ N ih =>
      have h := Q_homotopy_term u v hu hQ hp (N + 1)
      rw [ite_eq_right (Nat.succ_ne_zero N), show N + 1 - 1 = N by omega] at h
      have hH (w : State) : descentAdjointHomotopy (N + 1 + 1) u w =
          descentAdjointHomotopy (N + 1) u w + homotopyTerm u w (N + 1) :=
        Finset.sum_range_succ _ _
      have hC : descentAdjointCorrection (N + 1 + 1) u v =
          descentAdjointCorrection (N + 1) u v + correctionTerm u v (N + 1) :=
        Finset.sum_range_succ _ _
      rw [hH v, hH (Q v), hC, map_add]
      calc
        _ = (Q (descentAdjointHomotopy (N + 1) u v) + descentAdjointHomotopy (N + 1) u (Q v)) +
            (Q (homotopyTerm u v (N + 1)) + homotopyTerm u (Q v) (N + 1)) := by abel
        _ = _ := by rw [ih, h]; abel

/-- After the terminal mode vanishes the positive corrections are a BRST
anticommutator on the actual state space. -/
theorem Q_descentAdjointHomotopy (u v : State) (hu : u ∈ relativeStates) (hQ : Q u = 0)
    (hp : parity u = -u) (N : ℕ) (hN : (E ^ N) (b 1 u) = 0) :
    Q (descentAdjointHomotopy (N + 1) u v) + descentAdjointHomotopy (N + 1) u (Q v) =
      descentAdjointCorrection (N + 1) u v := by
  simpa only [tailTerm, hN, modeValue, map_zero, Pi.zero_apply, LinearMap.zero_apply,
    smul_zero, sub_zero] using Q_homotopy_sum u v hu hQ hp N

private theorem power_zero_above {s : State} {m n : ℕ}
    (hm : (E ^ m) s = 0) (hmn : m ≤ n) : (E ^ n) s = 0 := by
  rw [← Nat.sub_add_cancel hmn, pow_add, Module.End.mul_apply, hm, map_zero]

/-- Local nilpotence gives a common cutoff for the full correction and primitive
sums, at which the correction on a closed target is an explicit BRST boundary. -/
theorem descentAdjointCorrection_exact (u v : State) (hu : u ∈ relativeStates)
    (hQu : Q u = 0) (hp : parity u = -u) (hv : v ∈ relativeStates) (hQv : Q v = 0) :
    ∃ N : ℕ, (E ^ (N + 2)) (b (-1) u) = 0 ∧ (E ^ (N + 1)) (b 1 (b (-1) u)) = 0 ∧
      (E ^ N) (b 1 u) = 0 ∧ descentAdjointHomotopy (N + 1) u v ∈ relativeStates ∧
      Q (descentAdjointHomotopy (N + 1) u v) = descentAdjointCorrection (N + 1) u v := by
  obtain ⟨A, hA⟩ := totalL1_locally_nilpotent (b (-1) u)
  obtain ⟨B, hB⟩ := totalL1_locally_nilpotent (b 1 (b (-1) u))
  obtain ⟨C, hC⟩ := totalL1_locally_nilpotent (b 1 u)
  let N := A + B + C
  have hAN : A ≤ N + 2 := by dsimp only [N]; omega
  have hBN : B ≤ N + 1 := by dsimp only [N]; omega
  have hCN : C ≤ N := by dsimp only [N]; omega
  have hN : (E ^ N) (b 1 u) = 0 := power_zero_above hC hCN
  refine ⟨N, power_zero_above hA hAN, power_zero_above hB hBN, hN,
    descentAdjointHomotopy_mem_relativeStates u v hu hp hv (N + 1), ?_⟩
  have h := Q_descentAdjointHomotopy u v hu hQu hp N hN
  simpa only [hQv, descentAdjointHomotopy, homotopyTerm, modeValue, map_zero, smul_zero,
    Finset.sum_const_zero, add_zero] using h

#print axioms Q_descent_iterate
#print axioms descentAdjointHomotopy_mem_relativeStates
#print axioms Q_descentAdjointHomotopy
#print axioms descentAdjointCorrection_exact

end
end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTDescentAdjointHomotopy
