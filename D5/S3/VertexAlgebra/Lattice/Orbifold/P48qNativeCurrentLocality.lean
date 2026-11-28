/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeCurrentLocality
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transport current locality between residue strips and the threefold cover. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeNegativeCurrentIterate
import D5.S3.VertexAlgebra.SignedFields.SignedFieldResidueLocality

/-! Locality transport between the order-three cover and the integral coordinate. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentLocality

open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qThirdTwistedField (Cartan State)
open P48qAllJetWickField (NativeStates nativeField)
open NativeStandardThirdLift (standardLift)
open P48qNativeMonodromy (nativeField_monodromy)
open P48qTwistedGeneratorVacuum (rotateCover_coeff)
open FieldNormalProductLocality (delta)
local notation "fieldComm" => FieldNormalProductLocality.commutator

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "σ" => standardLift lattice g g_cube g_isometry

abbrev Field := VertexOperator ℂ State

/-- The Laurent exponents of the cover field are supported on the class of s. -/
def InResidue (s : ℤ) (A : Field) : Prop :=
  ∀ k : ℤ, k % 3 ≠ s % 3 → HVertexOperator.coeff A k = 0

/-- The actual field of a lift eigenstate has the residue forced by monodromy. -/
theorem nativeField_inResidue (v : NativeStates) (s : ℤ) (hv : σ v = ζ ^ s • v) :
    InResidue s (nativeField v) := by
  intro k hk
  have hz : IsPrimitiveRoot ζ 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive
  have hne : ζ ^ k ≠ ζ ^ s := by
    intro h
    have hpow : ζ ^ (k - s) = 1 := by
      rw [zpow_sub₀ (Units.ne_zero ThirdTwistedChargeCocycle.zeta), h,
        div_self (zpow_ne_zero _ (Units.ne_zero ThirdTwistedChargeCocycle.zeta))]
    obtain ⟨j, hj⟩ := (hz.zpow_eq_one_iff_dvd (k - s)).mp hpow
    exact hk (by norm_num at hj; omega)
  have h := congrArg (fun A : Field => HVertexOperator.coeff A k) (nativeField_monodromy v)
  simp only [hv, map_smul, Pi.smul_apply, rotateCover_coeff] at h
  exact (smul_eq_zero.mp (show (ζ ^ k - ζ ^ s) • HVertexOperator.coeff (nativeField v) k = 0 by
    rw [sub_smul, h, sub_self])).resolve_left (sub_ne_zero.mpr hne)

/-- Write the class s of a cover field as a Laurent field in the coordinate x³. -/
def stripResidue (s : ℤ) (A : Field) : Field :=
  VertexOperator.of_coeff (fun k => HVertexOperator.coeff A (3 * k + s)) (by
    intro w
    refine ⟨min 0 (((HahnModule.of ℂ).symm (A w)).order - s), ?_⟩
    intro k hk
    by_contra! h
    exact hk (VertexOperator.coeff_eq_zero_of_lt_order A _ w (by omega)))

@[simp]
theorem stripResidue_coeff (s : ℤ) (A : Field) (k : ℤ) :
    HVertexOperator.coeff (stripResidue s A) k = HVertexOperator.coeff A (3 * k + s) := rfl

/-- Read the integral field on the cover and multiply by the cover monomial x^s. -/
def restoreResidue (s : ℤ) (A : Field) : Field :=
  VertexOperator.of_coeff
    (fun k => if k % 3 = s % 3 then HVertexOperator.coeff A ((k - s) / 3) else 0) (by
      intro w
      refine ⟨3 * ((HahnModule.of ℂ).symm (A w)).order + s, ?_⟩
      intro k hk
      by_contra! h
      apply hk
      change (if k % 3 = s % 3 then HVertexOperator.coeff A ((k - s) / 3)
        else (0 : Module.End ℂ State)) w = 0
      split
      · exact VertexOperator.coeff_eq_zero_of_lt_order A _ w (by omega)
      · rfl)

@[simp]
theorem restoreResidue_coeff (s : ℤ) (A : Field) (k : ℤ) :
    HVertexOperator.coeff (restoreResidue s A) k =
      if k % 3 = s % 3 then HVertexOperator.coeff A ((k - s) / 3) else 0 := rfl

theorem restoreResidue_stripResidue (s : ℤ) (A : Field) (hA : InResidue s A) :
    restoreResidue s (stripResidue s A) = A := by
  apply HVertexOperator.coeff_inj
  funext k
  rw [restoreResidue_coeff]
  split
  · rw [stripResidue_coeff, show 3 * ((k - s) / 3) + s = k by omega]
  · exact (hA k ‹_›).symm

private abbrev Distribution := ℤ → ℤ → Module.End ℂ State

/-- Multiplication by x³-y³ on Laurent cover coefficients. -/
def coverDelta (F : Distribution) : Distribution :=
  fun k l => F (k - 3) l - F k (l - 3)

/-- The coefficient commutator in Laurent cover exponents. -/
def coverComm (A B : Field) : Distribution :=
  fun k l => ⁅HVertexOperator.coeff A k, HVertexOperator.coeff B l⁆

/-- Locality with respect to the physical difference x³-y³. -/
def CoverLocal (A B : Field) : Prop :=
  ∃ N : ℕ, coverDelta^[N] (coverComm A B) = 0

private theorem delta_strip (s t : ℤ) (F : Distribution) (N : ℕ) (i j : ℤ) :
    (delta^[N] (fun m n => F (s - 3 * (m + 1)) (t - 3 * (n + 1)))) i j =
      (coverDelta^[N] F) (s - 3 * (i + 1)) (t - 3 * (j + 1)) := by
  induction N generalizing i j with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', delta, coverDelta, ih, ih]
    rw [show s - 3 * (i + 1 + 1) = s - 3 * (i + 1) - 3 by omega,
      show t - 3 * (j + 1 + 1) = t - 3 * (j + 1) - 3 by omega]

private theorem coverComm_strip (s t : ℤ) (A B : Field) :
    fieldComm (stripResidue s A) (stripResidue t B) =
      fun i j => coverComm A B (s - 3 * (i + 1)) (t - 3 * (j + 1)) := by
  funext i j
  rw [FieldNormalProductLocality.commutator, VertexOperator.ncoeff_apply,
    VertexOperator.ncoeff_apply,
    stripResidue_coeff, stripResidue_coeff, coverComm, LieRing.of_associative_ring_bracket,
    show 3 * (-i - 1) + s = s - 3 * (i + 1) by omega,
    show 3 * (-j - 1) + t = t - 3 * (j + 1) by omega]

private theorem coverDelta_offResidue (s t : ℤ) (A B : Field)
    (hA : InResidue s A) (hB : InResidue t B) (N : ℕ) (k l : ℤ)
    (h : k % 3 ≠ s % 3 ∨ l % 3 ≠ t % 3) : coverDelta^[N] (coverComm A B) k l = 0 := by
  induction N generalizing k l with
  | zero =>
    change coverComm A B k l = 0
    rcases h with h | h
    · simp [coverComm, hA k h, LieRing.of_associative_ring_bracket]
    · simp [coverComm, hB l h, LieRing.of_associative_ring_bracket]
  | succ N ih =>
    rw [Function.iterate_succ_apply', coverDelta, ih, ih, sub_self]
    · simpa only [show (l - 3) % 3 = l % 3 by omega] using h
    · simpa only [show (k - 3) % 3 = k % 3 by omega] using h

/-- Test physical locality in integral coordinates on the two occupied residue
classes. The locality order is preserved in both directions. -/
theorem coverDelta_comm_eq_zero_iff (s t : ℤ) (A B : Field)
    (hA : InResidue s A) (hB : InResidue t B) (N : ℕ) :
    coverDelta^[N] (coverComm A B) = 0 ↔
      delta^[N] (fieldComm (stripResidue s A) (stripResidue t B)) = 0 := by
  rw [coverComm_strip]
  constructor
  · intro h
    funext i j
    rw [delta_strip, h]
    rfl
  · intro h
    funext k l
    by_cases hk : k % 3 = s % 3
    · by_cases hl : l % 3 = t % 3
      · have he := congrFun (congrFun h (-((k - s) / 3) - 1)) (-((l - t) / 3) - 1)
        rw [delta_strip, show s - 3 * (-((k - s) / 3) - 1 + 1) = k by omega,
          show t - 3 * (-((l - t) / 3) - 1 + 1) = l by omega] at he
        exact he
      · exact coverDelta_offResidue s t A B hA hB N k l (Or.inr hl)
    · exact coverDelta_offResidue s t A B hA hB N k l (Or.inl hk)

#print axioms nativeField_inResidue
#print axioms restoreResidue_stripResidue
#print axioms coverDelta_comm_eq_zero_iff

private def deltaCoverEnd : Module.End ℂ Distribution where
  toFun := coverDelta
  map_add' F G := by
    funext k l
    simp only [coverDelta, Pi.add_apply]
    abel
  map_smul' c F := by
    funext k l
    simp only [coverDelta, Pi.smul_apply, smul_sub, RingHom.id_apply]

private def coeffComm (C : Field) : (ℤ → Module.End ℂ State) →ₗ[ℂ] Distribution where
  toFun F k l := ⁅F k, HVertexOperator.coeff C l⁆
  map_add' F G := by
    funext k l
    change ⁅F k + G k, HVertexOperator.coeff C l⁆ = _
    simp only [LieRing.of_associative_ring_bracket, add_mul, mul_add, Pi.add_apply]
    abel
  map_smul' c F := by
    funext k l
    change ⁅c • F k, HVertexOperator.coeff C l⁆ = c • ⁅F k, HVertexOperator.coeff C l⁆
    simp only [LieRing.of_associative_ring_bracket, smul_mul_assoc, mul_smul_comm, smul_sub]

private theorem coverOrder_mono {F : Distribution} {a b : ℕ} (hab : a ≤ b)
    (h : (deltaCoverEnd ^ a) F = 0) : (deltaCoverEnd ^ b) F = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [add_comm, pow_add, Module.End.mul_apply, h, map_zero]

private def localCoefficients (C : Field) : Submodule ℂ (ℤ → Module.End ℂ State) where
  carrier := {F | ∃ N : ℕ, (deltaCoverEnd ^ N) (coeffComm C F) = 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro F G ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨max a b, ?_⟩
    rw [map_add, map_add, coverOrder_mono (le_max_left _ _) ha,
      coverOrder_mono (le_max_right _ _) hb, add_zero]
  smul_mem' := by
    rintro c F ⟨n, hn⟩
    exact ⟨n, by rw [map_smul, map_smul, hn, smul_zero]⟩

private theorem coverLocal_iff (A C : Field) :
    CoverLocal A C ↔ HVertexOperator.coeff A ∈ localCoefficients C := by
  change (∃ N : ℕ, coverDelta^[N] (coverComm A C) = 0) ↔
    ∃ N : ℕ, (deltaCoverEnd ^ N) (coeffComm C (HVertexOperator.coeff A)) = 0
  simp only [Module.End.pow_apply]
  rfl

private theorem localCoefficients_shift (C : Field) (F : ℤ → Module.End ℂ State) (a : ℤ)
    (h : F ∈ localCoefficients C) : (fun k => F (k + a)) ∈ localCoefficients C := by
  obtain ⟨N, hN⟩ := h
  have commute (D : Distribution) (n : ℕ) (k l : ℤ) :
      (coverDelta^[n] (fun i j => D (i + a) j)) k l = (coverDelta^[n] D) (k + a) l := by
    induction n generalizing k l with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', coverDelta, coverDelta,
        ih, ih, show (k - 3) + a = (k + a) - 3 by omega]
  refine ⟨N, ?_⟩
  funext k l
  rw [Module.End.pow_apply] at hN ⊢
  change (coverDelta^[N] (fun i j => coeffComm C F (i + a) j)) k l = 0
  rw [commute]
  exact congrFun (congrFun hN (k + a)) l

private theorem restoreResidue_inResidue (s : ℤ) (A : Field) :
    InResidue s (restoreResidue s A) := by
  intro k hk
  simp only [restoreResidue_coeff, ite_eq_right hk]

@[simp] theorem stripResidue_restoreResidue (s : ℤ) (A : Field) :
    stripResidue s (restoreResidue s A) = A := by
  apply HVertexOperator.coeff_inj
  funext k
  rw [stripResidue_coeff, restoreResidue_coeff, ite_eq_left (by omega),
    show (3 * k + s - s) / 3 = k by omega]

private theorem strip_local (s t : ℤ) (A C : Field) (h : CoverLocal A C) :
    ∃ N : ℕ, delta^[N] (fieldComm (stripResidue s A) (stripResidue t C)) = 0 := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  rw [coverComm_strip]
  funext i j
  rw [delta_strip, hN]
  rfl

private theorem restore_local (s t : ℤ) (A C : Field) (hc : InResidue t C)
    (h : ∃ N : ℕ, delta^[N] (fieldComm A (stripResidue t C)) = 0) :
    CoverLocal (restoreResidue s A) C := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, (coverDelta_comm_eq_zero_iff s t _ C (restoreResidue_inResidue s A) hc N).mpr ?_⟩
  simpa only [stripResidue_restoreResidue] using hN

open LatticeAllStateReconstruction (mu)
open LatticeSugawaraCurrents (vectorFrequencyBound)
open ThirdTwistedIterate (currentAlong)
open ThirdEigenspacePairing (p48qAction)
open P48qTwistedHeisenberg (mode currentField currentField_coeff mode_projectAt)
open P48qNativeCurrentCommutator (nativeField_current_commutator)
open P48qNativeNegativeCurrentIterate (nativeField_current_negative_iterate regularCollision
  regularGermCoeff signedNormalTaylor)
open private projectAt_on_residue from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCurrentChargedIterate
open private projectAt_off_residue from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField
open private sourceCoeff source_sum_cutoff from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeNegativeCurrentIterate

private theorem strip_current_ncoeff (u : Cartan) (r : ℕ) (i : ℤ) :
    (stripResidue (-(r : ℤ)) (currentField u))[[i]] = mode u (3 * i + r) := by
  rw [VertexOperator.ncoeff_apply, stripResidue_coeff, currentField_coeff,
    show -(3 * (-i - 1) + -(r : ℤ)) - 3 = 3 * i + r by omega]

private def sourceModeCoeff (u : Cartan) (v : NativeStates) (n : ℕ) (k : ℤ) :
    Module.End ℂ State :=
  HVertexOperator.coeff (nativeField (mu lattice (currentAlong lattice u) (n : ℤ) v))
    (k + 3 * (n : ℤ))

private def alignedComm (u : Cartan) (r : ℕ) (v : NativeStates) (k i : ℤ) :
    Module.End ℂ State :=
  ⁅mode u (3 * i + r), HVertexOperator.coeff (nativeField v) (k + (3 * i + r))⁆

private def difference (F : ℤ → Module.End ℂ State) (i : ℤ) : Module.End ℂ State :=
  F (i + 1) - F i

-- At fixed total exponent each forward difference lowers the binomial index by one.
private theorem alignedComm_differences (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (v : NativeStates) (q : ℕ) (k i : ℤ) :
    difference^[q] (alignedComm u r v k) i =
      ∑ n ∈ Finset.range (vectorFrequencyBound lattice v + 1),
        (if q ≤ n then Ring.choose ((i : ℂ) + (r : ℂ) / 3) (n - q) else 0) •
          sourceModeCoeff u v n k := by
  induction q generalizing i with
  | zero =>
    change alignedComm u r v k i = _
    unfold alignedComm
    rw [nativeField_current_commutator, projectAt_on_residue u r hr hu _ (by omega),
      show ((3 * i + (r : ℤ) : ℤ) : ℂ) / 3 = (i : ℂ) + (r : ℂ) / 3 by push_cast; ring]
    have h := source_sum_cutoff u v (k - 3)
      (fun n => Ring.choose ((i : ℂ) + (r : ℂ) / 3) n)
    simp only [zero_le, ite_true, Nat.sub_zero]
    convert h using 2 <;> simp only [sourceModeCoeff, sourceCoeff] <;> try ring_nf
  | succ q ih =>
    rw [Function.iterate_succ_apply', difference, ih, ih, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [← sub_smul]
    congr 1
    by_cases h : q + 1 ≤ n
    · simp only [ite_eq_left h, ite_eq_left (show q ≤ n by omega), Int.cast_add, Int.cast_one,
        show (i : ℂ) + 1 + (r : ℂ) / 3 = ((i : ℂ) + (r : ℂ) / 3) + 1 by ring,
        show n - q = (n - (q + 1)) + 1 by omega]
      rw [Ring.choose_succ_succ, add_sub_cancel_right]
    · by_cases he : q = n
      · simp [← he]
      · simp [h, show ¬q ≤ n by omega]

private theorem delta_alignedComm (u : Cartan) (r : ℕ) (v : NativeStates)
    (s : ℤ) (q : ℕ) (i j : ℤ) :
    delta^[q] (fieldComm (stripResidue (-(r : ℤ)) (currentField u))
      (stripResidue s (nativeField v))) i j =
      difference^[q] (alignedComm u r v (s - r - 3 * (i + j + q + 1))) i := by
  induction q generalizing i j with
  | zero =>
    change fieldComm (stripResidue (-(r : ℤ)) (currentField u))
      (stripResidue s (nativeField v)) i j = _
    rw [FieldNormalProductLocality.commutator, strip_current_ncoeff,
      VertexOperator.ncoeff_apply, stripResidue_coeff, Function.iterate_zero_apply,
      alignedComm, LieRing.of_associative_ring_bracket,
      show s - r - 3 * (i + j + ((0 : ℕ) : ℤ) + 1) + (3 * i + r) = 3 * (-j - 1) + s by omega]
  | succ q ih =>
    rw [Function.iterate_succ_apply', delta, ih, ih, Function.iterate_succ_apply', difference]
    push_cast
    rw [show i + 1 + j + q + 1 = i + j + ((q : ℤ) + 1) + 1 by ring,
      show i + (j + 1) + q + 1 = i + j + ((q : ℤ) + 1) + 1 by ring]

open SignedFieldNormalProductLocality (signedComm)
open SignedFieldResidueLocality (residueField)
open private positiveModes from D5.S3.VertexAlgebra.SignedFields.SignedFieldResidueLocality
open StateFieldResidueReconstruction (deltaEnd_iterate_apply)

private theorem oneComm (F G : Field) : signedComm 1 F G = fieldComm F G := by
  funext i j
  simp [signedComm, FieldNormalProductLocality.commutator]

private theorem ordinary_residue_mode (A B : Field) (q : ℕ) (p : ℤ) :
    ((residueField 1 (q : ℤ) A B).operator)[[p]] = delta^[q] (fieldComm A B) 0 p := by
  apply LinearMap.ext
  intro w
  rw [positiveModes, deltaEnd_iterate_apply, oneComm]


private theorem aligned_difference_local (u : Cartan) (r : ℕ) (v : NativeStates)
    (s t : ℤ) (C : Field) (hv : InResidue s (nativeField v)) (hC : InResidue t C)
    (hAC : CoverLocal (currentField u) C) (hBC : CoverLocal (nativeField v) C)
    (hAB : CoverLocal (currentField u) (nativeField v)) (q : ℕ) :
    (fun k => difference^[q] (alignedComm u r v k) 0) ∈ localCoefficients C := by
  let A := stripResidue (-(r : ℤ)) (currentField u)
  let B := stripResidue s (nativeField v)
  let R := (residueField 1 (q : ℤ) A B).operator
  have hR : CoverLocal (restoreResidue (s - r) R) C := by
    apply restore_local _ t _ _ hC
    simpa only [one_mul, oneComm] using
      SignedFieldResidueLocality.residue_locality 1 1 1 A B (stripResidue t C)
        (by simpa only [oneComm] using strip_local (-(r : ℤ)) t _ _ hAC)
        (by simpa only [oneComm] using strip_local s t _ _ hBC)
        (by simpa only [oneComm] using strip_local (-(r : ℤ)) s _ _ hAB) (q : ℤ)
  have hEq : (fun k => difference^[q] (alignedComm u r v k) 0) =
      fun k => HVertexOperator.coeff (restoreResidue (s - r) R) (k + 3 * (q : ℤ)) := by
    funext k
    rw [restoreResidue_coeff]
    by_cases hk : k % 3 = (s - (r : ℤ)) % 3
    · have hm : (k + 3 * (q : ℤ)) % 3 = (s - (r : ℤ)) % 3 := by omega
      rw [ite_eq_left hm, VertexOperator.coeff_eq_ncoeff, ordinary_residue_mode, delta_alignedComm]
      change difference^[q] (alignedComm u r v k) 0 =
        difference^[q] (alignedComm u r v
          (s - r - 3 * (0 + (-((k + 3 * (q : ℤ) - (s - r)) / 3) - 1) + q + 1))) 0
      rw [show s - (r : ℤ) - 3 * (0 + (-((k + 3 * (q : ℤ) - (s - r)) / 3) - 1) +
          q + 1) = k by omega]
    · have hm : (k + 3 * (q : ℤ)) % 3 ≠ (s - (r : ℤ)) % 3 := by omega
      rw [ite_eq_right hm]
      have hz : alignedComm u r v k = 0 := by
        funext i
        rw [alignedComm, hv _ (by omega)]
        simp [LieRing.of_associative_ring_bracket]
      have hz' (n : ℕ) : difference^[n] (0 : ℤ → Module.End ℂ State) = 0 := by
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [Function.iterate_succ_apply', ih]
          funext i
          exact sub_self _
      rw [hz, hz']
      rfl
  rw [hEq]
  exact localCoefficients_shift C _ _ ((coverLocal_iff _ _).mp hR)

private theorem sourceModeCoeff_local (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (v : NativeStates)
    (s t : ℤ) (C : Field) (hv : InResidue s (nativeField v)) (hC : InResidue t C)
    (hAC : CoverLocal (currentField u) C) (hBC : CoverLocal (nativeField v) C)
    (hAB : CoverLocal (currentField u) (nativeField v))
    (q : ℕ) (hq : q ≤ vectorFrequencyBound lattice v) :
    sourceModeCoeff u v q ∈ localCoefficients C := by
  classical
  let M := vectorFrequencyBound lattice v
  let L := localCoefficients C
  let weight (j n : ℕ) : ℂ := if j ≤ n then Ring.choose ((r : ℂ) / 3) (n - j) else 0
  have recover (gap : ℕ) : ∀ j ≤ M, M - j = gap → sourceModeCoeff u v j ∈ L := by
    induction gap using Nat.strong_induction_on with
    | h gap ih =>
      intro j hj hgap
      let S := Finset.range (M + 1)
      let F (n : ℕ) := weight j n • sourceModeCoeff u v n
      have hJ : j ∈ S := Finset.mem_range.mpr (by omega)
      have tail : (∑ n ∈ S.erase j, F n) ∈ L := by
        apply L.sum_mem
        intro n hn
        have hne := (Finset.mem_erase.mp hn).1
        have hnM : n ≤ M := by simpa [S] using (Finset.mem_erase.mp hn).2
        by_cases hnj : j ≤ n
        · exact L.smul_mem _ (ih (M - n) (by omega) n hnM rfl)
        · simp [F, weight, hnj, L.zero_mem]
      have hsum : (∑ n ∈ S, F n) ∈ L := by
        have hEq : (fun k => difference^[j] (alignedComm u r v k) 0) =
            ∑ n ∈ S, F n := by
          funext k
          simpa only [F, weight, S, M, Finset.sum_apply, Pi.smul_apply, Int.cast_zero, zero_add]
            using alignedComm_differences u r hr hu v j k 0
        rw [← hEq]
        exact aligned_difference_local u r v s t C hv hC hAC hBC hAB j
      rw [← Finset.sum_erase_add _ _ hJ] at hsum
      have hjF : F j = sourceModeCoeff u v j := by
        simp [F, weight]
      rw [hjF] at hsum
      exact (L.add_mem_iff_right tail).mp hsum
  exact recover (M - q) q hq rfl

/-- The nonnegative current products appearing in the actual commutator inherit
locality with the actual comparison field. The cover shift is invertible. -/
theorem native_positiveCurrent_local (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (v w : NativeStates) (s t : ℤ)
    (hv : σ v = ζ ^ s • v) (hw : σ w = ζ ^ t • w)
    (hAC : CoverLocal (currentField u) (nativeField w))
    (hBC : CoverLocal (nativeField v) (nativeField w))
    (hAB : CoverLocal (currentField u) (nativeField v))
    (q : ℕ) (hq : q ≤ vectorFrequencyBound lattice v) :
    CoverLocal (nativeField (mu lattice (currentAlong lattice u) (q : ℤ) v)) (nativeField w) := by
  apply (coverLocal_iff _ _).mpr
  have h := localCoefficients_shift (nativeField w) _ (-3 * (q : ℤ))
    (sourceModeCoeff_local u r hr hu v s t (nativeField w)
      (nativeField_inResidue v s hv) (nativeField_inResidue w t hw) hAC hBC hAB q hq)
  simpa only [sourceModeCoeff, show ∀ k : ℤ, k + -3 * (q : ℤ) + 3 * (q : ℤ) = k by
    intro k; ring] using h

#print axioms native_positiveCurrent_local


open FieldNormalProduct (dividedDerivative normalMinusOne)
open FieldNormalProductLocality (dividedDerivative_locality normalMinusOne_locality)
open P48qSignedNormalWord (insertMode_apply)
open P48qJetNormalOrdering (jetWeight)
open P48qTwistedHeisenberg (modeLinear)
open private signedTaylorTerm from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeNegativeCurrentIterate

private theorem mode_offResidue (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (m : ℤ) (hm : m % 3 ≠ (r : ℤ)) :
    mode u m = 0 := by
  rw [← mode_projectAt, projectAt_off_residue u r hr hu m hm]
  exact (modeLinear m).map_zero

private def normalAt (A B : Field) (p i : ℤ) (w : State) : State :=
  if i < 0 then (A[[i]]) ((B[[p - i - 1]]) w) else (B[[p - i - 1]]) ((A[[i]]) w)

private theorem normalAt_finite (A B : Field) (p : ℤ) (w : State) :
    Function.HasFiniteSupport (fun i => normalAt A B p i w) := by
  let a := ((HahnModule.of ℂ).symm (A w)).order
  let b := ((HahnModule.of ℂ).symm (B w)).order
  refine (Set.finite_Icc (min 0 (b + p)) (max 0 (-a - 1))).subset ?_
  intro i hi
  change min 0 (b + p) ≤ i ∧ i ≤ max 0 (-a - 1)
  constructor
  · by_contra! h
    apply hi
    have hn : i < 0 := h.trans_le (min_le_left _ _)
    have hz : (B[[p - i - 1]]) w = 0 :=
      VertexOperator.ncoeff_eq_zero_of_lt_order _ _ _ (by
        have hh := h.trans_le (min_le_right _ _)
        change - (p - i - 1) - 1 < b
        omega)
    simp only [normalAt, ite_eq_left hn, hz, map_zero]
  · by_contra! h
    apply hi
    have hn : ¬ i < 0 := not_lt_of_ge ((le_max_left _ _).trans h.le)
    have hz : (A[[i]]) w = 0 :=
      VertexOperator.ncoeff_eq_zero_of_lt_order _ _ _ (by
        have hh := (le_max_right _ _).trans_lt h
        change -i - 1 < a
        omega)
    simp only [normalAt, ite_eq_right hn, hz, map_zero]

private theorem normalAt_sum (A B : Field) (p : ℤ) (w : State) :
    ((normalMinusOne A B).val[[p]]) w = ∑ᶠ i, normalAt A B p i w := by
  let f := fun i => normalAt A B p i w
  let fneg : ℕ → ℤ := fun n => -(n : ℤ) - 1
  let fpos : ℕ → ℤ := fun n => (n : ℤ)
  have hneg : Function.Injective fneg := by intro i j h; dsimp [fneg] at h; omega
  have hpos : Function.Injective fpos := by intro i j h; dsimp [fpos] at h; exact_mod_cast h
  have hcover : Set.range fneg ∪ Set.range fpos = Set.univ := by
    ext i
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    by_cases h : i < 0
    · exact Or.inl ⟨(-i - 1).toNat, by dsimp [fneg]; omega⟩
    · exact Or.inr ⟨i.toNat, by dsimp [fpos]; omega⟩
  have hdisjoint : Disjoint (Set.range fneg) (Set.range fpos) := by
    rw [Set.disjoint_left]
    rintro i ⟨n, rfl⟩ ⟨m, h⟩
    dsimp [fneg, fpos] at h
    omega
  have hfinite := normalAt_finite A B p w
  change _ = ∑ᶠ i, f i
  rw [(normalMinusOne _ _).property]
  conv_rhs =>
    rw [← finsum_mem_univ, ← hcover,
      finsum_mem_union' hdisjoint (hfinite.subset Set.inter_subset_right)
        (hfinite.subset Set.inter_subset_right),
      finsum_mem_range hneg, finsum_mem_range hpos]
  congr 1
  apply finsum_congr
  intro n
  simp only [normalAt, fneg, ite_eq_left (show -(n : ℤ) - 1 < 0 by omega),
    show p - (-(n : ℤ) - 1) - 1 = p + n by omega]

private theorem derivative_mode_at (A : Field) (h : ℕ) (i : ℤ) :
    (dividedDerivative h A)[[i + (h : ℤ)]] =
      Ring.choose ((-i - 1 : ℤ) : ℂ) h • A[[i]] := by
  apply LinearMap.ext
  intro w
  change Ring.choose (-(i + (h : ℤ)) - 1 + h) h •
      HVertexOperator.coeff A (-(i + (h : ℤ)) - 1 + h) w = _
  rw [show -(i + (h : ℤ)) - 1 + h = -i - 1 by omega,
    ← VertexOperator.ncoeff_apply, ← Int.cast_smul_eq_zsmul ℂ,
    LinearMap.smul_apply]
  congr 1
  exact Ring.map_choose (Int.castRingHom ℂ) (-i - 1) h

private theorem shifted_normal_term (A B : Field) (p i : ℤ) (h : ℕ) (w : State) :
    normalAt (dividedDerivative h A) B (p + (h : ℤ)) (i + h) w =
      Ring.choose ((-i - 1 : ℤ) : ℂ) h • normalAt A B p i w := by
  simp only [normalAt, derivative_mode_at, show p + (h : ℤ) - (i + h) - 1 = p - i - 1 by ring,
    LinearMap.smul_apply]
  by_cases hi : i < 0
  · by_cases hh : i + (h : ℤ) < 0
    · rw [ite_eq_left hi, ite_eq_left hh]
    · -- A mode that crosses the cutoff has zero Hasse coefficient.
      have hi' : ((-i - 1 : ℤ) : ℂ) = (((-i - 1).toNat : ℕ) : ℂ) := by
        exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ -i - 1 by omega)).symm
      rw [hi', Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
      simp
  · rw [ite_eq_right hi, ite_eq_right (show ¬ i + (h : ℤ) < 0 by omega), map_smul]

private theorem normal_derivative_sum (A B : Field) (p : ℤ) (h : ℕ) (w : State) :
    ((normalMinusOne (dividedDerivative h A) B).val[[p + (h : ℤ)]]) w =
      ∑ᶠ i, Ring.choose ((-i - 1 : ℤ) : ℂ) h • normalAt A B p i w := by
  rw [normalAt_sum]
  symm
  exact finsum_eq_of_bijective (Equiv.addRight (h : ℤ))
    (Equiv.addRight (h : ℤ)).bijective (fun i => (shifted_normal_term A B p i h w).symm)


private def normalPartField (u : Cartan) (r : ℕ) (d : ℕ+) (v : NativeStates)
    (s : ℤ) : Field :=
  let A := stripResidue (-(r : ℤ)) (currentField u)
  let B := stripResidue s (nativeField v)
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal ((d : ℕ) - 1),
    Ring.choose (-(r : ℂ) / 3) ij.2 • restoreResidue (s - r - 3 * (ij.2 : ℤ))
      (normalMinusOne (dividedDerivative ij.1 A) B).val

private theorem signedNormalTaylor_eq (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (d : ℕ+) (v : NativeStates)
    (s : ℤ) (hv : InResidue s (nativeField v)) (k : ℤ) (w : State) :
    signedNormalTaylor u d v k w = HVertexOperator.coeff (normalPartField u r d v s) k w := by
  classical
  let A := stripResidue (-(r : ℤ)) (currentField u)
  let B := stripResidue s (nativeField v)
  let e := (d : ℕ) - 1
  let p := -((k - (s - (r : ℤ))) / 3) - 1
  let f := signedTaylorTerm u d k (HVertexOperator.coeff (nativeField v)) w
  have hoff (m : ℤ) (hm : m % 3 ≠ (r : ℤ)) : f m = 0 := by
    simp [f, signedTaylorTerm, insertMode_apply, mode_offResidue u r hr hu m hm]
  change (∑ᶠ m, f m) = _
  unfold normalPartField
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]
  by_cases hk : k % 3 = (s - (r : ℤ)) % 3
  · have hlift : k = s - (r : ℤ) - 3 * (p + 1) := by dsimp [p]; omega
    let liftMode : ℤ → ℤ := fun i => 3 * i + r
    have hinj : Function.Injective liftMode := by intro i j h; dsimp [liftMode] at h; omega
    have hsupport : Function.support f ⊆ Set.range liftMode := by
      intro m hm
      have hm' : m % 3 = (r : ℤ) := by
        by_contra h
        exact hm (hoff m h)
      exact ⟨(m - r) / 3, by dsimp [liftMode]; omega⟩
    have hsets : Set.range liftMode ∩ Function.support f =
        Set.univ ∩ Function.support f := by
      rw [Set.inter_eq_right.mpr hsupport, Set.univ_inter]
    rw [← finsum_mem_univ, ← finsum_mem_inter_support_eq f _ _ hsets, finsum_mem_range hinj]
    have hterm (i : ℤ) :
        f (liftMode i) =
          Ring.choose (((-i - 1 : ℤ) : ℂ) + (-(r : ℂ) / 3)) e •
            normalAt A B (p - (e : ℤ)) i w := by
      have hB : HVertexOperator.coeff (nativeField v)
          (k + 3 * ((d : ℕ) : ℤ) + liftMode i) = B[[p - (e : ℤ) - i - 1]] := by
        simp only [B, VertexOperator.ncoeff_apply, stripResidue_coeff, liftMode]
        have hd := d.pos
        have he : (e : ℤ) + 1 = ((d : ℕ) : ℤ) := by dsimp [e]; omega
        rw [show k + 3 * ((d : ℕ) : ℤ) + (3 * i + r) =
          3 * (-(p - (e : ℤ) - i - 1) - 1) + s by omega]
      have hchoose : -(liftMode i : ℂ) / 3 - 1 =
          ((-i - 1 : ℤ) : ℂ) + (-(r : ℂ) / 3) := by
        simp only [liftMode]
        push_cast
        ring
      simp only [f, signedTaylorTerm, hB, insertMode_apply, jetWeight, hchoose, normalAt, A,
        strip_current_ncoeff, show liftMode i < 0 ↔ i < 0 by dsimp [liftMode]; omega]
      split <;> rfl
    have hf (ij : ℕ × ℕ) (hij : ij ∈ Finset.HasAntidiagonal.antidiagonal e) :
        HVertexOperator.coeff
          (restoreResidue (s - r - 3 * (ij.2 : ℤ))
            (normalMinusOne (dividedDerivative ij.1 A) B).val) k w =
          ∑ᶠ i, Ring.choose ((-i - 1 : ℤ) : ℂ) ij.1 •
            normalAt A B (p - (e : ℤ)) i w := by
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      rw [restoreResidue_coeff, ite_eq_left (by omega), VertexOperator.coeff_eq_ncoeff]
      rw [show -((k - (s - r - 3 * (ij.2 : ℤ))) / 3) - 1 =
          (p - (e : ℤ)) + (ij.1 : ℤ) by omega]
      exact normal_derivative_sum A B _ _ w
    change (∑ᶠ i, f (liftMode i)) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal e, Ring.choose (-(r : ℂ) / 3) ij.2 • _
    let W (ij : ℕ × ℕ) (i : ℤ) : State :=
      (Ring.choose (-(r : ℂ) / 3) ij.2 * Ring.choose ((-i - 1 : ℤ) : ℂ) ij.1) •
        normalAt A B (p - (e : ℤ)) i w
    have hW (ij : ℕ × ℕ) : Function.HasFiniteSupport (W ij) := by
      refine (normalAt_finite A B (p - (e : ℤ)) w).subset ?_
      intro i hi hz
      exact hi (by simp only [W, hz, smul_zero])
    calc
      _ = ∑ᶠ i, ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal e, W ij i := by
        apply finsum_congr
        intro i
        rw [hterm, Ring.add_choose_eq e (Commute.all _ _), Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro ij _
        simp only [W, mul_comm (Ring.choose (-(r : ℂ) / 3) _)]
      _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal e, ∑ᶠ i, W ij i :=
        (sum_finsum_comm _ _ (fun ij _ => hW ij)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ij hij
        rw [hf ij hij, smul_finsum]
        apply finsum_congr
        intro i
        simp only [W, smul_smul]
  · rw [finsum_eq_zero_of_forall_eq_zero]
    · symm
      apply Finset.sum_eq_zero
      intro ij _
      rw [restoreResidue_coeff, ite_eq_right (by omega), LinearMap.zero_apply, smul_zero]
    · intro m
      by_cases hm : m % 3 = (r : ℤ)
      · have hB := hv (k + 3 * ((d : ℕ) : ℤ) + m) (by omega)
        simp [f, signedTaylorTerm, hB]
      · exact hoff m hm

private theorem normalPart_local (u : Cartan) (r : ℕ) (d : ℕ+) (v : NativeStates)
    (s t : ℤ) (C : Field) (hC : InResidue t C)
    (hAC : CoverLocal (currentField u) C) (hBC : CoverLocal (nativeField v) C)
    (hAB : CoverLocal (currentField u) (nativeField v)) :
    HVertexOperator.coeff (normalPartField u r d v s) ∈ localCoefficients C := by
  let A := stripResidue (-(r : ℤ)) (currentField u)
  let B := stripResidue s (nativeField v)
  let T := stripResidue t C
  obtain ⟨a, ha⟩ := strip_local (-(r : ℤ)) t _ _ hAC
  obtain ⟨b, hb⟩ := strip_local s t _ _ hBC
  obtain ⟨c, hc⟩ := strip_local (-(r : ℤ)) s _ _ hAB
  unfold normalPartField
  rw [map_sum]
  apply (localCoefficients C).sum_mem
  intro ij _
  rw [map_smul]
  apply (localCoefficients C).smul_mem
  apply (coverLocal_iff _ _).mp
  apply restore_local _ t _ _ hC
  exact ⟨_, normalMinusOne_locality (dividedDerivative ij.1 A) B T _ b _
    (dividedDerivative_locality A T a ij.1 ha) hb (dividedDerivative_locality A B c ij.1 hc)⟩

private theorem regularCollision_local (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (d : ℕ+) (v : NativeStates)
    (s t : ℤ) (C : Field) (hv : InResidue s (nativeField v)) (hC : InResidue t C)
    (hAC : CoverLocal (currentField u) C) (hBC : CoverLocal (nativeField v) C)
    (hAB : CoverLocal (currentField u) (nativeField v)) :
    regularCollision u r d v ∈ localCoefficients C := by
  let H (n : ℕ) : ℤ → Module.End ℂ State :=
    fun k => sourceModeCoeff u v n (k + 3 * ((d : ℕ) : ℤ))
  have hEq : regularCollision u r d v =
      ∑ n ∈ Finset.range (vectorFrequencyBound lattice v + 1),
        regularGermCoeff ((r : ℂ) / 3) d n • H n := by
    funext k
    unfold regularCollision
    rw [source_sum_cutoff]
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro n _
    simp only [H, sourceModeCoeff, sourceCoeff,
      show k + 3 * ((d : ℕ) : ℤ) - 3 + 3 * ((n : ℤ) + 1) =
        k + 3 * ((d : ℕ) : ℤ) + 3 * (n : ℤ) by ring]
  rw [hEq]
  apply (localCoefficients C).sum_mem
  intro n hn
  apply (localCoefficients C).smul_mem
  exact localCoefficients_shift C _ _
    (sourceModeCoeff_local u r hr hu v s t C hv hC hAC hBC hAB n (by simpa using hn))

private theorem negativeCurrent_local_residue (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (d : ℕ+) (v : NativeStates) (s t : ℤ)
    (C : Field) (hs : InResidue s (nativeField v)) (ht : InResidue t C)
    (hAC : CoverLocal (currentField u) C)
    (hBC : CoverLocal (nativeField v) C)
    (hAB : CoverLocal (currentField u) (nativeField v)) :
    CoverLocal (nativeField (mu lattice (currentAlong lattice u) (-((d : ℕ) : ℤ)) v)) C := by
  apply (coverLocal_iff _ _).mpr
  have hEq : HVertexOperator.coeff
      (nativeField (mu lattice (currentAlong lattice u) (-((d : ℕ) : ℤ)) v)) =
      HVertexOperator.coeff (normalPartField u r d v s) + regularCollision u r d v := by
    funext k
    apply LinearMap.ext
    intro x
    rw [nativeField_current_negative_iterate u r hr hu, signedNormalTaylor_eq u r hr hu d v s hs]
    rfl
  rw [hEq]
  exact (localCoefficients _).add_mem (normalPart_local u r d v s t _ ht hAC hBC hAB)
    (regularCollision_local u r hr hu d v s t _ hs ht hAC hBC hAB)

private def residueComponent (t : ℤ) (C : Field) : Field :=
  restoreResidue t (stripResidue t C)

private theorem delta_component_right (t : ℤ) (A C : Field) (N : ℕ) (k l : ℤ) :
    coverDelta^[N] (coverComm A (residueComponent t C)) k l =
      if l % 3 = t % 3 then coverDelta^[N] (coverComm A C) k l else 0 := by
  induction N generalizing k l with
  | zero =>
    simp only [Function.iterate_zero_apply, coverComm, residueComponent, restoreResidue_coeff]
    split
    · rw [stripResidue_coeff, show 3 * ((l - t) / 3) + t = l by omega]
    · simp [LieRing.of_associative_ring_bracket]
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', coverDelta, coverDelta,
      ih, ih, show (l - 3) % 3 = l % 3 by omega]
    by_cases h : l % 3 = t % 3
    · simp only [ite_eq_left h]
    · simp only [ite_eq_right h, sub_self]

private theorem coverLocal_right_components (A C : Field) :
    CoverLocal A C ↔ ∀ t : Fin 3, CoverLocal A (residueComponent (t.val : ℤ) C) := by
  classical
  constructor
  · rintro ⟨N, hN⟩ t
    refine ⟨N, ?_⟩
    funext k l
    rw [delta_component_right, hN]
    split <;> rfl
  · intro h
    choose order killed using h
    let N := Finset.univ.sup order
    refine ⟨N, ?_⟩
    funext k l
    let t : Fin 3 := ⟨(l % 3).toNat, by omega⟩
    have ht : l % 3 = (t.val : ℤ) % 3 := by dsimp [t]; omega
    have hN : order t ≤ N := Finset.le_sup (f := order) (Finset.mem_univ t)
    have hz : coverDelta^[N] (coverComm A (residueComponent (t.val : ℤ) C)) = 0 := by
      have h₀ : (deltaCoverEnd ^ order t) (coverComm A (residueComponent (t.val : ℤ) C)) =
          0 := by
        rw [Module.End.pow_apply]
        exact killed t
      have h₁ := coverOrder_mono hN h₀
      rw [Module.End.pow_apply] at h₁
      exact h₁
    have he := congrFun (congrFun hz k) l
    rw [delta_component_right, ite_eq_left ht] at he
    exact he

/-- Pairwise locality propagates to every negative product with a residue
eigen-current and a lift eigenstate. The comparison field is the actual field
of an arbitrary native state. -/
theorem native_negativeCurrent_local (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (d : ℕ+) (v w : NativeStates) (s : ℤ)
    (hv : σ v = ζ ^ s • v)
    (hAC : CoverLocal (nativeField (currentAlong lattice u)) (nativeField w))
    (hBC : CoverLocal (nativeField v) (nativeField w))
    (hAB : CoverLocal (nativeField (currentAlong lattice u)) (nativeField v)) :
    CoverLocal (nativeField (mu lattice (currentAlong lattice u) (-((d : ℕ) : ℤ)) v))
      (nativeField w) := by
  simp only [P48qNativeMonodromy.nativeField_current] at hAC hAB
  apply (coverLocal_right_components _ _).mpr
  intro t
  exact negativeCurrent_local_residue u r hr hu d v s (t.val : ℤ) _
    (nativeField_inResidue v s hv) (restoreResidue_inResidue _ _)
    ((coverLocal_right_components _ _).mp hAC t)
    ((coverLocal_right_components _ _).mp hBC t) hAB

/--
info:
'D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentLocality.native_negativeCurrent_local'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms native_negativeCurrent_local

/-- Every residue eigen-current is local against the actual field of any native state. -/
theorem native_current_local (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (v : NativeStates) :
    CoverLocal (nativeField (currentAlong lattice u)) (nativeField v) := by
  rw [P48qNativeMonodromy.nativeField_current, coverLocal_right_components]
  have hcurrent : InResidue (-(r : ℤ)) (currentField u) := by
    intro k hk
    rw [currentField_coeff]
    exact mode_offResidue u r hr hu _ (by omega)
  intro t
  let N := vectorFrequencyBound lattice v + 1
  refine ⟨N, (coverDelta_comm_eq_zero_iff _ _ _ _ hcurrent
    (restoreResidue_inResidue _ _) N).mpr ?_⟩
  funext i j
  rw [stripResidue_restoreResidue, delta_alignedComm,
    alignedComm_differences u r hr hu]
  exact Finset.sum_eq_zero fun n hn => by
    rw [ite_eq_right (not_le.mpr (Finset.mem_range.mp hn)), zero_smul]

#print axioms native_current_local

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentLocality
