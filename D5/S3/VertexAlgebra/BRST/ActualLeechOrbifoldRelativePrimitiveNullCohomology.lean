/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativePrimitiveNullCohomology
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativePrimitiveNullCohomology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual BRST differential and cohomology at primitive null momentum. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativePrimitiveNull
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The Ward identities determine the native differential on the relative shell. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldRelativePrimitiveNull

open ActualLeechOrbifoldCriticalMatter (matter hyperbolicPlane hyperbolicMatter Matter)
open ActualLeechOrbifoldBRST (ComplexState Q Q_squared)
open ActualLeechOrbifoldRelativeNormTwo (N)
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeSugawaraCurrents
open LatticeSugawaraConformal LatticeSugawaraVirasoro
open LatticeFiniteNegativeGeneration (neutralMode neutralPolynomialMode)
open ActualLeechHyperbolic (leechData)
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (ket vacuum annihilate annihilate_ket phase lowerCount)
open private plane_inverse from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCriticalMatter
open private mode_vacuum from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLowWeights
open private matter_mode_tmul from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwo
open private L_vacuum L_vacuum_nonneg from D5.S3.Quantum.Fermionic.BcGhostVirasoro
open private number_ket from D5.S3.Quantum.Fermionic.BcGhostCharge
open private cv cu cw Q_mem_C v_mem_C u_mem_C w_mem_C shellState excitation
  orbifoldVacuum slice slice_shellState coefficient excitation_ne
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativePrimitiveNull

private def ghostDegree (q : ℤ) : Submodule ℂ ComplexState :=
  Module.End.eigenspace (R := ℂ) (M := ComplexState) N (q : ℂ)

/-- The actual relative cochains of integral ghost degree q. -/
def Cq (q : ℤ) : Submodule ℂ ComplexState := C ⊓ ghostDegree q

private theorem N_shellState (d : Exponent hyperbolicPlane) (S : Finset ℕ) :
    N (shellState d S) = (BcGhostCharge.charge S : ℂ) • shellState d S := by
  change _ ⊗ₜ[ℂ] BcGhostCharge.ghostNumber (ket S) = _
  rw [number_ket, TensorProduct.tmul_smul]
  rfl

private theorem N_v : N v = 0 := by
  have h : BcGhostCharge.charge ∅ = 0 := by decide
  rw [v, N_shellState, h, Int.cast_zero, zero_smul]

private theorem N_u (i : Fin 2) : N (u i) = u i := by
  have h : BcGhostCharge.charge {1} = 1 := by decide
  rw [u, N_shellState, h, Int.cast_one, one_smul]

private theorem N_w : N w = (2 : ℂ) • w := by
  have h : BcGhostCharge.charge {1, 5} = 2 := by decide
  rw [w, N_shellState, h, Int.cast_ofNat]

private theorem v_mem_Cq : v ∈ Cq 0 :=
  ⟨v_mem_C, Module.End.mem_eigenspace_iff.mpr
    (by simpa only [Int.cast_zero, zero_smul] using N_v)⟩

private theorem u_mem_Cq (i : Fin 2) : u i ∈ Cq 1 :=
  ⟨u_mem_C i, Module.End.mem_eigenspace_iff.mpr
    (by simpa only [Int.cast_one, one_smul] using N_u i)⟩

private theorem w_mem_Cq : w ∈ Cq 2 :=
  ⟨w_mem_C, Module.End.mem_eigenspace_iff.mpr
    (by simpa only [Int.cast_ofNat] using N_w)⟩

private theorem coeff_shellState (l : Label hyperbolicPlane) (S : Finset ℕ)
    (d : Exponent hyperbolicPlane) (T : Finset ℕ) :
    coefficient l S (shellState d T) = if l = (momentum, d) ∧ S = T then 1 else 0 := by
  classical
  change carrierCoeffEquiv leechData (slice l S (shellState d T)).1.val (0, 0) = _
  rw [slice_shellState]
  split_ifs
  · change carrierCoeffEquiv leechData (Finsupp.single 0 1) (0, 0) = 1
    have h : carrierBasis leechData (0, 0) = (Finsupp.single 0 1 : Carrier leechData) := by
      simp
    rw [← h, carrierCoeffEquiv_basis, Finsupp.single_eq_same]
  · change carrierCoeffEquiv leechData 0 (0, 0) = 0
    rw [map_zero, Finsupp.zero_apply]

private theorem coeff_diagonal :
    cv v = 1 ∧ cv (u 0) = 0 ∧ cv (u 1) = 0 ∧ cv w = 0 ∧
    cu 0 v = 0 ∧ cu 0 (u 0) = 1 ∧ cu 0 (u 1) = 0 ∧ cu 0 w = 0 ∧
    cu 1 v = 0 ∧ cu 1 (u 0) = 0 ∧ cu 1 (u 1) = 1 ∧ cu 1 w = 0 ∧
    cw v = 0 ∧ cw (u 0) = 0 ∧ cw (u 1) = 0 ∧ cw w = 1 := by
  classical
  have h01 : (momentum, excitation 0) ≠ (momentum, excitation 1) :=
    fun e => excitation_ne (congrArg Prod.snd e)
  have e01 : (∅ : Finset ℕ) ≠ {1} := by decide
  have e02 : (∅ : Finset ℕ) ≠ {1, 5} := by decide
  have e12 : ({1} : Finset ℕ) ≠ {1, 5} := by decide
  simp [cv, cu, cw, v, u, w, coeff_shellState, h01, Ne.symm h01,
    e01, Ne.symm e01, e02, Ne.symm e02, e12, Ne.symm e12]

private theorem coefficients_in_degree {q : ℤ} {x : ComplexState} (hx : x ∈ Cq q) :
    (q ≠ 0 → cv x = 0) ∧ (q ≠ 1 → cu 0 x = 0 ∧ cu 1 x = 0) ∧ (q ≠ 2 → cw x = 0) := by
  obtain ⟨hv, hvu0, hvu1, hvw, hu0v, hu00, hu01, hu0w,
    hu1v, hu10, hu11, hu1w, hwv, hwu0, hwu1, hw⟩ := coeff_diagonal
  have hN := Module.End.mem_eigenspace_iff.mp hx.2
  change N x = (q : ℂ) • x at hN
  conv_lhs at hN => rw [expansion hx.1]
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
    N_v, N_u, N_u, N_w, smul_zero, zero_add] at hN
  have vanish {a : ℤ} {z : ℂ} (h : (a : ℂ) * z = (q : ℂ) * z) (hq : q ≠ a) : z = 0 := by
    apply (mul_eq_mul_right_iff.mp h).resolve_left
    exact_mod_cast hq.symm
  refine ⟨fun h => vanish (a := 0) ?_ h,
    fun h => ⟨vanish (a := 1) ?_ h, vanish (a := 1) ?_ h⟩, fun h => vanish (a := 2) ?_ h⟩
  · simpa only [map_add, map_smul, smul_eq_mul, hvu0, hvu1, hvw, mul_zero,
      add_zero, Int.cast_zero, zero_mul] using congrArg cv hN
  · simpa only [map_add, map_smul, smul_eq_mul, hu00, hu01, hu0w, mul_zero,
      mul_one, add_zero, Int.cast_one, one_mul] using congrArg (cu 0) hN
  · simpa only [map_add, map_smul, smul_eq_mul, hu10, hu11, hu1w, mul_zero,
      mul_one, zero_add, add_zero, Int.cast_one, one_mul] using congrArg (cu 1) hN
  · simpa only [map_add, map_smul, smul_eq_mul, hwu0, hwu1, hw, mul_zero, mul_one,
      add_zero, zero_add, Int.cast_ofNat, mul_comm, zero_mul, one_mul] using congrArg cw hN

private theorem degree_zero {x : ComplexState} (hx : x ∈ Cq 0) : x = cv x • v := by
  obtain ⟨h0, h1⟩ := (coefficients_in_degree hx).2.1 (by decide)
  simpa only [h0, h1, (coefficients_in_degree hx).2.2 (by decide), zero_smul, add_zero]
    using expansion hx.1

private theorem degree_one {x : ComplexState} (hx : x ∈ Cq 1) :
    x = cu 0 x • u 0 + cu 1 x • u 1 := by
  obtain ⟨h0, _, h2⟩ := coefficients_in_degree hx
  simpa only [h0 (by decide), h2 (by decide), zero_smul, zero_add, add_zero] using expansion hx.1

private theorem degree_two {x : ComplexState} (hx : x ∈ Cq 2) : x = cw x • w := by
  obtain ⟨h0, h1, h2⟩ := coefficients_in_degree hx
  obtain ⟨hu0, hu1⟩ := h1 (by decide)
  simpa only [h0 (by decide), hu0, hu1, zero_smul, zero_add] using expansion hx.1

private theorem degree_other {q : ℤ} {x : ComplexState} (hx : x ∈ Cq q)
    (h0 : q ≠ 0) (h1 : q ≠ 1) (h2 : q ≠ 2) : x = 0 := by
  obtain ⟨hv, hu, hw⟩ := coefficients_in_degree hx
  obtain ⟨hu0, hu1⟩ := hu h1
  simpa only [hv h0, hu0, hu1, hw h2, zero_smul, add_zero] using expansion hx.1

/-- The native ghost-degree spaces are exactly the four displayed basis directions. -/
theorem graded_shell :
    Cq 0 = Submodule.span ℂ ({v} : Set ComplexState) ∧
    Cq 1 = Submodule.span ℂ ({u 0, u 1} : Set ComplexState) ∧
    Cq 2 = Submodule.span ℂ ({w} : Set ComplexState) ∧
    ∀ q : ℤ, q ≠ 0 → q ≠ 1 → q ≠ 2 → Cq q = ⊥ := by
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_, le_antisymm ?_ ?_, ?_⟩
  · intro x hx
    exact Submodule.mem_span_singleton.mpr ⟨cv x, (degree_zero hx).symm⟩
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr v_mem_Cq
  · intro x hx
    exact Submodule.mem_span_pair.mpr ⟨cu 0 x, cu 1 x, (degree_one hx).symm⟩
  · apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact u_mem_Cq 0
    · rw [Set.mem_singleton_iff.mp hz]
      exact u_mem_Cq 1
  · intro x hx
    exact Submodule.mem_span_singleton.mpr ⟨cw x, (degree_two hx).symm⟩
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr w_mem_Cq
  · intro q h0 h1 h2
    apply le_antisymm _ bot_le
    intro x hx
    exact (Submodule.mem_bot ℂ).mpr (degree_other hx h0 h1 h2)

private theorem Q_mem_Cq {q : ℤ} {x : ComplexState} (hx : x ∈ Cq q) : Q x ∈ Cq (q + 1) := by
  refine ⟨Q_mem_C hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
  have hn := Module.End.mem_eigenspace_iff.mp hx.2
  have h := LinearMap.congr_fun (VirasoroBRST.N_Q matter) x
  change N (Q x) - Q (N x) = Q x at h
  change N x = (q : ℂ) • x at hn
  rw [hn, map_smul, sub_eq_iff_eq_add] at h
  change N (Q x) = ((q + 1 : ℤ) : ℂ) • Q x
  rw [Int.cast_add, Int.cast_one, add_smul, one_smul]
  exact h.trans (add_comm _ _)

private abbrev B (n : ℤ) := VirasoroBRST.ghostB matter n
private abbrev L (n : ℤ) := VirasoroBRST.Ltotal matter n

private abbrev planeGround : Carrier hyperbolicPlane := Finsupp.single momentum 1
private abbrev planeExcited (i : Fin 2) : Carrier hyperbolicPlane :=
  Finsupp.single momentum (MvPolynomial.X (i, 0))

private theorem plane_basis_ground :
    carrierBasis hyperbolicPlane (momentum, 0) = planeGround := by simp

private theorem plane_basis_excited (i : Fin 2) :
    carrierBasis hyperbolicPlane (momentum, excitation i) = planeExcited i := by
  rw [carrierBasis_apply]
  rfl

private theorem plane_L_neg_ground : hyperbolicMatter.mode (-1) planeGround = planeExcited 0 := by
  change sugawaraMode hyperbolicPlane (gramComplex hyperbolicPlane) (-1) _ = _
  rw [sugawaraMode_ground_minus_one _ _ plane_inverse plane_inverse]
  congr 1
  simp [chargePolynomial, momentum, unitCharge]

private theorem plane_L_pos_excited (i : Fin 2) :
    hyperbolicMatter.mode 1 (planeExcited i) = (OrderedHyperbolicExtension.U i 0 : ℂ) • planeGround := by
  let D := hyperbolicPlane
  let H := gramComplex D
  have hneg : neutralMode D i (-1) planeGround = planeExcited i := by
    simp [neutralMode, neutralPolynomialMode, planeGround, planeExcited]
  have hground : sugawaraMode D H 1 planeGround = 0 :=
    sugawaraMode_ground_positive D H momentum 1 (by decide)
  have h := LinearMap.congr_fun
    (sugawaraMode_current_commutator D H plane_inverse plane_inverse i 1 (-1)) planeGround
  change sugawaraMode D H 1 (neutralMode D i (-1) planeGround) -
    neutralMode D i (-1) (sugawaraMode D H 1 planeGround) =
    -((-1 : ℤ) : ℂ) • neutralMode D i (1 + -1) planeGround at h
  rw [hneg, hground, map_zero, sub_zero, show (1 : ℤ) + -1 = 0 by decide,
    neutralMode_zero_single] at h
  change sugawaraMode D H 1 _ = _
  have hp : chargeScalar D momentum i = (OrderedHyperbolicExtension.U i 0 : ℂ) := by
    change (bilinear hyperbolicPlane (unitCharge hyperbolicPlane i) momentum : ℂ) = _
    fin_cases i <;> norm_num [bilinear, hyperbolicPlane, Fin.sum_univ_two,
      momentum, unitCharge, OrderedHyperbolicExtension.U] <;> rfl
  simpa only [hp, Int.cast_neg, Int.cast_one, neg_neg, one_smul] using h

private theorem ghost_L_neg_vacuum : BcGhostVirasoro.L (-1) vacuum = 0 := by
  rw [L_vacuum, show Finset.Icc ((-1 : ℤ) + 2) 1 = {1} by decide]
  simp

private theorem ghost_L_pos_ket : BcGhostVirasoro.L 1 (ket {1}) = 0 := by
  rw [← BcGhostFock.ghost_vacuum.2.2.1]
  have h := LinearMap.congr_fun (BcGhostVirasoro.ward_c 1 1) vacuum
  change BcGhostVirasoro.L 1 (BcGhostFock.c 1 vacuum) -
    BcGhostFock.c 1 (BcGhostVirasoro.L 1 vacuum) =
    ((-2 * 1 - 1 : ℤ) : ℂ) • BcGhostFock.c 2 vacuum at h
  have hc := BcGhostFock.ghost_vacuum.2.1 2 (by decide)
  rw [L_vacuum_nonneg 1 (by decide), map_zero, sub_zero, hc, smul_zero] at h
  exact h

private theorem ghostB_tmul (n : ℤ) (m : Matter) (g : CountableOccupationFock.Fock) :
    B n (m ⊗ₜ[ℂ] g) = m ⊗ₜ[ℂ] BcGhostFock.b n g := rfl

private theorem L_neg_v : L (-1) v = B (-1) (u 0) := by
  change (matter.mode (-1) (orbifoldVacuum ⊗ₜ[ℂ] carrierBasis hyperbolicPlane (momentum, 0))
    ⊗ₜ[ℂ] vacuum) + (_ ⊗ₜ[ℂ] BcGhostVirasoro.L (-1) vacuum) = _
  rw [matter_mode_tmul, mode_vacuum (-1) (by decide), TensorProduct.zero_tmul, zero_add,
    plane_basis_ground, plane_L_neg_ground, ghost_L_neg_vacuum, TensorProduct.tmul_zero, add_zero]
  rw [u, shellState, ghostB_tmul, plane_basis_excited]
  change _ = _ ⊗ₜ[ℂ] annihilate 1 (ket {1})
  rw [annihilate_ket]
  have hc : lowerCount 1 {1} = 0 := by decide
  have he : ({1} : Finset ℕ).erase 1 = ∅ := by decide
  simp [phase, hc, he, vacuum]

private theorem B_pos_w : B 1 w = -shellState 0 {1} := by
  change _ ⊗ₜ[ℂ] annihilate 5 (ket {1, 5}) = _
  rw [annihilate_ket]
  have hc : lowerCount 5 {1, 5} = 1 := by decide
  have he : ({1, 5} : Finset ℕ).erase 5 = {1} := by decide
  simp [phase, hc, he, shellState, TensorProduct.tmul_neg]

private theorem L_pos_u (i : Fin 2) :
    L 1 (u i) = (OrderedHyperbolicExtension.U i 0 : ℂ) • B 1 (-w) := by
  have hb : B 1 (-w) = shellState 0 {1} := by
    have h := map_neg (B 1) w
    rw [B_pos_w] at h
    exact h.trans (neg_neg (shellState 0 {1}))
  rw [hb]
  change (matter.mode 1 (orbifoldVacuum ⊗ₜ[ℂ] carrierBasis hyperbolicPlane (momentum, excitation i))
    ⊗ₜ[ℂ] ket {1}) + (_ ⊗ₜ[ℂ] BcGhostVirasoro.L 1 (ket {1})) = _
  rw [matter_mode_tmul, mode_vacuum 1 (by decide), TensorProduct.zero_tmul, zero_add,
    plane_basis_excited, plane_L_pos_excited, ghost_L_pos_ket, TensorProduct.tmul_zero, add_zero]
  simp only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', shellState, plane_basis_ground]

private theorem B_neg_v : B (-1) v = 0 := by
  change _ ⊗ₜ[ℂ] annihilate 1 (ket ∅) = _
  rw [annihilate_ket, ite_eq_right (by decide), TensorProduct.tmul_zero]

private theorem B_pos_u (i : Fin 2) : B 1 (u i) = 0 := by
  change _ ⊗ₜ[ℂ] annihilate 5 (ket {1}) = _
  rw [annihilate_ket, ite_eq_right (by decide), TensorProduct.tmul_zero]

private theorem B_neg_u (i : Fin 2) : B (-1) (u i) = shellState (excitation i) ∅ := by
  change _ ⊗ₜ[ℂ] annihilate 1 (ket {1}) = _
  rw [annihilate_ket]
  have hc : lowerCount 1 {1} = 0 := by decide
  have he : ({1} : Finset ℕ).erase 1 = ∅ := by decide
  simp [phase, hc, he, shellState]

private theorem B_neg_detect {x : ComplexState} (hx : x ∈ Cq 1) (hb : B (-1) x = 0) : x = 0 := by
  have h := degree_one hx
  have hb' := hb
  conv_lhs at hb' => rw [h]
  rw [map_add, map_smul, map_smul, B_neg_u, B_neg_u] at hb'
  classical
  have h01 : (momentum, excitation 0) ≠ (momentum, excitation 1) :=
    fun e => excitation_ne (congrArg Prod.snd e)
  have hzero (i : Fin 2) (hi : i = 0 ∨ i = 1) : cu i x = 0 := by
    rcases hi with rfl | rfl
    · simpa [map_add, map_smul, smul_eq_mul, coeff_shellState, h01] using
        congrArg (coefficient (momentum, excitation 0) ∅) hb'
    · simpa [map_add, map_smul, smul_eq_mul, coeff_shellState, Ne.symm h01] using
        congrArg (coefficient (momentum, excitation 1) ∅) hb'
  simpa [hzero 0 (Or.inl rfl), hzero 1 (Or.inr rfl)] using h

private theorem B_pos_detect {x : ComplexState} (hx : x ∈ Cq 2) (hb : B 1 x = 0) : x = 0 := by
  have h := degree_two hx
  have hb' := hb
  conv_lhs at hb' => rw [h]
  rw [map_smul, B_pos_w] at hb'
  classical
  have hz : -(cw x) = 0 := by
    have hneg := map_neg (coefficient (momentum, 0) {1}) (shellState 0 {1})
    simpa only [map_smul, hneg, smul_eq_mul, coeff_shellState, and_self, ite_true,
      mul_neg, mul_one, map_zero] using congrArg (coefficient (momentum, 0) {1}) hb'
  simpa [neg_eq_zero.mp hz] using h

private theorem Q_v : Q v = u 0 := by
  apply sub_eq_zero.mp
  apply B_neg_detect
  · have h : Q v ∈ Cq 1 := Q_mem_Cq (q := 0) v_mem_Cq
    exact Submodule.sub_mem (R := ℂ) (M := ComplexState) (Cq 1) h (u_mem_Cq 0)
  · have h := LinearMap.congr_fun (VirasoroBRST.Q_ward_b matter (-1)) v
    change Q (B (-1) v) + B (-1) (Q v) = L (-1) v at h
    rw [B_neg_v, map_zero, zero_add, L_neg_v] at h
    rw [map_sub, h, sub_self]

private theorem Q_u (i : Fin 2) : Q (u i) = (OrderedHyperbolicExtension.U i 0 : ℂ) • -w := by
  apply sub_eq_zero.mp
  apply B_pos_detect
  · have h : Q (u i) ∈ Cq 2 := Q_mem_Cq (q := 1) (u_mem_Cq i)
    have hn := Submodule.neg_mem (R := ℂ) (M := ComplexState) (Cq 2) w_mem_Cq
    have hs := (Cq 2).smul_mem (OrderedHyperbolicExtension.U i 0 : ℂ) hn
    exact Submodule.sub_mem (R := ℂ) (M := ComplexState) (Cq 2) h hs
  · have h := LinearMap.congr_fun (VirasoroBRST.Q_ward_b matter 1) (u i)
    change Q (B 1 (u i)) + B 1 (Q (u i)) = L 1 (u i) at h
    rw [B_pos_u, map_zero, zero_add, L_pos_u] at h
    rw [map_sub, map_smul, h, sub_self]

private theorem Q_u0 : Q (u 0) = 0 := by
  rw [Q_u]
  norm_num [OrderedHyperbolicExtension.U]

private theorem Q_u1 : Q (u 1) = -w := by
  rw [Q_u]
  norm_num [OrderedHyperbolicExtension.U]

private theorem Q_w : Q w = 0 :=
  degree_other (Q_mem_Cq (q := 2) w_mem_Cq) (by decide) (by decide) (by decide)

/-- The actual BRST charge on the four basis states in native conventions. -/
theorem differential_on_basis :
    Q v = u 0 ∧ Q (u 0) = 0 ∧ Q (u 1) = -w ∧ Q w = 0 :=
  ⟨Q_v, Q_u0, Q_u1, Q_w⟩

/-- The native charge restricted to two successive relative cochain spaces. -/
def d (q : ℤ) : Cq q →ₗ[ℂ] Cq (q + 1) :=
  Q.domRestrict (Cq q) |>.codRestrict _ fun x => Q_mem_Cq x.property

/-- The native differential from the preceding degree into degree q. -/
def incoming (q : ℤ) : Cq (q - 1) →ₗ[ℂ] Cq q :=
  (LinearEquiv.ofEq _ _ (congrArg Cq (sub_add_cancel q 1))).toLinearMap.comp (d (q - 1))

/-- Cycles are the kernel of the actual restricted charge. -/
def Cycles (q : ℤ) : Submodule ℂ (Cq q) := LinearMap.ker (d q)

private instance cochainAddCommGroup (q : ℤ) : AddCommGroup (Cq q) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := ℂ) (M := ComplexState) (Cq q)

instance (q : ℤ) : AddCommGroup (Cycles q) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := ℂ) (M := Cq q) (Cycles q)

instance (q : ℤ) : Module ℂ (Cycles q) := Submodule.module (Cycles q)

private def incomingCycles (q : ℤ) : Cq (q - 1) →ₗ[ℂ] Cycles q :=
  (incoming q).codRestrict (Cycles q) fun x => by
    change d q (incoming q x) = 0
    apply Subtype.ext
    change Q (Q x.val) = 0
    simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun Q_squared x.val

/-- Boundaries sit inside cycles by nilpotence of the actual charge. -/
def Boundaries (q : ℤ) : Submodule ℂ (Cycles q) := LinearMap.range (incomingCycles q)

/-- Relative BRST cohomology at the specified primitive null momentum. -/
abbrev Cohomology (q : ℤ) := Cycles q ⧸ Boundaries q

/-- Every closed relative state has an actual primitive in the previous ghost degree. -/
theorem exact_in_degree (q : ℤ) (x : ComplexState) (hx : x ∈ Cq q) (hQ : Q x = 0) :
    ∃ y ∈ Cq (q - 1), Q y = x := by
  obtain ⟨hv, hvu0, hvu1, hvw, hu0v, hu00, hu01, hu0w,
    hu1v, hu10, hu11, hu1w, hwv, hwu0, hwu1, hw⟩ := coeff_diagonal
  by_cases h0 : q = 0
  · subst q
    have h := degree_zero hx
    conv_lhs at hQ => rw [h]
    rw [map_smul, Q_v] at hQ
    have hz : cv x = 0 := by
      simpa only [map_smul, smul_eq_mul, hu00, mul_one, map_zero] using congrArg (cu 0) hQ
    exact ⟨0, (Cq _).zero_mem, by simpa only [hz, zero_smul, map_zero] using h.symm⟩
  by_cases h1 : q = 1
  · subst q
    have h := degree_one hx
    conv_lhs at hQ => rw [h]
    rw [map_add, map_smul, map_smul, Q_u0, Q_u1, smul_zero, zero_add] at hQ
    have hz : cu 1 x = 0 := by
      have hz : -(cu 1 x) = 0 := by
        have hneg := map_neg cw w
        simpa only [map_smul, hneg, smul_eq_mul, hw, mul_neg, mul_one, map_zero]
          using congrArg cw hQ
      exact neg_eq_zero.mp hz
    refine ⟨cu 0 x • v, (Cq 0).smul_mem _ v_mem_Cq, ?_⟩
    calc
      Q (cu 0 x • v) = cu 0 x • u 0 := by rw [map_smul, Q_v]
      _ = x := by simpa only [hz, zero_smul, add_zero] using h.symm
  by_cases h2 : q = 2
  · subst q
    refine ⟨(-cw x) • u 1, (Cq 1).smul_mem _ (u_mem_Cq 1), ?_⟩
    rw [map_smul, Q_u1]
    exact (neg_smul_neg (cw x) w).trans (degree_two hx).symm
  exact ⟨0, (Cq _).zero_mem, by rw [map_zero, degree_other hx h0 h1 h2]⟩

/-- The actual relative BRST cohomology vanishes in every integral ghost degree. -/
theorem cohomology_vanishes (q : ℤ) : Subsingleton (Cohomology q) := by
  have hall : Boundaries q = ⊤ := by
    apply top_unique
    intro x _
    have hx : Q x.val.val = 0 := congrArg Subtype.val x.property
    obtain ⟨y, hy, h⟩ := exact_in_degree q x.val.val x.val.property hx
    refine ⟨⟨y, hy⟩, ?_⟩
    exact Subtype.ext (Subtype.ext h)
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (p := Boundaries q) a
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (p := Boundaries q) b
  have hz (z : Cycles q) : (Submodule.Quotient.mk z : Cohomology q) = 0 :=
    (Submodule.Quotient.mk_eq_zero (p := Boundaries q)).mpr (by
      rw [hall]
      exact Submodule.mem_top)
  exact (hz x).trans (hz y).symm

#print axioms graded_shell
#print axioms differential_on_basis
#print axioms exact_in_degree
#print axioms cohomology_vanishes

end D5.S3.VertexAlgebra.ActualLeechOrbifoldRelativePrimitiveNull
