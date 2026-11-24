import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedSemirelativeBRST

/-! The native double-relative mapping cone for the zero-energy semirelative
closed Leech BRST complex. -/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedSemirelative

open ActualLeechOrbifoldCriticalMatter (Matter matter hyperbolicPlane)
open ActualLeechOrbifoldMatter (Orbifold)
open LatticeGeneratingFieldLocality (Carrier)
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock parity)

local instance : AddCommGroup Matter :=
  TensorProduct.addCommGroup (R := ℂ) (M := Orbifold) (N := Carrier hyperbolicPlane)

local instance : AddCommGroup ComplexState :=
  TensorProduct.addCommGroup (R := ℂ) (M := Matter) (N := Fock)

local instance : AddCommGroup ClosedState :=
  TensorProduct.addCommGroup (R := ℂ) (M := ComplexState) (N := ComplexState)

open private b0_square from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRST
open private tensor_neg_left signedDifferential_square from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeBRST
open private energy_commutes preserves_total_energy number_map_commutator
  number_one_comm number_gamma_comm sends_total_degree from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedSemirelativeBRST

private abbrev ChiralEnd := Module.End ℂ ComplexState
private abbrev ClosedEnd := Module.End ℂ ClosedState

abbrev c0 : ChiralEnd := VirasoroBRST.ghostC matter 0

private theorem b0_c0 : b0 * c0 + c0 * b0 = 1 := by
  let lift := Module.End.lTensorAlgHom ℂ Fock Matter
  have h : BcGhostFock.b 0 * BcGhostFock.c 0 + BcGhostFock.c 0 * BcGhostFock.b 0 = 1 := by
    simpa using BcGhostFock.ghost_mixed_car 0 0
  change lift (BcGhostFock.b 0) * lift (BcGhostFock.c 0) +
    lift (BcGhostFock.c 0) * lift (BcGhostFock.b 0) = 1
  rw [← map_mul, ← map_mul, ← map_add, h, map_one]

private theorem gamma_c0 : Γ * c0 = -(c0 * Γ) := by
  apply eq_neg_of_add_eq_zero_left
  let lift := Module.End.lTensorAlgHom ℂ Fock Matter
  change lift parity * lift (BcGhostFock.c 0) + lift (BcGhostFock.c 0) * lift parity = 0
  rw [← map_mul, ← map_mul, ← map_add, (BcGhostFock.ghost_parity 0).2, map_zero]

private theorem c0_commutes_energy : c0 * E = E * c0 := by
  have h : BcGhostFock.c 0 * BcGhostVirasoro.L 0 =
      BcGhostVirasoro.L 0 * BcGhostFock.c 0 := by
    exact (sub_eq_zero.mp (by simpa using BcGhostVirasoro.ward_c 0 0)).symm
  change TensorProduct.map 1 (BcGhostFock.c 0) *
      (TensorProduct.map (matter.mode 0) 1 + TensorProduct.map 1 (BcGhostVirasoro.L 0)) =
    (TensorProduct.map (matter.mode 0) 1 + TensorProduct.map 1 (BcGhostVirasoro.L 0)) *
      TensorProduct.map 1 (BcGhostFock.c 0)
  simp only [mul_add, add_mul, ← TensorProduct.map_mul, one_mul, mul_one, h]

/-- The symmetric c zero mode normalized against the unscaled supplier antighost. -/
def C_plus : ClosedEnd :=
  (1 / 2 : ℂ) • (TensorProduct.map c0 1 + TensorProduct.map Γ c0)

theorem B_plus_square : B_plus * B_plus = 0 :=
  signedDifferential_square b0 b0 Γ b0_square b0_square gamma_b0

private theorem bLeft_C_plus :
    TensorProduct.map b0 1 * C_plus + C_plus * TensorProduct.map b0 1 =
      (1 / 2 : ℂ) • (1 : ClosedEnd) := by
  rw [C_plus, mul_smul_comm, smul_mul_assoc, ← smul_add]
  congr 1
  calc
    _ = TensorProduct.map (b0 * c0 + c0 * b0) 1 := by
      simp only [mul_add, add_mul, ← TensorProduct.map_mul, one_mul, mul_one,
        gamma_b0, tensor_neg_left, TensorProduct.map_add_left]
      abel
    _ = 1 := by rw [b0_c0, TensorProduct.map_one]

private theorem bRightSigned_C_plus :
    TensorProduct.map Γ b0 * C_plus + C_plus * TensorProduct.map Γ b0 =
      (1 / 2 : ℂ) • (1 : ClosedEnd) := by
  rw [C_plus, mul_smul_comm, smul_mul_assoc, ← smul_add]
  congr 1
  calc
    _ = TensorProduct.map 1 (b0 * c0 + c0 * b0) := by
      simp only [mul_add, add_mul, ← TensorProduct.map_mul, one_mul, mul_one,
        gamma_c0, gamma_square, tensor_neg_left, TensorProduct.map_add_right]
      abel
    _ = 1 := by rw [b0_c0, TensorProduct.map_one]

theorem B_plus_C_plus : B_plus * C_plus + C_plus * B_plus = 1 := by
  calc
    _ = (TensorProduct.map b0 1 * C_plus + C_plus * TensorProduct.map b0 1) +
        (TensorProduct.map Γ b0 * C_plus + C_plus * TensorProduct.map Γ b0) := by
      simp only [B_plus, add_mul, mul_add]
      abel
    _ = 1 := by
      rw [bLeft_C_plus, bRightSigned_C_plus, ← add_smul]
      norm_num

theorem B_minus_C_plus : B_minus * C_plus + C_plus * B_minus = 0 := by
  calc
    _ = (TensorProduct.map b0 1 * C_plus + C_plus * TensorProduct.map b0 1) -
        (TensorProduct.map Γ b0 * C_plus + C_plus * TensorProduct.map Γ b0) := by
      simp only [B_minus, sub_mul, mul_sub]
      abel
    _ = 0 := by rw [bLeft_C_plus, bRightSigned_C_plus, sub_self]

theorem C_plus_L_minus : C_plus * L_minus = L_minus * C_plus := by
  have hl := energy_commutes c0 1 c0_commutes_energy (by simp)
  have hr := energy_commutes Γ c0 gamma_E c0_commutes_energy
  rw [C_plus, smul_mul_assoc, mul_smul_comm]
  congr 1
  simp only [L_minus, add_mul, mul_add, sub_mul, mul_sub, hl.1, hl.2, hr.1, hr.2]
  abel

theorem C_plus_L_plus : C_plus * L_plus = L_plus * C_plus := by
  have hl := energy_commutes c0 1 c0_commutes_energy (by simp)
  have hr := energy_commutes Γ c0 gamma_E c0_commutes_energy
  rw [C_plus, smul_mul_assoc, mul_smul_comm]
  congr 1
  simp only [L_plus, add_mul, mul_add, hl.1, hl.2, hr.1, hr.2]
  abel

theorem C_plus_mem_B_minus_ker {x : ClosedState} (hx : B_minus x = 0) :
    B_minus (C_plus x) = 0 := by
  have h : B_minus (C_plus x) + C_plus (B_minus x) = 0 :=
    LinearMap.congr_fun B_minus_C_plus x
  simpa only [hx, map_zero, add_zero] using h

theorem C_plus_mem_L_minus_ker {x : ClosedState} (hx : L_minus x = 0) :
    L_minus (C_plus x) = 0 := by
  have h : C_plus (L_minus x) = L_minus (C_plus x) :=
    LinearMap.congr_fun C_plus_L_minus x
  simpa only [hx, map_zero] using h.symm

theorem C_plus_mem_energy {m : ℂ} {x : ClosedState} (hx : x ∈ EnergySpace m) :
    C_plus x ∈ EnergySpace m :=
  ⟨⟨C_plus_mem_B_minus_ker hx.1.1, C_plus_mem_L_minus_ker hx.1.2⟩,
    preserves_total_energy C_plus_L_plus hx.2⟩

private theorem B_plus_mem_energy {m : ℂ} {x : ClosedState} (hx : x ∈ EnergySpace m) :
    B_plus x ∈ EnergySpace m :=
  ⟨B_plus_mem_semirelative hx.1, preserves_total_energy B_plus_L_plus hx.2⟩

/-- The native double-relative zero shell, cut out on the full closed tensor. -/
abbrev R : Submodule ℂ ClosedState := EnergySpace 0 ⊓ B_plus.ker

private theorem both_zero_of_sub_add {x y : ClosedState} (hm : x - y = 0) (hp : x + y = 0) :
    x = 0 ∧ y = 0 := by
  have he := sub_eq_zero.mp hm
  have hy : (2 : ℂ) • y = 0 := by
    rw [two_smul]
    simpa only [he] using hp
  have hz := congrArg (fun z : ClosedState => (2 : ℂ)⁻¹ • z) hy
  change (2 : ℂ)⁻¹ • ((2 : ℂ) • y) = (2 : ℂ)⁻¹ • (0 : ClosedState) at hz
  rw [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul, smul_zero] at hz
  exact ⟨he.trans hz, hz⟩

private theorem signed_bRight_eq_zero_iff (x : ClosedState) :
    TensorProduct.map Γ b0 x = 0 ↔ TensorProduct.map (1 : ChiralEnd) b0 x = 0 := by
  have ha : TensorProduct.map Γ (1 : ChiralEnd) * TensorProduct.map Γ b0 =
      TensorProduct.map (1 : ChiralEnd) b0 := by
    rw [← TensorProduct.map_mul, gamma_square, one_mul]
  have hb : TensorProduct.map Γ (1 : ChiralEnd) * TensorProduct.map 1 b0 =
      TensorProduct.map Γ b0 := by
    rw [← TensorProduct.map_mul, mul_one, one_mul]
  constructor
  · intro h
    rw [← ha, Module.End.mul_apply, h, map_zero]
  · intro h
    rw [← hb, Module.End.mul_apply, h, map_zero]

/-- Membership in the double-relative shell is exactly vanishing of both
literal chiral antighosts and both literal chiral energies. -/
theorem mem_R_iff (x : ClosedState) :
    x ∈ R ↔
      TensorProduct.map b0 (1 : ChiralEnd) x = 0 ∧
      TensorProduct.map (1 : ChiralEnd) b0 x = 0 ∧
      TensorProduct.map E (1 : ChiralEnd) x = 0 ∧
      TensorProduct.map (1 : ChiralEnd) E x = 0 := by
  constructor
  · intro hx
    have hL : L_plus x = 0 := by
      simpa only [zero_smul] using Module.End.mem_eigenspace_iff.mp hx.1.2
    obtain ⟨hbL, hbR⟩ := both_zero_of_sub_add
      (show B_minus x = 0 from hx.1.1.1) (show B_plus x = 0 from hx.2)
    obtain ⟨heL, heR⟩ := both_zero_of_sub_add (show L_minus x = 0 from hx.1.1.2) hL
    exact ⟨hbL, (signed_bRight_eq_zero_iff x).mp hbR, heL, heR⟩
  · rintro ⟨hbL, hbR, heL, heR⟩
    have hbR' := (signed_bRight_eq_zero_iff x).mpr hbR
    refine ⟨⟨⟨?_, ?_⟩, Module.End.mem_eigenspace_iff.mpr ?_⟩, ?_⟩
    · change B_minus x = 0
      simp only [B_minus, LinearMap.sub_apply, hbL, hbR', sub_zero]
    · change L_minus x = 0
      simp only [L_minus, LinearMap.sub_apply, heL, heR, sub_zero]
    · simp only [L_plus, LinearMap.add_apply, heL, heR, add_zero, zero_smul]
    · change B_plus x = 0
      simp only [B_plus, LinearMap.add_apply, hbL, hbR', add_zero]

private theorem B_plus_C_plus_apply (x : ClosedState) :
    B_plus (C_plus x) + C_plus (B_plus x) = x :=
  LinearMap.congr_fun B_plus_C_plus x

private theorem B_plus_square_apply (x : ClosedState) : B_plus (B_plus x) = 0 :=
  LinearMap.congr_fun B_plus_square x

private theorem B_plus_D_apply {x : ClosedState} (hx : x ∈ EnergySpace 0) :
    B_plus (D x) = -D (B_plus x) := by
  have h : D (B_plus x) + B_plus (D x) = L_plus x :=
    LinearMap.congr_fun D_B_plus x
  have hL : L_plus x = 0 := by
    simpa only [zero_smul] using Module.End.mem_eigenspace_iff.mp hx.2
  rw [hL, add_comm] at h
  exact eq_neg_of_add_eq_zero_left h

theorem D_mem_R {x : ClosedState} (hx : x ∈ R) : D x ∈ R := by
  refine ⟨(differential 0 ⟨x, hx.1⟩).property, ?_⟩
  change B_plus (D x) = 0
  rw [B_plus_D_apply hx.1, show B_plus x = 0 from hx.2, map_zero, neg_zero]

/-- The native relative differential. -/
def D_R : Module.End ℂ R := D.restrict fun _ hx => D_mem_R hx

theorem D_R_square : D_R * D_R = 0 := by
  apply LinearMap.ext
  intro x
  exact Subtype.ext (LinearMap.congr_fun D_square x.val)

/-- The off-diagonal map before restriction to the relative shell. -/
def M : ClosedEnd := D * C_plus + C_plus * D

theorem M_mem_R {x : ClosedState} (hx : x ∈ R) : M x ∈ R := by
  have hDx := D_mem_R hx
  have hCx := C_plus_mem_energy hx.1
  refine ⟨(EnergySpace 0).add_mem (differential 0 ⟨C_plus x, hCx⟩).property
    (C_plus_mem_energy hDx.1), ?_⟩
  have hC {y : ClosedState} (hy : y ∈ R) : B_plus (C_plus y) = y := by
    simpa only [show B_plus y = 0 from hy.2, map_zero, add_zero] using B_plus_C_plus_apply y
  change B_plus (D (C_plus x) + C_plus (D x)) = 0
  rw [map_add, B_plus_D_apply hCx, hC hx, hC hDx, neg_add_cancel]

def M_R : Module.End ℂ R := M.restrict fun _ hx => M_mem_R hx

theorem D_R_M_R : D_R * M_R = M_R * D_R := by
  have h : D * M = M * D := by
    calc
      D * M = (D * D) * C_plus + D * C_plus * D := by unfold M; noncomm_ring
      _ = D * C_plus * D + C_plus * (D * D) := by rw [D_square, zero_mul, mul_zero, zero_add, add_zero]
      _ = M * D := by unfold M; noncomm_ring
  apply LinearMap.ext
  intro x
  exact Subtype.ext (LinearMap.congr_fun h x.val)

private theorem B_plus_mem_R {x : ClosedState} (hx : x ∈ EnergySpace 0) : B_plus x ∈ R :=
  ⟨B_plus_mem_energy hx, B_plus_square_apply x⟩

private theorem split_first_mem_R {x : ClosedState} (hx : x ∈ EnergySpace 0) :
    x - C_plus (B_plus x) ∈ R := by
  refine ⟨(EnergySpace 0).sub_mem hx (C_plus_mem_energy (B_plus_mem_energy hx)), ?_⟩
  have h := B_plus_C_plus_apply (B_plus x)
  rw [B_plus_square_apply, map_zero, add_zero] at h
  change B_plus (x - C_plus (B_plus x)) = 0
  rw [map_sub, h, sub_self]

/-- The literal split of the zero-energy semirelative space and its inverse. -/
def zeroEnergySplit : EnergySpace 0 ≃ₗ[ℂ] R × R where
  toFun x := (⟨x.val - C_plus (B_plus x.val), split_first_mem_R x.property⟩,
    ⟨B_plus x.val, B_plus_mem_R x.property⟩)
  invFun y := ⟨y.1.val + C_plus y.2.val,
    (EnergySpace 0).add_mem y.1.property.1 (C_plus_mem_energy y.2.property.1)⟩
  left_inv x := Subtype.ext (sub_add_cancel _ _)
  right_inv y := by
    have hs : B_plus (y.1.val + C_plus y.2.val) = y.2.val := by
      rw [map_add, show B_plus y.1.val = 0 from y.1.property.2, zero_add]
      simpa only [show B_plus y.2.val = 0 from y.2.property.2, map_zero, add_zero] using
        B_plus_C_plus_apply y.2.val
    apply Prod.ext
    · apply Subtype.ext
      change y.1.val + C_plus y.2.val - C_plus (B_plus (y.1.val + C_plus y.2.val)) = y.1.val
      rw [hs, add_sub_cancel_right]
    · exact Subtype.ext hs
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x.val + y.val - C_plus (B_plus (x.val + y.val)) =
        (x.val - C_plus (B_plus x.val)) + (y.val - C_plus (B_plus y.val))
      rw [map_add, map_add]
      abel
    · exact Subtype.ext (map_add B_plus x.val y.val)
  map_smul' a x := by
    apply Prod.ext
    · apply Subtype.ext
      change a • x.val - C_plus (B_plus (a • x.val)) = a • (x.val - C_plus (B_plus x.val))
      rw [map_smul, map_smul, smul_sub]
    · exact Subtype.ext (map_smul B_plus a x.val)

theorem zeroEnergySplit_apply (x : EnergySpace 0) :
    (zeroEnergySplit x).1.val = x.val - C_plus (B_plus x.val) ∧
    (zeroEnergySplit x).2.val = B_plus x.val := ⟨rfl, rfl⟩

theorem zeroEnergySplit_symm_apply (y : R × R) :
    (zeroEnergySplit.symm y).val = y.1.val + C_plus y.2.val := rfl

/-- The differential on the split double-relative shell. -/
def coneDifferential : Module.End ℂ (R × R) :=
  ((D_R.comp (LinearMap.fst ℂ R R)) + (M_R.comp (LinearMap.snd ℂ R R))).prod
    (-(D_R.comp (LinearMap.snd ℂ R R)))

theorem coneDifferential_apply (r s : R) :
    coneDifferential (r, s) = (D_R r + M_R s, -D_R s) := rfl

/-- The explicit split intertwines the native and cone differentials. -/
theorem zeroEnergySplit_differential (x : EnergySpace 0) :
    zeroEnergySplit (differential 0 x) = coneDifferential (zeroEnergySplit x) := by
  obtain ⟨⟨r, s⟩, rfl⟩ := zeroEnergySplit.symm.surjective x
  rw [zeroEnergySplit.apply_symm_apply]
  apply zeroEnergySplit.symm.injective
  rw [zeroEnergySplit.symm_apply_apply, coneDifferential_apply]
  apply Subtype.ext
  change D (r.val + C_plus s.val) =
    D r.val + (D (C_plus s.val) + C_plus (D s.val)) + C_plus (-D s.val)
  rw [map_add D, map_neg C_plus]
  rw [add_assoc (D r.val), add_assoc (D (C_plus s.val)), add_neg_cancel, add_zero]

theorem coneDifferential_square : coneDifferential * coneDifferential = 0 := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := zeroEnergySplit.surjective y
  change coneDifferential (coneDifferential (zeroEnergySplit x)) = 0
  rw [← zeroEnergySplit_differential, ← zeroEnergySplit_differential]
  have h : differential 0 (differential 0 x) = 0 :=
    LinearMap.congr_fun (differential_square 0) x
  exact (congrArg zeroEnergySplit h).trans zeroEnergySplit.map_zero

private theorem number_c0_comm : N * c0 = c0 * N + (1 : ℂ) • c0 := by
  rw [one_smul, add_comm]
  apply sub_eq_iff_eq_add.mp
  let lift := Module.End.lTensorAlgHom ℂ Fock Matter
  change lift BcGhostCharge.ghostNumber * lift (BcGhostFock.c 0) -
    lift (BcGhostFock.c 0) * lift BcGhostCharge.ghostNumber = lift (BcGhostFock.c 0)
  rw [← map_mul, ← map_mul, ← map_sub, BcGhostCharge.ghost_number_relations.2.2]

theorem N_total_C_plus : N_total * C_plus - C_plus * N_total = C_plus := by
  have hl := number_map_commutator c0 1 1 0 number_c0_comm number_one_comm
  have hr := number_map_commutator Γ c0 0 1 number_gamma_comm number_c0_comm
  simp only [add_zero, zero_add, one_smul] at hl hr
  rw [C_plus, mul_smul_comm, smul_mul_assoc]
  let c : ClosedEnd := TensorProduct.map c0 1 + TensorProduct.map Γ c0
  change (1 / 2 : ℂ) • (N_total * c) - (1 / 2 : ℂ) • (c * N_total) =
    (1 / 2 : ℂ) • c
  have h : N_total * c - c * N_total = c := by
    dsimp only [c]
    rw [mul_add, add_mul, add_sub_add_comm, hl, hr]
  exact (smul_sub (1 / 2 : ℂ) (N_total * c) (c * N_total)).symm.trans
    (congrArg (fun f : ClosedEnd => (1 / 2 : ℂ) • f) h)

theorem C_plus_degree {g : ℤ} {x : ClosedState} (hx : x ∈ GhostSpace g) :
    C_plus x ∈ GhostSpace (g + 1) :=
  sends_total_degree (by simpa only [Int.cast_one, one_smul] using N_total_C_plus) hx

theorem M_degree {g : ℤ} {x : ClosedState} (hx : x ∈ GhostSpace g) :
    M x ∈ GhostSpace (g + 2) := by
  have h : g + 1 + 1 = g + 2 := by omega
  rw [← h]
  exact (GhostSpace _).add_mem (D_degree (C_plus_degree hx)) (C_plus_degree (D_degree hx))

theorem M_R_degree {g : ℤ} {x : R} (hx : x.val ∈ GhostSpace g) :
    (M_R x).val ∈ GhostSpace (g + 2) :=
  M_degree hx

theorem D_R_degree {g : ℤ} {x : R} (hx : x.val ∈ GhostSpace g) :
    (D_R x).val ∈ GhostSpace (g + 1) :=
  D_degree hx

/-- Degree (g) is carried by the degree (g) and degree (g-1) relative
components of the split. -/
theorem zeroEnergySplit_degree_iff (g : ℤ) (x : EnergySpace 0) :
    x.val ∈ GhostSpace g ↔
      (zeroEnergySplit x).1.val ∈ GhostSpace g ∧
      (zeroEnergySplit x).2.val ∈ GhostSpace (g - 1) := by
  have h : g - 1 + 1 = g := by omega
  constructor
  · intro hx
    have hs := B_plus_degree hx
    have hcs := C_plus_degree hs
    rw [h] at hcs
    exact ⟨(GhostSpace g).sub_mem hx hcs, hs⟩
  · rintro ⟨hr, hs⟩
    have hcs := C_plus_degree hs
    rw [h] at hcs
    have hsum := (GhostSpace g).add_mem hr hcs
    rw [← zeroEnergySplit_symm_apply, zeroEnergySplit.symm_apply_apply] at hsum
    exact hsum

/-- Cycle equations for the native differential in the relative coordinates. -/
theorem zeroEnergy_cycle_iff (x : EnergySpace 0) :
    differential 0 x = 0 ↔
      D_R (zeroEnergySplit x).1 + M_R (zeroEnergySplit x).2 = 0 ∧
      D_R (zeroEnergySplit x).2 = 0 := by
  have h := zeroEnergySplit_differential x
  have hc : coneDifferential (zeroEnergySplit x) =
      (D_R (zeroEnergySplit x).1 + M_R (zeroEnergySplit x).2, -D_R (zeroEnergySplit x).2) :=
    coneDifferential_apply _ _
  rw [hc] at h
  constructor
  · intro hx
    rw [hx, zeroEnergySplit.map_zero] at h
    exact ⟨(congrArg Prod.fst h).symm, neg_eq_zero.mp (congrArg Prod.snd h).symm⟩
  · rintro ⟨hr, hs⟩
    apply zeroEnergySplit.injective
    have hz : zeroEnergySplit (differential 0 x) = ((0 : R), (0 : R)) := by
      simpa only [hr, hs, neg_zero] using h
    rw [zeroEnergySplit.map_zero]
    exact hz

/-- Boundary equations for the native differential in the relative coordinates. -/
theorem zeroEnergy_boundary_iff (x : EnergySpace 0) :
    x ∈ (differential 0).range ↔ ∃ a b : R,
      (zeroEnergySplit x).1 = D_R a + M_R b ∧ (zeroEnergySplit x).2 = -D_R b := by
  constructor
  · rintro ⟨y, rfl⟩
    have h := (zeroEnergySplit_differential y).trans (coneDifferential_apply _ _)
    exact ⟨(zeroEnergySplit y).1, (zeroEnergySplit y).2, congrArg Prod.fst h,
      congrArg Prod.snd h⟩
  · rintro ⟨a, b, ha, hb⟩
    refine ⟨zeroEnergySplit.symm (a, b), zeroEnergySplit.injective ?_⟩
    rw [zeroEnergySplit_differential, zeroEnergySplit.apply_symm_apply, coneDifferential_apply]
    exact Prod.ext ha.symm hb.symm

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedSemirelative
