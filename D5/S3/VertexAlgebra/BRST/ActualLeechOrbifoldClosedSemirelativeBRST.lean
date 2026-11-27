import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeBRST
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Level-matched closed semirelative Leech BRST

The carrier is the algebraic tensor product of the two original chiral BRST
state spaces. The semirelative condition is imposed after taking this tensor.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedSemirelative

open ActualLeechOrbifoldCriticalMatter (Matter matter hyperbolicPlane)
open ActualLeechOrbifoldMatter (Orbifold)
open LatticeGeneratingFieldLocality (Carrier)

local instance : AddCommGroup Matter :=
  TensorProduct.addCommGroup (R := ℂ) (M := Orbifold) (N := Carrier hyperbolicPlane)

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket parity parity_involution)
open BcGhostCharge (charge ghostNumber)
open BcGhostChargeTensor (liftGhost)

local instance : AddCommGroup ComplexState :=
  TensorProduct.addCommGroup (R := ℂ) (M := Matter) (N := Fock)


open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open private number_ket from D5.S3.Quantum.Fermionic.BcGhostCharge
open private b0_square Q_commutes_energy b0_commutes_energy from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRST
open private occupation_sign signedDifferential_square tensor_neg_left from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeBRST
open private reassoc_parity from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes
open private rightLift_tmul from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone

/-- The native bc parity on the original matter–ghost tensor. -/
def Γ : Module.End ℂ ComplexState := liftGhost (M := Matter) parity

theorem gamma_eq_originalParity : Γ = originalParity := by
  apply TensorProduct.ext'
  intro m f
  induction m using TensorProduct.inductionOn with
  | add v w hv hw => simp only [TensorProduct.add_tmul, map_add, hv, hw]
  | tmul v w =>
    apply reassoc.injective
    rw [reassoc_parity]
    simp only [Γ, liftGhost, TensorProduct.map_tmul, LinearMap.id_apply,
      reassoc, TensorProduct.assoc_tmul, rightLift_tmul, LatticeMatterGhostStateField.parity]

theorem gamma_square : Γ * Γ = 1 := by
  let lift := Module.End.lTensorAlgHom ℂ Fock Matter
  change lift parity * lift parity = 1
  rw [← map_mul, parity_involution, map_one]

/-- The chiral number operator in the original ghost-number convention. -/
abbrev N : Module.End ℂ ComplexState := VirasoroBRST.N matter

/-- Homogeneous chiral states of integer ghost number. -/
abbrev ChiralGhostSpace (g : ℤ) := N.eigenspace (g : ℂ)

private def occupationBasis : Module.Basis (Finset ℕ) ℂ Fock := Finsupp.basisSingleOne

private theorem occupationBasis_apply (s : Finset ℕ) : occupationBasis s = ket s := rfl

private def occupationCoordinates : ComplexState ≃ₗ[ℂ] (Finset ℕ →₀ Matter) :=
  TensorProduct.equivFinsuppOfBasisRight occupationBasis

private theorem occupationCoordinates_diagonal
    (f : Module.End ℂ Fock) (w : Finset ℕ → ℂ)
    (hf : ∀ s, f (ket s) = w s • ket s)
    (x : ComplexState) (s : Finset ℕ) :
    occupationCoordinates (liftGhost (M := Matter) f x) s = w s • occupationCoordinates x s := by
  classical
  have h : (Finsupp.lapply s).comp (occupationBasis.repr.toLinearMap.comp f) =
      w s • (Finsupp.lapply s).comp occupationBasis.repr.toLinearMap := by
    apply occupationBasis.ext
    intro t
    change occupationBasis.repr (f (occupationBasis t)) s =
      w s • occupationBasis.repr (occupationBasis t) s
    calc
      _ = occupationBasis.repr (w t • occupationBasis t) s := by
        rw [occupationBasis_apply t, hf]
      _ = _ := by
        rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply]
        split <;> simp_all
  induction x using TensorProduct.inductionOn with
  | tmul m v =>
    have hv := LinearMap.congr_fun h v
    change occupationBasis.repr (f v) s = w s • occupationBasis.repr v s at hv
    simp only [liftGhost, TensorProduct.map_tmul, LinearMap.id_apply, occupationCoordinates,
      TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, hv, smul_assoc]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, smul_add, hx, hy]

private theorem number_coordinates (x : ComplexState) (s : Finset ℕ) :
    occupationCoordinates (N x) s = (charge s : ℂ) • occupationCoordinates x s :=
  occupationCoordinates_diagonal ghostNumber (fun t => (charge t : ℂ)) number_ket x s

private theorem gamma_coordinates (x : ComplexState) (s : Finset ℕ) :
    occupationCoordinates (Γ x) s = (-1 : ℂ) ^ charge s • occupationCoordinates x s :=
  occupationCoordinates_diagonal parity _ (fun t => (parity_ket t).trans
    (congrArg (fun c : ℂ => c • ket t) (occupation_sign t))) x s

/-- Parity of every homogeneous state is the native integer ghost-number sign. -/
theorem gamma_on_degree {g : ℤ} {x : ComplexState} (hx : x ∈ ChiralGhostSpace g) :
    Γ x = (-1 : ℂ) ^ g • x := by
  apply occupationCoordinates.injective
  ext s
  rw [gamma_coordinates, map_smul, Finsupp.smul_apply]
  by_cases hs : charge s = g
  · rw [hs]
  · have h := Module.End.mem_eigenspace_iff.mp hx
    have hc := congrArg (fun y => occupationCoordinates y s) h
    have hz : ((charge s : ℂ) - (g : ℂ)) • occupationCoordinates x s = 0 := by
      simpa only [sub_smul, number_coordinates, map_smul, Finsupp.smul_apply]
        using sub_eq_zero.mpr hc
    have hne : (charge s : ℂ) - (g : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast hs)
    have hz' := congrArg (fun y : Matter => ((charge s : ℂ) - (g : ℂ))⁻¹ • y) hz
    change ((charge s : ℂ) - (g : ℂ))⁻¹ •
      (((charge s : ℂ) - (g : ℂ)) • occupationCoordinates x s) = _ at hz'
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul, smul_zero] at hz'
    rw [hz', smul_zero, smul_zero]

private theorem chiral_degree_spans : (⨆ g, ChiralGhostSpace g) = ⊤ := by
  classical
  apply top_unique
  intro x _
  obtain ⟨b, hb⟩ := TensorProduct.eq_repr_basis_right occupationBasis x
  rw [← hb]
  exact Submodule.sum_mem _ fun s _ =>
    (le_iSup ChiralGhostSpace (charge s)) (Module.End.mem_eigenspace_iff.mpr (by
      change liftGhost (M := Matter) ghostNumber (b s ⊗ₜ[ℂ] occupationBasis s) =
        (charge s : ℂ) • (b s ⊗ₜ[ℂ] occupationBasis s)
      simp only [occupationBasis_apply, liftGhost, TensorProduct.map_tmul, LinearMap.id_apply,
        number_ket, TensorProduct.tmul_smul]))

private theorem number_b0 : N * b0 - b0 * N = -b0 := by
  let lift := Module.End.lTensorAlgHom ℂ Fock Matter
  change lift ghostNumber * lift (BcGhostFock.b 0) -
      lift (BcGhostFock.b 0) * lift ghostNumber = -lift (BcGhostFock.b 0)
  rw [← map_mul, ← map_mul, ← map_sub, BcGhostCharge.ghost_number_relations.2.1]
  exact map_neg lift (BcGhostFock.b 0)

private theorem number_Q : N * Q - Q * N = Q := VirasoroBRST.N_Q matter

private theorem sends_degree
    {A : Module.End ℂ ComplexState} {k : ℤ}
    (hA : N * A - A * N = (k : ℂ) • A) {g : ℤ} {x : ComplexState}
    (hx : x ∈ ChiralGhostSpace g) : A x ∈ ChiralGhostSpace (g + k) := by
  apply Module.End.mem_eigenspace_iff.mpr
  have h := LinearMap.congr_fun hA x
  change N (A x) - A (N x) = (k : ℂ) • A x at h
  rw [Module.End.mem_eigenspace_iff.mp hx, map_smul] at h
  rw [Int.cast_add, add_smul, add_comm]
  exact sub_eq_iff_eq_add.mp h

private theorem chiral_Q_degree {g : ℤ} {x : ComplexState} (hx : x ∈ ChiralGhostSpace g) :
    Q x ∈ ChiralGhostSpace (g + 1) :=
  sends_degree (by simpa only [Int.cast_one, one_smul] using number_Q) hx

private theorem chiral_b0_degree {g : ℤ} {x : ComplexState} (hx : x ∈ ChiralGhostSpace g) :
    b0 x ∈ ChiralGhostSpace (g + -1) :=
  sends_degree (k := -1) (by
    rw [show ((-1 : ℤ) : ℂ) = -1 by norm_num]
    exact number_b0.trans (neg_one_smul ℂ b0).symm) hx

private theorem gamma_anticommutes
    (A : Module.End ℂ ComplexState) (k : ℤ) (hk : (-1 : ℂ) ^ k = -1)
    (hA : ∀ {g : ℤ} {x : ComplexState}, x ∈ ChiralGhostSpace g →
      A x ∈ ChiralGhostSpace (g + k)) : Γ * A = -(A * Γ) := by
  apply eq_neg_of_add_eq_zero_left
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  rw [← chiral_degree_spans]
  apply iSup_le
  intro g x hx
  change Γ (A x) + A (Γ x) = 0
  rw [gamma_on_degree (hA hx), gamma_on_degree hx, map_smul,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), hk, mul_neg_one, neg_smul, neg_add_cancel]

theorem gamma_Q : Γ * Q = -(Q * Γ) :=
  gamma_anticommutes Q 1 (by norm_num) chiral_Q_degree

theorem gamma_b0 : Γ * b0 = -(b0 * Γ) :=
  gamma_anticommutes b0 (-1) (by norm_num) chiral_b0_degree

private theorem chiral_ward : Q * b0 + b0 * Q = E :=
  VirasoroBRST.Q_ward_b matter 0

private theorem gamma_commutes_product (a b : Module.End ℂ ComplexState)
    (ha : Γ * a = -(a * Γ)) (hb : Γ * b = -(b * Γ)) :
    Γ * (a * b) = (a * b) * Γ := by
  calc
    Γ * (a * b) = (Γ * a) * b := by rw [mul_assoc]
    _ = -(a * Γ) * b := congrArg (· * b) ha
    _ = -((a * Γ) * b) := neg_mul (a * Γ) b
    _ = -(a * (Γ * b)) := congrArg Neg.neg (mul_assoc a Γ b)
    _ = -(a * -(b * Γ)) := congrArg (fun t => -(a * t)) hb
    _ = -(-(a * (b * Γ))) := congrArg Neg.neg (mul_neg a (b * Γ))
    _ = a * (b * Γ) := neg_neg _
    _ = (a * b) * Γ := (mul_assoc a b Γ).symm

theorem gamma_E : Γ * E = E * Γ := by
  calc
    Γ * E = Γ * (Q * b0 + b0 * Q) := congrArg (Γ * ·) chiral_ward.symm
    _ = Γ * (Q * b0) + Γ * (b0 * Q) := mul_add _ _ _
    _ = (Q * b0) * Γ + (b0 * Q) * Γ :=
      congrArg₂ (· + ·) (gamma_commutes_product Q b0 gamma_Q gamma_b0)
        (gamma_commutes_product b0 Q gamma_b0 gamma_Q)
    _ = (Q * b0 + b0 * Q) * Γ := (add_mul _ _ _).symm
    _ = E * Γ := congrArg (· * Γ) chiral_ward

/-- The algebraic tensor of the original left and right chiral state spaces. -/
abbrev ClosedState := ComplexState ⊗[ℂ] ComplexState

local instance : AddCommGroup ClosedState :=
  TensorProduct.addCommGroup (R := ℂ) (M := ComplexState) (N := ComplexState)

private local instance (priority := 2000) closedStateAddCommMonoid :
    AddCommMonoid ClosedState := inferInstance

private local instance (priority := 2000) closedStateModule : Module ℂ ClosedState :=
  inferInstance

private abbrev ChiralEnd := Module.End ℂ ComplexState
private abbrev ClosedEnd := Module.End ℂ ClosedState

/-- The right charge is signed by parity of the original left factor. -/
def D : ClosedEnd := TensorProduct.map Q 1 + TensorProduct.map Γ Q

def B_minus : ClosedEnd := TensorProduct.map b0 1 - TensorProduct.map Γ b0
def B_plus : ClosedEnd := TensorProduct.map b0 1 + TensorProduct.map Γ b0
def L_minus : ClosedEnd := TensorProduct.map E 1 - TensorProduct.map 1 E
def L_plus : ClosedEnd := TensorProduct.map E 1 + TensorProduct.map 1 E

private theorem Q_sq : Q * Q = 0 := by simpa only [pow_two] using Q_squared

theorem D_square : D * D = 0 := signedDifferential_square Q Q Γ Q_sq Q_sq gamma_Q

private theorem signed_ward_minus (q : ChiralEnd) (hΓ : Γ * q = -(q * Γ)) :
    (TensorProduct.map q 1 + TensorProduct.map Γ q) * B_minus +
      B_minus * (TensorProduct.map q 1 + TensorProduct.map Γ q) =
    TensorProduct.map (q * b0 + b0 * q) 1 - TensorProduct.map 1 (q * b0 + b0 * q) := by
  simp only [B_minus, add_mul, mul_add, sub_mul, mul_sub, ← TensorProduct.map_mul, one_mul,
    mul_one, gamma_square, hΓ, gamma_b0, tensor_neg_left, TensorProduct.map_add_left,
    TensorProduct.map_add_right]
  abel

theorem D_B_minus : D * B_minus + B_minus * D = L_minus :=
  (signed_ward_minus Q gamma_Q).trans (congrArg
    (fun e : ChiralEnd => TensorProduct.map e 1 - TensorProduct.map 1 e) chiral_ward)

private theorem signed_ward_plus (q : ChiralEnd) (hΓ : Γ * q = -(q * Γ)) :
    (TensorProduct.map q 1 + TensorProduct.map Γ q) * B_plus +
      B_plus * (TensorProduct.map q 1 + TensorProduct.map Γ q) =
    TensorProduct.map (q * b0 + b0 * q) 1 + TensorProduct.map 1 (q * b0 + b0 * q) := by
  simp only [B_plus, add_mul, mul_add, ← TensorProduct.map_mul, one_mul, mul_one, gamma_square,
    hΓ, gamma_b0, tensor_neg_left, TensorProduct.map_add_left, TensorProduct.map_add_right]
  abel

theorem D_B_plus : D * B_plus + B_plus * D = L_plus :=
  (signed_ward_plus Q gamma_Q).trans (congrArg
    (fun e : ChiralEnd => TensorProduct.map e 1 + TensorProduct.map 1 e) chiral_ward)

theorem B_minus_B_plus : B_minus * B_plus + B_plus * B_minus = 0 := by
  simp only [B_minus, B_plus, add_mul, mul_add, sub_mul, mul_sub, ← TensorProduct.map_mul,
    one_mul, mul_one, b0_square, TensorProduct.map_zero_left, TensorProduct.map_zero_right]
  abel

private theorem energy_commutes (a b : ChiralEnd) (ha : a * E = E * a)
    (hb : b * E = E * b) :
    TensorProduct.map a b * TensorProduct.map E 1 =
      TensorProduct.map E 1 * TensorProduct.map a b ∧
    TensorProduct.map a b * TensorProduct.map 1 E =
      TensorProduct.map 1 E * TensorProduct.map a b := by
  simp only [← TensorProduct.map_mul, one_mul, mul_one, ha, hb, and_self]

theorem D_L_minus : D * L_minus = L_minus * D := by
  have hL := energy_commutes Q 1 Q_commutes_energy (by simp)
  have hR := energy_commutes Γ Q gamma_E Q_commutes_energy
  simp only [D, L_minus, add_mul, mul_add, sub_mul, mul_sub, hL.1, hL.2, hR.1, hR.2]
  abel

theorem D_L_plus : D * L_plus = L_plus * D := by
  have hL := energy_commutes Q 1 Q_commutes_energy (by simp)
  have hR := energy_commutes Γ Q gamma_E Q_commutes_energy
  simp only [D, L_plus, add_mul, mul_add, hL.1, hL.2, hR.1, hR.2]
  abel

theorem B_plus_L_minus : B_plus * L_minus = L_minus * B_plus := by
  have hL := energy_commutes b0 1 b0_commutes_energy (by simp)
  have hR := energy_commutes Γ b0 gamma_E b0_commutes_energy
  simp only [B_plus, L_minus, add_mul, mul_add, sub_mul, mul_sub, hL.1, hL.2, hR.1, hR.2]
  abel

theorem B_plus_L_plus : B_plus * L_plus = L_plus * B_plus := by
  have hL := energy_commutes b0 1 b0_commutes_energy (by simp)
  have hR := energy_commutes Γ b0 gamma_E b0_commutes_energy
  simp only [B_plus, L_plus, add_mul, mul_add, hL.1, hL.2, hR.1, hR.2]
  abel

/-- The two semirelative constraints on the original closed states. -/
abbrev Semirelative : Submodule ℂ ClosedState := B_minus.ker ⊓ L_minus.ker

theorem D_mem_semirelative {x : ClosedState} (hx : x ∈ Semirelative) :
    D x ∈ Semirelative := by
  obtain ⟨hb, hl⟩ : B_minus x = 0 ∧ L_minus x = 0 := hx
  have h := LinearMap.congr_fun D_B_minus x
  change D (B_minus x) + B_minus (D x) = L_minus x at h
  have h' := LinearMap.congr_fun D_L_minus x
  change D (L_minus x) = L_minus (D x) at h'
  rw [hb, map_zero, zero_add, hl] at h
  rw [hl, map_zero] at h'
  exact ⟨h, h'.symm⟩

theorem B_plus_mem_semirelative {x : ClosedState} (hx : x ∈ Semirelative) :
    B_plus x ∈ Semirelative := by
  obtain ⟨hb, hl⟩ : B_minus x = 0 ∧ L_minus x = 0 := hx
  have h := LinearMap.congr_fun B_minus_B_plus x
  change B_minus (B_plus x) + B_plus (B_minus x) = 0 at h
  have h' := LinearMap.congr_fun B_plus_L_minus x
  change B_plus (L_minus x) = L_minus (B_plus x) at h'
  rw [hb, map_zero, add_zero] at h
  rw [hl, map_zero] at h'
  exact ⟨h, h'.symm⟩

/-- Semirelative closed strings of prescribed eigenvalue of the sum of chiral energies. -/
def EnergySpace (m : ℂ) : Submodule ℂ ClosedState := Semirelative ⊓ L_plus.eigenspace m

private theorem preserves_total_energy {A : ClosedEnd} (hA : A * L_plus = L_plus * A)
    {m : ℂ} {x : ClosedState} (hx : x ∈ L_plus.eigenspace m) :
    A x ∈ L_plus.eigenspace m := by
  apply Module.End.mem_eigenspace_iff.mpr
  have h := LinearMap.congr_fun hA x
  change A (L_plus x) = L_plus (A x) at h
  rw [← h, Module.End.mem_eigenspace_iff.mp hx, map_smul]

def differential (m : ℂ) : Module.End ℂ (EnergySpace m) :=
  D.restrict (fun _ hx =>
    ⟨D_mem_semirelative hx.1, preserves_total_energy D_L_plus hx.2⟩)

def homotopy (m : ℂ) : Module.End ℂ (EnergySpace m) :=
  m⁻¹ • B_plus.restrict (p := EnergySpace m) (q := EnergySpace m) (fun _ hx =>
    ⟨B_plus_mem_semirelative hx.1, preserves_total_energy B_plus_L_plus hx.2⟩)

theorem differential_square (m : ℂ) : differential m * differential m = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun D_square x.val

/-- On its actual nonzero-energy eigenspace the semirelative complex is contractible. -/
theorem contraction (m : ℂ) (hm : m ≠ 0) :
    differential m * homotopy m + homotopy m * differential m = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change D (m⁻¹ • B_plus x.val) + m⁻¹ • B_plus (D x.val) = x.val
  have h : D (B_plus x.val) + B_plus (D x.val) = L_plus x.val :=
    LinearMap.congr_fun D_B_plus x.val
  rw [map_smul, ← smul_add, h, Module.End.mem_eigenspace_iff.mp x.property.2,
    smul_smul, inv_mul_cancel₀ hm, one_smul]

/-- The literal primitive belongs to the same level-matched semirelative energy space. -/
theorem exact_of_closed (m : ℂ) (hm : m ≠ 0) {x : ClosedState}
    (hx : x ∈ EnergySpace m) (hc : D x = 0) :
    m⁻¹ • B_plus x ∈ EnergySpace m ∧ D (m⁻¹ • B_plus x) = x := by
  let y : EnergySpace m := ⟨x, hx⟩
  refine ⟨(homotopy m y).property, ?_⟩
  have h := congrArg Subtype.val (LinearMap.congr_fun (contraction m hm) y)
  change D (m⁻¹ • B_plus x) + m⁻¹ • B_plus (D x) = x at h
  simpa only [hc, map_zero, smul_zero, add_zero] using h

/-- At nonzero energy the actual cycles coincide with the actual boundaries. -/
theorem boundaries_eq_cycles (m : ℂ) (hm : m ≠ 0) :
    (differential m).range = (differential m).ker := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact LinearMap.congr_fun (differential_square m) x
  · intro x hx
    refine ⟨homotopy m x, ?_⟩
    have h := LinearMap.congr_fun (contraction m hm) x
    change differential m x = 0 at hx
    change differential m (homotopy m x) + homotopy m (differential m x) = x at h
    simpa only [hx, map_zero, add_zero] using h

/-- Total ghost number on the closed algebraic tensor is the sum of chiral numbers. -/
def N_total : ClosedEnd := TensorProduct.map N 1 + TensorProduct.map 1 N

abbrev GhostSpace (g : ℤ) : Submodule ℂ ClosedState := N_total.eigenspace (g : ℂ)

private theorem number_commutes_gamma : N * Γ = Γ * N := by
  apply LinearMap.ext
  intro x
  apply occupationCoordinates.injective
  ext s
  change occupationCoordinates (N (Γ x)) s = occupationCoordinates (Γ (N x)) s
  simp only [number_coordinates, gamma_coordinates, smul_smul]
  rw [mul_comm]

private theorem number_map_commutator (a b : ChiralEnd) (u v : ℂ)
    (ha : N * a = a * N + u • a) (hb : N * b = b * N + v • b) :
    N_total * TensorProduct.map a b - TensorProduct.map a b * N_total =
      (u + v) • TensorProduct.map a b := by
  simp only [N_total, add_mul, mul_add, ← TensorProduct.map_mul, one_mul, mul_one,
    ha, hb, TensorProduct.map_add_left, TensorProduct.map_add_right,
    TensorProduct.map_smul_left, TensorProduct.map_smul_right, add_smul]
  abel

private theorem number_one_comm : N * (1 : ChiralEnd) = 1 * N + (0 : ℂ) • (1 : ChiralEnd) := by
  simp

private theorem number_Q_comm : N * Q = Q * N + (1 : ℂ) • Q := by
  rw [one_smul, add_comm]
  exact sub_eq_iff_eq_add.mp number_Q

private theorem number_b0_comm : N * b0 = b0 * N + (-1 : ℂ) • b0 := by
  calc
    N * b0 = -b0 + b0 * N := sub_eq_iff_eq_add.mp number_b0
    _ = b0 * N + -b0 := add_comm _ _
    _ = b0 * N + (-1 : ℂ) • b0 := congrArg (b0 * N + ·) (neg_one_smul ℂ b0).symm

private theorem number_gamma_comm : N * Γ = Γ * N + (0 : ℂ) • Γ := by
  rw [zero_smul, add_zero, number_commutes_gamma]

theorem N_total_D : N_total * D - D * N_total = D := by
  have hL := number_map_commutator Q 1 1 0 number_Q_comm number_one_comm
  have hR := number_map_commutator Γ Q 0 1 number_gamma_comm number_Q_comm
  simp only [add_zero, zero_add, one_smul] at hL hR
  calc
    _ = (N_total * TensorProduct.map Q 1 - TensorProduct.map Q 1 * N_total) +
        (N_total * TensorProduct.map Γ Q - TensorProduct.map Γ Q * N_total) := by
      simp only [D, add_mul, mul_add]
      abel
    _ = D := by rw [hL, hR]; rfl

theorem N_total_B_plus : N_total * B_plus - B_plus * N_total = -B_plus := by
  have hL := number_map_commutator b0 1 (-1) 0 number_b0_comm number_one_comm
  have hR := number_map_commutator Γ b0 0 (-1) number_gamma_comm number_b0_comm
  simp only [add_zero, zero_add] at hL hR
  calc
    _ = (N_total * TensorProduct.map b0 1 - TensorProduct.map b0 1 * N_total) +
        (N_total * TensorProduct.map Γ b0 - TensorProduct.map Γ b0 * N_total) := by
      simp only [B_plus, add_mul, mul_add]
      abel
    _ = -B_plus := by
      rw [hL, hR, ← smul_add]
      exact neg_one_smul ℂ B_plus

private theorem sends_total_degree
    {A : ClosedEnd} {k : ℤ} (hA : N_total * A - A * N_total = (k : ℂ) • A)
    {g : ℤ} {x : ClosedState} (hx : x ∈ GhostSpace g) : A x ∈ GhostSpace (g + k) := by
  apply Module.End.mem_eigenspace_iff.mpr
  have h := LinearMap.congr_fun hA x
  change N_total (A x) - A (N_total x) = (k : ℂ) • A x at h
  rw [Module.End.mem_eigenspace_iff.mp hx, map_smul] at h
  rw [Int.cast_add, add_smul, add_comm]
  exact sub_eq_iff_eq_add.mp h

theorem D_degree {g : ℤ} {x : ClosedState} (hx : x ∈ GhostSpace g) :
    D x ∈ GhostSpace (g + 1) :=
  sends_total_degree (by simpa only [Int.cast_one, one_smul] using N_total_D) hx

theorem B_plus_degree {g : ℤ} {x : ClosedState} (hx : x ∈ GhostSpace g) :
    B_plus x ∈ GhostSpace (g - 1) := by
  rw [sub_eq_add_neg]
  exact sends_total_degree
    (k := -1) (by
      rw [show ((-1 : ℤ) : ℂ) = -1 by norm_num]
      exact N_total_B_plus.trans (neg_one_smul ℂ B_plus).symm) hx

/-- Every closed homogeneous state at nonzero energy is a boundary with the literal
primitive in ghost degree one lower, subject to both semirelative constraints. -/
theorem exact_of_closed_graded (m : ℂ) (hm : m ≠ 0) {g : ℤ} {x : ClosedState}
    (hx : x ∈ EnergySpace m ⊓ GhostSpace g) (hc : D x = 0) :
    m⁻¹ • B_plus x ∈ EnergySpace m ⊓ GhostSpace (g - 1) ∧
      D (m⁻¹ • B_plus x) = x := by
  obtain ⟨hP, hD⟩ := exact_of_closed m hm hx.1 hc
  exact ⟨⟨hP, (GhostSpace (g - 1)).smul_mem _ (B_plus_degree hx.2)⟩, hD⟩

open D5.S3.HomologicalAlgebra.FinitePerturbation (Boundaries)

local instance (m : ℂ) : AddCommGroup (EnergySpace m) :=
  Submodule.addCommGroup (R := ℂ) (M := ClosedState) (EnergySpace m)

local instance (m : ℂ) : AddCommGroup (differential m).ker :=
  Submodule.addCommGroup (R := ℂ) (M := EnergySpace m) (differential m).ker

/-- The kernel of the restricted differential modulo its actual boundaries. -/
abbrev Cohomology (m : ℂ) :=
  D5.S3.HomologicalAlgebra.FinitePerturbation.Cohomology (differential m) (differential_square m)

theorem cohomology_vanishes (m : ℂ) (hm : m ≠ 0) : Subsingleton (Cohomology m) := by
  suffices h : ∀ x : Cohomology m, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨z, rfl⟩ := (Boundaries (differential m) (differential_square m)).mkQ_surjective x
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have hz : z.val ∈ (differential m).range := (boundaries_eq_cycles m hm).symm ▸ z.property
  obtain ⟨w, hw⟩ := hz
  exact ⟨w, Subtype.ext hw⟩

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedSemirelative
