import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedSemirelativeZeroMomentumOperator

/-! The actual zero-energy semirelative complex at independent plane momenta. -/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedSemirelative

open ActualLeechOrbifoldCriticalMatter (Matter hyperbolicPlane)
open ActualLeechOrbifoldMatter (Orbifold)
open LatticeGeneratingFieldLocality (Carrier Charge)
open LatticeQuartetContraction (State chargeMatter chargeProject)
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock)
open BcGhostChargeTensor (liftGhost)
open ClosedRelative (Shell TotalGhostSpace)

local instance : AddCommGroup Matter :=
  TensorProduct.addCommGroup (R := ℂ) (M := Orbifold) (N := Carrier hyperbolicPlane)

local instance : AddCommGroup ComplexState :=
  TensorProduct.addCommGroup (R := ℂ) (M := Matter) (N := Fock)

local instance : AddCommGroup AssocState :=
  TensorProduct.addCommGroup (R := ℂ) (M := Orbifold) (N := State hyperbolicPlane)

local instance : AddCommGroup ClosedState :=
  TensorProduct.addCommGroup (R := ℂ) (M := ComplexState) (N := ComplexState)

local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup (relativeShell p)

local instance (pL pR : Charge hyperbolicPlane) : AddCommGroup (Shell pL pR) :=
  TensorProduct.addCommGroup (R := ℂ) (M := relativeShell pL) (N := relativeShell pR)

local instance : AddCommGroup (EnergySpace 0) := Submodule.addCommGroup (EnergySpace 0)

open private tensor_sub_left tensor_sub_right span_ghostSpace from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeBRST
open private tensor_prod_zero_iff prod_tensor_zero_iff from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedSemirelativeZeroMomentumOperator
open private mem_ghostSpace from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology

variable (p pL pR : Charge hyperbolicPlane)

/-- Projection onto the actual plane momentum in the original matter–ghost association. -/
def planeProject : Module.End ℂ ComplexState :=
  TensorProduct.map (TensorProduct.map (1 : Module.End ℂ Orbifold) (chargeMatter p))
    (1 : Module.End ℂ Fock)

private theorem reassoc_conj (A : Module.End ℂ ComplexState) (x : ComplexState) :
    ((reassoc.conjAlgEquiv ℂ) A) (reassoc x) = reassoc (A x) := by
  rw [LinearEquiv.conjAlgEquiv_apply (R := ℂ) reassoc A]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem reassoc_planeProject (x : ComplexState) :
    reassoc (planeProject p x) = rightLift (chargeProject p) (reassoc x) := by
  have h : reassoc.toLinearMap.comp (planeProject p) =
      (rightLift (chargeProject p)).comp reassoc.toLinearMap := by
    apply TensorProduct.ext'
    intro m s
    induction m using TensorProduct.inductionOn with
    | tmul v u => rfl
    | add m n hm hn =>
      simp only [LinearMap.comp_apply, TensorProduct.add_tmul, map_add] at hm hn ⊢
      rw [hm, hn]
  exact LinearMap.congr_fun h x

theorem planeProject_mul_self : planeProject p * planeProject p = planeProject p := by
  have h : chargeMatter p * chargeMatter p = chargeMatter p := by
    apply LinearMap.ext
    intro x
    change Finsupp.single p (Finsupp.single p (x p) p) = Finsupp.single p (x p)
    rw [Finsupp.single_eq_same]
  simp only [planeProject, ← TensorProduct.map_mul, one_mul, h]

theorem planeProject_mul_eq_zero {q : Charge hyperbolicPlane} (h : p ≠ q) :
    planeProject p * planeProject q = 0 := by
  have hplane : chargeMatter p * chargeMatter q = 0 := by
    apply LinearMap.ext
    intro x
    change Finsupp.single p (Finsupp.single q (x q) p) = 0
    rw [Finsupp.single_eq_of_ne h, Finsupp.single_zero]
  simp only [planeProject, ← TensorProduct.map_mul, one_mul, hplane,
    TensorProduct.map_zero_right, TensorProduct.map_zero_left]

abbrev leftMomentumProject : Module.End ℂ ClosedState :=
  TensorProduct.map (planeProject pL) 1

abbrev rightMomentumProject : Module.End ℂ ClosedState :=
  TensorProduct.map 1 (planeProject pR)

/-- The simultaneous fixed locus of the two actual plane momentum projectors. -/
def FixedMomentum : Submodule ℂ ClosedState :=
  (leftMomentumProject pL - 1).ker ⊓ (rightMomentumProject pR - 1).ker

theorem mem_fixedMomentum_iff (z : ClosedState) :
    z ∈ FixedMomentum pL pR ↔
      leftMomentumProject pL z = z ∧ rightMomentumProject pR z = z := by
  simp only [FixedMomentum, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero]

/-- The actual joint plane momentum projector. -/
def momentumProject : Module.End ℂ ClosedState :=
  TensorProduct.map (planeProject pL) (planeProject pR)

theorem momentumProject_mul_self :
    momentumProject pL pR * momentumProject pL pR = momentumProject pL pR := by
  rw [momentumProject, ← TensorProduct.map_mul, planeProject_mul_self, planeProject_mul_self]

theorem momentumProject_mul_eq_zero {qL qR : Charge hyperbolicPlane}
    (h : pL ≠ qL ∨ pR ≠ qR) :
    momentumProject pL pR * momentumProject qL qR = 0 := by
  rw [momentumProject, momentumProject, ← TensorProduct.map_mul]
  rcases h with h | h
  · rw [planeProject_mul_eq_zero _ h, TensorProduct.map_zero_left]
  · rw [planeProject_mul_eq_zero _ h, TensorProduct.map_zero_right]

theorem momentumProject_range : (momentumProject pL pR).range = FixedMomentum pL pR := by
  ext z
  rw [mem_fixedMomentum_iff]
  constructor
  · rintro ⟨x, rfl⟩
    have hL : leftMomentumProject pL * momentumProject pL pR = momentumProject pL pR := by
      rw [momentumProject, ← TensorProduct.map_mul, planeProject_mul_self, one_mul]
    have hR : rightMomentumProject pR * momentumProject pL pR = momentumProject pL pR := by
      rw [momentumProject, ← TensorProduct.map_mul, planeProject_mul_self, one_mul]
    exact ⟨LinearMap.congr_fun hL x, LinearMap.congr_fun hR x⟩
  · rintro ⟨hL, hR⟩
    have h : leftMomentumProject pL * rightMomentumProject pR = momentumProject pL pR := by
      rw [momentumProject, ← TensorProduct.map_mul, mul_one, one_mul]
    exact ⟨z, (LinearMap.congr_fun h z).symm.trans (by rwa [Module.End.mul_apply, hR])⟩

/-- The original-association inclusion of the literal chiral relative shell. -/
def momentumChiralInclusion : relativeShell p →ₗ[ℂ] ComplexState :=
  reassoc.symm.toLinearMap.comp (relativeShell p).subtype

theorem momentumChiralInclusion_injective : Function.Injective (momentumChiralInclusion p) :=
  reassoc.symm.injective.comp Subtype.val_injective

/-- The literal tensor inclusion into the native closed states. -/
def momentumShellInclusion : Shell pL pR →ₗ[ℂ] ClosedState :=
  TensorProduct.map (momentumChiralInclusion pL) (momentumChiralInclusion pR)

theorem momentumShellInclusion_tmul (x : relativeShell pL) (y : relativeShell pR) :
    momentumShellInclusion pL pR (x ⊗ₜ[ℂ] y) =
      reassoc.symm x.val ⊗ₜ[ℂ] reassoc.symm y.val := TensorProduct.map_tmul _ _ _ _

theorem momentumShellInclusion_injective : Function.Injective (momentumShellInclusion pL pR) :=
  TensorProduct.map_injective_of_flat_flat _ _
    (momentumChiralInclusion_injective pL) (momentumChiralInclusion_injective pR)

theorem reassoc_mem_relativeShell_iff (x : ComplexState) :
    reassoc x ∈ relativeShell p ↔ planeProject p x = x ∧ b0 x = 0 ∧ E x = 0 := by
  rw [mem_relativeShell_iff, ← reassoc_planeProject, show assocB0 (reassoc x) =
    reassoc (b0 x) from reassoc_conj b0 x, show assocE (reassoc x) =
    reassoc (E x) from reassoc_conj E x]
  simp only [reassoc.injective.eq_iff, reassoc.map_eq_zero_iff]

private abbrev MomentumConstraints := ComplexState × (ComplexState × ComplexState)

private def momentumConstraints : ComplexState →ₗ[ℂ] MomentumConstraints :=
  (planeProject p - 1).prod (b0.prod E)

private theorem momentumConstraints_exact :
    Function.Exact (momentumChiralInclusion p) (momentumConstraints p) := by
  intro x
  change (planeProject p x - x, (b0 x, E x)) = (0, (0, 0)) ↔ _
  simp only [Prod.mk.injEq, sub_eq_zero, Set.mem_range, ← reassoc_mem_relativeShell_iff]
  constructor
  · intro hx
    exact ⟨⟨reassoc x, hx⟩, reassoc.symm_apply_apply x⟩
  · rintro ⟨y, rfl⟩
    change reassoc (reassoc.symm y.val) ∈ relativeShell p
    rw [reassoc.apply_symm_apply]
    exact y.property

/-- The native image is precisely the intersection of the four literal kernels
with the two projector fixed loci. -/
theorem mem_momentumShellInclusion_range_iff (z : ClosedState) :
    z ∈ (momentumShellInclusion pL pR).range ↔ z ∈ R ∧ z ∈ FixedMomentum pL pR := by
  have hleft (z : ClosedState) : (momentumConstraints pL).rTensor ComplexState z = 0 ↔
      leftMomentumProject pL z = z ∧
      TensorProduct.map b0 (1 : Module.End ℂ ComplexState) z = 0 ∧
      TensorProduct.map E (1 : Module.End ℂ ComplexState) z = 0 := by
    rw [momentumConstraints, tensor_prod_zero_iff, tensor_prod_zero_iff]
    change TensorProduct.map (planeProject pL - 1) 1 z = 0 ∧ _ ↔ _
    simp only [tensor_sub_left, TensorProduct.map_one, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
    rfl
  have hright (z : ClosedState) : (momentumConstraints pR).lTensor ComplexState z = 0 ↔
      rightMomentumProject pR z = z ∧
      TensorProduct.map (1 : Module.End ℂ ComplexState) b0 z = 0 ∧
      TensorProduct.map (1 : Module.End ℂ ComplexState) E z = 0 := by
    rw [momentumConstraints, prod_tensor_zero_iff, prod_tensor_zero_iff]
    change TensorProduct.map 1 (planeProject pR - 1) z = 0 ∧ _ ↔ _
    simp only [tensor_sub_right, TensorProduct.map_one, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
    rfl
  have hl := Module.Flat.rTensor_exact ComplexState (momentumConstraints_exact pL) z
  have hr := Module.Flat.lTensor_exact (relativeShell pL) (momentumConstraints_exact pR)
  have hcomp : ((momentumConstraints pR).lTensor ComplexState).comp
      ((momentumChiralInclusion pL).rTensor ComplexState) =
      ((momentumChiralInclusion pL).rTensor MomentumConstraints).comp
        ((momentumConstraints pR).lTensor (relativeShell pL)) :=
    TensorProduct.ext' fun _ _ => rfl
  have hinj : Function.Injective ((momentumChiralInclusion pL).rTensor MomentumConstraints) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (momentumChiralInclusion_injective pL)
  have hmap : momentumShellInclusion pL pR =
      ((momentumChiralInclusion pL).rTensor ComplexState).comp
        ((momentumChiralInclusion pR).lTensor (relativeShell pL)) :=
    TensorProduct.ext' fun _ _ => rfl
  rw [mem_R_iff, mem_fixedMomentum_iff]
  constructor
  · rintro ⟨x, rfl⟩
    let y := (momentumChiralInclusion pR).lTensor (relativeShell pL) x
    have hR := (hr y).mpr ⟨x, rfl⟩
    have hx : momentumShellInclusion pL pR x = (momentumChiralInclusion pL).rTensor ComplexState y :=
      LinearMap.congr_fun hmap x
    have left := (hleft _).mp (hl.mpr ⟨y, hx.symm⟩)
    have right := (hright (momentumShellInclusion pL pR x)).mp (by
      rw [hx, ← LinearMap.comp_apply, hcomp, LinearMap.comp_apply, hR, map_zero])
    exact ⟨⟨left.2.1, right.2.1, left.2.2, right.2.2⟩, left.1, right.1⟩
  · rintro ⟨⟨hbL, hbR, heL, heR⟩, hpL, hpR⟩
    have hzR := (hright z).mpr ⟨hpR, hbR, heR⟩
    obtain ⟨y, hy⟩ := hl.mp ((hleft z).mpr ⟨hpL, hbL, heL⟩)
    have hyR : (momentumConstraints pR).lTensor (relativeShell pL) y = 0 := by
      apply ((momentumChiralInclusion pL).rTensor MomentumConstraints).map_eq_zero_iff hinj |>.mp
      change (((momentumChiralInclusion pL).rTensor MomentumConstraints).comp
        ((momentumConstraints pR).lTensor (relativeShell pL))) y = 0
      rw [← hcomp, LinearMap.comp_apply, hy]
      exact hzR
    obtain ⟨x, hx⟩ := (hr y).mp hyR
    exact ⟨x, by rw [hmap, LinearMap.comp_apply, hx, hy]⟩

/-- The same native tensor inclusion with its double-relative codomain. -/
def momentumShellToR : Shell pL pR →ₗ[ℂ] R :=
  (momentumShellInclusion pL pR).codRestrict R fun z =>
    ((mem_momentumShellInclusion_range_iff pL pR _).mp ⟨z, rfl⟩).1

theorem momentumShellToR_injective : Function.Injective (momentumShellToR pL pR) :=
  fun _ _ h => momentumShellInclusion_injective pL pR (congrArg Subtype.val h)

theorem gamma_momentumChiralInclusion (x : relativeShell p) :
    Γ (momentumChiralInclusion p x) = momentumChiralInclusion p (ClosedRelative.ghostParity p x) := by
  apply reassoc.injective
  rw [gamma_eq_originalParity]
  change reassoc (originalParity (reassoc.symm x.val)) =
    reassoc (reassoc.symm (ClosedRelative.ghostParity p x).val)
  rw [reassoc.apply_symm_apply, ClosedRelative.ghostParity_original]

private theorem Q_momentumChiralInclusion (x : relativeShell p) :
    Q (momentumChiralInclusion p x) = momentumChiralInclusion p (relativeQ planeFrame planeBasis p x) := by
  apply reassoc.injective
  change reassoc (Q (reassoc.symm x.val)) =
    reassoc (reassoc.symm (relativeQ planeFrame planeBasis p x).val)
  rw [reassoc.apply_symm_apply]
  exact (reassoc_conj Q (reassoc.symm x.val)).symm.trans
    (congrArg assocQ (reassoc.apply_symm_apply x.val))

theorem D_R_momentumShellToR (z : Shell pL pR) :
    D_R (momentumShellToR pL pR z) =
      momentumShellToR pL pR (ClosedRelative.differential pL pR z) := by
  apply Subtype.ext
  change D (momentumShellInclusion pL pR z) =
    momentumShellInclusion pL pR (ClosedRelative.differential pL pR z)
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    change Q (momentumChiralInclusion pL x) ⊗ₜ[ℂ] momentumChiralInclusion pR y +
      Γ (momentumChiralInclusion pL x) ⊗ₜ[ℂ] Q (momentumChiralInclusion pR y) =
      momentumShellInclusion pL pR
        (relativeQ planeFrame planeBasis pL x ⊗ₜ[ℂ] y +
          ClosedRelative.ghostParity pL x ⊗ₜ[ℂ] relativeQ planeFrame planeBasis pR y)
    rw [Q_momentumChiralInclusion, Q_momentumChiralInclusion, gamma_momentumChiralInclusion,
      map_add]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem momentumChiralInclusion_ghost_iff (g : ℤ) (x : relativeShell p) :
    momentumChiralInclusion p x ∈ ChiralGhostSpace g ↔
      x ∈ RelativeCohomology.GhostSpace p g := by
  rw [Module.End.mem_eigenspace_iff, mem_ghostSpace]
  have hx : reassoc (momentumChiralInclusion p x) = x.val := reassoc.apply_symm_apply x.val
  rw [← reassoc.injective.eq_iff, ← reassoc_conj N, map_smul, hx]

private theorem tmul_mem_closedGhost {a b : ℤ} {x y : ComplexState}
    (hx : x ∈ ChiralGhostSpace a) (hy : y ∈ ChiralGhostSpace b) :
    x ⊗ₜ[ℂ] y ∈ GhostSpace (a + b) := by
  have hx' := Module.End.mem_eigenspace_iff.mp hx
  have hy' := Module.End.mem_eigenspace_iff.mp hy
  rw [Module.End.mem_eigenspace_iff]
  change N x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] N y = _
  rw [hx', hy', ← TensorProduct.smul_tmul' (R := ℂ) (a : ℂ) x y,
    TensorProduct.tmul_smul (b : ℂ) x y, ← add_smul, Int.cast_add]

private theorem totalGhostSpace_le_comap (g : ℤ) :
    TotalGhostSpace pL pR g ≤ (GhostSpace g).comap (momentumShellInclusion pL pR) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, b, x, y, hx, hy, rfl, rfl⟩
  change momentumShellInclusion pL pR (x ⊗ₜ[ℂ] y) ∈ GhostSpace (a + b)
  rw [show momentumShellInclusion pL pR (x ⊗ₜ[ℂ] y) =
    momentumChiralInclusion pL x ⊗ₜ[ℂ] momentumChiralInclusion pR y from
    TensorProduct.map_tmul _ _ _ _]
  exact tmul_mem_closedGhost ((momentumChiralInclusion_ghost_iff pL a x).mpr hx)
    ((momentumChiralInclusion_ghost_iff pR b y).mpr hy)

/-- The existing total-degree submodules span the tensor of the native chiral shells. -/
theorem totalGhostSpace_iSup :
    (⨆ g, TotalGhostSpace pL pR g) = ⊤ := by
  let T := ⨆ g, TotalGhostSpace pL pR g
  let mk := TensorProduct.mk ℂ (relativeShell pL) (relativeShell pR)
  have right (a : ℤ) (x : relativeShell pL) (hx : x ∈ RelativeCohomology.GhostSpace pL a)
      (y : relativeShell pR) : x ⊗ₜ[ℂ] y ∈ T := by
    have h : (⨆ b, RelativeCohomology.GhostSpace pR b) ≤ T.comap (mk x) :=
      iSup_le fun b z hz => (le_iSup (TotalGhostSpace pL pR) (a + b))
        (Submodule.subset_span ⟨a, b, x, z, hx, hz, rfl, rfl⟩)
    rw [span_ghostSpace planeFrame planeBasis pR] at h
    exact h (Submodule.mem_top : y ∈ ⊤)
  have all_tmul (x : relativeShell pL) (y : relativeShell pR) : x ⊗ₜ[ℂ] y ∈ T := by
    have h : (⨆ a, RelativeCohomology.GhostSpace pL a) ≤ T.comap (mk.flip y) :=
      iSup_le fun a z hz => right a z hz y
    rw [span_ghostSpace planeFrame planeBasis pL] at h
    exact h (Submodule.mem_top : x ∈ ⊤)
  apply top_unique
  intro z hz
  clear hz
  change z ∈ T
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact all_tmul x y
  | add x y hx hy => exact T.add_mem hx hy

/-- The existing total relative ghost submodule is exactly the pullback of the
actual total ghost-number eigenspace. -/
theorem momentumShellInclusion_ghost_iff (g : ℤ) (z : Shell pL pR) :
    momentumShellInclusion pL pR z ∈ GhostSpace g ↔ z ∈ TotalGhostSpace pL pR g := by
  let incl := momentumShellInclusion pL pR
  let T := TotalGhostSpace pL pR
  constructor
  · intro hz
    have hz' : z ∈ T g ⊔ ⨆ (a) (_ : a ≠ g), T a := by
      rw [← iSup_split_single, totalGhostSpace_iSup]
      exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hz'
    have hx' : incl x ∈ GhostSpace g := totalGhostSpace_le_comap pL pR g hx
    have hy' : incl y ∈ ⨆ (a) (_ : a ≠ g), GhostSpace a := by
      have h : (⨆ (a) (_ : a ≠ g), T a) ≤
          (⨆ (a) (_ : a ≠ g), GhostSpace a).comap incl := by
        refine iSup_le fun a => iSup_le fun ha z' hz' => ?_
        exact (le_iSup₂ (f := fun b (_ : b ≠ g) => GhostSpace b) a ha)
          (totalGhostSpace_le_comap pL pR a hz')
      exact h hy
    have hy_g : incl y ∈ GhostSpace g := by
      have h := congrArg incl hxy
      rw [map_add] at h
      have hy_eq : incl y = incl z - incl x := by
        rw [← h]
        abel
      rw [hy_eq]
      exact (GhostSpace g).sub_mem hz hx'
    have hcast : Function.Injective (fun a : ℤ => (a : ℂ)) := Int.cast_injective
    have hdisj := (N_total.eigenspaces_iSupIndep.comp hcast) g
    have hy_zero := Submodule.disjoint_def.mp hdisj (incl y) hy_g hy'
    have hzero : y = 0 := (momentumShellInclusion_injective pL pR)
      (hy_zero.trans (map_zero incl).symm)
    rw [hzero, add_zero] at hxy
    exact hxy ▸ hx
  · intro hz
    exact totalGhostSpace_le_comap pL pR g hz

open private b0_c0 c0_commutes_energy from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedSemirelativeZeroEnergyCone
open private Q_commutes_energy from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRST

private theorem planeProject_ghost_comm (a : Module.End ℂ Fock) :
    planeProject p * liftGhost (M := Matter) a = liftGhost (M := Matter) a * planeProject p := by
  simp only [planeProject, liftGhost, ← TensorProduct.map_mul, one_mul, mul_one]
  rfl

private theorem momentumProject_signed_comm (a : Module.End ℂ ComplexState)
    (hL : planeProject pL * a = a * planeProject pL)
    (hR : planeProject pR * a = a * planeProject pR) :
    let T := TensorProduct.map a (1 : Module.End ℂ ComplexState) + TensorProduct.map Γ a
    momentumProject pL pR * T = T * momentumProject pL pR := by
  have hg : planeProject pL * Γ = Γ * planeProject pL :=
    planeProject_ghost_comm pL CountableOccupationFock.parity
  simp only [momentumProject, mul_add, add_mul, ← TensorProduct.map_mul, one_mul, mul_one,
    hL, hR, hg]

private theorem fixedMomentum_of_comm (a : Module.End ℂ ClosedState)
    (h : momentumProject pL pR * a = a * momentumProject pL pR)
    {z : ClosedState} (hz : z ∈ FixedMomentum pL pR) : a z ∈ FixedMomentum pL pR := by
  rw [← momentumProject_range] at hz ⊢
  obtain ⟨y, rfl⟩ := hz
  exact ⟨a y, LinearMap.congr_fun h y⟩

theorem B_plus_mem_fixedMomentum {z : ClosedState} (hz : z ∈ FixedMomentum pL pR) :
    B_plus z ∈ FixedMomentum pL pR :=
  fixedMomentum_of_comm pL pR B_plus (momentumProject_signed_comm pL pR b0
    (planeProject_ghost_comm pL (BcGhostFock.b 0))
    (planeProject_ghost_comm pR (BcGhostFock.b 0))) hz

theorem C_plus_mem_fixedMomentum {z : ClosedState} (hz : z ∈ FixedMomentum pL pR) :
    C_plus z ∈ FixedMomentum pL pR := by
  have hc := momentumProject_signed_comm pL pR c0
    (planeProject_ghost_comm pL (BcGhostFock.c 0))
    (planeProject_ghost_comm pR (BcGhostFock.c 0))
  apply fixedMomentum_of_comm pL pR C_plus _ hz
  rw [C_plus, mul_smul_comm, smul_mul_assoc, hc]

/-- The native splitting preserves each of the two fixed momentum conditions
together, in both directions. -/
theorem zeroEnergySplit_fixedMomentum_iff (z : EnergySpace 0) :
    z.val ∈ FixedMomentum pL pR ↔
      (zeroEnergySplit z).1.val ∈ FixedMomentum pL pR ∧
      (zeroEnergySplit z).2.val ∈ FixedMomentum pL pR := by
  constructor
  · intro hz
    obtain ⟨hfirst, hsecond⟩ := zeroEnergySplit_apply z
    have hb := B_plus_mem_fixedMomentum pL pR hz
    rw [hfirst, hsecond]
    exact ⟨(FixedMomentum pL pR).sub_mem hz (C_plus_mem_fixedMomentum pL pR hb), hb⟩
  · rintro ⟨hfirst, hsecond⟩
    have hsum := (FixedMomentum pL pR).add_mem hfirst (C_plus_mem_fixedMomentum pL pR hsecond)
    rwa [← zeroEnergySplit_symm_apply, zeroEnergySplit.symm_apply_apply] at hsum

/-- The two native cone coordinates map to the actual semirelative states. -/
def momentumConeInclusion : Shell pL pR × Shell pL pR →ₗ[ℂ] EnergySpace 0 :=
  zeroEnergySplit.symm.toLinearMap.comp ((momentumShellToR pL pR).prodMap (momentumShellToR pL pR))

theorem momentumConeInclusion_val (x y : Shell pL pR) :
    (momentumConeInclusion pL pR (x, y)).val =
      momentumShellInclusion pL pR x + C_plus (momentumShellInclusion pL pR y) :=
  zeroEnergySplit_symm_apply _

theorem zeroEnergySplit_momentumConeInclusion (x y : Shell pL pR) :
    zeroEnergySplit (momentumConeInclusion pL pR (x, y)) =
      (momentumShellToR pL pR x, momentumShellToR pL pR y) :=
  zeroEnergySplit.apply_symm_apply _

theorem momentumConeInclusion_injective : Function.Injective (momentumConeInclusion pL pR) := by
  intro x y h
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  have hs := congrArg zeroEnergySplit h
  rw [zeroEnergySplit_momentumConeInclusion, zeroEnergySplit_momentumConeInclusion] at hs
  exact Prod.ext (momentumShellToR_injective pL pR (congrArg Prod.fst hs))
    (momentumShellToR_injective pL pR (congrArg Prod.snd hs))

theorem mem_momentumConeInclusion_range_iff (z : EnergySpace 0) :
    z ∈ (momentumConeInclusion pL pR).range ↔ z.val ∈ FixedMomentum pL pR := by
  rw [zeroEnergySplit_fixedMomentum_iff pL pR]
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩
    rw [zeroEnergySplit_momentumConeInclusion]
    exact ⟨((mem_momentumShellInclusion_range_iff pL pR _).mp ⟨x, rfl⟩).2,
      ((mem_momentumShellInclusion_range_iff pL pR _).mp ⟨y, rfl⟩).2⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨x, hx'⟩ := (mem_momentumShellInclusion_range_iff pL pR _).mpr
      ⟨(zeroEnergySplit z).1.property, hx⟩
    obtain ⟨y, hy'⟩ := (mem_momentumShellInclusion_range_iff pL pR _).mpr
      ⟨(zeroEnergySplit z).2.property, hy⟩
    refine ⟨(x, y), zeroEnergySplit.injective ?_⟩
    rw [zeroEnergySplit_momentumConeInclusion]
    exact Prod.ext (Subtype.ext hx') (Subtype.ext hy')

/-- The actual momentum sector of the native zero-energy semirelative space. -/
def MomentumEnergySpace : Submodule ℂ (EnergySpace 0) :=
  (FixedMomentum pL pR).comap (EnergySpace 0).subtype

theorem momentumConeInclusion_range :
    (momentumConeInclusion pL pR).range = MomentumEnergySpace pL pR :=
  Submodule.ext (mem_momentumConeInclusion_range_iff pL pR)

theorem momentumConeInclusion_ghost_iff (g : ℤ) (x y : Shell pL pR) :
    (momentumConeInclusion pL pR (x, y)).val ∈ GhostSpace g ↔
      x ∈ TotalGhostSpace pL pR g ∧ y ∈ TotalGhostSpace pL pR (g - 1) := by
  rw [zeroEnergySplit_degree_iff, zeroEnergySplit_momentumConeInclusion]
  change momentumShellInclusion pL pR x ∈ GhostSpace g ∧
    momentumShellInclusion pL pR y ∈ GhostSpace (g - 1) ↔ _
  rw [momentumShellInclusion_ghost_iff, momentumShellInclusion_ghost_iff]

/-- The literal grade-`g` cone has relative grades `g` and `g - 1`. -/
theorem momentumCone_graded_range (g : ℤ) :
    ((TotalGhostSpace pL pR g).prod (TotalGhostSpace pL pR (g - 1))).map
      (momentumConeInclusion pL pR) =
        MomentumEnergySpace pL pR ⊓ (GhostSpace g).comap (EnergySpace 0).subtype := by
  ext z
  constructor
  · rintro ⟨⟨x, y⟩, hxy, rfl⟩
    exact ⟨(mem_momentumConeInclusion_range_iff pL pR _).mp ⟨(x, y), rfl⟩,
      (momentumConeInclusion_ghost_iff pL pR g x y).mpr hxy⟩
  · rintro ⟨hp, hg⟩
    obtain ⟨⟨x, y⟩, rfl⟩ := (mem_momentumConeInclusion_range_iff pL pR _).mpr hp
    exact ⟨(x, y), (momentumConeInclusion_ghost_iff pL pR g x y).mp hg, rfl⟩

private theorem chiralInclusion_constraints (x : relativeShell p) :
    planeProject p (momentumChiralInclusion p x) = momentumChiralInclusion p x ∧
      b0 (momentumChiralInclusion p x) = 0 ∧ E (momentumChiralInclusion p x) = 0 := by
  apply (reassoc_mem_relativeShell_iff p _).mp
  change reassoc (reassoc.symm x.val) ∈ relativeShell p
  rw [reassoc.apply_symm_apply]
  exact x.property

private theorem R0_preserves_chiralShell (x : relativeShell p) :
    reassoc (R0 (momentumChiralInclusion p x)) ∈ relativeShell p := by
  let z := momentumChiralInclusion p x
  obtain ⟨hp, hb, he⟩ := chiralInclusion_constraints p x
  have hbq : b0 (Q z) = 0 := by
    change b0 (Q (momentumChiralInclusion p x)) = 0
    rw [Q_momentumChiralInclusion]
    exact (chiralInclusion_constraints p _).2.1
  have heq : E (Q z) = 0 := by
    change E (Q (momentumChiralInclusion p x)) = 0
    rw [Q_momentumChiralInclusion]
    exact (chiralInclusion_constraints p _).2.2
  have hcE (v : ComplexState) : E (c0 v) = c0 (E v) :=
    LinearMap.congr_fun c0_commutes_energy.symm v
  have hqE (v : ComplexState) : E (Q v) = Q (E v) :=
    LinearMap.congr_fun Q_commutes_energy.symm v
  have hb_c (v : ComplexState) (hv : b0 v = 0) : b0 (c0 v) = v := by
    have h := LinearMap.congr_fun b0_c0 v
    simpa only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply,
      hv, map_zero, add_zero] using h
  have hc_ward : R0 z = Q (c0 z) + c0 (Q z) :=
    (LinearMap.congr_fun (VirasoroBRST.Q_ward_c ActualLeechOrbifoldCriticalMatter.matter 0) z).symm
  apply (reassoc_mem_relativeShell_iff p _).mpr
  refine ⟨?_, ?_, ?_⟩
  · have h := planeProject_ghost_comm p (BcGhostBRST.R 0)
    change planeProject p * R0 = R0 * planeProject p at h
    exact (LinearMap.congr_fun h z).trans (congrArg R0 hp)
  · have h := LinearMap.congr_fun
        (VirasoroBRST.Q_ward_b ActualLeechOrbifoldCriticalMatter.matter 0) (c0 z)
    change Q (b0 (c0 z)) + b0 (Q (c0 z)) = E (c0 z) at h
    rw [hb_c z hb, hcE, he, map_zero] at h
    rw [hc_ward, map_add, hb_c (Q z) hbq, add_comm]
    exact h
  · rw [hc_ward, map_add, hqE, hcE, hcE, he, heq, map_zero, map_zero, add_zero]

/-- The restriction of the actual chiral ghost Ward operator to its native relative shell. -/
def momentumChiralWard : Module.End ℂ (relativeShell p) :=
  ((reassoc.conjAlgEquiv ℂ) R0).restrict fun x hx => by
    have h := R0_preserves_chiralShell p ⟨x, hx⟩
    have he := reassoc_conj R0 (reassoc.symm x)
    rw [reassoc.apply_symm_apply] at he
    rw [he]
    exact h

theorem R0_momentumChiralInclusion (x : relativeShell p) :
    R0 (momentumChiralInclusion p x) =
      momentumChiralInclusion p (momentumChiralWard p x) := by
  apply reassoc.injective
  change reassoc (R0 (reassoc.symm x.val)) =
    reassoc (reassoc.symm (((reassoc.conjAlgEquiv ℂ) R0) x.val))
  rw [reassoc.apply_symm_apply]
  exact (reassoc_conj R0 (reassoc.symm x.val)).symm.trans
    (congrArg ((reassoc.conjAlgEquiv ℂ) R0) (reassoc.apply_symm_apply x.val))

/-- The native cone connecting map, as a sum of the two even chiral Ward maps. -/
def momentumM : Module.End ℂ (Shell pL pR) :=
  (1 / 2 : ℂ) • (TensorProduct.map (momentumChiralWard pL) 1 +
    TensorProduct.map 1 (momentumChiralWard pR))

theorem M_momentumShellInclusion (z : Shell pL pR) :
    M (momentumShellInclusion pL pR z) =
      momentumShellInclusion pL pR (momentumM pL pR z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [M_eq_tensor_R0, momentumM]
    change (1 / 2 : ℂ) •
      (R0 (momentumChiralInclusion pL x) ⊗ₜ[ℂ] momentumChiralInclusion pR y +
        momentumChiralInclusion pL x ⊗ₜ[ℂ] R0 (momentumChiralInclusion pR y)) =
      momentumShellInclusion pL pR ((1 / 2 : ℂ) •
        (momentumChiralWard pL x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] momentumChiralWard pR y))
    rw [R0_momentumChiralInclusion, R0_momentumChiralInclusion, map_smul, map_add]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem M_R_momentumShellToR (z : Shell pL pR) :
    M_R (momentumShellToR pL pR z) = momentumShellToR pL pR (momentumM pL pR z) :=
  Subtype.ext (M_momentumShellInclusion pL pR z)

theorem momentumM_degree (g : ℤ) {z : Shell pL pR} (hz : z ∈ TotalGhostSpace pL pR g) :
    momentumM pL pR z ∈ TotalGhostSpace pL pR (g + 2) := by
  rw [← momentumShellInclusion_ghost_iff, ← M_momentumShellInclusion]
  exact M_degree ((momentumShellInclusion_ghost_iff pL pR g z).mpr hz)

/-- The actual semirelative differential in the two native momentum-shell coordinates. -/
def momentumConeDifferential : Module.End ℂ (Shell pL pR × Shell pL pR) :=
  (((ClosedRelative.differential pL pR).comp (LinearMap.fst ℂ _ _)) +
    ((momentumM pL pR).comp (LinearMap.snd ℂ _ _))).prod
    (-((ClosedRelative.differential pL pR).comp (LinearMap.snd ℂ _ _)))

theorem momentumConeDifferential_apply (x y : Shell pL pR) :
    momentumConeDifferential pL pR (x, y) =
      (ClosedRelative.differential pL pR x + momentumM pL pR y,
        -ClosedRelative.differential pL pR y) := rfl

theorem momentumConeDifferential_degree (g : ℤ) {x y : Shell pL pR}
    (hx : x ∈ TotalGhostSpace pL pR g) (hy : y ∈ TotalGhostSpace pL pR (g - 1)) :
    momentumConeDifferential pL pR (x, y) ∈
      (TotalGhostSpace pL pR (g + 1)).prod (TotalGhostSpace pL pR g) := by
  rw [momentumConeDifferential_apply]
  have hM := momentumM_degree pL pR (g - 1) hy
  have hD := ClosedRelative.differential_degree pL pR (g - 1) y hy
  rw [show g - 1 + 2 = g + 1 by omega] at hM
  rw [sub_add_cancel] at hD
  exact ⟨(TotalGhostSpace pL pR (g + 1)).add_mem
    (ClosedRelative.differential_degree pL pR g x hx) hM,
    (TotalGhostSpace pL pR g).neg_mem hD⟩

theorem differential_momentumConeInclusion (x y : Shell pL pR) :
    differential 0 (momentumConeInclusion pL pR (x, y)) =
      momentumConeInclusion pL pR (momentumConeDifferential pL pR (x, y)) := by
  apply zeroEnergySplit.injective
  rw [zeroEnergySplit_differential, zeroEnergySplit_momentumConeInclusion,
    momentumConeDifferential_apply, zeroEnergySplit_momentumConeInclusion,
    coneDifferential_apply, D_R_momentumShellToR, D_R_momentumShellToR, M_R_momentumShellToR]
  exact Prod.ext (map_add (momentumShellToR pL pR) _ _).symm
    (map_neg (momentumShellToR pL pR) _).symm

theorem momentumConeDifferential_square :
    momentumConeDifferential pL pR * momentumConeDifferential pL pR = 0 := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply momentumConeInclusion_injective pL pR
  change momentumConeInclusion pL pR (momentumConeDifferential pL pR
    (momentumConeDifferential pL pR (x, y))) = momentumConeInclusion pL pR 0
  have h (z : Shell pL pR × Shell pL pR) :
      differential 0 (momentumConeInclusion pL pR z) =
        momentumConeInclusion pL pR (momentumConeDifferential pL pR z) :=
    differential_momentumConeInclusion pL pR z.1 z.2
  rw [← h, ← h, map_zero]
  exact LinearMap.congr_fun (differential_square 0) (momentumConeInclusion pL pR (x, y))

theorem differential_mem_momentumEnergySpace {x : EnergySpace 0}
    (hx : x ∈ MomentumEnergySpace pL pR) : differential 0 x ∈ MomentumEnergySpace pL pR := by
  rw [← momentumConeInclusion_range] at hx ⊢
  obtain ⟨⟨z, w⟩, rfl⟩ := hx
  exact ⟨_, (differential_momentumConeInclusion pL pR z w).symm⟩

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedSemirelative
