import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeNonzeroMomentum
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedSemirelativeMomentumShellBridge

/-! The two-nonzero-momentum semirelative BRST calculation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedSemirelative

open ActualLeechOrbifoldCriticalMatter (Matter hyperbolicPlane)
open ActualLeechOrbifoldMatter (Orbifold)
open LatticeGeneratingFieldLocality (Carrier Charge)
open LatticeLightConeCoordinates (NullFrame)
open LatticeQuartetContraction (State)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (Fock)
open RelativeCohomology (OrbifoldWeight)
open ClosedRelative (Shell Physical TotalGhostSpace GradedCycles GradedBoundaries
  GradedCohomology representative coefficient primitive)

open private gradedBoundaryMap from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeZeroMomentum

local instance : AddCommGroup Matter :=
  TensorProduct.addCommGroup (R := ℂ) (M := Orbifold) (N := Carrier hyperbolicPlane)

local instance : AddCommGroup ComplexState :=
  TensorProduct.addCommGroup (R := ℂ) (M := Matter) (N := Fock)

local instance : AddCommGroup AssocState :=
  TensorProduct.addCommGroup (R := ℂ) (M := Orbifold) (N := State hyperbolicPlane)

local instance : AddCommGroup ClosedState :=
  TensorProduct.addCommGroup (R := ℂ) (M := ComplexState) (N := ComplexState)

local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _

local instance (p : Charge hyperbolicPlane) : AddCommGroup (OrbifoldWeight p) :=
  Submodule.addCommGroup (R := ℂ) (M := Orbifold) (OrbifoldWeight p)

local instance (p q : Charge hyperbolicPlane) : AddCommGroup (Shell p q) :=
  TensorProduct.addCommGroup (R := ℂ) (M := relativeShell p) (N := relativeShell q)

local instance (p q : Charge hyperbolicPlane) (g : ℤ) :
    AddCommGroup (GradedCycles p q g) := Submodule.addCommGroup _

variable (pL pR : Charge hyperbolicPlane)

section Homotopy

variable (FL FR : NullFrame hyperbolicPlane)
variable (BL : Module.Basis (Fin 0) ℂ FL.K) (BR : Module.Basis (Fin 0) ℂ FR.K)
variable (hL : FL.pPlus pL ≠ 0) (hR : FR.pPlus pR ≠ 0)
variable (m : Module.End ℂ (Shell pL pR))

private def conePrimitive : Module.End ℂ (Shell pL pR) :=
  let first : Module.End ℂ (Shell pL pR) := ((primitive FL FR BL BR pL pR hL hR)).comp m
  let second : Module.End ℂ (Shell pL pR) := ((representative FL FR BL BR pL pR hL hR)).comp (((coefficient FL FR
    BL BR pL pR hL hR)).comp (m.comp (primitive FL FR BL BR pL pR hL hR)))
  first + second

private theorem conePrimitive_degree
    (hm : ∀ g x, x ∈ (TotalGhostSpace pL pR) g → m x ∈ (TotalGhostSpace pL pR) (g + 2)) {g : ℤ} {x : (Shell pL
      pR)} (hx : x ∈ (TotalGhostSpace pL pR) g) :
    conePrimitive pL pR FL FR BL BR hL hR m x ∈ (TotalGhostSpace pL pR) (g + 1) := by
  apply ((TotalGhostSpace pL pR) (g + 1)).add_mem
  · change primitive FL FR BL BR pL pR hL hR (m x) ∈ TotalGhostSpace pL pR (g + 1)
    simpa only [show g + 2 - 1 = g + 1 by omega] using
      ClosedRelative.primitive_degree FL FR BL BR pL pR hL hR (g + 2) (m x) (hm g x hx)
  · change (representative FL FR BL BR pL pR hL hR) ((coefficient FL FR BL BR pL pR hL hR) (m ((primitive FL FR BL
    BR pL pR hL hR) x))) ∈ (TotalGhostSpace pL pR) (g + 1)
    have hx' : m ((primitive FL FR BL BR pL pR hL hR) x) ∈ (TotalGhostSpace pL pR) (g + 1) := by
      simpa only [show g - 1 + 2 = g + 1 by omega] using hm (g - 1) (primitive FL FR BL BR pL pR hL hR x)
        (ClosedRelative.primitive_degree FL FR BL BR pL pR hL hR g x hx)
    by_cases hg : g + 1 = 2
    · rw [hg]
      exact ClosedRelative.representative_degree FL FR BL BR pL pR hL hR _
    · rw [ClosedRelative.coefficient_eq_zero_of_degree_ne_two FL FR BL BR pL pR hL hR
        (g + 1) hg _ hx', map_zero]
      exact ((TotalGhostSpace pL pR) (g + 1)).zero_mem

private theorem conePrimitive_identity
    (hm : ∀ g x, x ∈ (TotalGhostSpace pL pR) g → m x ∈ (TotalGhostSpace pL pR) (g + 2))
    (comm : ∀ x, (ClosedRelative.differential pL pR) (m x) = m ((ClosedRelative.differential pL pR) x)) (x :
      (Shell pL pR)) :
    let K := conePrimitive pL pR FL FR BL BR hL hR m
    (ClosedRelative.differential pL pR) (K x) + K ((ClosedRelative.differential pL pR) x) = m x := by
  have pmi (u : Physical pL pR) : (coefficient FL FR BL BR pL pR hL hR) (m ((representative FL FR BL BR pL pR hL
    hR) u)) = 0 :=
    ClosedRelative.coefficient_eq_zero_of_degree_ne_two FL FR BL BR pL pR hL hR
      4 (by norm_num) _ (hm 2 _ (ClosedRelative.representative_degree FL FR BL BR pL pR hL hR u))
  have di (u : Physical pL pR) : (ClosedRelative.differential pL pR) ((representative FL FR BL BR pL pR hL hR) u)
    = 0 :=
    LinearMap.congr_fun (ClosedRelative.representative_chain FL FR BL BR pL pR hL hR) u
  have pmd (z : (Shell pL pR)) : (coefficient FL FR BL BR pL pR hL hR) (m ((ClosedRelative.differential pL pR) z))
    = 0 := by
    rw [← comm]
    exact LinearMap.congr_fun (ClosedRelative.coefficient_chain FL FR BL BR pL pR hL hR) (m z)
  have contract (z : (Shell pL pR)) : (ClosedRelative.differential pL pR) ((primitive FL FR BL BR pL pR hL hR) z)
    + (primitive FL FR BL BR pL pR hL hR) ((ClosedRelative.differential pL pR) z) = z - (representative FL FR BL
    BR pL pR hL hR) ((coefficient FL FR BL BR pL pR hL hR) z) :=
    LinearMap.congr_fun (ClosedRelative.contraction FL FR BL BR pL pR hL hR) z
  have right : (coefficient FL FR BL BR pL pR hL hR) (m ((primitive FL FR BL BR pL pR hL hR)
    ((ClosedRelative.differential pL pR) x))) = (coefficient FL FR BL BR pL pR hL hR) (m x) := by
    have eq := congrArg (fun z => (coefficient FL FR BL BR pL pR hL hR) (m z)) (contract x)
    simpa only [map_add, map_sub, pmd, pmi, zero_add, sub_zero] using eq
  dsimp only [conePrimitive, LinearMap.add_apply, LinearMap.comp_apply]
  rw [map_add, di, add_zero, right, ← comm x, ← add_assoc, contract, sub_add_cancel]

private def coneShear (k : Module.End ℂ (Shell pL pR)) : ((Shell pL pR) × (Shell pL pR)) ≃ₗ[ℂ] (Shell pL pR) ×
  (Shell pL pR) where
  toFun z := (z.1 + k z.2, z.2)
  invFun z := (z.1 - k z.2, z.2)
  left_inv z := Prod.ext (add_sub_cancel_right _ _) rfl
  right_inv z := Prod.ext (sub_add_cancel _ _) rfl
  map_add' z w := Prod.ext (by simp only [Prod.fst_add, Prod.snd_add, map_add]; abel) rfl
  map_smul' c z := by
    apply Prod.ext
    · change c • z.1 + k (c • z.2) = c • (z.1 + k z.2)
      rw [map_smul, smul_add]
    · rfl

private theorem coneShear_degree_iff (k : Module.End ℂ (Shell pL pR))
    (hk : ∀ g x, x ∈ (TotalGhostSpace pL pR) g → k x ∈ (TotalGhostSpace pL pR) (g + 1)) (g : ℤ) (z : (Shell pL pR)
      × (Shell pL pR)) :
    z.1 ∈ (TotalGhostSpace pL pR) g ∧ z.2 ∈ (TotalGhostSpace pL pR) (g - 1) ↔
      (coneShear pL pR k z).1 ∈ (TotalGhostSpace pL pR) g ∧ (coneShear pL pR k z).2 ∈ (TotalGhostSpace pL pR) (g -
        1) := by
  change _ ↔ z.1 + k z.2 ∈ (TotalGhostSpace pL pR) g ∧ z.2 ∈ (TotalGhostSpace pL pR) (g - 1)
  have hk' (hy : z.2 ∈ (TotalGhostSpace pL pR) (g - 1)) : k z.2 ∈ (TotalGhostSpace pL pR) g := by
    simpa only [sub_add_cancel] using hk (g - 1) z.2 hy
  constructor
  · exact fun ⟨hx, hy⟩ => ⟨((TotalGhostSpace pL pR) g).add_mem hx (hk' hy), hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨by simpa only [add_sub_cancel_right] using ((TotalGhostSpace pL pR) g).sub_mem hx (hk' hy), hy⟩

private theorem coneShear_differential (op k : Module.End ℂ (Shell pL pR))
    (hk : ∀ x, (ClosedRelative.differential pL pR) (k x) + k ((ClosedRelative.differential pL pR) x) = op x) (z :
      (Shell pL pR) × (Shell pL pR)) :
    coneShear pL pR k ((ClosedRelative.differential pL pR) z.1 + op z.2, -(ClosedRelative.differential pL pR) z.2) =
      ((ClosedRelative.differential pL pR) (coneShear pL pR k z).1, -(ClosedRelative.differential pL pR)
        (coneShear pL pR k z).2) := by
  apply Prod.ext
  · change (ClosedRelative.differential pL pR) z.1 + op z.2 + k (-(ClosedRelative.differential pL pR) z.2) =
    (ClosedRelative.differential pL pR) (z.1 + k z.2)
    rw [← hk z.2, map_neg, ← sub_eq_add_neg, ← add_assoc, add_sub_cancel_right, map_add]
  · rfl

end Homotopy

section GradedQuotient

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (δ : Module.End ℂ V) (G : ℤ → Submodule ℂ V)
variable (e : V ≃ₗ[ℂ] (Shell pL pR) × (Shell pL pR))
variable (he : ∀ z, e (δ z) = ((ClosedRelative.differential pL pR) (e z).1, -(ClosedRelative.differential pL pR)
  (e z).2))
variable (hg : ∀ g z, z ∈ G g ↔ (e z).1 ∈ (TotalGhostSpace pL pR) g ∧ (e z).2 ∈ (TotalGhostSpace pL pR) (g - 1))

private abbrev sectorCycles (g : ℤ) := G g ⊓ δ.ker

local instance (g : ℤ) : AddCommGroup (sectorCycles δ G g) :=
  Submodule.addCommGroup _

private def sectorBoundary
    (hsq : ∀ z, δ (δ z) = 0) (hd : ∀ g z, z ∈ G g → δ z ∈ G (g + 1)) (g : ℤ) :
    G (g - 1) →ₗ[ℂ] sectorCycles δ G g :=
  (δ.comp (G (g - 1)).subtype).codRestrict _ fun z =>
      Submodule.mem_inf.mpr ⟨by
      change δ z.val ∈ G g
      simpa only [sub_add_cancel] using hd (g - 1) z.val z.property, hsq z.val⟩

private abbrev sectorBoundaries
    (hsq : ∀ z, δ (δ z) = 0) (hd : ∀ g z, z ∈ G g → δ z ∈ G (g + 1)) (g : ℤ) :=
  (sectorBoundary δ G hsq hd g).range

include pL pR he hg in
private theorem sectorCycles_iff (g : ℤ) (z : V) :
    z ∈ sectorCycles δ G g ↔
      (e z).1 ∈ GradedCycles pL pR g ∧ (e z).2 ∈ GradedCycles pL pR (g - 1) := by
  have hz : δ z = 0 ↔ (ClosedRelative.differential pL pR) (e z).1 = 0 ∧ (ClosedRelative.differential pL pR) (e
    z).2 = 0 := by
    rw [← e.map_eq_zero_iff, he, Prod.mk_eq_zero, neg_eq_zero]
  change (z ∈ G g ∧ δ z = 0) ↔ _
  rw [hg, hz]
  exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩,
    fun h => ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩⟩

include he hg in
private def sectorCyclesEquiv (g : ℤ) :
    sectorCycles δ G g ≃ₗ[ℂ] GradedCycles pL pR g × GradedCycles pL pR (g - 1) :=
  (e.submoduleMap _).trans
    ((LinearEquiv.ofEq _ ((GradedCycles pL pR g).prod (GradedCycles pL pR (g - 1))) (by
      ext w
      rw [Submodule.mem_map_equiv]
      have hw := sectorCycles_iff pL pR δ G e he hg g (e.symm w)
      simpa only [e.apply_symm_apply, Submodule.mem_prod] using hw)).trans (Submodule.prodEquiv _ _))

include he hg in
private def sectorClassMap (g : ℤ) :
    sectorCycles δ G g →ₗ[ℂ] GradedCohomology pL pR g × GradedCohomology pL pR (g - 1) :=
  ((GradedBoundaries pL pR g).mkQ.prodMap (GradedBoundaries pL pR (g - 1)).mkQ).comp
    (sectorCyclesEquiv pL pR δ G e he hg g).toLinearMap

include pL pR he hg in
private theorem sectorBoundaries_eq_ker
    (hsq : ∀ z, δ (δ z) = 0) (hd : ∀ g z, z ∈ G g → δ z ∈ G (g + 1)) (g : ℤ) :
    sectorBoundaries δ G hsq hd g = (sectorClassMap pL pR δ G e he hg g).ker := by
  ext z
  let w := sectorCyclesEquiv pL pR δ G e he hg g z
  change (∃ v : G (g - 1), sectorBoundary δ G hsq hd g v = z) ↔
    (Submodule.Quotient.mk w.1, Submodule.Quotient.mk w.2) = (0, 0)
  simp only [Prod.mk.injEq, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨v, rfl⟩
    have hdeg := (hg (g - 1) v.val).mp v.property
    exact ⟨⟨⟨(e v.val).1, hdeg.1⟩, Subtype.ext (congrArg Prod.fst (he v.val)).symm⟩,
      ⟨⟨-(e v.val).2, ((TotalGhostSpace pL pR) _).neg_mem hdeg.2⟩,
        Subtype.ext (((ClosedRelative.differential pL pR).map_neg _).trans (congrArg Prod.snd (he v.val)).symm)⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    let v := e.symm (a.val, -b.val)
    have hv : v ∈ G (g - 1) := by
      apply (hg (g - 1) v).mpr
      simpa only [v, e.apply_symm_apply] using
        And.intro a.property (((TotalGhostSpace pL pR) _).neg_mem b.property)
    refine ⟨⟨v, hv⟩, Subtype.ext (e.injective ?_)⟩
    change e (δ v) = e z.val
    rw [he, show e v = (a.val, -b.val) from e.apply_symm_apply _, (ClosedRelative.differential pL pR).map_neg,
      neg_neg]
    exact Prod.ext (congrArg Subtype.val ha) (congrArg Subtype.val hb)

include he hg in
private def sectorQuotientEquiv
    (hsq : ∀ z, δ (δ z) = 0) (hd : ∀ g z, z ∈ G g → δ z ∈ G (g + 1)) (g : ℤ) :
    (sectorCycles δ G g ⧸ sectorBoundaries δ G hsq hd g) ≃ₗ[ℂ]
      GradedCohomology pL pR g × GradedCohomology pL pR (g - 1) := by
  let f := sectorClassMap pL pR δ G e he hg g
  have hs : Function.Surjective f := by
    rintro ⟨x, y⟩
    obtain ⟨a, rfl⟩ := (GradedBoundaries pL pR g).mkQ_surjective x
    obtain ⟨b, rfl⟩ := (GradedBoundaries pL pR (g - 1)).mkQ_surjective y
    obtain ⟨z, hz⟩ := (sectorCyclesEquiv pL pR δ G e he hg g).surjective (a, b)
    exact ⟨z, congrArg
      ((GradedBoundaries pL pR g).mkQ.prodMap (GradedBoundaries pL pR (g - 1)).mkQ) hz⟩
  exact ((sectorBoundaries δ G hsq hd g).quotEquivOfEq _
    (sectorBoundaries_eq_ker pL pR δ G e he hg hsq hd g)).trans
    (f.quotKerEquivOfSurjective hs)

end GradedQuotient

section Native


private theorem momentumM_commutes (x : (Shell pL pR)) : (ClosedRelative.differential pL pR) ((momentumM pL pR) x)
  = (momentumM pL pR) ((ClosedRelative.differential pL pR) x) := by
  apply momentumShellToR_injective pL pR
  rw [← D_R_momentumShellToR, ← M_R_momentumShellToR,
    ← M_R_momentumShellToR, ← D_R_momentumShellToR]
  exact LinearMap.congr_fun D_R_M_R _

/-- The null homotopy of the literal Ward operator on the fixed relative shell. -/
def momentumConePrimitive (FL FR : NullFrame hyperbolicPlane)
    (BL : Module.Basis (Fin 0) ℂ FL.K) (BR : Module.Basis (Fin 0) ℂ FR.K)
    (hL : FL.pPlus pL ≠ 0) (hR : FR.pPlus pR ≠ 0) : Module.End ℂ (Shell pL pR) :=
  conePrimitive pL pR FL FR BL BR hL hR (momentumM pL pR)

variable (FL FR : NullFrame hyperbolicPlane)
variable (BL : Module.Basis (Fin 0) ℂ FL.K) (BR : Module.Basis (Fin 0) ℂ FR.K)
variable (hL : FL.pPlus pL ≠ 0) (hR : FR.pPlus pR ≠ 0)

theorem momentumConePrimitive_degree {g : ℤ} {x : (Shell pL pR)} (hx : x ∈ (TotalGhostSpace pL pR) g) :
    (momentumConePrimitive pL pR FL FR BL BR hL hR) x ∈ (TotalGhostSpace pL pR) (g + 1) :=
  conePrimitive_degree pL pR FL FR BL BR hL hR (momentumM pL pR) (fun g _ hx => momentumM_degree pL pR g hx) hx

theorem momentumConePrimitive_identity (x : (Shell pL pR)) :
    (ClosedRelative.differential pL pR) ((momentumConePrimitive pL pR FL FR BL BR hL hR) x) +
      (momentumConePrimitive pL pR FL FR BL BR hL hR) ((ClosedRelative.differential pL pR) x) = (momentumM pL pR)
      x :=
  conePrimitive_identity pL pR FL FR BL BR hL hR (momentumM pL pR)
    (fun g _ hx => momentumM_degree pL pR g hx) (momentumM_commutes pL pR) x

/-- Change of coordinates on the actual fixed-shell cone. -/
def momentumConeShear : ((Shell pL pR) × (Shell pL pR)) ≃ₗ[ℂ] (Shell pL pR) × (Shell pL pR) :=
  coneShear pL pR (momentumConePrimitive pL pR FL FR BL BR hL hR)

theorem momentumConeShear_differential (z : (Shell pL pR) × (Shell pL pR)) :
    (momentumConeShear pL pR FL FR BL BR hL hR) (momentumConeDifferential pL pR z) = ((ClosedRelative.differential
      pL pR) ((momentumConeShear pL pR FL FR BL BR hL hR) z).1, -(ClosedRelative.differential pL pR)
      ((momentumConeShear pL pR FL FR BL BR hL hR) z).2) := by
  rcases z with ⟨x, y⟩
  rw [momentumConeDifferential_apply]
  exact coneShear_differential pL pR (momentumM pL pR) (momentumConePrimitive pL pR FL FR BL BR hL hR)
    (momentumConePrimitive_identity pL pR FL FR BL BR hL hR) (x, y)

theorem momentumConeShear_degree_iff (g : ℤ) (z : (Shell pL pR) × (Shell pL pR)) :
    z.1 ∈ (TotalGhostSpace pL pR) g ∧ z.2 ∈ (TotalGhostSpace pL pR) (g - 1) ↔ ((momentumConeShear pL pR FL FR BL
      BR hL hR) z).1 ∈ (TotalGhostSpace pL pR) g ∧ ((momentumConeShear pL pR FL FR BL BR hL hR) z).2 ∈
      (TotalGhostSpace pL pR) (g - 1) :=
  coneShear_degree_iff pL pR (momentumConePrimitive pL pR FL FR BL BR hL hR)
    (fun _ _ hx => momentumConePrimitive_degree pL pR FL FR BL BR hL hR hx) g z

local instance : AddCommGroup (EnergySpace 0) := Submodule.addCommGroup _
local instance (q r : Charge hyperbolicPlane) : AddCommGroup (MomentumEnergySpace q r) :=
  Submodule.addCommGroup _

private local instance (priority := 2000) momentumEnergyAddCommMonoid
    (q r : Charge hyperbolicPlane) : AddCommMonoid (MomentumEnergySpace q r) :=
  Submodule.addCommMonoid (MomentumEnergySpace q r)

private local instance (priority := 2000) momentumEnergyModule
    (q r : Charge hyperbolicPlane) : Module ℂ (MomentumEnergySpace q r) :=
  Submodule.module (MomentumEnergySpace q r)

/-- The native differential on the jointly fixed, level-matched momentum sector. -/
def momentumDifferential : Module.End ℂ (MomentumEnergySpace pL pR) :=
  (differential 0).restrict fun _ hx => differential_mem_momentumEnergySpace pL pR hx

/-- A native cochain in this sector with actual total ghost degree `g`. -/
def MomentumGhostSpace (g : ℤ) : Submodule ℂ (MomentumEnergySpace pL pR) :=
  (GhostSpace g).comap ((EnergySpace 0).subtype.comp (MomentumEnergySpace pL pR).subtype)

private theorem momentumDifferential_sq (z : (MomentumEnergySpace pL pR)) : (momentumDifferential pL pR)
  ((momentumDifferential pL pR) z) = 0 :=
  Subtype.ext (LinearMap.congr_fun (differential_square 0) z.val)

private theorem momentumDifferential_degree (g : ℤ) (z : (MomentumEnergySpace pL pR)) (hz : z ∈
  (MomentumGhostSpace pL pR) g) :
    (momentumDifferential pL pR) z ∈ (MomentumGhostSpace pL pR) (g + 1) := D_degree hz

/-- Actual degree-`g` cycles on the fixed native sector. -/
def MomentumCycles (g : ℤ) : Submodule ℂ (MomentumEnergySpace pL pR) := sectorCycles (momentumDifferential pL
  pR) (MomentumGhostSpace pL pR) g


local instance (q r : Charge hyperbolicPlane) (g : ℤ) : AddCommGroup (MomentumCycles q r g) :=
  Submodule.addCommGroup _

private local instance (priority := 2000) momentumCyclesAddCommMonoid
    (q r : Charge hyperbolicPlane) (g : ℤ) : AddCommMonoid (MomentumCycles q r g) :=
  Submodule.addCommMonoid (MomentumCycles q r g)

private local instance (priority := 2000) momentumCyclesModule
    (q r : Charge hyperbolicPlane) (g : ℤ) : Module ℂ (MomentumCycles q r g) :=
  Submodule.module (MomentumCycles q r g)

/-- Images of the native differential from degree `g - 1`, viewed in the cycles. -/
def MomentumBoundaries (g : ℤ) : Submodule ℂ (MomentumCycles pL pR g) :=
  sectorBoundaries (momentumDifferential pL pR) (MomentumGhostSpace pL pR) (momentumDifferential_sq pL pR)
    (momentumDifferential_degree pL pR) g

/-- Native graded semirelative BRST cohomology at the two specified momenta. -/
abbrev MomentumCohomology (g : ℤ) := MomentumCycles pL pR g ⧸ MomentumBoundaries pL pR g

private def momentumConeEquiv : ((Shell pL pR) × (Shell pL pR)) ≃ₗ[ℂ] (MomentumEnergySpace pL pR) :=
  (LinearEquiv.ofInjective _ (momentumConeInclusion_injective pL pR)).trans
    (LinearEquiv.ofEq _ _ (momentumConeInclusion_range pL pR))

private theorem momentumConeEquiv_val (z : (Shell pL pR) × (Shell pL pR)) :
    (momentumConeEquiv pL pR z).val = momentumConeInclusion pL pR z := rfl

private theorem momentumConeEquiv_D (z : (Shell pL pR) × (Shell pL pR)) :
    (momentumDifferential pL pR) (momentumConeEquiv pL pR z) = momentumConeEquiv pL pR (momentumConeDifferential
      pL pR z) :=
  Subtype.ext (differential_momentumConeInclusion pL pR z.1 z.2)

/-- The graded chain diagonalization of the actual zero-energy momentum sector. -/
def momentumDiagonal : (MomentumEnergySpace pL pR) ≃ₗ[ℂ] (Shell pL pR) × (Shell pL pR) :=
  (momentumConeEquiv pL pR).symm.trans (momentumConeShear pL pR FL FR BL BR hL hR)

theorem momentumDiagonal_differential (z : (MomentumEnergySpace pL pR)) :
    (momentumDiagonal pL pR FL FR BL BR hL hR) ((momentumDifferential pL pR) z) = ((ClosedRelative.differential pL
      pR) ((momentumDiagonal pL pR FL FR BL BR hL hR) z).1, -(ClosedRelative.differential pL pR)
      ((momentumDiagonal pL pR FL FR BL BR hL hR) z).2) := by
  obtain ⟨v, rfl⟩ := (momentumConeEquiv pL pR).surjective z
  rw [momentumConeEquiv_D]
  simpa only [momentumDiagonal, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using
    momentumConeShear_differential pL pR FL FR BL BR hL hR v

theorem momentumDiagonal_degree_iff (g : ℤ) (z : (MomentumEnergySpace pL pR)) :
    z ∈ (MomentumGhostSpace pL pR) g ↔ ((momentumDiagonal pL pR FL FR BL BR hL hR) z).1 ∈ (TotalGhostSpace pL pR)
      g ∧ ((momentumDiagonal pL pR FL FR BL BR hL hR) z).2 ∈ (TotalGhostSpace pL pR) (g - 1) := by
  obtain ⟨v, rfl⟩ := (momentumConeEquiv pL pR).surjective z
  have h := (momentumConeInclusion_ghost_iff pL pR g v.1 v.2).trans
    (momentumConeShear_degree_iff pL pR FL FR BL BR hL hR g v)
  simpa only [MomentumGhostSpace, Submodule.mem_comap, LinearMap.comp_apply,
    Submodule.subtype_apply, momentumConeEquiv_val, momentumDiagonal, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply] using h

/-- The induced isomorphism on actual degreewise kernel/image quotients. -/
def momentumCohomologySplit (g : ℤ) :
    MomentumCohomology pL pR g ≃ₗ[ℂ]
      GradedCohomology pL pR g × GradedCohomology pL pR (g - 1) :=
  sectorQuotientEquiv pL pR (momentumDifferential pL pR) (MomentumGhostSpace pL pR) (momentumDiagonal pL pR FL FR
    BL BR hL hR) (momentumDiagonal_differential pL pR FL FR BL BR hL hR) (momentumDiagonal_degree_iff pL pR FL FR
    BL BR hL hR)
    (momentumDifferential_sq pL pR) (momentumDifferential_degree pL pR) g

/-- The degree-two semirelative cohomology reads the first relative class. -/
def momentumGhostTwoEquiv : MomentumCohomology pL pR 2 ≃ₗ[ℂ] Physical pL pR := by
  have trivial := ClosedRelative.gradedCohomology_vanishes
    FL FR BL BR pL pR hL hR (2 - 1) (by norm_num)
  letI : Unique (GradedCohomology pL pR (2 - 1)) := ⟨⟨0⟩, fun x => trivial.elim x 0⟩
  exact ((momentumCohomologySplit pL pR FL FR BL BR hL hR) 2).trans (LinearEquiv.prodUnique.trans
    (ClosedRelative.ghostTwoCohomologyEquiv FL FR BL BR pL pR hL hR))

/-- The degree-three semirelative cohomology reads the shifted relative class. -/
def momentumGhostThreeEquiv : MomentumCohomology pL pR 3 ≃ₗ[ℂ] Physical pL pR := by
  have trivial := ClosedRelative.gradedCohomology_vanishes FL FR BL BR pL pR hL hR 3 (by norm_num)
  letI : Unique (GradedCohomology pL pR 3) := ⟨⟨0⟩, fun x => trivial.elim x 0⟩
  exact ((momentumCohomologySplit pL pR FL FR BL BR hL hR) 3).trans (LinearEquiv.uniqueProd.trans
    (ClosedRelative.ghostTwoCohomologyEquiv FL FR BL BR pL pR hL hR))

private def momentumCyclesEquiv (g : ℤ) :
    MomentumCycles pL pR g ≃ₗ[ℂ] GradedCycles pL pR g × GradedCycles pL pR (g - 1) :=
  sectorCyclesEquiv pL pR (momentumDifferential pL pR) (MomentumGhostSpace pL pR)
    (momentumDiagonal pL pR FL FR BL BR hL hR)
    (momentumDiagonal_differential pL pR FL FR BL BR hL hR)
    (momentumDiagonal_degree_iff pL pR FL FR BL BR hL hR) g

/-- The degree-two representative is the corrected relative representative in the first slot. -/
def momentumGhostTwoRepresentative (u : Physical pL pR) : MomentumCycles pL pR 2 :=
  (momentumCyclesEquiv pL pR FL FR BL BR hL hR 2).symm
    (ClosedRelative.ghostTwoRepresentative FL FR BL BR pL pR hL hR u, 0)

/-- The degree-three representative is the corrected representative in the shifted slot
with its first slot determined by the inverse shear. -/
def momentumGhostThreeRepresentative (u : Physical pL pR) : MomentumCycles pL pR 3 :=
  (momentumCyclesEquiv pL pR FL FR BL BR hL hR 3).symm
    (0, ClosedRelative.ghostTwoRepresentative FL FR BL BR pL pR hL hR u)

private def relativeClasses (g : ℤ) (z : GradedCycles pL pR g × GradedCycles pL pR (g - 1)) :
    GradedCohomology pL pR g × GradedCohomology pL pR (g - 1) :=
  ((GradedBoundaries pL pR g).mkQ z.1, (GradedBoundaries pL pR (g - 1)).mkQ z.2)

private theorem momentumCohomologySplit_mk (g : ℤ) (z : MomentumCycles pL pR g) :
    (momentumCohomologySplit pL pR FL FR BL BR hL hR) g (Submodule.Quotient.mk z) =
      relativeClasses pL pR g (momentumCyclesEquiv pL pR FL FR BL BR hL hR g z) := rfl

private theorem momentumCyclesEquiv_symm_val (g : ℤ)
    (z : GradedCycles pL pR g × GradedCycles pL pR (g - 1)) :
    ((momentumCyclesEquiv pL pR FL FR BL BR hL hR g).symm z).val =
      (momentumDiagonal pL pR FL FR BL BR hL hR).symm (z.1.val, z.2.val) := by
  apply (momentumDiagonal pL pR FL FR BL BR hL hR).injective
  rw [(momentumDiagonal pL pR FL FR BL BR hL hR).apply_symm_apply]
  have h := (momentumCyclesEquiv pL pR FL FR BL BR hL hR g).apply_symm_apply z
  exact congrArg (fun w : GradedCycles pL pR g × GradedCycles pL pR (g - 1) =>
    (w.1.val, w.2.val)) h

theorem momentumGhostTwoRepresentative_val (u : Physical pL pR) :
    ((momentumGhostTwoRepresentative pL pR FL FR BL BR hL hR) u).val.val.val = momentumShellInclusion pL pR
      ((ClosedRelative.ghostTwoRepresentative FL FR BL BR pL pR hL hR) u).val := by
  rw [momentumGhostTwoRepresentative, momentumCyclesEquiv_symm_val]
  change (momentumConeInclusion pL pR (((ClosedRelative.ghostTwoRepresentative FL FR BL BR pL pR hL hR) u).val -
    (momentumConePrimitive pL pR FL FR BL BR hL hR) 0, 0)).val = _
  rw [map_zero, sub_zero, momentumConeInclusion_val, map_zero, map_zero, add_zero]

theorem momentumGhostThreeRepresentative_val (u : Physical pL pR) :
    ((momentumGhostThreeRepresentative pL pR FL FR BL BR hL hR) u).val.val.val =
      C_plus (momentumShellInclusion pL pR ((ClosedRelative.ghostTwoRepresentative FL FR BL BR pL pR hL hR)
        u).val) -
        momentumShellInclusion pL pR ((momentumConePrimitive pL pR FL FR BL BR hL hR)
          ((ClosedRelative.ghostTwoRepresentative FL FR BL BR pL pR hL hR) u).val) := by
  rw [momentumGhostThreeRepresentative, momentumCyclesEquiv_symm_val]
  change (momentumConeInclusion pL pR (0 - (momentumConePrimitive pL pR FL FR BL BR hL hR)
    ((ClosedRelative.ghostTwoRepresentative FL FR BL BR pL pR hL hR) u).val,
    ((ClosedRelative.ghostTwoRepresentative FL FR BL BR pL pR hL hR) u).val)).val = _
  rw [zero_sub, momentumConeInclusion_val, map_neg, sub_eq_add_neg, add_comm]

theorem momentumGhostTwoEquiv_symm_apply (u : Physical pL pR) :
    (momentumGhostTwoEquiv pL pR FL FR BL BR hL hR).symm u =
      Submodule.Quotient.mk (momentumGhostTwoRepresentative pL pR FL FR BL BR hL hR u) := by
  let E := momentumGhostTwoEquiv pL pR FL FR BL BR hL hR
  let P := ClosedRelative.ghostTwoCohomologyEquiv FL FR BL BR pL pR hL hR
  let z := momentumGhostTwoRepresentative pL pR FL FR BL BR hL hR u
  let r := ClosedRelative.ghostTwoRepresentative FL FR BL BR pL pR hL hR u
  let c := momentumCyclesEquiv pL pR FL FR BL BR hL hR 2
  let q := momentumCohomologySplit pL pR FL FR BL BR hL hR 2
  have hc : c z = (r, 0) := c.apply_symm_apply (r, 0)
  have hq := congrArg Prod.fst (momentumCohomologySplit_mk pL pR FL FR BL BR hL hR 2 z)
  have hr := congrArg P (ClosedRelative.ghostTwoCohomologyEquiv_symm_apply
    FL FR BL BR pL pR hL hR u)
  apply E.injective
  calc
    E (E.symm u) = u := E.apply_symm_apply u
    _ = P (Submodule.Quotient.mk r) := (P.apply_symm_apply u).symm.trans hr
    _ = P (Submodule.Quotient.mk (c z).1) :=
      congrArg (fun w => P ((GradedBoundaries pL pR 2).mkQ w.1)) hc.symm
    _ = P (q (Submodule.Quotient.mk z)).1 := congrArg P hq.symm
    _ = E (Submodule.Quotient.mk z) := rfl

theorem momentumGhostThreeEquiv_symm_apply (u : Physical pL pR) :
    (momentumGhostThreeEquiv pL pR FL FR BL BR hL hR).symm u =
      Submodule.Quotient.mk (momentumGhostThreeRepresentative pL pR FL FR BL BR hL hR u) := by
  let E := momentumGhostThreeEquiv pL pR FL FR BL BR hL hR
  let P := ClosedRelative.ghostTwoCohomologyEquiv FL FR BL BR pL pR hL hR
  let z := momentumGhostThreeRepresentative pL pR FL FR BL BR hL hR u
  let r := ClosedRelative.ghostTwoRepresentative FL FR BL BR pL pR hL hR u
  let c := momentumCyclesEquiv pL pR FL FR BL BR hL hR 3
  let q := momentumCohomologySplit pL pR FL FR BL BR hL hR 3
  have hc : c z = (0, r) := c.apply_symm_apply (0, r)
  have hq := congrArg Prod.snd (momentumCohomologySplit_mk pL pR FL FR BL BR hL hR 3 z)
  have hr := congrArg P (ClosedRelative.ghostTwoCohomologyEquiv_symm_apply
    FL FR BL BR pL pR hL hR u)
  apply E.injective
  calc
    E (E.symm u) = u := E.apply_symm_apply u
    _ = P (Submodule.Quotient.mk r) := (P.apply_symm_apply u).symm.trans hr
    _ = P (Submodule.Quotient.mk (c z).2) :=
      congrArg (fun w => P ((GradedBoundaries pL pR 2).mkQ w.2)) hc.symm
    _ = P (q (Submodule.Quotient.mk z)).2 := congrArg P hq.symm
    _ = E (Submodule.Quotient.mk z) := rfl

include FL FR BL BR hL hR in
theorem momentumCohomology_vanishes (g : ℤ) (h2 : g ≠ 2) (h3 : g ≠ 3) :
    Subsingleton (MomentumCohomology pL pR g) := by
  have hfst := ClosedRelative.gradedCohomology_vanishes FL FR BL BR pL pR hL hR g h2
  have hsnd := ClosedRelative.gradedCohomology_vanishes FL FR BL BR pL pR hL hR (g - 1) (by omega)
  exact ⟨fun x y => (momentumCohomologySplit pL pR FL FR BL BR hL hR g).injective
    (Prod.ext (hfst.elim _ _) (hsnd.elim _ _))⟩

private structure MomentumFrame (q : Charge hyperbolicPlane) where
  frame : NullFrame hyperbolicPlane
  basis : Module.Basis (Fin 0) ℂ frame.K
  nonzeroPlus : frame.pPlus q ≠ 0

private def momentumFrame (q : Charge hyperbolicPlane) (hq : q ≠ 0) : MomentumFrame q := by
  by_cases h : planeFrame.pPlus q ≠ 0
  · exact ⟨planeFrame, planeBasis, h⟩
  · exact ⟨swappedPlaneFrame, swappedPlaneBasis, (planeFrame_covers_nonzero q hq).resolve_left h⟩

variable (hpL : pL ≠ 0) (hpR : pR ≠ 0)

/-- At every pair of nonzero momenta the actual degree-two quotient is the native physical tensor. -/
def momentumGhostTwoEquivNonzero : MomentumCohomology pL pR 2 ≃ₗ[ℂ] Physical pL pR :=
  momentumGhostTwoEquiv pL pR ((momentumFrame pL hpL)).frame ((momentumFrame pR hpR)).frame ((momentumFrame pL
    hpL)).basis ((momentumFrame pR hpR)).basis
    ((momentumFrame pL hpL)).nonzeroPlus ((momentumFrame pR hpR)).nonzeroPlus

/-- At every pair of nonzero momenta the actual degree-three quotient is the native physical tensor. -/
def momentumGhostThreeEquivNonzero : MomentumCohomology pL pR 3 ≃ₗ[ℂ] Physical pL pR :=
  momentumGhostThreeEquiv pL pR ((momentumFrame pL hpL)).frame ((momentumFrame pR hpR)).frame ((momentumFrame pL
    hpL)).basis ((momentumFrame pR hpR)).basis
    ((momentumFrame pL hpL)).nonzeroPlus ((momentumFrame pR hpR)).nonzeroPlus

include hpL hpR in
/-- Every other ghost degree is exact in the native momentum sector. -/
theorem momentumCohomology_vanishes_nonzero (g : ℤ) (h2 : g ≠ 2) (h3 : g ≠ 3) :
    Subsingleton (MomentumCohomology pL pR g) :=
  momentumCohomology_vanishes pL pR ((momentumFrame pL hpL)).frame ((momentumFrame pR hpR)).frame ((momentumFrame
    pL hpL)).basis ((momentumFrame pR hpR)).basis
    ((momentumFrame pL hpL)).nonzeroPlus ((momentumFrame pR hpR)).nonzeroPlus g h2 h3

include hpL hpR in
theorem momentumExact_nonzero (g : ℤ) (h2 : g ≠ 2) (h3 : g ≠ 3)
    (z : MomentumCycles pL pR g) :
    ∃ w : MomentumGhostSpace pL pR (g - 1), momentumDifferential pL pR w.val = z.val := by
  have h := momentumCohomology_vanishes_nonzero pL pR hpL hpR g h2 h3
  have hz : z ∈ MomentumBoundaries pL pR g :=
    (Submodule.Quotient.mk_eq_zero _).mp (h.elim (Submodule.Quotient.mk z) 0)
  obtain ⟨w, hw⟩ := hz
  exact ⟨w, congrArg Subtype.val hw⟩

end Native

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedSemirelative
