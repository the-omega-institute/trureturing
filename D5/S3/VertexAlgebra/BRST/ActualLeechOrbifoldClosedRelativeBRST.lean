/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldClosedRelativeBRST
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldClosedRelativeBRST
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed double-relative BRST of the actual Leech orbifold at independent momenta. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology

/-!
The closed complex is the unprojected tensor product of two literal chiral
relative shells, with independently specified momenta. Semirelative
cohomology and any diagonal momentum constraint are outside this construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedRelative

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open ActualLeechOrbifoldMatter (Orbifold)
open LatticeGeneratingFieldLocality (Charge)
open LatticeLightConeCoordinates (NullFrame)
open LatticeQuartetContraction
open RelativeCohomology (GhostSpace OrbifoldWeight)
open D5.S3.HomologicalAlgebra
open D5.S3.Quantum.Fermionic.BcGhostCharge (charge siteSign)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (parity_involution)

open private rightLift_tmul rightSlice_tmul rightSlices_expand assocB0_eq from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone
open private rightSlice_assocE eq_zero_of_all_rightSlices from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightConeDegreeBounds
open private ghostWeight ghostSpace_iff_slices nilpotent
  coefficient_differential from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
open private chargeProject_basis from D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
open private charge_insert from D5.S3.Quantum.Fermionic.BcGhostCharge
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open private reassoc_parity from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes

variable (FL FR : NullFrame hyperbolicPlane)
variable (BL : Module.Basis (Fin 0) ℂ FL.K) (BR : Module.Basis (Fin 0) ℂ FR.K)
variable (pL pR : Charge hyperbolicPlane)

local instance : AddCommGroup AssocState :=
  TensorProduct.addCommGroup (R := ℂ) (M := Orbifold) (N := State hyperbolicPlane)

local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup (R := ℂ) (M := AssocState) (relativeShell p)

local instance (p : Charge hyperbolicPlane) : AddCommGroup (OrbifoldWeight p) :=
  Submodule.addCommGroup (R := ℂ) (M := Orbifold) (OrbifoldWeight p)

section GhostParity

variable (F : NullFrame hyperbolicPlane) (B : Module.Basis (Fin 0) ℂ F.K)
  (p : Charge hyperbolicPlane)

private abbrev assocParity := rightLift (LatticeMatterGhostStateField.parity hyperbolicPlane)

private theorem occupation_sign (S : Finset ℕ) : (-1 : ℂ) ^ S.card = (-1 : ℂ) ^ charge S := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [charge]
  | @insert j S hj ih =>
    rw [Finset.card_insert_of_notMem hj, pow_succ, ih, charge_insert j S hj,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    congr 1
    unfold siteSign
    split <;> norm_num

private theorem parity_basis (i : StateIndex hyperbolicPlane 0) :
    LatticeMatterGhostStateField.parity hyperbolicPlane (actualBasis F B i) =
      (-1 : ℂ) ^ ghostWeight i • actualBasis F B i := by
  rcases i with ⟨⟨q, m⟩, S⟩
  simp only [actualBasis_apply, sector, LatticeMatterGhostStateField.parity,
    TensorProduct.map_tmul, LinearMap.id_apply, parity_ket, TensorProduct.tmul_smul,
    ghostWeight, occupation_sign]

private theorem sliceTensor_mem (x : relativeShell p) (i : StateIndex hyperbolicPlane 0)
    (hi : rightSlice F B i x.val ≠ 0) :
    rightSlice F B i x.val ⊗ₜ[ℂ] actualBasis F B i ∈ relativeShell p := by
  classical
  obtain ⟨hq, hb, -⟩ := relativeShell_rightSlice_bounds F B p x.val x.property i hi
  have he := ((mem_relativeShell_iff p x.val).mp x.property).2.2
  apply (mem_relativeShell_iff p _).mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [rightLift_tmul, chargeProject_basis F B p i, ite_eq_left hq, one_smul]
  · rw [assocB0_eq, rightLift_tmul]
    have hbasis : ghostB0 (actualBasis F B i) = 0 := by
      apply (b0_coefficients F B _).mpr
      intro j hj
      have hne : i ≠ j := fun e => hb (e ▸ hj)
      rw [Module.Basis.repr_self_apply, ite_eq_right hne]
    rw [hbasis, TensorProduct.tmul_zero]
  · apply eq_zero_of_all_rightSlices F B
    intro j
    rw [rightSlice_assocE F B, rightSlice_tmul, Module.Basis.repr_self_apply]
    by_cases hji : i = j
    · subst j
      rw [ite_eq_left rfl, one_smul, ← rightSlice_assocE F B, he, map_zero]
    · rw [ite_eq_right hji, zero_smul, map_zero, smul_zero, add_zero]

include F B in
private theorem span_ghostSpace : (⨆ g, GhostSpace p g) = ⊤ := by
  classical
  apply top_unique
  intro x _
  let indices := (rightSlices F B x.val).support
  have support_nonzero (i : StateIndex hyperbolicPlane 0) (hi : i ∈ indices) :
      rightSlice F B i x.val ≠ 0 := Finsupp.mem_support_iff.mp hi
  let piece (i : StateIndex hyperbolicPlane 0) (hi : i ∈ indices) : relativeShell p :=
    ⟨_, sliceTensor_mem F B p x i (support_nonzero i hi)⟩
  have piece_degree (i : StateIndex hyperbolicPlane 0) (hi : i ∈ indices) :
      piece i hi ∈ GhostSpace p (ghostWeight i) := by
    apply (ghostSpace_iff_slices F B p _ _).mpr
    intro j hj
    change rightSlice F B j (rightSlice F B i x.val ⊗ₜ[ℂ] actualBasis F B i) ≠ 0 at hj
    have heq : i = j := by
      by_contra hne
      rw [rightSlice_tmul, Module.Basis.repr_self_apply, ite_eq_right hne, zero_smul] at hj
      exact hj rfl
    rw [heq]
  have hx : x = ∑ i ∈ indices.attach, piece i i.property := by
    apply (relativeShell p).subtype_injective
    rw [map_sum]
    change x.val = ∑ i ∈ indices.attach, rightSlice F B i.val x.val ⊗ₜ[ℂ] actualBasis F B i.val
    rw [Finset.sum_attach indices (fun i => rightSlice F B i x.val ⊗ₜ[ℂ] actualBasis F B i)]
    exact rightSlices_expand F B x.val
  rw [hx]
  exact Submodule.sum_mem _ (fun i _ =>
    (le_iSup (GhostSpace p) (ghostWeight i.val)) (piece_degree i.val i.property))

include F B in
private theorem assocParity_on_degree (g : ℤ) (x : relativeShell p) (hx : x ∈ GhostSpace p g) :
    assocParity x.val = (-1 : ℂ) ^ g • x.val := by
  classical
  let f (i : StateIndex hyperbolicPlane 0) :=
    rightSlice F B i x.val ⊗ₜ[ℂ] actualBasis F B i
  let indices := (rightSlices F B x.val).support
  have expand : x.val = ∑ i ∈ indices, f i := rightSlices_expand F B x.val
  calc
    assocParity x.val = ∑ i ∈ indices, assocParity (f i) :=
      (congrArg assocParity expand).trans (map_sum _ _ _)
    _ = ∑ i ∈ indices, (-1 : ℂ) ^ g • f i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hcharge := (ghostSpace_iff_slices F B p g x).mp hx i (Finsupp.mem_support_iff.mp hi)
      simp only [f, rightLift_tmul, parity_basis F B, hcharge, TensorProduct.tmul_smul]
    _ = (-1 : ℂ) ^ g • x.val := by rw [← Finset.smul_sum, ← expand]

/-- Canonical ghost parity on a literal relative shell. The empty occupation
vacuum has ghost number zero and sign +1, and the native c1 vacuum has ghost
number one and sign -1. Thus no overall minus is applied to original bc parity. -/
def ghostParity : Module.End ℂ (relativeShell p) :=
  assocParity.restrict (fun x hx => by
    change assocParity x ∈ relativeShell p
    have hle : (⨆ g, GhostSpace p g) ≤
        ((relativeShell p).comap assocParity).comap (relativeShell p).subtype := by
      apply iSup_le
      intro g y hy
      change assocParity y.val ∈ relativeShell p
      rw [assocParity_on_degree planeFrame planeBasis p g y hy]
      exact (relativeShell p).smul_mem _ y.property
    rw [span_ghostSpace planeFrame planeBasis p] at hle
    exact hle (Submodule.mem_top : (⟨x, hx⟩ : relativeShell p) ∈ ⊤))

/-- The shell operator is the actual original bc parity in reassociated form. -/
theorem ghostParity_original (x : relativeShell p) :
    (ghostParity p x).val = reassoc (originalParity (reassoc.symm x.val)) := by
  rw [reassoc_parity, reassoc.apply_symm_apply]
  rfl

/-- On homogeneous states the sign is the integer ghost-number sign. -/
theorem ghostParity_degree (g : ℤ) (x : relativeShell p) (hx : x ∈ GhostSpace p g) :
    ghostParity p x = (-1 : ℂ) ^ g • x := by
  apply Subtype.ext
  exact assocParity_on_degree planeFrame planeBasis p g x hx

theorem ghostParity_square : ghostParity p * ghostParity p = 1 := by
  have hp : LatticeMatterGhostStateField.parity hyperbolicPlane *
      LatticeMatterGhostStateField.parity hyperbolicPlane = 1 := by
    unfold LatticeMatterGhostStateField.parity
    change TensorProduct.map (1 : Module.End ℂ _) _ * TensorProduct.map (1 : Module.End ℂ _) _ = 1
    rw [← TensorProduct.map_mul, mul_one, parity_involution, TensorProduct.map_one]
  have h := congrArg rightLift hp
  simp only [map_mul, map_one] at h
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun h x.val

private theorem parity_anticommutes (f : Module.End ℂ (relativeShell p)) (k : ℤ)
    (hk : (-1 : ℂ) ^ k = -1)
    (hf : ∀ g x, x ∈ GhostSpace p g → f x ∈ GhostSpace p (g + k)) :
    ghostParity p * f = -(f * ghostParity p) := by
  apply sub_eq_zero.mp
  apply LinearMap.ker_eq_top.mp
  have hle : (⨆ g, GhostSpace p g) ≤ LinearMap.ker (ghostParity p * f - -(f * ghostParity p)) := by
    apply iSup_le
    intro g x hx
    change ghostParity p (f x) - -f (ghostParity p x) = 0
    rw [ghostParity_degree p _ _ (hf g x hx), ghostParity_degree p g x hx,
      map_smul, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), hk, mul_neg_one, neg_smul, sub_self]
  rw [span_ghostSpace planeFrame planeBasis p] at hle
  exact top_unique hle

theorem ghostParity_Q :
    ghostParity p * relativeQ F B p = -(relativeQ F B p * ghostParity p) :=
  parity_anticommutes p _ 1 (by norm_num) (RelativeCohomology.relativeQ_degree F B p)

theorem ghostParity_primitive (hp : F.pPlus p ≠ 0) :
    ghostParity p * RelativeCohomology.primitive F B p hp =
      -(RelativeCohomology.primitive F B p hp * ghostParity p) :=
  parity_anticommutes p _ (-1) (by norm_num)
    (fun g x hx => by simpa only [sub_eq_add_neg] using
      RelativeCohomology.primitive_degree F B p hp g x hx)

end GhostParity

section TensorIdentities

variable {L R : Type*} [AddCommGroup L] [AddCommGroup R] [Module ℂ L] [Module ℂ R]

private theorem tensor_neg_left (a : Module.End ℂ L) (b : Module.End ℂ R) :
    TensorProduct.map (-a) b = -TensorProduct.map a b := by
  apply TensorProduct.ext'
  intro x y
  simp only [TensorProduct.map_tmul, LinearMap.neg_apply, TensorProduct.neg_tmul]

private theorem tensor_sub_left (a b : Module.End ℂ L) (c : Module.End ℂ R) :
    TensorProduct.map (a - b) c = TensorProduct.map a c - TensorProduct.map b c := by
  rw [sub_eq_add_neg, TensorProduct.map_add_left, tensor_neg_left, ← sub_eq_add_neg]

private theorem tensor_sub_right (a : Module.End ℂ L) (b c : Module.End ℂ R) :
    TensorProduct.map a (b - c) = TensorProduct.map a b - TensorProduct.map a c := by
  apply TensorProduct.ext'
  intro x y
  simp only [TensorProduct.map_tmul, LinearMap.sub_apply, TensorProduct.tmul_sub]

private def signedDifferential (d : Module.End ℂ L) (e : Module.End ℂ R)
    (γ : Module.End ℂ L) : Module.End ℂ (L ⊗[ℂ] R) :=
  TensorProduct.map d 1 + TensorProduct.map γ e

private def signedHomotopy (h : Module.End ℂ L) (k : Module.End ℂ R)
    (γ E : Module.End ℂ L) : Module.End ℂ (L ⊗[ℂ] R) :=
  TensorProduct.map h 1 + TensorProduct.map (γ * E) k

private theorem signedDifferential_square (d : Module.End ℂ L) (e : Module.End ℂ R)
    (γ : Module.End ℂ L) (hd : d * d = 0) (he : e * e = 0) (hγ : γ * d = -(d * γ)) :
    signedDifferential d e γ * signedDifferential d e γ = 0 := by
  simp only [signedDifferential, add_mul, mul_add, ← TensorProduct.map_mul, one_mul, mul_one,
    hd, he, TensorProduct.map_zero_left, TensorProduct.map_zero_right, hγ, tensor_neg_left,
    add_zero, zero_add, neg_add_cancel]

private theorem signedHomotopy_contraction
    (d h γ E : Module.End ℂ L) (e k G : Module.End ℂ R)
    (γsq : γ * γ = 1) (dγ : γ * d = -(d * γ)) (hγ : γ * h = -(h * γ))
    (γE : γ * E = E * γ) (dE : d * E = 0) (Ed : E * d = 0)
    (left : d * h + h * d = 1 - E) (right : e * k + k * e = 1 - G) :
    signedDifferential d e γ * signedHomotopy h k γ E +
      signedHomotopy h k γ E * signedDifferential d e γ = 1 - TensorProduct.map E G := by
  have a : d * (γ * E) = 0 := by
    rw [← mul_assoc, ← neg_neg (d * γ), ← dγ, neg_mul, mul_assoc, dE, mul_zero, neg_zero]
  have b : (γ * E) * d = 0 := by rw [mul_assoc, Ed, mul_zero]
  have c : γ * (γ * E) = E := by rw [← mul_assoc, γsq, one_mul]
  have f : (γ * E) * γ = E := by rw [mul_assoc, ← γE, c]
  calc
    _ = TensorProduct.map (d * h + h * d) 1 + TensorProduct.map E (e * k + k * e) := by
      simp only [signedDifferential, signedHomotopy, add_mul, mul_add,
        ← TensorProduct.map_mul, one_mul, mul_one, a, b, c, f, hγ, tensor_neg_left,
        TensorProduct.map_zero_left, zero_add, add_zero, TensorProduct.map_add_left,
        TensorProduct.map_add_right]
      abel
    _ = _ := by
      rw [left, right, tensor_sub_left, tensor_sub_right, TensorProduct.map_one]
      abel

end TensorIdentities

/-- The unprojected double-relative complex at the specified pair of momenta. -/
abbrev Shell := relativeShell pL ⊗[ℂ] relativeShell pR

local instance : AddCommGroup (Shell pL pR) :=
  TensorProduct.addCommGroup (R := ℂ) (M := relativeShell pL) (N := relativeShell pR)

/-- The tensor of native transverse light-cone spaces, with zero differential. -/
abbrev Physical := OrbifoldWeight pL ⊗[ℂ] OrbifoldWeight pR

/-- The sum of the actual left differential and the parity-signed actual right differential. -/
def differential : Module.End ℂ (Shell pL pR) :=
  signedDifferential (relativeQ planeFrame planeBasis pL) (relativeQ planeFrame planeBasis pR)
    (ghostParity pL)

/-- The Koszul sign on a homogeneous left factor is fixed by its native ghost number. -/
theorem differential_tmul (g : ℤ) (x : relativeShell pL) (hx : x ∈ GhostSpace pL g)
    (y : relativeShell pR) :
    differential pL pR (x ⊗ₜ[ℂ] y) =
      relativeQ planeFrame planeBasis pL x ⊗ₜ[ℂ] y +
      (-1 : ℂ) ^ g • (x ⊗ₜ[ℂ] relativeQ planeFrame planeBasis pR y) := by
  simp only [differential, signedDifferential, LinearMap.add_apply, TensorProduct.map_tmul,
    Module.End.one_apply, ghostParity_degree pL g x hx, TensorProduct.smul_tmul']

theorem differential_square : differential pL pR * differential pL pR = 0 :=
  signedDifferential_square _ _ _
    (by simpa only [pow_two] using relativeQ_squared planeFrame planeBasis pL)
    (by simpa only [pow_two] using relativeQ_squared planeFrame planeBasis pR)
    (ghostParity_Q planeFrame planeBasis pL)

/-- Total ghost degree is the sum of the two native chiral ghost numbers. -/
def TotalGhostSpace (g : ℤ) : Submodule ℂ (Shell pL pR) :=
  Submodule.span ℂ {z | ∃ (a b : ℤ) (x : relativeShell pL) (y : relativeShell pR),
    x ∈ GhostSpace pL a ∧ y ∈ GhostSpace pR b ∧ a + b = g ∧ z = x ⊗ₜ[ℂ] y}

private theorem tmul_mem_total {a b : ℤ} {x : relativeShell pL} {y : relativeShell pR}
    (hx : x ∈ GhostSpace pL a) (hy : y ∈ GhostSpace pR b) :
    x ⊗ₜ[ℂ] y ∈ TotalGhostSpace pL pR (a + b) :=
  Submodule.subset_span ⟨a, b, x, y, hx, hy, rfl, rfl⟩

/-- The signed BRST differential raises total ghost number by one. -/
theorem differential_degree (g : ℤ) (z : Shell pL pR) (hz : z ∈ TotalGhostSpace pL pR g) :
    differential pL pR z ∈ TotalGhostSpace pL pR (g + 1) := by
  have hle : TotalGhostSpace pL pR g ≤
      (TotalGhostSpace pL pR (g + 1)).comap (differential pL pR) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, b, x, y, hx, hy, rfl, rfl⟩
    change differential pL pR (x ⊗ₜ[ℂ] y) ∈ TotalGhostSpace pL pR (a + b + 1)
    rw [differential_tmul pL pR a x hx]
    apply Submodule.add_mem
    · rw [show a + b + 1 = (a + 1) + b by omega]
      exact tmul_mem_total pL pR
        (RelativeCohomology.relativeQ_degree planeFrame planeBasis pL a x hx) hy
    · rw [show a + b + 1 = a + (b + 1) by omega]
      exact Submodule.smul_mem _ _ (tmul_mem_total pL pR hx
        (RelativeCohomology.relativeQ_degree planeFrame planeBasis pR b y hy))
  exact hle hz

section Retraction

open RelativeCohomology (groundEquiv input input_D)
open LocallyNilpotentPerturbation (locally_nilpotent_perturbation)

private def chiralRetraction (F : NullFrame hyperbolicPlane)
    (B : Module.Basis (Fin 0) ℂ F.K) (p : Charge hyperbolicPlane) (hp : F.pPlus p ≠ 0) :
    FinitePerturbation.Input (R := ℂ) (U := OrbifoldWeight p) (V := relativeShell p) := by
  let c := input F B p hp
  let hn := nilpotent F B p hp
  let e := groundEquiv F B p hp
  obtain ⟨_, _, _, _, hom, sq, hi, ph⟩ := locally_nilpotent_perturbation c hn
  refine
    { d0 := relativeQ F B p
      h := RelativeCohomology.primitive F B p hp
      delta := 0
      i := RelativeCohomology.representative F B p hp
      p := RelativeCohomology.coefficient F B p hp
      d0_sq := by simpa only [pow_two] using relativeQ_squared F B p
      pi := LinearMap.ext (RelativeCohomology.coefficient_representative F B p hp)
      di := LinearMap.ext (RelativeCohomology.representative_closed F B p hp)
      pd := LinearMap.ext (coefficient_differential F B p hp)
      contraction := ?_
      hh := sq
      hi := ?_
      ph := ?_
      perturbed_sq := by simpa only [add_zero, pow_two] using relativeQ_squared F B p }
  · apply LinearMap.ext
    intro x
    let H := LocallyNilpotentPerturbation.H c hn
    let I := LocallyNilpotentPerturbation.I c hn
    let P := LocallyNilpotentPerturbation.P c hn
    change relativeQ F B p (H x) + H (relativeQ F B p x) = x - I (e.symm (e (P x)))
    rw [e.symm_apply_apply]
    have he : c.D (H x) + H (c.D x) = x - I (P x) := LinearMap.congr_fun hom x
    have hD : c.D = relativeQ F B p := input_D F B p hp
    rwa [hD] at he
  · apply LinearMap.ext
    intro u
    exact LinearMap.congr_fun hi (e.symm u)
  · apply LinearMap.ext
    intro x
    let H := LocallyNilpotentPerturbation.H c hn
    let P := LocallyNilpotentPerturbation.P c hn
    change e (P (H x)) = 0
    have h : P (H x) = 0 := LinearMap.congr_fun ph x
    rw [h, e.map_zero]

private theorem projection_parity (F : NullFrame hyperbolicPlane)
    (B : Module.Basis (Fin 0) ℂ F.K) (p : Charge hyperbolicPlane) (hp : F.pPlus p ≠ 0) :
    let c := chiralRetraction F B p hp
    ghostParity p * (c.i.comp c.p) = (c.i.comp c.p) * ghostParity p := by
  let c := chiralRetraction F B p hp
  let γ := ghostParity p
  change γ * (c.i.comp c.p) = (c.i.comp c.p) * γ
  have identity : c.i.comp c.p = 1 - (c.d0 * c.h + c.h * c.d0) := by
    rw [c.contraction, sub_sub_cancel]
  have hd : γ * c.d0 = -(c.d0 * γ) := ghostParity_Q F B p
  have hh : γ * c.h = -(c.h * γ) := ghostParity_primitive F B p hp
  have commute (a b : Module.End ℂ (relativeShell p))
      (ha : γ * a = -(a * γ)) (hb : γ * b = -(b * γ)) :
      γ * (a * b) = (a * b) * γ := by
    apply LinearMap.ext
    intro x
    have hax : γ (a (b x)) = -a (γ (b x)) := LinearMap.congr_fun ha (b x)
    have hbx : γ (b x) = -b (γ x) := LinearMap.congr_fun hb x
    change γ (a (b x)) = a (b (γ x))
    rw [hax, hbx, a.map_neg, neg_neg]
  rw [identity, mul_sub, sub_mul, one_mul, mul_one, mul_add, add_mul,
    commute _ _ hd hh, commute _ _ hh hd]

variable (hL : FL.pPlus pL ≠ 0) (hR : FR.pPlus pR ≠ 0)

/-- The tensor of the native corrected representatives. -/
def representative : Physical pL pR →ₗ[ℂ] Shell pL pR :=
  TensorProduct.map (RelativeCohomology.representative FL BL pL hL)
    (RelativeCohomology.representative FR BR pR hR)

/-- The tensor of the native coefficients. -/
def coefficient : Shell pL pR →ₗ[ℂ] Physical pL pR :=
  TensorProduct.map (RelativeCohomology.coefficient FL BL pL hL)
    (RelativeCohomology.coefficient FR BR pR hR)

/-- The signed tensor contraction applies the right primitive after left retraction. -/
def primitive : Module.End ℂ (Shell pL pR) :=
  signedHomotopy (RelativeCohomology.primitive FL BL pL hL)
    (RelativeCohomology.primitive FR BR pR hR) (ghostParity pL)
    ((RelativeCohomology.representative FL BL pL hL).comp
      (RelativeCohomology.coefficient FL BL pL hL))

private theorem left_repCoeff_tmul (x : relativeShell pL) (y : relativeShell pR) :
    (representative FL FR BL BR pL pR hL hR).comp (coefficient FL FR BL BR pL pR hL hR)
      (x ⊗ₜ[ℂ] y) =
      (RelativeCohomology.representative FL BL pL hL
        (RelativeCohomology.coefficient FL BL pL hL x)) ⊗ₜ[ℂ]
      (RelativeCohomology.representative FR BR pR hR
        (RelativeCohomology.coefficient FR BR pR hR y)) := rfl

theorem representative_chain :
    (differential pL pR).comp (representative FL FR BL BR pL pR hL hR) = 0 := by
  apply TensorProduct.ext'
  intro u v
  change signedDifferential (relativeQ FL BL pL) (relativeQ FR BR pR) (ghostParity pL)
    (RelativeCohomology.representative FL BL pL hL u ⊗ₜ[ℂ]
      RelativeCohomology.representative FR BR pR hR v) = 0
  simp only [signedDifferential, LinearMap.add_apply, TensorProduct.map_tmul,
    Module.End.one_apply, RelativeCohomology.representative_closed, TensorProduct.zero_tmul,
    TensorProduct.tmul_zero, add_zero]

theorem coefficient_chain :
    (coefficient FL FR BL BR pL pR hL hR).comp (differential pL pR) = 0 := by
  apply TensorProduct.ext'
  intro x y
  change coefficient FL FR BL BR pL pR hL hR
    (signedDifferential (relativeQ FL BL pL) (relativeQ FR BR pR) (ghostParity pL)
      (x ⊗ₜ[ℂ] y)) = 0
  simp only [coefficient, signedDifferential, LinearMap.add_apply, map_add,
    TensorProduct.map_tmul, Module.End.one_apply, coefficient_differential,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]

theorem coefficient_representative :
    (coefficient FL FR BL BR pL pR hL hR).comp (representative FL FR BL BR pL pR hL hR) =
      LinearMap.id := by
  apply TensorProduct.ext'
  intro u v
  simp only [coefficient, representative, LinearMap.comp_apply, TensorProduct.map_tmul,
    RelativeCohomology.coefficient_representative, LinearMap.id_apply]

theorem contraction :
    differential pL pR * primitive FL FR BL BR pL pR hL hR +
      primitive FL FR BL BR pL pR hL hR * differential pL pR =
      1 - (representative FL FR BL BR pL pR hL hR).comp (coefficient FL FR BL BR pL pR hL hR) := by
  let c := chiralRetraction FL BL pL hL
  let b := chiralRetraction FR BR pR hR
  let E := c.i.comp c.p
  have hrep :
      (representative FL FR BL BR pL pR hL hR).comp (coefficient FL FR BL BR pL pR hL hR) =
        TensorProduct.map E (b.i.comp b.p) := TensorProduct.ext'
    (left_repCoeff_tmul FL FR BL BR pL pR hL hR)
  rw [hrep]
  have dE : c.d0 * E = 0 := by
    change c.d0.comp (c.i.comp c.p) = 0
    rw [← LinearMap.comp_assoc, c.di, LinearMap.zero_comp]
  have Ed : E * c.d0 = 0 := by
    change (c.i.comp c.p).comp c.d0 = 0
    rw [LinearMap.comp_assoc, c.pd, LinearMap.comp_zero]
  exact signedHomotopy_contraction c.d0 c.h (ghostParity pL) E b.d0 b.h (b.i.comp b.p)
    (ghostParity_square pL) (ghostParity_Q FL BL pL) (ghostParity_primitive FL BL pL hL)
    (projection_parity FL BL pL hL) dE Ed c.contraction b.contraction

/-- The strong contraction squares to zero and annihilates the inclusion
and projection on their respective sides. -/
theorem primitive_side_conditions :
    let h := primitive FL FR BL BR pL pR hL hR
    h * h = 0 ∧
      h.comp (representative FL FR BL BR pL pR hL hR) = 0 ∧
      (coefficient FL FR BL BR pL pR hL hR).comp h = 0 := by
  let c := chiralRetraction FL BL pL hL
  let b := chiralRetraction FR BR pR hR
  let E := c.i.comp c.p
  let γ := ghostParity pL
  have hE : c.h * E = 0 := by
    change c.h.comp (c.i.comp c.p) = 0
    rw [← LinearMap.comp_assoc, c.hi, LinearMap.zero_comp]
  have Eh : E * c.h = 0 := by
    change (c.i.comp c.p).comp c.h = 0
    rw [LinearMap.comp_assoc, c.ph, LinearMap.comp_zero]
  have hγ : γ * c.h = -(c.h * γ) := ghostParity_primitive FL BL pL hL
  have hhγ : c.h * (γ * E) = 0 := by
    apply LinearMap.ext
    intro x
    change c.h (γ (E x)) = 0
    have h := LinearMap.congr_fun hγ (E x)
    change γ (c.h (E x)) = -c.h (γ (E x)) at h
    have hz : c.h (E x) = 0 := LinearMap.congr_fun hE x
    rw [hz, map_zero, eq_comm, neg_eq_zero] at h
    exact h
  have hright : TensorProduct.map (γ * E * (γ * E)) (b.h * b.h) = 0 := by
    rw [b.hh, TensorProduct.map_zero_right]
  refine ⟨?_, ?_, ?_⟩
  · change signedHomotopy c.h b.h γ E * signedHomotopy c.h b.h γ E = 0
    simp only [signedHomotopy, add_mul, mul_add, ← TensorProduct.map_mul, one_mul, mul_one,
      c.hh, hright, hhγ, mul_assoc γ E c.h, Eh, mul_zero,
      TensorProduct.map_zero_left, add_zero]
  · apply TensorProduct.ext'
    intro u v
    change signedHomotopy c.h b.h γ E (c.i u ⊗ₜ[ℂ] b.i v) = 0
    have hu : c.h (c.i u) = 0 := LinearMap.congr_fun c.hi u
    have hv : b.h (b.i v) = 0 := LinearMap.congr_fun b.hi v
    simp only [signedHomotopy, LinearMap.add_apply, TensorProduct.map_tmul, hu, hv,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]
  · apply TensorProduct.ext'
    intro x y
    change TensorProduct.map c.p b.p (signedHomotopy c.h b.h γ E (x ⊗ₜ[ℂ] y)) = 0
    have hx : c.p (c.h x) = 0 := LinearMap.congr_fun c.ph x
    have hy : b.p (b.h y) = 0 := LinearMap.congr_fun b.ph y
    simp only [signedHomotopy, LinearMap.add_apply, TensorProduct.map_tmul, map_add, hx, hy,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]

/-- Literal cycles modulo the image of the actual signed differential. -/
abbrev Cohomology :=
  FinitePerturbation.Cohomology (differential pL pR) (differential_square pL pR)

local instance : AddCommGroup (LinearMap.ker (differential pL pR)) :=
  Submodule.addCommGroup (R := ℂ) (M := Shell pL pR) (LinearMap.ker (differential pL pR))

private def cycleCoefficient : LinearMap.ker (differential pL pR) →ₗ[ℂ] Physical pL pR :=
  (coefficient FL FR BL BR pL pR hL hR).comp (LinearMap.ker (differential pL pR)).subtype

private theorem cycle_sub_rep (x : Shell pL pR) (hx : differential pL pR x = 0) :
    differential pL pR (primitive FL FR BL BR pL pR hL hR x) =
      x - representative FL FR BL BR pL pR hL hR (coefficient FL FR BL BR pL pR hL hR x) := by
  simpa only [LinearMap.add_apply, Module.End.mul_apply, hx, map_zero, add_zero,
    LinearMap.sub_apply, Module.End.one_apply, LinearMap.comp_apply] using
    LinearMap.congr_fun (contraction FL FR BL BR pL pR hL hR) x

/-- The tensor representative has native bidegree (1, 1), hence total degree two. -/
theorem representative_degree (u : Physical pL pR) :
    representative FL FR BL BR pL pR hL hR u ∈ TotalGhostSpace pL pR 2 := by
  let r := representative FL FR BL BR pL pR hL hR
  have hle : (⊤ : Submodule ℂ (Physical pL pR)) ≤
      (TotalGhostSpace pL pR 2).comap r := by
    rw [← TensorProduct.span_tmul_eq_top ℂ (OrbifoldWeight pL) (OrbifoldWeight pR)]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, y, rfl⟩
    change RelativeCohomology.representative FL BL pL hL x ⊗ₜ[ℂ]
      RelativeCohomology.representative FR BR pR hR y ∈ TotalGhostSpace pL pR ((1 : ℤ) + 1)
    exact tmul_mem_total pL pR
      (RelativeCohomology.representative_degree FL BL pL hL x)
      (RelativeCohomology.representative_degree FR BR pR hR y)
  exact hle (Submodule.mem_top : u ∈ ⊤)

/-- The signed tensor primitive lowers total ghost number by one. -/
theorem primitive_degree (g : ℤ) (z : Shell pL pR) (hz : z ∈ TotalGhostSpace pL pR g) :
    primitive FL FR BL BR pL pR hL hR z ∈ TotalGhostSpace pL pR (g - 1) := by
  have hle : TotalGhostSpace pL pR g ≤
      (TotalGhostSpace pL pR (g - 1)).comap (primitive FL FR BL BR pL pR hL hR) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, b, x, y, hx, hy, rfl, rfl⟩
    change primitive FL FR BL BR pL pR hL hR (x ⊗ₜ[ℂ] y) ∈ TotalGhostSpace pL pR (a + b - 1)
    simp only [primitive, signedHomotopy, LinearMap.add_apply, TensorProduct.map_tmul,
      Module.End.one_apply, Module.End.mul_apply, LinearMap.comp_apply]
    apply Submodule.add_mem
    · rw [show a + b - 1 = (a - 1) + b by omega]
      exact tmul_mem_total pL pR (RelativeCohomology.primitive_degree FL BL pL hL a x hx) hy
    · by_cases ha : a = 1
      · subst a
        have hrep := RelativeCohomology.representative_degree FL BL pL hL
          (RelativeCohomology.coefficient FL BL pL hL x)
        have hleft : ghostParity pL (RelativeCohomology.representative FL BL pL hL
            (RelativeCohomology.coefficient FL BL pL hL x)) ∈ GhostSpace pL 1 := by
          rw [ghostParity_degree pL 1 _ hrep]
          exact (GhostSpace pL 1).smul_mem _ hrep
        rw [show 1 + b - 1 = 1 + (b - 1) by omega]
        exact tmul_mem_total pL pR hleft (RelativeCohomology.primitive_degree FR BR pR hR b y hy)
      · rw [RelativeCohomology.coefficient_eq_zero_of_degree_ne_one FL BL pL hL a ha x hx,
          map_zero, map_zero, TensorProduct.zero_tmul]
        exact Submodule.zero_mem _
  exact hle hz

/-- The physical coefficient is supported in total ghost degree two. -/
theorem coefficient_eq_zero_of_degree_ne_two (g : ℤ) (hg : g ≠ 2) (z : Shell pL pR)
    (hz : z ∈ TotalGhostSpace pL pR g) :
    coefficient FL FR BL BR pL pR hL hR z = 0 := by
  have hle : TotalGhostSpace pL pR g ≤ LinearMap.ker (coefficient FL FR BL BR pL pR hL hR) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, b, x, y, hx, hy, hab, rfl⟩
    change coefficient FL FR BL BR pL pR hL hR (x ⊗ₜ[ℂ] y) = 0
    rw [coefficient, TensorProduct.map_tmul]
    by_cases ha : a = 1
    · have hb : b ≠ 1 := by omega
      rw [RelativeCohomology.coefficient_eq_zero_of_degree_ne_one FR BR pR hR b hb y hy,
        TensorProduct.tmul_zero]
    · rw [RelativeCohomology.coefficient_eq_zero_of_degree_ne_one FL BL pL hL a ha x hx,
        TensorProduct.zero_tmul]
  exact hle hz

include FL FR BL BR hL hR in
/-- A cycle of total degree other than two is already exact through the preceding degree. -/
theorem exact_of_degree_ne_two (g : ℤ) (hg : g ≠ 2) (z : Shell pL pR)
    (hz : z ∈ TotalGhostSpace pL pR g) (hd : differential pL pR z = 0) :
    ∃ y ∈ TotalGhostSpace pL pR (g - 1), differential pL pR y = z := by
  refine ⟨primitive FL FR BL BR pL pR hL hR z,
    primitive_degree FL FR BL BR pL pR hL hR g z hz, ?_⟩
  rw [cycle_sub_rep FL FR BL BR pL pR hL hR z hd,
    coefficient_eq_zero_of_degree_ne_two FL FR BL BR pL pR hL hR g hg z hz, map_zero, sub_zero]

private theorem cycleCoefficient_surjective :
    Function.Surjective (cycleCoefficient FL FR BL BR pL pR hL hR) := by
  intro u
  refine ⟨⟨representative FL FR BL BR pL pR hL hR u, ?_⟩, ?_⟩
  · exact LinearMap.congr_fun (representative_chain FL FR BL BR pL pR hL hR) u
  · exact LinearMap.congr_fun (coefficient_representative FL FR BL BR pL pR hL hR) u

private theorem boundaries_eq_ker :
    FinitePerturbation.Boundaries (differential pL pR) (differential_square pL pR) =
      LinearMap.ker (cycleCoefficient FL FR BL BR pL pR hL hR) := by
  ext x
  change (∃ y, FinitePerturbation.boundaryMap (differential pL pR)
    (differential_square pL pR) y = x) ↔ coefficient FL FR BL BR pL pR hL hR x.val = 0
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (coefficient_chain FL FR BL BR pL pR hL hR) y
  · intro hx
    refine ⟨primitive FL FR BL BR pL pR hL hR x.val, Subtype.ext ?_⟩
    change differential pL pR (primitive FL FR BL BR pL pR hL hR x.val) = x.val
    rw [cycle_sub_rep FL FR BL BR pL pR hL hR x.val x.property, hx, map_zero, sub_zero]

/-- The double-relative BRST quotient is the tensor of the two native transverse spaces. -/
def cohomologyEquiv : Cohomology pL pR ≃ₗ[ℂ] Physical pL pR := by
  let b := FinitePerturbation.Boundaries (differential pL pR) (differential_square pL pR)
  let f := cycleCoefficient FL FR BL BR pL pR hL hR
  have hb : b = LinearMap.ker f := boundaries_eq_ker FL FR BL BR pL pR hL hR
  have hs : Function.Surjective f := cycleCoefficient_surjective FL FR BL BR pL pR hL hR
  change (LinearMap.ker (differential pL pR) ⧸ b) ≃ₗ[ℂ] Physical pL pR
  exact (b.quotEquivOfEq (LinearMap.ker f) hb).trans (f.quotKerEquivOfSurjective hs)

/-- The equivalence reads off the tensor coefficient on every genuine cycle. -/
theorem cohomologyEquiv_mk (x : LinearMap.ker (differential pL pR)) :
    cohomologyEquiv FL FR BL BR pL pR hL hR (Submodule.Quotient.mk x) =
      coefficient FL FR BL BR pL pR hL hR x.val := rfl

/-- In the inverse direction the class is represented by the native tensor inclusion. -/
theorem cohomologyEquiv_symm_apply (u : Physical pL pR) :
    (cohomologyEquiv FL FR BL BR pL pR hL hR).symm u =
      Submodule.Quotient.mk ⟨representative FL FR BL BR pL pR hL hR u,
        LinearMap.congr_fun (representative_chain FL FR BL BR pL pR hL hR) u⟩ := by
  apply (cohomologyEquiv FL FR BL BR pL pR hL hR).injective
  rw [LinearEquiv.apply_symm_apply, cohomologyEquiv_mk]
  exact (LinearMap.congr_fun (coefficient_representative FL FR BL BR pL pR hL hR) u).symm

end Retraction

/-- Each nonzero momentum admits its own light-cone polarization. -/
def cohomologyEquivNonzero (hpL : pL ≠ 0) (hpR : pR ≠ 0) :
    Cohomology pL pR ≃ₗ[ℂ] Physical pL pR := by
  by_cases left : planeFrame.pPlus pL ≠ 0
  · by_cases right : planeFrame.pPlus pR ≠ 0
    · exact cohomologyEquiv planeFrame planeFrame planeBasis planeBasis pL pR left right
    · exact cohomologyEquiv planeFrame swappedPlaneFrame planeBasis swappedPlaneBasis pL pR left
        ((planeFrame_covers_nonzero pR hpR).resolve_left right)
  · have left' := (planeFrame_covers_nonzero pL hpL).resolve_left left
    by_cases right : planeFrame.pPlus pR ≠ 0
    · exact cohomologyEquiv swappedPlaneFrame planeFrame swappedPlaneBasis planeBasis pL pR left' right
    · exact cohomologyEquiv swappedPlaneFrame swappedPlaneFrame swappedPlaneBasis swappedPlaneBasis
        pL pR left' ((planeFrame_covers_nonzero pR hpR).resolve_left right)

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedRelative
