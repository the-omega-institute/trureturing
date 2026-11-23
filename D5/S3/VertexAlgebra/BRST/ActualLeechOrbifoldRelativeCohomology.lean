/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeCohomology
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeCohomology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative BRST cohomology of the actual Leech orbifold at nonzero plane momentum. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightConeDegreeBounds
import Mathlib.LinearAlgebra.Isomorphisms

/-!
The lattice quartet retract is lifted through the identity on the actual
orbifold. Its range on the relative shell is identified by the right basis
coefficient of the plane ground state and the native c1 vacuum. The original
differential is recovered by the Gugenheim–Lambe–Stasheff perturbation formula
in LocallyNilpotentPerturbationCohomology. The bounded light-cone filtration
forces the transferred differential to vanish.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST

open ActualLeechOrbifoldMatter (Orbifold mode)
open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge Carrier Oscillator)
open LatticePositiveEnergy (chargeEnergy)
open LatticeLightConeCoordinates (NullFrame)
open LatticeQuartetContraction
open LatticeBRSTModeFiltration (degree exponentDegree)
open LatticeRelativeShellDegreeBounds (frameEnergy)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (ket)
open D5.S3.Quantum.Fermionic.BcGhostQuartetCount (c1vac c1vac_eq)
open D5.S3.Quantum.Fermionic.BcGhostCharge (charge)
open D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy
  (energy relativeEnergy siteEnergy_one)
open D5.S3.HomologicalAlgebra
open FiniteSupportEndomorphismCalculus (projectZero diagonal_coefficient)

open private rightLift_tmul rightSlice_tmul rightSlice_chargeProject
  assocB0_eq from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone
open private rightBasisEnergy originalEnergy_diagonal rightSlice_assocE
  eq_zero_of_all_rightSlices from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightConeDegreeBounds

namespace RelativeCohomology

variable (F : NullFrame hyperbolicPlane) (B : Module.Basis (Fin 0) ℂ F.K)
variable (p : Charge hyperbolicPlane) (hp : F.pPlus p ≠ 0)

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup

local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup (relativeShell p)

include hp in
private theorem lifted_contraction :
    rightLift (d0 F p) * rightLift (h F B p) +
      rightLift (h F B p) * rightLift (d0 F p) = 1 - rightLift (P0 F B) := by
  simpa only [map_mul, map_add, map_sub, map_one] using
    congrArg rightLift (homotopy_contraction F B p hp)

include hp in
/-- The zero-quartet projector restricted to the actual relative shell. -/
def projection0 : Module.End ℂ (relativeShell p) :=
  (rightLift (P0 F B)).restrict (fun x hx => by
    let y : relativeShell p := ⟨x, hx⟩
    let dy := relativeD0 F B p (relativeH F B p y)
    let hy := relativeH F B p (relativeD0 F B p y)
    have heq := LinearMap.congr_fun (lifted_contraction F B p hp) x
    change dy.val + hy.val = x - rightLift (P0 F B) x at heq
    have hv : rightLift (P0 F B) x = x - (dy.val + hy.val) := by
      rw [heq]
      exact (sub_sub_cancel x (rightLift (P0 F B) x)).symm
    rw [hv]
    exact (relativeShell p).sub_mem hx ((relativeShell p).add_mem dy.property hy.property))

private theorem projection0_idem :
    projection0 F B p hp * projection0 F B p hp = projection0 F B p hp := by
  have hh := congrArg rightLift (spectral_projection_inverse F B).2.2.1
  rw [map_mul] at hh
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun hh x.val

/-- The range of the lifted projector within the literal relative shell. -/
abbrev Ground := LinearMap.range (projection0 F B p hp)

local instance : AddCommGroup (Ground F B p hp) :=
  Submodule.addCommGroup (Ground F B p hp)

private theorem projection0_ground (u : Ground F B p hp) :
    projection0 F B p hp u.val = u.val := by
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp u.property
  rw [← hx]
  exact LinearMap.congr_fun (projection0_idem F B p hp) x

private theorem relativeD0_add_delta :
    relativeD0 F B p + relativeDelta F B p = relativeQ F B p := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change rightLift (d0 F p) x.val + (assocQ x.val - rightLift (d0 F p) x.val) =
    assocQ x.val
  rw [add_comm (rightLift (d0 F p) x.val), sub_add_cancel]

/-- The contraction data use the literal restricted Q through delta = Q - d0. -/
def input : FinitePerturbation.Input (R := ℂ) (U := Ground F B p hp)
    (V := relativeShell p) where
  d0 := relativeD0 F B p
  h := relativeH F B p
  delta := relativeDelta F B p
  i := (Ground F B p hp).subtype
  p := (projection0 F B p hp).rangeRestrict
  d0_sq := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hh := congrArg rightLift (d0_square F p)
    simp only [map_mul, map_zero] at hh
    exact LinearMap.congr_fun hh x.val
  pi := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    exact projection0_ground F B p hp u
  di := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    have hh := congrArg rightLift (d0_mul_P0 F B p)
    simp only [map_mul, map_zero] at hh
    change rightLift (d0 F p) u.val.val = 0
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp u.property
    rw [← hx]
    exact LinearMap.congr_fun hh x.val
  pd := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg rightLift (P0_mul_d0 F B p)
    simp only [map_mul, map_zero] at hh
    exact LinearMap.congr_fun hh x.val
  contraction := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (lifted_contraction F B p hp) x.val
  hh := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hh := congrArg rightLift (homotopy_square F B p)
    simp only [map_mul, map_zero] at hh
    exact LinearMap.congr_fun hh x.val
  hi := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    have hh := congrArg rightLift (h_mul_P0 F B p)
    simp only [map_mul, map_zero] at hh
    change rightLift (h F B p) u.val.val = 0
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp u.property
    rw [← hx]
    exact LinearMap.congr_fun hh x.val
  ph := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg rightLift (P0_mul_h F B p)
    simp only [map_mul, map_zero] at hh
    exact LinearMap.congr_fun hh x.val
  perturbed_sq := by
    rw [relativeD0_add_delta F B p, ← pow_two]
    exact relativeQ_squared F B p

theorem input_D : (input F B p hp).D = relativeQ F B p :=
  relativeD0_add_delta F B p

private def groundIndex : StateIndex hyperbolicPlane 0 := (⟨p, 0⟩, {1})

private theorem ground_count : totalCount (groundIndex p) = 0 := by
  apply (totalCount_zero_iff _).mpr
  exact ⟨fun _ => ⟨rfl, rfl⟩, Or.inl rfl⟩

private theorem ground_charge : charge (groundIndex p).2 = 1 := by
  exact (by decide : charge ({1} : Finset ℕ) = 1)

private theorem ground_degree : degree (groundIndex p) = 0 := by
  change exponentDegree (0 : Exponents 0) + charge (groundIndex p).2 - 1 = 0
  rw [ground_charge]
  simp [exponentDegree]

private theorem ground_energy :
    rightBasisEnergy (groundIndex p) = chargeEnergy hyperbolicPlane p - 1 := by
  simp [rightBasisEnergy, groundIndex, frameEnergy, relativeEnergy, energy, siteEnergy_one]

private theorem zero_count_index (i : StateIndex hyperbolicPlane 0)
    (hq : i.1.1 = p) (hb : 3 ∉ i.2) (hc : totalCount i = 0) :
    i = groundIndex p := by
  obtain ⟨⟨q, m⟩, S⟩ := i
  obtain ⟨hm, hS⟩ := (totalCount_zero_iff _).mp hc
  have hm0 : m = 0 := by
    ext ⟨label, r⟩
    change m (label, r) = 0
    rcases label with u | (u | j)
    · cases u
      exact (hm r).1
    · cases u
      exact (hm r).2
    · exact Fin.elim0 j
  change q = p at hq
  subst q
  subst m
  rcases hS with hS | hS
  · change S = {1} at hS
    subst S
    rfl
  · exfalso
    apply hb
    change 3 ∈ S
    change S = {1, 3} at hS
    rw [hS]
    simp

/-- The unperturbed right vector is the plane vacuum at p and the native c1 vacuum. -/
theorem groundBasis_eq :
    actualBasis F B (groundIndex p) =
      Finsupp.single p (1 : Oscillator hyperbolicPlane) ⊗ₜ[ℂ] c1vac := by
  change actualBasis F B (⟨p, 0⟩, {1}) = _
  rw [actualBasis_apply, c1vac_eq, sector,
    MvPolynomial.monomial_zero', MvPolynomial.C_1]
  have hu : (F.coordinateEquiv B).symm 1 = 1 :=
    (F.coordinateEquiv B).symm.toAlgHom.map_one
  rw [hu]

private theorem slice_projection0 (i : StateIndex hyperbolicPlane 0) (x : relativeShell p) :
    rightSlice F B i (projection0 F B p hp x).val =
      if totalCount i = 0 then rightSlice F B i x.val else 0 := by
  change rightSlice F B i (rightLift (P0 F B) x.val) = _
  generalize x.val = y
  classical
  induction y using TensorProduct.inductionOn with
  | tmul v y =>
    rw [rightLift_tmul, rightSlice_tmul, rightSlice_tmul, P0, projectZero, diagonal_coefficient]
    by_cases hi : totalCount i = 0 <;> simp [hi]
  | add y z hy hz =>
    rw [map_add (rightLift (P0 F B)), map_add (rightSlice F B i), hy, hz]
    by_cases hi : totalCount i = 0 <;> simp [hi]

private theorem projection0_support (x : relativeShell p) (i : StateIndex hyperbolicPlane 0)
    (hi : rightSlice F B i (projection0 F B p hp x).val ≠ 0) :
    i = groundIndex p := by
  have hc : totalCount i = 0 := by
    by_contra hn
    exact hi (by rw [slice_projection0 F B p hp, ite_eq_right hn])
  have hs := relativeShell_rightSlice_bounds F B p _ (projection0 F B p hp x).property i hi
  exact zero_count_index p i hs.1 hs.2.1 hc

private theorem ground_support (u : Ground F B p hp) (i : StateIndex hyperbolicPlane 0)
    (hi : rightSlice F B i u.val.val ≠ 0) :
    i = groundIndex p := by
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp u.property
  rw [← hx] at hi
  exact projection0_support F B p hp x i hi

private theorem ground_filtration (u : Ground F B p hp) :
    u.val.val ∈ momentumFiltration F B p 0 := by
  apply (mem_momentumFiltration_iff F B p 0 u.val.val).mpr
  intro i hi
  rw [ground_support F B p hp u i hi, ground_degree]
  exact ⟨rfl, le_rfl⟩

private theorem projection0_kills_filtration (x : relativeShell p)
    (hx : x.val ∈ momentumFiltration F B p 1) :
    projection0 F B p hp x = 0 := by
  apply Subtype.ext
  apply eq_zero_of_all_rightSlices F B
  intro i
  by_contra hi
  have hi0 := projection0_support F B p hp x i hi
  subst i
  have his : rightSlice F B (groundIndex p) x.val ≠ 0 := by
    rwa [slice_projection0 F B p hp, ite_eq_left (ground_count p)] at hi
  have hd := ((mem_momentumFiltration_iff F B p 1 x.val).mp hx _ his).2
  rw [ground_degree] at hd
  omega

/-- The required conformal weight in the actual orbifold matter module. -/
abbrev OrbifoldWeight := (mode 0).eigenspace ((1 - p (0 : Fin 2) * p (1 : Fin 2) : ℤ) : ℂ)

private theorem ground_eigenvalue :
    ((1 - p (0 : Fin 2) * p (1 : Fin 2) : ℤ) : ℂ) = -(rightBasisEnergy (groundIndex p) : ℂ) := by
  rw [ground_energy, plane_chargeEnergy]
  push_cast
  ring

private def groundTensor : Orbifold →ₗ[ℂ] AssocState :=
  (TensorProduct.mk ℂ Orbifold (State hyperbolicPlane)).flip (actualBasis F B (groundIndex p))

private theorem slice_groundTensor (v : Orbifold) (i : StateIndex hyperbolicPlane 0) :
    rightSlice F B i (groundTensor F B p v) = if i = groundIndex p then v else 0 := by
  classical
  change rightSlice F B i (v ⊗ₜ[ℂ] actualBasis F B (groundIndex p)) = _
  rw [rightSlice_tmul, Module.Basis.repr_self_apply]
  by_cases hi : i = groundIndex p
  · subst i
    simp
  · simp [hi, Ne.symm hi]

private theorem groundTensor_mem_shell (v : OrbifoldWeight p) :
    groundTensor F B p v.val ∈ relativeShell p := by
  classical
  apply (mem_relativeShell_iff p _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply (rightSlices F B).injective
    apply Finsupp.ext
    intro i
    change rightSlice F B i (rightLift (chargeProject p) (groundTensor F B p v.val)) =
      rightSlice F B i (groundTensor F B p v.val)
    rw [rightSlice_chargeProject F B, slice_groundTensor F B p]
    by_cases hi : i = groundIndex p
    · subst i
      simp [groundIndex]
    · simp [hi]
  · change assocB0 (v.val ⊗ₜ[ℂ] actualBasis F B (groundIndex p)) = 0
    rw [assocB0_eq, rightLift_tmul]
    have hb : ghostB0 (actualBasis F B (groundIndex p)) = 0 := by
      apply (b0_coefficients F B _).mpr
      intro i hi
      have hn : groundIndex p ≠ i := by
        rintro rfl
        simp [groundIndex] at hi
      rw [Module.Basis.repr_self_apply, ite_eq_right hn]
    rw [hb, TensorProduct.tmul_zero]
  · apply eq_zero_of_all_rightSlices F B
    intro i
    rw [rightSlice_assocE F B, slice_groundTensor F B p]
    by_cases hi : i = groundIndex p
    · subst i
      rw [ite_eq_left rfl, Module.End.mem_eigenspace_iff.mp v.property, ground_eigenvalue p,
        neg_smul, neg_add_cancel]
    · simp [hi]

private def groundShell : OrbifoldWeight p →ₗ[ℂ] relativeShell p :=
  ((groundTensor F B p).comp (OrbifoldWeight p).subtype).codRestrict _
    (groundTensor_mem_shell F B p)

private theorem projection0_groundShell (v : OrbifoldWeight p) :
    projection0 F B p hp (groundShell F B p v) = groundShell F B p v := by
  apply Subtype.ext
  change rightLift (P0 F B) (v.val ⊗ₜ[ℂ] actualBasis F B (groundIndex p)) = _
  rw [rightLift_tmul, P0_basis F B, ite_eq_left (ground_count p), one_smul]
  rfl

private def groundInclusion : OrbifoldWeight p →ₗ[ℂ] Ground F B p hp :=
  (groundShell F B p).codRestrict _
    (fun v => LinearMap.mem_range.mpr ⟨_, projection0_groundShell F B p hp v⟩)

private def groundCoefficient : Ground F B p hp →ₗ[ℂ] OrbifoldWeight p :=
  ((rightSlice F B (groundIndex p)).comp
    ((relativeShell p).subtype.comp (Ground F B p hp).subtype)).codRestrict _ (by
      intro u
      apply Module.End.mem_eigenspace_iff.mpr
      change mode 0 (rightSlice F B (groundIndex p) u.val.val) = _
      have he := (mem_relativeShell_iff p _).mp u.val.property
      have hs := rightSlice_assocE F B (groundIndex p) u.val.val
      rw [he.2.2, map_zero] at hs
      rw [ground_eigenvalue p, neg_smul]
      exact eq_neg_of_add_eq_zero_left hs.symm)

/-- The range of the projector is read directly on the actual orbifold
coefficient. The inverse inserts the plane vacuum and c1 vacuum. -/
def groundEquiv : Ground F B p hp ≃ₗ[ℂ] OrbifoldWeight p where
  toLinearMap := groundCoefficient F B p hp
  invFun := groundInclusion F B p hp
  left_inv := by
    intro u
    apply Subtype.ext
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply eq_zero_of_all_rightSlices F B
    intro i
    change rightSlice F B i
      (groundTensor F B p (rightSlice F B (groundIndex p) u.val.val) - u.val.val) = 0
    rw [(rightSlice F B i).map_sub, slice_groundTensor F B p]
    by_cases hi : i = groundIndex p
    · subst i
      rw [ite_eq_left rfl, sub_self]
    · have hz : rightSlice F B i u.val.val = 0 := by
        by_contra hn
        exact hi (ground_support F B p hp u i hn)
      rw [ite_eq_right hi, hz, sub_self]
  right_inv := by
    intro v
    apply Subtype.ext
    change rightSlice F B (groundIndex p) (groundTensor F B p v.val) = v.val
    rw [slice_groundTensor F B p, ite_eq_left rfl]

/-- The inverse ground identification inserts the explicit native vacua. -/
theorem groundEquiv_symm_value (v : OrbifoldWeight p) :
    ((groundEquiv F B p hp).symm v).val.val =
      v.val ⊗ₜ[ℂ] (Finsupp.single p (1 : Oscillator hyperbolicPlane) ⊗ₜ[ℂ] c1vac) := by
  change v.val ⊗ₜ[ℂ] actualBasis F B (groundIndex p) = _
  rw [groundBasis_eq F B p]

private def cutoff : ℕ := 2 * (1 - chargeEnergy hyperbolicPlane p).toNat + 1

private theorem nilpotent_power :
    ((input F B p hp).h * (input F B p hp).delta) ^ cutoff p = 0 :=
  relative_h_remainder_pow_eq_zero F B p

private theorem nilpotent (x : relativeShell p) :
    ∃ n : ℕ, (((input F B p hp).h * (input F B p hp).delta) ^ n) x = 0 := by
  refine ⟨cutoff p, ?_⟩
  rw [nilpotent_power F B p hp, LinearMap.zero_apply]

open LocallyNilpotentPerturbation (K I P H transferred locally_nilpotent_perturbation)

private theorem K_mem (S : Submodule ℂ (relativeShell p))
    (hS : ∀ y ∈ S, ((input F B p hp).h * (input F B p hp).delta) y ∈ S)
    (x : relativeShell p) (hx : x ∈ S) :
    K (input F B p hp) (nilpotent F B p hp) x ∈ S := by
  let A := (input F B p hp).h * (input F B p hp).delta
  have hpow (n : ℕ) : (A ^ n) x ∈ S := by
    induction n with
    | zero => simpa only [pow_zero, Module.End.one_apply] using hx
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hS _ ih
  have hz : (A ^ cutoff p) x = 0 :=
    LinearMap.congr_fun (nilpotent_power F B p hp) x
  rw [LocallyNilpotentPerturbation.K_apply_eq_inversePolynomial _ _ x (cutoff p) hz]
  change FinitePerturbation.inversePolynomial A (cutoff p) x ∈ S
  simp only [FinitePerturbation.inversePolynomial, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro n _
  rw [neg_pow, Module.End.mul_apply, neg_one_pow_eq_ite]
  split_ifs
  · simpa only [Module.End.one_apply] using hpow n
  · simpa only [LinearMap.neg_apply, Module.End.one_apply] using S.neg_mem (hpow n)

private theorem K_preserves_filtration (a : ℤ) (x : relativeShell p)
    (hx : x.val ∈ momentumFiltration F B p a) :
    (K (input F B p hp) (nilpotent F B p hp) x).val ∈ momentumFiltration F B p a := by
  let S := (momentumFiltration F B p a).comap (relativeShell p).subtype
  apply K_mem F B p hp S _ x hx
  intro y hy
  apply (mem_momentumFiltration_iff F B p a _).mpr
  intro i hi
  have hr := (relative_remainder_raises F B p a y hy).2
  have hs := (mem_momentumFiltration_iff F B p (a + 1) _).mp hr i hi
  exact ⟨hs.1, (by omega : a ≤ a + 1).trans hs.2⟩

/-- The actual transferred differential vanishes by the light-cone filtration. -/
theorem transferred_eq_zero :
    transferred (input F B p hp) (nilpotent F B p hp) = 0 := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  let y := K (input F B p hp) (nilpotent F B p hp) u.val
  change projection0 F B p hp (relativeDelta F B p y) = 0
  apply projection0_kills_filtration F B p hp
  exact (relative_remainder_raises F B p 0 y
    (K_preserves_filtration F B p hp 0 u.val (ground_filtration F B p hp u))).1

private def zeroCohomologyEquiv {W : Type*} [AddCommGroup W] [Module ℂ W]
    (d : Module.End ℂ W) (hs : d * d = 0) (hz : d = 0) :
    FinitePerturbation.Cohomology d hs ≃ₗ[ℂ] W := by
  subst d
  have hb : FinitePerturbation.Boundaries (0 : Module.End ℂ W) hs = ⊥ := by
    change LinearMap.range (FinitePerturbation.boundaryMap 0 hs) = ⊥
    apply LinearMap.range_eq_bot.mpr
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  exact ((FinitePerturbation.Boundaries (0 : Module.End ℂ W) hs).quotEquivOfEqBot hb).trans
    ((LinearEquiv.ofEq _ _ (LinearMap.ker_zero : LinearMap.ker (0 : Module.End ℂ W) = ⊤)).trans
      Submodule.topEquiv)

private def cohomologyCongr {W : Type*} [AddCommGroup W] [Module ℂ W]
    {d e : Module.End ℂ W} (h : d = e) (hd : d * d = 0) (he : e * e = 0) :
    FinitePerturbation.Cohomology d hd ≃ₗ[ℂ] FinitePerturbation.Cohomology e he := by
  subst e
  exact LinearEquiv.refl ℂ _

/-- The literal kernel modulo the actual image on the reassociated relative shell. -/
abbrev Cohomology :=
  FinitePerturbation.Cohomology (R := ℂ) (M := relativeShell p) (relativeQ F B p)
  (by simpa only [pow_two] using relativeQ_squared F B p)

/-- The actual relative cohomology for any valid choice of polarization. -/
def cohomologyEquiv : Cohomology F B p ≃ₗ[ℂ] OrbifoldWeight p := by
  let c := input F B p hp
  let nilp := nilpotent F B p hp
  have equiv := (LocallyNilpotentPerturbation.cohomologyEquiv c nilp).trans
    ((zeroCohomologyEquiv _ (locally_nilpotent_perturbation c nilp).1
      (transferred_eq_zero F B p hp)).trans (groundEquiv F B p hp))
  exact (cohomologyCongr (input_D F B p hp) c.perturbed_sq
    (by simpa only [pow_two] using relativeQ_squared F B p)).symm.trans equiv

/-- The corrected representative is the finite perturbation of ground insertion. -/
def representative : OrbifoldWeight p →ₗ[ℂ] relativeShell p :=
  (I (input F B p hp) (nilpotent F B p hp)).comp (groundEquiv F B p hp).symm.toLinearMap

/-- The actual perturbed cohomology projection followed by ground extraction. -/
def coefficient : relativeShell p →ₗ[ℂ] OrbifoldWeight p :=
  (groundEquiv F B p hp).toLinearMap.comp (P (input F B p hp) (nilpotent F B p hp))

/-- The actual perturbed homotopy gives a primitive on the original shell. -/
def primitive : Module.End ℂ (relativeShell p) :=
  H (input F B p hp) (nilpotent F B p hp)

theorem representative_closed (v : OrbifoldWeight p) :
    relativeQ F B p (representative F B p hp v) = 0 := by
  have hc := (locally_nilpotent_perturbation (input F B p hp) (nilpotent F B p hp)).2.1
  have he := LinearMap.congr_fun hc ((groundEquiv F B p hp).symm v)
  simpa only [input_D F B p hp, transferred_eq_zero F B p hp, representative,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply, map_zero] using he

theorem coefficient_representative (v : OrbifoldWeight p) :
    coefficient F B p hp (representative F B p hp v) = v := by
  have hr := (locally_nilpotent_perturbation (input F B p hp) (nilpotent F B p hp)).2.2.2.1
  have he := LinearMap.congr_fun hr ((groundEquiv F B p hp).symm v)
  change P (input F B p hp) (nilpotent F B p hp)
    (I (input F B p hp) (nilpotent F B p hp) ((groundEquiv F B p hp).symm v)) =
      (groundEquiv F B p hp).symm v at he
  unfold coefficient representative
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact (congrArg (groundEquiv F B p hp) he).trans (LinearEquiv.apply_symm_apply _ _)

/-- Every actual cycle differs from its corrected representative by this boundary. -/
theorem cycle_boundary_witness (x : relativeShell p) (hx : relativeQ F B p x = 0) :
    relativeQ F B p (primitive F B p hp x) =
      x - representative F B p hp (coefficient F B p hp x) := by
  have hc : (input F B p hp).D x = 0 := by simpa only [input_D F B p hp] using hx
  have he := LocallyNilpotentPerturbation.cycle_primitive
    (input F B p hp) (nilpotent F B p hp) x hc
  simpa only [input_D F B p hp, primitive, representative, coefficient, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using he

/-- The primitive is an exact witness when the projected coefficient is zero. -/
theorem primitive_of_coefficient_zero (x : relativeShell p) (hx : relativeQ F B p x = 0)
    (hc : coefficient F B p hp x = 0) :
    relativeQ F B p (primitive F B p hp x) = x := by
  rw [cycle_boundary_witness F B p hp x hx, hc, map_zero, sub_zero]

/-- The finite expression for the corrected representative on the literal shell. -/
theorem representative_polynomial (v : OrbifoldWeight p) :
    representative F B p hp v =
      FinitePerturbation.inversePolynomial
        (relativeH F B p * relativeDelta F B p) (cutoff p)
        (groundShell F B p v) := by
  change K (input F B p hp) (nilpotent F B p hp) (groundShell F B p v) = _
  apply LocallyNilpotentPerturbation.K_apply_eq_inversePolynomial
  exact LinearMap.congr_fun (nilpotent_power F B p hp) (groundShell F B p v)

/-- The actual primitive is the same finite inverse polynomial applied after h. -/
theorem primitive_polynomial (x : relativeShell p) :
    primitive F B p hp x =
      FinitePerturbation.inversePolynomial
        (relativeH F B p * relativeDelta F B p) (cutoff p)
        (relativeH F B p x) := by
  change K (input F B p hp) (nilpotent F B p hp) (relativeH F B p x) = _
  apply LocallyNilpotentPerturbation.K_apply_eq_inversePolynomial
  exact LinearMap.congr_fun (nilpotent_power F B p hp) (relativeH F B p x)

section GhostDegree

open ActualLeechOrbifoldCriticalMatter (matter)
open LatticeLightConeCoordinates (a)
open LatticeBRSTModeFiltration
  (Shift shift_smul shift_add shift_mul shift_diagonal family_total_shift
    sector_coefficient b_support_charge c_support_charge)
open FiniteSupportEndomorphismCalculus (diagonal diagonal_basis inverseNumber)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (Fock)
open D5.S3.Quantum.Fermionic.BcGhostFock (b c)
open D5.S3.Quantum.Fermionic.BcGhostCharge (ghostNumber)

open private number_ket from D5.S3.Quantum.Fermionic.BcGhostCharge
open private sector_current from D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
open private supportedOn rightLift_supportedOn from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone

/-- The original ghost-number operator, transported through tensor association. -/
abbrev assocN : Module.End ℂ AssocState := (reassoc.conjAlgEquiv ℂ) (VirasoroBRST.N matter)

/-- Actual ghost-number g states on the relative shell. -/
abbrev GhostSpace (g : ℤ) : Submodule ℂ (relativeShell p) :=
  (assocN.eigenspace (g : ℂ)).comap (relativeShell p).subtype

private theorem mem_ghostSpace (g : ℤ) (x : relativeShell p) :
    x ∈ GhostSpace p g ↔ assocN x.val = (g : ℂ) • x.val :=
  Module.End.mem_eigenspace_iff

private def ghostWeight (i : StateIndex hyperbolicPlane 0) : ℤ := charge i.2

private theorem assocN_eq :
    assocN = rightLift (tp (1 : Module.End ℂ (Carrier hyperbolicPlane)) ghostNumber) := by
  apply TensorProduct.ext'
  intro v y
  induction y using TensorProduct.inductionOn with
  | tmul u w => rfl
  | add y z hy hz =>
    rw [TensorProduct.tmul_add, map_add assocN, map_add (rightLift _), hy, hz]

private theorem rightNumber_diagonal :
    tp (1 : Module.End ℂ (Carrier hyperbolicPlane)) ghostNumber =
      diagonal (actualBasis F B) (fun i => (ghostWeight i : ℂ)) := by
  apply (actualBasis F B).ext
  rintro ⟨⟨q, m⟩, S⟩
  rw [diagonal_basis, actualBasis_apply, ghost_sector, number_ket, sector_smul_right]
  rfl

private theorem rightSlice_assocN (i : StateIndex hyperbolicPlane 0) (x : AssocState) :
    rightSlice F B i (assocN x) = (ghostWeight i : ℂ) • rightSlice F B i x := by
  rw [assocN_eq, rightNumber_diagonal F B]
  induction x using TensorProduct.inductionOn with
  | tmul v y =>
    rw [rightLift_tmul, rightSlice_tmul, rightSlice_tmul, diagonal_coefficient, smul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

private theorem ghostSpace_iff_slices (g : ℤ) (x : relativeShell p) :
    x ∈ GhostSpace p g ↔ ∀ i, rightSlice F B i x.val ≠ 0 → ghostWeight i = g := by
  rw [mem_ghostSpace]
  constructor
  · intro hx i hi
    have he := congrArg (rightSlice F B i) hx
    rw [rightSlice_assocN F B, map_smul] at he
    have hs := smul_left_injective ℂ hi he
    exact_mod_cast hs
  · intro hx
    apply sub_eq_zero.mp
    apply eq_zero_of_all_rightSlices F B
    intro i
    rw [(rightSlice F B i).map_sub, (rightSlice F B i).map_smul, rightSlice_assocN F B]
    by_cases hi : rightSlice F B i x.val = 0
    · simp [hi]
    · rw [hx i hi, sub_self]

private theorem current_ghost_shift (u : LatticeLightConeCoordinates.E hyperbolicPlane) (n : ℤ)
    (G : Module.End ℂ Fock) (k : ℤ)
    (hG : ∀ S T : Finset ℕ, (G (ket S)) T ≠ 0 → charge T = charge S + k) :
    Shift (actualBasis F B) ghostWeight (tp (a u n) G) k := by
  classical
  intro i j hij
  obtain ⟨⟨q, m⟩, S⟩ := i
  rw [actualBasis_apply, sector_current, sector_coefficient] at hij
  split_ifs at hij with hq
  · exact hG S j.2 (mul_ne_zero_iff.mp hij).2
  · exact (hij rfl).elim

private theorem d0_ghost_shift : Shift (actualBasis F B) ghostWeight (d0 F p) 1 := by
  change Shift (actualBasis F B) ghostWeight (F.pPlus p • (dFamily F).total) 1
  apply shift_smul
  apply family_total_shift
  intro r
  change Shift (actualBasis F B) ghostWeight (dTerm F r) 1
  apply shift_add
  · exact current_ghost_shift F B _ _ _ 1 (c_support_charge _)
  · exact current_ghost_shift F B _ _ _ 1 (c_support_charge _)

private theorem h_ghost_shift : Shift (actualBasis F B) ghostWeight (h F B p) (-1) := by
  have hr : Shift (actualBasis F B) ghostWeight (R F p) (-1) := by
    change Shift (actualBasis F B) ghostWeight ((F.pPlus p)⁻¹ • (rFamily F).total) (-1)
    apply shift_smul
    apply family_total_shift
    intro r
    change Shift (actualBasis F B) ghostWeight (rTerm F r) (-1)
    apply shift_smul
    apply shift_add
    · exact current_ghost_shift F B _ _ _ (-1)
        (fun S T hT => by simpa only [sub_eq_add_neg] using b_support_charge _ S T hT)
    · exact current_ghost_shift F B _ _ _ (-1)
        (fun S T hT => by simpa only [sub_eq_add_neg] using b_support_charge _ S T hT)
  have hm : Shift (actualBasis F B) ghostWeight (invM F B) 0 :=
    shift_diagonal (actualBasis F B) ghostWeight _
  simpa only [h, add_zero] using shift_mul (actualBasis F B) ghostWeight hr hm

private theorem rightLift_mem_ghostSpace {A : Module.End ℂ (State hyperbolicPlane)}
    {k g : ℤ} (hs : Shift (actualBasis F B) ghostWeight A k)
    (x y : relativeShell p) (hy : y.val = rightLift A x.val) (hx : x ∈ GhostSpace p g) :
    y ∈ GhostSpace p (g + k) := by
  have hxx : x.val ∈ supportedOn F B (fun i => ghostWeight i = g) := by
    intro i hi
    by_contra hn
    exact hi ((ghostSpace_iff_slices F B p g x).mp hx i hn)
  have hyy : rightLift A x.val ∈ supportedOn F B (fun i => ghostWeight i = g + k) :=
    rightLift_supportedOn F B A (fun i j hi hj => (hs i j hj).trans (by rw [hi])) hxx
  apply (ghostSpace_iff_slices F B p _ y).mpr
  intro i hi
  by_contra hn
  rw [hy] at hi
  exact hi (hyy i hn)

theorem relativeQ_degree (g : ℤ) (x : relativeShell p) (hx : x ∈ GhostSpace p g) :
    relativeQ F B p x ∈ GhostSpace p (g + 1) := by
  have hcomm : assocN * assocQ - assocQ * assocN = assocQ := by
    let e := reassoc.conjAlgEquiv ℂ
    let N : Module.End ℂ ComplexState := VirasoroBRST.N matter
    have hq : N * Q - Q * N = Q := VirasoroBRST.N_Q matter
    have hs : e (N * Q - Q * N) = e (N * Q) - e (Q * N) :=
      map_sub e.toLinearMap (N * Q) (Q * N)
    have hNQ : e (N * Q) = e N * e Q := map_mul e.toMonoidHom N Q
    have hQN : e (Q * N) = e Q * e N := map_mul e.toMonoidHom Q N
    change e N * e Q - e Q * e N = e Q
    rw [← hNQ, ← hQN, ← hs, hq]
  have he := LinearMap.congr_fun hcomm x.val
  change assocN (assocQ x.val) - assocQ (assocN x.val) = assocQ x.val at he
  rw [(mem_ghostSpace p g x).mp hx, map_smul] at he
  apply (mem_ghostSpace p _ _).mpr
  change assocN (assocQ x.val) = ((g + 1 : ℤ) : ℂ) • assocQ x.val
  rw [Int.cast_add, Int.cast_one, add_smul, one_smul, add_comm]
  exact sub_eq_iff_eq_add.mp he

private theorem delta_degree (g : ℤ) (x : relativeShell p) (hx : x ∈ GhostSpace p g) :
    (input F B p hp).delta x ∈ GhostSpace p (g + 1) :=
  (GhostSpace p (g + 1)).sub_mem (relativeQ_degree F B p g x hx)
    (rightLift_mem_ghostSpace F B p (d0_ghost_shift F B p) x (relativeD0 F B p x) rfl hx)

private theorem h_degree (g : ℤ) (x : relativeShell p) (hx : x ∈ GhostSpace p g) :
    relativeH F B p x ∈ GhostSpace p (g - 1) := by
  simpa only [sub_eq_add_neg] using
    rightLift_mem_ghostSpace F B p (h_ghost_shift F B p) x (relativeH F B p x) rfl hx

private theorem K_degree (g : ℤ) (x : relativeShell p) (hx : x ∈ GhostSpace p g) :
    K (input F B p hp) (nilpotent F B p hp) x ∈ GhostSpace p g := by
  apply K_mem F B p hp (GhostSpace p g)
  · intro y hy
    change relativeH F B p ((input F B p hp).delta y) ∈ GhostSpace p g
    simpa only [add_sub_cancel_right] using
      h_degree F B p (g + 1) _ (delta_degree F B p hp g y hy)
  · exact hx

/-- The corrected inclusion lands in actual ghost number one. -/
theorem representative_degree (v : OrbifoldWeight p) :
    representative F B p hp v ∈ GhostSpace p 1 := by
  change K (input F B p hp) (nilpotent F B p hp)
    ((groundEquiv F B p hp).symm v).val ∈ GhostSpace p 1
  apply K_degree F B p hp
  apply (ghostSpace_iff_slices F B p _ _).mpr
  intro i hi
  rw [ground_support F B p hp _ i hi]
  exact ground_charge p

/-- The perturbed homotopy lowers the actual ghost number by one. -/
theorem primitive_degree (g : ℤ) (x : relativeShell p) (hx : x ∈ GhostSpace p g) :
    primitive F B p hp x ∈ GhostSpace p (g - 1) :=
  K_degree F B p hp _ _ (h_degree F B p g x hx)

private theorem J_degree (g : ℤ) (x : relativeShell p) (hx : x ∈ GhostSpace p g) :
    LocallyNilpotentPerturbation.J (input F B p hp) (nilpotent F B p hp) x ∈ GhostSpace p g := by
  change x - (input F B p hp).delta (primitive F B p hp x) ∈ GhostSpace p g
  apply (GhostSpace p g).sub_mem hx
  simpa only [sub_add_cancel] using
    delta_degree F B p hp (g - 1) _ (primitive_degree F B p hp g x hx)

/-- The perturbed projection vanishes in all ghost degrees except the ground degree. -/
theorem coefficient_eq_zero_of_degree_ne_one (g : ℤ) (hg : g ≠ 1)
    (x : relativeShell p) (hx : x ∈ GhostSpace p g) :
    coefficient F B p hp x = 0 := by
  let y := LocallyNilpotentPerturbation.J (input F B p hp) (nilpotent F B p hp) x
  have hy := (ghostSpace_iff_slices F B p g y).mp (J_degree F B p hp g x hx)
  have hz : rightSlice F B (groundIndex p) y.val = 0 := by
    by_contra hn
    have he := hy (groundIndex p) hn
    exact hg (he.symm.trans (ground_charge p))
  apply Subtype.ext
  change rightSlice F B (groundIndex p) (projection0 F B p hp y).val = 0
  rw [slice_projection0 F B p hp, ite_eq_left (ground_count p), hz]

include hp in
/-- Every homogeneous cycle away from ghost number one has a primitive
of one lower ghost number in the same momentum and relative shell. -/
theorem exact_of_degree_ne_one (g : ℤ) (hg : g ≠ 1) (x : relativeShell p)
    (hx : x ∈ GhostSpace p g) (hc : relativeQ F B p x = 0) :
    ∃ y ∈ GhostSpace p (g - 1), relativeQ F B p y = x :=
  ⟨primitive F B p hp x, primitive_degree F B p hp g x hx,
    primitive_of_coefficient_zero F B p hp x hc
      (coefficient_eq_zero_of_degree_ne_one F B p hp g hg x hx)⟩

private theorem coefficient_differential (x : relativeShell p) :
    coefficient F B p hp (relativeQ F B p x) = 0 := by
  have hc := (locally_nilpotent_perturbation (input F B p hp) (nilpotent F B p hp)).2.2.1
  have he := LinearMap.congr_fun hc x
  have hz : P (input F B p hp) (nilpotent F B p hp) (relativeQ F B p x) = 0 := by
    simpa only [input_D F B p hp, transferred_eq_zero F B p hp,
      LinearMap.comp_apply, LinearMap.zero_apply] using he
  change groundEquiv F B p hp (P (input F B p hp) (nilpotent F B p hp) _) = 0
  rw [hz]
  exact (groundEquiv F B p hp).toLinearMap.map_zero

/-- The degree g cycles are the actual relative cycles in the N eigenspace. -/
abbrev GradedCycles (g : ℤ) : Submodule ℂ (relativeShell p) :=
  GhostSpace p g ⊓ LinearMap.ker (relativeQ F B p)

local instance (g : ℤ) : AddCommGroup (GradedCycles F B p g) :=
  Submodule.addCommGroup (GradedCycles F B p g)

private def gradedBoundaryMap (g : ℤ) : GhostSpace p (g - 1) →ₗ[ℂ] GradedCycles F B p g :=
  ((relativeQ F B p).comp (GhostSpace p (g - 1)).subtype).codRestrict _ (by
    intro y
    apply Submodule.mem_inf.mpr
    refine ⟨?_, ?_⟩
    · simpa only [LinearMap.comp_apply, Submodule.subtype_apply, sub_add_cancel] using
        relativeQ_degree F B p (g - 1) y.val y.property
    · change relativeQ F B p (relativeQ F B p y.val) = 0
      simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using
        LinearMap.congr_fun (relativeQ_squared F B p) y.val)

/-- The boundaries come from the actual preceding ghost-number eigenspace. -/
abbrev GradedBoundaries (g : ℤ) := LinearMap.range (gradedBoundaryMap F B p g)

/-- The actual graded kernel/image quotient. -/
abbrev GradedCohomology (g : ℤ) := GradedCycles F B p g ⧸ GradedBoundaries F B p g

include hp in
/-- Every class of ghost number other than one vanishes. -/
theorem gradedCohomology_vanishes (g : ℤ) (hg : g ≠ 1) :
    Subsingleton (GradedCohomology F B p g) := by
  have hzero (z : GradedCohomology F B p g) : z = 0 := by
    refine Submodule.Quotient.induction_on _ z (fun x => ?_)
    apply (Submodule.Quotient.mk_eq_zero (GradedBoundaries F B p g)).mpr
    obtain ⟨y, hy, he⟩ := exact_of_degree_ne_one F B p hp g hg x.val
      x.property.1 x.property.2
    exact LinearMap.mem_range.mpr ⟨⟨y, hy⟩, Subtype.ext he⟩
  exact ⟨fun z w => (hzero z).trans (hzero w).symm⟩

/-- In ghost number one the actual graded quotient has the same orbifold
coefficient and corrected representative. -/
def ghostOneCohomologyEquiv : GradedCohomology F B p 1 ≃ₗ[ℂ] OrbifoldWeight p := by
  let f := (coefficient F B p hp).comp (GradedCycles F B p 1).subtype
  have hs : Function.Surjective f := by
    intro v
    refine ⟨⟨representative F B p hp v, representative_degree F B p hp v,
      representative_closed F B p hp v⟩, coefficient_representative F B p hp v⟩
  have hb : GradedBoundaries F B p 1 = LinearMap.ker f := by
    ext x
    change (∃ y : GhostSpace p ((1 : ℤ) - 1), gradedBoundaryMap F B p 1 y = x) ↔
      coefficient F B p hp x.val = 0
    constructor
    · rintro ⟨y, rfl⟩
      exact coefficient_differential F B p hp y.val
    · intro hx
      have hp' := primitive_degree F B p hp 1 x.val x.property.1
      exact ⟨⟨primitive F B p hp x.val, hp'⟩,
        Subtype.ext (primitive_of_coefficient_zero F B p hp x.val x.property.2 hx)⟩
  exact ((GradedBoundaries F B p 1).quotEquivOfEq (LinearMap.ker f) hb).trans
    (f.quotKerEquivOfSurjective hs)

end GhostDegree

/-- The quotient depends only on the actual Q and charge, so either
polarization gives the same source and the same conformal-weight target. -/
def cohomologyEquivNonzero (hp : p ≠ 0) :
    Cohomology planeFrame planeBasis p ≃ₗ[ℂ] OrbifoldWeight p := by
  classical
  by_cases h : planeFrame.pPlus p ≠ 0
  · exact cohomologyEquiv planeFrame planeBasis p h
  · have hs := (planeFrame_covers_nonzero p hp).resolve_left h
    exact cohomologyEquiv swappedPlaneFrame swappedPlaneBasis p hs


/-- The ghost-number-one result at every nonzero momentum. -/
def ghostOneCohomologyEquivNonzero (hp : p ≠ 0) :
    GradedCohomology planeFrame planeBasis p 1 ≃ₗ[ℂ] OrbifoldWeight p := by
  classical
  by_cases h : planeFrame.pPlus p ≠ 0
  · exact ghostOneCohomologyEquiv planeFrame planeBasis p h
  · exact ghostOneCohomologyEquiv swappedPlaneFrame swappedPlaneBasis p
      ((planeFrame_covers_nonzero p hp).resolve_left h)

/-- Vanishing of the graded quotient in every other ghost number and
every nonzero momentum. -/
theorem gradedCohomology_vanishes_nonzero (hp : p ≠ 0) (g : ℤ) (hg : g ≠ 1) :
    Subsingleton (GradedCohomology planeFrame planeBasis p g) := by
  rcases planeFrame_covers_nonzero p hp with h | h
  · exact gradedCohomology_vanishes planeFrame planeBasis p h g hg
  · exact gradedCohomology_vanishes swappedPlaneFrame swappedPlaneBasis p h g hg

/-- The same relative shell in the original tensor association. -/
abbrev NativeShell := (relativeShell p).comap reassoc.toLinearMap

local instance : AddCommGroup (NativeShell p) := Submodule.addCommGroup (NativeShell p)

private def nativeShellEquiv : NativeShell p ≃ₗ[ℂ] relativeShell p :=
  reassoc.ofSubmodule' (relativeShell p)

private theorem assocQ_reassoc (x : ComplexState) : assocQ (reassoc x) = reassoc (Q x) := by
  change ((reassoc.conjAlgEquiv ℂ) Q) (reassoc x) = _
  rw [LinearEquiv.conjAlgEquiv_apply (R := ℂ) reassoc Q]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- Restriction of the original Q on its original tensor factors. -/
def nativeQ : Module.End ℂ (NativeShell p) :=
  Q.restrict (fun x hx => by
    change reassoc (Q x) ∈ relativeShell p
    rw [← assocQ_reassoc]
    exact assocQ_mem_relativeShell planeFrame planeBasis p hx)

private theorem nativeQ_sq : nativeQ p * nativeQ p = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change Q (Q x.val) = 0
  simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun Q_squared x.val

/-- The quotient of the actual kernel by the restricted image of the original Q. -/
abbrev NativeCohomology :=
  FinitePerturbation.Cohomology (R := ℂ) (M := NativeShell p) (nativeQ p) (nativeQ_sq p)

private theorem nativeQ_chain :
    (nativeShellEquiv p).toLinearMap.comp (nativeQ p) =
      (relativeQ planeFrame planeBasis p).comp (nativeShellEquiv p).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change reassoc (Q x.val) = assocQ (reassoc x.val)
  exact (assocQ_reassoc x.val).symm

private theorem nativeQ_chain_symm :
    (nativeShellEquiv p).symm.toLinearMap.comp (relativeQ planeFrame planeBasis p) =
      (nativeQ p).comp (nativeShellEquiv p).symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  apply (nativeShellEquiv p).injective
  have he := LinearMap.congr_fun (nativeQ_chain p) ((nativeShellEquiv p).symm x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using he.symm

open private cohomologyMap cohomologyMap_mk
  from D5.S3.HomologicalAlgebra.FinitePerturbationCohomology

private def nativeCohomologyReassoc :
    NativeCohomology p ≃ₗ[ℂ] Cohomology planeFrame planeBasis p := by
  let d := nativeQ p
  let e := relativeQ planeFrame planeBasis p
  have hd : d * d = 0 := nativeQ_sq p
  have he : e * e = 0 := by
    simpa only [e, pow_two] using (relativeQ_squared planeFrame planeBasis p)
  let f := nativeShellEquiv p
  refine
    { toLinearMap := cohomologyMap d e hd he f.toLinearMap (nativeQ_chain p)
      invFun := cohomologyMap e d he hd f.symm.toLinearMap (nativeQ_chain_symm p)
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    refine Submodule.Quotient.induction_on _ z (fun x => ?_)
    change cohomologyMap e d he hd f.symm.toLinearMap (nativeQ_chain_symm p)
      (cohomologyMap d e hd he f.toLinearMap (nativeQ_chain p) (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk x
    rw [cohomologyMap_mk, cohomologyMap_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    change f.symm (f x.val) = x.val
    exact f.symm_apply_apply x.val
  · intro z
    refine Submodule.Quotient.induction_on _ z (fun x => ?_)
    change cohomologyMap d e hd he f.toLinearMap (nativeQ_chain p)
      (cohomologyMap e d he hd f.symm.toLinearMap (nativeQ_chain_symm p)
        (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
    rw [cohomologyMap_mk, cohomologyMap_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    change f (f.symm x.val) = x.val
    exact f.apply_symm_apply x.val

/-- For every nonzero momentum the original relative BRST quotient is the
actual orbifold eigenspace of weight 1 - p₀ p₁. -/
def nativeCohomologyEquiv (hp : p ≠ 0) : NativeCohomology p ≃ₗ[ℂ] OrbifoldWeight p :=
  (nativeCohomologyReassoc p).trans (cohomologyEquivNonzero p hp)

end RelativeCohomology

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST
