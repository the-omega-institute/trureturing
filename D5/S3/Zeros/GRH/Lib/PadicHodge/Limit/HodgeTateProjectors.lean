/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/Limit/HodgeTateProjectors
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/Limit/HodgeTateProjectors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.Limit.HodgeTateProjectors. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/Limit/HodgeTateProjectors.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.Comparison.CrystallineLimit
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Limits of crystalline representations with bounded weights are crystalline (known
result; see Lib.PadicHodge.Limit.LocalLimit).

Part of: Bloch–Kato finite local condition: rank formula and size of its annihilator (known result;
see Lib.PadicHodge.BlochKato.BlochKato).

This file: Crystalline cocycles modulo p^m: continuity, kernel of reduction, stability under
corestriction. Hodge–Tate projectors of crystalline lattices with bounded weights have rank-free
bounded denominators. -/

noncomputable section

section

open Module Nat crysCocycles PadicInt LinearMap LE DiscreteModule Function Classical AddSubgroup
  Fint Topology
variable {p} [ThePrime p] {Γ R T μ : Type} [Group Γ] [CommRing R] [Algebra ℤ_[p] R] [AddCommGroup T]
  [Module R T] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [AddCommGroup μ] [𝒥 : OverGp Γ p]
  {ρ : Representation R Γ T} [Free ℤ_[p] T] [Module.Finite ℤ_[p] T] [TopologicalSpace Γ]
  [IsTopologicalGroup Γ] (hj : IsOpenEmbedding 𝒥.toGp)

variable (T) in
/-- For a natural number m, the Z_p-submodule p^m T of T, the image of multiplication by p^m. -/
abbrev pPowMultiples m := (lsmul ℤ_[p] T (p ^ m)).range.toAddSubgroup

/-- For a finite free Z_p-module T, the quotient T/p^mT has (p^m)^d elements, where d is the
rank of T. -/
@[simp] lemma index_pPowMultiples m : (pPowMultiples T m).index = (p ^ m) ^ finrank ℤ_[p] T := by
  erw [index_eq_card, pPowMultiples, range_eq_map, card_congr (QuotSMulTop.equivQuotTensor
    ..).toEquiv, card_congr ((finBasis ..).baseChange _).equivFun.toEquiv, ← ker_toZModPow, card_pi,
    card_congr (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective _)).1]; simp

/-- A chosen injective homomorphism from Z_p/p^m to the multiplicative group of Q̄_p, written
additively. -/
def zmodPowToUnits m : QuotSpan (p ^ m : ℤ_[p]) →+ DiscreteUnits (PadicAlgCl p) := (rootPowHom
  ..).1.comp (Ideal.Quotient.lift _ (toZModPow m) (by simp [← ker_toZModPow])).toAddMonoidHom

lemma map_cyclotomicGp_smul [Module ℤ_[p] μ] (f : μ →+ DiscreteUnits (PadicAlgCl p)) {n} (h : ∀ x,
  p ^ n • f x = 0) x g : f ((cyclotomicGp g).1 • x) = unitsRep g (f x) :=
  (map_cycChar_smul f n h x).trans (cycCharMod_eq_iff_unitsRep.1 zmod_eq_natCast_val (h x)).symm

variable (h : IsPotCrys ρ) {S} [CommRing S] {V : DiscreteModule S Γ} {q : T →+ V} {m}

lemma nsmul_zmodPowToUnits x :
  p ^ m • zmodPowToUnits m x = 0 := by simp [← map_nsmul, ↓nsmul_quot_eq_zero]

include hj h

/-- Let j: Γ → G_p be an open embedding and T potentially crystalline, finite free over Z_p. For an
additive map q from T to a group μ with any topology, values killed by p^m, and x in Z_f(T), the map
q∘x is continuous. -/
lemma crysCocycles.continuous_comp [TopologicalSpace μ] (q : T →+ μ) (k : ∀ y, p ^ m • q y = 0)
    {x} (hx : x ∈ crysCocycles ρ) : Continuous (q ∘ x) := (isLocallyConstant_of_eventually_mul
  (nearOne_eq_nhds_one hj ▸ (eventually_eq_pow_smul h hx m).mono
  (by grind [apply_mul hx]))).continuous

variable (e : ∀ g x, q (ρ g x) = V.ρ g (q x)) (k : q.ker = pPowMultiples T m)

/-- For T finite free over Z_p, potentially crystalline, j an open embedding, q: T → V
equivariant with kernel p^m T: the additive map c ↦ q∘c from Z_f(T) to Z¹(V). -/
abbrev IsPotCrys.reducedCocycle : crysCocycles ρ →+ Z1 V.ρ :=
  .codRestrict ((q.compLeft Γ).domRestrict _) _ fun ⟨_, u⟩ ↦ ⟨continuous_comp hj h q
  (by simpa [le, ← map_nsmul, ← cast_smul_eq_nsmul ℤ_[p]] using k.ge) u, by simp_all [apply_mul u]⟩

/-- Let T be finite free over Z_p and potentially crystalline, j an open embedding, q: T → V
additive and equivariant with kernel p^m T. Then the map `IsPotCrys.reducedCocycle` induced by q on
crystalline cocycles has kernel p^m Z_f(T). -/
lemma IsPotCrys.ker_reducedCocycle : (h.reducedCocycle hj e k).ker =
  pPowMultiples _ m := by ext ⟨c, u⟩; simpa [funext_iff, ← q.mem_ker,
  k, skolem] using ⟨.imp fun _ E ↦ ⟨of_smul NeZero.out (funext E ▸ u), E⟩, by tauto⟩

/-- Let Γ be compact, j an open embedding, T finite free over Z_p and potentially crystalline,
q: T → V onto, equivariant, with kernel p^m T, U ⊂ Γ open. Then q∘Z_f(T) contains the
coboundaries and a corestriction of each cocycle in q∘Z_f(T|U). -/
lemma IsPotCrys.holdsCorestrictions [CompactSpace Γ] (o : Surjective q) {U : OpenSubgroup Γ} (hU :
    IsOpenEmbedding (toGp.comp U.subtype)) :
  V.HoldsCorestrictions U (reducedCocycle (𝒥 := ⟨_, ⟨hU.2⟩⟩) hU (h.comp _)
  (e ·) k).range (h.reducedCocycle hj e k).range := have ⟨s, n, _, m⟩ := exists_coset_section U
  ⟨o.forall.2 (⟨⟨_, coboundary_mem ·⟩, by aesop⟩), fun ⟨y, _, c⟩ ⟨⟨_, Y, hz⟩, E⟩ ↦
               ⟨⟨fun g x ↦ V.ρ (s x) (y ⟨_, m x g⟩), by fun_prop, fun g
    k ↦ by simpa [mul_assoc, mul_smul, subgroupIncl, -ContinuousMonoidHom.coe_toMonoidHom] using!
    (congr(fun x ↦ V.ρ (s x) $(c ⟨_, m x g⟩ ⟨_, m (g⁻¹ • x) k⟩)))⟩, by
    ext u; show V.ρ _ (y ⟨_, m _ u⟩) = _; simp [n], ⟨_, ∑ x, tensorAction _ (toGp (s x)) (ρ _) Y,
    fun g ↦ by rw [map_sum, ← (MulAction.bijective g⁻¹).sum_comp,
    TensorProduct.tmul_sum]; simpa [↓tensorAction_tensorAction, ↓map_sub, tensorAction,
    ← map_mul, ← mul_assoc] using (congr(∑ x,
    tensorAction _ (toGp (s x)) (ρ (s x)) $(hz ⟨_, m x g⟩)))⟩, by cases E; ext; simp [sum, e]⟩⟩

end

open Module Matrix IsScalarTower RingHom Function Algebra Submodule.Quotient BdRPlus algebraMap

/-- Uniform reading of jumps, for j of open image. Some t in C_p, depending only on j, n, w,
works for all crystalline lattices T with jumps in [0,n], bases ε and x in T: there are z_s,
|z_s| ≤ 1, with t Σ z_s γ(tr u(ε_s)) the multiplicity of the jump w of r at γ, whenever r is
potentially crystalline, u(gy) = r(g)u(y), u(x) = 1. -/
lemma exists_uniform_trace_sum_eq_jump {p} [ThePrime p] Γ [Group Γ] [𝒥 : OverGp Γ p] n w : ∃ t,
  ∀ {T ι : Type} [AddCommGroup T] [Module ℤ_[p] T] [Fintype ι] (ε : Basis ι ℤ_[p] T) {ρ} x,
  IsCrystallineUpTo (R := ℤ_[p]) n ρ → ∃ z : ι → ℂ_[p], (∀ s, ‖z s‖ ≤ 1) ∧ ∀ γ (r :
  PadicRep Γ p) (u : T →ₗ[ℤ_[p]] _), (∀ g y, u (ρ g y) = (r.rep g).1 * u y) → u x = 1 →
  IsPotCrys (matrixRep r.rep) → t * ∑ s, z s * γ (u (ε s)).trace = jump (matrixRep r.rep) γ w := by
  obtain ⟨e, K, H⟩ := Lift.uniform_period_bound Γ n
  replace K := algebraMap_apply _ Bcris BdR e ▸ (K.map _).ne_zero
  obtain ⟨⟨m, δ, he⟩, R, hR⟩ :=
    exists_associated_xi_pow (ne_zero_of_map (algebraMap_apply _ BdRPlus BdR e ▸ K)), ((localFieldOf
    Γ).essFiniteType_iff.1 inferInstance).choose_spec ▸ CoeffRing.exists_mem_of_mem_adjoin _
  let O := (toAlgHom ..).liftEquiv ℤ_[p] Amax R BdRPlus
  obtain ⟨c, B⟩ := (@End.isNilpotent_iff_of_finite Amax (_ ⧸ (((toAlgHom _ BPlus _).toLinearMap
    ∘ₗ Algebra.linearMap ..).coprod (.mulLeft _ (xi ^ m.succ • 1))).range.comap
    O.toLinearMap) _ _ _ _ p).2 (Quot.ind (O · |>.exists_Ainf_approx m.succ |>.imp fun l ⟨a, w, h⟩ ↦
    mod_cast (mk_eq_zero _).2 ⟨(a, w), by simp [← h, smul_def, ← algebraMap_apply]⟩))
  have B {z y} (h : O y = e • z) : ‖thetaBdR (p ^ (2 * m) * (δ * (p ^ c * z)))‖ ≤ 1 := by
    obtain ⟨a, w, k⟩ := by simpa [h, smul_def, ← he, pow_succ, mul_assoc, mul_left_comm (_ ^ c),
      ← mul_sub, ← eq_sub_iff_add_eq] using (mk_eq_zero _).1 congr($((p.cast_pow c).trans B) ⟦y⟧)
    cases xi_pow_dvd_iff.1 ⟨_, k⟩
    cases amaxImage.p_pow_mul_mem_of_dvd_mu ⟨_, xi_mul_tau.symm⟩ ⟨a, by simpa [smul_def]⟩
    convert (thetaAmax ‹_›).2; clear K B H hR
    simp_all [← thetaBPlus_algebraMap_Amax, ← thetaBdR_algebraMap_BPlus, ← algebraMap_apply,
      prime_xi.1]
  use (p ^ (2 * m) * thetaBdR δ * p ^ c)⁻¹; introv hx; choose _ U U' Q hr using H ε hx
  obtain ⟨⟨Y, Z⟩, W, k, ⟨W, rfl⟩, A, E, H, I⟩ :=
    exists_hodge_frame Γ le_top (isUnit_of_mul_isUnit_left
    (by rw [← map_mul, Q]; simp [smul_eq_diagonal_mul, K, Pi.isUnit_iff])) (.trans (by
    simp [comp_def]; rfl) <| congrArg (algebraMap ..).mapMatrix <| hr ·)
  let ⟨y, J⟩ : ∃ y, O.mapMatrix y = (algebraMap ..).mapMatrix Y := ⟨of (1 ⊗ₜ ⟨Y · ·,
    by clear * - hR A I; simp_all [← ext_iff]⟩), ext (by simp [O])⟩
  let D {κ R} (k : κ → ℤ) [Ring R] := diagonal (if w = k · then (1 : R) else 0)
  let z := W.1 *ᵥ D k *ᵥ W⁻¹ *ᵥ (↑) ∘ ε.repr x
  refine ⟨_, fun s ↦ @B (z s) (mulVec (U.map (↑) * y * D k * y.adjugate * U'.map (↑))
    ((↑) ∘ ε.repr x) s) ?_, fun γ r u v o h ↦ ?_⟩
  erw [O.map_mulVec, ← O.mapMatrix_apply]; simp [↓map_mul, O.map_adjugate, comp_def, ← map_det, *,
    z, (map_injective (IsFractionRing.injective _ BdR)
    (by simp; erw [E, ← mul_assoc]; simp [hodgeMatrix, D, mul_assoc]) : SemiconjBy (U.map (↑) *
    (algebraMap ..).mapMatrix Y) ((D k).map O) (W.1 * D k * W.2)), mul_assoc,
    mul_adjugate, -mapMatrix_apply, ← U.map_mul, map_smul', -TensorProduct.algebraMap_apply]
  obtain ⟨_, ⟨P, k₁, -, hJ, b, hb, eb⟩, -, β, hβ, eβ⟩ := Finite.of_basis ε,
    h.exists_isHodgeTateFrame (Pi.basisFun ..) γ, hasJumps_of_rows (γ := ofId ..) ε (W.map
    thetaBdR.1.mapMatrix.1)⁻¹ _ (by exact .of_forall (H.mono fun _ ↦
    inv_mul_apply_of_isHodgeTateFrame ∘ isHodgeTateFrame_of_hodgeMatrix))
  let F y := P.2 * (u y).map γ; suffices ∑ s, thetaBdR _ • F _ = D k₁ * F x by
    simpa [F, Finset.mul_sum, mul_assoc, P.1.trace_mul_comm, D, o, hJ w, Multiset.count_map,
      ← isUnit_iff, NeZero.ne, AddMonoidHom.map_trace] using! congr((P * $this).trace)
  ext i c; simp [D, Matrix.sum_apply, -ite_mul, -mulVec_single, show ∀ y, F y i c = b i (u y *ᵥ
    Pi.single c 1) by simp [pi_eq_sum_univ' (col _ c), F, ← eb, ↓mul_apply, mul_comm]]
  refine (LinearMap.eqOn_span (f := dotProductBilin ℤ _ _ ∘ₗ .pi (.flip .id ∘ ε)) (g := .mulLeft
    .. ∘ₗ .flip .id x) (Set.forall_mem_image.2 fun l e ↦ ?_) (hodgeTateMaps.mem_span_same_weight hβ
    (hodgeTateMaps.pull (φ :=
    algebraMap ..) ⟨applyVec u _, by simp⟩ (by simp [v]) ⟨_, hb i⟩).2 (β.mem_span _)) :)
  rw [← ε.sum_repr x, map_sum]
  simpa [-toRingHom_ofId, eβ, e.out, D, entrywise, smul_def, diagonal,
    apply_ite, ite_apply, mul_comm] using congr(thetaBdR ($((inv_smul_smul W _ : _ *ᵥ z = _)) l))
