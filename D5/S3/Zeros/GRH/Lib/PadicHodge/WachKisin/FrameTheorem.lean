/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/FrameTheorem
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/FrameTheorem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.WachKisin.FrameTheorem. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/WachKisin/FrameTheorem.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.WachGamma.Letters
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Kisin lattice (Breuil–Kisin module) of a crystalline lattice (known result; see
Lib.PadicHodge.WachKisin.PeriodMatrixFrame).

This file: Kisin module of a crystalline lattice: frame, finite height, divisibility tests,
spanning by nearly invariant vectors. -/

open Algebra Algebra.TensorProduct Module _root_.TensorProduct FaithfulSMul Finset LinearMap Matrix
  MulSemiringAction Pointwise Submodule algebraMap Lift.Chart

namespace Lift.KummerChart.JumpLattice

attribute [-instance] Bialgebra.toAlgebra NormedAlgebra.toAlgebra NormedSpace.toModule

variable {p} [ThePrime p] [Γ : GroupOverGp p] {k : KummerChart Γ} {O} {L : JumpLattice O}

lemma exists_functional_extend (f : _ →ₗ[ℤ_[p]] BdR) : ∃ μ :
    L.Functional, ∀ t, μ (.mk 1 t) = f t := (exists_extend_of_notMem (p := ⊥) 0 (@NeZero.one _ _ (by
  apply_rules [nontrivial_of_algebraMap_injective_of_isDomain, algebraMap_injective])).1 f).rec
  fun Ψ h ↦ ⟨AlgebraTensorModule.lift ((liftBaseChangeEquiv BdR).2 Ψ), by bound⟩

attribute [-simp] LinearMap.map_smul_of_tower map_one map_smul

attribute [local simp ←] IsScalarTower.algebraMap_apply

attribute [local simp] Fintype.linearCombination_apply Function.comp_def S_smul basisValues
  frobGroup_smul_smul phiInvToBdR mulVec
  vecMul MonoidHom.map_one Prod.mk_one_one RingHom.map_one mul_smul dotProduct

lemma equivariant_iff_basisValues {μ g A μ'} (hA : IsUnit A) (H :
  (repMatrix L.ρ (finBasis ..) g).map (↑) * A.map (toGp g • ·) = A) : (∀ t, μ' (.mk 1 (L.ρ g t)) =
  toGp g • μ (.mk 1 t)) ↔ basisValues μ' ᵥ* A = toGp g • basisValues μ ᵥ* A := by
  erw [(funext ((toRingHom ..).map_vecMul A _) : toGp g • _ ᵥ* A = _), ← congr(_ ᵥ* $H),
    ← vecMul_vecMul, (vecMul_injective_of_isUnit (hA.map (toRingHom ..).mapMatrix)).eq_iff]
  simpa [funext_iff, repMatrix, toMatrixAlgEquiv_apply, ← smul_def', ← commutes,
    ← map_smul_of_tower, ← map_sum, -LinearMap.map_smulₛₗ] using ⟨by tauto, fun h t ↦ by
    simpa [inv_smul_eq_iff] using apply_eq_of_mem_fracSpan (conjForm μ' g) μ (funext (by simp [h]))
      (le_saturateBy (mk_one_mem_ainfLattice t))⟩

lemma kisinAinf_le_fracSpan : L.kisinAinf ≤ L.fracSpan := fun _ ⟨⟨_, ⟨_, rfl⟩, h⟩, _⟩ ↦
  ⟨_, by simp, h⟩

instance : IsTorsionFree Ainf L.Ambient := .trans_faithfulSMul _ WittCFlat (_ ⊗ _)

/-- Frame theorem, h the least bound of |jumps|: M = A_inf N, τ^h M ⊂ A_inf⊗L, τ^h(A_inf⊗L) ⊂ M,
E^h φN ⊂ N. Also: S-linear maps A_inf → S keep relations, crystalline forms test
divisibility in M, and for 3e ≤ p^l, eA ≤ p^l δ the vectors invariant modulo t^A span the
`valueFieldPoints` of φ^l(M) up to p^{4δ}.

Known result: Kisin lattice (Breuil–Kisin module) of a crystalline lattice. -/
lemma frame_theorem : ((∀ (f : _ →ₗ[k.S] k.S) {ι : Type} [Fintype ι] (v : ι → _) (c : ι → Ainf),
  (∀ i, v i ∈ L.valueFieldPoints fracSpan) → ∑ i, c i • v i = 0 → ∑ i, f (c i) • v i = 0) ∧ (∀ l A
  δ, 3 * k.e ≤ p ^ l → k.e * A ≤ p ^ l * δ → ∀ x ∈ L.valueFieldPoints (frobKisinAinf l), p ^ (4 * δ)
  • x ∈ span k.S {y ∈ L.valueFieldPoints (frobKisinAinf l) | ∀ μ ∈ forms, ∀ g : Γ', toGp g.1 • μ y -
  μ y ∈ hodgeFil A}) ∧ L.kisinAinf = span _ L.kisinModule ∧ (∀ μ ∈ crysForms, ∀ y ∈ L.kisinModule,
  ∃ s ∈ k.bicommutant, k.E.1 ^ L.jumpBound • μ y = algebraMap _ _ s) ∧ ∀ d, (∀ {m r}, ainfToBPlus
  d ∣ ainfToBPlus (k.E.1 ^ m * r) → d ∣ r) → ∀ x ∈ kisinAinf, (∀ μ ∈ L.crysForms, k.E.1 ^
  (2 * L.jumpBound) • μ x ∈ BPlus ∙ algebraMap _ _ d) → x ∈ d • kisinAinf) ∧ (∀ x ∈ kisinAinf, tau ^
  L.jumpBound • x ∈ L.ainfLattice) ∧ (∀ x ∈ ainfLattice, tau ^ L.jumpBound • x ∈ L.kisinAinf) ∧
  ∀ x ∈ L.kisinModule, k.frobEUnit 0 ^ L.jumpBound • FrobGroup.φ • x ∈ kisinModule := by
  set a := L.jumpBound
  let e := finBasis ℤ_[p] L.Carrier
  obtain ⟨M, U, v, hM, hv, hU, eU⟩ := isChartOf.exists_isPeriodMatrix a a (ρ := .comp (overZp _) _)
    (L.inClass.1.mono le_sup_right :) e (Nat.sInf_mem exists_jump_bound)
  obtain ⟨Q, Q', Z, Y, B, hQ, hZ, eZ, X, hB, hG⟩ := hU.exists_frame
  let s := Fintype.linearCombination Ainf (M := L.Ambient) (DiagTensor.mk 1 ∘ e)
  have hs : ainfLattice = s.range := by simp [ainfLattice_eq_span_basis, s, e]
  choose n hn using by simpa [← map_pow] using (((isUnit_WittCFlat_of_not_p_dvd not_p_dvd_tau).pow
    a).smul_bijective.2 <| s <| Qᵀ ·)
  let ν m := Fintype.linearCombination Ainf ((FrobGroup.φ • ·)^[m] ∘ n)
  have hν m t : (FrobGroup.φ ^ m • tau ^ a) • ν m t = s (Q.map (FrobGroup.φ ^ m • ·) *ᵥ t) := by
    simp [ν, smul_sum, smul_comm _ (t _), ← frobGroup_smul_smul, hn, ↓mulVec_eq_sum, -smul_pow']
    simp [s, smul_sum]
  have hν₀ := by simpa [ν] using hν 0
  let ψ m := (algebraMap _ BdR).comp (toRingHom FrobGal Bcris (.ofAdd m, 1))
  have I m {μ} : μ ∈ L.forms ↔ _ := forall_comm.trans (forall_congr' fun g ↦
    (equivariant_iff_basisValues (M.isUnit.map
    (ψ m).mapMatrix) (by simpa [ψ, smul_smul, ↓map_mul,
    @MulAction.compHom_smul_def _ _ Bcris] using! congr((ψ m).mapMatrix $(hM g)))).trans funext_iff)
  have G' μ m t : (k.frobE m).1 ^ a • μ (ν m t) = basisValues μ ᵥ* (ψ m).mapMatrix M ⬝ᵥ (↑) ∘
    (Z.map frobEnd^[m] *ᵥ ainfToBPlus ∘ t) := by
    have F := congr((k.frobE m).1 ^ (a + a) • μ $(hν m t) - basisValues μ ⬝ᵥ (ψ m).mapMatrix
      ($(eZ).map (↑)) *ᵥ t • 1)
    rw [Matrix.map_mul, eU, map_mul, ← mulVec_mulVec, dotProduct_mulVec] at F
    apply (((isUnit_smul_of_dvd_mu 1 ⟨_, hv.symm⟩).pow a).map (ψ m)).mul_left_cancel
    linear_combination (norm := (simp [s, ψ, smul_def', ↓map_apply, e, frobE_eq,
      FrobGroup.phi_pow_smul, mul_sum,
      ↓RingHom.mapMatrix_apply, FrobGal.smul_def, sum_mul, mul_comm (μ _)]; ring_nf)) F
  have G := by simpa [ν, smul_def'] using (G' · · <| Pi.single · 1)
  have K m {μ ν} hμ := mem_valueField_of_fixed ((@I m μ).1 hμ · ν)
  have hN i : n i ∈ L.kisinAinf := ⟨⟨_, ⟨a, rfl⟩, by simp [*]⟩, fun m μ hμ ↦
    (mul_mem_hodgeFil_iff_of_not_frobE_dvd (not_frobE_dvd_frobE_of_ne m.succ_pos.ne) a).1 (by
    simpa [G] using! sum_mem fun ν _ ↦ mul_mem_hodgeFil (K _ hμ).1 algebraMap_mem_hodgeFil_zero)⟩
  have hP l i : FrobGroup.φ ^ l • n i ∈ valueFieldPoints (frobKisinAinf l) := ⟨by
    simp [frobKisinAinf, *], fun μ hμ ↦ by simpa using (div_mem (G μ l i ▸ sum_mem fun ν _ ↦ mul_mem
    (K l hμ).2 (Subfield.subset_closure (.inr ⟨(⟨_, Set.MapsTo.iterate @k.frobEnd_mem_bicommutant l
    (hZ ν i)⟩, 1), by simp⟩)) :) (phiInvToBdR_mem_valueField (k.frobE l ^ a)))⟩
  have H m (W : Submodule BPlus _) t (H : ∀ μ ∈ L.crysForms, μ (ν m t) ∈ W) i :
    phiInvToBdR 0 (k.frobE m ^ (a + a) * t i) ∈ W := by
    choose μ hμ using (exists_functional_extend <| .comp (algHom ..).toLinearMap <| e.constr ℕ <|
      frobEnd^[m] ∘ M.2 ·)
    have R ν : basisValues (μ ν) ᵥ* (ψ m).mapMatrix M = (1 : Matrix ..) ν := funext fun l ↦ by
      simpa [ψ, FrobGal.smul_def, *, e, Matrix.mul_apply] using! congr(ψ m ($(M.4) ν l))
    convert sum_smul_mem W (Y.map frobEnd^[m] i) fun ν _ ↦ W.smul_of_tower_mem ((k.frobE m).1 ^ a)
      (H _ ⟨by simp [I m, ↓R], _, hμ ν⟩)
    simpa [-mulVec, ↓G', ↓R, ↓map_mul, ← mulVec_mulVec, frobE_eq, algebraMap_eq_diagonal,
      FrobGroup.phi_pow_smul, ↓mulVec.eq_1 (Y.map _), smul_def'] using
      congr(((((frobEnd ^ m).mapMatrix $X.symm *ᵥ ainfToBPlus ∘ t) i :) : BdR))
  have h₂ x : x ∈ L.ainfLattice → ∃ t, ν 0 t = tau ^ a • x := hs ▸ fun ⟨α, h⟩ ↦ ⟨_, by
    simpa [h, hQ, pow_add] using! hν₀ (Q' *ᵥ α)⟩
  refine and_assoc.2 ⟨?X, ?_⟩
  exact fun f _ _ v c hv e ↦ (fracSpan.sum_smul_mem (f <| c ·) (t := univ) fun i _ ↦ (hv i).1).elim
    fun r ⟨hr, E⟩ ↦ (h₂ _ E).rec fun t E ↦ by simpa [ν, by simpa using hr, by simpa using (H 0 ⊥
    t fun μ J ↦ by simp [E, smul_def', by simpa using (sum_map_mem_of_valueField f _ _ (hv · |>.2 _
    J.1) (W := ⊥) (by simpa [smul_def'] using congr(μ $e)))])] using E.symm
  have S := @mem_span_range_iff_exists_fun.{0}
  have K' w t h := (pi_dvd_iff.2 h : (fun _ ↦ w) ∣ t).imp fun s e ↦ (congr(ν 0 $e).trans
    (map_smul ..)).symm
  have e₀ := L.kisinAinf.span_eq_of_le (Set.range_subset_iff.2 hN) fun x f@⟨⟨_, ⟨N, rfl⟩, h⟩, _⟩ ↦
    (by
    rw [smul_smul, ← pow_add, S]
    induction' a + N with N ih <;> simp [pow_succ', ν]
    exact fun t h ↦ ih (by simpa [h, ν] using (K' _ t fun i ↦ tau_dvd_of_theta_frobEnd fun m ↦ by
      simpa [frobE_dvd_iff, FrobGroup.phi_pow_smul, mt frobE_dvd_iff.2 (not_frobE_dvd_frobE_of_ne
        m.succ_pos.ne)] using! phiInvToBdR_mem_hodgeFil_one_iff.1 (H (m + 1)
      ((hodgeFil 1).restrictScalars _) (FrobGroup.φ ^ (m + 1) • t ·) (by
      simp [h, ν, ← frobGroup_smul_smul, ← smul_sum]
      simpa [smul_def'] using (mul_mem_hodgeFil (phiInvToBdR_mem_hodgeFil_one_iff.2
        (frobE_dvd_phi_pow_tau m.succ_pos)) <| (smul_mem _ (tau ^ N)
      f).2 m · ·.1)) i))) : _ → _) (h₂ _ h)
  have D l := (valueFieldPoints _).span_eq_of_le (Set.range_subset_iff.2 (hP l)) fun x hx ↦
    have ⟨t, e⟩ := (S _).1 (e₀.ge hx.1)
    (S _).2 ⟨_, by simpa [add_eq_zero_iff_eq_neg'] using (?X k.coord₀ (Option.rec _ _)
      (FrobGroup.φ ^ l • ·.elim (-1) t) (.imp_left ((show frobKisinAinf l ≤ fracSpan from fun _
      h ↦ by simpa using smul_mem_fracSpan (FrobGroup.φ ^ l) (kisinAinf_le_fracSpan
      h)) ·) <| ·.rec hx (hP l)) (by simp [← frobGroup_smul_smul, ← smul_sum, e]))⟩
  simp only [↓← D, ↓← by simpa [frobKisinAinf_zero] using D 0, span_span_of_tower, ← e₀,
    forall_exists_index,
    mem_smul_pointwise_iff_exists, S, forall_apply_eq_imp_iff, exists_exists_eq_and]
  refine ⟨⟨fun l A δ b d c ↦ ?_, ⟨⟩, fun μ ⟨hμ, l, E⟩ c ↦ ?_, fun d D t h ↦ K' _ t fun i ↦ D
    (map_dvd _ (D ((mem_span_singleton.1 (H 0 _ ((_ : Ainf) • t) (by simpa [-map_sum] using! h)
    i)).imp fun y h ↦ algebraMap_injective _ BdR (by simpa [frobE, commutes y, smul_def'] using
    h.symm))))⟩, by simp [*], h₂, fun c ↦ ⟨B *ᵥ k.φ ∘ c, by
    simpa [mul_comm _ v.1, mul_comm _ tau, frobGroup_phi_smul, hB, ← hv, ← hν₀, ← mulVec_mulVec,
      mul_pow, ↓frobEUnit_pow_smul, Units.smul_def, smul_sum (r := FrobGroup.φ), «φ», frobE,
      ν] using (hν 1 (FrobGroup.φ • c ·)).symm⟩⟩
  obtain ⟨V, D, hD, eV, R⟩ := radius_lemma (fixes _) (by simpa using
    (exists_smul_z 1).choose_spec) hZ X (hG _ (fixes _)).choose_spec b a
  refine (map_nsmul (Fintype.linearCombination ..) ..).subst (mapsTo_span (fun y ↦ Exists.rec
    fun r h ↦ ⟨⟨y, rfl⟩, fun μ hμ g ↦ ?_⟩) (R A δ d c))
  choose w f using h
  simpa [by simpa [-mulVec, -mulVec_add, ν, eV, ← mulVec_mulVec, eq_add_of_sub_eq' (funext f : _ =
    (_ : BPlus) • w), algebraMap.smul, ← smul_sum] using G' μ l (y ·), ↓mulVec_add, mul_add, frobE,
    smul_sum, ← by simpa using (I l).1 hμ g, by simpa [← ext_iff] using hD _ (fixes g).1] using
    (fun F ↦ sub_mem (smul_mem_hodgeFil (toGp g) F) F) (sum_mem
    fun ν _ ↦ mul_mem_hodgeFil (K l hμ).1 (mul_mem_hodgeFil (frobE_zpow_mem_hodgeFil 0 A)
    (@algebraMap_mem_hodgeFil_zero _ _ ↑(D ν ⬝ᵥ w))))
  choose s f S using (isChartOf.exists_mem_bicommutant_of_fixed (b := ∑ i,
    l (e i) * M i ·) fun g ↦ by simpa [E, ψ, ← map_mul, ← map_sum] using ((I 0).1 hμ g _).symm)
  exact ⟨s ⬝ᵥ Z *ᵥ ainfToBPlus ∘ (c ·), by simp (maxDischargeDepth := 4) [sum_mem, mul_mem, *], by
    simpa [E, e, ψ, ← map_mul, ← map_sum, ← S] using! G' μ 0 (c ·)⟩
