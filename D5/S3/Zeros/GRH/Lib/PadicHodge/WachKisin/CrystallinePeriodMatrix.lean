/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/CrystallinePeriodMatrix
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/CrystallinePeriodMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.WachKisin.CrystallinePeriodMatrix. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/WachKisin/CrystallinePeriodMatrix.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline.RegularityFrobenius
import D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin.PeriodMatrixFrame
import D5.S3.Zeros.GRH.Lib.PadicHodge.PeriodRings.FundamentalKernel
import D5.S3.Zeros.GRH.Lib.PadicHodge.BlochKato.CocycleContinuity
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Kisin lattice (Breuil–Kisin module) of a crystalline lattice (known result; see
Lib.PadicHodge.WachKisin.PeriodMatrixFrame).

This file: Period matrix of a crystalline lattice with Frobenius matrix and Hodge basis. -/

open RingHom Algebra BdRPlus Function Matrix algebraMap Module.Basis

seal Module.Basis.baseChange

attribute [local simp ←] IsScalarTower.algebraMap_apply

attribute [local simp] AlgHom.map_smul_of_tower comp_def dotProduct hodgeMatrix mul_assoc smul_smul

variable {p} [ThePrime p] {T Γ ι : Type} [AddCommGroup T] [Module ℤ_[p] T] [Group Γ] [Fintype ι]
  [𝒥 : OverGp Γ p] {ρ : Representation ℤ_[p] Γ T} (a b : ℕ) {c} (hc : Lift.Chart.IsChartOf c 𝒥.toGp)

include hc

lemma Lift.Chart.IsChartOf.exists_mem_bicommutant_of_fixed {b : Bcris} (hb : ∀ g, 𝒥.toGp g • b =
  b) : ∃ s ∈ c.bicommutant, s = b := by
  obtain ⟨⟨u, h, f⟩, m, w, e⟩ := c.exists_bicommutant_mul_p_eq_one,
    exists_witt_coeff_of_isChartOf hc one_ne_zero (by simpa)
  exact ⟨_, mul_mem (pow_mem h m)
    (ainfToBPlus_mem_bicommutant w), by simpa [smul_def, mul_pow, e] using congr($f ^ m • b)⟩

/-- Let j(Γ) contain the fixer of Λ and θ(z), T be crystalline with basis e and jumps in [−a,
b]. There are an invertible M over B with invariant columns and a unit v of A_inf, Eτv = μ,
with U = (Eτ)^aM a period matrix over B^+ for (a + b, v^a). -/
lemma Lift.Chart.IsChartOf.exists_isPeriodMatrix (h : IsCrystalline ρ) e (hab : ∀ k,
  jump ρ (ofId ..) k ≠ 0 → -a ≤ k ∧ k ≤ b) : ∃ M : GL ι Bcris, ∃ U v,
  (∀ g, (repMatrix ρ e g).map (algebraMap _ _) * M.1.map (toGp g • ·) = M.1) ∧ c.E * tau * v.1 =
  mu ∧ c.IsPeriodMatrix U (a + b) (v ^ a) ∧ U.map (algebraMap ..) = (c.E * tau) ^
  a • M.1 := let A m := mapMatrix (MulSemiringAction.toRingHom FrobGal Bcris m)
  let P := {N : _ˣ // ∀ g, (repMatrix ρ e g).map (↑) * A (1, toGp g) N = N.1}
  let F := (ofId ..).mapMatrix
  have I : Injective F := map_injective injective_BPlus_Bcris
  have X {B m} (h : ∀ n i l, _) : ∃ C, F C = (_ * tau) ^ m • B := ⟨_, ext fun i l ↦
    invFun_eq (pow_smul_mem_range_BPlus _ m c.associated_E_mul_tau_mu.dvd' (h · i l))⟩
  (h.exists_basis le_top).rec fun _ ⟨u, hu⟩ ↦ by
  let M : P :=
    ⟨@unitOfInvertible _ _ _ (invertibleToMatrix ..), fun g ↦ ext_col ((equivFun_tensorAction
    ..).symm.trans <| congrArg _ <| u.reindex_apply (u.indexEquiv (e.baseChange _)) · ▸ hu ..)⟩
  let N n : P := ⟨M.1.map (A (.ofAdd n, 1)).1, (.trans (by simp [A]) congr(A _ $(M.2 ·)))⟩
  choose Y hY W k h₄ h₅ _ using fun N :
    P ↦ by simpa [IsUnit, -hodgeMatrix] using (exists_hodge_frame Γ le_top
    (N.1.isUnit.map (mapMatrix _)) (.trans (by simp; rfl) congr($(N.2 ·).map (ofId ..))))
  have J n i := hab (k n i)
    (by rw [(hasJumps_of_rows e (.map _ (W n))⁻¹ _
    (by exact .of_forall (inv_mul_apply_of_isHodgeTateFrame <| isHodgeTateFrame_of_hodgeMatrix <|
    h₅ n ·))).1]; simp)
  have T {B : Matrix ..} {k c P} (Q : GL ι BdRPlus) (h : ∀ i, _) (e : B * _ = hodgeMatrix P k) i l :
    B i l ∈ hodgeFil c := (Q.map (ofId ..).1).eq_mul_inv_iff_mul_eq.2 e ▸ sum_mem fun m _ ↦
    hodgeFil_anti (h m) (by simp [mem_hodgeFil, ← map_inv, field, ← map_mul])
  choose R hX eX using fun M N : P ↦ (hc.exists_mem_bicommutant_of_fixed fun g ↦ congrFun₂ (by
    simpa [← map_mul, N.2] using! congr(M.1⁻¹ * $(M.2 g) * A (1, toGp g) (M.1⁻¹ * N.1)).symm) · ·)
  obtain ⟨eX, ⟨v, o⟩, ⟨w, _⟩, ⟨V, H⟩, Z, _⟩ := ((F (of _)).ext <| eX · ·),
    c.associated_E_mul_tau_mu, c.exists_bicommutant_mul_phi_E_eq_one, X (T (.map _ (Y _).toGL) (J _
    · |>.1) <| h₄ <| N ·), X fun n ↦ T (W (N n)) (neg_le_neg <| J (N n) · |>.2) (((N n).1.map (ofId
    ..).mapMatrix.1.1).inv_mul_eq_iff_eq_mul.2 (by erw [← mul_assoc, h₄]; simp [zpow_ne_zero]))
  have G m : F (m • V) = (_ * m • tau) ^ a • A m _ := ext (by
    simpa [F, smul_def] using! congr(m • $H · ·))
  refine ⟨_, V, v, M.2, o, ⟨⟨Z, I (by simp [*]; module)⟩,
    ⟨Chart.ainfToBPlus (c.φ c.E) ^ a • of (R M (N 1)), w ^ a • of (R (N 1) M), by simp [*, mul_mem,
    pow_mem], I (by simp [↓smul_mul_smul, *, ← mul_pow]), I ((G _).trans
    (by simp [Units.smul_def, H, eX, N, ← o, «φ», -smul_of, FrobGal.smul_def]; module))⟩, fun g h ↦
    (hc g h).choose_spec ▸ ((c.associated_smul_E _).symm.mul_mul associated_smul_tau).rec fun r h ↦
    ⟨r.1 ^ a • (repMatrix ρ e _).map (↑), I (by erw [map_mul, G, H, map_smul
    (ofId Ainf _).mapMatrix, smul_mul_smul, ← mul_pow, mul_comm, h, M.2])⟩, fun f y ↦ ?_⟩, H⟩
  choose t ht using fun l ↦ hc.dvd_extendToBPlus _ (fun k ⟨_, g, rfl⟩ ↦
    congr($(((toGp g).toAlgHom.map_adjugate _).trans (congrArg _ (hY M g))) l k)) f y
  simp [smul_def, ← dvd_def, pi_dvd_iff, ← xi_pow_dvd_iff,
    (c.associated_E_xi.map _).pow_pow.dvd_iff_dvd_left]
  exact fun h i ↦ (Finset.dvd_sum fun _ _ ↦ (h _).mul_left _).trans (by
    obtain _ := congr((ofId _ BdR).mapMatrix $H), ((Y M).toGL.map _).eq_mul_inv_iff_mul_eq.2 (h₄ M)
    simp [F, ofId, map_mulVec, ↓← map_inv, ← coe_inj _ BdR] at *
    simp [*, ← mul_assoc]
    simp [↓← mulVec_mulVec, mulVec, diagonal]
    congr 2; ext j; grind [(algebraMap.coe_inj ..).1 (ht j)] :
    ((↑(W M) * diagonal t * (W M).2) *ᵥ (↑) ∘ (V *ᵥ y)) i = _).dvd
