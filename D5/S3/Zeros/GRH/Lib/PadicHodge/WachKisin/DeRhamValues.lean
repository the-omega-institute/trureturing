/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/DeRhamValues
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/DeRhamValues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.WachKisin.DeRhamValues. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/WachKisin/DeRhamValues.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin.KummerChart
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Kisin lattice (Breuil–Kisin module) of a crystalline lattice (known result; see
Lib.PadicHodge.WachKisin.PeriodMatrixFrame).

This file: Value fields in B_dR, filtration lemmas, S-linear retractions preserve B_dR^+
relations. -/

open Algebra Finset Submodule IntermediateField.algebraAdjoinAdjoin Lift.FrobGroup

variable {p} [ThePrime p] [Γ : GroupOverGp p]

/-- The ring homomorphism A_inf → B_dR given by φ^{−a} followed by the structure map A_inf →
B_dR. -/
noncomputable def Lift.phiInvToBdR a := (algebraMap _ BdR).comp
    (MulSemiringAction.toRingHom _ Ainf (φ ^ a)⁻¹)

variable [k : Lift.KummerChart Γ] {a : ℕ} {r : Ainf} {n : ℤ} (g : k.galMonoid) {x : BdR}

/-- The subfield 𝒦_a of B_dR generated over the fixed field K' of Γ' by the images of S_B and
φ^{−a}S. -/
noncomputable def Lift.KummerChart.valueField a := IntermediateField.adjoin (localFieldOf Γ')
    (.range fun x : k.bicommutant × k.S ↦ algebraMap _ _ x.1 * phiInvToBdR a x.2)

attribute [-simp] LinearMap.map_smul_of_tower map_smul

omit [Lift.KummerChart Γ] in
@[simp] lemma Lift.phiInvToBdR_eq_zero_iff : phiInvToBdR a r = 0 ↔ r = 0 := by simp [phiInvToBdR,
  inv_smul_eq_iff]

lemma Lift.smul_mem_hodgeFil [ThePrime a] {x} (g : Gp a) (h : x ∈ hodgeFil n) :
  g • x ∈ hodgeFil n := (mem_hodgeFil.1 h).choose_spec ▸ by simp [↓smul_mul', ↓smul_tUnit_zpow,
  smul_of_tower_mem, mem_hodgeFil]

namespace Lift.KummerChart

noncomputable instance : MulSemiringAction k.galMonoid BdR :=
  .compHom _ ((toGp.comp snd).domRestrict _)

instance : SMulDistribClass k.galMonoid Ainf BdR := ⟨fun ⟨_, γ, rfl⟩ ↦ smul_distrib_smul (toGp γ)⟩

@[simp] lemma smul_phiInvToBdR : g • phiInvToBdR a r =
  phiInvToBdR a (g • r) := by simp [phiInvToBdR, eq_inv_smul_iff, ← smul_phi_pow_comm]

lemma galMonoid_smul_mem_hodgeFil : x ∈ hodgeFil n → g • x ∈ hodgeFil n := smul_mem_hodgeFil _

/-- For r in A_inf, the image of φ^{−a}(r) in B_dR lies in tB_dR^+ if and only if φ^a(E) divides
r in A_inf. -/
lemma phiInvToBdR_mem_hodgeFil_one_iff : phiInvToBdR a r ∈ hodgeFil 1 ↔ ↑(k.frobE a) ∣ r :=
  algebraMap_mem_hodgeFil_one_iff.trans (by simp [frobE_dvd_iff, ← thetaPhiInv_phi_pow a])

/-- If r in A_inf is not divisible by φ^a(E), then for integers m, n and x in B_dR, φ^{−a}(r)^m·x
lies in tⁿB_dR^+ if and only if x does. -/
lemma mul_mem_hodgeFil_iff_of_not_frobE_dvd (hr : ¬↑(k.frobE a) ∣ r) (m : ℤ) :
  phiInvToBdR a r ^ m * x ∈ hodgeFil n ↔ x ∈ hodgeFil n := .trans
  (by cases m <;> simp [Units.smul_def, smul_def'] <;> rfl) (smul_mem_iff' _ ((BdRPlus.isUnit_iff.2
  (hr ∘ phiInvToBdR_mem_hodgeFil_one_iff.1 ∘ algebraMap_mem_hodgeFil_one_iff.2)).unit ^ m))

/-- For every a ≥ 0 and every integer m, the m-th power of the image of φ^a(E) under φ^{−a}
followed by A_inf → B_dR lies in t^m B_dR^+. -/
lemma frobE_zpow_mem_hodgeFil a m : phiInvToBdR a (k.frobE a) ^ m ∈ hodgeFil m :=
  ((k.associated_E_xi.map _).trans BdRPlus.associated_xi_tPeriod).rec fun w e ↦ mem_hodgeFil.2
  ⟨↑(w ^ m)⁻¹, by cases m <;> simp [phiInvToBdR, frobE_eq, tUnit, ← e, mul_pow, field] <;> rfl⟩

lemma phiInvToBdR_mem_valueField (s : k.S) : phiInvToBdR a s ∈ valueField a :=
  IntermediateField.subset_adjoin _ _ ⟨(1, s), by simp⟩

lemma valueField_zero_le : valueField 0 ≤ valueField a := IntermediateField.gc.monotone_l fun _ ⟨s,
  e⟩ ↦ ⟨(_ * ⟨_, k.ainfToBPlus_mem_bicommutant _⟩, 1), by simpa [phiInvToBdR] using! e⟩

/-- An element x of B_dR fixed by all of Γ' lies in B_dR^+ and in the field 𝒦₀
(`Lift.KummerChart.valueField`). -/
lemma mem_valueField_of_fixed (h : ∀ g : Γ', x = toGp g.1 • x) : x ∈ hodgeFil 0 ∧
  x ∈ valueField 0 := (BdR.exists_sub_mem_of_smul_sub_mem _ ⊥ (sub_eq_zero.2 <| h · |>.symm)).rec
  fun _ e ↦ sub_eq_zero.1 e ▸ ⟨algebraMap_mem_hodgeFil_zero, IntermediateField.algebraMap_mem ..⟩

@[simp] lemma coord₀_one : k.coord₀ 1 = 1 := k.coord₀_coe 1

/-- Let f: A_inf → S be S-linear, r_l in A_inf and v_l in the field 𝒦_a
(`Lift.KummerChart.valueField`), finitely many. A B_dR^+-submodule of B_dR that contains ∑
φ^{−a}(r_l) v_l also contains ∑ φ^{−a}(f(r_l)) v_l. -/
lemma sum_map_mem_of_valueField (f : _ →ₗ[k.S] k.S) {ι} [Fintype ι] (v r : ι → _) (hv : ∀ l,
  v l ∈ valueField a) {W : Submodule BdRPlus _} (h : ∑ l, phiInvToBdR a (r l) * v l ∈ W) : ∑ l,
  phiInvToBdR a (f (r l)) * v l ∈ W := by
  choose d w hw using (instIsFractionRingSubtypeMemSubalgebraAdjoinAdjoin
    ..).exist_integer_multiples_of_finite _ (⟨_, hv ·⟩)
  choose q _ c e using fun l ↦ mem_span_image_iff_exists_fun _ (s := ⊤).1 (by simpa using
    (adjoin_eq_span _ (.range ((algebraMap ..).1.coprod ((phiInvToBdR a).domRestrict _).1))).le (w
    l).2)
  obtain ⟨u, E⟩ := isChartOf.dvd_extendToBPlus _ (Sigma.uncurry c · |>.2) ⟨⟨fun x ↦
    («φ» ^ a)⁻¹ • f («φ» ^ a • x), by simp⟩, fun s
    x ↦ by simpa [smul_def', inv_smul_eq_iff, Subtype.ext_iff] using f.2 ⟨_, by simp [phi_pow_smul,
    ← k.coe_φ_pow]⟩ _⟩ fun ⟨l, ⟨b, s⟩, _⟩ ↦ b * Chart.ainfToBPlus ((«φ» ^ a)⁻¹ • s • r l)
  simp [k.extendToBPlus_mul, k.extendToBPlus_ainfToBPlus, Subtype.ext_iff, smul_def' d.1,
    ← inv_mul_eq_iff_eq_mul₀] at E hw
  convert smul_mem _ u h; with_unfolding_all simpa [↓mul_comm _ (v _), ← hw, ← e, sum_mul,
    ← mul_sum, sum_sigma', smul_def', commutes u, mul_assoc] using! congr(algebraMap _ BdR $E)

/-- Let x in B_dR^+ lie in the field 𝒦_a (`Lift.KummerChart.valueField`) and g, t_1, …, t_m in Γ'.
If φ^a(E) divides (g − 1)∑ t_l s for all s in S, then (g − 1)∑ t_l x lies in tB_dR^+. -/
lemma smul_sub_mem_hodgeFil_of_valueField (g : galMonoid) {m} (t : Fin m → galMonoid) (hx :
  x ∈ valueField a) (h : x ∈ hodgeFil 0) (hg : ∀ s : k.S, (k.frobE a).1 ∣ g • ∑ l, t l • s.1 - ∑ l,
  t l • s.1) : g • ∑ l, t l • x - ∑ l, t l • x ∈ hodgeFil 1 :=
  (mem_hodgeFil.1 h).rec fun y E ↦ (y.exists_Ainf_approx 1).rec fun m ⟨r, e⟩ ↦
  (mul_mem_hodgeFil_iff_of_not_frobE_dvd (not_frobE_dvd_p a) m).1 (by
  have F := sum_mem (t := univ) fun l _ ↦ galMonoid_smul_mem_hodgeFil (t l)
    (sum_map_mem_of_valueField k.coord₀ ![p ^ m • x, -1] ![1, «φ» ^ a • r] (by simp; bound)
    (by simpa [phiInvToBdR, ← E] using! algebraMap_mem_hodgeFil_iff_xi_pow_dvd.2 e))
  simpa [mul_sub, mul_sum, smul_sum, smul_sub, ← sub_eq_add_neg] using
    sub_mem (add_mem (galMonoid_smul_mem_hodgeFil g
    F) (phiInvToBdR_mem_hodgeFil_one_iff.2 (hg (k.coord₀ («φ» ^ a • r))))) F)
