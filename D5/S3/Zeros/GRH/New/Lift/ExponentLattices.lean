/- GID: D5/S3/Zeros/GRH/New/Lift/ExponentLattices
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Lift/ExponentLattices
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Lift.ExponentLattices. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Lift/ExponentLattices.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.WachGamma.GaloisOnFrames
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Cokernel bounds and vanishing cup products for Kisin modules (see New.Lift.LongGap).

Part of: Kisin lattice (Breuil–Kisin module) of a crystalline lattice (known result; see
Lib.PadicHodge.WachKisin.PeriodMatrixFrame).

This file: Lattices with prescribed exponents at each E_a, cost of Galois steps, retraction API. -/

noncomputable section

open Finset Algebra MulAction MulSemiringAction NeZero Pointwise Polynomial Set Submodule
  Lift.FrobGroup

attribute [-instance] NormedAlgebra.toAlgebra NormedSpace.toModule SubsemiringClass.toCommSemiring

attribute [-simp] IsUnit.dvd IsUnit.dvd_mul_left IsUnit.mul_left_dvd span_coe_eq_restrictScalars
  map_smul pow_eq_one_iff smul_algebraMap

variable {p} [P : ThePrime p] [Γ : GroupOverGp p] [k : Lift.KummerChart Γ]

/-- The cost of the step n at p_a = φ^a(E): the number v_p(n) + d + 3a, with v_p(0) = 0 and d =
`Lift.KummerChart.differentExp`. -/
def Lift.KummerChart.cost a n := padicValInt p n + (differentExp + 3 * a)

seal WittVector.eval

variable {O} {L : Lift.KummerChart.JumpLattice O} (l i a) {n : ℤ} (c : ℕ → ℤ → ℤ)

/-- For n ≠ 0 there are g in Γ', a unit ω and υ, X in A_inf with g p_a = ω p_a, p_a ∣ gs − s for
all s in S, zτX = ω^n − 1, and υX ≡ p^{cost(a,n)} modulo p_a = φ^a E. -/
lemma Lift.KummerChart.exists_depth_step (hn : n ≠ 0) : ∃ g : galMonoid, ∃ ω : _ˣ, ∃ υ X,
  g • (k.frobE a).1 = ↑ω * k.frobE a ∧ (∀ s : k.S, (k.frobE a).1 ∣ g • s - s) ∧
  (k.frobE a).1 ∣ υ * X - p ^ cost a n ∧ zTau * X = (ω ^ n).1 - 1 := by
  obtain ⟨⟨g, hg⟩, ⟨F, ⟨G, hG⟩, T⟩, ⟨t, ht⟩, u, he⟩ := exists_smul_z (p ^ a),
    exists_derivative_dvd_p_pow,
    exists_add_pow_prime_eq P.out (theta tau) 1, k.associated_E_mul_tau_mu
  obtain ⟨⟨ω, h₀⟩, D⟩ := k.associated_smul_E (toGp g.1), zTau_mul_E_dvd_smul_sub ⟨_, g, rfl⟩ k.E
  erw [← h₀, ← mul_sub_one, mul_comm, mul_dvd_mul_iff_left k.E_ne_zero] at D
  have A : Associated (ω.1 ^ n.natAbs - 1) ((ω ^ n).1 - 1) :=
    n.rec (by simp) (⟨-ω⁻¹ ^ ·.succ, by simp [sub_mul, ← mul_pow]⟩)
  obtain ⟨⟨X, hX⟩, r, hr⟩ := (k.zTau_dvd_phi_pow_smul a).trans
    (_root_.map_dvd (toRingHom _ _ («φ» ^ a)) ((D.trans (sub_one_dvd_pow_sub_one ..)).trans A.dvd)),
    (F.map (algebraMap ..)).binomExpansion k.z.1 (toGp g • k.z - _)
  have ⟨υ, _⟩ := theta_surjective.exists.1 (?_ : thetaPhiInv a X ∣ p ^ cost a n)
  use ⟨_, g, rfl⟩, .map (toRingHom _ _ («φ» ^ a)).1 ω, «φ» ^ a • υ, X, by
    erw [frobE_eq, smul_phi_pow_comm, ← h₀]; simp [mul_comm], k.dvd_smul_sub_of_fixesLambda (hg ▸ by
    simp [frobE_dvd_iff, ← iterate_frobEnd_teichmuller, ← phi_pow_smul]) (fixes g).1, by
    simp [frobE_dvd_iff, *, mul_comm], by simp [← hX, smul_sub, ← map_zpow]
  grw [← mul_dvd_mul_iff_left (not_frobE_dvd_zTau a ∘ frobE_dvd_iff.2), ← map_mul, ← hX,
    toRingHom_apply, thetaPhiInv_phi_pow, A.dvd', lifting_the_exponent theta_surjective ω k.z
    k.chart.4 (dvd_of_mul_left_dvd D) (D.rec fun d e ↦ by
    simp [e, zTau, mul_pow]; grw [← sub_eq_of_eq_add (sub_eq_of_eq_add ht),
      ← pow_dvd_pow (theta k.z) P.out.two_le, ← dvd_pow_self (theta d) out]
    use -t; simp [tau, (map_pow _ epsRoot p).symm.trans untilt_epsTilt]; ring) (by omega)]
  erw [add_sub_cancel, eval_map_algebraMap, aeval_algHom_apply (AlgHom.mk (toRingHom ..) (fixes
    g).1), hg, ← sub_one_mul, ← mul_geom_sum, ← mu, ← he, toRingHom_apply] at hr
  simp [hG, ← h₀, k.E_ne_zero, mul_assoc, mul_left_comm _ k.E.1, ← mul_add, sq] at hr
  apply_fun theta at hr
  simp [k.theta_E, k.smul_theta_of_fixesThetaZ (fixes g), ← sub_eq_iff_eq_add', ← sub_one_mul] at hr
  grw [map_sub, map_one, Dvd.intro _ hr, T, u.coe_dvd (a := 1), cost, padicValInt]
  cases a; simp [zTau]; ring_nf; rfl
  grw [k.theta_z_dvd_p, tau_dvd_xi_sub_p]
  simp +arith [← pow_succ, ← pow_succ', ← pow_add, pow_dvd_pow, dvd_mul_of_dvd_right]

/-- There are p^{d+3a} elements t_l of Γ', d = `Lift.KummerChart.differentExp`, such that φ^a(E)
divides g(∑ t_l s) − ∑ t_l s in A_inf for all g in Γ' and s in S. -/
lemma Lift.KummerChart.exists_depth_step_zero : ∃ t : Fin (p ^ cost a 0) → galMonoid,
  ∀ (g : galMonoid) (s : k.S), (k.frobE a).1 ∣ g • ∑ l, t l • s.1 - ∑ l, t l • s.1 := by
  choose t _ using exists_smul_z
  use (⟨_, t ·, rfl⟩), fun ⟨_, g, rfl⟩ s ↦ (k.exists_dvd_sub_sum_z_pow a rfl s).rec fun w e ↦ ?_
  simp [frobE_dvd_iff, k.dvd_iff_coe_dvd] at *
  simp_rw [e, smul_sum (r := toGp (t _).1)]; rw [sum_comm, smul_sum]; congr! with m
  obtain ⟨n, e⟩ | h := em (p ^ a ∣ m)
  simp [e, pow_mul, ← phi_pow_smul_z, smul_def', ← thetaPhiInv_smul, fixes]
  have Z := by simpa [← theta_teichmuller, ← thetaPhiInv_phi_pow a, phi_pow_smul, ne,
    ← map_pow, ← ofAdd_nsmul] using isPrimitiveRoot_untilt_epsPow (.ofAdd (p ^ a)⁻¹)
  have := (mul_geom_sum (_ ^ m.1 : OC) (p ^ cost a 0)).trans (by
    rw [pow_right_comm, (Z.pow_eq_one_iff_dvd _).2 (by simp +arith [cost, pow_dvd_pow])])
  simp_all [← mul_sum, ← sum_mul, pow_right_comm _ _ m, sum_range,
    ← Z.pow_eq_one_iff_dvd, ← thetaPhiInv_smul, mul_pow, smul_def', fixes]

namespace Lift.KummerChart.JumpLattice

/-- The x in `kisinLocAinf` (A_inf·𝒩, 𝒩 = `kisinLoc`) at the letter i with exponents c:
μ(φ^{−a}x) ∈ t^{c(a,u)}B_dR^+ for all a
and all forms μ of type u ∈ U at σ^{−a}i, the letter a steps before i (`Letter.stepBack`). -/
def withExponents : Submodule Ainf L.Ambient := L.kisinLocAinf ⊓ L.letterPart i ⊓ ⟨⟨⟨{x | ∀ a,
  ∀ u ∈ L.U (i.stepBack a), ∀ μ ∈ L.formsOfType (i.stepBack a) u, valueAt a μ x ∈ hodgeFil
  (c a u)}, by aesop⟩, by simp⟩, by simp_all [valueAt, frobGroup_smul_smul, smul_of_tower_mem]⟩

/-- The S-module of x in `Lift.KummerChart.JumpLattice.kisinLoc` at the letter i with the standard
exponents of level l: 0 at φ^a E for a < l, −u for a ≥ l. -/
abbrev locLetterPart := L.kisinLoc ⊓ (withExponents i (stdExponent l)).restrictScalars _

variable {a : ℕ} {i : Letter} {c : ℕ → ℤ → ℤ} {l : ℕ} {n u : ℤ} {L' c' μ} {x : L.Ambient} {g :
  galMonoid} (F : L.Hom L')

@[simp] lemma valueAt_zero : L.valueAt 0 μ x = μ x := by simp [valueAt]

lemma frobE_smul_mem_kisinLocAinf_iff : (k.frobE a).1 • x ∈ kisinLocAinf ↔ x ∈ kisinLocAinf :=
  ⟨mem_saturateBy_of_smul dvd_rfl (by bound), smul_mem _ _⟩

lemma frobEUnit_zpow_smul_mem_kisinLoc : k.frobEUnit a ^ n • x ∈ L.kisinLoc ↔ x ∈ L.kisinLoc :=
  mem_stabilizer_set.1 (zpow_mem (mem_stabilizer_set.2 fun _ ↦
  .symm ⟨smul_mem _ _, .imp frobE_smul_mem_kisinLocAinf_iff.1 (by
  simpa [phiInvToBdR, smul_def'] using
    flip div_mem (phiInvToBdR_mem_valueField (k.frobE a)) <| · · ·)⟩) n) x

lemma Hom.wittMap_mem_kisinLocAinf : x ∈ L.kisinLocAinf → F.wittMap x ∈ L'.kisinLocAinf :=
  .imp fun _ ↦ .imp_right (by simpa using F.map_mem_kisinAinf ·)

lemma Hom.wittMap_mem_kisinLoc : x ∈ L.kisinLoc → F.wittMap x ∈ L'.kisinLoc :=
  .imp F.wittMap_mem_kisinLocAinf fun h _ ↦ h _ ∘ F.comp_wittMap_mem_forms

lemma gal_smul_mem_kisinLocAinf (hx : x ∈ kisinLocAinf) :
  g • x ∈ kisinLocAinf := have ⟨_, _, rfl⟩ := g
  saturateBy_induction hx (fun _ ↦ le_saturateBy ∘ smul_mem_kisinAinf (by bound)) fun a _ ↦
    mem_saturateBy_of_smul (associated_smul_of_dvd _ (by simp [frobE_dvd_iff,
    (@frobE_dvd_iff p _ k.chart).1])).dvd (by bound) ∘ (frobGroup_smul_smul ..).subst

lemma mem_withExponents_of_mem_hodgeFil (h : x ∈ withExponents i c) (H : ∀ a,
  ∀ u ∈ L.U (i.stepBack a), c a u < c' a u → ∀ μ ∈ L.formsOfType (i.stepBack a) u,
  valueAt a μ x ∈ hodgeFil (c' a u)) : x ∈ withExponents i c' := h.imp_right fun h a u v ↦
  (lt_or_ge ..).elim (H a u v) (hodgeFil_anti · <| h a u v · ·)

lemma mem_withExponents_of_le (h : x ∈ withExponents i c) (H : ∀ a, ∀ u ∈ L.U (i.stepBack a), c' a
  u ≤ c a u := by grind) : x ∈ withExponents i c' := mem_withExponents_of_mem_hodgeFil h (by grind)

lemma valueAt_mem_hodgeFil_of_mem_ainfLattice (e : μ ∈ formsOfType (i.stepBack a) u) (hx :
  x ∈ ainfLattice) (hi : x ∈ letterPart i) :
  valueAt a μ x ∈ hodgeFil (-u) := congr(μ $(mem_letterPart_iff_letterProj.1
  (phi_pow_smul_mem_letterPart_iff.1 (by simpa)))).subst (mem_span.1 (smul_mem_ainfLattice _ hx)
  (((hodgeFil ..).restrictScalars _).comap (μ ∘ₗ L.letterProj _)) (fun _ ⟨k, h⟩ ↦ h ▸ e.2 k))

/-- Let F: L → L' be an equivariant map of lattice data, the jump set of L' lying in that of L
at every letter. Then F sends elements with exponents c at the letter i to elements with
exponents c at i. -/
lemma Hom.map_mem_withExponents (e : L'.U ≤ L.U) : x ∈ L.withExponents i c →
  F.wittMap x ∈ L'.withExponents i c := .imp (by
  simp_all [wittMap_mem_kisinLocAinf, mem_letterPart_iff_letterProj, ← wittMap_letterProj])
  (by simp_all [← valueAt_comp_wittMap, e _ _, formsOfType, comp_wittMap_mem_forms])

/-- Saturation: let r in A_inf be prime to φ^a E for all a, and let x lie in
`Lift.KummerChart.JumpLattice.kisinLocAinf`. If rx has exponents c at the letter i, then so does
x. -/
lemma mem_withExponents_of_smul {r} (hr : ∀ a, ¬(k.frobE a).1 ∣ r) (hx : x ∈ kisinLocAinf) (H :
  r • x ∈ withExponents i c) :
  x ∈ withExponents i c := by simp_all [withExponents, mem_letterPart_iff_letterProj,
  (by aesop : r ≠ 0), zpow_one (phiInvToBdR _ r) ▸ mul_mem_hodgeFil_iff_of_not_frobE_dvd (hr _) 1]

/-- If x has exponents c at the letter i (`Lift.KummerChart.JumpLattice.withExponents`), then (φ^b
E)^m·x, m an integer, has any exponents c' with c'(a,u) ≤ c(a,u) + m for a = b and c'(a,u) ≤ c(a,u)
otherwise, u in the jump sets. -/
lemma frobEUnit_zpow_mem_withExponents b m (hx : x ∈ withExponents i c) (H : ∀ a,
  ∀ u ∈ L.U (i.stepBack a), c' a u ≤ c a u + if b = a then m else 0 := by clear * -; grind) :
  k.frobEUnit b ^ m • x ∈ withExponents i c' := hx.imp (.imp (mem_stabilizer_set.1 (zpow_mem
  (mem_stabilizer_set.2 fun _ ↦ frobE_smul_mem_kisinLocAinf_iff) m) x).2 (by simp_all
  [mem_letterPart_iff_letterProj])) fun _ a u v _ _ ↦ hodgeFil_anti (H a u v) (by split <;> simp_all
  [valueAt_frobEUnit_zpow_smul, add_comm, mul_mem_hodgeFil, frobE_zpow_mem_hodgeFil,
  mul_mem_hodgeFil_iff_of_not_frobE_dvd, not_frobE_dvd_frobE_of_ne, eq_comm])

lemma kisinLocAinf_le_fracSpan : L.kisinLocAinf ≤ L.fracSpan := fun _ ↦
  (saturateBy_induction · kisinAinf_le_fracSpan fun _ _ ↦ mem_saturateBy_of_smul dvd_rfl (by simp))

lemma valueAt_smul_sub (hx : x ∈ kisinLocAinf) (e : μ ∈ L.forms) : valueAt a μ (g • x - x) = g •
  valueAt a μ x - valueAt a μ x := form_gal_smul g e (smul_mem_fracSpan _ (kisinLocAinf_le_fracSpan
  hx)) ▸ (map_sub ..).trans congr(μ $(by simp [inv_smul_eq_iff, ← smul_phi_pow_comm]) - _)

lemma smul_sub_mem_withExponents (hx : x ∈ withExponents i c) (g : k.galMonoid) : g • x - x ∈
  withExponents i c := show _ ∧ _ by simp_all [withExponents, formsOfType, gal_smul_mem_letterPart,
  ↓valueAt_smul_sub, sub_mem_iff_left, galMonoid_smul_mem_hodgeFil, gal_smul_mem_kisinLocAinf]

/-- For x in 𝒩 and g in Γ', gx − x is divisible by zτ in A_inf·𝒩, i.e. (gx − x)/(zτ) lies in
A_inf·𝒩: the factor zτ can be split off. -/
lemma smul_sub_mem_zTau_kisinLocAinf (g : k.galMonoid) (hx : x ∈ L.kisinLoc) : k.zTauUnit⁻¹ •
  (g • x - x) ∈ kisinLocAinf := saturateBy_induction hx.1 (fun x m b ↦ have ⟨_, γ, rfl⟩ := g
  frame_theorem.1.2.2.2.rec fun u v ↦ le_saturateBy (mem_smul_set_iff_inv_smul_mem.1 (v _ (pow_one
    k.z.1 ▸ k.chart.tau_mul_z_pow_dvd) _ (sub_mem (smul_mem_kisinAinf (by bound) m) m) fun μ e ↦
    map_sub μ .. ▸ form_gal_smul ⟨_, γ, rfl⟩ e.1 (kisinAinf_le_fracSpan
    m) ▸ pow_smul_gal_sub_mem_span_of_dvd (k.tau_mul_z_dvd_smul_sub (fixes _)) (u μ e x ⟨m, b.2⟩))))
  (fun a y H e ↦ (zTau_mul_E_dvd_smul_sub g (k.frobE a)).rec
  fun c f ↦ by simpa [smul_distrib_smul, eq_add_of_sub_eq' f, add_smul, mul_assoc, mul_smul k.zTau,
  ← zTauUnit_smul, add_sub_right_comm, ← smul_sub, smul_comm _ (k.frobE a).1,
  frobE_smul_mem_kisinLocAinf_iff, add_mem_cancel_right,
  smul_mem, gal_smul_mem_kisinLocAinf e.1] using H (smul_mem _ _ e)) hx

seal SMul.comp.smul

lemma phi_pow_mem_kisinLoc (hx : x ∈ kisinLoc) : φ ^ l • x ∈ kisinLoc := by
  induction' l with l ih <;> simp [pow_succ', mul_smul, hx]
  exact saturateBy_induction ih.1 (fun y m b ↦ frobEUnit_zpow_smul_mem_kisinLoc (n :=
    .ofNat _).1 (.imp_left le_saturateBy (frame_theorem.2.2.2 y
    ⟨m, b.2⟩))) (fun a y H e ↦ frobEUnit_zpow_smul_mem_kisinLoc (n := 1) (a := a.succ).1
    (by simpa [frobE_eq, pow_succ', mul_smul, frobGroup_smul_smul] using H (smul_mem _ _ e))) ih

lemma span_kisinLoc : span _ ↑L.kisinLoc = L.kisinLocAinf := span_eq_of_le _ (sep_subset ..) fun _ ↦
    (saturateBy_induction · (frame_theorem.1.2.2.1.trans_le (span_mono fun _ ↦
  .imp_left le_saturateBy)) fun a _ ↦
  (by simpa [← frobEUnit_smul] using
  mapsTo_span (f := k.frobEUnit a ^ (-1) • .id) (fun _ ↦ frobEUnit_zpow_smul_mem_kisinLoc.2) ·))

lemma valueAt_mem_valueField (hμ : μ ∈ forms) (hx : x ∈ kisinLoc) : valueAt a μ x ∈ valueField a :=
  have ⟨r, hr, e⟩ := smul_mem_fracSpan («φ» ^ a)⁻¹ (kisinLocAinf_le_fracSpan hx.1)
  have ⟨_, t, v, E⟩ := mem_span_set'.1 (span_kisinLoc.ge (le_saturateBy (frame_theorem.2.2.1 _ e)))
  (not_forall.1 · |>.elim fun i m ↦ mem_of_eq_of_mem ((eq_inv_mul_iff_mul_eq₀ (by simpa)).2 (by
  simpa [S_smul,
    neg_add_eq_zero, -LinearMap.map_smul_of_tower] using congr(valueAt a μ $(frame_theorem.1.1
   (k.adicBasis.coord i) (Option.rec _ _) («φ» ^ a • ·.elim (-(tau ^ L.jumpBound * r)) t)
    (.imp_left (kisinLocAinf_le_fracSpan ·) <| ·.rec hx (phi_pow_mem_kisinLoc <| v · |>.2))
    (by simpa [smul_sum, frobGroup_smul_smul, smul_smul, neg_add_eq_zero] using
    congr(«φ» ^ a • $E.symm)))))) (mul_mem (inv_mem (phiInvToBdR_mem_valueField _))
    (sum_mem fun l _ ↦ mul_mem (phiInvToBdR_mem_valueField _) (valueField_zero_le (by simp [valueAt,
    (v l).2.2, *]))))) (mt k.adicBasis.eq_zero_of_coord (by simp_all [smul_eq_zero_iff_eq]))

lemma exists_coordRetract : ∃ r : kisinLocAinf →ₗ[k.S] L.kisinLoc, ∀ a, ∀ x ∈ kisinLoc, ∀ m,
  (r ⟨a • x, m⟩).1 = k.coord₀ a • x :=
  span_kisinLoc ▸ (LinearMap.exists_range_eq_graph (f := .prod _ (TensorProduct.lift (.lsmul .. ∘ₗ
  k.coord₀))) (surjective_tensorToSpan _ _) (· - · |>.exists_sum_tmul_eq.rec fun _ ⟨_, v, E⟩ ↦ by
  simpa [eq_add_of_sub_eq E, Subtype.ext_iff] using frame_theorem.1.1 _ _ _ (v · |>.2.imp_left
    (kisinLocAinf_le_fracSpan ·)))).imp fun r e a x m _ ↦ congrArg _ (e.le ⟨a ⊗ₜ ⟨x, m⟩, rfl⟩).symm

/-- A chosen S-linear map A_inf·𝒩 → 𝒩 sending a·x to λ₀(a)·x for a in A_inf and x in 𝒩, where
λ₀: A_inf → S is the coordinate of 1. -/
def coordRetract := L.exists_coordRetract.choose

lemma coordRetract_sum {ι} [Fintype ι] {a v : ι → _} (hv : ∀ i, v i ∈ L.kisinLoc) {y} (e : ∑ i,
  a i • v i = y.1) : (coordRetract y).1 = ∑ i, k.coord₀ (a i) • v i := by simp [(by aesop : y = ∑ i,
  a i • ⟨_, (hv i).1⟩), coordRetract, exists_coordRetract.choose_spec, hv]

lemma coordRetract_of_mem_kisinLoc (hx : x ∈ L.kisinLoc) hy : (coordRetract ⟨x, hy⟩).1 = x := by
  simpa [*] using! exists_coordRetract.choose_spec 1 x hx

lemma Hom.map_coordRetract (y : L.kisinLocAinf) (y' : L'.kisinLocAinf) (e : F.wittMap y = y') :
    F.wittMap (coordRetract y) =
  coordRetract y' := have ⟨_, a, v, e₁⟩ := mem_span_set'.1 (span_kisinLoc.ge y.2)
  by simp [coordRetract_sum _ e₁, ← e, ← e₁,
    coordRetract_sum (a := a) (F.wittMap_mem_kisinLoc <| v · |>.2)]

/-- If x has exponents c at i and μ is a form of type u at the letter a steps before i, then
μ(φ^{−a}x) lies in every B_dR^+-submodule W containing t^{c_a(v)}B_dR^+ for all allowed
jumps v ≤ u; u itself need not be allowed. -/
lemma valueAt_mem_of_hodgeFil_le W (hx : x ∈ withExponents i c) (hμ : μ ∈ formsOfType (i.stepBack a)
  u) (H : ∀ v ∈ L.U (i.stepBack a), v ≤ u → hodgeFil (c a v) ≤ W := by grind [hodgeFil_anti.imp]) :
  valueAt a μ x ∈ W := by_contra fun e ↦ have ⟨_, _, f⟩ := kisinLocAinf_le_fracSpan hx.1.1
  have F m := hodgeFil_anti (le_neg.1 (inf_le_right (b := -m)))
    (valueAt_mem_hodgeFil_of_mem_ainfLattice (Int.leInductionDown hμ (fun v l
    f ↦ formsOfType_subset_pred_of_notMem (fun w ↦ e (H v w l (hx.2 a v w μ f))) f) _ inf_le_left) f
    (smul_mem _ _ hx.1.2))
  have ⟨y, _⟩ := mem_hodgeFil.1 (F 0)
  by simp_all [show y = 0 from eq_zero_of_forall_pow_dvd fun _ ↦
    algebraMap_mem_hodgeFil_iff_xi_pow_dvd.1 (by simp_all)]

/-- If x lies in 𝒩, g in Γ', and gx − x has exponents c at the letter i, then (gx − x)/(zτ) also
has exponents c at i. -/
lemma smul_sub_mem_zTauUnit_smul_of_deep (hx : x ∈ L.kisinLoc) (H : g • x - x ∈ withExponents i c) :
    k.zTauUnit⁻¹ • (g • x - x) ∈ withExponents i c := mem_withExponents_of_smul not_frobE_dvd_zTau
  (smul_sub_mem_zTau_kisinLocAinf g hx) (by simpa [← zTauUnit_smul])
