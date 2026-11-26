import GRH.Lib.General.Groups.ResidualIrreducibility
import GRH.Lib.PadicHodge.Crystalline.Jumps
import GRH.Lib.PadicHodge.WachKisin.KummerChartExists
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Kisin lattice (Breuil–Kisin module) of a crystalline lattice (known result; see
Lib.PadicHodge.WachKisin.PeriodMatrixFrame).

Part of: Fontaine's period rings and the fundamental exact sequence (known result; see
Lib.PadicHodge.PeriodRings.BdR).

This file: Regularity of B_max: invariant fractions lie in W[1/p], via a Kummer chart. Kisin's ring
W[[z]] in A_inf, primes φ^a E, Galois congruences, different bound. -/

noncomputable section

attribute [-simp] isUnit_map_iff map_smul

section

open BPlus BdRPlus Lift Polynomial IsLocalization IsScalarTower Algebra IsSeparable algebraMap
variable {p} [ThePrime p] {Γ} [Group Γ] [𝒥 : OverGp Γ p] {c : Chart}

/-- For a chart adapted to j, a_l in the field fixed by j(Γ), y_l ∈ B^+ (finitely many) and f an
S-linear endomorphism of A_inf with extension f̂ to B^+, the sum Σ a_l y_l divides Σ a_l
f̂(y_l) in B_dR^+. -/
lemma Lift.Chart.IsChartOf.dvd_extendToBPlus (hc : c.IsChartOf 𝒥.toGp) {ι} [Fintype ι] (a : ι →
  _) (ha : ∀ l, a l ∈ localFieldOf Γ) f (y : ι → _) : ∑ l, a l * algebraMap _ BdRPlus (y l) ∣ ∑ l,
  (a l : BdRPlus) * c.extendToBPlus f (y l) := by
  let T : Subalgebra ℚ_[p] _ := ⟨c.bicommutant.1, fun r G _ ↦ LinearMap.ext
    ((linearMap_compatibleSMul (nonZeroDivisors ℤ_[p]) ..).1 (G.restrictScalars _) r)⟩
  choose t ht using fun m l ↦ show ∃ t : T, (xi : BdRPlus) ^ m ∣ t - a l by
    obtain ⟨⟨t, k, _⟩, _, g, E⟩ := c.mem_of_fixed_thetaPhiInvS (K := T.map thetaBPlus) fun g h ↦
      (h 0 _ ⟨·, rfl⟩ ⟨_, ainfToBPlus_mem_bicommutant _, thetaBPlus_ainf _⟩) |> fun H ↦ ha l ⟨g,
      hc g ⟨by simpa [FixesLambda, smul_witt_eq_iff, thetaPhiInv, ← coe_wittToQpBar]
      using (H ⟨_, c.S.2 ·⟩), Subtype.ext (H c.z)⟩⟩, isSeparable ℚ_[p] (a l)
    let F := X - g * minpoly _ (a l)
    apply_fun aeval (a l : BdRPlus) at E
    grw [m.lt_two_pow_self]
    refine m.rec ⟨⟨t, k⟩, by simpa [← thetaBdR_eq_zero_iff]⟩ fun m ⟨t, h⟩ ↦ ⟨F.aeval t, ?_⟩
    cases (F.map (ofId _ BdRPlus).1).binomExpansion (a l) (t - a l)
    grw [pow_succ, pow_mul, h]
    simp_all [aeval_algebraMap_apply, F]
  have I m y : (c.E : BPlus) ^ m ∣ ∑ l, (t ..).1 * _ ↔ _ ∣ (↑) ∘ a ⬝ᵥ ofId _ BdRPlus ∘ y :=
    (c.associated_E_xi.map _).pow_pow.dvd_iff_dvd_left.trans (xi_pow_dvd_iff.symm.trans
    (dvd_iff_dvd_of_dvd_sub
    (by simpa [sub_mul] using! Finset.dvd_sum fun _ _ ↦ (ht ..).mul_right _)))
  simpa [← IsDiscreteValuationRing.addVal_le_iff_dvd, prime_xi.irreducible,
    ENat.forall_natCast_le_iff_le] using! ((I ..).1 <| I · y |>.2 · |>.imp' _ fun u h ↦ by
    simpa [c.extendToBPlus_mul, pow_mem] using congr(c.extendToBPlus f $h) :)

/-- Let j: Γ → G_p have open image, containing every g that fixes θ(S) pointwise, S the ring of
a chart over W(F_{p^𝔣}). If b, b' ∈ B, b' ≠ 0 and g(b)b' = b·g(b') on Γ, then p^m b = wb'
for some m and w ∈ W(F_{p^𝔣}). -/
lemma exists_witt_coeff_of_isChartOf (hc : c.IsChartOf 𝒥.toGp) {b b' : Bcris} (h₀ : b' ≠ 0) (h :
  ∀ g, b' * 𝒥.toGp g • b =
  toGp g • b' * b) : ∃ m, ∃ w : WittFq c.f, p ^ m * b = (w : Ainf) * b' := by
  obtain ⟨⟨⟨a, A⟩, e⟩, B, C, _⟩ :=
    @BdR.exists_sub_mem_of_smul_sub_mem p _ Γ _ _ ⊥ (b / b') (by simp_all [smul_div₀',
    ← map_mul, div_eq_div_iff, smul_eq_zero_iff_eq, mul_comm]), surj₂
    (.powers (mu : BPlus)) _ b b'
  have ⟨i, q⟩ : ∃ i, c.extendedCoord i C ≠ 0 := by by_contra!; simp_all [map_units,
              IsUnit.ne_zero, eq_zero_of_p_pow_amaxImage (by simpa [*] using
    (c.eventually_approx_sum_extendedCoord C · |>.exists))]
  obtain ⟨⟨n, γ, E, N⟩, J, _, H⟩ := exists_eq_pow_mul_of_not_forall_dvd (fun _ ↦
    _) (c.extendedCoord i ∘ ![B, C]) fun H ↦ q (c.eq_zero_of_z_pow_dvd (H · |> pi_dvd_iff.1 <| 1)),
    (isIntegral ℚ_[p] a).algebraMap (B := BdR), hc.dvd_extendToBPlus ![1, -a] (by simpa using
    A) (Algebra.linearMap .. ∘ₗ c.adicBasis.coord i) ![B, C]
  simp [funext_iff, -Fin.forall_fin_two] at E
  choose m w u _ _ using (Filter.Eventually.all (c.eventually_exists_pow_mul_eq_add_z_mul <|
    c.mem_bicommutant_of_mul (by bound)
    (left_ne_zero_of_mul (E 1 ▸ q)) <| E · ▸ c.extendedCoord_mem_bicommutant i _)).exists
  have I l := (IsIntegral.of_finite ℤ_[p] (w l)).algebraMap (B := Ainf)
  have := by_contra fun h ↦ N (pi_dvd_iff.2 fun _ ↦ ((IsIntegral.isLocalHom _ (integralClosure
    _ BdR)).1 _ (.of_mul_eq_one_right ⟨_, mul_mem ((J.mul (I 1).algebraMap.tower_top).sub
    (I 0).algebraMap.tower_top).inv.tower_top (sub_mem (algebraMap_mem _ (u 0)) (J.tower_top.smul
    (u 1)))⟩ (Subtype.ext ((mul_assoc ..).trans ((inv_mul_eq_one₀ h).2 (by
    simp [← coe_inj _ BdR, smul_def, ← algebraMap_apply] at *
    norm_cast at *; grind)))))).dvd)
  have ⟨r, t, h⟩ := (w 1).exists_eq_pow_p_mul' fun k ↦ N (((isUnit_p.pow
    m).map (ofId ..)).dvd_mul_left.1 ⟨u, funext (by simp_all)⟩)
  use r, ↑t⁻¹ * w 0, (coe_inj _ BdR).1 ?_
  have := congr(ofId Ainf BdR $(t.mul_inv_eq_iff_eq_mul.2 h))
  simp [h₀, field, ← algebraMap_apply] at *; grind

/-- If a, b ∈ B, b ≠ 0 and g(a)b = a·g(b) for all g near 1 in G_p, then p^n a = wb for some n,
some f and some w ∈ W(F_{p^f}). -/
lemma Bcris.exists_witt_ratio {a b : Bcris} (h₀ : b ≠ 0) (h : ∀ᶠ g : Gp p in nhds 1, b * g • a =
  g • b * a) : ∃ f n, ∃ w : WittFq f, p ^ n * a = (w : Ainf) * b :=
  have ⟨U, h⟩ := NonarchimedeanGroup.is_nonarchimedean _ h
  ⟨_, exists_witt_coeff_of_isChartOf (exists_kummer_chart _ (𝒥 :=
    ⟨_, ⟨U.1.range_subtype ▸ U.2⟩⟩)).choose.chart_isChartOf h₀ (h ·.2)⟩

end

namespace Lift.KummerChart

open Polynomial FrobGroup ValuationRing NeZero
variable {p} [ThePrime p] [Γ : GroupOverGp p] [k : KummerChart Γ] (a : ℕ)

/-- The submonoid of ℤ × Γ consisting of the elements (0, g) with g in the subgroup Γ' of the
Kummer chart. -/
def galMonoid := MonoidHom.mrange (inr.comp k.Γ'.subtype)

/-- The element δ = zτ of A_inf, where z is the coordinate of the Kummer chart. -/
def zTau := tau * k.z

lemma frobE_eq : (k.frobE a).1 = φ ^ a • k.E := by erw [phi_pow_smul, k.coe_φ_pow]

lemma p_not_dvd_frobE : ¬↑p ∣ (k.frobE a).1 := fun ⟨_, h⟩ ↦ not_p_dvd_xi (.trans
  ⟨_, by simpa [frobE_eq, ← eq_inv_smul_iff] using h⟩ k.associated_E_xi.dvd)

/-- The image in W(C^♭) of the element φ^a(E) of A_inf attached to the Kummer chart, as a unit; it
is invertible because p does not divide φ^a(E). -/
def frobEUnit := (isUnit_WittCFlat_of_not_p_dvd (p_not_dvd_frobE a)).unit

/-- The image in W(C^♭) of δ = zτ, as a unit; it is invertible because p divides neither z nor τ
in A_inf. -/
def zTauUnit :=
  (isUnit_WittCFlat_of_not_p_dvd (Ainf.prime_p.not_dvd_mul not_p_dvd_tau k.not_p_dvd_z)).unit

variable {a} {b : ℕ} (g : k.galMonoid)

attribute [local simp] Chart.theta_z_ne_zero ne frobE_dvd_iff zTau coeff_derivative

@[simp high] lemma frobE_ne_zero : (k.frobE a).1 ≠ 0 := p_not_dvd_frobE a ∘ by aesop

/-- For a Kummer chart there is a polynomial P over Λ with E dividing P(z) in S and θ(P'(z))
dividing p^d in the integers of C_p, where d = 0 if e = 1 and d = v_p(e) + 1 otherwise. -/
lemma exists_derivative_dvd_p_pow : ∃ P : (WittFq k.f)[X], k.E ∣ aeval k.z P ∧
  theta (aeval k.z P.derivative).1 ∣ p ^ differentExp := by
  choose r h u using k.weierstrass_division 0 (one_mul _)
  obtain ⟨⟨R, D⟩, _, -⟩ :=
    k.weierstrass_division 0 rfl (k.z ^ k.e); simp [degreeLT, differentExp] at D ⊢
  use X ^ k.e - R, by simpa
  split; simp [*, (by aesop : R.derivative = 0)]
  refine (dvd_total ..).resolve_right fun e ↦ ?_
  choose x H using k.coord₀_coe _ ▸ k.exists_frobE_dvd_sub_of_dvd 0 _ (p ^ _) _ (by simpa)
  have t := u _ (p ^ _ • _) (by simpa [mul_sub] using (h x).mul_left _) ▸ u _ ⟨_, by
    simp [degreeLT]; grind⟩ (dvd_sub_comm.1 H)
  simpa [by simpa [Padic.norm_eq_zpow_neg_valuation] using PadicComplex.norm_extends' p k.e, D,
    OC.dvd_iff_norm_le, norm_p_eq_inv, NeZero.one_le, inv_le_inv₀, pos, pow_le_pow_iff_right₀,
    Fact.out] using
    (theta.comp (algebraMap ..)).map_dvd ⟨_, congr($(t).1.coeff k.e.pred).trans (nsmul_eq_mul ..)⟩

/-- `Γ'` is a group over `G_p`. -/
@[simps] instance : OverGp Γ' p := ⟨toGp.comp _, ⟨Subgroup.isOpen_of_mem_nhds _
  (nhds_one_le_map_nearOne Γ (nearOne_le (⟨·, rfl⟩)))⟩⟩

/-- For a Kummer chart and a ≥ 0, the element p of A_inf is prime to φ^a(E), that is, not
divisible by it. -/
lemma not_frobE_dvd_p a : ¬(k.frobE a).1 ∣ p := by simp

lemma frobE_dvd_phi_pow_tau (h : a < b) :
  (k.frobE a).1 ∣ φ ^ b • tau := have ⟨b, e⟩ := a.exists_eq_add_of_lt h
  by simp [e, pow_add, mul_smul, frobGroup_phi_smul, phi_pow_smul b]

/-- For a Kummer chart and a ≠ b, the element φ^b(E) of A_inf is prime to φ^a(E), that is, not
divisible by it. -/
lemma not_frobE_dvd_frobE_of_ne (h : a ≠ b) : ¬(k.frobE a).1 ∣ k.frobE b := fun d ↦ by
  refine h.lt_or_gt.elim (?_ ∘ (Prime.associated_of_dvd ?_ ?_ d).dvd'.trans ∘ frobE_dvd_phi_pow_tau)
    (?_ ∘ d.trans ∘ frobE_dvd_phi_pow_tau) <;> simp [Prime, isUnit_iff_dvd_one]

lemma smul_phi_pow_comm {X} [MulAction (FrobGroup Γ) X] (x : X) : g • φ ^ a • x = φ ^ a • g • x :=
  by erw [smul_smul, smul_smul, Commute.pow_right (.prod (.all ..) (.one_right _))]

lemma phi_pow_smul_z : φ ^ a • k.z.1 = k.z ^ p ^ a := by simp [phi_pow_smul, k.z_eq_teichmuller]

lemma zTau_dvd_phi_pow_smul a : k.zTau ∣ φ ^ a • k.zTau := by simp [k.z_eq_teichmuller,
  phi_pow_smul, mul_dvd_mul, tau, sub_one_dvd_pow_sub_one]

/-- For a Kummer chart and a ≥ 0, the element δ = zτ of A_inf is prime to φ^a(E), that is, not
divisible by it. -/
lemma not_frobE_dvd_zTau a : ¬↑(k.frobE a) ∣ k.zTau :=
  (·.trans (zTau_dvd_phi_pow_smul a)).mt (by simp)

/-- For a Kummer chart, g in its group Γ' and s ∈ S, the element zτE divides gs − s in A_inf. -/
lemma zTau_mul_E_dvd_smul_sub (s : k.S) : zTau * k.E ∣ g • s - s := let ⟨_, g, rfl⟩ := g
  by obtain ⟨⟨h, hg⟩, _⟩ := fixes g, k.theta_z_ne_zero
     grw [zTau, mul_rotate, mul_assoc,
       k.associated_E_mul_tau_mu.dvd]; apply k.dvd_smul_sub_of_fixesLambda _ h
     erw [← theta_smul, k.z_eq_teichmuller, smul_teichmuller] at *
     cases untilt_dvd_iff.1 (by simpa using hg.symm.dvd)
     simp_all [mu_dvd_of_theta_frobEnd, mul_dvd_mul, ← mul_sub_one]
