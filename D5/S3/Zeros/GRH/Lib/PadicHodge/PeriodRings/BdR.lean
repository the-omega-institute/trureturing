/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/PeriodRings/BdR
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/PeriodRings/BdR
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.PeriodRings.BdR. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/PeriodRings/BdR.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.Places.CyclotomicCharacter
import D5.S3.Zeros.GRH.Lib.PadicHodge.PeriodRings.BdRPlus
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Fontaine's period rings and the fundamental exact sequence. Here Colmez's B_max
stands in place of B_cris, the period t is built without logarithms, and regularity is proved
through a Kummer chart. Source: P. Colmez, Théorie d'Iwasawa des représentations de de Rham d'un
corps local, Ann. of Math. 148 (1998), III.2-III.3; J.-M. Fontaine, Le corps des périodes p-adiques,
Astérisque 223 (1994); X. Caruso, An introduction to p-adic period rings (2019), §3.

This file: The ideal W(m♭) and continuity of the Galois action on W(C♭) modulo p^m. Galois acts on
[ε]−1 by the cyclotomic character modulo its square. Existence of Fontaine's period t with φt = pt,
gt = χ(g)t, without logarithm. Frobenius contraction: solutions of ξ^n v = uφ(w) in A_max lie in
A_inf[1/p]. B_dR with Galois action, embedding of Q̄_p; surjectivity in the fundamental exact
sequence. -/
seal Finset.univ Finset.sum Finset.prod

noncomputable section

namespace Lift

open WittVector Ideal RingHom Algebra algebraMap Valued IsLocalRing IsLocalization
  MonoidWithZeroHom.ValueGroup₀ Witt NeZero Metric Perfection OC nonZeroDivisors
variable {p} [ThePrime p]

/-- The ideal W(𝔪^♭) of A_inf: the kernel of the map from A_inf to the Witt vectors of the
residue field of O^♭. -/
def wittMaxIdeal := ker toWittResidue

lemma mem_wittMaxIdeal {a} : a ∈ wittMaxIdeal ↔ ∀ n,
  ¬IsUnit (a.coeff n) := by simp [wittMaxIdeal, toWittResidue, WittVector.ext_iff]

lemma teichmuller_mem_wittMaxIdeal {x} (h : ¬IsUnit x) : teichmuller p x ∈ wittMaxIdeal :=
  mem_wittMaxIdeal.2 (·.rec h (by simp))

/-- For a, d in W(C^♭) and m ≥ 0: for all g near 1 in G_p, (ga − a)d lies in W(𝔪^♭) + p^m
W(C^♭). -/
lemma WittCFlat.eventually_smul_sub_mem (a d : WittCFlat) m : ∀ᶠ g : Gp p in nhds 1,
  ∃ b ∈ wittMaxIdeal, p.cast ^ m ∣ (g • a - a) * d - b := by
  delta WittCFlat at *; let := mk' (ValuationRing.valuation OFlat CFlat)
  have A (x : OFlat) : Continuous (· • x : Gp p → CFlat) := .of_at fun g s t ↦ (mem_nhds.1 t).rec
    fun γ h ↦ ((restrict₀_surjective _).comp (mk'_surjective OFlat⁰) γ.1).elim fun (c, e) k ↦
    (not_forall.1 ((γ.ne_zero <| k ▸ by simp [·] : c ≠ 0) ∘ ext)).elim fun n H ↦
    (tendsto_nhds.1 (continuousAt_id.smul_const (x.untiltRoot n).1) ‖(p : OC)‖ (by simp [ne])).mono
    fun a b ↦ h (k ▸ v.restrict_lt_iff.2 (not_le.1 fun ⟨s, i⟩ ↦ H (by
    simp [eq_div_iff, smul_def, ← map_mul, ← map_sub, dist_eq_norm] at *
    erw [← i, map_mul, map_mul, map_sub, map_pow, map_pow, map_zero]
    simp [← coeff_tiltMap _ (x.mk_untiltRoot n), ← map_sub, (Quotient.eq_zero_iff_dvd ..).2,
      dvd_iff_norm_le, b.le, -map_smul])))
  let Z :=
    (mk p (fun i ↦ (⟨(· • a.1 i), (mk'_surjective OFlat⁰ (a.1 i)).rec fun (c, e) ↦ (· ▸ by simpa
    [smul_div₀'] using! ((A c).div (A e) (by simp [smul_eq_zero_iff_eq])))⟩ : C(Gp p, _))) - a) * d
  have E g : Z.map (ContinuousMap.evalAlgHom ℤ _ g).1 = (g • a - a) * d := by aesop
  filter_upwards [(Finset.range m).eventually_all.2 fun i _ ↦ (Z.1 i).2.tendsto 1 (mem_nhds.2
    ⟨1, fun y h ↦ ((v.restrict_lt_one_iff.1 h).rec fun ⟨c, e⟩ h ↦ ⟨⟨c, (h ⟨·.unit.inv,
    e ▸ by simp [smul_smul]⟩)⟩, e⟩ : ∃ c : maximalIdeal OFlat, c.1 • 1 = y - _)⟩)] with g h
  choose! c _ using h; use ⟨(c ·)⟩, mem_wittMaxIdeal.2 (c · |>.2)
  simp_all [pow_dvd_sub_iff_coeff_eq, algebraMap_toAlgebra, WittVector.ext_iff, Algebra.cast,
    smul_def]

end Lift

variable {p} [ThePrime p]

@[simp] lemma Lift.iterate_frobEnd_teichmuller (x : OFlat) n : frobEnd^[n] (WittVector.teichmuller p
  x) = .teichmuller p x ^ p ^ n := by induction n <;> simp_all; ring

/-- For x, y in A_inf with x ≡ y modulo ξ, and every m, one has x^(p^m) ≡ y^(p^m) modulo the
ideal (p, ξ)^m. -/
lemma Lift.pow_p_pow_sub_mem_of_xi_dvd {x y} (h : xi ∣ x - y) m :
    x ^ p ^ m - y ^ p ^ m ∈ Ideal.span {↑p, xi} ^ m := Ideal.mul_le_left (SModEq.sub_mem.1
    ((SModEq.sub_mem.2 (Ideal.mem_of_dvd _ h (by bound))).pow_pow_add_one (by bound) _))

/-- For g in G_p, gμ ≡ χ(g)μ modulo μ² in A_inf, where μ = [ε] − 1 and χ is the cyclotomic
character. -/
lemma Lift.mu_sq_dvd_smul_mu_sub g : mu ^ 2 ∣ g • mu - (cyclotomicGp g).1 • mu :=
  dvd_of_approx Ainf.prime_p.2.1 Ainf.prime_xi.2.1 (constantCoeff_mu_ne_zero ∘ by simp [map_pow,
  Witt.p_dvd_iff]) fun m ↦ let u := WittVector.teichmuller p ((frobeniusEquiv _ p).symm^[m] epsTilt)
  (sq_dvd_add_pow_sub_sub mu 1 _).imp fun _ e ↦ Eq.subst (by
    simp [← smul_pow', ↓← e, cycChar_eq_of_equivariant p (g := g) (j := algebraMap ..)
      (smul_coe_Cp g · |>.symm), pow_right_comm, u, mu, ← map_pow, smul_sub]
    algebra) (sub_mem (@pow_p_pow_sub_mem_of_xi_dvd
    _ _ (g • u) (u ^ (cycCharMod ℂ_[p] (p ^ m) g).1.val) (by simpa [← theta_eq_zero_iff_xi_dvd, u,
    Subtype.ext_iff] using! (cycCharMod_spec g (mod_cast by simp [OFlat]))) m) (Ideal.mem_of_dvd _
    ((map_dvd (algebraMap ..) ((pow_dvd_cycChar_sub_iff m).2
    zmod_eq_natCast_val)).mul_right mu) (by aesop (add 1% Ideal.pow_mem_pow))))

open Algebra NeZero algebraMap Ideal Amax IsScalarTower MulSemiringAction nonZeroDivisors
  AdicCompletion IsLocalization Away BdRPlus FormallySmooth BPlus IsFractionRing

lemma Amax.exists_sub_mul_frobEnd_eq {p} [ThePrime p] {u : Amax} (h : ↑p ∣ u) w : ∃ c,
  c - u * frobEnd c = w := mem_range_of_approx (.id _ - u • frobEnd.toAddMonoidHom) (map_zsmul _ p)
  id (⟨·, by simpa [← sub_eq_iff_eq_add'] using! h.mul_right _⟩) w

/-- There is t in the period ring A, equal to pμ up to a unit of A, with φ(t) = pt and g(t) =
χ(g)t for all g in G_p, χ the cyclotomic character. -/
lemma exists_tPeriod {p} [ThePrime p] : ∃ t, Associated (mu * p : Amax) t ∧ frobEnd t = p * t ∧ ∀ g,
  g • t = (cyclotomicGp g).1 • t := associated_p_frobEnd_xi.rec fun u a ↦
  tau_dvd_xi_sub_p.rec fun w k ↦ let ⟨c, _⟩ :=
    Amax.exists_sub_mul_frobEnd_eq ⟨u.1 ^ 2, rfl⟩ (frobEnd w); let t := mu * (p + mu * c)
    let ⟨e, h⟩ : mu * p * (u.1 + mu * u ^ 2 * frobEnd c) = t ∧ frobEnd t = p * t := by
      grind [map_natCast, frobEnd_algebraMap, frobEnd_tau, xi_mul_tau, congr(frobEnd ($k : Amax))]
    ⟨t, ⟨(isUnit_of_dvd_sub u.isUnit (π := ↑p) (by simp [← xi_mul_tau, mul_assoc])).unit, e⟩, h,
    fun g ↦ (Lift.mu_sq_dvd_smul_mu_sub g).rec fun d k ↦ eq_of_forall_pow_dvd_sub p (.trans ⟨mu ^ 2,
      rfl⟩ <| ·.rec ⟨p * d + ((cyclotomicGp g).1 + mu * d) ^ 2 * g • c - (cyclotomicGp g).1 •
      c, by simp [t, eq_add_of_sub_eq k, smul_def]; ring!⟩ fun n ⟨z, H⟩ ↦ ⟨u ^ 2 * frobEnd z,
      mul_left_cancel₀ (ne ↑p) (by convert congr(frobEnd $H) <;> simp [← smul_frobEnd, h,
      ← congr(frobEnd $xi_mul_tau), ← a, smul_def] <;> simp [frobEnd] <;> ring)⟩)⟩

/-- The period t: the image in B_dR^+ of a chosen element t of A, a unit multiple of pμ, with
φ(t) = pt and g(t) = χ(g)t on G_p. -/
def tPeriod {p} [ThePrime p] : BdRPlus := exists_tPeriod.choose

/-- Contraction: let V ⊂ B^+ lie in the image of A, let u be in A_inf, and suppose every v in V
satisfies ξ^n v = u φ(w) for some w in V. Then p^(n+1) V lies in the image of A_inf. -/
lemma exists_Ainf_eq_of_contraction {p} [ThePrime p] (V : Set _) n (u : Ainf) (hV : ∀ v ∈ V,
  v ∈ amaxImage) (h : ∀ v ∈ V, ∃ w ∈ V, xi ^ n • v = u • frobEnd w) v (hv : v ∈ V) : ∃ a : Ainf, a =
  p ^ n.succ * v := by
  choose! y hy using hV
  have := algebraMap_apply Ainf Amax BPlus
  choose a z H using fun k ↦ show ∃ a : Ainf, ∃ z, a =
      p ^ n.succ * y v - tau ^ n.succ * z * p ^ k by
    induction' k with k ih generalizing v
    simpa [eq_sub_iff_add_eq, eq_comm] using
      (y v).exists_p_pow_mul_eq_add ⟨1, by simp [tau_dvd_xi_sub_p]⟩ _
    obtain ⟨N, w, W, e⟩ := Ainf.prime_xi.1, h v hv
    let ⟨c, z, C⟩ := ih w W
    refine (pow_dvd_of_map (x := u * frobEnd c) (n := n) (map_mul (algebraMap _ BPlus) _)
      (by simpa) (by simp [↓← thetaBPlus_eq_zero_iff, theta_eq_zero_iff_xi_dvd]) ⟨_, ?E⟩).imp fun d
      e ↦ ⟨u * X * frobEnd z, injective_Amax_BPlus (by simpa [e, N] using! ?E)⟩
    simp_all [smul_def, mul_pow, ← frobEnd_algebraMap, frobEnd_algebraMap tau, ← xi_mul_tau]; grind
  peel by simpa [SModEq.sub_mem] using IsPrecomplete.prec' a fun h ↦ .sub_mem.2 ((mul_top
    _).ge (mem_span_pow_of_p_pow_dvd (by simp [H, dvd_sub, (pow_dvd_pow _ h).trans])))
  simp_all [← eq_of_forall_pow_dvd_sub _ (by
    simpa [H, sub_right_comm, dvd_sub_left] using p_pow_dvd_of_mem_pow <| this ·)]

variable {p : _} [ThePrime p] (g : Gp p) {R} [CommRing R] [SMul (Gp p) R] [Algebra R BPlus]
  [SMulDistribClass (Gp p) R BPlus] (x : PadicAlgCl p) {S} [CommRing S] [SMul R S]

attribute [local simp ←] xi_mul_tau IsScalarTower.algebraMap_apply

attribute [-simp] map_smul smul_algebraMap p_mul_X

instance : SMulCommClass FrobGal ℚ_[p] Bcris :=
  ⟨(map_smul <| toAlgHom _ _ · |>.extendScalarsOfIsLocalization _ ℤ_[p]⁰)⟩

/-- `G_p` acts on `B_dR⁺`. -/
instance actBdRPlus : MulSemiringAction (Gp p) BdRPlus := by
  apply actionOfHoms _ fun g ↦
    adicMap (toRingHom _ _ g) (by simp [mem_span_singleton, ↓← thetaBPlus_eq_zero_iff])
    <;> intros <;> exact DFunLike.ext' (map_ext _ fun _ ↦ ext_evalₐ (by simp [mul_smul]))

instance : SMulDistribClass (Gp p) R BdRPlus := smulDistribClass_of_tower fun _ :
  BPlus ↦ by apply adicMap_algebraMap

/-- The de Rham period field B_dR, defined as the fraction field of the ring B_dR^+. -/
@[instance_reducible] def BdR := FractionRing BdRPlus deriving Field

variable [Algebra R BdRPlus] [Algebra S BdRPlus] [IsScalarTower R S BdRPlus]
  [FaithfulSMul R BdRPlus] in
deriving instance Algebra R, IsScalarTower R S, IsFractionRing BdRPlus, FaithfulSMul R for @BdR p _

instance : CharZero BdR := charZero_of_charZero ℚ_[p] _

/-- `G_p` acts on `B_dR`. -/
instance actBdR : MulSemiringAction (Gp p) BdR := mulSemiringAction _ BdRPlus _

instance : SMulDistribClass (Gp p) R BdR := smulDistribClass_of_tower fun _ : BdRPlus ↦ by simp

instance : Algebra Bcris BdR :=
  (Away.lift _ ((coe_eq_zero_iff ..).ne.2 mu_ne_zero).isUnit).toAlgebra

instance : IsScalarTower R Bcris BdR := of_algebraMap_eq fun _ ↦ .symm (lift_eq _ _)

instance : FaithfulSMul Bcris BdR := .of_injective (ofId Bcris _)
  ((lift_injective_iff _).2 (by simp [injective_BPlus_Bcris.eq_iff]))

attribute [local instance] FormallyEtale.of_isSeparable

instance : Algebra (PadicAlgCl p) BdRPlus := (Exists.choose (exists_adicCompletionEvalOneₐ_comp_eq
  (thetaEquiv.symm.toAlgHom.comp (algHom ..))) : _ →ₐ[ℚ_[p]] BdRPlus).toAlgebra

instance : IsScalarTower ℤ_[p] (PadicAlgCl p) BdRPlus := to₁₃₄ _ ℚ_[p] ..

/-- In B_dR^+ the period t equals ξ times a unit. -/
lemma BdRPlus.associated_xi_tPeriod : Associated ↑xi tPeriod :=
  .trans (by simp [associated_mul_isUnit_right_iff, ne]) (.map _ exists_tPeriod.choose_spec.1)

/-- For x in Q̄_p, the map θ: B_dR^+ → ℂ_p sends the image of x in B_dR^+ to x itself, viewed in
ℂ_p. -/
@[simp] lemma thetaBdR_algebraMap_qpBar : thetaBdR x = .coe' x := thetaEquiv.eq_symm_apply.1
  (AlgHom.congr_fun (exists_adicCompletionEvalOneₐ_comp_eq _).choose_spec x)

@[simp] lemma thetaBdR_smul x : thetaBdR (g • x) = g • thetaBdR x := (x.exists_Ainf_approx 1).elim
  fun _ ⟨_, _, e⟩ ↦ by simpa [smul_sub, ne] using congr(thetaBdR (g • $e) = g • thetaBdR $e)

instance : SMulDistribClass (Gp p) Bcris BdR := smulDistribClass_of_tower (B := Bcris) (congrFun (by
  apply IsLocalization.ext (.powers (mu : BPlus)) <;> simp))

/-- The embedding of Q̄_p in B_dR is G_p-equivariant: g applied to the image of x is the image
of g(x). -/
@[simp] lemma BdR.smul_algebraMap_qpBar : g • (x : BdR) = g x := by simp [← by
  simpa using congrArg thetaBdR (coe_inj.1 (.trans (((toAlgHom _ _ g).extendScalarsOfIsLocalization
  ℚ_[p] ℤ_[p]⁰).restrictNormal_commutes _ x) (smul_algebraMap_eq_algebraMap_smul (R := BdR) ..)))]

/-- Surjectivity in the fundamental exact sequence: for a in B and β in B_dR there is y in B
with φ(y) − y = a and y − β in B_dR^+.

Known result: Fontaine's period rings and the fundamental exact sequence. -/
lemma Bcris.fundamental_sequence_surjective a β : ∃ y : Bcris, ∃ x : BdRPlus, frobEnd y - y = a ∧
  (x : BdR) = y - β := by
  obtain ⟨⟨U, V⟩, x, z, Z, E⟩ := (by simpa [-isUnit_map_iff] using isUnit_smul_of_dvd_mu 1 dvd_rfl),
    div_surjective BdRPlus β; obtain ⟨k, u, rfl⟩ := exists_associated_xi_pow (ne_zero Z)
  obtain ⟨⟨r, R⟩, y, x₀, X⟩ := U.pow k, (x * u.2).exists_xi_pow_dvd_sub k
  let ⟨m, b, hb⟩ := surj (mu : BPlus) (a - frobEnd (y • ↑r⁻¹) + y • ↑r⁻¹)
  let ⟨n, e, _, ⟨w, rfl⟩, h⟩ := b.exists_Ainf_approx 0 m.succ
  obtain ⟨⟨c, rfl⟩, ⟨s, S⟩, ⟨d, rfl⟩, t, T⟩ := e.exists_frobEnd_sub_xi_pow_mul_eq m,
    (V.pow m).smul (isUnit_p.pow n).unit, exists_sub_mul_frobEnd_eq associated_p_frobEnd_xi.dvd w,
    (by simp [ne] : IsUnit (tau ^ m * p ^ n : BdRPlus))
  use y • r⁻¹ + c • s⁻¹ - mu * d, c • t⁻¹ - mu * d - x₀, (s * U.unit ^ m).mul_right_inj.1 ?_
  linear_combination (norm := (simp [smul_def, Ainf.prime_xi.1, *]; ring)) -congr($E - r.2 * $X)
  linear_combination (norm := (simp [smul_def, S]; ring))
    congr(frobEnd (c • $(s.3)) - xi ^ m • c • $(s.3) - p ^ n * $hb - $h)
