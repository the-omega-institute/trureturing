/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/Comparison/CrystallineLimit
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/Comparison/CrystallineLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.Comparison.CrystallineLimit. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/Comparison/CrystallineLimit.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin.CrystallinePeriodMatrix
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Dwork's trick, as an integral crystalline comparison with a uniform denominator. The statement
here is integral over A_max. It uses one multiplier, invertible in B_max, that depends only on the
field and the range of weights, and not on the lattice or its rank. Source: M. Kisin, Crystalline
representations and F-crystals, Progr. Math. 253 (2006), Lemma 1.2.6; M. Kisin, Potentially
semi-stable deformation rings, JAMS 21 (2008), Lemma 2.2; B. Bhatt, P. Scholze, Prismatic F-crystals
and crystalline Galois representations (2023), proofs of Prop. 5.3 and Thm 7.9.

Part of: Limits of crystalline representations with bounded weights are crystalline (known result;
see Lib.PadicHodge.Limit.LocalLimit).

This file: Dwork's trick: after Frobenius the frame is constant basis times unit over A_max. Uniform
denominator for the integral crystalline comparison over A_max, independent of rank. Limit of
crystalline representations of bounded weights is crystalline (Liu), group-ring form. -/

namespace Lift.Chart

open BPlus Matrix Algebra PowerSeries WittVector Ideal Function NeZero RingHom Finset Nat
variable {p} [ThePrime p] {c : Chart} {d : Type} [Fintype d] {t} (hΛ : c.FixesThetaZ t)

attribute [-simp] isUnit_map_iff smul_of algebraMap_smul RingHom.coe_pow map_smul
  LinearMap.map_smul_of_tower

attribute [local simp] C_eq_algebraMap Subalgebra.algebraMap_def pow_mem extendToBPlus_mul
  extendedCoord_oneIndex_eq_self ite_mem sub_mul Associated.dvd associated_E_xi

lemma tau_mul_z_pow_dvd {n h a} (H : ainfToBPlus (tau * c.z ^ n) ∣ ainfToBPlus (c.E ^ h * a)) :
  tau * c.z ^ n ∣ a := by
  obtain ⟨a, rfl⟩ := @tau_dvd_of_theta_frobEnd _ _ a fun j ↦ by
    grw [c.associated_E_xi.dvd] at H
    obtain _ := theta_iterate_frobEnd_xi j, map_dvd thetaBPlus (map_dvd (frobEnd ^ (j + 1)) H)
    simp_all [coe_pow, ne]
  grw [pow_dvd_of_map _ _ (@z_dvd_of_dvd_E_pow_mul _ _ c h)] <;> simp_all [mul_left_comm,
    mul_dvd_mul_iff_left, ne_zero_of_map c.theta_z_ne_zero]

lemma frobEnd_pow_ainfToBPlus l s : (frobEnd ^ l) (ainfToBPlus s.1) = ainfToBPlus ((c.φ ^ l) s).1 :=
  coe_φ_pow .. ▸ iterate_frobEnd_algebraMap ..

@[simp] lemma frobEnd_pow_ainfToBPlus_z l : (frobEnd ^ l) (ainfToBPlus c.z) =
  ainfToBPlus c.z ^ p ^ l := by simp [coe_pow, z_eq_teichmuller]

include hΛ

lemma tau_mul_z_dvd_smul_sub {y} (hy : y ∈ c.bicommutant) : ainfToBPlus (tau * c.z) ∣ t • y - y :=
  (c.z_dvd_sub hΛ.1 hy).rec fun b
  h ↦ by grw [h, map_mul, mul_comm, ← dvd_of_thetaBPlus_frobEnd_eq_zero b tau_dvd_of_theta_frobEnd
  fun i ↦ (frobEnd^[i + 1] y).exists_p_pow_mul_eq_amax.rec fun k ⟨a, e⟩ ↦
  (c.exists_pow_mul_extendedCoord_eq_add c.E ⟨0, by simp⟩ a 1).rec fun s ⟨v, _, f⟩ ↦ by
    simpa [← e, Iterate.rec (· ∈ _) hy @c.frobEnd_mem_bicommutant, c.smul_theta_of_fixesThetaZ hΛ,
      mul_add, z_eq_teichmuller, ne, theta_E,
    eq_add_of_sub_eq h, c.z_eq_teichmuller ▸ c.theta_z_ne_zero, -theta_teichmuller, -iterate_succ,
    Commute.iterate_right (smul_frobEnd t) _ _] using congr(thetaBPlus (t • $f - $f))]

/-- Radius lemma. Let t fix Λ, tz = [ε]z, Z'Z = E^h, Z over S_B, tZ = ZG with G over A_inf, 3e ≤
p^l. Then φ^lZ = φ^l(E)^b·CV, V ∈ GL_d(A), C fixed by the fixer of Λ; if eA ≤ p^lδ, the y ∈
S^d with Vy ∈ ℕ^d + E^A(B^+)^d span p^{4δ}S^d at least.

Known result: Dwork's trick: integral crystalline comparison with a uniform denominator. -/
lemma radius_lemma (ht : t • c.z = teichmuller p epsTilt * c.z.1) {Z Z' : Matrix d d BPlus} {h}
  (hZ : ∀ i j, Z i j ∈ c.bicommutant) (e : Z' * Z = c.E ^ h • 1) {G} (hG : t • Z =
  Z * Matrix.map G ainfToBPlus) {l} (hl : 3 * c.e ≤ p ^ l) b : ∃ (V : (Matrix d d Amax)ˣ) (C :
  Matrix d d _), (∀ g : Gp p, FixesLambda c.f g → g • C = C) ∧ Z.map frobEnd^[l] =
  (c.frobE l).1 ^ b • (C * V.1.map (algebraMap ..)) ∧ ∀ A δ, c.e * A ≤ p ^ l * δ → ∀ x : d
  → c.S, p ^ (4 * δ) • x ∈ Submodule.span c.S {y | ∃ r : d → ℕ, ∀ i, ainfToBPlus c.E ^ A ∣ (V.1.map
  (algebraMap _ BPlus) *ᵥ fun i ↦ ainfToBPlus (y i)) i - r i} := by
  have P {n N} (h : c.e * n ≤ N) : ∃ y, ainfToBPlus c.z ^ N = p ^ n * ofId _ _ y :=
    ((pow_dvd_pow_of_dvd (by
    simpa [(c.unitSeries.isUnit.map _).map] using dvd_trans ⟨_, p_mul_X.symm⟩ (map_dvd _ c.7.dvd'))
    n).trans (by grw [← pow_mul, h])).imp fun y e ↦ by simpa using! congr(ofId _ BPlus $e)
  obtain ⟨⟨T, _⟩, hp, ⟨r, hr⟩, ⟨u, hu, U⟩, q, hq⟩ := P (mul_comm 3 _ ▸ hl), isUnit_p.pow,
    c.z_dvd_E_sub_p, c.exists_bicommutant_mul_p_eq_one,
    c.z_dvd_E_sub_p.trans (sub_dvd_pow_sub_pow _ _ h)
  have ⟨ev₀, h₀⟩ := exists_algHom_X_eq c.S (mem_span_singleton.2 (dvd_mul_right ↑p T))
  let ev := (algHom _ _ BPlus).comp ev₀
  have hX : ainfToBPlus c.z ^ p ^ l = p ^ 2 * ev X := by simp [ev, algHom, *]; ring
  choose m w y hy f using (u ^ h * Z' · · |> c.extendedCoord_mem_bicommutant c.oneIndex |>
    c.eventually_exists_pow_mul_eq_add_z_mul |>.exists)
  let B := of ((u ^ m · ·) * (ainfToBPlus <| ofId _ _ <| w · ·))
  have H (g : Gp p) := by simpa [mul_assoc, mul_eq_one_symm U] using congr(g • $U * u)
  let W := (u ^ h * ainfToBPlus q) • 1 - of ((u ^ m · ·) * y) * Z
  have hW : B * Z = 1 + ainfToBPlus c.z • W := by
    ext i j; linear_combination (norm := (simp +zetaDelta [mul_apply, ← sub_eq_of_eq_add (f ..),
      mul_sub, mul_add, ← mul_assoc, ← mul_pow, U, mul_sum, hu, hZ, mul_comm (Z' ..),
      smul_def (A := BPlus), mul_right_comm _ (Z ..)]; split <;> ring_nf))
      congr(u ^ h * (c.extendedCoord c.oneIndex ($e i j) + ainfToBPlus ($hq) * row 1 i j))
  have hY : t • (B * Z) = B * Z * G.map ainfToBPlus := (by simp [↓mul_assoc, ← hG, B, entrywise,
    smul_sum, H, hΛ])
  have hG i j : tau * c.z ∣ (G - 1) i j := pow_one c.z ▸ tau_mul_z_pow_dvd (by
    simpa [mul_sub, ← mul_assoc, *, smul_def (A := BPlus), apply_ite] using show _ ∣
    (Z' * (t • Z - Z)) i j from dvd_sum fun k _ ↦ (tau_mul_z_dvd_smul_sub hΛ (hZ k j)).mul_left _)
  have := IsHausdorff.mk fun x h ↦ c.eq_zero_of_z_pow_dvd (by grw [(hp 2).dvd_mul_left.1
    ((dvd_pow_self _ out).trans hX.dvd), smodEq_span_pow_iff_dvd.1 <| h ·, sub_zero])
  -- the entries of `φ ^ l (B Z)` are values of power series, by successive approximation
  choose F hF using fun i j ↦ mem_range_of_approx ev.toAddMonoidHom (ev.toSemilinearMap.2 X)
    (X := {x : ℕ × (d → _) // ∃ q : ℕ, ∃ A : d → _, ∀ j, x.2 j ∈ c.bicommutant ∧ ainfToBPlus (A j) =
    q • (B * Z) i j - ainfToBPlus c.z ^ x.1.succ * x.2 j}) (fun ⟨(n, W), _⟩ ↦
    p ^ (n - padicValNat p n ! + 2) * (frobEnd ^ l) (W j)) (fun ⟨(n, W), q, A, e⟩ ↦ by
    have ⟨α, β, f⟩ := c.exists_tau_mul_E_eq_mul_epsTilt_pow_sub n.succ_ne_zero
    set v := padicValNat p n.succ
    let a := n.succ - padicValNat p n.succ !
    choose s W' hW' H using fun j ↦ show ∃ s : c.S, ∃ W' ∈ c.bicommutant, ainfToBPlus s =
      p ^ v.succ * W j - ainfToBPlus c.z * W' from ((univ.dvd_sum fun l _ ↦
      (map_dvd ainfToBPlus (hG l j)).mul_left (W l)).sub ((tau_mul_z_dvd_smul_sub hΛ
      (e j).1).mul_left (ainfToBPlus (mu + 1) ^ n.succ))).rec fun D hD ↦
      have hV : ainfToBPlus (c.E ^ 0 * (α * (∑ l, A l * G l j - t • A j))) = ainfToBPlus (tau *
        c.z ^ n.succ) * (p ^ v.succ • W j - ainfToBPlus c.z * (ainfToBPlus α * D + -ainfToBPlus (p ^
        v • r + β * c.E) * W j)) := by linear_combination (norm :=
        (simp [← smul_algebraMap_eq_algebraMap_smul t (A _), smul_sub, e, ht, mu, mul_sub,
        mul_assoc, mul_apply, ← mul_sum]; ring)) -ainfToBPlus c.z ^ n.succ * (ainfToBPlus α * hD
        + W j * congr(ainfToBPlus ($f - p ^ v • tau * $hr))) - ainfToBPlus α * congr(q • $hY i j)
      (tau_mul_z_pow_dvd ⟨_, hV⟩).rec fun x hx ↦ ⟨_, _, c.extendedCoord_mem_bicommutant _ _, by
        simp [hx, ne_zero_of_map c.theta_z_ne_zero] at hV
        simpa [e, extendToBPlus_ainfToBPlus, -map_add] using congr(c.extendedCoord c.oneIndex $hV)⟩
    use C (p ^ a * (c.φ ^ l) (s j)), ⟨(n.succ, W'), p ^ v.succ * q, p ^ v.succ • A + (c.z.1 ^
      n.succ * s ·), by simp; grind⟩
    simp [show n - padicValNat p n ! + 2 = a + v + 1 by clear * -; grind [padicValNat_factorial_le,
      factorial, padicValNat.mul], ← frobEnd_pow_ainfToBPlus, hX, H]; ring) ⟨(0, W i), 1, row 1
    i, by simp (maxDischargeDepth := 5) [↓hW, W, mul_apply, sub_mem, _root_.sum_mem, mul_mem, *]⟩
  have ⟨⟨V, hV⟩, ε, hε⟩ : IsUnit (1 + @X c.S _ • of F) ∧ IsUnit (1 + X * C (p * (c.φ ^ l) r))
    := by simp [isUnit_iff_isUnit_det, det_one_add_smul X, isUnit_iff_constantCoeff]
  have hD := Matrix.map_mul.symm.trans (show (B * Z).map (frobEnd ^ l) = ev.mapMatrix V by
    ext; simp [hW, hV, hX, by simpa using hF]; ring)
  obtain ⟨⟨D, e⟩, V, rfl⟩ := (isUnit_of_mul_isUnit_left (hD ▸ V.isUnit.map _)).smul
    (hp b).unit, MulAction.surjective (ε ^ b) V
  refine ⟨V.map ev₀.mapMatrix.1.1, _, fun g hg ↦ congrArg (·⁻¹.1) (show
    D.map (MulSemiringAction.toRingHom ..).mapMatrix.1 = D by ext; simp [B, *,
    coe_pow, Commute.iterate_right (smul_frobEnd g) l _]), by
    erw [← mul_smul_comm, D.eq_inv_mul_iff_mul_eq, e, smul_mul_assoc, hD]; ext
    simp [frobE, hε, hX, eq_add_of_sub_eq' hr, ← mul_pow, ← mul_assoc, smul_def (A := BPlus),
      Units.smul_def, ← frobEnd_pow_ainfToBPlus]; ring!, fun A δ hA x ↦
    Submodule.mem_span.2 fun T hT ↦ (P hA).rec fun y hy ↦ ?_⟩
  -- a unit over `S⟦X⟧`, evaluated at `X = z ^ p ^ l / p ^ 2`, is nearly a matrix over `S`
  choose s G' e using fun D G ↦ show ∃ s : c.S, ∃ G', p ^ (2 * D) * ev G =
    ainfToBPlus s + ainfToBPlus c.z ^ (p ^ l
    * D) * ev G' from D.rec ⟨0, by simp⟩ fun D ⟨s, G', e⟩ ↦ ⟨p ^ 2 * (s + constantCoeff G' * c.z ^
    (p ^ l * D)), .mk _, by rw [G'.eq_X_mul_shift_add_const] at e
                            linear_combination (norm := (simp [pow_mul, hX]; ring)) p ^ 2 * e⟩
  choose a _ k using fun G ↦
    c.exists_pow_mul_extendedCoord_eq_add c.E ⟨0, by simp⟩ (y * ev₀ (G' δ G)) A
  let f := ((Ideal.Quotient.mk (span {ainfToBPlus c.E ^ A})).comp ev.1).mapMatrix (m := d)
  let g := f.comp C.mapMatrix
  choose N H using fun F ↦ show ∃ N, g N = p ^ (2 * δ) • f F from ⟨F.map (s δ + a), ext fun i j ↦
    Ideal.Quotient.eq.2 (have k := k (F i j)
    by erw [map_mul, ← map_p_pow_mul, ← mul_assoc, ← hy, extendToBPlus_mul, fun G ↦
      (sub_eq_zero.1 (c.eq_zero_of_z_pow_dvd fun n ↦ by
      grw [Nat.le_mul_of_pos_left n (pos (p ^ l)), ← (hp (2 * n)).dvd_mul_left]
      simp [mul_sub, ← map_p_pow_mul, e, _root_.dvd_sub]) :
      c.extendToBPlus _ (ev G) = ev G)] at k <;> simp [mem_span_singleton, e, k])⟩
  have K N (r : ℕ) (h : f V * g N = r) := (range_mulVecLin N).trans_le (T.span_le.2 fun
    | _, ⟨k, rfl⟩ => hT ⟨col r k, (by simpa +zetaDelta [entrywise,
      Matrix.natCast_apply, apply_ite, ← Quotient.eq_zero_iff_dvd] using! congr($h · k))⟩)
  convert add_mem (K (p ^ (4 * δ) • 1 - N V⁻¹ * N V) 0 ?_ ⟨x, rfl⟩)
    (K (N V⁻¹) (p ^ (2 * δ)) ?_ ⟨N V *ᵥ x, rfl⟩) <;>
    simp [H, ← f.map_mul, -nsmul_eq_mul, ← nsmul_one, smul_smul, ← pow_add, ← add_mul]

end Lift.Chart

open TensorProduct Matrix Module Submodule MulSemiringAction Function algebraMap MonoidAlgebra
  Finset LinearMap Algebra Lift nsmulRange NeZero ContinuousMap Set Metric IsLocalRing PadicInt
  WittVector

/-- For toGp : Γ → Gp p (from OverGp) with open image and h ≥ 0, some a in A, invertible in B,
serves every crystalline Z_p-lattice T with jumps in [0, h]: a⊗T lies in the A-span of (A⊗T)^Γ, and
UU' = a for matrices over A, U with Γ-invariant columns.

Known result: Dwork's trick: integral crystalline comparison with a uniform denominator. -/
lemma Lift.uniform_period_bound {p} [ThePrime p] Γ [Group Γ] [OverGp Γ p] h : ∃ a : Amax, IsUnit
  (a : Bcris) ∧ ∀ {T ι : Type} [AddCommGroup T] [Module ℤ_[p] T] [Fintype ι] (e : Basis ι ℤ_[p] T)
  {ρ}, IsCrystallineUpTo h ρ → (∀ t, a ⊗ₜ t ∈ span Amax (fixedPeriods ρ _ ⊤)) ∧ ∃ U U', U * U' =
  a • 1 ∧ ∀ g : Γ, ((ρ g).toMatrix e e).map ((↑) : _ → Amax) * U.map (toGp g • ·) =
  U := let ⟨k, hf, _⟩ := exists_kummer_chart Γ
  let m := (.ofAdd (p.clog (3 * k.e)), 1)
  let α := (algebraMap ..).comp (toRingHom FrobGal _ m)
  ⟨α (k.E * tau) ^ h, by simpa using! (isUnit_smul_of_dvd_mu m k.associated_E_mul_tau_mu.dvd).pow h,
    fun e ρ ⟨c, J⟩ ↦ (iff_and_self.2 fun H t ↦ let b := e.baseChange _
    let ⟨y, M, eV, H⟩ := (reindex_equiv (toLinAlgEquiv b).symm).2.1.1 H
    Eq.subst (by simpa [toLinAlgEquiv_apply, smul_tmul'] using
      congr(toLinAlgEquiv b $eV (1 ⊗ₜ t))) (sum_smul_mem _ _ fun _ _ ↦ subset_span
      (b.equivFun.injective <| (equivFun_tensorAction ..).trans congr(col $(H ·) _)))).1 (by
  choose M H _ U hU eU using by simpa using k.chart_isChartOf.exists_isPeriodMatrix 0 _ c e (J _)
  choose Q L Z _ _ hL hZ _ e' _ _ hG using hU.exists_frame
  choose V C hC eV _ using k.radius_lemma (hf _) (by simpa using
    (k.exists_smul_z 1).choose_spec) hZ e' (hG _ (hf _)) (p.le_pow_clog Fact.out _) 0
  exact let s m := (toRingHom _ _ m).mapMatrix
    let i := RingHom.mapMatrix _
    let q := (k.E.1 ^ h • Q).map α
    have E : i q = s m (U * Z) := Matrix.ext (by
      simp [*, i, s, q, @Algebra.smul_def _ BPlus]
      tauto)
    ⟨q * V.2, V * _, by simpa [q, mul_assoc, Matrix.map_smul', mul_pow, mul_smul] using
      congr(_ • ($hL).map α), fun g ↦ Matrix.map_injective injective_Amax_BPlus (by
      simpa [map_mul, ← (Matrix.ext fun _ _ ↦ smul_algebraMap_eq_algebraMap_smul (toGp g) (_ :
        Amax) : s _ (i _) = i (.map _ (toGp g • ·))), E, mul_assoc, ← map_mul i, show s (1, _) C =
        C from hC _ (hf g).1, s, m, comp_def, smul_smul, show s m Z =
        C * i V by simpa [← ext_iff, FrobGal.smul_def] using! eV] using! congr(s m
        ($((Matrix.map_injective injective_BPlus_Bcris (by simpa [← eU, comp_def] using! H g) :
      (repMatrix ρ e g).map (↑) * s (1, _) U = U))) * C) : i _ = i _)⟩)⟩


attribute [-simp] map_eq_zero

attribute [-instance] LieRinehartAlgebra.toIsScalarTower

variable {p} [ThePrime p] {G Δ κ I : Type} [Group G] [Group Δ] [OverGp Δ p] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] {ι : I → Type} [∀ η, Finite (ι η)] (w : Δ →* ℤ_[p][G])
  (σ : PadicRep G p) {R : PadicRep G p}

/-- For a matrix representation σ: G→GL_m(Q̄_p), the Z_p-algebra homomorphism from the group
ring Z_p[G] to m×m matrices over Q̄_p extending σ. -/
noncomputable abbrev groupRingHom := lift ℤ_[p] _ _ ((Units.coeHom _).comp σ.rep)

/-- For a multiplicative map w: Δ→Z_p[G] and a matrix representation σ of G over Q̄_p, the matrix
representation of Δ sending g to σ(w(g)), σ extended linearly. -/
noncomputable abbrev viaGroupRing := matrixRep ((groupRingHom σ).toMonoidHom.comp w).toHomUnits

variable (Δ) in
/-- For finitely many continuous representations τ_s of a compact group G over Q̄_p, there is a
finite free Z_p-algebra T, a quotient of Z_p[G], through which all τ_s factor by jointly
injective algebra maps. -/
lemma exists_finite_groupRing_quotient [Finite κ] {τ : κ → PadicRep G p} (hτ : ∀ s, Continuous
  (τ s).rep) : ∃ (T : AlgCat ℤ_[p]) (q : _ →ₐ[ℤ_[p]] T) (u : ∀ _, T →ₐ[ℤ_[p]] _), Free ℤ_[p] T ∧
  Module.Finite ℤ_[p] T ∧ (⇑q).Surjective ∧ (∀ s y, u s (q y) = groupRingHom (τ s) y) ∧ (∀ y,
  q y = 0 ↔ ∀ s, groupRingHom (τ s) y = 0) ∧ ∀ {h w}, (∀ s, IsCrystallineUpTo (Γ := Δ) h
  (viaGroupRing w (τ s))) → IsCrystallineUpTo h (actionRep ℤ_[p] T (q.toMonoidHom.comp w)) := by
  let Φ := AlgHom.pi (groupRingHom <| τ ·)
  choose O ν P h using (hτ · |> eventually_exists_isLatticeIn |>.exists)
  have := Finite.of_fg ((fg_pi fun s ↦ fg_range (mulLeftRight _ ((P s).1, (P s).2) ∘ₗ
    (O s).1.val.toLinearMap.mapMatrix)).of_le (S := Φ.range.toSubmodule) fun _ ⟨y, e⟩ s _ ↦
    ⟨y.lift _ _ _ (ν s), by simp [← e, Φ, lift_apply, Finsupp.sum, ← by simpa using h, mul_assoc]⟩)
  have := IsTorsionFree.trans_faithfulSMul ℤ_[p] (PadicAlgCl p)
  let u s := (Pi.evalAlgHom _ _ s).comp Φ.range.val
  let f (s : Σ s, (τ s).Index) := applyVec (u s.1).toLinearMap (Pi.single s.2 1)
  have I t (h : ∀ s, f s t = 0) : t = 0 := by ext s i l; simpa [f] using! congrFun (h ⟨s, l⟩) i
  refine ⟨.of .., _, u, inferInstance, ‹_›, Φ.rangeRestrict_surjective, ?_, ?_, fun C ↦
    ⟨.of_jointly_injective le_top (C ·.1 |>.1) _ ?_ I, fun γ _ h ↦ (exists_jump_of_linearIndependent
    (fun _ ↦ (C _).1.isPotCrys) _ (asSemilinear f) ?_ (linearIndependent_emb_coords f (finBasis ..)
    I) (ext_id _ γ _ ▸ h)).elim (C ·.1.1 |>.2 _ _)⟩⟩ <;> simp [f, u, Φ,
    asSemilinear, -mulVec_single, Subtype.ext_iff, funext_iff]

/-- Limits of crystalline representations. G compact, toGp : Δ → Gp p (from OverGp) of open image,
w: Δ → Z_p[G] multiplicative, R continuous with `IsTraceNondeg`; X finite families of continuous
representations, crystalline along w with jumps in [0, h]. If ‖tr R‖ ≤ ε on the kernel in Z_p[G] of
some family, for each ε > 0, then R∘w is crystalline.

Known result: Limits of crystalline representations with bounded weights are crystalline. -/
lemma isCrystalline_of_trace_limit {h} (hR : Continuous R.rep) (hn : IsTraceNondeg R.rep) {X : ∀ η,
  ι η → _} (hc : ∀ η x, IsCrystallineUpTo h (viaGroupRing w (X η x))) (hX : ∀ η x, Continuous (X η
  x).rep) (H : ∀ ε > 0, ∃ η, ∀ y, (∀ x, groupRingHom (X η x) y = 0) → ‖(groupRingHom R y).trace‖ ≤
  ε) : IsCrystalline (viaGroupRing w R) := by
  obtain ⟨⟨κ, hf, -⟩, ⟨T, q, u, _, _, hs, hu, hi, -⟩, _, e, h₀, E⟩ := exists_kummer_chart Δ,
    exists_finite_groupRing_quotient Δ
    fun _ : Unit ↦ hR, HasUniqueDiv.of_isTorsionFree.{0, 0} Amax, uniform_period_bound Δ h
  let A := Amax; let Λ := WittFq κ.f; let := Algebra.compHom A (ofId Λ Ainf).1
  let D {T : AlgCat ℤ_[p]} (q : _ →ₐ[ℤ_[p]] T) : Submodule Λ _ := ⟨⟨⟨fixedPeriods (actionRep ℤ_[p] T
    (q.toMonoidHom.comp w)) A ⊤, by simp +contextual [fixedPeriods]⟩, by tauto⟩,
    fun c _ h g ↦ by erw [← algebraMap_smul A, mem_ofPred, tensorAction_smul, h,
    smul_algebraMap_eq_algebraMap_smul (A := Ainf), (hf _).1]; rfl⟩
  have := (isMaximal_iff Λ).2 (irreducible p).maximalIdeal_eq.symm
  have hΛ {T : AlgCat _} [Free ℤ_[p] T] [Module.Finite ℤ_[p] T] q :
    (⇑(liftBaseChange A (@D T q).subtype)).Injective ∧ Free Λ (D q) ∧ Module.Finite Λ (D q) := ?_
  obtain ⟨⟨c⟩, F, -, ⟨⟩⟩ := Amax.nonempty_adicBasis Λ rfl, (finBasis ℤ_[p] T).equivFun, hΛ q
  -- traces define the `p`-adic topology on `T`, by compactness
  choose ε K x H using fun k ↦ (nhds_basis_closedBall.mem_iff.1 ((ContinuousMap.curry ⟨_, ((u () ∘ₗ
    F.symm.1).continuous_on_pi.fst'.mul (Units.continuous_val.comp hR.snd')).matrix_trace⟩
    ).2.isClosedMap.eventually_nhds_fiber 0 ((F.surjective.comp hs).forall.2 fun z n ↦
    (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_maximalIdeal_pow _ k).mem_nhds (by simp [(hi z).2
    fun _ ↦ hn _ (sum_mem (by simp [smul_of_tower_mem, mem_span_of_mem]) |> (lift_apply ..).substr)
    (by simpa [hu] using congr($n ·))])))).imp (H · |> ·.symm.imp_right)
  choose _ π _ _ _ S _ J Y using (exists_finite_groupRing_quotient Δ fun s : Σ l : Set.Iic ·,
    ι (x l.1) ↦ hX _ s.2)
  let Q := q.toLinearMap.baseChange A; let Q' k := (π k).toLinearMap.baseChange A
  choose n b y he using fun k ↦ mem_span_set'.1 ((span_preimage_eq (f := Q' k) (D _).nonempty fun _
    _ ↦ lTensor_surjective _ (S k) _).ge (x := e ⊗ₜ 1) ((E (finBasis ..) (Y k (hc _ ·.2))).1 _))
  have hker {k v} (h : Q' k v = 0) : Q v ∈ nsmulRange (p ^ k) _ ∧ ∀ i ≤ k, Q' i v = 0 := by
    obtain ⟨v, rfl⟩ := (lTensor_exact _ (exact_subtype_ker_map _) (S k) _).1 h
    exact v.inductionOn (fun a ⟨z, m⟩ ↦ have := by simpa [J, Sigma.forall] using m
      ⟨nsmulRange.map_mem (TensorProduct.mk _ _ _ a) ((Basis.ofEquivFun F).sum_equivFun (q z) ▸
        mem_span_pow_smul_top_iff.1 (sum_mem
        fun i _ ↦ smul_mem_smul (@maximalIdeal_eq_span_p p _ ▸ K k (by simpa [hu,
        norm_le_of_nonempty, this] using (H k <| z * .single · 1)) _ rfl i ⟨⟩) ⟨⟩)), fun l e ↦ by
        simp [Q', (J l z).2 fun s ↦ this _ (s.1.2.trans e) _]⟩) (by simp +contextual [add_mem])
  have hP {k v} : Q' k v ∈ D (π k) ↔ _ := forall_congr' fun g ↦ (tensorAction_periodTensorMap
    (g := mulLeft ℤ_[p] (w g)) (by simp) ..).congr_left.trans sub_mem_ker_iff.symm
  have P {M i j} := @isAdicComplete_of_free A M _ i j (.span {↑p}) _
  simp_rw [isAdicComplete_iff, isHausdorff_iff, isPrecomplete_iff, SModEq.sub_mem,
    mem_span_pow_smul_top_iff] at P
  choose z hz using fun s ↦ P.2 (fun k ↦ Q (∑ i, c.coord s (b k i) • y k i)) @fun k m e ↦
    let v m e := ∑ i, b m i ⊗ₜ[Λ] (⟨_, hP.2 (hP.1 (y m i).2 · |> hker |>.2 k e)⟩ : D _)
    Q.map_sub .. ▸ (hker (by simpa [v] using congr((lift (lsmul .. ∘ₗ c.coord s)
      $(@(hΛ _).1 (v _ .refl) (v _ e) (by simpa [v, ← he m] using congr(Q' k $(he k))))).1))).1
  lift z to c.Index → D q using fun s g ↦ (eqLocus_eq_ker_sub _ id).ge (P.1 _ fun k ↦ by
    erw [sub_zero, ← sub_sub_cancel (Q _) (z s), map_sub, LinearMap.sub_apply,
      tensorAction_periodTensorMap (R := ℤ_[p]), ← map_sub]
    exact sub_mem (hker (hP.1 (by simp [sum_mem,
      smul_mem _ _ (y ..).2]) g)).1 (nsmulRange.map_mem _ (hz ..))
    simp)
  choose G N using fun k ↦ Filter.eventually_atTop.1 (.all (b k · |> c.eventually_sub_sum_mem <| k))
  let W := partialSups G
  have ⟨ω, hω⟩ := P.2 (∑ s ∈ W ·, c.b s ⊗ₜ[Λ] z s) @fun k _ e ↦ sub_mem_comm_iff.1
    ((sum_sdiff_eq_sub (W.mono e)).subst (sum_mem fun s h ↦ nsmulRange.map_mem (TensorProduct.mk Λ A
    _ _) ((sub_sub_cancel _ (z s).1 ▸ sub_mem (nsmulRange.map_mem _ (sum_mem fun i _ ↦
    mem_span_pow_smul_top_iff.1 (smul_mem_smul (by
    simpa [Finsupp.single_apply, mem_sdiff.1 h] using c.coord_sub_mem_pow (f := (W k).sum (.single
      · _)) (by simpa using N k _ (le_partialSups ..) i) s) ⟨⟩))) (hz ..)).rec fun v e ↦ ⟨⟨v, (by
    simpa [← e, ne, -nsmul_eq_mul] using (z s).2 ·)⟩, Subtype.ext e⟩)))
  refine isAdmissible_of_one_tmul_mem_span fun v ↦
    (smul_mem_iff_of_isUnit _ h₀).1 (span_subset_span A _ _ ?_)
  simpa [Q, periodTensorMap, Algebra.smul_def] using mapsTo_span (f := periodTensorMap A Bcris
    (applyVec (u ()) v)) (forall_mem_range.2 (fixedPeriods.map (by simp [hu]) ·.2))
    ((range_liftBaseChange A (D _).subtype).le (x := Q (e ⊗ₜ 1)) ⟨ω, sub_eq_zero.1 (P.1 _ fun k ↦ by
    simpa [← he k, sub_smul, sum_smul, smul_sum, smul_sub, univ.sum_comm, smul_comm (c.b _)]
      using sub_mem (sub_mem (sum_mem (t := W k) fun s _ ↦ nsmulRange.map_mem (lsmul _ _ (-c.b s))
      (hz s k)) (nsmulRange.map_mem (liftBaseChange A (D _).subtype) (hω k))) (sum_mem (t := ⊤)
      fun i _ ↦ nsmulRange.map_mem (toSpanSingleton _ _ (Q (y k i))) (mem_span_pow_smul_top_iff.1 (N
      k (W k) (le_partialSups ..) i))))⟩)
  -- the fixed periods are finite over the fixed coefficients and stay independent over `A`
  have L {n : Type} [Fintype n] {y : n → D q} (h : LinearIndependent Λ y) : LinearIndependent _ (y ·
    |>.1) := .of_comp (periodTensorMap A Bcris .id) (.restrict_scalars (by
    simpa [Algebra.smul_def] using! injective_BPlus_Bcris.comp injective_Amax_BPlus) (ker_eq_bot.1
    (bot_unique (le_of_fixed_mem_of_saturated le_top (by simp +contextual) (fun w e g ↦ by erw
    [mem_ker, ← eventually_tensorAction_eq (fixedPeriods.map (by tauto) <| y · |>.2) w g, e,
    map_zero]) fun a e f ↦ by
    choose m w (hw : ∀ t, _ = algebraMap _ _ (algebraMap Λ A _)) using by
      simpa using fun t ↦
        exists_witt_coeff_of_isChartOf κ.chart_isChartOf (ne 1) (by simpa using congr($(f ·) t))
    simpa [a.ext_iff, (of_faithfulSMul ℚ_[p] ..).1, by simpa [Λ, p_nonzero] using (
      linearIndependent_iff'.1 h ⊤ ((sup ⊤ m - m · |> p.pow) • w) (Subtype.ext
      (periodTensorMap_injective (by simpa [← @algebraMap_smul A _ Bcris, ← algebraMap_smul A, ← hw,
      le_sup, smul_sum, smul_smul, ← pow_add, ← mul_assoc, a.sum_fintype,
      Finsupp.linearCombination] using congr(p ^ sup ⊤ m • $e)))))] using hw))))
  cases free_finite_of_rank_le span_insert_zero.symm (isHausdorff_of_injective_pi (.span {↑p})
    (.restrictScalars Λ (finBasis A _).equivFun.1 ∘ₗ (D q).subtype)) (by simp [ne,
    Nat.cast_smul_eq_nsmul Λ]) _ (rank_le fun _ h ↦ by simpa using (L h).fintype_card_le_finrank)
  use injective_of_linearIndependent ((finBasis ..).baseChange A).span_eq
    (by convert! L (finBasis ..).linearIndependent; simp)
