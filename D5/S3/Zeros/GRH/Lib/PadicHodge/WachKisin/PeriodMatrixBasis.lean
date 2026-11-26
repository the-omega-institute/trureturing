/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/PeriodMatrixBasis
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/PeriodMatrixBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.WachKisin.PeriodMatrixBasis. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/WachKisin/PeriodMatrixBasis.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin.ChartScalars
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Kisin lattice (Breuil–Kisin module) of a crystalline lattice (known result; see
Lib.PadicHodge.WachKisin.PeriodMatrixFrame).

This file: Kisin lattice of a period matrix is free and dense up to p-powers. -/

attribute [-instance] Subalgebra.moduleLeft

namespace Lift

open Ainf BPlus Fintype RingHom Function Algebra Matrix Amax Fact Ideal
variable {p} [ThePrime p] {d : Type} (c : Chart) [Fintype d] (U : Matrix d d BPlus) (h : ℕ) (v :
  Ainfˣ)

@[simp] lemma tau_ne_zero : tau ≠ 0 := ne_zero_of_map theta_tau_ne_zero

/-- Lifting the exponent. Let f: A_inf → R be a surjective ring map, v a non-unit dividing x −
1, with p·f(x − 1)·f(v) dividing f(x − 1)^p. For n ≠ 0, f(x^n − 1) divides p^{v_p(n)} f(x −
1). -/
lemma lifting_the_exponent {R} [CommRing R] {f : Ainf →+* R} (hf : Surjective f) x v {n}
    (hv : ¬IsUnit v) (h : v ∣ x - 1) (H : p * f (x - 1) * f v ∣ f (x - 1) ^ p) (hn : n ≠ 0) :
    f (x ^ n - 1) ∣ p ^ padicValNat p n * f (x - 1) := by
  set s := ∑ i ∈ .range (n.divMaxPow p), x ^ i
  have ⟨y, H⟩ := hf.exists.1 (ZMod.exists_one_add_mul_pow_prime_pow_eq out
    (by gcongr) H (f s) (padicValNat p n))
  have := (@isUnit_of_dvd_sub _ _ _ (s + v * y) (n.divMaxPow p) (isAdicComplete_span_singleton hv)
    (by simp [Ainf.isUnit_iff_isUnit_constantCoeff, CharP.isUnit_natCast_iff out,
    p.not_dvd_divMaxPow out hn]) (by simp_all [s, ← Quotient.eq_zero_iff_dvd])).map f
  simp_all [s, mul_geom_sum, ← pow_mul]

namespace Chart

lemma associated_E_mul_tau_mu : Associated (c.E * tau) mu :=
  xi_mul_tau ▸ c.associated_E_xi.mul_right _

lemma associated_smul_E g : Associated c.E.1 ((g : Gp p) • c.E) := (associated_smul_of_dvd g
  (by simp [c.associated_E_xi.dvd_iff_dvd_left, ← theta_eq_zero_iff_xi_dvd, theta_E])).symm

lemma exists_tau_mul_E_eq_mul_epsTilt_pow_sub {n} (hn : n ≠ 0) : ∃ α β, tau * c.E * (p ^ padicValNat
  p n + β * c.z) = α * (.teichmuller p epsTilt ^ n - 1) := match c.associated_E_mul_tau_mu.dvd',
  c.xi_mem_span_p_z with | ⟨v, _⟩, ⟨u, s, _⟩ => (lifting_the_exponent
  (Quotient.mkₐ_surjective ℤ (span {-c.z * mu})) _ _ (·.map _ |>.ne_zero toWittResidue_tau)
  (Dvd.intro_left _ xi_mul_tau) (.trans ⟨u, mk_span_eq_iff_dvd_sub.2
  ⟨-tau * s, by grind [mu, xi_mul_tau]⟩⟩ (pow_dvd_pow _ (out : 1 < p))) hn).rec (Quot.ind fun α ↦
  (⟨α * v, ·.imp (by grind [mu])⟩) ∘ mk_span_eq_iff_dvd_sub.1)

/-- U over B^+ is a period matrix: UW = (Eτ)^h for some W; φU = vUF, F over S_B invertible over
B^+; each g fixing Λ and θ(z) has ρ over A_inf with ρ·gU = U; E^h ∣ Uy implies E^h ∣ U·f̂(y)
(`Lift.Chart.extendToBPlus`). -/
structure IsPeriodMatrix where
  exists_inv : ∃ W, U * W = (c.E * tau) ^ h • 1
  exists_frob : ∃ F F', (∀ i j, F i j ∈ c.bicommutant) ∧ F' * F = 1 ∧ U.map frobEnd = v • (U * F)
  exists_gal g : c.FixesThetaZ g → ∃ ρ, .map ρ ainfToBPlus * g • U = U
  hat_stable f y : (∃ w, U *ᵥ y = c.E.1 ^ h • w) → ∃ w, U *ᵥ c.extendToBPlus f ∘ y = c.E.1 ^ h • w

lemma E_ne_zero : c.E.1 ≠ 0 := (c.associated_E_xi.symm.prime prime_xi).1

attribute [local simp] mul_assoc mul_pow funext_iff pow_add mulVec_sum smul_sub
attribute [local simp↓] mulVec_smul E_ne_zero dotProduct_smul extendToBPlus_ainfToBPlus
  extendToBPlus_mul mulVec_sub Units.smul_def

lemma exists_p_pow_mul_mem_amaxImage {e} (he : e ∣ mu) : ∃ k, ∀ {y w}, U *ᵥ y = e ^ h • w →
  (∀ i, y i ∈ amaxImage) → ∀ i, p ^ k * w i ∈ amaxImage :=
  (IsLocalization.exist_integer_multiples_of_finite (.powers (p : Amax)) U.uncurry).rec fun ⟨_, k,
  rfl⟩ hk ↦ ⟨_ + k, fun e hy i ↦ by simpa using amaxImage.p_pow_mul_mem_of_dvd_mu he (by
    erw [← mul_smul_comm, ← Pi.smul_apply, ← e, Finset.mul_sum]
    simpa [smul_def] using! sum_mem fun j _ ↦ mul_mem (hk (i, j)) (hy j))⟩

variable {c U h v} (hU : c.IsPeriodMatrix U h v)
include hU

namespace IsPeriodMatrix

lemma mulVec_injective : Injective U.mulVec := mulVec_injective_of_det_ne_zero (by
  simpa [·, @smul_def _ BPlus] using congr($(hU.1.choose_spec).det).symm)

/-- For a period matrix U there are Q over A_inf with det Q ≠ 0 and Z over S_B with UZ = E^h Q,
such that Uy = E^h x, y over S_B, gives x in QS^d, and for any y over B^+, δ ∣ lQ and p ∤ δ
give δ ∣ l·x. -/
lemma exists_basis : ∃ Q Z, Q.det ≠ 0 ∧ (∀ i j, Z i j ∈ c.bicommutant) ∧ U * Z =
  c.E.1 ^ h • Q.map ainfToBPlus ∧ (∀ x y, (∀ i, y i ∈ c.bicommutant) → U *ᵥ y =
  c.E.1 ^ h • ainfToBPlus ∘ x → ∃ s : d → c.S, Q *ᵥ (↑) ∘ s = x) ∧
  ∀ x y, U *ᵥ y = c.E.1 ^ h • ainfToBPlus ∘ x → ∀ δ l g, ¬↑p ∣ δ → l ᵥ* Q = δ • g → δ ∣ l ⬝ᵥ x := by
  obtain ⟨⟨⟨W, e'⟩, ⟨F, F', _, o, eF⟩, -, R⟩, K, μ, u, hu, eu⟩ :=
    hU, hU.mulVec_injective, c.associated_E_mul_tau_mu.dvd, c.exists_bicommutant_mul_p_eq_one
  obtain ⟨⟨n, hn⟩, ⟨k, hk⟩, ⟨ε, hε⟩, J, ψ, Ψ⟩ := exists_p_pow_mul_mem_amaxImage W h μ,
    exists_p_pow_mul_mem_amaxImage U h
    (dvd_of_mul_right_dvd μ), c.associated_E_xi.dvd, frobEnd_bijective.imp_right Classical.skolem.1
  simp [ext_iff_mulVec, ← mulVec_mulVec, -funext_iff, -mul_pow] at e'
  let g := c.E.1 ^ h • (Algebra.linearMap Ainf BPlus).compLeft d
  have V := @exists_Ainf_eq_of_contraction p _ {a | ∃ x y w f i, U *ᵥ y = g x ∧
    U *ᵥ c.extendToBPlus f ∘ y = c.E.1 ^ h • w ∧ p ^ k * (p ^ n • w) i = a} h (ε ^ h * v⁻¹) ?_ ?_
  any_goals rintro _ ⟨x, y, w, f, i, hy, hw, rfl⟩
  let P := (mulVecBilin ℕ _ U ∘ₗ c.bicommutant.val.toLinearMap.compLeft d).range.comap
    (g.restrictScalars _)
  choose y (ey : ∀ j, U *ᵥ (↑) ∘ y j = _) using P.coe_mem
  have ⟨⟨_, b⟩, _⟩ := free_finite_of_rank_le rfl (isHausdorff_of_injective_pi c.maxIdeal P.subtype)
    (fun ⟨x, y, k⟩ _ e ↦ (pi_dvd_iff.2 (prime_p.2.2 _ _ ⟨_, congr($e.1 ·)⟩ |>.resolve_left
    c.not_p_dvd_z)).rec (by rintro w rfl; exists ⟨w, (⟨_, hu⟩ * y ·), by
      simpa [g, ← mul_assoc, eu, ← mulVec_smul] using! congr(u • $k)⟩)) (card d) ?L
  choose q hq using (Cardinal.mk_fintype d ▸ b.mk_eq_rank''.trans_le
    ?L).some.2.surjective_comp_right b
  let N := h.succ + k + n
  refine ⟨_ᵀ, _, mt exists_vecMul_eq_zero_iff.2 fun ⟨l, o, _⟩ ↦ o (dotProduct_eq_zero _ fun x ↦ by
    simpa using c.eq_zero_of_z_pow_dvd (map_pow ainfToBPlus _ · ▸ map_dvd ainfToBPlus
      (?Y (tau ^ h • x) (W *ᵥ ainfToBPlus ∘ x) (by simp [e', smul_def]) _ l 0 (c.not_p_dvd_z ∘
      prime_p.dvd_of_dvd_pow) (by simp [*])) :)), by simp, ext_col (ey <| q ·), ?X, ?Y⟩
  exact fun x y o k ↦ ((Submodule.mem_span_range_iff_exists_fun _).1 (Submodule.span_mono
    (Set.range_comp_subset_range ..) (hq ▸ b.mem_span ⟨x, (⟨_, o ·⟩), k⟩))).imp
    (by simp [mulVec_eq_sum, Subtype.ext_iff]; tauto)
  refine fun x y e δ l g o a ↦ N.rec (by simp) (fun _ ↦ (Or.rec o.elim · ∘
    prime_p.left_dvd_or_dvd_right_of_dvd_mul ∘ by simp [pow_succ'])) (dvd_of_approx
    (y := l ⬝ᵥ p ^ N • x) prime_p.2.1 prime_xi.2.1 o fun m ↦ ?_)
  choose _ r using (R · _ ⟨_, e⟩)
  choose z _ using (V _ ⟨_, _, _, ·, ·, e, r _, rfl⟩)
  choose s hs using fun f ↦ (?X (z f) (p ^ N • c.extendToBPlus f ∘ y) · (by simp [*, N]))
  choose G w hw ew using (Filter.eventually_all.2 (y · |> c.eventually_approx_sum_extendedCoord <|
    m + k)).exists
  use g ⬝ᵥ ∑ l ∈ G, c.adicBasis.b l • (↑) ∘ s _ fun _ ↦
    nsmul_mem (c.extendedCoord_mem_bicommutant l _) _
  rw [← smul_eq_mul, ← smul_dotProduct, ← a, ← dotProduct_mulVec, ← dotProduct_sub]
  refine Submodule.sum_smul_mem _ _ fun i _ ↦ mem_span_pow_of_p_pow_dvd ((@hk (p ^ N • u ^ (m + k) •
    (y - ∑ l ∈ G, c.adicBasis.b l • c.extendedCoord l ∘ y)) (u ^ (m + k) • ainfToBPlus ∘ _) ?_
    (fun j ↦ nsmul_mem (by simp [*, ← mul_assoc, ← mul_pow, -pow_add]) _) i).imp fun z e ↦
    injective_Amax_BPlus (by simpa [← pow_add, -Pi.sub_apply, ← mul_assoc, ← mul_pow, eu,
    (mul_comm _ u)] using! congr(p ^ m * $e).symm))
  simp [*, N, G.mul_sum, G.smul_sum, smul_comm (_ ^ h), ← smul_def]
  exact rank_le fun b li ↦ have I {a : b → Ainf} : ∑ j, a j • (·.1) ∘ y j = 0 ↔ ∑ j, a j • j.1.1
    = 0 := (K.eq_iff.iff (g.map_eq_zero_iff fun _ _ ↦ by simp [g, smul_def])).1 (by simp [*])
    by simpa using (linearIndependent_iff.2 fun a ↦ (fun e j ↦ c.adicBasis.eq_zero_of_coord fun i ↦
      linearIndependent_iff.1 li _ (Subtype.ext (by simpa using! I.1 (by
      simpa [smul_def, mul_comm] using congr(c.extendedCoord i ∘ $e)))) j) ∘ I.2).cardinal_le_rank
  apply hk (by rw [smul_comm, ← hw, ← mulVec_smul]) (by simpa [map_p_pow_mul] using
    (c.extendToBPlus_mem_amaxImage f _ <| hn (K (by rw [e', mulVec_smul])) (by aesop) ·))
  have H {r w} (e : U *ᵥ w = r • ainfToBPlus ∘ ψ ∘ (v • c.E.1 ^ h • x)) : F *ᵥ _ =
    frobEnd (ainfToBPlus r) • y := K (by
    simpa [@smul_def _ BPlus, *, g, -e, map_mulVec, mul_left_comm] using congr(frobEnd ∘ $e))
  choose y' ha using (pow_dvd_of_map (map_mul frobEnd _) (by simp [↓mu_ne_zero]) (fun _ ⟨_, _⟩ ↦
    dvd_of_thetaBPlus_frobEnd_eq_zero _ tau_dvd_of_theta_frobEnd (by simp [*]))
    ⟨_, by simpa [o, mul_left_comm] using congr((F' *ᵥ $(H (e' _))) ·)⟩)
  refine match R ⟨⟨ψ ∘ f ∘ frobEnd, by simp [← J.eq_iff, *]⟩, fun s _ ↦ J (by
    simpa [smul_def, Ψ] using! f.2 (c.φ s) _)⟩ y' ⟨_, ?Z⟩, H ?Z with | ⟨w', hw'⟩, Y => ⟨_,
    ⟨_, _, _, _, i, ?Z, hw', rfl⟩, (?_ : _ → _) congr(frobEnd ($hw' i))⟩
  simpa [e', smul_def, mul_left_comm] using congr(U *ᵥ $((funext ha : _ = (_ : BPlus) • y'))).symm
  erw [map_mulVec, comp_def, funext fun _ ↦ show frobEnd _ = c.extendToBPlus f (frobEnd _) from
    sub_eq_zero.1 (eq_zero_of_ainfToBPlus (.mk' (_ ∘ _ - _ ∘ _) (by simp [sub_add_sub_comm])) (fun _
    _ ↦ by apply_rules [sub_mem, extendToBPlus_mem_amaxImage, smul_mem_amaxImage]) (by simp [*])),
    eF, smul_mulVec, ← mulVec_mulVec, show F *ᵥ _ = (_ : BPlus) • c.extendToBPlus f ∘ y by
    simpa [mulVec, dotProduct, *, -Y, pow_mem (c.frobEnd_mem_bicommutant _), -frobEnd_algebraMap]
      using congr(c.extendToBPlus f ∘ $Y)]
  exact (by simp [← by simpa [smul_def _ (w' _), map_eq_zero_iff _ J, hw,
    ← Algebra.mul_smul_comm] using ·, smul_smul, hε, mul_comm _ ε])
