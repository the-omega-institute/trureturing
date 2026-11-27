/- GID: D5/S3/Zeros/GRH/Lib/ClassField/HeckeL/EulerProduct
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/HeckeL/EulerProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.HeckeL.EulerProduct. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/HeckeL/EulerProduct.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.GaloisCohomology.CyclicClass
import D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline.NonUnitalUnits
import D5.S3.Zeros.GRH.Lib.Adelic.Adeles.AdeleIdempotent
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Hecke L-functions: Euler product, continuation to s = 1, non-vanishing, prime densities
(known result; see Lib.ClassField.HeckeL.HeckeContinuation).

Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes (known
result; see Lib.ClassField.Places.LocalFrobenius).

This file: Finite ideles: principal, local, S-ideles, openness, compactness, almost-everywhere
unramified characters. Euler products over primes of a number field, Dirichlet density, Dirichlet
series identity. -/

noncomputable section

open IsDedekindDomain Set Units FiniteAdeleRing
variable {K} [Field K] [NumberField K]

/-- The diagonal homomorphism from K^× to the finite ideles of K. -/
abbrev principalIdele := map (algebraMap K (𝔸f K)).1

variable (S : Set (FinPlace K)) (a : (𝔸f K)ˣ) (v : FinPlace K)

/-- The homomorphism sending x ∈ K_v^× to the finite idele with component x at v and 1
elsewhere. -/
def locIdele : (LocField v)ˣ →* (𝔸f K)ˣ := unitsMapNonUnital (singleAdele v)

/-- The homomorphism from the finite ideles of K to the units of `𝔸` K sending a to (1, a),
with component 1 at every infinite place. -/
abbrev finIdeleIncl : (𝔸f K)ˣ →* (𝔸 K)ˣ := map (.inr ..)

/-- For a finite place v of K, the homomorphism from K_v^× to the ideles of K placing x at v and
1 at all other places, finite and infinite. -/
def locFullIdele := finIdeleIncl.comp (unitsMapNonUnital (singleAdele v))

/-- The homomorphism sending a finite idele to its component in K_v^×. -/
def ideleAt := map (evalAt v).1

/-- The group of finite ideles of K whose components at all places outside S are units. -/
def idelesUnitOff := ⨅ v ∉ S, ((map Valued.v.toMonoidHom).comp (ideleAt v)).ker

@[simp] lemma locIdele_same x : (locIdele v x).1 v = x := by simp [locIdele]

@[simp] lemma ideleAt_locIdele x : ideleAt v (locIdele v x) = x := ext (locIdele_same ..)

@[fun_prop] lemma continuous_ideleAt : Continuous (ideleAt v) := (continuous_evalAt v).units_map

lemma finite_idele_val_ne_one : {v | Valued.v (a.1 v) ≠ 1}.Finite :=
  unitsEquiv_finite_valued_eq_one _

lemma coe_idelesUnitOff_empty : idelesUnitOff ∅ = (Ô K).units := by ext; simp [idelesUnitOff, mem_Ô,
                    forall_and, (Ô K).mem_units_iff, ← mabs_le_one, mabs_le', ← map_inv]; rfl

lemma isOpen_idelesUnitOff : (idelesUnitOff S).IsOpen := Subgroup.isOpen_mono
  (coe_idelesUnitOff_empty.ge.trans (biInf_mono nofun)) ((Ô K).isOpen_units isOpen_Ô)

variable {S a v w}

@[simp] lemma locIdele_of_ne (h : w ≠ v) x : (locIdele v x).1 w = 1 := by simp_all [locIdele]

@[simp] lemma ideleAt_locIdele_of_ne (h : w ≠ v) x : ideleAt w (locIdele v x) = 1 :=
  ext (locIdele_of_ne h x)

@[simp] lemma mem_idelesUnitOff : a ∈ idelesUnitOff S ↔ ∀ v ∉ S, Valued.v (a.1 v) = 1 := by
  simp [idelesUnitOff, ← val_inj, ideleAt]

lemma idelesUnitOff_mono {T} : S ⊆ T → idelesUnitOff S ≤ idelesUnitOff T := biInf_mono ∘ by tauto

lemma isCompact_idelesUnitOff_empty : IsCompact (SetLike.coe (@idelesUnitOff K _ _ ∅)) :=
  coe_idelesUnitOff_empty.substr ((Ô K).units_isCompact isCompact_Ô)

lemma principalIdele_mem_idelesUnitOff {x} : principalIdele x ∈ idelesUnitOff S ↔
  x ∈ S.unit K := by aesop

lemma exists_finset_cover_mulSupport_ideleAt {U} (h : IsOpen U) (e : 1 ∈ U) : ∃ T :
  Finset (FinPlace K), (idelesUnitOff ∅).carrier \ U ⊆ ⋃ v ∈ T, (ideleAt v).ker.carrierᶜ :=
  (isCompact_idelesUnitOff_empty.diff h).elim_finite_subcover _
  (continuous_ideleAt · |>.isOpen_mulSupport) fun a b ↦ by
  simpa [ideleAt, ← val_inj, DFunLike.ext_iff] using (by grind : a ≠ 1)

/-- A closed subgroup H of the finite ideles contains a as soon as it contains, for every place
v, the idele with component a_v at v and 1 elsewhere. -/
lemma mem_of_locIdele_mem {H : Subgroup _} (h : IsClosed H.carrier) (ha : ∀ v,
  locIdele v (ideleAt v a) ∈ H) : a ∈ H := by_contra fun _ ↦
  (exists_finset_cover_mulSupport_ideleAt (isOpenMap_mul_left a⁻¹ _ h.1) (by simpa)).rec fun T ↦
  not_subset.2 ⟨a⁻¹ * ∏ v ∈ T ∪ (finite_idele_val_ne_one a).toFinset, locIdele v (ideleAt v a), by
  aesop (add simp [idelesUnitOff, prod_mem,
    (Finset.prod_eq_ite _ fun _ _ ↦ (ideleAt_locIdele_of_ne ·.symm _))])⟩

lemma locIdele_mem_idelesUnitOff {x} (h : Valued.v x.1 = 1) {S} :
  locIdele v x ∈ idelesUnitOff S := by simp_all [← and_forall_ne v]

/-- Property of an element x of a field K: φ(x) > 0 for every ring homomorphism φ: K → ℝ. -/
def IsTotallyPositive x := ∀ φ : K →+* ℝ, 0 < φ x

/-- A homomorphism ψ with open kernel from the finite ideles of K to a commutative group is
trivial on the local units at all but finitely many finite places. -/
lemma eventually_unramified {C} [CommGroup C] (ψ : (𝔸f K)ˣ →* C) (h : ψ.ker.IsOpen) :
    ∀ᶠ v in .cofinite, ∀ x, Valued.v x.1 = 1 → ψ (locIdele v x) = 1 :=
  (exists_finset_cover_mulSupport_ideleAt h ψ.map_one).rec (·.finite_toSet.subset ∘ by
  simp [subset_def, -mem_idelesUnitOff]; grind [locIdele_mem_idelesUnitOff, ideleAt_locIdele_of_ne])

open NumberField IsDedekindDomain.HeightOneSpectrum Filter Topology Complex Finset Ideal Module
  ContinuousAt
variable {K : _} [Field K] [NumberField K] (ψ : (𝔸f K)ˣ →* ℂˣ) (n : _ → ℤ) (a b :
  FinPlace K → ℂ) {s : ℝ}

/-- The character ψ of the finite ideles is the finite part of a Hecke character of type n: its
kernel is open and ψ(x) ∏_w (Φ_w(x)/|Φ_w(x)|)^{n_w} = 1 on K^×. -/
def IsHeckeOfType [PlaceEmbedding K] := ψ.ker.IsOpen ∧ ∀ x, ψ (principalIdele x) * ∏ w,
  (Φ w x.1 / ‖Φ w x‖) ^ n w = 1

/-- The condition that the finite idele character ψ is trivial on the local units at the finite
place v. -/
def CharUnramifiedAt v := ∀ u, Valued.v u.1 = 1 → ψ (locIdele v u) = 1

/-- The function on finite places sending v outside S to the value of ψ at the local idele of
the chosen uniformiser at v, and v in S to 0. -/
def heckeCoeff S := indicator Sᶜ fun v ↦ (ψ (locIdele v (uniformizer v))).1

/-- The Euler product exp(−∑_v log(1 − a_v q_v^{−s})) over the primes of K, a function of real s
> 1, extended to s = 1 by the limit from the right. -/
def eulerProd := extendFrom (.Ioi 1) fun s : ℝ ↦ (-∑' v, (1 + -(a v * v.q ^ (-s : ℂ))).log).exp

/-- The family a has density l over primes of degree one: ∑ a_v q_v^{−s}, over v of prime norm,
converges and equals −l log(s − 1) + O(1) as s ↓ 1. -/
def HasPrimeDensity l := ∃ x, x =O[𝓝[>] 1] (1 : ℝ → ℝ) ∧ ∀ᶠ s : ℝ in 𝓝[>] 1,
  HasSum (fun v ↦ ite v.q.Prime (a v) 0 * v.q ^ (-s : ℂ)) (x s - l * (s - 1).log)

attribute [local simp] Nat.minFac_pos slitPlane_ne_zero dedekindZeta_residue_ne_zero
  LSeries.term_of_ne_zero' ne_zero_of_one_lt_re Real.rpow_neg cpow_neg

/-- For any finite set u of primes of K, the sum over v ∈ u of p_v⁻², with p_v the least prime
factor of q_v, is at most [K : ℚ]. -/
lemma sum_inv_minFac_sq_le_finrank (u : Finset (FinPlace K)) : ∑ v ∈ u, (v.q.minFac ^ 2 : ℝ)⁻¹ ≤
  finrank ℚ K := by
  have c {p : Ideal ℤ} [p.IsMaximal] (h : p ≠ ⊥) :
      #(IsDedekindDomain.primesOverFinset p (𝓞 K)) ≤ finrank ℚ K := by
    rw [← RingOfIntegers.rank, ← sum_ramification_inertia_eq_finrank p, ← Set.ncard_coe_finset,
      IsDedekindDomain.coe_primesOverFinset h, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
      Fintype.card_eq_sum_ones]
    exact sum_le_sum fun q _ ↦ mul_pos (ramificationIdx_pos ..) (inertiaDeg_pos ..)
  grw [sum_comp fun n ↦ (_ ^ 2)⁻¹, sum_le_sum fun n h ↦ nsmul_le_nsmul_left _ ((mem_image.1 h).rec
    fun v e ↦ by grw [card_le_card_of_injOn _ (fun w _ ↦ (IsDedekindDomain.coe_primesOverFinset
    (v.under ℤ).3 _).ge ⟨w.2, ⟨Ideal.ext (by
    simp_all [Int.cast_mem_ideal_iff, ← fun v : FinPlace K ↦ (v.1.under
    ℤ).absNorm_pow_inertiaDeg v.1, (Nat.absNorm_under_prime _).pow_minFac (inertiaDeg_pos ..).ne'])
    ⟩⟩) asIdeal_injective.injOn, c (ne_bot _)]), ← smul_sum,
    image_subset_iff.2 fun v h ↦ mem_Ioo.2 ⟨(Nat.minFac_prime v.one_lt_q.ne').one_lt,
    le_sup (f := (·.q.minFac + 1)) h⟩, sum_Ioo_inv_sq_le] <;> bound

variable {a b} (ha : ∀ v, ‖a v‖ ≤ 1) {l l'}

lemma summable_absNorm_rpow (hs : 1 < s) : Summable (absNorm · ^ (-s) : Ideal (𝓞 K) → ℝ) :=
    (((tendsto_sub_one_mul_dedekindZeta_nhdsGT K).eventually_ne (by simp)).and
    (Ioc_mem_nhdsGT hs)).exists.elim fun t ⟨h, _, k⟩ ↦ ((summable_partition (fun _ ↦ by positivity)
    (by simp)).2 ⟨(finite_setOfPred_absNorm_eq · |>.summable _), (@LSeriesSummable.of_re_le_re _ t s
    k ((right_ne_zero_of_mul h).imp_symm tsum_eq_zero_of_not_summable)).norm.congr fun _ ↦ by
    rw [tsum_congr (by rw [·.2])]; aesop⟩ : _)

include ha

lemma log_euler_factor_bounds {σ} (hσ : 1 ≤ σ) (hs : σ ≤
  s) v : let w := -(a v * v.q ^ (-s : ℂ)); ‖log (1 + w) - ite v.q.Prime w 0‖ ≤ 2 /
    v.q.minFac ^ 2 ∧ 1 + w ∈ slitPlane ∧ ‖log (1 + w)‖ ≤ 2 * v.q ^ (-σ) := by
  intro w
  have H {t} (h : t ≤ s) : ‖w‖ ≤ v.q ^ (-t) := by simp [w]; grw [ha, h] <;> bound
  have g := by simpa using H (hσ.trans hs)
  have h := g.trans (inv_anti₀ two_pos (mod_cast v.one_lt_q))
  refine ⟨?_, by grind [mem_slitPlane_of_norm_lt_one, norm_log_one_add_half_le_self, norm_nonneg]⟩
  split <;> [grw [norm_log_one_add_sub_self_le, g, h]; grw [sub_zero, norm_log_one_add_half_le_self,
    g, ← v.q.minFac_sq_le_self]] <;> simp [field, *] <;> bound

/-- If |a_v| ≤ 1 and s > 1, the series ∑_v log(1 − a_v q_v^{−s}) converges, its sum is
continuous at s, and `eulerProd` at s is the exponential of minus this sum. -/
@[local simp] lemma eulerProd_eq_exp (hs : 1 <
  s) : let l (s : ℝ) v := log (1 + -(a v * v.q ^ (-s : ℂ)))
  eulerProd a s = exp (-∑' v, l s v) ∧ Summable (l s) ∧ ContinuousAt (-∑' v, l · v) s := by
  have ⟨σ, h, h'⟩ := exists_between hs
  choose _ A B using (log_euler_factor_bounds (s := ·) ha h.le)
  refine (fun C ↦ ⟨extendFrom_eq (subset_closure hs) (tendsto_inf_left C.cexp), .of_norm_bounded ?S
    (B s h'.le), C⟩) (tendsto_tsum_of_dominated_convergence ?S
    (clog (by fun_prop (disch := simp)) <| A s h'.le ·) (.mono (le_mem_nhds h') B)).neg
  apply ((summable_absNorm_rpow h).comp_injective asIdeal_injective).mul_left

/-- If |a_v| ≤ 1 for all primes v of K and s > 1 is real, the Euler product ∏_v (1 − a_v
q_v^{−s})^{−1} converges unconditionally to the value of `eulerProd` for a at s. -/
lemma hasProd_eulerProd (hs : 1 < s) : HasProd (fun v ↦ (1 - a v * v.q ^ (-s : ℂ))⁻¹)
  (eulerProd a s) := by simpa [exp_neg, *] using! (hasProd_of_hasSum_log
  (by simp [log_euler_factor_bounds ha hs.le, -cpow_neg]) (eulerProd_eq_exp ha hs).2.1.hasSum).inv₀

/-- For |a_v| ≤ 1, Q finite and P(s) = ∏_{w∈Q}(1 − a_w q_w^{−s}): P is analytic at the real
point 1, P(1) ≠ 0, and for real s > 1 putting the coefficients at Q to zero multiplies the
Euler product by P(s). -/
lemma eulerProd_erase Q : let P s := ∏ w ∈ Q, (1 - a w * w.q ^ (-s))
  AnalyticAt ℝ (P ∘ ofReal) 1 ∧ P 1 ≠ 0 ∧ ∀ s > 1, eulerProd (indicator Qᶜ a) s = eulerProd a s * P
    s := ⟨.comp (.restrictScalars (𝕜' := ℂ) (by fun_prop (disch := simp))) (ofRealCLM.analyticAt 1),
  prod_ne_zero_iff.2 fun w _ ↦ slitPlane_ne_zero (log_euler_factor_bounds ha le_rfl le_rfl w).2.1,
  fun s hs ↦ ((hasProd_eulerProd (by simp [indicator]; bound) hs).unique
  ((hasProd_eulerProd ha hs).congr_cofinite₀ (s := Q) (by simp [sub_eq_add_neg,
  log_euler_factor_bounds ha hs.le, -cpow_neg]) (by aesop))).trans (by aesop)⟩

/-- If |a_v| ≤ 1 and (s − 1)^l times the Euler product of a tends to some c ≠ 0 as real s ↓ 1, then
a has density l over the primes of degree one. -/
lemma hasPrimeDensity_of_tendsto {c} (hc : c ≠ 0) (h : Tendsto (fun s ↦ (s - 1) ^ l * eulerProd a s)
  (𝓝[>] 1) (𝓝 c)) : HasPrimeDensity a l := let Q s := (s - 1).log * l + -∑' v, _
  have h := (tendsto_nhdsWithin_congr (g := exp ∘ Q) (by simp_all
    [Q, exp_add, cpow_def, ne_of_gt, ofReal_log, le_of_lt]) h).div_const c
  have ⟨b, r, H⟩ := ((nhdsGT_basis_Ioc 1).1 _).1 (h (isOpen_slitPlane.mem_nhds (by aesop)))
  have C : ContinuousOn Q (.Ioc 1 b) := .add (by fun_prop (disch := grind)) fun _ h ↦
    tendsto_inf_left (eulerProd_eq_exp ha h.1).2.2
  have S := (summable_of_sum_le (by aesop_cat) sum_inv_minFac_sq_le_finrank).mul_left _
  ⟨_, (IsBoundedUnder.isBigO_one ℝ ⟨_, eventually_nhdsWithin_of_forall fun s h ↦
  tsum_of_norm_bounded S.hasSum (log_euler_factor_bounds ha le_rfl h.le · |>.1)⟩).add (((h.clog
    (by aesop)).const_add (Q b - ((Q b).exp / c).log)).isBigO_one ℝ), .mono (Ioc_mem_nhdsGT r) fun s
    h ↦ by grind [(S.of_norm_bounded (log_euler_factor_bounds ha le_rfl h.1.le · |>.1)).hasSum.sub
    (eulerProd_eq_exp ha _).2.1.hasSum, isCoveringMap_exp.constOn_of_comp isPreconnected_Ioc
    (C.fun_sub (.clog (by fun_prop) H)) (by simp [*, exp_sub, exp_log])]⟩

open Real

/-- If |a_v| ≤ 1 for all v and s ≥ σ ≥ 2 are real, the Euler product with coefficients a is
non-zero at s, and the logarithm of its modulus has absolute value at most 2[K:ℚ]·2^{2−σ}. -/
lemma abs_log_norm_eulerProd_le {σ} (hσ : 2 ≤ σ) (hs : σ ≤ s) :
    eulerProd a s ≠ 0 ∧ |‖eulerProd a s‖.log| ≤ 2 * finrank ℚ K * 2 ^ (2 - σ) := by
  simp (disch := grind) [-cpow_neg]
  grw [abs_re_le_norm, le_of_tendsto' (eulerProd_eq_exp ha (by bound)).2.1.hasSum.norm]; intro
  grw [← sum_inv_minFac_sq_le_finrank, mul_sum, sum_mul, norm_sum_le_of_le]; intro v
  grw [← @rpow_le_rpow_of_nonpos _ v.q, (log_euler_factor_bounds ha _ hs _).2.2, Nat.minFac_le,
    rpow_sub] <;> simp [field] <;> grind [v.q_bounds]

omit ha

/-- Euler product: for χ multiplicative on the ideals of 𝓞_K with |χ| ≤ 1 and real s > 1, the
series ∑ χ(I) N(I)^{−s} converges to the Euler product with coefficients χ(v). -/
lemma hasSum_eulerProd (χ : Ideal (𝓞 K) →* ℂ) (hχ : ∀ I, ‖χ I‖ ≤ 1) (hs : 1 < s) :
    HasSum (fun I ↦ χ I * I.absNorm ^ (-s : ℂ)) (eulerProd (χ ·.1) s) := by
  use (Summable.hasSum_iff ?S).2 (eq_of_mul_inv_eq_one ((tendsto_nhds_unique (((hasProd_eulerProd
    (hχ ·.1) hs).inv₀ (by simp [*])).const_mul _) (.congr (HasSum.tsum_eq <| ·.cons_induction
    (by simpa using (?S).hasSum) fun v T n H ↦ ?_) (tendsto_tsum_of_dominated_convergence (f := fun
    T I ↦ ite (∀ v ∈ T, ¬v.1 ∣ I) (χ I * I.absNorm ^ (-s : ℂ)) 0) (?S).norm (fun I ↦ ?_) (.of_forall
    (by grind [norm_zero]))))).trans (tsum_ite_eq ⊤ 1)))
  exact (summable_absNorm_rpow hs).of_norm_bounded (by grw [norm_mul_le, hχ]; simp)
  rw [prod_cons, inv_inv, mul_left_comm, one_sub_mul]
  use (H.sub (((mul_right_injective₀ v.3).hasSum_iff (by grind [dvd_def])).1 ((H.mul_left
    _).congr_fun (by simp [Prime.dvd_mul, prime, natCast_mul_natCast_cpow,
    prime_dvd_prime_iff_eq]; grind [asIdeal_inj])))).congr_fun fun _ ↦ (sub_sub_self ..).symm
  split; simp_all [← one_eq_top, (prime _).not_dvd_one]
  cases (ideal_ne_top_iff_exists (RingOfIntegers.not_isField K) I).1 ‹_›
  use tendsto_atTop_of_eventually_const (i₀ := {‹_›}) (by grind [dvd_iff_le])

lemma HasPrimeDensity.sum {ι} [Fintype ι] {a : ι → FinPlace K → ℂ} (w : ι → ℂ) {l : ι → ℂ} (h : ∀ i,
  HasPrimeDensity (a i) (l i)) : HasPrimeDensity (∑ i, w i * a i ·) (∑ i, w i * l i) := ⟨_,
  .sum fun i _ ↦ (h i).choose_spec.1.const_mul_left _, .mono (.all (h · |>.choose_spec.2)) fun _ h ↦
  by simpa [sum_mul, mul_sub, mul_assoc] using hasSum_sum fun _ _ ↦ (h _).mul_left _⟩

lemma HasPrimeDensity.re_le_re : HasPrimeDensity a l → HasPrimeDensity b l' → (∀ᶠ v in cofinite,
  v.q.Prime → (a v).re ≤ (b v).re) → l.re ≤ l'.re | ⟨_, X, h⟩, ⟨_, Y, k⟩, e => not_lt.1 (fun H ↦
  not_isBoundedUnder_of_tendsto_atTop (.add_atTop (continuousWithinAt (by fun_prop (disch := simp)))
  ((tendsto_log_nhdsGT_zero.comp (sub_self (1 : ℝ) ▸ map_subRight_nhdsGT.le)).const_mul_atBot_of_neg
  (sub_neg.2 H))) ((Y.sub X).isBoundedUnder_le.mono_le (h.mp (k.mono fun _ k h ↦ (add_left_mono
  (sum_le_hasSum e.toFinset (by simp [cpow_ofReal, e.mem_toFinset, -ite_mul]; bound)
  (hasSum_re (k.sub h)))).trans (.trans (by simp; bound) (re_le_norm _))))))

lemma hasPrimeDensity_const c : HasPrimeDensity (fun _ : FinPlace K ↦ c) c := by simpa using
  (HasPrimeDensity.sum ![c] fun _ ↦
  hasPrimeDensity_of_tendsto (by simp) (by simp) (tendsto_sub_one_mul_dedekindZeta_nhdsGT K |>
  tendsto_nhdsWithin_congr fun s h ↦ congrArg₂ _ (cpow_one _).symm (((hasSum_eulerProd 1 (by simp)
  h).tsum_fiberwise absNorm).congr_fun fun _ ↦ by rw [tsum_congr (by rw [·.2])]; aesop).tsum_eq))

/-- A number field K has infinitely many primes of degree one, that is, finite places w whose
absolute norm q_w is a prime number. -/
lemma frequently_prime_q : ∃ᶠ w : FinPlace K in cofinite, w.q.Prime :=
  ((hasPrimeDensity_const 1).re_le_re (hasPrimeDensity_const 0) <| ·.mp (by simp)).mt (by simp)

/-- For an extension L/K of number fields and c ∈ ℂ, the family v ↦ c·#{w above v : q_w = q_v}
has density c over the primes of degree one of K, in the sense of `HasPrimeDensity`. -/
lemma hasPrimeDensity_card_degree_one L [Field L] [NumberField L] [Algebra K L] c :
    HasPrimeDensity (fun v ↦ c * {w : FinPlace L | w.below K = v ∧ w.q = v.q}.ncard) c := by
  peel 3 @hasPrimeDensity_const L ..
  convert! this.tsum_fiberwise (·.below K)
  erw [← ite_zero_mul, mul_right_comm, ← nsmul_eq_mul', ← tsum_const, tsum_congr,
    (inclusion_injective _).tsum_eq]; simp; rintro w ⟨⟩ p -
  use rfl, .symm (p.pow_eq_iff.1 (absNorm_pow_inertiaDeg (under ..) _)).1
  repeat grind
