/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/ChartScalars
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/ChartScalars
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.WachKisin.ChartScalars. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/WachKisin/ChartScalars.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin.HodgeFrame
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Kisin lattice (Breuil–Kisin module) of a crystalline lattice (known result; see
Lib.PadicHodge.WachKisin.PeriodMatrixFrame).

This file: Maps θφ^{-n}; tilt elements fixed by the fixer of S approximated from S (Ax). S-linear
maps extend from A_inf to B+; closure of S[1/p] and its properties. -/

open Algebra _root_.RingHom Amax BPlus Ideal NeZero OC RingEquiv Set Witt WittVector nonZeroDivisors

attribute [-simp] map_smul

variable {p : ℕ} [ThePrime p] (c : Lift.Chart) {m : FrobGal} {y : BPlus} (n : ℕ)

/-- The ring homomorphism θ ∘ φ^{−n} from A_inf to O_C. -/
noncomputable def Lift.thetaPhiInv := theta.comp ((ofBijective _ frobEnd_bijective)⁻¹ ^ n).toRingHom

@[simp] lemma Lift.thetaPhiInv_succ a :
    thetaPhiInv (n + 1) (frobEnd a) = thetaPhiInv n a := congr(thetaPhiInv n $(symm_apply_apply ..))

lemma Lift.mk_thetaPhiInv_eq_coeff : ∀ a, thetaPhiInv n a = PreTilt.coeff n a.constantCoeff := n.rec
    mk_fontaineTheta fun _ ↦ frobEnd_bijective.2.forall.2 ∘ by simp [↓constantCoeff_frobEnd]

@[simp] lemma Lift.thetaPhiInv_smul (g : Gp p) : ∀ a, thetaPhiInv n (g • a) = g • thetaPhiInv n a :=
  n.rec (theta_smul g) fun _ ↦ frobEnd_bijective.2.forall.2 ∘ by simp

lemma Lift.frobE_dvd_iff {c : Lift.Chart} {n a} : (c.frobE n).1 ∣ a ↔
  thetaPhiInv n a = 0 := by erw [c.coe_φ_pow, theta_eq_zero_iff_xi_dvd,
  ← c.associated_E_xi.dvd_iff_dvd_left, inv_pow, ← map_dvd_iff_dvd_symm (_ : RingAut _)]; simp

namespace Lift.Chart

/-- Let f: A_inf → S be S-linear, α in S, r in A_inf, and θ_n = θ∘φ^{−n}. If θ_n(α) divides
θ_n(r) in O_C, then θ_n(f(r)) = θ_n(αx) for some x in S. -/
lemma exists_frobE_dvd_sub_of_dvd (f : _ →ₗ[c.S] _) α r (h : thetaPhiInv n α.1 ∣ thetaPhiInv n r) :
  ∃ x, c.frobE n ∣ f r - α * x :=
  ((theta_surjective.comp (Equiv.surjective _)).exists.1 h).imp' f fun a _ ↦ .imp' f (fun b (k :
  r - α • a = c.frobE n • b) ↦ by simpa using congr(f $k)) (frobE_dvd_iff.2 (by simpa [smul_def]))

/-- For a chart and n, the Z_p-algebra homomorphism S → C_p given by restricting θ ∘ φ^{−n} to
S. -/
noncomputable abbrev thetaPhiInvS : c.S →ₐ[ℤ_[p]] ℂ_[p] :=
  toPadicIntAlgHom ((thetaPhiInv n).comp c.S.val)

/-- Let K be a Q_p-subalgebra of C_p and y in Q̄_p. If every g in G_p fixing all those
θφ^{−n}(s), n ≥ 0, s in S, that lie in K also fixes y, then y lies in K. -/
lemma mem_of_fixed_thetaPhiInvS {K : Subalgebra ℚ_[p] _} {y} (h : ∀ g : Gp p,
  (∀ n, ∀ x ∈ (c.thetaPhiInvS n).range, x ∈ K → g • x = x) → g y = y) : ↑y ∈ K :=
  (InfiniteGalois.fixedField_fixingSubgroup (subalgebraEquivIntermediateField
  (K.comap (algHom ..)))).le (x := y) fun g ↦ h _ fun n _ s ↦ (IsAIC.mem_range_of_isIntegralElem
  ((IsIntegral.of_mem_of_fg _ · _ s) ((Submodule.fg_range ((c.thetaPhiInvS n).toLinearMap
  ∘ₗ
  ((Pi.basisFun ..).constr ℕ (c.z ^ ·.1)).restrictScalars _)).of_le (range_subset_iff.2
  (c.exists_dvd_sub_sum_z_pow n rfl · |>.imp (by simp_all [dvd_iff_coe_dvd, frobE_dvd_iff]
  ))))).tower_top).rec fun x ↦ (· ▸ (.trans (smul_coe_Cp ..) congr($(g.2 ⟨x, ·⟩))))

/-- Let y in O^♭ be fixed by every g in G_p fixing S pointwise. For every N and all large n, the
N-th component of y in O_C/p is the n-th component of the reduction modulo p of some s in S. -/
lemma eventually_exists_coeff_eq_of_fixed {y : OFlat} (h : ∀ g : Gp p, (∀ s : c.S, g • s.1 = s) →
  g • y = y) N : ∀ᶠ n in .atTop,
  ∃ s : c.S, y.coeff N = PreTilt.coeff n s.1.constantCoeff := let t := teichmuller p y
  have ⟨_, ⟨x, hx, rfl⟩, e⟩ := SeminormedAddCommGroup.mem_closure_iff.1 (@ax_exists_near_fixed p _
    (fixingSubgroup _ c.S) (thetaPhiInv N t) (by erw [← coe_smul, ← thetaPhiInv_smul,
       smul_teichmuller, h · ·])) ‖(p : ℂ_[p])‖ (by simp [ne])
  have m := @monotone_nat_of_le_succ _ _ (c.thetaPhiInvS · |>.range) fun _ _ ↦
    .imp' c.φ (by simp [«φ»])
  (multiple_mem_adjoin_of_mem_localization_adjoin _⁰ _ _ _ (c.mem_of_fixed_thetaPhiInvS fun g G ↦
    hx ⟨g, fun s ↦ sub_eq_zero.1 (zero_dvd_iff.1 (dvd_of_mem_of_constantCoeff_dvd (⨅ n,
    ker (thetaPhiInv n)).zero_mem (by simp [ne]) (fun a h ↦ ⟨0, Perfection.ext
    (mk_thetaPhiInv_eq_coeff · a ▸ by aesop)⟩) _ (by simpa [Subtype.ext_iff] using (G · _
    ⟨_, rfl⟩ (subset_adjoin (Algebra.mem_iSup_of_mem _ ⟨_, rfl⟩))))))⟩)).elim fun ⟨a, _⟩ h ↦
  Filter.mem_atTop_sets.2 ((mem_iUnion.1 ((Subalgebra.coe_iSup_of_directed m.directed_le).le
  (adjoin_le le_rfl h))).imp fun _ w n l ↦ (m l w).elim fun s u ↦ ((c.thetaPhiInvS n).range.smul_mem
    (one_mem _) a).elim fun α v ↦ (c.exists_frobE_dvd_sub_of_dvd n c.coord₀ α s ⟨thetaPhiInv N t -
    ⟨_, mem_OC.2 (e.trans norm_p_lt_one).le⟩, by aesop⟩).imp fun s d ↦ mk_thetaPhiInv_eq_coeff N
    t ▸ by simp_all [↓← mk_thetaPhiInv_eq_coeff, coord₀_coe, dvd_iff_coe_dvd, frobE_dvd_iff,
    mk_span_eq_iff_dvd_sub, e.le, ne_zero, OC.dvd_iff_norm_le, ← algebraMap_smul ℚ_[p] a])

attribute [-instance] NormedAlgebra.toAlgebra NormedSpace.toModule Subalgebra.isScalarTower_left

attribute [-simp] IsEmpty.forall_iff LinearMap.map_smul_of_tower isUnit_map_iff

lemma _root_.Lift.eq_zero_of_p_pow_amaxImage (h : ∀ n, ∃ w ∈ amaxImage, y = p ^ n * w) :
  y = 0 := let ⟨_, ⟨b, _⟩, _⟩ := h 0
  by grind [@eq_of_forall_pow_dvd_sub _ _ b 0 p _ (by simp_all [← injective_Amax_BPlus.eq_iff,
    amaxImage, dvd_def])]

lemma _root_.Lift.map_p_pow_mul {F} [FunLike F BPlus BPlus] [AddMonoidHomClass F _ _] (G : F) n y :
    G (p ^ n * y) = p ^ n * G y := by grind [map_nsmul G (p ^ n)]

lemma _root_.Lift.smul_mem_amaxImage : ∀ y ∈ amaxImage, m • y ∈ amaxImage := by simp [amaxImage]

/-- The structure ring homomorphism from A_inf to B^+. -/
noncomputable abbrev ainfToBPlus := algebraMap Ainf BPlus

lemma theta_z_dvd_p : theta c.z ∣ p := by grw [c.dvd_iff_coe_dvd.1 c.z_dvd_E_sub_p]; simp [theta_E]

lemma theta_z_ne_zero : theta c.z ≠ 0 := ne_zero_of_dvd_ne_zero out c.theta_z_dvd_p

/-- The S-subalgebra S_B of those y in B^+ whose multiplication commutes with every S-linear
endomorphism of B^+ that maps the image of A into itself. -/
noncomputable def bicommutant :=
  Subalgebra.comap (lmul c.S _) (.centralizer _ {G | ∀ y ∈ amaxImage, G y ∈ amaxImage})

@[simp] lemma ainfToBPlus_mem_bicommutant {c : Chart} (s : c.S) : ainfToBPlus s ∈ c.bicommutant :=
  c.bicommutant.2 s

attribute [local simp] mem_span_singleton IsUnit.ne_zero IsUnit.pow map_p_pow_mul ne pow_mem

/-- Every S-linear map f from A_inf to itself extends, along A_inf → B^+, to an S-linear map
from B^+ to itself that sends the image of A into itself. -/
lemma exists_extendToBPlus (f : _ →ₗ[c.S] _) : ∃ G :
  _ →ₗ[c.S] _, (∀ a, G (ainfToBPlus a) = ainfToBPlus (f a)) ∧ ∀ y ∈ amaxImage, G y ∈ amaxImage := by
  let i := (IsScalarTower.toAlgHom c.S Ainf Amax).toLinearMap
  have K {n a} := p_pow_dvd_of_mem_pow ∘
    (by simpa [span_singleton_eq_span_singleton.2 c.associated_E_xi, span_insert,
    Ideal.map_pow, Ideal.map_sup] using ((span {↑p, c.E} ^ n).smul_top_le_comap_smul_top f ·)) ∘
    @Amax.mem_span_pow_of_p_pow_dvd _ _ a n
  let F := ((primaryComponent _ (span {↑p})).comap (i.prod (i ∘ₗ f)).range.mkQ).subtype
  choose G₀ h₀ using (by simpa [span_singleton_pow, F, i, LE.le, primaryComponent_mem,
    ← Submodule.Quotient.mk_smul, @smul_def _ Amax, Function.Surjective,
    Submodule.Quotient.forall] using (exists_adic_extension (span {↑p}) (.fst .. ∘ₗ F)
    (.snd .. ∘ₗ F)) :) (let ⟨d, a, w, e⟩ := ·.exists_algebraMap_eq_p_pow_mul_sub 1
    ⟨_, ⟨_, d, a, e, (K ⟨_, e⟩).choose_spec⟩, by simp⟩) fun n x z m a _ _ ↦ by
    grw [← le_self_add]; simpa [*, pow_add, mul_dvd_mul_iff_left] using @K (m + n) a
  have := (map_natCast (algebraMap c.S Amax) p ▸ isLocalizationAway_p_bPlus :)
  let j := (IsScalarTower.toAlgHom c.S Amax BPlus).toLinearMap
  have H := IsLocalizedModule.map_apply (.powers ↑p) j j G₀
  exact ⟨_, (by erw [H, h₀ _ _ 0 ·] <;> bound), by simp_all [amaxImage, j]⟩

/-- For an S-linear map f: A_inf → A_inf, a chosen S_B-linear extension f̂: B^+ → B^+ that maps
the image of A into itself. -/
noncomputable def extendToBPlus f := (c.exists_extendToBPlus f).choose

lemma extendToBPlus_ainfToBPlus f a : c.extendToBPlus f (ainfToBPlus a) =
  ainfToBPlus (f a) := by grind [extendToBPlus]

lemma extendToBPlus_mem_amaxImage f : ∀ y ∈ amaxImage,
  c.extendToBPlus f y ∈ amaxImage := by grind [extendToBPlus]

/-- The extension to B^+ of an S-linear map f on A_inf is S_B-linear: it commutes with
multiplication by every y in S_B. -/
lemma extendToBPlus_mul f (h : y ∈ c.bicommutant) x : c.extendToBPlus f (y * x) =
  y * c.extendToBPlus f x := congr($(h _ (c.extendToBPlus_mem_amaxImage f)) x)

/-- For a chart and an index i, the S-linear endomorphism λ̂_i of B^+ extending the coordinate
λ_i: A_inf → S ⊂ A_inf (`Lift.Chart.extendToBPlus`). -/
noncomputable abbrev extendedCoord i :=
  c.extendToBPlus (Algebra.linearMap .. ∘ₗ c.adicBasis.coord i)

attribute [local simp] smul_def extendToBPlus_mem_amaxImage extendToBPlus_ainfToBPlus
  extendToBPlus_mul smul_mem_amaxImage mul_assoc pow_add

lemma eq_zero_of_ainfToBPlus (G : _ →+ _) (hA : ∀ y ∈ amaxImage, G y ∈ amaxImage) (h : ∀ a,
  G (ainfToBPlus a) = 0) : G y = 0 := eq_zero_of_p_pow_amaxImage
  (let ⟨_, _, w, _, e⟩ := y.exists_Ainf_approx · 0; ⟨G w, by simpa [*, -e] using congr(G $e)⟩)

lemma smul_extendToBPlus_mem_bicommutant {f} (h : ∀ a, m • f a ∈ c.S) : m • c.extendToBPlus f y ∈
  c.bicommutant := fun G _ ↦ by ext; simpa [mul_left_comm (m • _)] using
  (fun w : amaxImage ↦ eq_zero_of_ainfToBPlus (.comp (G * .mulRight _ w -
  .mulRight _ (G w)).toAddMonoidHom (m • c.extendToBPlus f)) (by aesop)
  (by simpa using G.2 ⟨_, h ·⟩ _)) ⟨_, _, exists_p_pow_mul_eq_amax.choose_spec.choose_spec.symm⟩

/-- For each coordinate λ_i: A_inf → S of the chosen topological basis of A_inf over S, its
extension to B^+ takes all its values in S_B. -/
lemma extendedCoord_mem_bicommutant i y : c.extendedCoord i y ∈ c.bicommutant :=
  (one_smul ..).subst (c.smul_extendToBPlus_mem_bicommutant (by simp))

lemma mem_bicommutant_of_mul {u v} : v ∈ c.bicommutant → v ≠ 0 → v * u ∈ c.bicommutant →
  u ∈ c.bicommutant := by simp_all [bicommutant, Subalgebra.mem_centralizer_iff, DFunLike.ext_iff]

lemma exists_bicommutant_mul_p_eq_one : ∃ u ∈ c.bicommutant, u * p = 1 :=
  ⟨↑isUnit_p.unit⁻¹, by simp [c.mem_bicommutant_of_mul (v := p)]⟩

/-- The extension to B^+ of the coordinate λ₀ at the distinguished index i₀ of the topological
basis of A_inf over S is the identity on S_B. -/
lemma extendedCoord_oneIndex_eq_self (hy : y ∈ c.bicommutant) : c.extendedCoord c.oneIndex y =
  y := by
  obtain _ := c.coord₀_coe 1, (c.extendToBPlus_ainfToBPlus · 1), (c.extendToBPlus_mul · hy 1); aesop

/-- For y in B^+ and m ≥ 0, for all sufficiently large finite sets F of indices, y − Σ_{i∈F} b_i
λ̂_i(y) lies in p^m A, where λ̂_i extends the i-th coordinate of the topological basis (b_i)
to B^+. -/
lemma eventually_approx_sum_extendedCoord y m : ∀ᶠ F in Filter.atTop, ∃ w ∈ amaxImage, y - ∑ i ∈ F,
  c.adicBasis.b i • c.extendedCoord i y = p ^ m * w := (y.exists_Ainf_approx m 0).rec fun k ⟨a, w,
  hw, e⟩ ↦ (c.adicBasis.eventually_sub_sum_mem a _).mono fun F h ↦ ⟨_, .symm ⟨by
  simpa [← mul_add, map_add, ← IsScalarTower.algebraMap_apply, ↓@commutes c.S,
    sub_eq_iff_eq_add] using congr((1 - ∑ i ∈ F, c.adicBasis.b i • c.extendedCoord i) $e -
    algebraMap _ _ $((p_pow_dvd_of_mem_pow ((c.exists_maxIdeal_pow_le (k
    + m)).choose_spec h)).choose_spec.symm)), add_mem (sub_mem hw (sum_mem (by aesop))) ⟨_, rfl⟩⟩⟩

/-- For a chart, the Frobenius φ of B^+ maps the subring S_B into itself. -/
lemma frobEnd_mem_bicommutant : y ∈ c.bicommutant → frobEnd y ∈ c.bicommutant :=
  (extendedCoord_oneIndex_eq_self _ · ▸ smul_extendToBPlus_mem_bicommutant _ fun _ ↦ («φ» _ _).2)

lemma exists_bicommutant_mul_phi_E_eq_one : ∃ u ∈ c.bicommutant, u * ainfToBPlus
  (c.φ c.E) = 1 := have h : IsUnit (ainfToBPlus (c.φ _)) := ((associated_p_frobEnd_xi.trans
    ((c.associated_E_xi.map _).map _).symm).map (algebraMap ..)).isUnit (by simp)
  ⟨↑h.unit⁻¹, by simp [c.mem_bicommutant_of_mul _ h.ne_zero]⟩

/-- Let ν in S have ξ ∈ (p, ν)A_inf, and let λ₀ be the coordinate that is the identity on S. For
b in A and M ≥ 0, p^M λ̂₀(b) = s + ν^M w with s in S, w in S_B. -/
lemma exists_pow_mul_extendedCoord_eq_add (ν : c.S) (h : ∃ b, ν.1 ∣ xi - p * b) (b : Amax) M : ∃ s :
  c.S, ∃ w ∈ c.bicommutant, p ^ M * c.extendedCoord c.oneIndex (algebraMap _ _ b) =
  ainfToBPlus s + ainfToBPlus ν ^ M * w := let ⟨_, _, f⟩ := b.exists_p_pow_mul_eq_add h M
  ⟨_, _, c.extendedCoord_mem_bicommutant _ _, by
    simpa [← IsScalarTower.algebraMap_apply] using! congr(c.extendToBPlus _ (algebraMap _ _ $f))⟩

/-- For every y in S_B there are m ≥ 0, w in the coefficient ring Λ of the chart and y' in B^+
with p^m y = w + zy'. -/
lemma eventually_exists_pow_mul_eq_add_z_mul (hy : y ∈ c.bicommutant) : ∀ᶠ m in .atTop, ∃ w,
  ∃ x ∈ c.bicommutant, p ^ m * y = ainfToBPlus (algebraMap (WittFq c.f) _
  w) + ainfToBPlus c.z * x := y.exists_p_pow_mul_eq_amax.rec fun k ⟨b, hb⟩ ↦
  .mono (Filter.Ioi_mem_atTop k) fun _ h ↦ h.dest.rec fun n q ↦
  q ▸ let ⟨s, _, hx, e⟩ := c.exists_pow_mul_extendedCoord_eq_add _ c.xi_mem_span_p_z (p ^ n * b) 1
  (c.exists_z_dvd_sub_const s).imp fun _ ⟨r, h⟩ ↦ ⟨_, add_mem (ainfToBPlus_mem_bicommutant r) hx, by
    simpa [extendedCoord_oneIndex_eq_self, hy, h, mul_add, add_assoc, ← hb, mul_left_comm] using e⟩

/-- If g in G_p fixes the image of Λ in A_inf pointwise and y lies in S_B, then z divides gy − y
in B^+. -/
lemma z_dvd_sub {g} (h : FixesLambda c.f g) (hy : y ∈ c.bicommutant) :
  ainfToBPlus c.z ∣ g • y - y := by
  obtain ⟨⟨_, _, _, _, f⟩, _, e⟩ := (c.eventually_exists_pow_mul_eq_add_z_mul
    hy).exists, show c.z.1 ∣ g • c.z by erw [z_eq_teichmuller, smul_teichmuller]; simp [map_dvd,
    untilt_dvd_iff.1, OC.dvd_iff_norm_le, untilt_frobGal_smul]
  simpa [← mul_sub, h, e] using congr(ainfToBPlus c.z ∣ g • $f - $f)

lemma eq_zero_of_z_pow_dvd (h : ∀ n, ainfToBPlus c.z ^ n ∣ y) : y = 0 := c.7.rec fun a e ↦
  BPlus.eq_zero_of_forall_pow_dvd a (by
  simp_all (maxDischargeDepth := 4) [← e, add_mul, ← pow_mul, mul_pow, IsUnit.map, z])

/-- For a chart and a in A_inf: if z divides E^k a in B^+, then z divides a in A_inf. -/
lemma z_dvd_of_dvd_E_pow_mul {k a} (h : ainfToBPlus c.z ∣ ainfToBPlus (c.E ^ k * a)) : ↑c.z ∣ a :=
  dvd_of_mem_of_constantCoeff_dvd
  (I := (span {ainfToBPlus c.z}).comap ainfToBPlus) (by simp) (by simp) (fun _ h ↦
  mem_span_pair_iff.1 (by simpa [image_pair, -smul_def] using
  c.adicBasis.mem_of_coord le_rfl fun i ↦ Submodule.smul_mem_smul (((pow_one _).trans
  (c.seriesEquiv.isLocalRing.eq_maximalIdeal inferInstance)).ge fun u ↦ one_ne_zero
  (c.eq_zero_of_z_pow_dvd (by simp [isUnit_of_dvd_unit ((mem_span_singleton.1 h).imp' _ fun _ e ↦ by
  simpa using! congr(c.extendedCoord i $e)) (u.map (algebraMap ..))]))) ⟨⟩)) a (by induction k <;>
                             simp_all [pow_succ', E, add_mul, dvd_add_right, Dvd.dvd.mul_right])
