/- GID: D5/S3/Zeros/GRH/Lib/LocalGL/TraceFormula/TraceComparison
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/LocalGL/TraceFormula/TraceComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.LocalGL.TraceFormula.TraceComparison. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/LocalGL/TraceFormula/TraceComparison.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.LocalGL.TraceFormula.ChangingSigns
import D5.S3.Zeros.GRH.Lib.Weil.Periods.FiniteBesselGroup
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Character.FormalDegree
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.ReproducingKernel
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Comparison of simple trace formulas for unitary groups that differ only at real
places. The form here uses integrable idempotent kernels of very regular discrete series in place of
pseudo-coefficients, elliptic test functions, and a CM field containing the 5040th roots of unity
with an even number of infinite places. Convergence is obtained by packing, with no truncation and
no endoscopy. Source: Labesse, Changement de base CM et séries discrètes (2011), Thm 5.4 and its
proof; Arthur and Clozel (1989), ch. 1, Lemmas 2.4-2.6; integrable test functions as in Knightly and
Li, Traces of Hecke operators (2006).

Known result: Selberg principle, that orbital integrals of an idempotent vanish off the elliptic
set. The form here is for a minimal convolution idempotent with polynomial decay on a product of
groups U(p,q), inside the adelic orbital integral of a rational point with irreducible
characteristic polynomial. If that integral is non-zero, all eigenvalues have absolute value 1.
Source: Harish-Chandra, Discrete series II, Acta Math. 116 (1966), Thm 11; Blanc and Brylinski,
Cyclic homology and the Selberg principle, J. Funct. Anal. 109 (1992); Hochs and Wang, Orbital
integrals and K-theory classes (2019), Cor 4.8.

This file: Equal Hecke traces on unitary groups differing at real places; Selberg principle. -/

noncomputable section

open NumberField MeasureTheory Measure Matrix Polynomial Module Subgroup Complex Norms.L2Operator
  MulAction Pointwise Finset InnerProductSpace Equiv ComplexOrder ProbabilityTheory
  Fintype Real ConjAct ENNReal


variable {E n : Type} [Field E] [CMType E] [Fintype n] {s} (V : Space E n s) {B}
  (hE : Even (numInfPlaces E)) (hB : 16 * finrank ℚ E * (card n + 1) ^ 3 ≤ B) {Ω :
  Set
  (Gf E n)} (hΩ : IsCompact Ω) (hi : ∀ g ∈ Ω, ∃ w, Irreducible (g.atPlace w).1.charpoly) {k : _ → ℂ}
attribute [-simp] inv_mul_cancel₀ isConj_iff inv_mul_cancel_left₀ IsUnit.inv_mul_cancel_left
  mul_inv_cancel_left₀ IsUnit.mul_inv_cancel_left mul_inv_cancel_comm_assoc

/-- If A has irreducible characteristic polynomial, y ≠ 0 and Aʲy = Bʲy for all j ≤ n, for n × n
matrices A, B over a field, then A = B. -/
theorem eq_of_pow_mulVec_eq {F n} [Field F] [Fintype n] {A B : Matrix n n F} {y}
    (hA : Irreducible A.charpoly) (hy : y ≠ 0) (h : ∀ j ≤ card n, A ^ j *ᵥ y = B ^ j *ᵥ y) :
    A = B := toLin'.injective (LinearMap.ext_on_range (((degreeLT.basis F _).linearIndependent.map'
  (((aeval A).toLinearMap.smulRight y).domRestrict _) (bot_unique fun q l ↦ q.ext
  (eq_zero_of_dvd_of_degree_lt (hA.dvd_iff_not_isCoprime.2 (hy <| isUnit_aeval_iff_isCoprime.2
  · |>.smul_eq_zero.1 l)) (by simpa using mem_degreeLT.1 q.2)))).span_eq_top_of_card_eq_finrank'
  (by simp)) fun j ↦ by simpa [pow_succ', ← mulVec_mulVec, ← h j j.2.le] using! h _ j.2)

/-- For x in GL_n(𝔸_f) and y in GL_n(E), the GL_n(E)-orbit of (xG_f, y), with z acting by
(zxG_f, zyz⁻¹); formally the orbit of the triple (xG_f, y, 0). -/
def frameClass (a : _ × GL n E) :=
  Quotient.mk (orbitRel (GL n E) (MarkedTriple (U 1))) (⟦a.1⟧, a.2, 0)

lemma frameClass_eq_iff {x x' : GL n (𝔸f E)} {y y'} : frameClass (x, y) = frameClass (x', y') ↔ ∃ z,
  x⁻¹ * toFinGL z * x' ∈ U 1 ∧ z * y' * z⁻¹ = y := Quotient.eq.trans (exists_congr fun _ ↦ by
  erw [mul_assoc, ← QuotientGroup.eq, Prod.mk_inj, Prod.mk_inj]; tauto)

namespace Space

/-- For a rational γ in U(J)(E), seen in G, the function x ↦ k((x⁻¹γx)_∞)·1_Ω((x⁻¹γx)_f) on G,
for k a function on G_∞ and Ω a subset of G_f. -/
def geometricTerm (k : _ → ℂ) (Ω : Set _) γ x :=
  k (x⁻¹ * V.ratEmbed γ * x).1 * Ω.indicator 1 (x⁻¹ * V.ratEmbed γ * x).2

/-- The orbital integral of a class c: the sum, over the γ in U(J)(E) with `frameClass` (x_f, γ) =
c, of the integral over Γ\G of the term `Space.geometricTerm` of γ. -/
def orbitalIntegral k Ω c := ∑' γ : (frameClass ⟨V.xFin, ·.1⟩) ⁻¹' {c}, ∫ x,
  V.geometricTerm k Ω γ.1 x ∂V.quotMeasure

lemma mem_U_one_iff_gram_eq {y z β} (k : y.1ᴴ * .map β (algebraMap ..) * y.1 = 1) :
  V.xFin⁻¹ * toFinGL z * y ∈ U 1 ↔ z.1ᴴ * V.J * z.1 = β := by erw [mem_U, gram_mul_of_gram_eq
  (gram_mul_of_gram_eq (gram_inv_of_gram_eq gram_xFin) rfl) rfl, ← k, y.mul_left_inj,
  (star y).mul_right_inj, ← map_conjTranspose_mul_mul] <;> simp [← ext_iff, -Matrix.map_mul]

@[fun_prop] lemma measurable_geometricTerm (hΩ : IsCompact Ω) (hm : Measurable k) γ : Measurable
  (V.geometricTerm k Ω γ) := by fun_prop (disch := exact hΩ.measurableSet) [geometricTerm]

include hi

lemma irreducible_charpoly_of_local {γ x} : x⁻¹ * V.embFin γ * x ∈ Ω → Irreducible γ.1.1.charpoly :=
  (hi _ · |>.elim fun w h ↦ (charpoly_monic _).irreducible_of_irreducible_map (algebraMap ..) _
  (by simpa [coe_embFin, ← charpoly_map] using! (charpoly_map ..).subst h))

include hB hΩ

/-- Unfolding: B ≥ 16[E:ℚ](n+1)³, Ω compact, each point with irreducible characteristic polynomial
at some finite place, k measurable, |k(g)|(∏‖g_w‖)^B bounded. Then `Space.geometricTerm` of γ is
integrable over Γ_γ\G (Γ_γ the centraliser) with integral `Space.orbitalIntegral` of γ's class;
these sum to ∫_{Γ\G} ∑_γ `Space.geometricTerm` of γ. -/
lemma orbitalIntegral_unfold [Nonempty n] (j : ∃ C, ∀ g, ‖k g‖ * (∏ w, ‖(g w).1.1‖) ^ B ≤ C) (hm :
  Measurable k := by fun_prop) :
  (∀ γ, let S := (centralizer {γ}).map V.ratEmbed; let F := V.geometricTerm k Ω γ; S.FixesLeft F ∧
      Integrable F S.qms ∧ V.orbitalIntegral k Ω (frameClass (V.xFin, γ)) = S.qms[F]) ∧
  HasSum (V.orbitalIntegral k Ω) V.quotMeasure[(∑' γ, V.geometricTerm k Ω γ ·)] := by
  have : Countable (GL n E) := Units.val_injective.countable
  suffices _ from ⟨fun p ↦ (integral_tsum_orbit (i := V.ratEmbed.comp ofConjAct.toMonoidHom) (Γ :=
    V.Γ) V.ratEmbed_injective rfl (by fun_prop) (by simp [geometricTerm, ConjAct.smul_def,
    mul_assoc]) (congrArg _ (stabilizer_eq_centralizer _)) fun _ ↦ frameClass_eq_iff.trans
    (by simp [↓V.mem_U_one_iff_gram_eq gram_xFin, Subtype.ext_iff, mem_U, isConj_iff])).imp_right
    (· (.inl this) |>.imp_right (·.2)), (hasSum_integral_of_lintegral this).tsum_fiberwise _⟩
  rcases j, V.exists_smul_mulVec_mem_latticeBall hΩ with ⟨⟨C, hC⟩, c, hc, H⟩
  refine' (lintegral_mono fun x ↦ _).trans_lt (lintegral_const_lt_top ofReal_ne_top)
  have l := (V.move x).firstMinimum_pos.trans_le ((csInf_insert ?bdd ?ne).trans_le inf_le_right)
  let ⟨_, ⟨y, ⟨hy, y0⟩, rfl⟩, e⟩ := exists_lt_of_csInf_lt ?ne (lt_two_mul_self l)
  let g γ := x⁻¹ * V.ratEmbed γ * x
  let Z := {γ | (g γ).2 ∈ Ω}
  have o (γ : Z) := le_prod_opNorm (g γ).1
  have p (a : Z) j : (c : E) ^ j • a.1.1.1 ^ j *ᵥ y ∈ latticeBall _ ((c * _) ^ j * _) := j.rec
    (by simpa using ⟨hy, e.le⟩) fun j i ↦ by simpa [pow_succ', mul_smul]
    using (@H _ x x _ a.2 (o a).2 _ i.1).imp_right (·.trans (by grw [i.2, ← mul_assoc]))
  have b := tsum_le_of_separated l (R := c ^ _ * (2 * _)) (by positivity) (fun a b ↦ Not.imp_symm
    fun l ↦ ?_) (one_le_pow₀ <| o · |>.1) (fun a ↦ (pi_norm_le_iff_of_nonempty _).2 fun j : Fin
    (card n + 1) ↦ (p a j).2.trans (by grw [j.is_le, mul_pow, mul_right_comm]; bound [o a,
    hc.bot_lt])) (lt_two_mul_self (mod_cast finrank_pos)) (c := 2) (by grind)
  simp [mul_div_assoc, l.ne', finrank_eq_two_mul_card_infinitePlace, ← ofReal_norm] at b hB ⊢
  grw [← tsum_subtype_eq_of_support_subset (s := Z) fun _ ↦ by simp_all [geometricTerm, Z, g],
    ENNReal.tsum_le_tsum fun γ ↦ ofReal_mono ?_, ← ofReal_tsum_of_nonneg
    (fun _ ↦ by positivity) (b.1.mul_left |C|), tsum_mul_left, b.2]
  erw [geometricTerm, Ω.indicator_of_mem γ.2, mul_one, rpow_neg_eq_inv_rpow]
  norm_cast; grw [inv_pow, le_mul_inv_iff₀, ← pow_mul, (by lia : _ * _ ≤ B), hC] <;> bound [o γ]
  ext : 3; exact eq_of_pow_mulVec_eq (V.irreducible_charpoly_of_local hi a.2) y0 fun j i ↦ by_contra
    fun _ ↦ l (csInf_le_of_le ?bdd ⟨_, ⟨sub_mem (p a j).1 (p b j).1, by simpa [hc]⟩, by simp⟩
    (norm_le_pi_norm _ ⟨j, by lia⟩))
  exacts [⟨0, by aesop_cat⟩,
    have ⟨_, a, b⟩ := exists_smul_mem_baseLattice 1; .image _ ⟨_, b, by simpa [funext_iff]⟩]

attribute [-instance] Prod.isScalarTower in
/-- Let e be a cusp kernel of order B ≥ 16[E:ℚ](n+1)³, Ω ⊂ G_f compact, each point with irreducible
characteristic polynomial at some finite place. If the orbital integral of e·1_Ω at γ is nonzero, γ
has irreducible characteristic polynomial with complex roots of modulus one.

Known result: Selberg principle: orbital integrals of an idempotent vanish off the elliptic set. -/
lemma elliptic_of_integral_ne_zero [Nonempty n]
    {e} (he : IsCuspKernel B e) {γ} (hγ : ((centralizer {γ}).map
  V.ratEmbed).qms[V.geometricTerm e Ω γ] ≠ 0) : IsEllipticSimilitude 1 γ V.J := by
  obtain ⟨-, _, a⟩ := by simpa [geometricTerm] using exists_ne_zero_of_integral_ne_zero hγ
  have I := V.irreducible_charpoly_of_local hi a
  simp [IsEllipticSimilitude, I, ← mem_U, roots_eq_map_numberedRoots I.separable, mul_conj']
  intro w i
  rcases he.4, he.2, he.1.1.measurable, (isConj_diagonal_of_isRoot_charpoly (g := ((V.ratEmbed γ).1
    w).1.1) (by erw [charpoly_map]; simpa [← charpoly_map] using!
    isRoot_numberedRoots I.separable _)).symm with ⟨⟨C, dec⟩, J, _, k, d⟩
  let N (y : GInf E s) := ∏ w, ‖(y w).1.1‖
  let Q := diagonal (Pi.single i 1) * k.1
  have L0 : Q ≠ 0 ∧ (∀ y, 0 < N y) ∧ ∀ y, 1 ≤ N y := by simp [Q, N, prod_pos, le_prod_opNorm]
  let H (y : GInf E s) := ‖Q * (y w).1‖.log
  have hH {t} {m : ℂ} (e : Q * (t w).1.1 = m • Q) : m ≠ 0 ∧ ∀ y, H (t * y) = ‖m‖.log + H y := by
    by_cases m = 0 <;> simp_all [H, ← mul_assoc, norm_smul, Real.log_mul]
  have hQ {t} (e : Commute t _) : Q * t = (k * t * k⁻¹.1) i i • Q := k⁻¹.mul_left_inj.1 (by
    ext a b; have := congr($((d.mul_left e).mul_left d.units_inv_symm_left) i b)
    simp_all [Q, mul_assoc, diagonal_apply]; grind)
  have g := by simpa [d.eq] using hH (hQ rfl)
  have lip a b : |H (a * b) - H a| ≤ N b := .trans (by
    refine abs_sub_le_iff.2 ⟨?_, .trans_eq ?_ (U.norm_inv _)⟩ <;> grw [← log_div, log_le_self,
      div_le_iff₀', ← norm_mul_le] <;> simp [← mul_assoc, *, field]) ((le_prod_opNorm b).2 w)
  let v := @volume (GInf E s) _
  let m := ((centralizer {γ}).map V.ratEmbed).qms.prod (v.prod v)
  let c x := x⁻¹ * V.ratEmbed γ * x
  have mul a b : N (a * b) ≤ N a * N b := by simp [N]; grw [norm_mul_le]; simp
  have I {a : _ → ℝ} (ha : ∀ p, |a p| ≤ N p.2.1 * N p.2.2) (A : Measurable a := by fun_prop) :
    Integrable (fun p ↦ a p * (e p.2.1 * (e p.2.2 * e (p.2.2⁻¹ * (p.2.1⁻¹ * (c p.1).1))) *
    V.geometricTerm 1 Ω γ p.1)) m := .mono'
    ((((V.orbitalIntegral_unfold hB hΩ hi (k := (N · ^ B)⁻¹) ⟨1, by simp [N, inv_mul_le_one]⟩).1
    γ).2.1.norm.mul_prod (J.mul_prod J)).const_mul C) (by fun_prop) (.of_forall fun ⟨x, y, u⟩ ↦ by
    erw [geometricTerm, geometricTerm, ← mul_inv_cancel_left (y * u) (c x).1]; set z :=
      (y * u)⁻¹ * _
    simp [L0, abs_of_pos, field, mul_assoc]; grw [ha, mul, mul, ← dec z]; linear_combination)
  obtain ⟨h₁, h₂, O, S⟩ := I fun p ↦ (lip p.1.1 p.2.1).trans (by simp [*]), I (lip ·.1.1 _
    |>.trans (mul ..)), I (a := 1) (by simp; bound), measurePreserving_prod_inv_mul_swap v v
  have P {F : _ → ℂ} {T} h (t : MeasurePreserving T m m) := (t.fubini (f := F)
    h).2.symm.trans (integral_congr_ae ((t.fubini h).1.prod_right_ae.mono fun _ ↦ integral_prod _))
  have D := (integral_prod_symm _ ((((O.const_mul ‖numberedRoots (Φ w) γ.1.1.charpoly i‖.log).add
    h₁).sub h₂).sub h₂)).trans (.trans (congrArg _ (funext fun p ↦ .trans (by
    simp [c, geometricTerm, g, division_def, mul_assoc]; grind) (identDistrib_orbitMeasure_mul_right
    (p.1, 1) fun ⟨_, _, h, rfl⟩ y ↦ have h := Commute.map (h _ rfl) V.ratEmbed; by simp [c,
      ↓Pi.sub_apply, geometricTerm, Subgroup.smul_def, mul_assoc, h.left_comm,
      hH (hQ congr(($h.symm.1 w).1.1))]).integral_eq)) (integral_skew_product (fun x ↦
    (S.comp ((measurePreserving_div_left _ (c x).1).prod (.id _))).map_eq) ((h₂.sub h₁).sub h₁)).2)
  simp (disch := fun_prop) only [m, ← integral_prod, integral_sub', integral_add',
    integral_const_mul, P h₂ (.prod (.id _) S), P h₁ (.id _), P O (.id _)] at D
  simp [c, v, geometricTerm, he.convolution_self, ← mul_assoc _ (e (_ * _))] at D hγ
  grind [norm_nonneg]

omit hΩ hi
variable {K : Subgroup (Gf E n)} [hK : IsLevel K] {h : Gf E n}
  (hh : ∀ g ∈ h • SetLike.coe K, ∃ w, Irreducible (g.atPlace w).1.charpoly)
include hE hh

/-- Let E contain μ_5040, with evenly many infinite places; K a level; each point of hK have
irreducible characteristic polynomial at some finite place; B ≥ 16[E:ℚ](n+1)³, H ≥
500n³+10n⁵. Then ∑⟨b_i, hb_i⟩, b an orthonormal basis of K-fixed forms of type e_l, is the
same for all s, V with e_l a cusp kernel of order B, l of gap H.

Known result: Comparison of simple trace formulas for unitary groups that differ only at real
places. -/
theorem exists_trace_eq [Nonempty n] [StablyUnram E]
    l H (j : gapThreshold n (10 * card n ^ 5) ≤ H) : ∃ t, ∀ {s} (V : Space E n
  s) {ι} [Fintype ι] (b : OrthonormalBasis ι ℂ (levelSpace (V.formRep (typeKernel l s)) K)),
  IsCuspKernel B (typeKernel l s) →
  (∀ w, (toHCParam s (l w)).HasGap H) → ∑ i, ⟪(b i).1, V.formRep _ h (b i)⟫_ℂ = t := by
  choose u y o r using fun a :
    {c | ∃ u, ∃ y : GL n E, HasSignType 1 1 y {1} u ∧ frameClass (u, y) = c} ↦ a.2
  let z a w : n ↪ Circle := (numberedRoots ..).codRestrict _ (have ⟨_, ⟨I, _, _, h⟩, _⟩ := o a; by
              simp [roots_eq_map_numberedRoots I.separable] at h; simpa using congr(√‖$(h w ·)‖))
  have F a s (σ : _ → Perm n) {x} : HasSignType (s ∘ σ⁻¹ ·) 1 (y a) {1} x → ∃ W, xFin W = x ∧
      ∃ h, ∀ w, (ratEmbed W ⟨y a, h⟩).1 w = diagTorus s (z a w ∘ σ w) := fun ⟨β, hy, hx, H⟩ ↦ by
    choose k hk a using fun w ↦ have ⟨_, _, _, K, S⟩ := exists_eigenbasis_diag_form hy w (σ w); S s
        (by simpa [↓K, ↓eval_interpolate_univ_node] using H w)
    use ⟨β, _, gram_mkAdelicGL hk hx⟩, rfl, by simp [mem_U, hy.2], fun w ↦ ?_
    ext : 2; erw [coe_mk]; simpa using! a w
  choose X e q _ using (F · 1 1 (o _))
  choose β _ hβ using fun a ↦
    (hasCutoff_count ((X a).Γf ⊓ (centralizer {⟨_, q a⟩}).map (embFin _))).1
  constructor; intro s V ι _ b he g
  have ω := hK.isCompact.smul h
  obtain ⟨v, p, T, hO⟩ := (measureReal_pos_of_isLevel K).ne', integral_indicator_const (μ :=
    volume) (1 : ℂ) hK.2.measurableSet, V.orbitalIntegral_unfold hB ω hh he.4
  choose _ P using hO.summable.subtype
  choose f W hU hc hf using fun σ : _ → Perm n ↦ exists_hasSignType_mul_iff (E := E) (fun _ : ℂ ↦
    (s ∘ σ⁻¹ ·)⁻¹) (by cases hE; simp [pow_add, Equiv.prod_comp, *]) _
  replace hU σ := by simpa using (hU σ · 0 1 (s ∘ σ⁻¹ ·))
  refine (eq_inv_mul_iff_mul_eq₀ (ofReal_ne_zero.2 v)).2 (.trans ?_ ((hasSum_mul_left_iff ?_).1
    (.congr_fun (((hasSum_sum fun σ _ ↦ hasSum_subtype_iff_indicator.1 (P _)).congr_fun fun c ↦
    ?_).unique (hO.mul_left _) ▸ hasSum_sum fun σ _ ↦ ((f σ).image _).hasSum_iff.2 (P _)) fun a ↦
    ((congrArg _ (funext fun σ ↦ ?_)).trans (by simpa [← pow_mul, Fintype.prod_sum, sum_mul,
    HCParam.compactForm, hE, mul_assoc, toHCParam] using congr((∏ w,
    $((Orbital.harish_chandra_degree_and_orbital ((g w).mono j)).2 _ (z a w).2)) * ∫ v, (β a
    v).toReal • ((h • K.carrier).indicator 1 (v⁻¹ * embFin _ ⟨_, q a⟩ * v))))).symm)).tsum_eq.symm)
  choose k hk using (V.exists_kernel_form he ·⁻¹ K)
  have H x v : ⟪k x, v⟫_ℂ = _ := .trans (by
    simp [inner_eq_petersson, petersson, hk, mul_assoc, v.1.2.rat_mul, ← tsum_mul_right]; rfl)
    ((integral_quotMeasure_tsum V.Γ
    (v.1.2.isBoundedMeasurable.integrable_mul_comp (.comp_mul_left (μ := volume) (he.1.2.mul_prod
    (.of_integral_ne_zero (p.trans_ne (by simpa)))) x⁻¹) id)).2.trans ((integral_mul_left_eq_self _
    x).symm.trans ((congrArg _ (funext fun y : G E s ↦ by simp +contextual [Set.indicator,
    ← mem_levelSpace_formRep_iff.1 v.2 y.2 _ (_, x.2), Prod.mul_def])).trans
    ((integral_prod_mul ..).trans (congr($(v.1.2.3 he.1.2) x * $p).trans (mul_comm ..))))))
  erw [← integral_finsetSum _ fun i _ ↦ (b i).1.2.memLp.star.integrable_mul
    (V.formRep _ h _).2.memLp, ← integral_const_mul]
  congr with x
  refine .mp ?_ congr(star $(b.sum_inner_mul_inner (k x) (k (x * (1, h)))))
  simp [*, geometricTerm, mul_assoc, mul_left_comm, ← mul_sum, Set.indicator,
    show ∀ x (v : levelSpace (V.formRep _) K), ⟪(k x).1, v.1⟫_ℂ = _ from H,
    ← Set.preimage_smul_inv, (hk ..).trans ((ofInjective _ V.ratEmbed_injective).tsum_eq _).symm]
  simpa using ⟨1, rfl⟩
  obtain ⟨Y, d, hy, ht⟩ := F a s σ ((hU ..).1 (o a))
  obtain ⟨b, l, h, -, hγ⟩ := V.exists_eq_move Y
  set j := U.conj b h
  have c z (h : y a * z = z * y a) : (u a)⁻¹ * toFinGL z * u a = Y.xFin⁻¹ * toFinGL z * Y.xFin := by
    simp [*, mul_assoc, (hc _ _ _ _ h).left_comm]
  simp [← r, -real_smul]
  erw [(hf _ _ _ ⟦_⟧).trans (frameClass_eq_iff.2 ⟨b, d ▸ (V.mem_U_one_iff_gram_eq gram_xFin).2 h,
    rfl⟩).symm, (T (j ⟨_,
    hy⟩)).2.2, IsCutoff.integral_orbitMeasure (β := (β a ·.2) ∘ (l⁻¹ * ·)) ⟨by fun_prop, fun g ↦ ?_⟩
    ((T _).1 _ ·.2), ← integral_fintype_prod_eq_prod, (by simp [Gf.val_ext_iff, coe_embFin,
    *] : (X a).embFin _ = Y.embFin ⟨_, hy⟩), ← integral_prod_mul, ← integral_mul_left_eq_self _ l]
  simp [typeKernel, geometricTerm, *, mul_assoc, -real_smul]; rfl
  erw [← hβ a (l⁻¹ * g).2, lintegral_count, lintegral_count, tsum_image (fun t ↦ β a (_ * (t *
    g)).2) V.ratEmbed_injective.injOn, (?_ : _ ⊓ _ = .map (Y.embFin.comp j.symm) (centralizer {j ⟨_,
    hy⟩})), tsum_image (β a <| · * _) (Y.fact_embFin_injective.1.comp j.symm.injective).injOn]
  simp [embFin, mul_assoc, (by simpa using hγ <| j.symm ·)]
  ext; simp [mem_centralizer_iff, ← map_mul, reindex_equiv j, coe_embFin, Gf.val_ext_iff]
  grind [mem_U_one_iff_gram_eq, gram_xFin, mem_U]
  simp [-Set.mem_image_equiv, Set.indicator, ← sum_filter]; by_contra! ⟨b, a⟩; apply b
  obtain ⟨γ, ⟨⟩⟩ := not_isEmpty_iff.1 (a <| @tsum_empty _ _ _ _ _ _ ·)
  have m := V.elliptic_of_integral_ne_zero hB ω hh he ((T _).2.2 ▸ a)
  choose _ d b J H using (exists_eigenbasis_diag_form m · 1)
  have X w := gram_inv_of_gram_eq (x :=
    V.x.map (evalInf w)) (by simpa [stdForm] using! congr($(V.3).map (evalInf w)))
  have y w i u : 0 < d w i * (u : ℤˣ) ↔ ite (0 < d w i) 1 (-1) = u := by
    have b := congrArg (fun M ↦ IsUnit M ∧ Mᴴ = M) (gram_mul_of_gram_eq (X w) (b w))
    fin_cases u <;> simp [Complex.lt_def, Complex.ext_iff, Pi.isUnit_iff, Pi.star_def,
      -coe_units_inv] at b ⊢; grind
  choose τ H using fun w ↦
    sylvester_law_of_inertia (gram_mul_of_gram_eq (X w) (H w _ (y w · _ |>.2 rfl)).choose_spec.1)
  norm_cast; simp_rw [← Fintype.card_subtype, ← card_fun]
  refine .symm (card_congr ((subtypeEquiv (.mulLeft τ) fun σ ↦ .trans ⟨fun ⟨_, a, o, e⟩ w ↦ ?_,
    fun H ↦ mul_inv_cancel_left (W σ γ 0) V.xFin ▸ ⟨_, γ, (hU σ ..).2 ⟨_, m, by simp [gram_xFin],
    H⟩, hf ..⟩⟩ (forall_congr' fun w ↦ (J w _).trans ((reindex_equiv (σ w)).1.trans
    (by simp [↓eval_interpolate_univ_node, funext_iff, *])))).trans subtypePiEquivPi))
  obtain ⟨⟨β, _, f, H⟩, z, e⟩ := (hU σ ..).1 o, frameClass_eq_iff.1 (e.symm.trans (hf ..))
  rw [← (z.map (Φ w)).isUnit.posDef_star_left_conjugate_iff, mul_assoc, mul_assoc,
    ← aeval_semiconj (x := a.1.map (Φ w))] <;> simp [← e.2, ← Matrix.map_mul]
  simpa [↓map_conjTranspose_mul_mul, mul_assoc] using! ((V.mem_U_one_iff_gram_eq f).1 e.1 ▸ H w :)
