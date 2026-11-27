/- GID: D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/FlenstedJensenInvariance
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/FlenstedJensenInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.DiscreteSeries.FlenstedJensen.FlenstedJensenInvariance. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/DiscreteSeries/FlenstedJensen/FlenstedJensenInvariance.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Rigidity.CasimirBound
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Holomorphic.MinorEquivariance
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series
(known result; see Lib.DiscreteSeries.FlenstedJensen.KTypeProjection).

This file: Flensted-Jensen integral is analytic and independent of the accretive splitting. -/


open Matrix MeasureTheory Finset ComplexConjugate ComplexOrder Norms.L2Operator ContinuousMap
variable {n} [Fintype n] (ε) {l h} (hg : @HasGap n _ ε l h) {s v : Matrix n n ℂ}
attribute [local simp] add_mul Fintype.sum_prod_type diagChar twoRho mem_blockDiagAlg le_of_lt
  conj_weightMinors BlockTriangular

lemma twoRho_lt_twoRho {l} {a b : n} (o : l a < l b) : twoRho l ⊤ a < twoRho l ⊤ b := by
  simpa [← sum_boole, ← sum_sub_distrib] using sum_lt_sum (by lia) (by grind)

@[fun_prop] lemma analyticAt_matrix_inv (h : s.det ≠ 0) : AnalyticAt ℂ (·⁻¹) s :=
  by simpa [nonsing_inv_eq_ringInverse] using! analyticAt_inverse (s.nonsingInvUnit h.isUnit)

lemma fderiv_eq_of_borel_equivariant {f o w D i j} (hf : HasFDerivAt (𝕜 := ℂ) f D s) (hY : o j ≤
  o i) (m : ε i = ε j) (c : _ → _) (h : ∀ᶠ x in nhds s, ∀ b ∈ blockDiagAlg ε, IsBorelMatrix (-o) b →
  x = c b → f x = diagChar w b * f s)
  (e : ∀ t : ℂ, s + t • v = c (1 + t • single i j 1) := by simp [mul_add, add_mul, -smul_single])
  : D v = ite (i = j) (w i : ℂ) 0 * f s := by simpa [single, ite_and, comm] using
  ((hf.hasLineDerivAt v).unique (((HasDerivAt.fun_finsetProd fun _ _ ↦ (hasDerivAt_zpow _ _ (by
  simp)).comp 0 ((hasDerivAt_mul_const _).const_add _)).mul_const _).congr_of_eventuallyEq (.mp
  (ContinuousAt.eventually_ne (by fun_prop) (by simp)) (.mono (Continuous.tendsto' (by fun_prop) _ s
  (by simp) h) fun t ↦ (· _ (by simp; grind) ⟨by simp; grind, ·⟩ (e t))))))

variable {ε} (g : USign ε)

lemma isAnalyticFamily_flenstedJensen (l : HCParam ε) {a} (h : AnalyticAt ℂ a g.1.1) (e : a g =
  blockDiagPart ε g) : IsAnalyticFamily (fun x (k : maxCompactU
  ε) ↦ weightMinors l.lowestKType (a x * k) * conj (weightMinors l.lowestKType k) / weightMinors
  (-paramAddRho l) (k.1.1.1ᴴ * ((a x)⁻¹ * x) * k)) g :=
  by simp; apply IsAnalyticFamily.of_analyticAt (.prodMk ..) fun (x, y, z) ↦ weightMinors _ (a x *
  y) * weightMinors _ z / weightMinors _ (z * ((a x)⁻¹ * x) * y) <;> fun_prop (disch := simp_all)

/-- For every integer vector l = 2λ, the function ψ_λ on complex n×n matrices is complex
analytic at every point g of U(diag ε). -/
lemma HCParam.analyticAt_dsCoeff : AnalyticAt ℂ l.dsCoeff g :=
  ((isAnalyticFamily_flenstedJensen g l (by fun_prop) rfl).analyticAt_integral _).div_const

include hg

grind_pattern twoRho_lt_twoRho => paramAddRho l a, paramAddRho l b

lemma HCParam.HasGap.paramAddRho_lt_iff {i j} : paramAddRho l i < paramAddRho l j ↔
  l i < l j := by grind [paramAddRho, HasGap]

lemma HCParam.HasGap.isKDominant_neg_paramAddRho :
  IsKDominant 1 l (-paramAddRho l) := by simp_all [IsKDominant, hg.paramAddRho_lt_iff]

/-- If l = 2λ is a parameter of gap h, then Λ = λ + ρ − 2ρ_c is K-dominant: Λ_j ≤ Λ_i whenever
ε_i = ε_j and l_i > l_j. -/
lemma HCParam.HasGap.isKDominant_lowestKType : IsKDominant ε (-l) l.lowestKType := fun i j e o ↦ by
  suffices 2 * l.lowestKType j - l j - (2 * l.lowestKType i - l i) ≤ #(Ico (l j) (l i)) by aesop
  grw [← card_le_card_of_injOn (fun (i, (j : Fin 2)) ↦ l i - j) (mem_filter_univ · |>.1) fun _ ↦ by
    grind [HasGap, Fin.ext_iff]]
  simp_all [-sum_add_distrib, two_mul_lowestKType, ← add_sub, ← sum_boole,
    ← sum_sub_distrib]; gcongr; lia

/-- Let l be a parameter of some gap (hypothesis `hg`), a and b block diagonal for ε with a⁻¹g and
b⁻¹g of positive definite hermitian part. Then Ξ(b, b⁻¹g) = Ξ(a, a⁻¹g), Ξ = `flenstedJensen` (for
any matrix g). -/
lemma flenstedJensen_eq_of_accretive {g a b} (ha : a ∈ blockDiagAlg ε) (h1 :
  (a⁻¹ * g).IsAccretive) (hb : b ∈ blockDiagAlg ε) (h2 : (b⁻¹ * g).IsAccretive) :
  l.flenstedJensen b (b⁻¹ * g) = l.flenstedJensen a (a⁻¹ * g) := by
  have x s (F : Matrix n n ℂ → _ → ℂ) (h : ∀ k : maxCompactU ε, AnalyticAt ℂ F.uncurry (s,
    k.1.1.1) := by fun_prop (disch := simp [*, maxCompactU.coe_inv])) : ∃ d, HasFDerivAt (∫ k,
    F · k ∂haarK ε) (strongIntegral (haarK ε) (evalCLM ℂ) ∘L d) s ∧ ∀ k, HasFDerivAt (F · k.1)
    (evalCLM ℂ k ∘L d) s := have ⟨_, ⟨_, h⟩, e⟩ := IsAnalyticFamily.of_analyticAt (by fun_prop) _ h
    ⟨_, by constructor <;> intros <;> exact ((ContinuousLinearMap.hasFDerivAt _).comp _
      h.hasFDerivAt).congr_of_eventuallyEq (e.mono (by simp_all [strongIntegral_eval]))⟩
  obtain ⟨H, I, _, _, h1, h2⟩ := @IsAccretive.det_ne_zero_and_inv_mul (k := g), hg.neg.1,
    hg.isKDominant_lowestKType, (by simp_all [IsKDominant, hg.paramAddRho_lt_iff] :
    IsKDominant ε (-l) (paramAddRho l)), h1.det_ne_zero_and_inv_mul, h2.det_ne_zero_and_inv_mul
  let Φ a y := weightMinors l.lowestKType (a * y) * weightMinors l.lowestKType y⁻¹ / weightMinors
    (paramAddRho l) (y⁻¹ * (g⁻¹ * a) * y)
  simp [flenstedJensen, weightMinors_neg, *, ← maxCompactU.coe_inv, ← mul_assoc _ (_ * _)]; congr 1
  refine (LipschitzOnWith.zero_iff _).1 ((convex_iff_forall_pos.2 fun _ x _ y _ _ a b _ ↦ by
    simpa [IsAccretive, mul_add, add_add_add_comm] using! (x.smul a).add (y.smul b) :
    Convex ℝ {a : blockDiagAlg ε |
    (g⁻¹ * a).IsAccretive}).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (f' := 0) (fun a (h :
    IsAccretive _) ↦ (x a.1 Φ).elim fun d ⟨f, e⟩ ↦ (f.comp_hasFDerivWithinAt a (blockDiagAlg
    ε).toSubmodule.subtypeL.hasFDerivWithinAt).congr_fderiv ?_) (by simp)) ⟨_, hb⟩ h2.2 ⟨_, ha⟩ h1.2
  ext ⟨X, m⟩; let s : Finset _ := {(i, j) | ε i = ε j ∧ l i < l j}
  let P := fun (i, j) y ↦ Φ a y * (entryLinearMap ℂ ℂ i j).toContinuousLinearMap ((a * y)⁻¹ * X * y)
  choose D G E using (x 1 fun x y ↦ P · (y * x))
  simp; erw [(_ : d X = ∑ p ∈ s, D p (single p.1 p.2 1)), map_sum, sum_eq_zero fun p o ↦
    fderiv_eq_on_blockDiagAlg (G p) 0 (fun _ h ↦ funext (integral_mul_right_eq_self
    (μ := haarK ε) (P p ·) ⟨_, h ·⟩) ▸ deriv_const ..) (by simp; grind)]
  ext k; simp; have y := mem_blockDiagAlg.1 (mul_mem (mul_mem (blockDiagAlg.inv_mem
    (mul_mem a.2 (mem_maxCompactU.1 k.2))) m) (mem_maxCompactU.1 k.2)); set Y := _ * X * _
  let c := LinearMap.mulLeftRight ℂ (a.1 * k, k⁻¹)
  have h4 i j (o : (i, j) ∈ s) := ((E (i, j) k).hasLineDerivAt (single i j 1)).unique
    (((((hasDerivAt_id 0).mul ((hasDerivAt_mul_const (Y j i)).const_sub (Y i i - Y j j))).add_const
    (Y i j)).mul ((e k).hasLineDerivAt (c (single i j 1)))).congr_of_eventuallyEq (
    .of_forall fun t ↦ by
    have ⟨q, _⟩ : (1 + single i j t) * (1 - single i j t) = 1 ∧ ∀ x, ¬(i = x ∧ j = x) := by
      simp [mul_sub, (by grind : j ≠ i)]
    simp +zetaDelta [mul_assoc, *, det_ne_zero_of_right_inverse q, inv_eq_right_inv q,
      IsKDominant.weightMinors_oppBorel_mul
      (ε := ε) I _ _ (by simp; grind) ⟨by simp; grind, det_ne_zero_of_left_inverse q⟩]
    simp [mul_add, sub_mul]; simp [← mul_assoc, ← mul_smul_comm]; ring))
  rw [sum_congr rfl (h4 ·.1 _), (by simp +zetaDelta [mul_assoc, *, ← matrix_eq_sum_single] : X =
    c (∑ ⟨i, j⟩ : n × n, Y i j • single i j 1)), map_sum, map_sum, ContinuousMap.sum_apply,
    ← s.sum_compl_add_sum]
  simp +contextual [sub_mul, -smul_single, s, sum_filter, ↓not_and_or, ite_or, by
    simpa using fun i j (o : l j ≤ l i) q ↦
      fderiv_eq_of_borel_equivariant ε (w := l.lowestKType - paramAddRho l) (v := c (single i j 1))
      (e k) o q c (by simp +contextual +zetaDelta [← mul_assoc, zpow_sub₀,
      IsBorelMatrix.diag_ne_zero I, *, field, IsKDominant.weightMinors_mul_borel (ε := ε) I])
      (by simp [c, ↓map_add, ↓map_smul]), y, lowestKType, mul_sub]
  nth_rw 3 [sum_comm]; simp [sum_ite, eq_comm, mul_left_comm (Y ..)]

/-- Independence of the splitting: for a parameter l = 2λ of some gap, g in U(diag ε) and a
block diagonal matrix a such that a⁻¹g has positive definite hermitian part, ψ_λ(g) is the
normalised integral `HCParam.flenstedJensen` at (a, a⁻¹g). -/
lemma dsCoeff_eq_flenstedJensen {g : USign ε} {a} (ha : a ∈ blockDiagAlg ε) (h :
  (a⁻¹ * g).IsAccretive) : l.dsCoeff g = l.flenstedJensen a (a⁻¹ * g) :=
  flenstedJensen_eq_of_accretive hg ha h (blockDiagPart_mem _) (by simp)
