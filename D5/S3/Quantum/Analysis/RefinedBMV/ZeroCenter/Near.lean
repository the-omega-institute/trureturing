/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Near
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The real small-gap curvature lower expression, using the positive regularizing series. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Curvature
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Regularized
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.PhiSeries
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.EvenMoments

/-! Reduction of the small-gap curvature to a polynomial and two series jets. -/

namespace RefinedBMV.FourSpectrumLift

open Filter CurvatureJet
open scoped Topology

noncomputable section

private def smallRadicandJet (h c : ℝ) : CurvatureJet ℝ :=
  CurvatureJet.scale (27 * (1+h) * (1+2*h) * (1+3*h))
    ⟨zeroCenterRegularizingDerivative h 0 c, zeroCenterRegularizingDerivative h 1 c,
      zeroCenterRegularizingDerivative h 2 c / 2⟩

private def smallPhiJet (h c : ℝ) : CurvatureJet ℝ :=
  ⟨phi (3*h*c), (3*h) * deriv phi (3*h*c),
    (3*h)^2 * deriv (deriv phi) (3*h*c) / 2⟩

private def smallCorrectionJet (h c : ℝ) : CurvatureJet ℝ :=
  let rad := smallRadicandJet h c
  CurvatureJet.quot (CurvatureJet.sqrtFrom rad (Real.sqrt rad.value))
    (CurvatureJet.scale (3*(1+h)) (smallPhiJet h c))

private theorem smallRadicandJet_hasJet {h c : ℝ} (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hc : |c| < 2) : IsJet (smallRadicandJet h) c := by
  have hjet : IsJet (fun x ↦ ⟨zeroCenterRegularizingDerivative h 0 x,
      zeroCenterRegularizingDerivative h 1 x, zeroCenterRegularizingDerivative h 2 x / 2⟩) c := by
    refine ⟨hasDerivAt_zeroCenterRegularizingDerivative hh hh₁ hc 0, ?_⟩
    change HasDerivAt (zeroCenterRegularizingDerivative h 1)
      (2 * (zeroCenterRegularizingDerivative h 2 c / 2)) c
    convert hasDerivAt_zeroCenterRegularizingDerivative hh hh₁ hc 1 using 1
    ring
  exact hjet.scale _

private theorem smallPhiJet_hasJet {h c : ℝ} (hh : 0 < h) (hc : 0 < c) :
    IsJet (smallPhiJet h) c := by
  let k : ℝ := 3*h
  have ht : k*c ≠ 0 := by dsimp [k]; positivity
  have hk : HasDerivAt (fun x ↦ k*x) k c := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id c).const_mul k
  have h0 := hasDerivAt_phi ht
  have h1 := hasDerivAt_deriv_phi ht
  change HasDerivAt (fun x ↦ phi (k*x)) (k * deriv phi (k*c)) c ∧
    HasDerivAt (fun x ↦ k * deriv phi (k*x))
      (2 * (k^2 * deriv (deriv phi) (k*c) / 2)) c
  rw [h0.deriv, h1.deriv]
  refine ⟨?_, ?_⟩
  · convert h0.comp c hk using 1 <;> try rfl
    ring
  · convert (h1.comp c hk).const_mul k using 1 <;> try rfl
    ring

private theorem smallRadicandJet_pos {h c : ℝ} (hh : 0 < h) (hc : 0 < c) :
    0 < (smallRadicandJet h c).value := by
  let M : ℝ := 27 * (1+h) * (1+2*h) * (1+3*h)
  have hM : 0 < M := by dsimp [M]; positivity
  change 0 < M * zeroCenterRegularizingDerivative h 0 c
  rw [zeroCenterRegularizingDerivative_zero]
  have hd : zeroCenterRegularizingSeries h c =
      (Real.exp ((3+6*h)*c) * rationalizedRadicand c h) / (M*c^4) :=
    (hasSum_regularizing_series hc hh).tsum_eq
  rw [hd]
  apply mul_pos hM (div_pos _ (by positivity))
  exact (show 0 < M*c^4/24 by positivity).trans_le (rationalized_radicand_lower hc.le hh)

private theorem smallPhiJet_pos {h c : ℝ} (hh : 0 < h) (hc : 0 < c) :
    0 < (smallPhiJet h c).value := by
  have ht : 0 < 3*h*c := by positivity
  change 0 < phi (3*h*c)
  rw [phi, ite_eq_right ht.ne']
  exact div_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)) ht

private theorem smallCorrectionJet_hasJet {h c : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (hc : 0 < c) (hc₁ : c < 2) : IsJet (smallCorrectionJet h) c := by
  have hrad := smallRadicandJet_hasJet hh.le hh₁ (by rwa [abs_of_pos hc])
  have hp := smallPhiJet_hasJet hh hc
  have hden : 0 < (CurvatureJet.scale (3*(1+h)) (smallPhiJet h c)).value :=
    mul_pos (by positivity) (smallPhiJet_pos hh hc)
  exact (hrad.sqrtFrom (smallRadicandJet_pos hh hc)).quot (hp.scale _) hden.ne'

private theorem smallCorrectionJet_value (h c : ℝ) :
    (smallCorrectionJet h c).value = zeroCenterRegularizedCorrection h c := by
  unfold smallCorrectionJet zeroCenterRegularizedCorrection
  simp only [CurvatureJet.quot, CurvatureJet.sqrtFrom, smallRadicandJet, smallPhiJet,
    CurvatureJet.scale, zeroCenterRegularizingDerivative_zero]
  rfl

private theorem geometricSum_contDiff (p : ℕ) : ContDiff ℝ 2 (zeroCenterGeometricSum p) := by
  unfold zeroCenterGeometricSum
  apply ContDiff.div
  · fun_prop
  · fun_prop
  · intro x
    positivity

/-- Curvature lower expression on small positive gaps. The six series
arguments are the value and first two ordinary derivatives at their arguments. -/
def zeroCenterNearExpression (c h B B₁ B₂ P P₁ P₂ root : ℝ) : ℝ :=
  let M := 27 * (1+h) * (1+2*h) * (1+3*h)
  let rad := CurvatureJet.scale M (⟨B,B₁,B₂/2⟩ : CurvatureJet ℝ)
  let den := CurvatureJet.scale (3*(1+h)) (⟨P,(3*h)*P₁,(3*h)^2*P₂/2⟩ : CurvatureJet ℝ)
  let v := CurvatureJet.quot (CurvatureJet.sqrtFrom rad root) den
  zeroCenterEvenMomentLower c h - (2*v.first + 2*c*v.second)

/-- The small-gap expression bounds the second derivative of the actual profile. -/
theorem zeroCenterNearExpression_le_deriv2 {p : ℕ} (hp : 0 < p) {c : ℝ}
    (hc : 0 < c) (hc₁ : c < 2) :
    let h : ℝ := 1/p
    let t := 3*h*c
    let B := zeroCenterRegularizingDerivative h 0 c
    let root := Real.sqrt (27 * (1+h) * (1+2*h) * (1+3*h) * B)
    zeroCenterNearExpression c h B (zeroCenterRegularizingDerivative h 1 c)
      (zeroCenterRegularizingDerivative h 2 c) (phi t) (deriv phi t) (deriv (deriv phi) t) root ≤
      deriv^[2] (zeroProfile p) c := by
  let h : ℝ := 1/p
  let A := zeroCenterGeometricSum p
  let v := smallCorrectionJet h
  have hp' : 1 ≤ (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hh₁ : h ≤ 1 := (div_le_one (by positivity : 0 < (p : ℝ))).mpr hp'
  have hA := geometricSum_contDiff p
  have hA₁ : Differentiable ℝ A := hA.differentiable (by decide)
  have hA₂ : Differentiable ℝ (deriv A) := hA.differentiable_deriv_two
  have hV (x : ℝ) (hx : 0 < x) (hx' : x < 2) : IsJet v x :=
    smallCorrectionJet_hasJet hh hh₁ hx hx'
  have hu : ∀ᶠ x : ℝ in 𝓝 c, x ∈ Set.Ioo 0 2 := Ioo_mem_nhds hc hc₁
  have hProfile : zeroProfile p =ᶠ[𝓝 c] (fun x ↦ A x - x * (v x).value) := by
    filter_upwards [hu] with x hx
    rw [zeroProfile_eq_regularized hp hx.1, smallCorrectionJet_value]
    rfl
  have hFirst : deriv (zeroProfile p) =ᶠ[𝓝 c]
      (fun x ↦ deriv A x - ((v x).value + x*(v x).first)) := by
    filter_upwards [hu, hProfile.deriv] with x hx hx'
    rw [hx']
    convert (((hA₁ x).hasDerivAt).sub ((hasDerivAt_id x).mul (hV x hx.1 hx.2).1)).deriv
      using 1 <;> try rfl
    simp only [id_eq, one_mul]
  have hSecond : deriv^[2] (zeroProfile p) c =
      deriv^[2] A c - (2*(v c).first + 2*c*(v c).second) := by
    change deriv (deriv (zeroProfile p)) c =
      deriv (deriv A) c - (2*(v c).first + 2*c*(v c).second)
    rw [hFirst.deriv_eq]
    convert (((hA₂ c).hasDerivAt).sub ((hV c hc hc₁).1.add
      ((hasDerivAt_id c).mul (hV c hc hc₁).2))).deriv using 1 <;> try rfl
    simp only [id_eq, one_mul]
    ring
  rw [hSecond]
  exact sub_le_sub_right (zeroCenterEvenMomentLower_le_deriv2 hp c) _

#print axioms zeroCenterNearExpression_le_deriv2

private def regularizingPartial (h c : ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (81-k), regularizingDerivativeCoefficient h k n * c^n

private theorem regularizingPartial_mono {h h' c c' : ℝ}
    (hh₀ : 0 ≤ h) (hh : h ≤ h') (hc₀ : 0 ≤ c) (hc : c ≤ c') (k : ℕ) :
    regularizingPartial h c k ≤ regularizingPartial h' c' k := by
  unfold regularizingPartial
  apply Finset.sum_le_sum
  intro n _
  have hcoef := regularizingCoefficient_mono hh₀ hh (n+k)
  have h₀ := regularizingCoefficient_nonneg hh₀ (n+k)
  have h₁ : 0 ≤ ((n+k).factorial : ℝ) / (n.factorial : ℝ) := by positivity
  dsimp [regularizingDerivativeCoefficient]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hcoef h₁) (pow_le_pow_left₀ hc₀ hc _)
    (pow_nonneg hc₀ _) (mul_nonneg h₁ (h₀.trans hcoef))

/-- Exact endpoint coefficients are supplied by the rational recurrence. -/
structure RegularizingEndpointTable (h : ℚ) where
  row : ℕ → ℕ → ℚ
  base : ∀ n ≤ 80, row 0 n = if n = 0 then 1 else 0
  zero : ∀ i : Fin 6, row (i.val+1) 0 = row i.val 0
  next : ∀ (i : Fin 6) (n : ℕ), n < 80 →
    row (i.val+1) (n+1) = row i.val (n+1) + regularizingKnotsRat h i * row (i.val+1) n

private def endpointCoefficient {h : ℚ} (T : RegularizingEndpointTable h) (n : ℕ) : ℚ :=
  (T.row 5 n + (4*h+8/3) * (match n with | 0 => 0 | j+1 => T.row 6 j)) /
    (n+4).factorial

private theorem endpointCoefficient_sound {h : ℚ} (T : RegularizingEndpointTable h)
    {n : ℕ} (hn : n ≤ 80) :
    (endpointCoefficient T n : ℝ) = regularizingCoefficient (h : ℝ) n := by
  cases n <;> exact regularizingCoefficient_eq_of_recurrence h 80 T.row T.base T.zero T.next hn

def endpointPartial {h : ℚ} (T : RegularizingEndpointTable h) (c : ℚ) (k : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (81-k),
    (((n+k).factorial : ℚ) / n.factorial) * endpointCoefficient T (n+k) * c^n

private theorem endpointPartial_sound {h : ℚ} (T : RegularizingEndpointTable h)
    (c : ℚ) (k : ℕ) :
    (endpointPartial T c k : ℝ) = regularizingPartial (h : ℝ) (c : ℝ) k := by
  unfold endpointPartial regularizingPartial
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hm : n+k ≤ 80 := by have := Finset.mem_range.mp hn; omega
  push_cast
  rw [endpointCoefficient_sound T hm]
  rfl

/-- Enclose the factor and its first two derivatives across a real box using
two exact endpoint tables and the previously proved weighted remainder. -/
theorem regularizingDerivative_enclosed {hLo hHi cLo cHi : ℚ}
    (Tlo : RegularizingEndpointTable hLo) (Thi : RegularizingEndpointTable hHi)
    {c h : ℝ} (h₀ : 0 ≤ (hLo : ℝ)) (hLo' : (hLo : ℝ) ≤ h) (hHi' : h ≤ (hHi : ℝ))
    (h₁ : h ≤ 1) (c₀ : 0 ≤ (cLo : ℝ)) (cLo' : (cLo : ℝ) ≤ c)
    (cHi' : c ≤ (cHi : ℝ)) (c₁ : c ≤ 1) {k : ℕ} (hk : k ≤ 2) :
    (endpointPartial Tlo cLo k : ℝ) ≤ zeroCenterRegularizingDerivative h k c ∧
    zeroCenterRegularizingDerivative h k c ≤
      ((endpointPartial Thi cHi k + (2 : ℚ)⁻¹ ^ 100 : ℚ) : ℝ) := by
  have hh := h₀.trans hLo'
  have hc := c₀.trans cLo'
  have he := zeroCenterRegularizingDerivative_bounds hh h₁ hc c₁ hk
  rw [Rat.cast_add, endpointPartial_sound, endpointPartial_sound]
  push_cast
  exact ⟨(regularizingPartial_mono h₀ hLo' c₀ cLo' k).trans he.1,
    he.2.le.trans (add_le_add (regularizingPartial_mono hh hHi' hc cHi' k) le_rfl)⟩

def phiPartialRat (x : ℚ) (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range 32, x^j / ((j.factorial : ℚ) * ((j : ℚ) + (k : ℚ) + 1))

private theorem phiPartialRat_sound (x : ℚ) (k : ℕ) :
    (phiPartialRat x k : ℝ) = phiSeriesPartial (x : ℝ) k := by
  unfold phiPartialRat phiSeriesPartial phiSeriesTerm
  push_cast
  rfl

private theorem phiPartial_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (k : ℕ) :
    phiSeriesPartial x k ≤ phiSeriesPartial y k := by
  apply Finset.sum_le_sum
  intro n _
  unfold phiSeriesTerm
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy _) (by positivity)

/-- Both endpoint series enclose the actual quotient and both derivative values. -/
theorem phi_enclosed {xLo xHi : ℚ} {x : ℝ} (h₀ : 0 ≤ (xLo : ℝ))
    (hl : (xLo : ℝ) ≤ x) (hu : x ≤ (xHi : ℝ)) (hx : 0 < x) (hx' : x ≤ 9/32) :
    ∀ k : Fin 3,
      let p : Fin 3 → ℝ := ![phi x, deriv phi x, deriv (deriv phi) x]
      (phiPartialRat xLo k : ℝ) ≤ p k ∧ p k ≤
        ((phiPartialRat xHi k + 1 / (2 : ℚ)^128 : ℚ) : ℝ) := by
  have H (k : ℕ) (f : ℝ)
      (hb : phiSeriesPartial x k ≤ f ∧ f ≤ phiSeriesPartial x k + 1/(2 : ℝ)^128) :
      (phiPartialRat xLo k : ℝ) ≤ f ∧ f ≤
        ((phiPartialRat xHi k + 1 / (2 : ℚ)^128 : ℚ) : ℝ) := by
    rw [Rat.cast_add, phiPartialRat_sound, phiPartialRat_sound]
    push_cast
    exact ⟨(phiPartial_mono h₀ hl _).trans hb.1,
      hb.2.trans (add_le_add (phiPartial_mono hx.le hu _) le_rfl)⟩
  obtain ⟨h₀, h₁, h₂⟩ := phiSeries_bounds hx hx'
  intro k
  fin_cases k
  · exact H _ _ h₀
  · exact H _ _ h₁
  · exact H _ _ h₂

#print axioms regularizingDerivative_enclosed
#print axioms phi_enclosed

private def coefficientRowStep (d : ℚ) (previous : List ℚ) : List ℚ :=
  (previous.scanl (fun old next ↦ next + d*old) 0).tail

private def coefficientRows (h : ℚ) : ℕ → List ℚ
  | 0 => List.ofFn (fun i : Fin 81 ↦ if i.val = 0 then 1 else 0)
  | i+1 => coefficientRowStep (regularizingKnotsRat h (Fin.ofNat 6 i)) (coefficientRows h i)

private def coefficientCell (h : ℚ) (i n : ℕ) : ℚ :=
  ((coefficientRows h i)[n]?).getD 0

private theorem coefficientRows_length (h : ℚ) (i : ℕ) :
    (coefficientRows h i).length = 81 := by
  induction i with
  | zero => simp [coefficientRows]
  | succ i ih => simp [coefficientRows, coefficientRowStep, ih]

private theorem coefficientRowStep_cell (d : ℚ) (l : List ℚ) {i : ℕ}
    (hi : i < l.length) :
    ((coefficientRowStep d l)[i]?).getD 0 =
      (l.take (i+1)).foldl (fun old next ↦ next + d*old) 0 := by
  simp [coefficientRowStep, List.getElem?_tail, List.getElem?_scanl, Nat.succ_le_of_lt hi]

/-- The endpoint recurrence can also be computed, with its recurrence proved
for all inputs independently of the certificate producer. -/
def regularizingEndpointTable (h : ℚ) : RegularizingEndpointTable h where
  row := coefficientCell h
  base := by
    intro n hn
    have hlt : n < 81 := by omega
    unfold coefficientCell
    rw [coefficientRows, List.getElem?_ofFn, dif_pos hlt]
    rfl
  zero := by
    intro i
    have hn : 0 < (coefficientRows h i.val).length := by
      rw [coefficientRows_length]
      decide
    unfold coefficientCell
    rw [coefficientRows, coefficientRowStep_cell _ _ hn, List.take_succ_eq_append_getElem hn]
    have he := getElem?_pos (coefficientRows h i.val) 0 hn
    simp [he]
  next := by
    intro i n hn
    have hn' : n < (coefficientRows h i.val).length := by
      rw [coefficientRows_length]
      omega
    have hn'' : n+1 < (coefficientRows h i.val).length := by
      rw [coefficientRows_length]
      omega
    unfold coefficientCell
    rw [coefficientRows, coefficientRowStep_cell _ _ hn'',
      coefficientRowStep_cell _ _ hn',
      List.take_succ_eq_append_getElem hn'', List.foldl_append]
    have he := getElem?_pos (coefficientRows h i.val) (n+1) hn''
    simp [he, Fin.ofNat_eq_cast]

end
end RefinedBMV.FourSpectrumLift
