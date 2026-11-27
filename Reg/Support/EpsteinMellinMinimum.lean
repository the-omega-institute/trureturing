import Reg.Support.PlanarThetaFoundation
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Fourier.EpsteinMellinMinimum

/-! Families of Epstein terms, Mellin weights and lattice zeta values. -/

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open MeasureTheory Set
open scoped BigOperators

namespace Reg.Support.EpsteinMellinMinimum
noncomputable section

abbrev termSignature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, ℝ
  State _ := ℤ × ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def termActual : Realization termSignature :=
  realize termSignature (fun _ p v => (Q p.2.1 p.2.2 v) ^ (-p.1)) (fun e => nomatch e)

def termRejected : Realization termSignature :=
  realize termSignature (fun _ _ _ => 1) (fun e => nomatch e)

def summableArena : Arena where
  signature := termSignature
  Law R := ∀ {s x y : ℝ}, 1 < s → 0 < y →
    Summable (fun v : ℤ × ℤ => R.readout () ⟨s, x, y⟩ v)

private theorem summable_bridge : (type_of% (@epstein_summable)) ↔
    summableArena.Law termActual := Iff.rfl

private theorem term_dependence : ObservationalDependence termSignature termActual := by
  intro i
  refine ⟨⟨2, 0, 1⟩, (0, 0), (1, 0), ?_⟩
  norm_num [termActual, realize, Q]

private theorem summable_rejected : ¬ summableArena.Law termRejected := by
  intro h
  have h1 := h (s := 2) (x := 0) (y := 1) (by norm_num) (by norm_num)
  simp [termRejected, realize, summable_const_iff] at h1

def summableRegistration : Registration summableArena (type_of% (@epstein_summable)) where
  actual := termActual
  bridge := summable_bridge
  variation := ⟨@epstein_summable, termRejected, summable_rejected⟩
  sensitivity := ⟨fun i => ⟨termRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, summable_rejected⟩, fun e => nomatch e⟩
  dependence := term_dependence

abbrev mellinSignature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def mellinActual : Realization mellinSignature :=
  realize mellinSignature (fun _ p t => (F t p.2.1 p.2.2 - 1) * t ^ (p.1 - 1))
    (fun e => nomatch e)

def mellinRejected : Realization mellinSignature :=
  realize mellinSignature (fun _ _ _ => 1) (fun e => nomatch e)

def integrableArena : Arena where
  signature := mellinSignature
  Law R := ∀ {s x y : ℝ}, 1 < s → 0 < y →
    IntegrableOn (fun t => R.readout () ⟨s, x, y⟩ t) (Ioi 0)

private theorem integrable_bridge : (type_of% (@epstein_mellin_integrable)) ↔
    integrableArena.Law mellinActual := Iff.rfl

private theorem mellin_dependence : ObservationalDependence mellinSignature mellinActual := by
  intro i
  refine ⟨⟨2, 0, 1⟩, 0, 1, ?_⟩
  change (F 0 0 1 - 1) * (0 : ℝ) ^ (2 - 1 : ℝ) ≠
    (F 1 0 1 - 1) * (1 : ℝ) ^ (2 - 1 : ℝ)
  norm_num only [show (2 - 1 : ℝ) = 1 by norm_num, Real.rpow_one, mul_zero, mul_one]
  have hF : 1 < F 1 0 1 := by
    have hsum := summable 1 0 (y := 1) (by norm_num) (by norm_num)
    have h := Summable.tsum_lt_tsum (i := (1, 0))
      (f := fun v : ℤ × ℤ => if v = (0, 0) then 1 else 0)
      (g := fun v : ℤ × ℤ => Real.exp (-Real.pi * 1 * Q 0 1 v))
      (fun v => by
        by_cases hv : v = (0, 0)
        · subst v
          simp [Q]
        · dsimp only
          rw [if_neg hv]
          positivity)
      (by simp only [if_neg (by decide : ((1, 0) : ℤ × ℤ) ≠ (0, 0))]; positivity)
      (hasSum_ite_eq (0, 0) (1 : ℝ)).summable hsum
    have hsingle : (∑' v : ℤ × ℤ, if v = (0, 0) then (1 : ℝ) else 0) = 1 := by
      simpa only [eq_comm] using (hasSum_ite_eq (0, 0) (1 : ℝ)).tsum_eq
    simpa only [hsingle, F] using h
  exact ne_of_lt (by linarith)

private theorem integrable_rejected : ¬ integrableArena.Law mellinRejected := by
  intro h
  have h1 := h (s := 2) (x := 0) (y := 1) (by norm_num) (by norm_num)
  simp [mellinRejected, realize, integrableOn_const_iff, Real.volume_Ioi] at h1

def integrableRegistration : Registration integrableArena
    (type_of% (@epstein_mellin_integrable)) where
  actual := mellinActual
  bridge := integrable_bridge
  variation := ⟨@epstein_mellin_integrable, mellinRejected, integrable_rejected⟩
  sensitivity := ⟨fun i => ⟨mellinRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, integrable_rejected⟩, fun e => nomatch e⟩
  dependence := mellin_dependence

abbrev zetaSignature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def zetaActual : Realization zetaSignature :=
  realize zetaSignature (fun _ p y => epstein p.1 p.2 y) (fun e => nomatch e)

def zetaRejected : Realization zetaSignature :=
  realize zetaSignature (fun _ _ _ => 0) (fun e => nomatch e)

def formulaArena : Arena where
  signature := zetaSignature
  Law R := ∀ {s x y : ℝ}, 1 < s → 0 < y →
    R.readout () ⟨s, x⟩ y = (Real.pi ^ s / Real.Gamma s) *
      ∫ t : ℝ in Ioi 0, (F t x y - 1) * t ^ (s - 1)

private theorem formula_bridge : (type_of% (@epstein_mellin)) ↔
    formulaArena.Law zetaActual := Iff.rfl

private theorem zeta_pos : 0 < epstein 2 0 1 := by
  unfold epstein
  apply (epstein_summable (s := 2) (x := 0) (y := 1)
    (by norm_num) (by norm_num)).tsum_pos
      (fun v => Real.rpow_nonneg (by unfold Q; positivity) _) (1, 0)
  norm_num [Q]

private theorem zeta_dependence : ObservationalDependence zetaSignature zetaActual := by
  intro i
  refine ⟨⟨2, 0⟩, 0, 1, ?_⟩
  change epstein 2 0 0 ≠ epstein 2 0 1
  have hz : epstein 2 0 0 = 0 := by simp [epstein, Q]
  rw [hz]
  exact ne_of_lt zeta_pos

private theorem formula_rejected : ¬ formulaArena.Law zetaRejected := by
  intro h
  have h1 := h (s := 2) (x := 0) (y := 1) (by norm_num) (by norm_num)
  have h2 := epstein_mellin (s := 2) (x := 0) (y := 1) (by norm_num) (by norm_num)
  change 0 = _ at h1
  linarith [zeta_pos]

def formulaRegistration : Registration formulaArena (type_of% (@epstein_mellin)) where
  actual := zetaActual
  bridge := formula_bridge
  variation := ⟨@epstein_mellin, zetaRejected, formula_rejected⟩
  sensitivity := ⟨fun i => ⟨zetaRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, formula_rejected⟩, fun e => nomatch e⟩
  dependence := zeta_dependence

def minimumArena : Arena where
  signature := zetaSignature
  Law R := ∀ {s x y : ℝ}, 1 < s → 0 ≤ x → x ≤ 1 / 2 → Real.sqrt 3 / 2 ≤ y →
    epstein s (1 / 2) (Real.sqrt 3 / 2) ≤ R.readout () ⟨s, x⟩ y ∧
      (R.readout () ⟨s, x⟩ y = epstein s (1 / 2) (Real.sqrt 3 / 2) ↔
        x = 1 / 2 ∧ y = Real.sqrt 3 / 2)

private theorem minimum_bridge : (type_of% (@reduced_epstein_minimum)) ↔
    minimumArena.Law zetaActual := Iff.rfl

def minimumRejected : Realization zetaSignature :=
  realize zetaSignature (fun _ p _ => epstein p.1 (1 / 2) (Real.sqrt 3 / 2) + 1)
    (fun e => nomatch e)

private theorem minimum_rejected : ¬ minimumArena.Law minimumRejected := by
  intro h
  have h1 := (h (s := 2) (x := 1 / 2) (y := Real.sqrt 3 / 2)
    (by norm_num) (by norm_num) le_rfl le_rfl).2.mpr ⟨rfl, rfl⟩
  change epstein 2 (1 / 2) (Real.sqrt 3 / 2) + 1 = epstein 2 (1 / 2) (Real.sqrt 3 / 2) at h1
  linarith

def minimumRegistration : Registration minimumArena (type_of% (@reduced_epstein_minimum)) where
  actual := zetaActual
  bridge := minimum_bridge
  variation := ⟨@reduced_epstein_minimum, minimumRejected, minimum_rejected⟩
  sensitivity := ⟨fun i => ⟨minimumRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, minimum_rejected⟩, fun e => nomatch e⟩
  dependence := zeta_dependence

private theorem square_area : |(1 : ℂ).re * Complex.I.im - (1 : ℂ).im * Complex.I.re| = 1 := by
  norm_num

abbrev basisZetaSignature : Signature where
  Params := Σ _ : ℂ, ℂ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def basisZetaActual : Realization basisZetaSignature :=
  realize basisZetaSignature (fun _ p s => basisEpstein s p.1 p.2) (fun e => nomatch e)

private theorem basisSquare : basisEpstein 2 1 Complex.I = epstein 2 0 1 := by
  unfold basisEpstein epstein
  apply tsum_congr
  intro v
  congr 1
  simp [Q, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]

private theorem basisZeta_dependence :
    ObservationalDependence basisZetaSignature basisZetaActual := by
  intro i
  refine ⟨⟨1, Complex.I⟩, 0, 2, ?_⟩
  change basisEpstein 0 1 Complex.I ≠ basisEpstein 2 1 Complex.I
  have hz : basisEpstein 0 1 Complex.I = 0 := by simp [basisEpstein]
  rw [hz, basisSquare]
  exact ne_of_lt zeta_pos

def basisMinimumArena : Arena where
  signature := basisZetaSignature
  Law R := ∀ (a b : ℂ) {A s : ℝ}, 0 < A →
    |a.re * b.im - a.im * b.re| = A → 1 < s →
    A ^ (-s) * epstein s (1 / 2) (Real.sqrt 3 / 2) ≤ R.readout () ⟨a, b⟩ s ∧
      (R.readout () ⟨a, b⟩ s = A ^ (-s) * epstein s (1 / 2) (Real.sqrt 3 / 2) ↔
        IsHexagonalBasis (((Real.sqrt A)⁻¹ : ℝ) • a) (((Real.sqrt A)⁻¹ : ℝ) • b))

private theorem basisMinimum_bridge : (type_of% (@basis_epstein_minimum_isometry)) ↔
    basisMinimumArena.Law basisZetaActual := Iff.rfl

def basisMinimumRejected : Realization basisZetaSignature :=
  realize basisZetaSignature (fun _ _ s => epstein s (1 / 2) (Real.sqrt 3 / 2) - 1)
    (fun e => nomatch e)

private theorem basisMinimum_rejected : ¬ basisMinimumArena.Law basisMinimumRejected := by
  intro h
  have h1 := (h 1 Complex.I (A := 1) (s := 2) (by norm_num) square_area (by norm_num)).1
  change (1 : ℝ) ^ (-(2 : ℝ)) * epstein 2 (1 / 2) (Real.sqrt 3 / 2) ≤
    epstein 2 (1 / 2) (Real.sqrt 3 / 2) - 1 at h1
  norm_num only [Real.one_rpow, one_mul] at h1
  linarith

def basisMinimumRegistration : Registration basisMinimumArena
    (type_of% (@basis_epstein_minimum_isometry)) where
  actual := basisZetaActual
  bridge := basisMinimum_bridge
  variation := ⟨@basis_epstein_minimum_isometry, basisMinimumRejected, basisMinimum_rejected⟩
  sensitivity := ⟨fun i => ⟨basisMinimumRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, basisMinimum_rejected⟩, fun e => nomatch e⟩
  dependence := basisZeta_dependence

end
end Reg.Support.EpsteinMellinMinimum

namespace Reg.Support.PlanarThetaFoundation
noncomputable section

def temperatureContinuityArena : Arena where
  signature := thetaSignature
  Law R := ∀ (x : ℝ) {y : ℝ}, 0 < y →
    ContinuousOn (fun t => R.readout () ⟨x, y⟩ t) (Set.Ioi 0)

private theorem temperatureContinuity_bridge : (type_of% (@continuousOn_temperature)) ↔
    temperatureContinuityArena.Law thetaActual := Iff.rfl

open Classical in
def thetaDiscontinuous : Realization thetaSignature :=
  realize thetaSignature (fun _ _ t => if t = 1 then 0 else 1) (fun e => nomatch e)

private theorem temperatureContinuity_rejected :
    ¬ temperatureContinuityArena.Law thetaDiscontinuous := by
  classical
  intro h
  have hc : ContinuousAt (fun t : ℝ => if t = 1 then (0 : ℝ) else 1) 1 :=
    (h 0 (y := 1) (by norm_num)).continuousAt (Ioi_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, he⟩ := Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
  have hz : (1 : ℝ) + δ / 2 ≠ 1 := by linarith
  have hd : dist ((1 : ℝ) + δ / 2) 1 < δ := by
    rw [Real.dist_eq, show (1 : ℝ) + δ / 2 - 1 = δ / 2 by ring,
      abs_of_pos (by positivity)]
    linarith
  have hh := he hd
  norm_num [hz] at hh

def temperatureContinuityRegistration :
    Registration temperatureContinuityArena (type_of% (@continuousOn_temperature)) where
  actual := thetaActual
  bridge := temperatureContinuity_bridge
  variation := ⟨@continuousOn_temperature, thetaDiscontinuous, temperatureContinuity_rejected⟩
  sensitivity := ⟨fun i => ⟨thetaDiscontinuous,
    fun j h =>
      (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, temperatureContinuity_rejected⟩,
    fun e => nomatch e⟩
  dependence := theta_dependence

end
end Reg.Support.PlanarThetaFoundation
