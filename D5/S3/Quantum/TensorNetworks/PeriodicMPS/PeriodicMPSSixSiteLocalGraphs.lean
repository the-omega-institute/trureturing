/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteLocalGraphs
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteLocalGraphs
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteAnalyticDerivative]
   utility: none
   digest: The two raw observation germs have different normal cubic coefficients. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteAnalyticDerivative
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteSpecialJets
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSLocalObservationGraph
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteLocalGraphs

/-! The strict derivative of the normal coordinate vanishes at the chosen
lifts, so the tangential correction of order three leaves the cubic term
of the normal graph unchanged. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteLocalGraphs

open Asymptotics Filter Set Polynomial
open scoped Topology
open PeriodicMPSSixSiteJetCoordinates PeriodicMPSSixSiteJetReflection
  PeriodicMPSSixSiteAnalyticDerivative PeriodicMPSSixSiteSpecialJets
  PeriodicMPSLocalObservationGraph

open private remainder coefficient_zero_of_littleO
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteLocalGraphs

noncomputable section

abbrev E := Fin 9 → ℝ

/-- The source of a certified raw branch. -/
def center (i : Fin 2) : E := fun j => (source i j : ℝ)

/-- The tangential coordinates of the raw observation. -/
def tangent (u : E) : E := fun j => raw u j.castSucc

/-- The corner probability gives the remaining normal coordinate. -/
def normal (u : E) : ℝ := raw u 9

private def direction : E := fun j => if j = 3 then 1 else 0

private def path (i : Fin 2) (t : ℝ) : E :=
  center i + t • (fun k => (firstDirection i k : ℝ)) +
    t ^ 2 • (fun k => (secondDirection i k : ℝ))

private def poly (i : Fin 2) (j : Fin 10) : ℝ[X] :=
  realPathPolynomial (source i) (firstDirection i) (secondDirection i) j

private theorem eval_poly (i : Fin 2) (j : Fin 10) (t : ℝ) :
    (poly i j).eval t = raw (path i t) j := by
  exact eval_realPathPolynomial (source i) (firstDirection i) (secondDirection i) j t

private theorem path_tendsto (i : Fin 2) : Tendsto (path i) (𝓝 0) (𝓝 (center i)) := by
  have h : Continuous (path i) := by unfold path; fun_prop
  simpa [path] using h.continuousAt (x := (0 : ℝ)).tendsto

private theorem constant_coeff (i : Fin 2) (j : Fin 10) :
    (poly i j).coeff 0 = raw (center i) j := by
  rw [coeff_zero_eq_eval_zero, eval_poly]
  simp [path]

private theorem linear_coeff_tangent (i : Fin 2) (j : Fin 9) :
    (poly i j.castSucc).coeff 1 = direction j := by
  rw [poly, realPathPolynomial, coeff_map]
  change ((pathPolynomial _ _ _ _).coeff 1 : ℝ) = _
  rw [linearCoefficient_real]
  have h := congrArg (fun x : ℚ => (x : ℝ)) ((exact_jet_coefficients i).2.1 j)
  simpa [direction, tangentJacobian, Matrix.mulVec, dotProduct, apply_ite] using h

private theorem linear_coeff_normal (i : Fin 2) : (poly i 9).coeff 1 = 0 := by
  rw [poly, realPathPolynomial, coeff_map]
  change ((pathPolynomial _ _ _ _).coeff 1 : ℝ) = _
  rw [linearCoefficient_real]
  simp [(exact_jet_coefficients i).1]

private theorem quadratic_coeff_tangent (i : Fin 2) (j : Fin 9) :
    (poly i j.castSucc).coeff 2 = 0 := by
  simp [poly, coeff_two_realPathPolynomial, (exact_jet_coefficients i).2.2.1 j]

private theorem quadratic_coeff_normal (i : Fin 2) :
    (poly i 9).coeff 2 = (normalQuadratic : ℝ) := by
  rw [poly, coeff_two_realPathPolynomial, normalQuadratic_eq]

private theorem cubic_coeff_normal (i : Fin 2) :
    (poly i 9).coeff 3 = (normalCubics i : ℝ) := by
  rw [poly, coeff_three_realPathPolynomial, (exact_jet_coefficients i).2.2.2]

private theorem tangent_error (i : Fin 2) :
    (fun t => tangent (path i t) - (tangent (center i) + t • direction))
      =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  apply Asymptotics.isBigO_pi.mpr
  intro j
  have h := remainder (poly i j.castSucc)
  rw [constant_coeff, linear_coeff_tangent, quadratic_coeff_tangent] at h
  have hc : (fun t : ℝ => (poly i j.castSucc).coeff 3 * t ^ 3) =O[𝓝 0] fun t : ℝ => t ^ 3 :=
    (isBigO_refl _ _).const_mul_left _
  refine (h.isBigO.add hc).congr_left fun t => ?_
  simp only [eval_poly, tangent, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem normal_strict_derivative (i : Fin 2) :
    HasStrictFDerivAt normal (0 : E →L[ℝ] ℝ) (center i) := by
  have h : fderiv ℝ normal (center i) = 0 := by
    ext v
    change fderiv ℝ (fun q => raw q 9) (fun j => (source i j : ℝ)) v = 0
    rw [fderiv_raw_apply]
    simp [(exact_jet_coefficients i).1]
  rw [← h]
  exact (analytic_raw (center i) 9).hasStrictFDerivAt

private theorem tangent_invertible (i : Fin 2) :
    ∃ L : E ≃L[ℝ] E, HasFDerivAt tangent (L : E →L[ℝ] E) (center i) := by
  let M := (tangentJacobian (source i)).map (Rat.castHom ℝ)
  have hd : IsUnit M.det := by
    change IsUnit (((Rat.castHom ℝ).mapMatrix (tangentJacobian (source i))).det)
    rw [← (Rat.castHom ℝ).map_det]
    exact isUnit_iff_ne_zero.mpr (Rat.cast_ne_zero.mpr (tangent_nonsingular i))
  let _ := (Matrix.isUnit_iff_isUnit_det M).mpr hd |>.invertible
  let L : E ≃L[ℝ] E := (M.toLinearEquiv' inferInstance).toContinuousLinearEquiv
  refine ⟨L, hasFDerivAt_pi'' ?_⟩
  intro j
  have h := (analytic_raw (center i) j.castSucc).hasStrictFDerivAt.hasFDerivAt
  apply h.congr_fderiv
  symm
  ext v
  change M.mulVec v j =
    fderiv ℝ (fun q => raw q j.castSucc) (fun k => (source i k : ℝ)) v
  rw [fderiv_raw_apply]
  rfl

/-- Normal coefficients along the chosen tangential line. -/
def HasNormalJet (i : Fin 2) (g : E → ℝ) : Prop :=
  (fun t => g (tangent (center i) + t • direction) -
    (normal (center i) + (normalQuadratic : ℝ) * t ^ 2 + (normalCubics i : ℝ) * t ^ 3))
    =o[𝓝 0] (fun t : ℝ => t ^ 3)

/-- Each selected lift gives an analytic graph in the same tangential
coordinates, with the computed cubic coefficient along the selected line. -/
theorem exists_certified_graph (i : Fin 2) :
    ∃ (e : OpenPartialHomeomorph E E) (U : Set E) (g : E → ℝ),
      (e : E → E) = tangent ∧ center i ∈ e.source ∧ IsOpen U ∧ tangent (center i) ∈ U ∧
      U ⊆ e.target ∧ AnalyticOnNhd ℝ g U ∧
      (∀ y ∈ U, (tangent (e.symm y), normal (e.symm y)) = (y, g y)) ∧
      HasNormalJet i g := by
  obtain ⟨L, hL⟩ := tangent_invertible i
  have hT : AnalyticAt ℝ tangent (center i) :=
    analyticAt_pi_iff.mpr fun j => analytic_raw (center i) j.castSucc
  obtain ⟨e, U, g, he, hx, hU, hy, hsubset, hI, hG, hg⟩ :=
    exists_analytic_graph tangent normal (center i) hT (analytic_raw (center i) 9) L hL
  refine ⟨e, U, g, he, hx, hU, hy, hsubset, hG, hg, ?_⟩
  let line : ℝ → E := fun t => tangent (center i) + t • direction
  have hy' : Tendsto line (𝓝 0) (𝓝 (tangent (center i))) := by
    have hl : Continuous line := by unfold line; fun_prop
    simpa [line] using hl.continuousAt (x := (0 : ℝ)).tendsto
  have h := normal_graph_remainder e hx (by rw [he]; exact hI) (normal_strict_derivative i)
    (path_tendsto i) (by rw [he]; exact hy') (by simp only [he]; exact tangent_error i)
  have hn := remainder (poly i 9)
  rw [constant_coeff, linear_coeff_normal, quadratic_coeff_normal, cubic_coeff_normal] at hn
  refine (h.add hn).congr' ?_ EventuallyEq.rfl
  filter_upwards [hy' (hU.mem_nhds hy)] with t ht
  have hg' : normal (e.symm (line t)) = g (line t) := congrArg Prod.snd (hg _ ht)
  change (normal (e.symm (line t)) - normal (path i t)) + _ = g (line t) - _
  rw [hg', eval_poly, ← show normal (path i t) = raw (path i t) 9 from rfl]
  simp only [normal]
  ring

/-- Both branch centers have the same raw observation. -/
theorem raw_center_eq (i j : Fin 2) : raw (center i) = raw (center j) := by
  funext k
  have hmap (a : Fin 2) : ((raw (source a) k : ℚ) : ℝ) = raw (center a) k :=
    map_raw (Rat.castHom ℝ) (source a) k
  rw [← hmap i, ← hmap j, raw_source i, raw_source j]

/-- The two normal graphs have different germs in the common tangential coordinates. -/
theorem normal_germs_ne {g h : E → ℝ}
    (hg : HasNormalJet 0 g) (hh : HasNormalJet 1 h) :
    ¬ g =ᶠ[𝓝 (tangent (center 0))] h := by
  intro he
  have hT : tangent (center 0) = tangent (center 1) :=
    funext fun k => congrFun (raw_center_eq 0 1) k.castSucc
  have hN : normal (center 0) = normal (center 1) :=
    congrFun (raw_center_eq 0 1) 9
  let y := tangent (center 0)
  let line : ℝ → E := fun t => y + t • direction
  have hline : Tendsto line (𝓝 0) (𝓝 y) := by
    have hc : Continuous line := by unfold line; fun_prop
    simpa [line] using hc.continuousAt (x := (0 : ℝ)).tendsto
  have he' : (fun t => g (line t)) =ᶠ[𝓝 0] fun t => h (line t) := he.comp_tendsto hline
  unfold HasNormalJet at hg hh
  rw [← hT, ← hN] at hh
  let b := (normalCubics 0 : ℝ) - (normalCubics 1 : ℝ)
  have hb : (fun t : ℝ => b * t ^ 3) =o[𝓝 0] (fun t : ℝ => t ^ 3) := by
    apply (hh.sub hg).congr' _ EventuallyEq.rfl
    filter_upwards [he'] with t ht
    change (h (line t) - _) - (g (line t) - _) = _
    rw [ht]
    dsimp [b]
    ring
  exact normalCubics_ne (Rat.cast_injective (α := ℝ)
    (sub_eq_zero.mp (coefficient_zero_of_littleO b 3 hb)))

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteLocalGraphs
