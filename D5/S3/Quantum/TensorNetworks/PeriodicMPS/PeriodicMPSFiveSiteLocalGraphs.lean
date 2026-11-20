/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteLocalGraphs
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteLocalGraphs
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialJets]
   utility: none
   digest: The verified jets give the cubic coefficients of the actual local observation graphs. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteAnalyticDerivative
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteSpecialJets
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSLocalObservationGraph
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! The strict derivative of the normal coordinate vanishes at the chosen
lifts, so the tangential correction of order three leaves the cubic term
of the normal graph unchanged. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteLocalGraphs

open Asymptotics Filter Set Polynomial
open scoped Topology
open PeriodicMPSFiveSiteJetCoordinates PeriodicMPSFiveSiteJetReflection
  PeriodicMPSFiveSiteAnalyticDerivative PeriodicMPSFiveSiteSpecialJets
  PeriodicMPSLocalObservationGraph

noncomputable section

abbrev E := Fin 9 → ℝ

/-- The source of a certified raw branch. -/
def center (i : Fin 4) : E := fun j => (source i j : ℝ)

/-- The tangential coordinates of the raw observation. -/
def tangent (u : E) : E := fun j => raw u j.castSucc

/-- The corner probability gives the remaining normal coordinate. -/
def normal (u : E) : ℝ := raw u 9

private def direction : E := fun j => if j = 4 then 1 else 0

private def path (i : Fin 4) (t : ℝ) : E :=
  center i + t • (fun k => (firstDirection i k : ℝ)) +
    t ^ 2 • (fun k => (secondDirection i k : ℝ))

private def poly (i : Fin 4) (j : Fin 10) : ℝ[X] :=
  (pathPolynomial (source i) (firstDirection i) (secondDirection i) j).map (Rat.castHom ℝ)

private theorem eval_poly (i : Fin 4) (j : Fin 10) (t : ℝ) :
    (poly i j).eval t = raw (path i t) j := by
  rw [poly, Polynomial.eval_map, eval_pathPolynomial_real]
  congr 1
  funext k
  simp [path, center, mul_comm]

private theorem path_tendsto (i : Fin 4) : Tendsto (path i) (𝓝 0) (𝓝 (center i)) := by
  have h : Continuous (path i) := by unfold path; fun_prop
  simpa [path] using h.continuousAt (x := (0 : ℝ)).tendsto

private lemma eval_step (p : ℝ[X]) (t : ℝ) : p.eval t = p.coeff 0 + t * p.divX.eval t := by
  simpa only [eval_add, eval_mul, eval_X, eval_C, add_comm] using
    (congrArg (Polynomial.eval t) (X_mul_divX_add p)).symm

private lemma eval_degree_three (p : ℝ[X]) (t : ℝ) :
    p.eval t - (p.coeff 0 + p.coeff 1 * t + p.coeff 2 * t ^ 2 + p.coeff 3 * t ^ 3) =
      t ^ 4 * p.divX.divX.divX.divX.eval t := by
  rw [eval_step p, eval_step p.divX, eval_step p.divX.divX, eval_step p.divX.divX.divX]
  simp only [coeff_divX, Nat.reduceAdd]
  ring

private lemma remainder (p : ℝ[X]) :
    (fun t => p.eval t -
      (p.coeff 0 + p.coeff 1 * t + p.coeff 2 * t ^ 2 + p.coeff 3 * t ^ 3))
      =o[𝓝 0] (fun t : ℝ => t ^ 3) := by
  have h := (p.divX.divX.divX.divX.continuous.continuousAt (x := (0 : ℝ))).tendsto
  have hB := isBigO_const_of_tendsto h (one_ne_zero : (1 : ℝ) ≠ 0)
  exact ((isLittleO_pow_pow (𝕜 := ℝ) (show 3 < 4 by decide)).mul_isBigO hB).congr
    (fun t => (eval_degree_three p t).symm) (fun _ => mul_one _)

private theorem constant_coeff (i : Fin 4) (j : Fin 10) :
    (poly i j).coeff 0 = raw (center i) j := by
  rw [coeff_zero_eq_eval_zero, eval_poly]
  simp [path]

private theorem linear_coeff_tangent (i : Fin 4) (j : Fin 9) :
    (poly i j.castSucc).coeff 1 = direction j := by
  rw [poly, coeff_map]
  change ((pathPolynomial _ _ _ _).coeff 1 : ℝ) = _
  rw [linearCoefficient_real]
  have h := congrArg (fun x : ℚ => (x : ℝ)) ((exact_jet_coefficients i).2.1 j)
  simpa [direction, tangentJacobian, Matrix.mulVec, dotProduct, apply_ite] using h

private theorem linear_coeff_normal (i : Fin 4) : (poly i 9).coeff 1 = 0 := by
  rw [poly, coeff_map]
  change ((pathPolynomial _ _ _ _).coeff 1 : ℝ) = _
  rw [linearCoefficient_real]
  simp [(exact_jet_coefficients i).1]

private theorem quadratic_coeff_tangent (i : Fin 4) (j : Fin 9) :
    (poly i j.castSucc).coeff 2 = 0 := by
  rw [poly, coeff_map, ← quadraticCoefficient_eq_coeff, (exact_jet_coefficients i).2.2.1 j]
  exact map_zero (Rat.castHom ℝ)

private theorem cubic_coeff_normal (i : Fin 4) :
    (poly i 9).coeff 3 = (normalCubics i : ℝ) := by
  rw [poly, coeff_map, ← cubicCoefficient_eq_coeff, (exact_jet_coefficients i).2.2.2]
  rfl

private theorem tangent_error (i : Fin 4) :
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

private theorem normal_strict_derivative (i : Fin 4) :
    HasStrictFDerivAt normal (0 : E →L[ℝ] ℝ) (center i) := by
  have h : fderiv ℝ normal (center i) = 0 := by
    ext v
    change fderiv ℝ (fun q => raw q 9) (fun j => (source i j : ℝ)) v = 0
    rw [fderiv_raw_apply]
    simp [(exact_jet_coefficients i).1]
  rw [← h]
  exact (analytic_raw (center i) 9).hasStrictFDerivAt

private theorem tangent_invertible (i : Fin 4) :
    ∃ L : E ≃L[ℝ] E, HasFDerivAt tangent (L : E →L[ℝ] E) (center i) := by
  let M := (tangentJacobian (source i)).map (Rat.castHom ℝ)
  have hd : IsUnit M.det := by
    change IsUnit (((Rat.castHom ℝ).mapMatrix (tangentJacobian (source i))).det)
    rw [← (Rat.castHom ℝ).map_det]
    exact isUnit_iff_ne_zero.mpr (Rat.cast_ne_zero.mpr (tangent_nonsingular i))
  letI := (Matrix.isUnit_iff_isUnit_det M).mpr hd |>.invertible
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
def HasNormalJet (i : Fin 4) (g : E → ℝ) : Prop :=
  (fun t => g (tangent (center i) + t • direction) -
    (normal (center i) + (poly i 9).coeff 2 * t ^ 2 + (normalCubics i : ℝ) * t ^ 3))
    =o[𝓝 0] (fun t : ℝ => t ^ 3)

/-- Each selected lift gives an analytic graph in the same tangential
coordinates, with the computed cubic coefficient along the selected line. -/
theorem exists_certified_graph (i : Fin 4) :
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
  rw [constant_coeff, linear_coeff_normal, cubic_coeff_normal] at hn
  refine (h.add hn).congr' ?_ EventuallyEq.rfl
  filter_upwards [hy' (hU.mem_nhds hy)] with t ht
  have hg' : normal (e.symm (line t)) = g (line t) := congrArg Prod.snd (hg _ ht)
  change (normal (e.symm (line t)) - normal (path i t)) + _ = g (line t) - _
  rw [hg', eval_poly, ← show normal (path i t) = raw (path i t) 9 from rfl]
  simp only [normal]
  ring

private theorem coefficient_zero_of_littleO (c : ℝ) (n : ℕ)
    (h : (fun t : ℝ => c * t ^ n) =o[𝓝 0] (fun t : ℝ => t ^ n)) : c = 0 := by
  have hlim := h.tendsto_div_nhds_zero.mono_left
    (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have he : (fun t : ℝ => c * t ^ n / t ^ n) =ᶠ[𝓝[≠] (0 : ℝ)] fun _ => c := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_div_cancel_right₀ c (pow_ne_zero _ ht)
  exact tendsto_nhds_unique tendsto_const_nhds (hlim.congr' he)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- The common base point is calculated by reducing the ten rational coordinates.
/-- All four choices of the source give the same raw marginal. -/
theorem raw_center_eq (i j : Fin 4) : raw (center i) = raw (center j) := by
  have h (k : Fin 4) (l : Fin 10) : raw (source k) l = raw (source 0) l := by
    fin_cases k <;> fin_cases l <;> decide +kernel
  funext l
  have hmap (k : Fin 4) : ((raw (source k) l : ℚ) : ℝ) = raw (center k) l :=
    map_raw (Rat.castHom ℝ) (source k) l
  rw [← hmap i, ← hmap j, h i l, h j l]

/-- Distinct verified cubic coefficients imply distinct image germs. -/
theorem normal_germs_ne {i j : Fin 4} (hij : i ≠ j) {g h : E → ℝ}
    (hg : HasNormalJet i g) (hh : HasNormalJet j h) :
    ¬ g =ᶠ[𝓝 (tangent (center i))] h := by
  intro he
  have hT : tangent (center i) = tangent (center j) :=
    funext fun k => congrFun (raw_center_eq i j) k.castSucc
  have hN : normal (center i) = normal (center j) :=
    congrFun (raw_center_eq i j) 9
  let y := tangent (center i)
  let line : ℝ → E := fun t => y + t • direction
  have hline : Tendsto line (𝓝 0) (𝓝 y) := by
    have hc : Continuous line := by unfold line; fun_prop
    simpa [line] using hc.continuousAt (x := (0 : ℝ)).tendsto
  have he' : (fun t => g (line t)) =ᶠ[𝓝 0] fun t => h (line t) := he.comp_tendsto hline
  unfold HasNormalJet at hg hh
  rw [← hT, ← hN] at hh
  let a := (poly i 9).coeff 2 - (poly j 9).coeff 2
  let b := (normalCubics i : ℝ) - (normalCubics j : ℝ)
  have h₃ : (fun t : ℝ => a * t ^ 2 + b * t ^ 3) =o[𝓝 0] (fun t : ℝ => t ^ 3) := by
    apply (hh.sub hg).congr' _ EventuallyEq.rfl
    filter_upwards [he'] with t ht
    change (h (line t) - _) - (g (line t) - _) = _
    rw [ht]
    dsimp [a, b]
    ring
  have hpow := isLittleO_pow_pow (𝕜 := ℝ) (show 2 < 3 by decide)
  have ha : (fun t : ℝ => a * t ^ 2) =o[𝓝 0] (fun t : ℝ => t ^ 2) :=
    ((h₃.trans_isBigO hpow.isBigO).sub (hpow.const_mul_left b)).congr_left
      fun t => add_sub_cancel_right (a * t ^ 2) (b * t ^ 3)
  have ha' := coefficient_zero_of_littleO a 2 ha
  have hb := coefficient_zero_of_littleO b 3 (by simpa [ha'] using h₃)
  exact hij (normalCubics_injective (Rat.cast_injective (α := ℝ) (sub_eq_zero.mp hb)))

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteLocalGraphs
