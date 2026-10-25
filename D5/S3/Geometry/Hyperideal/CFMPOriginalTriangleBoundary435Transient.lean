import D5.S3.Geometry.Hyperideal.CFMPPlaneBoundaryMoment435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalRadialCurveLength435Transient
import Mathlib.Analysis.Convex.Combination

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Matrix Interval BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPLorentzLiftSurface435Transient CFMPNativePullbackMetric435Transient
open CFMPOriginalNativeCoordinates435Transient
open CFMPSimplexDirection435Transient CFMPPlaneMomentDivergence435Transient
open CFMPPlaneEdgeCofactor435Transient CFMPPlaneDualConormal435Transient
open CFMPPlaneBoundaryMoment435Transient

namespace CFMPOriginalTriangleBoundary435Transient

def originalV0 {l : Fin 6 → ℝ} (M : Matrix (Fin 4) (Fin 4) ℝ)
    (p : Fin 3 → cutBody l) : W := (p 0).val ᵥ* M

def originalB {l : Fin 6 → ℝ} (M : Matrix (Fin 4) (Fin 4) ℝ)
    (p : Fin 3 → cutBody l) : W := ((p 1).val-(p 0).val) ᵥ* M

def originalC {l : Fin 6 → ℝ} (M : Matrix (Fin 4) (Fin 4) ℝ)
    (p : Fin 3 → cutBody l) : W := ((p 2).val-(p 0).val) ᵥ* M

def triangleCoefficient {l : Fin 6 → ℝ} (p : Fin 3 → cutBody l) (q : ℝ × ℝ) : W :=
  (p 0).val+q.1 • ((p 1).val-(p 0).val)+q.2 • ((p 2).val-(p 0).val)

def edgeStart {l : Fin 6 → ℝ} (p : Fin 3 → cutBody l) (e : Fin 3) : cutBody l :=
  ![p 0,p 0,p 1] e

def edgeEnd {l : Fin 6 → ℝ} (p : Fin 3 → cutBody l) (e : Fin 3) : cutBody l :=
  ![p 2,p 1,p 2] e

theorem edge_distinct {l : Fin 6 → ℝ} (p : Fin 3 → cutBody l)
    (hp : Function.Injective p) (e : Fin 3) : edgeStart p e ≠ edgeEnd p e := by
  fin_cases e <;> simp only [edgeStart,edgeEnd,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two]
  all_goals
    intro h
    have hh := hp h
    norm_num at hh

theorem triangleCoefficient_mem (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (p : Fin 3 → cutBody l) (q : ℝ × ℝ) (hq : q ∈ triangle 1) :
    triangleCoefficient p q ∈ cutBody l := by
  have hconv : Convex ℝ (cutBody l) := by
    rw [← (D5.S3.Geometry.Hyperideal.LengthGramPolytope.cut_body_polytope l hl).2.1]
    exact convex_convexHull ℝ _
  let weights : Fin 3 → ℝ := ![1-q.1-q.2,q.1,q.2]
  have hn : ∀ i : Fin 3, 0 ≤ weights i := by
    intro i
    fin_cases i
    · change 0 ≤ 1-q.1-q.2
      linarith only [hq.2.2]
    · change 0 ≤ q.1
      exact hq.1
    · change 0 ≤ q.2
      exact hq.2.1
  have hs : (∑ i : Fin 3, weights i) = 1 := by
    simp [weights,Fin.sum_univ_three]
    ring
  have hm : (∑ i : Fin 3, weights i • (p i).val) ∈ cutBody l :=
    hconv.sum_mem (fun i _ => hn i) hs (fun i _ => (p i).property)
  have he : triangleCoefficient p q = ∑ i : Fin 3, weights i • (p i).val := by
    ext i
    simp [triangleCoefficient,weights,Fin.sum_univ_three,smul_eq_mul]
    ring
  rw [he]
  exact hm

theorem triangle_coefficient_image {l : Fin 6 → ℝ} (M : Matrix (Fin 4) (Fin 4) ℝ)
    (p : Fin 3 → cutBody l) (q : ℝ × ℝ) :
    (triangleCoefficient p q) ᵥ* M =
      originalV0 M p+q.1 • originalB M p+q.2 • originalC M p := by
  simp only [triangleCoefficient,originalV0,originalB,originalC,
    Matrix.add_vecMul,Matrix.smul_vecMul]

theorem raw_original_edge {l : Fin 6 → ℝ} (M : Matrix (Fin 4) (Fin 4) ℝ)
    (p : Fin 3 → cutBody l) (e : Fin 3) (r : ℝ) :
    rawPoint (originalV0 M p) (originalB M p) (originalC M p) e r =
      ((1-r) • (edgeStart p e).val+r • (edgeEnd p e).val) ᵥ* M := by
  fin_cases e <;> ext i <;>
    simp [rawPoint,edgePoint,originalV0,originalB,originalC,edgeStart,edgeEnd,
      Matrix.vecMul,dotProduct,Fin.sum_univ_four,smul_eq_mul] <;> ring

theorem tangent_original_edge {l : Fin 6 → ℝ} (M : Matrix (Fin 4) (Fin 4) ℝ)
    (p : Fin 3 → cutBody l) (e : Fin 3) :
    rawTangent (originalB M p) (originalC M p) e =
      ((edgeEnd p e).val-(edgeStart p e).val) ᵥ* M := by
  fin_cases e <;> ext i <;>
    simp [rawTangent,originalB,originalC,edgeStart,edgeEnd,Matrix.vecMul,
      dotProduct,Fin.sum_univ_four,smul_eq_mul] <;> ring

-- Endpoints and the curve belong to the same original f, including the closed endpoints.
theorem original_edge_speed_length
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (f : cutBody l → HyperbolicThreeSpace)
    (hfinj : Function.Injective f)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (p : Fin 3 → cutBody l) (hp : Function.Injective p) (e : Fin 3) :
    (∫ r in (0 : ℝ)..1,
      nativeSpeed (originalV0 M p) (originalB M p) (originalC M p) e r) =
        dist (f (edgeStart p e)) (f (edgeEnd p e)) := by
  have h := CFMPOriginalRadialCurveLength435Transient.original_radial_curve_length
    l hl M f hfinj hf (edgeStart p e) (edgeEnd p e) (edge_distinct p hp e)
  dsimp only at h
  obtain ⟨hcurve,hlength⟩ := h
  rw [← hlength]
  apply intervalIntegral.integral_congr
  intro r hr
  have hri : r ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hr
  obtain ⟨w,hw,hcoords,hheight,hD⟩ := hcurve r hri
  dsimp only [nativeSpeed]
  rw [raw_original_edge,tangent_original_edge,hD.deriv]

-- The remaining area term is explicitly a coordinate integral, not a claimed native H2 integral.
theorem original_triangle_boundary_moment
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (f : cutBody l → HyperbolicThreeSpace)
    (hfinj : Function.Injective f)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (p : Fin 3 → cutBody l) (hp : Function.Injective p)
    (hG : (gram (pairingEntries (originalV0 M p) (originalB M p)
      (originalC M p))).det < 0) (a : Fin 3 → ℝ) :
    let V0 := originalV0 M p
    let b := originalB M p
    let c := originalC M p
    (∫ z in triangle 1, 2*Real.sqrt (-(gram (pairingEntries V0 b c)).det)*
      moment (pairingEntries V0 b c) a z/(Q (pairingEntries V0 b c) z)^2) =
      ∑ e : Fin 3, lorentz (basisPoint V0 b c a) (dualUnit V0 b c e) *
        dist (f (edgeStart p e)) (f (edgeEnd p e)) := by
  dsimp only
  have hQ (q : ℝ × ℝ) :
      Q (pairingEntries (originalV0 M p) (originalB M p) (originalC M p)) q =
        radius ((triangleCoefficient p q) ᵥ* M) := by
    rw [triangle_coefficient_image]
    simp [Q,pairingEntries,radius,lorentz,Fin.sum_univ_four,smul_eq_mul]
    ring
  have hq (q : ℝ × ℝ) (hq : q ∈ triangle 1) :
      0 < Q (pairingEntries (originalV0 M p) (originalB M p) (originalC M p)) q := by
    rw [hQ]
    exact (original_native_coordinates l hl M f hf
      ⟨triangleCoefficient p q,triangleCoefficient_mem l hl p q hq⟩).1
  have hd (e : Fin 3) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      delta (rawPoint (originalV0 M p) (originalB M p) (originalC M p) e r) ≠ 0 := by
    have hmem := triangleCoefficient_mem l hl p (edgePoint e r) (edgePoint_mem e r hr)
    have h := (original_native_coordinates l hl M f hf
      ⟨triangleCoefficient p (edgePoint e r),hmem⟩).2.1.ne'
    rw [triangle_coefficient_image] at h
    exact h
  rw [native_speed_boundary_moment _ _ _ hG a hq hd]
  apply Finset.sum_congr rfl
  intro e he
  rw [original_edge_speed_length l hl M f hfinj hf p hp e]

end CFMPOriginalTriangleBoundary435Transient

run_cmd do
  let name := ``CFMPOriginalTriangleBoundary435Transient.original_triangle_boundary_moment
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError m!"CFMP483 missing declaration {name}"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP483 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP483 CHECKED {name} axioms={axioms}"
