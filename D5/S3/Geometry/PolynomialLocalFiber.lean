/- GID: D5/S3/Geometry/PolynomialLocalFiber
   generality: G
   mirror-B: D5/B/S3/Geometry/PolynomialLocalFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Analytic.Polynomial]
   utility: none
   digest: Polynomial certificates for globally maximal derivative rank and local fibers. -/

import D5.S3.Geometry.C1LocalFiber
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.LinearAlgebra.Determinant

/-! A normalized determinant certificate for the maximal-rank locus of a real
polynomial map, with actual local fibers supplied by the real C1 theorem. -/

noncomputable section

open Set Metric MvPolynomial
open scoped Topology

namespace D5.S3.Geometry.PolynomialLocalFiber

variable {n m : ℕ}

private lemma smooth_eval (p : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ 1 (fun x : Fin n → ℝ => eval x p) :=
  (AnalyticOnNhd.eval_mvPolynomial p).contDiff

private lemma directional_polynomial (p : MvPolynomial (Fin n) ℝ) (v : Fin n → ℝ) :
    ∃ q : MvPolynomial (Fin n) ℝ, ∀ x,
      eval x q = fderiv ℝ (fun y : Fin n → ℝ => eval y p) x v := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0, ?_⟩
    intro x
    simp
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    refine ⟨p' + q', ?_⟩
    intro x
    simp only [map_add]
    rw [fderiv_fun_add (smooth_eval p).differentiable_one.differentiableAt
      (smooth_eval q).differentiable_one.differentiableAt]
    simp [hp', hq']
  | mul_X p i hp =>
    obtain ⟨p', hp'⟩ := hp
    refine ⟨p' * X i + C (v i) * p, ?_⟩
    intro x
    have hd := ((smooth_eval p).differentiable_one.differentiableAt (x := x)).hasFDerivAt.mul
      (ContinuousLinearMap.proj i).hasFDerivAt
    have he := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L v) hd.fderiv
    simpa only [Pi.mul_def, ContinuousLinearMap.proj_apply, map_add, map_mul,
      eval_X, eval_C, hp', add_apply, smul_apply,
      smul_eq_mul, mul_comm, add_comm] using he.symm

private lemma projected_directional_polynomial
    (p : Fin m → MvPolynomial (Fin n) ℝ) (v : Fin n → ℝ)
    (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) :
    ∃ q : MvPolynomial (Fin n) ℝ, ∀ x,
      eval x q = L (fderiv ℝ (fun y j => eval y (p j)) x v) := by
  classical
  choose q hq using fun j => directional_polynomial (p j) v
  refine ⟨∑ j, C (L (Pi.single j 1)) * q j, ?_⟩
  intro x
  rw [fderiv_pi (fun j => (smooth_eval (p j)).differentiable_one.differentiableAt)]
  simp only [map_sum, map_mul, eval_C, hq]
  change (∑ j, L (Pi.single j 1) * fderiv ℝ (fun y => eval y (p j)) x v) =
    L (fun j => fderiv ℝ (fun y => eval y (p j)) x v)
  conv_rhs => rw [pi_eq_sum_univ' (fun j => fderiv ℝ (fun y => eval y (p j)) x v)]
  simp [map_sum, mul_comm]

/-- A literal real polynomial, equal to one at a witness, certifies globally
maximal derivative rank at every point where it does not vanish. The certificate
is a determinant of a fixed projection of the derivative along a fixed section. -/
private theorem maximal_rank_certificate (p : Fin m → MvPolynomial (Fin n) ℝ) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      (∃ a₀ : Fin n → ℝ, eval a₀ D = 1) ∧
      ∀ a : Fin n → ℝ, eval a D ≠ 0 → ∀ x : Fin n → ℝ,
        Module.finrank ℝ (LinearMap.range
          (fderiv ℝ (fun y j => eval y (p j)) x).toLinearMap) ≤
        Module.finrank ℝ (LinearMap.range
          (fderiv ℝ (fun y j => eval y (p j)) a).toLinearMap) := by
  classical
  let f : (Fin n → ℝ) → (Fin m → ℝ) := fun x j => eval x (p j)
  let rank (x : Fin n → ℝ) :=
    Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap)
  have hbound (x : Fin n → ℝ) : rank x ≤ m := by
    simpa using (Submodule.finrank_le (LinearMap.range (fderiv ℝ f x).toLinearMap))
  let Q (r : ℕ) := ∃ x, rank x = r
  obtain ⟨a₀, ha₀⟩ := Nat.findGreatest_spec (P := Q) (hbound 0) ⟨0, rfl⟩
  have hmax (x : Fin n → ℝ) : rank x ≤ rank a₀ := by
    rw [ha₀]
    exact Nat.le_findGreatest (hbound x) ⟨x, rfl⟩
  let A := (fderiv ℝ f a₀).toLinearMap
  let R := LinearMap.range A
  obtain ⟨C, hRC⟩ := Submodule.exists_isCompl R
  let P : (Fin m → ℝ) →ₗ[ℝ] R := R.projectionOnto C hRC
  have hPA : Function.Surjective (P.comp A) := by
    intro y
    obtain ⟨x, hx⟩ := y.property
    refine ⟨x, ?_⟩
    change P (A x) = y
    rw [hx]
    exact Submodule.projectionOnto_apply_left hRC y
  obtain ⟨I, hI⟩ := (P.comp A).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hPA)
  let B := Module.finBasis ℝ R
  choose entries hJ using fun i j => projected_directional_polynomial p (I (B j))
    ((B.coord i).comp P)
  let J : Matrix (Fin (Module.finrank ℝ R)) (Fin (Module.finrank ℝ R))
      (MvPolynomial (Fin n) ℝ) := entries
  let D : MvPolynomial (Fin n) ℝ := Matrix.det J
  let T (x : Fin n → ℝ) : R →ₗ[ℝ] R :=
    P.comp ((fderiv ℝ f x).toLinearMap.comp I)
  have hD (x : Fin n → ℝ) : eval x D = (LinearMap.toMatrix B B (T x)).det := by
    change eval x (Matrix.det J) = _
    rw [(eval x).map_det]
    congr 1
    ext i j
    have he : (eval x).mapMatrix J i j = eval x (entries i j) := rfl
    rw [he, LinearMap.toMatrix_apply]
    simpa only [T, f, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      Module.Basis.coord_apply] using hJ i j x
  have hDa₀ : eval a₀ D = 1 := by
    rw [hD]
    have hT : T a₀ = LinearMap.id := by
      simpa only [T, A, LinearMap.comp_assoc] using hI
    rw [hT, LinearMap.toMatrix_id, Matrix.det_one]
  refine ⟨D, ?_, ⟨a₀, hDa₀⟩, ?_⟩
  · intro h
    simp [h] at hDa₀
  · intro a ha x
    have hdet : IsUnit (LinearMap.toMatrix B B (T a)).det :=
      isUnit_iff_ne_zero.mpr (by rwa [← hD])
    have hsurj : Function.Surjective (T a) :=
      (LinearEquiv.ofIsUnitDet hdet).surjective
    have hlower : rank a₀ ≤ rank a := by
      have hmono := Submodule.finrank_mono
        (LinearMap.range_comp_le_range I (fderiv ℝ f a).toLinearMap)
      have hproj := Submodule.finrank_map_le P
        (LinearMap.range ((fderiv ℝ f a).toLinearMap.comp I))
      rw [← LinearMap.range_comp] at hproj
      have htop : LinearMap.range (T a) = ⊤ := LinearMap.range_eq_top.mpr hsurj
      change Module.finrank ℝ R ≤ rank a
      calc
        Module.finrank ℝ R = Module.finrank ℝ (LinearMap.range (T a)) := by
          rw [htop, finrank_top]
        _ ≤ Module.finrank ℝ (LinearMap.range
            ((fderiv ℝ f a).toLinearMap.comp I)) := hproj
        _ ≤ rank a := hmono
    exact (hmax x).trans hlower

/-- Outside the zero set of one explicitly nonzero real polynomial, every point
has globally maximal derivative rank and an actual C1 local fiber in each
specified open neighborhood. If the target dimension is smaller, that fiber
has positive dimension and gives a distinct point with the same polynomial
values in that neighborhood. No density or quotient-image assertion is used. -/
theorem exists_rank_fiber_polynomial (p : Fin m → MvPolynomial (Fin n) ℝ) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      (∃ a₀ : Fin n → ℝ, eval a₀ D = 1) ∧
      ∀ a : Fin n → ℝ, eval a D ≠ 0 →
        (∀ x : Fin n → ℝ,
          Module.finrank ℝ (LinearMap.range
            (fderiv ℝ (fun y j => eval y (p j)) x).toLinearMap) ≤
          Module.finrank ℝ (LinearMap.range
            (fderiv ℝ (fun y j => eval y (p j)) a).toLinearMap)) ∧
        ∀ U : Set (Fin n → ℝ), IsOpen U → a ∈ U →
          ∃ (K : Submodule ℝ (Fin n → ℝ)) (q : (Fin n → ℝ) →L[ℝ] K)
            (k : K → (Fin n → ℝ)) (ε : ℝ),
            0 < ε ∧
            Module.finrank ℝ K +
              Module.finrank ℝ (LinearMap.range
                (fderiv ℝ (fun y j => eval y (p j)) a).toLinearMap) = n ∧
            k 0 = a ∧ ContDiffOn ℝ 1 k (ball 0 ε) ∧
            (∀ z ∈ ball 0 ε, k z ∈ U ∧
              (∀ j, eval (k z) (p j) = eval a (p j)) ∧ q (k z - a) = z) ∧
            (m < n → 0 < Module.finrank ℝ K ∧
              ∃ b ∈ U, b ≠ a ∧ ∀ j, eval b (p j) = eval a (p j)) := by
  obtain ⟨D, hD, hw, hmax⟩ := maximal_rank_certificate p
  refine ⟨D, hD, hw, fun a ha => ⟨hmax a ha, ?_⟩⟩
  intro U hU haU
  have hf : ContDiff ℝ 1 (fun x : Fin n → ℝ => fun j => eval x (p j)) :=
    contDiff_pi.mpr fun j => smooth_eval (p j)
  obtain ⟨K, q, k, ε, hε, hdim, hk0, hkc, hk⟩ :=
    C1LocalFiber.exists_local_fiber hU hf.contDiffOn haU (fun x _ => hmax a ha x)
  have hdim' : Module.finrank ℝ K +
      Module.finrank ℝ (LinearMap.range
        (fderiv ℝ (fun y j => eval y (p j)) a).toLinearMap) = n := by
    simpa using hdim
  refine ⟨K, q, k, ε, hε, hdim', hk0, hkc, ?_, ?_⟩
  · intro z hz
    exact ⟨(hk z hz).1, fun j => congrFun (hk z hz).2.1 j, (hk z hz).2.2⟩
  · intro hmn
    have hr : Module.finrank ℝ (LinearMap.range
        (fderiv ℝ (fun y j => eval y (p j)) a).toLinearMap) ≤ m := by
      simpa using (Submodule.finrank_le (LinearMap.range
        (fderiv ℝ (fun y j => eval y (p j)) a).toLinearMap))
    have hpos : 0 < Module.finrank ℝ K := by omega
    let : Nontrivial K := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨z, hzn⟩ := exists_norm_eq K (le_of_lt (half_pos hε))
    have hz : z ∈ ball (0 : K) ε := by
      simpa [Metric.mem_ball, hzn] using half_lt_self hε
    have hzne : z ≠ 0 := norm_pos_iff.mp (by rw [hzn]; exact half_pos hε)
    refine ⟨hpos, k z, (hk z hz).1, ?_, fun j => congrFun (hk z hz).2.1 j⟩
    intro he
    have heq := (hk z hz).2.2
    rw [he, sub_self, map_zero] at heq
    exact hzne heq.symm

end D5.S3.Geometry.PolynomialLocalFiber
