/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQ2PolynomialFiber
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSQ2PolynomialFiber
   mirror-E: none(waiver:static-parameter-fibers)
   anchors: []
   utility: none
   digest: Polynomial raw two-site observations and local canonical-parameter fibers. -/

import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient
import D5.S3.Geometry.PolynomialLocalFiber

/-! The coordinates are five complex core entries, a real sigma and a complex
eta. They are distinct from the old boundary coordinates q0 and q1. Only the
positive representative uses a square root. All observations retain raw scale.
The canonical core and phase rigidity reuse Haobo Ma and Wenlin Zhang's
CC BY 4.0 Conjecture 8 supplier through OpenBoundaryMPSTwoSiteMinimality.
The local C1 supplier credits BochaoKong's Apache-2.0 LeanPool argument,
commit 2b1ec889365345f19a45fa94b6457a4d92c96295. -/

noncomputable section
open Set Matrix MvPolynomial
open scoped BigOperators Matrix Topology

namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber

open OpenBoundaryMPSTwoSiteMinimality
open OpenBoundaryMPSDensityRecovery
open OpenBoundaryMPSDensityGenericity
  (realCoeff imagCoeff coefficient_eval polynomial_nonzero_dense)
open PeriodicMPSParentIntersection (Bond Word wordMatrix)
open OpenBoundaryMPSQuotient
open OpenBoundaryMPSMarginalBirationality

abbrev Coordinates := Fin 13 → ℝ
abbrev Poly := MvPolynomial (Fin 13) ℂ
abbrev RealPoly := MvPolynomial (Fin 13) ℝ

def coreCoordinates (x : Coordinates) (i : Fin 5) : ℂ :=
  ⟨x ⟨i.val, by omega⟩, x ⟨i.val + 5, by omega⟩⟩

def sigma (x : Coordinates) : ℝ := x 10
def eta (x : Coordinates) : ℂ := ⟨x 11, x 12⟩

/-- An old parameter, whose final entries are q0 and q1, not sigma and eta. -/
def positiveRepresentative (x : Coordinates) : Parameter :=
  (coreCoordinates x, Real.sqrt (sigma x), (Real.sqrt (sigma x) : ℂ) * eta x)

private lemma representative_continuous : Continuous positiveRepresentative := by
  have hmk (i j : Fin 13) : Continuous (fun x : Coordinates => (⟨x i, x j⟩ : ℂ)) := by
    have h : Continuous (fun x : Coordinates => (x i : ℂ) + (x j : ℂ) * Complex.I) := by
      fun_prop
    convert h using 1
    funext x
    apply Complex.ext <;> simp
  have hc (i : Fin 5) : Continuous (fun x : Coordinates => coreCoordinates x i) :=
    hmk ⟨i.val, by omega⟩ ⟨i.val + 5, by omega⟩
  have he : Continuous eta := hmk 11 12
  have hs : Continuous (fun x : Coordinates => Real.sqrt (sigma x)) :=
    Real.continuous_sqrt.comp (continuous_apply 10)
  exact (continuous_pi hc).prodMk (hs.prodMk ((Complex.continuous_ofReal.comp hs).mul he))

private lemma representative_injective {x y : Coordinates}
    (hx : 0 < sigma x) (hy : 0 < sigma y)
    (h : positiveRepresentative x = positiveRepresentative y) : x = y := by
  have hc := congrArg (fun θ : Parameter => θ.1) h
  have hs := congrArg (fun θ : Parameter => θ.2.1) h
  change Real.sqrt (sigma x) = Real.sqrt (sigma y) at hs
  have hsigma : sigma x = sigma y := by
    rw [← Real.sq_sqrt hx.le, ← Real.sq_sqrt hy.le, hs]
  have he : eta x = eta y := by
    have hh := congrArg (fun θ : Parameter => θ.2.2) h
    change (Real.sqrt (sigma x) : ℂ) * eta x =
      (Real.sqrt (sigma y) : ℂ) * eta y at hh
    rw [← hs] at hh
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 hx))) hh
  have hcr (i : Fin 5) := congrArg Complex.re (congrFun hc i)
  have hci (i : Fin 5) := congrArg Complex.im (congrFun hc i)
  have her := congrArg Complex.re he
  have hei := congrArg Complex.im he
  funext i
  fin_cases i
  all_goals first
    | exact hcr 0 | exact hcr 1 | exact hcr 2 | exact hcr 3 | exact hcr 4
    | exact hci 0 | exact hci 1 | exact hci 2 | exact hci 3 | exact hci 4
    | exact hsigma | exact her | exact hei

/-- Coordinates of an old parameter with positive real q0. -/
def coordinatesOf (θ : Parameter) : Coordinates :=
  ![(θ.1 0).re, (θ.1 1).re, (θ.1 2).re, (θ.1 3).re, (θ.1 4).re,
    (θ.1 0).im, (θ.1 1).im, (θ.1 2).im, (θ.1 3).im, (θ.1 4).im,
    θ.2.1 ^ 2, (θ.2.2 / (θ.2.1 : ℂ)).re, (θ.2.2 / (θ.2.1 : ℂ)).im]

private lemma representative_coordinatesOf (θ : Parameter) (hθ : 0 < θ.2.1) :
    positiveRepresentative (coordinatesOf θ) = θ := by
  apply Prod.ext
  · funext i
    fin_cases i <;> apply Complex.ext <;> rfl
  · apply Prod.ext
    · simp [positiveRepresentative, sigma, coordinatesOf, Real.sqrt_sq_eq_abs, abs_of_pos hθ]
    · change (Real.sqrt (θ.2.1 ^ 2) : ℂ) *
        (⟨(θ.2.2 / (θ.2.1 : ℂ)).re, (θ.2.2 / (θ.2.1 : ℂ)).im⟩ : ℂ) = _
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hθ]
      exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hθ.ne')

def coreVariable (i : Fin 5) : Poly :=
  X ⟨i.val, by omega⟩ + C Complex.I * X ⟨i.val + 5, by omega⟩
def etaVariable : Poly := X 11 + C Complex.I * X 12

/-- Conjugation fixes the real variables and conjugates only coefficients. -/
def bar (p : Poly) : Poly := map (starRingEnd ℂ) p

def adjoint {n m : Type*} (M : Matrix n m Poly) : Matrix m n Poly :=
  fun i j => bar (M j i)

def corePolynomial : Fin 2 → Matrix (Fin 2) (Fin 2) Poly :=
  ![!![coreVariable 1, coreVariable 2;
       1 - coreVariable 0 * coreVariable 1, -coreVariable 0 * coreVariable 2],
    !![coreVariable 3, coreVariable 4;
       -coreVariable 0 * coreVariable 3, 1 - coreVariable 0 * coreVariable 4]]

def leftPolynomial : Fin 2 → Poly := ![coreVariable 0, 1]

/-- G10 is sigma times eta; G01 is sigma times conjugate eta. -/
def gramPolynomial : Matrix (Fin 2) (Fin 2) Poly :=
  (X 10 : Poly) • !![1, bar etaVariable; etaVariable, etaVariable * bar etaVariable]

def prefixPolynomial : Matrix (Word 2) (Fin 2) Poly :=
  fun w => leftPolynomial ᵥ* (corePolynomial (w 0) * corePolynomial (w 1))

def transferPolynomial (H : Matrix (Fin 2) (Fin 2) Poly) : Matrix (Fin 2) (Fin 2) Poly :=
  ∑ s : Fin 2, corePolynomial s * H * adjoint (corePolynomial s)

def q2Polynomial (m : ℕ) : Matrix (Word 2) (Word 2) Poly :=
  prefixPolynomial * transferPolynomial^[m] gramPolynomial * adjoint prefixPolynomial

private abbrev evaluate (x : Coordinates) : Poly →+* ℂ := eval (fun i => (x i : ℂ))

private lemma evaluate_coreVariable (x : Coordinates) (i : Fin 5) :
    evaluate x (coreVariable i) = coreCoordinates x i := by
  apply Complex.ext <;> simp [evaluate, coreVariable, coreCoordinates]

private lemma evaluate_eta (x : Coordinates) : evaluate x etaVariable = eta x := by
  apply Complex.ext <;> simp [evaluate, etaVariable, eta]

private lemma evaluate_bar (x : Coordinates) (p : Poly) :
    evaluate x (bar p) = star (evaluate x p) := by
  have h := MvPolynomial.map_eval (starRingEnd ℂ) (fun i => (x i : ℂ)) p
  simpa [evaluate, bar, Function.comp_def] using h.symm

private lemma evaluate_adjoint {n m : Type*} (x : Coordinates) (M : Matrix n m Poly) :
    (adjoint M).map (evaluate x) = (M.map (evaluate x))ᴴ := by
  ext i j
  exact evaluate_bar x (M j i)

private lemma evaluate_core (x : Coordinates) (s : Fin 2) :
    (evaluate x).mapMatrix (corePolynomial s) = core (positiveRepresentative x) s := by
  ext i j
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    simp [corePolynomial, core, positiveRepresentative, evaluate_coreVariable]

private lemma evaluate_left (x : Coordinates) :
    (evaluate x) ∘ leftPolynomial = left (positiveRepresentative x) := by
  funext i
  fin_cases i <;> simp [leftPolynomial, left, positiveRepresentative, evaluate_coreVariable]

private lemma evaluate_prefix (x : Coordinates) :
    prefixPolynomial.map (evaluate x) =
      prefixMap (core (positiveRepresentative x)) (left (positiveRepresentative x)) 2 := by
  ext w i
  change evaluate x ((leftPolynomial ᵥ* (corePolynomial (w 0) * corePolynomial (w 1))) i) = _
  rw [RingHom.map_vecMul, Matrix.map_mul]
  change ((evaluate x ∘ leftPolynomial) ᵥ*
    ((evaluate x).mapMatrix (corePolynomial (w 0)) *
      (evaluate x).mapMatrix (corePolynomial (w 1)))) i = _
  rw [evaluate_core, evaluate_core, evaluate_left]
  simp [prefixMap, wordMatrix, List.ofFn_succ]

private lemma evaluate_gram (x : Coordinates) (hx : 0 ≤ sigma x) :
    (evaluate x).mapMatrix gramPolynomial =
      vecMulVec (right (positiveRepresentative x)) (star (right (positiveRepresentative x))) := by
  have hs : (Real.sqrt (sigma x) : ℂ) ^ 2 = (sigma x : ℂ) := by
    exact_mod_cast Real.sq_sqrt hx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramPolynomial, right, positiveRepresentative, evaluate_bar, evaluate_eta,
      vecMulVec_apply, star_mul, evaluate]
  all_goals dsimp only [sigma] at hs ⊢
  · simpa [pow_two] using hs.symm
  · linear_combination -((starRingEnd ℂ) (eta x)) * hs
  · linear_combination -(eta x) * hs
  · linear_combination -(eta x * (starRingEnd ℂ) (eta x)) * hs

private lemma evaluate_transfer (x : Coordinates) (H : Matrix (Fin 2) (Fin 2) Poly) :
    (evaluate x).mapMatrix (transferPolynomial H) =
      transfer (core (positiveRepresentative x)) ((evaluate x).mapMatrix H) := by
  simp only [transferPolynomial, transfer, map_sum, map_mul]
  congr 1
  funext s
  rw [show (evaluate x).mapMatrix (adjoint (corePolynomial s)) =
    ((evaluate x).mapMatrix (corePolynomial s))ᴴ from evaluate_adjoint x _]
  rw [evaluate_core]

private lemma evaluate_iterate (m : ℕ) (x : Coordinates) :
    (evaluate x).mapMatrix (transferPolynomial^[m] gramPolynomial) =
      (transfer (core (positiveRepresentative x)))^[m] ((evaluate x).mapMatrix gramPolynomial) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', evaluate_transfer, ih]

/-- Exact raw-prefix evaluation, for every complement length, including zero. -/
theorem q2Polynomial_eval (m : ℕ) (x : Coordinates) (hx : 0 ≤ sigma x) :
    (evaluate x).mapMatrix (q2Polynomial m) = density m (positiveRepresentative x) := by
  change (q2Polynomial m).map (evaluate x) = _
  rw [q2Polynomial, Matrix.map_mul, Matrix.map_mul,
    evaluate_adjoint, evaluate_prefix]
  have hi := evaluate_iterate m x
  change (transferPolynomial^[m] gramPolynomial).map (evaluate x) = _ at hi
  rw [hi]
  rw [evaluate_gram x hx]
  exact (density_factor 2 m (core (positiveRepresentative x))
    (left (positiveRepresentative x)) (right (positiveRepresentative x))).symm

/-- All twelve old record components, with consecutive real/imaginary pairs. -/
def recordEquiv : Record ≃ (Fin 12 → ℝ) where
  toFun r := ![r.1.1, r.1.2, r.2.1.re, r.2.1.im,
    (r.2.2 0 0).re, (r.2.2 0 0).im, (r.2.2 0 1).re, (r.2.2 0 1).im,
    (r.2.2 1 0).re, (r.2.2 1 0).im, (r.2.2 1 1).re, (r.2.2 1 1).im]
  invFun x := ((x 0, x 1), ⟨x 2, x 3⟩,
    !![⟨x 4, x 5⟩, ⟨x 6, x 7⟩; ⟨x 8, x 9⟩, ⟨x 10, x 11⟩])
  left_inv r := by
    refine Prod.ext ?_ ?_
    · exact Prod.ext rfl rfl
    refine Prod.ext ?_ ?_
    · exact Complex.ext rfl rfl
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

def recordPolynomial (m : ℕ) : Fin 12 → RealPoly :=
  ![realCoeff (q2Polynomial m ![0, 0] ![0, 0]),
    realCoeff (q2Polynomial m ![0, 1] ![0, 1]),
    realCoeff (q2Polynomial m ![0, 0] ![0, 1]),
    imagCoeff (q2Polynomial m ![0, 0] ![0, 1]),
    realCoeff (q2Polynomial m ![0, 0] ![1, 0]),
    imagCoeff (q2Polynomial m ![0, 0] ![1, 0]),
    realCoeff (q2Polynomial m ![0, 0] ![1, 1]),
    imagCoeff (q2Polynomial m ![0, 0] ![1, 1]),
    realCoeff (q2Polynomial m ![0, 1] ![1, 0]),
    imagCoeff (q2Polynomial m ![0, 1] ![1, 0]),
    realCoeff (q2Polynomial m ![0, 1] ![1, 1]),
    imagCoeff (q2Polynomial m ![0, 1] ![1, 1])]

/-- The polynomial observation is exactly the packed existing density record. -/
theorem recordPolynomial_eval (m : ℕ) (x : Coordinates) (hx : 0 ≤ sigma x) :
    (fun j => eval x (recordPolynomial m j)) =
      recordEquiv (record m (positiveRepresentative x)) := by
  have he (u v : Word 2) := congrFun (congrFun (q2Polynomial_eval m x hx) u) v
  have hr (u v : Word 2) := (coefficient_eval (q2Polynomial m u v) x).1.trans
    (congrArg Complex.re (he u v))
  have hi (u v : Word 2) := (coefficient_eval (q2Polynomial m u v) x).2.trans
    (congrArg Complex.im (he u v))
  change (fun j => eval x (recordPolynomial m j)) =
    ![(density m (positiveRepresentative x) ![0, 0] ![0, 0]).re,
      (density m (positiveRepresentative x) ![0, 1] ![0, 1]).re,
      (density m (positiveRepresentative x) ![0, 0] ![0, 1]).re,
      (density m (positiveRepresentative x) ![0, 0] ![0, 1]).im,
      (density m (positiveRepresentative x) ![0, 0] ![1, 0]).re,
      (density m (positiveRepresentative x) ![0, 0] ![1, 0]).im,
      (density m (positiveRepresentative x) ![0, 0] ![1, 1]).re,
      (density m (positiveRepresentative x) ![0, 0] ![1, 1]).im,
      (density m (positiveRepresentative x) ![0, 1] ![1, 0]).re,
      (density m (positiveRepresentative x) ![0, 1] ![1, 0]).im,
      (density m (positiveRepresentative x) ![0, 1] ![1, 1]).re,
      (density m (positiveRepresentative x) ![0, 1] ![1, 1]).im]
  funext j
  fin_cases j
  · exact hr ![0, 0] ![0, 0]
  · exact hr ![0, 1] ![0, 1]
  · exact hr ![0, 0] ![0, 1]
  · exact hi ![0, 0] ![0, 1]
  · exact hr ![0, 0] ![1, 0]
  · exact hi ![0, 0] ![1, 0]
  · exact hr ![0, 0] ![1, 1]
  · exact hi ![0, 0] ![1, 1]
  · exact hr ![0, 1] ![1, 0]
  · exact hi ![0, 1] ![1, 0]
  · exact hr ![0, 1] ![1, 1]
  · exact hi ![0, 1] ![1, 1]

private lemma record_equality_density (m : ℕ) {x y : Coordinates}
    (hx : 0 < sigma x) (hy : 0 < sigma y)
    (hH : (leading (density m (positiveRepresentative x))).det ≠ 0)
    (h : ∀ j, eval y (recordPolynomial m j) = eval x (recordPolynomial m j)) :
    density m (positiveRepresentative y) = density m (positiveRepresentative x) := by
  have he : record m (positiveRepresentative x) = record m (positiveRepresentative y) := by
    apply recordEquiv.injective
    rw [← recordPolynomial_eval m x hx.le, ← recordPolynomial_eval m y hy.le]
    exact (funext h).symm
  exact (densityRecord_injective (density_hermitian m _) (density_hermitian m _)
    (density_rank m _) (density_rank m _) (isUnit_iff_ne_zero.mpr hH) he).symm

/-- Q2 has complement length 1+k, whereas the coherent Q3 chart has complement k. -/
def validityDomain (k : ℕ) : Set Coordinates :=
  {x | 0 < sigma x ∧ positiveRepresentative x ∈ canonicalChart k}

private lemma validity_open (k : ℕ) : IsOpen (validityDomain k) := by
  change IsOpen ({x : Coordinates | 0 < sigma x} ∩
    positiveRepresentative ⁻¹' canonicalChart k)
  exact (isOpen_lt continuous_const (continuous_apply 10)).inter
    ((isOpen_canonicalChart k).preimage representative_continuous)

private lemma validity_nonempty (k : ℕ) : (validityDomain k).Nonempty := by
  obtain ⟨θ, hθ⟩ := canonicalChart_nonempty k
  refine ⟨coordinatesOf θ, ?_, ?_⟩
  · change 0 < θ.2.1 ^ 2
    exact sq_pos_of_pos hθ.1
  · rwa [representative_coordinatesOf θ hθ.1]

/-- A principal generic locus in the canonical parameter domain. This definition
does not assert density in the actual MPS image or in a phase quotient. -/
def genericLocus (k : ℕ) (D : RealPoly) : Set Coordinates :=
  validityDomain k ∩ {x | eval x D ≠ 0}

/-- Through every certified parameter, every specified open neighborhood inside
the validity domain contains a positive-dimensional C1 same-Q2 fiber. Distinct
fiber points give actual states that are not unit-phase equivalent. The density
assertion is relative to the canonical parameter domain only. -/
theorem exists_generic_fiber (k : ℕ) :
    ∃ D : RealPoly, D ≠ 0 ∧ (∃ a₀ : Coordinates, eval a₀ D = 1) ∧
      IsOpen (validityDomain k) ∧ (validityDomain k).Nonempty ∧
      IsOpen (genericLocus k D) ∧ (genericLocus k D).Nonempty ∧
      Dense {x : validityDomain k | eval (x : Coordinates) D ≠ 0} ∧
      ∀ x ∈ genericLocus k D, ∀ U : Set Coordinates, IsOpen U → x ∈ U →
        U ⊆ validityDomain k →
        ∃ (K : Submodule ℝ Coordinates) (q : Coordinates →L[ℝ] K)
          (f : K → Coordinates) (ε : ℝ),
          0 < ε ∧ 0 < Module.finrank ℝ K ∧
          Module.finrank ℝ K + Module.finrank ℝ (LinearMap.range
            (fderiv ℝ (fun y j => eval y (recordPolynomial (1 + k) j)) x).toLinearMap) = 13 ∧
          f 0 = x ∧ ContDiffOn ℝ 1 f (Metric.ball 0 ε) ∧
          (∀ z ∈ Metric.ball 0 ε,
            f z ∈ U ∩ genericLocus k D ∧
            density (1 + k) (positiveRepresentative (f z)) =
              density (1 + k) (positiveRepresentative x) ∧
            q (f z - x) = z ∧
            (z ≠ 0 → ¬ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
              state (3 + k) (positiveRepresentative (f z)) =
                ζ • state (3 + k) (positiveRepresentative x))) ∧
          ∃ y ∈ U ∩ genericLocus k D, y ≠ x ∧
            density (1 + k) (positiveRepresentative y) =
              density (1 + k) (positiveRepresentative x) ∧
            ¬ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ state (3 + k) (positiveRepresentative y) =
              ζ • state (3 + k) (positiveRepresentative x) := by
  obtain ⟨D, hD, hw, hfiber⟩ :=
    D5.S3.Geometry.PolynomialLocalFiber.exists_rank_fiber_polynomial (recordPolynomial (1 + k))
  have hO := validity_open k
  have hOne := validity_nonempty k
  obtain ⟨a₀, ha₀⟩ := hw
  have hdense := polynomial_nonzero_dense D a₀ (by rw [ha₀]; norm_num)
  have hprincipal : IsOpen {x : Coordinates | eval x D ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval D) continuous_const
  have hgeneric : IsOpen (genericLocus k D) := hO.inter hprincipal
  have hne : (genericLocus k D).Nonempty :=
    hdense.inter_open_nonempty _ hO hOne
  refine ⟨D, hD, ⟨a₀, ha₀⟩, hO, hOne, hgeneric, hne,
    hdense.preimage hO.isOpenMap_subtype_val, ?_⟩
  intro x hx U hU hxU hUO
  have hxO := hx.1
  have no_phase {y : Coordinates} (hy : y ∈ validityDomain k) (hne : y ≠ x) :
      ¬ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ state (3 + k) (positiveRepresentative y) =
        ζ • state (3 + k) (positiveRepresentative x) := by
    rintro ⟨ζ, hζ, he⟩
    have hp := phase_rigidity k hxO.2 hy.2 ζ hζ he
    exact hne (representative_injective hxO.1 hy.1 hp).symm
  obtain ⟨K, q, f, ε, hε, hdim, hf0, hfc, hf, hpos⟩ :=
    (hfiber x hx.2).2 (U ∩ genericLocus k D) (hU.inter hgeneric) ⟨hxU, hx⟩
  obtain ⟨hdimpos, y, hy, hyx, heval⟩ := hpos (by decide)
  have lift_eq {y : Coordinates} (hy : y ∈ validityDomain k)
      (he : ∀ j, eval y (recordPolynomial (1 + k) j) =
        eval x (recordPolynomial (1 + k) j)) :
      density (1 + k) (positiveRepresentative y) =
        density (1 + k) (positiveRepresentative x) :=
    record_equality_density (1 + k) hxO.1 hy.1 hxO.2.2.2.2 he
  refine ⟨K, q, f, ε, hε, hdimpos, hdim, hf0, hfc, ?_,
    y, hy, hyx, lift_eq (hUO hy.1) heval, no_phase (hUO hy.1) hyx⟩
  intro z hz
  obtain ⟨hzU, hzeval, hzq⟩ := hf z hz
  refine ⟨hzU, lift_eq (hUO hzU.1) hzeval, hzq, ?_⟩
  intro hz0
  apply no_phase (hUO hzU.1)
  intro he
  apply hz0
  simpa [he] using hzq.symm


abbrev QuotientIndex := OpenBoundaryMPSQuotient.QuotientRealIndex

def quotientIndexEquiv : QuotientIndex ≃ Fin 13 :=
  (Equiv.sumCongr (Equiv.refl (Fin 5)) (finSumFinEquiv (m := 5) (n := 3))).trans
    (finSumFinEquiv (m := 5) (n := 8))

def quotientCoordinates13 (p : OpenBoundaryMPSQuotient.Quotient) : Coordinates :=
  fun j => OpenBoundaryMPSQuotient.quotientRealCoordinates p (quotientIndexEquiv.symm j)

def leadingPolynomial (m : ℕ) : RealPoly :=
  let d : Poly :=
    q2Polynomial (1 + m) ![0, 0] ![0, 0] * q2Polynomial (1 + m) ![0, 1] ![0, 1] -
      q2Polynomial (1 + m) ![0, 0] ![0, 1] * q2Polynomial (1 + m) ![0, 1] ![0, 0]
  realCoeff d * realCoeff d + imagCoeff d * imagCoeff d

private lemma leadingPolynomial_eval (m : ℕ) (x : Coordinates) (hx : 0 ≤ sigma x) :
    eval x (leadingPolynomial m) = Complex.normSq
      (leading (density (1 + m) (positiveRepresentative x))).det := by
  let d : Poly :=
    q2Polynomial (1 + m) ![0, 0] ![0, 0] * q2Polynomial (1 + m) ![0, 1] ![0, 1] -
      q2Polynomial (1 + m) ![0, 0] ![0, 1] * q2Polynomial (1 + m) ![0, 1] ![0, 0]
  let ceval : Poly →+* ℂ := eval (fun i => (x i : ℂ))
  have hd := coefficient_eval d x
  have he := q2Polynomial_eval (1 + m) x hx
  have hdet : ceval d = (leading (density (1 + m) (positiveRepresentative x))).det := by
    change ceval (_ * _ - _ * _) = _
    rw [map_sub, map_mul, map_mul]
    change _ * _ - _ * _ = _
    rw [show ceval (q2Polynomial (1 + m) ![0, 0] ![0, 0]) = _ from congrFun (congrFun he ![0,0]) ![0,0],
      show ceval (q2Polynomial (1 + m) ![0, 1] ![0, 1]) = _ from congrFun (congrFun he ![0,1]) ![0,1],
      show ceval (q2Polynomial (1 + m) ![0, 0] ![0, 1]) = _ from congrFun (congrFun he ![0,0]) ![0,1],
      show ceval (q2Polynomial (1 + m) ![0, 1] ![0, 0]) = _ from congrFun (congrFun he ![0,1]) ![0,0]]
    simpa only [Matrix.det_fin_two, leading]
  dsimp only [d, leadingPolynomial]
  rw [← hdet]
  simp only [map_add, map_mul]
  simp only [Complex.normSq_apply]
  rw [show eval x (realCoeff d) = (ceval d).re from hd.1,
    show eval x (imagCoeff d) = (ceval d).im from hd.2]


private lemma clear_polynomial {σ κ : Type*}
    (P : MvPolynomial σ ℝ) (N D : σ → MvPolynomial κ ℝ) :
    ∃ H B : MvPolynomial κ ℝ, ∀ a : κ → ℝ, (∀ i, eval a (D i) ≠ 0) →
      eval a B ≠ 0 ∧
      eval (fun i => eval a (N i) / eval a (D i)) P = eval a H / eval a B := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      refine ⟨C c, 1, ?_⟩
      intro a ha
      simp
  | add p q hp hq =>
      obtain ⟨Hp, Bp, hp⟩ := hp
      obtain ⟨Hq, Bq, hq⟩ := hq
      refine ⟨Hp * Bq + Hq * Bp, Bp * Bq, ?_⟩
      intro a ha
      obtain ⟨hBp, hp⟩ := hp a ha
      obtain ⟨hBq, hq⟩ := hq a ha
      refine ⟨(by simpa only [map_mul] using mul_ne_zero hBp hBq), ?_⟩
      simp only [map_add, map_mul]
      rw [hp, hq]
      field_simp
  | mul_X p i hp =>
      obtain ⟨Hp, Bp, hp⟩ := hp
      refine ⟨N i * Hp, D i * Bp, ?_⟩
      intro a ha
      obtain ⟨hBp, hp⟩ := hp a ha
      refine ⟨(by simpa only [map_mul] using mul_ne_zero (ha i) hBp), ?_⟩
      simp only [map_mul, eval_X]
      rw [hp]
      field_simp

def quotientRecordTarget (m : ℕ) : Fin 12 → RealPoly := recordPolynomial (1 + m)

def quotientLeadingTarget (m : ℕ) : RealPoly := leadingPolynomial m

def quotientFiberTarget (m : ℕ) (J : RealPoly) : RealPoly :=
  J * quotientLeadingTarget m

private lemma quotientFiberTarget_eval (m : ℕ) (J : RealPoly) (x : Coordinates)
    (hx : 0 ≤ sigma x) :
    eval x (quotientFiberTarget m J) = eval x J *
      Complex.normSq (leading (density (1 + m) (positiveRepresentative x))).det := by
  rw [quotientFiberTarget]
  simp only [map_mul]
  change _ * eval x (leadingPolynomial m) = _
  rw [leadingPolynomial_eval m x hx]

private lemma quotientCoordinate_ratio (m : ℕ) (Q : Matrix (Word 3) (Word 3) ℂ)
    (hQ : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => Q ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0)
    (j : Fin 13) :
    let a := OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => Q ij.1 ij.2)
    eval a (OpenBoundaryMPSQuotient.quotientRealNumerator m (quotientIndexEquiv.symm j)) /
      eval a (OpenBoundaryMPSQuotient.quotientRealDenominator m (quotientIndexEquiv.symm j)) =
      quotientCoordinates13 (OpenBoundaryMPSQuotient.quotientCoordinates m Q) j := by
  dsimp [quotientCoordinates13]
  have hr := (OpenBoundaryMPSQuotient.rational_quotient_inverse m Q hQ).2.1
    (quotientIndexEquiv.symm j)
  exact hr.2

private lemma quotient_denominators_nonzero (m : ℕ) (Q : Matrix (Word 3) (Word 3) ℂ)
    (hQ : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => Q ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0) :
    ∀ j : Fin 13, eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => Q ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientRealDenominator m (quotientIndexEquiv.symm j)) ≠ 0 := by
  intro j
  have hr := (OpenBoundaryMPSQuotient.rational_quotient_inverse m Q hQ).2.1
    (quotientIndexEquiv.symm j)
  exact ne_of_gt hr.1


def parameterVar (i : OpenBoundaryMPSMarginalBirationality.parameterIndex) :
    MvPolynomial (OpenBoundaryMPSMarginalBirationality.parameterIndex ⊕
      OpenBoundaryMPSMarginalBirationality.parameterIndex) ℂ :=
  X (.inl i) + C Complex.I * X (.inr i)

def parameterConjVar (i : OpenBoundaryMPSMarginalBirationality.parameterIndex) :
    MvPolynomial (OpenBoundaryMPSMarginalBirationality.parameterIndex ⊕
      OpenBoundaryMPSMarginalBirationality.parameterIndex) ℂ :=
  X (.inl i) - C Complex.I * X (.inr i)

abbrev ParamRealIndex := OpenBoundaryMPSMarginalBirationality.parameterIndex ⊕
  OpenBoundaryMPSMarginalBirationality.parameterIndex
abbrev ObsIndex := OpenBoundaryMPSQuotient.ObservationIndex

def rawParamPolynomial (m : ℕ) (ij : ObsIndex) : MvPolynomial ParamRealIndex ℂ :=
  ∑ b : Word m,
    eval₂Hom C parameterVar (OpenBoundaryMPSMarginalBirationality.parameterPolys
      (3 + m) (Fin.append ij.1 b)) *
      eval₂Hom C parameterConjVar (map (starRingEnd ℂ) (OpenBoundaryMPSMarginalBirationality.parameterPolys
        (3 + m) (Fin.append ij.2 b)))

def rawParamCoordinates (m : ℕ) : ObsIndex ⊕ ObsIndex → MvPolynomial ParamRealIndex ℝ :=
  Sum.elim (fun ij => realCoeff (rawParamPolynomial m ij))
    (fun ij => imagCoeff (rawParamPolynomial m ij))

private lemma parameterVar_eval (x : OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ)
    (i : OpenBoundaryMPSMarginalBirationality.parameterIndex) :
    eval (fun i => (OpenBoundaryMPSDensityGenericity.realCoordinates x i : ℂ)) (parameterVar i) = x i := by
  simp only [parameterVar, map_add, map_mul, eval_X, eval_C]
  cases i with
  | inl i => simp [OpenBoundaryMPSDensityGenericity.realCoordinates]; apply Complex.ext <;> simp [Complex.star_def]
  | inr i => simp [OpenBoundaryMPSDensityGenericity.realCoordinates]; apply Complex.ext <;> simp [Complex.star_def]

private lemma parameterConjVar_eval (x : OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ)
    (i : OpenBoundaryMPSMarginalBirationality.parameterIndex) :
    eval (fun i => (OpenBoundaryMPSDensityGenericity.realCoordinates x i : ℂ)) (parameterConjVar i) = star (x i) := by
  simp only [parameterConjVar, map_sub, map_add, map_mul, eval_X, eval_C]
  cases i with
  | inl i => simp [OpenBoundaryMPSDensityGenericity.realCoordinates]; apply Complex.ext <;> simp [Complex.star_def]
  | inr i => simp [OpenBoundaryMPSDensityGenericity.realCoordinates]; apply Complex.ext <;> simp [Complex.star_def]

private lemma parameterPolynomial_eval_complex (x : OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ)
    (p : MvPolynomial OpenBoundaryMPSMarginalBirationality.parameterIndex ℂ) :
    eval (fun i => (OpenBoundaryMPSDensityGenericity.realCoordinates x i : ℂ))
      (eval₂Hom C parameterVar p) = eval x p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.eval₂Hom_X', hp, parameterVar_eval, eval_X]

private lemma parameterConjPolynomial_eval_complex (x : OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ)
    (p : MvPolynomial OpenBoundaryMPSMarginalBirationality.parameterIndex ℂ) :
    eval (fun i => (OpenBoundaryMPSDensityGenericity.realCoordinates x i : ℂ))
      (eval₂Hom C parameterConjVar p) = eval (fun i => star (x i)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.eval₂Hom_X', hp, parameterConjVar_eval, eval_X]

private lemma conjugate_parameter_polynomial_eval
    (x : OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ)
    (p : MvPolynomial OpenBoundaryMPSMarginalBirationality.parameterIndex ℂ) :
    eval (fun i => star (x i)) (map (starRingEnd ℂ) p) = star (eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
      simp only [map_add, hp, hq]
      exact (map_add (starRingEnd ℂ) ((eval x) p) ((eval x) q)).symm
  | mul_X p i hp =>
      simp only [map_mul, map_X, eval_X, hp]
      exact (map_mul (starRingEnd ℂ) ((eval x) p) (x i)).symm

private lemma rawParamPolynomial_eval (m : ℕ)
    (x : OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ) (ij : ObsIndex) :
    eval (fun i => (OpenBoundaryMPSDensityGenericity.realCoordinates x i : ℂ))
      (rawParamPolynomial m ij) =
      OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
        (fun w => eval x (OpenBoundaryMPSMarginalBirationality.parameterPolys (3 + m) w))
        ij.1 ij.2 := by
  simp only [rawParamPolynomial, map_sum, map_mul,
    parameterPolynomial_eval_complex, parameterConjPolynomial_eval_complex,
    conjugate_parameter_polynomial_eval]
  simp [OpenBoundaryMPSDensityRecovery.rawPrefix,
    OpenBoundaryMPSDensityRecovery.amplitudeColumns, Matrix.mul_apply, dotProduct,
    conjTranspose_apply]

private lemma rawParamCoordinates_eval (m : ℕ)
    (x : OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ) :
    eval (OpenBoundaryMPSDensityGenericity.realCoordinates x) ∘ rawParamCoordinates m =
      OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
          (fun w => eval x (OpenBoundaryMPSMarginalBirationality.parameterPolys (3 + m) w))
          ij.1 ij.2) := by
  funext u
  cases u with
  | inl u =>
    exact (coefficient_eval (rawParamPolynomial m u)
      (OpenBoundaryMPSDensityGenericity.realCoordinates x)).1.trans
      (congrArg Complex.re (rawParamPolynomial_eval m x u))
  | inr u =>
    exact (coefficient_eval (rawParamPolynomial m u)
      (OpenBoundaryMPSDensityGenericity.realCoordinates x)).2.trans
      (congrArg Complex.im (rawParamPolynomial_eval m x u))

def parameterPullback (m : ℕ) (R : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ) :
    MvPolynomial ParamRealIndex ℝ :=
  eval₂Hom C (rawParamCoordinates m) R

private lemma parameterPullback_eval (m : ℕ) (R : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ)
    (x : OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ) :
    eval (OpenBoundaryMPSDensityGenericity.realCoordinates x) (parameterPullback m R) =
      eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
          (fun w => eval x (OpenBoundaryMPSMarginalBirationality.parameterPolys (3 + m) w))
          ij.1 ij.2)) R := by
  change eval (OpenBoundaryMPSDensityGenericity.realCoordinates x)
    (eval₂ C (rawParamCoordinates m) R) = _
  rw [← eval_assoc, rawParamCoordinates_eval]


def actualPrincipalLocus (m : ℕ) (R : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ) :
    Set (OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m)) :=
  {ψ | eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
        (ψ : Word (3 + m) → ℂ) ij.1 ij.2)) R ≠ 0}

def complexParameters' (a : ParamRealIndex → ℝ) :
    OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ :=
  fun i => (a (.inl i) : ℂ) + Complex.I * (a (.inr i) : ℂ)

private lemma complexParameters'_realCoordinates (a : ParamRealIndex → ℝ) :
    OpenBoundaryMPSDensityGenericity.realCoordinates (complexParameters' a) = a := by
  funext i
  cases i <;> simp [complexParameters', OpenBoundaryMPSDensityGenericity.realCoordinates]

private lemma complexParameters'_complexRealCoordinates
    (x : OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ) :
    complexParameters' (OpenBoundaryMPSDensityGenericity.realCoordinates x) = x := by
  funext i
  apply Complex.ext <;> simp [complexParameters', OpenBoundaryMPSDensityGenericity.realCoordinates]

private lemma complexParameters'_continuous :
    Continuous (complexParameters' : (ParamRealIndex → ℝ) →
      OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ) := by
  apply continuous_pi
  intro i
  simp only [complexParameters']
  fun_prop

theorem actual_principal_genericity (m : ℕ)
    (R : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ)
    (hw : ∃ ψ : OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m),
      eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
          (ψ : Word (3 + m) → ℂ) ij.1 ij.2)) R ≠ 0) :
    (actualPrincipalLocus m R).Nonempty ∧ IsOpen (actualPrincipalLocus m R) ∧
      Dense (actualPrincipalLocus m R) := by
  let f : (ParamRealIndex → ℝ) → Word (3 + m) → ℂ :=
    fun a w => eval (complexParameters' a)
      (OpenBoundaryMPSMarginalBirationality.parameterPolys (3 + m) w)
  have hf : Continuous f := by
    apply continuous_pi
    intro w
    apply (MvPolynomial.continuous_eval
      (OpenBoundaryMPSMarginalBirationality.parameterPolys (3 + m) w)).comp
    exact complexParameters'_continuous
  have hrange : Set.range f = OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m) := by
    rw [OpenBoundaryMPSMarginalBirationality.parameter_image]
    ext ψ
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨complexParameters' a, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨OpenBoundaryMPSDensityGenericity.realCoordinates x, ?_⟩
      simp only [f]
      funext w
      rw [complexParameters'_complexRealCoordinates]
  obtain ⟨ψ, hψ⟩ := hw
  have hψrange : (ψ : Word (3 + m) → ℂ) ∈ Set.range f := by
    rw [hrange]
    exact ψ.property
  obtain ⟨a, ha⟩ := Set.mem_range.mp hψrange
  have hpa : eval a (parameterPullback m R) ≠ 0 := by
    rw [← complexParameters'_realCoordinates a]
    rw [parameterPullback_eval m R (complexParameters' a)]
    rw [← ha] at hψ
    exact hψ
  have hd := polynomial_nonzero_dense (parameterPullback m R) a hpa
  have hset : actualPrincipalLocus m R =
      {ψ : OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m) |
        eval (OpenBoundaryMPSDensityGenericity.realCoordinates
          (fun ij => OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
            (ψ : Word (3 + m) → ℂ) ij.1 ij.2)) R ≠ 0} := rfl
  have hraw : Continuous (fun ψ : OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m) =>
      fun ij : ObsIndex => OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
        (ψ : Word (3 + m) → ℂ) ij.1 ij.2) := by
    apply continuous_pi
    intro ij
    change Continuous (fun ψ : OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m) =>
      ∑ b : Word m, (ψ : Word (3 + m) → ℂ) (Fin.append ij.1 b) *
        star ((ψ : Word (3 + m) → ℂ) (Fin.append ij.2 b)))
    apply continuous_finset_sum Finset.univ
    intro b hb
    exact ((continuous_apply (Fin.append ij.1 b)).comp continuous_subtype_val).mul
      (Continuous.star ((continuous_apply (Fin.append ij.2 b)).comp continuous_subtype_val))

  have hrc : Continuous (OpenBoundaryMPSDensityGenericity.realCoordinates :
      (ObsIndex → ℂ) → (ObsIndex ⊕ ObsIndex → ℝ)) := by
    apply continuous_pi
    intro i
    cases i with
    | inl ij => exact Complex.continuous_re.comp (continuous_apply ij)
    | inr ij => exact Complex.continuous_im.comp (continuous_apply ij)
  have hopen : IsOpen (actualPrincipalLocus m R) := by
    exact isOpen_ne.preimage ((MvPolynomial.continuous_eval R).comp
      (hrc.comp hraw))
  refine ⟨?_, hopen, ?_⟩
  · refine ⟨⟨f a, by rw [← hrange]; exact Set.mem_range_self a⟩, ?_⟩
    change eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
        (f a) ij.1 ij.2)) R ≠ 0
    rw [← parameterPullback_eval m R (complexParameters' a),
      complexParameters'_realCoordinates]
    exact hpa
  · apply Subtype.dense_iff.mpr
    intro ψ hψ'
    have hψrange : ψ ∈ Set.range f := by
      have ht : ψ ∈ OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m) := hψ'
      rw [← hrange] at ht
      exact ht
    obtain ⟨a₀, ha₀⟩ := Set.mem_range.mp hψrange
    apply Set.mem_of_subset_of_mem (closure_mono ?_)
      (hf.range_subset_closure_image_dense hd (by rw [hrange]; exact hψ'))
    rintro y ⟨b, hb, rfl⟩
    have hgood : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
          (f b) ij.1 ij.2)) R ≠ 0 := by
      rw [← parameterPullback_eval m R (complexParameters' b),
        complexParameters'_realCoordinates]
      exact hb
    exact ⟨⟨f b, by rw [← hrange]; exact Set.mem_range_self b⟩, hgood, rfl⟩


/-- The quotient-locus polynomial is nonzero on a nonempty open dense subset of the
literal actual MPS image. This is the intrinsic source-side density bridge used
by the later Q2 fiber descent. -/
theorem quotient_locus_actual_genericity (m : ℕ) :
    (actualPrincipalLocus m (OpenBoundaryMPSQuotient.quotientLocusPolynomial m)).Nonempty ∧
      IsOpen (actualPrincipalLocus m (OpenBoundaryMPSQuotient.quotientLocusPolynomial m)) ∧
      Dense (actualPrincipalLocus m (OpenBoundaryMPSQuotient.quotientLocusPolynomial m)) := by
  have hw := OpenBoundaryMPSQuotient.quotient_locus_witness m
  dsimp only at hw
  rcases hw with ⟨hψ, hQ, hrec, h00⟩
  apply actual_principal_genericity m (OpenBoundaryMPSQuotient.quotientLocusPolynomial m)
  refine ⟨⟨_, hψ⟩, ?_⟩
  exact hQ

private def quotientRawPrefix (m : ℕ) (x : Coordinates) : Matrix (Word 3) (Word 3) ℂ :=
  OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
    (OpenBoundaryMPSTwoSiteMinimality.state (3 + m) (positiveRepresentative x))

private def parameterCoordinatesParameter
    (θ : OpenBoundaryMPSTwoSiteMinimality.Parameter) :
    OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ :=
  Sum.elim
    (fun t => OpenBoundaryMPSTwoSiteMinimality.core θ t.1 t.2.1 t.2.2)
    (Sum.elim
      (fun i => OpenBoundaryMPSTwoSiteMinimality.left θ i)
      (fun i => OpenBoundaryMPSTwoSiteMinimality.right θ i))

private def parameterCoordinates (x : Coordinates) :
    OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ :=
  parameterCoordinatesParameter (positiveRepresentative x)

private lemma parameterCoordinates_eval (m : ℕ) (x : Coordinates) :
    (fun w => eval (parameterCoordinates x)
      (OpenBoundaryMPSMarginalBirationality.parameterPolys (3 + m) w)) =
      OpenBoundaryMPSTwoSiteMinimality.state (3 + m) (positiveRepresentative x) := by
  have h := OpenBoundaryMPSMarginalBirationality.parameter_eval (3 + m)
    (parameterCoordinates x)
  change (fun w => eval (parameterCoordinates x)
      (OpenBoundaryMPSMarginalBirationality.parameterPolys (3 + m) w)) =
    OpenBoundaryMPSMarginalBirationality.mpsState (3 + m)
      (OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative x) 0)
      (OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative x) 1)
      (OpenBoundaryMPSTwoSiteMinimality.left (positiveRepresentative x))
      (OpenBoundaryMPSTwoSiteMinimality.right (positiveRepresentative x))
  convert h using 1 <;>
    ext <;> rfl

private lemma parameterCoordinatesParameter_continuous :
    Continuous (parameterCoordinatesParameter :
      OpenBoundaryMPSTwoSiteMinimality.Parameter →
        OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ) := by
  apply continuous_pi
  intro i
  cases i with
  | inl t =>
      rcases t with ⟨s, ⟨j, k⟩⟩
      fin_cases s <;> fin_cases j <;> fin_cases k <;>
        simp [parameterCoordinatesParameter, OpenBoundaryMPSTwoSiteMinimality.core]
        <;> fun_prop
  | inr i =>
      cases i with
      | inl j =>
          fin_cases j <;>
            simp [parameterCoordinatesParameter, OpenBoundaryMPSTwoSiteMinimality.left]
            <;> fun_prop
      | inr j =>
          fin_cases j
          · exact Complex.continuous_ofReal.comp
              (continuous_fst.comp
                (continuous_snd : Continuous
                  (fun θ : OpenBoundaryMPSTwoSiteMinimality.Parameter => θ.2)))
          · exact continuous_snd.comp
              (continuous_snd : Continuous
                (fun θ : OpenBoundaryMPSTwoSiteMinimality.Parameter => θ.2))

private lemma parameterCoordinates_continuous :
    Continuous (parameterCoordinates : Coordinates →
      OpenBoundaryMPSMarginalBirationality.parameterIndex → ℂ) := by
  change Continuous (parameterCoordinatesParameter ∘ positiveRepresentative)
  exact parameterCoordinatesParameter_continuous.comp representative_continuous

private lemma quotientRawPrefix_continuous (m : ℕ) :
    Continuous (quotientRawPrefix m) := by
  have hc : Continuous (fun x : Coordinates =>
      OpenBoundaryMPSTwoSiteMinimality.state (3 + m) (positiveRepresentative x)) :=
    by
      have hpar : Continuous (fun x : Coordinates =>
          fun w => eval (parameterCoordinates x)
            (OpenBoundaryMPSMarginalBirationality.parameterPolys (3 + m) w)) := by
        apply continuous_pi
        intro w
        exact (MvPolynomial.continuous_eval _).comp parameterCoordinates_continuous
      exact hpar.congr (fun x => parameterCoordinates_eval m x)
  apply continuous_matrix
  intro u v
  unfold quotientRawPrefix OpenBoundaryMPSDensityRecovery.rawPrefix
  simp only [Matrix.mul_apply, OpenBoundaryMPSDensityRecovery.amplitudeColumns,
    Matrix.conjTranspose_apply]
  apply continuous_finset_sum Finset.univ
  intro b hb
  exact ((continuous_apply (Fin.append u b)).comp hc).mul
    (Continuous.star ((continuous_apply (Fin.append v b)).comp hc))

private lemma positiveRepresentative_witness (m : ℕ) :
    positiveRepresentative (coordinatesOf (witnessParameter m)) = witnessParameter m := by
  apply representative_coordinatesOf
  dsimp [witnessParameter]
  positivity

private def quotientValidityDomain (m : ℕ) : Set Coordinates :=
  {x | 0 < sigma x ∧
    eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0 ∧
    eval x (leadingPolynomial m) ≠ 0}

private lemma quotientValidityDomain_open (m : ℕ) :
    IsOpen (quotientValidityDomain m) := by
  unfold quotientValidityDomain
  have hcoords : Continuous (fun x : Coordinates =>
      OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij : ObsIndex => quotientRawPrefix m x ij.1 ij.2)) := by
    have hraw : Continuous (fun x : Coordinates =>
        (fun ij : ObsIndex => quotientRawPrefix m x ij.1 ij.2)) := by
      apply continuous_pi
      intro ij
      exact (continuous_apply ij.2).comp
        ((continuous_apply ij.1).comp (quotientRawPrefix_continuous m))
    apply continuous_pi
    intro i
    cases i with
    | inl ij => exact Complex.continuous_re.comp ((continuous_apply ij).comp hraw)
    | inr ij => exact Complex.continuous_im.comp ((continuous_apply ij).comp hraw)
  apply (isOpen_lt continuous_const (continuous_apply 10)).inter
  apply IsOpen.inter
  · exact isOpen_ne.preimage ((MvPolynomial.continuous_eval _).comp
      hcoords)
  · exact isOpen_ne.preimage (MvPolynomial.continuous_eval _)

set_option maxHeartbeats 800000 in
private lemma quotientValidityDomain_nonempty (m : ℕ) :
    (quotientValidityDomain m).Nonempty := by
  let x₀ := coordinatesOf (witnessParameter m)
  have hrep : positiveRepresentative x₀ = witnessParameter m := by
    exact positiveRepresentative_witness m
  have hwit := OpenBoundaryMPSQuotient.quotient_locus_witness m
  dsimp only at hwit
  rcases hwit with ⟨hψ, hQ, hg, h00⟩
  have hw := OpenBoundaryMPSTwoSiteMinimality.witness_gauge m
  have hρ : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x₀ ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0 := by
    simpa [quotientRawPrefix, hrep, hw] using hQ
  have hσ : 0 < sigma x₀ := by
    dsimp [x₀, sigma, coordinatesOf]
    dsimp [witnessParameter]
    norm_num
  obtain ⟨θ, hθpos, hθchart, hθcore, hθlead⟩ :=
    OpenBoundaryMPSTwoSiteMinimality.canonicalChart_nonempty m
  have hθrep : positiveRepresentative (coordinatesOf θ) = θ :=
    representative_coordinatesOf θ hθpos
  have hLθ : eval (coordinatesOf θ) (leadingPolynomial m) ≠ 0 := by
    rw [leadingPolynomial_eval m (coordinatesOf θ) (by
      dsimp [sigma, coordinatesOf]
      positivity)]
    rw [hθrep]
    exact fun hz => hθlead ((Complex.normSq_eq_zero.mp hz))
  have hLdense := polynomial_nonzero_dense (leadingPolynomial m)
    (coordinatesOf θ) hLθ
  let R : Set Coordinates := {x | 0 < sigma x ∧
    eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0}
  have hRopen : IsOpen R := by
    unfold R
    have hcoords : Continuous (fun x : Coordinates =>
        OpenBoundaryMPSDensityGenericity.realCoordinates
          (fun ij : ObsIndex => quotientRawPrefix m x ij.1 ij.2)) := by
      have hraw : Continuous (fun x : Coordinates =>
          (fun ij : ObsIndex => quotientRawPrefix m x ij.1 ij.2)) := by
        apply continuous_pi
        intro ij
        exact (continuous_apply ij.2).comp
          ((continuous_apply ij.1).comp (quotientRawPrefix_continuous m))
      apply continuous_pi
      intro i
      cases i with
      | inl ij => exact Complex.continuous_re.comp ((continuous_apply ij).comp hraw)
      | inr ij => exact Complex.continuous_im.comp ((continuous_apply ij).comp hraw)
    apply (isOpen_lt continuous_const (continuous_apply 10)).inter
    exact isOpen_ne.preimage ((MvPolynomial.continuous_eval _).comp hcoords)
  have hRne : R.Nonempty := ⟨x₀, hσ, hρ⟩
  obtain ⟨x, hxR, hxL⟩ := hLdense.inter_open_nonempty R hRopen hRne
  exact ⟨x, hxR.1, hxR.2, hxL⟩

private lemma rawPrefix_scale_local (k m : ℕ) (z : ℂ)
    (ψ : Word (k + m) → ℂ) :
    OpenBoundaryMPSDensityRecovery.rawPrefix k m (z • ψ) =
      (Complex.normSq z : ℂ) • OpenBoundaryMPSDensityRecovery.rawPrefix k m ψ := by
  unfold OpenBoundaryMPSDensityRecovery.rawPrefix
  have hC : OpenBoundaryMPSDensityRecovery.amplitudeColumns k m (z • ψ) =
      z • OpenBoundaryMPSDensityRecovery.amplitudeColumns k m ψ := rfl
  rw [hC, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  change (z * (starRingEnd ℂ) z) • _ = _
  rw [Complex.mul_conj]

private lemma positiveBoundary_state_eq (m : ℕ)
    (p : OpenBoundaryMPSQuotient.Quotient) :
    OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
        (p.1, Real.sqrt p.2.1, (Real.sqrt p.2.1 : ℂ) * p.2.2) =
      OpenBoundaryMPSMarginalBirationality.mpsState (3 + m)
        (OpenBoundaryMPSTwoSiteMinimality.core p 0)
        (OpenBoundaryMPSTwoSiteMinimality.core p 1)
        (OpenBoundaryMPSTwoSiteMinimality.left p)
        (OpenBoundaryMPSQuotient.positiveBoundary p) := by
  funext w
  rfl

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_zero : quotientIndexEquiv.symm 0 = Sum.inl 0 := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_one : quotientIndexEquiv.symm 1 = Sum.inl 1 := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_two : quotientIndexEquiv.symm 2 = Sum.inl 2 := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_three : quotientIndexEquiv.symm 3 = Sum.inl 3 := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_four : quotientIndexEquiv.symm 4 = Sum.inl 4 := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_five : quotientIndexEquiv.symm 5 = Sum.inr (Sum.inl 0) := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_six : quotientIndexEquiv.symm 6 = Sum.inr (Sum.inl 1) := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_seven : quotientIndexEquiv.symm 7 = Sum.inr (Sum.inl 2) := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_eight : quotientIndexEquiv.symm 8 = Sum.inr (Sum.inl 3) := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_nine : quotientIndexEquiv.symm 9 = Sum.inr (Sum.inl 4) := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_ten : quotientIndexEquiv.symm 10 = Sum.inr (Sum.inr 0) := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_eleven : quotientIndexEquiv.symm 11 = Sum.inr (Sum.inr 1) := by decide

set_option maxHeartbeats 800000 in
private lemma quotientIndexEquiv_symm_twelve : quotientIndexEquiv.symm 12 = Sum.inr (Sum.inr 2) := by decide

set_option maxHeartbeats 800000 in
private lemma quotientCoordinates_positiveRepresentative (p : OpenBoundaryMPSQuotient.Quotient)
    (hp : 0 < p.2.1) :
    positiveRepresentative (quotientCoordinates13 p) =
      (p.1, Real.sqrt p.2.1, (Real.sqrt p.2.1 : ℂ) * p.2.2) := by
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp [positiveRepresentative, coreCoordinates, quotientCoordinates13,
        OpenBoundaryMPSQuotient.quotientRealCoordinates,
        sigma, eta, quotientRealCoordinates,
        quotientIndexEquiv_symm_zero, quotientIndexEquiv_symm_one,
        quotientIndexEquiv_symm_two, quotientIndexEquiv_symm_three,
        quotientIndexEquiv_symm_four, quotientIndexEquiv_symm_five,
        quotientIndexEquiv_symm_six, quotientIndexEquiv_symm_seven,
        quotientIndexEquiv_symm_eight, quotientIndexEquiv_symm_nine,
        quotientIndexEquiv_symm_ten, quotientIndexEquiv_symm_eleven,
        quotientIndexEquiv_symm_twelve]
  · apply Prod.ext
    · simp [positiveRepresentative, quotientCoordinates13,
        OpenBoundaryMPSQuotient.quotientRealCoordinates, sigma, eta,
        quotientRealCoordinates, quotientIndexEquiv_symm_ten,
        quotientIndexEquiv_symm_eleven, quotientIndexEquiv_symm_twelve]
    · apply Complex.ext <;>
        simp [positiveRepresentative, quotientCoordinates13,
          OpenBoundaryMPSQuotient.quotientRealCoordinates, sigma, eta,
          quotientRealCoordinates, quotientIndexEquiv_symm_ten,
          quotientIndexEquiv_symm_eleven, quotientIndexEquiv_symm_twelve]

private def quotientParameterOfCoordinates (x : Coordinates) :
    OpenBoundaryMPSQuotient.Quotient := (coreCoordinates x, sigma x, eta x)

private lemma quotientParameter_coordinates (x : Coordinates) :
    quotientCoordinates13 (quotientParameterOfCoordinates x) = x := by
  funext i
  fin_cases i <;>
    simp [quotientParameterOfCoordinates, quotientCoordinates13,
      quotientIndexEquiv_symm_zero, quotientIndexEquiv_symm_one,
      quotientIndexEquiv_symm_two, quotientIndexEquiv_symm_three,
      quotientIndexEquiv_symm_four, quotientIndexEquiv_symm_five,
      quotientIndexEquiv_symm_six, quotientIndexEquiv_symm_seven,
      quotientIndexEquiv_symm_eight, quotientIndexEquiv_symm_nine,
      quotientIndexEquiv_symm_ten, quotientIndexEquiv_symm_eleven,
      quotientIndexEquiv_symm_twelve, OpenBoundaryMPSQuotient.quotientRealCoordinates,
      quotientRealCoordinates, coreCoordinates, sigma, eta]

private lemma quotientParameter_positiveBoundary (x : Coordinates) :
    positiveRepresentative x =
      ((quotientParameterOfCoordinates x).1,
        Real.sqrt (quotientParameterOfCoordinates x).2.1,
        (Real.sqrt (quotientParameterOfCoordinates x).2.1 : ℂ) *
          (quotientParameterOfCoordinates x).2.2) := by
  rfl

private lemma positiveObservation_local (m : ℕ) (x : Coordinates) (hx : 0 ≤ sigma x) :
    quotientRawPrefix m x =
      OpenBoundaryMPSQuotient.quotientObservation 3 m
        (quotientParameterOfCoordinates x) := by
  let p := quotientParameterOfCoordinates x
  have hs0 : OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
      (positiveRepresentative x) =
      OpenBoundaryMPSMarginalBirationality.mpsState (3 + m)
        (OpenBoundaryMPSTwoSiteMinimality.core p 0)
        (OpenBoundaryMPSTwoSiteMinimality.core p 1)
        (OpenBoundaryMPSTwoSiteMinimality.left p)
        (OpenBoundaryMPSQuotient.positiveBoundary p) := by
    rw [quotientParameter_positiveBoundary x]
    exact positiveBoundary_state_eq m p
  have hs1 : OpenBoundaryMPSMarginalBirationality.mpsState (3 + m)
      (OpenBoundaryMPSTwoSiteMinimality.core p 0)
      (OpenBoundaryMPSTwoSiteMinimality.core p 1)
      (OpenBoundaryMPSTwoSiteMinimality.left p)
      (OpenBoundaryMPSQuotient.positiveBoundary p) =
      (Real.sqrt (sigma x) : ℂ) •
        OpenBoundaryMPSMarginalBirationality.mpsState (3 + m)
          (OpenBoundaryMPSTwoSiteMinimality.core p 0)
          (OpenBoundaryMPSTwoSiteMinimality.core p 1)
          (OpenBoundaryMPSTwoSiteMinimality.left p)
          (OpenBoundaryMPSTwoSiteMinimality.right
            (p.1, 1, p.2.2)) := by
    have hr : OpenBoundaryMPSQuotient.positiveBoundary p =
        (Real.sqrt p.2.1 : ℂ) •
          OpenBoundaryMPSTwoSiteMinimality.right (p.1, 1, p.2.2) := by
      ext i
      fin_cases i <;>
        simp [OpenBoundaryMPSQuotient.positiveBoundary,
          OpenBoundaryMPSTwoSiteMinimality.right]
    rw [hr]
    funext w
    simp only [OpenBoundaryMPSMarginalBirationality.mpsState,
      OpenBoundaryMPSDensityRecovery.state_formula, Matrix.mulVec_smul,
      dotProduct_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  have hs := hs0.trans hs1
  rw [show quotientRawPrefix m x =
      OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
        (OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
          (positiveRepresentative x)) by rfl]
  rw [hs, rawPrefix_scale_local]
  have hz : Complex.normSq (Real.sqrt (sigma x) : ℂ) = (sigma x : ℂ) := by
    rw [Complex.normSq_ofReal]
    congr 1
    rw [← sq, Real.sq_sqrt hx]
  rw [hz]
  rfl

private lemma quotientCoordinates_retraction_local (m : ℕ) (x : Coordinates)
    (hx : 0 < sigma x)
    (hρ : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0) :
    quotientCoordinates13
        (OpenBoundaryMPSQuotient.quotientCoordinates m (quotientRawPrefix m x)) = x := by
  let p := quotientParameterOfCoordinates x
  have hparts := (OpenBoundaryMPSQuotient.quotientLocus_eval m
    (quotientRawPrefix m x)).mp hρ
  have hobs := positiveObservation_local m x hx.le
  rw [hobs] at hparts
  have hp := OpenBoundaryMPSQuotient.quotient_retraction m p hx hparts.1
  rw [← hobs] at hp
  rw [hp, quotientParameter_coordinates]

private def quotientNumeratorFamily (m : ℕ) (j : Fin 13) :
    MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ :=
  OpenBoundaryMPSQuotient.quotientRealNumerator m (quotientIndexEquiv.symm j)

private def quotientDenominatorFamily (m : ℕ) (j : Fin 13) :
    MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ :=
  OpenBoundaryMPSQuotient.quotientRealDenominator m (quotientIndexEquiv.symm j)

private lemma quotient_ratio_vector_local (m : ℕ) (x : Coordinates)
    (hσ : 0 < sigma x)
    (hρ : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0) :
    (fun j =>
      eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => quotientRawPrefix m x ij.1 ij.2)) (quotientNumeratorFamily m j) /
      eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => quotientRawPrefix m x ij.1 ij.2)) (quotientDenominatorFamily m j)) = x := by
  funext j
  have hr := quotientCoordinate_ratio m (quotientRawPrefix m x) (by simpa using hρ) j
  rw [quotientCoordinates_retraction_local m x hσ hρ] at hr
  exact hr

private lemma state_continuous (m : ℕ) :
    Continuous (fun x : Coordinates =>
      OpenBoundaryMPSTwoSiteMinimality.state (3 + m) (positiveRepresentative x)) := by
  have hpar : Continuous (fun x : Coordinates =>
      fun w => eval (parameterCoordinates x)
        (OpenBoundaryMPSMarginalBirationality.parameterPolys (3 + m) w)) := by
    apply continuous_pi
    intro w
    exact (MvPolynomial.continuous_eval _).comp parameterCoordinates_continuous
  exact hpar.congr (fun x => parameterCoordinates_eval m x)

private lemma openBoundaryMPS_smul {n : ℕ} {ψ : Word n → ℂ}
    (hψ : ψ ∈ OpenBoundaryMPSMarginalBirationality.openBoundaryMPS n) (z : ℂ) :
    z • ψ ∈ OpenBoundaryMPSMarginalBirationality.openBoundaryMPS n := by
  rcases hψ with ⟨a₀, a₁, l, r, hr⟩
  refine ⟨a₀, a₁, l, z • r, ?_⟩
  rw [hr]
  funext w
  simp only [OpenBoundaryMPSMarginalBirationality.mpsState,
    Matrix.mulVec_smul, dotProduct_smul, Pi.smul_apply, smul_eq_mul]

private def q2WordCast (m : ℕ) (w : Word (2 + (1 + m))) : Word (3 + m) :=
  fun i => w (Fin.cast (by omega) i)

private def actualQ2RawPrefix (m : ℕ)
    (ψ : Word (3 + m) → ℂ) : Matrix (Word 2) (Word 2) ℂ :=
  OpenBoundaryMPSDensityRecovery.rawPrefix 2 (1 + m)
    (fun w => ψ (q2WordCast m w))

def intrinsicActualQ2Fiber (m : ℕ) : Prop :=
  ∃ G : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ, G ≠ 0 ∧
    let L := actualPrincipalLocus m G
    L.Nonempty ∧ IsOpen L ∧ Dense L ∧
      ∀ ψ ∈ L, ∀ V : Set (OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m)),
        V ∈ 𝓝 ψ →
        ∃ φ ∈ V,
          actualQ2RawPrefix m (φ : Word (3 + m) → ℂ) =
            actualQ2RawPrefix m (ψ : Word (3 + m) → ℂ) ∧
          ¬ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
            (φ : Word (3 + m) → ℂ) = ζ • (ψ : Word (3 + m) → ℂ)

set_option maxHeartbeats 1000000 in
theorem intrinsic_actual_q2_fiber (m : ℕ) : intrinsicActualQ2Fiber m := by
  obtain ⟨J, hJ, hJw, hJfiber⟩ :=
    D5.S3.Geometry.PolynomialLocalFiber.exists_rank_fiber_polynomial
      (recordPolynomial (1 + m))
  let P : RealPoly := J * leadingPolynomial m
  obtain ⟨H, B, hclear⟩ :=
    clear_polynomial P (quotientNumeratorFamily m) (quotientDenominatorFamily m)
  obtain ⟨x₀, hx₀⟩ := hJw
  have hJdense := polynomial_nonzero_dense J x₀ (by rw [hx₀]; norm_num)
  obtain ⟨x, hxDom, hxJ⟩ := hJdense.inter_open_nonempty _
    (quotientValidityDomain_open m) (quotientValidityDomain_nonempty m)
  change eval x J ≠ 0 at hxJ
  let Qx := quotientRawPrefix m x
  let ax : ObsIndex ⊕ ObsIndex → ℝ :=
    OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij : ObsIndex => Qx ij.1 ij.2)
  have hρx : eval ax (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0 := by
    exact hxDom.2.1
  have hdenx : ∀ j, eval ax (quotientDenominatorFamily m j) ≠ 0 := by
    intro j
    exact quotient_denominators_nonzero m Qx hρx j
  have hratx : (fun j => eval ax (quotientNumeratorFamily m j) /
      eval ax (quotientDenominatorFamily m j)) = x := by
    exact quotient_ratio_vector_local m x hxDom.1 hρx
  have hcx := hclear ax hdenx
  rw [hratx] at hcx
  have hPx : eval x P ≠ 0 := by
    simpa [P] using mul_ne_zero hxJ hxDom.2.2
  have hHx : eval ax H ≠ 0 := by
    intro h
    have : eval x P = 0 := by simpa [h] using hcx.2
    exact hPx this
  let G : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ :=
    OpenBoundaryMPSQuotient.quotientLocusPolynomial m * H
  have hGx : eval ax G ≠ 0 := by
    simpa [G] using mul_ne_zero hρx hHx
  have hG : G ≠ 0 := by
    intro h
    rw [h] at hGx
    simpa using hGx
  let ψ₀ : Word (3 + m) → ℂ :=
    OpenBoundaryMPSTwoSiteMinimality.state (3 + m) (positiveRepresentative x)
  have hψ₀ : ψ₀ ∈ OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m) := by
    refine ⟨OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative x) 0,
      OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative x) 1,
      OpenBoundaryMPSTwoSiteMinimality.left (positiveRepresentative x),
      OpenBoundaryMPSTwoSiteMinimality.right (positiveRepresentative x), ?_⟩
    rfl
  let ψ : OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m) := ⟨ψ₀, hψ₀⟩
  have hψG : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
        (ψ : Word (3 + m) → ℂ) ij.1 ij.2)) G ≠ 0 := by
    simpa [ψ, ψ₀, Qx, ax, quotientRawPrefix, actualPrincipalLocus] using hGx
  obtain ⟨Lne, Lopen, Ldense⟩ :=
    actual_principal_genericity m G ⟨ψ, hψG⟩
  refine ⟨G, hG, Lne, Lopen, Ldense, ?_⟩
  intro ψ' hψ' V hV
  obtain ⟨O, hOV, hO, hψ'O⟩ := mem_nhds_iff.mp hV
  let Qψ := OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
    (ψ' : Word (3 + m) → ℂ)
  have hGψ := hψ'
  change eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => Qψ ij.1 ij.2)) G ≠ 0 at hGψ
  have hρψ : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => Qψ ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0 := by
    have hmul : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => Qψ ij.1 ij.2))
        (OpenBoundaryMPSQuotient.quotientLocusPolynomial m * H) ≠ 0 := by
      simpa [G] using hGψ
    simp only [map_mul] at hmul
    exact (mul_ne_zero_iff.mp hmul).1
  have hpartsψ := (OpenBoundaryMPSQuotient.quotientLocus_eval m Qψ).mp hρψ
  obtain ⟨_, _, _, _, _, h00ψ⟩ :=
    OpenBoundaryMPSQuotient.rational_quotient_inverse m Qψ hρψ
  have hrep := OpenBoundaryMPSQuotient.actual_quotient_representative m
      (ψ' : Word (3 + m) → ℂ) ψ'.property hpartsψ.1 h00ψ
  dsimp only at hrep
  let p := OpenBoundaryMPSQuotient.quotientCoordinates m Qψ
  have hrep' : 0 < p.2.1 ∧ ∃ z : ℂ, ‖z‖ = 1 ∧
      (ψ' : Word (3 + m) → ℂ) = z •
        OpenBoundaryMPSMarginalBirationality.mpsState (3 + m)
          (OpenBoundaryMPSTwoSiteMinimality.core p 0)
          (OpenBoundaryMPSTwoSiteMinimality.core p 1)
          (OpenBoundaryMPSTwoSiteMinimality.left p)
          (OpenBoundaryMPSQuotient.positiveBoundary p) := by
    simpa [p] using hrep
  obtain ⟨hpσ, z, hz, hphase⟩ := hrep'
  let x' := quotientCoordinates13 p
  have hx'σ : 0 < sigma x' := by
    simpa [x', sigma, quotientCoordinates13, quotientRealCoordinates,
      quotientIndexEquiv_symm_ten] using hpσ
  have hx'Q : Qψ = quotientRawPrefix m x' := by
    have hrep := quotientCoordinates_positiveRepresentative p hpσ
    have hstate : OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
        (positiveRepresentative x') =
        OpenBoundaryMPSMarginalBirationality.mpsState (3 + m)
          (OpenBoundaryMPSTwoSiteMinimality.core p 0)
          (OpenBoundaryMPSTwoSiteMinimality.core p 1)
          (OpenBoundaryMPSTwoSiteMinimality.left p)
          (OpenBoundaryMPSQuotient.positiveBoundary p) := by
      rw [hrep]
      exact positiveBoundary_state_eq m p
    have hzsq : Complex.normSq z = 1 := by
      rw [← Complex.sq_norm, hz]
      norm_num
    change OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
        (ψ' : Word (3 + m) → ℂ) =
      OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
        (OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
          (positiveRepresentative x'))
    rw [hphase, rawPrefix_scale_local, hzsq, hstate]
    simp
  have hρx' : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x' ij.1 ij.2))
      (OpenBoundaryMPSQuotient.quotientLocusPolynomial m) ≠ 0 := by
    rw [← hx'Q]
    exact hρψ
  have hdenx' : ∀ j, eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x' ij.1 ij.2))
      (quotientDenominatorFamily m j) ≠ 0 := by
    intro j
    exact quotient_denominators_nonzero m (quotientRawPrefix m x') hρx' j
  have hratx' := quotient_ratio_vector_local m x' hx'σ hρx'
  have hcx' := hclear
    (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x' ij.1 ij.2)) hdenx'
  rw [hratx'] at hcx'
  have hHrawx' : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
      (fun ij => quotientRawPrefix m x' ij.1 ij.2)) H ≠ 0 := by
    have hmul : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => Qψ ij.1 ij.2))
        (OpenBoundaryMPSQuotient.quotientLocusPolynomial m * H) ≠ 0 := by
      simpa [G] using hGψ
    simp only [map_mul] at hmul
    have hHψ : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => Qψ ij.1 ij.2)) H ≠ 0 :=
      (mul_ne_zero_iff.mp hmul).2
    rw [← hx'Q]
    exact hHψ
  have hPx' : eval x' P ≠ 0 := by
    intro h
    have hdiv : eval (OpenBoundaryMPSDensityGenericity.realCoordinates
        (fun ij => quotientRawPrefix m x' ij.1 ij.2)) H /
        eval (OpenBoundaryMPSDensityGenericity.realCoordinates
          (fun ij => quotientRawPrefix m x' ij.1 ij.2)) B = 0 := by
      simpa [h] using hcx'.2.symm
    rcases (div_eq_zero_iff.mp hdiv) with hH | hB
    · exact False.elim (hHrawx' hH)
    · exact False.elim (hcx'.1 hB)
  have hx'J : eval x' J ≠ 0 := by
    exact (mul_ne_zero_iff.mp (by simpa [P] using hPx')).1
  have hx'lead : eval x' (leadingPolynomial m) ≠ 0 := by
    exact (mul_ne_zero_iff.mp (by simpa [P] using hPx')).2
  let S : Coordinates → (Word (3 + m) → ℂ) := fun y =>
    z • OpenBoundaryMPSTwoSiteMinimality.state (3 + m) (positiveRepresentative y)
  have hScont : Continuous S := by
    dsimp [S]
    exact (continuous_const : Continuous (fun _ : Coordinates => z)).smul
      (state_continuous m)
  let Ssub : Coordinates →
      OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m) := fun y =>
    ⟨S y, openBoundaryMPS_smul (by
      exact ⟨OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative y) 0,
        OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative y) 1,
        OpenBoundaryMPSTwoSiteMinimality.left (positiveRepresentative y),
        OpenBoundaryMPSTwoSiteMinimality.right (positiveRepresentative y), rfl⟩) z⟩
  have hSsubcont : Continuous Ssub := hScont.subtype_mk _
  have hstate' : OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
      (positiveRepresentative x') =
      OpenBoundaryMPSMarginalBirationality.mpsState (3 + m)
        (OpenBoundaryMPSTwoSiteMinimality.core p 0)
        (OpenBoundaryMPSTwoSiteMinimality.core p 1)
        (OpenBoundaryMPSTwoSiteMinimality.left p)
        (OpenBoundaryMPSQuotient.positiveBoundary p) := by
    have hrep := quotientCoordinates_positiveRepresentative p hpσ
    rw [hrep]
    exact positiveBoundary_state_eq m p
  have hSsubx : Ssub x' = ψ' := by
    apply Subtype.ext
    change z • OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
        (positiveRepresentative x') = (ψ' : Word (3 + m) → ℂ)
    rw [hstate']
    exact hphase.symm
  let U : Set Coordinates := Ssub ⁻¹' O ∩ quotientValidityDomain m ∩
    {y | eval y J ≠ 0}
  have hUopen : IsOpen U := by
    simpa [U, inter_assoc] using
      (hSsubcont.isOpen_preimage O hO).inter
        ((quotientValidityDomain_open m).inter
          (isOpen_ne.preimage (MvPolynomial.continuous_eval J)))
  have hx'U : x' ∈ U := by
    refine ⟨?_, hx'J⟩
    refine ⟨?_, ?_⟩
    · change Ssub x' ∈ O
      rw [hSsubx]
      exact hψ'O
    · exact ⟨hx'σ, hρx', hx'lead⟩
  obtain ⟨K, q, f, ε, hε, hdim, hf0, hfc, hf, hpos⟩ :=
    (hJfiber x' hx'J).2 U hUopen hx'U
  obtain ⟨hKpos, y, hyU, hyx, hyrec⟩ := hpos (by decide)
  let φ₀ : Word (3 + m) → ℂ := S y
  have hφ₀ : φ₀ ∈ OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m) := by
    exact openBoundaryMPS_smul (by
      exact ⟨OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative y) 0,
        OpenBoundaryMPSTwoSiteMinimality.core (positiveRepresentative y) 1,
        OpenBoundaryMPSTwoSiteMinimality.left (positiveRepresentative y),
        OpenBoundaryMPSTwoSiteMinimality.right (positiveRepresentative y), rfl⟩) z
  let φ : OpenBoundaryMPSMarginalBirationality.openBoundaryMPS (3 + m) := ⟨φ₀, hφ₀⟩
  have hφV : φ ∈ V := hOV (by
    simpa [φ, φ₀, S, Ssub] using hyU.1.1)
  refine ⟨φ, hφV, ?_, ?_⟩
  · have hdens := record_equality_density (1 + m) hx'σ hyU.1.2.1
      (by
        intro h
        apply hx'lead
        rw [leadingPolynomial_eval m x' hx'σ.le]
        simp [h])
      hyrec
    have hzsq : Complex.normSq z = 1 := by
      rw [← Complex.sq_norm, hz]
      norm_num
    have hq2_scale (u : Coordinates) :
        actualQ2RawPrefix m (z • OpenBoundaryMPSTwoSiteMinimality.state
          (3 + m) (positiveRepresentative u)) =
          Complex.normSq z • actualQ2RawPrefix m
            (OpenBoundaryMPSTwoSiteMinimality.state
              (3 + m) (positiveRepresentative u)) := by
      unfold actualQ2RawPrefix
      rw [show (fun w =>
          (z • OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
            (positiveRepresentative u)) (q2WordCast m w)) =
          z • (fun w => OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
            (positiveRepresentative u) (q2WordCast m w)) by rfl]
      exact rawPrefix_scale_local 2 (1 + m) z
        (fun w => OpenBoundaryMPSTwoSiteMinimality.state
          (3 + m) (positiveRepresentative u) (q2WordCast m w))
    have hcast (u : OpenBoundaryMPSTwoSiteMinimality.Parameter) :
        (fun w : Word (2 + (1 + m)) =>
          OpenBoundaryMPSTwoSiteMinimality.state (3 + m) u (q2WordCast m w)) =
        OpenBoundaryMPSTwoSiteMinimality.state (2 + (1 + m)) u := by
      funext w
      simp [q2WordCast, OpenBoundaryMPSTwoSiteMinimality.state,
        OpenBoundaryMPSMarginalBirationality.mpsState, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
    have hψstate : (ψ' : Word (3 + m) → ℂ) = z •
        OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
          (positiveRepresentative x') := by
      simpa [hstate'] using hphase
    rw [show (φ : Word (3 + m) → ℂ) = z •
        OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
          (positiveRepresentative y) by rfl,
      hψstate]
    rw [hq2_scale, hq2_scale, hzsq]
    simp only [one_smul]
    change OpenBoundaryMPSDensityRecovery.rawPrefix 2 (1 + m)
        (fun w => OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
          (positiveRepresentative y) (q2WordCast m w)) =
      OpenBoundaryMPSDensityRecovery.rawPrefix 2 (1 + m)
        (fun w => OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
          (positiveRepresentative x') (q2WordCast m w))
    rw [hcast, hcast]
    exact hdens
  · intro hphaseφ
    obtain ⟨lambda, hlam, hphaseEq⟩ := hphaseφ
    have hNormSq : Complex.normSq lambda = 1 := by
      rw [← Complex.sq_norm, hlam]
      norm_num
    have hzsq : Complex.normSq z = 1 := by
      rw [← Complex.sq_norm, hz]
      norm_num
    have hQeq : quotientRawPrefix m y = quotientRawPrefix m x' := by
      have hraw := congrArg (fun v : Word (3 + m) → ℂ =>
          OpenBoundaryMPSDensityRecovery.rawPrefix 3 m v) hphaseEq
      have hφraw : OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
          (φ : Word (3 + m) → ℂ) = quotientRawPrefix m y := by
        change OpenBoundaryMPSDensityRecovery.rawPrefix 3 m (z •
          OpenBoundaryMPSTwoSiteMinimality.state (3 + m)
            (positiveRepresentative y)) = _
        rw [rawPrefix_scale_local]
        have hzsq : Complex.normSq z = 1 := by
          rw [← Complex.sq_norm, hz]
          norm_num
        rw [hzsq]
        simpa [quotientRawPrefix]
      rw [hφraw] at hraw
      rw [rawPrefix_scale_local 3 m lambda, hNormSq] at hraw
      have hψQ : OpenBoundaryMPSDensityRecovery.rawPrefix 3 m
          (ψ' : Word (3 + m) → ℂ) = quotientRawPrefix m x' := by
        simpa [Qψ] using hx'Q
      rw [hψQ] at hraw
      norm_num at hraw
      exact hraw
    have hx'y := quotientCoordinates_retraction_local m y hyU.1.2.1
      (by exact hyU.1.2.2.1)
    have hxx := quotientCoordinates_retraction_local m x' hx'σ hρx'
    apply hyx
    rw [← hxx, ← hx'y, hQeq]

end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber
