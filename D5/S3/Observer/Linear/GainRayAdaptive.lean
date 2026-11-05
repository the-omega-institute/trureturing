/- GID: D5/S3/Observer/Linear/GainRayAdaptive
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayAdaptive
   mirror-E: none(waiver:unrestricted-native-protocols)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.Equiv]
   utility: none
   digest: A deterministic native protocol attains the whole-world gain-ray upper read bound. -/

import D5.S3.Observer.Linear.GainRayNuisance
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Topology.Algebra.MvPolynomial
import D5.S3.Observer.Linear.GainRayEndpoint
import Mathlib.MeasureTheory.Measure.OpenPos
import D5.S3.Observer.Linear.GainRayJets
import D5.S3.Observer.Linear.GainRayIdenticalRows

set_option autoImplicit false
noncomputable section
open scoped Matrix
open MeasureTheory
namespace D5.S3.Observer.Linear.GainRay

private theorem clocks_injective (n : ℕ) : Function.Injective (clocks n) := by
  intro i j h
  apply Fin.ext
  dsimp [clocks] at h
  exact_mod_cast h

/-- Interpolation at all declared-degree clocks, with ordinary coefficients. -/
def clockEquiv (d : ℕ) : Coeff d ≃ₗ[ℝ] Coeff d :=
  LinearEquiv.ofBijective (evaluate d (d+1) (clocks (d+1)))
    ⟨evaluation_injective d (d+1) _ (clocks_injective _) le_rfl,
      evaluation_surjective d (d+1) _ (clocks_injective _) le_rfl⟩

def interpolationMatrix (d : ℕ) : Matrix (Fin (d+1)) (Fin (d+1)) ℝ :=
  LinearMap.toMatrix' (clockEquiv d).symm.toLinearMap

private theorem interpolation_apply (d : ℕ) (v : Coeff d) :
    (interpolationMatrix d).mulVec v = (clockEquiv d).symm v :=
  LinearMap.toMatrix'_mulVec _ _

/-- The first three fiber coordinates are x,r,delta; the others are gain values
at clocks n,...,d. There are exactly d+1-n remaining gain coordinates. -/
abbrev Fiber (d n : ℕ) := Fin (d+4-n) → ℝ
abbrev FiberPolynomial (d n : ℕ) := MvPolynomial (Fin (d+4-n) ⊕ Fin n) ℝ

def fiberX (d n : ℕ) (hn : n ≤ d+1) : FiberPolynomial d n :=
  MvPolynomial.X (.inl ⟨0, by omega⟩)
def fiberR (d n : ℕ) (hn : n ≤ d+1) : FiberPolynomial d n :=
  MvPolynomial.X (.inl ⟨1, by omega⟩)
def fiberDrift (d n : ℕ) (hn : n ≤ d+1) : FiberPolynomial d n :=
  MvPolynomial.X (.inl ⟨2, by omega⟩)
def fiberDen (d n : ℕ) (hn : n ≤ d+1) : FiberPolynomial d n :=
  fiberX d n hn + fiberR d n hn

def fiberValues (d n : ℕ) (hn : n ≤ d+1) (i : Fin (d+1)) :
    FiberPolynomial d n :=
  if h : i.val < n then
    (MvPolynomial.X (.inr ⟨i.val,h⟩) - fiberDrift d n hn) *
      (if i.val % 2 = 0 then fiberDen d n hn
       else 1 + fiberX d n hn * fiberR d n hn)
  else MvPolynomial.X (.inl ⟨i.val-n+3, by omega⟩) * fiberDen d n hn

def fiberNumerator (d n : ℕ) (hn : n ≤ d+1) (k : Fin (d+1)) :
    FiberPolynomial d n :=
  ∑ i : Fin (d+1), MvPolynomial.C (interpolationMatrix d k i) * fiberValues d n hn i

/-- Polynomial substitution uses denominator-multiplied coefficients and drift. -/
def fiberSubstitution (d n : ℕ) (hn : n ≤ d+1) (i : Fin (d+4)) :
    FiberPolynomial d n :=
  if h : i.val < 2 then (if i.val = 0 then fiberX d n hn else fiberR d n hn)
  else if h' : i.val < d+3 then fiberNumerator d n hn ⟨i.val-2, by omega⟩
  else fiberDrift d n hn * fiberDen d n hn

def fiberPullback (d n : ℕ) (hn : n ≤ d+1) (p : ChartPolynomial d) :
    FiberPolynomial d n := MvPolynomial.bind₁ (fiberSubstitution d n hn) p

def fiberSpecialize {d n : ℕ} (Q : FiberPolynomial d n) (y : Fin n → ℝ) :
    MvPolynomial (Fin (d+4-n)) ℝ :=
  MvPolynomial.map (MvPolynomial.eval y)
    (MvPolynomial.sumRingEquiv ℝ (Fin (d+4-n)) (Fin n) Q)

theorem eval_fiber_specialize {d n : ℕ} (Q : FiberPolynomial d n)
    (y : Fin n → ℝ) (f : Fiber d n) :
    MvPolynomial.eval f (fiberSpecialize Q y) = MvPolynomial.eval (Sum.elim f y) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [fiberSpecialize]
  | add p q hp hq => simpa [fiberSpecialize] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
      cases i <;> simp_all [fiberSpecialize, MvPolynomial.sumRingEquiv_X_inl,
        MvPolynomial.sumRingEquiv_X_inr]

/-- A nonzero joint polynomial has a nonzero history coefficient. Outside its
zero set the polynomial on that prescribed fiber is nonzero. -/
theorem fiber_nonzero_coefficient {d n : ℕ} (Q : FiberPolynomial d n) (hQ : Q ≠ 0) :
    ∃ q : MvPolynomial (Fin n) ℝ, q ≠ 0 ∧
      ∀ y, MvPolynomial.eval y q ≠ 0 → fiberSpecialize Q y ≠ 0 := by
  classical
  let P := MvPolynomial.sumRingEquiv ℝ (Fin (d+4-n)) (Fin n) Q
  have hP : P ≠ 0 := by
    intro h
    exact hQ ((MvPolynomial.sumRingEquiv ℝ _ _).injective (by simpa [P] using h))
  obtain ⟨a, ha⟩ : ∃ a, P.coeff a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP (by
      apply MvPolynomial.ext
      intro a
      simpa using h a)
  refine ⟨P.coeff a, ha, ?_⟩
  intro y hy hz
  apply hy
  have h := congrArg (fun p : MvPolynomial (Fin (d+4-n)) ℝ => p.coeff a) hz
  simpa [fiberSpecialize, P, MvPolynomial.coeff_map] using h


private theorem fiber_numerator_evaluation (d n : ℕ) (hn : n ≤ d+1)
    (y : Fin n → ℝ) (f : Fiber d n) (i : Fin (d+1)) :
    (gain d (fun k => MvPolynomial.eval (Sum.elim f y) (fiberNumerator d n hn k))).eval
        (clocks (d+1) i) =
      MvPolynomial.eval (Sum.elim f y) (fiberValues d n hn i) := by
  have h : (fun k => MvPolynomial.eval (Sum.elim f y) (fiberNumerator d n hn k)) =
      (clockEquiv d).symm (fun i => MvPolynomial.eval (Sum.elim f y) (fiberValues d n hn i)) := by
    rw [← interpolation_apply]
    ext k
    simp [fiberNumerator, Matrix.mulVec, dotProduct]
  rw [h, ← evaluation_polynomial]
  exact congrFun ((clockEquiv d).apply_symm_apply _) i

/-- The original gain, after dividing the numerator by its positive denominator. -/
def fiberBeta (d n : ℕ) (hn : n ≤ d+1) (y : Fin n → ℝ) (f : Fiber d n) : Coeff d :=
  (MvPolynomial.eval (Sum.elim f y) (fiberDen d n hn))⁻¹ •
    (fun k => MvPolynomial.eval (Sum.elim f y) (fiberNumerator d n hn k))

private theorem fiber_beta_evaluation (d n : ℕ) (hn : n ≤ d+1)
    (y : Fin n → ℝ) (f : Fiber d n) (i : Fin (d+1)) :
    (gain d (fiberBeta d n hn y f)).eval (clocks (d+1) i) =
      (MvPolynomial.eval (Sum.elim f y) (fiberDen d n hn))⁻¹ *
        MvPolynomial.eval (Sum.elim f y) (fiberValues d n hn i) := by
  change (gain d (_ • _)).eval _ = _
  rw [show gain d (_ • _) = _ • gain d
      (fun k => MvPolynomial.eval (Sum.elim f y) (fiberNumerator d n hn k)) from
    (Polynomial.ofFn (d+1)).map_smul _ _, Polynomial.eval_smul,
    fiber_numerator_evaluation]
  rfl

/-- Every prescribed history has a legal nonempty fiber: x=r=1 and a drift
unequal to its initial value produce a nonzero whole gain, also when n=d+1. -/
theorem fiber_beta_nonzero (d n : ℕ) (hn0 : 1 ≤ n) (hn : n ≤ d+1)
    (y : Fin n → ℝ) (f : Fiber d n)
    (hx : 0 < f ⟨0,by omega⟩) (hr : 0 < f ⟨1,by omega⟩)
    (hδ : f ⟨2,by omega⟩ ≠ y ⟨0,by omega⟩) : fiberBeta d n hn y f ≠ 0 := by
  intro hz
  have he := fiber_beta_evaluation d n hn y f ⟨0,by omega⟩
  have hd : f ⟨0,by omega⟩ + f ⟨1,by omega⟩ ≠ 0 := ne_of_gt (add_pos hx hr)
  have hden : MvPolynomial.eval (Sum.elim f y) (fiberDen d n hn) ≠ 0 := by
    simpa [fiberDen, fiberX, fiberR] using hd
  have hval : MvPolynomial.eval (Sum.elim f y) (fiberValues d n hn ⟨0,by omega⟩) ≠ 0 := by
    simpa [fiberValues, fiberDen, fiberX, fiberR, fiberDrift, show 0 < n by omega] using
      mul_ne_zero (sub_ne_zero.mpr hδ.symm) hd
  exact (mul_ne_zero (inv_ne_zero hden) hval) (by simpa [hz, gain] using he.symm)

/-- Every point of the full compatible fiber is a legal original world. -/
def fiberWorld (d n : ℕ) (hn : n ≤ d+1) (y : Fin n → ℝ) (f : Fiber d n)
    (hx : 0 < f ⟨0,by omega⟩) (hr : 0 < f ⟨1,by omega⟩)
    (hβ : fiberBeta d n hn y f ≠ 0) : World d :=
  chartWorld d (f ⟨0,by omega⟩) (f ⟨1,by omega⟩) hx hr
    (fiberBeta d n hn y f) hβ (f ⟨2,by omega⟩)

/-- Its pure-J reads are exactly the prescribed values at the original clocks. -/
theorem fiber_world_prefix (d n : ℕ) (hn0 : 1 ≤ n) (hn : n ≤ d+1)
    (y : Fin n → ℝ) (f : Fiber d n)
    (hx : 0 < f ⟨0,by omega⟩) (hr : 0 < f ⟨1,by omega⟩)
    (hβ : fiberBeta d n hn y f ≠ 0) (i : Fin n) :
    readAt (fiberWorld d n hn y f hx hr hβ) (List.replicate (n-1) true) i.val = y i := by
  have hi : min i.val (n-1) = i.val := by omega
  have he := fiber_beta_evaluation d n hn y f ⟨i.val,by omega⟩
  have hd : f ⟨0,by omega⟩ + f ⟨1,by omega⟩ ≠ 0 := ne_of_gt (add_pos hx hr)
  have ht : 1 + f ⟨0,by omega⟩ * f ⟨1,by omega⟩ ≠ 0 := ne_of_gt (by positivity)
  simp only [readAt, fiberWorld, chartWorld, List.take_replicate, hi]
  rw [source_chart_pureJ _ _ hx hr]
  change (gain d (fiberBeta d n hn y f)).eval (clocks (d+1) ⟨i.val,by omega⟩) * _ + _ = _
  rw [he]
  simp only [fiberValues, dif_pos i.isLt, fiberDen, fiberX, fiberR, fiberDrift,
    map_add, map_sub, map_mul, map_one, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]
  split_ifs <;>
    simp only [map_add, map_mul, map_one, MvPolynomial.eval_X, Sum.elim_inl] <;>
    field_simp <;> ring


/-- Actual pure-J data with no restriction on the whole gain. -/
def fiberHistory (d n : ℕ) (x r : ℝ) (β : Coeff d) (δ : ℝ) : Fin n → ℝ :=
  fun i => (gain d β).eval (i.val : ℝ) *
    (if i.val % 2 = 0 then 1 else (x+r)/(1+x*r)) + δ

/-- The free tail records exactly the remaining fixed-clock gain values. -/
def fiberEncoding (d n : ℕ) (x r : ℝ) (β : Coeff d) (δ : ℝ) : Fiber d n :=
  fun j => if j.val = 0 then x else if j.val = 1 then r else if j.val = 2 then δ
    else (gain d β).eval ((j.val-3+n : ℕ) : ℝ)

private theorem numerator_encoded (d n : ℕ) (hn : n ≤ d+1) (x r : ℝ)
    (hx : 0 < x) (hr : 0 < r) (β : Coeff d) (δ : ℝ) :
    (fun k => MvPolynomial.eval
      (Sum.elim (fiberEncoding d n x r β δ) (fiberHistory d n x r β δ))
        (fiberNumerator d n hn k)) = (x+r) • β := by
  apply evaluation_injective d (d+1) _ (clocks_injective _) le_rfl
  ext i
  rw [evaluation_polynomial, fiber_numerator_evaluation, evaluation_polynomial]
  rw [show gain d ((x+r) • β) = (x+r) • gain d β from
    (Polynomial.ofFn (d+1)).map_smul _ _, Polynomial.eval_smul]
  simp only [smul_eq_mul]
  have hD : x+r ≠ 0 := ne_of_gt (add_pos hx hr)
  have hT : 1+x*r ≠ 0 := ne_of_gt (by positivity)
  by_cases hi : i.val < n
  · simp only [fiberValues, dif_pos hi, map_mul, map_sub, MvPolynomial.eval_X,
      Sum.elim_inr, fiberHistory]
    split_ifs <;>
      simp [fiberDrift, fiberDen, fiberX, fiberR, fiberEncoding, clocks] <;>
      field_simp <;> ring
  · have h0 : i.val-n+3 ≠ 0 := by omega
    have h1 : i.val-n+3 ≠ 1 := by omega
    have h2 : i.val-n+3 ≠ 2 := by omega
    have he : i.val-n+3-3+n = i.val := by omega
    have he' : ((i.val-n : ℕ) : ℝ) + (n : ℝ) = (i.val : ℝ) := by
      exact_mod_cast (show i.val-n+n = i.val by omega)
    simp [fiberValues, hi, fiberEncoding, h0, h1, h2, he, fiberDen, fiberX, fiberR,
      clocks, mul_comm, he']

/-- All compatible original worlds occur in these rational coordinates. -/
theorem fiber_coordinates_cover (d n : ℕ) (hn : n ≤ d+1) (x r : ℝ)
    (hx : 0 < x) (hr : 0 < r) (β : Coeff d) (δ : ℝ) :
    fiberBeta d n hn (fiberHistory d n x r β δ) (fiberEncoding d n x r β δ) = β := by
  have hD : x+r ≠ 0 := ne_of_gt (add_pos hx hr)
  unfold fiberBeta
  rw [numerator_encoded d n hn x r hx hr β δ]
  simp [fiberDen, fiberX, fiberR, fiberEncoding, hD]

theorem eval_fiber_pullback (d n : ℕ) (hn : n ≤ d+1) (p : ChartPolynomial d)
    (y : Fin n → ℝ) (f : Fiber d n) :
    MvPolynomial.eval (Sum.elim f y) (fiberPullback d n hn p) =
      MvPolynomial.eval (chartParameters d (f ⟨0,by omega⟩) (f ⟨1,by omega⟩)
        (fun k => MvPolynomial.eval (Sum.elim f y) (fiberNumerator d n hn k))
        (f ⟨2,by omega⟩ * (f ⟨0,by omega⟩ + f ⟨1,by omega⟩))) p := by
  rw [fiberPullback]
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) (Sum.elim f y) _ = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval
    (fun i => MvPolynomial.eval (Sum.elim f y) (fiberSubstitution d n hn i)) p = _
  apply congrArg (fun v : Fin (d+4) → ℝ => MvPolynomial.eval v p)
  funext i
  simp only [fiberSubstitution, chartParameters]
  split_ifs <;> simp [fiberX, fiberR, fiberDrift, fiberDen]

private theorem eval_pullback_encoded (d n : ℕ) (hn : n ≤ d+1)
    (p : ChartPolynomial d) (x r : ℝ) (hx : 0 < x) (hr : 0 < r)
    (β : Coeff d) (δ : ℝ) :
    MvPolynomial.eval
      (Sum.elim (fiberEncoding d n x r ((x+r)⁻¹ • β) (δ/(x+r)))
        (fiberHistory d n x r ((x+r)⁻¹ • β) (δ/(x+r))))
      (fiberPullback d n hn p) = MvPolynomial.eval (chartParameters d x r β δ) p := by
  rw [eval_fiber_pullback]
  have hD : x+r ≠ 0 := ne_of_gt (add_pos hx hr)
  have hc := congrArg (fun b : Coeff d => (x+r) • b)
    (fiber_coordinates_cover d n hn x r hx hr ((x+r)⁻¹ • β) (δ/(x+r)))
  unfold fiberBeta at hc
  have hden : MvPolynomial.eval
      (Sum.elim (fiberEncoding d n x r ((x+r)⁻¹ • β) (δ/(x+r)))
        (fiberHistory d n x r ((x+r)⁻¹ • β) (δ/(x+r)))) (fiberDen d n hn) = x+r := by
    simp [fiberDen, fiberX, fiberR, fiberEncoding]
  simp only [hden, smul_inv_smul₀ hD] at hc
  rw [hc]
  simp [fiberEncoding, hD]

/-- Nonzero ambient polynomials stay nonzero under the actual full-history
rational coordinates after clearing the strictly positive denominator. -/
theorem fiber_pullback_nonzero (d n : ℕ) (hn : n ≤ d+1)
    (p : ChartPolynomial d) (hp : p ≠ 0) : fiberPullback d n hn p ≠ 0 := by
  intro hz
  apply hp
  apply MvPolynomial.funext_set
    (fun i : Fin (d+4) => if i.val < 2 then Set.Ioi 0 else Set.univ)
    (fun i => by split_ifs; exact Set.Ioi_infinite 0; exact Set.infinite_univ)
  intro a ha
  let x := a 0
  let r := a 1
  let β : Coeff d := fun k => a ⟨k.val+2,by omega⟩
  let δ := a ⟨d+3,by omega⟩
  have hx : 0 < x := by simpa [x] using ha 0 (Set.mem_univ _)
  have hr : 0 < r := by simpa [r] using ha 1 (Set.mem_univ _)
  have he : chartParameters d x r β δ = a := by
    ext i
    dsimp [chartParameters, x, r, β, δ]
    split_ifs with hi h0 hc
    · congr 1; exact Fin.ext h0.symm
    · have h1 : i.val = 1 := by omega
      congr 1; exact Fin.ext h1.symm
    · exact congrArg a (Fin.ext (by dsimp; omega))
    · exact congrArg a (Fin.ext (by dsimp; omega))
  have h := eval_pullback_encoded d n hn p x r hx hr β δ
  simpa [hz, he] using h.symm

abbrev WordMatrix (d : ℕ) := (w : List Bool) × Readout d w

def Eligible (d : ℕ) (c : WordMatrix d) : Prop :=
  false ∈ c.1 ∧ c.1.length+1 ≤ 2*(d+1)

private theorem m_word_wedge (d : ℕ) (hd : 1 ≤ d) (w : List Bool)
    (hM : false ∈ w) (hN : w.length+1 ≤ 2*(d+1)) (C : Readout d w)
    (W : World d) (hW : Succeeds W w C) :
    ∃ j k : Fin (d+1), chartWedge d w C j k ≠ 0 := by
  by_cases hJ : true ∈ w
  · obtain ⟨j,k,hp,_,_⟩ := mixed_chart_success_certificate d hd w hM hJ hN C W hW
    exact ⟨j,k,hp⟩
  · have hw : w = List.replicate w.length false := List.eq_replicate_length.mpr (by
      intro a ha
      cases a
      · rfl
      · exact False.elim (hJ ha))
    obtain ⟨n,rfl⟩ : ∃ n, w = List.replicate n false := ⟨w.length,hw⟩
    apply (chart_wedge_nonzero_iff d _ C).mpr
    intro hu
    obtain ⟨hb,he⟩ := universal_scalar_identity d hd _ C hu
    have hn := successful_scalar_nonzero _ C hb he W hW
    have hid (S : Mat) (β : Coeff d) :
        C.mulVec (fun i => (gain d β).eval (i.val : ℝ) *
          Matrix.trace (acquisition ((List.replicate n false).take i.val) * S)) =
          scalarFunctional d _ C S • β := by
      calc
        _ = (response d _ C S).mulVec β := by
          change _ = (C * responseMatrix d _ S).mulVec β
          rw [← Matrix.mulVec_mulVec]
          congr 1
          ext i
          simp [responseMatrix, Matrix.mulVec, dotProduct, gain,
            Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum, Finset.mul_sum,
            mul_comm, mul_left_comm, mul_assoc]
        _ = _ := by rw [he S, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hz : scalarFunctional d _ C = 0 :=
      pureM_universal_obstruction d hd n (by simpa using hN) C
        (scalarFunctional d _ C) hb hid
    exact hn (by rw [hz]; rfl)

private theorem chart_success_scale (d : ℕ) (w : List Bool) (C : Readout d w)
    (x r : ℝ) (hx : 0 < x) (hr : 0 < r) (β : Coeff d) (hβ : β ≠ 0) (δ a : ℝ)
    (ha : a ≠ 0) (hs : Succeeds (chartWorld d x r hx hr β hβ δ) w C) :
    Succeeds (chartWorld d x r hx hr (a • β) (smul_ne_zero ha hβ) (a*δ)) w C := by
  obtain ⟨s,hs,hv⟩ := hs
  refine ⟨s,hs,?_⟩
  have he : readings (chartWorld d x r hx hr (a • β) (smul_ne_zero ha hβ) (a*δ)) w =
      a • readings (chartWorld d x r hx hr β hβ δ) w := by
    ext i
    simp only [readings, readAt, chartWorld]
    rw [show gain d (a • β) = a • gain d β from (Polynomial.ofFn (d+1)).map_smul _ _,
      Polynomial.eval_smul]
    simp only [Pi.smul_apply, smul_eq_mul, readings, readAt, chartWorld]
    ring
  rw [he, Matrix.mulVec_smul, hv, smul_comm]
  rfl

private theorem eligible_polynomial (d : ℕ) (hd : 1 ≤ d) (c : WordMatrix d)
    (hc : Eligible d c) :
    ∃ p : ChartPolynomial d, p ≠ 0 ∧
      ∀ (x r : ℝ) (hx : 0 < x) (hr : 0 < r) (β : Coeff d) (hβ : β ≠ 0)
        (δ a : ℝ), a ≠ 0 → Succeeds (chartWorld d x r hx hr β hβ δ) c.1 c.2 →
          MvPolynomial.eval (chartParameters d x r (a • β) (a*δ)) p = 0 := by
  classical
  by_cases h : ∃ W : World d, Succeeds W c.1 c.2
  · obtain ⟨W,hW⟩ := h
    obtain ⟨j,k,hp⟩ := m_word_wedge d hd c.1 hc.1 hc.2 c.2 W hW
    refine ⟨chartWedge d c.1 c.2 j k,hp,?_⟩
    intro x r hx hr β hβ δ a ha hs
    exact success_chart_wedge_zero d c.1 c.2 x r hx hr _ _ _
      (chart_success_scale d c.1 c.2 x r hx hr β hβ δ a ha hs) j k
  · exact ⟨1,one_ne_zero,fun x r hx hr β hβ δ a ha hs =>
      False.elim (h ⟨_,hs⟩)⟩

theorem countable_polynomial_avoidance {ι : Type*} [Countable ι]
    (N : ℕ) (p : ι → MvPolynomial (Fin N) ℝ) (hp : ∀ i, p i ≠ 0)
    (U : Set (Fin N → ℝ)) (ho : IsOpen U) (hne : U.Nonempty) :
    ∃ f ∈ U, ∀ i, MvPolynomial.eval f (p i) ≠ 0 := by
  have hall : ∀ᵐ f : Fin N → ℝ ∂volume, ∀ i, MvPolynomial.eval f (p i) ≠ 0 :=
    ae_all_iff.mpr (fun i =>
      D5.S3.Quantum.Algebra.GenericLieLength.ae_mvPolynomial_ne_zero N (p i) (hp i))
  exact Measure.exists_mem_of_measure_ne_zero_of_ae (ho.measure_ne_zero volume hne)
    (ae_restrict_of_ae hall)


/-- The full legal compatible fiber, including gains vanishing at any prescribed clock. -/
def fiberDomain (d n : ℕ) (hn : n ≤ d+1) (y : Fin n → ℝ) : Set (Fiber d n) :=
  {f | 0 < f ⟨0,by omega⟩ ∧ 0 < f ⟨1,by omega⟩ ∧
    (fun k => MvPolynomial.eval (Sum.elim f y) (fiberNumerator d n hn k)) ≠ 0}

private theorem fiber_domain_open_nonempty (d n : ℕ) (hn0 : 1 ≤ n) (hn : n ≤ d+1)
    (y : Fin n → ℝ) : IsOpen (fiberDomain d n hn y) ∧ (fiberDomain d n hn y).Nonempty := by
  have hc : Continuous (fun f : Fiber d n => fun k =>
      MvPolynomial.eval (Sum.elim f y) (fiberNumerator d n hn k)) := by
    apply continuous_pi
    intro k
    apply (MvPolynomial.continuous_eval (fiberNumerator d n hn k)).comp
    apply continuous_pi
    intro i
    cases i with
    | inl j => exact continuous_apply j
    | inr j => exact continuous_const
  constructor
  · exact (isOpen_lt continuous_const (continuous_apply _)).inter
      ((isOpen_lt continuous_const (continuous_apply _)).inter
        (isOpen_ne.preimage hc))
  · let f : Fiber d n := fun j => if j.val = 0 then 1 else if j.val = 1 then 1
        else if j.val = 2 then y ⟨0,by omega⟩ + 1 else 0
    have hx : 0 < f ⟨0,by omega⟩ := by norm_num [f]
    have hr : 0 < f ⟨1,by omega⟩ := by norm_num [f]
    have hδ : f ⟨2,by omega⟩ ≠ y ⟨0,by omega⟩ := by dsimp [f]; linarith
    refine ⟨f,hx,hr,?_⟩
    intro hz
    apply fiber_beta_nonzero d n hn0 hn y f hx hr hδ
    simp [fiberBeta,hz]

/-- A countable union of zero sets, with one polynomial per preassigned pair. -/
def exceptionalHistories {n : ℕ} {ι : Type*} (q : ι → MvPolynomial (Fin n) ℝ) :
    Set (Fin n → ℝ) := {y | ∃ c, MvPolynomial.eval y (q c) = 0}

/-- Full Lemma 9.3: every history outside the countable algebraic exceptional set
has one legal whole-world completion simultaneously avoiding every eligible pair. -/
theorem short_history_completion (d : ℕ) (hd : 1 ≤ d)
    (s : Set (WordMatrix d)) (hs : s.Countable) (he : ∀ c ∈ s, Eligible d c)
    (n : ℕ) (hn0 : 1 ≤ n) (hn : n ≤ d+1) :
    ∃ q : s → MvPolynomial (Fin n) ℝ, (∀ c, q c ≠ 0) ∧
      ∀ y, y ∉ exceptionalHistories q →
        ∃ W : World d,
          (∀ i : Fin n, readAt W (List.replicate (n-1) true) i.val = y i) ∧
          ∀ c : s, ¬ Succeeds W c.1.1 c.1.2 := by
  classical
  letI : Countable s := hs.to_subtype
  choose p hp hcert using (fun c : s => eligible_polynomial d hd c.1 (he c.1 c.2))
  let Q : s → FiberPolynomial d n := fun c => fiberPullback d n hn (p c)
  have hQ (c : s) : Q c ≠ 0 := fiber_pullback_nonzero d n hn (p c) (hp c)
  choose q hq hspecial using (fun c : s => fiber_nonzero_coefficient (Q c) (hQ c))
  refine ⟨q,hq,?_⟩
  intro y hy
  have hspec (c : s) : fiberSpecialize (Q c) y ≠ 0 := hspecial c y (by
    intro h
    exact hy ⟨c,h⟩)
  obtain ⟨ho,hne⟩ := fiber_domain_open_nonempty d n hn0 hn y
  obtain ⟨f,hf,havoid⟩ := countable_polynomial_avoidance (d+4-n)
    (fun c : s => fiberSpecialize (Q c) y) hspec (fiberDomain d n hn y) ho hne
  have hD : f ⟨0,by omega⟩ + f ⟨1,by omega⟩ ≠ 0 := ne_of_gt (add_pos hf.1 hf.2.1)
  have hdv : MvPolynomial.eval (Sum.elim f y) (fiberDen d n hn) =
      f ⟨0,by omega⟩ + f ⟨1,by omega⟩ := by simp [fiberDen,fiberX,fiberR]
  have hβ : fiberBeta d n hn y f ≠ 0 := by
    unfold fiberBeta
    rw [hdv]
    exact smul_ne_zero (inv_ne_zero hD) hf.2.2
  let W := fiberWorld d n hn y f hf.1 hf.2.1 hβ
  refine ⟨W, fiber_world_prefix d n hn0 hn y f hf.1 hf.2.1 hβ, ?_⟩
  intro c hc
  apply havoid c
  rw [eval_fiber_specialize, eval_fiber_pullback]
  have hnum : (f ⟨0,by omega⟩ + f ⟨1,by omega⟩) • fiberBeta d n hn y f =
      (fun k => MvPolynomial.eval (Sum.elim f y) (fiberNumerator d n hn k)) := by
    unfold fiberBeta
    rw [hdv, smul_inv_smul₀ hD]
  have h := hcert c (f ⟨0,by omega⟩) (f ⟨1,by omega⟩) hf.1 hf.2.1
    (fiberBeta d n hn y f) hβ (f ⟨2,by omega⟩)
    (f ⟨0,by omega⟩ + f ⟨1,by omega⟩) hD hc
  simpa only [hnum, mul_comm (f ⟨0,by omega⟩ + f ⟨1,by omega⟩) (f ⟨2,by omega⟩)] using h

/-- A singleton preassigned palette exists at every word. Only the intended
terminal word is reached at the stopping time. -/
def upperReadout (d : ℕ) (w : List Bool) : Readout d w :=
  if h : w = List.replicate (2*(d+1)) false then
    h.symm ▸ exactBetaReadout d else 0

def upperProtocol (d : ℕ) : Protocol d where
  palette w := {upperReadout d w}
  countable _ := Set.countable_singleton _
  decide w _ := if w.length < 2*(d+1) then Sum.inl false
    else Sum.inr ⟨upperReadout d w, Set.mem_singleton _⟩

private theorem upper_reaches (d : ℕ) (W : World d) (k : ℕ) (hk : k ≤ 2*(d+1)) :
    Reaches (upperProtocol d) W (List.replicate k false) := by
  induction k with
  | zero => simpa using (Reaches.initial (P := upperProtocol d) (W := W))
  | succ k ih =>
      rw [List.replicate_succ']
      apply Reaches.step (ih (by omega))
      simp [upperProtocol, show k < 2*(d+1) by omega]

/-- The exact native trajectory takes 2d+3 initial-inclusive consecutive reads,
terminates there, and returns the whole original coefficient vector with scalar 1. -/
theorem upper_protocol_correct (d : ℕ) (W : World d) :
    ∃ C : {C : Readout d (List.replicate (2*(d+1)) false) //
        C ∈ (upperProtocol d).palette (List.replicate (2*(d+1)) false)},
      Terminates (upperProtocol d) W (List.replicate (2*(d+1)) false) C ∧
      (List.replicate (2*(d+1)) false).length + 1 = 2*d+3 ∧
      C.1.mulVec (readings W (List.replicate (2*(d+1)) false)) = W.coeff := by
  refine ⟨⟨upperReadout d _, Set.mem_singleton _⟩, ⟨upper_reaches d W _ le_rfl, ?_⟩,
    by simp; omega, ?_⟩
  · simp [upperProtocol]
  · simpa [upperReadout] using pureM_exact_beta d W

/-- The attained upper bound is an actual protocol in the unrestricted history domain. -/
theorem adaptive_upper (d : ℕ) : UniformlySuccessful (upperProtocol d) (2*d+3) := by
  intro W
  obtain ⟨C,ht,hn,hβ⟩ := upper_protocol_correct d W
  exact ⟨_, C, ht, hn.le, 1, one_ne_zero, by simpa using hβ⟩


abbrev RowPolynomial (d : ℕ) := MvPolynomial (Fin (d+3)) ℝ

def rowParameters (d : ℕ) (θ : ℝ) (β : Coeff d) (δ : ℝ) : Fin (d+3) → ℝ :=
  fun i => if i.val = 0 then θ else if h : i.val < d+2 then β ⟨i.val-1,by omega⟩ else δ

private theorem row_parameter_coeff (d : ℕ) (θ : ℝ) (β : Coeff d) (δ : ℝ)
    (k : Fin (d+1)) : rowParameters d θ β δ ⟨k.val+1,by omega⟩ = β k := by
  simp [rowParameters,show k.val+1 ≠ 0 by omega,show k.val+1 < d+2 by omega]

def rowReadPolynomial (d : ℕ) (w : List Bool) (i : Fin (w.length+1)) : RowPolynomial d :=
  (MvPolynomial.C (rowBase w i) + MvPolynomial.X 0 * MvPolynomial.C (rowSlope w i)) *
    (∑ k : Fin (d+1), MvPolynomial.C ((i.val : ℝ)^k.val) *
      MvPolynomial.X ⟨k.val+1,by omega⟩) + MvPolynomial.X ⟨d+2,by omega⟩

def rowOutputPolynomial (d : ℕ) (w : List Bool) (C : Readout d w)
    (k : Fin (d+1)) : RowPolynomial d :=
  ∑ i : Fin (w.length+1), MvPolynomial.C (C k i) * rowReadPolynomial d w i

def rowWedge (d : ℕ) (w : List Bool) (C : Readout d w)
    (j k : Fin (d+1)) : RowPolynomial d :=
  MvPolynomial.X ⟨j.val+1,by omega⟩ * rowOutputPolynomial d w C k -
    MvPolynomial.X ⟨k.val+1,by omega⟩ * rowOutputPolynomial d w C j

private theorem eval_row_read (d : ℕ) (w : List Bool)
    (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1) (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ)
    (i : Fin (w.length+1)) :
    MvPolynomial.eval (rowParameters d θ β δ) (rowReadPolynomial d w i) =
      readings (rowWorld d θ hθ hθ' β hβ δ) w i := by
  simp only [rowReadPolynomial, map_add, map_mul, map_sum, MvPolynomial.eval_C,
    MvPolynomial.eval_X, row_parameter_coeff]
  rw [row_readings_affine]
  simp [rowParameters, gain, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum, mul_comm]

private theorem eval_row_wedge (d : ℕ) (w : List Bool) (C : Readout d w)
    (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1) (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ)
    (j k : Fin (d+1)) :
    MvPolynomial.eval (rowParameters d θ β δ) (rowWedge d w C j k) =
      β j * C.mulVec (readings (rowWorld d θ hθ hθ' β hβ δ) w) k -
        β k * C.mulVec (readings (rowWorld d θ hθ hθ' β hβ δ) w) j := by
  simp only [rowWedge, map_sub, map_mul, MvPolynomial.eval_X, row_parameter_coeff,
    rowOutputPolynomial, map_sum, MvPolynomial.eval_C, eval_row_read d w θ hθ hθ' β hβ δ]
  rfl

def RowEligible (d : ℕ) (w : List Bool) : Prop :=
  false ∉ w ∨ ∃ k tail, w = List.replicate k true ++ [false] ++ tail ∧
    tail.length+1 < d+1

private theorem row_success_polynomial (d : ℕ) (hd : 1 ≤ d) (c : WordMatrix d)
    (hc : RowEligible d c.1) :
    ∃ p : RowPolynomial d, p ≠ 0 ∧
      ∀ (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1) (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ),
        Succeeds (rowWorld d θ hθ hθ' β hβ δ) c.1 c.2 →
          MvPolynomial.eval (rowParameters d θ β δ) p = 0 := by
  classical
  by_cases hh : ∃ (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1) (β : Coeff d)
      (hβ : β ≠ 0) (δ : ℝ), Succeeds (rowWorld d θ hθ hθ' β hβ δ) c.1 c.2
  · have hex : ∃ j k, rowWedge d c.1 c.2 j k ≠ 0 := by
      by_contra h
      push_neg at h
      have hu : RowUniversallyCollinear d c.1 c.2 := by
        intro θ hθ hθ' β hβ δ
        apply collinear_of_wedges β _ hβ
        intro j k
        have he := eval_row_wedge d c.1 c.2 θ hθ hθ' β hβ δ j k
        rw [h j k,map_zero] at he
        exact he.symm
      obtain ⟨θ,hθ,hθ',β,hβ,δ,hs⟩ := hh
      exact (identical_row_annihilation d hd c.1 c.2 hu hc θ hθ hθ' β hβ δ).2 hs
    obtain ⟨j,k,hp⟩ := hex
    refine ⟨rowWedge d c.1 c.2 j k,hp,?_⟩
    intro θ hθ hθ' β hβ δ hs
    rw [eval_row_wedge d c.1 c.2 θ hθ hθ' β hβ δ j k]
    obtain ⟨a,_,ha⟩ := hs
    change c.2.mulVec (readings _ c.1) = a • β at ha
    simp only [ha, Pi.smul_apply, smul_eq_mul]
    ring
  · exact ⟨1,one_ne_zero,fun θ hθ hθ' β hβ δ hs =>
      False.elim (hh ⟨θ,hθ,hθ',β,hβ,δ,hs⟩)⟩

def pureJHistoryPolynomial (d n : ℕ) (i : Fin n) : RowPolynomial d :=
  (∑ k : Fin (d+1), MvPolynomial.C ((i.val : ℝ)^k.val) *
    MvPolynomial.X ⟨k.val+1,by omega⟩) + MvPolynomial.X ⟨d+2,by omega⟩

def historyPullback (d n : ℕ) (p : MvPolynomial (Fin n) ℝ) : RowPolynomial d :=
  MvPolynomial.bind₁ (pureJHistoryPolynomial d n) p

private theorem eval_history_pullback (d n : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (θ : ℝ) (β : Coeff d) (δ : ℝ) :
    MvPolynomial.eval (rowParameters d θ β δ) (historyPullback d n p) =
      MvPolynomial.eval (fun i : Fin n => (gain d β).eval (clocks n i) + δ) p := by
  rw [historyPullback]
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) _ _ = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval (fun i => MvPolynomial.eval (rowParameters d θ β δ)
    (pureJHistoryPolynomial d n i)) p = _
  apply congrArg (fun v : Fin n → ℝ => MvPolynomial.eval v p)
  ext i
  simp only [pureJHistoryPolynomial, map_add, map_mul, map_sum, MvPolynomial.eval_C,
    MvPolynomial.eval_X, row_parameter_coeff]
  simp [rowParameters, clocks, gain, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum, mul_comm]

/-- Surjectivity concerns the extended coefficient-and-drift space, including
its zero vector; the actual-world restriction is imposed only afterwards. -/
theorem history_pullback_nonzero (d n : ℕ) (hn : n ≤ d+1)
    (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) : historyPullback d n p ≠ 0 := by
  intro hz
  apply hp
  apply MvPolynomial.funext
  intro y
  obtain ⟨⟨β,δ⟩,he⟩ := pureJ_history_surjective d n hn y
  have hh := eval_history_pullback d n p 0 β δ
  change (fun i : Fin n => (gain d β).eval (clocks n i) + δ) = y at he
  rw [hz,map_zero,he] at hh
  exact hh.symm


private theorem palette_pairs_countable (d : ℕ) (P : Protocol d) :
    ({c : WordMatrix d | c.2 ∈ P.palette c.1} : Set (WordMatrix d)).Countable := by
  letI (w : List Bool) : Countable {C : Readout d w // C ∈ P.palette w} :=
    (P.countable w).to_subtype
  have h := Set.countable_range
    (fun c : (w : List Bool) × {C : Readout d w // C ∈ P.palette w} =>
      (⟨c.1,c.2.1⟩ : WordMatrix d))
  apply h.mono
  rintro ⟨w,C⟩ hc
  exact ⟨⟨w,⟨C,hc⟩⟩,rfl⟩

private theorem first_m_decomposition (w : List Bool) (h : false ∈ w) :
    ∃ k tail, w = List.replicate k true ++ [false] ++ tail := by
  induction w with
  | nil => simp at h
  | cons a w ih =>
      cases a with
      | false => exact ⟨0,w,by simp⟩
      | true =>
          obtain ⟨k,tail,he⟩ := ih (by simpa using h)
          exact ⟨k+1,tail,by simp [List.replicate_succ,he]⟩

private theorem reached_last (d : ℕ) (P : Protocol d) (W : World d)
    (v : List Bool) (a : Bool) (hr : Reaches P W (v ++ [a])) :
    Reaches P W v ∧ P.decide v (readings W v) = Sum.inl a := by
  generalize he : v ++ [a] = z at hr
  cases hr with
  | initial => simp at he
  | @step u b hu hb =>
      obtain ⟨hv,ha⟩ := List.append_inj' he (by simp)
      have hab : a = b := by simpa using ha
      subst u
      subst b
      exact ⟨hu,hb⟩

/-- The lower bound uses only actual reached histories and countable fixed
palettes. Decisions, stopping and selectors carry no regularity hypothesis. -/
theorem adaptive_lower (d : ℕ) (hd : 1 ≤ d) (P : Protocol d) :
    ¬ UniformlySuccessful P (2*d+2) := by
  classical
  intro hsuccess
  let s : Set (WordMatrix d) := {c | c.2 ∈ P.palette c.1 ∧ Eligible d c}
  let t : Set (WordMatrix d) := {c | c.2 ∈ P.palette c.1 ∧ RowEligible d c.1}
  have hs : s.Countable := (palette_pairs_countable d P).mono (fun _ h => h.1)
  have ht : t.Countable := (palette_pairs_countable d P).mono (fun _ h => h.1)
  letI : Countable s := hs.to_subtype
  letI : Countable t := ht.to_subtype
  choose q hq hcomplete using (fun n : Fin (d+1) =>
    short_history_completion d hd s hs (fun _ h => h.2) (n.val+1) (by omega) (by omega))
  choose r hr hrcert using (fun c : t => row_success_polynomial d hd c.1 c.2.2)
  let I := t ⊕ (Fin (d+1) × s)
  let poly : I → RowPolynomial d :=
    Sum.elim r (fun z => historyPullback d (z.1.val+1) (q z.1 z.2))
  have hp (i : I) : poly i ≠ 0 := by
    cases i with
    | inl c => exact hr c
    | inr z => exact history_pullback_nonzero d _ (by omega) _ (hq z.1 z.2)
  let U : Set (Fin (d+3) → ℝ) := {a | 0 < a 0 ∧ a 0 < 1 ∧
    (fun k : Fin (d+1) => a ⟨k.val+1,by omega⟩) ≠ 0}
  have ho : IsOpen U :=
    (isOpen_lt continuous_const (continuous_apply _)).inter
      ((isOpen_lt (continuous_apply _) continuous_const).inter
        (isOpen_ne.preimage (continuous_pi fun _ => continuous_apply _)))
  have hne : U.Nonempty := by
    let a := rowParameters d (1/2) (Pi.single (⟨0,by omega⟩ : Fin (d+1)) 1) 0
    refine ⟨a,by norm_num [a,rowParameters],by norm_num [a,rowParameters],?_⟩
    intro hz
    have h := congrFun hz (⟨0,by omega⟩ : Fin (d+1))
    change rowParameters d (1/2) (Pi.single (⟨0,by omega⟩ : Fin (d+1)) 1) 0
      ⟨0+1,by omega⟩ = 0 at h
    rw [row_parameter_coeff d (1/2) (Pi.single (⟨0,by omega⟩ : Fin (d+1)) 1) 0
      (⟨0,by omega⟩ : Fin (d+1))] at h
    simpa using h
  obtain ⟨a,ha,havoid⟩ := countable_polynomial_avoidance (d+3) poly hp U ho hne
  let θ := a 0
  let β : Coeff d := fun k => a ⟨k.val+1,by omega⟩
  let δ := a ⟨d+2,by omega⟩
  have hθ : 0 < θ := ha.1
  have hθ' : θ < 1 := ha.2.1
  have hβ : β ≠ 0 := ha.2.2
  have hparam : rowParameters d θ β δ = a := by
    ext i
    dsimp [rowParameters, θ,β,δ]
    split_ifs with h0 hb
    · exact congrArg a (Fin.ext h0.symm)
    · exact congrArg a (Fin.ext (by dsimp; omega))
    · exact congrArg a (Fin.ext (by dsimp; omega))
  let W := rowWorld d θ hθ hθ' β hβ δ
  have hbad (w : List Bool) (C : Readout d w) (hC : C ∈ P.palette w)
      (hw : RowEligible d w) : ¬ Succeeds W w C := by
    intro hh
    let c : t := ⟨⟨w,C⟩,hC,hw⟩
    apply havoid (.inl c)
    rw [← hparam]
    exact hrcert c θ hθ hθ' β hβ δ hh
  obtain ⟨w,C,hterm,hN,hout⟩ := hsuccess W
  by_cases hM : false ∈ w
  · obtain ⟨k,tail,hw⟩ := first_m_decomposition w hM
    by_cases hk : k+1 ≤ d+1
    · let n : Fin (d+1) := ⟨k,by omega⟩
      let y : Fin (n.val+1) → ℝ := fun i => (gain d β).eval (clocks _ i) + δ
      have hy : y ∉ exceptionalHistories (q n) := by
        rintro ⟨c,hc⟩
        apply havoid (.inr (n,c))
        rw [← hparam]
        exact (eval_history_pullback d _ (q n c) θ β δ).trans hc
      obtain ⟨W',hprefix,hfail⟩ := hcomplete n y hy
      have htake : w.take (k+1) = List.replicate k true ++ [false] := by
        rw [hw]
        simpa using (List.take_left (l₁ := List.replicate k true ++ [false]) (l₂ := tail))
      have hreach := reaches_take P W hterm.1 (k+1) (by rw [hw]; simp)
      rw [htake] at hreach
      obtain ⟨hpre,hnext⟩ := reached_last d P W _ false hreach
      have he : readings W (List.replicate k true) = readings W' (List.replicate k true) := by
        ext i
        have hi : i.val < n.val+1 := by have := i.isLt; simp [n] at *; omega
        have hh := hprefix ⟨i.val,hi⟩
        have hirow := congrFun (identical_row_readings d θ hθ hθ' β hβ δ k) i
        change readAt W _ i.val = readAt W' _ i.val
        have hh' : readAt W' (List.replicate k true) i.val =
            (gain d β).eval (i.val : ℝ) + δ := by simpa [n,y,clocks] using hh
        have hl : readAt W (List.replicate k true) i.val =
            (gain d β).eval (i.val : ℝ) + δ := by simpa [W,readings] using hirow
        exact hl.trans hh'.symm
      have hfirst := identical_prefix_firstM P W W' k hpre he hnext
      obtain ⟨w',C',ht',hN',hs'⟩ := hsuccess W'
      have hpreword := terminal_extends_reached P W' _ w' C' hfirst ht'
      have hM' : false ∈ w' := by
        obtain ⟨u,hu⟩ := hpreword
        rw [← hu]
        simp
      let c' : s := ⟨⟨w',C'.1⟩,C'.2,hM',by omega⟩
      exact hfail c' hs'
    · exact hbad w C.1 C.2 (.inr ⟨k,tail,hw,by
        have hh : w.length = k+1+tail.length := by simp [hw]; omega
        omega⟩) hout
  · exact hbad w C.1 C.2 (.inl hM) hout

/-- Both halves of the original native adaptive gain-ray threshold. -/
theorem adaptive_threshold (d : ℕ) (hd : 1 ≤ d) :
    (∀ P : Protocol d, ¬ UniformlySuccessful P (2*d+2)) ∧
      ∃ P : Protocol d, UniformlySuccessful P (2*d+3) :=
  ⟨adaptive_lower d hd, upperProtocol d, adaptive_upper d⟩

#print axioms short_history_completion
#print axioms adaptive_lower
#print axioms adaptive_threshold
end D5.S3.Observer.Linear.GainRay
