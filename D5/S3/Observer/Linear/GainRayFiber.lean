/- GID: D5/S3/Observer/Linear/GainRayFiber
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayFiber
   mirror-E: none(waiver:actual-compatible-history-coordinates)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.Equiv]
   utility: none
   digest: Full compatible pure-J histories admit rational coordinates and nonzero polynomial pullbacks. -/

import D5.S3.Observer.Linear.GainRaySuccessPolynomial
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Topology.Algebra.MvPolynomial

set_option autoImplicit false
noncomputable section
open scoped Matrix
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
  rw [eval_fiber_pullback, numerator_encoded d n hn x r hx hr]
  have hD : x+r ≠ 0 := ne_of_gt (add_pos hx hr)
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

#print axioms fiber_pullback_nonzero
#print axioms fiber_world_prefix
#print axioms fiber_nonzero_coefficient
end D5.S3.Observer.Linear.GainRay
