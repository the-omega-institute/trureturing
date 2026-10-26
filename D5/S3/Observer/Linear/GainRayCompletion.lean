/- GID: D5/S3/Observer/Linear/GainRayCompletion
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayCompletion
   mirror-E: none(waiver:countable-actual-history-completion)
   anchors: []
   utility: none
   digest: Countable eligible word palettes admit whole-world completions of every generic short history. -/

import D5.S3.Observer.Linear.GainRayFiber
import D5.S3.Observer.Linear.GainRayNuisance
import D5.S3.Observer.Linear.GainRayEndpoint
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
noncomputable section
open scoped Matrix
open MeasureTheory
namespace D5.S3.Observer.Linear.GainRay

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

#print axioms short_history_completion
end D5.S3.Observer.Linear.GainRay
