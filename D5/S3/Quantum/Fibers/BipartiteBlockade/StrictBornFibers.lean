/- GID: D5/S3/Quantum/Fibers/BipartiteBlockade/StrictBornFibers
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/BipartiteBlockade/StrictBornFibers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full-rank centered single-drive ambiguities change a strictly positive five-mode joint endpoint mass. -/

import D5.S3.Quantum.Fibers.BipartiteBlockade.GraphResidualDimension
import D5.S3.Quantum.Fibers.BipartiteBlockade.FiveModeSettingNumber
import D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates

attribute [local instance] LieRing.ofAssociativeRing
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Fibers.BipartiteBlockade.StrictBornFibers

open DiagonalResidual GraphResidualDimension
open D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates
open private small_centered_density_perturbations from
  D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower
open private five_formula from
  D5.S3.Quantum.Fibers.BipartiteBlockade.FiveModeSettingNumber

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem strict_modes (G : SimpleGraph V) (u v w : V)
    (hN : ∀ x, G.Adj v x ↔ x = u ∨ x = w) (huw : u ≠ w)
    (color : V → Bool) (proper : ∀ x y, G.Adj x y → color x ≠ color y)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) (positive : ρ.PosDef) :
    ∀ k, 0 < bornModeLaw G u v w ρ k := by
  have hvu : G.Adj v u := (hN u).2 (Or.inl rfl)
  have hvw : G.Adj v w := (hN w).2 (Or.inr rfl)
  have hvune : v ≠ u := G.ne_of_adj hvu
  have hvwne : v ≠ w := G.ne_of_adj hvw
  have hind : ¬ G.Adj u w := by
    intro hadj
    have hl := proper v u hvu
    have hr := proper v w hvw
    have he := proper u w hadj
    cases hc : color v <;> cases hu : color u <;> cases hw : color w <;> simp_all
  let empty : Configuration G := ⟨∅, by simp⟩
  let left : Configuration G := ⟨{u}, by simp⟩
  let center : Configuration G := ⟨{v}, by simp⟩
  let right : Configuration G := ⟨{w}, by simp⟩
  let both : Configuration G := ⟨{u,w}, by
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact G.irrefl
    · exact hind
    · exact fun h => hind h.symm
    · exact G.irrefl⟩
  let rep : Fin 5 → Configuration G := ![empty,left,center,right,both]
  have hrep (k : Fin 5) : localMode G u v w (rep k) = k := by
    fin_cases k <;> simp [rep, empty, left, center, right, both, localMode,
      hvune, hvwne, huw, huw.symm]
  intro k
  unfold bornModeLaw
  apply Finset.sum_pos'
  · intro S _
    split_ifs
    · exact (Complex.nonneg_iff.mp positive.posSemidef.diag_nonneg).1
    · rfl
  · refine ⟨rep k, Finset.mem_univ _, ?_⟩
    rw [if_pos (hrep k)]
    exact (Complex.pos_iff.mp positive.diag_pos).1

private theorem strict_coordinates (G : SimpleGraph V) (u v w : V)
    (hN : ∀ x, G.Adj v x ↔ x = u ∨ x = w) (huw : u ≠ w)
    (color : V → Bool) (proper : ∀ x y, G.Adj x y → color x ≠ color y)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ)
    (positive : ρ.PosDef) (normalized : Matrix.trace ρ = 1) :
    0 < 1 - occupationMean G ρ v ∧
    0 < min (min (occupationMean G ρ u) (occupationMean G ρ w))
      (min (1 - occupationMean G ρ v - occupationMean G ρ u)
        (1 - occupationMean G ρ v - occupationMean G ρ w)) := by
  have hs : bornModeLaw G u v w ρ ∈ openSimplex :=
    ⟨strict_modes G u v w hN huw color proper ρ positive,
      (born_five_mode_reconstruction G u v w hN huw color proper
        (fun _ => 1) (by norm_num) ρ positive.posSemidef normalized).2.1⟩
  have hvisible : visible (bornModeLaw G u v w ρ) =
      (occupationMean G ρ u, occupationMean G ρ w, occupationMean G ρ v) := by
    rw [five_formula G color proper ρ positive.posSemidef normalized u v w hN huw]
    apply Prod.ext
    · simp [visible]; ring
    · apply Prod.ext <;> simp [visible] <;> ring
  have hp := mixed_coordinates_global_chart.1 _ hs
  rw [hvisible] at hp
  obtain ⟨hx, hy, hz, hxz, hyz⟩ := hp
  refine ⟨by linarith, lt_min (lt_min hx hy) (lt_min ?_ ?_)⟩ <;> linarith

/-- Product of the endpoint occupation indicators in the five physical modes. -/
private def endpointTask (k : Fin 5) : ℝ :=
  (if k = 1 ∨ k = 4 then 1 else 0) * (if k = 3 ∨ k = 4 then 1 else 0)

/-- At degree at most two, a single-drive ambiguity can occur arbitrarily close
to the maximally mixed state with every local mode strictly positive, while an
actual endpoint joint probability changes. -/
theorem strict_born_single_setting_fiber (G : SimpleGraph V) (connected : G.Connected)
    (color : V → Bool) (proper : ∀ x y, G.Adj x y → color x ≠ color y)
    (Ω : V → ℝ) (positiveDrive : ∀ v, 0 < Ω v)
    (maximum : ∀ v, (G.neighborFinset v).card ≤ 2)
    (two : 2 ≤ (nonlinearNeighborhoods G).card) (radius : ℝ) (hRadius : 0 < radius) :
    ∃ ρ σ : Matrix (Configuration G) (Configuration G) ℂ,
      ρ.PosDef ∧ Matrix.trace ρ = 1 ∧ σ.PosDef ∧ Matrix.trace σ = 1 ∧
      ‖CStarMatrix.ofMatrix (ρ - maximallyMixed G)‖ < radius ∧
      ‖CStarMatrix.ofMatrix (σ - maximallyMixed G)‖ < radius ∧
      (∀ v, occupationMean G ρ v = occupationMean G σ v) ∧
      (∀ v, acceleration G Ω ρ v = acceleration G Ω σ v) ∧
      (∀ u v w, (∀ x, G.Adj v x ↔ x = u ∨ x = w) → u ≠ w →
        ∀ k, 0 < bornModeLaw G u v w ρ k ∧ 0 < bornModeLaw G u v w σ k) ∧
      ∃ u v w, (∀ x, G.Adj v x ↔ x = u ∨ x = w) ∧ u ≠ w ∧
        0 < 1 - occupationMean G ρ v ∧ 0 < 1 - occupationMean G σ v ∧
        0 < min (min (occupationMean G ρ u) (occupationMean G ρ w))
          (min (1 - occupationMean G ρ v - occupationMean G ρ u)
            (1 - occupationMean G ρ v - occupationMean G ρ w)) ∧
        0 < min (min (occupationMean G σ u) (occupationMean G σ w))
          (min (1 - occupationMean G σ v - occupationMean G σ u)
            (1 - occupationMean G σ v - occupationMean G σ w)) ∧
        bornModeLaw G u v w ρ 4 ≠ bornModeLaw G u v w σ 4 ∧
        endpointTask 4 - endpointTask 1 - endpointTask 3 + endpointTask 0 = 1 ∧
        (∑ k, bornModeLaw G u v w ρ k * endpointTask k) ≠
          (∑ k, bornModeLaw G u v w σ k * endpointTask k) ∧
        (1 - occupationMean G ρ v) * bornModeLaw G u v w ρ 4 -
          occupationMean G ρ u * occupationMean G ρ w ≠
        (1 - occupationMean G σ v) * bornModeLaw G u v w σ 4 -
          occupationMean G σ u * occupationMean G σ w := by
  have classification := five_mode_setting_number_classification G connected color proper maximum
  have insufficient : ¬ fiveModeSettingsSufficient G (fun _ : Fin 1 => Ω) := by
    intro sufficient
    have hmem : 1 ∈ feasibleFiveModeCounts G :=
      ⟨(fun _ : Fin 1 => Ω), (fun _ => positiveDrive), sufficient⟩
    have hmin : fiveModeSettingNumber G ≤ 1 := Nat.sInf_le hmem
    rw [classification.2.2, Nat.min_eq_left two] at hmin
    omega
  unfold fiveModeSettingsSufficient at insufficient
  push_neg at insufficient
  obtain ⟨P, Q, hP, htP, hQ, htQ, hm, ha, u, v, w, hN, huw, hLaw⟩ := insufficient
  have hblock : blockadeMean G P v ≠ blockadeMean G Q v := by
    intro heq
    apply hLaw
    rw [five_formula G color proper P hP htP u v w hN huw,
      five_formula G color proper Q hQ htQ u v w hN huw, heq, hm u, hm v, hm w]
  let R := P - Q
  have hRH : R.IsHermitian := hP.isHermitian.sub hQ.isHermitian
  have hRt : Matrix.trace R = 0 := by simp [R, Matrix.trace_sub, htP, htQ]
  have hRn (x : V) : (Matrix.trace (R * number G x)).re = 0 := by
    change occupationMean G (P - Q) x = 0
    simpa [occupationMean, Matrix.sub_mul, Matrix.trace_sub] using sub_eq_zero.mpr (hm x)
  have hRa (x : V) :
      (Matrix.trace (R * ⁅hamiltonian G (fun y => (Ω y : ℂ)),
        ⁅hamiltonian G (fun y => (Ω y : ℂ)), number G x⁆⁆)).re = 0 := by
    have heq := ha 0 x
    change acceleration G Ω P x = acceleration G Ω Q x at heq
    unfold acceleration at heq
    simp only [R, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
    linarith
  have hRb : (Matrix.trace (R * blockade G v)).re =
      blockadeMean G P v - blockadeMean G Q v := by
    simp [R, Matrix.sub_mul, Matrix.trace_sub, blockadeMean]
  letI : Nonempty (Configuration G) := ⟨⟨∅, by simp⟩⟩
  obtain ⟨η, hη, hsmall⟩ := small_centered_density_perturbations R hRH hRt
  let B := CStarMatrix.ofMatrix R
  let t : ℝ := min (η / 2) (radius / (2 * (‖B‖ + 1)))
  have htpos : 0 < t := lt_min (by linarith) (div_pos hRadius (by positivity))
  have htη : |t| < η := by
    rw [abs_of_pos htpos]
    have := min_le_left (η / 2) (radius / (2 * (‖B‖ + 1)))
    linarith
  have htNorm : |t| * ‖B‖ < radius := by
    rw [abs_of_pos htpos]
    have htbound := min_le_right (η / 2) (radius / (2 * (‖B‖ + 1)))
    have hden : 0 < 2 * (‖B‖ + 1) := by positivity
    have hmul := (le_div_iff₀ hden).mp htbound
    have hn := norm_nonneg B
    nlinarith
  let ρ := maximallyMixed G + t • R
  let σ := maximallyMixed G + (-t) • R
  have hρ := hsmall t htη
  have hσ := hsmall (-t) (by simpa only [abs_neg] using htη)
  have near (s : ℝ) (hs : |s| = |t|) :
      ‖CStarMatrix.ofMatrix (maximallyMixed G + s • R - maximallyMixed G)‖ < radius := by
    have hd : maximallyMixed G + s • R - maximallyMixed G = s • R := by abel
    rw [hd]
    change ‖(s : ℂ) • B‖ < radius
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, hs]
    exact htNorm
  have eval (s : ℝ) (O : Matrix (Configuration G) (Configuration G) ℂ) :
      Matrix.trace ((maximallyMixed G + s • R) * O) =
        Matrix.trace (maximallyMixed G * O) + s • Matrix.trace (R * O) := by
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul]
  have sameM (x : V) : occupationMean G ρ x = occupationMean G σ x := by
    unfold occupationMean
    simp only [ρ, σ, eval, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, hRn, zero_mul, mul_zero, sub_zero, add_zero]
  have sameA (x : V) : acceleration G Ω ρ x = acceleration G Ω σ x := by
    unfold acceleration
    simp only [ρ, σ, eval, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, hRa, zero_mul, mul_zero, sub_zero, add_zero]
  refine ⟨ρ, σ, hρ.1, hρ.2, hσ.1, hσ.2, near t rfl,
    near (-t) (abs_neg t), sameM, sameA, ?_, ?_⟩
  · intro u v w hN huw k
    exact ⟨strict_modes G u v w hN huw color proper ρ hρ.1 k,
      strict_modes G u v w hN huw color proper σ hσ.1 k⟩
  · have hcρ := strict_coordinates G u v w hN huw color proper ρ hρ.1 hρ.2
    have hcσ := strict_coordinates G u v w hN huw color proper σ hσ.1 hσ.2
    have jointDifferent : bornModeLaw G u v w ρ 4 ≠ bornModeLaw G u v w σ 4 := by
      intro heq
      rw [five_formula G color proper ρ hρ.1.posSemidef hρ.2 u v w hN huw,
        five_formula G color proper σ hσ.1.posSemidef hσ.2 u v w hN huw] at heq
      change blockadeMean G ρ v - 1 + occupationMean G ρ u + occupationMean G ρ w =
        blockadeMean G σ v - 1 + occupationMean G σ u + occupationMean G σ w at heq
      have hbeq : blockadeMean G ρ v = blockadeMean G σ v := by
        have hu := sameM u
        have hw := sameM w
        linarith
      have hbρ : blockadeMean G ρ v = blockadeMean G (maximallyMixed G) v +
          t * (blockadeMean G P v - blockadeMean G Q v) := by
        unfold blockadeMean
        rw [eval]
        simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hRb, blockadeMean]
      have hbσ : blockadeMean G σ v = blockadeMean G (maximallyMixed G) v +
          (-t) * (blockadeMean G P v - blockadeMean G Q v) := by
        unfold blockadeMean
        rw [eval]
        simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hRb, blockadeMean]
      rw [hbρ, hbσ] at hbeq
      have hproduct : t * (blockadeMean G P v - blockadeMean G Q v) = 0 := by linarith
      exact mul_ne_zero (ne_of_gt htpos) (sub_ne_zero.mpr hblock) hproduct
    refine ⟨u, v, w, hN, huw, hcρ.1, hcσ.1, hcρ.2, hcσ.2, jointDifferent, ?_, ?_, ?_⟩
    · norm_num [endpointTask]
    · simpa [Fin.sum_univ_five, endpointTask] using jointDifferent
    · rw [← sameM v, ← sameM u, ← sameM w]
      intro heq
      apply jointDifferent
      apply mul_left_cancel₀ (ne_of_gt hcρ.1)
      linarith

/-- info: 'D5.S3.Quantum.Fibers.BipartiteBlockade.StrictBornFibers.strict_born_single_setting_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms strict_born_single_setting_fiber

end D5.S3.Quantum.Fibers.BipartiteBlockade.StrictBornFibers
