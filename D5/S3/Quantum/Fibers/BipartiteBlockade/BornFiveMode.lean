/- GID: D5/S3/Quantum/Fibers/BipartiteBlockade/BornFiveMode
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/BipartiteBlockade/BornFiveMode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Born marginal at a degree-two blocked center is a five-mode law recovered from occupations and the empty-neighborhood probability. -/

import D5.S3.Quantum.Fibers.BipartiteBlockade.TwoColorReadout

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Classical ComplexOrder

namespace D5.S3.Quantum.Fibers.BipartiteBlockade

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The order is vacuum, left, center, right, both ends. -/
def localMode (G : SimpleGraph V) (u v w : V) (S : Configuration G) : Fin 5 :=
  if v ∈ S.val then 2 else if u ∈ S.val then
    if w ∈ S.val then 4 else 1
  else if w ∈ S.val then 3 else 0

/-- The diagonal Born marginal, without an independence assumption on the state. -/
def bornModeLaw (G : SimpleGraph V) (u v w : V)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) (k : Fin 5) : ℝ :=
  ∑ S, if localMode G u v w S = k then (ρ S S).re else 0

private theorem occupationMean_sum (G : SimpleGraph V)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) (x : V) :
    occupationMean G ρ x = ∑ S, if x ∈ S.val then (ρ S S).re else 0 := by
  simp only [occupationMean, number, Matrix.trace, Matrix.mul_diagonal,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hx : x ∈ S.val <;> simp [hx]

private theorem blockadeMean_sum (G : SimpleGraph V)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) (x : V) :
    blockadeMean G ρ x = ∑ S, if clear G x S then (ρ S S).re else 0 := by
  simp only [blockadeMean, blockade, Matrix.trace, Matrix.mul_diagonal,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hx : clear G x S <;> simp [hx]

private theorem local_blocking (G : SimpleGraph V) (u v w : V)
    (hN : ∀ x, G.Adj v x ↔ x = u ∨ x = w) (S : Configuration G) :
    clear G v S ↔ u ∉ S.val ∧ w ∉ S.val := by
  constructor
  · intro h
    exact ⟨fun hu => h u hu ((hN u).2 (Or.inl rfl)),
      fun hw => h w hw ((hN w).2 (Or.inr rfl))⟩
  · rintro ⟨hu, hw⟩ x hx hadj
    rcases (hN x).1 hadj with rfl | rfl
    · exact hu hx
    · exact hw hx

private theorem local_legality (G : SimpleGraph V) (u v w : V)
    (hN : ∀ x, G.Adj v x ↔ x = u ∨ x = w) (S : Configuration G)
    (hv : v ∈ S.val) : u ∉ S.val ∧ w ∉ S.val := by
  exact ⟨fun hu => S.property v hv u hu ((hN u).2 (Or.inl rfl)),
    fun hw => S.property v hv w hw ((hN w).2 (Or.inr rfl))⟩

private def pureConfiguration (G : SimpleGraph V) (S : Configuration G) :
    Matrix (Configuration G) (Configuration G) ℂ :=
  Matrix.diagonal fun T => if T = S then 1 else 0

private theorem pureConfiguration_density (G : SimpleGraph V) (S : Configuration G) :
    (pureConfiguration G S).PosSemidef ∧ Matrix.trace (pureConfiguration G S) = 1 := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro T
    simp only [pureConfiguration]
    split_ifs <;> norm_num
  · simp [pureConfiguration, Matrix.trace]

private theorem pureConfiguration_occupation (G : SimpleGraph V) (S : Configuration G)
    (x : V) : occupationMean G (pureConfiguration G S) x =
      if x ∈ S.val then 1 else 0 := by
  rw [occupationMean_sum]
  simp only [pureConfiguration, Matrix.diagonal_apply_eq]
  simp only [apply_ite Complex.re, Complex.one_re, Complex.zero_re]
  calc
    _ = ∑ T, if T = S then (if x ∈ S.val then (1 : ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      by_cases h : T = S <;> simp [h]
    _ = _ := by simp

private theorem pureConfiguration_blockade (G : SimpleGraph V) (S : Configuration G)
    (x : V) : blockadeMean G (pureConfiguration G S) x =
      if clear G x S then 1 else 0 := by
  rw [blockadeMean_sum]
  simp only [pureConfiguration, Matrix.diagonal_apply_eq]
  simp only [apply_ite Complex.re, Complex.one_re, Complex.zero_re]
  calc
    _ = ∑ T, if T = S then (if clear G x S then (1 : ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      by_cases h : T = S <;> simp [h]
    _ = _ := by simp

private theorem expectation_affine (G : SimpleGraph V)
    (P Q : Matrix (Configuration G) (Configuration G) ℂ) (x : V) :
    occupationMean G ((1 / 2 : ℝ) • (P + Q)) x =
      (occupationMean G P x + occupationMean G Q x) / 2 ∧
    blockadeMean G ((1 / 2 : ℝ) • (P + Q)) x =
      (blockadeMean G P x + blockadeMean G Q x) / 2 := by
  simp [occupationMean, blockadeMean, Matrix.add_mul, Matrix.trace_add,
    Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul]
  constructor <;> ring

/-- A degree-two center's Born marginal is an actual probability law. Its five
masses, including the joint endpoint mass, follow from the three occupations
and the empty-neighborhood expectation, for arbitrary initial coherence. -/
theorem born_five_mode_reconstruction (G : SimpleGraph V) (u v w : V)
    (hN : ∀ x, G.Adj v x ↔ x = u ∨ x = w)
    (huw : u ≠ w)
    (color : V → Bool) (hcolor : ∀ x y, G.Adj x y → color x ≠ color y)
    (Ω : V → ℝ) (hΩ : Ω v ≠ 0)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ)
    (hρ : ρ.PosSemidef) (ht : Matrix.trace ρ = 1) :
    let β := 2 * occupationMean G ρ v +
      if color v then
        (acceleration G (colorScaledDrive color Ω) ρ v - 2 * acceleration G Ω ρ v) /
          (4 * Ω v ^ 2)
      else
        (2 * acceleration G Ω ρ v - acceleration G (colorScaledDrive color Ω) ρ v) /
          (2 * Ω v ^ 2)
    (∀ k, 0 ≤ bornModeLaw G u v w ρ k) ∧
    (∑ k, bornModeLaw G u v w ρ k) = 1 ∧
    bornModeLaw G u v w ρ =
      ![β - occupationMean G ρ v,
        1 - β - occupationMean G ρ w,
        occupationMean G ρ v,
        1 - β - occupationMean G ρ u,
        β - 1 + occupationMean G ρ u + occupationMean G ρ w] ∧
    ∃ σ τ : Matrix (Configuration G) (Configuration G) ℂ,
      σ.PosSemidef ∧ Matrix.trace σ = 1 ∧
      τ.PosSemidef ∧ Matrix.trace τ = 1 ∧
      (∀ x, occupationMean G σ x = occupationMean G τ x) ∧
      blockadeMean G σ v ≠ blockadeMean G τ v := by
  dsimp only
  rw [← two_color_readout_inverse G color hcolor Ω ρ v hΩ]
  have hind : ¬ G.Adj u w := by
    intro hadj
    have hleft := hcolor v u ((hN u).2 (Or.inl rfl))
    have hright := hcolor v w ((hN w).2 (Or.inr rfl))
    have hends := hcolor u w hadj
    cases hc : color v <;> cases hl : color u <;> cases hr : color w <;> simp_all
  have hs : (∑ S : Configuration G, (ρ S S).re) = 1 := by
    simpa [Matrix.trace] using congrArg Complex.re ht
  have hp (k : Fin 5) : 0 ≤ bornModeLaw G u v w ρ k := by
    apply Finset.sum_nonneg
    intro S _
    split_ifs
    · exact (Complex.nonneg_iff.mp hρ.diag_nonneg).1
    · rfl
  have partition (S : Configuration G) :
      (∑ k : Fin 5, if localMode G u v w S = k then (ρ S S).re else 0) =
        (ρ S S).re := by simp
  have htotal : (∑ k, bornModeLaw G u v w ρ k) = 1 := by
    unfold bornModeLaw
    rw [Finset.sum_comm]
    simpa only [partition] using hs
  have hlocal (S : Configuration G) :
      (if v ∈ S.val then (ρ S S).re else 0) =
        (if localMode G u v w S = 2 then (ρ S S).re else 0) ∧
      (if u ∈ S.val then (ρ S S).re else 0) =
        (if localMode G u v w S = 1 then (ρ S S).re else 0) +
        (if localMode G u v w S = 4 then (ρ S S).re else 0) ∧
      (if w ∈ S.val then (ρ S S).re else 0) =
        (if localMode G u v w S = 3 then (ρ S S).re else 0) +
        (if localMode G u v w S = 4 then (ρ S S).re else 0) ∧
      (if clear G v S then (ρ S S).re else 0) =
        (if localMode G u v w S = 0 then (ρ S S).re else 0) +
        (if localMode G u v w S = 2 then (ρ S S).re else 0) := by
    rw [local_blocking G u v w hN]
    by_cases hv : v ∈ S.val
    · obtain ⟨hu, hw⟩ := local_legality G u v w hN S hv
      simp [localMode, hv, hu, hw]
    · by_cases hu : u ∈ S.val <;> by_cases hw : w ∈ S.val <;>
        simp [localMode, hv, hu, hw]
  have hm : occupationMean G ρ v = bornModeLaw G u v w ρ 2 := by
    rw [occupationMean_sum]
    exact Finset.sum_congr rfl (fun S _ => (hlocal S).1)
  have hu : occupationMean G ρ u =
      bornModeLaw G u v w ρ 1 + bornModeLaw G u v w ρ 4 := by
    rw [occupationMean_sum]
    unfold bornModeLaw
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun S _ => (hlocal S).2.1)
  have hw : occupationMean G ρ w =
      bornModeLaw G u v w ρ 3 + bornModeLaw G u v w ρ 4 := by
    rw [occupationMean_sum]
    unfold bornModeLaw
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun S _ => (hlocal S).2.2.1)
  have hb : blockadeMean G ρ v =
      bornModeLaw G u v w ρ 0 + bornModeLaw G u v w ρ 2 := by
    rw [blockadeMean_sum]
    unfold bornModeLaw
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun S _ => (hlocal S).2.2.2)
  refine ⟨hp, htotal, ?_, ?_⟩
  · rw [Fin.sum_univ_five] at htotal
    funext k
    fin_cases k <;> simp <;> linarith
  · let empty : Configuration G := ⟨∅, by simp⟩
    let left : Configuration G := ⟨{u}, by simp [G.irrefl]⟩
    let right : Configuration G := ⟨{w}, by simp [G.irrefl]⟩
    let both : Configuration G := ⟨{u, w}, by
      intro a ha b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact G.irrefl
      · exact hind
      · exact fun h => hind h.symm
      · exact G.irrefl⟩
    let σ := (1 / 2 : ℝ) • (pureConfiguration G empty + pureConfiguration G both)
    let τ := (1 / 2 : ℝ) • (pureConfiguration G left + pureConfiguration G right)
    have hd (S T : Configuration G) :
        ((1 / 2 : ℝ) • (pureConfiguration G S + pureConfiguration G T)).PosSemidef ∧
        Matrix.trace ((1 / 2 : ℝ) • (pureConfiguration G S + pureConfiguration G T)) = 1 := by
      refine ⟨((pureConfiguration_density G S).1.add
        (pureConfiguration_density G T).1).smul (by norm_num), ?_⟩
      simp [Matrix.trace_smul, Matrix.trace_add, (pureConfiguration_density G S).2,
        (pureConfiguration_density G T).2]
      norm_num
    refine ⟨σ, τ, (hd empty both).1, (hd empty both).2,
      (hd left right).1, (hd left right).2, ?_, ?_⟩
    · intro x
      rw [(expectation_affine G _ _ x).1, (expectation_affine G _ _ x).1]
      simp only [pureConfiguration_occupation]
      by_cases hx : x = u <;> by_cases hw : x = w
      · exact (huw (hx.symm.trans hw)).elim
      · simp [empty, left, right, both, hx, hw, huw]
      · simp [empty, left, right, both, hx, hw, Ne.symm huw]
      · simp [empty, left, right, both, hx, hw]
    · have he : clear G v empty := by simp [clear, empty]
      have hleft : ¬ clear G v left := by
        intro h
        exact h u (by simp [left]) ((hN u).2 (Or.inl rfl))
      have hright : ¬ clear G v right := by
        intro h
        exact h w (by simp [right]) ((hN w).2 (Or.inr rfl))
      have hboth : ¬ clear G v both := by
        intro h
        exact h u (by simp [both]) ((hN u).2 (Or.inl rfl))
      change blockadeMean G ((1 / 2 : ℝ) • _) v ≠
        blockadeMean G ((1 / 2 : ℝ) • _) v
      rw [(expectation_affine G _ _ v).2, (expectation_affine G _ _ v).2]
      simp [pureConfiguration_blockade, he, hleft, hright, hboth]

/-- info: 'D5.S3.Quantum.Fibers.BipartiteBlockade.born_five_mode_reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms born_five_mode_reconstruction

end D5.S3.Quantum.Fibers.BipartiteBlockade
