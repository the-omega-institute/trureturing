/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickAttainment
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickAttainment
   mirror-E: none(waiver:finite-dimensional-attainment)
   anchors: []
   utility: none
   digest: Fixed-alphabet compact minimization of actual closed-perspective costs. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Semicontinuity.Basic

/-! The bounded-alphabet compactness architecture is due to Matsumoto,
`A new quantum version of f-divergence`, arXiv:1311.4722v4, Lemmas 4.1 and
9.2--9.3. Here the nonnegative curvature remainder retains both possibly
infinite endpoint costs. No priority claim is made for this architecture. -/

noncomputable section

universe u

open Matrix MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal ComplexOrder MatrixOrder Matrix.Norms.Elementwise
open D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest
open D5.S3.Quantum.Divergence.MaximalHockeyStickConvex
open D5.S3.Quantum.Divergence.MaximalHockeyStickL1Preparation

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickAttainment

variable {n : Type*} [Fintype n] [DecidableEq n] {f : ℝ → ℝ}

/-- Fatou applies to the actual nonnegative remainder, even on the axes and
at the origin; no finite endpoint assumption is needed. -/
theorem curvatureRemainder_lowerSemicontinuous (hf : ConvexOn ℝ (Ioi 0) f) :
    LowerSemicontinuous (fun z : ℝ × ℝ => curvatureRemainder hf z.1 z.2) := by
  have fatou {μ : Measure Positive} (g : (ℝ × ℝ) → Positive → ℝ≥0∞)
      (hm : ∀ z, Measurable (g z)) (hc : ∀ t, Continuous (fun z => g z t)) :
      LowerSemicontinuous (fun z => ∫⁻ t, g z t ∂μ) := by
    apply lowerSemicontinuous_iff_le_liminf.mpr
    intro z
    calc
      (∫⁻ t, g z t ∂μ) = ∫⁻ t, liminf (fun y => g y t) (𝓝 z) ∂μ := by
        apply lintegral_congr
        intro t
        exact (hc t).continuousAt.tendsto.liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le hm
  apply LowerSemicontinuous.add
  · apply fatou
    · intro z
      exact ((measurable_subtype_coe.mul_const z.2).sub_const z.1).ennreal_ofReal
    · intro t
      exact ENNReal.continuous_ofReal.comp
        ((continuous_const.mul continuous_snd).sub continuous_fst)
  · apply fatou
    · intro z
      exact (measurable_const.sub (measurable_subtype_coe.mul_const z.2)).ennreal_ofReal
    · intro t
      exact ENNReal.continuous_ofReal.comp
        (continuous_fst.sub (continuous_const.mul continuous_snd))

private theorem test_masses {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k) :
    (∑ i, R.p i = A.trace.re) ∧ (∑ i, R.q i = B.trace.re) := by
  have ht (i : Fin k) : (CStarMatrix.ofMatrix.symm (R.state i).1).trace = 1 :=
    (R.state i).2.2
  constructor
  · have h := congrArg (fun M : Matrix n n ℂ => M.trace.re) R.prepares_left
    simpa [Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum, ht, Complex.real_smul] using h
  · have h := congrArg (fun M : Matrix n n ℂ => M.trace.re) R.prepares_right
    simpa [Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum, ht, Complex.real_smul] using h

private theorem coe_real_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) :
    ((∑ i ∈ s, c i : ℝ) : EReal) = ∑ i ∈ s, (c i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, EReal.coe_add, ih]

private theorem coe_remainder_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0∞) :
    ((∑ i ∈ s, c i : ℝ≥0∞) : EReal) = ∑ i ∈ s, (c i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, EReal.coe_ennreal_add, ih]

/-- The affine part is fixed by the actual two outputs; the remaining objective
is nonnegative and permits infinite costs. -/
theorem finiteCost_eq_affine_remainder (hf : ConvexOn ℝ (Ioi 0) f)
    {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k) :
    finiteCost hf R = (affineMass f A B : EReal) +
      ((∑ i, curvatureRemainder hf (R.p i) (R.q i) : ℝ≥0∞) : EReal) := by
  unfold finiteCost
  simp_rw [closedPerspective_eq_affine_add_curvature hf (R.p_nonneg _) (R.q_nonneg _)]
  rw [Finset.sum_add_distrib]
  rw [← coe_real_sum, ← coe_remainder_sum]
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_sub_distrib, (test_masses R).1, (test_masses R).2]
  rfl

private theorem bounded_convex_representation {E α : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (F : α → E) {x : E} (hx : x ∈ convexHull ℝ (range F)) :
    ∃ (l : ℕ) (w : Fin l → ℝ) (a : Fin l → α),
      l ≤ Module.finrank ℝ E + 1 ∧ (∀ i, 0 ≤ w i) ∧
        ∑ i, w i = 1 ∧ ∑ i, w i • F (a i) = x := by
  classical
  let t := Caratheodory.minCardFinsetOfMemConvexHull hx
  have ht : (↑t : Set E) ⊆ range F :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  obtain ⟨w, hw, hw1, he⟩ := Finset.mem_convexHull'.mp
    (Caratheodory.mem_minCardFinsetOfMemConvexHull hx)
  have hc : Fintype.card t ≤ Module.finrank ℝ E + 1 :=
    (Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  choose a ha using (fun y : t => ht y.property)
  let e := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, fun i => w (e i), fun i => a (e i), hc,
    fun i => hw _ (e i).property, ?_, ?_⟩
  · exact (e.sum_comp (fun y : t => w y)).trans
      (by simpa only [Finset.univ_eq_attach, Finset.sum_attach] using hw1)
  · have hz : ∑ y : t, w y • F (a y) = x := by
      simp_rw [ha]
      change (∑ y ∈ t.attach, w (y : E) • (y : E)) = x
      rw [Finset.sum_attach t (fun y : E => w y • y)]
      exact he
    exact (e.sum_comp (fun y : t => w y • F (a y))).trans hz

/-- A uniform finite alphabet bound. Using the full complex matrix spaces avoids
any Hermitian affine-dimension calculation. -/
def alphabetBound (n : Type*) [Fintype n] : ℕ :=
  Module.finrank ℝ ((Matrix n n ℂ × Matrix n n ℂ) × ℝ) + 1

/-- Finite-cost compression preserves both actual outputs and the real cost.
The selected atoms are original density states. -/
theorem finite_cost_compression (hf : ConvexOn ℝ (Ioi 0) f)
    {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k)
    (hc : finiteCost hf R ≠ ⊤) :
    ∃ (l : ℕ) (S : ReverseTest A B l), l ≤ alphabetBound n ∧
      finiteCost hf S = finiteCost hf R := by
  classical
  by_cases hk : k = 0
  · subst k
    exact ⟨0, R, Nat.zero_le _, rfl⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hsum : (∑ i, curvatureRemainder hf (R.p i) (R.q i)) ≠ ∞ := by
    intro h
    apply hc
    rw [finiteCost_eq_affine_remainder, h]
    simp
  have hri (i : Fin k) : curvatureRemainder hf (R.p i) (R.q i) ≠ ∞ :=
    ne_top_of_le_ne_top hsum (Finset.single_le_sum
      (f := fun j => curvatureRemainder hf (R.p j) (R.q j))
      (fun _ _ => bot_le) (Finset.mem_univ i))
  let c : Fin k → ℝ := fun i =>
    f 1 * R.q i + rightDeriv f 1 * (R.p i - R.q i) +
      (curvatureRemainder hf (R.p i) (R.q i)).toReal
  have hce (i : Fin k) : closedPerspective hf (R.p i) (R.q i) = (c i : EReal) := by
    rw [closedPerspective_eq_affine_add_curvature hf (R.p_nonneg i) (R.q_nonneg i),
      ← EReal.coe_ennreal_toReal (hri i), ← EReal.coe_add]
  let F : Fin k → (Matrix n n ℂ × Matrix n n ℂ) × ℝ :=
    fun i => ((R.p i • R.stateMatrix i, R.q i • R.stateMatrix i), c i)
  let x := ∑ i, (1 / (k : ℝ)) • F i
  have hx : x ∈ convexHull ℝ (range F) := by
    apply mem_convexHull_of_exists_fintype (fun _ : Fin k => 1 / (k : ℝ)) F
      (fun _ => by positivity) ?_ (fun i => mem_range_self i) rfl
    simp [hkpos.ne']
  obtain ⟨l, w, a, hl, hw, hw1, he⟩ := bounded_convex_representation F hx
  have he' : ∑ i, ((k : ℝ) * w i) • F (a i) = ∑ i, F i := by
    rw [show (fun i => ((k : ℝ) * w i) • F (a i)) =
      (fun i => (k : ℝ) • (w i • F (a i))) by funext i; rw [mul_smul],
      ← Finset.smul_sum, he]
    dsimp [x]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, mul_one_div_cancel hkpos.ne', one_smul]
  have hp : ∑ i, ((k : ℝ) * w i * R.p (a i)) • R.stateMatrix (a i) = A := by
    have h := congrArg (fun z : (Matrix n n ℂ × Matrix n n ℂ) × ℝ => z.1.1) he'
    simpa only [F, Prod.fst_sum, Prod.smul_fst, mul_smul,
      ReverseTest.stateMatrix, R.prepares_left] using h
  have hq : ∑ i, ((k : ℝ) * w i * R.q (a i)) • R.stateMatrix (a i) = B := by
    have h := congrArg (fun z : (Matrix n n ℂ × Matrix n n ℂ) × ℝ => z.1.2) he'
    simpa only [F, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, mul_smul,
      ReverseTest.stateMatrix, R.prepares_right] using h
  let S : ReverseTest A B l :=
    { p := fun i => (k : ℝ) * w i * R.p (a i)
      q := fun i => (k : ℝ) * w i * R.q (a i)
      p_nonneg := fun i => mul_nonneg (mul_nonneg hkpos.le (hw i)) (R.p_nonneg _)
      q_nonneg := fun i => mul_nonneg (mul_nonneg hkpos.le (hw i)) (R.q_nonneg _)
      state := fun i => R.state (a i)
      prepares_left := hp
      prepares_right := hq }
  refine ⟨l, S, hl, ?_⟩
  have hreal : ∑ i, (k : ℝ) * w i * c (a i) = ∑ i, c i := by
    simpa only [F, Prod.snd_sum, Prod.smul_snd, smul_eq_mul] using
      congrArg (fun z : (Matrix n n ℂ × Matrix n n ℂ) × ℝ => z.2) he'
  change (∑ i, closedPerspective hf ((k : ℝ) * w i * R.p (a i))
    ((k : ℝ) * w i * R.q (a i))) = ∑ i, closedPerspective hf (R.p i) (R.q i)
  simp_rw [closedPerspective_homogeneous hf _ _ _ (mul_nonneg hkpos.le (hw _)), hce,
    ← EReal.coe_mul]
  rw [← coe_real_sum, ← coe_real_sum]
  exact_mod_cast hreal

private def densitySet (n : Type*) [Fintype n] : Set (Matrix n n ℂ) :=
  {τ | τ.PosSemidef ∧ τ.trace = 1}

private theorem density_nonempty [Nonempty n] : (densitySet n).Nonempty := by
  classical
  let i := Classical.choice (inferInstance : Nonempty n)
  refine ⟨diagonal (Pi.single i 1), ?_, ?_⟩
  · apply posSemidef_diagonal_iff.mpr
    intro j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · simp [Matrix.trace_diagonal]

private theorem density_compact [Nonempty n] : IsCompact (densitySet n) := by
  obtain ⟨τ, hτ⟩ := density_nonempty (n := n)
  have h := D5.S3.Quantum.Fibers.PhysicalFiber.finite_dimensional_physical_fiber
    (0 : Matrix n n ℂ →ₗ[ℂ] (Empty → ℂ)) τ hτ.1 hτ.2
  simpa [D5.S3.Quantum.Fibers.PhysicalFiber.physicalFiber, densitySet] using h.2.1

private abbrev TestData (n : Type*) (k : ℕ) :=
  (Fin k → ℝ) × (Fin k → ℝ) × (Fin k → Matrix n n ℂ)

private def feasible (A B : Matrix n n ℂ) (k : ℕ) : Set (TestData n k) :=
  ((univ.pi (fun _ : Fin k => Icc 0 A.trace.re)) ×ˢ
    ((univ.pi (fun _ : Fin k => Icc 0 B.trace.re)) ×ˢ
      (univ.pi (fun _ : Fin k => densitySet n)))) ∩
  {z | (∑ i, z.1 i • z.2.2 i) = A ∧ (∑ i, z.2.1 i • z.2.2 i) = B}

private theorem feasible_compact [Nonempty n] (A B : Matrix n n ℂ) (k : ℕ) :
    IsCompact (feasible A B k) := by
  have hp : IsCompact (univ.pi (fun _ : Fin k => Icc 0 A.trace.re)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hq : IsCompact (univ.pi (fun _ : Fin k => Icc 0 B.trace.re)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hτ : IsCompact (univ.pi (fun _ : Fin k => densitySet n)) :=
    isCompact_univ_pi (fun _ => density_compact)
  have hleft : Continuous (fun z : TestData n k => ∑ i, z.1 i • z.2.2 i) := by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp continuous_fst).smul
      ((continuous_apply i).comp (continuous_snd.comp continuous_snd))
  have hright : Continuous (fun z : TestData n k => ∑ i, z.2.1 i • z.2.2 i) := by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp (continuous_fst.comp continuous_snd)).smul
      ((continuous_apply i).comp (continuous_snd.comp continuous_snd))
  exact (hp.prod (hq.prod hτ)).inter_right
    ((isClosed_eq hleft continuous_const).inter (isClosed_eq hright continuous_const))

private def dataRemainder (hf : ConvexOn ℝ (Ioi 0) f) {k : ℕ}
    (z : TestData n k) : ℝ≥0∞ :=
  ∑ i, curvatureRemainder hf (z.1 i) (z.2.1 i)

private theorem dataRemainder_lsc (hf : ConvexOn ℝ (Ioi 0) f) (k : ℕ) :
    LowerSemicontinuous (dataRemainder (n := n) hf (k := k)) := by
  change LowerSemicontinuous (fun z : TestData n k =>
    ∑ i, curvatureRemainder hf (z.1 i) (z.2.1 i))
  apply lowerSemicontinuous_sum
  intro i _
  have hg : Continuous (fun z : TestData n k => (z.1 i, z.2.1 i)) :=
    (((continuous_apply i).comp continuous_fst).prodMk
      ((continuous_apply i).comp (continuous_fst.comp continuous_snd)))
  exact (curvatureRemainder_lowerSemicontinuous hf).comp hg

private def dataTest {A B : Matrix n n ℂ} {k : ℕ} (z : TestData n k)
    (hz : z ∈ feasible A B k) : ReverseTest A B k where
  p := z.1
  q := z.2.1
  p_nonneg := fun i => (hz.1.1 i (mem_univ i)).1
  q_nonneg := fun i => (hz.1.2.1 i (mem_univ i)).1
  state := fun i => ⟨CStarMatrix.ofMatrix (z.2.2 i),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (hz.1.2.2 i (mem_univ i)).1.nonneg,
    (hz.1.2.2 i (mem_univ i)).2⟩
  prepares_left := by simpa only [Equiv.symm_apply_apply] using hz.2.1
  prepares_right := by simpa only [Equiv.symm_apply_apply] using hz.2.2

private theorem test_feasible {A B : Matrix n n ℂ} {k : ℕ} (S : ReverseTest A B k) :
    (⟨S.p, S.q, S.stateMatrix⟩ : TestData n k) ∈ feasible A B k := by
    refine ⟨⟨?_, ?_, ?_⟩, S.prepares_left, S.prepares_right⟩
    · intro i _
      refine ⟨S.p_nonneg i, ?_⟩
      rw [← (test_masses S).1]
      exact Finset.single_le_sum (fun j _ => S.p_nonneg j) (Finset.mem_univ i)
    · intro i _
      refine ⟨S.q_nonneg i, ?_⟩
      rw [← (test_masses S).2]
      exact Finset.single_le_sum (fun j _ => S.q_nonneg j) (Finset.mem_univ i)
    · intro i _
      exact ⟨(map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (S.state i).2.1).posSemidef,
        (S.state i).2.2⟩

/-- On each fixed nonempty feasible alphabet the actual nonnegative objective
has a minimizer, reconstructing an actual repository reverse test. -/
theorem fixed_alphabet_minimum [Nonempty n] (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (k : ℕ) (hne : (feasible A B k).Nonempty) :
    ∃ R : ReverseTest A B k, ∀ S : ReverseTest A B k,
      finiteCost hf R ≤ finiteCost hf S := by
  obtain ⟨z, hz, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne
    (feasible_compact A B k) ((dataRemainder_lsc (n := n) hf k).lowerSemicontinuousOn _)
  refine ⟨dataTest z hz, ?_⟩
  intro S
  rw [finiteCost_eq_affine_remainder, finiteCost_eq_affine_remainder]
  apply add_le_add le_rfl
  apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
  exact hmin (test_feasible S)

private def padTest {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k)
    (l : ℕ) (τ : DensityState n) : ReverseTest A B (k + l) where
  p := Fin.addCases R.p (fun _ => 0)
  q := Fin.addCases R.q (fun _ => 0)
  p_nonneg := Fin.addCases (fun i => by simpa only [Fin.addCases_left] using R.p_nonneg i)
    (fun i => by simp only [Fin.addCases_right, le_refl])
  q_nonneg := Fin.addCases (fun i => by simpa only [Fin.addCases_left] using R.q_nonneg i)
    (fun i => by simp only [Fin.addCases_right, le_refl])
  state := Fin.addCases R.state (fun _ => τ)
  prepares_left := by
    simpa only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      zero_smul, Finset.sum_const_zero, add_zero] using R.prepares_left
  prepares_right := by
    simpa only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      zero_smul, Finset.sum_const_zero, add_zero] using R.prepares_right

private theorem padTest_cost (hf : ConvexOn ℝ (Ioi 0) f)
    {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k) (l : ℕ) (τ : DensityState n) :
    finiteCost hf (padTest R l τ) = finiteCost hf R := by
  simp [finiteCost, padTest, Fin.sum_univ_add, closedPerspective_origin]

private theorem pad_to_bound [Nonempty n] (hf : ConvexOn ℝ (Ioi 0) f)
    {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k) (hk : k ≤ alphabetBound n) :
    ∃ S : ReverseTest A B (alphabetBound n), finiteCost hf S = finiteCost hf R := by
  obtain ⟨τ, hτ⟩ := density_nonempty (n := n)
  let ρ : DensityState n := ⟨CStarMatrix.ofMatrix τ,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hτ.1.nonneg, hτ.2⟩
  have hlen : k + (alphabetBound n - k) = alphabetBound n := Nat.add_sub_of_le hk
  have h := padTest_cost hf R (alphabetBound n - k) ρ
  exact hlen ▸ ⟨padTest R (alphabetBound n - k) ρ, h⟩

/-- The bounded-alphabet minimum is the infimum over every finite alphabet.
Infinite-cost competitors are included in the comparison. -/
theorem finite_attainment_nonempty [Nonempty n] (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (c : ℝ) (hc : maximalValue hf A B = (c : EReal)) :
    ∃ R : ReverseTest A B (alphabetBound n), finiteCost hf R = (c : EReal) := by
  have hlt : maximalValue hf A B < ((c + 1 : ℝ) : EReal) := by
    rw [hc, EReal.coe_lt_coe_iff]
    linarith
  obtain ⟨_, ⟨k, S, rfl⟩, hS⟩ := sInf_lt_iff.mp hlt
  obtain ⟨l, U, hl, hU⟩ := finite_cost_compression hf S (ne_top_of_lt hS)
  obtain ⟨V, hV⟩ := pad_to_bound hf U hl
  obtain ⟨R, hR⟩ := fixed_alphabet_minimum hf A B (alphabetBound n) ⟨_, test_feasible V⟩
  refine ⟨R, le_antisymm ?_ ?_⟩
  · rw [← hc]
    apply le_sInf
    rintro _ ⟨j, W, rfl⟩
    by_cases hW : finiteCost hf W = ⊤
    · rw [hW]
      exact le_top
    · obtain ⟨l, X, hl, hX⟩ := finite_cost_compression hf W hW
      obtain ⟨Y, hY⟩ := pad_to_bound hf X hl
      exact (hR Y).trans_eq (hY.trans hX)
  · rw [← hc]
    exact sInf_le ⟨alphabetBound n, R, rfl⟩

private def emptyTest : ReverseTest (0 : Matrix n n ℂ) 0 0 where
  p := Fin.elim0
  q := Fin.elim0
  p_nonneg := fun i => Fin.elim0 i
  q_nonneg := fun i => Fin.elim0 i
  state := Fin.elim0
  prepares_left := by simp
  prepares_right := by simp

private theorem zero_pair_value (hf : ConvexOn ℝ (Ioi 0) f) :
    maximalValue hf (0 : Matrix n n ℂ) 0 = 0 := by
  apply le_antisymm
  · exact sInf_le ⟨0, emptyTest, by simp [finiteCost]⟩
  · apply le_sInf
    rintro _ ⟨k, S, rfl⟩
    have hp (i : Fin k) : S.p i = 0 := by
      apply le_antisymm _ (S.p_nonneg i)
      have h := Finset.single_le_sum (fun j _ => S.p_nonneg j) (Finset.mem_univ i)
      simpa only [(test_masses S).1, Matrix.trace_zero, Complex.zero_re] using h
    have hq (i : Fin k) : S.q i = 0 := by
      apply le_antisymm _ (S.q_nonneg i)
      have h := Finset.single_le_sum (fun j _ => S.q_nonneg j) (Finset.mem_univ i)
      simpa only [(test_masses S).2, Matrix.trace_zero, Complex.zero_re] using h
    simp [finiteCost, hp, hq, closedPerspective_origin]

/-- A real finite original whole-complex-L1 value is attained by an actual finite
reverse test. The empty output type, zero pairs and arbitrary traces are included. -/
theorem original_finite_attainment (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (c : ℝ)
    (hc : MaximalHockeyStickAllL1Convex.originalL1Value.{u} hf A B = (c : EReal)) :
    ∃ (k : ℕ) (R : ReverseTest A B k), finiteCost hf R = (c : EReal) := by
  have hm : maximalValue hf A B = (c : EReal) := by
    rw [MaximalHockeyStickAllL1Convex.originalL1Value,
      MaximalHockeyStickL1ReverseTest.sigma_finite_source_infimum_eq.{u}] at hc
    exact hc
  by_cases hT : (A + B).trace.re = 0
  · have htr : A.trace.re + B.trace.re = 0 := by
      simpa only [Matrix.trace_add, Complex.add_re] using hT
    have hta : A.trace.re = 0 := by
      have ha := (Complex.nonneg_iff.mp hA.trace_nonneg).1
      have hb := (Complex.nonneg_iff.mp hB.trace_nonneg).1
      linarith
    have htb : B.trace.re = 0 := by linarith
    have hA0 : A = 0 := hA.trace_eq_zero_iff.mp (by
      rw [Complex.eq_re_of_ofReal_le hA.trace_nonneg, hta]
      rfl)
    have hB0 : B = 0 := hB.trace_eq_zero_iff.mp (by
      rw [Complex.eq_re_of_ofReal_le hB.trace_nonneg, htb]
      rfl)
    subst A
    subst B
    exact ⟨0, emptyTest, (by simp [finiteCost] : finiteCost hf emptyTest = 0).trans
      ((zero_pair_value hf).symm.trans hm)⟩
  cases isEmpty_or_nonempty n with
  | inr hn =>
    obtain ⟨R, hR⟩ := finite_attainment_nonempty hf A B c hm
    exact ⟨alphabetBound n, R, hR⟩
  | inl hn =>
    exact (hT (by simp [Matrix.trace])).elim

#print axioms curvatureRemainder_lowerSemicontinuous
#print axioms finiteCost_eq_affine_remainder
#print axioms finite_cost_compression
#print axioms fixed_alphabet_minimum
#print axioms finite_attainment_nonempty
#print axioms original_finite_attainment

end D5.S3.Quantum.Divergence.MaximalHockeyStickAttainment
