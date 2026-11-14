/- GID: D5/S3/Geometry/ProbabilityTransport/HalfRangePotentials
   generality: G
   mirror-B: D5/B/S3/Geometry/ProbabilityTransport/HalfRangePotentials
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary supported feasible potentials admit jointly feasible half-range Lipschitz majorants. -/

import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

/-!
# Half-range regularization of rectangular-cost potentials

The classical c-transform construction applies to arbitrary nonempty supports,
without regularity of the original potentials. The two spaces have independent
universes and carry only pseudometrics. Classical c-transforms are discussed in
arXiv:1803.00567v4, section 5.1; no novelty claim is made here.
-/

namespace HalfRangePotentials

open scoped NNReal

universe u v w

/-- Uniform comparison passes to real infima without an attained minimum. -/
private lemma infimum_le_add {I : Type w} [Nonempty I] (f g : I → ℝ)
    (hf : BddBelow (Set.range f)) (d : ℝ) (h : ∀ i, f i ≤ g i + d) :
    (⨅ i, f i) ≤ (⨅ i, g i) + d := by
  have hb : (⨅ i, f i) - d ≤ ⨅ i, g i := le_ciInf fun i => by
    have hi := ciInf_le hf i
    linarith [h i]
  linarith

/-- A pointwise Lipschitz family with bounded-below fibers has a Lipschitz infimum. -/
private lemma lipschitz_infimum {A : Type u} {I : Type w}
    [PseudoMetricSpace A] [Nonempty I] (L : ℝ≥0) (f : A → I → ℝ)
    (hb : ∀ x, BddBelow (Set.range (f x)))
    (hf : ∀ i, LipschitzWith L (fun x => f x i)) :
    LipschitzWith L (fun x => ⨅ i, f x i) := by
  apply LipschitzWith.of_le_add_mul L
  intro x z
  exact infimum_le_add (f x) (f z) (hb x) _ (fun i => (hf i).le_add_mul x z)

/-- Every feasible pair on arbitrary nonempty supports has globally feasible
exact-L Lipschitz majorants after one common shift, both in the half-range. -/
theorem exists_half_range_majorants
    {X : Type u} {Y : Type v} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (M : ℝ) (L : ℝ≥0) (c : X × Y → ℝ)
    (hc : ∀ z, 0 ≤ c z ∧ c z ≤ M) (hcL : LipschitzWith L c)
    (K : Set X) (H : Set Y) (hK : K.Nonempty) (hH : H.Nonempty)
    (φ : K → ℝ) (ψ : H → ℝ)
    (hfeas : ∀ k : K, ∀ h : H, φ k + ψ h ≤ c (k.val, h.val)) :
    ∃ (a : ℝ) (F : X → ℝ) (G : Y → ℝ),
      LipschitzWith L F ∧ LipschitzWith L G ∧
      (∀ x, -M / 2 ≤ F x ∧ F x ≤ M / 2) ∧
      (∀ y, -M / 2 ≤ G y ∧ G y ≤ M / 2) ∧
      (∀ x y, F x + G y ≤ c (x, y)) ∧
      (∀ k : K, φ k + a ≤ F k.val) ∧
      (∀ h : H, ψ h - a ≤ G h.val) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hK
  obtain ⟨y₀, hy₀⟩ := hH
  let k₀ : K := ⟨x₀, hx₀⟩
  let h₀ : H := ⟨y₀, hy₀⟩
  have : Nonempty X := ⟨x₀⟩
  have : Nonempty H := ⟨h₀⟩
  have hM : 0 ≤ M := (hc (x₀, y₀)).1.trans (hc (x₀, y₀)).2
  let r : X → H → ℝ := fun x h => c (x, h.val) - ψ h
  have rb (x : X) : BddBelow (Set.range (r x)) := by
    refine ⟨φ k₀ - M, ?_⟩
    rintro _ ⟨h, rfl⟩
    dsimp [r]
    have hh := hfeas k₀ h
    have hupper := (hc (x₀, h.val)).2
    have hlower := (hc (x, h.val)).1
    change φ k₀ + ψ h ≤ c (x₀, h.val) at hh
    linarith
  let f : X → ℝ := fun x => ⨅ h, r x h
  have f_le (x : X) (h : H) : f x ≤ c (x, h.val) - ψ h :=
    ciInf_le (rb x) h
  have f_dom (k : K) : φ k ≤ f k.val := by
    apply le_ciInf
    intro h
    dsimp [r]
    linarith [hfeas k h]
  have f_osc (x z : X) : f x ≤ f z + M := by
    apply infimum_le_add (r x) (r z) (rb x) M
    intro h
    dsimp [r]
    linarith [(hc (x, h.val)).2, (hc (z, h.val)).1]
  have fL : LipschitzWith L f := by
    apply lipschitz_infimum L r rb
    intro h
    apply LipschitzWith.of_le_add_mul L
    intro x z
    have hh := hcL.le_add_mul (x, h.val) (z, h.val)
    rw [dist_prod_same_right] at hh
    dsimp [r]
    linarith
  have fb : BddAbove (Set.range f) := by
    refine ⟨M - ψ h₀, ?_⟩
    rintro _ ⟨x, rfl⟩
    linarith [f_le x h₀, (hc (x, h₀.val)).2]
  let b : ℝ := ⨆ x, f x
  have f_upper (x : X) : f x ≤ b := le_ciSup fb x
  have f_lower (x : X) : b - M ≤ f x := by
    have hh : b ≤ f x + M := ciSup_le fun z => f_osc z x
    linarith
  have b_support (h : H) : b ≤ M - ψ h := by
    apply ciSup_le
    intro x
    linarith [f_le x h, (hc (x, h.val)).2]
  let a : ℝ := -b + M / 2
  let F : X → ℝ := fun x => f x + a
  have Fb (x : X) : -M / 2 ≤ F x ∧ F x ≤ M / 2 := by
    dsimp [F, a]
    constructor <;> linarith [f_upper x, f_lower x]
  have FL : LipschitzWith L F := by
    apply LipschitzWith.of_le_add_mul L
    intro x z
    dsimp [F]
    linarith [fL.le_add_mul x z]
  let s : Y → X → ℝ := fun y x => c (x, y) - F x
  have sb (y : Y) : BddBelow (Set.range (s y)) := by
    refine ⟨-M / 2, ?_⟩
    rintro _ ⟨x, rfl⟩
    dsimp [s]
    linarith [(Fb x).2, (hc (x, y)).1]
  let g : Y → ℝ := fun y => ⨅ x, s y x
  have gL : LipschitzWith L g := by
    apply lipschitz_infimum L s sb
    intro x
    apply LipschitzWith.of_le_add_mul L
    intro y z
    have hh := hcL.le_add_mul (x, y) (x, z)
    rw [dist_prod_same_left] at hh
    dsimp [s]
    linarith
  have g_lower (y : Y) : -M / 2 ≤ g y := by
    apply le_ciInf
    intro x
    dsimp [s]
    linarith [(Fb x).2, (hc (x, y)).1]
  have g_dom (h : H) : ψ h - a ≤ g h.val := by
    apply le_ciInf
    intro x
    have hh := f_le x h
    dsimp [s, F]
    linarith
  let G : Y → ℝ := fun y => min (g y) (M / 2)
  refine ⟨a, F, G, FL, gL.min_const _, Fb, ?_, ?_, ?_, ?_⟩
  · intro y
    exact ⟨le_min (g_lower y) (by linarith), min_le_right _ _⟩
  · intro x y
    have hh : g y ≤ c (x, y) - F x := ciInf_le (sb y) x
    have hG : G y ≤ g y := min_le_left _ _
    linarith
  · intro k
    dsimp [F]
    linarith [f_dom k]
  · intro h
    apply le_min (g_dom h)
    dsimp [a]
    linarith [b_support h]

end HalfRangePotentials
