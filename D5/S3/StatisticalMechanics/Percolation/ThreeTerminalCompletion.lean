/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCompletion
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Graph determinant bounds control independent completion errors. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness

/-! Boundary-inclusive independent completion of actual five-mode graph laws. -/

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCompletion
open ThreeTerminalBond ThreeTerminalTree ThreeTerminalCactusSharpness
open scoped BigOperators

noncomputable section

/-- The independent base completion preserves X=p(ab)+p(all), Y=p(bc)+p(all)
and Z=p(ac). Its all-connected mass is XY/(1-Z). -/
def completion (p : Mode → ℝ) (s : Mode) : ℝ :=
  let X := p .ab+p .all
  let Y := p .bc+p .all
  let Z := p .ac
  let q := X*Y/(1-Z)
  match s with
  | .separate => 1-Z-X-Y+q
  | .ab => X-q
  | .bc => Y-q
  | .all => q
  | .ac => Z

/-- The observable's interaction across the four base corners. -/
def interaction (f : Mode → ℝ) : ℝ := f .separate-f .ab-f .bc+f .all

private lemma mode_sum (g : Mode → ℝ) :
    ∑ s, g s = g .separate+g .ab+g .bc+g .all+g .ac := by
  have h : (Finset.univ : Finset Mode) = {.separate,.ab,.bc,.all,.ac} := by decide
  rw [h]
  simp <;> ring

private lemma completion_error (p : Mode → ℝ) (hn : ∑ s, p s = 1)
    (hZ : p .ac < 1) :
    p .all-(p .ab+p .all)*(p .bc+p .all)/(1-p .ac) = delta p/(1-p .ac) := by
  rw [mode_sum] at hn
  have h0 : p .separate = 1-p .ab-p .bc-p .all-p .ac := by linarith
  unfold delta
  rw [h0]
  have hd : 1-p .ac ≠ 0 := ne_of_gt (sub_pos.mpr hZ)
  field_simp [hd]
  <;> ring

private lemma observable_error (p f : Mode → ℝ) (hn : ∑ s, p s = 1) :
    (∑ s, f s*p s)-(∑ s, f s*completion p s) =
      interaction f*(p .all-(p .ab+p .all)*(p .bc+p .all)/(1-p .ac)) := by
  rw [mode_sum] at hn
  rw [mode_sum,mode_sum]
  have h0 : p .separate = 1-p .ab-p .bc-p .all-p .ac := by linarith
  simp only [completion,interaction]
  rw [h0]
  ring

private lemma complete_of_zero (p : Mode → ℝ) (hn : ∑ s, p s = 1)
    (hZ : p .ac = 0) (hD : delta p = 0) : p = completion p := by
  have he := completion_error p hn (by linarith)
  rw [hD,zero_div] at he
  rw [mode_sum] at hn
  funext s
  cases s <;> simp only [completion] <;> linarith

private lemma vertex_of_one (p : Mode → ℝ) (hn : ∑ s, p s = 1)
    (hp : ∀ s, 0 ≤ p s) (hZ : p .ac = 1) :
    p = fun s => if s = .ac then 1 else 0 := by
  rw [mode_sum] at hn
  have h0 := hp .separate
  have h1 := hp .ab
  have h2 := hp .bc
  have h3 := hp .all
  funext s
  cases s <;> simp <;> linarith

private lemma pyramid_of_bound (p : Mode → ℝ) (C : ℝ) (hn : ∑ s, p s = 1)
    (hp : ∀ s, 0 ≤ p s) (hD : 0 ≤ delta p ∧ delta p ≤ C*p .ac) :
    (p .ac < 1 →
      |p .all-(p .ab+p .all)*(p .bc+p .all)/(1-p .ac)| ≤ C*p .ac/(1-p .ac) ∧
      ∀ f : Mode → ℝ,
        |(∑ s, f s*p s)-(∑ s, f s*completion p s)| ≤
          |interaction f| *(C*p .ac/(1-p .ac))) ∧
    (p .ac = 0 → p = completion p) ∧
    (p .ac = 1 → p = fun s => if s = .ac then 1 else 0) := by
  refine ⟨?_,?_,vertex_of_one p hn hp⟩
  · intro hZ
    have hd : 0 < 1-p .ac := sub_pos.mpr hZ
    have hb : |p .all-(p .ab+p .all)*(p .bc+p .all)/(1-p .ac)| ≤
        C*p .ac/(1-p .ac) := by
      rw [completion_error p hn hZ,abs_div,abs_of_pos hd,abs_of_nonneg hD.1]
      exact div_le_div_of_nonneg_right hD.2 hd.le
    refine ⟨hb,?_⟩
    intro f
    rw [observable_error p f hn,abs_mul]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  · intro hZ
    apply complete_of_zero p hn hZ
    have := hD.2
    rw [hZ,mul_zero] at this
    linarith [hD.1]

private lemma bond_probability {V : Type*} {G : SimpleGraph V} [Fintype G.edgeSet]
    (a b c : V) (θ : G.edgeSet → ℝ) (hθ : ∀ e, θ e ∈ Set.Icc 0 1) :
    (∑ s, bondLaw G a b c θ s = 1) ∧ ∀ s, 0 ≤ bondLaw G a b c θ s := by
  classical
  constructor
  · exact bondLaw_sum a b c θ
  · intro s
    unfold bondLaw
    apply Finset.sum_nonneg
    intro ω _
    split_ifs
    · apply Finset.prod_nonneg
      intro e _
      split_ifs
      · exact (hθ e).1
      · exact sub_nonneg.mpr (hθ e).2
    · exact le_rfl

/-- Tree structure controls hidden mass, every observable and both pyramid boundaries. -/
theorem tree_pyramid {V : Type*} {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : G.IsTree) (a b c : V) (θ : G.edgeSet → ℝ)
    (hθ : ∀ e, θ e ∈ Set.Icc 0 1) :
    let p := bondLaw G a b c θ
    (p .ac < 1 →
      |p .all-(p .ab+p .all)*(p .bc+p .all)/(1-p .ac)| ≤ p .ac/(1-p .ac) ∧
      ∀ f : Mode → ℝ,
        |(∑ s, f s*p s)-(∑ s, f s*completion p s)| ≤
          |interaction f| *(p .ac/(1-p .ac))) ∧
    (p .ac = 0 → p = completion p) ∧
    (p .ac = 1 → p = fun s => if s = .ac then 1 else 0) := by
  obtain ⟨hn,hp⟩ := bond_probability a b c θ hθ
  simpa only [one_mul] using
    pyramid_of_bound (bondLaw G a b c θ) 1 hn hp (by simpa using tree_bound hG a b c θ hθ)

/-- The same error modulus, with constant two, for the entire four-edge cactus family. -/
theorem pendant_pyramid (u v s A : ℝ) (hu : u ∈ Set.Icc 0 1)
    (hv : v ∈ Set.Icc 0 1) (hs : s ∈ Set.Icc 0 1) (hA : A ∈ Set.Icc 0 1) :
    let p := law pendantEnds 0 1 2 ![u,v,s,A]
    (p .ac < 1 →
      |p .all-(p .ab+p .all)*(p .bc+p .all)/(1-p .ac)| ≤ 2*p .ac/(1-p .ac) ∧
      ∀ f : Mode → ℝ,
        |(∑ mode, f mode*p mode)-(∑ mode, f mode*completion p mode)| ≤
          |interaction f| *(2*p .ac/(1-p .ac))) ∧
    (p .ac = 0 → p = completion p) ∧
    (p .ac = 1 → p = fun mode => if mode = .ac then 1 else 0) := by
  have hn : ∑ mode, law pendantEnds 0 1 2 ![u,v,s,A] mode = 1 := by
    unfold law
    rw [Finset.sum_comm]
    simpa using weight_sum (![u,v,s,A] : Fin 4 → ℝ)
  have hθ (e : Fin 4) : (![u,v,s,A] : Fin 4 → ℝ) e ∈ Set.Icc 0 1 := by
    fin_cases e
    · simpa using hu
    · simpa using hv
    · simpa using hs
    · simpa using hA
  have hp mode : 0 ≤ law pendantEnds 0 1 2 ![u,v,s,A] mode := by
    unfold law
    apply Finset.sum_nonneg
    intro ω _
    split_ifs
    · apply Finset.prod_nonneg
      intro e _
      split_ifs
      · exact (hθ e).1
      · exact sub_nonneg.mpr (hθ e).2
    · exact le_rfl
  exact pyramid_of_bound _ 2 hn hp (pendant_bound u v s A hu hv hs hA)

end

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCompletion.tree_pyramid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tree_pyramid
/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCompletion.pendant_pyramid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pendant_pyramid

end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCompletion
