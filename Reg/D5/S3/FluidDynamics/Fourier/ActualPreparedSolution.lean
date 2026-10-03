import Reg.Support.DependentFamily
import D5.S3.FluidDynamics.Fourier.ActualPreparedSolution

open scoped ENNReal NNReal BigOperators
open Set MeasureTheory
open D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.FluidDynamics.Fourier.ActualPreparedSolution

structure Params where
  ν : ℝ
  A : ℝ
  B : ℝ
  α : ℝ
  β : ℝ

abbrev H := lp (fun _ : ℤ × ℤ => EuclideanSpace ℂ (Fin 2)) 2

def admissible (p : Params) : Prop :=
  0 < p.ν ∧ 0 < p.A ∧ 0 ≤ p.B ∧ |p.α| ≤ p.A ∧ |p.β| ≤ p.B

def candidatePredicate (p : Params) (x : (ℝ → H) × (ℝ → H)) : Prop :=
    let ν := p.ν
    let A := p.A
    let B := p.B
    let α := p.α
    let β := p.β
    let K := ℤ × ℤ
    let V := EuclideanSpace ℂ (Fin 2)
    let TV := EuclideanSpace ℂ (Fin 2 × Fin 2)
    let H := lp (fun _ : K => V) 2
    let ρ : K → ℝ := fun k => (k.1 : ℝ)^2 + (k.2 : ℝ)^2
    let κ : K → V := fun k => WithLp.toLp 2 (fun i => (![k.1, k.2] i : ℂ))
    let P := fun k => (ℂ ∙ κ k)ᗮ.starProjection
    let R := 2 * Real.sqrt (2*A^2 + 9*B^2)
    let τ := ν / (16384 * R^2)
    let a : V := WithLp.toLp 2 ![0, (α : ℂ)]
    let b : V := WithLp.toLp 2 ![(3*β/2 : ℂ), (3*β/2 : ℂ)]
    let X0 : H := lp.single 2 (1,0) a + lp.single 2 (-1,0) a +
      lp.single 2 (-1,1) b + lp.single 2 (1,-1) b
    let u : ℝ → H := x.1
    let D : ℝ → H := x.2
    ContinuousOn u (Icc 0 τ) ∧ u 0 = X0 ∧
      (∀ t ∈ Icc 0 τ, ‖u t‖ ≤ R) ∧
      (∀ t ∈ Icc 0 τ, u t 0 = 0 ∧
        (∀ k i, u t (-k) i = star (u t k i)) ∧ (∀ k, P k (u t k) = u t k)) ∧
      (∀ v : ℝ → H, ContinuousOn v (Icc 0 τ) →
        (∀ t ∈ Icc 0 τ, ∀ k,
          v t k = Real.exp (-ν*t*ρ k) • X0 k - ∫ s in (0:ℝ)..t, Real.exp (-ν*(t-s)*ρ k) •
            (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
              ∑ j : Fin 2, κ k j * (weight k • convolution
                (fun l => (weight l)⁻¹ • v s l)
                (fun l => (weight l)⁻¹ • v s l) k) (i,j))))) →
        ∀ t ∈ Icc 0 τ, v t = u t) ∧
      (∀ (β₂ : ℝ) (v : ℝ → H), ContinuousOn v (Icc 0 τ) →
        (∀ t ∈ Icc 0 τ, ‖v t‖ ≤ R) →
        let b₂ : V := WithLp.toLp 2 ![(3*β₂/2 : ℂ),(3*β₂/2 : ℂ)]
        let X₂ : H := lp.single (E := fun _ : K => V) 2 (1,0) a +
          lp.single (E := fun _ : K => V) 2 (-1,0) a +
          lp.single (E := fun _ : K => V) 2 (-1,1) b₂ +
          lp.single (E := fun _ : K => V) 2 (1,-1) b₂
        (∀ t ∈ Icc 0 τ, ∀ k,
          v t k = Real.exp (-ν*t*ρ k) • X₂ k - ∫ s in (0:ℝ)..t, Real.exp (-ν*(t-s)*ρ k) •
            (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
              ∑ j : Fin 2, κ k j * (weight k • convolution
                (fun l => (weight l)⁻¹ • v s l)
                (fun l => (weight l)⁻¹ • v s l) k) (i,j))))) →
        ∀ t ∈ Icc 0 τ, ‖u t-v t‖ ≤ 6*|β-β₂|) ∧
      (∀ x y : ℝ, ∀ i : Fin 2,
        (∑' k : K, ((((weight k)⁻¹:ℝ):ℂ) * X0 k i) *
          D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis.character k x y) =
        (D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis.realVelocity α β x y i.castSucc : ℂ)) ∧
      Continuous D ∧ D 0 = 0 ∧
        (∀ t ∈ Icc 0 τ, ‖D t‖ ≤ R/4) ∧
        (∀ t ∈ Icc 0 τ, ∀ k,
          u t k = Real.exp (-ν*t*ρ k) • X0 k - D t k) ∧
        (∀ t ∈ Icc 0 τ, ∀ k,
          D t k = ∫ s in (0:ℝ)..t, Real.exp (-ν*(t-s)*ρ k) •
            (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
              ∑ j : Fin 2, κ k j * (weight k • convolution
                (fun l => (weight l)⁻¹ • u s l)
                (fun l => (weight l)⁻¹ • u s l) k) (i,j))))) ∧
        let w : ℕ → K → ℝ := fun m k => (1+ρ k)^((m:ℝ)/2)
        let dec : ℕ → H → K → V := fun m z k => (w m k)⁻¹ • z k
        let aa : ℝ → K → V := fun t k => (1+ρ k)⁻¹ • u t k
        let N : (K → V) → (K → V) → K → V := fun a' b' k =>
          Complex.I • P k (∑' l : K, (∑ j : Fin 2, κ k j*a' l j) • b' (k-l))
        ∃ (U : ℕ → ℝ → H) (L : ℕ → H →L[ℝ] H)
          (B : ℕ → H →L[ℝ] H →L[ℝ] H),
          (∀ m t, t ∈ Icc 0 τ → ∀ k, U m t k = w m k • aa t k) ∧
          (∀ m, ContinuousOn (U m) (Icc 0 τ)) ∧
          (∀ m z k, L m z k = w m k • ((-ν*ρ k) • dec (m+2) z k)) ∧
          (∀ m z z' k, B m z z' k = w m k • N (dec (m+2) z) (dec (m+2) z') k) ∧
          (∀ m t, t ∈ Icc 0 τ → HasDerivWithinAt (U m)
            (L m (U (m+2) t) - B m (U (m+2) t) (U (m+2) t)) (Icc 0 τ) t) ∧
          (∀ m n : ℕ, ContDiffOn ℝ n (U m) (Icc 0 τ)) ∧
          (∀ n : ℕ, ContDiffOn ℝ n
            (fun z : ℝ × (Fin 2 → ℝ) => WithLp.toLp 2 (fun i : Fin 2 =>
              (∑' k : K, Complex.exp (Complex.I *
                ((k.1:ℝ)*z.2 0+(k.2:ℝ)*z.2 1)) • aa z.1 k) i |>.re))
            (Icc 0 τ ×ˢ (Set.univ : Set (Fin 2 → ℝ)))) ∧
          (∀ t ∈ Icc 0 τ, ∀ x : Fin 2 → ℝ,
            Summable (fun k : K => ‖Complex.exp (Complex.I *
              ((k.1:ℝ)*x 0+(k.2:ℝ)*x 1)) • aa t k‖) ∧
            ‖WithLp.toLp 2 (fun i : Fin 2 =>
              (∑' k : K, Complex.exp (Complex.I *
                ((k.1:ℝ)*x 0+(k.2:ℝ)*x 1)) • aa t k) i |>.re)‖ ≤ 4*R)

def preparedPredicate (p : Params) (u : ℝ → H) : Prop :=
  ∃ D : ℝ → H, candidatePredicate p (u,D)

def sourceStatement : Prop := ∀ (ν A B α β : ℝ),
    0 < ν → 0 < A → 0 ≤ B → |α| ≤ A → |β| ≤ B →
    let K := ℤ × ℤ
    let V := EuclideanSpace ℂ (Fin 2)
    let TV := EuclideanSpace ℂ (Fin 2 × Fin 2)
    let H := lp (fun _ : K => V) 2
    let ρ : K → ℝ := fun k => (k.1 : ℝ)^2 + (k.2 : ℝ)^2
    let κ : K → V := fun k => WithLp.toLp 2 (fun i => (![k.1, k.2] i : ℂ))
    let P := fun k => (ℂ ∙ κ k)ᗮ.starProjection
    let R := 2 * Real.sqrt (2*A^2 + 9*B^2)
    let τ := ν / (16384 * R^2)
    let a : V := WithLp.toLp 2 ![0, (α : ℂ)]
    let b : V := WithLp.toLp 2 ![(3*β/2 : ℂ), (3*β/2 : ℂ)]
    let X0 : H := lp.single 2 (1,0) a + lp.single 2 (-1,0) a +
      lp.single 2 (-1,1) b + lp.single 2 (1,-1) b
    ∃ u : ℝ → H, ContinuousOn u (Icc 0 τ) ∧ u 0 = X0 ∧
      (∀ t ∈ Icc 0 τ, ‖u t‖ ≤ R) ∧
      (∀ t ∈ Icc 0 τ, u t 0 = 0 ∧
        (∀ k i, u t (-k) i = star (u t k i)) ∧ (∀ k, P k (u t k) = u t k)) ∧
      (∀ v : ℝ → H, ContinuousOn v (Icc 0 τ) →
        (∀ t ∈ Icc 0 τ, ∀ k,
          v t k = Real.exp (-ν*t*ρ k) • X0 k - ∫ s in (0:ℝ)..t, Real.exp (-ν*(t-s)*ρ k) •
            (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
              ∑ j : Fin 2, κ k j * (weight k • convolution
                (fun l => (weight l)⁻¹ • v s l)
                (fun l => (weight l)⁻¹ • v s l) k) (i,j))))) →
        ∀ t ∈ Icc 0 τ, v t = u t) ∧
      (∀ (β₂ : ℝ) (v : ℝ → H), ContinuousOn v (Icc 0 τ) →
        (∀ t ∈ Icc 0 τ, ‖v t‖ ≤ R) →
        let b₂ : V := WithLp.toLp 2 ![(3*β₂/2 : ℂ),(3*β₂/2 : ℂ)]
        let X₂ : H := lp.single (E := fun _ : K => V) 2 (1,0) a +
          lp.single (E := fun _ : K => V) 2 (-1,0) a +
          lp.single (E := fun _ : K => V) 2 (-1,1) b₂ +
          lp.single (E := fun _ : K => V) 2 (1,-1) b₂
        (∀ t ∈ Icc 0 τ, ∀ k,
          v t k = Real.exp (-ν*t*ρ k) • X₂ k - ∫ s in (0:ℝ)..t, Real.exp (-ν*(t-s)*ρ k) •
            (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
              ∑ j : Fin 2, κ k j * (weight k • convolution
                (fun l => (weight l)⁻¹ • v s l)
                (fun l => (weight l)⁻¹ • v s l) k) (i,j))))) →
        ∀ t ∈ Icc 0 τ, ‖u t-v t‖ ≤ 6*|β-β₂|) ∧
      (∀ x y : ℝ, ∀ i : Fin 2,
        (∑' k : K, ((((weight k)⁻¹:ℝ):ℂ) * X0 k i) *
          D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis.character k x y) =
        (D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis.realVelocity α β x y i.castSucc : ℂ)) ∧
      ∃ D : ℝ → H, Continuous D ∧ D 0 = 0 ∧
        (∀ t ∈ Icc 0 τ, ‖D t‖ ≤ R/4) ∧
        (∀ t ∈ Icc 0 τ, ∀ k,
          u t k = Real.exp (-ν*t*ρ k) • X0 k - D t k) ∧
        (∀ t ∈ Icc 0 τ, ∀ k,
          D t k = ∫ s in (0:ℝ)..t, Real.exp (-ν*(t-s)*ρ k) •
            (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
              ∑ j : Fin 2, κ k j * (weight k • convolution
                (fun l => (weight l)⁻¹ • u s l)
                (fun l => (weight l)⁻¹ • u s l) k) (i,j))))) ∧
        let w : ℕ → K → ℝ := fun m k => (1+ρ k)^((m:ℝ)/2)
        let dec : ℕ → H → K → V := fun m z k => (w m k)⁻¹ • z k
        let aa : ℝ → K → V := fun t k => (1+ρ k)⁻¹ • u t k
        let N : (K → V) → (K → V) → K → V := fun a' b' k =>
          Complex.I • P k (∑' l : K, (∑ j : Fin 2, κ k j*a' l j) • b' (k-l))
        ∃ (U : ℕ → ℝ → H) (L : ℕ → H →L[ℝ] H)
          (B : ℕ → H →L[ℝ] H →L[ℝ] H),
          (∀ m t, t ∈ Icc 0 τ → ∀ k, U m t k = w m k • aa t k) ∧
          (∀ m, ContinuousOn (U m) (Icc 0 τ)) ∧
          (∀ m z k, L m z k = w m k • ((-ν*ρ k) • dec (m+2) z k)) ∧
          (∀ m z z' k, B m z z' k = w m k • N (dec (m+2) z) (dec (m+2) z') k) ∧
          (∀ m t, t ∈ Icc 0 τ → HasDerivWithinAt (U m)
            (L m (U (m+2) t) - B m (U (m+2) t) (U (m+2) t)) (Icc 0 τ) t) ∧
          (∀ m n : ℕ, ContDiffOn ℝ n (U m) (Icc 0 τ)) ∧
          (∀ n : ℕ, ContDiffOn ℝ n
            (fun z : ℝ × (Fin 2 → ℝ) => WithLp.toLp 2 (fun i : Fin 2 =>
              (∑' k : K, Complex.exp (Complex.I *
                ((k.1:ℝ)*z.2 0+(k.2:ℝ)*z.2 1)) • aa z.1 k) i |>.re))
            (Icc 0 τ ×ˢ (Set.univ : Set (Fin 2 → ℝ)))) ∧
          (∀ t ∈ Icc 0 τ, ∀ x : Fin 2 → ℝ,
            Summable (fun k : K => ‖Complex.exp (Complex.I *
              ((k.1:ℝ)*x 0+(k.2:ℝ)*x 1)) • aa t k‖) ∧
            ‖WithLp.toLp 2 (fun i : Fin 2 =>
              (∑' k : K, Complex.exp (Complex.I *
                ((k.1:ℝ)*x 0+(k.2:ℝ)*x 1)) • aa t k) i |>.re)‖ ≤ 4*R)

def signature : Signature where
  Params := Params
  State _ := ℝ → H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Fin 0
  finiteAnchor := inferInstance

def actual : Realization signature := by
  classical
  exact realize signature (fun _ p x => decide (preparedPredicate p x)) (fun i => Fin.elim0 i)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun i => Fin.elim0 i)

def arena : Arena := ⟨signature, fun r => ∀ p, admissible p →
  ∃ x, r.readout () p x = true⟩

theorem actual_positive : arena.Law actual := by
  classical
  intro p hp
  rcases p with ⟨ν,A,B,α,β⟩
  rcases hp with ⟨hν,hA,hB,hα,hβ⟩
  rcases _root_.D5.S3.FluidDynamics.Fourier.ActualPreparedSolution.prepared_mild_solution
      ν A B α β hν hA hB hα hβ with
    ⟨u,hc,hu0,hn,hg,hUnique,hStability,hphysical,D,hDc,hD0,hDb,huk,hDk,hgrades⟩
  refine ⟨u, ?_⟩
  change decide (preparedPredicate ⟨ν,A,B,α,β⟩ u) = true
  apply decide_eq_true_iff.mpr
  exact ⟨D,hc,hu0,hn,hg,hUnique,hStability,hphysical,hDc,hD0,hDb,huk,hDk,hgrades⟩

def p0 : Params := ⟨1,1,0,0,0⟩

theorem hp0 : admissible p0 := by norm_num [admissible,p0]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x,hx⟩ := h p0 hp0
  exact Bool.false_ne_true hx

theorem bridge : sourceStatement ↔ arena.Law actual := by
  classical
  constructor
  · intro h p hp
    rcases p with ⟨ν,A,B,α,β⟩
    rcases hp with ⟨hν,hA,hB,hα,hβ⟩
    obtain ⟨u,hc,hu0,hn,hg,hUnique,hStability,hphysical,D,hDc,hD0,hDb,huk,hDk,hgrades⟩ :=
      h ν A B α β hν hA hB hα hβ
    refine ⟨u, ?_⟩
    change decide (preparedPredicate ⟨ν,A,B,α,β⟩ u) = true
    exact decide_eq_true_iff.mpr ⟨D,hc,hu0,hn,hg,hUnique,hStability,hphysical,hDc,hD0,hDb,huk,hDk,hgrades⟩
  · intro h ν A B α β hν hA hB hα hβ
    obtain ⟨u,hu⟩ := h ⟨ν,A,B,α,β⟩ ⟨hν,hA,hB,hα,hβ⟩
    change decide (preparedPredicate ⟨ν,A,B,α,β⟩ u) = true at hu
    obtain ⟨D,hc,hu0,hn,hg,hUnique,hStability,hphysical,hDc,hD0,hDb,huk,hDk,hgrades⟩ :=
      decide_eq_true_iff.mp hu
    exact ⟨u,hc,hu0,hn,hg,hUnique,hStability,hphysical,D,hDc,hD0,hDb,huk,hDk,hgrades⟩

theorem variation : Variation arena actual := ⟨actual_positive,rejected,rejected_law⟩

theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j h
    have he : j = i := by cases i; cases j; rfl
    exact (h he).elim
  · intro i
    exact Fin.elim0 i

def bad : signature.State p0 :=
  fun _ => lp.single 2 (0,0) (WithLp.toLp 2 ![(1:ℂ),0])

theorem bad_rejected : ¬ preparedPredicate p0 bad := by
  rintro ⟨D,h⟩
  have he := h.2.1
  have hc := congrArg (fun z : H => z (0,0) 0) he
  norm_num [bad, p0, lp.single_apply, PiLp.smul_apply] at hc

theorem dependence : ObservationalDependence signature actual := by
  classical
  intro i
  obtain ⟨good,hgood⟩ := actual_positive p0 hp0
  refine ⟨p0,good,bad, ?_⟩
  cases i
  have hb : actual.readout () p0 bad = false := by
    change decide (preparedPredicate p0 bad) = false
    exact decide_eq_false bad_rejected
  rw [hgood,hb]
  exact Bool.false_ne_true ∘ Eq.symm

def registration : Registration arena sourceStatement where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

-- Source-bound registration remains open: the complete Boolean candidate
-- predicate still needs an admitted SourceSelection and reconstruction bridge.
#print axioms registration

end Reg.D5.S3.FluidDynamics.Fourier.ActualPreparedSolution
