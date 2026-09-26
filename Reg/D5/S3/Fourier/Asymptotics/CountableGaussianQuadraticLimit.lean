import D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit
import Mathlib.Probability.HasLawExists
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- Use the original source's additive norm dictionary. The ring-derived route
available after the audit imports is definitionally equal but has different raw operands. -/
local instance : SeminormedAddCommGroup ℝ :=
  Real.normedAddCommGroup.toSeminormedAddCommGroup

abbrev signature : Signature where
  Params := Σ Ω : Type, Σ _ : ℕ → ℕ → Ω → ℝ, Σ _ : ℕ → ℕ → ℝ, Σ _ : ℕ, ℕ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p ω =>
    p.2.2.1 p.2.2.2.1 p.2.2.2.2 * ((p.2.1 p.2.2.2.1 p.2.2.2.2 ω) ^ 2 - 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete original telescope and conclusion, with the same weighted summand
replaced in both the existential MemLp witnesses and their actual L² sums. -/
def arena : Arena where
  signature := signature
  Law r := ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → ℕ → Ω → ℝ) (a : ℕ → ℕ → ℝ) (v : ℝ≥0),
    (∀ n j, HasLaw (G n j) (gaussianReal 0 1) P) →
    (∀ n, iIndepFun (G n) P) →
    (∀ n, Summable (fun j => (a n j) ^ 2)) →
    Tendsto (fun n => ⨆ j, |a n j|) atTop (𝓝 0) →
    Tendsto (fun n => ∑' j, (a n j) ^ 2) atTop (𝓝 ((v : ℝ) / 2)) →
    ∃ (hmem : ∀ n j, MemLp (fun ω => (r.readout () ⟨Ω, G, a, n, j⟩ ω : ℝ)) 2 P)
      (Q : ℕ → Lp ℝ 2 P),
      (∀ n, HasSum (fun j => (hmem n j).toLp
        (fun ω => (r.readout () ⟨Ω, G, a, n, j⟩ ω : ℝ))) (Q n)) ∧
      TendstoInDistribution (fun n => ⇑(Q n)) atTop (id : ℝ → ℝ)
        (fun _ => P) (gaussianReal 0 v)

/-- A genuine probability space with independent standard Gaussians satisfies every
original premise at a = 0 and v = 0. Constant-one interventions cannot be summed in L². -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨Ω, mΩ, P, X, _, hX, hind, hP⟩ := exists_iid ℕ (gaussianReal 0 1)
  let := mΩ
  let := hP
  obtain ⟨hmem, Q, hsum, _⟩ := h Ω P (fun _ => X) (fun _ _ => 0) 0
    (fun _ j => hX j) (fun _ => hind)
    (by simp) (by simp) (by simp)
  have hs : Summable (fun _ : ℕ => Lp.const 2 P (1 : ℝ)) := (hsum 0).summable
  have hz : Lp.const 2 P (1 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hs.tendsto_atTop_zero
  have hn := congrArg norm hz
  simp [Lp.norm_const] at hn

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ℝ, (fun _ _ ω => ω), (fun _ _ => 1), 0, 0⟩, (0 : ℝ), (1 : ℝ), ?_⟩
    exact (by norm_num : (1 : ℝ) * (0 ^ 2 - 1) ≠ 1 * (1 ^ 2 - 1))

register_information_theorem
  _root_.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.result in arena
  readout via (realize signature (fun _ p ω =>
    p.2.2.1 p.2.2.2.1 p.2.2.2.2 * ((p.2.1 p.2.2.2.1 p.2.2.2.2 ω) ^ 2 - 1))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit
    coordinates := #[0, 4, 5, 12, 13]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "fn", "arg", "body"]
      stateBinder := 14 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit
