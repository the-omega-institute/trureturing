import D5.S3.PolynomialSigns.FullLineSampling
import Reg.Support.DependentFamily

namespace Reg.D5.S3.PolynomialSigns.FullLineSampling

open _root_.D5.S3.PolynomialSigns.FullLineSampling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial
open scoped BigOperators

noncomputable section

/-- Parameters retain the entire original family; states select a member. -/
def signature : Signature where
  Params := (m : ℕ) × (Fin m → ℝ[X])
  State a := Fin a.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ[X]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a i => a.2 i) (fun e => nomatch e)

/-- Sampling locations remain those of the original family. All five sign
readouts use the observed member, so their agreement is a joint condition. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (f : Fin m → ℝ[X]) (s : Fin m → Fin 3),
    let p := ∏ i, if f i = 0 then 1 else f i
    (∃ y : ℝ, ∀ i, ternary ((R.readout () ⟨m, f⟩ i).eval y) = s i) ↔
      (∀ i, ternary (R.readout () ⟨m, f⟩ i).leadingCoeff = s i) ∨
      (∀ i, ternary ((R.readout () ⟨m, f⟩ i).comp (-X)).leadingCoeff = s i) ∨
      (∃ r : p.roots.toFinset, ∀ i,
        ternary ((R.readout () ⟨m, f⟩ i).eval r.val) = s i) ∨
      (∃ r : p.derivative.roots.toFinset, ∀ i,
        ternary ((R.readout () ⟨m, f⟩ i).eval r.val) = s i)

/-- Replacing constant members by X leaves the original empty root supports
unable to represent the zero sign attained at the origin. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => X) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h' := h (fun _ : Fin 1 => (1 : ℝ[X])) (fun _ => (1 : Fin 3))
  have attained : ∃ y : ℝ, ∀ i : Fin 1, ternary ((X : ℝ[X]).eval y) = 1 := by
    exact ⟨0, by intro i; norm_num [ternary]⟩
  have failed := h'.mp attained
  norm_num [rejected, realize, signature, ternary, Polynomial.leadingCoeff_neg] at failed
  rcases failed with ht | hb
  · have impossible := ht (0 : Fin 1)
    exact (by decide : (2 : Fin 3) ≠ 1) impossible
  · exact hb (0 : Fin 1)

theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨2, fun i => if i = 0 then 0 else 1⟩, (0 : Fin 2), (1 : Fin 2), ?_⟩
  change (if (0 : Fin 2) = 0 then (0 : ℝ[X]) else 1) ≠
    (if (1 : Fin 2) = 0 then (0 : ℝ[X]) else 1)
  norm_num

def registration : Registration arena
    (∀ {m : ℕ} (f : Fin m → ℝ[X]) (s : Fin m → Fin 3),
      let p := ∏ i, if f i = 0 then 1 else f i
      (∃ y : ℝ, ∀ i, ternary ((f i).eval y) = s i) ↔
        (∀ i, ternary (f i).leadingCoeff = s i) ∨
        (∀ i, ternary ((f i).comp (-X)).leadingCoeff = s i) ∨
        (∃ r : p.roots.toFinset, ∀ i, ternary ((f i).eval r.val) = s i) ∨
        (∃ r : p.derivative.roots.toFinset, ∀ i, ternary ((f i).eval r.val) = s i)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨full_line_sampling, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      have hji : j = i := by cases j; cases i; rfl
      exact False.elim (hj hji)
    · intro e
      exact nomatch e
  dependence := dependence

register_information_theorem full_line_sampling in arena
  readout via (realize signature (fun _ a i => a.2 i) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.PolynomialSigns.FullLineSampling
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

#print axioms registration
end
end Reg.D5.S3.PolynomialSigns.FullLineSampling
