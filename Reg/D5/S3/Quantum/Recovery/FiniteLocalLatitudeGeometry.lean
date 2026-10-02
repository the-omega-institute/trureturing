import D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
import Reg.Support.DependentFamily

open D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ _ r => h r) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℝ) (hr : 0 < r) (hlo : 1/2 < r^2) (hhi : r^2 < 2),
    ((∃ b : Fin 3 → ℂ, Normalized b ∧ Flat r b) ∧
    (∀ b : Fin 3 → ℂ, Normalized b → Flat r b →
      (∀ i, response r b i = 1/3) ∧
      (∀ k, Complex.normSq (b k) = 1/3) ∧
      ‖b 1^2 - 2*b 0*b 2‖ = kappa r)) ∧
    (∃ x y : Fin 2 → ℂ, UnitSpinor x ∧ UnitSpinor y ∧ ∀ i, productResponse r x y i = R.readout () () r) ∧
    (∀ x y : Fin 2 → ℂ, UnitSpinor x → UnitSpinor y → FlatProduct r x y →
      (∀ i, productResponse r x y i = h r) ∧ antisymmetricWeight x y = g r ∧
      spinorZ x = -spinorZ y ∧ (spinorZ x)^2 = 1-4*h r) ∧
    (K_s r).Nonempty ∧
    (∀ a b : Bloch, (a,b) ∈ K_s r →
      a 2 = -b 2 ∧ (a 2)^2 = 1-4*h r ∧ defect a b = g r)

theorem actual_law : arena.Law actual := all_r_flat_geometry

theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  obtain ⟨_,⟨x,y,hx,hy,flat⟩,_⟩ := bad 1 (by norm_num) (by norm_num) (by norm_num)
  have hf : FlatProduct 1 x y := by
    intro i
    exact (flat i).trans (flat 0).symm
  have geom := (all_r_flat_geometry 1 (by norm_num) (by norm_num) (by norm_num)).2.2.1 x y hx hy hf
  have eq := (geom.1 0).symm.trans (flat 0)
  have hp : 0 < h 1 := by unfold h kappa; positivity
  exact (ne_of_gt hp) eq

def registration : Registration arena (∀ (r : ℝ) (hr : 0 < r)
    (hlo : 1/2 < r^2) (hhi : r^2 < 2),
    ((∃ b : Fin 3 → ℂ, Normalized b ∧ Flat r b) ∧
    (∀ b : Fin 3 → ℂ, Normalized b → Flat r b →
      (∀ i, response r b i = 1/3) ∧
      (∀ k, Complex.normSq (b k) = 1/3) ∧
      ‖b 1^2 - 2*b 0*b 2‖ = kappa r)) ∧
    (∃ x y : Fin 2 → ℂ, UnitSpinor x ∧ UnitSpinor y ∧ ∀ i, productResponse r x y i = h r) ∧
    (∀ x y : Fin 2 → ℂ, UnitSpinor x → UnitSpinor y → FlatProduct r x y →
      (∀ i, productResponse r x y i = h r) ∧ antisymmetricWeight x y = g r ∧
      spinorZ x = -spinorZ y ∧ (spinorZ x)^2 = 1-4*h r) ∧
    (K_s r).Nonempty ∧
    (∀ a b : Bloch, (a,b) ∈ K_s r →
      a 2 = -b 2 ∧ (a 2)^2 = 1-4*h r ∧ defect a b = g r)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(),(0:ℝ),(1:ℝ),?_⟩
    change h 0 ≠ h 1
    intro heq
    have h0 : kappa 0 = 2/3 := by norm_num [kappa]
    have kp : 0 < 1+kappa 1 := by unfold kappa; positivity
    have hks : (kappa 1)^2 = 8/9 := by
      unfold kappa
      rw [div_pow,Real.sq_sqrt (by norm_num)]
      norm_num
    unfold h at heq
    rw [h0] at heq
    have kk : kappa 1 = 2/3 := by
      field_simp [ne_of_gt kp] at heq
      linarith
    rw [kk] at hks
    norm_num at hks

register_information_theorem all_r_flat_geometry in arena
  readout via (realize signature (fun _ _ r => h r) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg", "body",
        "arg", "body", "arg", "arg", "body", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
