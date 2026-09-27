import D5.S3.Quantum.Matrix.FinitePhaseMixture
import Reg.Support.DependentFamily

open scoped BigOperators ComplexConjugate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture

noncomputable section

def signature : Signature where
  Params := ℕ
  State := fun d => Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ d => Matrix (Fin d) (Fin d) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ H => H) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ (d : ℕ) _ => (0 : Matrix (Fin d) (Fin d) ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (_hd : 1 ≤ d) (H : Matrix (Fin d) (Fin d) ℂ)
    (_hH : H.IsHermitian) (_hdiag : ∀ i, H i i = 1)
    (_hmass : (∑ i, ∑ j, if i < j then ‖H i j‖ else 0) ≤ 1),
    ∃ n : ℕ, 0 < n ∧ ∃ (p : Fin n → ℝ) (z : Fin n → Fin d → ℂ),
      (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1 ∧
      (∀ a i, ‖z a i‖ = 1) ∧
      ∀ i j, R.readout () d H i j = ∑ a, (p a : ℂ) * z a i * conj (z a j)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨_root_.D5.S3.Quantum.Matrix.FinitePhaseMixture.result, rejected, ?_⟩
    intro h
    obtain ⟨n, _, p, z, _, hp, hz, he⟩ := h 1 (by omega) 1
      (Matrix.isHermitian_one) (by simp) (by simp)
    have he0 := he 0 0
    change (0 : ℂ) = ∑ a, (p a : ℂ) * z a 0 * conj (z a 0) at he0
    simp only [mul_assoc, Complex.mul_conj', hz, one_pow, Complex.ofReal_one, mul_one] at he0
    have hpC : (∑ a, (p a : ℂ)) = 1 := by exact_mod_cast hp
    exact zero_ne_one (he0.trans hpC)
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        obtain ⟨n, _, p, z, _, hp, hz, he⟩ := h 1 (by omega) 1
          (Matrix.isHermitian_one) (by simp) (by simp)
        have he0 := he 0 0
        change (0 : ℂ) = ∑ a, (p a : ℂ) * z a 0 * conj (z a 0) at he0
        simp only [mul_assoc, Complex.mul_conj', hz, one_pow, Complex.ofReal_one, mul_one] at he0
        have hpC : (∑ a, (p a : ℂ)) = 1 := by exact_mod_cast hp
        exact zero_ne_one (he0.trans hpC)
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(1 : ℕ), (0 : Matrix (Fin 1) (Fin 1) ℂ),
      (1 : Matrix (Fin 1) (Fin 1) ℂ), ?_⟩
    intro h
    have hh := congrFun (congrFun h 0) 0
    norm_num [actual, realize] at hh

register_information_theorem _root_.D5.S3.Quantum.Matrix.FinitePhaseMixture.result
  in arena
  readout via (realize signature (fun _ _ H => H) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Matrix.FinitePhaseMixture
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "body", "arg", "body", "arg", "arg", "arg", "body", "body",
        "fn", "arg", "fn", "fn"]
      stateBinder := 2 }] })
  escape continues (open)

end
end Reg.D5.S3.Quantum.Matrix.FinitePhaseMixture
