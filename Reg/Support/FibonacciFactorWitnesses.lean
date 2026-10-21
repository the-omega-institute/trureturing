import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph

namespace Reg.Support.FibonacciFactorWitnesses
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
noncomputable section

theorem word_weight_ne_one (w : List CuLetter) : wordWeight w ≠ 1 := by
  cases w with
  | nil => simp [wordWeight]
  | cons a w => cases a <;> simp only [wordWeight] <;> omega

theorem all_u_path (n : ℕ) (side : MemorySide) (K : ℕ) (d : ℝ) :
    BilateralGraphPath side K d (fun (_ : ℤ) (_ : Fin n) => CuLetter.u)
      (fun _ : ℤ => CuLetter.u) := by
  intro i
  refine ⟨?_, ?_, ?_⟩
  · funext k
    simp [memoryShift]
  · intro h
    cases h.1
  · intro h
    cases h.1

theorem all_u_live (n : ℕ) (side : MemorySide) (K : ℕ) (d : ℝ) :
    LiveVertex side K d (fun _ : Fin n => CuLetter.u) :=
  ⟨(fun _ _ => .u), (fun _ => .u), all_u_path n side K d, rfl⟩

def empty_retained : RetainedPathDictionary .lower 1 1 0 0 :=
  ⟨((fun _ => .u), []), all_u_live 1 .lower 1 0, rfl⟩

theorem all_u_auxiliary : (fun _ : ℤ => CuLetter.u) ∈ AuxiliaryLanguage 1 0 := by
  constructor
  · intro i h
    have bad := h 0
    cases bad
  · intro i h
    have bad := h 0
    cases bad

end
end Reg.Support.FibonacciFactorWitnesses
