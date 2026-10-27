module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Polynomial.AlgebraMap

public section

namespace Reg.Support.PolynomialSubalgebra

/-- The polynomial variable distinguishes the full algebra from its constants. -/
theorem X_not_mem_bot {k : Type*} [CommSemiring k] [Nontrivial k] :
    Polynomial.X ∉ (⊥ : Subalgebra k (Polynomial k)) := by
  rintro ⟨c, hc⟩
  exact Polynomial.X_ne_C c hc.symm

end Reg.Support.PolynomialSubalgebra
