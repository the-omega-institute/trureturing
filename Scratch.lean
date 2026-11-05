import D5.S3.Quantum.Dynamics.NativeProtocolGraft
open scoped BigOperators Matrix
namespace D5.S3.Quantum.Dynamics.NativeProtocolGraft
namespace Actual
namespace CutCovariance
open Coeff
abbrev K := QuadraticAlgebra Coeff.S (Coeff.inc Coeff.tau) 0
abbrev Col (L : Type) (T : Tree L) := Tree.Path T × Actual.Rest
def betaK : K := QuadraticAlgebra.omega

def coeff {L : Type} (T : Tree L) (p : Tree.Path T) (i : Fin 2) (e : Rest) : K :=
  betaK ^ Coeff.exponent (Actual.cut.symm (i,e)) *
    algebraMap Coeff.S K (Coeff.branch T p Coeff.initial (Actual.cut.symm (i,e)))

def V {L : Type} (T : Tree L) (event : Tree.Path T → Bool) :
    Matrix (Fin 2) (Col L T) K := fun i c =>
  if event c.1 then coeff T c.1 i c.2 else 0

def Xi {L : Type} (T : Tree L) (event : Tree.Path T → Bool) : Matrix (Fin 2) (Fin 2) K :=
  fun i j => ∑ p, ∑ e, if event p then
      coeff T p i e * star (coeff T p j e) else 0

def Vstar {L : Type} (T : Tree L) (event : Tree.Path T → Bool) :
    Matrix (Col L T) (Fin 2) K := fun c j => star (V T event j c)

theorem Xi_eq_VVstar {L : Type} (T : Tree L) (event : Tree.Path T → Bool) :
    Xi T event = V T event * Vstar T event := by
  classical
  ext i j
  simp only [Xi, V, Vstar, Matrix.mul_apply, Finset.univ_product_univ]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  rcases c with ⟨p,e⟩
  by_cases hp : event p <;> simp [hp]

end CutCovariance
end Actual
end D5.S3.Quantum.Dynamics.NativeProtocolGraft
