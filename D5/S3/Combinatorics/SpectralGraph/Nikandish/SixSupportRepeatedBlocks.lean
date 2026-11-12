/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportRepeatedBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportRepeatedBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full repeated-exponent invariant operators and actual graph consumers. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportClassificationAlgebra
import Mathlib.Tactic

/-! The original symmetric four-cell and antisymmetric two-cell operators,
with full intertwining on every source vector. The cubic is consumed by the
literal six-cell characteristic polynomial and then the actual ideal graph. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportRepeatedBlocks

open Matrix
open D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra
open D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
open D5.S3.Combinatorics.SpectralGraph.SixSupportIdealIntersectionLift (exponents)
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions

/-- Actual nonuniversal support population N. -/
def size {R : Type*} [CommRing R] (a b : R) : R := a^2+2*a*b+2*a+b

/-- The complete original symmetric cell-constant Laplacian operator of H. -/
def symmetricBlock (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![a^2+a*b,0,-a^2,-a*b;
     0,2*a*b,0,-2*a*b;
     -2*a,0,2*a+2*a*b,-2*a*b;
     -a,-b,-a^2,a^2+a+b]

/-- The complete original antisymmetric operator of H. -/
def antisymmetricBlock (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a^2+a*b,-a*b; -a,a^2+a+b+2*a*b]

/-- Restore both swapped coordinates on every symmetric source vector. -/
def symmetricLift (v : Fin 4 → ℝ) : Fin 6 → ℝ := ![v 0,v 0,v 1,v 2,v 3,v 3]

/-- Restore the opposite signs on every antisymmetric source vector. -/
def antisymmetricLift (v : Fin 2 → ℝ) : Fin 6 → ℝ := ![v 0,-v 0,0,0,v 1,-v 1]

/-- Both invariant representations are injective on their entire vector domains. -/
theorem lifts_injective : Function.Injective symmetricLift ∧ Function.Injective antisymmetricLift := by
  constructor
  · intro v w h
    ext i
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 2
    · exact congrFun h 3
    · exact congrFun h 4
  · intro v w h
    ext i
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 4

/-- Full antisymmetric intertwining with the literal six-cell complement operator. -/
theorem antisymmetric_intertwining (a b : ℝ) (v : Fin 2 → ℝ) :
    quotient a a b *ᵥ antisymmetricLift v =
      antisymmetricLift ((Matrix.scalar (Fin 2) (size a b)-antisymmetricBlock a b) *ᵥ v) := by
  ext i
  fin_cases i <;>
    simp [quotient,antisymmetricLift,antisymmetricBlock,size,Matrix.scalar,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.sub_apply] <;> ring <;> simp

/-- Full symmetric intertwining, with the weighted constant component explicit.
Zero sum is not silently presumed for an arbitrary source vector. -/
theorem symmetric_intertwining (a b : ℝ) (v : Fin 4 → ℝ) :
    quotient a a b *ᵥ symmetricLift v =
      size a b • symmetricLift v - symmetricLift (symmetricBlock a b *ᵥ v) -
        (2*a*v 0+b*v 1+a^2*v 2+2*a*b*v 3) • (fun _ : Fin 6 => (1 : ℝ)) := by
  ext i
  fin_cases i <;>
    simp [quotient,symmetricLift,symmetricBlock,size,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

/-- The actual source fiber weights symmetrize the full four-cell operator. -/
theorem weighted_symmetric (a b : ℝ) :
    (Matrix.diagonal ![2*a,b,a^2,2*a*b]*symmetricBlock a b).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricBlock,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

/-- The original source symmetric cubic, over any commutative coefficient ring. -/
def cubic {R : Type*} [CommRing R] (a b x : R) : R :=
  x^3-(2*a^2+5*a*b+3*a+b)*x^2+
    (a^4+7*a^3*b+3*a^3+8*a^2*b^2+11*a^2*b+2*a^2+3*a*b^2+2*a*b)*x-
    2*a^2*b*(a+b+1)*(a^2+2*a*b+2*a+b)

/-- The complementary antisymmetric characteristic quadratic. -/
def quadratic {R : Type*} [CommRing R] (a b x : R) : R :=
  x^2-(a*b+3*a+b)*x+(a*b+2*a^2)

/-- Exact whole repeated-exponent characteristic factorization. -/
theorem factorization (a b x : ℝ) :
    h a a b x = -quadratic a b x*cubic a b (size a b-x) := by
  simp [h,quintic,quadratic,cubic,size]
  ring

/-- The cubic cannot have the excluded complementary value N as a root. -/
theorem cubic_at_size {R : Type*} [CommRing R] (a b : R) :
    cubic a b (size a b) = a*b*size a b := by
  dsimp [cubic,size]
  ring

/-- Every real symmetric cubic root acts on actual ideals, for all positive
repeated and third exponents, with the exact original universal-vertex shift. -/
theorem actual_cubic_eigenvalue (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (r : ℝ) (hr : cubic (a : ℝ) (b : ℝ) r = 0) :
    HasActualEigenvalue (modulus p (exponents a a b)) (r+(a : ℝ)^2*b-1) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hN : 0 < size (a : ℝ) (b : ℝ) := by dsimp [size]; positivity
  have he0 : size (a : ℝ) (b : ℝ)-r ≠ 0 := by
    intro hz
    have heq : r = size (a : ℝ) (b : ℝ) := by linarith
    rw [heq,cubic_at_size] at hr
    have : 0 < (a : ℝ)*(b : ℝ)*size (a : ℝ) (b : ℝ) := by positivity
    linarith
  have hroot : h (a : ℝ) (a : ℝ) (b : ℝ) (size (a : ℝ) (b : ℝ)-r) = 0 := by
    rw [factorization]
    have heq : size (a : ℝ) (b : ℝ)-(size (a : ℝ) (b : ℝ)-r) = r := by ring
    rw [heq,hr,mul_zero]
  have he := actual_of_root p hp hinj a a b ha ha hb _ he0 hroot
  have hprod : 2 ≤ (a+1)*(a+1)*(b+1) := by
    calc
      2 ≤ 2*2*2 := by decide
      _ ≤ (a+1)*(a+1)*(b+1) := Nat.mul_le_mul
        (Nat.mul_le_mul (by omega) (by omega)) (by omega)
  convert he using 1
  rw [Nat.cast_sub hprod]
  push_cast
  dsimp [size]
  ring

/-- Noninteger unit-interval cubic roots refute actual integral spectrum on
the full original positive repeated-exponent family. -/
theorem actual_nonintegral_of_unit_root (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (r : ℝ) (hr : cubic (a : ℝ) (b : ℝ) r = 0)
    (q : ℤ) (hl : (q : ℝ) < r) (hu : r < (q : ℝ)+1) :
    ¬ActualLaplacianIntegral (modulus p (exponents a a b)) := by
  intro hint
  obtain ⟨z,hz⟩ := hint _ (actual_cubic_eigenvalue p hp hinj a b ha hb r hr)
  have hrepr : r = ((z-(a : ℤ)^2*b+1 : ℤ) : ℝ) := by push_cast; linarith
  have hlow : q < z-(a : ℤ)^2*b+1 := by exact_mod_cast (show (q : ℝ) <
    ((z-(a : ℤ)^2*b+1 : ℤ) : ℝ) by rw [← hrepr]; exact hl)
  have hupp : z-(a : ℤ)^2*b+1 < q+1 := by exact_mod_cast (show
    ((z-(a : ℤ)^2*b+1 : ℤ) : ℝ) < (q : ℝ)+1 by rw [← hrepr]; exact hu)
  omega

#print axioms lifts_injective
#print axioms antisymmetric_intertwining
#print axioms symmetric_intertwining
#print axioms weighted_symmetric
#print axioms factorization
#print axioms actual_cubic_eigenvalue
#print axioms actual_nonintegral_of_unit_root

end D5.S3.Combinatorics.SpectralGraph.SixSupportRepeatedBlocks
