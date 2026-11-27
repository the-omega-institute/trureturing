/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qArbitraryWickRecursion
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Wick recursion by retained, singleton, and paired first-oscillator occurrences. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedTwoCurrentIterate

/-!
A finite arbitrary-length Wick recursion for first oscillator directions.

The signed current normal order is supplied separately as `normal`.  The
construction below performs only the scalar Wick bookkeeping.  Every pending
occurrence is either left in the uncontracted word, used once by the momentum
mean, or paired once by the scalar covariance.  Thus current normal ordering
and scalar Wick combinatorics remain distinct.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qArbitraryWickRecursion

open LatticeGeneratingFieldLocality (Charge)
open P48qThirdTwistedField (Cartan State fieldCoeff fixedDualBases)
open P48qCurrentChargedIterate (contraction normalOrderedCurrentCoeff)
open P48qTwistedChargeAction (lattice)

variable {I M : Type*} [AddCommMonoid M] [Module ℂ M]

/--
The scalar Wick moment on a finite occurrence word.  Equal labels at
separate positions remain separate summands because the partner index is a
`Fin` occurrence position.
-/
def scalarWick (A : Matrix I I ℂ) (μ : I → ℂ) : List I → ℂ
  | [] => 1
  | a :: tail =>
      μ a * scalarWick A μ tail +
        ∑ j : Fin tail.length,
          A a (tail.get j) * scalarWick A μ (tail.eraseIdx j)
termination_by l => l.length
decreasing_by
  all_goals
    simp only [List.length_cons]
    first
    | exact Nat.lt_succ_self _
    | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

@[simp] theorem scalarWick_nil (A : Matrix I I ℂ) (μ : I → ℂ) :
    scalarWick A μ [] = 1 := by
  simp [scalarWick]

/-- The scalar singleton/pair recursion, with a genuinely finite partner sum. -/
theorem scalarWick_cons (A : Matrix I I ℂ) (μ : I → ℂ) (a : I) (tail : List I) :
    scalarWick A μ (a :: tail) =
      μ a * scalarWick A μ tail +
        ∑ j : Fin tail.length,
          A a (tail.get j) * scalarWick A μ (tail.eraseIdx j) := by
  simp only [scalarWick]

/--
The arbitrary-length expansion with an independent uncontracted-word value.
`pre` contains modes already declared uncontracted and `pending` contains
modes still to be classified.
-/
def normalWick (A : Matrix I I ℂ) (μ : I → ℂ) (normal : List I → M) :
    List I → List I → M
  | [], pre => normal pre
  | a :: pending, pre =>
      normalWick A μ normal pending (pre ++ [a]) +
        μ a • normalWick A μ normal pending pre +
        ∑ j : Fin pending.length,
          A a (pending.get j) • normalWick A μ normal (pending.eraseIdx j) pre
termination_by l => l.length
decreasing_by
  all_goals
    simp only [List.length_cons]
    first
    | exact Nat.lt_succ_self _
    | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

@[simp] theorem normalWick_nil (A : Matrix I I ℂ) (μ : I → ℂ)
    (normal : List I → M) (pre : List I) :
    normalWick A μ normal [] pre = normal pre := by
  simp [normalWick]

/-- The one-step finite recursion used at every length. -/
theorem normalWick_step (A : Matrix I I ℂ) (μ : I → ℂ)
    (normal : List I → M) (pre : List I) (a : I) (pending : List I) :
    normalWick A μ normal (a :: pending) pre =
      normalWick A μ normal pending (pre ++ [a]) +
        μ a • normalWick A μ normal pending pre +
        ∑ j : Fin pending.length,
          A a (pending.get j) • normalWick A μ normal (pending.eraseIdx j) pre := by
  simp only [normalWick]

/-- A list-level expression for an arbitrary product of first directions. -/
def normalWickWord (A : Matrix I I ℂ) (μ : I → ℂ)
    (normal : List I → M) (word : List I) : M :=
  normalWick A μ normal word []

/-- The finite two-occurrence expansion, including uncontracted modes. -/
theorem normalWick_two (A : Matrix I I ℂ) (μ : I → ℂ)
    (normal : List I → M) (u v : I) :
    normalWickWord A μ normal [u, v] =
      normal [u, v] + μ v • normal [u] + μ u • normal [v] +
        (μ u * μ v + A u v) • normal [] := by
  simp [normalWickWord, normalWick, Fin.sum_univ_two, add_assoc, add_left_comm,
    add_comm, smul_add, add_smul, smul_smul] <;> abel

/-- The scalar two-occurrence pairing is invariant under exchanging positions. -/
theorem scalarWick_two_swap (A : Matrix I I ℂ) (μ : I → ℂ) (u v : I)
    (hA : A u v = A v u) :
    scalarWick A μ [u, v] = scalarWick A μ [v, u] := by
  simp [scalarWick]
  rw [hA]
  ring

/--
At degree two the full readout is permutation invariant once the supplied
signed normal word has the established exchange symmetry.
-/
theorem normalWick_two_swap (A : Matrix I I ℂ) (μ : I → ℂ)
    (normal : List I → M) (u v : I)
    (hA : A u v = A v u) (hN : normal [u, v] = normal [v, u]) :
    normalWickWord A μ normal [u, v] = normalWickWord A μ normal [v, u] := by
  rw [normalWick_two, normalWick_two, hN, hA]
  rw [mul_comm (μ u) (μ v)]
  abel

open P48qChargedTwoCurrentIterate

/--
The two-current normal part is isolated from the scalar Wick corrections.
This is a local readout used only for the degree-two bridge below.
-/
def p48qSecondNormal (a : Charge lattice) (k : ℤ) (u v : Cartan) :
    Module.End ℂ State :=
  HVertexOperator.coeff
      (P48qChargedTwoCurrentIterate.stateField (chargedSecond a u v)) k +
    contraction a u • normalOrderedCurrentCoeff a (k + 3) v +
    contraction a v • normalOrderedCurrentCoeff a (k + 3) u -
    (P48qQuadraticStateField.correction u v + contraction a u * contraction a v) •
      fieldCoeff fixedDualBases a (k + 6)

/-- The uncontracted-word readout needed through degree two. -/
def p48qNormalWord (a : Charge lattice) (k : ℤ) :
    List Cartan → Module.End ℂ State
  | [] => fieldCoeff fixedDualBases a (k + 6)
  | [u] => normalOrderedCurrentCoeff a (k + 3) u
  | [u, v] => p48qSecondNormal a k u v
  | _ => 0

/--
The established charged degree-two coefficient is the two-occurrence case of
the abstract recursion.  The mean is `-contraction`, while the scalar pair
covariance is the established diagonal correction.
-/
theorem p48q_degree_two_wick (a : Charge lattice) (k : ℤ) (u v : Cartan) :
    HVertexOperator.coeff
        (P48qChargedTwoCurrentIterate.stateField (chargedSecond a u v)) k =
      normalWickWord (Matrix.of (fun x y => P48qQuadraticStateField.correction x y))
        (fun x => -contraction a x) (p48qNormalWord a k) [u, v] := by
  rw [normalWick_two]
  simp only [p48qNormalWord, p48qSecondNormal, Matrix.of_apply, neg_smul, neg_mul,
    one_smul, neg_one_smul, smul_smul, smul_eq_mul]
  rw [P48qChargedTwoCurrentIterate.stateField_second_coeff]
  module

#print axioms normalWick_step
#print axioms p48q_degree_two_wick

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qArbitraryWickRecursion
