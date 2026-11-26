import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFirstOscillatorField

/-!
Linearity in each Cartan occurrence of the first-oscillator Wick field and
its agreement with the field on first-oscillator coordinate polynomials.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFirstOscillatorField

open LatticeGeneratingFieldLocality (Charge)
open P48qTwistedChargeAction (lattice)
open P48qThirdTwistedField (Cartan State)
open P48qTwistedHeisenberg (modeLinear)
open P48qSignedNormalWord (Indices insertMode_apply wordTerm wordTerm_finite
  normalOrderedCoeff wickCoeff)
open P48qArbitraryWickRecursion (normalWick normalWickWord normalWick_nil normalWick_step)
open P48qCurrentChargedIterate (contraction)
open P48qQuadraticStateField (correction)
open MvPolynomial (X)
open scoped BigOperators VertexOperator

open private wordTerm_cons from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSignedNormalWord

private def wordTermHeadLinear (a : Charge lattice) (k : ℤ) (tail : List Cartan)
    (p : ℤ × Indices tail.length) : Cartan →ₗ[ℂ] Module.End ℂ State :=
  let B := wordTerm a (k + 3 + p.1) tail p.2
  if p.1 < 0 then (LinearMap.mulRight ℂ B).comp (modeLinear p.1)
  else (LinearMap.mulLeft ℂ B).comp (modeLinear p.1)

private theorem wordTermHeadLinear_apply (a : Charge lattice) (k : ℤ) (tail : List Cartan)
    (p : ℤ × Indices tail.length) (u : Cartan) :
    wordTermHeadLinear a k tail p u = wordTerm a k (u :: tail) p := by
  rcases p with ⟨m, rest⟩
  rw [wordTerm_cons, insertMode_apply]
  by_cases hm : m < 0 <;> simp only [wordTermHeadLinear, hm, ite_true, ite_false,
    LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply] <;> rfl

/-- The signed normal-order sum is linear in the distinguished head occurrence. -/
def normalOrderedCoeffHeadLinear (a : Charge lattice) (k : ℤ) (tail : List Cartan) :
    Cartan →ₗ[ℂ] Module.End ℂ State where
  toFun u := normalOrderedCoeff a k (u :: tail)
  map_add' u v := by
    apply LinearMap.ext
    intro w
    change (∑ᶠ p : ℤ × Indices tail.length, wordTerm a k ((u + v) :: tail) p w) =
      (∑ᶠ p : ℤ × Indices tail.length, wordTerm a k (u :: tail) p w) +
      ∑ᶠ p : ℤ × Indices tail.length, wordTerm a k (v :: tail) p w
    calc
      _ = ∑ᶠ p : ℤ × Indices tail.length,
          (wordTerm a k (u :: tail) p w + wordTerm a k (v :: tail) p w) := by
        apply finsum_congr
        intro p
        simpa only [LinearMap.add_apply, wordTermHeadLinear_apply] using
          DFunLike.congr_fun ((wordTermHeadLinear a k tail p).map_add u v) w
      _ = _ := finsum_add_distrib (wordTerm_finite a k (u :: tail) w)
        (wordTerm_finite a k (v :: tail) w)
  map_smul' c u := by
    apply LinearMap.ext
    intro w
    change (∑ᶠ p : ℤ × Indices tail.length, wordTerm a k ((c • u) :: tail) p w) =
      c • ∑ᶠ p : ℤ × Indices tail.length, wordTerm a k (u :: tail) p w
    calc
      _ = ∑ᶠ p : ℤ × Indices tail.length, c • wordTerm a k (u :: tail) p w := by
        apply finsum_congr
        intro p
        simpa only [LinearMap.smul_apply, wordTermHeadLinear_apply] using
          DFunLike.congr_fun ((wordTermHeadLinear a k tail p).map_smul c u) w
      _ = _ := (smul_finsum' c (wordTerm_finite a k (u :: tail) w)).symm

-- Once the head is kept, recursion over the remaining occurrences leaves it in the prefix.
private theorem normalWick_kept_apply (A : Matrix Cartan Cartan ℂ) (μ : Cartan → ℂ)
    (normal : List Cartan → Module.End ℂ State)
    (linearNormal : List Cartan → Cartan →ₗ[ℂ] Module.End ℂ State)
    (hNormal : ∀ (u : Cartan) (kept : List Cartan), linearNormal kept u = normal (u :: kept))
    (pending kept : List Cartan) (u : Cartan) :
    normalWick A μ linearNormal pending kept u =
      normalWick A μ normal pending (u :: kept) := by
  cases pending with
  | nil => simpa only [normalWick_nil] using hNormal u kept
  | cons b tail =>
    rw [normalWick_step A μ linearNormal kept b tail,
      normalWick_step A μ normal (u :: kept) b tail]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, List.cons_append]
    rw [normalWick_kept_apply A μ normal linearNormal hNormal tail (kept ++ [b]) u,
      normalWick_kept_apply A μ normal linearNormal hNormal tail kept u]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [normalWick_kept_apply A μ normal linearNormal hNormal (tail.eraseIdx j) kept u]
termination_by pending.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals first | exact Nat.lt_succ_self _ | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

/-- The kept occurrence, singleton mean, and indexed pairings give a linear map in the head. -/
def wickCoeffHeadLinear (a : Charge lattice) (k : ℤ) (tail : List Cartan) :
    Cartan →ₗ[ℂ] Module.End ℂ State :=
  let A := Matrix.of fun u v => correction u v
  let μ : Cartan →ₗ[ℂ] ℂ := -contraction a
  let exponent (keptLength : ℕ) := k + 3 * (((tail.length + 1 : ℕ) : ℤ) - keptLength)
  let normal (kept : List Cartan) := normalOrderedCoeff a (exponent kept.length) kept
  let linearNormal (kept : List Cartan) :=
    normalOrderedCoeffHeadLinear a (exponent (kept.length + 1)) kept
  normalWick A μ linearNormal tail [] +
    μ.smulRight (normalWick A μ normal tail []) +
    ∑ j : Fin tail.length, (correction.flip (tail.get j)).smulRight
      (normalWick A μ normal (tail.eraseIdx j) [])

theorem wickCoeffHeadLinear_apply (a : Charge lattice) (k : ℤ) (tail : List Cartan) (u : Cartan) :
    wickCoeffHeadLinear a k tail u = wickCoeff a k (u :: tail) := by
  unfold wickCoeffHeadLinear wickCoeff normalWickWord
  dsimp only [List.length_cons]
  rw [normalWick_step]
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.neg_apply, LinearMap.BilinForm.flip_apply, Matrix.of_apply]
  rw [normalWick_kept_apply _ _
    (fun kept => normalOrderedCoeff a (k + 3 * (((tail.length + 1 : ℕ) : ℤ) - kept.length)) kept)
    _ (fun _ _ => rfl)]
  rfl

private def wordFieldHeadLinear (a : Charge lattice) (tail : List Cartan) :
    Cartan →ₗ[ℂ] VertexOperator ℂ State where
  toFun u := wordField a (u :: tail)
  map_add' u v := by
    apply HVertexOperator.coeff_inj
    funext k
    simp only [map_add, Pi.add_apply, wordField_coeff, ← wickCoeffHeadLinear_apply]
  map_smul' c u := by
    apply HVertexOperator.coeff_inj
    funext k
    simp only [RingHom.id_apply, map_smul, Pi.smul_apply, wordField_coeff,
      ← wickCoeffHeadLinear_apply]

private theorem sum_coordinateDirection (u : Cartan) :
    ∑ i : Coord, u i • coordinateDirection i = u := by
  classical
  apply funext
  intro j
  simp only [coordinateDirection, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem wordField_append_coordinate (a : Charge lattice) (pre : List Coord)
    (directions : List Cartan) :
    wordField a (pre.map coordinateDirection ++ directions) =
      polynomialField a (wordPolynomial pre * (directions.map directionPolynomial).prod) := by
  induction directions generalizing pre with
  | nil =>
    simpa only [List.append_nil, List.map_nil, List.prod_nil, mul_one] using
      (polynomialField_word a pre).symm
  | cons u tail ih =>
    let F := wordFieldHeadLinear a (pre.map coordinateDirection ++ tail)
    have move (v : Cartan) : wordField a (pre.map coordinateDirection ++ v :: tail) = F v :=
      wordField_perm a List.perm_middle
    calc
      _ = F u := move u
      _ = ∑ i : Coord, u i • F (coordinateDirection i) := by
        calc
          F u = F (∑ i : Coord, u i • coordinateDirection i) :=
            congrArg F (sum_coordinateDirection u).symm
          _ = _ := by simp only [map_sum, map_smul]
      _ = ∑ i : Coord, u i • polynomialField a
          (wordPolynomial (pre ++ [i]) * (tail.map directionPolynomial).prod) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← move]
        congr 1
        simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
          List.singleton_append] using ih (pre ++ [i])
      _ = _ := by
        simp only [wordPolynomial, directionPolynomial, List.map_append, List.prod_append,
          List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Finset.mul_sum,
          Finset.sum_mul, smul_mul_assoc, mul_smul_comm, map_sum, map_smul, mul_assoc]
        rfl

/-- The actual field of an arbitrary Cartan word is the field of its coordinate polynomial. -/
theorem wordField_eq_polynomialField (a : Charge lattice) (directions : List Cartan) :
    wordField a directions = polynomialField a (directions.map directionPolynomial).prod := by
  simpa only [List.map_nil, List.nil_append, wordPolynomial, List.prod_nil, one_mul] using
    wordField_append_coordinate a [] directions

/-- The coordinate-polynomial bridge holds on the actual first-oscillator source subspace. -/
theorem subspaceField_direction_word (a : Charge lattice) (directions : List Cartan) :
    subspaceField (sourceEquiv (Finsupp.single a (directions.map directionPolynomial).prod)) =
      wordField a directions := by
  rw [subspaceField_sourceEquiv, stateField_single, wordField_eq_polynomialField]

#print axioms normalOrderedCoeffHeadLinear
#print axioms wickCoeffHeadLinear_apply
#print axioms wordField_eq_polynomialField
#print axioms subspaceField_direction_word

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFirstOscillatorField
