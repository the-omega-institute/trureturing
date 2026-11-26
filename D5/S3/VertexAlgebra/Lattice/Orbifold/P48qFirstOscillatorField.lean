import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSignedNormalWord

/-!
Actual P48q twisted fields on all charge polynomials in the first oscillator
coordinates, with Wick coefficients in the cover coordinate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFirstOscillatorField

open LatticeGeneratingFieldLocality (Carrier Charge Oscillator)
open P48qTwistedChargeAction (lattice)
open P48qThirdTwistedField (Cartan State concreteChargedField fieldCoeff fixedDualBases)
open P48qArbitraryWickRecursion (normalWick normalWickWord normalWick_nil normalWick_step)
open P48qSignedNormalWord (normalOrderedCoeff normalOrderedCoeff_bddBelow
  normalOrderedCoeff_nil normalOrderedCoeff_singleton wickCoeff wickCoeff_perm wickCoeff_pair)
open P48qCurrentChargedIterate (chargedFirst contraction)
open P48qChargedTwoCurrentIterate (chargedSecond stateField_first)
open P48qQuadraticStateField (correction)
open MvPolynomial
open scoped BigOperators

open private currentPolynomial from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField

/-- A finite Wick recursion preserves pointwise lower truncation of its leaves. -/
private theorem normalWick_zero_below (A : Matrix Cartan Cartan ℂ) (μ : Cartan → ℂ)
    (normal : ℤ → List Cartan → Module.End ℂ State) (w : State)
    (leafBound : ∀ kept, ∃ b : ℤ, ∀ k < b, normal k kept w = 0)
    (pending kept : List Cartan) :
    ∃ b : ℤ, ∀ k < b, normalWick A μ (normal k) pending kept w = 0 := by
  classical
  cases pending with
  | nil => simpa only [normalWick_nil] using leafBound kept
  | cons u tail =>
    obtain ⟨keepBound, hKeep⟩ := normalWick_zero_below A μ normal w leafBound tail (kept ++ [u])
    obtain ⟨singleBound, hSingle⟩ := normalWick_zero_below A μ normal w leafBound tail kept
    have hPairs (j : Fin tail.length) :
        ∃ b : ℤ, ∀ k < b, normalWick A μ (normal k) (tail.eraseIdx j) kept w = 0 :=
      normalWick_zero_below A μ normal w leafBound (tail.eraseIdx j) kept
    choose pairBound hPair using hPairs
    let bounds := insert (min keepBound singleBound) (Finset.univ.image pairBound)
    let nonempty : bounds.Nonempty := Finset.insert_nonempty _ _
    refine ⟨bounds.min' nonempty, fun k hk => ?_⟩
    have hBase : k < min keepBound singleBound :=
      hk.trans_le (Finset.min'_le bounds _ (Finset.mem_insert_self _ _))
    have hPairSum :
        (∑ j : Fin tail.length,
          A u (tail.get j) • normalWick A μ (normal k) (tail.eraseIdx j) kept w) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hmem : pairBound j ∈ bounds :=
        Finset.mem_insert_of_mem (Finset.mem_image_of_mem pairBound hj)
      rw [hPair j k (hk.trans_le (Finset.min'_le bounds _ hmem)), smul_zero]
    simp only [normalWick_step A μ (normal k) kept u tail, LinearMap.add_apply,
      LinearMap.sum_apply, LinearMap.smul_apply,
      hKeep k (hBase.trans_le (min_le_left _ _)),
      hSingle k (hBase.trans_le (min_le_right _ _)), hPairSum, smul_zero, add_zero]
termination_by pending.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals first | exact Nat.lt_succ_self _ | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

/-- Every first-oscillator Wick word has a lower exponent bound on each input. -/
theorem wickCoeff_bddBelow (a : Charge lattice) (word : List Cartan) (w : State) :
    BddBelow (Function.support fun k => wickCoeff a k word w) := by
  let normal (k : ℤ) (kept : List Cartan) :=
    normalOrderedCoeff a (k + 3 * ((word.length : ℤ) - kept.length)) kept
  have leafBound (kept : List Cartan) : ∃ b : ℤ, ∀ k < b, normal k kept w = 0 := by
    obtain ⟨b, hb⟩ := normalOrderedCoeff_bddBelow a kept w
    refine ⟨b - 3 * ((word.length : ℤ) - kept.length), fun k hk => ?_⟩
    by_contra h
    exact (not_lt_of_ge (hb h)) (by omega)
  obtain ⟨b, hb⟩ := normalWick_zero_below (Matrix.of fun u v => correction u v)
    (fun u => -contraction a u) normal w leafBound word []
  exact ⟨b, fun k hk => le_of_not_gt fun h => hk (hb k h)⟩

/-- The charged field attached to an arbitrary first-oscillator word. -/
def wordField (a : Charge lattice) (word : List Cartan) : VertexOperator ℂ State :=
  VertexOperator.of_coeff (fun k => wickCoeff a k word) (wickCoeff_bddBelow a word)

theorem wordField_coeff (a : Charge lattice) (word : List Cartan) (k : ℤ) :
    HVertexOperator.coeff (wordField a word) k = wickCoeff a k word := rfl

theorem wordField_perm (a : Charge lattice) {left right : List Cartan} (h : left.Perm right) :
    wordField a left = wordField a right :=
  HVertexOperator.coeff_inj (funext fun k => wickCoeff_perm a k h)

abbrev Coord := Fin lattice.rank
abbrev FirstOscillatorPolynomial := MvPolynomial Coord ℂ
abbrev FirstOscillatorStates := Charge lattice →₀ FirstOscillatorPolynomial

/-- The Cartan direction associated with the source coordinate variable `i`. -/
def coordinateDirection (i : Coord) : Cartan := Pi.single i 1

/-- The variables are embedded as `(i, 0)`, the source's first oscillator. -/
def sourceInclusion : FirstOscillatorStates →ₗ[ℂ] Carrier lattice :=
  Finsupp.mapRange.linearMap (rename (fun i : Coord => (i, (0 : ℕ)))).toLinearMap

theorem sourceInclusion_injective : Function.Injective sourceInclusion :=
  Finsupp.mapRange_injective _ (map_zero (rename _))
    (rename_injective _ fun _ _ h => congrArg Prod.fst h)

theorem sourceInclusion_single (a : Charge lattice) (p : FirstOscillatorPolynomial) :
    sourceInclusion (Finsupp.single a p) =
      Finsupp.single a (rename (fun i : Coord => (i, (0 : ℕ))) p) := by
  simp [sourceInclusion, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]

/-- The full subspace of the lattice carrier with only first-mode variables at every charge. -/
def sourceSubspace : Submodule ℂ (Carrier lattice) := LinearMap.range sourceInclusion

def sourceEquiv : FirstOscillatorStates ≃ₗ[ℂ] sourceSubspace :=
  LinearEquiv.ofInjective sourceInclusion sourceInclusion_injective

@[simp] theorem sourceEquiv_coe (s : FirstOscillatorStates) :
    (sourceEquiv s : Carrier lattice) = sourceInclusion s := rfl

/-- Enumerate the variable occurrences of a monomial, including repetitions. -/
def occurrences (e : Coord →₀ ℕ) : List Coord := e.toMultiset.toList

/-- Extend the fields of coordinate monomials linearly within a charge. -/
def polynomialField (a : Charge lattice) : FirstOscillatorPolynomial →ₗ[ℂ] VertexOperator ℂ State :=
  (basisMonomials Coord ℂ).constr ℂ (fun e => wordField a ((occurrences e).map coordinateDirection))

/-- Extend the sector fields to finite sums over charges. -/
def stateField : FirstOscillatorStates →ₗ[ℂ] VertexOperator ℂ State :=
  Finsupp.lsum ℂ polynomialField

/-- The actual field on the first-oscillator subspace of the source carrier. -/
def subspaceField : sourceSubspace →ₗ[ℂ] VertexOperator ℂ State :=
  stateField.comp sourceEquiv.symm.toLinearMap

@[simp] theorem subspaceField_sourceEquiv (s : FirstOscillatorStates) :
    subspaceField (sourceEquiv s) = stateField s := by
  simp [subspaceField]

@[simp] theorem stateField_single (a : Charge lattice) (p : FirstOscillatorPolynomial) :
    stateField (Finsupp.single a p) = polynomialField a p :=
  Finsupp.lsum_single ℂ polynomialField a p

theorem polynomialField_monomial (a : Charge lattice) (e : Coord →₀ ℕ) :
    polynomialField a (monomial e 1) = wordField a ((occurrences e).map coordinateDirection) :=
  (basisMonomials Coord ℂ).constr_basis ℂ _ e

/-- The source polynomial represented by a list of coordinate occurrences. -/
def wordPolynomial (word : List Coord) : FirstOscillatorPolynomial :=
  (word.map X).prod

private theorem wordPolynomial_eq_monomial (word : List Coord) :
    wordPolynomial word = monomial (word : Multiset Coord).toFinsupp 1 := by
  induction word with
  | nil => simp [wordPolynomial, Multiset.toFinsupp_zero]
  | cons i tail ih =>
    change X i * wordPolynomial tail =
      monomial ((i :: tail : List Coord) : Multiset Coord).toFinsupp 1
    rw [show ((i :: tail : List Coord) : Multiset Coord) = (tail : Multiset Coord) + {i} by
      rw [add_comm, Multiset.singleton_add]
      rfl,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, monomial_add_single, pow_one, ih,
      mul_comm]

theorem polynomialField_word (a : Charge lattice) (word : List Coord) :
    polynomialField a (wordPolynomial word) = wordField a (word.map coordinateDirection) := by
  rw [wordPolynomial_eq_monomial, polynomialField_monomial]
  apply wordField_perm a
  apply List.Perm.map
  exact Multiset.coe_eq_coe.mp (by simp [occurrences])

/-- Exact cover coefficients for every coordinate word in every charge sector. -/
theorem subspaceField_word_coeff (a : Charge lattice) (word : List Coord) (k : ℤ) :
    HVertexOperator.coeff (subspaceField (sourceEquiv (Finsupp.single a (wordPolynomial word)))) k =
      wickCoeff a k (word.map coordinateDirection) := by
  rw [subspaceField_sourceEquiv, stateField_single, polynomialField_word, wordField_coeff]

theorem wordField_nil (a : Charge lattice) : wordField a [] = concreteChargedField a := by
  apply HVertexOperator.coeff_inj
  funext k
  rw [wordField_coeff, wickCoeff, normalWickWord, normalWick_nil]
  simp only [List.length_nil, Nat.cast_zero, sub_zero, mul_zero, add_zero]
  change normalOrderedCoeff a k [] = fieldCoeff fixedDualBases a k
  exact normalOrderedCoeff_nil a k

theorem wordField_singleton (a : Charge lattice) (u : Cartan) :
    wordField a [u] = P48qCurrentChargedIterate.stateField (chargedFirst a u) := by
  apply HVertexOperator.coeff_inj
  funext k
  rw [wordField_coeff, P48qCurrentChargedIterate.stateField_first_coeff, wickCoeff,
    normalWickWord, normalWick_step]
  simp [normalWick_nil, normalOrderedCoeff_singleton, normalOrderedCoeff_nil, sub_eq_add_neg]

theorem wordField_pair (a : Charge lattice) (u v : Cartan) :
    wordField a [u, v] = P48qChargedTwoCurrentIterate.stateField (chargedSecond a u v) :=
  HVertexOperator.coeff_inj (funext fun k => wickCoeff_pair a k u v)

private theorem currentPolynomial_coordinateDirection (i : Coord) :
    currentPolynomial (coordinateDirection i) = (X (i, 0) : Oscillator lattice) := by
  classical
  simp [currentPolynomial, coordinateDirection, Pi.single_apply, ite_smul]

theorem subspaceField_ground (a : Charge lattice) :
    subspaceField (sourceEquiv (Finsupp.single a 1)) = concreteChargedField a := by
  rw [subspaceField_sourceEquiv, stateField_single]
  change polynomialField a (wordPolynomial []) = _
  rw [polynomialField_word]
  exact wordField_nil a

theorem subspaceField_first (a : Charge lattice) (i : Coord) :
    subspaceField (sourceEquiv (Finsupp.single a (X i))) =
      P48qChargedTwoCurrentIterate.stateField (sourceInclusion (Finsupp.single a (X i))) := by
  rw [sourceInclusion_single, rename_X, subspaceField_sourceEquiv, stateField_single]
  have hSource : Finsupp.single a (X (i, 0) : Oscillator lattice) =
      chargedFirst a (coordinateDirection i) := by
    rw [chargedFirst, currentPolynomial_coordinateDirection]
  rw [hSource, stateField_first, ← wordField_singleton]
  simpa only [wordPolynomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    using polynomialField_word a [i]

theorem subspaceField_second (a : Charge lattice) (i j : Coord) :
    subspaceField (sourceEquiv (Finsupp.single a (X i * X j))) =
      P48qChargedTwoCurrentIterate.stateField (sourceInclusion (Finsupp.single a (X i * X j))) := by
  rw [sourceInclusion_single, map_mul, rename_X, rename_X,
    subspaceField_sourceEquiv, stateField_single]
  have hSource : Finsupp.single a (X (i, 0) * X (j, 0) : Oscillator lattice) =
      chargedSecond a (coordinateDirection i) (coordinateDirection j) := by
    simp only [chargedSecond, currentPolynomial_coordinateDirection]
  rw [hSource, ← wordField_pair]
  simpa only [wordPolynomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    using polynomialField_word a [i, j]

/-- The first-oscillator polynomial of an arbitrary Cartan direction. -/
def directionPolynomial (u : Cartan) : FirstOscillatorPolynomial := ∑ i, u i • X i

private theorem rename_directionPolynomial (u : Cartan) :
    rename (fun i : Coord => (i, (0 : ℕ))) (directionPolynomial u) = currentPolynomial u := by
  let R := rename (R := ℂ) (fun i : Coord => (i, (0 : ℕ)))
  change R.toLinearMap (∑ i : Coord, u i • X i) = currentPolynomial u
  simp only [map_sum, map_smul, AlgHom.toLinearMap_apply, R, rename_X, currentPolynomial]

/-- The linear extension agrees with the charged singleton field for all Cartan directions. -/
theorem subspaceField_direction (a : Charge lattice) (u : Cartan) :
    subspaceField (sourceEquiv (Finsupp.single a (directionPolynomial u))) = wordField a [u] := by
  let single : FirstOscillatorPolynomial →ₗ[ℂ] FirstOscillatorStates := Finsupp.lsingle a
  let F := subspaceField.comp (sourceEquiv.toLinearMap.comp single)
  let G := P48qChargedTwoCurrentIterate.stateField.comp (sourceInclusion.comp single)
  have hX (i : Coord) : F (X i) = G (X i) := subspaceField_first a i
  change F (directionPolynomial u) = _
  calc
    _ = G (directionPolynomial u) := by simp only [directionPolynomial, map_sum, map_smul, hX]
    _ = _ := by
      change P48qChargedTwoCurrentIterate.stateField
        (sourceInclusion (Finsupp.single a (directionPolynomial u))) = _
      rw [sourceInclusion_single, rename_directionPolynomial, ← chargedFirst,
        stateField_first, wordField_singleton]

/-- The linear extension agrees with the charged pair field for all Cartan directions. -/
theorem subspaceField_direction_pair (a : Charge lattice) (u v : Cartan) :
    subspaceField (sourceEquiv (Finsupp.single a (directionPolynomial u * directionPolynomial v))) =
      wordField a [u, v] := by
  let single : FirstOscillatorPolynomial →ₗ[ℂ] FirstOscillatorStates := Finsupp.lsingle a
  let F := subspaceField.comp (sourceEquiv.toLinearMap.comp single)
  let G := P48qChargedTwoCurrentIterate.stateField.comp (sourceInclusion.comp single)
  have hXX (i j : Coord) : F (X i * X j) = G (X i * X j) := subspaceField_second a i j
  change F (directionPolynomial u * directionPolynomial v) = _
  calc
    _ = G (directionPolynomial u * directionPolynomial v) := by
      simp only [directionPolynomial, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
        mul_smul_comm, map_sum, map_smul, hXX]
    _ = _ := by
      change P48qChargedTwoCurrentIterate.stateField
        (sourceInclusion (Finsupp.single a (directionPolynomial u * directionPolynomial v))) = _
      rw [sourceInclusion_single, map_mul, rename_directionPolynomial, rename_directionPolynomial,
        ← chargedSecond, wordField_pair]

#print axioms wickCoeff_bddBelow
#print axioms subspaceField_word_coeff
#print axioms subspaceField_ground
#print axioms subspaceField_direction
#print axioms subspaceField_direction_pair

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFirstOscillatorField
