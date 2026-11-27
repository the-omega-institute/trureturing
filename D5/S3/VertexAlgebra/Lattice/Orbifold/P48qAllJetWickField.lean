/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qAllJetWickField
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed normal-order Wick field for arbitrary finite words of current jets. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qJetContractions

/-!
The arbitrary-level P48q Wick field on finite words of current jets.

The scalar singleton and pair kernels are the checked jet contraction kernels.
The finite Wick recursion is kept separate from the checked all-level signed
normal order, and its leaves retain the total level shift of every contracted
jet.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qAllJetWickField

open LatticeGeneratingFieldLocality (Charge Carrier)
open P48qTwistedChargeAction (lattice)
open P48qThirdTwistedField (Cartan State chargeVector concreteChargedField)
open P48qTwistedHeisenberg (projectAt)
open P48qArbitraryWickRecursion (normalWick normalWickWord normalWick_nil
  normalWick_step normalWick_perm)
open P48qJetNormalOrdering (Jet normalOrderedCoeff normalOrderedCoeff_bddBelow
  normalOrderedField)
open P48qJetContractions (pairJetCoeff pairJetCoeff_swap)
open P48qCurrentChargedIterate (contraction contraction_apply)
open ThirdEigenspacePairing (p48qForm)
open MvPolynomial

open private formSymmetric from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

abbrev Jet := P48qJetNormalOrdering.Jet

/- The total positive source level of a finite jet word. -/
def totalLevel : List Jet → ℕ
  | [] => 0
  | p :: tail => (p.2 : ℕ) + totalLevel tail

theorem totalLevel_perm {left right : List Jet} (h : left.Perm right) :
    totalLevel left = totalLevel right := by
  induction h with
  | nil => rfl
  | cons p _ ih => simp [totalLevel, ih]
  | swap p q tail => simp [totalLevel, Nat.add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/- The scalar singleton kernel on the three order-three projections. -/
def singletonWeight (a : Charge lattice) (p : Jet) : ℂ :=
  ∑ r ∈ Finset.range 3,
    Ring.choose (-((r : ℂ) / 3)) (p.2 : ℕ) *
      p48qForm (projectAt r p.1) (chargeVector a)

/- The scalar pair kernel on opposite moving projections. -/
def pairWeight (p q : Jet) : ℂ :=
  pairJetCoeff ((1 : ℂ) / 3) (p.2 : ℕ) (q.2 : ℕ) *
      p48qForm (projectAt 1 p.1) (projectAt 2 q.1) +
    pairJetCoeff ((2 : ℂ) / 3) (p.2 : ℕ) (q.2 : ℕ) *
      p48qForm (projectAt 2 p.1) (projectAt 1 q.1)

theorem singletonWeight_first (a : Charge lattice) (u : Cartan) :
    singletonWeight a (u, (1 : ℕ+)) = -contraction a u := by
  simp [singletonWeight, contraction_apply, Finset.sum_range_succ]

theorem pairWeight_swap (p q : Jet) :
    pairWeight p q = pairWeight q p := by
  unfold pairWeight
  have h₁ : p48qForm (projectAt 1 p.1) (projectAt 2 q.1) =
      p48qForm (projectAt 2 q.1) (projectAt 1 p.1) :=
    formSymmetric.eq _ _
  have h₂ : p48qForm (projectAt 2 p.1) (projectAt 1 q.1) =
      p48qForm (projectAt 1 q.1) (projectAt 2 p.1) :=
    formSymmetric.eq _ _
  have hc₁ := pairJetCoeff_swap ((1 : ℂ) / 3) (p.2 : ℕ) (q.2 : ℕ)
    p.2.pos q.2.pos
  have hc₂ := pairJetCoeff_swap ((2 : ℂ) / 3) (p.2 : ℕ) (q.2 : ℕ)
    p.2.pos q.2.pos
  rw [hc₁, hc₂, h₁, h₂]
  norm_num [show 1 - (1 : ℂ) / 3 = (2 : ℂ) / 3 by ring,
    show 1 - (2 : ℂ) / 3 = (1 : ℂ) / 3 by ring]
  ring

/- The exponent shift carried by a Wick leaf after contractions. -/
def leafShift (input kept : List Jet) : ℤ :=
  3 * ((totalLevel input : ℤ) - (totalLevel kept : ℤ))

def allJetCoeff (a : Charge lattice) (k : ℤ) (jets : List Jet) :
    Module.End ℂ State :=
  normalWickWord (Matrix.of fun p q => pairWeight p q)
    (fun p => singletonWeight a p)
    (fun kept => normalOrderedCoeff a (k + leafShift jets kept) kept) jets

theorem allJetCoeff_perm (a : Charge lattice) (k : ℤ)
    {left right : List Jet} (h : left.Perm right) :
    allJetCoeff a k left = allJetCoeff a k right := by
  unfold allJetCoeff normalWickWord
  have hlevel : totalLevel left = totalLevel right := totalLevel_perm h
  simp only [leafShift, hlevel]
  apply normalWick_perm
  · intro p q
    exact pairWeight_swap p q
  · intro xs ys hs
    have hxs : totalLevel xs = totalLevel ys := totalLevel_perm hs
    simp only [hxs]
    exact P48qJetNormalOrdering.normalOrderedCoeff_perm a _ hs
  · exact h

private theorem normalWick_zero_below (A : Matrix Jet Jet ℂ) (μ : Jet → ℂ)
    (normal : ℤ → List Jet → Module.End ℂ State) (w : State)
    (leafBound : ∀ kept, ∃ b : ℤ, ∀ k < b, normal k kept w = 0)
    (pending kept : List Jet) :
    ∃ b : ℤ, ∀ k < b, normalWick A μ (normal k) pending kept w = 0 := by
  classical
  cases pending with
  | nil => simpa only [normalWick_nil] using leafBound kept
  | cons p tail =>
    obtain ⟨keepBound, hKeep⟩ :=
      normalWick_zero_below A μ normal w leafBound tail (kept ++ [p])
    obtain ⟨singleBound, hSingle⟩ :=
      normalWick_zero_below A μ normal w leafBound tail kept
    have hPairs (j : Fin tail.length) :
        ∃ b : ℤ, ∀ k < b,
          normalWick A μ (normal k) (tail.eraseIdx j) kept w = 0 :=
      normalWick_zero_below A μ normal w leafBound (tail.eraseIdx j) kept
    choose pairBound hPair using hPairs
    let bounds := insert (min keepBound singleBound) (Finset.univ.image pairBound)
    refine ⟨bounds.min' (Finset.insert_nonempty _ _), fun k hk => ?_⟩
    have hBase : k < min keepBound singleBound :=
      hk.trans_le (Finset.min'_le bounds _ (Finset.mem_insert_self _ _))
    have hPairSum :
        (∑ j : Fin tail.length,
          A p (tail.get j) • normalWick A μ (normal k)
            (tail.eraseIdx j) kept w) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hmem : pairBound j ∈ bounds :=
        Finset.mem_insert_of_mem (Finset.mem_image_of_mem pairBound hj)
      rw [hPair j k (hk.trans_le (Finset.min'_le bounds _ hmem)), smul_zero]
    simp only [normalWick_step A μ (normal k) kept p tail,
      LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      hKeep k (hBase.trans_le (min_le_left _ _)),
      hSingle k (hBase.trans_le (min_le_right _ _)), hPairSum,
      smul_zero, add_zero]
termination_by pending.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals first | exact Nat.lt_succ_self _ | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

theorem allJetCoeff_bddBelow (a : Charge lattice) (jets : List Jet) (w : State) :
    BddBelow (Function.support fun k => allJetCoeff a k jets w) := by
  let normal (k : ℤ) (kept : List Jet) :=
    normalOrderedCoeff a (k + leafShift jets kept) kept
  have leafBound (kept : List Jet) : ∃ b : ℤ, ∀ k < b, normal k kept w = 0 := by
    obtain ⟨b, hb⟩ := normalOrderedCoeff_bddBelow a kept w
    refine ⟨b - leafShift jets kept, fun k hk => ?_⟩
    by_contra h
    exact (not_lt_of_ge (hb h)) (by dsimp [normal, leafShift] at *; omega)
  obtain ⟨b, hb⟩ := normalWick_zero_below
    (Matrix.of fun p q => pairWeight p q) (fun p => singletonWeight a p)
    normal w leafBound jets []
  exact ⟨b, fun k hk => le_of_not_gt fun h => hk (hb k h)⟩

def allJetField (a : Charge lattice) (jets : List Jet) : VertexOperator ℂ State :=
  VertexOperator.of_coeff (fun k => allJetCoeff a k jets)
    (allJetCoeff_bddBelow a jets)

theorem allJetField_coeff (a : Charge lattice) (jets : List Jet) (k : ℤ) :
    HVertexOperator.coeff (allJetField a jets) k = allJetCoeff a k jets := rfl

theorem allJetField_perm (a : Charge lattice) {left right : List Jet}
    (h : left.Perm right) : allJetField a left = allJetField a right :=
  HVertexOperator.coeff_inj (funext fun k => allJetCoeff_perm a k h)

theorem allJetField_nil (a : Charge lattice) :
    allJetField a [] = concreteChargedField a := by
  apply HVertexOperator.coeff_inj
  funext k
  change allJetCoeff a k [] = HVertexOperator.coeff (concreteChargedField a) k
  rw [allJetCoeff, normalWickWord, normalWick_nil]
  change normalOrderedCoeff a (k + leafShift [] []) [] = _
  have hzero : k + leafShift [] [] = k := by
    simp [leafShift]
  rw [hzero]
  rw [← P48qJetNormalOrdering.normalOrderedField_coeff a [] k,
    P48qJetNormalOrdering.normalOrderedField_nil]

abbrev NativeIndex := LatticeGeneratingFieldLocality.Index lattice
abbrev NativePolynomial := LatticeGeneratingFieldLocality.Oscillator lattice
abbrev NativeStates := Carrier lattice

def oscillatorJet (j : NativeIndex) : Jet :=
  (Pi.single j.1 1, ⟨j.2 + 1, Nat.succ_pos j.2⟩)

def oscillatorOccurrences (e : NativeIndex →₀ ℕ) : List NativeIndex :=
  e.toMultiset.toList

def nativePolynomialField (a : Charge lattice) :
    NativePolynomial →ₗ[ℂ] VertexOperator ℂ State :=
  (basisMonomials NativeIndex ℂ).constr ℂ (fun e =>
    allJetField a ((oscillatorOccurrences e).map oscillatorJet))

def nativeField : NativeStates →ₗ[ℂ] VertexOperator ℂ State :=
  Finsupp.lsum ℂ nativePolynomialField

theorem nativePolynomialField_monomial (a : Charge lattice)
    (e : NativeIndex →₀ ℕ) :
    nativePolynomialField a (monomial e 1) =
      allJetField a ((oscillatorOccurrences e).map oscillatorJet) :=
  (basisMonomials NativeIndex ℂ).constr_basis ℂ _ e

def nativeWordPolynomial (word : List NativeIndex) : NativePolynomial :=
  (word.map X).prod

private theorem nativeWordPolynomial_eq_monomial (word : List NativeIndex) :
    nativeWordPolynomial word = monomial (word : Multiset NativeIndex).toFinsupp 1 := by
  induction word with
  | nil => simp [nativeWordPolynomial, Multiset.toFinsupp_zero]
  | cons j tail ih =>
    change X j * nativeWordPolynomial tail =
      monomial ((j :: tail : List NativeIndex) : Multiset NativeIndex).toFinsupp 1
    rw [show ((j :: tail : List NativeIndex) : Multiset NativeIndex) =
      (tail : Multiset NativeIndex) + {j} by
        rw [add_comm, Multiset.singleton_add]
        rfl,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, monomial_add_single,
      pow_one, ih, mul_comm]

theorem nativePolynomialField_word (a : Charge lattice)
    (word : List NativeIndex) :
    nativePolynomialField a (nativeWordPolynomial word) =
      allJetField a (word.map oscillatorJet) := by
  rw [nativeWordPolynomial_eq_monomial, nativePolynomialField_monomial]
  apply allJetField_perm a
  apply List.Perm.map
  exact Multiset.coe_eq_coe.mp (by simp [oscillatorOccurrences])

theorem nativeField_word (a : Charge lattice) (word : List NativeIndex) :
    nativeField (Finsupp.single a (nativeWordPolynomial word)) =
      allJetField a (word.map oscillatorJet) := by
  rw [nativeField, Finsupp.lsum_single, nativePolynomialField_word]

theorem nativeField_ground (a : Charge lattice) :
    nativeField (Finsupp.single a 1) = concreteChargedField a := by
  have hword := nativeField_word a ([] : List NativeIndex)
  simpa only [nativeWordPolynomial, List.map_nil, List.prod_nil, allJetField_nil] using hword

theorem nativeField_coordinate (a : Charge lattice) (i : Fin lattice.rank)
    (n : ℕ) :
    nativeField (Finsupp.single a (MvPolynomial.X (i, n))) =
      allJetField a [oscillatorJet (i, n)] := by
  simpa only [nativeWordPolynomial, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] using nativeField_word a [(i, n)]

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qAllJetWickField
