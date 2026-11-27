/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qSignedNormalWord
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed normal-order coefficients and support for arbitrary first-current words. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qWickPermutation

/-!
The normal-order summands for arbitrary finite words of first oscillator
directions in the order-three P48q twist, in the cover coordinate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSignedNormalWord

open LatticeGeneratingFieldLocality (Charge)
open P48qTwistedChargeAction (lattice)
open P48qThirdTwistedField (Cartan State fieldCoeff fixedDualBases concreteChargedField
  lowerBound fieldCoeff_eq_zero_below)
open P48qTwistedHeisenberg (mode mode_eq_zero_above_coverBound)
open P48qFixedCurrentIterate (coverBound)
open scoped BigOperators VertexOperator

open private mode_mul_comm_of_sign from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField
open private place place_apply firstTerm_eq_place from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedTwoCurrentIterate

/-- Insert an actual signed cover mode on the appropriate side of a coefficient. -/
def insertMode (p : Cartan × ℤ) : Module.End ℂ (Module.End ℂ State) :=
  place p.1 p.2

theorem insertMode_apply (u : Cartan) (m : ℤ) (B : Module.End ℂ State) :
    insertMode (u, m) B = if m < 0 then mode u m * B else B * mode u m :=
  place_apply u m B

/-- Same-sign modes commute on their side. Opposite sides commute by associativity. -/
theorem insertMode_commute (p q : Cartan × ℤ) :
    Commute (insertMode p) (insertMode q) := by
  rcases p with ⟨u, m⟩
  rcases q with ⟨v, n⟩
  apply LinearMap.ext
  intro B
  simp only [Module.End.mul_apply, insertMode_apply]
  by_cases hm : m < 0 <;> by_cases hn : n < 0
  · simp only [hm, hn, ite_true, ← mul_assoc]
    rw [mode_mul_comm_of_sign u v m n (Or.inl ⟨hm, hn⟩)]
  · simp only [hm, hn, ite_true, ite_false, mul_assoc]
  · simp only [hm, hn, ite_true, ite_false, mul_assoc]
  · simp only [hm, hn, ite_false, mul_assoc]
    rw [mode_mul_comm_of_sign v u n m (Or.inr ⟨le_of_not_gt hn, le_of_not_gt hm⟩)]

/-- One actual normal-order summand. A cover mode m contributes exponent -m-3. -/
def signedWordCoeff (a : Charge lattice) (k : ℤ) (word : List (Cartan × ℤ)) :
    Module.End ℂ State :=
  word.foldr (fun p B => insertMode p B)
    (HVertexOperator.coeff (concreteChargedField a) (k + (word.map (fun p => p.2 + 3)).sum))

theorem signedWordCoeff_perm (a : Charge lattice) (k : ℤ)
    {left right : List (Cartan × ℤ)} (h : left.Perm right) :
    signedWordCoeff a k left = signedWordCoeff a k right := by
  have : LeftCommutative (fun p B => insertMode p B) :=
    ⟨fun p q B => DFunLike.congr_fun (insertMode_commute p q).eq B⟩
  unfold signedWordCoeff
  rw [(h.map (fun p => p.2 + 3)).sum_eq]
  exact h.foldr_eq (f := fun p B => insertMode p B) _

private theorem signedWordCoeff_cons (a : Charge lattice) (k : ℤ)
    (u : Cartan) (m : ℤ) (tail : List (Cartan × ℤ)) :
    signedWordCoeff a k ((u, m) :: tail) =
      insertMode (u, m) (signedWordCoeff a (k + 3 + m) tail) := by
  simp only [signedWordCoeff, List.foldr_cons, List.map_cons, List.sum_cons]
  rw [show k + (m + 3 + (List.map (fun p : Cartan × ℤ => p.2 + 3) tail).sum) =
    k + 3 + m + (List.map (fun p : Cartan × ℤ => p.2 + 3) tail).sum by omega]

theorem signedWordCoeff_nil (a : Charge lattice) (k : ℤ) :
    signedWordCoeff a k [] = fieldCoeff fixedDualBases a k := by
  simp only [signedWordCoeff, List.map_nil, List.sum_nil, add_zero, List.foldr_nil]
  rfl

theorem signedWordCoeff_singleton (a : Charge lattice) (k : ℤ) (u : Cartan) (m : ℤ) :
    signedWordCoeff a k [(u, m)] = P48qCurrentChargedIterate.orderedTerm a k m u := by
  rw [signedWordCoeff_cons, signedWordCoeff_nil, firstTerm_eq_place]
  rfl

/-- One signed cover index per occurrence, including repeated directions. -/
def Indices : ℕ → Type
  | 0 => Unit
  | n + 1 => ℤ × Indices n

/-- Attach the cover indices to the first oscillator directions in occurrence order. -/
def occurrences : (directions : List Cartan) → Indices directions.length → List (Cartan × ℤ)
  | [], _ => []
  | u :: tail, (m, rest) => (u, m) :: occurrences tail rest

/-- The summand for a fixed assignment of cover indices. -/
def wordTerm (a : Charge lattice) (k : ℤ) (directions : List Cartan)
    (indices : Indices directions.length) : Module.End ℂ State :=
  signedWordCoeff a k (occurrences directions indices)

private theorem wordTerm_cons (a : Charge lattice) (k : ℤ) (u : Cartan)
    (tail : List Cartan) (m : ℤ) (rest : Indices tail.length) :
    wordTerm a k (u :: tail) (m, rest) =
      insertMode (u, m) (wordTerm a (k + 3 + m) tail rest) :=
  signedWordCoeff_cons a k u m _

private def nonnegativeIndices (w : State) : Finset ℤ :=
  Finset.Icc 0 (coverBound w : ℤ)

/-- A common lower exponent bound for every mode assignment on a fixed input. -/
private def wordLower (a : Charge lattice) : List Cartan → State → ℤ
  | [], w => lowerBound a w
  | u :: tail, w =>
    let bounds := (nonnegativeIndices w).image fun m =>
      wordLower a tail (mode u m w) - 3 - m
    (insert (wordLower a tail w - 3) bounds).min' (Finset.insert_nonempty _ _)

private theorem wordTerm_zero_below (a : Charge lattice) (directions : List Cartan)
    (w : State) (k : ℤ) (indices : Indices directions.length)
    (hk : k < wordLower a directions w) : wordTerm a k directions indices w = 0 := by
  induction directions generalizing w k with
  | nil =>
    change k < lowerBound a w at hk
    change signedWordCoeff a k [] w = 0
    rw [signedWordCoeff_nil, fieldCoeff_eq_zero_below fixedDualBases a w k hk]
  | cons u tail ih =>
    rcases indices with ⟨m, rest⟩
    rw [wordTerm_cons, insertMode_apply]
    dsimp only [wordLower] at hk
    by_cases hm : m < 0
    · have hlow := hk.trans_le (Finset.min'_le _ _ (Finset.mem_insert_self _ _))
      rw [ite_eq_left hm, Module.End.mul_apply, ih w (k + 3 + m) rest (by omega), map_zero]
    · rw [ite_eq_right hm, Module.End.mul_apply]
      by_cases hb : (coverBound w : ℤ) < m
      · rw [mode_eq_zero_above_coverBound w u m hb, map_zero]
      · have hmem : m ∈ nonnegativeIndices w :=
          Finset.mem_Icc.mpr ⟨le_of_not_gt hm, le_of_not_gt hb⟩
        have hlow := hk.trans_le (Finset.min'_le _ _
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hmem)))
        exact ih (mode u m w) (k + 3 + m) rest (by omega)

private theorem wordTerm_firstIndex (a : Charge lattice) (k : ℤ) (u : Cartan)
    (tail : List Cartan) (w : State) (m : ℤ) (rest : Indices tail.length)
    (h : wordTerm a k (u :: tail) (m, rest) w ≠ 0) :
    m ∈ Finset.Icc (min 0 (wordLower a tail w - k - 3)) (coverBound w : ℤ) := by
  apply Finset.mem_Icc.mpr
  constructor
  · apply le_of_not_gt
    intro hm
    have hneg := hm.trans_le (min_le_left _ _)
    have hlow := hm.trans_le (min_le_right _ _)
    exact h (by rw [wordTerm_cons, insertMode_apply, ite_eq_left hneg, Module.End.mul_apply,
      wordTerm_zero_below a tail w _ rest (by omega), map_zero])
  · apply le_of_not_gt
    intro hm
    exact h (by rw [wordTerm_cons, insertMode_apply, ite_eq_right (by omega : ¬ m < 0),
      Module.End.mul_apply, mode_eq_zero_above_coverBound w u m hm, map_zero])

/-- At fixed cover exponent and input, only finitely many index tuples contribute.
Positive modes truncate by the Fock-variable cutoff. The negative cutoff uses a
common charged lower bound over the finitely many possible right-mode inputs. -/
theorem wordTerm_finite (a : Charge lattice) (k : ℤ) (directions : List Cartan) (w : State) :
    Function.HasFiniteSupport (fun indices => wordTerm a k directions indices w) := by
  induction directions generalizing k w with
  | nil =>
    change (Function.support (fun indices : Unit => wordTerm a k [] indices w)).Finite
    exact Set.toFinite _
  | cons u tail ih =>
    let cut := Finset.Icc (min 0 (wordLower a tail w - k - 3)) (coverBound w : ℤ)
    let rows (m : ℤ) :=
      Function.support (fun rest => wordTerm a k (u :: tail) (m, rest) w)
    have hrow (m : ℤ) : (rows m).Finite := by
      by_cases hm : m < 0
      · refine (ih (k + 3 + m) w).subset ?_
        intro rest h
        change wordTerm a (k + 3 + m) tail rest w ≠ 0
        intro hz
        apply h
        change wordTerm a k (u :: tail) (m, rest) w = 0
        rw [wordTerm_cons, insertMode_apply, ite_eq_left hm, Module.End.mul_apply, hz, map_zero]
      · apply (ih (k + 3 + m) (mode u m w)).subset
        intro rest h
        simpa only [rows, Function.mem_support, wordTerm_cons, insertMode_apply,
          ite_eq_right hm, Module.End.mul_apply] using h
    refine ((Finset.finite_toSet cut).biUnion
      (t := fun m => Prod.mk m '' rows m) (fun m _ => (hrow m).image _)).subset ?_
    rintro ⟨m, rest⟩ h
    exact Set.mem_iUnion₂.mpr ⟨m, wordTerm_firstIndex a k u tail w m rest h, rest, h, rfl⟩

/-- The actual normal-order coefficient, summed pointwise on the twisted state. -/
def normalOrderedCoeff (a : Charge lattice) (k : ℤ) (directions : List Cartan) :
    Module.End ℂ State where
  toFun w := ∑ᶠ indices, wordTerm a k directions indices w
  map_add' w v := by
    simp only [map_add]
    exact finsum_add_distrib (wordTerm_finite a k directions w) (wordTerm_finite a k directions v)
  map_smul' c w := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' c (wordTerm_finite a k directions w)).symm

/-- Each coefficient is lower truncated on each input state. -/
theorem normalOrderedCoeff_bddBelow (a : Charge lattice) (directions : List Cartan) (w : State) :
    BddBelow (Function.support fun k => normalOrderedCoeff a k directions w) := by
  refine ⟨wordLower a directions w, ?_⟩
  intro k hk
  apply le_of_not_gt
  intro h
  apply hk
  exact finsum_eq_zero_of_forall_eq_zero fun indices =>
    wordTerm_zero_below a directions w k indices h

theorem normalOrderedCoeff_cons_apply (a : Charge lattice) (k : ℤ) (u : Cartan)
    (tail : List Cartan) (w : State) :
    normalOrderedCoeff a k (u :: tail) w =
      ∑ᶠ m : ℤ, insertMode (u, m) (normalOrderedCoeff a (k + 3 + m) tail) w := by
  change (∑ᶠ p : ℤ × Indices tail.length, wordTerm a k (u :: tail) p w) = _
  rw [finsum_curry _ (wordTerm_finite a k (u :: tail) w)]
  apply finsum_congr
  intro m
  simp only [wordTerm_cons, insertMode_apply]
  by_cases hm : m < 0
  · simp only [ite_eq_left hm, Module.End.mul_apply]
    exact (map_finsum (mode u m) (wordTerm_finite a (k + 3 + m) tail w)).symm
  · simp only [ite_eq_right hm, Module.End.mul_apply]
    rfl

theorem normalOrderedCoeff_nil (a : Charge lattice) (k : ℤ) :
    normalOrderedCoeff a k [] = fieldCoeff fixedDualBases a k := by
  apply LinearMap.ext
  intro w
  change (∑ᶠ _ : Unit, signedWordCoeff a k [] w) = _
  simp [signedWordCoeff_nil, finsum_eq_sum_of_fintype]

theorem normalOrderedCoeff_singleton (a : Charge lattice) (k : ℤ) (u : Cartan) :
    normalOrderedCoeff a k [u] = P48qCurrentChargedIterate.normalOrderedCurrentCoeff a k u := by
  apply LinearMap.ext
  intro w
  rw [normalOrderedCoeff_cons_apply, P48qCurrentChargedIterate.normalOrderedCurrentCoeff]
  apply finsum_congr
  intro m
  rw [normalOrderedCoeff_nil, firstTerm_eq_place]
  rfl

theorem normalOrderedCoeff_pair (a : Charge lattice) (k : ℤ) (u v : Cartan) :
    normalOrderedCoeff a k [u, v] =
      P48qChargedTwoCurrentIterate.normalOrderedSecondCoeff a k u v := by
  apply LinearMap.ext
  intro w
  rw [normalOrderedCoeff_cons_apply, P48qChargedTwoCurrentIterate.normalOrderedSecondCoeff]
  apply finsum_congr
  intro m
  rw [normalOrderedCoeff_singleton]
  rfl

/-- Reindexing the pointwise finite sum preserves the normal-order coefficient. -/
theorem normalOrderedCoeff_perm (a : Charge lattice) (k : ℤ)
    {left right : List Cartan} (h : left.Perm right) :
    normalOrderedCoeff a k left = normalOrderedCoeff a k right := by
  induction h generalizing k with
  | nil => rfl
  | cons u h ih =>
    apply LinearMap.ext
    intro w
    simp only [normalOrderedCoeff_cons_apply, ih]
  | swap u v tail =>
    apply LinearMap.ext
    intro w
    let swapIndices (p : ℤ × ℤ × Indices tail.length) := (p.2.1, p.1, p.2.2)
    change (∑ᶠ p : ℤ × ℤ × Indices tail.length, wordTerm a k (v :: u :: tail) p w) =
      ∑ᶠ p : ℤ × ℤ × Indices tail.length, wordTerm a k (u :: v :: tail) p w
    apply finsum_eq_of_bijective swapIndices
      (Function.Involutive.bijective (fun _ => rfl))
    rintro ⟨m, n, rest⟩
    exact DFunLike.congr_fun (signedWordCoeff_perm a k
      (List.Perm.swap (u, n) (v, m) (occurrences tail rest))) w
  | trans _ _ ih₁ ih₂ => exact (ih₁ k).trans (ih₂ k)

open P48qArbitraryWickRecursion (normalWickWord normalWick_perm normalWick_two)
open P48qCurrentChargedIterate (contraction)
open P48qQuadraticStateField (correction correction_swap)

/-- The Wick coefficient for a finite word of first directions. Each contracted
occurrence removes a current, contributing a cover exponent of -3. -/
def wickCoeff (a : Charge lattice) (k : ℤ) (directions : List Cartan) :
    Module.End ℂ State :=
  normalWickWord (Matrix.of fun u v => correction u v) (fun u => -contraction a u)
    (fun kept => normalOrderedCoeff a (k + 3 * ((directions.length : ℤ) - kept.length)) kept)
    directions

theorem wickCoeff_perm (a : Charge lattice) (k : ℤ)
    {left right : List Cartan} (h : left.Perm right) :
    wickCoeff a k left = wickCoeff a k right := by
  unfold wickCoeff normalWickWord
  rw [h.length_eq]
  refine normalWick_perm _ _ _ correction_swap ?_ h []
  intro xs ys hs
  rw [hs.length_eq]
  exact normalOrderedCoeff_perm a _ hs

/-- At degree two the Wick coefficient recovers the established charged field. -/
theorem wickCoeff_pair (a : Charge lattice) (k : ℤ) (u v : Cartan) :
    wickCoeff a k [u, v] =
      HVertexOperator.coeff
        (P48qChargedTwoCurrentIterate.stateField (P48qChargedTwoCurrentIterate.chargedSecond a u v))
        k := by
  rw [wickCoeff, normalWick_two]
  change normalOrderedCoeff a (k + 3 * (2 - 2)) [u, v] +
    (-contraction a v) • normalOrderedCoeff a (k + 3 * (2 - 1)) [u] +
    (-contraction a u) • normalOrderedCoeff a (k + 3 * (2 - 1)) [v] +
    ((-contraction a u) * (-contraction a v) + correction u v) •
      normalOrderedCoeff a (k + 3 * (2 - 0)) [] = _
  rw [P48qChargedTwoCurrentIterate.stateField_second_coeff]
  simp only [show (3 : ℤ) * (2 - 2) = 0 by decide,
    show (3 : ℤ) * (2 - 1) = 3 by decide, show (3 : ℤ) * (2 - 0) = 6 by decide,
    add_zero, normalOrderedCoeff_pair, normalOrderedCoeff_singleton, normalOrderedCoeff_nil,
    neg_mul_neg, neg_smul, sub_eq_add_neg]
  rw [add_comm (contraction a u * contraction a v) (correction u v)]
  ac_rfl

#print axioms insertMode_commute
#print axioms signedWordCoeff_perm
#print axioms wordTerm_finite
#print axioms normalOrderedCoeff_bddBelow
#print axioms normalOrderedCoeff_pair
#print axioms normalOrderedCoeff_perm
#print axioms wickCoeff_perm
#print axioms wickCoeff_pair

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSignedNormalWord
