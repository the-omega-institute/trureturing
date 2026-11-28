/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qJetNormalOrdering
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hasse-weighted signed normal ordering for arbitrary positive-level jets. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qHigherCurrentIterate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSignedNormalWord

/-!
Normal ordering of all positive-level current jets against the concrete charged
P48q field. Each slot contributes its Hasse derivative in the physical
coordinate. Scalar and pair contractions belong to the twisted iterate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qJetNormalOrdering

open LatticeGeneratingFieldLocality (Charge)
open P48qTwistedChargeAction (lattice)
open P48qThirdTwistedField (Cartan State concreteChargedField lowerBound)
open P48qTwistedHeisenberg (mode modeLinear mode_projectAt currentField_coeff)
open P48qFixedCurrentIterate (coverBound)
open P48qSignedNormalWord (Indices insertMode insertMode_apply insertMode_commute wordTerm
  wordTerm_finite signedWordCoeff_nil)
open P48qCurrentChargedIterate (orderedTerm orderedTerm_fields orderedTerm_support)
open P48qHigherCurrentIterate (signedStripIndex hasseWeight higherNormalTerm higherNormalCoeff)
open ThirdEigenspacePairing (p48qAction)
open scoped BigOperators VertexOperator

open private wordTerm_cons wordLower wordTerm_zero_below wordTerm_firstIndex from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSignedNormalWord
open private projectAt_off_residue from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

/-- A current direction and its positive source oscillator level. -/
abbrev Jet := Cartan × ℕ+

/-- The Hasse weight for the `(d - 1)`st derivative of `z^(-m/3-1)`. -/
def jetWeight (d : ℕ+) (m : ℤ) : ℂ :=
  Ring.choose (-(m : ℂ) / 3 - 1) ((d : ℕ) - 1)

/-- Relative to first oscillators, each jet shifts the requested exponent by `3(d-1)`. -/
def coverShift (jets : List Jet) : ℤ :=
  (jets.map fun p => 3 * (((p.2 : ℕ) - 1 : ℕ) : ℤ)).sum

private def weightProduct : (jets : List Jet) → Indices (jets.map Prod.fst).length → ℂ
  | [], _ => 1
  | p :: tail, (m, rest) => jetWeight p.2 m * weightProduct tail rest

/-- One normal-order summand, with an independent signed mode for each labelled slot. -/
def jetTerm (a : Charge lattice) (k : ℤ) (jets : List Jet)
    (indices : Indices (jets.map Prod.fst).length) : Module.End ℂ State :=
  weightProduct jets indices • wordTerm a (k + coverShift jets) (jets.map Prod.fst) indices

private theorem coverShift_cons (p : Jet) (tail : List Jet) :
    coverShift (p :: tail) + 3 = 3 * ((p.2 : ℕ) : ℤ) + coverShift tail := by
  have hd : 0 < (p.2 : ℕ) := p.2.pos
  simp only [coverShift, List.map_cons, List.sum_cons]
  omega

/-- The head slot uses the genuine signed insertion and contributes exponent `-m-3d`. -/
theorem jetTerm_cons (a : Charge lattice) (k : ℤ) (p : Jet) (tail : List Jet)
    (m : ℤ) (rest : Indices (tail.map Prod.fst).length) :
    jetTerm a k (p :: tail) (m, rest) =
      jetWeight p.2 m • insertMode (p.1, m)
        (jetTerm a (k + 3 * ((p.2 : ℕ) : ℤ) + m) tail rest) := by
  rw [show jetTerm a k (p :: tail) (m, rest) =
      (jetWeight p.2 m * weightProduct tail rest) •
        wordTerm a (k + coverShift (p :: tail)) (p.1 :: tail.map Prod.fst) (m, rest) from rfl,
    wordTerm_cons]
  simp only [jetTerm, map_smul, smul_smul]
  rw [show k + coverShift (p :: tail) + 3 + m =
      k + 3 * ((p.2 : ℕ) : ℤ) + m + coverShift tail by
    have h := coverShift_cons p tail
    omega]

/-- The first-oscillator support bound applies at the shifted exponent. -/
theorem jetTerm_finite (a : Charge lattice) (k : ℤ) (jets : List Jet) (w : State) :
    Function.HasFiniteSupport (fun indices => jetTerm a k jets indices w) := by
  refine (wordTerm_finite a (k + coverShift jets) (jets.map Prod.fst) w).subset ?_
  intro indices hi hz
  change wordTerm a (k + coverShift jets) (jets.map Prod.fst) indices w = 0 at hz
  exact hi (by simp only [jetTerm, LinearMap.smul_apply, hz, smul_zero])

/-- The possible head indices have the signed cutoff with `3d` in place of `3`. -/
theorem jetTerm_firstIndex (a : Charge lattice) (k : ℤ) (p : Jet) (tail : List Jet)
    (w : State) (m : ℤ) (rest : Indices (tail.map Prod.fst).length)
    (h : jetTerm a k (p :: tail) (m, rest) w ≠ 0) :
    m ∈ Finset.Icc
      (min 0 (wordLower a (tail.map Prod.fst) w - coverShift tail - k - 3 * ((p.2 : ℕ) : ℤ)))
      (P48qFixedCurrentIterate.coverBound w : ℤ) := by
  have hbase : wordTerm a (k + coverShift (p :: tail)) (p.1 :: tail.map Prod.fst)
      (m, rest) w ≠ 0 := by
    intro hz
    apply h
    change ((jetWeight p.2 m * weightProduct tail rest) •
      wordTerm a (k + coverShift (p :: tail)) (p.1 :: tail.map Prod.fst) (m, rest)) w = 0
    rw [LinearMap.smul_apply, hz, smul_zero]
  have hshift := coverShift_cons p tail
  convert wordTerm_firstIndex a _ p.1 _ w m rest hbase using 2
  congr 1
  omega

/-- The pointwise finite normal-order sum as an endomorphism of the full concrete carrier. -/
def normalOrderedCoeff (a : Charge lattice) (k : ℤ) (jets : List Jet) : Module.End ℂ State where
  toFun w := ∑ᶠ indices, jetTerm a k jets indices w
  map_add' w v := by
    simp only [map_add]
    exact finsum_add_distrib (jetTerm_finite a k jets w) (jetTerm_finite a k jets v)
  map_smul' c w := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' c (jetTerm_finite a k jets w)).symm

/-- On each input, all coefficients below the shifted first-oscillator bound vanish. -/
theorem normalOrderedCoeff_bddBelow (a : Charge lattice) (jets : List Jet) (w : State) :
    BddBelow (Function.support fun k => normalOrderedCoeff a k jets w) := by
  refine ⟨wordLower a (jets.map Prod.fst) w - coverShift jets, ?_⟩
  intro k hk
  apply le_of_not_gt
  intro h
  apply hk
  apply finsum_eq_zero_of_forall_eq_zero
  intro indices
  simp only [jetTerm, LinearMap.smul_apply,
    wordTerm_zero_below a (jets.map Prod.fst) w (k + coverShift jets) indices (by omega),
    smul_zero]

/-- The lower-truncated all-jet normal-ordered field. -/
def normalOrderedField (a : Charge lattice) (jets : List Jet) : VertexOperator ℂ State :=
  VertexOperator.of_coeff (fun k => normalOrderedCoeff a k jets)
    (normalOrderedCoeff_bddBelow a jets)

theorem normalOrderedField_coeff (a : Charge lattice) (jets : List Jet) (k : ℤ) :
    HVertexOperator.coeff (normalOrderedField a jets) k = normalOrderedCoeff a k jets := rfl

theorem normalOrderedCoeff_cons_apply (a : Charge lattice) (k : ℤ) (p : Jet)
    (tail : List Jet) (w : State) :
    normalOrderedCoeff a k (p :: tail) w =
      ∑ᶠ m : ℤ, jetWeight p.2 m • insertMode (p.1, m)
        (normalOrderedCoeff a (k + 3 * ((p.2 : ℕ) : ℤ) + m) tail) w := by
  change (∑ᶠ q : ℤ × Indices (tail.map Prod.fst).length, jetTerm a k (p :: tail) q w) = _
  rw [finsum_curry _ (jetTerm_finite a k (p :: tail) w)]
  apply finsum_congr
  intro m
  let j := k + 3 * ((p.2 : ℕ) : ℤ) + m
  simp only [jetTerm_cons, LinearMap.smul_apply, insertMode_apply]
  by_cases hm : m < 0
  · simp only [ite_eq_left hm, Module.End.mul_apply]
    change (∑ᶠ i, jetWeight p.2 m • mode p.1 m (jetTerm a j tail i w)) =
      jetWeight p.2 m • mode p.1 m (∑ᶠ i, jetTerm a j tail i w)
    rw [map_finsum (mode p.1 m) (jetTerm_finite a j tail w)]
    refine (smul_finsum' _ ((jetTerm_finite a j tail w).subset ?_)).symm
    intro i hi hz
    change jetTerm a j tail i w = 0 at hz
    exact hi (by simp only [hz, map_zero])
  · simp only [ite_eq_right hm, Module.End.mul_apply]
    exact (smul_finsum' _ (jetTerm_finite a j tail (mode p.1 m w))).symm

private theorem normalOrderedCoeff_nil (a : Charge lattice) (k : ℤ) :
    normalOrderedCoeff a k [] = HVertexOperator.coeff (concreteChargedField a) k := by
  apply LinearMap.ext
  intro w
  change (∑ᶠ _ : Unit, (1 : ℂ) • P48qSignedNormalWord.signedWordCoeff a (k + 0) [] w) = _
  simp only [one_smul, add_zero, signedWordCoeff_nil, finsum_eq_sum_of_fintype,
    Finset.univ_unique, Finset.sum_singleton]
  rfl

/-- Taking every level to be one gives the checked first-oscillator normal-order sum. -/
theorem normalOrderedCoeff_allFirst (a : Charge lattice) (k : ℤ) (directions : List Cartan) :
    normalOrderedCoeff a k (directions.map fun u => (u, (1 : ℕ+))) =
      P48qSignedNormalWord.normalOrderedCoeff a k directions := by
  induction directions generalizing k with
  | nil =>
    rw [List.map_nil, normalOrderedCoeff_nil, P48qSignedNormalWord.normalOrderedCoeff_nil]
    rfl
  | cons u tail ih =>
    apply LinearMap.ext
    intro w
    rw [List.map_cons, normalOrderedCoeff_cons_apply,
      P48qSignedNormalWord.normalOrderedCoeff_cons_apply]
    apply finsum_congr
    intro m
    change jetWeight 1 m •
      insertMode (u, m) (normalOrderedCoeff a (k + 3 + m)
        (tail.map fun v => (v, (1 : ℕ+)))) w = _
    rw [ih]
    simp only [jetWeight, PNat.val_ofNat, Nat.sub_self, Ring.choose_zero_right, one_smul]

/-- The singleton coefficient uses actual first-current terms at the shifted exponent. -/
theorem normalOrderedCoeff_singleton_apply (a : Charge lattice) (k : ℤ) (u : Cartan)
    (d : ℕ+) (w : State) :
    normalOrderedCoeff a k [(u, d)] w =
      ∑ᶠ m : ℤ, jetWeight d m • orderedTerm a (k + 3 * ((d : ℕ) - 1 : ℕ)) m u w := by
  rw [normalOrderedCoeff_cons_apply]
  apply finsum_congr
  intro m
  rw [normalOrderedCoeff_nil, insertMode_apply, orderedTerm_fields, currentField_coeff,
    show -(-m - 3) - 3 = m by omega]
  have hd := d.pos
  rw [show k + 3 * ((d : ℕ) - 1 : ℕ) + 3 + m = k + 3 * ((d : ℕ) : ℤ) + m by omega]

private theorem jetWeight_signedStrip (d : ℕ+) (m : ℤ) (r : ℕ)
    (hm : m % 3 = (r : ℤ)) :
    jetWeight d m =
      ∑ j ∈ Finset.range (((d : ℕ) - 1) + 1),
        hasseWeight r m (j + 1) * Ring.choose (-(r : ℂ) / 3) ((d : ℕ) - 1 - j) := by
  have h : 3 * signedStripIndex r m + (r : ℤ) = m := by
    unfold signedStripIndex
    rw [← hm]
    omega
  have hc := congrArg (fun x : ℤ => (x : ℂ)) h
  push_cast at hc
  rw [jetWeight, show -(m : ℂ) / 3 - 1 =
    (-(signedStripIndex r m : ℂ) - 1) + (-(r : ℂ) / 3) by linear_combination hc / 3]
  rw [Ring.add_choose_eq _ (Commute.all _ _),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [hasseWeight]

private theorem orderedTerm_off_strip (a : Charge lattice) (u : Cartan)
    (r : ℕ) (hr : r < 3) (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (k m : ℤ)
    (hm : m % 3 ≠ (r : ℤ)) : orderedTerm a k m u = 0 := by
  have hz : mode u m = 0 := by
    rw [← mode_projectAt u m, projectAt_off_residue u r hr hu m hm]
    exact (modeLinear m).map_zero
  rw [orderedTerm_fields, currentField_coeff, show -(-m - 3) - 3 = m by omega, hz]
  split <;> simp

/-- On a residue eigenspace, the physical jet is the binomial expansion of the
checked integer-strip coefficients, all at the same underlying first exponent. -/
theorem normalOrderedCoeff_singleton_signedStrip (a : Charge lattice) (u : Cartan)
    (r : ℕ) (hr : r < 3) (hu : p48qAction u = (ζ ^ r) ^ 2 • u)
    (d : ℕ+) (k : ℤ) (w : State) :
    normalOrderedCoeff a k [(u, d)] w =
      ∑ j ∈ Finset.range (((d : ℕ) - 1) + 1),
        Ring.choose (-(r : ℂ) / 3) ((d : ℕ) - 1 - j) •
          higherNormalCoeff a u r (j + 1) (k + 3 * (((d : ℕ) - 1 - j : ℕ) : ℤ)) w := by
  let n := (d : ℕ) - 1
  let e := k + 3 * (n : ℤ)
  let cut := Finset.Icc (min 0 (lowerBound a w - e - 3)) (coverBound w : ℤ)
  let base (m : ℤ) := orderedTerm a e m u w
  let strip (j : ℕ) (m : ℤ) :=
    higherNormalTerm a u r (j + 1) (k + 3 * ((n - j : ℕ) : ℤ)) m w
  have hbase : Function.support base ⊆ (cut : Set ℤ) := orderedTerm_support a u e w
  have hphysical : Function.support (fun m => jetWeight d m • base m) ⊆ (cut : Set ℤ) :=
    fun m hm => hbase (fun hz => hm (by simp only [hz, smul_zero]))
  have hstrip (j : ℕ) (hj : j ∈ Finset.range (n + 1)) (m : ℤ) :
      strip j m = if m % 3 = (r : ℤ) then hasseWeight r m (j + 1) • base m else 0 := by
    have hj' := Finset.mem_range.mp hj
    have he : k + 3 * ((n - j : ℕ) : ℤ) + 3 * ((j + 1 - 1 : ℕ) : ℤ) = e := by
      dsimp [e]
      omega
    simp only [strip, higherNormalTerm, he, base]
  rw [normalOrderedCoeff_singleton_apply]
  change (∑ᶠ m, jetWeight d m • base m) =
    ∑ j ∈ Finset.range (n + 1), Ring.choose (-(r : ℂ) / 3) (n - j) • ∑ᶠ m, strip j m
  rw [finsum_eq_sum_of_support_subset _ hphysical]
  calc
    _ = ∑ m ∈ cut, ∑ j ∈ Finset.range (n + 1),
          Ring.choose (-(r : ℂ) / 3) (n - j) • strip j m := by
      apply Finset.sum_congr rfl
      intro m _
      by_cases hm : m % 3 = (r : ℤ)
      · rw [jetWeight_signedStrip d m r hm, Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hstrip j hj m, ite_eq_left hm, smul_smul, mul_comm]
      · have hz : base m = 0 := by
          simp only [base, orderedTerm_off_strip a u r hr hu e m hm, LinearMap.zero_apply]
        rw [hz, smul_zero]
        symm
        apply Finset.sum_eq_zero
        intro j hj
        rw [hstrip j hj m, ite_eq_right hm, smul_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      have hcut : Function.support (strip j) ⊆ (cut : Set ℤ) := by
        intro m hm
        apply hbase
        intro hz
        exact hm (by rw [hstrip j hj m, hz, smul_zero, ite_self])
      rw [finsum_eq_sum_of_support_subset _ hcut, Finset.smul_sum]

/-- The physical and stripped coefficients coincide directly at residue zero or level one. -/
theorem normalOrderedCoeff_singleton_eq_signedStrip (a : Charge lattice) (u : Cartan)
    (r : ℕ) (hr : r < 3) (hu : p48qAction u = (ζ ^ r) ^ 2 • u)
    (d : ℕ+) (h : r = 0 ∨ d = 1) (k : ℤ) (w : State) :
    normalOrderedCoeff a k [(u, d)] w = higherNormalCoeff a u r (d : ℕ) k w := by
  rw [normalOrderedCoeff_singleton_signedStrip a u r hr hu d k w]
  let n := (d : ℕ) - 1
  change (∑ j ∈ Finset.range (n + 1),
    Ring.choose (-(r : ℂ) / 3) (n - j) •
      higherNormalCoeff a u r (j + 1) (k + 3 * ((n - j : ℕ) : ℤ)) w) = _
  rw [Finset.sum_eq_single n]
  · have hn : n + 1 = (d : ℕ) := Nat.sub_add_cancel d.pos
    simp only [Nat.sub_self, Ring.choose_zero_right, one_smul, hn,
      Nat.cast_zero, mul_zero, add_zero]
  · intro j hj hjn
    have hj' := Finset.mem_range.mp hj
    have hr0 : r = 0 := h.resolve_right fun hd => by
      have hn : n = 0 := by simp [n, hd]
      omega
    simp only [hr0, Nat.cast_zero, neg_zero, zero_div,
      Ring.choose_zero_pos ℂ (show 0 < n - j by omega), zero_smul]
  · intro hn
    exact (hn (Finset.mem_range.mpr (Nat.lt_succ_self n))).elim

/-- Permuting labelled slots preserves the sum, even with repeated directions and levels. -/
theorem normalOrderedCoeff_perm (a : Charge lattice) (k : ℤ)
    {left right : List Jet} (h : left.Perm right) :
    normalOrderedCoeff a k left = normalOrderedCoeff a k right := by
  induction h generalizing k with
  | nil => rfl
  | cons p _ ih =>
    apply LinearMap.ext
    intro w
    simp only [normalOrderedCoeff_cons_apply, ih]
  | swap p q tail =>
    apply LinearMap.ext
    intro w
    let swapIndices (i : ℤ × ℤ × Indices (tail.map Prod.fst).length) := (i.2.1, i.1, i.2.2)
    change (∑ᶠ i : ℤ × ℤ × Indices (tail.map Prod.fst).length, jetTerm a k (q :: p :: tail) i w) =
      ∑ᶠ i : ℤ × ℤ × Indices (tail.map Prod.fst).length, jetTerm a k (p :: q :: tail) i w
    apply finsum_eq_of_bijective swapIndices
      (Function.Involutive.bijective (fun _ => rfl))
    rintro ⟨m, n, rest⟩
    change jetTerm a k (q :: p :: tail) (m, n, rest) w =
      jetTerm a k (p :: q :: tail) (n, m, rest) w
    simp only [jetTerm_cons, map_smul, smul_smul]
    rw [mul_comm (jetWeight q.2 m) (jetWeight p.2 n),
      show k + 3 * ((q.2 : ℕ) : ℤ) + m + 3 * ((p.2 : ℕ) : ℤ) + n =
        k + 3 * ((p.2 : ℕ) : ℤ) + n + 3 * ((q.2 : ℕ) : ℤ) + m by omega]
    rw [← Module.End.mul_apply, (insertMode_commute (q.1, m) (p.1, n)).eq, Module.End.mul_apply]
  | trans _ _ ih₁ ih₂ => exact (ih₁ k).trans (ih₂ k)

theorem normalOrderedField_nil (a : Charge lattice) :
    normalOrderedField a [] = concreteChargedField a :=
  HVertexOperator.coeff_inj (funext fun k => normalOrderedCoeff_nil a k)

theorem normalOrderedField_perm (a : Charge lattice) {left right : List Jet}
    (h : left.Perm right) : normalOrderedField a left = normalOrderedField a right :=
  HVertexOperator.coeff_inj (funext fun k => normalOrderedCoeff_perm a k h)

#print axioms jetTerm_cons
#print axioms jetTerm_finite
#print axioms jetTerm_firstIndex
#print axioms normalOrderedCoeff_bddBelow
#print axioms normalOrderedField
#print axioms normalOrderedCoeff_allFirst
#print axioms normalOrderedCoeff_singleton_apply
#print axioms normalOrderedCoeff_singleton_signedStrip
#print axioms normalOrderedCoeff_singleton_eq_signedStrip
#print axioms normalOrderedField_perm

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qJetNormalOrdering
