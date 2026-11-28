/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeCurrentStateAction
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Identify nonnegative native current products on jet-word states. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeWickCurrentCommutator

/-! The current commutator on the actual native field, with the untwisted
nonnegative state products in the Bakalov--Kac commutator formula. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentCommutator

open LatticeGeneratingFieldLocality (Charge Carrier Oscillator bilinear unitCharge)
open LatticeAllStateField (Y vacuum)
open LatticeAllStateReconstruction (mu)
open LatticeActualConformalState (currentState current_state_field)
open LatticeFiniteNegativeGeneration (neutralPolynomialMode neutralMode)
open LatticeSugawaraCurrents (weightedPartial neutralPolynomialMode_positive neutralMode_single
  neutralField_ncoeff neutralMode_vanish vectorFrequencyBound)
open ThirdTwistedIterate (currentAlong)
open P48qTwistedChargeAction (lattice)
open P48qThirdTwistedField (Cartan State chargeVector concreteChargedField)
open ThirdEigenspacePairing (p48qForm)
open P48qTwistedHeisenberg (mode projectAt)
open P48qJetNormalOrdering (jetWeight)
open P48qAllJetWickField
open MvPolynomial
open private sumErase sumErase_cons sumErase_add smul_sumErase from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qWickPermutation
open private chargeWeight shift from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentCommutator
open private commLinear from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeWickCurrentCommutator
open private jetPolynomial jetWordPolynomial nativeCoeff nativeCoeff_jetWord
  jetPolynomial_oscillatorJet from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeMonodromy
open private nativeWordPolynomial_eq_monomial from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qAllJetWickField

private def wordState (a : Charge lattice) (jets : List Jet) : NativeStates :=
  Finsupp.single a (jetWordPolynomial jets)

private theorem wordState_coeff (a : Charge lattice) (k : ℤ) (jets : List Jet) :
    HVertexOperator.coeff (nativeField (wordState a jets)) k = allJetCoeff a k jets := by
  have h := nativeCoeff_jetWord a k jets []
  simpa only [nativeWordPolynomial, List.map_nil, List.prod_nil, mul_one, List.append_nil,
    nativeCoeff, LinearMap.comp_apply, LinearMap.proj_apply, Finsupp.lsingle_apply, wordState]
    using h

private theorem jetWordPolynomial_map (word : List NativeIndex) :
    jetWordPolynomial (word.map oscillatorJet) = nativeWordPolynomial word := by
  induction word with
  | nil => rfl
  | cons j tail ih =>
    change jetPolynomial (oscillatorJet j).2 (oscillatorJet j).1 *
      jetWordPolynomial (tail.map oscillatorJet) = X j * nativeWordPolynomial tail
    rw [jetPolynomial_oscillatorJet, ih]

private theorem current_mode_sum (u : Cartan) (n : ℤ) :
    (Y lattice (currentAlong lattice u))[[n]] =
      ∑ i : Fin lattice.rank, u i • neutralMode lattice i n := by
  simp only [currentAlong, map_sum, map_smul, current_state_field, Finset.sum_apply,
    Pi.smul_apply, neutralField_ncoeff]

private theorem mu_current_single (u : Cartan) (n : ℤ) (a : Charge lattice)
    (P : NativePolynomial) :
    mu lattice (currentAlong lattice u) n (Finsupp.single a P) =
      Finsupp.single a (∑ i : Fin lattice.rank, u i • neutralPolynomialMode lattice i a n P) := by
  rw [mu, current_mode_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, neutralMode_single, Finsupp.smul_single,
    Finsupp.single_finsetSum]

private theorem form_apply (u v : Cartan) :
    p48qForm u v = ∑ i : Fin lattice.rank, ∑ j : Fin lattice.rank,
      u i * (lattice.G i j : ℂ) * v j := by
  simp only [p48qForm, Matrix.toBilin'_apply, Matrix.map_apply]
  rfl

private theorem charge_pairing (u : Cartan) (a : Charge lattice) :
    p48qForm u (chargeVector a) =
      ∑ i : Fin lattice.rank, u i * (bilinear lattice (unitCharge lattice i) a : ℂ) := by
  classical
  rw [form_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hb : bilinear lattice (unitCharge lattice i) a =
      ∑ j : Fin lattice.rank, lattice.G i j * a j := by
    unfold bilinear
    rw [Finset.sum_eq_single i]
    · simp [unitCharge]
    · intro j _ hji
      simp [unitCharge, hji]
    · simp
  rw [hb]
  simp only [Int.cast_sum, Int.cast_mul, Finset.mul_sum, chargeVector, mul_assoc]

private theorem mu_current_zero (u : Cartan) (a : Charge lattice) (P : NativePolynomial) :
    mu lattice (currentAlong lattice u) 0 (Finsupp.single a P) =
      p48qForm u (chargeVector a) • Finsupp.single a P := by
  rw [mu_current_single, charge_pairing, Finsupp.smul_single]
  simp only [neutralPolynomialMode, Int.lt_irrefl, ite_false, ite_true,
    LinearMap.smul_apply, LinearMap.id_apply, smul_smul, Finset.sum_smul]

private def jetDerivative (u : Cartan) (r : ℕ) : Module.End ℂ NativePolynomial :=
  ∑ i : Fin lattice.rank, u i • weightedPartial lattice i r

private theorem mu_current_succ (u : Cartan) (r : ℕ) (a : Charge lattice) (P : NativePolynomial) :
    mu lattice (currentAlong lattice u) ((r : ℤ) + 1) (Finsupp.single a P) =
      ((r + 1 : ℕ) : ℂ) • Finsupp.single a (jetDerivative u r P) := by
  rw [mu_current_single, Finsupp.smul_single]
  simp only [neutralPolynomialMode_positive, jetDerivative, LinearMap.sum_apply,
    LinearMap.smul_apply, Nat.cast_add, Nat.cast_one, Finset.smul_sum]
  apply congrArg (Finsupp.single a)
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

private theorem jetDerivative_mul (u : Cartan) (r : ℕ) (P Q : NativePolynomial) :
    jetDerivative u r (P * Q) = jetDerivative u r P * Q + P * jetDerivative u r Q := by
  simp only [jetDerivative, weightedPartial, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe, pderiv_mul, smul_add, Finset.sum_add_distrib, Finset.smul_sum,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]

private theorem pderiv_jetPolynomial (r : ℕ) (j : Fin lattice.rank) (p : Jet) :
    pderiv (j, r) (jetPolynomial p.2 p.1) =
      if r = (p.2 : ℕ) - 1 then p.1 j • (1 : NativePolynomial) else 0 := by
  classical
  by_cases hr : r = (p.2 : ℕ) - 1
  · simp [jetPolynomial, pderiv_X, Pi.single_apply, hr, eq_comm]
  · simp [jetPolynomial, pderiv_X, hr]

private theorem jetDerivative_jetPolynomial (u : Cartan) (r : ℕ) (p : Jet) :
    jetDerivative u r (jetPolynomial p.2 p.1) =
      if r + 1 = (p.2 : ℕ) then p48qForm u p.1 • (1 : NativePolynomial) else 0 := by
  have hd : 0 < (p.2 : ℕ) := p.2.pos
  simp only [jetDerivative, weightedPartial, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe, pderiv_jetPolynomial]
  by_cases hr : r + 1 = (p.2 : ℕ)
  · rw [ite_eq_left hr]
    simp only [show r = (p.2 : ℕ) - 1 by omega, ite_true, form_apply,
      Finset.smul_sum, smul_smul, Finset.sum_smul, mul_assoc]
  · simp only [show r ≠ (p.2 : ℕ) - 1 by omega, ite_false, hr, smul_zero,
      Finset.sum_const_zero]

set_option maxHeartbeats 1000000 in
-- The product rule elaborates over the native polynomial and finite deletion sum.
private theorem jetDerivative_word (u : Cartan) (r : ℕ) (jets : List Jet) :
    jetDerivative u r (jetWordPolynomial jets) =
      sumErase jets (fun p rest =>
        if r + 1 = (p.2 : ℕ) then p48qForm u p.1 • jetWordPolynomial rest else 0) := by
  induction jets with
  | nil =>
    change jetDerivative u r 1 = _
    simp [jetDerivative, weightedPartial, sumErase]
  | cons p tail ih =>
    rw [show jetWordPolynomial (p :: tail) =
      jetPolynomial p.2 p.1 * jetWordPolynomial tail from rfl]
    rw [jetDerivative_mul, jetDerivative_jetPolynomial, ih, sumErase_cons]
    apply congrArg₂ (· + ·)
    · by_cases hr : r + 1 = (p.2 : ℕ) <;> simp only [hr, ite_true, ite_false,
        smul_mul_assoc, one_mul, zero_mul]
    · unfold sumErase
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hr : r + 1 = (tail.get j).2.val
      · simp only [hr, ite_true, mul_smul_comm]
        rfl
      · simp only [hr, ite_false, mul_zero]

/-- On a jet word, each positive actual untwisted current product deletes
exactly the occurrences at its own oscillator level. -/
theorem mu_current_word_succ (u : Cartan) (r : ℕ) (a : Charge lattice) (jets : List Jet) :
    mu lattice (currentAlong lattice u) ((r : ℤ) + 1) (wordState a jets) =
      sumErase jets (fun p rest =>
        if r + 1 = (p.2 : ℕ) then
          (((r + 1 : ℕ) : ℂ) * p48qForm u p.1) • wordState a rest else 0) := by
  rw [wordState, mu_current_succ, jetDerivative_word]
  simp only [sumErase, Finsupp.single_finsetSum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hr : r + 1 = (jets.get j).2.val
  · simp only [hr, ite_true, ← Finsupp.smul_single, smul_smul, wordState]
  · simp only [hr, ite_false, Finsupp.single_zero, smul_zero]

private theorem slotWeight_eq_choose (h : Cartan) (m : ℤ) (p : Jet) :
    slotWeight h m p =
      Ring.choose ((m : ℂ) / 3) (p.2 : ℕ) *
        (((p.2 : ℕ) : ℂ) * p48qForm (projectAt m h) p.1) := by
  have hc := Ring.choose_smul_choose ((m : ℂ) / 3) (n := (p.2 : ℕ)) (k := 1)
    (Nat.one_le_iff_ne_zero.mpr p.2.ne_zero)
  simp only [Nat.choose_one_right, nsmul_eq_mul, Ring.choose_one_right, Nat.cast_one] at hc
  rw [slotWeight, jetWeight, Int.cast_neg, neg_neg]
  linear_combination (-(p48qForm (projectAt m h) p.1)) * hc

/-- A coefficient of the genuine untwisted product read by the native field. -/
private def sourceTerm (h : Cartan) (m k : ℤ) (n : ℕ) :
    NativeStates →ₗ[ℂ] Module.End ℂ State :=
  Ring.choose ((m : ℂ) / 3) n •
    (((LinearMap.proj (k - m + 3 * (n : ℤ))).comp HVertexOperator.coeff).comp
      (nativeField.comp ((Y lattice (currentAlong lattice (projectAt m h)))[[(n : ℤ)]])))

private theorem sourceTerm_apply (h : Cartan) (m k : ℤ) (n : ℕ) (v : NativeStates) :
    sourceTerm h m k n v =
      Ring.choose ((m : ℂ) / 3) n • HVertexOperator.coeff
      (nativeField (mu lattice (currentAlong lattice (projectAt m h)) (n : ℤ) v))
      (k - m + 3 * (n : ℤ)) := rfl

private theorem sourceTerm_finite (h : Cartan) (m k : ℤ) (v : NativeStates) :
    Function.HasFiniteSupport (fun n => sourceTerm h m k n v) := by
  refine (Set.finite_Iic (vectorFrequencyBound lattice v)).subset ?_
  intro n hn
  by_contra hlarge
  have hlarge' : (vectorFrequencyBound lattice v : ℤ) < (n : ℤ) := by
    exact_mod_cast (lt_of_not_ge hlarge)
  apply hn
  change sourceTerm h m k n v = 0
  rw [sourceTerm_apply, mu, current_mode_sum, LinearMap.sum_apply]
  have hz : (∑ i : Fin lattice.rank,
      ((projectAt m h) i • neutralMode lattice i (n : ℤ)) v) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [LinearMap.smul_apply, neutralMode_vanish lattice i v _ hlarge', smul_zero]
  simp only [hz, map_zero, Pi.zero_apply, smul_zero]

private theorem sourceTerm_word (h : Cartan) (m k : ℤ) (n : ℕ) (a : Charge lattice)
    (jets : List Jet) :
    sourceTerm h m k n (wordState a jets) =
      (if n = 0 then chargeWeight h m a • allJetCoeff a (k - m) jets else 0) +
        sumErase jets (fun p rest => if n = (p.2 : ℕ) then
          slotWeight h m p • allJetCoeff a (k - m + shift p) rest else 0) := by
  cases n with
  | zero =>
    rw [sourceTerm_apply]
    simp only [Nat.cast_zero, mul_zero, add_zero, Ring.choose_zero_right, one_smul, ite_true]
    have hmode : mu lattice (currentAlong lattice (projectAt m h)) 0 (wordState a jets) =
        chargeWeight h m a • wordState a jets := mu_current_zero _ _ _
    rw [hmode, map_smul, map_smul, Pi.smul_apply, wordState_coeff]
    have hs : sumErase jets (fun p rest => if 0 = (p.2 : ℕ) then
        slotWeight h m p • allJetCoeff a (k - m + shift p) rest else 0) = 0 := by
      unfold sumErase
      apply Finset.sum_eq_zero
      intro j _
      change (if 0 = (jets.get j).2.val then _ else 0) = 0
      exact ite_eq_right (Ne.symm (Nat.ne_of_gt (jets.get j).2.pos))
    rw [hs, add_zero]
  | succ r =>
    rw [sourceTerm_apply, Nat.cast_succ, mu_current_word_succ]
    simp only [Nat.succ_ne_zero, ite_false, zero_add, sumErase, map_sum, Finset.sum_apply,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    let p := jets.get j
    let rest := jets.eraseIdx j
    change Ring.choose ((m : ℂ) / 3) (r + 1) • HVertexOperator.coeff
      (nativeField (if r + 1 = (p.2 : ℕ) then
        (((r + 1 : ℕ) : ℂ) * p48qForm (projectAt m h) p.1) • wordState a rest else 0))
      (k - m + 3 * ((r : ℤ) + 1)) =
      if r + 1 = (p.2 : ℕ) then slotWeight h m p •
        allJetCoeff a (k - m + shift p) rest else 0
    by_cases hr : r + 1 = (p.2 : ℕ)
    · have hshift : k - m + 3 * ((r : ℤ) + 1) = k - m + shift p := by
        unfold shift
        omega
      rw [ite_eq_left hr, ite_eq_left hr, map_smul, map_smul, Pi.smul_apply, smul_smul, hshift,
        wordState_coeff, slotWeight_eq_choose, hr]
    · simp only [ite_eq_right hr, map_zero, Pi.zero_apply, smul_zero]

private def sourceSum (h : Cartan) (m k : ℤ) :
    NativeStates →ₗ[ℂ] Module.End ℂ State where
  toFun v := ∑ᶠ n, sourceTerm h m k n v
  map_add' v w := by
    simp only [map_add]
    exact finsum_add_distrib (sourceTerm_finite h m k v) (sourceTerm_finite h m k w)
  map_smul' c v := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' c (sourceTerm_finite h m k v)).symm

private theorem sourceSum_word (h : Cartan) (m k : ℤ) (a : Charge lattice)
    (jets : List Jet) :
    sourceSum h m k (wordState a jets) =
      chargeWeight h m a • allJetCoeff a (k - m) jets +
        sumErase jets (fun p rest =>
          slotWeight h m p • allJetCoeff a (k - m + shift p) rest) := by
  let F (n : ℕ) := if n = 0 then chargeWeight h m a • allJetCoeff a (k - m) jets else 0
  let G (j : Fin jets.length) (n : ℕ) :=
    if n = (jets.get j).2.val then slotWeight h m (jets.get j) •
      allJetCoeff a (k - m + shift (jets.get j)) (jets.eraseIdx j) else 0
  have hf : Function.HasFiniteSupport F := by
    refine (Set.finite_singleton (0 : ℕ)).subset ?_
    intro n hn
    by_contra hz
    have hz' : n ≠ 0 := hz
    exact hn (by simp [F, hz'])
  have hg (j : Fin jets.length) : Function.HasFiniteSupport (G j) := by
    refine (Set.finite_singleton (jets.get j).2.val).subset ?_
    intro n hn
    by_contra hz
    have hz' : n ≠ (jets.get j).2.val := hz
    exact hn (by dsimp only [G]; rw [ite_eq_right hz'])
  have hs : Function.HasFiniteSupport (fun n => ∑ j, G j n) := by
    refine (Set.finite_univ.biUnion (t := fun j : Fin jets.length =>
      Function.support (G j)) (fun j _ => hg j)).subset ?_
    intro n hn
    by_contra hz
    apply hn
    apply Finset.sum_eq_zero
    intro j _
    by_contra hne
    exact hz (Set.mem_iUnion₂.mpr ⟨j, Set.mem_univ j, hne⟩)
  change (∑ᶠ n, sourceTerm h m k n (wordState a jets)) = _
  calc
    _ = ∑ᶠ n : ℕ, (F n + ∑ j, G j n) := by
      apply finsum_congr
      intro n
      exact sourceTerm_word h m k n a jets
    _ = _ := by
      rw [finsum_add_distrib hf hs, finsum_eq_single F 0 (by intro n hn; simp [F, hn]),
        ← sum_finsum_comm _ _ (fun j _ => hg j)]
      simp only [F, ite_true]
      apply congrArg (fun B : Module.End ℂ State => chargeWeight h m a •
        allJetCoeff a (k - m) jets + B)
      unfold sumErase
      apply Finset.sum_congr rfl
      intro j _
      rw [finsum_eq_single (G j) (jets.get j).2.val (by intro n hn; dsimp only [G]; rw [ite_eq_right hn])]
      simp only [G, ite_true, eq_self]

/-- Bakalov--Kac (3.12), nonnegative current products, on the actual native
field. The current is its residue projection in the untwisted products,
while the left side uses its signed cover mode. -/
theorem nativeField_current_commutator (h : Cartan) (m k : ℤ) (v : NativeStates) :
    ⁅mode h m, HVertexOperator.coeff (nativeField v) k⁆ =
      ∑ᶠ n : ℕ, Ring.choose ((m : ℂ) / 3) n • HVertexOperator.coeff
        (nativeField (mu lattice (currentAlong lattice (projectAt m h)) (n : ℤ) v))
        (k - m + 3 * (n : ℤ)) := by
  let read : NativeStates →ₗ[ℂ] Module.End ℂ State :=
    ((LinearMap.proj k).comp HVertexOperator.coeff).comp nativeField
  have hEq : (commLinear h m).comp read = sourceSum h m k := by
    apply Finsupp.lhom_ext
    intro a P
    change (commLinear h m).comp read (Finsupp.single a P) =
      sourceSum h m k (Finsupp.single a P)
    induction P using MvPolynomial.induction_on' with
    | monomial e c =>
      classical
      have he : nativeWordPolynomial (oscillatorOccurrences e) = monomial e 1 := by
        rw [nativeWordPolynomial_eq_monomial, oscillatorOccurrences, Multiset.coe_toList,
          Finsupp.toMultiset_toFinsupp]
      let jets := (oscillatorOccurrences e).map oscillatorJet
      have hword : Finsupp.single a (monomial e c) = c • wordState a jets := by
        rw [wordState, Finsupp.smul_single]
        change Finsupp.single a (monomial e c) =
          Finsupp.single a (c • jetWordPolynomial ((oscillatorOccurrences e).map oscillatorJet))
        rw [jetWordPolynomial_map, he, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hword, map_smul, map_smul]
      apply congrArg (fun B : Module.End ℂ State => c • B)
      change ⁅mode h m, HVertexOperator.coeff (nativeField (wordState a jets)) k⁆ =
        sourceSum h m k (wordState a jets)
      rw [wordState_coeff, sourceSum_word, allJetCoeff_commutator]
    | add P Q ihP ihQ =>
      simp only [Finsupp.single_add, map_add, ihP, ihQ]
  have hv := DFunLike.congr_fun hEq v
  change ⁅mode h m, HVertexOperator.coeff (nativeField v) k⁆ =
    ∑ᶠ n, sourceTerm h m k n v at hv
  simpa only [sourceTerm_apply] using hv

-- Ground coefficient: the charged term has exponent k - m.
example (h : Cartan) (m k : ℤ) (a : Charge lattice) :
    ⁅mode h m, HVertexOperator.coeff (nativeField (Finsupp.single a 1)) k⁆ =
      p48qForm (projectAt m h) (chargeVector a) •
        HVertexOperator.coeff (nativeField (Finsupp.single a 1)) (k - m) := by
  change ⁅mode h m, HVertexOperator.coeff (nativeField (wordState a [])) k⁆ =
    p48qForm (projectAt m h) (chargeVector a) •
      HVertexOperator.coeff (nativeField (wordState a [])) (k - m)
  rw [wordState_coeff, wordState_coeff, allJetCoeff_commutator]
  simp [sumErase, chargeWeight]

-- A level-one charged descendant has one central deletion, with the actual
-- m/3 pairing and exponent k - m + 3.
example (h u : Cartan) (m k : ℤ) (a : Charge lattice) :
    ⁅mode h m, HVertexOperator.coeff (nativeField (wordState a [(u, 1)])) k⁆ =
      p48qForm (projectAt m h) (chargeVector a) •
        HVertexOperator.coeff (nativeField (wordState a [(u, 1)])) (k - m) +
      ((m : ℂ) / 3 * p48qForm (projectAt m h) u) •
        HVertexOperator.coeff (nativeField (Finsupp.single a 1)) (k - m + 3) := by
  change _ = _ + ((m : ℂ) / 3 * p48qForm (projectAt m h) u) •
    HVertexOperator.coeff (nativeField (wordState a [])) (k - m + 3)
  rw [wordState_coeff, wordState_coeff, wordState_coeff, allJetCoeff_commutator, sumErase_cons]
  simp only [sumErase, List.length_nil, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    chargeWeight, slotWeight, jetWeight, PNat.val_ofNat, Nat.sub_self, Ring.choose_zero_right,
    one_mul, shift, Nat.cast_one, mul_one]

-- On the neutral current, the same sign convention gives the central mode.
example (h u : Cartan) (m k : ℤ) :
    ⁅mode h m, HVertexOperator.coeff (nativeField (currentAlong lattice u)) k⁆ =
      if m + (-k - 3) = 0 then ((m : ℂ) / 3 * p48qForm (projectAt m h) u) •
        (1 : Module.End ℂ State) else 0 := by
  rw [P48qNativeMonodromy.nativeField_current, P48qTwistedHeisenberg.currentField_coeff,
    P48qTwistedHeisenberg.mode_commutator]

#print axioms mu_current_word_succ
#print axioms nativeField_current_commutator

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentCommutator
