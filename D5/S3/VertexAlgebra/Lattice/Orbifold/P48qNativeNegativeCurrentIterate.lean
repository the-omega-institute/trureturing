/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeNegativeCurrentIterate
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recover negative native current iterates from regular Taylor coefficients. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentStateAction

/-! The negative current iterate on the native P48q oscillator carrier.
The positive signed modes of the actual commutator determine the collision
germ. Its regular Taylor coefficients supply the singleton and pair terms
of the existing Wick field. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeNegativeCurrentIterate

open LatticeGeneratingFieldLocality (Charge)
open LatticeAllStateReconstruction (mu)
open LatticeFiniteNegativeGeneration (neutralMode)
open LatticeSugawaraCurrents (vectorFrequencyBound neutralMode_vanish neutralField_ncoeff)
open ThirdTwistedIterate (currentAlong)
open ThirdEigenspacePairing (p48qAction p48qForm)
open P48qTwistedChargeAction (lattice)
open P48qThirdTwistedField (Cartan State chargeVector)
open P48qTwistedHeisenberg (mode projectAt mode_projectAt mode_eq_zero_above_coverBound)
open P48qFixedCurrentIterate (coverBound)
open P48qSignedNormalWord (insertMode insertMode_apply)
open P48qJetNormalOrdering (normalOrderedCoeff normalOrderedCoeff_bddBelow
  normalOrderedCoeff_cons_apply jetWeight)
open P48qAllJetWickField
open P48qArbitraryWickRecursion (normalWick normalWickWord normalWick_step)
open P48qJetContractions (pairJetCoeff scalarKernel dividedKernelCoeff)
open PowerSeries (coeff X binomialSeries invOneSubPow)

open private projectAt_on_residue from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCurrentChargedIterate
open private projectAt_off_residue root_cube from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField
open private pairing_project from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg
open private formSymmetric from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
open private wordState wordState_coeff jetWordPolynomial_map current_mode_sum mu_current_zero from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentStateAction
open P48qNativeCurrentCommutator (mu_current_word_succ)
open private jetPolynomial jetWordPolynomial from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeMonodromy
open private neutral_negative_single from D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open private sumErase from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qWickPermutation
open private wickAt wickAt_step wickAt_nil totalLevel_eraseIdx from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeWickCurrentCommutator
open private normalWick_zero_below from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qAllJetWickField

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

private theorem mu_current_negative_single (u : Cartan) (d : ℕ+) (a : Charge lattice)
    (P : NativePolynomial) :
    mu lattice (currentAlong lattice u) (-((d : ℕ) : ℤ)) (Finsupp.single a P) =
      Finsupp.single a (P48qHigherCurrentIterate.sourceOscillator u d * P) := by
  have hd := d.pos
  have h (i : Fin lattice.rank) :
      neutralMode lattice i (-((d : ℕ) : ℤ)) (Finsupp.single a P) =
      Finsupp.single a (MvPolynomial.X (i, (d : ℕ) - 1) * P) := by
    simpa only [neutralField_ncoeff,
      show -(((d : ℕ) - 1 : ℕ) : ℤ) - 1 = -((d : ℕ) : ℤ) by omega] using
      neutral_negative_single lattice i ((d : ℕ) - 1) a P
  simp only [mu, currentAlong, map_sum, map_smul, LatticeActualConformalState.current_state_field,
    Finset.sum_apply, Pi.smul_apply, neutralField_ncoeff, LinearMap.sum_apply, LinearMap.smul_apply,
    h, Finsupp.smul_single, Finsupp.single_finsetSum, P48qHigherCurrentIterate.sourceOscillator,
    Finset.sum_mul, smul_mul_assoc]

/-- The actual untwisted negative current product inserts its oscillator at the head. -/
theorem mu_current_negative_word (a : Charge lattice) (u : Cartan) (d : ℕ+)
    (jets : List Jet) :
    mu lattice (currentAlong lattice u) (-((d : ℕ) : ℤ)) (wordState a jets) =
      wordState a ((u, d) :: jets) := by
  rw [wordState, mu_current_negative_single]
  rfl

private theorem source_zero_above (u : Cartan) (v : NativeStates) (n : ℕ)
    (hn : vectorFrequencyBound lattice v < n) :
    mu lattice (currentAlong lattice u) (n : ℤ) v = 0 := by
  rw [mu, current_mode_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [LinearMap.smul_apply, neutralMode_vanish lattice i v _ (by exact_mod_cast hn), smul_zero]

/-- The source-mode cutoff is independent of the cover mode and coefficient index. -/
theorem current_source_support (u : Cartan) (v : NativeStates) :
    Function.support (fun n : ℕ => mu lattice (currentAlong lattice u) (n : ℤ) v) ⊆
      Set.Iic (vectorFrequencyBound lattice v) := by
  intro n hn
  exact le_of_not_gt (fun h => hn (source_zero_above u v n h))

private def sourceCoeff (u : Cartan) (v : NativeStates) (k : ℤ) (n : ℕ) :
    Module.End ℂ State :=
  HVertexOperator.coeff (nativeField (mu lattice (currentAlong lattice u) (n : ℤ) v))
    (k + 3 * ((n : ℤ) + 1))

private theorem sourceCoeff_zero_above (u : Cartan) (v : NativeStates) (k : ℤ) (n : ℕ)
    (hn : vectorFrequencyBound lattice v < n) : sourceCoeff u v k n = 0 := by
  simp only [sourceCoeff, source_zero_above u v n hn, map_zero, Pi.zero_apply]

private theorem source_sum_cutoff (u : Cartan) (v : NativeStates) (k : ℤ)
    (f : ℕ → ℂ) :
    (∑ᶠ n : ℕ, f n • sourceCoeff u v k n) =
      ∑ n ∈ Finset.range (vectorFrequencyBound lattice v + 1), f n • sourceCoeff u v k n := by
  apply finsum_eq_sum_of_support_subset
  intro n hn
  change n ∈ Finset.range _
  rw [Finset.mem_range]
  apply lt_of_not_ge
  intro h
  apply hn
  change f n • sourceCoeff u v k n = 0
  rw [sourceCoeff_zero_above u v k n (by omega), smul_zero]

/-- Expansion in the reciprocal coordinate y = (1+t)⁻¹, with y^(r/3+1)
factored out. Each pole t^(-j-1) becomes y^(j+1)/(1-y)^(j+1). -/
def commutatorReciprocal (α : ℂ) (n : ℕ) : PowerSeries ℂ :=
  ∑ j ∈ Finset.range (n + 1), Ring.choose α (n - j) •
    ((invOneSubPow ℂ (j + 1)).val * X ^ j)

private theorem reciprocalPole_coeff (i j : ℕ) :
    coeff i ((invOneSubPow ℂ (j + 1)).val * X ^ j) = (i.choose j : ℂ) := by
  rw [PowerSeries.coeff_mul_X_pow']
  by_cases h : j ≤ i
  · simp only [h, ite_true, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
      PowerSeries.coeff_mk, Nat.add_sub_of_le h]
  · simp only [h, ite_false, Nat.choose_eq_zero_of_lt (lt_of_not_ge h), Nat.cast_zero]

private theorem commutatorReciprocal_coeff (α : ℂ) (n i : ℕ) :
    coeff i (commutatorReciprocal α n) = Ring.choose ((i : ℂ) + α) n := by
  rw [Ring.add_choose_eq n (Commute.all _ _), Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [commutatorReciprocal, map_sum, PowerSeries.coeff_smul, reciprocalPole_coeff,
    smul_eq_mul, Ring.choose_natCast]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- The reciprocal expansion agrees with the positive signed modes of the
actual native commutator, with one cutoff for every reciprocal degree. -/
theorem commutatorReciprocal_native (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (v : NativeStates) (k : ℤ) (i : ℕ) :
    let m : ℤ := 3 * (i : ℤ) + (r : ℤ)
    ⁅mode u m, HVertexOperator.coeff (nativeField v) (k + 3 + m)⁆ =
      ∑ n ∈ Finset.range (vectorFrequencyBound lattice v + 1),
        coeff i (commutatorReciprocal ((r : ℂ) / 3) n) • sourceCoeff u v k n := by
  dsimp only
  let m : ℤ := 3 * (i : ℤ) + (r : ℤ)
  have hm : m % 3 = (r : ℤ) := by dsimp [m]; omega
  have hc : (m : ℂ) / 3 = (i : ℂ) + (r : ℂ) / 3 := by dsimp [m]; push_cast; ring
  rw [P48qNativeCurrentCommutator.nativeField_current_commutator,
    projectAt_on_residue u r hr hu m hm, hc, ← source_sum_cutoff]
  apply finsum_congr
  intro n
  rw [commutatorReciprocal_coeff, sourceCoeff]
  rw [show k + 3 + m - m + 3 * (n : ℤ) = k + 3 * ((n : ℤ) + 1) by omega]

/-- The local numerator after multiplying the collision term of source mode
n by t^(n+1). The coordinate factor is the binomial series (1+t)^(-r/3). -/
def commutatorLocalNumerator (α : ℂ) (n : ℕ) : PowerSeries ℂ :=
  ∑ j ∈ Finset.range (n + 1), Ring.choose α j • (binomialSeries ℂ (-α) * X ^ j)

/-- The coefficient in degree d-1 after discarding the negative powers of t. -/
def regularGermCoeff (α : ℂ) (d n : ℕ) : ℂ :=
  coeff (d + n) (commutatorLocalNumerator α n)

private theorem regularGermCoeff_sum (α : ℂ) (d n : ℕ) :
    regularGermCoeff α d n =
      ∑ j ∈ Finset.range (n + 1), Ring.choose (-α) (d + j) * Ring.choose α (n - j) := by
  unfold regularGermCoeff commutatorLocalNumerator
  rw [map_sum, ← Finset.sum_range_reflect
    (fun j => coeff (d + n) (Ring.choose α j • (binomialSeries ℂ (-α) * X ^ j))) (n + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hle : n + 1 - 1 - j ≤ d + n := by omega
  rw [PowerSeries.coeff_smul, PowerSeries.coeff_mul_X_pow', ite_eq_left hle,
    PowerSeries.binomialSeries_coeff]
  simp only [Nat.add_sub_cancel, smul_eq_mul, one_mul,
    show d + n - (n - j) = d + j by omega, mul_comm]

private theorem regularGermCoeff_zero (α : ℂ) (d : ℕ+) :
    regularGermCoeff α d 0 = Ring.choose (-α) d := by
  simp [regularGermCoeff_sum]

private theorem regularGermCoeff_pair (α : ℂ) (d e : ℕ+) :
    ((e : ℕ) : ℂ) * regularGermCoeff α d e = pairJetCoeff α d e := by
  rw [regularGermCoeff_sum, pairJetCoeff, dividedKernelCoeff, Nat.sub_add_cancel d.pos]

/-- Regular part of the collision at the physical cover coefficient k. -/
def regularCollision (u : Cartan) (r : ℕ) (d : ℕ+) (v : NativeStates) (k : ℤ) :
    Module.End ℂ State :=
  ∑ᶠ n : ℕ, regularGermCoeff ((r : ℂ) / 3) d n •
    sourceCoeff u v (k + 3 * ((d : ℕ) : ℤ) - 3) n

private def signedTaylorTerm (u : Cartan) (d : ℕ+) (k : ℤ)
    (B : ℤ → Module.End ℂ State) (w : State) (m : ℤ) : State :=
  jetWeight d m • insertMode (u, m) (B (k + 3 * ((d : ℕ) : ℤ) + m)) w

private theorem signedTaylorTerm_finite (u : Cartan) (d : ℕ+) (k : ℤ)
    (B : ℤ → Module.End ℂ State) (w : State)
    (hb : BddBelow (Function.support fun j => B j w)) :
    Function.HasFiniteSupport (signedTaylorTerm u d k B w) := by
  obtain ⟨lo, hlo⟩ := hb
  refine (Finset.Icc (min 0 (lo - k - 3 * ((d : ℕ) : ℤ))) (coverBound w : ℤ)).finite_toSet.subset ?_
  intro m hm
  change m ∈ Finset.Icc _ _
  rw [Finset.mem_Icc]
  have hm' : signedTaylorTerm u d k B w m ≠ 0 := hm
  constructor
  · by_contra! h
    have hneg : m < 0 := h.trans_le (min_le_left _ _)
    have hlow : k + 3 * ((d : ℕ) : ℤ) + m < lo := by
      have := h.trans_le (min_le_right _ _)
      omega
    have hz : B (k + 3 * ((d : ℕ) : ℤ) + m) w = 0 :=
      Function.notMem_support.mp (fun hmem => (not_le_of_gt hlow) (hlo hmem))
    exact hm' (by simp only [signedTaylorTerm, insertMode_apply, ite_eq_left hneg,
      Module.End.mul_apply, hz, map_zero, smul_zero])
  · by_contra! h
    have hnonneg : ¬m < 0 := by omega
    exact hm' (by simp only [signedTaylorTerm, insertMode_apply, ite_eq_right hnonneg,
      Module.End.mul_apply, mode_eq_zero_above_coverBound w u m h,
      map_zero, smul_zero])

/-- The actual signed normal-order Taylor coefficient at physical displacement
t, with x = w(1+t) in the physical coordinates. -/
def signedNormalTaylor (u : Cartan) (d : ℕ+) (v : NativeStates) (k : ℤ) (w : State) : State :=
  ∑ᶠ m, signedTaylorTerm u d k (HVertexOperator.coeff (nativeField v)) w m

private theorem wickAt_bddBelow (a : Charge lattice) (pending kept : List Jet) (w : State) :
    BddBelow (Function.support fun j => wickAt a j pending kept w) := by
  have leafBound (xs : List Jet) : ∃ b : ℤ, ∀ j < b,
      normalOrderedCoeff a (j - 3 * (totalLevel xs : ℤ)) xs w = 0 := by
    obtain ⟨lo, hlo⟩ := normalOrderedCoeff_bddBelow a xs w
    refine ⟨lo + 3 * (totalLevel xs : ℤ), fun j hj => ?_⟩
    apply Function.notMem_support.mp
    intro h
    have hl := hlo h
    omega
  obtain ⟨lo, hlo⟩ := normalWick_zero_below (Matrix.of fun p q : Jet => pairWeight p q)
    (singletonWeight a) (fun j xs => normalOrderedCoeff a (j - 3 * (totalLevel xs : ℤ)) xs)
    w leafBound pending kept
  exact ⟨lo, fun j hj => le_of_not_gt (fun h => hj (hlo j h))⟩

set_option maxHeartbeats 1500000 in
-- The recursive proof compares pointwise finite sums of endomorphisms.
private theorem retainedHead_eq_signedTaylor (a : Charge lattice) (u : Cartan) (d : ℕ+)
    (k : ℤ) (pending kept : List Jet) (w : State) :
    wickAt a (k + 3 * ((d : ℕ) : ℤ)) pending ((u, d) :: kept) w =
      ∑ᶠ m, signedTaylorTerm u d k (fun j => wickAt a j pending kept) w m := by
  cases pending with
  | nil =>
    simp only [wickAt_nil, totalLevel, Nat.cast_add, Int.mul_add,
      normalOrderedCoeff_cons_apply, signedTaylorTerm]
    apply finsum_congr
    intro m
    rw [show k + 3 * ((d : ℕ) : ℤ) -
        (3 * ((d : ℕ) : ℤ) + 3 * (totalLevel kept : ℤ)) + 3 * ((d : ℕ) : ℤ) + m =
      k + 3 * ((d : ℕ) : ℤ) + m - 3 * (totalLevel kept : ℤ) by ring]
  | cons p tail =>
    rw [wickAt_step]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, sumErase, LinearMap.sum_apply]
    rw [List.cons_append, retainedHead_eq_signedTaylor a u d k tail (kept ++ [p]) w,
      retainedHead_eq_signedTaylor a u d k tail kept w]
    let f (xs ys : List Jet) := signedTaylorTerm u d k (fun j => wickAt a j xs ys) w
    have hf (xs ys : List Jet) : Function.HasFiniteSupport (f xs ys) :=
      signedTaylorTerm_finite u d k _ w (wickAt_bddBelow a xs ys w)
    have hpair :
        (∑ j : Fin tail.length, pairWeight p (tail.get j) •
          wickAt a (k + 3 * ((d : ℕ) : ℤ)) (tail.eraseIdx j) ((u, d) :: kept) w) =
        ∑ j : Fin tail.length, pairWeight p (tail.get j) • (∑ᶠ m, f (tail.eraseIdx j) kept m) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [retainedHead_eq_signedTaylor a u d k (tail.eraseIdx j) kept w]
    rw [hpair]
    simp only [signedTaylorTerm, wickAt_step a _ p tail kept, sumErase, map_add, map_smul,
      map_sum, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      smul_add, Finset.smul_sum, ← smul_comm (singletonWeight a p) (jetWeight d _),
      ← smul_comm (pairWeight p _) (jetWeight d _)]
    change (∑ᶠ m, f tail (kept ++ [p]) m) +
        singletonWeight a p • (∑ᶠ m, f tail kept m) +
        ∑ j : Fin tail.length, pairWeight p (tail.get j) • (∑ᶠ m, f (tail.eraseIdx j) kept m) =
      ∑ᶠ m, (f tail (kept ++ [p]) m + singletonWeight a p • f tail kept m +
        ∑ j : Fin tail.length, pairWeight p (tail.get j) • f (tail.eraseIdx j) kept m)
    have hs : Function.HasFiniteSupport (fun m => singletonWeight a p • f tail kept m) :=
      (hf tail kept).smul_right (fun _ => singletonWeight a p)
    have hp (j : Fin tail.length) : Function.HasFiniteSupport
        (fun m => pairWeight p (tail.get j) • f (tail.eraseIdx j) kept m) :=
      (hf (tail.eraseIdx j) kept).smul_right (fun _ => pairWeight p (tail.get j))
    have hsum : Function.HasFiniteSupport
        (fun m => ∑ j : Fin tail.length,
          pairWeight p (tail.get j) • f (tail.eraseIdx j) kept m) := by
      refine (Set.finite_univ.biUnion (t := fun j : Fin tail.length =>
        Function.support (fun m => pairWeight p (tail.get j) •
          f (tail.eraseIdx j) kept m))
        (fun j _ => hp j)).subset ?_
      intro m hm
      by_contra h
      apply hm
      apply Finset.sum_eq_zero
      intro j _
      by_contra hne
      exact h (Set.mem_iUnion₂.mpr ⟨j, Set.mem_univ j, hne⟩)
    have hsplit := finsum_add_distrib ((hf tail (kept ++ [p])).add hs) hsum
    simp only [Pi.add_apply] at hsplit
    rw [hsplit, finsum_add_distrib (hf tail (kept ++ [p])) hs,
      ← sum_finsum_comm _ _ (fun j _ => hp j)]
    simp only [smul_finsum]
termination_by pending.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals first | exact Nat.lt_succ_self _ | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

set_option maxHeartbeats 1000000 in
-- Compare the two exponent conventions without unfolding the Wick recursion.
private theorem allJetCoeff_eq_wickAt (a : Charge lattice) (k : ℤ) (jets : List Jet) :
    allJetCoeff a k jets = wickAt a (k + 3 * (totalLevel jets : ℤ)) jets [] := by
  unfold allJetCoeff normalWickWord wickAt leafShift
  apply congrArg (fun N => normalWick (Matrix.of fun p q : Jet => pairWeight p q)
    (singletonWeight a) N jets [])
  funext kept
  rw [show k + 3 * ((totalLevel jets : ℤ) - (totalLevel kept : ℤ)) =
    k + 3 * (totalLevel jets : ℤ) - 3 * (totalLevel kept : ℤ) by ring]

private theorem word_Taylor (a : Charge lattice) (u : Cartan) (d : ℕ+)
    (k : ℤ) (jets : List Jet) (w : State) :
    wickAt a (k + 3 * (totalLevel ((u, d) :: jets) : ℤ)) jets [(u, d)] w =
      signedNormalTaylor u d (wordState a jets) k w := by
  have hlevel : k + 3 * (totalLevel ((u, d) :: jets) : ℤ) =
      (k + 3 * (totalLevel jets : ℤ)) + 3 * ((d : ℕ) : ℤ) := by
    simp only [totalLevel, Nat.cast_add]
    ring
  rw [hlevel, retainedHead_eq_signedTaylor]
  unfold signedNormalTaylor
  apply finsum_congr
  intro m
  simp only [signedTaylorTerm, wordState_coeff, allJetCoeff_eq_wickAt]
  rw [show k + 3 * (totalLevel jets : ℤ) + 3 * ((d : ℕ) : ℤ) + m =
      k + 3 * ((d : ℕ) : ℤ) + m + 3 * (totalLevel jets : ℤ) by ring]

private theorem singletonWeight_residue (a : Charge lattice) (u : Cartan) (d : ℕ+)
    (r : ℕ) (hr : r < 3) (hu : p48qAction u = (ζ ^ r) ^ 2 • u) :
    singletonWeight a (u, d) =
      Ring.choose (-((r : ℂ) / 3)) d * p48qForm u (chargeVector a) := by
  unfold singletonWeight
  rw [Finset.sum_eq_single r]
  · rw [projectAt_on_residue u r hr hu r (by omega)]
  · intro s hs hsr
    rw [projectAt_off_residue u r hr hu (s : ℤ) (by
      have := Finset.mem_range.mp hs
      omega), map_zero, LinearMap.zero_apply, mul_zero]
  · simp [hr]

private theorem pairWeight_residue (u : Cartan) (d : ℕ+) (q : Jet) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) :
    pairWeight (u, d) q =
      pairJetCoeff ((r : ℂ) / 3) d q.2 * p48qForm u q.1 := by
  interval_cases r
  · rw [pairWeight, projectAt_off_residue u 0 (by decide) hu 1 (by decide),
      projectAt_off_residue u 0 (by decide) hu 2 (by decide)]
    simp [P48qJetContractions.pairJetCoeff_zero _ _ d.pos]
  · have hp : p48qForm u (projectAt 2 q.1) = p48qForm u q.1 := by
      rw [formSymmetric.eq u, P48qTwistedHeisenberg.projectAt_eq_fourier]
      exact (pairing_project (ζ ^ 2) q.1 u (by simpa using hu)).trans (formSymmetric.eq _ _)
    rw [pairWeight, projectAt_off_residue u 1 (by decide) hu 2 (by decide),
      projectAt_on_residue u 1 (by decide) hu 1 (by decide)]
    simp only [hp, map_zero, LinearMap.zero_apply, mul_zero, add_zero, Nat.cast_one]
  · have hp : p48qForm u (projectAt 1 q.1) = p48qForm u q.1 := by
      rw [formSymmetric.eq u, P48qTwistedHeisenberg.projectAt_eq_fourier]
      have hz : (ζ ^ 2) ^ 2 = ζ := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by decide, pow_add,
          show ζ ^ 3 = 1 by simpa only [pow_one] using root_cube 1, one_mul, pow_one]
      simpa only [show (1 % 3 : ℤ).toNat = 1 by decide, pow_one] using
        ((pairing_project ζ q.1 u (by simpa only [hz] using hu)).trans (formSymmetric.eq _ _))
    rw [pairWeight, projectAt_off_residue u 2 (by decide) hu 1 (by decide),
      projectAt_on_residue u 2 (by decide) hu 2 (by decide)]
    simp only [hp, map_zero, LinearMap.zero_apply, mul_zero, zero_add, Nat.cast_ofNat]

private theorem collisionTerm_word (a : Charge lattice) (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (d : ℕ+) (k : ℤ) (jets : List Jet) (n : ℕ) :
    regularGermCoeff ((r : ℂ) / 3) d n •
        sourceCoeff u (wordState a jets) (k + 3 * ((d : ℕ) : ℤ) - 3) n =
      (if n = 0 then singletonWeight a (u, d) •
        allJetCoeff a (k + 3 * ((d : ℕ) : ℤ)) jets else 0) +
      sumErase jets (fun q rest => if n = (q.2 : ℕ) then
        pairWeight (u, d) q • allJetCoeff a (k + 3 * (((d : ℕ) : ℤ) + (q.2 : ℕ))) rest
        else 0) := by
  unfold sourceCoeff
  cases n with
  | zero =>
    rw [show mu lattice (currentAlong lattice u) (↑(0 : ℕ) : ℤ) (wordState a jets) =
        p48qForm u (chargeVector a) • wordState a jets from mu_current_zero u a _]
    simp only [regularGermCoeff_zero, singletonWeight_residue a u d r hr hu,
      map_smul, Pi.smul_apply, wordState_coeff, smul_smul, Nat.cast_zero, zero_add,
      mul_one, sub_add_cancel, ite_true]
    have hz : (sumErase jets (fun q rest => if 0 = (q.2 : ℕ) then
        pairWeight (u, d) q • allJetCoeff a (k + 3 * (((d : ℕ) : ℤ) + (q.2 : ℕ))) rest
        else 0)) = 0 := by
      unfold sumErase
      apply Finset.sum_eq_zero
      intro j _
      dsimp only
      rw [ite_eq_right (Ne.symm (jets.get j).2.ne_zero)]
    rw [hz, add_zero]
  | succ n =>
    rw [Nat.cast_succ, mu_current_word_succ]
    simp only [Nat.succ_ne_zero, ite_false, zero_add, sumErase, map_sum,
      Finset.sum_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    let q := jets.get j
    by_cases h : n + 1 = (q.2 : ℕ)
    · rw [ite_eq_left h, ite_eq_left h, map_smul, map_smul, Pi.smul_apply,
        wordState_coeff, smul_smul, pairWeight_residue u d q r hr hu, h]
      rw [show k + 3 * ((d : ℕ) : ℤ) - 3 + 3 * ((n : ℤ) + 1 + 1) =
          k + 3 * (((d : ℕ) : ℤ) + (q.2 : ℕ)) by omega]
      congr 1
      rw [← mul_assoc, mul_comm (regularGermCoeff _ _ _), regularGermCoeff_pair]
    · rw [ite_eq_right h, ite_eq_right h, map_zero, map_zero, Pi.zero_apply, smul_zero]

private theorem regularCollision_word (a : Charge lattice) (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (d : ℕ+) (k : ℤ) (jets : List Jet) :
    regularCollision u r d (wordState a jets) k =
      singletonWeight a (u, d) • allJetCoeff a (k + 3 * ((d : ℕ) : ℤ)) jets +
      sumErase jets (fun q rest => pairWeight (u, d) q •
        allJetCoeff a (k + 3 * (((d : ℕ) : ℤ) + (q.2 : ℕ))) rest) := by
  classical
  let C := singletonWeight a (u, d) • allJetCoeff a (k + 3 * ((d : ℕ) : ℤ)) jets
  let P (j : Fin jets.length) := pairWeight (u, d) (jets.get j) •
    allJetCoeff a (k + 3 * (((d : ℕ) : ℤ) + ((jets.get j).2 : ℕ))) (jets.eraseIdx j)
  let e (j : Fin jets.length) : ℕ := (jets.get j).2
  let T := insert 0 (Finset.univ.image e)
  have h0 : 0 ∈ T := Finset.mem_insert_self _ _
  have he (j : Fin jets.length) : e j ∈ T :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem e (Finset.mem_univ j))
  unfold regularCollision
  simp_rw [collisionTerm_word a u r hr hu d k jets]
  let f (n : ℕ) := (if n = 0 then C else 0) + (∑ j, if n = e j then P j else 0)
  change (∑ᶠ n, f n) = C + ∑ j, P j
  have hs : Function.support f ⊆ (T : Set ℕ) := by
    intro n hn
    change n ∈ T
    by_contra h
    have hn0 : n ≠ 0 := fun hh => h (hh ▸ h0)
    have hne (j : Fin jets.length) : n ≠ e j := fun hh => h (hh ▸ he j)
    exact hn (by simp only [f, hn0, hne, ite_false, Finset.sum_const_zero, add_zero])
  rw [finsum_eq_sum_of_support_subset _ hs]
  simp only [f, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := T) (t := Finset.univ)]
  simp [Finset.sum_ite_eq', h0, he]

set_option maxHeartbeats 1200000 in
-- The coefficient comparison rewrites the three branches of the Wick head step.
/-- The BK negative iterate on a charged oscillator word. Its collision
part is read from the actual current commutator in the physical coordinate. -/
theorem nativeField_current_negative_word (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (d : ℕ+) (a : Charge lattice)
    (jets : List Jet) (k : ℤ) (w : State) :
    HVertexOperator.coeff
      (nativeField (mu lattice (currentAlong lattice u) (-((d : ℕ) : ℤ)) (wordState a jets))) k w =
      signedNormalTaylor u d (wordState a jets) k w +
      regularCollision u r d (wordState a jets) k w := by
  let h : ℤ := k + 3 * (totalLevel ((u, d) :: jets) : ℤ)
  let S := singletonWeight a (u, d)
  let P (j : Fin jets.length) := pairWeight (u, d) (jets.get j)
  have hsingle : wickAt a h jets [] = allJetCoeff a (k + 3 * ((d : ℕ) : ℤ)) jets := by
    rw [allJetCoeff_eq_wickAt]
    have hshift : h = k + 3 * ((d : ℕ) : ℤ) + 3 * (totalLevel jets : ℤ) := by
      simp only [h, totalLevel, Nat.cast_add]
      ring
    rw [hshift]
  have hpair (j : Fin jets.length) : wickAt a h (jets.eraseIdx j) [] =
      allJetCoeff a (k + 3 * (((d : ℕ) : ℤ) + ((jets.get j).2 : ℕ))) (jets.eraseIdx j) := by
    rw [allJetCoeff_eq_wickAt]
    have hj := congrArg (fun n : ℕ => (n : ℤ)) (totalLevel_eraseIdx jets j)
    push_cast at hj
    have hshift : h = k + 3 * (((d : ℕ) : ℤ) + ((jets.get j).2 : ℕ)) +
        3 * (totalLevel (jets.eraseIdx j) : ℤ) := by
      simp only [h, totalLevel, Nat.cast_add]
      omega
    rw [hshift]
  rw [mu_current_negative_word, wordState_coeff, allJetCoeff_eq_wickAt, wickAt_step]
  simp only [List.nil_append, LinearMap.add_apply, LinearMap.smul_apply]
  rw [regularCollision_word a u r hr hu]
  simp only [sumErase, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply]
  change wickAt a h jets [(u, d)] w + S • wickAt a h jets [] w +
      (∑ j : Fin jets.length, P j • wickAt a h (jets.eraseIdx j) [] w) =
      signedNormalTaylor u d (wordState a jets) k w +
        (S • allJetCoeff a (k + 3 * ((d : ℕ) : ℤ)) jets w +
          ∑ j : Fin jets.length, P j •
            allJetCoeff a (k + 3 * (((d : ℕ) : ℤ) + ((jets.get j).2 : ℕ))) (jets.eraseIdx j) w)
  rw [hsingle, show wickAt a h jets [(u, d)] w =
    signedNormalTaylor u d (wordState a jets) k w from word_Taylor a u d k jets w]
  simp only [hpair, add_assoc]

private theorem nativeCoeff_bddBelow (v : NativeStates) (w : State) :
    BddBelow (Function.support fun j => HVertexOperator.coeff (nativeField v) j w) := by
  refine ⟨((HahnModule.of ℂ).symm (nativeField v w)).order, ?_⟩
  intro j hj
  exact le_of_not_gt (fun h => hj (VertexOperator.coeff_eq_zero_of_lt_order (nativeField v) j w h))

private def signedNormalTaylorLinear (u : Cartan) (d : ℕ+) (k : ℤ) (w : State) :
    NativeStates →ₗ[ℂ] State where
  toFun v := signedNormalTaylor u d v k w
  map_add' v x := by
    unfold signedNormalTaylor
    rw [← finsum_add_distrib
      (signedTaylorTerm_finite u d k _ w (nativeCoeff_bddBelow v w))
      (signedTaylorTerm_finite u d k _ w (nativeCoeff_bddBelow x w))]
    apply finsum_congr
    intro m
    simp only [signedTaylorTerm, map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
  map_smul' c v := by
    unfold signedNormalTaylor
    rw [smul_finsum]
    apply finsum_congr
    intro m
    simp only [signedTaylorTerm, map_smul, Pi.smul_apply, LinearMap.smul_apply,
      RingHom.id_apply, smul_comm (jetWeight d m) c]

private theorem collisionTerm_finite (u : Cartan) (r : ℕ) (d : ℕ+) (v : NativeStates) (k : ℤ) :
    Function.HasFiniteSupport (fun n : ℕ =>
      regularGermCoeff ((r : ℂ) / 3) d n • sourceCoeff u v k n) := by
  refine (Set.finite_Iic (vectorFrequencyBound lattice v)).subset ?_
  intro n hn
  change n ≤ vectorFrequencyBound lattice v
  apply le_of_not_gt
  intro h
  apply hn
  change regularGermCoeff ((r : ℂ) / 3) d n • sourceCoeff u v k n = 0
  rw [sourceCoeff_zero_above u v k n h, smul_zero]

private def regularCollisionLinear (u : Cartan) (r : ℕ) (d : ℕ+) (k : ℤ) (w : State) :
    NativeStates →ₗ[ℂ] State where
  toFun v := regularCollision u r d v k w
  map_add' v x := by
    unfold regularCollision
    rw [← LinearMap.add_apply, ← finsum_add_distrib
      (collisionTerm_finite u r d v _) (collisionTerm_finite u r d x _)]
    apply congrArg (fun B : Module.End ℂ State => B w)
    apply finsum_congr
    intro n
    simp only [sourceCoeff, mu, map_add, Pi.add_apply, smul_add]
  map_smul' c v := by
    unfold regularCollision
    simp only [RingHom.id_apply]
    rw [← LinearMap.smul_apply, smul_finsum]
    apply congrArg (fun B : Module.End ℂ State => B w)
    apply finsum_congr
    intro n
    simp only [sourceCoeff, mu, map_smul, Pi.smul_apply, smul_comm c]

open private nativeWordPolynomial_eq_monomial from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qAllJetWickField

/-- The BK negative iterate with a current in the first slot, for arbitrary
states on both native carriers and every positive source depth. -/
theorem nativeField_current_negative_iterate (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (d : ℕ+) (v : NativeStates) (k : ℤ) (w : State) :
    HVertexOperator.coeff
      (nativeField (mu lattice (currentAlong lattice u) (-((d : ℕ) : ℤ)) v)) k w =
      signedNormalTaylor u d v k w + regularCollision u r d v k w := by
  let L : NativeStates →ₗ[ℂ] State :=
    (LinearMap.applyₗ (R := ℂ) w).comp
      (((LinearMap.proj k).comp HVertexOperator.coeff).comp
        (nativeField.comp
          ((LatticeAllStateField.Y lattice (currentAlong lattice u))[[ -((d : ℕ) : ℤ) ]])))
  let R := signedNormalTaylorLinear u d k w + regularCollisionLinear u r d k w
  change L v = R v
  suffices h : L = R from LinearMap.congr_fun h v
  apply Finsupp.lhom_ext
  intro a P
  induction P using MvPolynomial.induction_on' with
  | monomial e c =>
    classical
    let jets := (oscillatorOccurrences e).map oscillatorJet
    have hword : Finsupp.single a (MvPolynomial.monomial e c) = c • wordState a jets := by
      rw [wordState, Finsupp.smul_single]
      have he : nativeWordPolynomial (oscillatorOccurrences e) = MvPolynomial.monomial e 1 := by
        rw [nativeWordPolynomial_eq_monomial, oscillatorOccurrences, Multiset.coe_toList,
          Finsupp.toMultiset_toFinsupp]
      rw [show jets = (oscillatorOccurrences e).map oscillatorJet from rfl,
        jetWordPolynomial_map, he, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hword, map_smul, map_smul]
    exact congrArg (c • ·) (nativeField_current_negative_word u r hr hu d a jets k w)
  | add P Q ihP ihQ =>
    simp only [Finsupp.single_add, map_add, ihP, ihQ]

/-- Clearing the reciprocal denominator puts the pole polynomial in the
coordinate t = (1-y)/y. Before clearing, the factor y^(r/3+1) restores
the binomial coordinate factor and the extra power of y. -/
theorem commutatorReciprocal_clear (α : ℂ) (n : ℕ) :
    (1 - X) ^ (n + 1) * commutatorReciprocal α n =
      ∑ j ∈ Finset.range (n + 1),
        Ring.choose α (n - j) • ((1 - X) ^ (n - j) * X ^ j) := by
  unfold commutatorReciprocal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have h := Finset.mem_range.mp hj
  rw [mul_smul_comm, ← mul_assoc, show n + 1 = (n - j) + (j + 1) by omega,
    PowerSeries.one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow]

private theorem localNumerator_low (α : ℂ) (n i : ℕ) (hi : i ≤ n) :
    coeff i (commutatorLocalNumerator α n) = coeff i (1 : PowerSeries ℂ) := by
  rw [commutatorLocalNumerator, map_sum]
  let f (j : ℕ) := coeff i (Ring.choose α j • (binomialSeries ℂ (-α) * X ^ j))
  change (∑ j ∈ Finset.range (n + 1), f j) = _
  have hsub : Finset.range (i + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_mono (Nat.succ_le_succ hi)
  rw [← Finset.sum_subset hsub (f := f) (by
    intro j _ hj
    simp only [Finset.mem_range, not_lt] at hj
    have h : ¬ j ≤ i := by omega
    simp [f, PowerSeries.coeff_mul_X_pow', h])]
  have h := Ring.add_choose_eq i (Commute.all α (-α))
  rw [add_neg_cancel, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  rw [← PowerSeries.binomialSeries_zero (R := ℂ), PowerSeries.binomialSeries_coeff, h, smul_eq_mul,
    mul_one]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ i := by simpa using Finset.mem_range.mp hj
  simp only [f, PowerSeries.coeff_smul, PowerSeries.coeff_mul_X_pow', ite_eq_left hj',
    PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]

/-- Removing the actual principal part t^(-n-1) leaves a power series
with the regular coefficients used in the negative iterate. -/
theorem commutatorLocal_regular (α : ℂ) (n : ℕ) :
    PowerSeries.mk (fun i => regularGermCoeff α (i + 1) n) * X ^ (n + 1) =
      commutatorLocalNumerator α n - 1 := by
  ext i
  rw [PowerSeries.coeff_mul_X_pow', map_sub]
  by_cases hi : n + 1 ≤ i
  · rw [ite_eq_left hi, PowerSeries.coeff_mk, regularGermCoeff,
      show i - (n + 1) + 1 + n = i by omega]
    simp [PowerSeries.coeff_one, show i ≠ 0 by omega]
  · rw [ite_eq_right hi, localNumerator_low α n i (by omega), sub_self]

open private currentPolynomial correction_on_residue choose_two from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField

-- Ground-charge normalization against the checked higher current action.
example (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (d : ℕ+) (a : Charge lattice) (k : ℤ) (w : State) :
    HVertexOperator.coeff
      (nativeField (P48qHigherCurrentIterate.chargedNegativeSource a u d)) k w =
      signedNormalTaylor u d (P48qCurrentChargedIterate.chargedGround a) k w +
      P48qHigherCurrentIterate.higherCorrection a u r d k w := by
  rw [← P48qHigherCurrentIterate.source_product_negative a u d d.pos,
    nativeField_current_negative_iterate u r hr hu]
  change signedNormalTaylor u d (wordState a []) k w +
      regularCollision u r d (wordState a []) k w =
    signedNormalTaylor u d (wordState a []) k w +
      P48qHigherCurrentIterate.higherCorrection a u r d k w
  rw [regularCollision_word a u r hr hu, singletonWeight_residue a u d r hr hu]
  simp only [sumErase, List.length_nil, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    LinearMap.smul_apply, P48qHigherCurrentIterate.higherCorrection, smul_smul]
  rw [← wordState_coeff, show wordState a [] = Finsupp.single a 1 from rfl, nativeField_ground]
  rfl

set_option maxHeartbeats 1000000 in
-- Compare the three Wick leaves with the checked charged quadratic field.
example (u v : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (a : Charge lattice) (k : ℤ) :
    HVertexOperator.coeff (nativeField (mu lattice (currentAlong lattice u) (-1)
      (P48qCurrentChargedIterate.chargedFirst a v))) k =
    HVertexOperator.coeff (P48qChargedTwoCurrentIterate.stateField
      (P48qChargedTwoCurrentIterate.chargedSecond a u v)) k := by
  rw [P48qChargedTwoCurrentIterate.source_product_second]
  have source : P48qChargedTwoCurrentIterate.chargedSecond a u v =
      wordState a [(u, 1), (v, 1)] := by
    simp only [P48qChargedTwoCurrentIterate.chargedSecond, wordState, jetWordPolynomial,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, jetPolynomial,
      currentPolynomial, PNat.val_ofNat, Nat.sub_self]
  have pair : pairWeight (u, 1) (v, 1) = P48qQuadraticStateField.correction u v := by
    rw [pairWeight_residue u 1 (v, 1) r hr hu, correction_on_residue u v r hr hu,
      PNat.val_ofNat, P48qJetContractions.pairJetCoeff_one_one, choose_two]
    ring
  rw [source, wordState_coeff, allJetCoeff, P48qArbitraryWickRecursion.normalWick_two]
  have hn (q : Cartan) : normalOrderedCoeff a (k + 3) [(q, 1)] =
      P48qCurrentChargedIterate.normalOrderedCurrentCoeff a (k + 3) q :=
    (P48qJetNormalOrdering.normalOrderedCoeff_allFirst a (k + 3) [q]).trans
      (P48qSignedNormalWord.normalOrderedCoeff_singleton a (k + 3) q)
  have hnil : normalOrderedCoeff a (k + 6) [] =
      P48qThirdTwistedField.fieldCoeff P48qThirdTwistedField.fixedDualBases a (k + 6) := by
    rw [← P48qJetNormalOrdering.normalOrderedField_coeff,
      P48qJetNormalOrdering.normalOrderedField_nil]
    rfl
  have hn₂ := P48qJetNormalOrdering.normalOrderedCoeff_allFirst a k [u, v]
  change normalOrderedCoeff a k [(u, 1), (v, 1)] = _ at hn₂
  have hboth : leafShift [(u, 1), (v, 1)] [(u, 1), (v, 1)] = 0 := rfl
  have huShift : leafShift [(u, 1), (v, 1)] [(u, 1)] = 3 := rfl
  have hvShift : leafShift [(u, 1), (v, 1)] [(v, 1)] = 3 := rfl
  have hnone : leafShift [(u, 1), (v, 1)] [] = 6 := rfl
  simp only [hboth, huShift, hvShift, hnone, add_zero, Matrix.of_apply]
  rw [← source, P48qChargedTwoCurrentIterate.stateField_second_coeff,
    hn₂, P48qSignedNormalWord.normalOrderedCoeff_pair, hn u, hn v, hnil]
  simp only [singletonWeight_first, pair, neg_smul, neg_mul_neg, sub_eq_add_neg]
  rw [add_comm (P48qCurrentChargedIterate.contraction a u * _) _]
  abel

#print axioms commutatorReciprocal_clear
#print axioms commutatorLocal_regular
#print axioms nativeField_current_negative_word
#print axioms nativeField_current_negative_iterate
#print axioms mu_current_negative_word
#print axioms current_source_support
#print axioms commutatorReciprocal_native

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeNegativeCurrentIterate
