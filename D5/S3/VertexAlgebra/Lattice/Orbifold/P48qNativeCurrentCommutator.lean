/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeCurrentCommutator
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The current commutator of signed normal-order coefficients from mode insertion. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeMonodromy

/-! Current-mode commutators of the actual arbitrary-level P48q twisted fields. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentCommutator

open LatticeGeneratingFieldLocality (Charge)
open P48qTwistedChargeAction (lattice)
open P48qThirdTwistedField (Cartan State chargeVector concreteChargedField)
open ThirdEigenspacePairing (p48qForm)
open P48qTwistedHeisenberg (mode projectAt mode_commutator mode_fieldCoeff_commutator)
open P48qSignedNormalWord (Indices insertMode insertMode_apply)
open P48qJetNormalOrdering (jetWeight jetTerm jetTerm_cons jetTerm_finite
  normalOrderedCoeff normalOrderedCoeff_cons_apply normalOrderedField_coeff normalOrderedField_nil)
open P48qAllJetWickField (Jet totalLevel leafShift allJetCoeff allJetField nativeField
  singletonWeight pairWeight)
open P48qArbitraryWickRecursion (normalWick normalWickWord normalWick_nil normalWick_step)
open private sumErase sumErase_cons sumErase_add smul_sumErase sumErase_twice_swap
  normalWick_cons_sumErase from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qWickPermutation

/-- The scalar from the Heisenberg central term for a single retained jet. -/
def slotWeight (h : Cartan) (m : ℤ) (p : Jet) : ℂ :=
  jetWeight p.2 (-m) * ((m : ℂ) / 3 * p48qForm (projectAt m h) p.1)

private def chargeWeight (h : Cartan) (m : ℤ) (a : Charge lattice) : ℂ :=
  p48qForm (projectAt m h) (chargeVector a)

private def shift (p : Jet) : ℤ := 3 * ((p.2 : ℕ) : ℤ)

private theorem end_lie_mul (A B C : Module.End ℂ State) :
    ⁅A, B * C⁆ = ⁅A, B⁆ * C + B * ⁅A, C⁆ := by
  simp only [Ring.lie_def]
  noncomm_ring

private theorem insertMode_lie (h : Cartan) (m : ℤ) (u : Cartan) (n : ℤ)
    (B : Module.End ℂ State) :
    ⁅mode h m, insertMode (u, n) B⁆ =
      insertMode (u, n) ⁅mode h m, B⁆ +
        (if n = -m then ((m : ℂ) / 3 * p48qForm (projectAt m h) u) • B else 0) := by
  have hc : ⁅mode h m, mode u n⁆ =
      if n = -m then ((m : ℂ) / 3 * p48qForm (projectAt m h) u) •
        (1 : Module.End ℂ State) else 0 := by
    rw [mode_commutator]
    simp only [show (m + n = 0) ↔ n = -m by omega]
  simp only [insertMode_apply]
  split <;> rw [end_lie_mul, hc] <;> split <;>
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, zero_mul, mul_zero,
      add_zero, add_comm]

private def headTerm (a : Charge lattice) (k : ℤ) (p : Jet) (tail : List Jet)
    (n : ℤ) : Module.End ℂ State :=
  jetWeight p.2 n • insertMode (p.1, n) (normalOrderedCoeff a (k + shift p + n) tail)

private theorem headTerm_row (a : Charge lattice) (k : ℤ) (p : Jet) (tail : List Jet)
    (n : ℤ) (w : State) :
    headTerm a k p tail n w = ∑ᶠ rest, jetTerm a k (p :: tail) (n, rest) w := by
  let j := k + shift p + n
  simp only [headTerm, jetTerm_cons, LinearMap.smul_apply, insertMode_apply]
  by_cases hn : n < 0
  · simp only [ite_eq_left hn, Module.End.mul_apply]
    change jetWeight p.2 n • mode p.1 n (∑ᶠ i, jetTerm a j tail i w) =
      ∑ᶠ i, jetWeight p.2 n • mode p.1 n (jetTerm a j tail i w)
    rw [map_finsum (mode p.1 n) (jetTerm_finite a j tail w)]
    exact smul_finsum' _ ((jetTerm_finite a j tail w).subset (by
      intro i hi hz
      exact hi (by simp [hz])))
  · simp only [ite_eq_right hn, Module.End.mul_apply]
    exact smul_finsum' _ (jetTerm_finite a j tail (mode p.1 n w))

private theorem headTerm_finite (a : Charge lattice) (k : ℤ) (p : Jet) (tail : List Jet)
    (w : State) : Function.HasFiniteSupport (fun n => headTerm a k p tail n w) := by
  refine ((jetTerm_finite a k (p :: tail) w).image Prod.fst).subset ?_
  intro n hn
  by_contra h
  apply hn
  change headTerm a k p tail n w = 0
  rw [headTerm_row]
  apply finsum_eq_zero_of_forall_eq_zero
  intro rest
  by_contra hrest
  exact h ⟨(n, rest), hrest, rfl⟩

private theorem normal_cons (a : Charge lattice) (k : ℤ) (p : Jet)
    (tail : List Jet) (w : State) :
    normalOrderedCoeff a k (p :: tail) w = ∑ᶠ n, headTerm a k p tail n w :=
  normalOrderedCoeff_cons_apply a k p tail w

private theorem end_lie_smul (A B : Module.End ℂ State) (c : ℂ) :
    ⁅A, c • B⁆ = c • ⁅A, B⁆ := by
  simp only [Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub]

private theorem headTerm_lie (h : Cartan) (m : ℤ) (a : Charge lattice) (k : ℤ)
    (p : Jet) (tail : List Jet) (n : ℤ) :
    ⁅mode h m, headTerm a k p tail n⁆ =
      jetWeight p.2 n • insertMode (p.1, n)
        ⁅mode h m, normalOrderedCoeff a (k + shift p + n) tail⁆ +
        (if n = -m then slotWeight h m p • normalOrderedCoeff a (k - m + shift p) tail
          else 0) := by
  rw [headTerm, end_lie_smul, insertMode_lie, smul_add]
  congr 1
  by_cases hn : n = -m
  · subst n
    simp only [ite_true, smul_smul, slotWeight]
    rw [show k + shift p + -m = k - m + shift p by omega]
  · simp only [ite_eq_right hn, smul_zero]

private theorem lie_apply (A B : Module.End ℂ State) (w : State) :
    ⁅A, B⁆ w = A (B w) - B (A w) := rfl

private theorem finite_smul (c : ℂ) {f : ℤ → State}
    (hf : Function.HasFiniteSupport f) : Function.HasFiniteSupport (fun n => c • f n) :=
  hf.subset (by intro n hn hz; exact hn (by simp [hz]))

private theorem finite_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ → State)
    (hf : ∀ i ∈ s, Function.HasFiniteSupport (f i)) :
    Function.HasFiniteSupport (fun n => ∑ i ∈ s, f i n) := by
  refine (s.finite_toSet.biUnion (t := fun i => Function.support (f i))
    (fun i hi => hf i hi)).subset ?_
  intro n hn
  by_contra hz
  apply hn
  apply Finset.sum_eq_zero
  intro i hi
  by_contra hne
  exact hz (Set.mem_iUnion₂.mpr ⟨i, hi, hne⟩)

private theorem headTerm_add (a : Charge lattice) (k : ℤ) (p : Jet)
    (tail : List Jet) (n : ℤ) (c : ℂ) (s : Jet → ℂ) (m : ℤ) :
    jetWeight p.2 n • insertMode (p.1, n)
      (c • normalOrderedCoeff a (k + shift p + n - m) tail +
        sumErase tail (fun q rest => s q •
          normalOrderedCoeff a (k + shift p + n - m + shift q) rest)) =
    c • headTerm a (k - m) p tail n +
      sumErase tail (fun q rest => s q • headTerm a (k - m + shift q) p rest n) := by
  simp only [map_add, map_smul, smul_add, sumErase, map_sum, Finset.smul_sum]
  rw [smul_comm (jetWeight p.2 n) c]
  apply congrArg₂ (· + ·)
  · rw [headTerm, show k + shift p + n - m = k - m + shift p + n by omega]
  · apply Finset.sum_congr rfl
    intro j _
    rw [headTerm, smul_comm (jetWeight p.2 n) (s (tail.get j)),
      show k + shift p + n - m + shift (tail.get j) =
        k - m + shift (tail.get j) + shift p + n by omega]

set_option maxHeartbeats 800000 in
/-- All signed normal-order jet words satisfy the current commutator.
Every deletion is a separate occurrence, including repeated jet labels. -/
theorem normalOrderedCoeff_commutator (h : Cartan) (m : ℤ) (a : Charge lattice)
    (k : ℤ) (jets : List Jet) :
    ⁅mode h m, normalOrderedCoeff a k jets⁆ =
      chargeWeight h m a • normalOrderedCoeff a (k - m) jets +
        sumErase jets (fun p rest =>
          slotWeight h m p • normalOrderedCoeff a (k - m + shift p) rest) := by
  induction jets generalizing k with
  | nil =>
    simp only [sumErase, List.length_nil, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rw [← normalOrderedField_coeff, ← normalOrderedField_coeff, normalOrderedField_nil]
    exact mode_fieldCoeff_commutator h a m k
  | cons p tail ih =>
    classical
    apply LinearMap.ext
    intro w
    rw [lie_apply, normal_cons, normal_cons, map_finsum _ (headTerm_finite a k p tail w),
      ← finsum_sub_distrib
        ((headTerm_finite a k p tail w).subset (by
          intro n hn hz
          exact hn (by simp [hz])))
        (headTerm_finite a k p tail (mode h m w))]
    simp only [← lie_apply]
    let c := chargeWeight h m a
    let F (n : ℤ) := c • headTerm a (k - m) p tail n w
    let G (j : Fin tail.length) (n : ℤ) :=
      slotWeight h m (tail.get j) •
        headTerm a (k - m + shift (tail.get j)) p (tail.eraseIdx j) n w
    let D (n : ℤ) := if n = -m then
      slotWeight h m p • normalOrderedCoeff a (k - m + shift p) tail w else 0
    have hF : Function.HasFiniteSupport F :=
      finite_smul c (headTerm_finite a (k - m) p tail w)
    have hG (j : Fin tail.length) : Function.HasFiniteSupport (G j) :=
      finite_smul _ (headTerm_finite a _ p _ w)
    have hsum : Function.HasFiniteSupport (fun n => ∑ j : Fin tail.length, G j n) :=
      finite_sum Finset.univ G (fun j _ => hG j)
    have hD : Function.HasFiniteSupport D := by
      refine (Set.finite_singleton (-m)).subset ?_
      intro n hn
      by_contra hne
      have hn' : n ≠ -m := hne
      exact hn (by simp [D, hn'])
    calc
      _ = ∑ᶠ n : ℤ, ((F n + ∑ j : Fin tail.length, G j n) + D n) := by
        apply finsum_congr
        intro n
        rw [headTerm_lie, ih, headTerm_add]
        simp only [LinearMap.add_apply, LinearMap.smul_apply, sumErase, LinearMap.sum_apply,
          F, G, c, D]
        by_cases hn : n = -m
        · simp only [ite_eq_left hn, LinearMap.smul_apply]
        · simp only [ite_eq_right hn, LinearMap.zero_apply]
      _ = (∑ᶠ n, F n) + (∑ᶠ n : ℤ, (∑ j : Fin tail.length, G j n)) +
          D (-m) := by
        have hsplit : (∑ᶠ n : ℤ, ((F n + ∑ j : Fin tail.length, G j n) + D n)) =
            (∑ᶠ n : ℤ, (F n + ∑ j : Fin tail.length, G j n)) + (∑ᶠ n, D n) :=
          finsum_add_distrib (hF.add hsum) hD
        rw [hsplit, finsum_add_distrib hF hsum,
          finsum_eq_single D (-m) (by intro n hn; simp [D, hn])]
      _ = _ := by
        have hfirst : (∑ᶠ n, F n) = c • normalOrderedCoeff a (k - m) (p :: tail) w := by
          rw [normal_cons]
          exact (smul_finsum' c (headTerm_finite a (k - m) p tail w)).symm
        have hrest : (∑ᶠ n : ℤ, (∑ j : Fin tail.length, G j n)) =
            ∑ j : Fin tail.length, slotWeight h m (tail.get j) •
              normalOrderedCoeff a (k - m + shift (tail.get j)) (p :: tail.eraseIdx j) w := by
          rw [← sum_finsum_comm _ _ (fun j _ => hG j)]
          apply Finset.sum_congr rfl
          intro j _
          rw [normal_cons]
          exact (smul_finsum' _ (headTerm_finite a _ p _ w)).symm
        rw [hfirst, hrest]
        rw [sumErase_cons]
        simp only [LinearMap.add_apply, LinearMap.smul_apply, sumErase,
          LinearMap.sum_apply, D, c, ite_true, eq_self]
        abel

#print axioms normalOrderedCoeff_commutator

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentCommutator
