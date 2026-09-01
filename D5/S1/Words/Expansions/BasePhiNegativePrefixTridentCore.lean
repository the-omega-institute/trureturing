/- GID: D5/S1/Words/Expansions/BasePhiNegativePrefixTridentCore
   generality: I
   mirror-B: none(waiver:negative-base-phi-frontier)
   mirror-E: none(waiver:frontier-support-companion)
   anchors: []
   digest: Admissible negative prefixes have infinitely many canonical core occurrences. -/

import D5.S1.Words.Expansions.BasePhiNegativePrefixTridentSupport

namespace D5.X_Frontier.BasePhiNegativePrefixTrident

open D5.S0.Carrier
open D5.S1.Scale
open D5.S1.Words.Expansions.BasePhiCanonicalExpansion
open D5.S1.Words.Expansions.BasePhiNegative

noncomputable section

private noncomputable def symmetricLucasExtension
    (digits : Int →₀ Nat) (K : Nat) : Int →₀ Nat :=
  digits + Finsupp.single (K : Int) 1 + Finsupp.single (-(K : Int)) 1

private theorem negative_phiUnit_even {K : Nat} (hK : Even K) :
    (((phiUnit ^ (-(K : Int)) : GoldenIntˣ) : GoldenInt)) = conj (phi ^ K) := by
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  change (phi - 1) ^ K = conj (phi ^ K)
  have hphi : phi - 1 = -conj phi := by
    rw [conj_phi]
    abel
  rw [hphi, neg_pow]
  rw [Even.neg_one_pow hK, one_mul]
  exact (conjEquiv.map_pow phi K).symm

private theorem symmetricLucasExtension_value
    (digits : Int →₀ Nat) (K : Nat) (hK : Even K) :
    basePhiValue (symmetricLucasExtension digits K) =
      basePhiValue digits + (goldenLucas K : GoldenInt) := by
  rw [symmetricLucasExtension,
    D5.S1.Words.Expansions.BasePhiTailBounds.basePhiValue_add,
    D5.S1.Words.Expansions.BasePhiTailBounds.basePhiValue_add]
  have hpositive : basePhiValue (Finsupp.single (K : Int) 1) = phi ^ K := by
    simp [basePhiValue]
  have hnegative : basePhiValue (Finsupp.single (-(K : Int)) 1) = conj (phi ^ K) := by
    simpa [basePhiValue] using negative_phiUnit_even hK
  rw [hpositive, hnegative, add_assoc, add_conj_eq_trace]
  rfl

private theorem symmetricLucasExtension_binary
    {digits : Int →₀ Nat} {K : Nat}
    (hK : 0 < K)
    (hbinary : ∀ i : Int, digits i ≤ 1)
    (hfar : ∀ i : Int, digits i ≠ 0 →
      -((K : Nat) : Int) + 1 < i ∧ i + 1 < (K : Int)) :
    ∀ i : Int, symmetricLucasExtension digits K i ≤ 1 := by
  intro i
  by_cases hpositive : i = (K : Int)
  · subst i
    have hdigit : digits (K : Int) = 0 := by
      by_contra hne
      have := (hfar (K : Int) hne).2
      omega
    simp [symmetricLucasExtension, hdigit, hK.ne']
  · by_cases hnegative : i = -(K : Int)
    · subst i
      have hdigit : digits (-(K : Int)) = 0 := by
        by_contra hne
        have := (hfar (-(K : Int)) hne).1
        omega
      simp [symmetricLucasExtension, hdigit, hK.ne']
    · simpa [symmetricLucasExtension, hpositive, hnegative,
        Ne.symm hpositive, Ne.symm hnegative] using hbinary i

private theorem symmetricLucasExtension_canonical
    {digits : Int →₀ Nat} {K : Nat}
    (hK : 2 < K)
    (hcanonical : ∀ i : Int, digits i = 1 → digits (i + 1) = 0)
    (hfar : ∀ i : Int, digits i ≠ 0 →
      -((K : Nat) : Int) + 1 < i ∧ i + 1 < (K : Int)) :
    ∀ i : Int, symmetricLucasExtension digits K i = 1 →
      symmetricLucasExtension digits K (i + 1) = 0 := by
  intro i hi
  by_cases hpositive : i = (K : Int)
  · subst i
    have hdigit : digits ((K : Int) + 1) = 0 := by
      by_contra hne
      have := (hfar ((K : Int) + 1) hne).2
      omega
    have hnext_ne_pos : (K : Int) + 1 ≠ (K : Int) := by omega
    have hnext_ne_neg : (K : Int) + 1 ≠ -(K : Int) := by omega
    simp [symmetricLucasExtension, hdigit, hnext_ne_pos, hnext_ne_neg]
  · by_cases hnegative : i = -(K : Int)
    · subst i
      have hdigit : digits (-(K : Int) + 1) = 0 := by
        by_contra hne
        have := (hfar (-(K : Int) + 1) hne).1
        omega
      have hnext_ne_pos : -(K : Int) + 1 ≠ (K : Int) := by omega
      have hnext_ne_neg : -(K : Int) + 1 ≠ -(K : Int) := by omega
      simp [symmetricLucasExtension, hdigit, hnext_ne_pos, hnext_ne_neg]
    · have hdigit : digits i = 1 := by
        simpa [symmetricLucasExtension, hpositive, hnegative,
          Ne.symm hpositive, Ne.symm hnegative] using hi
      have hnext := hcanonical i hdigit
      have hnextPositive : i + 1 ≠ (K : Int) := by
        intro heq
        have := (hfar i (by omega)).2
        omega
      have hnextNegative : i + 1 ≠ -(K : Int) := by
        intro heq
        have := (hfar i (by omega)).1
        omega
      simp [symmetricLucasExtension, hnext,
        Ne.symm hnextPositive, Ne.symm hnextNegative]

private theorem support_radius_bounds (digits : Int →₀ Nat) :
    let radius := digits.support.sup Int.natAbs
    ∀ i : Int, digits i ≠ 0 →
      -((radius : Nat) : Int) ≤ i ∧ i ≤ (radius : Int) := by
  intro radius i hi
  have himem : i ∈ digits.support := Finsupp.mem_support_iff.mpr hi
  have habs : i.natAbs ≤ radius := Finset.le_sup (f := Int.natAbs) himem
  by_cases hnonnegative : 0 ≤ i
  · have hcast : (i.natAbs : Int) = i := by simp [Int.natAbs_of_nonneg hnonnegative]
    constructor
    · omega
    · exact hcast ▸ (Int.ofNat_le.mpr habs)
  · have hnonpositive : i ≤ 0 := le_of_not_ge hnonnegative
    have hcast : (i.natAbs : Int) = -i :=
      Int.ofNat_natAbs_of_nonpos hnonpositive
    constructor
    · have := Int.ofNat_le.mpr habs
      omega
    · exact hnonpositive.trans (Int.natCast_nonneg radius)

private theorem canonical_occurrence_unbounded {w : List Bool}
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w) :
    ∀ bound : Nat, ∃ N ∈ occurrenceSet canonicalExpansion w, bound < N := by
  classical
  obtain ⟨seed, hseedPositive, hseedPrefix⟩ := hadmissible
  let digits := canonicalDigits seed
  let radius := digits.support.sup Int.natAbs
  intro bound
  let K := 2 * (bound + radius + w.length + 5)
  have hKEven : Even K := by simp [K]
  have hKLarge : bound + radius + w.length + 4 < K := by
    dsimp [K]
    omega
  have hKPositive : 0 < K := by omega
  have hfar : ∀ i : Int, digits i ≠ 0 →
      -((K : Nat) : Int) + 1 < i ∧ i + 1 < (K : Int) := by
    intro i hi
    have hb := support_radius_bounds digits i hi
    have hKLargeInt :
        ((bound + radius + w.length + 4 : Nat) : Int) < (K : Int) := by
      exact_mod_cast hKLarge
    constructor <;> omega
  let lucasNat := (goldenLucas K).toNat
  let N := seed + lucasNat
  let extended := symmetricLucasExtension digits K
  have hlucasPositive : 0 < goldenLucas K :=
    lucas_parameter_pos ⟨K, rfl⟩
  have hlucasCast : (lucasNat : Int) = goldenLucas K := by
    exact Int.toNat_of_nonneg hlucasPositive.le
  have hlucasNatPositive : 0 < lucasNat := by
    have : (0 : Int) < (lucasNat : Int) := by rw [hlucasCast]; exact hlucasPositive
    exact_mod_cast this
  have hextendedValue : basePhiValue extended = (N : GoldenInt) := by
    rw [show extended = symmetricLucasExtension digits K by rfl,
      symmetricLucasExtension_value digits K hKEven]
    rw [show basePhiValue digits = (seed : GoldenInt) by
      exact (canonicalDigits_spec seed).2.2]
    apply GoldenInt.ext
    · simp [N, lucasNat, hlucasCast]
    · simp
  have hextendedBinary : ∀ i : Int, extended i ≤ 1 := by
    exact symmetricLucasExtension_binary hKPositive
      (canonicalDigits_spec seed).1 hfar
  have hextendedCanonical : ∀ i : Int, extended i = 1 → extended (i + 1) = 0 := by
    exact symmetricLucasExtension_canonical (by omega)
      (canonicalDigits_spec seed).2.1 hfar
  have hdigitsN : canonicalDigits N = extended := by
    apply bilateral_basePhi_injective
      (canonicalDigits_spec N).1 (canonicalDigits_spec N).2.1
      hextendedBinary hextendedCanonical
    rw [(canonicalDigits_spec N).2.2, hextendedValue]
  have hprefixN : NegativePrefixOccurs canonicalExpansion w N := by
    constructor
    · rcases hseedPrefix.1 with ⟨hdepth, i, hiSupport, hi⟩
      refine ⟨hdepth, i, ?_, hi⟩
      rw [Finsupp.mem_support_iff] at hiSupport ⊢
      change digits i ≠ 0 at hiSupport
      change canonicalDigits N i ≠ 0
      rw [hdigitsN]
      change digits i + (Finsupp.single (K : Int) 1) i +
        (Finsupp.single (-(K : Int)) 1) i ≠ 0
      omega
    · intro i
      have hindexPositive : -(((i.1 + 1 : Nat) : Int)) ≠ (K : Int) := by omega
      have hindexNegative : -(((i.1 + 1 : Nat) : Int)) ≠ -(K : Int) := by
        intro heq
        have hiLength := i.2
        push_cast at heq
        omega
      have hseedDigit := hseedPrefix.2 i
      unfold negativeDigit at hseedDigit ⊢
      change decide (digits (-(((i.1 + 1 : Nat) : Int))) = 1) =
        w.get i at hseedDigit
      change decide (canonicalDigits N (-(((i.1 + 1 : Nat) : Int))) = 1) =
        w.get i
      rw [hdigitsN]
      have hextendedAt :
          extended (-(((i.1 + 1 : Nat) : Int))) =
            digits (-(((i.1 + 1 : Nat) : Int))) := by
        have hpositive' : (K : Int) ≠ -1 + -(i.1 : Int) := by omega
        have hnegative' : -(K : Int) ≠ -1 + -(i.1 : Int) := by omega
        dsimp [extended, symmetricLucasExtension]
        simp [hpositive', hnegative']
      rw [hextendedAt]
      exact hseedDigit
  refine ⟨N, ⟨?_, hprefixN⟩, ?_⟩
  · dsimp [N, lucasNat]
    omega
  · have hKFive : 5 ≤ K := by omega
    have hLucasGe : (K : Int) ≤ goldenLucas K := by
      by_cases hzero : K = 0
      · omega
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hzero
        rw [hk] at hKFive ⊢
        change ((k + 1 : Nat) : Int) ≤ goldenLucas (k + 1)
        rw [golden_lucas_succ_eq_fib_add_fib]
        have hFibSelf : k + 2 ≤ Nat.fib (k + 2) :=
          Nat.le_fib_self (by omega)
        exact_mod_cast (show k + 1 ≤ Nat.fib k + Nat.fib (k + 2) by omega)
    have hLucasNatGe : K ≤ lucasNat := by
      have : (K : Int) ≤ (lucasNat : Int) := by rw [hlucasCast]; exact hLucasGe
      exact_mod_cast this
    dsimp [N]
    omega

theorem core_infinite_proved {w : List Bool} (hw : w ≠ [])
    (hadmissible : AdmissibleNegativePrefix canonicalExpansion w)
    (hfibers : negative_tail_fiber_shape hw hadmissible)
    (hlift : core_occurrence_unique_lift hw hadmissible hfibers) :
    (Core w).Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro bound
  obtain ⟨N, hN, hlarge⟩ :=
    canonical_occurrence_unbounded hadmissible (bound + 2)
  obtain ⟨qj, hqj, _⟩ := hlift N hN
  have hj : qj.2 < 3 := by
    have := hqj.2.1
    simp only [prefixMultiplicity] at this
    split at this <;> omega
  refine ⟨qj.1, hqj.1, ?_⟩
  omega

/-- `FrontierRunStep` sees only the enumerated source indices. In particular,
it cannot determine a next phase or a gap letter. -/
theorem frontierRunStep_phase_blind (left right : FrontierReturnWord) (n : Nat)
    (henumerate : left.enumerate = right.enumerate) :
    FrontierRunStep left n ↔ FrontierRunStep right n := by
  simp only [FrontierRunStep, frontierState, henumerate]

end

end D5.X_Frontier.BasePhiNegativePrefixTrident
