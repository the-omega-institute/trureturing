/- GID: D5/S3/StatisticalMechanics/CellularAutomata/CloitreVToothpickPrefix
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/CloitreVToothpickPrefix
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: All prefix corrections of the honeycomb V-toothpick kernel vanish. -/

import D5.S3.StatisticalMechanics.CellularAutomata.HoneycombBirthKernel

/-! The displaced-wall comparison proves that every prefix correction vanishes. -/

namespace D5.S3.StatisticalMechanics.CellularAutomata.CloitreVToothpickPrefix

open D5.S3.StatisticalMechanics.HoneycombCylinderCoordination (Vertex)
open D5.S3.StatisticalMechanics.CellularAutomata
open HoneycombFirstTouch HoneycombBirthKernel
open Polynomial
open scoped BigOperators

attribute [local instance] repositoryAdjacency

section

/-! Displaced-wall comparison of the two signed coefficients. -/

variable {G : SimpleGraph Vertex} [DecidableRel G.Adj]

private theorem support_lt_horizon {P j τ : ℕ} {v : Vertex}
    (hP : j < P) (hy : 0 ≤ v.2.2) {i : ℕ}
    (hg : g v = (τ : ℤ) - i) (support : i + v.2.2.toNat ≤ j) :
    τ + j < horizon P v := by
  unfold g at hg
  unfold horizon
  omega

private theorem birthWeight_clipped (laws : NeighborLaws G) {b m N K t : ℕ}
    (hm : 0 < m) (hN : m < N) (hK : 1 ≤ K) (upperCut : K ≤ 2 * m)
    (divides : 2 ^ b ∣ m) (first : EarliestBirths G (domain N K))
    (v : Vertex) (short : t < horizon (2 ^ b) v) :
    birthWeight G (domain N K) t v = birthWeight G (domain m K) t v := by
  have comparison := clipped_first_touch laws hm hN hK upperCut divides first t
  have equiv : Born G (domain m K) (A 0 0) t v ↔ Born G (domain N K) (A 0 0) t v := by
    by_cases shared : v ∈ domain m K
    · exact comparison.1 v shared short 1 (by decide)
    · have noneSmall : ¬ Born G (domain m K) (A 0 0) t v :=
        fun birth => shared (touch_retained_and_positive birth).1
      have noneLarge : ¬ Born G (domain N K) (A 0 0) t v :=
        fun birth => comparison.2 v (touch_retained_and_positive birth).1 shared short birth
      exact ⟨fun birth => (noneSmall birth).elim, fun birth => (noneLarge birth).elim⟩
  change (state G (domain m K) (A 0 0) t v = some (t, 1) ↔
    state G (domain N K) (A 0 0) t v = some (t, 1)) at equiv
  simp only [birthWeight, ← equiv]

/-- A forced coefficient comparison for any dyadic `P > j`, on the honeycomb. -/
private theorem prefix_shift
    (laws : NeighborLaws G)
    (first : EarliestBirthIff G) {b j c : ℕ}
    (hc : c + 2 ≤ j) (hj : j < 2 ^ b) :
    kernelEntry G j c = kernelEntry G j (c + 2 * 2 ^ b) := by
  let P := 2 ^ b
  let M := 4 * P
  let m := 3 * P
  let cHat := c + 2 * P
  let τ := 2 * m - c - 1
  let s := τ + j
  have support := signedSupport_of_neighborLaws laws
  have Ppos : 0 < P := Nat.two_pow_pos b
  have hm : 0 < m := by dsimp [m]; omega
  have hN : m < M := by dsimp [m, M]; omega
  have Mpower : 2 ^ (b + 2) = M := by rw [pow_add]; simp [M, P, Nat.mul_comm]
  have divm : 2 ^ b ∣ m := ⟨3, Nat.mul_comm 3 P⟩
  have divM : 2 ^ b ∣ M := ⟨4, Nat.mul_comm 4 P⟩
  have cutm : c < m := by change j < P at hj; dsimp [m]; omega
  have cutM : cHat < M := by change j < P at hj; dsimp [cHat, M]; omega
  have cSmall : c + 1 ≤ P := by change j < P at hj; omega
  have cutEq : ∀ ε ≤ 1, 2 * M - (cHat + ε) = 2 * m - (c + ε) := by
    intro ε _
    dsimp [M, m, cHat]
    omega
  have sBig : 2 * M - cHat - 1 + j = s := by
    dsimp [M, m, cHat, s, τ]
    omega
  have sUnshifted : 2 * M - c - 1 + j = s + 2 * P := by
    dsimp [M, m, s, τ]
    omega
  have delta_m_subset : omegaDomain m c ⊆ omegaDomain M cHat := by
    have eq0 : 2 * M - cHat = 2 * m - c := by simpa using cutEq 0 (by decide)
    unfold omegaDomain
    rw [eq0]
    exact domain_mono hN.le
  have sameBirth : ∀ ε ≤ 1, ∀ v, s < horizon P v →
      birthWeight G (omegaDomain M (cHat + ε)) s v =
        birthWeight G (omegaDomain m (c + ε)) s v := by
    intro ε he v short
    have lo : 1 ≤ 2 * m - (c + ε) := by omega
    have hi : 2 * m - (c + ε) ≤ 2 * m := by omega
    have first' : EarliestBirths G (domain M (2 * m - (c + ε))) := by
      rw [← cutEq ε he]
      intro v hv bits
      exact (first M (cHat + ε) (by omega) (by omega) v hv).mpr bits
    unfold omegaDomain
    rw [cutEq ε he]
    exact birthWeight_clipped laws hm hN lo hi divm first' v short
  have shortOfSupport : ∀ v,
      (signedWeight G M cHat s v ≠ 0 ∨ signedWeight G m c s v ≠ 0) →
      s < horizon P v := by
    intro v nonzero
    rcases nonzero with outer | inner
    · rw [← sBig] at outer
      obtain ⟨retained, i, hg, bound⟩ := support M cHat cutM j v outer
      have time : 2 * M - cHat - 1 = τ := by dsimp [M, m, cHat, τ]; omega
      rw [time] at hg
      exact support_lt_horizon hj (mem_domain.mp retained).2.1 hg bound
    · obtain ⟨retained, i, hg, bound⟩ := support m c cutm j v inner
      exact support_lt_horizon hj (mem_domain.mp retained).2.1 hg bound
  have sameSigned : ∀ v, signedWeight G M cHat s v = signedWeight G m c s v := by
    intro v
    by_cases active : signedWeight G M cHat s v ≠ 0 ∨ signedWeight G m c s v ≠ 0
    · have short := shortOfSupport v active
      have zeroCut := sameBirth 0 (by decide) v short
      have oneCut := sameBirth 1 (by decide) v short
      simpa [signedWeight, zeroCut, oneCut]
    · have zeroBig : signedWeight G M cHat s v = 0 := by
        by_contra nonzero
        exact active (Or.inl nonzero)
      have zeroSmall : signedWeight G m c s v = 0 := by
        by_contra nonzero
        exact active (Or.inr nonzero)
      rw [zeroBig, zeroSmall]
  have aligned : (delta G M cHat).coeff s = (delta G m c).coeff s := by
    rw [coeff_delta_on (fun _ hv => hv) s, coeff_delta_on delta_m_subset s]
    exact Finset.sum_congr rfl (fun v _ => sameSigned v)
  have shift : delta G M c = X ^ (2 * P) * delta G m c := by
    rw [adjacent_copy_of_earliest laws first (by omega : 0 < M) divM cSmall,
      adjacent_copy_of_earliest laws first hm divm cSmall, ← mul_assoc, ← pow_add]
    have exponents : 2 * (M - P) = 2 * P + 2 * (m - P) := by dsimp [M, m]; omega
    rw [exponents]
  have leftRead := kernelEntry_eq_coeff laws first (b := b + 2) (d := c) j (by
    rw [Mpower]
    dsimp [cHat] at cutM
    omega)
  have rightRead := kernelEntry_eq_coeff laws first (b := b + 2) (d := cHat) j (by rwa [Mpower])
  rw [Mpower, sUnshifted, shift, coeff_X_pow_mul] at leftRead
  rw [Mpower, sBig, aligned] at rightRead
  simpa [Nat.add_sub_cancel] using leftRead.trans rightRead.symm

end

/-- Equation (43) uses Euclidean remainder on the signed offset `r - j + 1`. -/
def periodIndex (j p r : ℕ) : ℕ := ((j : ℤ) - 1 + (((r : ℤ) - j + 1) % p)).toNat

private theorem prefix_period_index {j P c : ℕ} (hc : c + 2 ≤ j) (hj : j < P) :
    periodIndex j (2 * P) (c % (2 * P)) = c + 2 * P := by
  rw [Nat.mod_eq_of_lt (by omega : c < 2 * P)]
  unfold periodIndex
  have residue : ((c : ℤ) - j + 1) % ((2 * P : ℕ) : ℤ) =
      (c : ℤ) - j + 1 + ((2 * P : ℕ) : ℤ) := by
    rw [Int.emod_eq_add_self_emod]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [residue]
  omega

def columnPeriod (j : ℕ) : ℕ := 2 ^ (j.log2 + 2)

private theorem least_dyadic_above (j : ℕ) (hj : 1 ≤ j) :
    j < 2 ^ (j.log2 + 1) ∧ ∀ b, j < 2 ^ b → 2 ^ (j.log2 + 1) ≤ 2 ^ b := by
  have positive : j ≠ 0 := by omega
  refine ⟨(Nat.log2_lt positive).mp (by omega), ?_⟩
  intro b hb
  exact Nat.pow_le_pow_right (by decide)
    (Nat.succ_le_of_lt ((Nat.log2_lt positive).mpr hb))

/-- The prefix agrees with its period translate and has zero correction in equation (43). -/
theorem result {j c : ℕ} (hj : 1 ≤ j) (hc : c + 2 ≤ j) :
    birthKernelEntry j c = birthKernelEntry j (c + columnPeriod j) ∧
      birthKernelEntry j (c + columnPeriod j) =
        birthKernelEntry j (periodIndex j (columnPeriod j) (c % columnPeriod j)) ∧
      birthKernelEntry j c -
        birthKernelEntry j (periodIndex j (columnPeriod j) (c % columnPeriod j)) = 0 := by
  have above := (least_dyadic_above j hj).1
  have period : columnPeriod j = 2 * 2 ^ (j.log2 + 1) := by
    unfold columnPeriod
    rw [show j.log2 + 2 = (j.log2 + 1) + 1 by omega, pow_succ]
    exact Nat.mul_comm _ _
  rw [period, prefix_period_index hc above]
  have shift := prefix_shift repositoryNeighborLaws
    (earliestBirthIff_of_neighborLaws repositoryNeighborLaws) hc above
  exact ⟨shift, rfl, sub_eq_zero.mpr shift⟩

end D5.S3.StatisticalMechanics.CellularAutomata.CloitreVToothpickPrefix
