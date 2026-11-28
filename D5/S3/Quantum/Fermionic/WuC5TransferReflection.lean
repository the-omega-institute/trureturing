/- GID: D5/S3/Quantum/Fermionic/WuC5TransferReflection
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/WuC5TransferReflection
   mirror-E: none(waiver:compact-signed-matrix-identity)
   anchors: []
   utility: none
   digest: The signed five-cycle transfer has a scalar reflection product. -/

import D5.S3.HilbertOperators.WuTransferReflectionBound
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
The grouped five-cycle transfer of the signed Wu model. The two word squares
are certified by the cycle signs, including the four crossing counts for
distinct independent pairs. The occupation matrices are the private pendant
involutions of the five base vertices.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Fermionic.WuC5TransferReflection

/-- The interchange sign of two sites, including sign one for the same site. -/
def cycleSign (i j : Fin 5) : ℤ :=
  if j = i + 1 ∨ i = j + 1 then -1 else 1

/-- The five unordered independent pairs, directed by the cyclic step two. -/
def pairWord {R : Type*} [Mul R] (C : Fin 5 → R) (i : Fin 5) : R :=
  C i * C (i + 2)

private lemma cycleSign_next (i : Fin 5) : cycleSign i (i + 1) = -1 := by
  simp [cycleSign]

private lemma cycleSign_pair (i : Fin 5) : cycleSign i (i + 2) = 1 := by
  fin_cases i <;> decide

private def crossings (i j : Fin 5) : ℕ :=
  ((cycleSign i j == -1).toNat) + ((cycleSign i (j + 2) == -1).toNat) +
  ((cycleSign (i + 2) j == -1).toNat) + ((cycleSign (i + 2) (j + 2) == -1).toNat)

private lemma crossing_counts (i : Fin 5) :
    crossings i (i + 1) = 3 ∧ crossings i (i + 2) = 1 ∧
    crossings i (i + 3) = 1 ∧ crossings i (i + 4) = 3 := by
  fin_cases i <;> decide

private lemma crossing_sign (i j : Fin 5) :
    (cycleSign i j * cycleSign i (j + 2)) *
      (cycleSign (i + 2) j * cycleSign (i + 2) (j + 2)) = (-1) ^ crossings i j := by
  fin_cases i <;> fin_cases j <;> decide

private lemma pair_anticommute {R : Type*} [Ring R] {C : Fin 5 → R}
    (hsign : ∀ i j, C i * C j = cycleSign i j • (C j * C i))
    {i j : Fin 5} (hij : i ≠ j) :
    pairWord C i * pairWord C j = -(pairWord C j * pairWord C i) := by
  have swap (k l m : Fin 5) :
      C k * (C l * C m) =
        (cycleSign k l * cycleSign k m) • ((C l * C m) * C k) := by
    calc
      _ = (C k * C l) * C m := (mul_assoc _ _ _).symm
      _ = _ := by
        rw [hsign k l, smul_mul_assoc, mul_assoc, hsign k m, mul_smul_comm,
          smul_smul, mul_assoc]
  have hodd : (-1 : ℤ) ^ crossings i j = -1 := by
    obtain ⟨h1, h2, h3, h4⟩ := crossing_counts i
    have hstep : j = i + 1 ∨ j = i + 2 ∨ j = i + 3 ∨ j = i + 4 := by
      fin_cases i <;> fin_cases j <;> first | exact False.elim (hij rfl) | decide
    rcases hstep with rfl | rfl | rfl | rfl <;> simp [h1, h2, h3, h4]
  unfold pairWord
  calc
    _ = C i * (C (i + 2) * (C j * C (j + 2))) := mul_assoc _ _ _
    _ = _ := by
      rw [swap, mul_smul_comm, ← mul_assoc (C i), swap, smul_mul_assoc, smul_smul,
        mul_comm (cycleSign (i + 2) j * cycleSign (i + 2) (j + 2)), crossing_sign,
        hodd, neg_one_zsmul, mul_assoc]

private lemma five_sum_sq {R : Type*} [Ring R] (B : Fin 5 → R) :
    (∑ i, B i) ^ 2 =
      (∑ i, B i ^ 2) + (∑ i, (B i * B (i + 1) + B (i + 1) * B i)) +
        (∑ i, (B i * B (i + 2) + B (i + 2) * B i)) := by
  have sum_five (f : Fin 5 → R) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
    simp [Fin.sum_univ_succ, add_assoc]
  simp only [sum_five]
  change (B 0 + B 1 + B 2 + B 3 + B 4) ^ 2 =
    (B 0 ^ 2 + B 1 ^ 2 + B 2 ^ 2 + B 3 ^ 2 + B 4 ^ 2) +
    (B 0 * B 1 + B 1 * B 0 + (B 1 * B 2 + B 2 * B 1) + (B 2 * B 3 + B 3 * B 2) +
      (B 3 * B 4 + B 4 * B 3) + (B 4 * B 0 + B 0 * B 4)) +
    (B 0 * B 2 + B 2 * B 0 + (B 1 * B 3 + B 3 * B 1) + (B 2 * B 4 + B 4 * B 2) +
      (B 3 * B 0 + B 0 * B 3) + (B 4 * B 1 + B 1 * B 4))
  noncomm_ring

private lemma step_one_ne (i : Fin 5) : i ≠ i + 1 := by fin_cases i <;> decide
private lemma step_two_ne (i : Fin 5) : i ≠ i + 2 := by fin_cases i <;> decide

section Words

variable {K R : Type*} [CommRing K] [Ring R] [Algebra K R]

/-- The linear and quadratic words of the signed five-cycle have scalar square
remainders. This applies to the dressed words with arbitrary central squares. -/
theorem word_squares (C : Fin 5 → R) (q : Fin 5 → K)
    (hsq : ∀ i, C i ^ 2 = q i • (1 : R))
    (hsign : ∀ i j, C i * C j = cycleSign i j • (C j * C i)) :
    (∑ i, C i) ^ 2 = (∑ i, q i) • (1 : R) + 2 • (∑ i, pairWord C i) ∧
    (∑ i, pairWord C i) ^ 2 = (∑ i, q i * q (i + 2)) • (1 : R) := by
  have hcomm (i : Fin 5) : Commute (C i) (C (i + 2)) := by
    change C i * C (i + 2) = C (i + 2) * C i
    simpa only [cycleSign_pair, one_zsmul] using hsign i (i + 2)
  constructor
  · rw [five_sum_sq]
    have hadj (i : Fin 5) : C i * C (i + 1) + C (i + 1) * C i = 0 := by
      simpa only [cycleSign_next, neg_one_zsmul, neg_add_cancel, add_zero] using
        congrArg (· + C (i + 1) * C i) (hsign i (i + 1))
    simp only [hsq, ← Finset.sum_smul, hadj, Finset.sum_const_zero, add_zero,
      ← (hcomm _).eq, pairWord, Finset.sum_add_distrib, two_nsmul]
  · rw [five_sum_sq]
    have hzero {i j : Fin 5} (h : i ≠ j) :
        pairWord C i * pairWord C j + pairWord C j * pairWord C i = 0 := by
      rw [pair_anticommute hsign h, neg_add_cancel]
    have hpair (i : Fin 5) : pairWord C i ^ 2 = (q i * q (i + 2)) • (1 : R) := by
      rw [pairWord, (hcomm i).mul_pow, hsq, hsq, smul_mul_assoc, mul_smul_comm, one_mul, smul_smul]
    simp only [hpair, hzero (step_one_ne _), hzero (step_two_ne _),
      Finset.sum_const_zero, add_zero, ← Finset.sum_smul]

end Words

section Transfer

/-- The five base involutions and their commuting private occupation involutions. -/
structure SignedCycle (n : Type*) [Fintype n] [DecidableEq n] where
  base : Fin 5 → Matrix n n ℂ
  occupation : Fin 5 → Matrix n n ℂ
  base_sq : ∀ i, base i ^ 2 = 1
  occupation_sq : ∀ i, occupation i ^ 2 = 1
  base_sign : ∀ i j, base i * base j = cycleSign i j • (base j * base i)
  occupation_comm : ∀ i j, Commute (occupation i) (occupation j)
  own_sign : ∀ i, occupation i * base i = -(base i * occupation i)
  other_comm : ∀ i j, i ≠ j → Commute (occupation i) (base j)

private abbrev sites : Finset (Fin 5) := Finset.univ

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "M" => Matrix n n ℂ

variable (H : SignedCycle n) (t a : Fin 5 → ℝ)

private def weight (i : Fin 5) : M := (t i : ℂ) • H.base i

private def factor (z : ℂ) (i : Fin 5) : M := 1 + ((a i : ℂ) * z) • H.occupation i

private lemma factor_comm (z w : ℂ) (i j : Fin 5) :
    Commute (factor H a z i) (factor H a w j) :=
  ((Commute.one_left _).add_right ((Commute.one_left _).smul_right _)).add_left
    (((Commute.one_right _).smul_left _).add_right
      (((H.occupation_comm i j).smul_left _).smul_right _))

private def occupationProd {R : Type*} [Monoid R] (L : Fin 5 → R)
    (hL : ∀ i j, Commute (L i) (L j)) (s : Finset (Fin 5)) : R :=
  s.noncommProd L (fun i _ j _ _ ↦ hL i j)

private lemma factor_mul_erase {R : Type*} [Monoid R] (L : Fin 5 → R)
    (hL : ∀ i j, Commute (L i) (L j)) {i : Fin 5} {s : Finset (Fin 5)} (hi : i ∈ s) :
    L i * occupationProd L hL (s.erase i) = occupationProd L hL s :=
  Finset.mul_noncommProd_erase s hi L _

private lemma commute_occupationProd {R : Type*} [Monoid R] {L : Fin 5 → R}
    {hL : ∀ i j, Commute (L i) (L j)} {s : Finset (Fin 5)} {B : R}
    (h : ∀ j ∈ s, Commute B (L j)) : Commute B (occupationProd L hL s) :=
  Finset.noncommProd_commute s L _ B h

private def grouped {R : Type*} [Ring R] (B L : Fin 5 → R)
    (hL : ∀ i j, Commute (L i) (L j)) (z : R) : R :=
  occupationProd L hL sites +
    z * (∑ i, B i * occupationProd L hL (sites.erase i)) +
    z ^ 2 * (∑ i, pairWord B i * occupationProd L hL ((sites.erase i).erase (i + 2)))

/-- The physical transfer grouped by the empty base set, the five singletons,
and the five independent pairs. Each term retains precisely the unused occupation factors. -/
def transfer (z : ℂ) : M :=
  grouped (weight H t) (factor H a z) (factor_comm H a z z) (z • 1)

private def ell (z : ℂ) (i : Fin 5) : ℂ := 1 - (a i : ℂ) ^ 2 * z ^ 2

/-- The reflection scalar with its denominators cleared. Each term omits the
occupation factors at its selected base sites. -/
def reflectionScalar (z : ℂ) : ℂ :=
  (∏ i, ell a z i) -
    z ^ 2 * (∑ i, (t i : ℂ) ^ 2 * ∏ k ∈ sites.erase i, ell a z k) +
    z ^ 4 * (∑ i, ((t i : ℂ) ^ 2 * (t (i + 2) : ℂ) ^ 2) *
      ∏ k ∈ (sites.erase i).erase (i + 2), ell a z k)

private lemma factor_reflect (z : ℂ) (i : Fin 5) :
    factor H a (-z) i * factor H a z i = ell a z i • (1 : M) := by
  simp only [factor, ell, mul_neg, neg_smul, add_mul, mul_add, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, neg_mul, ← pow_two, H.occupation_sq]
  module

private lemma factor_weight_comm (z : ℂ) {i j : Fin 5} (hij : i ≠ j) :
    Commute (factor H a z i) (weight H t j) :=
  ((Commute.one_left _).add_left ((H.other_comm i j hij).smul_left _)).smul_right _

private lemma factor_weight_flip (z : ℂ) (i : Fin 5) :
    factor H a z i * weight H t i = weight H t i * factor H a (-z) i := by
  simp only [factor, weight, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, H.own_sign, mul_neg, neg_smul, smul_smul]
  module

private def dressed (z : ℂ) (i : Fin 5) : M :=
  (ell a z i)⁻¹ • (weight H t i * factor H a (-z) i)

private lemma ell_neg (z : ℂ) (i : Fin 5) : ell a (-z) i = ell a z i := by
  simp [ell]

private lemma dressed_factor (z : ℂ) (i : Fin 5) (hi : ell a z i ≠ 0) :
    dressed H t a z i * factor H a z i = weight H t i := by
  simp [dressed, mul_assoc, factor_reflect, smul_smul, hi]

private lemma factor_dressed (z : ℂ) (i : Fin 5) (hi : ell a z i ≠ 0) :
    factor H a z i * dressed H t a (-z) i = weight H t i := by
  rw [dressed, ell_neg, mul_smul_comm, ← mul_assoc, factor_weight_flip]
  simpa only [dressed, smul_mul_assoc, neg_neg] using dressed_factor H t a z i hi

private lemma dressed_sq (z : ℂ) (i : Fin 5) (hi : ell a z i ≠ 0) :
    dressed H t a z i ^ 2 = ((t i : ℂ) ^ 2 / ell a z i) • (1 : M) := by
  have hw : weight H t i ^ 2 = (t i : ℂ) ^ 2 • (1 : M) := by
    rw [weight, smul_pow, H.base_sq]
  have hproduct :
      (weight H t i * factor H a (-z) i) ^ 2 =
        ((t i : ℂ) ^ 2 * ell a z i) • (1 : M) := by
    calc
      _ = weight H t i * (factor H a (-z) i * weight H t i) * factor H a (-z) i := by
        simp only [pow_two, mul_assoc]
      _ = (weight H t i) ^ 2 * (factor H a z i * factor H a (-z) i) := by
        rw [factor_weight_flip H t a (-z), neg_neg, pow_two]
        simp only [mul_assoc]
      _ = _ := by
        rw [(factor_comm H a z (-z) i i).eq, factor_reflect, hw,
          smul_mul_assoc, mul_smul_one, smul_smul]
  rw [dressed, smul_pow, hproduct, smul_smul]
  congr 1
  field_simp

private lemma weight_sign (i j : Fin 5) :
    weight H t i * weight H t j = cycleSign i j • (weight H t j * weight H t i) := by
  simp only [weight, smul_mul_assoc, mul_smul_comm, smul_smul, H.base_sign i j]
  rw [mul_comm (t i : ℂ), smul_comm]

private lemma dressed_sign (z : ℂ) (i j : Fin 5) :
    dressed H t a z i * dressed H t a z j =
      cycleSign i j • (dressed H t a z j * dressed H t a z i) := by
  by_cases hij : i = j
  · subst j
    have hs : cycleSign i i = 1 := by simp [cycleSign]
    rw [hs, one_zsmul]
  have hmove (k l : Fin 5) (hkl : k ≠ l) :
      (weight H t k * factor H a (-z) k) * (weight H t l * factor H a (-z) l) =
        (weight H t k * weight H t l) * (factor H a (-z) k * factor H a (-z) l) :=
    (factor_weight_comm H t a (-z) hkl).mul_mul_mul_comm _ _
  simp only [dressed, smul_mul_assoc, mul_smul_comm, smul_smul, hmove i j hij,
    hmove j i (Ne.symm hij)]
  rw [weight_sign H t i j, (factor_comm H a (-z) (-z) i j).eq, smul_mul_assoc,
    mul_comm (ell a z i)⁻¹, smul_comm]

private def allFactors (z : ℂ) : M :=
  occupationProd (factor H a z) (factor_comm H a z z) sites

private lemma dressed_mul_prod (z : ℂ) {i : Fin 5} {s : Finset (Fin 5)}
    (hi : i ∈ s) (hne : ell a z i ≠ 0) :
    dressed H t a z i * occupationProd (factor H a z) (factor_comm H a z z) s =
      weight H t i * occupationProd (factor H a z) (factor_comm H a z z) (s.erase i) := by
  rw [← factor_mul_erase _ _ hi, ← mul_assoc, dressed_factor H t a z i hne]

private lemma prod_intertwines (z : ℂ) (i : Fin 5) (hi : ell a z i ≠ 0) :
    allFactors H a z * dressed H t a (-z) i = dressed H t a z i * allFactors H a z := by
  have h := factor_mul_erase (factor H a z) (factor_comm H a z z) (Finset.mem_univ i)
  have hc := commute_occupationProd (hL := factor_comm H a z z)
    (s := sites.erase i) (B := factor H a z i) (fun j _ ↦ factor_comm H a z z i j)
  have hw := commute_occupationProd (hL := factor_comm H a z z)
    (s := sites.erase i) (B := weight H t i)
    (fun j hj ↦ (factor_weight_comm H t a z (Finset.ne_of_mem_erase hj)).symm)
  unfold allFactors
  rw [dressed_mul_prod H t a z (Finset.mem_univ i) hi, ← h, hc.eq, mul_assoc,
    factor_dressed H t a z i hi, hw.eq]

private lemma dressed_pair_mul_prod (z : ℂ) (i : Fin 5) (hne : ∀ i, ell a z i ≠ 0) :
    pairWord (dressed H t a z) i * allFactors H a z =
      pairWord (weight H t) i *
        occupationProd (factor H a z) (factor_comm H a z z) ((sites.erase i).erase (i + 2)) := by
  let j := i + 2
  have hij : i ≠ j := step_two_ne i
  have hij' : i ∈ sites.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩
  have he : (sites.erase j).erase i = (sites.erase i).erase j := by ext; simp [and_comm]
  change (dressed H t a z i * dressed H t a z j) * allFactors H a z =
    (weight H t i * weight H t j) * _
  unfold allFactors
  rw [mul_assoc, dressed_mul_prod _ _ _ _ (Finset.mem_univ j) (hne j),
    ← factor_mul_erase _ _ hij', ← mul_assoc (weight H t j),
    ← (factor_weight_comm H t a z hij).eq, mul_assoc,
    ← mul_assoc (dressed H t a z i), dressed_factor H t a z i (hne i),
    ← mul_assoc, he]

private def wordFactor (z : ℂ) (C : Fin 5 → M) : M :=
  1 + z • (∑ i, C i) + z ^ 2 • (∑ i, pairWord C i)

private lemma transfer_dressed (z : ℂ) (hne : ∀ i, ell a z i ≠ 0) :
    transfer H t a z = wordFactor z (dressed H t a z) * allFactors H a z := by
  simp only [transfer, grouped, wordFactor, add_mul, one_mul, smul_mul_assoc, Finset.sum_mul]
  have hs (i : Fin 5) : dressed H t a z i * allFactors H a z =
      weight H t i * occupationProd (factor H a z) (factor_comm H a z z) (sites.erase i) :=
    dressed_mul_prod H t a z (Finset.mem_univ i) (hne i)
  simp_rw [hs, dressed_pair_mul_prod H t a z _ hne]
  simp [allFactors, smul_pow]

private lemma prod_intertwines_word (z : ℂ) (hne : ∀ i, ell a z i ≠ 0) :
    allFactors H a z * wordFactor (-z) (dressed H t a (-z)) =
      wordFactor (-z) (dressed H t a z) * allFactors H a z := by
  have hpair (i : Fin 5) :
      allFactors H a z * pairWord (dressed H t a (-z)) i =
        pairWord (dressed H t a z) i * allFactors H a z := by
    rw [pairWord, pairWord, ← mul_assoc, prod_intertwines H t a z i (hne i),
      mul_assoc, prod_intertwines H t a z (i + 2) (hne _), ← mul_assoc]
  simp only [wordFactor, mul_add, add_mul, one_mul, mul_one, mul_smul_comm, smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul, prod_intertwines H t a z _ (hne _), hpair]

private lemma allFactors_reflect (z : ℂ) :
    allFactors H a z * allFactors H a (-z) = (∏ i, ell a z i) • (1 : M) := by
  have h (s : Finset (Fin 5)) :
      occupationProd (factor H a z) (factor_comm H a z z) s *
        occupationProd (factor H a (-z)) (factor_comm H a (-z) (-z)) s =
          (∏ i ∈ s, ell a z i) • (1 : M) := by
    induction s using Finset.induction_on with
    | empty =>
      change (1 : M) * 1 = _
      simp
    | @insert i s hi ih =>
      have him : i ∈ insert i s := Finset.mem_insert_self _ _
      rw [← factor_mul_erase _ _ him, ← factor_mul_erase (factor H a (-z)) _ him,
        Finset.erase_insert hi]
      have hc := commute_occupationProd (hL := factor_comm H a z z) (s := s)
        (B := factor H a (-z) i) (fun j _ ↦ factor_comm H a (-z) z i j)
      rw [hc.symm.mul_mul_mul_comm, ih, (factor_comm H a z (-z) i i).eq, factor_reflect,
        Finset.prod_insert hi, smul_mul_assoc, mul_smul_one, smul_smul]
  exact h sites

private lemma wordFactor_reflect (C : Fin 5 → M) (q : Fin 5 → ℂ)
    (hsq : ∀ i, C i ^ 2 = q i • (1 : M))
    (hsign : ∀ i j, C i * C j = cycleSign i j • (C j * C i)) (z : ℂ) :
    wordFactor z C * wordFactor (-z) C =
      (1 - z ^ 2 * (∑ i, q i) + z ^ 4 * (∑ i, q i * q (i + 2))) • (1 : M) := by
  let X := ∑ i, C i
  let Y := ∑ i, pairWord C i
  let S := ∑ i, q i
  let D := ∑ i, q i * q (i + 2)
  obtain ⟨hX, hY⟩ := word_squares C q hsq hsign
  change X ^ 2 = S • (1 : M) + 2 • Y at hX
  change Y ^ 2 = D • (1 : M) at hY
  have hy : Y = (2 : ℂ)⁻¹ • (X ^ 2 - S • (1 : M)) := by
    rw [hX, two_nsmul]
    module
  have hcomm : Commute X Y := by
    rw [hy]
    exact (((Commute.refl X).pow_right 2).sub_right
      ((Commute.one_right X).smul_right S)).smul_right _
  change (1 + z • X + z ^ 2 • Y) * (1 + (-z) • X + (-z) ^ 2 • Y) = _
  calc
    _ = 1 + z ^ 2 • (2 • Y - X ^ 2) + z ^ 4 • Y ^ 2 := by
      simp only [two_nsmul, neg_pow_two, neg_smul, mul_add, add_mul, one_mul, mul_one,
        mul_neg, smul_mul_assoc, mul_smul_comm, ← pow_two, hcomm.eq]
      module
    _ = _ := by rw [hX, hY, two_nsmul]; module

private lemma transfer_reflect_of_ne (z : ℂ) (hne : ∀ i, ell a z i ≠ 0) :
    transfer H t a z * transfer H t a (-z) = reflectionScalar t a z • (1 : M) := by
  let q := fun i ↦ (t i : ℂ) ^ 2 / ell a z i
  let p := ∏ i, ell a z i
  have hneg (i : Fin 5) : ell a (-z) i ≠ 0 := by simpa only [ell_neg] using hne i
  rw [transfer_dressed H t a z hne, transfer_dressed H t a (-z) hneg, mul_assoc,
    ← mul_assoc (allFactors H a z), prod_intertwines_word H t a z hne, mul_assoc,
    allFactors_reflect H a z, ← mul_assoc,
    wordFactor_reflect (dressed H t a z) q (fun i ↦ dressed_sq H t a z i (hne i))
      (dressed_sign H t a z) z, smul_mul_assoc, one_mul, smul_smul]
  have hp₁ (i : Fin 5) : q i * p = (t i : ℂ) ^ 2 * ∏ k ∈ sites.erase i, ell a z k := by
    have hp : ell a z i * (∏ k ∈ sites.erase i, ell a z k) = p :=
      Finset.mul_prod_erase _ _ (Finset.mem_univ i)
    rw [← hp, ← mul_assoc]
    simp [q, div_mul_cancel₀ _ (hne i)]
  have hp₂ (i : Fin 5) :
      q i * q (i + 2) * p =
        ((t i : ℂ) ^ 2 * (t (i + 2) : ℂ) ^ 2) *
          ∏ k ∈ (sites.erase i).erase (i + 2), ell a z k := by
    have hj : i + 2 ∈ sites.erase i :=
      Finset.mem_erase.mpr ⟨(step_two_ne i).symm, Finset.mem_univ _⟩
    have hp : ell a z (i + 2) * (∏ k ∈ (sites.erase i).erase (i + 2), ell a z k) =
        ∏ k ∈ sites.erase i, ell a z k := Finset.mul_prod_erase _ _ hj
    calc
      _ = q (i + 2) * (q i * p) := by ring
      _ = q (i + 2) * ((t i : ℂ) ^ 2 *
          (ell a z (i + 2) * ∏ k ∈ (sites.erase i).erase (i + 2), ell a z k)) := by
        rw [hp₁, hp]
      _ = (t i : ℂ) ^ 2 * ((q (i + 2) * ell a z (i + 2)) *
          ∏ k ∈ (sites.erase i).erase (i + 2), ell a z k) := by ring
      _ = _ := by rw [show q (i + 2) * ell a z (i + 2) = (t (i + 2) : ℂ) ^ 2 from
        div_mul_cancel₀ _ (hne (i + 2)), mul_assoc]
  change ((1 - z ^ 2 * (∑ i, q i) + z ^ 4 * (∑ i, q i * q (i + 2))) * p) • _ = _
  congr 1
  simp only [reflectionScalar, add_mul, sub_mul, one_mul, mul_assoc, Finset.sum_mul, hp₁, hp₂, p]

open Polynomial in
private def polynomialFactor (i : Fin 5) : Polynomial M :=
  1 + X * C ((a i : ℂ) • H.occupation i)

open Polynomial in
private lemma polynomialFactor_comm (i j : Fin 5) :
    Commute (polynomialFactor H a i) (polynomialFactor H a j) := by
  let P : Polynomial M := C ((a i : ℂ) • H.occupation i)
  let Q : Polynomial M := C ((a j : ℂ) • H.occupation j)
  have hmat : Commute ((a i : ℂ) • H.occupation i) ((a j : ℂ) • H.occupation j) :=
    ((H.occupation_comm i j).smul_left (a i : ℂ)).smul_right (a j : ℂ)
  have hPQ : Commute P Q := hmat.map (C (R := M))
  have hX : Commute (X : Polynomial M) X := Commute.refl _
  have h : Commute (X * P) (X * Q) :=
    (hX.mul_left (commute_X P).symm).mul_right ((commute_X Q).mul_left hPQ)
  change Commute (1 + X * P) (1 + X * Q)
  exact ((Commute.one_left (1 + X * Q)).add_left
    ((Commute.one_right (X * P)).add_right h))

/-- The same grouped transfer as a polynomial with complex matrix coefficients. -/
def transferPolynomial : Polynomial M :=
  grouped (fun i ↦ Polynomial.C (weight H t i)) (polynomialFactor H a)
    (polynomialFactor_comm H a) Polynomial.X

private lemma map_occupationProd {R S : Type*} [Monoid R] [Monoid S] (f : R →* S)
    (L : Fin 5 → R) (hL : ∀ i j, Commute (L i) (L j)) (s : Finset (Fin 5)) :
    f (occupationProd L hL s) =
      occupationProd (fun i ↦ f (L i)) (fun i j ↦ (hL i j).map f) s :=
  Finset.map_noncommProd s L _ f

open Polynomial in
private def evaluate (z : ℂ) : Polynomial M →+* M :=
  Polynomial.eval₂RingHom' (RingHom.id M) (z • 1)
    (fun B ↦ (Commute.one_right B).smul_right z)

open Polynomial in
private lemma evaluate_transferPolynomial (z : ℂ) :
    evaluate z (transferPolynomial H t a) = transfer H t a z := by
  have hF (i) : evaluate z (polynomialFactor H a i) = factor H a z i := by
    have hC (B : M) : evaluate z (C B) = B := by simp [evaluate]
    have hX : evaluate z (X : Polynomial M) = z • (1 : M) := by simp [evaluate]
    simp only [polynomialFactor, factor, map_add, map_mul, map_one, hC, hX,
      smul_one_mul, smul_smul, mul_comm]
  have hP (s : Finset (Fin 5)) :
      evaluate z (occupationProd (polynomialFactor H a) (polynomialFactor_comm H a) s) =
        occupationProd (factor H a z) (factor_comm H a z z) s := by
    rw [show evaluate z _ = (evaluate z).toMonoidHom _ from rfl, map_occupationProd]
    exact Finset.noncommProd_congr rfl (fun i _ ↦ hF i) _
  have hC (B : M) : evaluate z (C B) = B := by simp [evaluate]
  have hX : evaluate z (X : Polynomial M) = z • (1 : M) := by simp [evaluate]
  simp only [transferPolynomial, transfer, grouped, map_add, map_mul, map_pow, map_sum,
    hP, hC, hX, pairWord]

open Polynomial in
private lemma continuous_transfer : Continuous (transfer H t a) := by
  let P := transferPolynomial H t a
  have hev (z : ℂ) : transfer H t a z = ∑ i ∈ P.support, P.coeff i * (z • (1 : M)) ^ i := by
    rw [← evaluate_transferPolynomial H t a z]
    change P.eval₂ (RingHom.id M) (z • 1) = _
    rw [eval₂_eq_sum]
    rfl
  rw [show transfer H t a = fun z ↦ ∑ i ∈ P.support, P.coeff i * (z • (1 : M)) ^ i from
    funext hev]
  fun_prop

private lemma dense_ell_ne : Dense {z : ℂ | ∀ i, ell a z i ≠ 0} := by
  classical
  let P (i : Fin 5) : Polynomial ℂ := 1 - Polynomial.C ((a i : ℂ) ^ 2) * Polynomial.X ^ 2
  have he (i : Fin 5) (z : ℂ) : (P i).eval z = ell a z i := by simp [P, ell]
  have hn (i : Fin 5) : P i ≠ 0 := by
    intro h
    have := he i 0
    simp [h, ell] at this
  have hf (i : Fin 5) : {z : ℂ | ell a z i = 0}.Finite := by
    refine ((P i).roots.toFinset.finite_toSet).subset ?_
    intro z hz
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hn i)).mpr (by simpa [he] using hz))
  have ht : {z : ℂ | ∃ i, ell a z i = 0}.Finite := by
    rw [show {z : ℂ | ∃ i, ell a z i = 0} = ⋃ i, {z : ℂ | ell a z i = 0} by ext; simp]
    exact Set.finite_iUnion hf
  have hd (s : Set ℂ) (hs : s.Finite) : Dense sᶜ := by
    induction s, hs using Set.Finite.induction_on with
    | empty => simp
    | @insert x s hx hs ih =>
      rw [show (insert x s)ᶜ = ({x} : Set ℂ)ᶜ ∩ sᶜ by ext; simp]
      exact (dense_compl_singleton x).inter_of_isOpen_right ih (isOpen_compl_iff.mpr hs.isClosed)
  simpa only [Set.compl_ofPred, not_exists] using hd _ ht

/-- The dressed word proof yields the exact polynomial identity at every complex
argument, including the zeros of the occupation denominators. -/
theorem transfer_reflection (z : ℂ) :
    transfer H t a z * transfer H t a (-z) = reflectionScalar t a z • (1 : M) := by
  have hl : Continuous (fun w ↦ transfer H t a w * transfer H t a (-w)) :=
    (continuous_transfer H t a).mul ((continuous_transfer H t a).comp continuous_neg)
  have hr : Continuous (fun w ↦ reflectionScalar t a w • (1 : M)) := by
    unfold reflectionScalar ell
    fun_prop
  have he : Set.EqOn (fun w ↦ transfer H t a w * transfer H t a (-w))
      (fun w ↦ reflectionScalar t a w • (1 : M)) {w | ∀ i, ell a w i ≠ 0} :=
    fun w hw ↦ transfer_reflect_of_ne H t a w hw
  exact he.closure hl hr (dense_ell_ne a z)

open Polynomial in
private lemma occupationProd_coeff_zero (s : Finset (Fin 5)) :
    (occupationProd (polynomialFactor H a) (polynomialFactor_comm H a) s).coeff 0 = 1 := by
  induction s using Finset.induction_on with
  | empty =>
    change (1 : Polynomial M).coeff 0 = 1
    simp
  | @insert i s hi ih =>
    have him : i ∈ insert i s := Finset.mem_insert_self _ _
    rw [← factor_mul_erase _ _ him, Finset.erase_insert hi, mul_coeff_zero, ih]
    simp [polynomialFactor]

open Polynomial in
private lemma occupationProd_coeff_one (s : Finset (Fin 5)) :
    (occupationProd (polynomialFactor H a) (polynomialFactor_comm H a) s).coeff 1 =
      ∑ i ∈ s, (a i : ℂ) • H.occupation i := by
  induction s using Finset.induction_on with
  | empty =>
    change (1 : Polynomial M).coeff 1 = _
    rw [← Polynomial.C_1, Polynomial.coeff_C]
    simp
  | @insert i s hi ih =>
    have him : i ∈ insert i s := Finset.mem_insert_self _ _
    rw [← factor_mul_erase _ _ him, Finset.erase_insert hi, Finset.sum_insert hi]
    simp [polynomialFactor, add_mul, mul_assoc, coeff_X_mul,
      occupationProd_coeff_zero, ih, add_comm]

/-- The linear coefficient is the weighted base Hamiltonian plus the occupation field. -/
theorem transfer_firstCoeff :
    (transferPolynomial H t a).coeff 1 =
      ∑ i, ((t i : ℂ) • H.base i + (a i : ℂ) • H.occupation i) := by
  simp [transferPolynomial, grouped, Polynomial.coeff_X_pow_mul',
    occupationProd_coeff_zero, occupationProd_coeff_one, Finset.sum_add_distrib, weight, add_comm]

/-- The linear coefficient belongs to a transfer normalized at zero. -/
theorem transfer_constantCoeff : (transferPolynomial H t a).coeff 0 = 1 := by
  simp [transferPolynomial, grouped, occupationProd_coeff_zero]

private lemma erase_next_mem (i : Fin 5) : i + 2 ∈ sites.erase i :=
  Finset.mem_erase.mpr ⟨(step_two_ne i).symm, Finset.mem_univ _⟩

private lemma card_erase_site (i : Fin 5) : (sites.erase i).card = 4 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
  decide

private lemma card_erase_pair (i : Fin 5) : ((sites.erase i).erase (i + 2)).card = 3 := by
  rw [Finset.card_erase_of_mem (erase_next_mem i), card_erase_site]

open Polynomial in
private lemma occupationProd_natDegree_le (s : Finset (Fin 5)) :
    (occupationProd (polynomialFactor H a) (polynomialFactor_comm H a) s).natDegree ≤ s.card := by
  have hf (i) : (polynomialFactor H a i).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le (by simp)
    exact natDegree_mul_le.trans (by simpa using (natDegree_X_le (R := M)))
  induction s using Finset.induction_on with
  | empty =>
    change (1 : Polynomial M).natDegree ≤ (∅ : Finset (Fin 5)).card
    simp
  | @insert i s hi ih =>
    have him : i ∈ insert i s := Finset.mem_insert_self _ _
    rw [← factor_mul_erase _ _ him, Finset.erase_insert hi, Finset.card_insert_of_notMem hi]
    exact natDegree_mul_le.trans (Nat.add_le_add (hf i) ih |>.trans_eq (Nat.add_comm _ _))

open Polynomial in
private lemma transfer_natDegree_le : (transferPolynomial H t a).natDegree ≤ 5 := by
  unfold transferPolynomial grouped
  have h₀ : (occupationProd (polynomialFactor H a) (polynomialFactor_comm H a) sites).natDegree
      ≤ 5 := occupationProd_natDegree_le H a sites
  have h₁ : (∑ i, C (weight H t i) *
      occupationProd (polynomialFactor H a) (polynomialFactor_comm H a) (sites.erase i)).natDegree
      ≤ 4 := by
    refine natDegree_sum_le_of_forall_le _ _ fun i _ ↦ natDegree_mul_le.trans ?_
    simpa [card_erase_site] using occupationProd_natDegree_le H a (sites.erase i)
  have h₂ : (∑ i, pairWord (fun j ↦ C (weight H t j)) i *
      occupationProd (polynomialFactor H a) (polynomialFactor_comm H a)
        ((sites.erase i).erase (i + 2))).natDegree ≤ 3 := by
    refine natDegree_sum_le_of_forall_le _ _ fun i _ ↦ natDegree_mul_le.trans ?_
    simpa [pairWord, ← map_mul, card_erase_pair] using
      occupationProd_natDegree_le H a ((sites.erase i).erase (i + 2))
  apply natDegree_add_le_of_degree_le
  · apply natDegree_add_le_of_degree_le h₀
    exact natDegree_mul_le.trans (Nat.add_le_add natDegree_X_le h₁)
  · exact natDegree_mul_le.trans (by have := natDegree_X_pow_le (R := M) 2; omega)

open Polynomial in
/-- Evaluating the actual C5 matrix coefficients through the spectral consumer's
evaluation function gives the grouped transfer. -/
theorem transferEval_eq (z : ℂ) :
    D5.S3.HilbertOperators.WuTransferReflectionBound.transferEval
      (transferPolynomial H t a).coeff 5 z = transfer H t a z := by
  rw [← evaluate_transferPolynomial H t a z]
  change _ = (transferPolynomial H t a).eval₂ (RingHom.id M) (z • 1)
  rw [eval₂_eq_sum, sum_over_range' _ (fun _ ↦ zero_mul _) 6 (by
    exact Nat.lt_succ_of_le (transfer_natDegree_le H t a))]
  unfold D5.S3.HilbertOperators.WuTransferReflectionBound.transferEval
  apply Finset.sum_congr rfl
  intro k _
  rw [RingHom.id_apply, smul_pow, one_pow, mul_smul_one]

/-- For a common occupation weight, setting `l = 1 - a₀² z²` gives the
scalar reflection factor `l³ (l² - z² l S + z⁴ D)`. -/
theorem transfer_reflection_common (a₀ : ℝ) (z : ℂ) :
    let l := 1 - (a₀ : ℂ) ^ 2 * z ^ 2
    let S := ∑ i : Fin 5, (t i : ℂ) ^ 2
    let D := ∑ i : Fin 5, (t i : ℂ) ^ 2 * (t (i + 2) : ℂ) ^ 2
    transfer H t (fun _ ↦ a₀) z * transfer H t (fun _ ↦ a₀) (-z) =
      (l ^ 3 * (l ^ 2 - z ^ 2 * l * S + z ^ 4 * D)) • (1 : M) := by
  dsimp only
  rw [transfer_reflection, reflectionScalar]
  simp only [ell, Finset.prod_const, card_erase_site, card_erase_pair]
  congr 1
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hcard : sites.card = 5 := by decide
  rw [hcard]
  ring

end Transfer

end D5.S3.Quantum.Fermionic.WuC5TransferReflection
