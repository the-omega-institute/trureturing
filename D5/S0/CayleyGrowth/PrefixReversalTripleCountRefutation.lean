/- GID: D5/S0/CayleyGrowth/PrefixReversalTripleCountRefutation
   generality: G
   mirror-B: D5/B/S0/CayleyGrowth/PrefixReversalTripleCountRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A congruence sieve refutes the proposed prefix-reversal triple asymptotic. -/

/-
admission_basis: open-problem-resolution (#22875; Refuted)
escape_witness: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23187
Direct frozen dependencies (declaration identities, not module pins):
F1: D5/S0/CayleyGrowth/PrefixReversalTripleEvenNonGeneration.even_prefix_reversal_triple_ne_top
  statement_id: sha256:66c2460134fc263f54e1cfa99cbfef567541354974090ae632065423a60c23d1
F2: D5/S0/CayleyGrowth/PrefixReversalTripleOddNonGeneration.reverseIndex
  statement_id: sha256:67a36ab155f25a49fb000f1633e700498aa841c8b7840f7ebcaf826250761e69
F3: D5/S0/CayleyGrowth/PrefixReversalTripleOddNonGeneration.prefixReversal
  statement_id: sha256:12aafb76aaac90c1d859479e20f175a109e975c529088fc5c62386617c039073
F4: D5/S0/CayleyGrowth/PrefixReversalTripleOddNonGeneration.tripleSubgroup
  statement_id: sha256:926f9e2b0557a6f5a6eb7cc4c643478d86a2c8b44f343e84066dd3dd0a5c42f7
F5: D5/S0/CayleyGrowth/PrefixReversalTripleOddNonGeneration.reverseIndex_involutive
  statement_id: sha256:cff3178773254840b3480e7971394207bc191806b434e7d27cd505bbd5194d24
The rows inline same-delivery helpers when identifying frozen dependencies.
Every row has escape_witness: none; admission uses the settling result.
Declaration classifications and consumers:
f: proof_shape: bind-only; frozen: F4.
  consumers: claim,generatingPairs_card,result,sieve_count_bound,uniform_sieve_bound.
leadingCoefficient: proof_shape: bind-only; frozen: none.
  consumers: claim,result.
claim: proof_shape: bind-only; frozen: F4.
  consumers: result.
generation_triangle: proof_shape: bind-only; frozen: F1,F4.
  consumers: generatingPairs_properties.
triple_preserves_relation: proof_shape: content; frozen: F3,F4.
  consumers: generation_opposite_parity.
reversal_preserves_adjacent_pairs: proof_shape: bind-only; frozen: F3,F2.
  consumers: generation_opposite_parity.
reversal_preserves_parity: proof_shape: bind-only; frozen: F3,F2.
  consumers: generation_opposite_parity.
full_reversal_preserves_parity_relation: proof_shape: bind-only; frozen: F3,F2.
  consumers: generation_opposite_parity.
generation_opposite_parity: proof_shape: content; frozen: F3,F2,F4.
  consumers: generatingPairs_properties.
reversal_mod_invariant: proof_shape: bind-only; frozen: F3,F2,F5.
  consumers: generation_mod_obstruction.
generation_mod_obstruction: proof_shape: content; frozen: F3,F2,F5,F4.
  consumers: generatingPairs_properties.
reversal_sign: proof_shape: content; frozen: F3,F2.
  consumers: generation_odd_generator.
generation_odd_generator: proof_shape: content; frozen: F3,F2,F4.
  consumers: generatingPairs_properties.
modulus: proof_shape: bind-only; frozen: none.
  consumers: admissible,card_admissible,card_localAllowed,generatingPairs_properties,localAllowed,moduli_product,modulus_dvd,modulus_pos,residueEquiv,residuePairEquiv.
sieveModulus: proof_shape: bind-only; frozen: none.
  consumers: admissible,card_admissible,generatingPairs_properties,moduli_product,modulus_dvd,residueEquiv,residuePairEquiv,result,sieve_count_bound,uniform_sieve_bound.
modulus_pos: proof_shape: bind-only; frozen: none.
  consumers: card_localAllowed,generatingPairs_properties,residueEquiv,residueEquiv_apply.
moduli_product: proof_shape: bind-only; frozen: none.
  consumers: residueEquiv.
residueEquiv: proof_shape: bind-only; frozen: none.
  consumers: residueEquiv_apply,residuePairEquiv.
residueEquiv_apply: proof_shape: bind-only; frozen: none.
  consumers: generatingPairs_properties.
residuePairEquiv: proof_shape: bind-only; frozen: none.
  consumers: admissible,card_admissible,generatingPairs_properties.
fourCondition: proof_shape: bind-only; frozen: none.
  consumers: card_fourCondition,card_localAllowed,fourConditionDecidable,generatingPairs_properties,localAllowed.
fourConditionDecidable: proof_shape: bind-only; frozen: none.
  consumers: card_fourCondition.
localAllowed: proof_shape: bind-only; frozen: none.
  consumers: admissible,card_admissible,card_localAllowed,generatingPairs_properties.
admissible: proof_shape: bind-only; frozen: none.
  consumers: card_admissible,generatingPairs_properties,sieve_count_bound.
card_fourCondition: proof_shape: bind-only; frozen: none.
  consumers: card_localAllowed.
card_localAllowed: proof_shape: bind-only; frozen: none.
  consumers: card_admissible.
card_admissible: proof_shape: bind-only; frozen: none.
  consumers: sieve_count_bound.
residue_interval_card: proof_shape: content; frozen: none.
  consumers: lattice_bound.
separated_sum_bound: proof_shape: content; frozen: none.
  consumers: lattice_bound.
lattice_bound: proof_shape: content; frozen: none.
  consumers: sieve_count_bound.
generatingPairs: proof_shape: bind-only; frozen: F4.
  consumers: generatingPairs_card,generatingPairs_properties,sieve_count_bound.
generatingPairs_card: proof_shape: bind-only; frozen: F4.
  consumers: sieve_count_bound.
modulus_dvd: proof_shape: bind-only; frozen: none.
  consumers: generatingPairs_properties.
generatingPairs_properties: proof_shape: content; frozen: F1,F3,F2,F5,F4.
  consumers: sieve_count_bound.
sieve_count_bound: proof_shape: content; frozen: F1,F3,F2,F5,F4.
  consumers: uniform_sieve_bound.
uniform_sieve_bound: proof_shape: content; frozen: F1,F3,F2,F5,F4.
  consumers: result.
result: proof_shape: content; frozen: F1,F3,F2,F5,F4.
  consumers: terminal result.
The source's count and asymptotic clauses retain their stated expressions.
Positions j in {1,...,n} correspond to i = j - 1 in Fin n.
The existing permutation and generated-subgroup owners supply that action.
-/

import D5.S0.CayleyGrowth.PrefixReversalTripleOddNonGeneration
import D5.S0.CayleyGrowth.PrefixReversalTripleEvenNonGeneration
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace D5.S0.CayleyGrowth.PrefixReversalTripleCountRefutation

open PrefixReversalTripleOddNonGeneration

/-!
The source acts on {1,...,n}. The existing owner acts on Fin n, with the
correspondence j = i + 1. Its prefixReversal L hL sends i < L to L - 1 - i
and fixes the other indices. Its tripleSubgroup is the subgroup closure of
exactly the three reversals; equality with top means the full symmetric group.
These existing definitions are reused directly, without replacement aliases.
-/

/-- The source's explicit finite count of pairs (m,k), with 2 ≤ k < m < n. -/
noncomputable def f (n : ℕ) : ℕ :=
  Nat.card {p : Fin n × Fin n //
    2 ≤ p.2.val ∧ p.2.val < p.1.val ∧
      tripleSubgroup n p.1.val p.2.val
        (Nat.le_of_lt p.1.isLt) (Nat.le_of_lt p.2.isLt) = ⊤}

/-- The four leading constants in Conjecture 1, indexed by n modulo four. -/
noncomputable def leadingCoefficient (q : Fin 4) : ℝ :=
  match q.val with
  | 0 => 1 / 13
  | 1 => 1 / 9
  | 2 => 1 / 10
  | _ => 1 / 7

/-- Conjecture 1, with each residue-class O(n) written with all quantifiers. -/
def claim : Prop :=
  ∀ q : Fin 4, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → n % 4 = q.val →
      |(f n : ℝ) - leadingCoefficient q * (n : ℝ) ^ 2| ≤ C * (n : ℝ)

open scoped Pointwise
open PrefixReversalTripleOddNonGeneration
open PrefixReversalTripleEvenNonGeneration


private lemma generation_triangle {n m k : ℕ} (hk : 2 ≤ k) (hkm : k < m) (hmn : m < n)
    (hn : n % 2 = 0)
    (hgen : tripleSubgroup n m k (by omega) (by omega) = ⊤) : n ≤ m + k := by
  by_contra h
  exact even_prefix_reversal_triple_ne_top hk hkm hmn (Nat.even_iff.mpr hn)
    (by omega) hgen

private lemma triple_preserves_relation {n m k : ℕ} (hm : m ≤ n) (hk : k ≤ n)
    (R : Fin n → Fin n → Prop)
    (hnR : ∀ i j, R (prefixReversal n le_rfl i) (prefixReversal n le_rfl j) ↔ R i j)
    (hmR : ∀ i j, R (prefixReversal m hm i) (prefixReversal m hm j) ↔ R i j)
    (hkR : ∀ i j, R (prefixReversal k hk i) (prefixReversal k hk j) ↔ R i j)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ tripleSubgroup n m k hm hk) :
    ∀ i j, R (g i) (g j) ↔ R i j := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact hnR
    · exact hmR
    · exact hkR
  | one => intro i j; rfl
  | mul g h _ _ ihg ihh =>
    intro i j
    exact (ihg (h i) (h j)).trans (ihh i j)
  | inv g _ ih =>
    intro i j
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using (ih (g.symm i) (g.symm j)).symm

private lemma reversal_preserves_adjacent_pairs {n L : ℕ} (hL : L ≤ n) (he : L % 2 = 0)
    (i j : Fin n) :
    (prefixReversal L hL i).val / 2 = (prefixReversal L hL j).val / 2 ↔
      i.val / 2 = j.val / 2 := by
  change (reverseIndex L hL i).val / 2 = (reverseIndex L hL j).val / 2 ↔ _
  by_cases hi : i.val < L <;> by_cases hj : j.val < L <;>
    simp only [reverseIndex, hi, hj, dite_true, dite_false] <;> omega

private lemma reversal_preserves_parity {n L : ℕ} (hL : L ≤ n) (ho : L % 2 = 1)
    (i : Fin n) : (prefixReversal L hL i).val % 2 = i.val % 2 := by
  change (reverseIndex L hL i).val % 2 = _
  by_cases hi : i.val < L <;> simp only [reverseIndex, hi, dite_true, dite_false] <;> omega

private lemma full_reversal_preserves_parity_relation {n : ℕ} (i j : Fin n) :
    (prefixReversal n le_rfl i).val % 2 = (prefixReversal n le_rfl j).val % 2 ↔
      i.val % 2 = j.val % 2 := by
  change (reverseIndex n le_rfl i).val % 2 = (reverseIndex n le_rfl j).val % 2 ↔ _
  have hi := i.isLt
  have hj := j.isLt
  simp only [reverseIndex, dite_eq_left hi, dite_eq_left hj]
  omega

private lemma generation_opposite_parity {n m k : ℕ} (hn : 4 ≤ n)
    (hm : m ≤ n) (hk : k ≤ n) (he : n % 2 = 0)
    (hgen : tripleSubgroup n m k hm hk = ⊤) : m % 2 ≠ k % 2 := by
  intro hsame
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  have hmem (g : Equiv.Perm (Fin n)) : g ∈ tripleSubgroup n m k hm hk := by
    rw [hgen]; trivial
  by_cases hm0 : m % 2 = 0
  · have h := triple_preserves_relation hm hk (fun i j => i.val / 2 = j.val / 2)
      (reversal_preserves_adjacent_pairs le_rfl he)
      (reversal_preserves_adjacent_pairs hm hm0)
      (reversal_preserves_adjacent_pairs hk (by omega)) (hmem (Equiv.swap b c)) a b
    norm_num [a, b, c, Equiv.swap_apply_def] at h
  · have hm1 : m % 2 = 1 := by exact Nat.mod_two_ne_zero.mp hm0
    have hk1 : k % 2 = 1 := by omega
    have h := triple_preserves_relation hm hk (fun i j => i.val % 2 = j.val % 2)
      full_reversal_preserves_parity_relation
      (fun i j => by rw [reversal_preserves_parity hm hm1, reversal_preserves_parity hm hm1])
      (fun i j => by rw [reversal_preserves_parity hk hk1, reversal_preserves_parity hk hk1])
      (hmem (Equiv.swap a b)) a c
    norm_num [a, b, c, Equiv.swap_apply_def] at h



private lemma reversal_mod_invariant {n L p : ℕ} (hL : L ≤ n) (hcong : L % p = n % p)
    (i : Fin n) :
    ((prefixReversal L hL i).val % p = 0 ∨
      ((prefixReversal L hL i).val + 1) % p = n % p) ↔
    (i.val % p = 0 ∨ (i.val + 1) % p = n % p) := by
  have forward (i : Fin n) (hiS : i.val % p = 0 ∨ (i.val + 1) % p = n % p) :
      (prefixReversal L hL i).val % p = 0 ∨
        ((prefixReversal L hL i).val + 1) % p = n % p := by
    change (reverseIndex L hL i).val % p = 0 ∨
      ((reverseIndex L hL i).val + 1) % p = n % p
    by_cases hi : i.val < L
    · simp only [reverseIndex, dite_eq_left hi]
      have hsum : i.val + (L - 1 - i.val + 1) = L := by omega
      have hsum' : (i.val + 1) + (L - 1 - i.val) = L := by omega
      rcases hiS with hzero | hlast
      · right
        have hzero' : Nat.ModEq p i.val 0 := by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Eq.symm hzero)) rfl)
        have hh : Nat.ModEq p (i.val + (L - 1 - i.val + 1)) (0 + n) := by
          simpa [hsum, Nat.ModEq] using hcong
        exact hzero'.add_left_cancel hh
      · left
        have hlast' : Nat.ModEq p (i.val + 1) n := hlast
        have hh : Nat.ModEq p ((i.val + 1) + (L - 1 - i.val)) (n + 0) := by exact Nat.ModEq.trans (congrFun (congrArg HMod.hMod hsum') p) hcong
        simpa [Nat.ModEq] using hlast'.add_left_cancel hh
    · simpa only [reverseIndex, dite_eq_right hi] using hiS
  constructor
  · intro hi
    have hh := forward (prefixReversal L hL i) hi
    change (reverseIndex L hL (reverseIndex L hL i)).val % p = 0 ∨
      ((reverseIndex L hL (reverseIndex L hL i)).val + 1) % p = n % p at hh
    simpa only [reverseIndex_involutive hL i] using hh
  · exact forward i

private lemma generation_mod_obstruction {n m k p : ℕ} (hp : 3 ≤ p) (hn : p ≤ n)
    (hm : m ≤ n) (hk : k ≤ n)
    (hgen : tripleSubgroup n m k hm hk = ⊤) :
    ¬ (m % p = n % p ∧ k % p = n % p) := by
  classical
  rintro ⟨hmp, hkp⟩
  let S : Set (Fin n) := {i | i.val % p = 0 ∨ (i.val + 1) % p = n % p}
  have generator (L : ℕ) (hL : L ≤ n) (hc : L % p = n % p) :
      prefixReversal L hL ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) S := by
    rw [MulAction.mem_stabilizer_iff]
    change prefixReversal L hL '' S = S
    ext i
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact (reversal_mod_invariant hL hc j).mpr hj
    · intro hi
      refine ⟨prefixReversal L hL i, (reversal_mod_invariant hL hc i).mpr hi, ?_⟩
      exact reverseIndex_involutive hL i
  have hle : tripleSubgroup n m k hm hk ≤
      MulAction.stabilizer (Equiv.Perm (Fin n)) S := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact generator n le_rfl rfl
    · exact generator m hm hmp
    · exact generator k hk hkp
  let a : Fin n := ⟨0, by omega⟩
  have ha : a ∈ S := by simp [S, a]
  obtain ⟨b, hb⟩ : ∃ b : Fin n, b ∉ S := by
    by_cases h : n % p = 2
    · refine ⟨⟨2, by omega⟩, ?_⟩
      simp only [S, Set.mem_ofPred_eq, not_or]
      constructor
      · rw [Nat.mod_eq_of_lt (by omega : 2 < p)]; omega
      · by_cases hp3 : p = 3
        · subst p; norm_num [h]
        · rw [Nat.mod_eq_of_lt (by omega : 3 < p), h]; omega
    · refine ⟨⟨1, by omega⟩, ?_⟩
      simp only [S, Set.mem_ofPred_eq, not_or]
      constructor
      · rw [Nat.mod_eq_of_lt (by omega : 1 < p)]; omega
      · simpa only [Nat.mod_eq_of_lt (by omega : 2 < p)] using Ne.symm h
  have hs : Equiv.swap a b ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) S :=
    hle (by rw [hgen]; trivial)
  exact hb ((Equiv.swap_mem_stabilizer.mp hs).mp ha)

open PrefixReversalTripleOddNonGeneration
open scoped BigOperators

private lemma reversal_sign {n L : ℕ} (hL : L ≤ n) :
    Equiv.Perm.sign (prefixReversal L hL) = (-1 : ℤˣ) ^ (L / 2) := by
  classical
  have hsmall (i : Fin n) (h : prefixReversal L hL i ≠ i) : i.val < L := by
    by_contra hi
    apply h
    change reverseIndex L hL i = i
    simp [reverseIndex, hi]
  have hnotmid (i : Fin n) (h : prefixReversal L hL i ≠ i) : L - 1 - i.val ≠ i.val := by
    intro hh
    apply h
    apply Fin.ext
    change (reverseIndex L hL i).val = i.val
    simp [reverseIndex, hsmall i h, hh]
  let code : ∀ i : Fin n, prefixReversal L hL i ≠ i → Fin (L / 2) × Fin 2 :=
    fun i h => (⟨min i.val (L - 1 - i.val), by
      have hs := hsmall i h
      have hn := hnotmid i h
      omega⟩, if i.val < L / 2 then 0 else 1)
  let flip : Equiv.Perm (Fin (L / 2) × Fin 2) :=
    Equiv.prodCongrRight fun _ => Equiv.swap (0 : Fin 2) 1
  have hsign : Equiv.Perm.sign (prefixReversal L hL) = Equiv.Perm.sign flip := by
    apply Equiv.Perm.sign_bij code
    · intro i hi hi'
      have hs := hsmall i hi
      have hn := hnotmid i hi
      have hv : (prefixReversal L hL i).val = L - 1 - i.val := by
        simp [prefixReversal, reverseIndex, hs]
      apply Prod.ext
      · apply Fin.ext
        dsimp [code, flip]
        rw [hv]
        omega
      · dsimp [code, flip]
        by_cases hh : i.val < L / 2
        · have hh' : ¬(prefixReversal L hL i).val < L / 2 := by omega
          simp [hh, hh']
        · have hh' : (prefixReversal L hL i).val < L / 2 := by omega
          simp [hh, hh']
    · intro i j hi hj hc
      have hiS := hsmall i hi
      have hjS := hsmall j hj
      have ha := congrArg (fun z : Fin (L / 2) × Fin 2 => z.1.val) hc
      have hb := congrArg (fun z : Fin (L / 2) × Fin 2 => z.2.val) hc
      dsimp [code] at ha hb
      apply Fin.ext
      split_ifs at hb <;> omega
    · intro y hy
      rcases y with ⟨a, b⟩
      fin_cases b
      · let i : Fin n := ⟨a.val, by have := a.isLt; omega⟩
        have hi : prefixReversal L hL i ≠ i := by
          intro hh
          have hv := congrArg Fin.val hh
          have ha := a.isLt
          dsimp [i, prefixReversal, reverseIndex] at hv
          split_ifs at hv <;> simp only at hv <;> omega
        refine ⟨i, hi, ?_⟩
        apply Prod.ext
        · apply Fin.ext
          dsimp [code, i]
          have := a.isLt
          omega
        · dsimp [code, i]
          simp [a.isLt]
      · let i : Fin n := ⟨L - 1 - a.val, by have := a.isLt; omega⟩
        have hi : prefixReversal L hL i ≠ i := by
          intro hh
          have hv := congrArg Fin.val hh
          have ha := a.isLt
          dsimp [i, prefixReversal, reverseIndex] at hv
          split_ifs at hv <;> simp only at hv <;> omega
        refine ⟨i, hi, ?_⟩
        apply Prod.ext
        · apply Fin.ext
          dsimp [code, i]
          have := a.isLt
          omega
        · dsimp [code, i]
          have ha := a.isLt
          have hh : ¬ L - 1 - a.val < L / 2 := by omega
          simp [hh]
  rw [hsign]
  dsimp [flip]
  rw [Equiv.Perm.sign_prodCongrRight]
  simp [Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]

private lemma generation_odd_generator {n m k : ℕ} (hn : 2 ≤ n)
    (hm : m ≤ n) (hk : k ≤ n) (hn4 : n % 4 = 0)
    (hgen : tripleSubgroup n m k hm hk = ⊤) :
    m % 4 = 2 ∨ m % 4 = 3 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
  classical
  by_contra h
  push Not at h
  have sign_one (L : ℕ) (hL : L ≤ n) (hr : L % 4 ≠ 2 ∧ L % 4 ≠ 3) :
      Equiv.Perm.sign (prefixReversal L hL) = 1 := by
    rw [reversal_sign]
    apply Even.neg_one_pow
    apply Nat.even_iff.mpr
    omega
  have hle : tripleSubgroup n m k hm hk ≤ (Equiv.Perm.sign : _ →* ℤˣ).ker := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact sign_one n le_rfl (by omega)
    · exact sign_one m hm ⟨h.1, h.2.1⟩
    · exact sign_one k hk ⟨h.2.2.1, h.2.2.2⟩
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hs := hle (show Equiv.swap a b ∈ tripleSubgroup n m k hm hk by rw [hgen]; trivial)
  have hab : a ≠ b := by exact not_eq_of_beq_eq_false rfl
  change Equiv.Perm.sign (Equiv.swap a b) = 1 at hs
  rw [Equiv.Perm.sign_swap hab] at hs
  norm_num at hs

open scoped BigOperators Function

private def modulus (i : Fin 8) : ℕ :=
  match i.val with
  | 0 => 4 | 1 => 3 | 2 => 5 | 3 => 7 | 4 => 11 | 5 => 13 | 6 => 17 | _ => 19
private def sieveModulus : ℕ := 19399380

private lemma modulus_pos (i : Fin 8) : 0 < modulus i := by
  fin_cases i <;> decide
private lemma moduli_product : ((List.finRange 8).map modulus).prod = sieveModulus := by exact Nat.eq_of_beq_eq_true rfl

private noncomputable def residueEquiv : Fin sieveModulus ≃ ((i : Fin 8) → Fin (modulus i)) := by
  letI : NeZero sieveModulus := ⟨by decide⟩
  letI (i : Fin 8) : NeZero (modulus i) := ⟨(modulus_pos i).ne'⟩
  have hprod : (∏ i : Fin 8, modulus i) = sieveModulus := by
    simpa only [Fin.prod_univ_def] using moduli_product
  letI : NeZero (∏ i : Fin 8, modulus i) := ⟨by rw [hprod]; decide⟩
  have hcop : Pairwise (Nat.Coprime on modulus) := by
    intro i j hij
    change Nat.Coprime (modulus i) (modulus j)
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
  exact (finCongr hprod.symm).trans
    ((ZMod.finEquiv _).toEquiv.trans
      ((ZMod.prodEquivPi modulus hcop).toEquiv.trans
        (Equiv.piCongrRight fun i => (ZMod.finEquiv (modulus i)).symm.toEquiv)))

private lemma residueEquiv_apply (x : Fin sieveModulus) (i : Fin 8) :
    residueEquiv x i = ⟨x.val % modulus i, Nat.mod_lt _ (modulus_pos i)⟩ := by
  letI : NeZero (∏ i : Fin 8, modulus i) := ⟨by
    rw [show (∏ i : Fin 8, modulus i) = sieveModulus by
      simpa only [Fin.prod_univ_def] using moduli_product]
    decide⟩
  have finEquiv_val (n : ℕ) [NeZero n] (a : Fin n) :
      (ZMod.finEquiv n a).val = a.val := by
    cases n with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  have finEquiv_symm_val (n : ℕ) [NeZero n] (a : ZMod n) :
      ((ZMod.finEquiv n).symm a).val = a.val := by
    cases n with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  apply Fin.ext
  symm
  change x.val % modulus i = _
  simp only [residueEquiv, Equiv.trans_apply, Equiv.piCongrRight_apply,
    RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, Pi.map, finEquiv_symm_val,
    ZMod.prodEquivPi_apply, ZMod.castHom_apply, ZMod.cast_eq_val,
    ZMod.val_natCast, finEquiv_val, finCongr_apply_coe]
  erw [ZMod.prodEquivPi_apply]
  simp only [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast,
    finEquiv_val, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, finCongr_apply_coe]
  all_goals erw [ZMod.cast_eq_val, ZMod.val_natCast, finEquiv_val, finCongr_apply_coe]

private noncomputable def residuePairEquiv : (Fin sieveModulus × Fin sieveModulus) ≃
    ((i : Fin 8) → Fin (modulus i) × Fin (modulus i)) :=
  (residueEquiv.prodCongr residueEquiv).trans
    (Equiv.arrowProdEquivProdArrow (Fin 8) (fun i => Fin (modulus i))
      (fun i => Fin (modulus i))).symm

private def fourCondition (m k : ℕ) : Prop :=
  m % 2 ≠ k % 2 ∧ (m = 2 ∨ m = 3 ∨ k = 2 ∨ k = 3)

private instance fourConditionDecidable (m k : ℕ) : Decidable (fourCondition m k) := by
  unfold fourCondition; infer_instance

private def localAllowed (n : ℕ) (i : Fin 8) (x : Fin (modulus i) × Fin (modulus i)) : Prop :=
  if i = 0 then fourCondition x.1.val x.2.val
  else ¬ (x.1.val = n % modulus i ∧ x.2.val = n % modulus i)

private def admissible (n : ℕ) (x : Fin sieveModulus × Fin sieveModulus) : Prop :=
  ∀ i, localAllowed n i (residuePairEquiv x i)

private lemma card_fourCondition : Nat.card {x : Fin 4 × Fin 4 // fourCondition x.1.val x.2.val} = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

private lemma card_localAllowed (n : ℕ) (i : Fin 8) :
    Nat.card {x : Fin (modulus i) × Fin (modulus i) // localAllowed n i x} =
      if i = 0 then 6 else modulus i ^ 2 - 1 := by
  classical
  by_cases hi : i = 0
  · subst i
    rw [ite_eq_left rfl]
    exact (Nat.card_congr (Equiv.subtypeEquivRight
      (fun (x : Fin 4 × Fin 4) => show localAllowed n 0 x ↔ fourCondition x.1.val x.2.val from Iff.rfl))).trans
        card_fourCondition
  · simp only [localAllowed, ite_eq_right hi]
    have he : Fintype.card {x : Fin (modulus i) × Fin (modulus i) //
        x.1.val = n % modulus i ∧ x.2.val = n % modulus i} = 1 := by
      let a : Fin (modulus i) := ⟨n % modulus i, Nat.mod_lt _ (modulus_pos i)⟩
      have hpred (x : Fin (modulus i) × Fin (modulus i)) :
          (x.1.val = n % modulus i ∧ x.2.val = n % modulus i) ↔ x = (a, a) := by
        constructor
        · rintro ⟨h1, h2⟩
          exact Prod.ext (Fin.ext h1) (Fin.ext h2)
        · intro h; rw [h]; exact ⟨rfl, rfl⟩
      simp_rw [hpred]
      exact Fintype.card_subtype_eq _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, he, Fintype.card_prod, Fintype.card_fin]
    simp [pow_two]

private lemma card_admissible (n : ℕ) :
    Nat.card {x : Fin sieveModulus × Fin sieveModulus // admissible n x} =
      115579079884800 := by
  classical
  let e : {x : Fin sieveModulus × Fin sieveModulus // admissible n x} ≃
      ((i : Fin 8) → {x : Fin (modulus i) × Fin (modulus i) // localAllowed n i x}) :=
    (residuePairEquiv.subtypeEquiv (fun x => Iff.rfl)).trans Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_pi]
  simp_rw [card_localAllowed]
  decide

open scoped BigOperators

private lemma residue_interval_card (s : Finset ℕ) {M lo hi : ℕ}
    (hlo : ∀ x ∈ s, lo ≤ x) (hhi : ∀ x ∈ s, x ≤ hi)
    (hmod : ∀ x ∈ s, ∀ y ∈ s, x % M = y % M) :
    s.card * M ≤ hi - lo + M := by
  classical
  let code : s × Fin M → Fin (hi - lo + M) := fun z =>
    ⟨z.1.val + z.2.val - lo, by
      have hl := hlo z.1.val z.1.prop
      have hh := hhi z.1.val z.1.prop
      have hj := z.2.isLt
      omega⟩
  have hinj : Function.Injective code := by
    intro x y h
    have hv := congrArg Fin.val h
    have hxlo := hlo x.1.val x.1.prop
    have hylo := hlo y.1.val y.1.prop
    have hxj := x.2.isLt
    have hyj := y.2.isLt
    have heq : x.1.val + x.2.val = y.1.val + y.2.val := by
      dsimp [code] at hv
      omega
    have hmods : Nat.ModEq M x.1.val y.1.val := hmod _ x.1.prop _ y.1.prop
    have hjmod : Nat.ModEq M x.2.val y.2.val :=
      hmods.add_left_cancel (congrArg (fun a => a % M) heq)
    have hj : x.2.val = y.2.val := by exact Nat.ModEq.eq_of_lt_of_lt hjmod hxj hyj
    apply Prod.ext
    · apply Subtype.ext
      omega
    · exact Fin.ext hj
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective code hinj

private lemma separated_sum_bound (s : Finset ℕ) (D : ℝ)
    (hgap : ∀ x ∈ s, ∀ y ∈ s, x < y → (x : ℝ) + D ≤ y) :
    ∀ U : ℝ, (∀ x ∈ s, (x : ℝ) ≤ U) →
      2 * (∑ x ∈ s, (x : ℝ)) ≤
        2 * U * s.card - D * s.card * ((s.card : ℝ) - 1) := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | @insert a s hmax ih =>
    intro U hU
    have ha : a ∉ s := by intro h; have := hmax a h; omega
    have hgapS : ∀ x ∈ s, ∀ y ∈ s, x < y → (x : ℝ) + D ≤ y := by
      intro x hx y hy hxy
      exact hgap x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    have hb : ∀ x ∈ s, (x : ℝ) ≤ (a : ℝ) - D := by
      intro x hx
      have hh := hgap x (Finset.mem_insert_of_mem hx) a (Finset.mem_insert_self _ _) (hmax x hx)
      linarith
    have hsum := ih hgapS ((a : ℝ) - D) hb
    have hau := hU a (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    push_cast
    have ht : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hau) (show 0 ≤ (s.card : ℝ) + 1 by positivity)]



private lemma lattice_bound (S : Finset (ℕ × ℕ)) (n M : ℕ) (hM : 0 < M)
    (hreg : ∀ p ∈ S, p.2 < p.1 ∧ p.1 < n ∧ n ≤ p.1 + p.2)
    (hresM : ∀ p ∈ S, ∀ q ∈ S, p.1 % M = q.1 % M)
    (hresK : ∀ p ∈ S, ∀ q ∈ S, p.2 % M = q.2 % M) :
    4 * (M : ℝ) ^ 2 * S.card ≤ ((n : ℝ) + 2 * M) ^ 2 := by
  classical
  let T := S.image Prod.fst
  let U (m : ℕ) := (S.filter (fun p => p.1 = m)).image Prod.snd
  have memU {m x : ℕ} (hx : x ∈ U m) : (m, x) ∈ S := by
    rcases Finset.mem_image.mp hx with ⟨p, hp, he⟩
    have hh := Finset.mem_filter.mp hp
    simpa only [← hh.2, ← he] using hh.1
  have exists_row {m : ℕ} (hm : m ∈ T) : ∃ k, (m, k) ∈ S := by
    rcases Finset.mem_image.mp hm with ⟨p, hp, rfl⟩
    exact ⟨p.2, hp⟩
  have row_bound (m : ℕ) (hm : m ∈ T) :
      (M : ℝ) * (U m).card ≤ 2 * (m : ℝ) - n + M := by
    obtain ⟨k, hmk⟩ := exists_row hm
    have hr := hreg (m, k) hmk
    have hnm : n - m ≤ m := by omega
    have hc := residue_interval_card (U m) (M := M) (lo := n - m) (hi := m)
      (fun x hx => by have := hreg (m, x) (memU hx); dsimp at this; omega)
      (fun x hx => by have := hreg (m, x) (memU hx); dsimp at this; omega)
      (fun x hx y hy => hresK (m, x) (memU hx) (m, y) (memU hy))
    have hcR : ((U m).card : ℝ) * M ≤ ((m - (n - m) + M : ℕ) : ℝ) := by
      exact_mod_cast hc
    rw [Nat.cast_add, Nat.cast_sub hnm, Nat.cast_sub hr.2.1.le] at hcR
    nlinarith
  have hcount : (S.card : ℝ) = ∑ m ∈ T, ((U m).card : ℝ) := by
    have hu (m : ℕ) : (U m).card = (S.filter (fun p => p.1 = m)).card := by
      apply Finset.card_image_of_injOn
      intro p hp q hq he
      exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he
    have hh := Finset.card_eq_sum_card_image Prod.fst S
    simp_rw [← hu] at hh
    exact_mod_cast hh
  have hsep : ∀ x ∈ T, ∀ y ∈ T, x < y → (x : ℝ) + M ≤ y := by
    intro x hx y hy hxy
    obtain ⟨k, hmk⟩ := exists_row hx
    obtain ⟨l, hml⟩ := exists_row hy
    have hh := Nat.ModEq.add_le_of_lt (hresM (x, k) hmk (y, l) hml) hxy
    exact_mod_cast hh
  have hupper : ∀ x ∈ T, (x : ℝ) ≤ n := by
    intro x hx
    obtain ⟨k, hmk⟩ := exists_row hx
    exact_mod_cast (hreg (x, k) hmk).2.1.le
  have hsum := separated_sum_bound T (M : ℝ) hsep (n : ℝ) hupper
  have hrows := Finset.sum_le_sum (s := T) row_bound
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul] at hrows
  rw [← hcount] at hrows
  have hMr : 0 < (M : ℝ) := by exact Nat.cast_pos'.mpr hM
  have hMt : 0 ≤ (M : ℝ) := hMr.le
  have hsquare := sq_nonneg ((M : ℝ) * T.card - ((n : ℝ) + 2 * M) / 2)
  have hh : (M : ℝ) * S.card ≤
      -(M : ℝ) * (T.card : ℝ) ^ 2 + ((n : ℝ) + 2 * M) * T.card := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 4 * M by positivity)]

set_option maxRecDepth 2000

open scoped BigOperators
open PrefixReversalTripleOddNonGeneration

private noncomputable def generatingPairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p =>
    2 ≤ p.2.val ∧ p.2.val < p.1.val ∧ tripleSubgroup n p.1.val p.2.val
      (Nat.le_of_lt p.1.isLt) (Nat.le_of_lt p.2.isLt) = ⊤)).image
        (fun p => (p.1.val, p.2.val))

private lemma generatingPairs_card (n : ℕ) : (generatingPairs n).card = f n := by
  classical
  unfold generatingPairs f
  rw [Finset.card_image_of_injective]
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  · intro p q hpq
    exact Prod.ext (Fin.ext (congrArg Prod.fst hpq)) (Fin.ext (congrArg Prod.snd hpq))

private lemma modulus_dvd (i : Fin 8) : modulus i ∣ sieveModulus := by
  fin_cases i <;> norm_num [modulus, sieveModulus]

private lemma generatingPairs_properties {n : ℕ} (hn : sieveModulus ≤ n) (hn4 : n % 4 = 0)
    {p : ℕ × ℕ} (hp : p ∈ generatingPairs n) :
    (p.2 < p.1 ∧ p.1 < n ∧ n ≤ p.1 + p.2) ∧ admissible n (Prod.map (@Fin.ofNat sieveModulus ⟨by decide⟩) (@Fin.ofNat sieveModulus ⟨by decide⟩) p) := by
  classical
  rcases Finset.mem_image.mp hp with ⟨x, hx, rfl⟩
  have hh := (Finset.mem_filter.mp hx).2
  have hn2 : n % 2 = 0 := by omega
  have hn4min : 4 ≤ n := by exact Nat.le_of_add_left_le hn
  have htriangle := generation_triangle hh.1 hh.2.1 x.1.isLt hn2 hh.2.2
  refine ⟨⟨hh.2.1, x.1.isLt, htriangle⟩, ?_⟩
  have hpar := generation_opposite_parity hn4min
    (Nat.le_of_lt x.1.isLt) (Nat.le_of_lt x.2.isLt) hn2 hh.2.2
  have hsign := generation_odd_generator (by omega : 2 ≤ n)
    (Nat.le_of_lt x.1.isLt) (Nat.le_of_lt x.2.isLt) hn4 hh.2.2
  intro i
  change localAllowed n i (residueEquiv _ i, residueEquiv _ i)
  rw [residueEquiv_apply, residueEquiv_apply]
  change localAllowed n i
    (⟨(x.1.val % sieveModulus) % modulus i, _⟩,
     ⟨(x.2.val % sieveModulus) % modulus i, _⟩)
  dsimp only [localAllowed]
  split_ifs with hi
  · subst i
    change fourCondition ((x.1.val % sieveModulus) % 4) ((x.2.val % sieveModulus) % 4)
    simp only [fourCondition, Nat.mod_mod_of_dvd _ (by decide : 4 ∣ sieveModulus)]
    constructor
    · omega
    · exact hsign
  · have hpi : 3 ≤ modulus i := by fin_cases i <;> decide
    have hpn : modulus i ≤ n := by
      have hl : modulus i ≤ sieveModulus := Nat.le_of_dvd (by decide) (modulus_dvd i)
      omega
    have hm := generation_mod_obstruction hpi hpn
      (Nat.le_of_lt x.1.isLt) (Nat.le_of_lt x.2.isLt) hh.2.2
    simpa only [Nat.mod_mod_of_dvd _ (modulus_dvd i)] using hm

private lemma sieve_count_bound {n : ℕ} (hn : sieveModulus ≤ n) (hn4 : n % 4 = 0) :
    4 * (sieveModulus : ℝ) ^ 2 * f n ≤
      115579079884800 * ((n : ℝ) + 2 * sieveModulus) ^ 2 := by
  classical
  obtain ⟨R, hRdef⟩ : ∃ R : Finset (Fin sieveModulus × Fin sieveModulus),
      R = Finset.univ.filter (admissible n) := ⟨_, rfl⟩
  let S := generatingPairs n
  have hR : R.card = 115579079884800 := by
    rw [hRdef]
    have hh := card_admissible n
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hh
    exact hh
  have hfiber (r : Fin sieveModulus × Fin sieveModulus) :
      4 * (sieveModulus : ℝ) ^ 2 * (S.filter (fun p => Prod.map (@Fin.ofNat sieveModulus ⟨by decide⟩) (@Fin.ofNat sieveModulus ⟨by decide⟩) p = r)).card ≤
        ((n : ℝ) + 2 * sieveModulus) ^ 2 := by
    apply lattice_bound _ n sieveModulus (by decide)
    · intro p hp
      exact (generatingPairs_properties hn hn4 (Finset.mem_filter.mp hp).1).1
    · intro p hp q hq
      have he := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
      exact congrArg (fun a => a.1.val) he
    · intro p hp q hq
      have he := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
      exact congrArg (fun a => a.2.val) he
  have hcount : S.card = ∑ r ∈ R, (S.filter (fun p => Prod.map (@Fin.ofNat sieveModulus ⟨by decide⟩) (@Fin.ofNat sieveModulus ⟨by decide⟩) p = r)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro p hp
    change p ∈ S at hp
    change Prod.map (@Fin.ofNat sieveModulus ⟨by decide⟩) (@Fin.ofNat sieveModulus ⟨by decide⟩) p ∈ R
    simp only [hRdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (generatingPairs_properties hn hn4 hp).2
  have hh := Finset.sum_le_sum (s := R) (fun r _ => hfiber r)
  simp only [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hh
  rw [← Nat.cast_sum, ← hcount, hR, generatingPairs_card] at hh
  exact hh

private lemma uniform_sieve_bound {n : ℕ} (hn : sieveModulus ≤ n) (hn4 : n % 4 = 0) :
    (f n : ℝ) ≤ (1146617856 / 14933966047 : ℝ) * (n : ℝ) ^ 2 +
      3 * sieveModulus * n := by
  have hh := sieve_count_bound hn hn4
  have hnR : (19399380 : ℝ) ≤ n := by exact Nat.ofNat_le_cast.mpr hn
  norm_num [sieveModulus] at hh ⊢
  nlinarith

set_option maxRecDepth 4000


theorem result : ¬ claim := by
  intro hclaim
  obtain ⟨C, hC, N, hestimate⟩ := hclaim (0 : Fin 4)
  let delta : ℝ := 2148763 / 14933966047
  let T : ℝ := max (N : ℝ) (max (sieveModulus : ℝ) (max 19 ((C + 3 * sieveModulus) / delta)))
  let n : ℕ := 4 * (Nat.floor (T / 4) + 1)
  have hnT : T < (n : ℝ) := by
    have hh := Nat.lt_floor_add_one (T / 4)
    dsimp [n]
    push_cast
    linarith
  have hnN : N ≤ n := by
    have hh : (N : ℝ) < n := (le_max_left _ _).trans_lt hnT
    exact_mod_cast hh.le
  have hnM : sieveModulus ≤ n := by
    have hh : (sieveModulus : ℝ) < n :=
      (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hnT
    exact_mod_cast hh.le
  have hn4 : n % 4 = 0 := by exact Nat.mul_mod_right 4 (⌊T / 4⌋₊ + 1)
  have hdelta : 0 < delta := by norm_num [delta]
  have hnpos : (0 : ℝ) < n := by exact Nat.ofNat_pos'
  have hratio : (C + 3 * sieveModulus) / delta < (n : ℝ) := by
    exact (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans_lt hnT
  have hlarge : C + 3 * sieveModulus < delta * (n : ℝ) := by
    have hh := (div_lt_iff₀ hdelta).mp hratio
    linarith
  have hlarge2 := mul_lt_mul_of_pos_right hlarge hnpos
  have hbound := uniform_sieve_bound hnM hn4
  have hdeficit : C * (n : ℝ) < (1 / 13 : ℝ) * (n : ℝ) ^ 2 - f n := by
    dsimp [delta] at hlarge2
    nlinarith only [hbound, hlarge2]
  have hest := hestimate n hnN hn4
  change |(f n : ℝ) - (1 / 13 : ℝ) * (n : ℝ) ^ 2| ≤ C * (n : ℝ) at hest
  have hnegative := neg_le_abs ((f n : ℝ) - (1 / 13 : ℝ) * (n : ℝ) ^ 2)
  linarith only [hdeficit, hest, hnegative]

end D5.S0.CayleyGrowth.PrefixReversalTripleCountRefutation
