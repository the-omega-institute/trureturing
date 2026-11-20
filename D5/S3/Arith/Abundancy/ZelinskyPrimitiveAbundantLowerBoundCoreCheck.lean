import D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
open Finset Real
open scoped BigOperators

namespace D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound

private def coreH (s : Finset ℕ) : ℝ := ∏ p ∈ s, (1 + 1 / (p : ℝ))

private def coreAlpha (s : Finset ℕ) : ℝ := coreH s / (2 - coreH s)

private lemma core_step_numeric {a p : ℝ} (ha : 2 ≤ a)
    (hp : 2 * a < p) (hp' : p ≤ 3 * a) :
    (3 / 2 : ℝ) * a ≤ a * (p + 1) / (p - a) ∧
      a * (p + 1) / (p - a) ≤ 3 * a ∧
      p < 2 * (a * (p + 1) / (p - a)) := by
  have ha0 : 0 < a := by linarith
  have hp0 : 0 < p := by linarith
  have hd : 0 < p - a := by linarith
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr hp')]
  constructor
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr hp.le)]
  · rw [← mul_div_assoc, lt_div_iff₀ hd]
    have hpp : p * p ≤ p * (3 * a) := mul_le_mul_of_nonneg_left hp' hp0.le
    nlinarith

private lemma core_step_prime : ∃ Y : ℝ, ∀ a : ℝ, Y ≤ a →
    ∃ p : ℕ, p.Prime ∧ 2 * a < (p : ℝ) ∧ (p : ℝ) ≤ 3 * a := by
  obtain ⟨Y, hY⟩ :=
    D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity.fixed_cardinality_prime_window
      (A := 2) (B := 3) (by norm_num) (by norm_num) 1
  refine ⟨Y, fun a ha => ?_⟩
  obtain ⟨s, hs, hsp⟩ := hY a ha
  have hne : s.Nonempty := card_pos.mp (by omega)
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, hsp p hp⟩

private lemma coreH_pos (s : Finset ℕ) : 0 < coreH s := by
  apply prod_pos
  intro p hp
  positivity

private lemma coreH_one_le (s : Finset ℕ) : 1 ≤ coreH s := by
  apply one_le_prod₀
  intro p hp
  have : 0 ≤ 1 / (p : ℝ) := by positivity
  linarith

private lemma coreH_insert (s : Finset ℕ) {p : ℕ} (hp : p ∉ s) :
    coreH (insert p s) = coreH s * (1 + 1 / (p : ℝ)) := by
  simp only [coreH, prod_insert hp]
  ring

private lemma core_step_ratio {h p : ℝ} (hh : 0 < h) (hh2 : h < 2)
    (hp : h / (2 - h) < p) :
    h * (1 + 1 / p) < 2 ∧
      h * (1 + 1 / p) / (2 - h * (1 + 1 / p)) =
        (h / (2 - h)) * (p + 1) / (p - h / (2 - h)) := by
  have hd : 0 < 2 - h := by linarith
  have ha : 0 < h / (2 - h) := div_pos hh hd
  have hp0 : 0 < p := ha.trans hp
  have hpa : 0 < p - h / (2 - h) := sub_pos.mpr hp
  have hcross : h < p * (2 - h) := (div_lt_iff₀ hd).mp hp
  have hhnew : h * (1 + 1 / p) < 2 := by
    rw [mul_add, mul_one]
    have hdiv : h / p < 2 - h := (div_lt_iff₀ hp0).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul] using (by linarith : h + h / p < 2)
  refine ⟨hhnew, ?_⟩
  have hbase : p * 2 - p * h - h ≠ 0 := by nlinarith [hcross]
  field_simp [hd.ne', hp0.ne', hpa.ne', (sub_pos.mpr hhnew).ne', hbase]
  <;> field_simp [hbase]
  <;> ring

private lemma core_reciprocal_tail (B : ℕ) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ B < p) ∧
      1 ≤ ∑ p ∈ s, 1 / (p : ℝ) := by
  classical
  let s := (4 ^ ((B + 1).primesBelow.card + 1)).succ.primesBelow \
    (B + 1).primesBelow
  let K := max (B + 1) (s.sup id + 1)
  let t := (4 ^ (K.primesBelow.card + 1)).succ.primesBelow \ K.primesBelow
  have block (A p : ℕ)
      (hp : p ∈ (4 ^ (A.primesBelow.card + 1)).succ.primesBelow \ A.primesBelow) :
      p.Prime ∧ A ≤ p := by
    obtain ⟨hp₁, hp₂⟩ := mem_sdiff.mp hp
    have hprime := Nat.prime_of_mem_primesBelow hp₁
    refine ⟨hprime, ?_⟩
    by_contra! hlt
    exact hp₂ (Nat.mem_primesBelow.mpr ⟨hlt, hprime⟩)
  have hdis : Disjoint s t := by
    apply disjoint_left.mpr
    intro p hps hpt
    have hpK := (block K p hpt).2
    have hsup : p ≤ s.sup id := Finset.le_sup (f := id) hps
    have hK : s.sup id + 1 ≤ K := le_max_right _ _
    omega
  refine ⟨s ∪ t, ?_, ?_⟩
  · intro p hp
    rcases mem_union.mp hp with hp | hp
    · have hd := block (B + 1) p hp
      exact ⟨hd.1, by omega⟩
    · have hd := block K p hp
      have hK : B + 1 ≤ K := le_max_left _ _
      exact ⟨hd.1, by omega⟩
  · rw [sum_union hdis]
    have hs := one_half_le_sum_primes_ge_one_div (B + 1)
    have ht := one_half_le_sum_primes_ge_one_div K
    change (1 / 2 : ℝ) ≤ ∑ p ∈ s, 1 / (p : ℝ) at hs
    change (1 / 2 : ℝ) ≤ ∑ p ∈ t, 1 / (p : ℝ) at ht
    linarith

private lemma core_sum_le (s : Finset ℕ) :
    1 + (∑ p ∈ s, 1 / (p : ℝ)) ≤ coreH s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coreH]
  | @insert p s hp ih =>
    rw [coreH_insert s hp, sum_insert hp]
    have hsum : 0 ≤ ∑ p ∈ s, 1 / (p : ℝ) := sum_nonneg (by intros; positivity)
    have hp0 : 0 ≤ 1 / (p : ℝ) := by positivity
    nlinarith

private lemma core_seed (B : ℕ) (hB : 2 ≤ B) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ B < p) ∧ coreH s < 2 ∧
      (B : ℝ) < coreAlpha s ∧
      (∀ p ∈ s, (p : ℝ) < 2 * coreAlpha s) := by
  classical
  obtain ⟨s, hs, hmass⟩ := core_reciprocal_tail B
  have hcross : ∃ k : ℕ, ∃ t : Finset ℕ,
      t ⊆ s ∧ t.card = k ∧ 2 ≤ coreH t :=
    ⟨s.card, s, Subset.rfl, rfl, by linarith [core_sum_le s]⟩
  obtain ⟨t, hts, htcard, htH⟩ := Nat.find_spec hcross
  have htne : t.Nonempty := by
    by_contra hn
    have ht0 := not_nonempty_iff_eq_empty.mp hn
    simp only [ht0, coreH, prod_empty] at htH
    norm_num at htH
  obtain ⟨r, hrt, hrmax⟩ := Finset.exists_mem_eq_sup t htne id
  change t.sup id = r at hrmax
  let u := t.erase r
  have huH : coreH u < 2 := by
    by_contra! hn
    have hcard : u.card < Nat.find hcross := by
      dsimp [u]
      rw [card_erase_of_mem hrt, htcard]
      have hpos := card_pos.mpr htne
      omega
    exact Nat.find_min hcross hcard
      ⟨u, (erase_subset _ _).trans hts, rfl, hn⟩
  have hrP := (hs r (hts hrt)).1
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hrP.pos
  have hde : 0 < 2 - coreH u := by linarith
  have huins : insert r u = t := insert_erase hrt
  have hrec : 2 ≤ coreH u * (1 + 1 / (r : ℝ)) := by
    rw [← coreH_insert u (by simp [u]), huins]
    exact htH
  have hralpha : (r : ℝ) ≤ coreAlpha u := by
    apply (le_div_iff₀ hde).mpr
    have hrec' : 2 - coreH u ≤ coreH u / r := by
      rw [mul_add, mul_one] at hrec
      rw [← div_eq_mul_one_div] at hrec
      linarith
    have hmul := (le_div_iff₀ hr0).mp hrec'
    nlinarith
  have hBr : (B : ℝ) < r := by exact_mod_cast (hs r (hts hrt)).2
  refine ⟨u, ?_, huH, hBr.trans_le hralpha, ?_⟩
  · intro p hp
    exact hs p (hts (mem_of_mem_erase hp))
  · intro p hp
    have hpt := mem_of_mem_erase hp
    have hpr : p ≤ r := by
      rw [← hrmax]
      exact Finset.le_sup (f := id) hpt
    have hprR : (p : ℝ) ≤ r := by exact_mod_cast hpr
    have halpha : 0 < coreAlpha u := hr0.trans_le hralpha
    linarith

private def coreLog (s : Finset ℕ) : ℝ := ∑ p ∈ s, log (p : ℝ)

private structure CoreState (B : ℕ) (Y : ℝ) where
  support : Finset ℕ
  prime_data : ∀ p ∈ support, p.Prime ∧ B < p
  deficient : coreH support < 2
  large : max (B : ℝ) (max 2 Y) ≤ coreAlpha support
  largest : ∀ p ∈ support, (p : ℝ) < 2 * coreAlpha support

private lemma core_extend {B : ℕ} {Y : ℝ}
    (hY : ∀ a : ℝ, Y ≤ a → ∃ p : ℕ,
      p.Prime ∧ 2 * a < (p : ℝ) ∧ (p : ℝ) ≤ 3 * a)
    (s : CoreState B Y) :
    ∃ u : CoreState B Y,
      (3 / 2 : ℝ) * coreAlpha s.support ≤ coreAlpha u.support ∧
      coreAlpha u.support ≤ 3 * coreAlpha s.support ∧
      coreLog u.support ≤ coreLog s.support + log (3 * coreAlpha s.support) := by
  have ha2 : 2 ≤ coreAlpha s.support :=
    (le_max_left 2 Y).trans ((le_max_right _ _).trans s.large)
  have ha0 : 0 < coreAlpha s.support := by linarith
  have haY : Y ≤ coreAlpha s.support :=
    (le_max_right 2 Y).trans ((le_max_right _ _).trans s.large)
  obtain ⟨p, hp, hplo, hphi⟩ := hY _ haY
  have hpn : p ∉ s.support := by
    intro hps
    exact (s.largest p hps).not_gt hplo
  have hratio := core_step_ratio (coreH_pos s.support) s.deficient
    (by linarith : coreAlpha s.support < (p : ℝ))
  have hnH : coreH (insert p s.support) < 2 := by
    rw [coreH_insert _ hpn]
    exact hratio.1
  have hnA : coreAlpha (insert p s.support) =
      coreAlpha s.support * (p + 1) / (p - coreAlpha s.support) := by
    unfold coreAlpha
    rw [coreH_insert _ hpn]
    exact hratio.2
  obtain ⟨hlo, hhi, hpbound⟩ := core_step_numeric ha2 hplo hphi
  rw [← hnA] at hlo hhi hpbound
  have hainc : coreAlpha s.support ≤ coreAlpha (insert p s.support) := by linarith
  let u : CoreState B Y :=
    { support := insert p s.support
      prime_data := by
        intro q hq
        rcases mem_insert.mp hq with rfl | hq
        · refine ⟨hp, ?_⟩
          have hBa : (B : ℝ) ≤ coreAlpha s.support :=
            (le_max_left _ _).trans s.large
          have : (B : ℝ) < p := by linarith
          exact_mod_cast this
        · exact s.prime_data q hq
      deficient := hnH
      large := s.large.trans hainc
      largest := by
        intro q hq
        rcases mem_insert.mp hq with rfl | hq
        · exact hpbound
        · exact (s.largest q hq).trans_le (by linarith) }
  refine ⟨u, hlo, hhi, ?_⟩
  change coreLog (insert p s.support) ≤ _
  simp only [coreLog, sum_insert hpn]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  linarith [log_le_log hp0 hphi]

private def coreNext {B : ℕ} {Y : ℝ}
    (hY : ∀ a : ℝ, Y ≤ a → ∃ p : ℕ,
      p.Prime ∧ 2 * a < (p : ℝ) ∧ (p : ℝ) ≤ 3 * a)
    (s : CoreState B Y) : CoreState B Y := (core_extend hY s).choose

private lemma coreNext_spec {B : ℕ} {Y : ℝ}
    (hY : ∀ a : ℝ, Y ≤ a → ∃ p : ℕ,
      p.Prime ∧ 2 * a < (p : ℝ) ∧ (p : ℝ) ≤ 3 * a)
    (s : CoreState B Y) :
    (3 / 2 : ℝ) * coreAlpha s.support ≤ coreAlpha (coreNext hY s).support ∧
      coreAlpha (coreNext hY s).support ≤ 3 * coreAlpha s.support ∧
      coreLog (coreNext hY s).support ≤
        coreLog s.support + log (3 * coreAlpha s.support) :=
  (core_extend hY s).choose_spec

private def coreIter {B : ℕ} {Y : ℝ}
    (hY : ∀ a : ℝ, Y ≤ a → ∃ p : ℕ,
      p.Prime ∧ 2 * a < (p : ℝ) ∧ (p : ℝ) ≤ 3 * a)
    (s : CoreState B Y) : ℕ → CoreState B Y
  | 0 => s
  | j + 1 => coreNext hY (coreIter hY s j)

private lemma coreIter_bounds {B : ℕ} {Y : ℝ}
    (hY : ∀ a : ℝ, Y ≤ a → ∃ p : ℕ,
      p.Prime ∧ 2 * a < (p : ℝ) ∧ (p : ℝ) ≤ 3 * a)
    (s : CoreState B Y) (j : ℕ) :
    coreAlpha s.support * (3 / 2 : ℝ) ^ j ≤
        coreAlpha (coreIter hY s j).support ∧
      coreAlpha (coreIter hY s j).support ≤ coreAlpha s.support * 3 ^ j ∧
      coreLog (coreIter hY s j).support ≤ coreLog s.support +
        (j : ℝ) * (log (3 * coreAlpha s.support) + j * log 3) := by
  induction j with
  | zero => simp [coreIter]
  | succ j ih =>
    obtain ⟨hlo, hhi, hlog⟩ := coreNext_spec hY (coreIter hY s j)
    have ha2 : 2 ≤ coreAlpha (coreIter hY s j).support :=
      (le_max_left 2 Y).trans ((le_max_right _ _).trans (coreIter hY s j).large)
    have ha0 : 0 < coreAlpha s.support :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
        ((le_max_left 2 Y).trans ((le_max_right _ _).trans s.large))
    have hlogbound : log (3 * coreAlpha (coreIter hY s j).support) ≤
        log (3 * coreAlpha s.support) + (j : ℝ) * log 3 := by
      have hmul : 3 * coreAlpha (coreIter hY s j).support ≤
          (3 * coreAlpha s.support) * 3 ^ j := by nlinarith [ih.2.1]
      have hmono := log_le_log (by linarith :
        0 < 3 * coreAlpha (coreIter hY s j).support) hmul
      rw [log_mul (by positivity) (by positivity), log_pow] at hmono
      exact hmono
    change coreAlpha s.support * (3 / 2 : ℝ) ^ (j + 1) ≤
        coreAlpha (coreNext hY (coreIter hY s j)).support ∧ _
    constructor
    · rw [pow_succ]
      nlinarith [ih.1]
    constructor
    · rw [pow_succ]
      nlinarith [ih.2.1]
    · push_cast
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have h3 : 0 < log (3 : ℝ) := log_pos (by norm_num)
      nlinarith [ih.2.2, mul_nonneg hj h3.le]

private lemma coreLog_nonneg {B : ℕ} {Y : ℝ} (s : CoreState B Y) :
    0 ≤ coreLog s.support := by
  apply sum_nonneg
  intro p hp
  exact log_natCast_nonneg p

private lemma coreIter_log_bound {B : ℕ} {Y : ℝ}
    (hY : ∀ a : ℝ, Y ≤ a → ∃ p : ℕ,
      p.Prime ∧ 2 * a < (p : ℝ) ∧ (p : ℝ) ≤ 3 * a)
    (s : CoreState B Y) :
    ∃ K : ℝ, 0 < K ∧ ∀ j : ℕ,
      coreLog (coreIter hY s j).support ≤ K * ((j : ℝ) + 1) ^ 2 := by
  let A := log (3 * coreAlpha s.support)
  let L := coreLog s.support
  have ha2 : 2 ≤ coreAlpha s.support :=
    (le_max_left 2 Y).trans ((le_max_right _ _).trans s.large)
  have hA : 0 ≤ A := log_nonneg (by dsimp; linarith)
  have hL : 0 ≤ L := coreLog_nonneg s
  have h3 : 0 ≤ log (3 : ℝ) := (log_pos (by norm_num)).le
  refine ⟨L + A + log 3 + 1, by positivity, fun j => ?_⟩
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj1 : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith
  have hj2 : (j : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith
  have hj3 : (j : ℝ) ^ 2 ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith
  have h := (coreIter_bounds hY s j).2.2
  change _ ≤ L + j * (A + j * log 3) at h
  nlinarith [mul_le_mul_of_nonneg_right hj1 hL,
    mul_le_mul_of_nonneg_right hj2 hA, mul_le_mul_of_nonneg_right hj3 h3,
    sq_nonneg ((j : ℝ) + 1)]

end D5.S3.Arith.Abundancy.ZelinskyPrimitiveAbundantLowerBound
