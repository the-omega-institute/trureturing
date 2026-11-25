/- GID: D5/S3/Arith/FactorialRatio/Compression/SharpLoss
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/Compression/SharpLoss
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Chebyshev]
   utility: none
   digest: Local residue counts and common-parameter transfer of compact factorial excess. -/


import D5.S3.Arith.FactorialRatio.CompactFactorialGcd
import OmegaMath.Arithmetic.CompactFloor
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
For the compact factorial family, the excess at a modulus is the paired
floor sum minus the corresponding tail count. A parameter close to `kp/r`
has at most `k` residue bands. Each band has a bounded number of marks.
Nonnegative bounded weights and complementary weights can use the same
parameter before taking their separate minima.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FactorialRatio.Compression.SharpLoss

open Finset
open scoped Nat
open D5.S3.Arith.FactorialRatio.RankOneLCMGcd (tailLCM)
open D5.S3.Arith.FactorialRatio.CompactFactorialGcd

/-- The nonnegative excess of the compact gcd over the tail product. -/
def compactExcess (r s : ℕ) : ℕ :=
  selbergGcd r s / tailLCM (r * s + r - 1) (r - 1)

/-- Excess at one modulus and one legal compact parameter. -/
def floorDefect (q r s b : ℕ) : ℕ :=
  floorSum q r s b - ((r * s + (r - 1)) / q - (r - 1))

private theorem residue_band_card {p b u : ℕ} (hb : 0 < b)
    (A : Finset ℕ) (j : ℕ)
    (hA : ∀ i ∈ A, i * b / p = j ∧ i * b % p ≤ u) :
    A.card ≤ u / b + 1 := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  let m := A.min' hne
  have hm : m ∈ A := A.min'_mem hne
  have hlow (i : ℕ) (hi : i ∈ A) : m ≤ i := A.min'_le i hi
  have hspan (i : ℕ) (hi : i ∈ A) : i - m < u / b + 1 := by
    obtain ⟨hij, hiv⟩ := hA i hi
    obtain ⟨hmj, _⟩ := hA m hm
    have hdi := Nat.div_add_mod (i * b) p
    have hdm := Nat.div_add_mod (m * b) p
    rw [hij] at hdi
    rw [hmj] at hdm
    have hsub : (i - m) * b + m * b = i * b := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (hlow i hi)]
    have hmul : (i - m) * b ≤ u :=
      Omega.Arithmetic.CompactFloor.band_span Nat.add Nat.le
        (gap := (i - m) * b) (lower := m * b) (base := p * j) (cap := u)
        (fun h h' => Nat.le_trans h h')
        (fun a _ _ h => Nat.add_le_add_left h a)
        (fun h => Nat.le_of_add_le_add_right h)
        (by
          change (i - m) * b + m * b ≤ u + p * j
          omega) (by
          change p * j ≤ m * b
          omega)
    have hdiv := (Nat.le_div_iff_mul_le hb).mpr hmul
    omega
  have hc := Finset.card_le_card_of_injOn (fun i => i - m)
    (s := A) (t := range (u / b + 1))
    (fun i hi => Finset.mem_range.mpr (hspan i hi))
    (fun i hi i' hi' heq => by
      have := hlow i hi
      have := hlow i' hi'
      dsimp only at heq
      omega)
  simpa using hc

private theorem residue_count_le {p r b u k : ℕ} (hp : 0 < p) (hb : 0 < b)
    (hspan : r * b < k * p) :
    ((Icc 1 r).filter (fun i => i * b % p ≤ u)).card ≤ k * (u / b + 1) := by
  classical
  let A := (Icc 1 r).filter (fun i => i * b % p ≤ u)
  have hmap : Set.MapsTo (fun i => i * b / p) A (range k) := by
    intro i hi
    have hir := (Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1).2
    exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hp).mpr
      ((Nat.mul_le_mul_right b hir).trans_lt hspan))
  calc
    A.card = ∑ j ∈ range k, (A.filter (fun i => i * b / p = j)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _j ∈ range k, (u / b + 1) := by
      apply Finset.sum_le_sum
      intro j _
      apply residue_band_card hb
      intro i hi
      obtain ⟨hiA, hij⟩ := Finset.mem_filter.mp hi
      exact ⟨hij, (Finset.mem_filter.mp hiA).2⟩
    _ = _ := by simp

private theorem floorSum_eq_mark_count {p r s b : ℕ} (hp : 0 < p) (hb : b < p)
    (hbs : r * b ≤ s) (hps : p ≤ s) :
    floorSum p r s b = r * ((s + b) / p - 1) +
      ((Icc 1 r).filter (fun i => i * b % p ≤ (s + b) % p)).card := by
  have hk : 1 ≤ (s + b) / p := Nat.div_pos (by omega) hp
  have hterm (i : ℕ) (hi : i ∈ range r) :
      pairedFloor p s b i = ((s + b) / p - 1) +
        (if ((i + 1) * b) % p ≤ (s + b) % p then 1 else 0) := by
    have hib : i * b ≤ s :=
      (Nat.mul_le_mul_right b (Nat.le_of_lt (Finset.mem_range.mp hi))).trans hbs
    have hc := pairedFloor_carry hp hib
    rw [Nat.mod_eq_of_lt hb] at hc
    unfold pairedFloor
    rw [Nat.div_eq_of_lt hb]
    split_ifs at hc ⊢ <;> omega
  unfold floorSum
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hcount : (∑ i ∈ range r, if ((i + 1) * b) % p ≤ (s + b) % p then 1 else 0) =
      ((Icc 1 r).filter (fun i => i * b % p ≤ (s + b) % p)).card := by
    calc
      _ = ∑ i ∈ Ico 1 (r + 1), if (i * b) % p ≤ (s + b) % p then 1 else 0 := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp [add_comm]
      _ = _ := by
        have hsets : Ico 1 (r + 1) = Icc 1 r := by
          ext i
          simp only [mem_Ico, mem_Icc]
          omega
        rw [hsets, ← Finset.sum_filter]
        simp
  rw [hcount]
  simp

set_option maxHeartbeats 800000 in
/-- A count using `k` residue bands. The conclusion has no primality
assumption; `r*b < k*p` is the strict endpoint condition. -/
private theorem local_floor_defect_bound {p r s b k : ℕ}
    (hp : 2 ≤ p) (hr : 1 ≤ r) (hb : 0 < b) (hbp : b < p)
    (hbs : r * b ≤ s) (hps : p ≤ s)
    (hspan : r * b < k * p) (hgap : k * p - r * b ≤ r) :
    (floorDefect p r s b : ℝ) ≤ 2 * (k : ℝ) + (r : ℝ) / b := by
  have hp0 : 0 < p := by omega
  let v := s % p
  let B := (r * v + (r - 1)) / p
  let Q := (r * s + (r - 1)) / p - (r - 1)
  have hvl : v < p := Nat.mod_lt s hp0
  have hk : 1 ≤ s / p := Nat.div_pos hps hp0
  have hmul : r * (s / p) = r * (s / p - 1) + r := by
    calc
      _ = r * ((s / p - 1) + 1) := by rw [Nat.sub_add_cancel hk]
      _ = _ := by ring
  have hQ : Q = r * (s / p - 1) + B + 1 := by
    have htail := compactTail_floor_add hp0 hps hr
    change Q + r = r * (s / p) + B + 1 at htail
    omega
  have hlower : Q ≤ floorSum p r s b := selberg_floor_lower hp hr hbs
  have hB := Nat.div_add_mod (r * v + (r - 1)) p
  have hBlt := Nat.mod_lt (r * v + (r - 1)) hp0
  have hbr : 0 < (b : ℝ) := by exact_mod_cast hb
  by_cases hnw : v + b < p
  · let g := ((Icc 1 r).filter (fun i => i * b % p ≤ v + b)).card
    have hg : g ≤ k * (v / b + 2) := by
      have h := residue_count_le (u := v + b) hp0 hb hspan
      simpa [g, Nat.add_div_right _ hb, add_assoc] using h
    have hgb : b * g ≤ k * v + 2 * k * b := by
      have hdiv := Nat.div_mul_le_self v b
      have h := Nat.mul_le_mul_left b hg
      nlinarith
    obtain ⟨hdiv, hmod⟩ := div_mod_add s b hp0
    rw [Nat.mod_eq_of_lt hbp, Nat.div_eq_of_lt hbp, Nat.div_eq_of_lt hnw] at hdiv
    rw [Nat.mod_eq_of_lt hbp, Nat.mod_eq_of_lt hnw] at hmod
    have hF : floorSum p r s b = r * (s / p - 1) + g := by
      simpa only [hdiv, hmod, add_zero, g] using floorSum_eq_mark_count hp0 hbp hbs hps
    have hD : floorDefect p r s b + B + 1 = g := by
      unfold floorDefect
      change floorSum p r s b - Q + B + 1 = g
      omega
    have hprod : p * b * floorDefect p r s b ≤ 2 * k * p * b + r * p := by
      have hB' : r * v < p * (B + 1) := by dsimp [B] at *; nlinarith
      have hgbp := Nat.mul_le_mul_left p hgb
      have hBmul := Nat.mul_le_mul_left b hB'.le
      have hDmul : p * b * g = p * b * floorDefect p r s b + p * b * (B + 1) := by
        rw [← hD]
        ring
      have hvb : (k * p - r * b) * v ≤ r * p :=
        (Nat.mul_le_mul hgap hvl.le)
      have hsplit : k * p = r * b + (k * p - r * b) := by omega
      nlinarith
    have hprodR : (p : ℝ) * b * floorDefect p r s b ≤
        2 * k * p * b + r * p := by exact_mod_cast hprod
    apply (mul_le_mul_iff_left₀ hbr).mp
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp0
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hbr)]
    nlinarith
  · have hvlower : p ≤ v + b := by omega
    have hw : v + b - p < b := by omega
    obtain ⟨hd, hm⟩ := div_mod_of_eq hp0
      (show v + b = p * 1 + (v + b - p) by omega) (by omega)
    obtain ⟨hdiv, hmod⟩ := div_mod_add s b hp0
    rw [Nat.mod_eq_of_lt hbp, Nat.div_eq_of_lt hbp, hd] at hdiv
    rw [Nat.mod_eq_of_lt hbp, hm] at hmod
    have hg : ((Icc 1 r).filter (fun i => i * b % p ≤ v + b - p)).card ≤ k := by
      have h := residue_count_le (u := v + b - p) hp0 hb hspan
      simpa only [Nat.div_eq_of_lt hw, zero_add, mul_one] using h
    have hF : floorSum p r s b ≤ r * (s / p) + k := by
      have hf := floorSum_eq_mark_count hp0 hbp hbs hps
      rw [hdiv, hmod] at hf
      simp only [add_zero, Nat.add_sub_cancel] at hf
      omega
    have hBge : r ≤ B + k := by
      have hfloor : r * v + (r - 1) < p * (B + 1) := by
        dsimp only [B]
        nlinarith only [hB, hBlt]
      by_contra h
      have hmul' := Nat.mul_le_mul_left p (show B + k + 1 ≤ r by omega)
      have hmulv := Nat.mul_le_mul_left r hvlower
      nlinarith only [hfloor, hmul', hmulv, hspan]
    have hDk : floorDefect p r s b ≤ 2 * k := by
      unfold floorDefect
      change floorSum p r s b - Q ≤ 2 * k
      omega
    have hcast : (floorDefect p r s b : ℝ) ≤ 2 * k := by exact_mod_cast hDk
    have hnon : 0 ≤ (r : ℝ) / b := by positivity
    exact hcast.trans (le_add_of_nonneg_right hnon)

theorem compactExcess_factorization {r s p : ℕ} (hr : 2 ≤ r) (hs : s < r ^ 2) :
    (compactExcess r s).factorization p = (selbergGcd r s).factorization p -
      (tailLCM (r * s + r - 1) (r - 1)).factorization p := by
  unfold compactExcess
  rw [Nat.factorization_div (compact_factorial_gcd r s hr hs).1, Finsupp.tsub_apply]

/-- The legal parameter `floor(kp/r)` gives the local large-prime estimate.
Only the first prime power contributes because `r < p` and `s < r^2`. -/
theorem local_prime_excess_bound {r s p k : ℕ} (hr : 2 ≤ r)
    (hs : s < r ^ 2) (hp : p.Prime) (hrp : r < p) (hkp : k * p ≤ s)
    (hk : 1 ≤ k) :
    ((compactExcess r s).factorization p : ℝ) ≤
      2 * (k : ℝ) + 2 * (r : ℝ) ^ 2 / ((k : ℝ) * p) := by
  let b := k * p / r
  have hr0 : 0 < r := by omega
  have hps : p ≤ s := (Nat.le_mul_of_pos_left p hk).trans hkp
  have hkr : k < r := by
    by_contra h
    have hmul' := Nat.mul_le_mul (show r ≤ k by omega) hrp.le
    nlinarith
  have hcop : Nat.Coprime r p := (hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hr0 hrp)).symm
  have hrem : 0 < k * p % r := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hd : r ∣ k := hcop.dvd_mul_right.mp (Nat.dvd_iff_mod_eq_zero.mpr hz)
    have := Nat.le_of_dvd (by omega : 0 < k) hd
    omega
  have hdecomp : r * b + k * p % r = k * p := Nat.div_add_mod _ _
  have hrem_lt : k * p % r < r := Nat.mod_lt _ hr0
  have hb0 : 0 < b := Nat.div_pos (by nlinarith) hr0
  have hbp : b < p := by
    by_contra h
    have hmul' := Nat.mul_le_mul_left r (show p ≤ b by omega)
    have hmul'' := Nat.mul_lt_mul_of_pos_right hkr hp.pos
    omega
  have hbs : r * b ≤ s := by omega
  have hlocal := local_floor_defect_bound hp.two_le (by omega : 1 ≤ r)
    hb0 hbp hbs hps (by omega : r * b < k * p) (by omega)
  have hspp : s < p ^ 2 := by nlinarith
  have hlog : Nat.log p s < 2 := (Nat.log_lt_iff_lt_pow hp.one_lt
    (by omega : s ≠ 0)).mpr hspp
  have hval := gcd_factorization_le hp hr0 hbs
  have htail := compact_tail_factorization hp (by omega : 1 ≤ r) hspp
  have hterm := selberg_factorization hp hbs hlog
  have hone : Ico (1 : ℕ) 2 = {1} := Nat.Ico_succ_singleton 1
  rw [hone, Finset.sum_singleton, pow_one] at htail hterm
  have hD : (compactExcess r s).factorization p ≤ floorDefect p r s b := by
    rw [compactExcess_factorization hr hs]
    rw [Nat.add_sub_assoc (by omega : 1 ≤ r), htail]
    unfold floorDefect
    omega
  have hbr : 0 < (b : ℝ) := by exact_mod_cast hb0
  have hkpR : 0 < (k : ℝ) * p :=
    mul_pos (by exact_mod_cast (show 0 < k by omega)) (by exact_mod_cast hp.pos)
  have hhalf : (k : ℝ) * p ≤ 2 * r * b := by
    have hnat : k * p ≤ 2 * r * b := by
      have hge : r ≤ r * b := Nat.le_mul_of_pos_right r hb0
      nlinarith
    exact_mod_cast hnat
  have hquot : (r : ℝ) / b ≤ 2 * (r : ℝ) ^ 2 / ((k : ℝ) * p) := by
    apply (div_le_div_iff₀ hbr hkpR).mpr
    have h := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ (r : ℝ) by positivity)
    nlinarith
  exact (show ((compactExcess r s).factorization p : ℝ) ≤ floorDefect p r s b
    by exact_mod_cast hD).trans (by linarith only [hlocal, hquot])

private def legalParameters (r s : ℕ) : Finset ℕ := range (s / r + 1)

private theorem legalParameters_nonempty (r s : ℕ) : (legalParameters r s).Nonempty :=
  ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩

private noncomputable def minimum (r s : ℕ) (f : ℕ → ℕ) : ℕ :=
  ((legalParameters r s).image f).min' ((legalParameters_nonempty r s).image f)

private theorem minimum_le {r s b : ℕ} (f : ℕ → ℕ)
    (hb : b ∈ legalParameters r s) : minimum r s f ≤ f b :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩)

private theorem minimum_attained (r s : ℕ) (f : ℕ → ℕ) :
    ∃ b ∈ legalParameters r s, f b = minimum r s f := by
  exact Finset.mem_image.mp (Finset.min'_mem _ _)

/-- The least weighted sum of the prime-power defects, with the same
compact parameter for every power of this rational prime. -/
noncomputable def weightedPrimeLoss
    (r s p K : ℕ) (c : ℕ → ℕ) : ℕ :=
  minimum r s (fun b => ∑ j ∈ Ico 1 K, c j * floorDefect (p ^ j) r s b)

private theorem ordinary_prime_loss {r s p : ℕ} (hr : 2 ≤ r) (hs : s < r ^ 2)
    (hp : p.Prime) :
    weightedPrimeLoss r s p (Nat.log p s + 1) (fun _ => 1) =
      (compactExcess r s).factorization p := by
  classical
  let T := tailLCM (r * s + r - 1) (r - 1)
  let G := selbergGcd r s
  let K := Nat.log p s + 1
  have hG0 : G ≠ 0 := selbergGcd_ne_zero _ _
  have hcost (b : ℕ) (hb : b ∈ legalParameters r s) :
      (∑ j ∈ Ico 1 K, floorDefect (p ^ j) r s b) =
        (selbergFactorial r s b).factorization p - T.factorization p := by
    have hbr : r * b ≤ s := by
      have h := Finset.mem_range.mp hb
      have := (Nat.le_div_iff_mul_le (by omega : 0 < r)).mp (show b ≤ s / r by omega)
      simpa [mul_comm] using this
    have hbound (j : ℕ) (hj : j ∈ Ico 1 K) :
        (r * s + (r - 1)) / p ^ j - (r - 1) ≤ floorSum (p ^ j) r s b := by
      apply selberg_floor_lower _ (by omega : 1 ≤ r) hbr
      calc
        2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ j := Nat.pow_le_pow_right hp.pos (Finset.mem_Ico.mp hj).1
    unfold floorDefect
    rw [Finset.sum_tsub_distrib _ hbound]
    rw [← selberg_factorization hp hbr (Nat.lt_succ_self _)]
    have ht := compact_tail_factorization hp (by omega : 1 ≤ r)
      (Nat.lt_pow_succ_log_self hp.one_lt s)
    simpa only [T, K, Nat.add_sub_assoc (by omega : 1 ≤ r)] using
      congrArg (fun n => (selbergFactorial r s b).factorization p - n) ht.symm
  let f := fun b => (selbergFactorial r s b).factorization p
  obtain ⟨b, hb, hmin⟩ := minimum_attained r s f
  have hminG : minimum r s f = G.factorization p := by
    apply Nat.le_antisymm
    · have hpow : p ^ minimum r s f ∣ G := by
        apply Finset.dvd_gcd
        intro a ha
        exact (hp.pow_dvd_iff_le_factorization (selbergFactorial_ne_zero _ _ _)).mpr
          (minimum_le f ha)
      exact (hp.pow_dvd_iff_le_factorization hG0).mp hpow
    · have hdvd : G ∣ selbergFactorial r s b := Finset.gcd_dvd hb
      have hv := (Nat.factorization_prime_le_iff_dvd hG0
        (selbergFactorial_ne_zero _ _ _)).mpr hdvd p hp
      change G.factorization p ≤ f b at hv
      rw [hmin] at hv
      exact hv
  have hEq : minimum r s (fun a => ∑ j ∈ Ico 1 K, floorDefect (p ^ j) r s a) =
      G.factorization p - T.factorization p := by
    apply Nat.le_antisymm
    · have := minimum_le (fun a => ∑ j ∈ Ico 1 K, floorDefect (p ^ j) r s a) hb
      rw [hcost b hb, show (selbergFactorial r s b).factorization p =
        G.factorization p from hmin.trans hminG] at this
      exact this
    · obtain ⟨a, ha, hamin⟩ := minimum_attained r s
        (fun a => ∑ j ∈ Ico 1 K, floorDefect (p ^ j) r s a)
      have h := minimum_le f ha
      rw [hminG] at h
      rw [← hamin, hcost a ha]
      exact Nat.sub_le_sub_right h _
  simpa only [weightedPrimeLoss, one_mul, K, compactExcess_factorization hr hs, T, G]
    using hEq

/-- A finite weighted compact excess. All weights are nonnegative natural
numbers, and each prime uses its own common parameter across its powers. -/
noncomputable def weightedExcess (r s : ℕ)
    (P : Finset ℕ) (c : ℕ → ℕ → ℕ) : ℕ :=
  ∏ p ∈ P, p ^ weightedPrimeLoss r s p (Nat.log p s + 1) (c p)

private theorem prime_loss_shared {r s p K C : ℕ} (c d : ℕ → ℕ)
    (hc : ∀ j ∈ Ico 1 K, c j + d j ≤ C) :
    weightedPrimeLoss r s p K c + weightedPrimeLoss r s p K d ≤
      C * weightedPrimeLoss r s p K (fun _ => 1) := by
  obtain ⟨b, hb, hmin⟩ := minimum_attained r s
    (fun b => ∑ j ∈ Ico 1 K, 1 * floorDefect (p ^ j) r s b)
  have hleft := minimum_le
    (fun b => ∑ j ∈ Ico 1 K, c j * floorDefect (p ^ j) r s b) hb
  have hright := minimum_le
    (fun b => ∑ j ∈ Ico 1 K, d j * floorDefect (p ^ j) r s b) hb
  unfold weightedPrimeLoss
  calc
    _ ≤ (∑ j ∈ Ico 1 K, c j * floorDefect (p ^ j) r s b) +
        ∑ j ∈ Ico 1 K, d j * floorDefect (p ^ j) r s b := Nat.add_le_add hleft hright
    _ = ∑ j ∈ Ico 1 K, (c j + d j) * floorDefect (p ^ j) r s b := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ j ∈ Ico 1 K, C * (1 * floorDefect (p ^ j) r s b) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [one_mul] using Nat.mul_le_mul_right (floorDefect (p ^ j) r s b) (hc j hj)
    _ = _ := by rw [← Finset.mul_sum, hmin]

private theorem prime_prod_factorization (P : Finset ℕ) (e : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) (p : ℕ) :
    (∏ q ∈ P, q ^ e q).factorization p = if p ∈ P then e p else 0 := by
  classical
  rw [Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (hP q hq).ne_zero)]
  calc
    _ = ∑ q ∈ P, if q = p then e q else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [(hP q hq).factorization_pow, Finsupp.single_apply, eq_comm]
    _ = _ := by simp

/-- Bounded weights and two complementary weight systems share the same
ordinary compact budget. The hypotheses concern the sum of the two weights
at each prime power, so independently selected minimizing parameters are
never identified with one another. -/
theorem weighted_shared_budget {r s C : ℕ} (hr : 2 ≤ r) (hs : s < r ^ 2)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (c d : ℕ → ℕ → ℕ)
    (hc : ∀ p ∈ P, ∀ j ∈ Ico 1 (Nat.log p s + 1), c p j + d p j ≤ C) :
    weightedExcess r s P c * weightedExcess r s P d ∣ compactExcess r s ^ C := by
  classical
  have hE : compactExcess r s ≠ 0 := by
    unfold compactExcess
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (selbergGcd_ne_zero r s))
      (compact_factorial_gcd r s hr hs).1) (Nat.pos_of_ne_zero (tail_nonzero _ _))).ne'
  have hW (w : ℕ → ℕ → ℕ) : weightedExcess r s P w ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hP p hp).ne_zero
  apply (Nat.factorization_prime_le_iff_dvd (mul_ne_zero (hW c) (hW d))
    (pow_ne_zero _ hE)).mp
  intro p hp
  rw [Nat.factorization_mul (hW c) (hW d), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  unfold weightedExcess
  rw [prime_prod_factorization P _ hP, prime_prod_factorization P _ hP]
  by_cases hpP : p ∈ P
  · rw [if_pos hpP, if_pos hpP]
    have h := prime_loss_shared (r := r) (s := s) (p := p) (c p) (d p) (hc p hpP)
    rw [ordinary_prime_loss hr hs hp] at h
    exact h
  · simp [hpP]

end D5.S3.Arith.FactorialRatio.Compression.SharpLoss
