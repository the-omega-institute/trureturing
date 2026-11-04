/- GID: D5/S3/Combinatorics/Circle/Orbit/ZeroIncidence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/Orbit/ZeroIncidence
   mirror-E: none(waiver:unregistered-new-circle-orbit)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate, mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: All cyclic physical translates of an actual centered source subset vanish exactly at balanced negative incidence, with an exact covering law and coprime obstruction. -/

module
public import D5.S3.Combinatorics.Circle.SourceWidth
public import D5.S3.Combinatorics.Circle.ZeroSumSubsets
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic

/-! # Orbitwise zero incidence for the labelled circle source

The phase variable acts on the physical labels.  Equal source values and
proper numerical periods therefore remain distinct occurrences throughout.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence

open scoped BigOperators
open D5.S3.Combinatorics.Circle.SourceWidth
open D5.S3.Combinatorics.Circle.ZeroSumSubsets

def orbitSum (k : ℕ) (hk : 0 < k) (S : Finset (Fin k))
    (f : Fin k → ℤ) (h : Fin k) : ℤ :=
  letI : NeZero k := ⟨ne_of_gt hk⟩
  (∑ i ∈ S, f (finCycle h i))

def orbitNegativeCount (k : ℕ) (hk : 0 < k) (S : Finset (Fin k))
    (b : Fin k → Bool) (h : Fin k) : ℕ :=
  letI : NeZero k := ⟨ne_of_gt hk⟩
  (S.filter (fun i => b (finCycle h i) = true)).card

def negativeBit (k t : ℕ) (i : Fin k) : Bool :=
  decide (actualSource k t i < 0)

def negativeSupport (k t : ℕ) (hk : 0 < k) : Finset (Fin k) :=
  Finset.univ.filter (fun i => actualSource k t i < 0)

private theorem bool_toNat_decide (p : Prop) [Decidable p] :
    Bool.toNat (decide p) = if p then 1 else 0 := by
  by_cases hp : p <;> simp [hp]

private theorem phase_step {k : ℕ} (hk : 0 < k) (N : ℤ) (f : Fin k → ℤ)
    (b : Fin k → Bool)
    (hrec : ∀ i, f (finRotate k i) =
      2 * f i + N * ((b i).toNat - (b (finRotate k i)).toNat))
    (S : Finset (Fin k)) (h : Fin k) :
    orbitSum k hk S f (finRotate k h) =
      2 * orbitSum k hk S f h + N *
        ((orbitNegativeCount k hk S b h : ℤ) -
          (orbitNegativeCount k hk S b (finRotate k h) : ℤ)) := by
  letI : NeZero k := ⟨ne_of_gt hk⟩
  have hcomm (i : Fin k) : finCycle (finRotate k h) i =
      finRotate k (finCycle h i) := by
    apply Fin.ext
    simp [finCycle_apply, finRotate_apply, Fin.val_add, Nat.add_assoc]
  simp only [orbitSum, orbitNegativeCount]
  simp_rw [hcomm]
  simp_rw [hrec]
  simp_rw [mul_sub]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hbits (j : Fin k) :
      ((b j).toNat : ℤ) = if b j = true then 1 else 0 := by
    cases hb : b j <;> simp [hb]
  simp only [Finset.card_filter]
  simp_rw [hbits]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp only [Finset.mul_sum]

private theorem adjacent_equal_of_zero {k : ℕ} (hk : 0 < k) {N : ℤ} (hN : 0 < N)
    {f : Fin k → ℤ} {b : Fin k → Bool} (S : Finset (Fin k))
    (hrec : ∀ i, f (finRotate k i) =
      2 * f i + N * ((b i).toNat - (b (finRotate k i)).toNat))
    (hzero : ∀ h, orbitSum k hk S f h = 0) :
    ∀ h, orbitNegativeCount k hk S b h =
      orbitNegativeCount k hk S b (finRotate k h) := by
  intro h
  have hs := phase_step hk N f b hrec S h
  rw [hzero h, hzero (finRotate k h)] at hs
  have hz : (N : ℤ) *
      ((orbitNegativeCount k hk S b h : ℤ) -
        (orbitNegativeCount k hk S b (finRotate k h) : ℤ)) = 0 := by
    simpa using hs
  have hd : (orbitNegativeCount k hk S b h : ℤ) -
      (orbitNegativeCount k hk S b (finRotate k h) : ℤ) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (ne_of_gt hN)
  exact_mod_cast (by omega : orbitNegativeCount k hk S b h =
    orbitNegativeCount k hk S b (finRotate k h))

theorem all_equal_of_adjacent {k : ℕ} (hk : 0 < k) (g : Fin k → ℕ)
    (hadj : ∀ h, g h = g (finRotate k h)) :
    ∀ h, g h = g ⟨0, by omega⟩ := by
  letI : NeZero k := ⟨ne_of_gt hk⟩
  have hnat : ∀ n : ℕ, ∀ hn : n < k,
      g ⟨n, hn⟩ = g 0 := by
    intro n
    induction n with
    | zero => intro; rfl
    | succ n ih =>
        intro hn
        have hi := ih (by omega)
        have ha := hadj (⟨n, by omega⟩ : Fin k)
        have hrot : finRotate k (⟨n, by omega⟩ : Fin k) =
            (⟨n + 1, hn⟩ : Fin k) := by
          apply Fin.ext
          simp [finRotate_apply, Fin.val_add,
            Nat.mod_eq_of_lt (show n + 1 < k by omega)]
        rw [hrot] at ha
        exact ha.symm.trans hi
  intro h
  exact hnat h.val h.isLt

private theorem zero_of_doubling_cycle {k : ℕ} (hk : 0 < k) (g : Fin k → ℤ)
    (hadj : ∀ h, g (finRotate k h) = 2 * g h) :
    ∀ h, g h = 0 := by
  letI : NeZero k := ⟨ne_of_gt hk⟩
  have hpow : ∀ n : ℕ, ∀ hn : n < k,
      g ⟨n, hn⟩ = (2 : ℤ) ^ n * g 0 := by
    intro n
    induction n with
    | zero => intro; simp
    | succ n ih =>
        intro hn
        have hi := ih (by omega)
        have ha := hadj (⟨n, by omega⟩ : Fin k)
        have hrot : finRotate k (⟨n, by omega⟩ : Fin k) =
            (⟨n + 1, hn⟩ : Fin k) := by
          apply Fin.ext
          simp [finRotate_apply, Fin.val_add,
            Nat.mod_eq_of_lt (show n + 1 < k by omega)]
        rw [hrot] at ha
        rw [ha, hi, pow_succ]
        ring
  let last : Fin k := ⟨k - 1, by omega⟩
  have hlast := hadj last
  have hlastrot : finRotate k last = (0 : Fin k) := by
    apply Fin.ext
    simp [last, finRotate_apply, Fin.val_add]
    rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
  rw [hlastrot, hpow (k - 1) (by omega)] at hlast
  have hpow_ne : (2 : ℤ) ^ k ≠ 1 := by
    have hpoweq : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
      have hk' : (k - 1) + 1 = k := Nat.sub_add_cancel (by omega)
      calc
        (2 : ℤ) ^ k = (2 : ℤ) ^ ((k - 1) + 1) := by rw [hk']
        _ = (2 : ℤ) ^ (k - 1) * 2 := by rw [pow_succ]
        _ = 2 * (2 : ℤ) ^ (k - 1) := by ring
    have hpos : 0 < (2 : ℤ) ^ (k - 1) := pow_pos (by norm_num) _
    rw [hpoweq]
    nlinarith
  have hz : g 0 = 0 := by
    have hpoweq : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
      have hk' : (k - 1) + 1 = k := Nat.sub_add_cancel (by omega)
      calc
        (2 : ℤ) ^ k = (2 : ℤ) ^ ((k - 1) + 1) := by rw [hk']
        _ = (2 : ℤ) ^ (k - 1) * 2 := by rw [pow_succ]
        _ = 2 * (2 : ℤ) ^ (k - 1) := by ring
    have hrel : g 0 = (2 : ℤ) ^ k * g 0 := by
      calc
        g 0 = 2 * ((2 : ℤ) ^ (k - 1) * g 0) := hlast
        _ = (2 * (2 : ℤ) ^ (k - 1)) * g 0 := by ring
        _ = (2 : ℤ) ^ k * g 0 := by rw [hpoweq]
    have : ((2 : ℤ) ^ k - 1) * g 0 = 0 := by
      nlinarith [hrel]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hpow_ne)
  intro h
  exact (hpow h.val h.isLt).trans (by simp [hz])

private theorem orbit_zero_iff_balanced {k : ℕ} (hk : 0 < k) {N : ℤ} (hN : 0 < N)
    (f : Fin k → ℤ) (b : Fin k → Bool)
    (hrec : ∀ i, f (finRotate k i) =
      2 * f i + N * ((b i).toNat - (b (finRotate k i)).toNat))
    (S : Finset (Fin k)) :
    (∀ h, orbitSum k hk S f h = 0) ↔
      (∀ h, orbitNegativeCount k hk S b h =
        orbitNegativeCount k hk S b ⟨0, by omega⟩) := by
  constructor
  · intro hzero
    have hadj := adjacent_equal_of_zero hk hN S hrec hzero
    exact all_equal_of_adjacent hk _ hadj
  · intro hbal
    have hstep (h : Fin k) :
        orbitSum k hk S f (finRotate k h) =
          2 * orbitSum k hk S f h := by
      have hs := phase_step hk N f b hrec S h
      rw [hbal h, hbal (finRotate k h)] at hs
      omega
    exact zero_of_doubling_cycle hk _ hstep

private theorem incidence_sum {k : ℕ} (hk : 0 < k) (S : Finset (Fin k))
    (b : Fin k → Bool) :
    ∑ h : Fin k, (orbitNegativeCount k hk S b h : ℤ) =
      (S.card : ℤ) * (Finset.univ.filter (fun i => b i = true)).card := by
  letI : NeZero k := ⟨ne_of_gt hk⟩
  classical
  simp only [orbitNegativeCount, Finset.card_filter]
  norm_cast
  rw [Finset.sum_comm]
  calc
    (∑ y ∈ S, ∑ x : Fin k, if b (finCycle x y) = true then (1 : ℕ) else 0) =
        ∑ y ∈ S, ∑ x : Fin k, if b x = true then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      have hrewrite : (fun x : Fin k =>
          if b (finCycle x y) = true then (1 : ℕ) else 0) =
          (fun x : Fin k => if b (finCycle y x) = true then (1 : ℕ) else 0) := by
        funext x
        have heq : finCycle x y = finCycle y x := by
          apply Fin.ext
          simp [finCycle_apply, Fin.val_add, Nat.add_comm]
        rw [heq]
      rw [hrewrite]
      exact Equiv.sum_comp (finCycle y) (fun x => if b x = true then (1 : ℕ) else 0)
    _ = S.card * ∑ i : Fin k, if b i = true then (1 : ℕ) else 0 := by
      simp

private theorem actual_recurrence {k : ℕ} (hk : 0 < k) (t : ℕ) :
    ∀ i : Fin k, actualSource k t (finRotate k i) =
      2 * actualSource k t i + modulus k *
        (((negativeBit k t i).toNat : ℤ) -
          ((negativeBit k t (finRotate k i)).toNat : ℤ)) := by
  letI : NeZero k := ⟨ne_of_gt hk⟩
  intro i
  have hN : 0 < modulus k := by
    have hp : 1 < (2 : ℕ) ^ k := Nat.one_lt_two_pow (ne_of_gt hk)
    have hpi : (1 : ℤ) < (2 : ℤ) ^ k := by exact_mod_cast hp
    dsimp [modulus]
    omega
  have hodd : modulus k % 2 = 1 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
    rw [modulus, pow_succ]
    omega
  have hnext : actualSource k t (finRotate k i) =
      doubleStep (modulus k) (actualSource k t i) := by
    have hnext : actualSource k t (finRotate k i) =
        centered (modulus k) ((2 : ℤ) ^ (i.val + 1) * t) := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
      by_cases hi : i = Fin.last r
      · subst i
        simp only [finRotate_last, actualSource, Fin.val_zero, pow_zero, one_mul,
          Fin.val_last, centered_full_period]
      · simp only [actualSource, coe_finRotate, ite_eq_right hi]
    rw [hnext]
    have he : (2 : ℤ) ^ (i.val + 1) * t = 2 * (2 ^ i.val * (t : ℤ)) := by
      rw [pow_succ]
      ring
    rw [he, centered_double hN hodd]
    rfl
  have hbound := centered_bounds hN hodd ((2 : ℤ) ^ i.val * (t : ℤ))
  have hbound' : -(modulus k / 2) ≤ actualSource k t i ∧
      actualSource k t i ≤ modulus k / 2 := by
    simpa [actualSource] using hbound
  have hu := unsigned_step hN hodd hbound'
  rw [← hnext] at hu
  have hbi : (negativeBit k t i).toNat =
      (if actualSource k t i < 0 then 1 else 0) := by
    simpa [negativeBit] using bool_toNat_decide (actualSource k t i < 0)
  have hbj : (negativeBit k t (finRotate k i)).toNat =
      (if actualSource k t (finRotate k i) < 0 then 1 else 0) := by
    simpa [negativeBit] using bool_toNat_decide
      (actualSource k t (finRotate k i) < 0)
  rw [hbi, hbj]
  by_cases hi : actualSource k t i < 0
  · by_cases hj : actualSource k t (finRotate k i) < 0
    · rw [if_pos hi, if_pos hj] at hu ⊢
      omega
    · rw [if_pos hi, if_neg hj] at hu ⊢
      omega
  · by_cases hj : actualSource k t (finRotate k i) < 0
    · rw [if_neg hi, if_pos hj] at hu ⊢
      omega
    · rw [if_neg hi, if_neg hj] at hu ⊢
      omega

/- The endpoint is the reusable actual-source theorem: the iff, its exact
covering multiplicity, and the coprime empty/full obstruction live together. -/
theorem actualSource_orbit_zero_balanced (k : ℕ) (hk : 0 < k) (t : ℕ)
    (S : Finset (Fin k)) :
    let b := negativeBit k t
    let n := (negativeSupport k t hk).card
    let E := orbitNegativeCount k hk S b ⟨0, by omega⟩
    ((∀ h, orbitSum k hk S (actualSource k t) h = 0) ↔
      (∀ h, orbitNegativeCount k hk S b h = E)) ∧
    ((∀ h, orbitSum k hk S (actualSource k t) h = 0) →
      k * E = S.card * n) ∧
    (Nat.Coprime k n →
      (∀ h, orbitSum k hk S (actualSource k t) h = 0) →
      (S = ∅ ∨ S = Finset.univ)) := by
  letI : NeZero k := ⟨ne_of_gt hk⟩
  dsimp
  let b := negativeBit k t
  let n := (negativeSupport k t hk).card
  let E := orbitNegativeCount k hk S b ⟨0, by omega⟩
  have hN : 0 < modulus k := by
    have hp : 1 < (2 : ℕ) ^ k := Nat.one_lt_two_pow (ne_of_gt hk)
    have hpi : (1 : ℤ) < (2 : ℤ) ^ k := by exact_mod_cast hp
    dsimp [modulus]
    omega
  have hrec := actual_recurrence hk t
  have hiff := orbit_zero_iff_balanced hk hN (actualSource k t) b hrec S
  have hcard : n = (Finset.univ.filter (fun i => b i = true)).card := by
    simp [n, negativeSupport, b, negativeBit]
  refine ⟨?_, ?_, ?_⟩
  · simpa [E] using hiff
  · intro hz
    have hbal := hiff.mp hz
    have hsum := incidence_sum hk S b
    have hconst : ∀ h, (orbitNegativeCount k hk S b h : ℤ) = E := by
      intro h
      exact_mod_cast hbal h
    have hsum' : ∑ h : Fin k, (orbitNegativeCount k hk S b h : ℤ) =
        (k : ℤ) * E := by
      simp_rw [hconst]
      simp
    rw [hsum, ← hcard] at hsum'
    exact_mod_cast hsum'.symm
  · intro hcop hz
    have hbal := hiff.mp hz
    have hsum := incidence_sum hk S b
    have hconst : ∀ h, (orbitNegativeCount k hk S b h : ℤ) = E := by
      intro h
      exact_mod_cast hbal h
    have hsum' : (k : ℤ) * E = (S.card : ℤ) * n := by
      have hs := hsum
      rw [show (∑ h : Fin k, (orbitNegativeCount k hk S b h : ℤ)) =
        (k : ℤ) * E by
          simp_rw [hconst]
          simp] at hs
      rw [← hcard] at hs
      exact hs
    have hdiv : k ∣ S.card * n := by
      exact_mod_cast (show (k : ℤ) ∣ (S.card : ℤ) * n by
        refine ⟨E, ?_⟩
        exact_mod_cast hsum'.symm)
    have hcardle : S.card ≤ k := by simpa using S.card_le_univ
    have hkd : k ∣ S.card := hcop.dvd_of_dvd_mul_right
      (by simpa [Nat.mul_comm] using hdiv)
    obtain ⟨q, hq⟩ := hkd
    have hqle : q ≤ 1 := by
      by_contra hqle
      have hq2 : 2 ≤ q := by omega
      have hk1 : 1 ≤ k := by omega
      nlinarith [hcardle]
    have hcases : q = 0 ∨ q = 1 := by omega
    have : S.card = 0 ∨ S.card = k := by
      rcases hcases with rfl | rfl
      · left; simp [hq]
      · right; simpa [hq, Nat.mul_comm]
    rcases this with hzero | hfull
    · left
      exact Finset.card_eq_zero.mp hzero
    · right
      apply Finset.eq_univ_of_card
      simpa using hfull

#print axioms actualSource_orbit_zero_balanced

end D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence
