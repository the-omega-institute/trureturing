/- GID: D5/S3/Arith/Congruence/ConditionalComparison/TerminalDonor
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/ConditionalComparison/TerminalDonor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Terminal donor descent preserves whole covers, oddness and distinctness. -/

import D5.S3.Arith.Congruence.ConditionalComparison.PrefixLiability
import D5.S3.Arith.Congruence.ConditionalComparison.ArithmeticCoordinates
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos7

set_option maxHeartbeats 1000000 in
-- The proof combines finite prefix allocation, CRT transport, and indexed cover reconstruction.
/-- A pure donor above a prime-power parent admits terminal prefix substitution
when its complete private ternary projection fits the continuing digit budget.
The resulting cover has no more classes and a strictly smaller modulus sum;
oddness and distinctness are preserved whenever the original cover has them. -/
theorem terminal_donor_descent {L q G W k : ℕ}
    (modulus residue : Fin L → ℕ)
    (hcover : ∀ z : ℕ, ∃ i, z ≡ residue i [MOD modulus i])
    (hnonunit : ∀ i, 1 < modulus i)
    (hq : Nat.Prime q) (hW : Nat.Coprime W (3 * q))
    (hperiod : ∀ i, modulus i ∣ 9 * q ^ G * W)
    (donor : Fin L) (hpure : modulus donor = q ^ (k + 1))
    (hcontract : 27 < q)
    (hcapacity :
      27 * Nat.card {v : Fin 9 // ∃ y : ℕ,
        y ≡ residue donor [MOD modulus donor] ∧
        (∀ i : Fin L, i ≠ donor → ¬ y ≡ residue i [MOD modulus i]) ∧
        y % 9 = v.val} + 1 ≤ q + 9) :
    ∃ L' : ℕ, ∃ modulus' residue' : Fin L' → ℕ,
      (∀ z : ℕ, ∃ i, z ≡ residue' i [MOD modulus' i]) ∧
      (∀ i, 1 < modulus' i) ∧ L' ≤ L ∧
      (∑ i : Fin L', modulus' i) < ∑ i : Fin L, modulus i ∧
      (Function.Injective modulus → Function.Injective modulus') ∧
      ((∀ i, Odd (modulus i)) → ∀ i, Odd (modulus' i)) := by
  classical
  let Outcome : {L : ℕ} → (Fin L → ℕ) → Prop := fun {L} old =>
    ∃ L' : ℕ, ∃ modulus' residue' : Fin L' → ℕ,
      (∀ z : ℕ, ∃ i, z ≡ residue' i [MOD modulus' i]) ∧
      (∀ i, 1 < modulus' i) ∧ L' ≤ L ∧
      (∑ i : Fin L', modulus' i) < ∑ i : Fin L, old i ∧
      (Function.Injective old → Function.Injective modulus') ∧
      ((∀ i, Odd (old i)) → ∀ i, Odd (modulus' i))
  -- Enumerate a subset of the original indices, preserving its total weight.
  have assemble {L : ℕ} (old : Fin L → ℕ)
      (P : Fin L → Prop) [DecidablePred P] (m r : Fin L → ℕ)
      (hcover : ∀ z, ∃ i, P i ∧ z ≡ r i [MOD m i])
      (hgt : ∀ i, P i → 1 < m i)
      (hweight : ∀ i, (if P i then m i else 0) ≤ old i)
      (hstrict : ∃ i, (if P i then m i else 0) < old i)
      (hinj : Function.Injective old → ∀ i j, P i → P j → m i = m j → i = j)
      (hodd : (∀ i, Odd (old i)) → ∀ i, P i → Odd (m i)) : Outcome old := by
    classical
    let A := {i : Fin L // P i}
    let n := Fintype.card A
    let enum : Fin n ≃ A := (Fintype.equivFin A).symm
    have hsum : (∑ i : Fin n, m (enum i).val) = ∑ i : Fin L, if P i then m i else 0 := by
      rw [enum.sum_comp (fun i : A => m i.val)]
      calc
        (∑ i : A, m i.val) = ∑ i ∈ Finset.univ.filter P, m i :=
          (Finset.sum_subtype _ (by simp) m).symm
        _ = ∑ i : Fin L, if P i then m i else 0 := Finset.sum_filter _ _
    refine ⟨n, (fun i => m (enum i).val), (fun i => r (enum i).val), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z
      obtain ⟨i, hi, hz⟩ := hcover z
      refine ⟨enum.symm ⟨i, hi⟩, ?_⟩
      simpa only [Equiv.apply_symm_apply] using hz
    · intro i
      exact hgt _ (enum i).property
    · simpa only [Fintype.card_fin] using Fintype.card_subtype_le P
    · rw [hsum]
      exact Finset.sum_lt_sum (fun i _ => hweight i)
        (by obtain ⟨i, hi⟩ := hstrict; exact ⟨i, Finset.mem_univ _, hi⟩)
    · intro ho i j hij
      apply enum.injective
      apply Subtype.ext
      exact hinj ho _ _ (enum i).property (enum j).property hij
    · intro ho i
      exact hodd ho _ (enum i).property
  -- An original class without a private point can be deleted.
  have delete_redundant {L : ℕ} (old res : Fin L → ℕ)
      (hgt : ∀ i, 1 < old i) (bad : Fin L)
      (hcover : ∀ z, ∃ i, i ≠ bad ∧ z ≡ res i [MOD old i]) : Outcome old := by
    classical
    apply assemble old (fun i => i ≠ bad) old res hcover
    · intro i _; exact hgt i
    · intro i; split_ifs <;> omega
    · refine ⟨bad, ?_⟩
      simp only [ne_eq, not_true_eq_false, ↓reduceIte]
      exact lt_trans Nat.zero_lt_one (hgt bad)
    · intro hi i j _ _ hij; exact hi hij
    · intro ho i _; exact ho i
  -- Separate the two prime powers from the common cofactor.
  have decompose {q G W d : ℕ} (hq : Nat.Prime q) (hsize : 27 < q)
      (hW : Nat.Coprime W (3 * q)) (hd : d ∣ 9 * q ^ G * W) :
      ∃ a e m, a ≤ 2 ∧ e ≤ G ∧ m ∣ W ∧ 0 < m ∧
        Nat.Coprime m (3 * q) ∧ d = 3 ^ a * q ^ e * m := by
    have hW0 : W ≠ 0 := by
      intro h
      subst W
      simp only [Nat.coprime_zero_left] at hW
      omega
    have hd' : d ∣ 3 ^ 2 * (q ^ G * W) := by convert hd using 1; ring
    obtain ⟨u, v, hu, hv, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd'
    obtain ⟨a, ha, rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hu
    obtain ⟨w, m, hw, hm, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hv
    obtain ⟨e, he, rfl⟩ := (Nat.dvd_prime_pow hq).mp hw
    refine ⟨a, e, m, ha, he, hm, ?_, hW.coprime_dvd_left hm, by ring⟩
    exact Nat.pos_of_ne_zero (by intro h; subst m; simp only [zero_dvd_iff] at hm; exact hW0 hm)
  -- The cofactor has zero valuation at both distinguished primes.
  have factorization_values {q a e m : ℕ} (hq : Nat.Prime q) (hsize : 27 < q)
      (hm : Nat.Coprime m (3 * q)) (hmpos : 0 < m) :
      (3 ^ a * q ^ e * m).factorization 3 = a ∧
        (3 ^ a * q ^ e * m).factorization q = e := by
    have h3 : Nat.Prime 3 := by decide
    have hneq : q ≠ 3 := by omega
    have h3m : ¬ 3 ∣ m := h3.coprime_iff_not_dvd.mp
      (Nat.coprime_mul_iff_right.mp hm).1.symm
    have hqm : ¬ q ∣ m := hq.coprime_iff_not_dvd.mp
      (Nat.coprime_mul_iff_right.mp hm).2.symm
    constructor <;>
      simp [Nat.factorization_mul, hq.ne_zero, Nat.ne_of_gt hmpos,
        Nat.factorization_pow, h3.factorization, hq.factorization,
        hneq, Ne.symm hneq,
        Nat.factorization_eq_zero_of_not_dvd h3m,
        Nat.factorization_eq_zero_of_not_dvd hqm]
  -- Each removed label contracts because every ternary block costs 27 < q.
  have label_bounds {q a e k m : ℕ} (hsize : 27 < q)
      (hek : k < e) (hmpos : 0 < m) :
      1 < 3 ^ (3 * (e - k) + a) * q ^ k * m ∧
      3 ^ (3 * (e - k) + a) * q ^ k * m < 3 ^ a * q ^ e * m := by
    have hqpos : 0 < q := by omega
    have hpow : 1 < 3 ^ (3 * (e - k) + a) :=
      one_lt_pow₀ (by decide) (by omega)
    constructor
    · calc
        1 < 3 ^ (3 * (e - k) + a) := hpow
        _ ≤ 3 ^ (3 * (e - k) + a) * (q ^ k * m) :=
          Nat.le_mul_of_pos_right _ (mul_pos (pow_pos hqpos _) hmpos)
        _ = 3 ^ (3 * (e - k) + a) * q ^ k * m := by ring
    · have hpowlt : 27 ^ (e - k) < q ^ (e - k) :=
        Nat.pow_lt_pow_left hsize (by omega)
      have hfactor : 0 < 3 ^ a * q ^ k * m := by positivity
      calc
        3 ^ (3 * (e - k) + a) * q ^ k * m =
            27 ^ (e - k) * (3 ^ a * q ^ k * m) := by
          rw [pow_add, pow_mul]
          norm_num
          ring
        _ < q ^ (e - k) * (3 ^ a * q ^ k * m) :=
          (Nat.mul_lt_mul_right hfactor).2 hpowlt
        _ = 3 ^ a * q ^ e * m := by
          have he : e = (e - k) + k := by omega
          nth_rw 2 [he]
          rw [pow_add]
          ring
  -- The remainder modulo three of the new valuation recovers the old height.
  have label_parameters {q a b e f k m n : ℕ}
      (hq : Nat.Prime q) (hsize : 27 < q)
      (ha : a ≤ 2) (hb : b ≤ 2) (hek : k < e) (hfk : k < f)
      (hm : Nat.Coprime m (3 * q)) (hn : Nat.Coprime n (3 * q))
      (hmpos : 0 < m) (hnpos : 0 < n)
      (heq : 3 ^ (3 * (e - k) + a) * q ^ k * m =
        3 ^ (3 * (f - k) + b) * q ^ k * n) :
      a = b ∧ e = f ∧ m = n := by
    have h3eq := congrArg (fun z : ℕ ↦ z.factorization 3) heq
    rw [(factorization_values hq hsize hm hmpos).1,
      (factorization_values hq hsize hn hnpos).1] at h3eq
    have hab : a = b := by omega
    have hef : e = f := by omega
    subst b
    subst f
    have hmn : m = n := Nat.eq_of_mul_eq_mul_left
      (mul_pos (pow_pos (by decide : 0 < 3) _) (pow_pos hq.pos _)) heq
    exact ⟨rfl, rfl, hmn⟩
  have label_injective {q a b e f k m n : ℕ}
      (hq : Nat.Prime q) (hsize : 27 < q)
      (ha : a ≤ 2) (hb : b ≤ 2) (hek : k < e) (hfk : k < f)
      (hm : Nat.Coprime m (3 * q)) (hn : Nat.Coprime n (3 * q))
      (hmpos : 0 < m) (hnpos : 0 < n)
      (heq : 3 ^ (3 * (e - k) + a) * q ^ k * m =
        3 ^ (3 * (f - k) + b) * q ^ k * n) :
      3 ^ a * q ^ e * m = 3 ^ b * q ^ f * n := by
    obtain ⟨rfl, rfl, rfl⟩ := label_parameters hq hsize ha hb hek hfk hm hn hmpos hnpos heq
    rfl
  -- Every new label has ternary valuation at least three.
  have label_ne_retained {q a b e f k m n : ℕ}
      (hq : Nat.Prime q) (hsize : 27 < q) (hb : b ≤ 2) (hek : k < e)
      (hm : Nat.Coprime m (3 * q)) (hn : Nat.Coprime n (3 * q))
      (hmpos : 0 < m) (hnpos : 0 < n) :
      3 ^ (3 * (e - k) + a) * q ^ k * m ≠ 3 ^ b * q ^ f * n := by
    intro heq
    have h3eq := congrArg (fun z : ℕ ↦ z.factorization 3) heq
    rw [(factorization_values hq hsize hm hmpos).1,
      (factorization_values hq hsize hn hnpos).1] at h3eq
    omega
  -- Reserve one terminal child and inject the remaining fine prefixes.
  have terminal_initial_fragment {q : ℕ} (hq : 27 < q)
      (Lambda : Finset (Fin 9)) (c0 : Fin 9) (hc0 : c0 ∈ Lambda) (delta : Fin q)
      (hcapacity : 27 * Lambda.card + 1 ≤ q + 9) :
      ∃ first : ℕ → ℕ,
        (∀ x, first x < q) ∧
        (∀ x, ((⟨x % 9, Nat.mod_lt _ (by decide)⟩ : Fin 9) ∈ Lambda ∧
          x % 27 ≠ c0.val) → first x ≠ delta.val) ∧
        (∀ x y,
          ((⟨x % 9, Nat.mod_lt _ (by decide)⟩ : Fin 9) ∈ Lambda ∧
            x % 27 ≠ c0.val) →
          ((⟨y % 9, Nat.mod_lt _ (by decide)⟩ : Fin 9) ∈ Lambda ∧
            y % 27 ≠ c0.val) → first x = first y → x % 243 = y % 243) := by
    classical
    let Forest := {a : Fin 9 // a ∈ Lambda} × Fin 27
    let terminal : Forest → Prop := fun z ↦ z.1.val = c0 ∧ z.2.val % 3 = 0
    let te : {z : Forest // terminal z} ≃ Fin 9 := {
      toFun := fun z ↦ ⟨z.val.2.val / 3, by have := z.val.2.isLt; omega⟩
      invFun := fun i ↦ ⟨(⟨c0, hc0⟩, ⟨3 * i.val, by have := i.isLt; omega⟩),
        by simp [terminal]⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          exact z.property.1.symm
        · apply Fin.ext
          change 3 * (z.val.2.val / 3) = z.val.2.val
          have hmod := z.property.2
          dsimp [terminal] at hmod
          omega
      right_inv := by intro i; apply Fin.ext; simp }
    have hterminal : Fintype.card {z : Forest // terminal z} = 9 := by
      simpa using Fintype.card_congr te
    have hforest : Fintype.card Forest = 27 * Lambda.card := by
      simp [Forest, Nat.mul_comm]
    have hcontinue : Fintype.card {z : Forest // ¬terminal z} =
        27 * Lambda.card - 9 := by
      rw [Fintype.card_subtype_compl, hforest, hterminal]
    have hlabels : Fintype.card {d : Fin q // d ≠ delta} = q - 1 := by
      simp [Fintype.card_subtype_compl]
    obtain ⟨embed⟩ : Nonempty ({z : Forest // ¬terminal z} ↪ {d : Fin q // d ≠ delta}) := by
      apply Function.Embedding.nonempty_of_card_le
      rw [hcontinue, hlabels]
      omega
    let allowed : ℕ → Prop := fun x ↦
      (⟨x % 9, Nat.mod_lt _ (by decide)⟩ : Fin 9) ∈ Lambda ∧ x % 27 ≠ c0.val
    let point : (x : ℕ) → allowed x → {z : Forest // ¬terminal z} := fun x hx ↦
      ⟨(⟨⟨x % 9, Nat.mod_lt _ (by decide)⟩, hx.1⟩,
        ⟨x / 9 % 27, Nat.mod_lt _ (by decide)⟩), by
        intro hp
        have hroot : x % 9 = c0.val := congrArg Fin.val hp.1
        have hhigh : x / 9 % 3 = 0 := by
          have hmod := Nat.mod_mod_of_dvd (x / 9) (by decide : 3 ∣ 27)
          exact hmod.symm.trans hp.2
        have hmod : x % 27 = x % 9 + 9 * (x / 9 % 3) :=
          Nat.mod_mul (a := 9) (b := 3)
        exact hx.2 (by simpa [hroot, hhigh] using hmod)⟩
    let first : ℕ → ℕ := fun x ↦ if hx : allowed x then (embed (point x hx)).val.val
      else delta.val
    refine ⟨first, ?_, ?_, ?_⟩
    · intro x
      by_cases hx : allowed x
      · simp [first, hx]
      · simp [first, hx]
    · intro x hx
      change allowed x at hx
      have hne := (embed (point x hx)).property
      intro heq
      apply hne
      apply Fin.ext
      simpa [first, hx] using heq
    · intro x y hx hy hxy
      change allowed x at hx
      change allowed y at hy
      have hpoint : point x hx = point y hy := by
        apply embed.injective
        apply Subtype.ext
        apply Fin.ext
        simpa [first, hx, hy] using hxy
      have hroot : x % 9 = y % 9 := congrArg (fun z ↦ z.val.1.val.val) hpoint
      have hhigh : x / 9 % 27 = y / 9 % 27 := congrArg (fun z ↦ z.val.2.val) hpoint
      have hxmod : x % 243 = x % 9 + 9 * (x / 9 % 27) :=
        Nat.mod_mul (a := 9) (b := 27)
      have hymod : y % 243 = y % 9 + 9 * (y / 9 % 27) :=
        Nat.mod_mul (a := 9) (b := 27)
      rw [hxmod, hymod, hroot, hhigh]
  -- Later ternary blocks provide distinct prime-adic continuation digits.
  have terminal_radix_fragment {q N : ℕ} (hq : 27 < q) (hN : 1 ≤ N)
      (allowed : ℕ → Prop) (first : ℕ → ℕ)
      (hfirst : ∀ x, first x < q)
      (hinitial : ∀ x y, allowed x → allowed y →
        first x = first y → x % 243 = y % 243) :
      ∃ f : ℕ → ℕ,
        (∀ x, f x % q = first x) ∧
        ∀ t, 1 ≤ t → t ≤ N → ∀ x y, allowed x → allowed y →
          f x ≡ f y [MOD q ^ t] → x ≡ y [MOD 3 ^ (2 + 3 * t)] := by
    let word : ℕ → Word q N := fun x i ↦
      if hi : i.val = 0 then ⟨first x, hfirst x⟩
      else ⟨x / 243 / 27 ^ (i.val - 1) % 27,
        (Nat.mod_lt _ (by decide : 0 < 27)).trans hq⟩
    let f : ℕ → ℕ := fun x ↦ embeddedWordValue q (word x)
    have hfzero : ∀ x, f x % q = first x := by
      intro x
      have hdigits : ∀ z ∈ List.ofFn (fun i ↦ (word x i : ℕ)), z < q := by
        intro z hz
        simp only [List.mem_ofFn] at hz
        obtain ⟨i, rfl⟩ := hz
        exact (word x i).isLt
      have htake := Nat.ofDigits_mod_pow_eq_ofDigits_take 1 (by omega : 0 < q)
        (List.ofFn fun i ↦ (word x i : ℕ)) hdigits
      change Nat.ofDigits q (List.ofFn fun i ↦ (word x i : ℕ)) % q = first x
      rw [pow_one] at htake
      rw [htake, ← Fin.ofFn_take_eq_take_ofFn hN]
      simp [Fin.take, word, List.ofFn_succ, Nat.ofDigits_cons]
    have hdigits : ∀ (m a b : ℕ),
        (∀ i, i < m → a / 27 ^ i % 27 = b / 27 ^ i % 27) →
        a % 27 ^ m = b % 27 ^ m := by
      intro m
      induction m with
      | zero => intro a b hab; simp only [pow_zero, Nat.mod_one]
      | succ m ih =>
        intro a b hab
        rw [Nat.mod_pow_succ, Nat.mod_pow_succ,
          ih a b (fun i hi ↦ hab i (by omega)), hab m (by omega)]
    refine ⟨f, hfzero, ?_⟩
    intro t ht htN x y hx hy hxy
    have hpre := embeddedWordValue_prefix_eq (by omega : 1 < q) le_rfl htN
      (word x) (word y) hxy
    have hfirstxy : first x = first y := by
      have h := congrArg Fin.val (hpre ⟨0, by omega⟩)
      simpa [word, Fin.take] using h
    have hinitialxy := hinitial x y hx hy hfirstxy
    have htail : x / 243 % 27 ^ (t - 1) = y / 243 % 27 ^ (t - 1) := by
      apply hdigits
      intro i hi
      have h := congrArg Fin.val (hpre ⟨i + 1, by omega⟩)
      simpa [word, Fin.take] using h
    have hmod : x % (243 * 27 ^ (t - 1)) = y % (243 * 27 ^ (t - 1)) := by
      rw [Nat.mod_mul, Nat.mod_mul, hinitialxy, htail]
    have hpow : 243 * 27 ^ (t - 1) = 3 ^ (2 + 3 * t) := by
      calc
        243 * 27 ^ (t - 1) = 3 ^ 5 * (3 ^ 3) ^ (t - 1) := by norm_num
        _ = 3 ^ (5 + 3 * (t - 1)) := by rw [← pow_mul, ← pow_add]
        _ = 3 ^ (2 + 3 * t) := by congr 1; omega
    simpa only [Nat.ModEq, hpow] using hmod
  -- A whole inverse fibre lies in one target arithmetic progression.
  have donor_enclosure_fragment {q k G a e m W : ℕ}
      (hq : Nat.Prime q) (hsize : 27 < q) (ha : a ≤ 2)
      (hek : k < e) (heG : e ≤ G) (hmW : m ∣ W)
      (hm : Nat.Coprime m (3 * q))
      (allowed : ℕ → Prop) (f source : ℕ → ℕ) (u : ℕ)
      (hsourceq : ∀ x, source x ≡ u + q ^ k * f x [MOD q ^ G])
      (hsourceR : ∀ x, source x ≡ x [MOD 9 * W])
      (hfsep : ∀ t, 1 ≤ t → t ≤ G - k → ∀ x y, allowed x → allowed y →
        f x ≡ f y [MOD q ^ t] → x ≡ y [MOD 3 ^ (2 + 3 * t)])
      {x y : ℕ} (hx : allowed x) (hy : allowed y)
      (hparent : x ≡ y [MOD q ^ k])
      (hsource : source x ≡ source y [MOD 3 ^ a * q ^ e * m]) :
      x ≡ y [MOD 3 ^ (3 * (e - k) + a) * q ^ k * m] := by
    have hqdvd : q ^ e ∣ 3 ^ a * q ^ e * m :=
      dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    have hsourcee := hsource.of_dvd hqdvd
    have hxe := (hsourceq x).of_dvd (pow_dvd_pow q heG)
    have hye := (hsourceq y).of_dvd (pow_dvd_pow q heG)
    have hcoords : u + q ^ k * f x ≡ u + q ^ k * f y [MOD q ^ e] :=
      hxe.symm.trans (hsourcee.trans hye)
    have hmul : q ^ k * f x ≡ q ^ k * f y [MOD q ^ e] :=
      Nat.ModEq.add_left_cancel (Nat.ModEq.refl u) hcoords
    have hf : f x ≡ f y [MOD q ^ (e - k)] := by
      apply Nat.ModEq.mul_left_cancel' (pow_ne_zero _ hq.ne_zero)
      convert hmul using 1
      rw [← pow_add]
      congr 1
      omega
    have hternary := hfsep (e - k) (by omega) (by omega) x y hx hy hf
    have hternary' : x ≡ y [MOD 3 ^ (3 * (e - k) + a)] :=
      hternary.of_dvd (pow_dvd_pow 3 (by omega))
    have hcoprime3q : Nat.Coprime (3 ^ (3 * (e - k) + a)) (q ^ k) :=
      Nat.coprime_pow_primes _ _ (by decide) hq (by omega)
    have hprefix : x ≡ y [MOD 3 ^ (3 * (e - k) + a) * q ^ k] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcoprime3q).mp ⟨hternary', hparent⟩
    have hmR : m ∣ 9 * W := dvd_mul_of_dvd_right hmW _
    have hmsource : source x ≡ source y [MOD m] :=
      hsource.of_dvd (dvd_mul_left _ _)
    have hmxy : x ≡ y [MOD m] :=
      ((hsourceR x).of_dvd hmR).symm.trans
        (hmsource.trans ((hsourceR y).of_dvd hmR))
    have h3m : Nat.Coprime 3 m := (Nat.coprime_mul_iff_right.mp hm).1.symm
    have hqm : Nat.Coprime q m := (Nat.coprime_mul_iff_right.mp hm).2.symm
    have hcoprimem : Nat.Coprime (3 ^ (3 * (e - k) + a) * q ^ k) m :=
      Nat.coprime_mul_iff_left.mpr ⟨h3m.pow_left _, hqm.pow_left _⟩
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcoprimem).mp ⟨hprefix, hmxy⟩
  -- The constructive branch has private points for every original class.
  by_cases hprivate : ∀ i, ∃ z, z ≡ residue i [MOD modulus i] ∧
      ∀ j, j ≠ i → ¬z ≡ residue j [MOD modulus j]
  swap
  · push Not at hprivate
    obtain ⟨bad, hbad⟩ := hprivate
    apply delete_redundant modulus residue hnonunit bad
    intro z
    obtain ⟨i, hi⟩ := hcover z
    by_cases hne : i ≠ bad
    · exact ⟨i, hne, hi⟩
    have hieq : i = bad := Classical.not_not.mp hne
    subst i
    obtain ⟨j, hj, hz⟩ := hbad z hi
    exact ⟨j, hj, hz⟩
  have hq3 : Nat.Coprime q 3 := hq.coprime_iff_not_dvd.mpr (by
    intro h; have := Nat.le_of_dvd (by decide : 0 < 3) h; omega)
  have hqW : Nat.Coprime q W := (Nat.coprime_mul_iff_right.mp hW).2.symm
  have hqR : Nat.Coprime q (9 * W) := by
    simpa only [show 9 = 3^2 by norm_num] using (hq3.pow_right 2).mul_right hqW
  have hperiod' : ∀ i, modulus i ∣ q^G*(9*W) := by
    intro i; convert hperiod i using 1; ring
  have hdecomp := fun i => decompose hq hcontract hW (hperiod i)
  choose a e m ha he hm hmpos hmco hdeq using hdecomp
  have hvals : ∀ i, (modulus i).factorization 3 = a i ∧
      (modulus i).factorization q = e i := by
    intro i; rw [hdeq]; exact factorization_values hq hcontract (hmco i) (hmpos i)
  have hdonore : e donor = k+1 := by
    have := (hvals donor).2
    rw [hpure] at this
    simpa [Nat.factorization_pow, hq.factorization] using this.symm
  have hkG : k+1 ≤ G := hdonore ▸ he donor
  let J : Fin L → Prop := fun i => q^(k+1) ∣ modulus i ∧ residue i ≡ residue donor [MOD q^k]
  have hdonorJ : J donor := ⟨by rw [hpure], Nat.ModEq.refl _⟩
  have hJexp : ∀ i, J i → k+1 ≤ e i := by
    intro i hi
    have hh := (hq.pow_dvd_iff_le_factorization (by have := hnonunit i; omega)).mp hi.1
    simpa only [(hvals i).2] using hh
  have hprefix := prefix_liability modulus residue hq hqR hperiod' hcover donor hpure
    (fun i _ hne => by
      obtain ⟨z, hzi, hz⟩ := hprivate i
      exact ⟨z, hzi, hz donor (Ne.symm hne)⟩)
  let Private : ℕ → Prop := fun y => y ≡ residue donor [MOD modulus donor] ∧
    ∀ i, i ≠ donor → ¬ y ≡ residue i [MOD modulus i]
  let Lambda : Finset (Fin 9) := Finset.univ.filter (fun v => ∃ y, Private y ∧ y%9=v.val)
  have hLambda : ∀ x, (⟨x%9, Nat.mod_lt _ (by decide)⟩ : Fin 9) ∈ Lambda ↔
      ∃ y, Private y ∧ y%9=x%9 := by simp [Lambda]
  obtain ⟨y0, hy0⟩ := hprivate donor
  let c0 : Fin 9 := ⟨y0%9, Nat.mod_lt _ (by decide)⟩
  have hc0 : c0 ∈ Lambda := by exact (hLambda y0).mpr ⟨y0, hy0, rfl⟩
  have hcap : 27*Lambda.card+1 ≤ q+9 := by
    have hcard : Lambda.card = Nat.card {v : Fin 9 // ∃ y : ℕ,
      y ≡ residue donor [MOD modulus donor] ∧
      (∀ i, i≠donor → ¬y ≡ residue i [MOD modulus i]) ∧ y%9=v.val} := by
      simp [Lambda, Private, Nat.card_eq_fintype_card, Fintype.card_subtype, and_assoc]
    simpa only [hcard] using hcapacity
  let delta : Fin q := ⟨(residue donor / q^k)%q, Nat.mod_lt _ hq.pos⟩
  obtain ⟨first, hfirst, havoid, hinitial⟩ :=
    terminal_initial_fragment hcontract Lambda c0 hc0 delta hcap
  let allowed : ℕ → Prop := fun x =>
    (⟨x%9, Nat.mod_lt _ (by decide)⟩ : Fin 9) ∈ Lambda ∧ x%27≠c0.val
  obtain ⟨f, hffirst, hfsep⟩ := terminal_radix_fragment hcontract
    (by omega : 1 ≤ G-k) allowed first hfirst hinitial
  let u := residue donor % q^k
  let source : ℕ → ℕ := fun x =>
    (Nat.chineseRemainder (hqR.pow_left G) (u+q^k*f x) x).val
  have hsourceq : ∀ x, source x ≡ u+q^k*f x [MOD q^G] := fun x =>
    (Nat.chineseRemainder (hqR.pow_left G) (u+q^k*f x) x).property.1
  have hsourceR : ∀ x, source x ≡ x [MOD 9*W] := fun x =>
    (Nat.chineseRemainder (hqR.pow_left G) (u+q^k*f x) x).property.2
  have hsourceparent : ∀ x, source x ≡ residue donor [MOD q^k] := by
    intro x
    exact ((hsourceq x).of_dvd (pow_dvd_pow q (by omega))).trans (by
      simp [Nat.ModEq, u])
  have hsourcemiss : ∀ x, allowed x → ¬source x ≡ residue donor [MOD modulus donor] := by
    intro x hx hmatch
    have hcode : u+q^k*f x ≡ residue donor [MOD q^(k+1)] :=
      ((hsourceq x).of_dvd (pow_dvd_pow q hkG)).symm.trans (by simpa only [hpure] using hmatch)
    have hmod : (u+q^k*f x)%q^(k+1) = (residue donor)%q^(k+1) := hcode
    have hleft : (u+q^k*f x)%q^(k+1) = u+q^k*(f x%q) := by
      rw [pow_succ, Nat.mod_mul]
      rw [Nat.add_mul_mod_self_left]
      have hu : u < q^k := Nat.mod_lt _ (pow_pos hq.pos _)
      simp [Nat.mod_eq_of_lt hu, Nat.div_eq_of_lt hu, Nat.add_mul_div_left, pow_pos hq.pos]
    have hright : residue donor % q^(k+1) = u+q^k*((residue donor/q^k)%q) :=
      Nat.mod_mul (a:=q^k) (b:=q)
    rw [hleft, hright, hffirst] at hmod
    have hsame : first x = delta.val := by dsimp [delta]; nlinarith [pow_pos hq.pos k]
    exact havoid x hx hsame
  have hsourcehole : ∀ x, (∀ i, ¬J i → ¬x ≡ residue i [MOD modulus i]) →
      ∀ i, ¬J i → ¬source x ≡ residue i [MOD modulus i] := by
    intro x hx
    obtain ⟨_, y, hy, hpriv, hyR⟩ := (hprefix x).mp hx
    exact (hprefix (source x)).mpr ⟨hsourceparent x, y, hy, hpriv,
      hyR.trans (hsourceR x).symm⟩
  have hdonora : a donor = 0 := by
    have hh := (hvals donor).1
    rw [hpure] at hh
    simpa [Nat.factorization_pow, hq.factorization, (show q≠3 by omega)] using hh.symm
  have hdonorm : m donor = 1 := by
    have hh := hdeq donor
    rw [hpure, hdonora, hdonore, pow_zero, one_mul] at hh
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hq.pos _) (by simpa using hh.symm)
  let label : Fin L → ℕ := fun i => 3^(3*(e i-k)+a i)*q^k*m i
  have hlabeldonor : label donor = 27*q^k := by
    simp [label, hdonora, hdonore, hdonorm]
  let terminal : ℕ := (Nat.chineseRemainder ((hq3.pow_left k).pow_right 3)
    (residue donor) c0.val).val
  have hterminal : ∀ x, x ≡ residue donor [MOD q^k] → x%27=c0.val →
      x ≡ terminal [MOD label donor] := by
    intro x hx hterm
    have htq : terminal ≡ residue donor [MOD q^k] :=
      (Nat.chineseRemainder ((hq3.pow_left k).pow_right 3) (residue donor) c0.val).property.1
    have ht3 : terminal ≡ c0.val [MOD 27] :=
      (Nat.chineseRemainder ((hq3.pow_left k).pow_right 3) (residue donor) c0.val).property.2
    have hx3 : x ≡ c0.val [MOD 27] := by
      change x%27=c0.val%27
      simpa only [Nat.mod_eq_of_lt (by have := c0.isLt; omega : c0.val<27)] using hterm
    rw [hlabeldonor]
    exact (Nat.modEq_and_modEq_iff_modEq_mul (by
      simpa using ((hq3.pow_left k).pow_right 3).symm)).mp
      ⟨hx3.trans ht3.symm, hx.trans htq.symm⟩
  let inverse : Fin L → ℕ → Prop := fun i x =>
    x ≡ residue donor [MOD q^k] ∧ allowed x ∧ source x ≡ residue i [MOD modulus i]
  let Has : Fin L → Prop := fun i => ∃ x, inverse i x
  let chosen : Fin L → ℕ := fun i => if h : Has i then h.choose else 0
  have hchosen : ∀ i, Has i → inverse i (chosen i) := by
    intro i hi
    simpa only [chosen, dif_pos hi] using hi.choose_spec
  have enclosure : ∀ i, J i → ∀ x y, inverse i x → inverse i y →
      x ≡ y [MOD label i] := by
    intro i hi x y hx hy
    apply donor_enclosure_fragment hq hcontract (ha i) (by have := hJexp i hi; omega)
      (he i) (hm i) (hmco i) allowed f source u
      hsourceq hsourceR hfsep hx.2.1 hy.2.1 (hx.1.trans hy.1.symm)
    simpa only [←hdeq i] using hx.2.2.trans hy.2.2.symm
  let active : Fin L → Prop := fun i => ¬J i ∨ i=donor ∨ Has i
  let newmod : Fin L → ℕ := fun i => if J i then label i else modulus i
  let newres : Fin L → ℕ := fun i => if J i then
    (if i=donor then terminal else chosen i) else residue i
  have hnewcover : ∀ x, ∃ i, active i ∧ x ≡ newres i [MOD newmod i] := by
    intro x
    by_cases hret : ∃ i, ¬J i ∧ x ≡ residue i [MOD modulus i]
    · obtain ⟨i, hi, hxi⟩ := hret
      exact ⟨i, Or.inl hi, by simpa only [newres, newmod, if_neg hi] using hxi⟩
    have hxhole : ∀ i, ¬J i → ¬x ≡ residue i [MOD modulus i] := by
      intro i hi hxi; exact hret ⟨i,hi,hxi⟩
    obtain ⟨hxparent,y,hy,hpriv,hyR⟩ := (hprefix x).mp hxhole
    by_cases hterm : x%27=c0.val
    · refine ⟨donor, Or.inr (Or.inl rfl), ?_⟩
      simpa only [newres, newmod, if_pos hdonorJ, if_true] using hterminal x hxparent hterm
    have hxallowed : allowed x := ⟨(hLambda x).mpr ⟨y, ⟨hy,hpriv⟩,
      hyR.of_dvd (dvd_mul_right 9 W)⟩, hterm⟩
    obtain ⟨i,hsi⟩ := hcover (source x)
    have hi : J i := by
      by_contra hni; exact hsourcehole x hxhole i hni hsi
    have hne : i≠donor := by
      intro heq; subst i; exact hsourcemiss x hxallowed hsi
    have hxi : inverse i x := ⟨hxparent,hxallowed,hsi⟩
    have hhas : Has i := ⟨x,hxi⟩
    refine ⟨i, Or.inr (Or.inr hhas), ?_⟩
    simpa only [newres,newmod,if_pos hi,if_neg hne] using
      enclosure i hi x (chosen i) hxi (hchosen i hhas)
  have hlabelbound : ∀ i, J i → 1<label i ∧ label i<modulus i := by
    intro i hi
    simpa only [label,hdeq i] using
      label_bounds hcontract (by have := hJexp i hi; omega : k<e i) (hmpos i)
  apply assemble modulus active newmod newres hnewcover
  · intro i _
    by_cases hi : J i
    · simpa only [newmod,if_pos hi] using (hlabelbound i hi).1
    · simpa only [newmod,if_neg hi] using hnonunit i
  · intro i
    by_cases hi : active i
    · rw [if_pos hi]
      by_cases hj : J i
      · simpa only [newmod,if_pos hj] using (hlabelbound i hj).2.le
      · simp only [newmod,if_neg hj,le_refl]
    · simp only [if_neg hi,zero_le]
  · refine ⟨donor, ?_⟩
    have hdactive : active donor := Or.inr (Or.inl rfl)
    simpa only [if_pos hdactive,newmod,if_pos hdonorJ] using (hlabelbound donor hdonorJ).2
  · intro hold i j _ _ hij
    apply hold
    by_cases hi : J i <;> by_cases hj : J j
    · have hh : label i=label j := by simpa only [newmod,if_pos hi,if_pos hj] using hij
      rw [hdeq i,hdeq j]
      exact label_injective hq hcontract (ha i) (ha j)
        (by have := hJexp i hi; omega) (by have := hJexp j hj; omega)
        (hmco i) (hmco j) (hmpos i) (hmpos j) hh
    · have hh : label i=modulus j := by simpa only [newmod,if_pos hi,if_neg hj] using hij
      exact False.elim (label_ne_retained (a:=a i) (e:=e i) (k:=k) (f:=e j) hq hcontract (ha j)
        (by have := hJexp i hi; omega) (hmco i) (hmco j) (hmpos i) (hmpos j)
        (by simpa only [label,hdeq j] using hh))
    · have hh : label j=modulus i := by simpa only [newmod,if_pos hj,if_neg hi] using hij.symm
      exact False.elim (label_ne_retained (a:=a j) (e:=e j) (k:=k) (f:=e i) hq hcontract (ha i)
        (by have := hJexp j hj; omega) (hmco j) (hmco i) (hmpos j) (hmpos i)
        (by simpa only [label,hdeq i] using hh))
    · simpa only [newmod,if_neg hi,if_neg hj] using hij
  · intro hold i _
    by_cases hi : J i
    · have hmOdd : Odd (m i) := (Nat.odd_mul.mp (by simpa only [hdeq i] using hold i)).2
      have hqOdd : Odd q := hq.odd_of_ne_two (by omega)
      simpa only [newmod,if_pos hi,label] using
        (((by decide : Odd (3:ℕ)).pow).mul hqOdd.pow).mul hmOdd
    · simpa only [newmod,if_neg hi] using hold i

end Erdos7
