/- GID: D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelIntervals
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelIntervals
   mirror-E: none(waiver:binary-run-interval-construction)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Forbidden binary runs construct witnesses in the cyclotomic zero intervals. -/

import D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelIntervals

open CyclotomicDigitHankelDefs

/-- Evaluate alternating constant binary runs, with the first run having bit `b`. -/
def runValue (b : Bool) : List ℕ → ℕ
  | [] => 0
  | a :: rs => (if b then 2 ^ a - 1 else 0) * 2 ^ rs.sum + runValue (!b) rs

/-- The surviving run language: internal runs are short, with the two terminal exceptions. -/
def RunAdmissible (d : ℕ) : List ℕ → Prop
  | [] => False
  | [a] => a ≤ d
  | [a, b] => a ≤ d ∧ b ≤ d ∧ (a < d ∨ b < d)
  | a :: b :: c :: rs => a < d ∧ RunAdmissible d (b :: c :: rs)

/-- A forbidden binary-run expansion places its integer in a cyclotomic zero interval. -/
theorem forbidden_runs_mem (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (hm : 0 < m)
    (hbad : ∀ rs : List ℕ, rs ≠ [] → (∀ a ∈ rs, 0 < a) →
      runValue true rs = m → ¬RunAdmissible d rs) : InZeroSet d (m + 1) := by
  have forbidden (b : Bool) (rs : List ℕ) (hrs : ∀ a ∈ rs, 0 < a)
      (hne : rs ≠ []) (p : ℕ) (hp : p % 2 = if b then 0 else 1)
      (hbad : ¬RunAdmissible d rs) :
      InZeroSet d (2 ^ rs.sum * p + runValue b rs + 1) := by
    have rv : ∀ (ss : List ℕ) (bit : Bool),
        runValue bit ss < 2 ^ ss.sum ∧
        runValue bit ss + runValue (!bit) ss = 2 ^ ss.sum - 1 := by
      intro ss
      induction ss with
      | nil => intro bit; cases bit <;> simp [runValue]
      | cons a ss ih =>
        intro bit
        have h0 := ih false
        have h1 := ih true
        have ha : 0 < 2 ^ a := by positivity
        have hs : 0 < 2 ^ ss.sum := by positivity
        have hasub : 2 ^ a - 1 + 1 = 2 ^ a := by omega
        have hssub : 2 ^ ss.sum - 1 + 1 = 2 ^ ss.sum := by omega
        simp only [Bool.not_false, Bool.not_true] at h0 h1
        have hm := congrArg (· * 2 ^ ss.sum) hasub
        have hprod : 2 ^ a * 2 ^ ss.sum - 1 + 1 = 2 ^ a * 2 ^ ss.sum := by
          have : 0 < 2 ^ a * 2 ^ ss.sum := Nat.mul_pos ha hs
          omega
        simp only [List.sum_cons, pow_add]
        cases bit <;> simp only [runValue, Bool.not_false, Bool.not_true,
          Bool.false_eq_true, if_false, if_true, zero_mul]
        · constructor
          · nlinarith [h1.1]
          · nlinarith [h1.2]
        · constructor
          · nlinarith [h0.1]
          · nlinarith [h1.2]
    have zlow : ∀ l : ℕ, d + 1 ≤ l → (2 : ℤ) ^ (l - d) - 2 ≤ zBound d l := by
      intro l hl
      let r := (l - 1) % d + 1
      let q := (l - 1) / d
      have hd0 : 0 < d := by omega
      have hr : 1 ≤ r ∧ r ≤ d := by
        have := Nat.mod_lt (l - 1) hd0
        dsimp [r]
        omega
      have hlq : l = q * d + r := by
        have hh := Nat.mod_add_div (l - 1) d
        rw [Nat.mul_comm d] at hh
        change l = (l - 1) / d * d + ((l - 1) % d + 1)
        omega
      have hq : 1 ≤ q := by
        by_contra hh
        have : q = 0 := Nat.eq_zero_of_not_pos hh
        simp only [this, zero_mul, zero_add] at hlq
        omega
      have he : (l - r) / d = q := by
        have : l - r = q * d := by omega
        rw [this, Nat.mul_div_cancel _ hd0]
      have hexp : l - d = r + (q - 1) * d := by
        have : q * d = d + (q - 1) * d := by
          have : q = q - 1 + 1 := by omega
          calc
            q * d = (q - 1 + 1) * d := congrArg (· * d) this
            _ = d + (q - 1) * d := by ring
        omega
      have hpow : (2 : ℤ) ^ (q * d) = 2 ^ d * 2 ^ ((q - 1) * d) := by
        have : q * d = d + (q - 1) * d := by
          have : q = q - 1 + 1 := by omega
          calc
            q * d = (q - 1 + 1) * d := congrArg (· * d) this
            _ = d + (q - 1) * d := by ring
        rw [this, pow_add]
      have hden : 0 < (2 : ℤ) ^ d - 1 := by
        have : (2 : ℤ) ^ 1 ≤ 2 ^ d := by gcongr <;> omega
        norm_num at this ⊢
        omega
      have hquot : (2 : ℤ) ^ (l - d) ≤
          2 ^ r * (2 ^ (q * d) - 1) / (2 ^ d - 1) := by
        apply (Int.le_ediv_iff_mul_le hden).2
        rw [hexp, pow_add, hpow]
        have hge : (1 : ℤ) ≤ 2 ^ ((q - 1) * d) := by
          exact one_le_pow₀ (by norm_num)
        have hpr : 0 ≤ (2 : ℤ) ^ r := by positivity
        nlinarith
      unfold zBound
      change _ ≤ (2 : ℤ) ^ r * (2 ^ (((l - r) / d) * d) - 1) /
        (2 ^ d - 1) - if r < d then 2 else 1
      rw [he]
      split_ifs <;> omega
    have zdouble : zBound d (2 * d) = (2 : ℤ) ^ d - 1 := by
      have hd0 : 0 < d := by omega
      have hmod : (2 * d - 1) % d = d - 1 := by
        have : 2 * d - 1 = d + (d - 1) := by omega
        rw [this, Nat.add_mod]
        simp [Nat.mod_eq_of_lt (show d - 1 < d by omega)]
      have hr : (2 * d - 1) % d + 1 = d := by omega
      unfold zBound
      simp only [hr]
      have he : (2 * d - d) / d = 1 := by
        rw [show 2 * d - d = d by omega, Nat.div_self hd0]
      rw [he]
      simp only [one_mul, lt_self_iff_false, if_false]
      have hp : (2 : ℤ) ^ d - 1 ≠ 0 := by
        have : (2 : ℤ) ^ 1 ≤ 2 ^ d := by gcongr <;> omega
        norm_num at this
        omega
      rw [Int.mul_ediv_cancel _ hp]
    have sharp : ∀ (a c : ℕ) (ts : List ℕ), 0 < c →
        (∀ e ∈ ts, 0 < e) → runValue true (a :: c :: ts) ≤ 2 ^ (a + c + ts.sum) - 2 := by
      intro a c ts hc hts
      have hc2 : 2 ≤ 2 ^ c := by
        have : 2 ^ 1 ≤ (2 : ℕ) ^ c := by gcongr <;> omega
        simpa using this
      have hcval := rv ts true
      have ha : 0 < (2 : ℕ) ^ a := by positivity
      have ht : 0 < (2 : ℕ) ^ ts.sum := by positivity
      simp only [runValue, Bool.not_true, Bool.not_false, if_true, if_false, zero_mul,
        Bool.false_eq_true, List.sum_cons, pow_add]
      have haSub : 2 ^ a - 1 + 1 = 2 ^ a := by omega
      have htSub : 2 ^ (a + c + ts.sum) - 2 + 2 = 2 ^ (a + c + ts.sum) := by
        have : 2 ≤ (2 : ℕ) ^ (a + c + ts.sum) := by
          have : 2 ^ 1 ≤ (2 : ℕ) ^ (a + c + ts.sum) := by gcongr <;> omega
          simpa using this
        omega
      rw [pow_add, pow_add] at htSub
      have hm := congrArg (· * (2 ^ c * 2 ^ ts.sum)) haSub
      have hh : 2 * 2 ^ ts.sum ≤ 2 ^ c * 2 ^ ts.sum :=
        Nat.mul_le_mul_right _ hc2
      nlinarith [hcval.1]
    induction rs generalizing b p with
    | nil => exact (hne rfl).elim
    | cons a ts ih =>
      have ha : 0 < a := hrs a (by simp)
      have hts : ∀ e ∈ ts, 0 < e := by intro e he; exact hrs e (by simp [he])
      have local_mem : ∀ l r : ℕ, l = a + ts.sum → d + 1 ≤ l →
          (r : ℤ) ≤ zBound d l → r = runValue true ts →
          InZeroSet d (2 ^ (a + ts.sum) * p + runValue b (a :: ts) + 1) := by
        intro l r hl hld hr hre
        subst l
        subst r
        have hc := (rv ts false).2
        simp only [Bool.not_false] at hc
        have ht : 0 < (2 : ℕ) ^ ts.sum := by positivity
        have ha2 : 0 < (2 : ℕ) ^ a := by positivity
        have hasub : 2 ^ a - 1 + 1 = 2 ^ a := by omega
        have htsub : 2 ^ ts.sum - 1 + 1 = 2 ^ ts.sum := by omega
        cases b with
        | false =>
          have hpodd : Odd p := Nat.odd_iff.mpr (by simpa using hp)
          refine ⟨by omega, a + ts.sum, p, hld, hpodd, ?_, ?_⟩
          all_goals simp only [runValue, Bool.not_false, Bool.false_eq_true,
            if_false, zero_mul, zero_add, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
            Nat.cast_ofNat]
          all_goals omega
        | true =>
          have hs : Odd (p + 1) := Nat.odd_iff.mpr (by simp only [if_true] at hp; omega)
          have hbig : runValue true ts ≤ 2 ^ (a + ts.sum) * (p + 1) := by
            have hrv := (rv ts true).1
            rw [pow_add]
            calc
              runValue true ts ≤ 2 ^ ts.sum := by omega
              _ ≤ 2 ^ a * 2 ^ ts.sum := Nat.le_mul_of_pos_left _ ha2
              _ ≤ 2 ^ a * 2 ^ ts.sum * (p + 1) :=
                Nat.le_mul_of_pos_right _ (by omega)
          have hv : 2 ^ (a + ts.sum) * p + runValue true (a :: ts) + 1 =
              2 ^ (a + ts.sum) * (p + 1) - runValue true ts := by
            rw [pow_add]
            simp only [runValue, Bool.not_true, if_true]
            have hm := congrArg (· * 2 ^ ts.sum) hasub
            have hb : runValue true ts ≤ 2 ^ a * 2 ^ ts.sum * (p + 1) := by
              simpa [pow_add] using hbig
            have hs : 2 ^ a * 2 ^ ts.sum * (p + 1) - runValue true ts +
                runValue true ts = 2 ^ a * 2 ^ ts.sum * (p + 1) := by omega
            nlinarith
          refine ⟨by omega, a + ts.sum, p + 1, hld, hs, ?_, ?_⟩
          all_goals rw [hv]
          all_goals simp only [Nat.cast_sub hbig, Nat.cast_mul, Nat.cast_pow,
            Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
          all_goals omega
      simp only [List.sum_cons]
      by_cases habig : d < a
      · have hl : d + 1 ≤ a + ts.sum := by omega
        have hlo := zlow (a + ts.sum) hl
        have hrv := (rv ts true).1
        have hpow2 : 2 * (2 : ℕ) ^ ts.sum ≤ 2 ^ (a + ts.sum - d) := by
          rw [← pow_succ']
          exact Nat.pow_le_pow_right (by omega) (by omega)
        apply local_mem (a + ts.sum) (runValue true ts) rfl hl _ rfl
        have hpos : 0 < (2 : ℕ) ^ ts.sum := by positivity
        exact_mod_cast (show (runValue true ts : ℤ) ≤ zBound d (a + ts.sum) by
          have hh : (runValue true ts : ℤ) < (2 : ℤ) ^ ts.sum := by exact_mod_cast hrv
          have hh2 : 2 * (2 : ℤ) ^ ts.sum ≤ 2 ^ (a + ts.sum - d) := by
            exact_mod_cast hpow2
          omega)
      · have had : a ≤ d := by omega
        by_cases hadsmall : a < d
        · have hbadts : ¬RunAdmissible d ts := by
            intro hgood
            cases ts with
            | nil => exact hbad had
            | cons c tail =>
              cases tail with
              | nil => exact hbad ⟨had, hgood, Or.inl hadsmall⟩
              | cons e rest => exact hbad ⟨hadsmall, hgood⟩
          have hnets : ts ≠ [] := by intro he; subst ts; exact hbad had
          let p' := 2 ^ a * p + if b then 2 ^ a - 1 else 0
          have hp' : p' % 2 = if !b then 0 else 1 := by
            have he : 2 ^ a % 2 = 0 := by
              obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
              rw [hj, pow_succ]
              simp
            cases b <;> simp [p', Nat.add_mod, Nat.mul_mod, he]
            have hp2 : 0 < 2 ^ a := by positivity
            omega
          have hchild := ih (!b) hts hnets p' hp' hbadts
          have heq : 2 ^ ts.sum * p' + runValue (!b) ts + 1 =
              2 ^ (a :: ts).sum * p + runValue b (a :: ts) + 1 := by
            simp only [List.sum_cons, pow_add, runValue]
            dsimp [p']
            ring
          rwa [heq] at hchild
        · have had_eq : a = d := by omega
          subst a
          cases ts with
          | nil => exact (hbad (by exact le_rfl)).elim
          | cons c tail =>
            have hc : 0 < c := hts c (by simp)
            cases tail with
            | nil =>
              have hcge : d ≤ c := by
                by_contra hh
                exact hbad ⟨le_rfl, by omega, Or.inr (by omega)⟩
              by_cases hcbig : d < c
              · have hn : [c] ≠ ([] : List ℕ) := by simp
                have hbadc : ¬RunAdmissible d [c] := by
                  change ¬c ≤ d
                  omega
                let p' := 2 ^ d * p + if b then 2 ^ d - 1 else 0
                have hp' : p' % 2 = if !b then 0 else 1 := by
                  have he : 2 ^ d % 2 = 0 := by
                    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
                    rw [hj, pow_succ]
                    simp
                  cases b <;> simp [p', Nat.add_mod, Nat.mul_mod, he]
                  have hp2 : 0 < 2 ^ d := by positivity
                  omega
                have hchild := ih (!b) hts hn p' hp' hbadc
                have heq : 2 ^ [c].sum * p' + runValue (!b) [c] + 1 =
                    2 ^ (d :: [c]).sum * p + runValue b (d :: [c]) + 1 := by
                  simp only [List.sum_cons, pow_add, runValue]
                  dsimp [p']
                  ring
                rwa [heq] at hchild
              · have he : c = d := by omega
                subst c
                apply local_mem (2 * d) (2 ^ d - 1)
                · simp; omega
                · omega
                · rw [zdouble]
                  have hpd : 1 ≤ (2 : ℕ) ^ d := one_le_pow₀ (by omega)
                  exact_mod_cast (le_refl (2 ^ d - 1))
                · simp [runValue]
            | cons e rest =>
              have he : 0 < e := hts e (by simp)
              have hpos : 0 < c + e + rest.sum := by omega
              have hl : d + 1 ≤ d + (c :: e :: rest).sum := by simp; omega
              apply local_mem (d + (c :: e :: rest).sum)
                (runValue true (c :: e :: rest)) rfl hl _ rfl
              have hh := sharp c e rest he (by
                intro j hj; exact hts j (by simp [hj]))
              have hlo := zlow (d + (c :: e :: rest).sum) hl
              simp only [List.sum_cons, Nat.add_sub_cancel_left] at hlo
              exact_mod_cast (show (runValue true (c :: e :: rest) : ℤ) ≤
                  zBound d (d + (c :: e :: rest).sum) by
                have hh' : (runValue true (c :: e :: rest) : ℤ) ≤
                    (2 : ℤ) ^ (c + e + rest.sum) - 2 := by
                  have hsize : 2 ≤ (2 : ℕ) ^ (c + e + rest.sum) := by
                    have : 2 ^ 1 ≤ (2 : ℕ) ^ (c + e + rest.sum) := by gcongr <;> omega
                    simpa using this
                  exact_mod_cast hh
                have hsum : c + (e + rest.sum) = c + e + rest.sum := by omega
                rw [hsum] at hlo
                simpa only [List.sum_cons, ← Nat.add_assoc] using hh'.trans hlo)
  have run_representation (m : ℕ) (hm : 0 < m) :
      ∃ rs : List ℕ, rs ≠ [] ∧ (∀ a ∈ rs, 0 < a) ∧ runValue true rs = m := by
    let appendBit (b : Bool) (rs : List ℕ) (c : Bool) : List ℕ :=
      (List.rec (motive := fun _ : List ℕ => Bool → Bool → List ℕ)
        (fun (_ _ : Bool) => [1])
        (fun a tail ih b c => match tail with
          | [] => if b == c then [a + 1] else [a, 1]
          | _ :: _ => a :: ih (!b) c) rs) b c
    have append_spec : ∀ (rs : List ℕ) (b c : Bool), rs ≠ [] →
        (∀ a ∈ rs, 0 < a) →
        appendBit b rs c ≠ [] ∧
        (∀ a ∈ appendBit b rs c, 0 < a) ∧
        (appendBit b rs c).sum = rs.sum + 1 ∧
        runValue b (appendBit b rs c) = 2 * runValue b rs + if c then 1 else 0 := by
      intro rs
      induction rs with
      | nil => intro b c hn; exact (hn rfl).elim
      | cons a rs ih =>
        intro b c hn hpos
        have ha : 0 < a := hpos a (by simp)
        have hpa : 0 < (2 : ℕ) ^ a := by positivity
        have has : 2 ^ a - 1 + 1 = 2 ^ a := by omega
        cases rs with
        | nil =>
          cases b <;> cases c <;>
            simp only [appendBit]
          all_goals refine ⟨by simp, ?_, by simp, ?_⟩
          all_goals simp [runValue, pow_succ]
          all_goals omega
        | cons e tail =>
          have hs : ∀ j ∈ e :: tail, 0 < j := by
            intro j hj; exact hpos j (by simp [hj])
          have hh := ih (!b) c (by simp) hs
          simp only [appendBit]
          refine ⟨by simp, ?_, ?_, ?_⟩
          · intro j hj
            simp only [List.mem_cons] at hj
            rcases hj with rfl | hj
            · exact ha
            · exact hh.2.1 j hj
          · change a + (appendBit (!b) (e :: tail) c).sum = a + (e :: tail).sum + 1
            rw [hh.2.2.1]
            omega
          · change (if b then 2 ^ a - 1 else 0) *
                2 ^ (appendBit (!b) (e :: tail) c).sum +
                runValue (!b) (appendBit (!b) (e :: tail) c) =
              2 * ((if b then 2 ^ a - 1 else 0) * 2 ^ (e :: tail).sum +
                runValue (!b) (e :: tail)) + if c then 1 else 0
            rw [hh.2.2.1, pow_succ, hh.2.2.2]
            ring
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases hsmall : m = 1
      · subst m
        refine ⟨[1], by simp, ?_, ?_⟩
        · intro a ha; simp only [List.mem_singleton] at ha; omega
        · norm_num [runValue]
      · have hm2 : 2 ≤ m := by omega
        have hhalf : 0 < m / 2 := by omega
        have hless : m / 2 < m := Nat.div_lt_self hm (by omega)
        obtain ⟨rs, hne, hrs, hr⟩ := ih (m / 2) hless hhalf
        by_cases hbit : m % 2 = 0
        · have hh := append_spec rs true false hne hrs
          refine ⟨appendBit true rs false, hh.1, hh.2.1, ?_⟩
          rw [hh.2.2.2, hr]
          simp only [Bool.false_eq_true, if_false, add_zero]
          omega
        · have hh := append_spec rs true true hne hrs
          refine ⟨appendBit true rs true, hh.1, hh.2.1, ?_⟩
          rw [hh.2.2.2, hr]
          simp only [if_true]
          omega
  obtain ⟨rs, hne, hrs, heq⟩ := run_representation m hm
  have h := forbidden true rs hrs hne 0 (by norm_num) (hbad rs hne hrs heq)
  simpa only [mul_zero, zero_add, heq] using h

/-- Peel a run through regular phases and the singular phase, then induct on the run list. -/
theorem run_survival (d : ℕ) (hd : 2 ≤ d) (P : ℕ → List ℕ → Prop)
    (hterm : ∀ a : ℕ, P a [1])
    (hdelete : ∀ (a L : ℕ) (tail : List ℕ),
      (∀ e ∈ L :: tail, 0 < e) → 1 < L → ¬d ∣ a →
      (P a (L :: tail) ↔ P (a + 1) ((L - 1) :: tail)))
    (hreflect : ∀ (a : ℕ) (tail : List ℕ),
      (∀ e ∈ tail, 0 < e) → tail ≠ [] → ¬d ∣ a →
      (P a (1 :: tail) ↔ P 1 tail))
    (hsingular : ∀ (a L : ℕ) (tail : List ℕ),
      (∀ e ∈ L :: tail, 0 < e) → d ∣ a →
      (P a (L :: tail) ↔ L = 1 ∧
        (tail = [] ∨ ∃ K : ℕ, tail = [K] ∧ K < d)))
    (rs : List ℕ) (hrs : ∀ a ∈ rs, 0 < a) (hne : rs ≠ []) :
    P 1 rs ↔ RunAdmissible d rs := by
  have peel : ∀ (L : ℕ) (a : ℕ) (tail : List ℕ), 0 < L → 1 ≤ a → a ≤ d →
      (∀ e ∈ tail, 0 < e) →
      (P a (L :: tail) ↔
        if L < d - a + 1 then tail = [] ∨ P 1 tail
        else if L = d - a + 1 then tail = [] ∨ ∃ K : ℕ, tail = [K] ∧ K < d
        else False) := by
    intro L
    induction L with
    | zero => intro a tail hL; omega
    | succ L ih =>
      intro a tail hL ha had htail
      have hpositive : ∀ e ∈ (L + 1) :: tail, 0 < e := by
        intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · omega
        · exact htail e he
      by_cases hae : a = d
      · subst a
        have hs := hsingular d (L + 1) tail hpositive (dvd_refl d)
        simpa using hs
      · have hadlt : a < d := by omega
        have hregular : ¬d ∣ a := by
          intro hh
          have := Nat.le_of_dvd (by omega : 0 < a) hh
          omega
        by_cases hzero : L = 0
        · subst L
          simp only [zero_add]
          have hc : 1 < d - a + 1 := by omega
          rw [if_pos hc]
          cases tail with
          | nil => simp [hterm]
          | cons K tail =>
            simpa using hreflect a (K :: tail) htail (by simp) hregular
        · have hLpos : 0 < L := by omega
          have hc := hdelete a (L + 1) tail hpositive (by omega) hregular
          simp only [Nat.add_sub_cancel] at hc
          rw [hc, ih (a + 1) tail hLpos (by omega) (by omega) htail]
          have hlt : L + 1 < d - a + 1 ↔ L < d - (a + 1) + 1 := by omega
          have heq : L + 1 = d - a + 1 ↔ L = d - (a + 1) + 1 := by omega
          simp only [hlt, heq]
  induction rs with
  | nil => exact (hne rfl).elim
  | cons L tail ih =>
    have hL : 0 < L := hrs L (by simp)
    have ht : ∀ e ∈ tail, 0 < e := by intro e he; exact hrs e (by simp [he])
    have hpeel := peel L 1 tail hL (by omega) (by omega) ht
    have hphase : d - 1 + 1 = d := by omega
    rw [hphase] at hpeel
    rw [hpeel]
    cases tail with
    | nil =>
      simp only [RunAdmissible, List.nil_eq, true_or]
      split_ifs <;> simp only [true_iff, false_iff] <;> omega
    | cons K rest =>
      have hchild := ih ht (by simp)
      cases rest with
      | nil =>
        simp only [RunAdmissible] at hchild ⊢
        have hk : 0 < K := ht K (by simp)
        simp only [List.cons_ne_nil, false_or, List.cons.injEq,
          and_true]
        have hext : (∃ j : ℕ, K = j ∧ j < d) ↔ K < d := by
          constructor
          · rintro ⟨j, rfl, hj⟩; exact hj
          · intro hj; exact ⟨K, rfl, hj⟩
        simp only [hchild, hext]
        split_ifs with hlt heq
        · constructor <;> intro hh <;> omega
        · constructor <;> intro hh <;> omega
        · exact ⟨False.elim, fun hh => heq
            (Nat.le_antisymm hh.1 (Nat.le_of_not_gt hlt))⟩
      | cons J rest =>
        have hs : ¬∃ K' : ℕ, K :: J :: rest = [K'] ∧ K' < d := by simp
        simp only [RunAdmissible]
        by_cases hld : L < d
        · rw [if_pos hld]
          simpa only [List.cons_ne_nil, false_or, hld, true_and] using hchild
        · rw [if_neg hld]
          simp only [List.cons_ne_nil, false_or, hs, hld, false_and, ite_self, iff_self]

end D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelIntervals
