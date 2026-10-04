/- GID: D5/S1/Words/AdmissibleWords/KBonacciResonantWindowCounts
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciResonantWindowCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact all-length parity window counts on the two resonant phase cosets. -/

import D5.S0.Tower.DBonacciGeneral.UniformBaseGap
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Periodic
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace D5.S1.Words.AdmissibleWords.KBonacciResonantWindowCounts

open Finset D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacciGeneral.UniformBaseGap

/-- Distinct actual weight windows on the resonant coset and its one-step translate. -/
theorem kbonacci_resonant_window_counts (k m : ℕ) (hk : 2 ≤ k) (_hm : 1 ≤ m)
    (hg : 2 ≤ Nat.gcd m (k + 1)) :
    let g := Nat.gcd m (k + 1)
    let p := (k + 1) / g
    let P : Finset (ZMod (k + 1)) := univ.image (fun z => (g : ZMod (k + 1)) * z)
    let W := fun (j : ℕ) (θ : ZMod (k + 1)) (i : Fin j) =>
      (dbonacci k (θ.val + i.val + 2) : ZMod 2)
    (P.image (W 0)).card = 1 ∧
    ((P.image (fun θ => θ + 1)).image (W 0)).card = 1 ∧
    ∀ j : ℕ, 1 ≤ j →
      (P.image (W j)).card = min p (2 + j / g) ∧
      ((P.image (fun θ => θ + 1)).image (W j)).card = min p (1 + (j + 1) / g) := by
  classical
  let T := k + 1
  let g := Nat.gcd m T
  let p := T / g
  let c := fun n => (dbonacci k (n + 2) : ZMod 2)
  let P : Finset (ZMod T) := univ.image (fun z => (g : ZMod T) * z)
  let W := fun (j : ℕ) (θ : ZMod T) (i : Fin j) => c (θ.val + i.val)
  change (P.image (W 0)).card = 1 ∧
    ((P.image (fun θ => θ + 1)).image (W 0)).card = 1 ∧
    ∀ j : ℕ, 1 ≤ j →
      (P.image (W j)).card = min p (2 + j / g) ∧
      ((P.image (fun θ => θ + 1)).image (W j)).card = min p (1 + (j + 1) / g)
  have hT : 0 < T := by dsimp [T]; omega
  have hg' : 2 ≤ g := hg
  have hgpos : 0 < g := by omega
  have hpg : p * g = T := Nat.div_mul_cancel (Nat.gcd_dvd_right m T)
  have hppos : 0 < p := by nlinarith
  have hrec : ∀ n, dbonacci k (n + k + 2) =
      ∑ i ∈ range k, dbonacci k (n + i + 2) := by
    intro n
    rw [dbonacci_add_two_of_le k (n + k) (by omega), sum_fin_eq_sum_range]
    apply sum_congr rfl
    intro i hi
    simp [mem_range.mp hi]
  have hslide : ∀ n, dbonacci k (n + k + 1 + 2) + dbonacci k (n + 2) =
      2 * dbonacci k (n + k + 2) := by
    intro n
    have hs := sum_range_succ' (fun i => dbonacci k (n + i + 2)) k
    rw [sum_range_succ] at hs
    have hshift : (∑ i ∈ range k, dbonacci k (n + (i + 1) + 2)) =
        dbonacci k (n + k + 1 + 2) := by
      rw [show n + k + 1 = (n + 1) + k by omega, hrec]
      apply sum_congr rfl
      intro i _
      congr 1
      omega
    calc
      _ = (∑ i ∈ range k, dbonacci k (n + (i + 1) + 2)) +
          dbonacci k (n + 2) := by rw [hshift]
      _ = (∑ i ∈ range k, dbonacci k (n + i + 2)) +
          dbonacci k (n + k + 2) := hs.symm
      _ = _ := by rw [← hrec]; omega
  have hper : Function.Periodic c T := by
    intro n
    have hs := congrArg (fun a : ℕ => (a : ZMod 2)) (hslide n)
    have hs' : c (n + T) + c n = 0 := by
      simpa [c, T, Nat.cast_add, Nat.cast_mul, Nat.add_assoc, CharTwo.two_eq_zero] using hs
    exact CharTwo.add_eq_zero.mp hs'
  have hinit : ∀ n, n < T → c n = if n = 0 ∨ n = k then 1 else 0 := by
    intro n hn
    by_cases hnk : n = k
    · subst n
      dsimp [c]
      rw [dbonacci_diagonal_cardinality,
        Nat.cast_sub (one_le_pow_of_one_le' (by norm_num : 1 ≤ (2 : ℕ)) k)]
      have hp : (2 : ZMod 2) ^ k = 0 := by simp [CharTwo.two_eq_zero, show k ≠ 0 by omega]
      simp [Nat.cast_pow, hp]
    · have hsmall : n < k := by dsimp [T] at hn; omega
      dsimp [c]
      rw [dbonacci_add_two_of_lt k n hsmall, Nat.cast_pow]
      by_cases hn0 : n = 0
      · simp [hn0]
      · simp [hn0, hnk, CharTwo.two_eq_zero]
  have hcycle : ∀ n, c n = if n % T = 0 ∨ n % T = k then 1 else 0 := by
    intro n
    rw [← hper.map_mod_nat n]
    exact hinit _ (Nat.mod_lt _ hT)
  have hcoset : P = (range p).image (fun q => ((q * g : ℕ) : ZMod T)) := by
    ext z
    simp only [P, mem_image, mem_univ, true_and, mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨a.val % p, Nat.mod_lt _ hppos, ?_⟩
      have hmod : ∀ n : ℕ, (n % p * g) % T = (n * g) % T := by
        intro n
        rw [← hpg, Nat.mul_mod_mul_right, Nat.mul_mod_mul_right]
        simp
      calc
        _ = ((a.val * g : ℕ) : ZMod T) :=
          (ZMod.natCast_eq_natCast_iff' _ _ T).mpr (hmod a.val)
        _ = _ := by simp [Nat.cast_mul, mul_comm]
    · rintro ⟨q, hq, rfl⟩
      refine ⟨(q : ZMod T), ?_⟩
      simp [Nat.cast_mul, mul_comm]
  let a := fun r => if r = 0 then 0 else (p - r) * g
  let d := fun r => (p - (r + 1)) * g + 1
  let e := fun r => if r = 0 then 0 else r * g - 1
  let f := fun r => (r + 1) * g - 2
  have hAphase : P = (range p).image (fun r => (a r : ZMod T)) := by
    rw [hcoset]
    ext z
    simp only [mem_image, mem_range]
    constructor
    · rintro ⟨q, hq, rfl⟩
      by_cases hq0 : q = 0
      · refine ⟨0, hppos, ?_⟩
        simp [a, hq0]
      · refine ⟨p - q, by omega, ?_⟩
        have hne : p - q ≠ 0 := by omega
        have heq : p - (p - q) = q := by omega
        simp [a, hne, heq]
    · rintro ⟨r, hr, rfl⟩
      by_cases hr0 : r = 0
      · refine ⟨0, hppos, ?_⟩
        simp [a, hr0]
      · refine ⟨p - r, by omega, ?_⟩
        simp [a, hr0]
  have hDphase : P.image (fun θ => θ + 1) =
      (range p).image (fun r => (d r : ZMod T)) := by
    rw [hcoset, image_image]
    ext z
    simp only [mem_image, mem_range, Function.comp_apply]
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨p - 1 - q, by omega, ?_⟩
      have heq : p - (p - 1 - q + 1) = q := by omega
      simp [d, heq]
    · rintro ⟨r, hr, rfl⟩
      refine ⟨p - (r + 1), by omega, ?_⟩
      simp [d]
  have hAarith : ∀ r, r < p → r ≠ 0 → a r + r * g = T := by
    intro r hr hr0
    dsimp [a]
    rw [if_neg hr0, ← Nat.add_mul, Nat.sub_add_cancel (by omega), hpg]
  have hDarith : ∀ r, r < p → d r + (r + 1) * g = T + 1 := by
    intro r hr
    dsimp [d]
    have hs : p - (r + 1) + (r + 1) = p := by omega
    nlinarith [congrArg (fun n => n * g) hs]
  have hAstart : ∀ r, r < p → a r < T := by
    intro r hr
    by_cases hr0 : r = 0
    · simp [a, hr0, hT]
    · have ha := hAarith r hr hr0
      have hrg : 0 < r * g := Nat.mul_pos (by omega) hgpos
      omega
  have hDstart : ∀ r, r < p → d r < T := by
    intro r hr
    have hd := hDarith r hr
    have hrg : 2 ≤ (r + 1) * g := by nlinarith
    omega
  have hfirst : ∀ s h, 0 < s → s + h = k →
      c (s + h) = 1 ∧ ∀ i, i < h → c (s + i) = 0 := by
    intro s h hs heq
    constructor
    · rw [heq, hcycle, Nat.mod_eq_of_lt (by dsimp [T]; omega)]
      simp
    · intro i hi
      have hlt : s + i < T := by dsimp [T]; omega
      rw [hcycle, Nat.mod_eq_of_lt hlt]
      rw [if_neg (by omega : ¬ (s + i = 0 ∨ s + i = k))]
  have hAfirst : ∀ r, r < p →
      c (a r + e r) = 1 ∧ ∀ i, i < e r → c (a r + i) = 0 := by
    intro r hr
    by_cases hr0 : r = 0
    · subst r
      simp only [a, e, if_pos rfl, Nat.zero_add]
      constructor
      · rw [hcycle]; simp
      · intro i hi; omega
    · have ha := hAarith r hr hr0
      have hrg : 0 < r * g := Nat.mul_pos (by omega) hgpos
      have hpq : 0 < p - r := by omega
      have hap : 0 < a r := by
        dsimp [a]; rw [if_neg hr0]; exact Nat.mul_pos hpq hgpos
      apply hfirst (a r) (e r) hap
      dsimp [e]
      rw [if_neg hr0]
      dsimp [T] at ha
      omega
  have hDfirst : ∀ r, r < p →
      c (d r + f r) = 1 ∧ ∀ i, i < f r → c (d r + i) = 0 := by
    intro r hr
    have hd := hDarith r hr
    have hrg : 2 ≤ (r + 1) * g := by nlinarith
    apply hfirst (d r) (f r) (by dsimp [d]; omega)
    dsimp [f, T] at *
    omega
  have hEstr : ∀ r s, r < s → e r < e s := by
    intro r s hrs
    have hs0 : s ≠ 0 := by omega
    have hsm : 2 ≤ s * g := by nlinarith
    by_cases hr0 : r = 0
    · simp only [e, if_pos hr0, if_neg hs0]
      omega
    · have hrm : 1 ≤ r * g := Nat.mul_pos (by omega) hgpos
      have hmul := Nat.mul_lt_mul_of_pos_right hrs hgpos
      simp only [e, if_neg hr0, if_neg hs0]
      omega
  have hFstr : ∀ r s, r < s → f r < f s := by
    intro r s hrs
    have hrm : 2 ≤ (r + 1) * g := by nlinarith
    have hsm : 2 ≤ (s + 1) * g := by nlinarith
    have hmul := Nat.mul_lt_mul_of_pos_right (show r + 1 < s + 1 by omega) hgpos
    dsimp [f]
    omega
  have hAvis : ∀ j r, 1 ≤ j → (e r < j ↔ r < 1 + j / g) := by
    intro j r hj
    by_cases hr0 : r = 0
    · simp [e, hr0]; omega
    · have hrg : 1 ≤ r * g := Nat.mul_pos (by omega) hgpos
      simp only [e, if_neg hr0]
      rw [show (r * g - 1 < j) ↔ r * g ≤ j by omega,
        ← Nat.le_div_iff_mul_le hgpos]
      omega
  have hDvis : ∀ j r, (f r < j ↔ r < (j + 1) / g) := by
    intro j r
    have hrg : 2 ≤ (r + 1) * g := by nlinarith
    dsimp [f]
    rw [show ((r + 1) * g - 2 < j) ↔ (r + 1) * g ≤ j + 1 by omega,
      ← Nat.le_div_iff_mul_le hgpos]
    omega
  have hfiber : ∀ (j : ℕ) (S H : ℕ → ℕ),
      (∀ r s, r < s → H r < H s) →
      (∀ r, r < p → c (S r + H r) = 1 ∧ ∀ i, i < H r → c (S r + i) = 0) →
      ∀ r s, r < p → s < p →
        ((fun i : Fin j => c (S r + i.val)) = (fun i : Fin j => c (S s + i.val)) ↔
          r = s ∨ (j ≤ H r ∧ j ≤ H s)) := by
    intro j S H hstrict hhit r s hr hs
    have hsep : ∀ r s, r < p → s < p → r < s → H r < j →
        (fun i : Fin j => c (S r + i.val)) ≠ (fun i : Fin j => c (S s + i.val)) := by
      intro r s hr hs hrs hv heq
      have he := congrFun heq ⟨H r, hv⟩
      change c (S r + H r) = c (S s + H r) at he
      rw [(hhit r hr).1, (hhit s hs).2 (H r) (hstrict r s hrs)] at he
      exact one_ne_zero he
    constructor
    · intro heq
      by_cases he : r = s
      · exact Or.inl he
      · right
        rcases lt_or_gt_of_ne he with hrs | hsr
        · have hlim : j ≤ H r := by
            by_contra hn
            exact hsep r s hr hs hrs (by omega) heq
          have hlt := hstrict r s hrs
          exact ⟨hlim, by omega⟩
        · have hlim : j ≤ H s := by
            by_contra hn
            exact hsep s r hs hr hsr (by omega) heq.symm
          have hlt := hstrict s r hsr
          exact ⟨by omega, hlim⟩
    · rintro (he | ⟨hjr, hjs⟩)
      · subst s; rfl
      · funext i
        rw [(hhit r hr).2 i.val (by omega), (hhit s hs).2 i.val (by omega)]
  have hcount : ∀ (j v : ℕ) (F : ℕ → Fin j → ZMod 2),
      (∀ r s, r < p → s < p → r < s → r < v → F r ≠ F s) →
      (∀ r, r < p → v ≤ r → F r = fun _ => 0) →
      ((range p).image F).card = min p (v + 1) := by
    intro j v F hsep hzero
    let N := min p (v + 1)
    have hNp : N ≤ p := min_le_left _ _
    have hNv : N ≤ v + 1 := min_le_right _ _
    have himage : (range p).image F = (range N).image F := by
      ext w
      simp only [mem_image, mem_range]
      constructor
      · rintro ⟨r, hr, rfl⟩
        by_cases hrN : r < N
        · exact ⟨r, hrN, rfl⟩
        · have hvp : v < p := by dsimp [N] at hrN; omega
          have hvN : v < N := by dsimp [N]; omega
          refine ⟨v, hvN, ?_⟩
          rw [hzero v hvp le_rfl, hzero r hr (by dsimp [N] at hrN; omega)]
      · rintro ⟨r, hr, rfl⟩
        exact ⟨r, by omega, rfl⟩
    rw [himage, card_image_of_injOn, card_range]
    intro r hr s hs heq
    have hrN := mem_range.mp hr
    have hsN := mem_range.mp hs
    by_contra hne
    rcases lt_or_gt_of_ne hne with hrs | hsr
    · exact hsep r s (by omega) (by omega) hrs (by omega) heq
    · exact hsep s r (by omega) (by omega) hsr (by omega) heq.symm
  have hAwindow : ∀ j, P.image (W j) =
      (range p).image (fun r (i : Fin j) => c (a r + i.val)) := by
    intro j
    rw [hAphase, image_image]
    apply image_congr
    intro r hr
    funext i
    dsimp [W]
    rw [ZMod.val_natCast_of_lt (hAstart r (mem_range.mp hr))]
  have hDwindow : ∀ j, (P.image (fun θ => θ + 1)).image (W j) =
      (range p).image (fun r (i : Fin j) => c (d r + i.val)) := by
    intro j
    rw [hDphase, image_image]
    apply image_congr
    intro r hr
    funext i
    dsimp [W]
    rw [ZMod.val_natCast_of_lt (hDstart r (mem_range.mp hr))]
  have hzero : ∀ (S : ℕ → ℕ),
      ((range p).image (fun r (i : Fin 0) => c (S r + i.val))).card = 1 := by
    intro S
    have hf : (fun r (i : Fin 0) => c (S r + i.val)) =
        (fun _ => (fun i : Fin 0 => Fin.elim0 i : Fin 0 → ZMod 2)) := by
      funext r i
      exact Fin.elim0 i
    rw [hf, image_const]
    · simp
    · exact ⟨0, mem_range.mpr hppos⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hAwindow]; exact hzero a
  · rw [hDwindow]; exact hzero d
  · intro j hj
    constructor
    · rw [hAwindow]
      have hc := hcount j (1 + j / g) (fun r i => c (a r + i.val))
      have hs : ∀ r s, r < p → s < p → r < s → r < 1 + j / g →
          (fun i : Fin j => c (a r + i.val)) ≠ (fun i : Fin j => c (a s + i.val)) := by
        intro r s hr hs hrs hv heq
        have hhit := (hAvis j r hj).mpr hv
        have he := (hfiber j a e hEstr hAfirst r s hr hs).mp heq
        rcases he with he | he <;> omega
      have hz : ∀ r, r < p → 1 + j / g ≤ r →
          (fun i : Fin j => c (a r + i.val)) = fun _ => 0 := by
        intro r hr hv
        have hhit : j ≤ e r := by
          have := hAvis j r hj
          omega
        funext i
        exact (hAfirst r hr).2 i.val (by omega)
      convert hc hs hz using 1
      congr 1
      omega
    · rw [hDwindow]
      have hc := hcount j ((j + 1) / g) (fun r i => c (d r + i.val))
      have hs : ∀ r s, r < p → s < p → r < s → r < (j + 1) / g →
          (fun i : Fin j => c (d r + i.val)) ≠ (fun i : Fin j => c (d s + i.val)) := by
        intro r s hr hs hrs hv heq
        have hhit := (hDvis j r).mpr hv
        have he := (hfiber j d f hFstr hDfirst r s hr hs).mp heq
        rcases he with he | he <;> omega
      have hz : ∀ r, r < p → (j + 1) / g ≤ r →
          (fun i : Fin j => c (d r + i.val)) = fun _ => 0 := by
        intro r hr hv
        have hhit : j ≤ f r := by
          have := hDvis j r
          omega
        funext i
        exact (hDfirst r hr).2 i.val (by omega)
      simpa [Nat.add_comm] using hc hs hz

#print axioms kbonacci_resonant_window_counts

end D5.S1.Words.AdmissibleWords.KBonacciResonantWindowCounts
