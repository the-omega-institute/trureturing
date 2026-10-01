/- GID: D5/S1/Words/Attractors/PeriodicPrefixAttractors
   generality: G
   mirror-B: D5/B/S1/Words/Attractors/PeriodicPrefixAttractors
   mirror-E: none(waiver:structural-word-proof)
   anchors: []
   utility: none
   digest: Endpoint attractors and residual windows for coherent periodic prefix families. -/

import D5.S1.Words.Attractors.FiniteWordAttractors
import D5.S1.Words.Powers.WordPower

namespace D5.S1.Words.Attractors

open D5.S1.Words.Powers

/-- Canonical endpoint induction from nested prefixes, periodic cuts and actual suffixes. -/
theorem nested_word_endpoint_attractors {α : Type*} (k : Nat) (hk : 2 ≤ k)
    (w : Nat → List α) (U : Nat → Nat)
    (hlen : ∀ m, (w m).length = m)
    (hprefix : ∀ m n, m ≤ n → w m = (w n).take m)
    (hU0 : U 0 = 1) (hU : StrictMono U)
    (hgaps : Monotone fun n => U (n + 1) - U n)
    (hperiod : ∀ n, List.HasPeriod (w (U (n + 1) - 1)) (U n))
    (hsuffix : ∀ n, k ≤ n → w (U (n - k)) <:+ w (U n)) :
    let B := fun n => U (n + 1) - 1
    let Δ := fun n => B n - U n
    let P := fun n => U n + if n < k then 0 else Δ (n - k)
    let Γ := fun n => (Finset.Icc (n + 1 - k) n).image fun j => U j - 1
    ∀ n, P n ≤ B n ∧ ∀ m, P n ≤ m → m ≤ B n → IsAttractor (w m) (Γ n) := by
  classical
  dsimp only
  let B := fun n => U (n + 1) - 1
  let Δ := fun n => B n - U n
  let P := fun n => U n + if n < k then 0 else Δ (n - k)
  let Γ := fun n => (Finset.Icc (n + 1 - k) n).image fun j => U j - 1
  have Upos (n : Nat) : 0 < U n := by have := hU.monotone (Nat.zero_le n); omega
  have Ustep (n : Nat) : U n < U (n + 1) := hU (by omega)
  have capbound (n : Nat) : P n ≤ B n := by
    have hstep := Ustep n
    dsimp [P, Δ, B]
    split_ifs with hnk
    · omega
    · have ht := Ustep (n - k)
      have hg := hgaps (Nat.sub_le n k)
      change U (n - k + 1) - U (n - k) ≤ U (n + 1) - U n at hg
      omega
  have lowerP (n : Nat) : U n ≤ P n := by dsimp [P]; omega
  have hwprefix {m n : Nat} (h : m ≤ n) : w m <+: w n := by
    rw [hprefix m n h]
    exact List.take_prefix _ _
  have per (n m : Nat) (hm : m ≤ B n) : List.HasPeriod (w m) (U n) :=
    (hperiod n).infix (hwprefix hm).isInfix
  have suffix_window (w : List α) (p q B : Nat)
      (hq : 0 < q) (hqB : q ≤ B) (hBp : B ≤ p) (hqw : p - q + B ≤ w.length)
      (hper : List.HasPeriod w p) (hcutper : List.HasPeriod (w.take B) q)
      (hsuffix : w.take q <:+ w.take p) :
      (w.drop (p - q)).take B = w.take B := by
    have hqp : q ≤ p := hqB.trans hBp
    have hpw : p ≤ w.length := by omega
    have hBw : B ≤ w.length := by omega
    have hsuffix' : w.take q = (w.take p).drop (p - q) := by
      have h := List.suffix_iff_eq_drop.mp hsuffix
      simpa only [List.length_take, Nat.min_eq_left hpw, Nat.min_eq_left (hqp.trans hpw)] using h
    apply List.ext_getElem?
    intro i
    by_cases hi : i < B
    · simp only [List.getElem?_take, if_pos hi, List.getElem?_drop]
      by_cases hiq : i < q
      · have h := congrArg (fun v : List α => v[i]?) hsuffix'
        simp only [List.getElem?_take_of_lt hiq, List.getElem?_drop,
          List.getElem?_take_of_lt (by omega : p - q + i < p)] at h
        exact h.symm
      · have hqi : q ≤ i := by omega
        have hshift : p - q + i = p + (i - q) := by omega
        rw [hshift, ← hper.getElem?_mod p (p + (i - q)) w (by omega), Nat.add_mod_left,
          Nat.mod_eq_of_lt (by omega : i - q < p)]
        have h := List.hasPeriod_iff_getElem?.mp hcutper (i - q)
          (by simp only [List.length_take, Nat.min_eq_left hBw]; omega)
        rw [List.getElem?_take_of_lt (by omega : i - q < B),
          List.getElem?_take_of_lt (by omega : i - q + q < B)] at h
        simpa only [Nat.sub_add_cancel hqi] using h
    · simp [hi]
  have pointmono : StrictMono fun j => U j - 1 := by
    intro a b hab
    change U a - 1 < U b - 1
    have := hU hab
    have := Upos a
    omega
  have emptyAttractor : IsAttractor ([] : List α) ∅ := by
    refine ⟨by simp, ?_⟩
    intro a l hl hal
    simp only [List.length_nil] at hal
    omega
  change ∀ n, P n ≤ B n ∧ ∀ m, P n ≤ m → m ≤ B n → IsAttractor (w m) (Γ n)
  intro n
  induction n with
  | zero =>
    refine ⟨capbound 0, ?_⟩
    intro m hmP hmB
    have hm : 1 ≤ m := by have := lowerP 0; omega
    have hG : Γ 0 = {0} := by
      simp [Γ, Nat.sub_eq_zero_of_le (by omega : 1 ≤ k), hU0]
    rw [hG]
    have hper : List.HasPeriod (w m) 1 := by simpa [hU0] using per 0 m hmB
    simpa using periodic_attractor_extension (w m) 1 ∅ (by omega)
      (by rw [hlen]; omega) hper (by simpa using emptyAttractor)
  | succ n ih =>
    refine ⟨capbound (n + 1), ?_⟩
    intro m hmP hmB
    have hp : U (n + 1) ≤ m := (lowerP (n + 1)).trans hmP
    have hpw : U (n + 1) ≤ (w m).length := by simpa [hlen] using hp
    have hBm : B n ≤ m := by dsimp [B]; omega
    have hold : IsAttractor ((w m).take (U (n + 1) - 1)) (Γ n) := by
      rw [← hprefix (B n) m hBm]
      exact ih.2 (B n) ih.1 le_rfl
    have hper := per (n + 1) m hmB
    by_cases hsmall : n + 1 < k
    · have hG : Γ (n + 1) = insert (U (n + 1) - 1) (Γ n) := by
        have hn0 : n + 1 - k = 0 := by omega
        have hn1 : n + 1 + 1 - k = 0 := by omega
        have hsplit : insert (n + 1) (Finset.Icc 0 n) = Finset.Icc 0 (n + 1) := by
          simpa using (Finset.insert_Icc_right_eq_Icc_succ (a := 0) (b := n) (by omega))
        dsimp [Γ]
        rw [hn0, hn1, ← hsplit, Finset.image_insert]
      rw [hG]
      exact periodic_attractor_extension _ _ _ (Upos _) hpw hper hold
    · let t := n + 1 - k
      have hkn : k ≤ n + 1 := by omega
      have ht : t ≤ n := by dsimp [t]; omega
      have hts : t + 1 ≤ n := by dsimp [t]; omega
      have hqB : U t ≤ B t := by have := Ustep t; dsimp [B]; omega
      have hBN : B t ≤ U (n + 1) - 1 := by
        have := hU.monotone (by omega : t + 1 ≤ n + 1)
        dsimp [B]; omega
      have hwindowbound : U (n + 1) - U t + B t ≤ (w m).length := by
        have htU := hU.monotone (by omega : t ≤ n + 1)
        have hmP' : U (n + 1) + Δ t ≤ m := by
          simpa only [P, if_neg hsmall, t] using hmP
        rw [hlen]
        dsimp [Δ] at hmP'
        omega
      have hs : (w m).take (U t) <:+ (w m).take (U (n + 1)) := by
        have htU := hU.monotone (by omega : t ≤ n + 1)
        rw [← hprefix (U t) m (by omega), ← hprefix (U (n + 1)) m hp]
        exact hsuffix (n + 1) hkn
      have hcutper : List.HasPeriod ((w m).take (B t)) (U t) := by
        rw [← hprefix (B t) m (by omega)]
        exact hperiod t
      have hwindow := suffix_window (w m) (U (n + 1)) (U t) (B t)
        (Upos t) hqB (by omega) hwindowbound hper hcutper hs
      have hqS : U t - 1 ∈ Γ n := by
        apply Finset.mem_image.mpr
        exact ⟨t, Finset.mem_Icc.mpr ⟨le_rfl, ht⟩, rfl⟩
      have hcut : B t ∈ (Γ n).erase (U t - 1) := by
        apply Finset.mem_erase.mpr
        refine ⟨?_, ?_⟩
        · have := Ustep t
          have := Upos t
          dsimp [B]; omega
        · exact Finset.mem_image.mpr ⟨t + 1,
            Finset.mem_Icc.mpr ⟨by dsimp [t]; omega, hts⟩, rfl⟩
      have hG : Γ (n + 1) = insert (U (n + 1) - 1) ((Γ n).erase (U t - 1)) := by
        have hstart : n + 1 + 1 - k = t + 1 := by dsimp [t]; omega
        have herase : Finset.Ioc t n = Finset.Icc (t + 1) n := by
          simpa using (Finset.Icc_succ_left_eq_Ioc t n).symm
        have hsplit : insert (n + 1) (Finset.Icc (t + 1) n) =
            Finset.Icc (t + 1) (n + 1) := by
          simpa using (Finset.insert_Icc_right_eq_Icc_succ (a := t + 1) (b := n)
            (by change t + 1 ≤ n + 1; omega))
        dsimp [Γ]
        change (Finset.Icc (n + 1 + 1 - k) (n + 1)).image (fun j => U j - 1) =
          insert (U (n + 1) - 1) (((Finset.Icc t n).image (fun j => U j - 1)).erase (U t - 1))
        rw [hstart, ← Finset.image_erase pointmono.injective, Finset.Icc_erase_left,
          herase, ← hsplit,
          Finset.image_insert]
      rw [hG]
      exact (attractor_window_transfer (w m) (U (n + 1)) (U t) (U (n + 1)) (B t)
        (Γ n) (Upos _) hpw (Upos _) (hU.monotone (by omega)) le_rfl hqB hBN
        hwindow hwindowbound hold hqS (Or.inr hcut) (Or.inl ⟨rfl, hper⟩)).1

/-- A finite descending stack of literal coefficient blocks. -/
def descendingBlocks {α : Type*} (w : Nat → List α) (U b : Nat → Nat) :
    Nat → Nat → List α
  | 0, _ => []
  | count + 1, t => descendingBlocks w U b count (t + 1) ++ wordPower (b t) (w (U t))

/-- The additive residual scan finds an actual bounded replacement window.
    Zero blocks are skipped without subtracting from their multiplicity. -/
theorem periodic_residual_scan {α : Type*} (w : Nat → List α) (U b : Nat → Nat)
    (hlen : ∀ m, (w m).length = m)
    (hprefix : ∀ m n, m ≤ n → w m = (w n).take m)
    (hU : StrictMono U) (hpos : ∀ n, 0 < U n)
    (hperiod : ∀ n, List.HasPeriod (w (U (n + 1) - 1)) (U n))
    (count t N r : Nat) (X W : List α)
    (hcount : 0 < count)
    (hX : X <+: w (U (t + 1) - 1))
    (hR : X.length < U (t + 1) - 1) (hr : r ≤ X.length)
    (hstack : W = descendingBlocks w U b count t ++ X)
    (hsize : W.length = N + r)
    (htop : U (t + count) - 1 < W.length) :
    ∃ h p, t ≤ h ∧ h < t + count ∧ U h ≤ p ∧ p ≤ N ∧
      p - U h + (U (h + 1) - 1) ≤ W.length ∧
      (W.drop (p - U h)).take (U (h + 1) - 1) = w (U (h + 1) - 1) ∧
      W.drop p <+: w (U (h + 1) - 1) := by
  let B := fun h => U (h + 1) - 1
  have cap (h : Nat) : U h ≤ B h := by
    have := hU (by omega : h < h + 1)
    dsimp only [B]; omega
  have wpref {a d : Nat} (had : a ≤ d) : w a <+: w d := by
    rw [hprefix a d had]; exact List.take_prefix _ _
  have read (h j : Nat) (Y : List α) (hY : Y <+: w (B h)) (i : Nat)
      (hi : i < (wordPower j (w (U h)) ++ Y).length) :
      (wordPower j (w (U h)) ++ Y)[i]? = (w (B h))[i % U h]? := by
    have hu := cap h
    have hw := hprefix (U h) (B h) hu
    have hy := List.prefix_iff_eq_take.mp hY
    have hn := hlen (U h)
    have hp := length_wordPower j (w (U h))
    rw [hn] at hp
    by_cases hil : i < j * U h
    · rw [List.getElem?_append_left (by rw [length_wordPower, hlen]; exact hil),
        wordPower_getElem? j _ i (by rw [hlen]; exact hil), hn,
        hw, List.getElem?_take_of_lt (Nat.mod_lt _ (hpos h))]
    · have hli : j * U h ≤ i := by omega
      rw [List.getElem?_append_right (by omega), hp]
      have hiY : i - j * U h < Y.length := by
        simp only [List.length_append, hp] at hi; omega
      rw [hy, List.getElem?_take_of_lt hiY,
        ← (hperiod h).getElem?_mod (U h) (i - j * U h) (w (B h))
          (hiY.trans_le hY.length_le)]
      congr 1
      simpa only [Nat.mul_comm] using (Nat.sub_mul_mod (by simpa only [Nat.mul_comm] using hli))
  have prepend (h j : Nat) (Y : List α) (hY : Y <+: w (B h))
      (hbound : (wordPower j (w (U h)) ++ Y).length ≤ B h) :
      wordPower j (w (U h)) ++ Y <+: w (B h) := by
    apply List.prefix_iff_getElem?.mpr
    intro i hi
    have hiB : i < (w (B h)).length := by rw [hlen]; omega
    have he := read h j Y hY i hi
    rw [(hperiod h).getElem?_mod (U h) i (w (B h)) hiB] at he
    exact he.symm.trans (List.getElem?_eq_getElem hi)
  induction count generalizing t X with
  | zero => omega
  | succ count ih =>
    change X.length < B t at hR
    change X <+: w (B t) at hX
    have hUpos := hpos t
    have hcap := cap t
    by_cases hstop : B t ≤ b t * U t + X.length
    · have hb : 0 < b t := by
        by_contra hb; have hz : b t = 0 := by omega
        simp only [hz, Nat.zero_mul, Nat.zero_add] at hstop
        exact (not_le_of_gt hR) hstop
      let s := min (b t - 1) ((B t - X.length) / U t)
      let L := s * U t + X.length
      have hs : s ≤ b t - 1 := Nat.min_le_left _ _
      have hsdiv : s ≤ (B t - X.length) / U t := Nat.min_le_right _ _
      have hLB : L ≤ B t := by
        have hm := (Nat.mul_le_mul_right (U t) hsdiv).trans
          (Nat.div_mul_le_self (B t - X.length) (U t))
        dsimp only [L]; omega
      have hΔL : B t - U t ≤ L := by
        by_cases hh : b t - 1 ≤ (B t - X.length) / U t
        · have hs' : s = b t - 1 := Nat.min_eq_left hh
          have hb' : b t = (b t - 1) + 1 := by omega
          rw [hb', Nat.add_mul] at hstop
          dsimp only [L]; rw [hs']; omega
        · have hs' : s = (B t - X.length) / U t := Nat.min_eq_right (by omega)
          have hd := Nat.lt_div_mul_add (a := B t - X.length) hUpos
          dsimp only [L]; rw [hs']; omega
      let Y := wordPower (s + 1) (w (U t)) ++ X
      have hYlen : Y.length = U t + L := by
        simp only [Y, List.length_append, length_wordPower, hlen, Nat.add_mul]
        dsimp only [L]; omega
      have hYsuffix : Y <:+ W := by
        rw [hstack, descendingBlocks, List.append_assoc]
        apply List.suffix_append_of_suffix
        apply List.suffix_append_self_iff.mpr
        apply List.IsSuffix.flatten
        apply List.suffix_replicate_iff.mpr
        simp only [List.length_replicate]
        exact ⟨by omega, by simp⟩
      have hYbound := hYsuffix.length_le
      let p := W.length - L
      have hpU : U t ≤ p := by dsimp [p]; omega
      have hpN : p ≤ N := by dsimp [p, L]; omega
      have hshift : W.length - Y.length = p - U t := by dsimp [p]; omega
      have hYeq : W.drop (p - U t) = Y := by
        rw [← hshift]; exact (List.suffix_iff_eq_drop.mp hYsuffix).symm
      have hYB : B t ≤ Y.length := by omega
      have hwin : Y.take (B t) = w (B t) := by
        apply List.ext_getElem?
        intro i
        by_cases hi : i < B t
        · rw [List.getElem?_take_of_lt hi, read t (s + 1) X hX i (by change i < Y.length; omega),
            (hperiod t).getElem?_mod (U t) i (w (B t)) (by rw [hlen]; exact hi)]
        · simp [hi, hlen]
      have hdrop : W.drop p = wordPower s (w (U t)) ++ X := by
        have hp : p = p - U t + U t := by omega
        conv_lhs => rw [hp]
        rw [← List.drop_drop, hYeq]
        simp only [Y, wordPower_succ, List.append_assoc]
        exact List.drop_left' (hlen (U t))
      refine ⟨t, p, le_rfl, by omega, hpU, hpN, ?_, ?_, ?_⟩
      · change p - U t + B t ≤ W.length
        omega
      · rw [hYeq]; exact hwin
      · rw [hdrop]
        exact prepend t s X hX (by
          simpa only [List.length_append, length_wordPower, hlen] using hLB)
    · let X' := wordPower (b t) (w (U t)) ++ X
      have hX'len : X'.length = b t * U t + X.length := by
        simp [X', length_wordPower, hlen]
      have hX'B : X'.length < B t := by rw [hX'len]; omega
      have hBnext : B t < B (t + 1) := by
        have hstep : U (t + 1) < U (t + 1 + 1) := hU (by omega)
        have := hpos (t + 1)
        dsimp only [B]; omega
      have hX' : X' <+: w (B (t + 1)) :=
        (prepend t (b t) X hX (by change X'.length ≤ B t; omega)).trans (wpref hBnext.le)
      have hX'R : X'.length < B (t + 1) := hX'B.trans hBnext
      have hr' : r ≤ X'.length := by omega
      have hstack' : W = descendingBlocks w U b count (t + 1) ++ X' := by
        rw [hstack, descendingBlocks, List.append_assoc]
      have hcount' : 0 < count := by
        by_contra hz
        have hz' : count = 0 := by omega
        rw [hz', descendingBlocks, List.nil_append] at hstack'
        have := congrArg List.length hstack'
        subst count
        change B t < W.length at htop
        omega
      obtain ⟨h, p, ht, hh, hpU, hpN, hb, hw, hs⟩ := ih (t + 1) X' hcount'
        hX' hX'R hr' hstack' (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htop)
      exact ⟨h, p, by omega, by omega, hpU, hpN, hb, hw, hs⟩

end D5.S1.Words.Attractors
