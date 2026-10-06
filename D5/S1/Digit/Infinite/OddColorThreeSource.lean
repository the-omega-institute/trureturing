/- GID: D5/S1/Digit/Infinite/OddColorThreeSource
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/OddColorThreeSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Odd closed color words support at most two actual periodic addresses. -/

import D5.S1.Digit.Infinite.ClosedObservationGraphRealization
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Set.Card

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.OddColorThreeSource

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.SignedSeriesRange (signedValue signed_series_range v)
open D5.S1.Digit.Infinite.SignedSeriesFibres
open private prependBlock from D5.S1.Digit.Infinite.SignedSeriesFibres

private theorem shift_add (x : LegalDigits) (a b : ℕ) :
    bitShift (bitShift x a) b = bitShift x (a + b) := by
  apply Subtype.ext
  funext j
  simp only [bitShift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem periodic_shift (x : LegalDigits) (d n : ℕ)
    (hx : Function.Periodic x.val d) :
    Function.Periodic (bitShift x n).val d := by
  exact hx.add_const n

private theorem prepend_not_odd_periodic (w : List Block) (d : ℕ) (hd : Odd d) :
    ¬ Function.Periodic (prependWord w v).val d := by
  induction w with
  | nil =>
    intro h
    have h0 := h 0
    have hm : d % 2 = 1 := Nat.odd_iff.mp hd
    simp [prependWord, v, hm] at h0
  | cons c w ih =>
    intro h
    apply ih
    intro j
    cases c with
    | zero =>
      simpa [prependWord, prependBlock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using h (j + 1)
    | oneZero =>
      simpa [prependWord, prependBlock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using h (j + 2)

private theorem odd_periodic_scalar_injective (d : ℕ) (hd : Odd d)
    (x y : LegalDigits) (hx : Function.Periodic x.val d)
    (he : kappa x = kappa y) : x = y := by
  have hg := D5.S1.Digit.Infinite.ClosedObservationGraphRealization.closed_observation_graph_realization.1
  have hs : signedValue x = signedValue y := by
    have ht : 0 < t := inv_pos.mpr Real.goldenRatio_pos
    rw [hg x, hg y] at he
    exact neg_injective ((div_left_inj' (ne_of_gt (sq_pos_of_pos ht))).mp he)
  have hn : signedValue x ∉ Set.range seam := by
    rintro ⟨w, hw⟩
    rcases ((signed_series_fibres.1 w).2 x).mp hw.symm with h | h
    · subst x
      exact prepend_not_odd_periodic (w ++ [D5.S0.Automata.BinaryZeckendorfBlockSkeleton.ReturnBlock.zero]) d hd (by change Function.Periodic (prependWord (w ++ [D5.S0.Automata.BinaryZeckendorfBlockSkeleton.ReturnBlock.zero]) v).val d at hx; exact hx)
    · subst x
      exact prepend_not_odd_periodic (w ++ [D5.S0.Automata.BinaryZeckendorfBlockSkeleton.ReturnBlock.oneZero]) d hd (by change Function.Periodic (prependWord (w ++ [D5.S0.Automata.BinaryZeckendorfBlockSkeleton.ReturnBlock.oneZero]) v).val d at hx; exact hx)
  have hb : signedValue x ∈ Set.Icc
      D5.S1.Digit.Infinite.SignedSeriesRange.a D5.S1.Digit.Infinite.SignedSeriesRange.b := by
    rw [← signed_series_range.1]
    exact ⟨x, rfl⟩
  obtain ⟨z, hz, hu⟩ := signed_series_fibres.2.2 _ hb hn
  exact (hu x rfl).trans (hu y hs.symm).symm



private theorem golden_relations :
    0 < t ∧ t < 1 ∧ t ^ 2 = 1 - t ∧ g = 2 * t - 1 ∧ (1 : ℝ) / 2 < t := by
  have ht : 0 < t := inv_pos.mpr Real.goldenRatio_pos
  have ht1 : t < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have ht2 : t ^ 2 + t = 1 := by
    dsimp [t, D5.S1.Digit.Infinite.SignedSeriesRange.alpha]
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  refine ⟨ht, ht1, by linarith, ?_, ?_⟩
  · dsimp [g]
    nlinarith [mul_nonneg ht.le (sq_nonneg t),
      congrArg (fun z : ℝ => t * z) ht2]
  · nlinarith

private theorem root_bounds (x : LegalDigits) :
    kappa x ∈ Set.Icc
      (if (window x 0).val 1 then -1 else if (window x 0).val 0 then
        (if (window x 0).val 2 then 2 * t else t) else
        (if (window x 0).val 2 then g else t - 1))
      (if (window x 0).val 1 then t - 1 else if (window x 0).val 0 then
        (if (window x 0).val 2 then 1 + t else 2 * t) else
        (if (window x 0).val 2 then t else g)) := by
  obtain ⟨_, hrange, hrec, _, _, _, _, _, hroot⟩ :=
    D5.S1.Digit.Infinite.ClosedObservationGraphRealization.closed_observation_graph_realization
  rw [← hroot, (hrec x).1]
  refine ⟨kappa (originalT x), ?_, rfl⟩
  apply (hrange (outgoing (window x 0))).subset
  exact ⟨originalT x, (hrec x).2.1, rfl⟩

private theorem color_geometry (β : ℝ) (hb : β < lambda) (c : Fin 6) :
    ∃ lo hi : Label,
      offset lo < offset hi ∧
      min (1 + t) (cellUpper c + β) - max (-1) (cellLower c - β) <
        offset hi - offset lo ∧
      (∀ x : LegalDigits, kappa x ∈ observation β c →
        window x 0 = lo ∨ window x 0 = hi) ∧
      (∀ x y : LegalDigits, window x 0 = lo → window y 0 = hi → kappa x ≤ kappa y) := by
  obtain ⟨ht, ht1, ht2, hg, hhalf⟩ := golden_relations
  let low (c : Fin 6) : Label :=
    if c.val ≤ 1 then threeLabel else if c.val = 2 then nullLabel else
      if c.val = 3 then fiveLabel else twoLabel
  let high (c : Fin 6) : Label :=
    if c.val ≤ 1 then nullLabel else if c.val = 2 then fiveLabel else
      if c.val = 3 then twoLabel else twoFiveLabel
  have labels (l : Label) : l = nullLabel ∨ l = threeLabel ∨ l = fiveLabel ∨
      l = twoLabel ∨ l = twoFiveLabel := by
    have h0 := l.property 0 (by decide)
    have h1 := l.property 1 (by decide)
    have hext (p q : Label) : p = q ↔ ∀ i, p.val i = q.val i := by
      exact Subtype.ext_iff.trans funext_iff
    simp only [hext, Fin.forall_fin_succ,
      Fin.forall_fin_zero, nullLabel, threeLabel, fiveLabel, twoLabel, twoFiveLabel]
    cases ha : l.val 0 <;> cases hb : l.val 1 <;> cases hc : l.val 2 <;>
      simp_all
  classical
  refine ⟨low c, high c, ?_, ?_, ?_, ?_⟩
  · fin_cases c <;> dsimp [low, high, offset, nullLabel, threeLabel,
      fiveLabel, twoLabel, twoFiveLabel] <;>
      norm_num <;> (try simp only [abs_of_pos ht]) <;> nlinarith
  · fin_cases c
    all_goals dsimp [low, high, offset, nullLabel, threeLabel,
      fiveLabel, twoLabel, twoFiveLabel, cellUpper, cellLower, cuts] at *
    all_goals norm_num at *
    all_goals dsimp [lambda] at *
    all_goals simp only [ht2, hg] at *
    · have hL := le_max_left (-1 : ℝ) (-1 - β)
      have hR := min_le_right (1 + t) (-(1 - t) - (1 - t) / 10 + β)
      linarith
    all_goals
      first
      | exact lt_of_le_of_lt
          (sub_le_sub (min_le_right _ _) (le_max_right _ _)) (by linarith)
      | exact lt_of_le_of_lt
          (sub_le_sub (min_le_left _ _) (le_max_right _ _)) (by linarith)
  · intro x hx
    have hr := root_bounds x
    have hL := (le_max_right (-1 : ℝ) (cellLower c - β)).trans hx.1
    have hR := hx.2.trans (min_le_right (1 + t) (cellUpper c + β))
    rcases labels (window x 0) with h | h | h | h | h
    all_goals rw [h] at hr ⊢
    all_goals fin_cases c
    all_goals dsimp [low, high] at *
    all_goals norm_num at *
    all_goals try (first | exact Or.inl rfl | exact Or.inr rfl)
    all_goals
      exfalso
      dsimp [nullLabel, threeLabel, fiveLabel, twoLabel, twoFiveLabel,
        cellLower, cellUpper, cuts, lambda] at hr hL hR hb
      norm_num at hr hL hR hb
      simp only [ht2, hg] at hr hL hR hb
      linarith only [ht, ht1, hhalf, hr.1, hr.2, hL, hR, hb]
  · intro x y hx hy
    have hX := root_bounds x
    have hY := root_bounds y
    rw [hx] at hX
    rw [hy] at hY
    fin_cases c <;> dsimp [low, high, nullLabel, threeLabel, fiveLabel,
      twoLabel, twoFiveLabel] at hX hY
    all_goals norm_num at hX hY
    all_goals try simp only [ht2, hg] at hX hY
    all_goals linarith

/-- The parity of the three strict comparisons of an ordered triple. -/
private noncomputable def orderParity (x : Fin 3 → ℝ) : Bool :=
  (decide (x 0 < x 1) ^^ decide (x 1 < x 2)) ^^ decide (x 2 < x 0)

private theorem two_branch_parity (a b g L R : ℝ) (hg : 0 < g)
    (hgap : R - L < b - a) (x y : Fin 3 → ℝ) (p : Fin 3 → Bool)
    (hrec : ∀ i, x i = (if p i then b else a) - g * y i)
    (hbound : ∀ i, L ≤ x i ∧ x i ≤ R)
    (hneq : ∀ i j, i ≠ j → x i ≠ x j)
    (horder : ∀ i j, p i = false → p j = true → x i < x j) :
    orderParity x = !(orderParity y) := by
  classical
  have hsame (xi xj yi yj A : ℝ) (hi : xi = A - g * yi)
      (hj : xj = A - g * yj) (hne : xi ≠ xj) :
      decide (xi < xj) = !decide (yi < yj) := by
    by_cases hy : yi < yj
    · have hm := mul_pos hg (sub_pos.mpr hy)
      have hx : ¬ xi < xj := by nlinarith
      simp only [hy, hx, decide_true, decide_false, Bool.not_true]
    · have hyle : yj ≤ yi := le_of_not_gt hy
      have hyne : yj ≠ yi := by intro he; apply hne; rw [he] at hj; linarith
      have hm := mul_pos hg (sub_pos.mpr (lt_of_le_of_ne hyle hyne))
      have hx : xi < xj := by nlinarith
      simp only [hy, hx, decide_true, decide_false, Bool.not_false]
  have hcross (i j : Fin 3) (hpi : p i = false) (hpj : p j = true) :
      x i < x j ∧ y i < y j := by
    refine ⟨horder i j hpi hpj, ?_⟩
    have hi := hrec i
    have hj := hrec j
    simp only [hpi, hpj, Bool.false_eq_true, ↓reduceIte] at hi hj
    have hbi := hbound i
    have hbj := hbound j
    by_contra hn
    have hm := mul_nonneg hg.le (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith
  have hpairs (i j : Fin 3) (hij : i ≠ j) :
      decide (x i < x j) =
        if p i = p j then !decide (y i < y j) else decide (y i < y j) := by
    have hi := hrec i
    have hj := hrec j
    cases hpi : p i <;> cases hpj : p j
    · simp only [hpi, hpj, Bool.false_eq_true, ↓reduceIte] at hi hj ⊢
      exact hsame _ _ _ _ a hi hj (hneq i j hij)
    · have hh := hcross i j hpi hpj
      simp [hpi, hpj, hh.1, hh.2]
    · have hh := hcross j i hpj hpi
      simp [hpi, hpj, not_lt_of_gt hh.1, not_lt_of_gt hh.2]
    · simp only [hpi, hpj, ↓reduceIte] at hi hj ⊢
      exact hsame _ _ _ _ b hi hj (hneq i j hij)
  have h01 := hpairs 0 1 (by decide)
  have h12 := hpairs 1 2 (by decide)
  have h20 := hpairs 2 0 (by decide)
  unfold orderParity
  rw [h01, h12, h20]
  cases p 0 <;> cases p 1 <;> cases p 2 <;>
    cases decide (y 0 < y 1) <;> cases decide (y 1 < y 2) <;>
    cases decide (y 2 < y 0) <;> rfl


private theorem periodic_shift_injective (d : ℕ) (hd : 0 < d) (n : ℕ)
    (x y : LegalDigits) (hx : Function.Periodic x.val d)
    (hy : Function.Periodic y.val d) (he : bitShift x n = bitShift y n) : x = y := by
  have hlarge : n ≤ (n + 1) * d := by nlinarith
  have hret (z : LegalDigits) (hz : Function.Periodic z.val d) :
      bitShift z ((n + 1) * d) = z := by
    apply Subtype.ext
    funext j
    exact hz.nat_mul (n + 1) j
  have hh := congrArg (fun z => bitShift z ((n + 1) * d - n)) he
  rw [shift_add, shift_add, Nat.add_sub_of_le hlarge, hret x hx, hret y hy] at hh
  exact hh

private theorem actual_parity_step (β : ℝ) (hb : β < lambda) (c : Fin 6)
    (x : Fin 3 → LegalDigits)
    (hobs : ∀ i, kappa (x i) ∈ observation β c)
    (hne : ∀ i j, i ≠ j → kappa (x i) ≠ kappa (x j)) :
    orderParity (fun i => kappa (x i)) =
      !orderParity (fun i => kappa (originalT (x i))) := by
  classical
  obtain ⟨lo, hi, hoff, hgap, hallow, horder⟩ := color_geometry β hb c
  let p (i : Fin 3) : Bool := decide (window (x i) 0 = hi)
  have hlab (i : Fin 3) : window (x i) 0 = if p i then hi else lo := by
    rcases hallow (x i) (hobs i) with h | h
    · have hn : lo ≠ hi := by intro he; rw [he] at hoff; exact (lt_irrefl _ hoff)
      simp [p, h, hn]
    · simp [p, h]
  have hg : 0 < g := pow_pos golden_relations.1 3
  apply two_branch_parity (offset lo) (offset hi) g
    (max (-1) (cellLower c - β)) (min (1 + t) (cellUpper c + β)) hg hgap
    (fun i => kappa (x i)) (fun i => kappa (originalT (x i))) p
  · intro i
    have hr := D5.S1.Digit.Infinite.ClosedObservationGraphRealization.closed_observation_graph_realization.2.2.1 (x i)
    rw [hr.1]
    unfold branch
    rw [hlab]
    cases p i <;> rfl
  · exact hobs
  · exact hne
  · intro i j hi' hj'
    have hiL : window (x i) 0 = lo := by simpa only [hi', Bool.false_eq_true, ↓reduceIte] using hlab i
    have hjH : window (x j) 0 = hi := by simpa only [hj', ↓reduceIte] using hlab j
    apply lt_of_le_of_ne (horder (x i) (x j) hiL hjH)
    intro he
    have hij : i ≠ j := by
      intro hij
      subst j
      rw [hiL] at hjH
      rw [hjH] at hoff
      exact lt_irrefl _ hoff
    exact hne i j hij he

private theorem no_three_sources (β : ℝ) (hb : β < lambda) (m : ℕ)
    (hm : Odd m) (c : Fin m → Fin 6) (x : Fin 3 → LegalDigits)
    (hp : ∀ i, Function.Periodic (x i).val (3 * m))
    (ho : ∀ i j, kappa (bitShift (x i) (3 * j)) ∈
      observation β (c ⟨j % m, Nat.mod_lt j (by
        have hh : m % 2 = 1 := Nat.odd_iff.mp hm
        omega)⟩))
    (hi : Function.Injective x) : False := by
  classical
  have hmpos : 0 < m := by
    have hh : m % 2 = 1 := Nat.odd_iff.mp hm
    omega
  have hdodd : Odd (3 * m) := (by decide : Odd (3 : ℕ)).mul hm
  have hsep (j : ℕ) (a b : Fin 3) (hab : a ≠ b) :
      kappa (bitShift (x a) (3 * j)) ≠ kappa (bitShift (x b) (3 * j)) := by
    intro he
    have hs := odd_periodic_scalar_injective (3 * m) hdodd _ _
      (periodic_shift _ _ _ (hp a)) he
    exact hab (hi (periodic_shift_injective (3 * m) (by omega) (3 * j)
      _ _ (hp a) (hp b) hs))
  let S (j : ℕ) : Bool := orderParity (fun i => kappa (bitShift (x i) (3 * j)))
  have hstep (j : ℕ) : S (j + 1) = !(S j) := by
    have hh := actual_parity_step β hb (c ⟨j % m, Nat.mod_lt j hmpos⟩)
      (fun i => bitShift (x i) (3 * j)) (fun i => ho i j) (hsep j)
    have hs (i : Fin 3) : originalT (bitShift (x i) (3 * j)) =
        bitShift (x i) (3 * (j + 1)) := by
      rw [originalT, shift_add]
      congr 1 <;> omega
    simp_rw [hs] at hh
    have hn := congrArg Bool.not hh
    simpa only [Bool.not_not] using hn.symm
  have htwo : Function.Periodic S 2 := by
    intro j
    change S ((j + 1) + 1) = S j
    rw [hstep, hstep, Bool.not_not]
  have hreturn : S m = S 0 := by
    have hr (i : Fin 3) : bitShift (x i) (3 * m) = x i := by
      apply Subtype.ext
      funext j
      exact hp i j
    change orderParity (fun i => kappa (bitShift (x i) (3 * m))) =
      orderParity (fun i => kappa (bitShift (x i) (3 * 0)))
    apply congrArg orderParity
    funext i
    rw [hr i]
    rfl
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m = 2 * k + 1 := by
    rcases hm with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hodd : S m = !(S 0) := by
    have he := htwo.nat_mul k 1
    rw [hk]
    have he' : S (2 * k + 1) = S 1 := by
      convert he using 1 <;> omega
    exact he'.trans (hstep 0)
  exact Bool.not_ne_self _ (hodd.symm.trans hreturn)

/-- Every fixed odd closed color word admits at most two distinct actual periodic
addresses whose window period divides its length. -/
theorem result (β : ℝ) (hb : β < lambda) (m : ℕ) (hm : Odd m)
    (c : Fin m → Fin 6) :
    {x : LegalDigits | Function.Periodic x.val (3 * m) ∧
      ∀ j : ℕ, kappa (bitShift x (3 * j)) ∈ observation β
        (c ⟨j % m, Nat.mod_lt j (by
          have hh : m % 2 = 1 := Nat.odd_iff.mp hm
          omega)⟩)}.encard ≤ 2 := by
  classical
  let A : Set LegalDigits := {x | Function.Periodic x.val (3 * m) ∧
      ∀ j : ℕ, kappa (bitShift x (3 * j)) ∈ observation β
        (c ⟨j % m, Nat.mod_lt j (by
          have hh : m % 2 = 1 := Nat.odd_iff.mp hm
          omega)⟩)}
  change A.encard ≤ 2
  by_contra hn
  have h3 : (3 : ℕ∞) ≤ A.encard :=
    (ENat.add_one_le_iff (by simp : (2 : ℕ∞) ≠ ⊤)).mpr (lt_of_not_ge hn)
  obtain ⟨B, hBA, hB⟩ := Set.exists_subset_encard_eq h3
  obtain ⟨x, y, z, hxy, hxz, hyz, hset⟩ := Set.encard_eq_three.mp hB
  have hX : x ∈ A := hBA (by rw [hset]; simp)
  have hY : y ∈ A := hBA (by rw [hset]; simp)
  have hZ : z ∈ A := hBA (by rw [hset]; simp)
  let triple : Fin 3 → LegalDigits := ![x, y, z]
  apply no_three_sources β hb m hm c triple
  · intro i
    fin_cases i
    · exact hX.1
    · exact hY.1
    · exact hZ.1
  · intro i
    fin_cases i
    · exact hX.2
    · exact hY.2
    · exact hZ.2
  · intro i j he
    fin_cases i <;> fin_cases j <;> simp [triple] at he ⊢
    all_goals first | exact False.elim (hxy he) | exact False.elim (hxz he) |
      exact False.elim (hyz he) | exact False.elim (hxy he.symm) |
      exact False.elim (hxz he.symm) | exact False.elim (hyz he.symm)

end D5.S1.Digit.Infinite.OddColorThreeSource
