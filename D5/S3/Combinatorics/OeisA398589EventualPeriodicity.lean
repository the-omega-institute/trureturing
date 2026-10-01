/- GID: D5/S3/Combinatorics/OeisA398589EventualPeriodicity
   generality: I
   mirror-B: D5/B/S3/Combinatorics/OeisA398589EventualPeriodicity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The original A398589 self-banning rows are eventually periodic. -/

import D5.S3.ObserverMemory.Prediction.FiniteInputGeneratorPeriodicity

open D5.S3.ObserverMemory.Prediction.FiniteInputGeneratorPeriodicity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.OeisA398589EventualPeriodicity

noncomputable section

def legal (k t x : ℕ) (h : ℕ → ℕ) : Prop :=
  k ≤ x ∧ ∀ s, s < t → h s = x → s + x < t

noncomputable def rowStep (k t : ℕ) (rec : (m : ℕ) → m < t → ℕ) : ℕ := by
  classical
  exact
    if ht : t = 0 then k
    else Nat.find (show ∃ x, legal k t x
      (fun s => if hs : s < t then rec s hs else 0) from by
        classical
        let candidates : Finset ℕ := (Finset.range (t + 1)).image (fun i => k + i)
        let h : ℕ → ℕ := fun s => if hs : s < t then rec s hs else 0
        let used : Finset ℕ := (Finset.range t).image h
        have hc : candidates.card = t + 1 := by
          dsimp [candidates]
          rw [Finset.card_image_iff.mpr]
          · simp
          · intro i hi j hj hij
            exact Nat.add_left_cancel hij
        have hu : used.card ≤ t := Finset.card_image_le.trans (by simp)
        obtain ⟨x, hx, hxu⟩ := Finset.exists_mem_notMem_of_card_lt_card
          (by omega : used.card < candidates.card)
        refine ⟨x, ?_, ?_⟩
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
          omega
        · intro s hs hsx
          exfalso
          apply hxu
          exact Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr hs, hsx⟩)

noncomputable def row (k t : ℕ) : ℕ :=
  Nat.strongRec (motive := fun _ => ℕ) (rowStep k) t

/-- Every initialized, untruncated self-banning row is eventually periodic. -/
theorem eventual_periodicity (k : ℕ) :
    ∃ N p : ℕ, 0 < p ∧ ∀ t : ℕ, N ≤ t → row k (t + p) = row k t := by
  classical
  have row_zero : row k 0 = k := by
    unfold row
    rw [Nat.strongRec_eq]
    simp [rowStep]
  have row_law (t : ℕ) : legal k t (row k t) (row k) ∧
      ∀ x, legal k t x (row k) → row k t ≤ x := by
    by_cases ht : t = 0
    · subst t
      constructor
      · simp [legal, row_zero]
      · intro x hx
        simpa [row_zero] using hx.1
    · have hstep : row k t = rowStep k t (fun m _ => row k m) := by
        unfold row
        rw [Nat.strongRec_eq]
      rw [hstep]
      unfold rowStep
      rw [dif_neg ht]
      generalize_proofs h
      have heq (x : ℕ) :
          legal k t x (fun s => if hs : s < t then row k s else 0) ↔
          legal k t x (row k) := by
        constructor
        · intro hx
          refine ⟨hx.1, ?_⟩
          intro s hs hsx
          exact hx.2 s hs (by simpa [hs] using hsx)
        · intro hx
          refine ⟨hx.1, ?_⟩
          intro s hs hsx
          exact hx.2 s hs (by simpa [hs] using hsx)
      exact ⟨(heq _).mp (Nat.find_spec h), fun x hx =>
        Nat.find_min' h ((heq x).mpr hx)⟩
  have row_legal (t : ℕ) := (row_law t).1
  have row_min (t x : ℕ) := (row_law t).2 x
  by_cases hk : k = 0
  · have hzero (t : ℕ) : row k t = 0 := by
      have hmin := row_min t 0 (by
        refine ⟨by omega, ?_⟩
        intro s hs _
        omega)
      omega
    exact ⟨0, 1, by omega, fun t _ => (hzero (t + 1)).trans (hzero t).symm⟩
  have hk : 0 < k := by omega
  have row_minimum_clock (t : ℕ) : row k t = k ↔ (k + 1) ∣ t := by
    let p := k + 1
    have hp : 0 < p := by dsimp [p]; omega
    have hclock : ∀ n : ℕ, row k n = k ↔ p ∣ n := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        have hrow_legal : legal k n (row k n) (row k) := row_legal n
        have hrow_eq_legal : row k n = k ↔ legal k n k (row k) := by
          constructor
          · intro h
            simpa [h] using hrow_legal
          · intro h
            exact Nat.le_antisymm (row_min n k h) (by exact (row_legal n).1)
        constructor
        · intro hrow
          have hlegal := hrow_eq_legal.mp hrow
          by_cases hr : n % p = 0
          · exact Nat.dvd_of_mod_eq_zero hr
          · let q := n / p
            let s := p * q
            have hrem : n % p < p := Nat.mod_lt n hp
            have hsdiv : p ∣ s := by exact ⟨q, by simp [s]
            ⟩
            have hsn : s < n := by
              have hdiv := Nat.div_add_mod n p
              have hn : n = s + n % p := by
                dsimp [s, q]
                omega
              have hpos : 0 < n % p := by omega
              omega
            have hsk : row k s = k := (ih s hsn).mpr hsdiv
            have hbad := hlegal.2 s hsn hsk
            have hdiv := Nat.div_add_mod n p
            dsimp [s, q] at hbad ⊢
            omega
        · intro hdiv
          apply hrow_eq_legal.mpr
          refine And.intro (by omega) ?_
          intro s hs hsk
          have hsdiv : p ∣ s := (ih s hs).mp hsk
          obtain ⟨q, rfl⟩ := hsdiv
          obtain ⟨r, hn⟩ := hdiv
          have hqr : q < r := by
            apply (Nat.mul_lt_mul_left hp).mp
            simpa [hn] using hs
          have hqp : q + 1 ≤ r := Nat.succ_le_of_lt hqr
          have hmul : p * (q + 1) ≤ p * r := Nat.mul_le_mul_left p hqp
          have hkp : k < p := by dsimp [p]; omega
          have hsmall : p * q + k < p * q + p := Nat.add_lt_add_left hkp (p * q)
          have hstep : p * q + p ≤ p * r := by simpa [Nat.mul_add] using hmul
          have : p * q + k < p * r := lt_of_lt_of_le hsmall hstep
          simpa [hn] using this
    simpa [p] using hclock t
  have row_bound (t : ℕ) : row k t ≤ k * (k + 2) := by
    classical
    let p := k + 1
    let B := k * (k + 2)
    let L := B - k + 1
    let M := B - k
    have hp : 0 < p := by dsimp [p]; omega
    have hB : k ≤ B := by
      dsimp [B]
      calc
        k = k * 1 := by simp
        _ ≤ k * (k + 2) := Nat.mul_le_mul_left k (by omega)
    by_contra hrow
    have hrow' : B < row k t := Nat.lt_of_not_ge hrow
    have hbad : ∀ x, k ≤ x → x ≤ B →
        ∃ s, s < t ∧ row k s = x ∧ t ≤ s + x := by
      intro x hxk hxb
      have hnlegal : ¬ legal k t x (row k) := by
        intro hlegal
        have hmin := row_min t x hlegal
        omega
      have hforall : ¬ ∀ s, s < t → row k s = x → s + x < t := by
        intro h
        exact hnlegal ⟨hxk, h⟩
      push Not at hforall
      obtain ⟨s, hs, hsx, hst⟩ := hforall
      exact ⟨s, hs, hsx, by omega⟩
    have hLform : L = k * p + 1 := by
      have hBexp : B = k * p + k := by
        dsimp [B, p]
        rw [show k + 2 = (k + 1) + 1 by omega, Nat.mul_add]
        simp
      have hBsub : B - k = k * p := by
        rw [hBexp]
        simp [Nat.add_comm]
      dsimp [L]
      rw [hBsub]
    have hMform : M + k + 1 = B + 1 := by
      dsimp [M]
      omega
    let wAll : ℕ → ℕ := fun i =>
      if hi : i < L then
        Classical.choose (hbad (k + i) (by omega) (by
          have hi' : i ≤ B - k := by dsimp [L] at hi; omega
          have hi'' : i + k ≤ B := (Nat.le_sub_iff_add_le hB).mp hi'
          omega))
      else 0
    have hwAll : ∀ i, i < L →
        wAll i < t ∧ row k (wAll i) = k + i ∧ t ≤ wAll i + (k + i) := by
      intro i hi
      dsimp [wAll]
      rw [dif_pos hi]
      have hi' : i ≤ B - k := by dsimp [L] at hi; omega
      have hi'' : i + k ≤ B := (Nat.le_sub_iff_add_le hB).mp hi'
      exact Classical.choose_spec (hbad (k + i) (by omega) (by omega))
    let allTimes : Finset ℕ := Finset.image wAll (Finset.range L)
    have hAllCard : allTimes.card = L := by
      have hinj : Set.InjOn wAll (↑(Finset.range L) : Set ℕ) := by
        intro i hi j hj hij
        have hi' := Finset.mem_range.mp hi
        have hj' := Finset.mem_range.mp hj
        have hwi := hwAll i hi'
        have hwj := hwAll j hj'
        have heq := congrArg (row k) hij
        rw [hwi.2.1, hwj.2.1] at heq
        omega
      simpa [allTimes] using (Finset.card_image_iff.mpr hinj)
    let W : Finset ℕ := (Finset.range t).filter (fun s => t ≤ s + B)
    have hallW : allTimes ⊆ W := by
      intro s hs
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
      have hi' := Finset.mem_range.mp hi
      have hwi := hwAll i hi'
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr hwi.1
      · have hi' : i ≤ B - k := by dsimp [L] at hi; omega
        have hi'' : i + k ≤ B := (Nat.le_sub_iff_add_le hB).mp hi'
        exact le_trans hwi.2.2 (Nat.add_le_add_left (by omega : k + i ≤ B) _)
    have hL_le_W : L ≤ W.card := by
      rw [← hAllCard]
      exact Finset.card_le_card hallW
    let f : ℕ → ℕ := fun s => t - 1 - s
    let fW : Finset ℕ := Finset.image f W
    have hfW_sub : fW ⊆ Finset.range B := by
      intro z hz
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
      have hs' := Finset.mem_filter.mp hs
      have hslt : s < t := Finset.mem_range.mp hs'.1
      apply Finset.mem_range.mpr
      have hsle : s ≤ t - 1 := Nat.le_sub_of_add_le (by omega)
      apply (Nat.sub_lt_iff_lt_add' hsle).2
      exact lt_of_lt_of_le (Nat.sub_lt (by omega) (by omega)) hs'.2
    have hf_inj : Set.InjOn f (↑W : Set ℕ) := by
      intro a ha b hb hab
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      have halt : a < t := Finset.mem_range.mp ha'.1
      have hblt : b < t := Finset.mem_range.mp hb'.1
      have hae : a ≤ t - 1 := Nat.le_sub_of_add_le (by omega)
      have hbe : b ≤ t - 1 := Nat.le_sub_of_add_le (by omega)
      have hca : t - 1 = (t - 1 - a) + a := (Nat.sub_add_cancel hae).symm
      have hcb : t - 1 = (t - 1 - b) + b := (Nat.sub_add_cancel hbe).symm
      dsimp [f] at hab
      have heq : (t - 1 - a) + a = (t - 1 - b) + b := hca.symm.trans hcb
      rw [hab] at heq
      exact Nat.add_left_cancel heq
    have hWcard : W.card ≤ B := by
      have himg : fW.card = W.card := by
        change (Finset.image f W).card = W.card
        exact Finset.card_image_iff.mpr hf_inj
      rw [← himg]
      simpa using (Finset.card_le_card hfW_sub)
    have hL_le_t : L ≤ t := by
      calc
        L ≤ W.card := hL_le_W
        _ ≤ t := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range t)
    have hAll : row k t = k ↔ p ∣ t := row_minimum_clock t
    have hnotdiv : ¬ p ∣ t := by
      intro hdiv
      have hkrow : row k t = k := hAll.mpr hdiv
      omega
    have hr : t % p ≠ 0 := by
      intro hr0
      exact hnotdiv (Nat.dvd_of_mod_eq_zero hr0)
    have hrem : t % p < p := Nat.mod_lt t hp
    have hdivform := Nat.div_add_mod t p
    have hq : k ≤ t / p := by
      by_contra hq'
      have hqle : t / p + 1 ≤ k := by omega
      have hlt : t < p * ((t / p) + 1) := by
        calc
          t = p * (t / p) + t % p := hdivform.symm
          _ < p * (t / p) + p := Nat.add_lt_add_left hrem _
          _ = p * ((t / p) + 1) := by rw [Nat.mul_add]; simp
      have hmul : p * ((t / p) + 1) ≤ p * k := Nat.mul_le_mul_left p hqle
      have hL' : k * p + 1 ≤ t := by simpa [hLform] using hL_le_t
      have hltK : t < k * p := lt_of_lt_of_le hlt (by simpa [Nat.mul_comm] using hmul)
      omega
    let wHigh : ℕ → ℕ := fun i =>
      if hi : i < M then
        Classical.choose (hbad (k + 1 + i) (by omega) (by
          have hi' : i ≤ B - k := by dsimp [M] at hi; omega
          have hi'' : i + k ≤ B := (Nat.le_sub_iff_add_le hB).mp hi'
          omega))
      else 0
    have hwHigh : ∀ i, i < M →
        wHigh i < t ∧ row k (wHigh i) = k + 1 + i ∧ t ≤ wHigh i + (k + 1 + i) := by
      intro i hi
      dsimp [wHigh]
      rw [dif_pos hi]
      have hi' : i ≤ B - k := by dsimp [M] at hi; omega
      have hi'' : i + k ≤ B := (Nat.le_sub_iff_add_le hB).mp hi'
      exact Classical.choose_spec (hbad (k + 1 + i) (by omega) (by omega))
    let highTimes : Finset ℕ := Finset.image wHigh (Finset.range M)
    have hHighCard : highTimes.card = M := by
      have hinj : Set.InjOn wHigh (↑(Finset.range M) : Set ℕ) := by
        intro i hi j hj hij
        have hi' := Finset.mem_range.mp hi
        have hj' := Finset.mem_range.mp hj
        have hwi := hwHigh i hi'
        have hwj := hwHigh j hj'
        have heq := congrArg (row k) hij
        rw [hwi.2.1, hwj.2.1] at heq
        omega
      simpa [highTimes] using (Finset.card_image_iff.mpr hinj)
    have hhighW : highTimes ⊆ W := by
      intro s hs
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
      have hi' := Finset.mem_range.mp hi
      have hwi := hwHigh i hi'
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr hwi.1
      · exact le_trans hwi.2.2 (Nat.add_le_add_left (by
          have hi' : i ≤ B - k := by dsimp [M] at hi; omega
          have hi'' : i + k ≤ B := (Nat.le_sub_iff_add_le hB).mp hi'
          omega) _)
    let q := t / p
    let u : ℕ → ℕ := fun j => (q - j) * p
    let clockTimes : Finset ℕ := Finset.image u (Finset.range (k + 1))
    have hu_props : ∀ j, j < k + 1 →
        u j < t ∧ row k (u j) = k ∧ t ≤ u j + B := by
      intro j hj
      have hjk : j ≤ k := by omega
      have hju : j ≤ q := le_trans hjk hq
      have hrowclock : row k (u j) = k := by
        apply (row_minimum_clock (u j)).mpr
        refine ⟨q - j, ?_⟩
        dsimp [u, p]
        simp [Nat.mul_comm]
      have hqt : q * p < t := by
        have hposr : 0 < t % p := by omega
        calc
          q * p < q * p + t % p := Nat.lt_add_of_pos_right hposr
          _ = t := by simpa [q, Nat.mul_comm] using hdivform
      have hu_le : u j ≤ q * p := by
        dsimp [u]
        exact Nat.mul_le_mul_right p (Nat.sub_le _ _)
      have hu_lt : u j < t := lt_of_le_of_lt hu_le hqt
      have hsplit : q * p = (q - j) * p + j * p := by
        calc
          q * p = (q - j + j) * p := by rw [Nat.sub_add_cancel hju]
          _ = (q - j) * p + j * p := by rw [Nat.add_mul]
      have hjp : j * p ≤ k * p := Nat.mul_le_mul_right p hjk
      have hrk : t % p ≤ k := by
        dsimp [p] at hrem ⊢
        omega
      have hwindow : t ≤ u j + B := by
        have htdecomp : t = u j + j * p + t % p := by
          calc
            t = p * q + t % p := by simpa [q] using hdivform.symm
            _ = q * p + t % p := by rw [Nat.mul_comm]
            _ = ((q - j) * p + j * p) + t % p := by rw [hsplit]
            _ = u j + j * p + t % p := by rfl
        have hsmall : j * p + t % p ≤ B := by
          have hBexp : B = k * p + k := by
            dsimp [B, p]
            rw [show k + 2 = (k + 1) + 1 by omega, Nat.mul_add]
            simp
          rw [hBexp]
          exact Nat.add_le_add hjp hrk
        calc
          t = u j + (j * p + t % p) := by simpa [Nat.add_assoc] using htdecomp
          _ ≤ u j + B := Nat.add_le_add_left hsmall _
      exact ⟨hu_lt, hrowclock, hwindow⟩
    have hclockW : clockTimes ⊆ W := by
      intro s hs
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
      have hj' := Finset.mem_range.mp hj
      have hu := hu_props j hj'
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu.1, by omega⟩
    have hclockCard : clockTimes.card = k + 1 := by
      have hinj : Set.InjOn u (↑(Finset.range (k + 1)) : Set ℕ) := by
        intro i hi j hj hij
        have hi' := Finset.mem_range.mp hi
        have hj' := Finset.mem_range.mp hj
        have hmul : (q - i) * p = (q - j) * p := hij
        have hsub : q - i = q - j := Nat.mul_right_cancel hp hmul
        have hqi : i ≤ q := by omega
        have hqj : j ≤ q := by omega
        have hci : q - i + i = q := Nat.sub_add_cancel hqi
        have hcj : q - j + j = q := Nat.sub_add_cancel hqj
        omega
      simpa [clockTimes] using (Finset.card_image_iff.mpr hinj)
    have hdisj : Disjoint highTimes clockTimes := by
      rw [Finset.disjoint_left]
      intro s hsHigh hsClock
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hsHigh
      obtain ⟨j, hj, hsame⟩ := Finset.mem_image.mp hsClock
      have hwi := hwHigh i (Finset.mem_range.mp hi)
      have hu := hu_props j (Finset.mem_range.mp hj)
      have : row k (wHigh i) = row k (u j) := by rw [hsame]
      rw [hwi.2.1, hu.2.1] at this
      omega
    have hunion : highTimes ∪ clockTimes ⊆ W := Finset.union_subset hhighW hclockW
    have hcard_union : (highTimes ∪ clockTimes).card = B + 1 := by
      rw [Finset.card_union_of_disjoint hdisj, hHighCard, hclockCard]
      exact hMform
    have : B + 1 ≤ B := by
      rw [← hcard_union]
      exact (Finset.card_le_card hunion).trans hWcard
    omega
  let B := k * (k + 2)
  have hB : 0 < B := Nat.mul_pos hk (by omega)
  let Y := Fin B → Fin (B + 1)
  let state (t : ℕ) : Y := fun i => ⟨row k (t + i.val), by
    have hb := row_bound (t + i.val)
    change row k (t + i.val) < B + 1
    omega⟩
  let eligible (w : Y) (x : ℕ) : Prop :=
    k ≤ x ∧ x ≤ B ∧ ∀ i : Fin B, (w i).val = x → i.val + x < B
  have eligible_iff (t x : ℕ) : eligible (state t) x ↔
      legal k (t + B) x (row k) ∧ x ≤ B := by
    constructor
    · rintro ⟨hxk, hxb, hx⟩
      refine ⟨⟨hxk, ?_⟩, hxb⟩
      intro s hs hsx
      by_cases hst : s < t
      · omega
      · have hts : t ≤ s := by omega
        have hi : s - t < B := by omega
        have hval : ((state t) ⟨s - t, hi⟩).val = x := by
          change row k (t + (s - t)) = x
          simpa [Nat.add_sub_of_le hts] using hsx
        have hsmall := hx ⟨s - t, hi⟩ hval
        change s - t + x < B at hsmall
        omega
    · rintro ⟨hx, hxb⟩
      refine ⟨hx.1, hxb, ?_⟩
      intro i hix
      have hs : t + i.val < t + B := by omega
      have hsx : row k (t + i.val) = x := hix
      have hsmall := hx.2 (t + i.val) hs hsx
      omega
  have has_eligible (t : ℕ) : ∃ x, eligible (state t) x :=
    ⟨row k (t + B), (eligible_iff t _).mpr ⟨row_legal (t + B), row_bound (t + B)⟩⟩
  let next (w : Y) : Fin (B + 1) :=
    if hw : ∃ x, eligible w x then
      ⟨Nat.find hw, by have hx := (Nat.find_spec hw).2.1; omega⟩
    else ⟨0, by omega⟩
  have next_actual (t : ℕ) : (next (state t)).val = row k (t + B) := by
    dsimp [next]
    rw [dif_pos (has_eligible t)]
    apply Nat.le_antisymm
    · exact Nat.find_min' (has_eligible t)
        ((eligible_iff t _).mpr ⟨row_legal (t + B), row_bound (t + B)⟩)
    · exact row_min (t + B) _
        ((eligible_iff t _).mp (Nat.find_spec (has_eligible t))).1
  let shift (w : Y) : Y := fun i =>
    if hi : i.val + 1 < B then w ⟨i.val + 1, hi⟩ else next w
  have shift_actual (t : ℕ) : shift (state t) = state (t + 1) := by
    funext i
    apply Fin.ext
    dsimp [shift]
    split_ifs with hi
    · change row k (t + (i.val + 1)) = row k (t + 1 + i.val)
      congr 1
      omega
    · rw [next_actual]
      change row k (t + B) = row k (t + 1 + i.val)
      congr 1
      omega
  let step : Y × Unit → Y × Unit := fun z => (shift z.1, z.2)
  have orbit_actual (t : ℕ) : (step^[t]) (state 0, ()) = (state t, ()) := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply', ih]
      change (shift (state t), ()) = (state (t + 1), ())
      rw [shift_actual]
  obtain ⟨N, p, hp, hperiod⟩ :=
    finite_input_generator_eventually_periodic
        (Y := Y) (C := Unit) (U := Unit)
        (fun _ w => shift w) id (fun _ => ()) (state 0, ())
  refine ⟨N, p, hp, ?_⟩
  intro t ht
  have heq := hperiod (t - N)
  change (step^[N + (t - N) + p]) (state 0, ()) =
    (step^[N + (t - N)]) (state 0, ()) at heq
  rw [orbit_actual, orbit_actual] at heq
  have htime : N + (t - N) = t := Nat.add_sub_of_le ht
  rw [htime] at heq
  have hhead := congrArg (fun z : Y × Unit => (z.1 ⟨0, hB⟩).val) heq
  simpa [state] using hhead

end
end D5.S3.Combinatorics.OeisA398589EventualPeriodicity
