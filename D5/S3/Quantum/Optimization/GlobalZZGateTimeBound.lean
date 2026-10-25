/- GID: D5/S3/Quantum/Optimization/GlobalZZGateTimeBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Optimization/GlobalZZGateTimeBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Global ZZ couplings admit nonnegative sign schedules within the sharp parity bound. -/

import D5.S3.Observer.Linear.FiniteRealZeroFillRegister
import D5.S3.Entropy.Forgetting.CapacityMonotone
import D5.S3.ConceptDynamics.CausalMoments.BipartiteMediatorPricing

/-! Nonnegative sign schedules from round-robin matchings and their product laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Optimization.GlobalZZGateTimeBound

open D5.S3.Observer.Linear.FiniteRealZeroFillRegister (bitSign)
open D5.S3.Entropy.Forgetting.CapacityMonotone (pushforward)
open D5.S3.ConceptDynamics.CausalMoments.BipartiteMediatorPricing
  (flipTable flipTable_involutive)

abbrev SignVec (n : ℕ) :=
  {s : Fin n → Bool // ∀ i, i.val + 1 = n → s i = false}

def IsFeasible {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (lam : SignVec n → ℝ) : Prop :=
  (∀ m, 0 ≤ lam m) ∧ ∀ i j, i < j →
    M i j = ∑ m, lam m * ((-1 : ℝ) ^ (m.val i).toNat * (-1 : ℝ) ^ (m.val j).toNat)

def offDiagSup {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun p : Option (Fin n × Fin n) =>
    p.elim 0 (fun e => if e.1 < e.2 then |M e.1 e.2| else 0))

def gateBound (n : ℕ) : ℝ := ((if Even n then n - 1 else n : ℕ) : ℝ)

def claim : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ M : Matrix (Fin n) (Fin n) ℝ,
    M.IsSymm → (∀ i, M i i = 0) →
    ∃ lam, IsFeasible M lam ∧ ∑ m, lam m ≤ gateBound n * offDiagSup M

private def IsMatching {n : ℕ} (R : Finset (Fin n × Fin n)) : Prop :=
  (∀ e ∈ R, e.1 < e.2) ∧
    (R : Set (Fin n × Fin n)).PairwiseDisjoint (fun e => ({e.1, e.2} : Finset (Fin n)))

private theorem partition_from_color (n k : ℕ) (color : Fin n → Fin n → Fin k)
    (hsymm : ∀ i j, color i j = color j i)
    (hproper : ∀ i j l, i ≠ j → i ≠ l → color i j = color i l → j = l) :
    ∃ R : Fin k → Finset (Fin n × Fin n), (∀ r, IsMatching (R r)) ∧
      ∀ i j, i < j → ∃! r, (i, j) ∈ R r := by
  classical
  let R := fun r => Finset.univ.filter (fun e : Fin n × Fin n =>
    e.1 < e.2 ∧ color e.1 e.2 = r)
  refine ⟨R, ?_, ?_⟩
  · intro r
    refine ⟨fun e he => (Finset.mem_filter.mp he).2.1, ?_⟩
    rintro ⟨a, b⟩ he ⟨c, d⟩ hf hef
    have hab : a < b := (Finset.mem_filter.mp he).2.1
    have hcd : c < d := (Finset.mem_filter.mp hf).2.1
    have hcolor : color a b = color c d :=
      (Finset.mem_filter.mp he).2.2.trans (Finset.mem_filter.mp hf).2.2.symm
    apply Finset.disjoint_left.mpr
    intro v hv hfv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv hfv
    rcases hv with ha | hb <;> rcases hfv with hc | hd
    · have hac : a = c := ha.symm.trans hc
      clear ha hc
      subst c
      exact hef (Prod.ext rfl (hproper a b d (ne_of_lt hab) (ne_of_lt hcd) hcolor))
    · have had : a = d := ha.symm.trans hd
      clear ha hd
      subst d
      have hbc := hproper a b c (ne_of_lt hab) (ne_of_gt hcd)
        (hcolor.trans (hsymm c a))
      omega
    · have hbc : b = c := hb.symm.trans hc
      clear hb hc
      subst c
      have had := hproper b a d (ne_of_gt hab) (ne_of_lt hcd)
        ((hsymm b a).trans hcolor)
      omega
    · have hbd : b = d := hb.symm.trans hd
      clear hb hd
      subst d
      have hac := hproper b a c (ne_of_gt hab) (ne_of_gt hcd)
        ((hsymm b a).trans (hcolor.trans (hsymm c b)))
      exact hef (Prod.ext hac rfl)
  · intro i j hij
    refine ⟨color i j, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, rfl⟩
    · intro r hr
      exact (Finset.mem_filter.mp hr).2.2.symm

private def cyclicColor {q : ℕ} : Option (ZMod q) → Option (ZMod q) → ZMod q
  | none, none => 0
  | none, some y => y + y
  | some x, none => x + x
  | some x, some y => x + y

private theorem cyclicColor_symm {q : ℕ} (u v : Option (ZMod q)) :
    cyclicColor u v = cyclicColor v u := by
  cases u <;> cases v
  · rfl
  · rfl
  · rfl
  · exact add_comm _ _

private theorem cyclicColor_proper {q : ℕ} (hq : Odd q) (u v w : Option (ZMod q))
    (huv : u ≠ v) (huw : u ≠ w) (h : cyclicColor u v = cyclicColor u w) : v = w := by
  cases u with
  | none =>
    cases v with
    | none => exact (huv rfl).elim
    | some y =>
      cases w with
      | none => exact (huw rfl).elim
      | some z =>
        congr 1
        apply sub_eq_zero.mp
        apply (ZMod.add_self_eq_zero_iff_eq_zero hq).mp
        change y + y = z + z at h
        linear_combination h
  | some x =>
    cases v with
    | none =>
      cases w with
      | none => rfl
      | some z =>
        change x + x = x + z at h
        exact (huw (congrArg some (add_left_cancel h))).elim
    | some y =>
      cases w with
      | none =>
        change x + y = x + x at h
        exact (huv (congrArg some (add_left_cancel h).symm)).elim
      | some z =>
        exact congrArg some (add_left_cancel h)

private theorem round_robin_partition (n : ℕ) (hn : 2 ≤ n) :
    ∃ R : Fin (if Even n then n - 1 else n) → Finset (Fin n × Fin n),
      (∀ r, IsMatching (R r)) ∧
      ∀ i j, i < j → ∃! r, (i, j) ∈ R r := by
  classical
  by_cases he : Even n
  · have hq : Odd (n - 1) := by
      obtain ⟨k, hk⟩ := he
      exact ⟨k - 1, by omega⟩
    letI : NeZero (n - 1) := ⟨by omega⟩
    let e : Fin n ≃ Option (ZMod (n - 1)) := Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, Fintype.card_option, ZMod.card]
      omega)
    let er : ZMod (n - 1) ≃ Fin (n - 1) := Fintype.equivOfCardEq (by
      rw [ZMod.card, Fintype.card_fin])
    rw [ite_eq_left he]
    apply partition_from_color n (n - 1) (fun i j => er (cyclicColor (e i) (e j)))
    · intro i j
      rw [cyclicColor_symm]
    · intro i j l hij hil h
      exact e.injective (cyclicColor_proper hq _ _ _
        (fun h => hij (e.injective h)) (fun h => hil (e.injective h)) (er.injective h))
  · letI : NeZero n := ⟨by omega⟩
    let e : Fin n ≃ ZMod n := Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, ZMod.card])
    rw [ite_eq_right he]
    apply partition_from_color n n (fun i j => e.symm (e i + e j))
    · intro i j
      rw [add_comm]
    · intro i j l _ _ h
      exact e.injective (add_left_cancel (e.symm.injective h))

private theorem matching_subset {n : ℕ} {R S : Finset (Fin n × Fin n)}
    (hR : IsMatching R) (hSR : S ⊆ R) : IsMatching S :=
  ⟨fun e he => hR.1 e (hSR he), hR.2.subset hSR⟩

private def spin {n : ℕ} (s : Fin n → Bool) (i : Fin n) : ℝ :=
  bitSign (s i)

private theorem spin_flip {n : ℕ} (A : Finset (Fin n)) (s : Fin n → Bool) (i : Fin n) :
    spin (A.piecewise (fun i => !(s i)) s) i = if i ∈ A then -spin s i else spin s i := by
  unfold spin bitSign Finset.piecewise
  by_cases hi : i ∈ A <;> cases h : s i <;> simp only [hi, h, ite_true, ite_false,
    Bool.not_false, Bool.not_true, Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one,
    neg_one_mul, neg_neg]

private theorem sum_flip_zero {n : ℕ} (A : Finset (Fin n)) (F : (Fin n → Bool) → ℝ)
    (hF : ∀ s, F (A.piecewise (fun i => !(s i)) s) = -F s) : ∑ s, F s = 0 := by
  exact Finset.sum_ninvolution (fun s => A.piecewise (fun i => !(s i)) s)
    (fun s => by rw [hF, add_neg_cancel])
    (fun s hne hfix => hne ((CharZero.eq_neg_self_iff (R := ℝ)).mp
      ((congrArg F hfix).symm.trans (hF s))))
    (fun _ => Finset.mem_univ _) (fun s => by
      simpa +unfoldPartialApp only [flipTable, Bool.decide_iff, Finset.piecewise] using
        flipTable_involutive (fun i => decide (i ∈ A)) s)

private def matchingWeight {n : ℕ} (R : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ) (s : Fin n → Bool) : ℝ :=
  ∏ e ∈ R, (1 + c e.1 e.2 * spin s e.1 * spin s e.2)

private theorem matchingWeight_flip {n : ℕ} (R : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ) (A : Finset (Fin n))
    (hA : ∀ e ∈ R, e.1 ∈ A ↔ e.2 ∈ A) (s : Fin n → Bool) :
    matchingWeight R c (A.piecewise (fun i => !(s i)) s) = matchingWeight R c s := by
  unfold matchingWeight
  apply Finset.prod_congr rfl
  intro e he
  rw [spin_flip, spin_flip]
  by_cases hi : e.1 ∈ A
  · rw [ite_eq_left hi, ite_eq_left ((hA e he).mp hi)]
    ring
  · rw [ite_eq_right hi, ite_eq_right (mt (hA e he).mpr hi)]

private theorem matching_separating_block {n : ℕ} (R : Finset (Fin n × Fin n))
    (hR : IsMatching R) (i j : Fin n) (hij : i < j) (hijR : (i, j) ∉ R) :
    ∃ A : Finset (Fin n), i ∈ A ∧ j ∉ A ∧ ∀ e ∈ R, e.1 ∈ A ↔ e.2 ∈ A := by
  classical
  by_cases hex : ∃ e ∈ R, i = e.1 ∨ i = e.2
  · obtain ⟨e, he, hie⟩ := hex
    refine ⟨{e.1, e.2}, by simpa using hie, ?_, ?_⟩
    · intro hj
      have heord := hR.1 e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hie with hi | hi <;> rcases hj with hj | hj
      · omega
      · have heq : e = (i, j) := Prod.ext hi.symm hj.symm
        exact hijR (heq ▸ he)
      · omega
      · omega
    · intro f hf
      by_cases hfe : f = e
      · subst f
        simp
      · have hdis := hR.2.disjoint_of_ne he hf (Ne.symm hfe)
        have hf1 : f.1 ∉ ({e.1, e.2} : Finset (Fin n)) := fun h =>
          Finset.disjoint_left.mp hdis h (by simp)
        have hf2 : f.2 ∉ ({e.1, e.2} : Finset (Fin n)) := fun h =>
          Finset.disjoint_left.mp hdis h (by simp)
        simp only [hf1, hf2]
  · refine ⟨{i}, by simp, by simpa using ne_of_gt hij, ?_⟩
    intro e he
    have hi1 : i ≠ e.1 := fun h => hex ⟨e, he, Or.inl h⟩
    have hi2 : i ≠ e.2 := fun h => hex ⟨e, he, Or.inr h⟩
    simp only [Finset.mem_singleton, Ne.symm hi1, Ne.symm hi2]

private theorem matchingWeight_pair_zero {n : ℕ} (R : Finset (Fin n × Fin n))
    (hR : IsMatching R) (c : Fin n → Fin n → ℝ)
    (i j : Fin n) (hij : i < j) (hijR : (i, j) ∉ R) :
    ∑ s, matchingWeight R c s * (spin s i * spin s j) = 0 := by
  obtain ⟨A, hi, hj, hA⟩ := matching_separating_block R hR i j hij hijR
  apply sum_flip_zero A
  intro s
  rw [matchingWeight_flip R c A hA, spin_flip, spin_flip,
    ite_eq_left hi, ite_eq_right hj]
  ring

private theorem matchingWeight_sum {n : ℕ} (R : Finset (Fin n × Fin n))
    (hR : IsMatching R) (c : Fin n → Fin n → ℝ) :
    ∑ s, matchingWeight R c s = (2 : ℝ) ^ n := by
  classical
  revert hR
  induction R using Finset.induction_on with
  | empty =>
    intro _
    unfold matchingWeight
    simp
  | @insert e R he ih =>
    intro hR
    have hrest := matching_subset hR (Finset.subset_insert e R)
    have hz := matchingWeight_pair_zero R hrest c e.1 e.2
      (hR.1 e (Finset.mem_insert_self _ _)) he
    calc
      (∑ s, matchingWeight (insert e R) c s) =
          ∑ s, (matchingWeight R c s + c e.1 e.2 *
            (matchingWeight R c s * (spin s e.1 * spin s e.2))) := by
        apply Finset.sum_congr rfl
        intro s _
        unfold matchingWeight
        rw [Finset.prod_insert he]
        ring
      _ = (∑ s, matchingWeight R c s) + c e.1 e.2 *
          ∑ s, matchingWeight R c s * (spin s e.1 * spin s e.2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (2 : ℝ) ^ n := by rw [ih hrest, hz, mul_zero, add_zero]

private theorem matchingWeight_pair_mem {n : ℕ} (R : Finset (Fin n × Fin n))
    (hR : IsMatching R) (c : Fin n → Fin n → ℝ)
    (i j : Fin n) (hij : i < j) (hijR : (i, j) ∈ R) :
    ∑ s, matchingWeight R c s * (spin s i * spin s j) = c i j * (2 : ℝ) ^ n := by
  classical
  have hrest := matching_subset hR (Finset.erase_subset (i, j) R)
  have hz := matchingWeight_pair_zero (R.erase (i, j)) hrest c i j hij
    (Finset.notMem_erase _ _)
  have hmass := matchingWeight_sum (R.erase (i, j)) hrest c
  calc
    (∑ s, matchingWeight R c s * (spin s i * spin s j)) =
        ∑ s, (matchingWeight (R.erase (i, j)) c s * (spin s i * spin s j) +
          c i j * matchingWeight (R.erase (i, j)) c s) := by
      apply Finset.sum_congr rfl
      intro s _
      have hfactor : matchingWeight R c s =
          (1 + c i j * spin s i * spin s j) * matchingWeight (R.erase (i, j)) c s := by
        unfold matchingWeight
        exact (Finset.mul_prod_erase R _ hijR).symm
      rw [hfactor]
      unfold spin bitSign
      cases hi : s i <;> cases hj : s j <;> simp only [hi, hj, Bool.toNat_false,
        Bool.toNat_true, pow_zero, pow_one] <;> ring
    _ = c i j * (2 : ℝ) ^ n := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hz, hmass, zero_add]

private theorem matching_law {n : ℕ} (R : Finset (Fin n × Fin n))
    (hR : IsMatching R) (c : Fin n → Fin n → ℝ)
    (hc : ∀ i j, i < j → |c i j| ≤ 1) :
    ∃ p : (Fin n → Bool) → ℝ,
      (∀ s, 0 ≤ p s) ∧ (∑ s, p s = 1) ∧
      ∀ i j, i < j →
        (∑ s, p s * ((-1 : ℝ) ^ (s i).toNat * (-1 : ℝ) ^ (s j).toNat)) =
          if (i, j) ∈ R then c i j else 0 := by
  classical
  let p : (Fin n → Bool) → ℝ := fun s => matchingWeight R c s / (2 : ℝ) ^ n
  have htwo : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  refine ⟨p, ?_, ?_, ?_⟩
  · intro s
    apply div_nonneg _ htwo.le
    unfold matchingWeight
    apply Finset.prod_nonneg
    intro e he
    have hb := abs_le.mp (hc e.1 e.2 (hR.1 e he))
    unfold spin bitSign
    cases hi : s e.1 <;> cases hj : s e.2 <;>
      simp only [hi, hj, Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one] <;>
      nlinarith
  · dsimp only [p]
    rw [← Finset.sum_div, matchingWeight_sum R hR c]
    exact div_self (ne_of_gt htwo)
  · intro i j hij
    change (∑ s, p s * (spin s i * spin s j)) = _
    dsimp only [p]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    by_cases he : (i, j) ∈ R
    · rw [matchingWeight_pair_mem R hR c i j hij he, ite_eq_left he,
        mul_div_cancel_right₀ _ (ne_of_gt htwo)]
    · rw [matchingWeight_pair_zero R hR c i j hij he, ite_eq_right he, zero_div]

private theorem fold_law {n : ℕ} (hn : 2 ≤ n) (p : (Fin n → Bool) → ℝ)
    (hp : ∀ s, 0 ≤ p s) :
    ∃ q : SignVec n → ℝ,
      (∀ m, 0 ≤ q m) ∧ (∑ m, q m = ∑ s, p s) ∧
      ∀ i j, (∑ m, q m * ((-1 : ℝ) ^ (m.val i).toNat * (-1 : ℝ) ^ (m.val j).toNat)) =
        ∑ s, p s * ((-1 : ℝ) ^ (s i).toNat * (-1 : ℝ) ^ (s j).toNat) := by
  classical
  letI : DecidableEq (SignVec n) := Classical.decEq _
  let last : Fin n := ⟨n - 1, by omega⟩
  let f : (Fin n → Bool) → SignVec n := fun s =>
    ⟨fun i => if s last then !(s i) else s i, by
      intro i hi
      have hil : i = last := Fin.ext (by dsimp only [last]; omega)
      subst i
      cases h : s last <;> simp [h]⟩
  have hprod (s : Fin n → Bool) (i j : Fin n) :
      (-1 : ℝ) ^ ((f s).val i).toNat * (-1 : ℝ) ^ ((f s).val j).toNat =
        (-1 : ℝ) ^ (s i).toNat * (-1 : ℝ) ^ (s j).toNat := by
    dsimp only [f]
    cases s last <;> cases s i <;> cases s j <;> norm_num
  refine ⟨pushforward f p, ?_, ?_, ?_⟩
  · intro m
    change 0 ≤ ∑ s, if f s = m then p s else 0
    exact Finset.sum_nonneg fun s _ => ite_nonneg (hp s) le_rfl
  · simpa only [pushforward, Finset.sum_filter] using Finset.sum_fiberwise Finset.univ f p
  · intro i j
    let g : SignVec n → ℝ := fun m =>
      (-1 : ℝ) ^ (m.val i).toNat * (-1 : ℝ) ^ (m.val j).toNat
    change (∑ m, pushforward f p m * g m) = _
    calc
      _ = ∑ m, ∑ s with f s = m, p s * g (f s) := by
        simp only [pushforward, Finset.sum_filter, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m _
        apply Finset.sum_congr rfl
        intro s _
        split_ifs with hs
        · rw [hs]
        · simp only [zero_mul]
      _ = ∑ s, p s * g (f s) := Finset.sum_fiberwise Finset.univ f (fun s => p s * g (f s))
      _ = _ := by simp only [g, hprod]

private theorem offDiagSup_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ offDiagSup M := by
  unfold offDiagSup
  exact Finset.le_sup' (fun p : Option (Fin n × Fin n) =>
    p.elim (0 : ℝ) (fun e => if e.1 < e.2 then |M e.1 e.2| else 0)) (Finset.mem_univ none)

private theorem entry_le_offDiagSup {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (hij : i < j) : |M i j| ≤ offDiagSup M := by
  unfold offDiagSup
  have h := Finset.le_sup' (fun p : Option (Fin n × Fin n) =>
      p.elim (0 : ℝ) (fun e => if e.1 < e.2 then |M e.1 e.2| else 0))
      (Finset.mem_univ (some (i, j)))
  change (if i < j then |M i j| else 0) ≤ _ at h
  rw [ite_eq_left hij] at h
  exact h

private theorem assemble_schedule (n : ℕ) (hn : 2 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (R : Fin (if Even n then n - 1 else n) → Finset (Fin n × Fin n))
    (hR : ∀ r, IsMatching (R r))
    (hcover : ∀ i j, i < j → ∃! r, (i, j) ∈ R r) :
    ∃ lam, IsFeasible M lam ∧ ∑ m, lam m ≤ gateBound n * offDiagSup M := by
  classical
  have hd := offDiagSup_nonneg M
  have hentries := entry_le_offDiagSup M
  by_cases hd0 : offDiagSup M = 0
  · refine ⟨fun _ => 0, ⟨fun _ => le_rfl, ?_⟩, ?_⟩
    · intro i j hij
      have heabs : |M i j| ≤ 0 := by simpa only [hd0] using hentries i j hij
      have he : M i j = 0 := abs_eq_zero.mp (le_antisymm heabs (abs_nonneg _))
      simp only [he, zero_mul, Finset.sum_const_zero]
    · simp only [Finset.sum_const_zero, hd0, mul_zero, le_refl]
  have hdpos : 0 < offDiagSup M := lt_of_le_of_ne hd (Ne.symm hd0)
  have hc (i j : Fin n) (hij : i < j) : |M i j / offDiagSup M| ≤ 1 := by
    rw [abs_div, abs_of_pos hdpos]
    exact (div_le_one hdpos).2 (hentries i j hij)
  choose p hp hmass hmoment using fun r => matching_law (R r) (hR r)
    (fun i j => M i j / offDiagSup M) hc
  let w : (Fin n → Bool) → ℝ := fun s => offDiagSup M * ∑ r, p r s
  have hw (s) : 0 ≤ w s := mul_nonneg hd (Finset.sum_nonneg fun r _ => hp r s)
  obtain ⟨q, hq, hqmass, hqmoment⟩ := fold_law hn w hw
  refine ⟨q, ⟨hq, ?_⟩, ?_⟩
  · intro i j hij
    rw [hqmoment]
    obtain ⟨r, hr, hur⟩ := hcover i j hij
    have huniq (r') : (i, j) ∈ R r' ↔ r' = r :=
      ⟨hur r', fun h => h ▸ hr⟩
    have hsum : (∑ r', if (i, j) ∈ R r' then M i j / offDiagSup M else 0) =
        M i j / offDiagSup M := by
      simp_rw [huniq]
      simp
    calc
      M i j = offDiagSup M * (M i j / offDiagSup M) :=
        (mul_div_cancel₀ _ hd0).symm
      _ = offDiagSup M * ∑ r', ∑ s, p r' s *
          ((-1 : ℝ) ^ (s i).toNat * (-1 : ℝ) ^ (s j).toNat) := by
        simp_rw [hmoment _ i j hij]
        rw [hsum]
      _ = ∑ s, w s * ((-1 : ℝ) ^ (s i).toNat * (-1 : ℝ) ^ (s j).toNat) := by
        dsimp only [w]
        simp_rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
  · rw [hqmass]
    change (∑ s, offDiagSup M * ∑ r, p r s) ≤ gateBound n * offDiagSup M
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hmass]
    unfold gateBound
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_comm, le_refl]

theorem result : claim := by
  intro n hn M _ _
  obtain ⟨R, hR, hcover⟩ := round_robin_partition n hn
  exact assemble_schedule n hn M R hR hcover

end D5.S3.Quantum.Optimization.GlobalZZGateTimeBound
