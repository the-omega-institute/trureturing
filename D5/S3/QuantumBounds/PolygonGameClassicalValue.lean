/- GID: D5/S3/QuantumBounds/PolygonGameClassicalValue
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/PolygonGameClassicalValue
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The odd polygon game's classical value is one minus its Fibonacci loss fraction. -/

import D5.S1.Words.AdmissibleWords.AdmissibleCount
import D5.S0.Automata.TwoStateCertificateWidth
import D5.S3.Arith.Robin.FibonacciRankEulerTail
import D5.S3.Quantum.Information.BargmannImaginaryMaximizers

/-! The uniform-input polygon game, with arbitrary local deterministic response tables. -/

noncomputable section

open scoped BigOperators

namespace D5.S3.QuantumBounds.PolygonGameClassicalValue

open D5.S1.Words.AdmissibleWords.AdmissibleCount

/-- Edge `i` joins player `i` to `finRotate P i`. -/
def IsMatching (P : ℕ) (M : Finset (Fin P)) : Prop :=
  ∀ i ∈ M, finRotate P i ∉ M

/-- The input is true exactly at endpoints of matching edges. -/
def matchingInput (P : ℕ) (M : Finset (Fin P)) : Fin P → Bool :=
  fun i => decide (i ∈ M ∨ (finRotate P).symm i ∈ M)

/-- Even local triples, even middle parity, and the source matching rule. -/
def wins (P : ℕ) (s : Fin P → Bool → Bool × Bool × Bool) (x : Fin P → Bool) : Prop :=
  (∀ i, ((s i (x i)).1.toNat + (s i (x i)).2.1.toNat +
    (s i (x i)).2.2.toNat : ZMod 2) = 0) ∧
  (∑ i, ((s i (x i)).2.1.toNat : ZMod 2)) = 0 ∧
  ∀ M : Finset (Fin P), IsMatching P M → matchingInput P M = x →
    (∑ i ∈ M, ((s i true).1.toNat + (s (finRotate P i) true).2.2.toNat : ZMod 2)) +
      (∑ i ∈ Finset.univ.filter (fun i => matchingInput P M i = false),
        ((s i false).1.toNat : ZMod 2)) = (M.card : ZMod 2)

/-- Shared randomness is a probability weight on all local deterministic response tables. -/
def winProbability (P : ℕ) (μ : (Fin P → Bool → Bool × Bool × Bool) → ℝ) : ℝ := by
  classical
  exact ∑ s, μ s * ((Finset.univ.filter (wins P s)).card : ℝ) / 2 ^ P

/-- The classical upper bound and deterministic attainment, for every odd polygon. -/
def claim : Prop := by
  classical
  exact ∀ P : ℕ, Odd P → 3 ≤ P →
    (∀ μ : (Fin P → Bool → Bool × Bool × Bool) → ℝ,
      (∀ s, 0 ≤ μ s) → ∑ s, μ s = 1 →
      winProbability P μ ≤ 1 - (Nat.fib (P - 1) : ℝ) / 2 ^ P) ∧
    ∃ s : Fin P → Bool → Bool × Bool × Bool,
      ((Finset.univ.filter (wins P s)).card : ℝ) / 2 ^ P =
        1 - (Nat.fib (P - 1) : ℝ) / 2 ^ P

private def locallyLegal (P : ℕ) (s : Fin P → Bool → Bool × Bool × Bool) : Prop :=
  ∀ i x, ((s i x).1.toNat + (s i x).2.1.toNat + (s i x).2.2.toNat : ZMod 2) = 0

private def fixedMiddle (P : ℕ) (s : Fin P → Bool → Bool × Bool × Bool) : Prop :=
  ∀ i, (s i false).2.1 = (s i true).2.1

private def baseline (P : ℕ) (s : Fin P → Bool → Bool × Bool × Bool) : ZMod 2 :=
  ∑ i, ((s i false).1.toNat : ZMod 2)

private def edgeCharge (P : ℕ) (s : Fin P → Bool → Bool × Bool × Bool) (i : Fin P) :
    ZMod 2 :=
  1 + ((s i false).1.toNat : ZMod 2) + (s i true).1.toNat +
    (s (finRotate P i) false).1.toNat + (s (finRotate P i) true).1.toNat +
    (s (finRotate P i) false).2.1.toNat

private def avoiding (P : ℕ) (j : Fin P) : Finset (Finset (Fin P)) := by
  classical
  exact Finset.univ.filter (fun N => IsMatching P N ∧
    (finRotate P).symm j ∉ N ∧ j ∉ N ∧ finRotate P j ∉ N)

private def attainingStrategy (P : ℕ) : Fin P → Bool → Bool × Bool × Bool :=
  fun i x => if i.val + 1 < P then (true, true, false)
    else if x then (true, false, true) else (false, false, false)

open Classical in
private lemma local_violation_half (P : ℕ)
    (s : Fin P → Bool → Bool × Bool × Bool) (h : ¬ locallyLegal P s) :
    2 ^ (P - 1) ≤ (Finset.univ.filter (fun x => ¬ wins P s x)).card := by
  classical
  rw [locallyLegal.eq_1] at h
  obtain ⟨i, b, hbad⟩ : ∃ i b,
      ((s i b).1.toNat + (s i b).2.1.toNat + (s i b).2.2.toNat : ZMod 2) ≠ 0 := by
    simpa only [not_forall] using h
  calc
    2 ^ (P - 1) = (Finset.univ.filter (fun x : Fin P → Bool => x i = b)).card := by
      simpa only [Fintype.piFinset_univ, Finset.card_univ, Fintype.card_bool,
        Fintype.card_fin] using (Fintype.card_filter_piFinset_const_eq_of_mem
        (Finset.univ : Finset Bool) i (Finset.mem_univ b)).symm
    _ ≤ _ := Finset.card_le_card (by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      intro hw
      exact hbad (by simpa only [hx] using hw.1 i))

open Classical in
private lemma varying_middle_half (P : ℕ) (hP : 3 ≤ P)
    (s : Fin P → Bool → Bool × Bool × Bool) (h : ¬ fixedMiddle P s) :
    2 ^ (P - 1) ≤ (Finset.univ.filter (fun x => ¬ wins P s x)).card := by
  classical
  rw [fixedMiddle.eq_1] at h
  obtain ⟨i, hi⟩ : ∃ i, (s i false).2.1 ≠ (s i true).2.1 := by
    simpa only [not_forall] using h
  let flip : (Fin P → Bool) → (Fin P → Bool) :=
    fun x => Function.update x i (!(x i))
  have hinv (x : Fin P → Bool) : flip (flip x) = x := by
    simp only [flip, Function.update_self, Bool.not_not,
      Function.update_idem, Function.update_eq_self]
  have hbit (b : Bool) : ((s i (!b)).2.1.toNat : ZMod 2) =
      (s i b).2.1.toNat + 1 := by
    cases b with
    | false =>
      change ((s i true).2.1.toNat : ZMod 2) = (s i false).2.1.toNat + 1
      cases hzero : (s i false).2.1 <;> cases hone : (s i true).2.1
      all_goals first | exact (hi (hzero.trans hone.symm)).elim | decide
    | true =>
      change ((s i false).2.1.toNat : ZMod 2) = (s i true).2.1.toNat + 1
      cases hzero : (s i false).2.1 <;> cases hone : (s i true).2.1
      all_goals first | exact (hi (hzero.trans hone.symm)).elim | decide
  have hsum (x : Fin P → Bool) :
      (∑ j, ((s j (flip x j)).2.1.toNat : ZMod 2)) =
        (∑ j, ((s j (x j)).2.1.toNat : ZMod 2)) + 1 := by
    have hfun : (fun j => ((s j (flip x j)).2.1.toNat : ZMod 2)) =
        Function.update (fun j => ((s j (x j)).2.1.toNat : ZMod 2)) i
          ((s i (!(x i))).2.1.toNat : ZMod 2) := by
      exact funext (Function.apply_update
        (fun j b => ((s j b).2.1.toNat : ZMod 2)) x i (!(x i)))
    rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ i), hbit]
    rw [← Finset.add_sum_erase Finset.univ
      (fun j => ((s j (x j)).2.1.toNat : ZMod 2)) (Finset.mem_univ i)]
    simp only [Finset.sdiff_singleton_eq_erase]
    ring
  have hcard : (Finset.univ.filter (wins P s)).card ≤
      (Finset.univ.filter (fun x => ¬ wins P s x)).card := by
    apply Finset.card_le_card_of_injOn flip
    · intro x hx
      have hw : wins P s x := (Finset.mem_filter.mp hx).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hwin
      have hh := hwin.2.1
      rw [hsum, hw.2.1, zero_add] at hh
      exact one_ne_zero hh
    · intro x _ y _ heq
      have hh := congrArg flip heq
      simpa only [hinv] using hh
  have htotal := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin P → Bool))) (wins P s)
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at htotal
  have hp : 2 ^ P = 2 * 2 ^ (P - 1) := by
    conv_lhs => rw [(Nat.sub_add_cancel (by omega : 1 ≤ P)).symm]
    rw [pow_succ, Nat.mul_comm]
  omega


open Classical in
private lemma odd_middle_all (P : ℕ) (s : Fin P → Bool → Bool × Bool × Bool)
    (hfixed : fixedMiddle P s)
    (hodd : (∑ i, ((s i false).2.1.toNat : ZMod 2)) ≠ 0) :
    (Finset.univ.filter (fun x => ¬ wins P s x)).card = 2 ^ P := by
  classical
  have hlose (x : Fin P → Bool) : ¬ wins P s x := by
    intro hw
    apply hodd
    convert hw.2.1 using 1
    apply Finset.sum_congr rfl
    intro i _
    cases hbit : x i
    · rfl
    · exact congrArg (fun b : Bool => (b.toNat : ZMod 2)) (hfixed i)
  have hfilter : Finset.univ.filter (fun x => ¬ wins P s x) = Finset.univ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact hlose x
  rw [hfilter]
  simp

open Classical in
private lemma affine_matching_rule (P : ℕ) (s : Fin P → Bool → Bool × Bool × Bool)
    (hlegal : locallyLegal P s) (hfixed : fixedMiddle P s)
    (M : Finset (Fin P)) (hM : IsMatching P M) :
    ((∑ i ∈ M, ((s i true).1.toNat + (s (finRotate P i) true).2.2.toNat : ZMod 2)) +
      (∑ i ∈ Finset.univ.filter (fun i => matchingInput P M i = false),
        ((s i false).1.toNat : ZMod 2)) = (M.card : ZMod 2)) ↔
      baseline P s + ∑ i ∈ M, edgeCharge P s i = 0 := by
  classical
  let a : Fin P → ZMod 2 := fun i => (s i false).1.toNat
  let U := Finset.univ.filter (fun i => matchingInput P M i = false)
  have hd : Disjoint M (M.image (finRotate P)) := by
    apply Finset.disjoint_left.2
    intro i hi himage
    obtain ⟨k, hk, hki⟩ := Finset.mem_image.1 himage
    exact hM k hk (hki ▸ hi)
  have hmem (i : Fin P) : i ∈ M.image (finRotate P) ↔ (finRotate P).symm i ∈ M := by
    simpa only [← Finset.coe_image, Finset.mem_coe] using
      (Set.mem_image_equiv (S := (M : Set (Fin P))) (f := finRotate P) (x := i))
  have hUeq : U = (M ∪ M.image (finRotate P))ᶜ := by
    ext i
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, matchingInput,
      decide_eq_false_iff_not, not_or, Finset.mem_compl, Finset.mem_union, hmem]
  have hdU : Disjoint (M ∪ M.image (finRotate P)) U := by
    rw [hUeq]
    exact disjoint_compl_right
  have hcover : (M ∪ M.image (finRotate P)) ∪ U = Finset.univ := by
    rw [hUeq]
    exact Finset.union_compl _
  have hsplit : baseline P s = (∑ i ∈ M, a i) +
      (∑ i ∈ M, a (finRotate P i)) + ∑ i ∈ U, a i := by
    change (∑ i, a i) = _
    rw [← hcover, Finset.sum_union hdU, Finset.sum_union hd,
      Finset.sum_image (fun i _ k _ hik => (finRotate P).injective hik)]
  have he (i : Fin P) : ((s i true).2.2.toNat : ZMod 2) =
      (s i true).1.toNat + (s i false).2.1.toNat := by
    have hh := hlegal i true
    rw [← hfixed i] at hh
    apply (CharTwo.add_eq_zero).1
    convert hh using 1
    ring
  have hcharge : (∑ i ∈ M, edgeCharge P s i) = (M.card : ZMod 2) +
      (∑ i ∈ M, a i) + (∑ i ∈ M, a (finRotate P i)) +
      ∑ i ∈ M, ((s i true).1.toNat + (s (finRotate P i) true).2.2.toNat : ZMod 2) := by
    simp only [edgeCharge, he, a, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  change ((∑ i ∈ M, ((s i true).1.toNat +
      (s (finRotate P i) true).2.2.toNat : ZMod 2)) + ∑ i ∈ U, a i = (M.card : ZMod 2)) ↔ _
  rw [hsplit, hcharge]
  have hn : (∑ i ∈ M, a i) + (∑ i ∈ M, a (finRotate P i)) + (∑ i ∈ U, a i) +
      ((M.card : ZMod 2) + (∑ i ∈ M, a i) + (∑ i ∈ M, a (finRotate P i)) +
        ∑ i ∈ M, ((s i true).1.toNat + (s (finRotate P i) true).2.2.toNat : ZMod 2)) =
      ((∑ i ∈ M, ((s i true).1.toNat + (s (finRotate P i) true).2.2.toNat : ZMod 2)) +
        ∑ i ∈ U, a i) + M.card := by
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]
  rw [hn, CharTwo.add_eq_zero]

open Classical in
private lemma marked_edge (P : ℕ) (hodd : Odd P)
    (s : Fin P → Bool → Bool × Bool × Bool)
    (heven : (∑ i, ((s i false).2.1.toNat : ZMod 2)) = 0) :
    ∃ j : Fin P, edgeCharge P s j = 1 := by
  have hsum : (∑ i, edgeCharge P s i) = 1 := by
    simp only [edgeCharge, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Equiv.sum_comp (finRotate P) (fun i => ((s i false).1.toNat : ZMod 2)),
      Equiv.sum_comp (finRotate P) (fun i => ((s i true).1.toNat : ZMod 2)),
      Equiv.sum_comp (finRotate P) (fun i => ((s i false).2.1.toNat : ZMod 2)),
      heven, hodd.natCast_zmod_two]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
  exact ⟨i, Fin.eq_one_of_ne_zero (edgeCharge P s i) hi⟩

open Classical in
private lemma matching_input_injective (P : ℕ) (hodd : Odd P) (hP : 3 ≤ P)
    (M N : Finset (Fin P)) (hM : IsMatching P M) (hN : IsMatching P N)
    (hinput : matchingInput P M = matchingInput P N) : M = N := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : P ≠ 0)
  let z : Fin (n + 1) → ℤ := fun i =>
    (if i ∈ M then 1 else 0) - (if i ∈ N then 1 else 0)
  have hinc (i : Fin (n + 1)) :
      (if i ∈ M then (1 : ℤ) else 0) + (if (finRotate (n + 1)).symm i ∈ M then 1 else 0) =
      (if i ∈ N then (1 : ℤ) else 0) + (if (finRotate (n + 1)).symm i ∈ N then 1 else 0) := by
    have hm : ¬ (i ∈ M ∧ (finRotate (n + 1)).symm i ∈ M) := by
      rintro ⟨hi, hp⟩
      exact hM _ hp (by simpa only [Equiv.apply_symm_apply] using hi)
    have hn : ¬ (i ∈ N ∧ (finRotate (n + 1)).symm i ∈ N) := by
      rintro ⟨hi, hp⟩
      exact hN _ hp (by simpa only [Equiv.apply_symm_apply] using hi)
    have hm' := Set.indicator_union_of_notMem_inter
      (s := {k | k ∈ M}) (t := {k | (finRotate (n + 1)).symm k ∈ M})
      (a := i) hm (fun _ => (1 : ℤ))
    have hn' := Set.indicator_union_of_notMem_inter
      (s := {k | k ∈ N}) (t := {k | (finRotate (n + 1)).symm k ∈ N})
      (a := i) hn (fun _ => (1 : ℤ))
    simp only [Set.indicator_apply, Set.mem_union, Set.mem_ofPred_eq] at hm' hn'
    rw [← hm', ← hn']
    exact if_congr (decide_eq_decide.1 (congrFun hinput i)) rfl rfl
  have hstep (i : Fin (n + 1)) : z (finRotate (n + 1) i) = -z i := by
    have hh := hinc (finRotate (n + 1) i)
    simp only [Equiv.symm_apply_apply] at hh
    dsimp only [z]
    linarith
  have hform (k : ℕ) (hk : k < n + 1) : z ⟨k, hk⟩ = (-1 : ℤ) ^ k * z 0 := by
    have ha : Function.Antiperiodic z (1 : Fin (n + 1)) := by
      intro i
      simpa only [finRotate_apply] using hstep i
    have hidx := @nsmul_one (Fin (n + 1)) (Fin.instAddMonoidWithOne (n + 1)) k
    simpa only [zero_add, hidx, Fin.natCast_eq_mk hk, zsmul_eq_mul,
      Int.cast_pow, Int.cast_neg, Int.cast_one] using ha.add_nsmul_eq (x := 0) k
  have hz : z 0 = 0 := by
    have hw := hstep (Fin.last n)
    rw [finRotate_last] at hw
    have he : z 0 = (-1 : ℤ) ^ (n + 1) * z 0 := by
      calc
        z 0 = -z (Fin.last n) := hw
        _ = -((-1 : ℤ) ^ n * z 0) := by
          change -z ⟨n, by omega⟩ = _
          rw [hform]
        _ = (-1 : ℤ) ^ (n + 1) * z 0 := by rw [pow_succ]; ring
    rw [hodd.neg_one_pow] at he
    linarith
  ext i
  have hi : z i = 0 := by rw [hform i.val i.isLt, hz, mul_zero]
  dsimp only [z] at hi
  by_cases hm : i ∈ M <;> by_cases hn : i ∈ N <;> simp [hm, hn] at hi ⊢


open Classical in
private lemma insert_avoiding (P : ℕ) (hP : 3 ≤ P) (j : Fin P)
    (N : Finset (Fin P)) (hN : N ∈ avoiding P j) :
    IsMatching P N ∧ IsMatching P (insert j N) ∧ j ∉ N ∧
      matchingInput P N j = false ∧ matchingInput P (insert j N) j = true := by
  classical
  obtain ⟨hmatch, hprev, hj, hnext⟩ := Finset.mem_filter.1 hN |>.2
  refine ⟨hmatch, ?_, hj, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · simpa only [Finset.mem_insert, not_or] using And.intro
        (D5.S0.Automata.TwoStateCertificateWidth.rotate_ne (m := P) (by omega) i) hnext
    · simp only [Finset.mem_insert, not_or]
      refine ⟨?_, hmatch i hi⟩
      intro heq
      have hieq : i = (finRotate P).symm j := (Equiv.eq_symm_apply (finRotate P)).2 heq
      exact hprev (hieq ▸ hi)
  · rw [matchingInput.eq_1]
    simp only [decide_eq_false_iff_not, not_or]
    exact ⟨hj, hprev⟩
  · simp only [matchingInput, Finset.mem_insert_self, true_or, decide_true]


open Classical in
private lemma avoiding_count (P : ℕ) (hP : 3 ≤ P) (j : Fin P) :
    (avoiding P j).card = Nat.fib (P - 1) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, P = n + 3 := Nat.exists_eq_add_of_le' hP
  let e : Fin n → Fin (n + 3) := fun k => j + ⟨k.val + 2, by omega⟩
  have einj : Function.Injective e := by
    intro k l hh
    have he : (⟨k.val + 2, by omega⟩ : Fin (n + 3)) = ⟨l.val + 2, by omega⟩ :=
      add_left_cancel hh
    have hv := congrArg Fin.val he
    exact Fin.ext (by simpa only [Fin.val_mk, Nat.add_right_cancel_iff] using hv)
  have enext (k l : Fin n) : finRotate (n + 3) (e k) = e l ↔ k.val + 1 = l.val := by
    rw [finRotate_apply]
    change (j + (⟨k.val + 2, by omega⟩ : Fin (n + 3))) + 1 =
      j + ⟨l.val + 2, by omega⟩ ↔ _
    rw [add_assoc, add_left_cancel_iff, Fin.ext_iff,
      Fin.val_add_one_of_lt' (by change k.val + 2 + 1 < n + 3; omega)]
    change k.val + 2 + 1 = l.val + 2 ↔ k.val + 1 = l.val
    omega
  have eavoid (k : Fin n) : e k ≠ (finRotate (n + 3)).symm j ∧
      e k ≠ j ∧ e k ≠ finRotate (n + 3) j := by
    refine ⟨?_, ?_, ?_⟩
    · intro hh
      rw [finRotate_symm_apply, sub_eq_add_neg] at hh
      have he : (⟨k.val + 2, by omega⟩ : Fin (n + 3)) = -1 := add_left_cancel hh
      have hv := congrArg Fin.val he
      simp only [Fin.coe_neg_one] at hv
      omega
    · intro hh
      have he : (⟨k.val + 2, by omega⟩ : Fin (n + 3)) = 0 :=
        add_left_cancel (hh.trans (add_zero j).symm)
      have hv := congrArg Fin.val he
      simp only [Fin.val_zero] at hv
      omega
    · intro hh
      rw [finRotate_apply] at hh
      have he : (⟨k.val + 2, by omega⟩ : Fin (n + 3)) = 1 := add_left_cancel hh
      have hv := congrArg Fin.val he
      simp only [Fin.val_one] at hv
      omega
  have represent (N : Finset (Fin (n + 3))) (hN : N ∈ avoiding (n + 3) j)
      (i : Fin (n + 3)) (hi : i ∈ N) : ∃ k, e k = i := by
    obtain ⟨_, hp, hj, hn⟩ := Finset.mem_filter.1 hN |>.2
    let q := i - j
    have hzero : q.val ≠ 0 := by
      intro hh
      have he : q = 0 := Fin.ext hh
      exact hj ((sub_eq_zero.1 he) ▸ hi)
    have hone : q.val ≠ 1 := by
      intro hh
      have he : q = 1 := Fin.ext (by simpa only [Fin.val_one] using hh)
      have heq : i = finRotate (n + 3) j := by
        rw [finRotate_apply]
        exact (sub_eq_iff_eq_add).1 he |>.trans (add_comm 1 j)
      exact hn (heq ▸ hi)
    have hlast : q.val ≠ n + 2 := by
      intro hh
      have he : q = -1 := Fin.ext (by simpa only [Fin.coe_neg_one] using hh)
      have heq : i = (finRotate (n + 3)).symm j := by
        rw [finRotate_symm_apply, sub_eq_add_neg]
        exact (sub_eq_iff_eq_add).1 he |>.trans (add_comm (-1) j)
      exact hp (heq ▸ hi)
    have hq := q.isLt
    let k : Fin n := ⟨q.val - 2, by omega⟩
    refine ⟨k, ?_⟩
    have he : (⟨k.val + 2, by omega⟩ : Fin (n + 3)) = q := Fin.ext (by dsimp [k]; omega)
    change j + (⟨k.val + 2, by omega⟩ : Fin (n + 3)) = i
    rw [he]
    dsimp only [q]
    exact add_sub_cancel _ _
  have reconstruct (N : Finset (Fin (n + 3))) (hN : N ∈ avoiding (n + 3) j) :
      N = (Finset.univ.filter (fun k => e k ∈ N)).image e := by
    rw [← Finset.filter_image (s := Finset.univ) (f := e) (p := fun i => i ∈ N),
      Finset.filter_mem_eq_inter]
    exact (Finset.inter_eq_right.mpr (by
      intro i hi
      obtain ⟨k, rfl⟩ := represent N hN i hi
      exact Finset.mem_image_of_mem _ (Finset.mem_univ k))).symm
  have valid (w : Fin n → Bool) (hw : Adm n w) :
      (Finset.univ.filter (fun k => w k = true)).image e ∈ avoiding (n + 3) j := by
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_, ?_⟩
    · intro i hi hnext
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨l, hl, he⟩ := Finset.mem_image.1 hnext
      have ha := (adm_iff_no_adjacent_true n w).1 hw k l ((enext k l).1 he.symm)
      have hktrue := (Finset.mem_filter.1 hk).2
      have hltrue := (Finset.mem_filter.1 hl).2
      rcases ha with ha | ha
      · exact Bool.false_ne_true (ha.symm.trans hktrue)
      · exact Bool.false_ne_true (ha.symm.trans hltrue)
    · intro hi
      obtain ⟨k, _, hk⟩ := Finset.mem_image.1 hi
      exact (eavoid k).1 hk
    · intro hi
      obtain ⟨k, _, hk⟩ := Finset.mem_image.1 hi
      exact (eavoid k).2.1 hk
    · intro hi
      obtain ⟨k, _, hk⟩ := Finset.mem_image.1 hi
      exact (eavoid k).2.2 hk
  have hcard : (avoiding (n + 3) j).card =
      (Finset.univ.filter (Adm n)).card := by
    apply Finset.card_bij (fun N _ => fun k => decide (e k ∈ N))
    · intro N hN
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _, (adm_iff_no_adjacent_true n _).2 ?_⟩
      intro k l hkl
      by_cases hk : e k ∈ N
      · right
        simp only [decide_eq_false_iff_not]
        intro hl
        have hm := (Finset.mem_filter.1 hN).2.1
        exact hm (e k) hk (((enext k l).2 hkl).symm ▸ hl)
      · left
        exact decide_eq_false hk
    · intro M hM N hN heq
      rw [reconstruct M hM, reconstruct N hN]
      congr 1
      apply Finset.filter_congr
      intro k _
      exact decide_eq_decide.1 (congrFun heq k)
    · intro w hw
      refine ⟨(Finset.univ.filter (fun k => w k = true)).image e,
        valid w (Finset.mem_filter.1 hw).2, ?_⟩
      funext k
      have hm : e k ∈ (Finset.univ.filter (fun l => w l = true)).image e ↔ w k = true := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
          (einj.mem_finset_image
            (s := Finset.univ.filter (fun l => w l = true)) (a := k))
      simp only [hm, Bool.decide_coe]
  calc
    (avoiding (n + 3) j).card = (Finset.univ.filter (Adm n)).card := hcard
    _ = Fintype.card {w : Fin n → Bool // Adm n w} := (Fintype.card_subtype _).symm
    _ = Nat.fib (n + 3 - 1) := by simpa using admissibleWord_card_eq_fib n


open Classical in
private lemma pairing_losses (P : ℕ) (hodd : Odd P) (hP : 3 ≤ P)
    (s : Fin P → Bool → Bool × Bool × Bool)
    (hlegal : locallyLegal P s) (hfixed : fixedMiddle P s)
    (j : Fin P) (hj : edgeCharge P s j = 1) :
    (avoiding P j).card ≤ (Finset.univ.filter (fun x => ¬ wins P s x)).card := by
  classical
  have hpair (N : Finset (Fin P)) (hN : N ∈ avoiding P j) :
      wins P s (matchingInput P N) → ¬ wins P s (matchingInput P (insert j N)) := by
    intro hw hwin
    obtain ⟨hm, hmj, hnot, _, _⟩ := insert_avoiding P hP j N hN
    have hz := (affine_matching_rule P s hlegal hfixed N hm).1 (hw.2.2 N hm rfl)
    have ho := (affine_matching_rule P s hlegal hfixed (insert j N) hmj).1
      (hwin.2.2 (insert j N) hmj rfl)
    rw [Finset.sum_insert hnot, hj] at ho
    have he : baseline P s + ∑ i ∈ N, edgeCharge P s i = 1 := by
      apply (CharTwo.add_eq_zero).1
      convert ho using 1
      ring
    rw [hz] at he
    exact zero_ne_one he
  let f : Finset (Fin P) → (Fin P → Bool) := fun N =>
    if wins P s (matchingInput P N) then matchingInput P (insert j N) else matchingInput P N
  apply Finset.card_le_card_of_injOn f
  · intro N hN
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp only [f]
    split_ifs with hw
    · exact hpair N hN hw
    · exact hw
  · intro M hM N hN heq
    obtain ⟨hm, hmj, hmnot, hmzero, hmone⟩ := insert_avoiding P hP j M hM
    obtain ⟨hn, hnj, hnnot, hnzero, hnone⟩ := insert_avoiding P hP j N hN
    dsimp only [f] at heq
    split_ifs at heq with hwM hwN hwN
    · have he := matching_input_injective P hodd hP (insert j M) (insert j N) hmj hnj heq
      have herase := congrArg (fun K : Finset (Fin P) => K.erase j) he
      simpa only [Finset.erase_insert hmnot, Finset.erase_insert hnnot] using herase
    · have he := congrFun heq j
      rw [hmone, hnzero] at he
      exact Bool.noConfusion he
    · have he := congrFun heq j
      rw [hmzero, hnone] at he
      exact Bool.noConfusion he
    · exact matching_input_injective P hodd hP M N hm hn heq


open Classical in
private lemma deterministic_losses (P : ℕ) (hodd : Odd P) (hP : 3 ≤ P)
    (s : Fin P → Bool → Bool × Bool × Bool) :
    Nat.fib (P - 1) ≤ (Finset.univ.filter (fun x => ¬ wins P s x)).card := by
  classical
  by_cases hlegal : locallyLegal P s
  · by_cases hfixed : fixedMiddle P s
    · by_cases heven : (∑ i, ((s i false).2.1.toNat : ZMod 2)) = 0
      · obtain ⟨j, hj⟩ := marked_edge P hodd s heven
        rw [← avoiding_count P hP j]
        exact pairing_losses P hodd hP s hlegal hfixed j hj
      · rw [odd_middle_all P s hfixed heven]
        exact (D5.S3.Arith.Robin.FibonacciRankEulerTail.fibonacci_lt_two_pow (P - 1)).le.trans
          (Nat.pow_le_pow_right (by decide) (by omega))
    · exact (D5.S3.Arith.Robin.FibonacciRankEulerTail.fibonacci_lt_two_pow (P - 1)).le.trans
        (varying_middle_half P hP s hfixed)
  · exact (D5.S3.Arith.Robin.FibonacciRankEulerTail.fibonacci_lt_two_pow (P - 1)).le.trans
      (local_violation_half P s hlegal)

open Classical in
private lemma deterministic_bound (P : ℕ) (hodd : Odd P) (hP : 3 ≤ P)
    (s : Fin P → Bool → Bool × Bool × Bool) :
    ((Finset.univ.filter (wins P s)).card : ℝ) / 2 ^ P ≤
      1 - (Nat.fib (P - 1) : ℝ) / 2 ^ P := by
  classical
  have hloss := deterministic_losses P hodd hP s
  have htotal := Finset.card_filter_add_card_filter_not (s :=
    (Finset.univ : Finset (Fin P → Bool))) (wins P s)
  have hcard : (Finset.univ.filter (wins P s)).card + Nat.fib (P - 1) ≤ 2 ^ P := by
    simpa using (Nat.add_le_add_left hloss (Finset.univ.filter (wins P s)).card).trans_eq
      htotal
  have hreal : ((Finset.univ.filter (wins P s)).card : ℝ) + (Nat.fib (P - 1) : ℝ) ≤
      2 ^ P := by exact_mod_cast hcard
  have hden : (0 : ℝ) < 2 ^ P := by positivity
  apply (div_le_iff₀ hden).2
  field_simp
  linarith

open Classical in
private lemma attaining_charges (P : ℕ) (hodd : Odd P) (hP : 3 ≤ P) :
    locallyLegal P (attainingStrategy P) ∧ fixedMiddle P (attainingStrategy P) ∧
    (∑ i, ((attainingStrategy P i false).2.1.toNat : ZMod 2)) = 0 ∧
    baseline P (attainingStrategy P) = 0 ∧
    ∃ j : Fin P, ∀ i, edgeCharge P (attainingStrategy P) i = if i = j then 1 else 0 := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, P = n + 3 := Nat.exists_eq_add_of_le' hP
  let j : Fin (n + 3) := Fin.last (n + 2)
  have hlt (i : Fin (n + 3)) : i.val + 1 < n + 3 ↔ i ≠ j := by
    simpa only [j, Fin.lt_def, Fin.val_last, Nat.lt_succ_iff, Nat.succ_le_iff] using
      (Fin.lt_last_iff_ne_last (a := i))
  have hzero (i : Fin (n + 3)) : attainingStrategy (n + 3) i false =
      if i = j then (false, false, false) else (true, true, false) := by
    rw [attainingStrategy.eq_1]
    simp only [hlt]
    by_cases hi : i = j <;> simp [hi]
  have hone (i : Fin (n + 3)) : attainingStrategy (n + 3) i true =
      if i = j then (true, false, true) else (true, true, false) := by
    simp only [attainingStrategy, hlt]
    by_cases hi : i = j <;> simp [hi]
  have hpoint (i : Fin (n + 3)) : ((attainingStrategy (n + 3) i false).1.toNat : ZMod 2) =
      if i = j then 0 else 1 := by
    rw [hzero]
    split_ifs <;> rfl
  have hnum : ((n + 2 : ℕ) : ZMod 2) = 0 := by
    have hh := hodd.natCast_zmod_two
    rw [show n + 3 = (n + 2) + 1 from rfl, Nat.cast_add, Nat.cast_one] at hh
    exact add_right_cancel (hh.trans (zero_add (1 : ZMod 2)).symm)
  have hbase : baseline (n + 3) (attainingStrategy (n + 3)) = 0 := by
    change (∑ i, ((attainingStrategy (n + 3) i false).1.toNat : ZMod 2)) = 0
    simp only [hpoint, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
      nsmul_eq_mul, mul_one, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin]
    exact hnum
  refine ⟨?_, ?_, ?_, hbase, j, ?_⟩
  · intro i x
    cases x
    · rw [hzero]
      split_ifs <;> decide
    · rw [hone]
      split_ifs <;> decide
  · intro i
    rw [hzero, hone]
    split_ifs <;> rfl
  · convert hbase using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hzero]
    split_ifs <;> rfl
  · intro i
    by_cases hi : i = j
    · subst i
      have hr : finRotate (n + 3) j = 0 := finRotate_last
      have hz : (0 : Fin (n + 3)) ≠ j := Fin.ne_of_lt (Fin.last_pos' (n := n + 2))
      rw [edgeCharge.eq_1]
      simp only [hzero, hone, hr, ite_true, ite_eq_right hz,
        Bool.toNat_true, Bool.toNat_false, Nat.cast_one, Nat.cast_zero, add_zero]
      decide
    · by_cases hn : finRotate (n + 3) i = j <;>
        simp only [edgeCharge, hzero, hone, hi, hn, ite_true, ite_false, Bool.toNat_true,
          Bool.toNat_false, Nat.cast_one, Nat.cast_zero,
          add_zero] <;> decide


open Classical in
private lemma attaining_losses (P : ℕ) (hodd : Odd P) (hP : 3 ≤ P) :
    (Finset.univ.filter (fun x => ¬ wins P (attainingStrategy P) x)).card ≤
      Nat.fib (P - 1) := by
  classical
  obtain ⟨hlegal, hfixed, heven, hbase, j, hcharge⟩ := attaining_charges P hodd hP
  have hsub : Finset.univ.filter (fun x => ¬ wins P (attainingStrategy P) x) ⊆
      (avoiding P j).image (fun N => matchingInput P (insert j N)) := by
    intro x hx
    have hloss := (Finset.mem_filter.1 hx).2
    have hmiddle : (∑ i, ((attainingStrategy P i (x i)).2.1.toNat : ZMod 2)) = 0 := by
      convert heven using 1
      apply Finset.sum_congr rfl
      intro i _
      cases hbit : x i
      · rfl
      · exact congrArg (fun b : Bool => (b.toNat : ZMod 2)) (hfixed i).symm
    have hbad : ∃ M, IsMatching P M ∧ matchingInput P M = x ∧ j ∈ M := by
      by_contra hnone
      apply hloss
      refine ⟨fun i => hlegal i (x i), hmiddle, ?_⟩
      intro M hM hinput
      apply (affine_matching_rule P (attainingStrategy P) hlegal hfixed M hM).2
      rw [hbase, zero_add]
      have hjnot : j ∉ M := fun hj => hnone ⟨M, hM, hinput, hj⟩
      apply Finset.sum_eq_zero
      intro i hi
      rw [hcharge]
      exact ite_eq_right (fun hij : i = j => hjnot (hij ▸ hi))
    obtain ⟨M, hM, hinput, hj⟩ := hbad
    have hN : M.erase j ∈ avoiding P j := by
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _, ?_, ?_, Finset.notMem_erase j M, ?_⟩
      · intro i hi hnext
        exact hM i (Finset.mem_of_mem_erase hi) (Finset.mem_of_mem_erase hnext)
      · intro hp
        exact hM ((finRotate P).symm j) (Finset.mem_of_mem_erase hp)
          (by simpa only [Equiv.apply_symm_apply] using hj)
      · intro hn
        exact hM j hj (Finset.mem_of_mem_erase hn)
    apply Finset.mem_image.2
    refine ⟨M.erase j, hN, ?_⟩
    rw [Finset.insert_erase hj]
    exact hinput
  calc
    (Finset.univ.filter (fun x => ¬ wins P (attainingStrategy P) x)).card ≤
        ((avoiding P j).image (fun N => matchingInput P (insert j N))).card :=
      Finset.card_le_card hsub
    _ ≤ (avoiding P j).card := Finset.card_image_le
    _ = Nat.fib (P - 1) := avoiding_count P hP j

open Classical in
private lemma attainment (P : ℕ) (hodd : Odd P) (hP : 3 ≤ P) :
    ((Finset.univ.filter (wins P (attainingStrategy P))).card : ℝ) / 2 ^ P =
      1 - (Nat.fib (P - 1) : ℝ) / 2 ^ P := by
  classical
  have hlower := deterministic_losses P hodd hP (attainingStrategy P)
  have hupper := attaining_losses P hodd hP
  have heq := Nat.le_antisymm hupper hlower
  have htotal := Finset.card_filter_add_card_filter_not (s :=
    (Finset.univ : Finset (Fin P → Bool))) (wins P (attainingStrategy P))
  rw [heq] at htotal
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at htotal
  have hreal : ((Finset.univ.filter (wins P (attainingStrategy P))).card : ℝ) +
      (Nat.fib (P - 1) : ℝ) = 2 ^ P := by exact_mod_cast htotal
  have hden : (2 : ℝ) ^ P ≠ 0 := by positivity
  apply (div_eq_iff hden).2
  field_simp
  linarith

open Classical in
private lemma mixture_bound (P : ℕ) (hodd : Odd P) (hP : 3 ≤ P)
    (μ : (Fin P → Bool → Bool × Bool × Bool) → ℝ)
    (hpos : ∀ s, 0 ≤ μ s) (hnorm : ∑ s, μ s = 1) :
    winProbability P μ ≤ 1 - (Nat.fib (P - 1) : ℝ) / 2 ^ P := by
  classical
  simpa only [winProbability.eq_1, mul_div_assoc, mul_comm] using
    (D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Fourier.weighted_edge_bound
      μ (fun s => ((Finset.univ.filter (wins P s)).card : ℝ) / 2 ^ P)
      (1 - (Nat.fib (P - 1) : ℝ) / 2 ^ P) hpos hnorm
      (deterministic_bound P hodd hP)).1

theorem result : claim := by
  classical
  intro P hodd hP
  exact ⟨fun μ hpos hnorm => mixture_bound P hodd hP μ hpos hnorm,
    ⟨attainingStrategy P, attainment P hodd hP⟩⟩

end D5.S3.QuantumBounds.PolygonGameClassicalValue
