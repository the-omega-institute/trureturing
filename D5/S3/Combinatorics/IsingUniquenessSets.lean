/- GID: D5/S3/Combinatorics/IsingUniquenessSets
   generality: G
   mirror-B: D5/B/S3/Combinatorics/IsingUniquenessSets
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: No set of uniqueness for the Ising cone on the k-cube has at most k points; for k ≥ 3 the smallest has k + 1. -/

/-
proof_shape: result: content
escape_witness: form (2) — squares of affine functions of the Rademacher coordinates lie in
  B^k_2, so a kernel vector of the evaluation map on at most k points yields a nonzero
  nonnegative function vanishing there (the local `lower_bound` inside `result`)
admission_basis: open-problem-resolution (issue #10022)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

open scoped BigOperators

namespace D5.S3.Combinatorics.IsingUniquenessSets

/-- The coordinate value in `{-1, +1}`: `true ↦ +1`, `false ↦ -1`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The Walsh function `w_L(x) = ∏_{j ∈ L} x_j` on `X = {-1, +1}^k`. -/
def walsh {k : ℕ} (L : Finset (Fin k)) (x : Fin k → Bool) : ℝ := ∏ j ∈ L, sgn (x j)

/-- `B^k_q = Lin{w_L : L ⊆ {1, …, k}, |L| ≤ q}`. -/
def walshSpace (k q : ℕ) : Submodule ℝ ((Fin k → Bool) → ℝ) :=
  Submodule.span ℝ {f | ∃ L : Finset (Fin k), L.card ≤ q ∧ f = walsh L}

/-- `U` is a set of uniqueness for `(B^k_q)_+`: the only nonnegative function of `B^k_q`
vanishing on `U` is zero. -/
def IsSetOfUniqueness (k q : ℕ) (U : Finset (Fin k → Bool)) : Prop :=
  ∀ φ ∈ walshSpace k q, (∀ x, 0 ≤ φ x) → (∀ x ∈ U, φ x = 0) → φ = 0

/-- `u(k, q)`: the size of the smallest set of uniqueness for `(B^k_q)_+`. -/
noncomputable def minUniqueness (k q : ℕ) : ℕ :=
  sInf {n | ∃ U : Finset (Fin k → Bool), U.card = n ∧ IsSetOfUniqueness k q U}

/-- The conjecture `u(k, 2) = k + 1` of arXiv:2511.20925: no set of uniqueness for the Ising
cone has at most `k` points, `u(k, 2) = k + 1` for `k ≥ 3`, and the printed edge `k = 2`
where `B^2_2` is the whole function space and `u(2, 2) = 4`. -/
def claim : Prop :=
  (∀ k : ℕ, ∀ U : Finset (Fin k → Bool), IsSetOfUniqueness k 2 U → k + 1 ≤ U.card) ∧
    (∀ k : ℕ, 3 ≤ k → minUniqueness k 2 = k + 1) ∧ minUniqueness 2 2 = 4

/-- The point with the single coordinate `m` equal to `+1`. -/
private def oneUp {k : ℕ} (m : Fin k) : Fin k → Bool := fun j => decide (j = m)

/-- The point with the single coordinate `m` equal to `-1`. -/
private def oneDown {k : ℕ} (m : Fin k) : Fin k → Bool := fun j => !decide (j = m)

/-- The `k + 1` points `W_1 ∪ {(+1, …, +1)}` of Lemma rem:three. -/
private def upSet (k : ℕ) : Finset (Fin k → Bool) :=
  insert (fun _ => true) (Finset.univ.image oneUp)

/-- `u(k, 2) = k + 1` fails only at the printed edge `k = 2`; the conjecture's content, that no
set of uniqueness has at most `k` points, holds for every `k`. -/
theorem result : claim := by
  have sgn_sq (b : Bool) : sgn b * sgn b = 1 := by
    cases b <;> norm_num [sgn]
  have walsh_mem {k q : ℕ} (L : Finset (Fin k)) (hL : L.card ≤ q) :
      walsh L ∈ walshSpace k q :=
    Submodule.subset_span ⟨L, hL, rfl⟩
  have walsh_empty {k : ℕ} : walsh (∅ : Finset (Fin k)) = fun _ => 1 := by
    funext x
    simp [walsh]
  have walsh_single {k : ℕ} (i : Fin k) : walsh {i} = fun x => sgn (x i) := by
    funext x
    simp [walsh]
  have walsh_pair {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
      walsh {i, j} = fun x => sgn (x i) * sgn (x j) := by
    funext x
    simp [walsh, Finset.prod_pair hij]
  have sgn_mul_mem {k : ℕ} (i j : Fin k) :
      (fun x : Fin k → Bool => sgn (x i) * sgn (x j)) ∈ walshSpace k 2 := by
    by_cases hij : i = j
    · subst hij
      have h : (fun x : Fin k → Bool => sgn (x i) * sgn (x i)) = walsh ∅ := by
        rw [walsh_empty]
        funext x
        exact sgn_sq _
      rw [h]
      exact walsh_mem _ (by simp)
    · rw [← walsh_pair hij]
      exact walsh_mem _ (by rw [Finset.card_pair hij])
  have lower_bound (k : ℕ) (U : Finset (Fin k → Bool)) (hU : IsSetOfUniqueness k 2 U) :
      k + 1 ≤ U.card := by
    classical
    by_contra hlt
    push Not at hlt
    -- the evaluation map v ↦ (v₀ + Σ vᵢ uᵢ)_{u ∈ U} has a nonzero kernel vector
    let M : Matrix U (Option (Fin k)) ℝ := fun u o => match o with
      | none => 1
      | some i => sgn (u.1 i)
    have hdim : Module.finrank ℝ (U → ℝ) < Module.finrank ℝ (Option (Fin k) → ℝ) := by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_option,
        Fintype.card_fin]
      omega
    obtain ⟨v, hvker, hv0⟩ :=
      (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := M.mulVecLin) hdim)
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hvker
    let a : (Fin k → Bool) → ℝ := fun x => v none + ∑ i, v (some i) * sgn (x i)
    have haU : ∀ u ∈ U, a u = 0 := by
      intro u hu
      have := congrFun hvker ⟨u, hu⟩
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, Pi.zero_apply] at this
      simpa [a, M, mul_comm] using this
    let φ : (Fin k → Bool) → ℝ := fun x => a x ^ 2
    have hφmem : φ ∈ walshSpace k 2 := by
      have hexp : φ = (v none ^ 2) • walsh ∅ +
          ∑ i, (2 * v none * v (some i)) • walsh {i} +
          ∑ i, ∑ j, (v (some i) * v (some j)) •
            (fun x : Fin k → Bool => sgn (x i) * sgn (x j)) := by
        funext x
        simp only [φ, a, walsh_empty, walsh_single, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Finset.sum_apply]
        rw [add_sq, sq (∑ i, v (some i) * sgn (x i)), Finset.sum_mul_sum, Finset.mul_sum, mul_one]
        congr 1
        · congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
      rw [hexp]
      refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
      · exact Submodule.smul_mem _ _ (walsh_mem _ (by simp))
      · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (walsh_mem _ (by simp))
      · exact Submodule.sum_mem _ fun i _ =>
          Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (sgn_mul_mem i j)
    have hφ0 : φ = 0 := hU φ hφmem (fun x => sq_nonneg _) (fun u hu => by simp [φ, haU u hu])
    have ha0 : ∀ x, a x = 0 := fun x => by
      have := congrFun hφ0 x
      simpa [φ] using this
    apply hv0
    have hsome : ∀ i, v (some i) = 0 := by
      intro i
      have h1 := ha0 (fun _ => true)
      have h2 := ha0 (Function.update (fun _ => true) i false)
      have hsplit : ∀ y : Fin k → Bool, (∑ j, v (some j) * sgn (y j)) =
          v (some i) * sgn (y i) + ∑ j ∈ Finset.univ.erase i, v (some j) * sgn (y j) := by
        intro y
        exact (Finset.add_sum_erase Finset.univ (fun j => v (some j) * sgn (y j))
          (Finset.mem_univ i)).symm
      simp only [a] at h1 h2
      rw [hsplit] at h1 h2
      have hrest : (∑ j ∈ Finset.univ.erase i, v (some j) *
          sgn (Function.update (fun _ => true) i false j)) =
          ∑ j ∈ Finset.univ.erase i, v (some j) * sgn true := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hrest] at h2
      simp only [Function.update_self] at h2
      norm_num [sgn] at h1 h2
      linarith
    funext o
    cases o with
    | none =>
      have h1 := ha0 (fun _ => true)
      simp only [a, hsome, zero_mul, Finset.sum_const_zero, add_zero] at h1
      simpa using h1
    | some i => simpa using hsome i
  have sgn_not (b : Bool) : sgn (!b) = -sgn b := by
    cases b <;> norm_num [sgn]
  have sgn_decide (p : Prop) [Decidable p] :
      sgn (decide p) = 2 * (if p then 1 else 0) - 1 := by
    by_cases hp : p <;> norm_num [sgn, hp]
  have sum_odd_flip {k : ℕ} (i : Fin k) (g : (Fin k → Bool) → ℝ)
      (hg : ∀ x, g (Function.update x i (!x i)) = -g x) : ∑ x, g x = 0 := by
    have hinv : Function.Involutive fun x : Fin k → Bool => Function.update x i (!x i) := by
      intro x
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Function.update_of_ne hj]
    have h := Equiv.sum_comp hinv.toPerm g
    simp only [Function.Involutive.coe_toPerm, hg, Finset.sum_neg_distrib] at h
    linarith
  have walsh_identities {k : ℕ} (φ : (Fin k → Bool) → ℝ) (hφ : φ ∈ walshSpace k 2) :
      (∑ m, φ (oneDown m) - ∑ m, φ (oneUp m) +
          ((k : ℝ) - 2) * (φ (fun _ => false) - φ (fun _ => true)) = 0) ∧
        (∑ m, φ (oneUp m) + ∑ m, φ (oneDown m) -
          ((k : ℝ) - 4) * (φ (fun _ => true) + φ (fun _ => false)) -
            8 / 2 ^ k * ∑ x, φ x = 0) := by
    classical
    have hsum1 : ∀ i : Fin k, (∑ m : Fin k, sgn (oneUp m i)) = 2 - k := by
      intro i
      simp only [oneUp, sgn_decide, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
    have hsum2 : ∀ i : Fin k, (∑ m : Fin k, sgn (oneDown m i)) = k - 2 := by
      intro i
      simp only [oneDown, sgn_not, sgn_decide, Finset.sum_neg_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      ring
    have hprod : ∀ i j : Fin k, i ≠ j →
        (∑ m : Fin k, (2 * (if i = m then (1 : ℝ) else 0) - 1) *
          (2 * (if j = m then (1 : ℝ) else 0) - 1)) = k - 4 := by
      intro i j hij
      have hcross : ∀ m : Fin k,
          (if i = m then (1 : ℝ) else 0) * (if j = m then (1 : ℝ) else 0) = 0 := by
        intro m
        by_cases him : i = m
        · subst him
          simp [Ne.symm hij]
        · simp [him]
      have hexp : ∀ m : Fin k, (2 * (if i = m then (1 : ℝ) else 0) - 1) *
          (2 * (if j = m then (1 : ℝ) else 0) - 1) =
          4 * ((if i = m then (1 : ℝ) else 0) * (if j = m then (1 : ℝ) else 0)) -
            2 * (if i = m then (1 : ℝ) else 0) - 2 * (if j = m then (1 : ℝ) else 0) + 1 := by
        intro m
        ring
      simp only [hexp, hcross, mul_zero, zero_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      ring
    have hsum3 : ∀ i j : Fin k, i ≠ j →
        (∑ m : Fin k, sgn (oneUp m i) * sgn (oneUp m j)) = k - 4 := by
      intro i j hij
      simp only [oneUp, sgn_decide]
      exact hprod i j hij
    have hsum4 : ∀ i j : Fin k, i ≠ j →
        (∑ m : Fin k, sgn (oneDown m i) * sgn (oneDown m j)) = k - 4 := by
      intro i j hij
      simp only [oneDown, sgn_not, sgn_decide, neg_mul_neg]
      exact hprod i j hij
    have hcube1 : ∀ i : Fin k, (∑ x : Fin k → Bool, sgn (x i)) = 0 := by
      intro i
      exact sum_odd_flip i _ fun x => by simp [sgn_not]
    have hcube2 : ∀ i j : Fin k, i ≠ j → (∑ x : Fin k → Bool, sgn (x i) * sgn (x j)) = 0 := by
      intro i j hij
      exact sum_odd_flip i _ fun x => by
        simp [sgn_not, Function.update_of_ne (Ne.symm hij)]
    have hcard : (∑ _x : Fin k → Bool, (1 : ℝ)) = 2 ^ k := by
      simp [Finset.card_univ, Fintype.card_bool]
    have htwo : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
    induction hφ using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨L, hL, rfl⟩ := hf
      rcases Nat.lt_or_ge L.card 2 with hlt | hge
      · rcases Nat.lt_or_ge L.card 1 with h0 | h1
        · have hL0 : L = ∅ := Finset.card_eq_zero.1 (show L.card = 0 by omega)
          subst hL0
          simp only [walsh_empty, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_one, hcard]
          constructor
          · ring
          · field_simp
            ring
        · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 (show L.card = 1 by omega)
          simp only [walsh_single, hsum1, hsum2, hcube1]
          norm_num [sgn]
          ring
      · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 (show L.card = 2 by omega)
        simp only [walsh_pair hij, hsum3 i j hij, hsum4 i j hij, hcube2 i j hij]
        norm_num [sgn]
        ring
    | zero => simp
    | add f g _ _ hf hg =>
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      constructor
      · linear_combination hf.1 + hg.1
      · linear_combination hf.2 + hg.2
    | smul c f _ hf =>
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      constructor
      · linear_combination c * hf.1
      · linear_combination c * hf.2
  have upSet_card (k : ℕ) (hk : 2 ≤ k) : (upSet k).card = k + 1 := by
    classical
    have hinj : Function.Injective (oneUp : Fin k → Fin k → Bool) := by
      intro m m' h
      have := congrFun h m
      simpa [oneUp, eq_comm] using this
    have hnot : (fun _ : Fin k => true) ∉ Finset.univ.image oneUp := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      intro m h
      obtain ⟨j, hj⟩ : ∃ j : Fin k, j ≠ m := by
        by_cases hm : m.val = 0
        · exact ⟨⟨1, by omega⟩, fun e => by simp [Fin.ext_iff] at e; omega⟩
        · exact ⟨⟨0, by omega⟩, fun e => by simp [Fin.ext_iff] at e; omega⟩
      have := congrFun h j
      simp [oneUp, hj] at this
    rw [upSet, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj,
      Finset.card_univ, Fintype.card_fin]
  have upper_bound (k : ℕ) (hk : 3 ≤ k) : IsSetOfUniqueness k 2 (upSet k) := by
    classical
    intro φ hφ hnn hU
    obtain ⟨h1, h2⟩ := walsh_identities φ hφ
    have hup : ∀ m, φ (oneUp m) = 0 := fun m =>
      hU _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ m)))
    have hall : φ (fun _ => true) = 0 := hU _ (Finset.mem_insert_self _ _)
    simp only [hup, hall, Finset.sum_const_zero, sub_zero] at h1 h2
    have hk2 : (0 : ℝ) < (k : ℝ) - 2 := by
      have : (3 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hdown_nn : 0 ≤ ∑ m, φ (oneDown m) := Finset.sum_nonneg fun m _ => hnn _
    have hall' := hnn (fun _ => false)
    have hd0 : φ (fun _ => false) = 0 := by nlinarith
    have hsd : ∑ m, φ (oneDown m) = 0 := by nlinarith
    rw [hsd, hd0] at h2
    have htot : ∑ x, φ x = 0 := by
      have hpos : (0 : ℝ) < 8 / 2 ^ k := by positivity
      nlinarith
    funext x
    exact (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hnn y).1 htot x (Finset.mem_univ x)
  have two_two_univ (U : Finset (Fin 2 → Bool)) (hU : IsSetOfUniqueness 2 2 U) :
      U = Finset.univ := by
    classical
    by_contra hne
    obtain ⟨y, hyU⟩ : ∃ y, y ∉ U := by
      by_contra h
      push Not at h
      exact hne (Finset.eq_univ_iff_forall.2 h)
    let δ : (Fin 2 → Bool) → ℝ := fun x =>
      (1 + sgn (y 0) * sgn (x 0)) / 2 * ((1 + sgn (y 1) * sgn (x 1)) / 2)
    have hδmem : δ ∈ walshSpace 2 2 := by
      have hexp : δ = (1 / 4 : ℝ) • walsh ∅ + (sgn (y 0) / 4) • walsh {0} +
          (sgn (y 1) / 4) • walsh {1} + (sgn (y 0) * sgn (y 1) / 4) • walsh {0, 1} := by
        funext x
        simp only [δ, walsh_empty, walsh_single, walsh_pair (show (0 : Fin 2) ≠ 1 by decide),
          Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hexp]
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
        exact Submodule.smul_mem _ _ (walsh_mem _ (by decide))
    have hfac : ∀ a b : Bool, 0 ≤ (1 + sgn a * sgn b) / 2 := by
      intro a b
      cases a <;> cases b <;> norm_num [sgn]
    have hδnn : ∀ x, 0 ≤ δ x := fun x => mul_nonneg (hfac _ _) (hfac _ _)
    have hδU : ∀ x ∈ U, δ x = 0 := by
      intro x hx
      have hxy : x ≠ y := fun h => hyU (h ▸ hx)
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
        by_contra h
        push Not at h
        exact hxy (funext h)
      have hzero : ∀ a b : Bool, a ≠ b → (1 + sgn b * sgn a) / 2 = 0 := by
        intro a b hab
        cases a <;> cases b <;> simp_all [sgn]
      obtain rfl | rfl : j = 0 ∨ j = 1 := by
        fin_cases j <;> simp
      · simp only [δ]
        rw [hzero _ _ hj, zero_mul]
      · simp only [δ]
        rw [hzero _ _ hj, mul_zero]
    have hδ0 := congrFun (hU δ hδmem hδnn hδU) y
    have hδy : δ y = 1 := by
      simp only [δ]
      cases y 0 <;> cases y 1 <;> norm_num [sgn]
    rw [hδy] at hδ0
    norm_num at hδ0
  classical
  refine ⟨lower_bound, ?_, ?_⟩
  · intro k hk
    unfold minUniqueness
    apply le_antisymm
    · exact Nat.sInf_le ⟨upSet k, upSet_card k (by omega), upper_bound k hk⟩
    · exact le_csInf ⟨_, upSet k, upSet_card k (by omega), upper_bound k hk⟩
        fun n ⟨U, hUc, hU⟩ => hUc ▸ lower_bound k U hU
  · unfold minUniqueness
    have huniv : IsSetOfUniqueness 2 2 Finset.univ := by
      intro φ _ _ hU
      funext x
      exact hU x (Finset.mem_univ x)
    have hcard : (Finset.univ : Finset (Fin 2 → Bool)).card = 4 := by
      simp [Finset.card_univ, Fintype.card_bool]
    apply le_antisymm
    · exact Nat.sInf_le ⟨Finset.univ, hcard, huniv⟩
    · exact le_csInf ⟨_, Finset.univ, hcard, huniv⟩
        fun n ⟨U, hUc, hU⟩ => by rw [← hUc, two_two_univ U hU, hcard]

#print axioms result

end D5.S3.Combinatorics.IsingUniquenessSets
