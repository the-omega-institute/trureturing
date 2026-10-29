/- GID: D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The linear span of binary bond-two uniform matrix product states. -/

import D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoTraceWords

/-! The source tensor span and the weighted invariant monomial count. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan

open scoped BigOperators Matrix
open UniformMPSExpectedDimensionRefutation (traceWord uMPS)

noncomputable section

/-- De Lazzari–Motwani–Seynnaeve Conjecture 3.8, for positive word lengths. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (Module.finrank ℂ (Submodule.span ℂ (uMPS 2 2 n)) : ℚ) =
      if Even n then ((n : ℚ) ^ 4 - 4 * n ^ 2 + 192 * n + 192) / 192
      else ((n : ℚ) ^ 4 - 10 * n ^ 2 + 192 * n + 201) / 192

private abbrev extraIndex (n : ℕ) :=
  {e : Fin 5 → Fin (n + 1) //
        (e 0).val + (e 1).val + 2 * (e 2).val + 2 * (e 3).val + 2 * (e 4).val + 4 = n}

private lemma evaluation_bridge (n : ℕ) :
    Module.finrank ℂ (Submodule.span ℂ (uMPS 2 2 n)) =
      Module.finrank ℂ (Submodule.span ℂ (Set.range fun i : Fin n → Fin 2 =>
        fun p : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ => traceWord 2 2 n p i)) := by
  classical
  let c := Submodule.span ℂ (Set.range fun i : Fin n → Fin 2 =>
    fun p : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ => traceWord 2 2 n p i)
  let v := (Fin n → Fin 2) → ℂ
  let s : Submodule ℂ v := Submodule.span ℂ (uMPS 2 2 n)
  let r : Module.Dual ℂ v →ₗ[ℂ] ((Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) → ℂ) :=
    { toFun := fun f p => f (traceWord 2 2 n p)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hrange : LinearMap.range r = c := by
    apply le_antisymm
    · rintro _ ⟨f, rfl⟩
      have heq : r f = ∑ i : Fin n → Fin 2,
          f (Pi.single i 1) • (fun p => traceWord 2 2 n p i) := by
        funext p
        have h := (Pi.basisFun ℂ (Fin n → Fin 2)).sum_repr (traceWord 2 2 n p)
        simp only [Pi.basisFun_repr, Pi.basisFun_apply] at h
        change f (traceWord 2 2 n p) = _
        rw [← h, map_sum]
        simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
      rw [heq]
      apply (c).sum_mem
      intro i _
      exact (c).smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨LinearMap.proj i, rfl⟩
  have hker : LinearMap.ker r = s.dualAnnihilator := by
    ext f
    change (fun p => f (traceWord 2 2 n p)) = 0 ↔ f ∈ s.dualAnnihilator
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro hf w hw
      have hs : s ≤ LinearMap.ker f := by
        apply Submodule.span_le.mpr
        rintro _ ⟨p, rfl⟩
        exact congrFun hf p
      exact hs hw
    · intro hf
      funext p
      exact hf _ (Submodule.subset_span ⟨p, rfl⟩)
  have h1 := r.finrank_range_add_finrank_ker
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq s
  rw [hrange, hker, Subspace.dual_finrank_eq] at h1
  change Module.finrank ℂ s = Module.finrank ℂ (c)
  omega

private def weight (e : Fin 5 → ℕ) : ℕ :=
  e 0 + e 1 + 2 * e 2 + 2 * e 3 + 2 * e 4

private abbrev weighted (n : ℕ) := {e : Fin 5 → ℕ // weight e + 4 = n}
private abbrev compositions (k : ℕ) := {e : Fin 5 → ℕ // ∑ j, e j = k}

private lemma weight_bound (e : Fin 5 → ℕ) (j : Fin 5) : e j ≤ weight e := by
  fin_cases j
  · change e 0 ≤ e 0 + e 1 + 2 * e 2 + 2 * e 3 + 2 * e 4; omega
  · change e 1 ≤ e 0 + e 1 + 2 * e 2 + 2 * e 3 + 2 * e 4; omega
  · change e 2 ≤ e 0 + e 1 + 2 * e 2 + 2 * e 3 + 2 * e 4; omega
  · change e 3 ≤ e 0 + e 1 + 2 * e 2 + 2 * e 3 + 2 * e 4; omega
  · change e 4 ≤ e 0 + e 1 + 2 * e 2 + 2 * e 3 + 2 * e 4; omega

private def index_unbounded (n : ℕ) : extraIndex n ≃ weighted n where
  toFun e := ⟨(fun j => (e.val j).val), e.property⟩
  invFun e := ⟨(fun j => ⟨e.val j, by
    have h := weight_bound e.val j
    have he := e.property
    omega⟩),
    e.property⟩
  left_inv e := rfl
  right_inv e := rfl

private lemma compositions_card (k : ℕ) :
    (Nat.card (compositions k) : ℚ) =
      ((k : ℚ) + 1) * (k + 2) * (k + 3) * (k + 4) / 24 := by
  have hc := Nat.card_congr (Sym.equivNatSumOfFintype (Fin 5) k)
  rw [Sym.natCard_sym_eq_choose, Nat.card_fin] at hc
  have he : 5 + k - 1 = k + 4 := by omega
  rw [he, ← Nat.choose_symm (by omega : k ≤ k + 4)] at hc
  have hsub : k + 4 - k = 4 := by omega
  rw [hsub] at hc
  rw [← hc]
  have h := Nat.descFactorial_eq_factorial_mul_choose (k + 4) 4
  have h1 : k + 4 - 1 = k + 3 := by omega
  have h2 : k + 4 - 2 = k + 2 := by omega
  have h3 : k + 4 - 3 = k + 1 := by omega
  norm_num only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
    h1, h2, h3, Nat.factorial] at h
  have hq := congrArg (fun a : ℕ => (a : ℚ)) h
  push_cast at hq ⊢
  linear_combination -hq / 24

private def halfExponents (e : Fin 5 → ℕ) : Fin 5 → ℕ :=
  ![e 0 / 2, e 1 / 2, e 2, e 3, e 4]

private def expandExponents (r s : ℕ) (e : Fin 5 → ℕ) : Fin 5 → ℕ :=
  ![2 * e 0 + r, 2 * e 1 + s, e 2, e 3, e 4]

private lemma sum_five (e : Fin 5 → ℕ) :
    (∑ j, e j) = e 0 + e 1 + e 2 + e 3 + e 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change e 0 + (e 1 + (e 2 + (e 3 + e 4))) = _
  omega

private lemma half_sum (e : Fin 5 → ℕ) :
    (∑ j, halfExponents e j) = e 0 / 2 + e 1 / 2 + e 2 + e 3 + e 4 := by
  rw [sum_five]
  rfl

private lemma expand_weight (r s : ℕ) (e : Fin 5 → ℕ) :
    weight (expandExponents r s e) = 2 * (∑ j, e j) + r + s := by
  rw [sum_five]
  change (2 * e 0 + r) + (2 * e 1 + s) + 2 * e 2 + 2 * e 3 + 2 * e 4 = _
  omega

private def odd_equiv (k : ℕ) : weighted (2 * k + 5) ≃ Fin 2 × compositions k where
  toFun e := (⟨e.val 0 % 2, Nat.mod_lt _ (by decide)⟩,
    ⟨halfExponents e.val, by
      rw [half_sum]
      have he := e.property
      change e.val 0 + e.val 1 + 2 * e.val 2 + 2 * e.val 3 + 2 * e.val 4 + 4 = _ at he
      omega⟩)
  invFun a := ⟨expandExponents a.1.val (1 - a.1.val) a.2.val, by
    rw [expand_weight, a.2.property]
    have h := a.1.isLt
    omega⟩
  left_inv e := by
    apply Subtype.ext
    funext j
    have he := e.property
    change e.val 0 + e.val 1 + 2 * e.val 2 + 2 * e.val 3 + 2 * e.val 4 + 4 = _ at he
    fin_cases j
    · change 2 * (e.val 0 / 2) + e.val 0 % 2 = e.val 0; omega
    · change 2 * (e.val 1 / 2) + (1 - e.val 0 % 2) = e.val 1; omega
    · rfl
    · rfl
    · rfl
  right_inv a := by
    apply Prod.ext
    · apply Fin.ext
      change (2 * a.2.val 0 + a.1.val) % 2 = a.1.val
      have h := a.1.isLt
      omega
    · apply Subtype.ext
      funext j
      have h := a.1.isLt
      fin_cases j
      · change (2 * a.2.val 0 + a.1.val) / 2 = a.2.val 0; omega
      · change (2 * a.2.val 1 + (1 - a.1.val)) / 2 = a.2.val 1; omega
      · rfl
      · rfl
      · rfl

private def even_equiv (k : ℕ) :
    weighted (2 * k + 6) ≃ compositions (k + 1) ⊕ compositions k where
  toFun e := if h : e.val 0 % 2 = 0 then
    Sum.inl ⟨halfExponents e.val, by
      rw [half_sum]
      have he := e.property
      change e.val 0 + e.val 1 + 2 * e.val 2 + 2 * e.val 3 + 2 * e.val 4 + 4 = _ at he
      omega⟩
    else Sum.inr ⟨halfExponents e.val, by
      rw [half_sum]
      have he := e.property
      change e.val 0 + e.val 1 + 2 * e.val 2 + 2 * e.val 3 + 2 * e.val 4 + 4 = _ at he
      omega⟩
  invFun a := match a with
    | .inl a => ⟨expandExponents 0 0 a.val, by rw [expand_weight, a.property] <;> omega⟩
    | .inr a => ⟨expandExponents 1 1 a.val, by rw [expand_weight, a.property] <;> omega⟩
  left_inv e := by
    dsimp only
    split_ifs with h
    · apply Subtype.ext
      funext j
      have he := e.property
      change e.val 0 + e.val 1 + 2 * e.val 2 + 2 * e.val 3 + 2 * e.val 4 + 4 = _ at he
      fin_cases j
      · change 2 * (e.val 0 / 2) + 0 = e.val 0; omega
      · change 2 * (e.val 1 / 2) + 0 = e.val 1; omega
      · rfl
      · rfl
      · rfl
    · apply Subtype.ext
      funext j
      have he := e.property
      change e.val 0 + e.val 1 + 2 * e.val 2 + 2 * e.val 3 + 2 * e.val 4 + 4 = _ at he
      fin_cases j
      · change 2 * (e.val 0 / 2) + 1 = e.val 0; omega
      · change 2 * (e.val 1 / 2) + 1 = e.val 1; omega
      · rfl
      · rfl
      · rfl
  right_inv a := by
    cases a with
    | inl a =>
      dsimp only
      rw [dif_pos (by change (2 * a.val 0 + 0) % 2 = 0; omega)]
      apply congrArg Sum.inl
      apply Subtype.ext
      funext j
      fin_cases j
      · change (2 * a.val 0 + 0) / 2 = a.val 0; omega
      · change (2 * a.val 1 + 0) / 2 = a.val 1; omega
      · rfl
      · rfl
      · rfl
    | inr a =>
      dsimp only
      rw [dif_neg (by change ¬(2 * a.val 0 + 1) % 2 = 0; omega)]
      apply congrArg Sum.inr
      apply Subtype.ext
      funext j
      fin_cases j
      · change (2 * a.val 0 + 1) / 2 = a.val 0; omega
      · change (2 * a.val 1 + 1) / 2 = a.val 1; omega
      · rfl
      · rfl
      · rfl

private lemma small_count (n : ℕ) (hn : n < 4) : Fintype.card (extraIndex n) = 0 := by
  classical
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun e => by have h := e.property; omega⟩

private lemma count_four : Fintype.card (extraIndex 4) = 1 := by
  classical
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨fun _ => 0, rfl⟩, ?_⟩
  intro e
  apply Subtype.ext
  funext j
  apply Fin.ext
  have h := weight_bound (fun j => (e.val j).val) j
  have he := e.property
  change weight (fun j => (e.val j).val) + 4 = 4 at he
  change (e.val j).val = 0
  omega

private lemma monomial_count_even (k : ℕ) :
    (Fintype.card (extraIndex (2 * k)) : ℚ) =
      ((2 * k : ℚ) ^ 4 - 4 * (2 * k) ^ 2) / 192 := by
  classical
  by_cases hk : k < 3
  · interval_cases k <;>
      norm_num [small_count 0 (by decide), small_count 2 (by decide), count_four]
  · let l := k - 3
    have hkl : k = l + 3 := by omega
    rw [hkl]
    have he : 2 * (l + 3) = 2 * l + 6 := by omega
    rw [he]
    have : Finite (compositions (l + 1)) :=
      Finite.of_equiv (Sym (Fin 5) (l + 1)) (Sym.equivNatSumOfFintype (Fin 5) (l + 1))
    have : Finite (compositions l) :=
      Finite.of_equiv (Sym (Fin 5) l) (Sym.equivNatSumOfFintype (Fin 5) l)
    have hc : Fintype.card (extraIndex (2 * l + 6)) =
        Nat.card (compositions (l + 1)) + Nat.card (compositions l) := by
      rw [← Nat.card_eq_fintype_card, Nat.card_congr (index_unbounded _),
        Nat.card_congr (even_equiv l), Nat.card_sum]
    rw [hc, Nat.cast_add, compositions_card, compositions_card]
    push_cast
    ring

private lemma monomial_count_odd (k : ℕ) :
    (Fintype.card (extraIndex (2 * k + 1)) : ℚ) =
      ((2 * k + 1 : ℚ) ^ 4 - 10 * (2 * k + 1) ^ 2 + 9) / 192 := by
  classical
  by_cases hk : k < 2
  · interval_cases k <;> norm_num [small_count 1 (by decide), small_count 3 (by decide)]
  · let l := k - 2
    have hkl : k = l + 2 := by omega
    rw [hkl]
    have he : 2 * (l + 2) + 1 = 2 * l + 5 := by omega
    rw [he]
    have hc : Fintype.card (extraIndex (2 * l + 5)) = 2 * Nat.card (compositions l) := by
      rw [← Nat.card_eq_fintype_card, Nat.card_congr (index_unbounded _),
        Nat.card_congr (odd_equiv l), Nat.card_prod, Nat.card_fin]
    rw [hc, Nat.cast_mul, Nat.cast_ofNat, compositions_card]
    push_cast
    ring

private lemma normal_count (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℕ) + Fintype.card (extraIndex n) : ℚ) =
      if Even n then ((n : ℚ) ^ 4 - 4 * n ^ 2 + 192 * n + 192) / 192
      else ((n : ℚ) ^ 4 - 10 * n ^ 2 + 192 * n + 201) / 192 := by
  classical
  push_cast
  by_cases he : Even n
  · rw [if_pos he]
    obtain ⟨k, hk⟩ := he
    have hnk : n = 2 * k := by omega
    rw [hnk, monomial_count_even]
    push_cast
    ring
  · rw [if_neg he]
    obtain ⟨k, hk⟩ := (Nat.not_even_iff_odd.mp he).exists_bit1
    subst n
    rw [monomial_count_odd]
    push_cast
    ring

/-- The exact complex dimension of the span of binary bond-two uniform MPS. -/
theorem result : claim := by
  intro n hn
  rw [evaluation_bridge, UniformMPSTwoByTwoTraceWords.coordinate_dimension]
  simpa only [Nat.cast_add] using normal_count n hn

end

end D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan
