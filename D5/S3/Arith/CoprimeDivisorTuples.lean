/- GID: D5/S3/Arith/CoprimeDivisorTuples
   generality: G
   mirror-B: D5/B/S3/Arith/CoprimeDivisorTuples
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Pairwise coprime ordered tuples of divisors of n count the divisors of n^n. -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.CoprimeDivisorTuples

/-- Ordered `k`-tuples of divisors of `n` whose distinct coordinates are coprime;
entries equal to `1`, including repeated `1`s, are allowed. -/
def coprimeDivisorTuples (k n : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => n.divisors).filter
    fun f => ∀ i j, i ≠ j → Nat.Coprime (f i) (f j)

def claim : Prop :=
  ∀ n : ℕ, 0 < n → (coprimeDivisorTuples n n).card = (n ^ n).divisors.card

theorem result : claim := by
  classical
  have key : ∀ k n : ℕ, 0 < n →
      (coprimeDivisorTuples k n).card =
        ∏ p ∈ n.primeFactors, (1 + k * n.factorization p) := by
    intro k n hn
    have hn0 : n ≠ 0 := hn.ne'
    let P := {p : ℕ // p ∈ n.primeFactors}
    let D := {d : ℕ // d ∈ n.divisors}
    let E := ∀ p : P, Fin (n.factorization p.val + 1)

    -- Route A: first identify each divisor with its bounded exponent vector.
    have divisor_dvd : ∀ d : D, d.val ∣ n :=
      fun d => (Nat.mem_divisors.mp d.property).1
    have divisor_ne : ∀ d : D, d.val ≠ 0 :=
      fun d => (Nat.pos_of_mem_divisors d.property).ne'
    have divisor_bound : ∀ d : D, d.val.factorization ≤ n.factorization :=
      fun d => (Nat.factorization_le_iff_dvd (divisor_ne d) hn0).mpr (divisor_dvd d)
    let encode : D → E := fun d p =>
      ⟨d.val.factorization p.val, Nat.lt_succ_of_le (divisor_bound d p.val)⟩
    have encode_injective : Function.Injective encode := by
      intro a b hab
      apply Subtype.ext
      apply Nat.eq_of_factorization_eq (divisor_ne a) (divisor_ne b)
      intro p
      by_cases hp : p ∈ n.primeFactors
      · exact congrArg Fin.val (congrFun hab ⟨p, hp⟩)
      · have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
        have ha := divisor_bound a p
        have hb := divisor_bound b p
        omega
    have encode_surjective : Function.Surjective encode := by
      intro e
      let v : ℕ →₀ ℕ := Finsupp.onFinset n.primeFactors
        (fun p => if hp : p ∈ n.primeFactors then (e ⟨p, hp⟩).val else 0)
        (by
          intro p hp
          by_contra h
          simp [h] at hp)
      have hv : ∀ p : P, v p.val = (e p).val := by
        rintro ⟨p, hp⟩
        simp only [v, Finsupp.onFinset_apply, dif_pos hp]
      have hle : v ≤ n.factorization := by
        intro p
        by_cases hp : p ∈ n.primeFactors
        · have he : (e ⟨p, hp⟩).val < n.factorization p + 1 := (e ⟨p, hp⟩).isLt
          simp only [v, Finsupp.onFinset_apply, dif_pos hp]
          exact Nat.lt_succ_iff.mp he
        · simp only [v, Finsupp.onFinset_apply, dif_neg hp]
          exact Nat.zero_le _
      let d : D := ⟨v.prod (· ^ ·), Nat.mem_divisors.mpr
        ⟨Nat.prod_pow_dvd_of_le_factorization hle, hn0⟩⟩
      refine ⟨d, ?_⟩
      funext p
      apply Fin.ext
      change (v.prod (· ^ ·)).factorization p.val = (e p).val
      rw [Nat.factorization_prod_pow_eq_self_of_le_factorization hle]
      exact hv p
    let divisorEquiv : D ≃ E :=
      Equiv.ofBijective encode ⟨encode_injective, encode_surjective⟩

    -- Coprimality means that no prime has positive exponents in both divisors.
    have coprime_iff : ∀ a b : D, Nat.Coprime a.val b.val ↔
        ∀ p : P, divisorEquiv a p = 0 ∨ divisorEquiv b p = 0 := by
      intro a b
      constructor
      · intro hab p
        by_cases ha : a.val.factorization p.val = 0
        · left
          exact Fin.ext ha
        · right
          apply Fin.ext
          change b.val.factorization p.val = 0
          apply Nat.factorization_eq_zero_of_not_dvd
          intro hb
          exact Nat.not_coprime_of_dvd_of_dvd
            (Nat.prime_of_mem_primeFactors p.property).one_lt
            (Nat.dvd_of_factorization_pos ha) hb hab
      · intro h
        apply Nat.coprime_of_dvd
        intro p hp hpa hpb
        have hpn : p ∈ n.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp, hpa.trans (divisor_dvd a), hn0⟩
        have ha := hp.factorization_pos_of_dvd (divisor_ne a) hpa
        have hb := hp.factorization_pos_of_dvd (divisor_ne b) hpb
        rcases h ⟨p, hpn⟩ with hza | hzb
        · have hz := congrArg Fin.val hza
          change a.val.factorization p = 0 at hz
          omega
        · have hz := congrArg Fin.val hzb
          change b.val.factorization p = 0 at hz
          omega

    -- A sparse exponent vector is either empty or a slot and a positive exponent.
    have columnEquiv : ∀ m : ℕ, Option (Fin k × Fin m) ≃
        {v : Fin k → Fin (m + 1) //
          ∀ i j, i ≠ j → v i = 0 ∨ v j = 0} := by
      intro m
      let C := {v : Fin k → Fin (m + 1) //
        ∀ i j, i ≠ j → v i = 0 ∨ v j = 0}
      let spike : Option (Fin k × Fin m) → C := fun o =>
        ⟨(fun i => match o with
          | none => 0
          | some a => if i = a.1 then
              ⟨a.2.val + 1, Nat.succ_lt_succ a.2.isLt⟩ else 0), by
          intro i j hij
          cases o with
          | none => exact Or.inl rfl
          | some a =>
            by_cases hi : i = a.1
            · right
              have hj : j ≠ a.1 := fun h => hij (hi.trans h.symm)
              simp [hj]
            · left
              simp [hi]⟩
      apply Equiv.ofBijective spike
      constructor
      · intro a b hab
        have heq : ∀ i, (spike a).val i = (spike b).val i :=
          fun i => congrArg (fun w : C => w.val i) hab
        cases a with
        | none =>
          cases b with
          | none => rfl
          | some b =>
            have h := congrArg Fin.val (heq b.1)
            simp [spike] at h
        | some a =>
          cases b with
          | none =>
            have h := congrArg Fin.val (heq a.1)
            simp [spike] at h
          | some b =>
            have hij : a.1 = b.1 := by
              by_contra h
              have hh := congrArg Fin.val (heq a.1)
              simp [spike, h] at hh
            have he : a.2 = b.2 := by
              apply Fin.ext
              have hh := congrArg Fin.val (heq a.1)
              have hs : a.2.val + 1 = b.2.val + 1 := by
                simpa [spike, hij] using hh
              omega
            exact congrArg some (Prod.ext hij he)
      · intro v
        by_cases h : ∃ i, v.val i ≠ 0
        · obtain ⟨i, hi⟩ := h
          have hi0 : 0 < (v.val i).val := by
            apply Nat.pos_of_ne_zero
            intro hz
            exact hi (Fin.ext hz)
          let e : Fin m := ⟨(v.val i).val - 1, by
            have hv := (v.val i).isLt
            omega⟩
          refine ⟨some (i, e), ?_⟩
          apply Subtype.ext
          funext j
          by_cases hji : j = i
          · subst j
            apply Fin.ext
            dsimp only [spike]
            simp only []
            change (v.val i).val - 1 + 1 = (v.val i).val
            omega
          · have hj : v.val j = 0 :=
              (v.property i j (Ne.symm hji)).resolve_left hi
            simp [spike, hji, hj]
        · refine ⟨none, ?_⟩
          apply Subtype.ext
          funext i
          have hi : v.val i = 0 := by
            by_contra hi
            exact h ⟨i, hi⟩
          simpa [spike] using hi.symm

    -- Transpose the exponent matrix: the columns are independent prime choices.
    let T := {f : Fin k → ℕ // f ∈ coprimeDivisorTuples k n}
    let C : P → Type := fun p =>
      {v : Fin k → Fin (n.factorization p.val + 1) //
        ∀ i j, i ≠ j → v i = 0 ∨ v j = 0}
    let coordinate : T → Fin k → D := fun t i =>
      ⟨t.val i, Fintype.mem_piFinset.mp (Finset.mem_filter.mp t.property).1 i⟩
    have coordinate_coprime : ∀ (t : T) (i j : Fin k), i ≠ j →
        Nat.Coprime (coordinate t i).val (coordinate t j).val := by
      intro t i j hij
      exact (Finset.mem_filter.mp t.property).2 i j hij
    let columns : T → ∀ p : P, C p := fun t p =>
      ⟨fun i => divisorEquiv (coordinate t i) p, fun i j hij =>
        (coprime_iff (coordinate t i) (coordinate t j)).mp
          (coordinate_coprime t i j hij) p⟩
    have columns_injective : Function.Injective columns := by
      intro t u h
      apply Subtype.ext
      funext i
      have hc : coordinate t i = coordinate u i := by
        apply divisorEquiv.injective
        funext p
        exact congrArg (fun g : ∀ p : P, C p => (g p).val i) h
      exact congrArg Subtype.val hc
    have columns_surjective : Function.Surjective columns := by
      intro c
      let ds : Fin k → D := fun i =>
        divisorEquiv.symm (fun p => (c p).val i)
      have hds : ∀ (i : Fin k) (p : P), divisorEquiv (ds i) p = (c p).val i := by
        intro i p
        exact congrFun (divisorEquiv.apply_symm_apply (fun q => (c q).val i)) p
      have ht : (fun i => (ds i).val) ∈ coprimeDivisorTuples k n := by
        apply Finset.mem_filter.mpr
        constructor
        · exact Fintype.mem_piFinset.mpr (fun i => (ds i).property)
        · intro i j hij
          apply (coprime_iff (ds i) (ds j)).mpr
          intro p
          rw [hds i p, hds j p]
          exact (c p).property i j hij
      refine ⟨⟨(fun i => (ds i).val), ht⟩, ?_⟩
      funext p
      apply Subtype.ext
      funext i
      change divisorEquiv (ds i) p = (c p).val i
      exact hds i p
    have choices : T ≃ (∀ p : P, Option (Fin k × Fin (n.factorization p.val))) :=
      (Equiv.ofBijective columns ⟨columns_injective, columns_surjective⟩).trans
        (Equiv.piCongrRight fun p => (columnEquiv (n.factorization p.val)).symm)
    calc
      (coprimeDivisorTuples k n).card = Fintype.card T :=
        (Fintype.card_coe _).symm
      _ = Fintype.card (∀ p : P, Option (Fin k × Fin (n.factorization p.val))) :=
        Fintype.card_congr choices
      _ = ∏ p : P, (1 + k * n.factorization p.val) := by
        simp [Fintype.card_pi, Fintype.card_option, Fintype.card_prod, Nat.add_comm]
      _ = ∏ p ∈ n.primeFactors, (1 + k * n.factorization p) :=
        Finset.prod_coe_sort n.primeFactors fun p => 1 + k * n.factorization p

  have rhs : ∀ n : ℕ, 0 < n →
      (n ^ n).divisors.card = ∏ p ∈ n.primeFactors, (1 + n * n.factorization p) := by
    intro n hn
    rw [Nat.card_divisors (pow_ne_zero n hn.ne'), Nat.primeFactors_pow n hn.ne']
    apply Finset.prod_congr rfl
    intro p hp
    simp [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.add_comm]

  -- Empty prime support already covers n = 1; no exceptional case is needed.
  intro n hn
  exact (key n n hn).trans (rhs n hn).symm

end D5.S3.Arith.CoprimeDivisorTuples
