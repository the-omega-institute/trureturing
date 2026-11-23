/- GID: D5/S3/Arith/PrimitiveRoot/CharacterExpansion
   generality: G
   mirror-B: D5/B/S3/Arith/PrimitiveRoot/CharacterExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Character expansions and error bounds for power-subgroup sieves. -/
import D5.S3.Factorization.Galois.GeneralPowerCharacterLayer
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
/-! Character expansions and weighted bounds for primitive roots. -/
namespace D5.S3.Arith.PrimitiveRoot.CharacterExpansion
open scoped BigOperators Classical
open D5.S3.Factorization.Galois.GeneralPowerCharacterLayer (powerSubgroup)
private noncomputable def kernelCharacters (p : ℕ) [NeZero p] (q : ℕ) :
    Subgroup (DirichletCharacter ℂ p) :=
  (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod p) ℂ (powerSubgroup
      ((ZMod p)ˣ) q)).ofDual
private lemma kernelCharacters_mem (p : ℕ) [NeZero p] (q : ℕ)
    (χ : DirichletCharacter ℂ p) : χ ∈ kernelCharacters p q ↔ χ ^ q = 1 := by
  rw [kernelCharacters, MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff]; constructor
  · intro h
    apply MulChar.ext; intro u; rw [MulChar.pow_apply_coe, ← map_pow, MulChar.one_apply_coe]
    simpa only [powMonoidHom_apply, Units.val_pow_eq_pow_val] using h _ ⟨u, rfl⟩
  · intro h u hu
    obtain ⟨v, rfl⟩ := hu; change χ ((v ^ q : (ZMod p)ˣ) : ZMod p) = 1
    rw [Units.val_pow_eq_pow_val, map_pow, ← MulChar.pow_apply_coe, h]
    exact MulChar.one_apply_coe v
private lemma kernelCharacters_card (p : ℕ) [Fact p.Prime] {q : ℕ}
    (hq : q ∣ p - 1) : Nat.card (kernelCharacters p q) = q := by
  rw [kernelCharacters, MulChar.card_subgroupOrderIsoSubgroupMulChar,
    ← Subgroup.index_eq_card, powerSubgroup, IsCyclic.index_powMonoidHom_range,
    Nat.card_eq_fintype_card, ZMod.card_units, Nat.gcd_eq_right hq]
private lemma kernelCharacters_sum (p : ℕ) [Fact p.Prime] {q : ℕ}
    (hq : q ∣ p - 1) (a : (ZMod p)ˣ) :
    ∑ χ : kernelCharacters p q, (χ : DirichletCharacter ℂ p) a =
      if a ∈ powerSubgroup ((ZMod p)ˣ) q then (q : ℂ) else 0 := by
  classical
  by_cases ha : a ∈ powerSubgroup ((ZMod p)ˣ) q
  · rw [ite_eq_left ha]
    have hval (χ : kernelCharacters p q) : (χ : DirichletCharacter ℂ p) a = 1 :=
      (MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff.mp χ.property) a ha
    simp only [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card, kernelCharacters_card p hq]
  · rw [ite_eq_right ha]
    have hsep : ∃ χ : kernelCharacters p q, (χ : DirichletCharacter ℂ p) a ≠ 1 := by
      by_contra! h
      apply ha; have hh : a ∈ (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod p) ℂ).symm
          (OrderDual.toDual (kernelCharacters p q)) := by
        rw [MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff]; intro χ hχ; exact h ⟨χ, hχ⟩
      simpa [kernelCharacters] using hh
    obtain ⟨ψ, hψ⟩ := hsep; let f : MulChar (kernelCharacters p q) ℂ := {
      toFun := fun χ => (χ : DirichletCharacter ℂ p) a
      map_one' := MulChar.one_apply_coe a
      map_mul' := fun χ η => MulChar.mul_apply (χ : DirichletCharacter ℂ p) η a
      map_nonunit' := fun χ hχ => (hχ (Group.isUnit χ)).elim }
    have hf : f ≠ 1 := by
      intro hf; have hh := congrArg (fun ξ : MulChar (kernelCharacters p q) ℂ => ξ ψ) hf
      change (ψ : DirichletCharacter ℂ p) a = (1 : MulChar (kernelCharacters p q) ℂ) ψ at hh
      rw [MulChar.one_apply (Group.isUnit ψ)] at hh; exact hψ hh
    exact MulChar.sum_eq_zero_of_ne_one hf
private noncomputable def primeCharacters (p q : ℕ) : Finset (DirichletCharacter ℂ p) :=
  Finset.univ.filter (fun χ => orderOf χ = q)
private lemma primeCharacters_card (p : ℕ) [Fact p.Prime] {q : ℕ}
    (hq : q ∣ p - 1) : (primeCharacters p q).card = q.totient := by
  let : IsCyclic (DirichletCharacter ℂ p) :=
    isCyclic_of_injective (DirichletCharacter.mulEquiv_units ℂ p).some.toMonoidHom
      (DirichletCharacter.mulEquiv_units ℂ p).some.injective
  apply IsCyclic.card_orderOf_eq_totient; rwa [← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, Nat.totient_prime Fact.out]
private lemma primeCharacters_sum (p : ℕ) [Fact p.Prime] {q : ℕ}
    (hprime : q.Prime) (hq : q ∣ p - 1) (a : (ZMod p)ˣ) :
    1 + ∑ χ ∈ primeCharacters p q, χ a =
      if a ∈ powerSubgroup ((ZMod p)ˣ) q then (q : ℂ) else 0 := by
  classical
  have hmem (χ : DirichletCharacter ℂ p) :
      χ ∈ insert 1 (primeCharacters p q) ↔ χ ∈ kernelCharacters p q := by
    simp only [Finset.mem_insert, primeCharacters, Finset.mem_filter,
      Finset.mem_univ, true_and, kernelCharacters_mem,
      ← orderOf_dvd_iff_pow_eq_one, Nat.dvd_prime hprime, orderOf_eq_one_iff]
  have hs := kernelCharacters_sum p hq a
  rw [← Finset.sum_subtype _ hmem (fun χ : DirichletCharacter ℂ p => χ a),
    Finset.sum_insert, MulChar.one_apply_coe] at hs
  · exact hs
  · simp [primeCharacters, hprime.ne_one.symm]
private noncomputable def localFree (p q : ℕ) (a : (ZMod p)ˣ) : ℝ :=
  if a ∈ powerSubgroup ((ZMod p)ˣ) q then 0 else 1
private lemma localFree_character (p : ℕ) [Fact p.Prime] {q : ℕ}
    (hprime : q.Prime) (hq : q ∣ p - 1) (a : (ZMod p)ˣ) :
    (localFree p q a : ℂ) = (1 - (q : ℂ)⁻¹) *
      (1 - ((q : ℂ) - 1)⁻¹ * ∑ χ ∈ primeCharacters p q, χ a) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  have hq1 : (q : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hprime.ne_one)
  have hs := primeCharacters_sum p hprime hq a
  unfold localFree; split_ifs with ha
  · rw [ite_eq_left ha] at hs
    have he : ∑ χ ∈ primeCharacters p q, χ a = (q : ℂ) - 1 := by linear_combination hs
    rw [he]; simp [hq1]
  · rw [ite_eq_right ha] at hs
    have he : ∑ χ ∈ primeCharacters p q, χ a = -(1 : ℂ) := by linear_combination hs
    rw [he]; push_cast; field_simp; ring
private noncomputable def multiplyTerms (p q : ℕ)
    (L : List (ℝ × DirichletCharacter ℂ p)) : List (ℝ × DirichletCharacter ℂ p) :=
  (primeCharacters p q).toList.flatMap fun χ =>
    L.map (fun z => (-z.1 / ((q : ℝ) - 1), χ * z.2))
private noncomputable def errorTerms (p : ℕ) : List ℕ → List (ℝ × DirichletCharacter ℂ p)
  | [] => []
  | q :: L => errorTerms p L ++ multiplyTerms p q ((1, 1) :: errorTerms p L)
private noncomputable def evaluateTerms (p : ℕ)
    (L : List (ℝ × DirichletCharacter ℂ p)) (a : (ZMod p)ˣ) : ℂ :=
  (L.map (fun z => (z.1 : ℂ) * z.2 a)).sum
private noncomputable def termMass (p : ℕ)
    (L : List (ℝ × DirichletCharacter ℂ p)) : ℝ := (L.map (fun z => |z.1|)).sum
private lemma evaluateTerms_multiply (p q : ℕ)
    (L : List (ℝ × DirichletCharacter ℂ p)) (a : (ZMod p)ˣ) :
    evaluateTerms p (multiplyTerms p q L) a =
      -((q : ℂ) - 1)⁻¹ * (∑ χ ∈ primeCharacters p q, χ a) * evaluateTerms p L a := by
  unfold multiplyTerms evaluateTerms
  simp only [List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_natCast,
    Complex.ofReal_one, MulChar.mul_apply]
  have he (χ : DirichletCharacter ℂ p) :
      (L.map (fun z => -((z.1 : ℂ)) / ((q : ℂ) - 1) * (χ a * z.2 a))).sum =
        -((q : ℂ) - 1)⁻¹ * χ a * (L.map (fun z => (z.1 : ℂ) * z.2 a)).sum := by
    rw [← List.sum_map_mul_left]; congr 1; apply List.map_congr_left; intro z hz; ring
  simp_rw [he]
  rw [List.sum_map_mul_right, Finset.sum_map_toList, ← Finset.mul_sum]
private lemma termMass_multiply (p : ℕ) [Fact p.Prime] {q : ℕ}
    (hprime : q.Prime) (hq : q ∣ p - 1)
    (L : List (ℝ × DirichletCharacter ℂ p)) :
    termMass p (multiplyTerms p q L) = termMass p L := by
  have hq1 : 0 < (q : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hprime.one_lt)
  unfold termMass multiplyTerms
  simp only [List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def,
    abs_div, abs_neg, abs_of_pos hq1]
  simp_rw [div_eq_mul_inv, List.sum_map_mul_right]
  rw [List.map_const', List.sum_replicate, Finset.length_toList, primeCharacters_card p hq,
    Nat.totient_prime hprime, nsmul_eq_mul, Nat.cast_sub hprime.one_le, Nat.cast_one]
  field_simp
private lemma errorTerms_mass (p : ℕ) [Fact p.Prime] (L : List ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ q ∣ p - 1) :
    termMass p (errorTerms p L) = 2 ^ L.length - 1 := by
  induction L with
  | nil => simp [errorTerms, termMass]
  | cons q L ih =>
    have hq := hL q List.mem_cons_self
    have ht : ∀ t ∈ L, t.Prime ∧ t ∣ p - 1 := fun t ht => hL t (List.mem_cons_of_mem q ht)
    simp only [errorTerms, termMass, List.map_append, List.sum_append]
    change termMass p (errorTerms p L) +
      termMass p (multiplyTerms p q ((1, 1) :: errorTerms p L)) = _
    rw [termMass_multiply p hq.1 hq.2]; simp only [termMass, List.map_cons, List.sum_cons, abs_one]
    change termMass p (errorTerms p L) + (1 + termMass p (errorTerms p L)) = _
    rw [ih ht, List.length_cons, pow_succ]; ring
private lemma errorTerms_order (p : ℕ) (L : List ℕ) :
    ∀ z ∈ errorTerms p L, orderOf z.2 ∣ L.prod := by
  induction L with
  | nil => simp [errorTerms]
  | cons q L ih =>
    intro z hz; rw [errorTerms, List.mem_append] at hz; rcases hz with hz | hz
    · exact (ih z hz).trans (by simp [List.prod_cons])
    · obtain ⟨χ, hχ, hz⟩ := List.mem_flatMap.mp hz
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      have hχq := (Finset.mem_filter.mp (Finset.mem_toList.mp hχ)).2
      have hwL : orderOf w.2 ∣ L.prod := by
        rcases List.mem_cons.mp hw with rfl | hw
        · simp
        · exact ih w hw
      have hd := (Commute.all χ w.2).orderOf_mul_dvd_mul_orderOf
      rw [hχq] at hd; exact hd.trans (Nat.mul_dvd_mul_left q hwL)
private lemma multiply_ne_one (p : ℕ) {q : ℕ} (hprime : q.Prime) (L : List ℕ)
    (hL : ∀ t ∈ L, t.Prime) (hqL : q ∉ L)
    (χ : DirichletCharacter ℂ p) (hχ : orderOf χ = q)
    (ψ : DirichletCharacter ℂ p) (hψ : orderOf ψ ∣ L.prod) : χ * ψ ≠ 1 := by
  intro he
  have hc : q.Coprime L.prod := Nat.coprime_list_prod_right_iff.mpr fun t ht =>
    (Nat.coprime_primes hprime (hL t ht)).mpr (by rintro rfl; exact hqL ht)
  have hd : q ∣ L.prod := by rw [← hχ, eq_inv_of_mul_eq_one_left he, orderOf_inv]; exact hψ
  exact hprime.ne_one (hc.eq_one_of_dvd hd)
private lemma errorTerms_nonprincipal (p : ℕ) (L : List ℕ) (hnd : L.Nodup)
    (hL : ∀ q ∈ L, q.Prime) : ∀ z ∈ errorTerms p L, z.2 ≠ 1 := by
  induction L with
  | nil => simp [errorTerms]
  | cons q L ih =>
    intro z hz; rw [errorTerms, List.mem_append] at hz; rcases hz with hz | hz
    · exact ih hnd.of_cons (fun t ht => hL t (List.mem_cons_of_mem q ht)) z hz
    · obtain ⟨χ, hχ, hz⟩ := List.mem_flatMap.mp hz
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      have hwL : orderOf w.2 ∣ L.prod := by
        rcases List.mem_cons.mp hw with rfl | hw
        · simp
        · exact errorTerms_order p L w hw
      exact multiply_ne_one p (hL q List.mem_cons_self) L
        (fun t ht => hL t (List.mem_cons_of_mem q ht)) (List.nodup_cons.mp hnd).1
        χ (Finset.mem_filter.mp (Finset.mem_toList.mp hχ)).2 w.2 hwL
private lemma errorTerms_expansion (p : ℕ) [Fact p.Prime] (L : List ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ q ∣ p - 1) (a : (ZMod p)ˣ) :
    (((L.map (fun q : ℕ => localFree p q a)).prod : ℝ) : ℂ) =
      ((L.map (fun q : ℕ => 1 - (q : ℂ)⁻¹)).prod) *
        (1 + evaluateTerms p (errorTerms p L) a) := by
  induction L with
  | nil => simp [errorTerms, evaluateTerms]
  | cons q L ih =>
    have hq := hL q List.mem_cons_self
    have ht : ∀ t ∈ L, t.Prime ∧ t ∣ p - 1 := fun t ht => hL t (List.mem_cons_of_mem q ht)
    have heval : evaluateTerms p (errorTerms p (q :: L)) a =
        evaluateTerms p (errorTerms p L) a + -((q : ℂ) - 1)⁻¹ *
          (∑ χ ∈ primeCharacters p q, χ a) * (1 + evaluateTerms p (errorTerms p L) a) := by
      simp only [errorTerms, evaluateTerms, List.map_append, List.sum_append]
      change evaluateTerms p (errorTerms p L) a +
        evaluateTerms p (multiplyTerms p q ((1, 1) :: errorTerms p L)) a = _
      rw [evaluateTerms_multiply]; simp [evaluateTerms]
    simp only [List.map_cons, List.prod_cons, Complex.ofReal_mul]
    rw [localFree_character p hq.1 hq.2, ih ht, heval]; ring
private lemma localFree_gap (p : ℕ) [Fact p.Prime] {q : ℕ}
    (hprime : q.Prime) (hq : q ∣ p - 1) (a : (ZMod p)ˣ) :
    (1 - (localFree p q a : ℂ)) =
      (q : ℂ)⁻¹ * (1 + ∑ χ ∈ primeCharacters p q, χ a) := by
  rw [primeCharacters_sum p hprime hq]; unfold localFree; split_ifs <;> simp [hprime.ne_zero]
theorem sum_units_character (p : ℕ) [NeZero p] (W : ZMod p → ℂ)
    (χ : DirichletCharacter ℂ p) :
    (∑ a : ZMod p, W a * χ a) = ∑ a : (ZMod p)ˣ, W a * χ a := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun a : ZMod p => IsUnit a)]
  have hz : ∑ a ∈ Finset.univ.filter (fun a : ZMod p => ¬IsUnit a),
      W a * χ a = 0 := by
    apply Finset.sum_eq_zero
    intro a ha; rw [MulChar.map_nonunit _ (Finset.mem_filter.mp ha).2, mul_zero]
  rw [hz, add_zero]
  refine Finset.sum_bij (fun a ha => (Finset.mem_filter.mp ha).2.unit) ?_ ?_ ?_ ?_
  · intro a ha; exact Finset.mem_univ _
  · intro a ha b hb hab
    have := congrArg Units.val hab
    simpa using this
  · intro u hu
    refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.isUnit⟩, ?_⟩; exact Units.ext (by simp)
  · intro a ha; simp
private noncomputable def weightedTerms (p : ℕ) [NeZero p] (W : ZMod p → ℝ)
    (L : List (ℝ × DirichletCharacter ℂ p)) (ψ : DirichletCharacter ℂ p) : ℂ :=
  (L.map (fun z => (z.1 : ℂ) * ∑ a : ZMod p, (W a : ℂ) * (z.2 * ψ) a)).sum
private lemma weightedTerms_bound (p : ℕ) [NeZero p] (W : ZMod p → ℝ) (M : ℝ)
    (P : DirichletCharacter ℂ p → Prop)
    (hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → P χ → |(∑ a, (W a : ℂ) * χ a).re| ≤ M)
    (L : List (ℝ × DirichletCharacter ℂ p)) (ψ : DirichletCharacter ℂ p)
    (hL : ∀ z ∈ L, z.2 * ψ ≠ 1 ∧ P (z.2 * ψ)) :
    |(weightedTerms p W L ψ).re| ≤ termMass p L * M := by
  induction L with
  | nil => simp [weightedTerms, termMass]
  | cons z L ih =>
    simp only [weightedTerms, List.map_cons, List.sum_cons, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    change |z.1 * (∑ a, (W a : ℂ) * (z.2 * ψ) a).re +
      (weightedTerms p W L ψ).re| ≤ (|z.1| + termMass p L) * M
    calc
      _ ≤ |z.1 * (∑ a, (W a : ℂ) * (z.2 * ψ) a).re| +
          |(weightedTerms p W L ψ).re| := abs_add_le _ _
      _ ≤ |z.1| * M + termMass p L * M := add_le_add
        (by rw [abs_mul]
            exact mul_le_mul_of_nonneg_left
              (hM _ (hL z List.mem_cons_self).1 (hL z List.mem_cons_self).2) (abs_nonneg _))
        (ih (fun w hw => hL w (List.mem_cons_of_mem z hw)))
      _ = _ := by ring
private lemma weightedTerms_evaluate (p : ℕ) [NeZero p] (W : ZMod p → ℝ)
    (L : List (ℝ × DirichletCharacter ℂ p)) (ψ : DirichletCharacter ℂ p) :
    weightedTerms p W L ψ = ∑ a : (ZMod p)ˣ,
      (W a : ℂ) * ψ a * evaluateTerms p L a := by
  induction L with
  | nil => simp [weightedTerms, evaluateTerms]
  | cons z L ih =>
    change (z.1 : ℂ) * (∑ a, (W a : ℂ) * (z.2 * ψ) a) + weightedTerms p W L ψ =
      ∑ a : (ZMod p)ˣ, (W a : ℂ) * ψ a *
        ((z.1 : ℂ) * z.2 a + evaluateTerms p L a)
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [ih, sum_units_character p (fun a => (W a : ℂ)), Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl
    intro a ha; rw [MulChar.mul_apply]; ring
private lemma localFree_prod (p : ℕ) (L : List ℕ) (a : (ZMod p)ˣ) :
    (L.map (fun q => localFree p q a)).prod =
      if ∀ q ∈ L, a ∉ powerSubgroup ((ZMod p)ˣ) q then (1 : ℝ) else 0
      := by
  induction L with
  | nil => simp
  | cons q L ih =>
    simp only [List.map_cons, List.prod_cons, List.forall_mem_cons, ih]
    unfold localFree; split_ifs <;> simp_all
/-- The density of integers avoiding every prime divisor of `e`. -/
noncomputable def theta (e : ℕ) : ℝ := ∏ q ∈ e.primeFactors, (1 - (q : ℝ)⁻¹)
/-- The margin contributed by the remaining sieve primes. -/
noncomputable def delta (T : Finset ℕ) : ℝ := 1 - ∑ t ∈ T, (t : ℝ)⁻¹
/-- The error coefficient of the combined character sieve. -/
noncomputable def errorCoefficient (e : ℕ) (T : Finset ℕ) : ℝ :=
  delta T * (2 ^ e.primeFactors.card - 1) +
    ((T.card : ℝ) - 1 + delta T) * 2 ^ e.primeFactors.card
/-- The absolute coefficient mass, valid for every sign of the margin. -/
noncomputable def errorCoefficientAbs (e : ℕ) (T : Finset ℕ) : ℝ :=
  |delta T| * (2 ^ e.primeFactors.card - 1) +
    ((T.card : ℝ) - 1 + delta T) * 2 ^ e.primeFactors.card
/-- The absolute and signed coefficients agree exactly in these two cases. -/
theorem errorCoefficientAbs_eq (e : ℕ) (T : Finset ℕ) :
    errorCoefficientAbs e T = errorCoefficient e T ↔
      0 ≤ delta T ∨ e.primeFactors = ∅ := by
  have hr : (2 : ℝ) ^ e.primeFactors.card - 1 = 0 ↔ e.primeFactors = ∅ := by
    constructor
    · intro h
      by_contra hn
      have hc : 0 < e.primeFactors.card := Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr hn)
      have hp : (1 : ℝ) < 2 ^ e.primeFactors.card := one_lt_pow₀ (by norm_num) hc.ne'
      linarith
    · intro h; simp [h]
  have hh : errorCoefficientAbs e T = errorCoefficient e T ↔
      (|delta T| - delta T) * (2 ^ e.primeFactors.card - 1) = 0 := by
    unfold errorCoefficientAbs errorCoefficient; constructor <;> intro h <;> nlinarith
  rw [hh, mul_eq_zero, sub_eq_zero, abs_eq_self, hr]
/-- The reciprocal-sum criterion is equivalent to the signed coefficient bounds. -/
theorem errorCoefficient_nonneg (e : ℕ) (T : Finset ℕ) :
    (∑ t ∈ T, (t : ℝ)⁻¹ ≤ (T.card : ℝ) / 2) ↔
      (2 ^ e.primeFactors.card - delta T ≤ errorCoefficient e T ∧
        0 ≤ errorCoefficient e T) := by
  have hr : 1 ≤ (2 : ℝ) ^ e.primeFactors.card := one_le_pow₀ (by norm_num)
  have hr0 : 0 < (2 : ℝ) ^ e.primeFactors.card := by positivity
  constructor
  · intro hT
    have hs0 : 0 ≤ ∑ t ∈ T, (t : ℝ)⁻¹ := Finset.sum_nonneg fun t ht => by positivity
    have hd : delta T ≤ 1 := by unfold delta; linarith
    have hsd : 1 ≤ (T.card : ℝ) - 1 + 2 * delta T := by unfold delta; linarith
    have hm := mul_le_mul_of_nonneg_right hsd hr0.le
    unfold errorCoefficient; constructor <;> nlinarith
  · rintro ⟨hK, _⟩
    have hid : errorCoefficient e T - (2 ^ e.primeFactors.card - delta T) =
        2 ^ e.primeFactors.card * ((T.card : ℝ) - 2 * ∑ t ∈ T, (t : ℝ)⁻¹) := by
      unfold errorCoefficient delta; ring
    have hh : 0 ≤ (T.card : ℝ) - 2 * ∑ t ∈ T, (t : ℝ)⁻¹ :=
      (mul_nonneg_iff_of_pos_left hr0).mp (hid ▸ sub_nonneg.mpr hK)
    linarith
/-- Every local density factor is positive. -/
theorem theta_pos (e : ℕ) : 0 < theta e := by
  apply Finset.prod_pos; intro q hq; apply sub_pos.mpr
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_lt)
private noncomputable def sieveError (p : ℕ) [NeZero p] (W : ZMod p → ℝ)
    (e : ℕ) (T : Finset ℕ) : ℂ :=
  (delta T : ℂ) * weightedTerms p W (errorTerms p e.primeFactors.toList) 1 -
    ∑ t ∈ T, (t : ℂ)⁻¹ * ∑ χ ∈ primeCharacters p t,
      weightedTerms p W ((1, 1) :: errorTerms p e.primeFactors.toList) χ
private lemma sieveError_bound (p : ℕ) [Fact p.Prime] (W : ZMod p → ℝ)
    (e : ℕ) (he : ∀ q ∈ e.primeFactors, q ∣ p - 1) (T : Finset ℕ)
    (hT : ∀ t ∈ T, t.Prime ∧ t ∣ p - 1 ∧ t ∉ e.primeFactors) (M : ℝ)
    (hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → (orderOf χ ∣ ∏ q ∈ e.primeFactors, q ∨
        ∃ t ∈ T, orderOf χ ∣ t * (∏ q ∈ e.primeFactors, q)) → |(∑ a, (W a : ℂ) * χ a).re| ≤ M)
    : |(sieveError p W e T).re| ≤ errorCoefficientAbs e T * M := by
  let L := e.primeFactors.toList
  let r : ℝ := 2 ^ e.primeFactors.card
  have hL : ∀ q ∈ L, q.Prime ∧ q ∣ p - 1 := fun q hq =>
    ⟨Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp hq),
      he q (Finset.mem_toList.mp hq)⟩
  have hmass : termMass p (errorTerms p L) = r - 1 := by simpa [L, r] using errorTerms_mass p L hL
  have hE : |(weightedTerms p W (errorTerms p L) 1).re| ≤ (r - 1) * M := by
    rw [← hmass]; apply weightedTerms_bound p W M _ hM; intro z hz; simp only [mul_one]
    exact ⟨errorTerms_nonprincipal p L (Finset.nodup_toList _)
      (fun q hq => (hL q hq).1) z hz,
      Or.inl (by simpa [L] using errorTerms_order p L z hz)⟩
  have htwist (t : ℕ) (ht : t ∈ T) (χ : DirichletCharacter ℂ p)
      (hχ : χ ∈ primeCharacters p t) :
      |(weightedTerms p W ((1, 1) :: errorTerms p L) χ).re| ≤ r * M := by
    have hf : termMass p ((1, 1) :: errorTerms p L) = r := by
      change |(1 : ℝ)| + termMass p (errorTerms p L) = r
      rw [abs_one, hmass]; ring
    rw [← hf]; apply weightedTerms_bound p W M _ hM; intro z hz
    have ho : orderOf z.2 ∣ L.prod := by
      rcases List.mem_cons.mp hz with rfl | hz
      · simp
      · exact errorTerms_order p L z hz
    constructor
    · rw [mul_comm]
      exact multiply_ne_one p (hT t ht).1 L (fun q hq => (hL q hq).1)
        (fun htL => (hT t ht).2.2 (Finset.mem_toList.mp htL))
        χ (Finset.mem_filter.mp hχ).2 z.2 ho
    · apply Or.inr; refine ⟨t, ht, ?_⟩
      have hd := (Commute.all z.2 χ).orderOf_mul_dvd_mul_orderOf
      rw [(Finset.mem_filter.mp hχ).2] at hd
      simpa [L, mul_comm] using hd.trans (Nat.mul_dvd_mul ho (dvd_refl t))
  have hB (t : ℕ) (ht : t ∈ T) :
      |((t : ℂ)⁻¹ * ∑ χ ∈ primeCharacters p t,
        weightedTerms p W ((1, 1) :: errorTerms p L) χ).re| ≤
          (1 - (t : ℝ)⁻¹) * r * M := by
    have hb := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun χ hχ => htwist t ht χ hχ))
    rw [Finset.sum_const, nsmul_eq_mul, primeCharacters_card p (hT t ht).2.1,
      Nat.totient_prime (hT t ht).1, Nat.cast_sub (hT t ht).1.one_le, Nat.cast_one] at hb
    have hre : ((t : ℂ)⁻¹ * ∑ χ ∈ primeCharacters p t,
        weightedTerms p W ((1, 1) :: errorTerms p L) χ).re =
        (t : ℝ)⁻¹ * ∑ χ ∈ primeCharacters p t,
          (weightedTerms p W ((1, 1) :: errorTerms p L) χ).re := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, Complex.re_sum]
    rw [hre, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (t : ℝ)⁻¹)]; calc
      _ ≤ (t : ℝ)⁻¹ * (((t : ℝ) - 1) * (r * M)) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by
        have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (hT t ht).1.ne_zero
        field_simp
  have hre : (sieveError p W e T).re =
      delta T * (weightedTerms p W (errorTerms p L) 1).re -
      ∑ t ∈ T, ((t : ℂ)⁻¹ * ∑ χ ∈ primeCharacters p t,
        weightedTerms p W ((1, 1) :: errorTerms p L) χ).re := by
    simp only [sieveError, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum, L]
  rw [hre]; calc
    _ ≤ |delta T * (weightedTerms p W (errorTerms p L) 1).re| +
        |∑ t ∈ T, ((t : ℂ)⁻¹ * ∑ χ ∈ primeCharacters p t,
          weightedTerms p W ((1, 1) :: errorTerms p L) χ).re| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        (delta T * (weightedTerms p W (errorTerms p L) 1).re)
        (∑ t ∈ T, ((t : ℂ)⁻¹ * ∑ χ ∈ primeCharacters p t,
          weightedTerms p W ((1, 1) :: errorTerms p L) χ).re)
    _ ≤ |delta T| * ((r - 1) * M) + ∑ t ∈ T, (1 - (t : ℝ)⁻¹) * r * M := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hE (abs_nonneg _)
      · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hB)
    _ = errorCoefficientAbs e T * M := by
      simp only [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul, mul_one]
      unfold errorCoefficientAbs delta; dsimp only [r]; ring
private lemma weighted_sieve_identity (p : ℕ) [Fact p.Prime] (W : ZMod p → ℝ)
    (e : ℕ) (he : ∀ q ∈ e.primeFactors, q ∣ p - 1) (T : Finset ℕ)
    (hT : ∀ t ∈ T, t.Prime ∧ t ∣ p - 1) :
    ((∑ a : (ZMod p)ˣ, W a *
      (e.primeFactors.toList.map (fun q => localFree p q a)).prod *
        (1 - ∑ t ∈ T, (1 - localFree p t a)) : ℝ) : ℂ) =
      (theta e : ℂ) * ((delta T : ℂ) * (∑ a : (ZMod p)ˣ, W a : ℝ) +
        sieveError p W e T) := by
  let L := e.primeFactors.toList
  let E := fun a : (ZMod p)ˣ => evaluateTerms p (errorTerms p L) a
  let F := fun a : (ZMod p)ˣ => evaluateTerms p ((1, 1) :: errorTerms p L) a
  have hF (a : (ZMod p)ˣ) : F a = 1 + E a := by simp [F, E, evaluateTerms]
  have ht : (L.map (fun q : ℕ => 1 - (q : ℂ)⁻¹)).prod = (theta e : ℂ) := by simp [L, theta]
  have hprod (a : (ZMod p)ˣ) :
      (((L.map (fun q => localFree p q a)).prod : ℝ) : ℂ) =
        (theta e : ℂ) * (1 + E a) := by
    rw [← ht]; exact errorTerms_expansion p L (fun q hq =>
      ⟨Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp hq),
        he q (Finset.mem_toList.mp hq)⟩) a
  have hgap (a : (ZMod p)ˣ) :
      1 - ∑ t ∈ T, (1 - (localFree p t a : ℂ)) = (delta T : ℂ) -
        ∑ t ∈ T, (t : ℂ)⁻¹ * ∑ χ ∈ primeCharacters p t, χ a := by
    have hh := Finset.sum_congr (s₁ := T) rfl (fun t ht =>
      localFree_gap p (hT t ht).1 (hT t ht).2 a)
    rw [hh]; simp only [mul_add, mul_one, Finset.sum_add_distrib, delta,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_sum,
      Complex.ofReal_inv, Complex.ofReal_natCast]
    ring
  let J : ((ZMod p)ˣ → ℂ) →ₗ[ℂ] ℂ := {
    toFun := fun f => ∑ a : (ZMod p)ˣ, (W a : ℂ) * f a
    map_add' := by intro f g; simp [mul_add, Finset.sum_add_distrib]
    map_smul' := by intro c f; simp [Finset.mul_sum, mul_left_comm] }
  have hf :
      (fun a : (ZMod p)ˣ => (((L.map (fun q => localFree p q a)).prod : ℝ) : ℂ) *
        (1 - ∑ t ∈ T, (1 - (localFree p t a : ℂ)))) =
      (theta e : ℂ) • ((delta T : ℂ) • (fun _ : (ZMod p)ˣ => (1 : ℂ)) +
        (delta T : ℂ) • E - ∑ t ∈ T, (t : ℂ)⁻¹ •
          ∑ χ ∈ primeCharacters p t, (fun a : (ZMod p)ˣ => χ a * F a)) := by
    funext a
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul]
    rw [hprod, hgap]; simp_rw [hF]; simp only [← Finset.sum_mul, ← mul_assoc]
    ring
  have hh := congrArg J hf
  simp only [map_smul, map_add, map_sub, map_sum, smul_eq_mul] at hh
  unfold sieveError; simp_rw [weightedTerms_evaluate]
  simpa [J, L, E, F, Complex.ofReal_sum, mul_assoc, add_sub_assoc] using hh
theorem bound_nonneg (p : ℕ) [Fact p.Prime] (W : ZMod p → ℂ) (M : ℝ) (t : ℕ)
    (hM : ∀ χ : DirichletCharacter ℂ p, orderOf χ = Nat.gcd t (p - 1) →
      |(∑ a, W a * χ a).re| ≤ M) : 0 ≤ M := by
  let d := Nat.gcd t (p - 1)
  have hd0 : 0 < d := by
    dsimp [d]; rw [Nat.gcd_comm]
    exact Nat.gcd_pos_of_pos_left _ (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
  have hc : (primeCharacters p d).Nonempty := by
    apply Finset.card_pos.mp
    rw [primeCharacters_card p (Nat.gcd_dvd_right t (p - 1))]
    exact Nat.totient_pos.mpr hd0
  obtain ⟨χ, hχ⟩ := hc
  exact (abs_nonneg _).trans (hM χ (Finset.mem_filter.mp hχ).2)
/-- A two-sided elementary sieve estimate for arbitrary real weights and margins. -/
theorem weighted_sieve_error_bound (p : ℕ) [Fact p.Prime] (W : ZMod p → ℝ)
    (e : ℕ) (he : ∀ q ∈ e.primeFactors, q ∣ p - 1) (T : Finset ℕ)
    (hT : ∀ t ∈ T, t.Prime ∧ t ∣ p - 1 ∧ t ∉ e.primeFactors) (M : ℝ)
    (hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ e.primeFactors, q ∨
        ∃ t ∈ T, orderOf χ ∣ t * (∏ q ∈ e.primeFactors, q)) →
      |(∑ a, (W a : ℂ) * χ a).re| ≤ M) :
    |(∑ a : (ZMod p)ˣ, W a *
        (if ∀ q ∈ e.primeFactors, a ∉ powerSubgroup ((ZMod p)ˣ) q then 1 else 0) *
        (1 - ((T.filter (fun t => a ∈ powerSubgroup ((ZMod p)ˣ) t)).card : ℝ))) -
      theta e * delta T * ∑ a : (ZMod p)ˣ, W a| ≤ theta e * errorCoefficientAbs e T * M := by
  have herr := sieveError_bound p W e he T hT M hM
  have hid := congrArg Complex.re (weighted_sieve_identity p W e he T
    (fun t ht => ⟨(hT t ht).1, (hT t ht).2.1⟩))
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.add_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero] at hid
  have hb : |(∑ a : (ZMod p)ˣ, W a *
        (e.primeFactors.toList.map (fun q => localFree p q a)).prod *
        (1 - ∑ t ∈ T, (1 - localFree p t a))) -
      theta e * delta T * ∑ a : (ZMod p)ˣ, W a| ≤
        theta e * errorCoefficientAbs e T * M := by
    have hh : (∑ a : (ZMod p)ˣ, W a *
        (e.primeFactors.toList.map (fun q => localFree p q a)).prod *
        (1 - ∑ t ∈ T, (1 - localFree p t a))) -
        theta e * delta T * ∑ a : (ZMod p)ˣ, W a =
        theta e * (sieveError p W e T).re := by rw [hid]; ring
    rw [hh, abs_mul, abs_of_pos (theta_pos e)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left herr (theta_pos e).le
  simp_rw [localFree_prod, Finset.mem_toList] at hb
  simpa only [localFree, sub_ite, sub_zero, sub_self, Finset.sum_boole] using hb
/-- The signed-coefficient estimate whenever the coefficient masses agree. -/
theorem weighted_sieve_lower_bound (p : ℕ) [Fact p.Prime] (W : ZMod p → ℝ)
    (e : ℕ) (he : ∀ q ∈ e.primeFactors, q ∣ p - 1) (T : Finset ℕ)
    (hT : ∀ t ∈ T, t.Prime ∧ t ∣ p - 1 ∧ t ∉ e.primeFactors) (M : ℝ)
    (hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      (orderOf χ ∣ ∏ q ∈ e.primeFactors, q ∨
        ∃ t ∈ T, orderOf χ ∣ t * (∏ q ∈ e.primeFactors, q)) →
      |(∑ a, (W a : ℂ) * χ a).re| ≤ M) (hδ : 0 ≤ delta T ∨ e.primeFactors = ∅) :
    |(∑ a : (ZMod p)ˣ, W a *
        (if ∀ q ∈ e.primeFactors, a ∉ powerSubgroup ((ZMod p)ˣ) q then 1 else 0) *
        (1 - ((T.filter (fun t => a ∈ powerSubgroup ((ZMod p)ˣ) t)).card : ℝ))) -
      theta e * delta T * ∑ a : (ZMod p)ˣ, W a| ≤ theta e * errorCoefficient e T * M := by
  rw [← (errorCoefficientAbs_eq e T).mpr hδ]
  exact weighted_sieve_error_bound p W e he T hT M hM

end D5.S3.Arith.PrimitiveRoot.CharacterExpansion
