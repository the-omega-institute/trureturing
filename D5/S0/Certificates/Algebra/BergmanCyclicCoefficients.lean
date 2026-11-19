/- GID: D5/S0/Certificates/Algebra/BergmanCyclicCoefficients
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/BergmanCyclicCoefficients
   mirror-E: none(waiver:noncomputational)
   anchors: [mathlib/module/Mathlib.Algebra.Algebra.Unitization, mathlib/module/Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots, mathlib/module/Mathlib.LinearAlgebra.Finsupp.LinearCombination]
   utility: none
   digest: Exact terminal coefficients and span cancellation on cyclic contracted algebras. -/

import D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
import D5.S0.Certificates.Algebra.BergmanContractedAlgebra
import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Exact coefficients on cyclic contracted algebras -/

noncomputable section

namespace D5.S0.Certificates.Algebra.BergmanCyclicCoefficients

open BergmanCyclicSemigroup
open BergmanQuestion15Refutation (Contracted delta positivePower)
open BergmanContractedAlgebra
open scoped BigOperators IsMulCommutative

variable {F : Type*} [Field F]

abbrev Algebra (F : Type*) [Field F] (n : ℕ) (q : Bool) := Contracted F (Model n q)

/-- A linear combination of the actual three generator basis images. -/
def combination (n : ℕ) (q : Bool) (a : Fin 3 → F) : Algebra F n q :=
  ∑ i, a i • delta F (Model n q) (generator n q i)

private def word {d : ℕ} (f : Fin d → Fin 3) : Exponent := List.ofFn f

private theorem word_card {d : ℕ} (f : Fin d → Fin 3) : (word f).card = d := by
  simp [word]

private theorem word_mem {d : ℕ} (f : Fin d → Fin 3) (i : Fin 3) :
    i ∈ word f ↔ ∃ j, f j = i := by
  simp [word, List.mem_ofFn]

private theorem inr_positivePower (n : ℕ) (q : Bool) (v : Algebra F n q) (k : ℕ) :
    (Unitization.inr (positivePower v k) : Unitization F (Algebra F n q)) =
      (Unitization.inr v) ^ (k + 1) := by
  induction k with
  | zero => simp [positivePower]
  | succ k ih =>
    rw [positivePower, Unitization.inr_mul, ih]
    exact (pow_succ _ _).symm

private theorem word_product (n : ℕ) (q : Bool) (a : Fin 3 → F) (k : ℕ)
    (f : Fin (k + 1) → Fin 3) :
    (∏ j, Unitization.inr (a (f j) • delta F (Model n q) (generator n q (f j))) :
      Unitization F (Algebra F n q)) =
    Unitization.inr ((∏ j, a (f j)) • delta F (Model n q) (normal n q (word f))) := by
  induction k with
  | zero => simp [Fin.prod_univ_succ, word, List.ofFn_succ, generator]
  | succ k ih =>
    have hw : ({f 0} : Exponent) + word (fun j => f j.succ) = word f := by
      simp [word, List.ofFn_succ]
    have hp := normal_mul (n := n) (q := q) {f 0} (word (fun j => f j.succ))
      (by simp) (by rw [word_card]; omega)
    rw [hw] at hp
    rw [Fin.prod_univ_succ, ih]
    rw [← Unitization.inr_mul, smul_mul_assoc, mul_smul_comm, delta_mul, smul_smul]
    change Unitization.inr ((_ * _) • delta F (Model n q)
      (normal n q {f 0} * normal n q (word (fun j => f j.succ)))) = _
    rw [hp]
    simp only [Fin.prod_univ_succ]

private theorem power_expansion (n : ℕ) (q : Bool) (a : Fin 3 → F) (k : ℕ) :
    positivePower (combination n q a) k =
      ∑ f : Fin (k + 1) → Fin 3,
        (∏ j, a (f j)) • delta F (Model n q) (normal n q (word f)) := by
  apply Unitization.inr_injective (R := F)
  rw [inr_positivePower]
  have hsum : (Unitization.inr (combination n q a) : Unitization F (Algebra F n q)) =
      ∑ i, Unitization.inr (a i • delta F (Model n q) (generator n q i)) := by
    exact map_sum (Unitization.inrHom F F (Algebra F n q)) _ _
  rw [hsum, Fintype.sum_pow]
  simp_rw [word_product]
  exact (map_sum (Unitization.inrHom F F (Algebra F n q)) _ _).symm

private def avoid (i : Fin 3) (j : Fin 3) : F := if j ≠ i then 1 else 0
private def only (i : Fin 3) (j : Fin 3) : F := if j = i then 1 else 0

private theorem avoid_product {d : ℕ} (f : Fin d → Fin 3) (i : Fin 3) :
    (∏ j, avoid (F := F) i (f j)) = if i ∉ word f then 1 else 0 := by
  simp only [avoid, Fintype.prod_boole, word_mem, not_exists]
  congr 1

private theorem only_product {d : ℕ} (f : Fin d → Fin 3) (i j k : Fin 3)
    (h : ∀ x : Fin 3, x = i ↔ x ≠ j ∧ x ≠ k) :
    (∏ l, only (F := F) i (f l)) = if j ∉ word f ∧ k ∉ word f then 1 else 0 := by
  simp only [only, Fintype.prod_boole, word_mem, not_exists]
  congr 1
  simp only [h, forall_and]

private theorem terminal_word (n : ℕ) (hn : 0 < n) (q : Bool) (f : Fin n → Fin 3) :
    delta F (Model n q) (normal n q (word f)) =
      ((∏ j, avoid (F := F) 2 (f j)) - ∏ j, only (F := F) 1 (f j)) •
        delta F (Model n q) (.terminal 0) +
      ((∏ j, avoid (F := F) 0 (f j)) - ∏ j, only (F := F) 2 (f j)) •
        delta F (Model n q) (.terminal 1) +
      ((∏ j, avoid (F := F) 1 (f j)) - ∏ j, only (F := F) 0 (f j)) •
        delta F (Model n q) (.terminal 2) := by
  rw [avoid_product, avoid_product, avoid_product]
  rw [only_product f 1 0 2 (by intro x; fin_cases x <;> decide),
    only_product f 2 0 1 (by intro x; fin_cases x <;> decide),
    only_product f 0 1 2 (by intro x; fin_cases x <;> decide)]
  have hp : ∃ i, i ∈ word f := Multiset.card_pos_iff_exists_mem.mp (by rwa [word_card])
  have hd := word_card f
  simp only [normal, hd, lt_self_iff_false, and_false, false_and, dite_false,
    hn, and_self, if_true]
  rcases hp with ⟨i, hi⟩
  fin_cases i <;>
    by_cases h0 : (0 : Fin 3) ∈ word f <;>
    by_cases h1 : (1 : Fin 3) ∈ word f <;>
    by_cases h2 : (2 : Fin 3) ∈ word f <;>
    simp_all [terminalLabel, delta]

private theorem filtered_sum (a w : Fin 3 → F) (n : ℕ) :
    (∑ f : Fin n → Fin 3, (∏ j, a (f j)) * ∏ j, w (f j)) =
      (∑ i, a i * w i) ^ n := by
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.sum_pow (fun i => a i * w i) n).symm

/-- Complete terminal support and coefficients, for every positive exponent and either presentation. -/
theorem terminal_coefficients (n : ℕ) (hn : 0 < n) (q : Bool) (a : Fin 3 → F) :
    positivePower (combination n q a) (n - 1) =
      ((a 0 + a 1) ^ n - (a 1) ^ n) • delta F (Model n q) (.terminal 0) +
      ((a 1 + a 2) ^ n - (a 2) ^ n) • delta F (Model n q) (.terminal 1) +
      ((a 2 + a 0) ^ n - (a 0) ^ n) • delta F (Model n q) (.terminal 2) := by
  have he : n - 1 + 1 = n := by omega
  have hexp := power_expansion n q a (n - 1)
  rw [he] at hexp
  rw [hexp]
  simp_rw [terminal_word (F := F) n hn q]
  simp_rw [smul_add, smul_smul, mul_sub]
  simp only [Finset.sum_add_distrib, ← Finset.sum_smul, Finset.sum_sub_distrib]
  simp_rw [filtered_sum]
  simp [avoid, only, Fin.sum_univ_succ, add_comm]
  congr 2 <;> ring

private theorem generator_survives (q : Bool) (i : Fin 3) :
    survives q ({i} : Exponent) := by
  fin_cases i <;> simp [survives, mixed]

private theorem generator_ne_zero (n : ℕ) (hn : 2 ≤ n) (q : Bool) (i : Fin 3) :
    generator n q i ≠ 0 := by
  simp [generator, normal, generator_survives, show 1 < n by omega]

private theorem generator_eq (n : ℕ) (hn : 2 ≤ n) (q : Bool) (i j : Fin 3) :
    generator n q i = generator n q j ↔ i = j := by
  simp [generator, normal, generator_survives, show 1 < n by omega]

private theorem combination_coordinate (n : ℕ) (hn : 2 ≤ n) (q : Bool)
    (a : Fin 3 → F) (i : Fin 3) :
    combination n q a ⟨generator n q i, generator_ne_zero n hn q i⟩ = a i := by
  classical
  simp [combination, delta, generator_ne_zero n hn q, Finsupp.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, generator_eq n hn q, eq_comm]

private theorem combination_zero_iff (n : ℕ) (hn : 2 ≤ n) (q : Bool)
    (a : Fin 3 → F) : combination n q a = 0 ↔ a = 0 := by
  constructor
  · intro h
    funext i
    have := congrArg (fun v : Algebra F n q =>
      v ⟨generator n q i, generator_ne_zero n hn q i⟩) h
    simpa only [combination_coordinate n hn q a i, Finsupp.zero_apply,
      Pi.zero_apply] using this
  · rintro rfl
    simp [combination]

private theorem power_zero_iff (n : ℕ) (hn : 0 < n) (q : Bool) (a : Fin 3 → F) :
    positivePower (combination n q a) (n - 1) = 0 ↔
      (a 0 + a 1) ^ n = a 1 ^ n ∧
      (a 1 + a 2) ^ n = a 2 ^ n ∧
      (a 2 + a 0) ^ n = a 0 ^ n := by
  rw [terminal_coefficients n hn q]
  constructor
  · intro h
    have h0 := congrArg (fun v : Algebra F n q =>
      v ⟨.terminal 0, by intro h; cases h⟩) h
    have h1 := congrArg (fun v : Algebra F n q =>
      v ⟨.terminal 1, by intro h; cases h⟩) h
    have h2 := congrArg (fun v : Algebra F n q =>
      v ⟨.terminal 2, by intro h; cases h⟩) h
    simpa [delta, sub_eq_zero] using And.intro h0 (And.intro h1 h2)
  · rintro ⟨h0, h1, h2⟩
    simp [h0, h1, h2]

private theorem zero_coordinate (n : ℕ) (hn : 0 < n) (a : Fin 3 → F)
    (h : (a 0 + a 1) ^ n = a 1 ^ n ∧
      (a 1 + a 2) ^ n = a 2 ^ n ∧ (a 2 + a 0) ^ n = a 0 ^ n)
    (hz : ∃ i, a i = 0) : a = 0 := by
  rcases h with ⟨h0, h1, h2⟩
  rcases hz with ⟨i, hi⟩
  have hp (x : F) (hx : x ^ n = 0) : x = 0 := (pow_eq_zero_iff hn.ne').mp hx
  fin_cases i
  · change a 0 = 0 at hi
    have hc : a 2 = 0 := hp _ (by simpa [hi, hn.ne'] using h2)
    have hb : a 1 = 0 := hp _ (by simpa [hc, hn.ne'] using h1)
    funext i; fin_cases i <;> simp [hi, hb, hc]
  · change a 1 = 0 at hi
    have ha : a 0 = 0 := hp _ (by simpa [hi, hn.ne'] using h0)
    have hc : a 2 = 0 := hp _ (by simpa [ha, hn.ne'] using h2)
    funext i; fin_cases i <;> simp [hi, ha, hc]
  · change a 2 = 0 at hi
    have hb : a 1 = 0 := hp _ (by simpa [hi, hn.ne'] using h1)
    have ha : a 0 = 0 := hp _ (by simpa [hb, hn.ne'] using h0)
    funext i; fin_cases i <;> simp [hi, ha, hb]

/-- Every two-generator coordinate span has no nonzero nth-power zero vector. -/
private theorem two_generator_nonvanishing (n : ℕ) (hn : 2 ≤ n) (q : Bool)
    (a : Fin 3 → F) (hz : ∃ i, a i = 0) (ha : combination n q a ≠ 0) :
    positivePower (combination n q a) (n - 1) ≠ 0 := by
  intro h
  exact ha ((combination_zero_iff n hn q a).mpr
    (zero_coordinate n (by omega) a ((power_zero_iff n (by omega) q a).mp h) hz))

private theorem combination_mem_span (n : ℕ) (q : Bool) (a : Fin 3 → F) :
    combination n q a ∈ Submodule.span F
      (Set.range (fun i => delta F (Model n q) (generator n q i))) := by
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- On either actual algebra, a primitive cube root gives a nonzero span witness
for every positive exponent divisible by six. -/
theorem root_witness (n : ℕ) (hn : 0 < n) (hdiv : 6 ∣ n) (q : Bool)
    (ω : F) (hω : IsPrimitiveRoot ω 3) :
    ∃ v ∈ Submodule.span F
      (Set.range (fun i => delta F (Model n q) (generator n q i))),
      v ≠ 0 ∧ positivePower v (n - 1) = 0 := by
  have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := hdiv; omega
  let a : Fin 3 → F := ![1, ω, ω ^ 2]
  refine ⟨combination n q a, combination_mem_span n q a, ?_, ?_⟩
  · intro hz
    have hz' := congrFun ((combination_zero_iff n hn2 q a).mp hz) 0
    norm_num [a] at hz'
  · apply (power_zero_iff n hn q a).mpr
    have hsum : 1 + ω + ω ^ 2 = 0 := by
      simpa [Finset.sum_range_succ, add_assoc] using hω.geom_sum_eq_zero (by decide)
    have hA : 1 + ω = -(ω ^ 2) := by linear_combination hsum
    have hB : ω + ω ^ 2 = -1 := by linear_combination hsum
    have hC : ω ^ 2 + 1 = -ω := by linear_combination hsum
    have hpow : ω ^ n = 1 :=
      (hω.pow_eq_one_iff_dvd n).mpr (dvd_trans (by decide : 3 ∣ 6) hdiv)
    have hpow2 : (ω ^ 2) ^ n = 1 := by
      rw [← pow_mul, Nat.mul_comm 2 n, pow_mul, hpow, one_pow]
    have heven : Even n := even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 6) hdiv)
    change (1 + ω) ^ n = ω ^ n ∧
      (ω + ω ^ 2) ^ n = (ω ^ 2) ^ n ∧ (ω ^ 2 + 1) ^ n = 1 ^ n
    simp [hA, hB, hC, heven.neg_pow, hpow, hpow2]

private theorem root_of_quadratic [CharZero F] (x : F) (h : x ^ 2 + x + 1 = 0) :
    IsPrimitiveRoot x 3 := by
  have h3 : x ^ 3 = 1 := by linear_combination (x - 1) * h
  have hne : x ≠ 1 := by intro hx; subst x; norm_num at h
  apply IsPrimitiveRoot.mk_of_lt x (by decide) h3
  intro l hl hlt
  interval_cases l
  · simpa using hne
  · intro hx
    apply hne
    calc
      x = x ^ 3 := by rw [show 3 = 2 + 1 from rfl, pow_succ, hx, one_mul]
      _ = 1 := h3

private theorem sixth_roots [CharZero F]
    (hno : ¬ ∃ ω : F, IsPrimitiveRoot ω 3) (x : F) (h : x ^ 6 = 1) :
    x = 1 ∨ x = -1 := by
  have hf : (x - 1) * (x + 1) * (x ^ 2 + x + 1) * (x ^ 2 - x + 1) = 0 := by
    calc
      _ = x ^ 6 - 1 := by ring
      _ = 0 := sub_eq_zero.mpr h
  rcases mul_eq_zero.mp hf with hleft | hlast
  · rcases mul_eq_zero.mp hleft with hleft | hquad
    · rcases mul_eq_zero.mp hleft with hp | hm
      · exact Or.inl (sub_eq_zero.mp hp)
      · exact Or.inr (by linear_combination hm)
    · exact (hno ⟨x, root_of_quadratic x hquad⟩).elim
  · exact (hno ⟨-x, root_of_quadratic (-x) (by linear_combination hlast)⟩).elim

private theorem cancellation_requires_root [CharZero F] (a : Fin 3 → F)
    (ha : a ≠ 0)
    (h : (a 0 + a 1) ^ 6 = a 1 ^ 6 ∧
      (a 1 + a 2) ^ 6 = a 2 ^ 6 ∧ (a 2 + a 0) ^ 6 = a 0 ^ 6) :
    ∃ ω : F, IsPrimitiveRoot ω 3 := by
  by_contra hno
  have hne (i : Fin 3) : a i ≠ 0 := by
    intro hz
    exact ha (zero_coordinate 6 (by decide) a h ⟨i, hz⟩)
  have ratio (x y : F) (hx : x ≠ 0) (hy : y ≠ 0)
      (hxy : (x + y) ^ 6 = y ^ 6) : x = -2 * y := by
    have hr : ((x + y) / y) ^ 6 = 1 := by rw [div_pow, hxy, div_self (pow_ne_zero _ hy)]
    have hrne : (x + y) / y ≠ 1 := by
      intro hz
      have := (div_eq_one_iff_eq hy).mp hz
      exact hx (by linear_combination this)
    have hm := (sixth_roots hno _ hr).resolve_left hrne
    have he := (div_eq_iff hy).mp hm
    linear_combination he
  have hab := ratio (a 0) (a 1) (hne 0) (hne 1) h.1
  have hbc := ratio (a 1) (a 2) (hne 1) (hne 2) h.2.1
  have hca := ratio (a 2) (a 0) (hne 2) (hne 0) h.2.2
  have hz : (9 : F) * a 0 = 0 := by linear_combination hab - 2 * hbc + 4 * hca
  exact hne 0 ((mul_eq_zero.mp hz).resolve_left (by norm_num))

/-- The exact field criterion on each of the two n=6 contracted algebras. -/
theorem sixth_power_criterion [CharZero F] (q : Bool) :
    (∃ v ∈ Submodule.span F
      (Set.range (fun i => delta F (Model 6 q) (generator 6 q i))),
      v ≠ 0 ∧ positivePower v 5 = 0) ↔ ∃ ω : F, IsPrimitiveRoot ω 3 := by
  constructor
  · rintro ⟨v, hv, hne, hp⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hv
    change combination 6 q a = v at ha
    subst v
    exact cancellation_requires_root a
      (fun hz => hne ((combination_zero_iff 6 (by decide) q a).mpr hz))
      ((power_zero_iff 6 (by decide) q a).mp hp)
  · rintro ⟨ω, hω⟩
    exact root_witness 6 (by decide) (by decide) q ω hω

/-- Each of the three actual spans obtained by omitting one generator has no
nonzero nth-power-zero element. -/
theorem pair_span_nonvanishing (n : ℕ) (hn : 2 ≤ n) (q : Bool) (i : Fin 3)
    (v : Algebra F n q)
    (hv : v ∈ Submodule.span F (Set.range (fun j : {j : Fin 3 // j ≠ i} =>
      delta F (Model n q) (generator n q j.val)))) (hne : v ≠ 0) :
    positivePower v (n - 1) ≠ 0 := by
  have hvfull : v ∈ Submodule.span F
      (Set.range (fun j => delta F (Model n q) (generator n q j))) := by
    apply Submodule.span_mono _ hv
    rintro x ⟨j, rfl⟩
    exact ⟨j.val, rfl⟩
  have hcoord : v ⟨generator n q i, generator_ne_zero n hn q i⟩ = 0 := by
    clear hne hvfull
    induction hv using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨j, rfl⟩
      simp [delta, generator_ne_zero n hn q, Finsupp.single_apply,
        generator_eq n hn q, j.property]
    | zero => rfl
    | add x y hx hy ihx ihy => simp [ihx, ihy]
    | smul r x hx ih => simp [ih]
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hvfull
  change combination n q a = v at ha
  subst v
  have hai : a i = 0 := by rwa [combination_coordinate n hn q a i] at hcoord
  exact two_generator_nonvanishing n hn q a ⟨i, hai⟩ hne

end D5.S0.Certificates.Algebra.BergmanCyclicCoefficients
