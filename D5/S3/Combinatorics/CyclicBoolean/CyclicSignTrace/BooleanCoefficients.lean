/- GID: D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/BooleanCoefficients
   mirror-E: none(waiver:capacity-split-support)
   anchors: []
   utility: none
   digest: Boolean coefficient extraction and top-degree derivative constraints. -/

import D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace.Prelude

/-! Boolean coefficient extraction and top-degree derivative constraints. -/

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace

open D5.S3.QuantumBounds.MerminMeasurementDependence (bit_cases)

/-- A squarefree monomial, evaluated on an actual binary word. -/
def booleanMonomial {n : ℕ} (s : Finset (ZMod n)) (z : Word n) : ZMod 2 :=
  ∏ i ∈ s, z i

/-- The indicator word of a finite set of cyclic coordinates. -/
noncomputable def indicatorWord {n : ℕ} (s : Finset (ZMod n)) : Word n :=
  fun i => if i ∈ s then 1 else 0

/-- Boolean coefficient extraction from function values, rather than a formal
polynomial whose evaluation might have a kernel. -/
noncomputable def booleanCoeff {n : ℕ} (f : Word n → ZMod 2)
    (s : Finset (ZMod n)) : ZMod 2 :=
  ∑ t ∈ s.powerset, f (indicatorWord t)

private theorem monomial_indicator {n : ℕ} (s t : Finset (ZMod n)) :
    booleanMonomial s (indicatorWord t) = if s ⊆ t then 1 else 0 := by
  classical
  by_cases h : s ⊆ t
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [indicatorWord, h hi]
  · obtain ⟨i, hi, hit⟩ := Finset.not_subset.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero hi (by simp [indicatorWord, hit])

private theorem subset_parity {n : ℕ} (s t : Finset (ZMod n)) :
    (∑ v ∈ s.powerset, if t ⊆ v then (1 : ZMod 2) else 0) =
      if s = t then 1 else 0 := by
  classical
  induction s using Finset.induction_on generalizing t with
  | empty =>
      simp only [Finset.powerset_empty, Finset.sum_singleton, Finset.subset_empty]
      simp only [eq_comm]
  | @insert i s hi ih =>
      rw [Finset.sum_powerset_insert hi]
      by_cases hit : i ∈ t
      · have hz : (∑ v ∈ s.powerset, if t ⊆ v then (1 : ZMod 2) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro v hv
          have hiv : i ∉ v := fun h => hi ((Finset.mem_powerset.mp hv) h)
          simp [show ¬t ⊆ v from fun h => hiv (h hit)]
        rw [hz, zero_add]
        simp_rw [Finset.subset_insert_iff]
        rw [ih]
        have he : s = t.erase i ↔ insert i s = t := by
          constructor
          · intro h
            rw [h, Finset.insert_erase hit]
          · intro h
            rw [← h, Finset.erase_insert hi]
        simp only [he]
      · have he (v : Finset (ZMod n)) : t ⊆ insert i v ↔ t ⊆ v :=
          Finset.subset_insert_iff_of_notMem hit
        simp_rw [he]
        rw [CharTwo.add_self_eq_zero]
        simp [show insert i s ≠ t from fun h => hit (h ▸ Finset.mem_insert_self i s)]

theorem coeff_monomial {n : ℕ} (s t : Finset (ZMod n)) :
    booleanCoeff (booleanMonomial t) s = if s = t then 1 else 0 := by
  classical
  simp only [booleanCoeff, monomial_indicator]
  exact subset_parity s t

theorem coeff_add {n : ℕ} (f g : Word n → ZMod 2)
    (s : Finset (ZMod n)) :
    booleanCoeff (fun z => f z + g z) s = booleanCoeff f s + booleanCoeff g s := by
  classical
  simp [booleanCoeff, Finset.sum_add_distrib]

theorem coeff_sum {n : ℕ} {ι : Type*} (v : Finset ι)
    (f : ι → Word n → ZMod 2) (s : Finset (ZMod n)) :
    booleanCoeff (fun z => ∑ i ∈ v, f i z) s =
      ∑ i ∈ v, booleanCoeff (f i) s := by
  classical
  simp only [booleanCoeff]
  exact Finset.sum_comm

theorem coeff_mul {n : ℕ} (a : ZMod 2) (f : Word n → ZMod 2)
    (s : Finset (ZMod n)) :
    booleanCoeff (fun z => a * f z) s = a * booleanCoeff f s := by
  classical
  simp [booleanCoeff, Finset.mul_sum]

theorem coeff_constant {n : ℕ} (a : ZMod 2) (s : Finset (ZMod n))
    (hs : s.Nonempty) : booleanCoeff (fun _ : Word n => a) s = 0 := by
  have he : (fun _ : Word n => a) = fun z => a * booleanMonomial ∅ z := by
    funext z
    simp [booleanMonomial]
  rw [he, coeff_mul, coeff_monomial]
  simp [Finset.nonempty_iff_ne_empty.mp hs]

/-- The cyclic variable set in an alternating prefix. -/
def prefixVariables {n : ℕ} (i : ZMod n) (r : ℕ) : Finset (ZMod n) :=
  (Finset.range r).image (fun t => i + (2 * t + 1 : ℕ))

private theorem bit_square (a : ZMod 2) : a * a = a := by
  rcases bit_cases a with rfl | rfl <;> decide

theorem monomial_insert {n : ℕ} (s : Finset (ZMod n))
    (i : ZMod n) (z : Word n) :
    booleanMonomial (insert i s) z = z i * booleanMonomial s z := by
  classical
  by_cases hi : i ∈ s
  · rw [Finset.insert_eq_of_mem hi]
    have hp : booleanMonomial s z = z i * booleanMonomial (s.erase i) z := by
      exact (Finset.mul_prod_erase s z hi).symm
    rw [hp, ← mul_assoc, bit_square]
  · exact Finset.prod_insert hi

private theorem prefix_monomial {n : ℕ} (z : Word n) (i : ZMod n) (r : ℕ) :
    alternatingPrefix (1 + z) i r = booleanMonomial (prefixVariables i r) z := by
  classical
  induction r with
  | zero => simp [alternatingPrefix, prefixVariables, booleanMonomial]
  | succ r ih =>
      have he : prefixVariables i (r + 1) = insert (i + (2 * r + 1 : ℕ))
          (prefixVariables i r) := by
        simp [prefixVariables, Finset.range_add_one, Finset.image_insert]
      rw [he, monomial_insert]
      simp only [alternatingPrefix, Finset.prod_range_succ] at ih ⊢
      rw [ih]
      have hz : 1 + (1 + z) (i + (2 * r + 1 : ℕ)) = z (i + (2 * r + 1 : ℕ)) := by
        change 1 + (1 + z _) = _
        rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      rw [hz, mul_comm]

theorem shifted_inverse_expansion (m : ℕ) (b z : Word (2 * m + 1)) :
    inverseComponent m b (1 + z) =
      ∑ i, ∑ r ∈ Finset.range (m + 1), b i *
        (booleanMonomial (prefixVariables i r) z +
          booleanMonomial (insert (i + (2 * r : ℕ)) (prefixVariables i r)) z) := by
  classical
  simp only [inverseComponent, dot, inverse, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro r _
  rw [prefix_monomial, monomial_insert]
  change b i * (booleanMonomial _ z * (1 + z _)) = _
  ring

/-- Extract the coefficients of the shifted inverse component from its actual
function values. Coincident cyclic variables are identified by finite sets. -/
theorem inverse_component_boolean_coefficient (m : ℕ) (b : Word (2 * m + 1))
    (s : Finset (ZMod (2 * m + 1))) :
    booleanCoeff (fun z => inverseComponent m b (1 + z)) s =
      ∑ i, ∑ r ∈ Finset.range (m + 1), b i *
        ((if s = prefixVariables i r then 1 else 0) +
          (if s = insert (i + (2 * r : ℕ)) (prefixVariables i r) then 1 else 0)) := by
  classical
  have he := funext (shifted_inverse_expansion m b)
  rw [he, coeff_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [coeff_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [coeff_mul, coeff_add, coeff_monomial, coeff_monomial]

/-- The coefficient at s in the derivative of the monomial at t. -/
noncomputable def monomialDerivativeCoeff {n : ℕ} (t s : Finset (ZMod n))
    (u : Word n) : ZMod 2 :=
  (if s ⊆ t then booleanMonomial (t \ s) u else 0) +
    (if s = t then 1 else 0)

private theorem coeff_translated_monomial {n : ℕ} (t s : Finset (ZMod n))
    (u : Word n) :
    booleanCoeff (fun z => booleanMonomial t (z + u)) s =
      if s ⊆ t then booleanMonomial (t \ s) u else 0 := by
  classical
  have he : (fun z => booleanMonomial t (z + u)) =
      fun z => ∑ v ∈ t.powerset,
        booleanMonomial (t \ v) u * booleanMonomial v z := by
    funext z
    simp only [booleanMonomial, Pi.add_apply, Finset.prod_add]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he, coeff_sum]
  simp_rw [coeff_mul, coeff_monomial]
  simp only [mul_ite, mul_one, mul_zero]
  simp [Finset.mem_powerset]

/-- Every nonconstant coefficient of a constant derivative of the actual
inverse component vanishes. This supplies the function-to-coefficient bridge
for the cyclic overlap classification, without assuming that classification. -/
theorem inverse_component_derivative_coefficients (m : ℕ)
    (b u : Word (2 * m + 1))
    (hc : ∃ c, ∀ y, inverseComponent m b (y + u) + inverseComponent m b y = c)
    (s : Finset (ZMod (2 * m + 1))) (hs : s.Nonempty) :
    (∑ i, ∑ r ∈ Finset.range (m + 1), b i *
      (monomialDerivativeCoeff (prefixVariables i r) s u +
        monomialDerivativeCoeff
          (insert (i + (2 * r : ℕ)) (prefixVariables i r)) s u)) = 0 := by
  classical
  obtain ⟨c, hc⟩ := hc
  have hconst : booleanCoeff (fun z =>
      inverseComponent m b (1 + (z + u)) + inverseComponent m b (1 + z)) s = 0 := by
    have he : (fun z => inverseComponent m b (1 + (z + u)) +
        inverseComponent m b (1 + z)) = fun _ => c := by
      funext z
      simpa only [add_assoc] using hc (1 + z)
    rw [he]
    exact coeff_constant c s hs
  have hshift : booleanCoeff (fun z => inverseComponent m b (1 + (z + u))) s =
      ∑ i, ∑ r ∈ Finset.range (m + 1), b i *
        ((if s ⊆ prefixVariables i r then
            booleanMonomial (prefixVariables i r \ s) u else 0) +
          (if s ⊆ insert (i + (2 * r : ℕ)) (prefixVariables i r) then
            booleanMonomial (insert (i + (2 * r : ℕ)) (prefixVariables i r) \ s) u
          else 0)) := by
    have he := funext (fun z => shifted_inverse_expansion m b (z + u))
    rw [he, coeff_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [coeff_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [coeff_mul, coeff_add, coeff_translated_monomial, coeff_translated_monomial]
  rw [coeff_add, hshift, inverse_component_boolean_coefficient] at hconst
  rw [← Finset.sum_add_distrib] at hconst
  convert hconst using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  simp only [monomialDerivativeCoeff]
  ring

/-- The highest-degree variable set in a shifted inverse coordinate. -/
def topVariables (m : ℕ) (i : ZMod (2 * m + 1)) : Finset (ZMod (2 * m + 1)) :=
  insert (i + (2 * m : ℕ)) (prefixVariables i m)

theorem prefix_index_injective (m r : ℕ) (hr : r ≤ m)
    (i : ZMod (2 * m + 1)) :
    Set.InjOn (fun t : ℕ => i + (2 * t + 1 : ℕ)) (Finset.range r) := by
  intro a ha b hb hab
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  have he := (ZMod.natCast_eq_natCast_iff' (2 * a + 1) (2 * b + 1)
    (2 * m + 1)).mp (add_left_cancel hab)
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
  omega

theorem prefix_card (m r : ℕ) (hr : r ≤ m) (i : ZMod (2 * m + 1)) :
    (prefixVariables i r).card = r := by
  rw [prefixVariables, Finset.card_image_of_injOn (prefix_index_injective m r hr i),
    Finset.card_range]

theorem endpoint_not_prefix (m r : ℕ) (hr : r ≤ m)
    (i : ZMod (2 * m + 1)) : i + (2 * r : ℕ) ∉ prefixVariables i r := by
  classical
  intro h
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
  have ha' := Finset.mem_range.mp ha
  have he' := (ZMod.natCast_eq_natCast_iff' (2 * a + 1) (2 * r)
    (2 * m + 1)).mp (add_left_cancel he)
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he'
  omega

theorem top_card (m : ℕ) (i : ZMod (2 * m + 1)) :
    (topVariables m i).card = m + 1 := by
  classical
  rw [topVariables, Finset.card_insert_of_notMem (endpoint_not_prefix m m le_rfl i),
    prefix_card m m le_rfl]

private theorem top_sum (m : ℕ) (i : ZMod (2 * m + 1)) :
    (∑ k ∈ topVariables m i, k) = (m + 1 : ℕ) * i +
      (((2 * m : ℕ) : ZMod (2 * m + 1)) +
        ∑ r ∈ Finset.range m, ((2 * r + 1 : ℕ) : ZMod (2 * m + 1))) := by
  classical
  rw [topVariables, Finset.sum_insert (endpoint_not_prefix m m le_rfl i)]
  unfold prefixVariables
  rw [Finset.sum_image (prefix_index_injective m m le_rfl i)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

private theorem top_injective (m : ℕ) : Function.Injective (topVariables m) := by
  intro i k hik
  have h := congrArg (fun s : Finset (ZMod (2 * m + 1)) => ∑ j ∈ s, j) hik
  rw [top_sum, top_sum] at h
  have he := add_right_cancel h
  have h2 := congrArg (fun z : ZMod (2 * m + 1) => 2 * z) he
  simpa only [← mul_assoc, twice_half, one_mul] using h2

/-- Every highest-degree monomial of the shifted inverse component has exactly
its original mask bit as coefficient, at every positive odd length. -/
theorem inverse_component_top_coefficient (m : ℕ) (b : Word (2 * m + 1))
    (i : ZMod (2 * m + 1)) :
    booleanCoeff (fun z => inverseComponent m b (1 + z)) (topVariables m i) = b i := by
  classical
  rw [inverse_component_boolean_coefficient]
  have hprefix (k : ZMod (2 * m + 1)) (r : ℕ) (hr : r ∈ Finset.range (m + 1)) :
      topVariables m i ≠ prefixVariables k r := by
    intro h
    have hc := congrArg Finset.card h
    rw [top_card, prefix_card m r (by simpa using hr)] at hc
    have := Finset.mem_range.mp hr
    omega
  have hterm (k : ZMod (2 * m + 1)) (r : ℕ) (hr : r ∈ Finset.range (m + 1)) :
      topVariables m i = insert (k + (2 * r : ℕ)) (prefixVariables k r) ↔
        r = m ∧ k = i := by
    constructor
    · intro h
      have hrm : r ≤ m := by simpa using hr
      have hc := congrArg Finset.card h
      rw [top_card, Finset.card_insert_of_notMem (endpoint_not_prefix m r hrm k),
        prefix_card m r hrm] at hc
      have hr' : r = m := by omega
      subst r
      exact ⟨rfl, (top_injective m h).symm⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have hinner (k : ZMod (2 * m + 1)) :
      (∑ r ∈ Finset.range (m + 1), b k *
        ((if topVariables m i = prefixVariables k r then 1 else 0) +
          (if topVariables m i = insert (k + (2 * r : ℕ)) (prefixVariables k r)
          then 1 else 0))) = if k = i then b k else 0 := by
    have he : (∑ r ∈ Finset.range (m + 1), b k *
        ((if topVariables m i = prefixVariables k r then 1 else 0) +
          (if topVariables m i = insert (k + (2 * r : ℕ)) (prefixVariables k r)
          then 1 else 0))) =
        ∑ r ∈ Finset.range (m + 1), if r = m ∧ k = i then b k else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [if_neg (hprefix k r hr), zero_add, hterm k r hr, mul_ite,
        mul_one, mul_zero]
    rw [he]
    by_cases hk : k = i <;> simp [hk]
  simp_rw [hinner]
  simp

private theorem monomial_derivative_degree {n : ℕ} (t s : Finset (ZMod n))
    (u : Word n) (h : t.card ≤ s.card) : monomialDerivativeCoeff t s u = 0 := by
  classical
  by_cases hst : s ⊆ t
  · have he : s = t := Finset.eq_of_subset_of_card_le hst h
    subst t
    simp [monomialDerivativeCoeff, booleanMonomial, CharTwo.add_self_eq_zero]
  · have hne : s ≠ t := fun he => hst (he ▸ Finset.Subset.refl s)
    simp [monomialDerivativeCoeff, hst, hne]

/-- In degree m only deletions from the highest-degree monomials can contribute
to a constant inverse derivative. No cyclic overlap classification is assumed. -/
theorem inverse_component_top_derivative (m : ℕ) (hm : 0 < m)
    (b u : Word (2 * m + 1))
    (hu : u ∈ constantDerivativeSubmodule (inverseComponent m b))
    (s : Finset (ZMod (2 * m + 1))) (hs : s.card = m) :
    (∑ i, b i * (if s ⊆ topVariables m i then
      booleanMonomial (topVariables m i \ s) u else 0)) = 0 := by
  classical
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  have hc := (constantDerivative_affineSpan_duality (inverseComponent m b)).1 u |>.mp hu
  have hcoeff := inverse_component_derivative_coefficients m b u hc s hsne
  have hinner (i : ZMod (2 * m + 1)) :
      (∑ r ∈ Finset.range (m + 1), b i *
        (monomialDerivativeCoeff (prefixVariables i r) s u +
          monomialDerivativeCoeff
            (insert (i + (2 * r : ℕ)) (prefixVariables i r)) s u)) =
      b i * (if s ⊆ topVariables m i then
        booleanMonomial (topVariables m i \ s) u else 0) := by
    rw [Finset.sum_eq_single m]
    · rw [monomial_derivative_degree (prefixVariables i m) s u
        (by rw [prefix_card m m le_rfl, hs])]
      change b i * (0 + monomialDerivativeCoeff (topVariables m i) s u) = _
      have hne : s ≠ topVariables m i := by
        intro he
        have he' := congrArg Finset.card he
        rw [hs, top_card] at he'
        omega
      simp [monomialDerivativeCoeff, hne]
    · intro r hr hrm
      have hr' : r ≤ m := by simpa using hr
      have hrlt : r < m := by omega
      rw [monomial_derivative_degree (prefixVariables i r) s u
          (by rw [prefix_card m r hr', hs]; omega),
        monomial_derivative_degree
          (insert (i + (2 * r : ℕ)) (prefixVariables i r)) s u
          (by rw [Finset.card_insert_of_notMem (endpoint_not_prefix m r hr' i),
            prefix_card m r hr', hs]; omega)]
      simp
    · simp
  simpa only [hinner] using hcoeff


end D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace
