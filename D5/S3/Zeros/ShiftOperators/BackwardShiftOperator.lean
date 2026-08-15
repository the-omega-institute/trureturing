/- GID: D5/S3/Zeros/ShiftOperators/BackwardShiftOperator
   generality: I
   mirror-B: D5/B/S3/Zeros/ShiftOperators/BackwardShiftOperator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Realize the backward address shift as a contraction adjoint with truncated ket action. -/

import D5.S3.Zeros.SpectralShift

namespace D5.S3.Zeros.ShiftOperators.BackwardShiftOperator

open D5.S1.Digit
open D5.S3.Weil.SpectralHilbert
open D5.S3.Zeros.SpectralShift
open scoped ComplexConjugate

attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq PrimeAxisTable := Classical.decEq _

/-- Divide a prime-axis address by `u`; its laws are used only under the corresponding
divisibility hypothesis. -/
noncomputable def normalizedTableSub (b u : PrimeAxisTable) : PrimeAxisTable :=
  primeAxisEncoding.symm (PNat.divExact (primeAxisEncoding b) (primeAxisEncoding u))

/-- Multiplication by a fixed prime-axis address is injective. -/
theorem normalizedTableAdd_right_injective (u : PrimeAxisTable) :
    Function.Injective fun a : PrimeAxisTable => normalizedTableAdd a u := by
  intro a b hab
  apply primeAxisEncoding.injective
  have h := congrArg primeAxisEncoding hab
  simp only [normalizedTableAdd, Equiv.apply_symm_apply] at h
  exact mul_right_cancel h

/-- Exact subtraction followed by addition recovers a divisible address. -/
theorem normalizedTableSub_add_cancel {b u : PrimeAxisTable}
    (h : primeAxisEncoding u ∣ primeAxisEncoding b) :
    normalizedTableAdd (normalizedTableSub b u) u = b := by
  apply primeAxisEncoding.injective
  simp only [normalizedTableAdd, normalizedTableSub, Equiv.apply_symm_apply]
  rw [mul_comm, PNat.mul_div_exact h]

private theorem normalizedTableAdd_dvd (a u : PrimeAxisTable) :
    primeAxisEncoding u ∣ primeAxisEncoding (normalizedTableAdd a u) := by
  refine ⟨primeAxisEncoding a, ?_⟩
  simp [normalizedTableAdd, mul_comm]

private theorem backwardShift_memℓp (u : PrimeAxisTable) (x : ZetaHilbertSpace) :
    Memℓp (backwardShift u x) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hx := (lp.memℓp x).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  simpa [backwardShift, Function.comp_def] using
    hx.comp_injective (normalizedTableAdd_right_injective u)

/-- The coefficient pullback from the frozen `backwardShift`, bundled linearly on the
repository's zeta Hilbert space. -/
noncomputable def backwardShiftLinearMap (u : PrimeAxisTable) :
    ZetaHilbertSpace →ₗ[ℂ] ZetaHilbertSpace where
  toFun x := ⟨backwardShift u x, backwardShift_memℓp u x⟩
  map_add' x y := by
    ext a
    rfl
  map_smul' c x := by
    ext a
    rfl

/-- Pullback along multiplication by `u` is norm-nonincreasing. -/
theorem backwardShiftLinearMap_norm_nonincreasing (u : PrimeAxisTable)
    (x : ZetaHilbertSpace) : ‖backwardShiftLinearMap u x‖ ≤ ‖x‖ := by
  let f : PrimeAxisTable → PrimeAxisTable := fun a => normalizedTableAdd a u
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hx : Summable fun a : PrimeAxisTable => ‖x a‖ ^ (2 : ENNReal).toReal :=
    (lp.memℓp x).summable hp
  apply lp.norm_le_of_tsum_le hp (norm_nonneg x)
  calc
    (∑' a : PrimeAxisTable, ‖backwardShiftLinearMap u x a‖ ^ (2 : ENNReal).toReal) =
        ∑' a : PrimeAxisTable, (fun b => ‖x b‖ ^ (2 : ENNReal).toReal) (f a) := by
      rfl
    _ ≤ ∑' b : PrimeAxisTable, ‖x b‖ ^ (2 : ENNReal).toReal :=
      tsum_comp_le_tsum_of_inj hx (fun _ => by positivity)
        (normalizedTableAdd_right_injective u)
    _ = ‖x‖ ^ (2 : ENNReal).toReal := (lp.norm_rpow_eq_tsum hp x).symm

/-- The frozen backward shift as an actual bounded operator on `ZetaHilbertSpace`. -/
noncomputable def backwardShiftCLM (u : PrimeAxisTable) :
    ZetaHilbertSpace →L[ℂ] ZetaHilbertSpace :=
  (backwardShiftLinearMap u).mkContinuous 1 fun x => by
    simpa using backwardShiftLinearMap_norm_nonincreasing u x

@[simp]
theorem backwardShiftCLM_apply (u : PrimeAxisTable) (x : ZetaHilbertSpace)
    (a : PrimeAxisTable) : backwardShiftCLM u x a = backwardShift u x a :=
  rfl

/-- The backward-shift operator norm is at most one. -/
theorem backward_shift_operator_norm_le_one (u : PrimeAxisTable) :
    ‖backwardShiftCLM u‖ ≤ 1 :=
  (backwardShiftCLM u).opNorm_le_bound zero_le_one fun x => by
    change ‖backwardShiftLinearMap u x‖ ≤ 1 * ‖x‖
    simpa using backwardShiftLinearMap_norm_nonincreasing u x

private noncomputable def forwardTranslationFamily (u : PrimeAxisTable)
    (x : ZetaHilbertSpace) : PrimeAxisTable → ℂ :=
  Function.extend (fun a : PrimeAxisTable => normalizedTableAdd a u) x 0

private theorem forwardTranslationFamily_norm_rpow (u : PrimeAxisTable)
    (x : ZetaHilbertSpace) (b : PrimeAxisTable) :
    ‖forwardTranslationFamily u x b‖ ^ (2 : ENNReal).toReal =
      Function.extend (fun a : PrimeAxisTable => normalizedTableAdd a u)
        (fun a => ‖x a‖ ^ (2 : ENNReal).toReal) 0 b := by
  by_cases hb : ∃ a, normalizedTableAdd a u = b
  · obtain ⟨a, rfl⟩ := hb
    simp [forwardTranslationFamily, normalizedTableAdd_right_injective]
  · simp [forwardTranslationFamily, Function.extend_apply', hb]

private theorem forwardTranslation_memℓp (u : PrimeAxisTable) (x : ZetaHilbertSpace) :
    Memℓp (forwardTranslationFamily u x) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hx : Summable fun a : PrimeAxisTable => ‖x a‖ ^ (2 : ENNReal).toReal :=
    (lp.memℓp x).summable (by norm_num)
  have hext : Summable (Function.extend
      (fun a : PrimeAxisTable => normalizedTableAdd a u)
      (fun a => ‖x a‖ ^ (2 : ENNReal).toReal) 0) :=
    (summable_extend_zero (normalizedTableAdd_right_injective u)).2 hx
  exact hext.congr fun b => (forwardTranslationFamily_norm_rpow u x b).symm

private theorem forwardTranslationFamily_add (u : PrimeAxisTable)
    (x y : ZetaHilbertSpace) :
    forwardTranslationFamily u (x + y) =
      forwardTranslationFamily u x + forwardTranslationFamily u y := by
  funext b
  by_cases hb : ∃ a, normalizedTableAdd a u = b
  · obtain ⟨a, rfl⟩ := hb
    simp only [forwardTranslationFamily, (normalizedTableAdd_right_injective u).extend_apply,
      lp.coeFn_add, Pi.add_apply]
  · simp only [forwardTranslationFamily, Function.extend_apply' _ _ _ hb,
      Pi.add_apply, Pi.zero_apply, add_zero]

private theorem forwardTranslationFamily_smul (u : PrimeAxisTable) (c : ℂ)
    (x : ZetaHilbertSpace) :
    forwardTranslationFamily u (c • x) = c • forwardTranslationFamily u x := by
  funext b
  by_cases hb : ∃ a, normalizedTableAdd a u = b
  · obtain ⟨a, rfl⟩ := hb
    simp [forwardTranslationFamily, normalizedTableAdd_right_injective]
  · simp [forwardTranslationFamily, Function.extend_apply', hb]

/-- Zero-extension along multiplicative address translation, constructed independently of
the backward operator. -/
noncomputable def forwardTranslationLinearMap (u : PrimeAxisTable) :
    ZetaHilbertSpace →ₗ[ℂ] ZetaHilbertSpace where
  toFun x := ⟨forwardTranslationFamily u x, forwardTranslation_memℓp u x⟩
  map_add' x y := by
    ext b
    exact congrFun (forwardTranslationFamily_add u x y) b
  map_smul' c x := by
    ext b
    exact congrFun (forwardTranslationFamily_smul u c x) b

/-- Zero-extension along an injective translation is norm-nonincreasing. -/
theorem forwardTranslationLinearMap_norm_nonincreasing (u : PrimeAxisTable)
    (x : ZetaHilbertSpace) : ‖forwardTranslationLinearMap u x‖ ≤ ‖x‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  apply lp.norm_le_of_tsum_le hp (norm_nonneg x)
  calc
    (∑' b : PrimeAxisTable,
        ‖forwardTranslationLinearMap u x b‖ ^ (2 : ENNReal).toReal) =
        ∑' b : PrimeAxisTable,
          Function.extend (fun a : PrimeAxisTable => normalizedTableAdd a u)
            (fun a => ‖x a‖ ^ (2 : ENNReal).toReal) 0 b := by
      congr 1
      funext b
      exact forwardTranslationFamily_norm_rpow u x b
    _ = ∑' a : PrimeAxisTable, ‖x a‖ ^ (2 : ENNReal).toReal :=
      tsum_extend_zero (normalizedTableAdd_right_injective u) _
    _ ≤ ‖x‖ ^ (2 : ENNReal).toReal :=
      le_of_eq (lp.norm_rpow_eq_tsum hp x).symm

/-- The multiplicative translation on the Hilbert space, by zero-extension off its image. -/
noncomputable def forwardTranslationCLM (u : PrimeAxisTable) :
    ZetaHilbertSpace →L[ℂ] ZetaHilbertSpace :=
  (forwardTranslationLinearMap u).mkContinuous 1 fun x => by
    simpa using forwardTranslationLinearMap_norm_nonincreasing u x

@[simp]
theorem forwardTranslationCLM_apply (u : PrimeAxisTable) (x : ZetaHilbertSpace)
    (b : PrimeAxisTable) :
    forwardTranslationCLM u x b = forwardTranslationFamily u x b :=
  rfl

/-- In the frozen source pairing convention, the backward shift is the adjoint of the
honestly constructed multiplicative translation. -/
theorem backward_shift_sourcePairing_adjoint (u : PrimeAxisTable)
    (x y : ZetaHilbertSpace) :
    sourcePairing (backwardShiftCLM u x) y =
      sourcePairing x (forwardTranslationCLM u y) := by
  rw [source_pairing_eq_tsum, source_pairing_eq_tsum]
  let f : PrimeAxisTable → PrimeAxisTable := fun a => normalizedTableAdd a u
  have hf : Function.Injective f := normalizedTableAdd_right_injective u
  have hfamily :
      (fun b : PrimeAxisTable => x b * conj (forwardTranslationCLM u y b)) =
        Function.extend f (fun a => x (f a) * conj (y a)) 0 := by
    funext b
    by_cases hb : ∃ a, f a = b
    · obtain ⟨a, rfl⟩ := hb
      simp [f, forwardTranslationCLM_apply, forwardTranslationFamily, hf]
    · have hb' : ¬∃ a, normalizedTableAdd a u = b := by
        simpa [f] using hb
      change x b * conj
          (Function.extend (fun a : PrimeAxisTable => normalizedTableAdd a u) y 0 b) =
        Function.extend f (fun a => x (f a) * conj (y a)) 0 b
      rw [Function.extend_apply' _ _ _ hb', Function.extend_apply' _ _ _ hb]
      simp
  calc
    (∑' a : PrimeAxisTable, backwardShiftCLM u x a * conj (y a)) =
        ∑' a : PrimeAxisTable, x (f a) * conj (y a) := by rfl
    _ = ∑' b : PrimeAxisTable,
        Function.extend f (fun a => x (f a) * conj (y a)) 0 b :=
      (tsum_extend_zero hf _).symm
    _ = ∑' b : PrimeAxisTable, x b * conj (forwardTranslationCLM u y b) := by
      rw [← hfamily]

/-- On a divisible basis ket, the backward shift subtracts the translating address. -/
theorem backward_shift_basis_of_dvd (u b : PrimeAxisTable)
    (h : primeAxisEncoding u ∣ primeAxisEncoding b) :
    backwardShiftCLM u (lp.single 2 b (1 : ℂ)) =
      lp.single 2 (normalizedTableSub b u) (1 : ℂ) := by
  classical
  ext a
  by_cases ha : a = normalizedTableSub b u
  · subst a
    simp only [backwardShiftCLM_apply, backwardShift,
      normalizedTableSub_add_cancel h, lp.single_apply_self]
  · have hadd : normalizedTableAdd a u ≠ b := by
      intro hab
      apply ha
      exact (normalizedTableAdd_right_injective u)
        (hab.trans (normalizedTableSub_add_cancel h).symm)
    simp [backwardShiftCLM_apply, backwardShift, hadd, ha]

/-- On a nondivisible basis ket, the backward shift truncates to zero. -/
theorem backward_shift_basis_of_not_dvd (u b : PrimeAxisTable)
    (h : ¬primeAxisEncoding u ∣ primeAxisEncoding b) :
    backwardShiftCLM u (lp.single 2 b (1 : ℂ)) = 0 := by
  classical
  ext a
  have hadd : normalizedTableAdd a u ≠ b := by
    intro hab
    apply h
    rw [← hab]
    exact normalizedTableAdd_dvd a u
  simp [backwardShiftCLM_apply, backwardShift, hadd]

/-- Basis-ket subtraction with truncation: `T_u* |b⟩` is `|b-u⟩` exactly when `u`
divides `b`, and is zero otherwise. -/
theorem backward_shift_basis_subtraction (u b : PrimeAxisTable) :
    backwardShiftCLM u (lp.single 2 b (1 : ℂ)) =
      if primeAxisEncoding u ∣ primeAxisEncoding b then
        lp.single 2 (normalizedTableSub b u) (1 : ℂ)
      else 0 := by
  by_cases h : primeAxisEncoding u ∣ primeAxisEncoding b
  · rw [if_pos h, backward_shift_basis_of_dvd u b h]
  · rw [if_neg h, backward_shift_basis_of_not_dvd u b h]

example : Nonempty ZetaHilbertSpace := ⟨0⟩

example (u : PrimeAxisTable) :
    primeAxisEncoding u ∣ primeAxisEncoding (normalizedTableAdd u u) :=
  normalizedTableAdd_dvd u u

#print axioms backward_shift_operator_norm_le_one
#print axioms backward_shift_sourcePairing_adjoint
#print axioms backward_shift_basis_subtraction

end D5.S3.Zeros.ShiftOperators.BackwardShiftOperator
