/- GID: D5/S3/ArithUnits/MercaQuarticCharacter
   generality: G
   mirror-B: D5/B/S3/ArithUnits/MercaQuarticCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The unique normalized quartic character at primes congruent to five modulo eight. -/

import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
The orientation is the one used in the Ma--Zhang historical note: the value
at two is `I`. The construction uses a genuine cyclic generator only as an
auxiliary choice. It does not assert that two generates the unit group.
-/

set_option autoImplicit false
noncomputable section

namespace D5.S3.ArithUnits.MercaQuarticCharacter

private lemma generator_two_exponent (r : ℕ) [Fact r.Prime]
    (hr : r % 8 = 5) (g : (ZMod r)ˣ)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ∃ j : ℕ, (g : ZMod r) ^ j = 2 ∧ Odd j := by
  have hr2 : r ≠ 2 := by omega
  have htwo : (2 : ZMod r) ≠ 0 :=
    Ring.two_ne_zero ((ZMod.ringChar_zmod_n r).substr hr2)
  let u : (ZMod r)ˣ := Units.mk0 2 htwo
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff u g).mp
    (mem_powers_iff_mem_zpowers.mpr (hg u))
  have hj' : (g : ZMod r) ^ j = 2 := by
    simpa [u] using congrArg Units.val hj
  refine ⟨j, hj', ?_⟩
  by_contra hodd
  have heven : Even j := Nat.not_odd_iff_even.mp hodd
  obtain ⟨a, ha⟩ := heven
  have hsquare : IsSquare (2 : ZMod r) := by
    refine ⟨(g : ZMod r) ^ a, ?_⟩
    rw [← hj', ha, pow_add]
  rcases (ZMod.exists_sq_eq_two_iff hr2).mp hsquare with h | h <;> omega

private lemma generator_half_eq_neg_one (r : ℕ) [Fact r.Prime]
    (hr : r % 8 = 5) (g : (ZMod r)ˣ)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    (g : ZMod r) ^ ((r - 1) / 2) = -1 := by
  have hcard : Fintype.card (ZMod r)ˣ = r - 1 := by
    rw [Fintype.card_units, ZMod.card]
  have hord : orderOf g = r - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard]
  have hhalf : (r - 1) / 2 * 2 = r - 1 := by omega
  have hsquare : ((g : ZMod r) ^ ((r - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, hhalf]
    exact congrArg Units.val (hord ▸ pow_orderOf_eq_one g)
  rcases sq_eq_one_iff.mp hsquare with hone | hneg
  · have hu : g ^ ((r - 1) / 2) = 1 := Units.ext hone
    have hne := pow_ne_one_of_lt_orderOf (x := g)
      (show (r - 1) / 2 ≠ 0 by omega)
      (show (r - 1) / 2 < orderOf g by rw [hord]; omega)
    exact (hne hu).elim
  · exact hneg

/-- No primitive-root assumption on two is made: a generator is used only to
construct the character, and nonsquareness of two determines its orientation.
The resulting character is primitive and odd, and is unique with the stated
order and normalization. -/
theorem normalized_quartic_exists_unique (r : ℕ) [Fact r.Prime]
    (hr : r % 8 = 5) :
    ∃ χ : DirichletCharacter ℂ r,
      orderOf χ = 4 ∧ χ 2 = Complex.I ∧ χ.IsPrimitive ∧ χ.Odd ∧
      ∀ ψ : DirichletCharacter ℂ r,
        orderOf ψ = 4 → ψ 2 = Complex.I → ψ = χ := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod r)ˣ)
  have hcard : Fintype.card (ZMod r)ˣ = r - 1 := by
    rw [Fintype.card_units, ZMod.card]
  have hfour : 4 ∣ Fintype.card (ZMod r)ˣ := by rw [hcard]; omega
  let iu : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero
  have hiu : iu ∈ rootsOfUnity (Fintype.card (ZMod r)ˣ) ℂ := by
    apply (mem_rootsOfUnity _ _).mpr
    apply Units.ext
    exact (Complex.isPrimitiveRoot_I.pow_eq_one_iff_dvd _).mpr hfour
  let χ₀ : DirichletCharacter ℂ r := MulChar.ofRootOfUnity hiu hg
  have hgen : χ₀ (g : ZMod r) = Complex.I := by
    simpa [χ₀, iu] using MulChar.ofRootOfUnity_spec hiu hg
  have hpow : χ₀ ^ 4 = 1 := by
    apply (MulChar.eq_iff hg _ _).mpr
    simp only [MulChar.pow_apply_coe, hgen, Complex.I_pow_four,
      MulChar.one_apply_coe]
  have hodd₀ : χ₀.Odd := by
    change χ₀ (-1) = -1
    rw [← generator_half_eq_neg_one r hr g hg, map_pow, hgen,
      pow_eq_pow_mod _ Complex.I_pow_four]
    have hh : (r - 1) / 2 % 4 = 2 := by omega
    rw [hh, Complex.I_sq]
  obtain ⟨j, hj, hjodd⟩ := generator_two_exponent r hr g hg
  have hjmod : j % 4 = 1 ∨ j % 4 = 3 := by
    have hj2 := Nat.odd_iff.mp hjodd
    omega
  have htwo₀ : χ₀ 2 = Complex.I ∨ χ₀ 2 = -Complex.I := by
    rw [← hj, map_pow, hgen, pow_eq_pow_mod _ Complex.I_pow_four]
    rcases hjmod with h | h <;> rw [h] <;> norm_num
  have hexists : ∃ χ : DirichletCharacter ℂ r,
      χ ^ 4 = 1 ∧ χ 2 = Complex.I ∧ χ.Odd := by
    rcases htwo₀ with h | h
    · exact ⟨χ₀, hpow, h, hodd₀⟩
    · refine ⟨χ₀ ^ 3, ?_, ?_, ?_⟩
      · rw [← pow_mul, show 3 * 4 = 4 * 3 by omega, pow_mul, hpow, one_pow]
      · rw [MulChar.pow_apply' χ₀ (by decide : 3 ≠ 0), h]
        norm_num [Complex.ext_iff, pow_succ]
      · change (χ₀ ^ 3) (-1) = -1
        rw [MulChar.pow_apply' χ₀ (by decide : 3 ≠ 0), hodd₀]
        norm_num
  obtain ⟨χ, hχfour, hχtwo, hχodd⟩ := hexists
  have hχorder : orderOf χ = 4 := by
    have hd : orderOf χ ∣ 4 := orderOf_dvd_of_pow_eq_one hχfour
    have horder0 : orderOf χ ≠ 0 := by
      intro ho
      simp [ho] at hd
    have hi : orderOf (χ 2) ∣ orderOf χ := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← MulChar.pow_apply' χ horder0, pow_orderOf_eq_one]
      exact MulChar.one_apply (isUnit_iff_ne_zero.mpr
        (Ring.two_ne_zero ((ZMod.ringChar_zmod_n r).substr (by omega))))
    rw [hχtwo, Complex.isPrimitiveRoot_I.eq_orderOf.symm] at hi
    exact Nat.dvd_antisymm hd hi
  have hχne : χ ≠ 1 := by
    intro heq
    have := congrArg orderOf heq
    simp [hχorder] at this
  have hχprim : χ.IsPrimitive := by
    rcases (Nat.dvd_prime (Fact.out : r.Prime)).mp
      (DirichletCharacter.conductor_dvd_level χ) with h | h
    · exact (hχne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)).elim
    · exact h
  refine ⟨χ, hχorder, hχtwo, hχprim, hχodd, ?_⟩
  intro ψ hψorder hψtwo
  apply (MulChar.eq_iff hg _ _).mpr
  have hψfour : ψ ^ 4 = 1 := hψorder ▸ pow_orderOf_eq_one ψ
  have hχg : χ (g : ZMod r) ^ 4 = 1 := by
    rw [← MulChar.pow_apply_coe, hχfour, MulChar.one_apply_coe]
  have hψg : ψ (g : ZMod r) ^ 4 = 1 := by
    rw [← MulChar.pow_apply_coe, hψfour, MulChar.one_apply_coe]
  have hinv (z : ℂ) (hz : z ^ 4 = 1) : (z ^ j) ^ j = z := by
    have hjj : j * j % 4 = 1 := by
      rcases hjmod with h | h <;> norm_num [Nat.mul_mod, h]
    rw [← pow_mul, pow_eq_pow_mod _ hz, hjj, pow_one]
  have heq : ψ (g : ZMod r) ^ j = χ (g : ZMod r) ^ j := by
    rw [← map_pow, ← map_pow, hj, hψtwo, hχtwo]
  exact (hinv _ hψg).symm.trans ((congrArg (fun z : ℂ => z ^ j) heq).trans
    (hinv _ hχg))

/-- The normalized character; uniqueness makes the auxiliary generator choice
irrelevant. -/
def character (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) : DirichletCharacter ℂ r :=
  (normalized_quartic_exists_unique r hr).choose

/-- The actual kernel in the unit group, with no surrogate scalar object. -/
def kernel (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) : Subgroup (ZMod r)ˣ :=
  (character r hr).toUnitHom.ker

/-- The normalized character and its literal unit kernel have index four and
order `(r-1)/4`; minus one is omitted. This includes the conductor five at the
finite character layer; later class-number constants exclude that conductor. -/
theorem kernel_structure (r : ℕ) [Fact r.Prime] (hr : r % 8 = 5) :
    let χ := character r hr
    let K := kernel r hr
    orderOf χ = 4 ∧ χ 2 = Complex.I ∧ χ.IsPrimitive ∧ χ.Odd ∧
    (∀ ψ : DirichletCharacter ℂ r, orderOf ψ = 4 → ψ 2 = Complex.I → ψ = χ) ∧
    Nat.card K = (r - 1) / 4 ∧ K.index = 4 ∧ (-1 : (ZMod r)ˣ) ∉ K := by
  classical
  obtain ⟨horder, htwo, hprim, hodd, hunique⟩ :=
    (normalized_quartic_exists_unique r hr).choose_spec
  change orderOf (character r hr) = 4 at horder
  change character r hr 2 = Complex.I at htwo
  have hfour : character r hr ^ 4 = 1 := horder ▸ pow_orderOf_eq_one _
  have hrange : (character r hr).toUnitHom.range = rootsOfUnity 4 ℂ := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      apply (mem_rootsOfUnity _ _).mpr
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, Units.val_one]
      rw [← MulChar.pow_apply_coe, hfour, MulChar.one_apply_coe]
    · intro hz
      have hzfour : (z : ℂ) ^ 4 = 1 := by
        simpa using congrArg Units.val ((mem_rootsOfUnity 4 z).mp hz)
      obtain ⟨j, _, hj⟩ := Complex.isPrimitiveRoot_I.eq_pow_of_pow_eq_one hzfour
      have htwo0 : (2 : ZMod r) ≠ 0 :=
        Ring.two_ne_zero ((ZMod.ringChar_zmod_n r).substr (by omega))
      refine ⟨Units.mk0 (2 : ZMod r) htwo0 ^ j, ?_⟩
      apply Units.ext
      simpa only [MulChar.coe_toUnitHom, Units.val_pow_eq_pow_val,
        Units.val_mk0, map_pow, htwo] using hj
  have hindex : (kernel r hr).index = 4 := by
    rw [kernel, Subgroup.index_ker, hrange, Complex.card_rootsOfUnity]
  have hcard : Nat.card (kernel r hr) = (r - 1) / 4 := by
    have hc := (kernel r hr).card_mul_index
    have hu : Nat.card (ZMod r)ˣ = r - 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ZMod.card]
    rw [hindex, hu] at hc
    omega
  refine ⟨horder, htwo, hprim, hodd, hunique, hcard, hindex, ?_⟩
  intro hneg
  have hn : character r hr (-1) = 1 := by
    simpa only [kernel, MonoidHom.mem_ker, Units.ext_iff,
      MulChar.coe_toUnitHom, Units.val_neg, Units.val_one] using hneg
  change character r hr (-1) = -1 at hodd
  rw [hodd] at hn
  norm_num at hn

end D5.S3.ArithUnits.MercaQuarticCharacter
