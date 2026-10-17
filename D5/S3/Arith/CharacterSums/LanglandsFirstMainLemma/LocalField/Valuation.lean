/- GID: D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/Valuation
   generality: G
   mirror-B: none(waiver:upstream-proof-complete-port)
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   utility: none
   digest: Upstream valuation support required by the retained local-field closure. -/

/-
Attributed source: https://github.com/fukubillueda-web/epsilon_FML/blob/
b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed/LanglandsFirstMainLemma/LocalField/Valuation.lean
License: Apache-2.0; the verbatim upstream LICENSE and original source hashes are in
Library/Fourier/epsilonfml2026hassedavenport.md.
Modifications: repository import paths; direct Mathlib import omits unused upstream metadata.
The upstream namespace, theorem statements, normalization, and proof structure are
retained. The pinned upstream distribution contains no NOTICE file.
-/

import Mathlib

/-!
# The normalized additive order of a nonarchimedean local field

This file transports Mathlib's canonical multiplicative valuation to the normalized additive
value group `WithTop ℤ`.  The transport is kept private: downstream files use `ord` and never
depend on a particular presentation of `ValuativeRel.ValueGroupWithZero`.

The sign convention is the manuscript's convention.  Thus a uniformizer has order `1`, the
valuation ring consists of elements of nonnegative order, and zero has order `⊤`.
-/

namespace LanglandsFirstMainLemma

open scoped WithZero

section Construction

/-- The canonical multiplicative valuation, normalized in `ℤᵐ⁰` by Mathlib's local-field
value-group equivalence.  This is an implementation detail of `ord`. -/
private noncomputable def normalizedMultiplicativeValuation
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Valuation F ℤᵐ⁰ :=
  (ValuativeRel.valuation F).map
    { toMonoidWithZeroHom :=
        (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toMulEquiv.toMonoidWithZeroHom
      monotone' := fun _ _ h ↦
        (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).map_le_map_iff'.mpr h }

/-- Negative logarithm on the nonzero part of `ℤᵐ⁰`, with zero sent to infinity. -/
private def multiplicativeToAdditiveOrder (a : ℤᵐ⁰) : WithTop ℤ :=
  if a = 0 then ⊤ else ((-WithZero.log a : ℤ) : WithTop ℤ)

private lemma multiplicativeToAdditiveOrder_mul (a b : ℤᵐ⁰) :
    multiplicativeToAdditiveOrder (a * b) =
      multiplicativeToAdditiveOrder a + multiplicativeToAdditiveOrder b := by
  by_cases ha : a = 0
  · simp [ha, multiplicativeToAdditiveOrder]
  by_cases hb : b = 0
  · simp [hb, multiplicativeToAdditiveOrder]
  simp [multiplicativeToAdditiveOrder, ha, hb, WithZero.log_mul, add_comm]

private lemma multiplicativeToAdditiveOrder_le_iff (a b : ℤᵐ⁰) :
    multiplicativeToAdditiveOrder a ≤ multiplicativeToAdditiveOrder b ↔ b ≤ a := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simp [multiplicativeToAdditiveOrder]
    · simp [multiplicativeToAdditiveOrder, hb]
  by_cases hb : b = 0
  · subst b
    simp [multiplicativeToAdditiveOrder, ha]
  simp only [multiplicativeToAdditiveOrder, if_neg ha, if_neg hb, WithTop.coe_le_coe]
  rw [neg_le_neg_iff, WithZero.log_le_log hb ha]

private lemma multiplicativeToAdditiveOrder_eq_coe_iff (a : ℤᵐ⁰) (n : ℤ) :
    multiplicativeToAdditiveOrder a = (n : WithTop ℤ) ↔ a = WithZero.exp (-n) := by
  by_cases ha : a = 0
  · subst a
    simp only [multiplicativeToAdditiveOrder, if_true, WithTop.top_ne_coe, false_iff]
    exact (WithZero.exp_ne_zero (a := -n)).symm
  simp only [multiplicativeToAdditiveOrder, if_neg ha, WithTop.coe_eq_coe]
  constructor
  · intro h
    have hlog : WithZero.log a = -n := by omega
    rw [← WithZero.exp_log ha, hlog]
  · rintro rfl
    simp

private lemma min_multiplicativeToAdditiveOrder_le {a b c : ℤᵐ⁰}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (h : c ≤ max a b) :
    min (multiplicativeToAdditiveOrder a) (multiplicativeToAdditiveOrder b) ≤
      multiplicativeToAdditiveOrder c := by
  simp only [multiplicativeToAdditiveOrder, if_neg ha, if_neg hb, if_neg hc,
    ← WithTop.coe_min, WithTop.coe_le_coe]
  rcases (le_max_iff.mp h) with hca | hcb
  · have hlog : WithZero.log c ≤ WithZero.log a :=
      (WithZero.log_le_log hc ha).2 hca
    omega
  · have hlog : WithZero.log c ≤ WithZero.log b :=
      (WithZero.log_le_log hc hb).2 hcb
    omega

/-- The normalized integer-valued additive order on a nonarchimedean local field.

It is bundled as an `AddValuation`, so it can be used as a function `F → WithTop ℤ` while its
zero, product, and ultrametric laws remain available through Mathlib's valuation API. -/
noncomputable def ord (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : AddValuation F (WithTop ℤ) :=
  AddValuation.of
    (fun x ↦ multiplicativeToAdditiveOrder (normalizedMultiplicativeValuation F x))
    (by simp [multiplicativeToAdditiveOrder, normalizedMultiplicativeValuation])
    (by simp [multiplicativeToAdditiveOrder, normalizedMultiplicativeValuation])
    (fun x y ↦ by
      by_cases hx : x = 0
      · subst x
        simp
      by_cases hy : y = 0
      · subst y
        simp
      by_cases hxy : x + y = 0
      · rw [hxy]
        simp [multiplicativeToAdditiveOrder, normalizedMultiplicativeValuation]
      exact min_multiplicativeToAdditiveOrder_le
        ((normalizedMultiplicativeValuation F).ne_zero_iff.mpr hx)
        ((normalizedMultiplicativeValuation F).ne_zero_iff.mpr hy)
        ((normalizedMultiplicativeValuation F).ne_zero_iff.mpr hxy)
        ((normalizedMultiplicativeValuation F).map_add x y))
    (fun x y ↦ by
      rw [(normalizedMultiplicativeValuation F).map_mul]
      exact multiplicativeToAdditiveOrder_mul _ _)

end Construction

section OrderAPI

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

@[simp]
theorem ord_zero : ord F 0 = ⊤ := (ord F).map_zero

@[simp]
theorem ord_one : ord F 1 = 0 := (ord F).map_one

@[simp]
theorem ord_eq_top_iff {x : F} : ord F x = ⊤ ↔ x = 0 := (ord F).top_iff

@[simp]
theorem ord_ne_top_iff {x : F} : ord F x ≠ ⊤ ↔ x ≠ 0 := (ord F).ne_top_iff

@[simp]
theorem ord_neg (x : F) : ord F (-x) = ord F x := (ord F).map_neg x

@[simp]
theorem ord_mul (x y : F) : ord F (x * y) = ord F x + ord F y :=
  (ord F).map_mul x y

/-- The nonarchimedean triangle inequality in order notation. -/
theorem ord_add (x y : F) : min (ord F x) (ord F y) ≤ ord F (x + y) :=
  (ord F).map_add x y

/-- If the two summands have distinct orders, no cancellation raises the order of their sum. -/
theorem ord_add_eq_min {x y : F} (h : ord F x ≠ ord F y) :
    ord F (x + y) = min (ord F x) (ord F y) :=
  (ord F).map_add_of_distinct_val h

/-- The nonarchimedean triangle inequality for a difference. -/
theorem ord_sub (x y : F) : min (ord F x) (ord F y) ≤ ord F (x - y) :=
  (ord F).map_sub x y

@[simp]
theorem ord_sub_swap (x y : F) : ord F (x - y) = ord F (y - x) :=
  (ord F).map_sub_swap x y

@[simp]
theorem ord_inv (x : F) : ord F x⁻¹ = -ord F x := (ord F).map_inv

@[simp]
theorem ord_div (x y : F) : ord F (x / y) = ord F x - ord F y := (ord F).map_div

@[simp]
theorem ord_pow (x : F) (n : ℕ) : ord F (x ^ n) = n • ord F x :=
  (ord F).map_pow x n

/-- The order formula for integer powers.  Mathlib's extended negation fixes `⊤`, so this also
has the correct value for negative powers of zero. -/
@[simp]
theorem ord_zpow (x : F) (n : ℤ) : ord F (x ^ n) = n • ord F x := by
  cases n with
  | ofNat n => simp
  | negSucc n =>
      rw [zpow_negSucc, AddValuation.map_inv, AddValuation.map_pow]
      exact (negSucc_zsmul (ord F x) n).symm

/-- A common lower bound for the orders of finitely many summands bounds their sum. -/
theorem ord_sum {ι : Type*} {s : Finset ι} {f : ι → F} {g : WithTop ℤ}
    (hf : ∀ i ∈ s, g ≤ ord F (f i)) : g ≤ ord F (∑ i ∈ s, f i) :=
  (ord F).map_le_sum hf

/-- Comparison by `ord` is the reverse of Mathlib's canonical valuative relation. -/
theorem ord_le_ord_iff (x y : F) : ord F x ≤ ord F y ↔ y ≤ᵥ x := by
  change multiplicativeToAdditiveOrder (normalizedMultiplicativeValuation F x) ≤
      multiplicativeToAdditiveOrder (normalizedMultiplicativeValuation F y) ↔ _
  rw [multiplicativeToAdditiveOrder_le_iff]
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
      (ValuativeRel.valuation F y) ≤
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
      (ValuativeRel.valuation F x) ↔ _
  rw [map_le_map_iff]
  exact (Valuation.Compatible.vle_iff_le y x).symm

/-- Strict comparison by `ord` is the reverse strict valuative relation. -/
theorem ord_lt_ord_iff (x y : F) : ord F x < ord F y ↔ y <ᵥ x := by
  rw [lt_iff_not_ge, ord_le_ord_iff]
  rfl

/-- Nonnegative order is membership in the valuation subring. -/
theorem ord_nonneg_iff_mem_integer (x : F) :
    0 ≤ ord F x ↔ x ∈ (ValuativeRel.valuation F).integer := by
  calc
    0 ≤ ord F x ↔ ord F 1 ≤ ord F x := by simp
    _ ↔ x ≤ᵥ (1 : F) := ord_le_ord_iff F 1 x
    _ ↔ ValuativeRel.valuation F x ≤ ValuativeRel.valuation F 1 :=
      Valuation.Compatible.vle_iff_le x 1
    _ ↔ ValuativeRel.valuation F x ≤ 1 := by simp
    _ ↔ x ∈ (ValuativeRel.valuation F).integer :=
      (Valuation.mem_integer_iff (ValuativeRel.valuation F) x).symm

/-- Positive order in the valuation subring is membership in its maximal ideal. -/
theorem ord_pos_iff_mem_maximalIdeal
    (x : (ValuativeRel.valuation F).valuationSubring) :
    0 < ord F (x : F) ↔
      x ∈ IsLocalRing.maximalIdeal ((ValuativeRel.valuation F).valuationSubring) := by
  calc
    0 < ord F (x : F) ↔ ord F 1 < ord F (x : F) := by simp
    _ ↔ (x : F) <ᵥ (1 : F) := ord_lt_ord_iff F 1 x
    _ ↔ ValuativeRel.valuation F (x : F) < ValuativeRel.valuation F 1 := by
      change (¬ (1 : F) ≤ᵥ (x : F)) ↔ _
      rw [Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation F) (1 : F) (x : F), not_le]
    _ ↔ ValuativeRel.valuation F (x : F) < 1 := by simp
    _ ↔ x ∈ IsLocalRing.maximalIdeal ((ValuativeRel.valuation F).valuationSubring) :=
      ((ValuativeRel.valuation F).mem_maximalIdeal_iff).symm

/-- Every finite integer order is attained. -/
theorem exists_ord_eq (n : ℤ) : ∃ x : F, ord F x = (n : WithTop ℤ) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  obtain ⟨γ, hγ⟩ := e.surjective (WithZero.exp (-n))
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective γ
  refine ⟨x, ?_⟩
  change multiplicativeToAdditiveOrder (e (ValuativeRel.valuation F x)) =
    (n : WithTop ℤ)
  rw [hx, multiplicativeToAdditiveOrder_eq_coe_iff]
  exact hγ

end OrderAPI

section Uniformizer

private lemma zpowers_exp_neg_one :
    Subgroup.zpowers (Units.mk0 (WithZero.exp (-1 : ℤ)) (by simp) : ℤᵐ⁰ˣ) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro u
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨-WithZero.log (u : ℤᵐ⁰), ?_⟩
  apply Units.ext
  simp [← WithZero.exp_zsmul]

private lemma canonicalValueGroup_eq_top
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    MonoidWithZeroHom.valueGroup (ValuativeRel.valuation F).toMonoidWithZeroHom = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro u
  apply MonoidWithZeroHom.mem_valueGroup
  exact ⟨(ValuativeRel.valuation_surjective
      (u : ValuativeRel.ValueGroupWithZero F)).choose,
    (ValuativeRel.valuation_surjective
      (u : ValuativeRel.ValueGroupWithZero F)).choose_spec⟩

private lemma valueGroupIso_generator
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
        ((Valuation.IsRankOneDiscrete.generator (ValuativeRel.valuation F) :
          (ValuativeRel.ValueGroupWithZero F)ˣ) : ValuativeRel.ValueGroupWithZero F) =
      WithZero.exp (-1 : ℤ) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  let eu := e.unitsCongr
  have hlt : eu (Valuation.IsRankOneDiscrete.generator (ValuativeRel.valuation F)) < 1 := by
    simpa only [map_one] using eu.strictMono
      (Valuation.IsRankOneDiscrete.generator_lt_one (ValuativeRel.valuation F))
  have hzp : Subgroup.zpowers
      (eu (Valuation.IsRankOneDiscrete.generator (ValuativeRel.valuation F))) = ⊤ := by
    calc
      _ = (Subgroup.zpowers
          (Valuation.IsRankOneDiscrete.generator (ValuativeRel.valuation F))).map
            eu.toMonoidHom := (MonoidHom.map_zpowers _ _).symm
      _ = ⊤ := by
        rw [Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup,
          canonicalValueGroup_eq_top F]
        exact Subgroup.map_top_of_surjective eu.toMonoidHom eu.surjective
  have hgen := LinearOrderedCommGroup.Subgroup.genLTOne_unique
    (H := (⊤ : Subgroup ℤᵐ⁰ˣ)) hlt hzp
  have hexp := LinearOrderedCommGroup.Subgroup.genLTOne_unique
    (H := (⊤ : Subgroup ℤᵐ⁰ˣ))
    (show (Units.mk0 (WithZero.exp (-1 : ℤ)) (by simp) : ℤᵐ⁰ˣ) < 1 by
      change WithZero.exp (-1 : ℤ) < 1
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega)
    zpowers_exp_neg_one
  apply_fun ((↑) : ℤᵐ⁰ˣ → ℤᵐ⁰) at hgen hexp
  exact hgen.trans hexp.symm

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- An element has order `1` exactly when it is a uniformizer for Mathlib's canonical discrete
valuation.  This pins down the normalization of `ord`. -/
theorem ord_eq_one_iff_isUniformizer (π : F) :
    ord F π = (1 : WithTop ℤ) ↔ (ValuativeRel.valuation F).IsUniformizer π := by
  change multiplicativeToAdditiveOrder (normalizedMultiplicativeValuation F π) =
      ((1 : ℤ) : WithTop ℤ) ↔ _
  rw [multiplicativeToAdditiveOrder_eq_coe_iff]
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
      (ValuativeRel.valuation F π) = WithZero.exp (-1 : ℤ) ↔
    ValuativeRel.valuation F π =
      (Valuation.IsRankOneDiscrete.generator (ValuativeRel.valuation F) :
        (ValuativeRel.ValueGroupWithZero F)ˣ)
  constructor
  · intro h
    exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).injective
      (h.trans (valueGroupIso_generator F).symm)
  · intro h
    rw [h, valueGroupIso_generator F]

/-- A uniformizer has normalized order `1`. -/
theorem ord_uniformizer {π : F} (hπ : (ValuativeRel.valuation F).IsUniformizer π) :
    ord F π = (1 : WithTop ℤ) :=
  (ord_eq_one_iff_isUniformizer F π).2 hπ

end Uniformizer

section Congruence

/-- Congruence at integer depth `n`: the difference has order at least `n`.

The depth is an integer, rather than a natural number, so that the same relation also describes
congruence in fractional-ideal lattices. -/
noncomputable def CongruentAtDepth {F : Type*} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℤ) (x y : F) : Prop :=
  (n : WithTop ℤ) ≤ ord F (x - y)

namespace CongruentAtDepth

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {m n r s : ℤ} {a b x y z : F}

theorem iff (n : ℤ) (x y : F) :
    CongruentAtDepth n x y ↔ (n : WithTop ℤ) ≤ ord F (x - y) := Iff.rfl

theorem refl (x : F) : CongruentAtDepth n x x := by
  simp [CongruentAtDepth]

theorem zero_right : CongruentAtDepth n x 0 ↔ (n : WithTop ℤ) ≤ ord F x := by
  simp [CongruentAtDepth]

theorem zero_left : CongruentAtDepth n 0 x ↔ (n : WithTop ℤ) ≤ ord F x := by
  simp [CongruentAtDepth]

theorem symm (h : CongruentAtDepth n x y) : CongruentAtDepth n y x := by
  rw [CongruentAtDepth] at h ⊢
  rw [← ord_sub_swap F x y]
  exact h

theorem trans (hxy : CongruentAtDepth n x y) (hyz : CongruentAtDepth n y z) :
    CongruentAtDepth n x z := by
  rw [CongruentAtDepth] at hxy hyz ⊢
  rw [show x - z = (x - y) + (y - z) by ring]
  exact (ord F).map_le_add hxy hyz

/-- A congruence at a deeper depth implies the same congruence at every shallower depth. -/
theorem mono (hmn : m ≤ n) (h : CongruentAtDepth n x y) : CongruentAtDepth m x y :=
  (WithTop.coe_le_coe.mpr hmn).trans h

theorem add (hab : CongruentAtDepth n a b) (hxy : CongruentAtDepth n x y) :
    CongruentAtDepth n (a + x) (b + y) := by
  rw [CongruentAtDepth] at hab hxy ⊢
  rw [show a + x - (b + y) = (a - b) + (x - y) by ring]
  exact (ord F).map_le_add hab hxy

theorem neg (h : CongruentAtDepth n x y) : CongruentAtDepth n (-x) (-y) := by
  rw [CongruentAtDepth] at h ⊢
  rw [show -x - -y = -(x - y) by ring, ord_neg]
  exact h

theorem sub (hab : CongruentAtDepth n a b) (hxy : CongruentAtDepth n x y) :
    CongruentAtDepth n (a - x) (b - y) := by
  simpa only [sub_eq_add_neg] using hab.add hxy.neg

theorem add_left (a : F) (h : CongruentAtDepth n x y) :
    CongruentAtDepth n (a + x) (a + y) :=
  (refl a).add h

theorem add_right (a : F) (h : CongruentAtDepth n x y) :
    CongruentAtDepth n (x + a) (y + a) :=
  h.add (refl a)

/-- Multiplication by an element of order at least `r` raises congruence depth by `r`. -/
theorem mul_left_shift (a : F) (ha : (r : WithTop ℤ) ≤ ord F a)
    (h : CongruentAtDepth s x y) : CongruentAtDepth (r + s) (a * x) (a * y) := by
  rw [CongruentAtDepth] at h ⊢
  rw [← mul_sub, ord_mul]
  change (r : WithTop ℤ) + (s : WithTop ℤ) ≤ ord F a + ord F (x - y)
  exact add_le_add ha h

/-- Right multiplication has the same shifted-depth estimate. -/
theorem mul_right_shift (a : F) (ha : (r : WithTop ℤ) ≤ ord F a)
    (h : CongruentAtDepth s x y) : CongruentAtDepth (r + s) (x * a) (y * a) := by
  simpa only [mul_comm a] using mul_left_shift a ha h

/-- Multiplication by an integral element preserves a congruence depth. -/
theorem mul_left (ha : 0 ≤ ord F a) (h : CongruentAtDepth n x y) :
    CongruentAtDepth n (a * x) (a * y) := by
  simpa using mul_left_shift (r := 0) (s := n) a ha h

/-- Right multiplication by an integral element preserves a congruence depth. -/
theorem mul_right (ha : 0 ≤ ord F a) (h : CongruentAtDepth n x y) :
    CongruentAtDepth n (x * a) (y * a) := by
  simpa only [mul_comm a] using mul_left ha h

/-- If `a` and `y` have nonnegative order, then the products `a * x` and `b * y` of
depth-`n` congruent pairs are again congruent at depth `n`. -/
theorem mul (ha : 0 ≤ ord F a) (hy : 0 ≤ ord F y)
    (hab : CongruentAtDepth n a b) (hxy : CongruentAtDepth n x y) :
    CongruentAtDepth n (a * x) (b * y) :=
  (hxy.mul_left ha).trans (hab.mul_right hy)

/-- Inversion preserves depth for elements of order zero. -/
theorem inv (hx : ord F x = 0) (hy : ord F y = 0)
    (h : CongruentAtDepth n x y) : CongruentAtDepth n x⁻¹ y⁻¹ := by
  have hx0 : x ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  have hy0 : y ≠ 0 := by
    intro hzero
    simp [hzero] at hy
  rw [CongruentAtDepth] at h ⊢
  rw [inv_sub_inv hx0 hy0, ord_div, ord_sub_swap, ord_mul, hx, hy]
  simpa using h

/-- For each fixed depth, `CongruentAtDepth` is an equivalence relation. -/
theorem equivalence (n : ℤ) : Equivalence (@CongruentAtDepth F _ _ _ _ n) :=
  ⟨fun x ↦ refl x, fun {_ _} h ↦ symm h, fun {_ _ _} hxy hyz ↦ trans hxy hyz⟩

/-- The setoid determined by congruence at a fixed depth. -/
noncomputable def setoid (n : ℤ) : Setoid F where
  r := CongruentAtDepth n
  iseqv := equivalence n

end CongruentAtDepth

end Congruence

end LanglandsFirstMainLemma
