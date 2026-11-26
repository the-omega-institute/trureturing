import GRH.Lib.General.NumberTheory.QuadField
import GRH.Lib.ClassField.Places.SelmerDefs
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic number theory (textbook or folklore).

This file: Inertia at p fixes roots of unity of order prime to p. l-adic valuation on the algebraic
closure; normalised lengths over integer rings. -/

open ENNReal IsDiscreteValuationRing NeZero Real ZMod

variable {p} [ThePrime p] {f ℓ : ℕ} [ThePrime ℓ] {x y : PadicAlgCl ℓ} {c : NNReal}

lemma apply_eq_self_of_mem_inertiaGroup [NeZero f] {g : Gp p} (h : ¬p ∣ f) (m :
  g ∈ inertiaGroup _ (intQpBar p)) ζ : ζ ^ f = 1 → g ζ = ζ := by grind [apply_eq_pow_of_isFrob m]

instance [NeZero f] : NeZero (p ^ f - 1) := by simp [of_pos, Fact.out, ne]

lemma not_dvd_pow_sub_one [NeZero f] : ¬p ∣ p ^ f - 1 := by simp [← natCast_eq_zero_iff, pos, ne]

attribute [local simp] ofReal_add_le ofReal_le_ofReal ne logb_mul logb_pow ellVal

lemma ellVal_le_add_iff (hy : ‖y‖ ≤ 1) : ellVal x ≤ c + ellVal y ↔ ℓ ^ (-c.toReal) * ‖y‖ ≤ ‖x‖ := by
  simp; split_ifs <;> simp_all [← le_div_iff₀, ← le_logb_iff_rpow_le, logb_nonpos, rpow_pos_of_pos,
    pos, logb_div, ofReal_le_iff_le_toReal, toReal_add, Fact.out]

lemma ellVal_le_iff : ellVal x ≤ c ↔
  ℓ ^ (-c.toReal) ≤ ‖x‖ := by simpa using ellVal_le_add_iff norm_one.le

lemma dvd_iff_ellVal_le {x y : intQpBar ℓ} : x ∣ y ↔ ellVal x.1 ≤ ellVal y.1 :=
  (Valuation.integer.integers
  _).dvd_iff_le.trans (by simpa [-ellVal] using! (ellVal_le_add_iff (c := 0) y.2).symm)

lemma ellVal_le_ellVal (h : ‖y‖ ≤ ‖x‖) : ellVal x ≤ ellVal y := by aesop (add simp Fact.out)

lemma ellVal_mul_le : ellVal (x * y) ≤ ellVal x + ellVal y := by aesop (add simp add_comm)

variable {O : CoeffRing ℓ} (x : ↑O) (k : ℕ)

@[simp] lemma ellVal_pow : ellVal (y ^ k) = k * ellVal y := by simp [← mul_neg]; aesop

lemma ellVal_natCast (h : f ≠ 0) : @ellVal ℓ _ f =
  padicValNat ℓ f := have := PadicAlgCl.norm_extends ℓ f
  by simp_all [Padic.norm_eq_zpow_neg_valuation, Fact.out]

@[simp] lemma ellVal_ell : @ellVal ℓ _ ℓ = 1 := by simp [norm_p_eq_inv, Fact.out]

namespace CoeffRing

lemma isUnit_iff_norm_eq_one :
  IsUnit x ↔ ‖x.1‖ = 1 := by simp [isUnit_iff_dvd_one, dvd_iff_norm_le, le_antisymm_iff]

/-- Normalised length: the additive map sending n to n·v(ϖ), ϖ a uniformiser of O and v(ℓ) = 1,
so that O mod ℓ has length 1. -/
noncomputable def normLength : ℕ∞ →+ ℝ≥0∞ := .ENatMap
    ⟨⟨(· * (-logb ℓ ‖(exists_irreducible O).choose.1‖).toNNReal), by simp⟩, by simp [add_mul]⟩

@[simp] lemma normLength_addVal : O.normLength (addVal O x) = ellVal x.1 := by
  have i := (exists_irreducible O).choose_spec
  obtain rfl | ⟨n, u, rfl⟩ := (eq_or_ne x 0).imp_right (eq_unit_mul_pow_irreducible · i) <;>
    simp_all [← mul_neg, i.ne_zero, (isUnit_iff_norm_eq_one _).1] <;> rfl

@[simp] lemma normLength_natCast_mul g : O.normLength (k * g) =
  k * O.normLength g := by simp [← nsmul_eq_mul]

@[gcongr] lemma normLength_mono : Monotone O.normLength := by simp [Monotone, le_iff_exists_add]

lemma eventually_primitiveRoot [NeZero k] : ∀ᶠ O : CoeffRing ℓ in .atTop, ∃ ζ :
    ↑O, IsPrimitiveRoot ζ k := HasEnoughRootsOfUnity.prim.elim fun _ h ↦ (eventually_mem
    (h.isOfFinOrder out).norm_eq_one.le).mono fun _ ↦ (⟨⟨_, ·⟩, .coe_submonoidClass_iff.1 h⟩)

noncomputable instance : PadicIntegerRing O ℓ where
  finiteQuotient _ := AddSubgroup.quotient_finite_of_isOpen _ (isOpen_iff.2 ‹_›)
