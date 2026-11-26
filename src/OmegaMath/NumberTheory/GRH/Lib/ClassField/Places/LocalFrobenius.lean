import OmegaMath.NumberTheory.GRH.Lib.General.Groups.ArtinDefs
import OmegaMath.NumberTheory.GRH.Lib.ClassField.Places.Places
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Hilbert ramification theory for infinite Galois extensions; ideles and ideal
classes. Here places are valuation rings of an algebraic closure acted on by an abstract profinite
group, and local fields are only henselian with finite residue field. Of tame inertia, only the
prime-to-p quotients and the relation with Frobenius are proved. Source: J. Neukirch, Algebraic
Number Theory, 1999, I §9, II §§7–9, VI §1; J.-P. Serre, Local Fields, 1979, I §7, IV §2; Stacks
Project, tag 09EE.

This file: Uniformisers and the normalised rational valuation on the algebraic closure of a local
field. Frobenius exists and, with inertia, topologically generates a local Galois group. -/

open FiniteField Classical Finset Fint Ideal IsDiscreteValuationRing IsLocalRing MulAction
  MulSemiringAction Subgroup Valuation Ideal.Quotient

variable {Γ k Ω} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω] [Algebra k Ω] [MulSemiringAction
  Γ Ω] {A : ValuationSubring Ω} (L : IsLocalGalois Γ k A) {π : kˣ} (h : IsUniformiser A π.1) {x y :
  valRingBelow k A}

lemma IsUniformiser.val_lt_one {π} : IsUniformiser A π → valuationVia k A π < 1 := (· π |>.2 le_rfl)

lemma dvd_iff_valuationVia_le : x ∣ y ↔ valuationVia k A y ≤ valuationVia k A x :=
  (integer.integers _).dvd_iff_le

/-- If A ∩ k is a discrete valuation ring, then π ∈ k is a uniformiser for A if and only if π
lies in A ∩ k and is irreducible there. -/
lemma isUniformiser_iff_irreducible [IsDiscreteValuationRing (valRingBelow k A)] {π} :
    IsUniformiser A π ↔ ∃ h, Irreducible (⟨π, h⟩ : valRingBelow k A) := by
  simp [irreducible_iff_uniformizer, Ideal.ext_iff, ↓mem_maximalIdeal_iff, mem_span_singleton,
    dvd_iff_valuationVia_le, ← comap_apply, IsUniformiser]
  grind

lemma exists_val_eq_pow_index [G : IsProGalois Γ k Ω] (h : ∀ g, g ∈ decompGroup Γ A) x : ∃ c,
  valuationVia k A c = A x ^
  (stabilizer Γ x).index := have : Finite (orbit Γ x) := (isLocallyConstant_smul x).range_finite
  (G.1.3.1 _ fun g ↦ smul_prod'.trans (Equiv.prod_comp (toPerm g) ((↑) : orbit Γ x → Ω))).imp
    (by simp_all [index_stabilizer, prod_eq_pow_card, mem_orbit_iff, decompGroup.val_smul,
    valuationVia])

include L h in
lemma IsUniformiser.card_quot a (e : valuationVia k A x = valuationVia k A π ^ a) :
  .card (_ ⧸ span {x}) = residueCard k A ^ a := have := L.5; ((span _).ext
    (by simp_all [(isUniformiser_iff_irreducible.1 h).2.maximalIdeal_eq, dvd_iff_valuationVia_le,
    span_singleton_pow, mem_span_singleton, valuationVia])).substr (cardQuot_pow_of_prime this.3)

lemma IsUniformiser.exists_val_eq_zpow (L : IsLocalGalois Γ k A) (h : IsUniformiser A π.1) x (hx :
  x ≠ 0) : ∃ a : ℤ, valuationVia k A x = valuationVia k A π ^ a := have := L.5
  (exists_units_eq_smul_zpow_of_irreducible (isUniformiser_iff_irreducible.1 h).2 hx).imp fun _ ⟨u,
    e⟩ ↦ by erw [e, valuationVia, ← comap_apply, map_mul, (integer.integers _).valuation_unit]; simp

/-- Let k be a henselian local field with uniformiser π. For x ∈ Ω^×, n ∈ ℕ and a ∈ ℤ, x^n and
π^a have equal A-valuation if and only if n·ord(x) = a, ord the order normalised on k. -/
lemma IsUniformiser.val_pow_eq_iff_mul_ordRat (L : IsLocalGalois Γ k A) {π : kˣ} (h :
  IsUniformiser A π.1) {x} (n : ℕ) (a : ℤ) :
  A.valuation x.toMul ^ n = valuationVia k A π ^ a ↔ n * ordRat k A x = a := by
  have := (quotient_finite_of_isOpen _ <| L.1.6 ·)
  choose b e using fun x : Ωˣ ↦ (exists_val_eq_pow_index L.4 x).elim fun c e ↦
    e ▸ h.exists_val_eq_zpow L _ (by simpa [·, valuationVia] using e.ge)
  refine (epsilon_spec ⟨.mk' (fun x ↦ b x.toMul / (stabilizer Γ x.toMul.1).index) ?_, fun p q ↦
    (by grind [IsUniformiser] : valuationVia k A π = valuationVia k A p).rec ?_⟩ :
    Set.ofPred _ (ordRat ..)) _ h ..
  all_goals simp [field]; norm_cast; simp [← zpow_right_inj₀ _ h.val_lt_one.ne,
    ← e, pos_iff, zpow_add₀, zpow_mul, mul_comm, pow_right_comm, mul_pow]

lemma IsUniformiser.ordRat_eq_one (h : IsUniformiser A π.1) :
    _root_.ordRat k A (DiscreteUnits.ofBase Γ Ω (.ofMul π)) = 1 :=
  (one_mul _).symm.trans ((h.val_pow_eq_iff_mul_ordRat L ..).1 rfl)

namespace IsLocalGalois

lemma exists_isUniformiser (L : IsLocalGalois Γ k A) : ∃ π : kˣ, IsUniformiser A π.1 := have := L.5
  this.exists_irreducible.rec (⟨.mk0 · (by aesop), isUniformiser_iff_irreducible.2 ⟨_, ·⟩⟩)

lemma ordRat_eq_zero (L : IsLocalGalois Γ k A) {x} : ordRat k A x = 0 ↔ A x.toMul = 1 := by
  simpa using (L.exists_isUniformiser.choose_spec.val_pow_eq_iff_mul_ordRat L 1 0).symm

/-- Let Γ = Gal(Ω/K) be the absolute Galois group of a henselian local field, with valuation ring A
of Ω. An arithmetic Frobenius exists; for any such φ the products φ^n·i (n ≥ 0, i in inertia) are
dense in Γ; A is integral over A ∩ K. -/
lemma frobenius_spec {K} [Field K] [Algebra K Ω] [L : IsLocalGalois Γ K A] : (∃ φ : Γ, IsFrob A
  (residueCard K A) φ) ∧ (∀ {φ}, IsFrob A (residueCard K A) φ → DenseRange fun p : ℕ × inertiaGroup
  Γ A ↦ φ ^ p.1 * p.2.1) ∧ ∀ x : valRingBelow Ω A, IsIntegral (valRingBelow K A) x.1 := by
  let B := valRingBelow Ω A; let R := IsLocalRing.ResidueField B; let : UniformSpace B := ⊥
  let := (⟨by simp [B, mem_decompGroup_iff.1, L.4]⟩ : IsInvariantSubring Γ B.1).toMulSemiringAction
  rcases (⟨(Subtype.ext <| smul_comm · · ·.1)⟩ : SMulCommClass Γ (valRingBelow K A) B),
    continuousSMul_iff_stabilizer_isOpen (X := B).2 (isOpen_mono (by aesop_cat) <| L.1.6 ·)
  have : Algebra.IsInvariant (valRingBelow K A) B Γ :=
    ⟨fun ⟨x, _⟩ e ↦ by obtain ⟨_, ⟨⟩⟩ := L.1.1.3.1 x (congr($(e ·))); tauto⟩
  have := this.isIntegral_of_profinite
  have e {q} {g : Γ} : (∀ y : R, g • y = y ^ q) ↔ IsFrob A q g := by
    simp [IsFrob, B, R, residue_surjective.forall, L.4]
    congr!; exact residue_eq_iff_valuation_sub_lt_one
  use ⟨_, Fintype.card_eq_nat_card ▸ e.1 (congr($((stabilizerHom_surjective_of_profinite (G := Γ) _
    _ (@frobeniusAlgEquivOfAlgebraic _ _ (@.ofFinite _ L.6) R _ _ (algebra_isIntegral_of_liesOver
    ..).isAlgebraic)).choose_spec) ·))⟩, fun {φ} hφ g ↦ (@stabilizerHom_surjective_of_profinite
    (FixedPoints.subring ..) _ _ _ _ (zpowers φ).topologicalClosure _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl⟩
    ⟨by tauto⟩ {toRingAut _ R g with commutes' := ?_}).rec fun s hs ↦ mul_inv_cancel_left ↑s g ▸
    map_mem_closure (f := (· * _)) (by fun_prop) ((closure_range_zpow_eq_pow φ).le s.1.2)
    fun _ ⟨n, k⟩ ↦ ⟨⟨n, _, e.1 (by simpa [mul_smul, inv_smul_eq_iff] using! (congr($hs ·).symm))⟩,
    congr($k * _)⟩, (this.1 · |>.algebraMap)
  rintro ⟨a⟩; obtain ⟨⟨⟩, e⟩ := Polynomial.splits_X_pow_nat_card_sub_X.mem_range_of_isRoot
    (i := algebraMap _ R) (X_pow_card_sub_X_ne_zero _ L.6.one_lt_card)
    (by simpa [e.2 hφ] using congr(residue _ $(a.2 ⟨_, subset_closure ⟨1, rfl⟩⟩)))
  exact e ▸ congr(⟦$(smul_algebraMap g _)⟧)
