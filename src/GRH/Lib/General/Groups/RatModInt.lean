import GRH.Lib.ClassField.Places.LocalDefs
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of group theory (textbook or folklore).

This file: Basic facts on Q/Z; character group of a finite abelian group. -/

open Nat AddCircle AddMonoidHom Function NeZero QuotientAddGroup ZMod

variable {n : ℕ} {G H A B W} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Monoid H]
  [TopologicalSpace H] [ContinuousMul H] [AddCommGroup A] [AddCommGroup B] [AddCommGroup W]

lemma Continuous.of_isOpen_ker (f : G →* H) (h : f.ker.IsOpen) : Continuous f :=
    continuous_of_tendsto_nhds_one f (tendsto_nhds_of_eventually_eq (h.mem_nhds f.map_one))

lemma QZ.isAddTorsion : IsAddTorsion QZ :=
  Quot.ind (isOfFinAddOrder_iff_exists_rat_eq_div.2 ⟨·, by simp⟩)

lemma QZ.addOrderOf_mk_inv : 0 < n → addOrderOf (mk n⁻¹) = n :=
  one_div (n : ℚ) ▸ addOrderOf_period_div

/-- The group homomorphism from Q/Z, written multiplicatively, to C^× sending the class of x to
e^{2πix}. -/
noncomputable def QZ.expUnit : Multiplicative QZ →* ℂˣ := Circle.toUnits.comp
  (toCircle_addChar.compAddMonoidHom (map _ (.zmultiples 1) (Rat.castHom ℝ) (by simp))).toMonoidHom

lemma QZ.expUnit_eq_one_iff {a} : expUnit a = 1 ↔ a = 1 := a.ind' fun _ ↦ by
  erw [Units.ext_iff, Complex.exp_eq_one_iff, coe_eq_zero_iff]; simp [field, @eq_comm ℂ]; norm_cast

variable [DivisibleBy W ℤ] {a : A} [NeZero n]

lemma QZ.exists_extend f (u : A →+ W) (h : ker f ≤ u.ker) : ∃ v :
    B →+ W, ∀ a, v (f a) = u a := ((Module.Baer.of_divisible W).extension_property_addMonoidHom _
    (kerLift_injective f) (QuotientAddGroup.lift _ u h)).imp fun _ e _ ↦ DFunLike.congr_fun e ⟦_⟧

lemma QZ.eq_zero_of_forall_hom_eq_zero : (∀ u : A →+ QZ, u a = 0) → a = 0 :=
  CharacterModule.eq_zero_of_character_apply

/-- For n nonzero, the additive homomorphism Z/n → Q/Z sending the class of k to the class of
k/n. -/
noncomputable def QZ.ofZMod (n : ℕ) [NeZero n] := ZMod.lift n
    ⟨zmultiplesHom _ (mk _), CharacterModule.int.divByNat_self n⟩

lemma QZ.ofZMod_apply b : ofZMod n b = mk (b.val / n) := congr(mk $(by aesop))

@[simp] lemma QZ.ofZMod_injective : Injective (ofZMod n) := by simp [ofZMod, lift_injective, pos,
  ← addOrderOf_dvd_iff_zsmul_eq_zero, addOrderOf_mk_inv, dvd_def]

lemma QZ.exists_ofZMod {a} : n • a = 0 → ∃ b, ofZMod n b = a := .imp' (↑) (by
  simp_all [ofZMod_apply, mod_eq_of_lt]; tauto) ∘ (AddCircle.nsmul_eq_zero_iff (pos n)).1

lemma QZ.bijective_ofZMod_comp (h : ∀ a : A, n • a = 0) : Bijective ((ofZMod n).comp (M := A)) :=
    ⟨fun _ _ ↦ (cancel_left (by simp)).1, fun f ↦ (Classical.skolem.1 (exists_ofZMod <| by
  simp [← map_nsmul, h ·])).rec (⟨.mk' · fun _ _ ↦ ofZMod_injective (by simp [*]), ext ·⟩)⟩

variable (A) [Finite A]

/-- A finite abelian group A has exactly #A homomorphisms to ℚ/ℤ: its Pontryagin dual has the
same order as A. -/
@[simp] lemma card_hom_QZ : Nat.card (A →+ QZ) = .card A := (card_congr <| .trans (.symm
  (.ofBijective _ (QZ.bijective_ofZMod_comp AddMonoid.exponent_nsmul_eq_zero))) <|
  toMultiplicative.trans
  toUnits.monoidHomCongrRightEquiv).trans (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (hM :=
  ⟨⟨_, .iff_orderOf.2 (addOrderOf_one _)⟩, (toUnits.symm.subgroupMap _).isCyclic.2 inferInstance⟩))

instance : Finite (A →+ QZ) := finite_of_card_ne_zero (by simp [ne])
