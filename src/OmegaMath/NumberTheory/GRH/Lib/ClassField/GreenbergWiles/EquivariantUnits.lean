import OmegaMath.NumberTheory.GRH.Lib.ClassField.GreenbergWiles.SelmerBasic
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic number theory (textbook or folklore).

Part of: Greenberg–Wiles formula, as a lower bound for the dual side (known result; see
Lib.ClassField.GreenbergWiles.GreenbergWilesBound).

Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes (known
result; see Lib.ClassField.Places.LocalFrobenius).

This file: Herbrand's equivariant S-unit theorem: units plus Z span permutation module of places. -/

open Quot NumberField Pointwise MulAction InfinitePlace Units Matrix NeZero Function Module
  LinearMap Set Ideal


variable (G) {K : Type} [Group G] [TopologicalSpace G] [Field K] [NumberField K] (N : ℕ) [NeZero N]

/-- Non-vanishing of the S-regulator: on pairs (u, n), u an S-unit and n an integer, functions
M_v (v in S) vanishing exactly when u is a unit at v, and log|u|_w + n (w infinite), are
ℝ-linearly independent. -/
lemma linearIndependent_sUnit_log {S : Set (FinPlace K)} [Fintype S] {M : S ⊕ InfinitePlace K →
  S.unit K × ℤ → ℝ} (ho : ∀ v u, M (.inl v) u = 0 ↔ v.1.valuation K u.1.1 = 1) (hi : ∀ w u,
  M (.inr w) u = (w u.1.1).log + u.2) : LinearIndependent ℝ M := by
  choose _ _ y s using exists_valuation_eq_exp_mul S.toFinite
  exact .of_comp (funLeft ℝ ℝ (Sum.rec (y <| Pi.single · 1, 0) fun i ↦ if e : i = _ then 1 else
    (⟨.mk0 (fundSystem K ((equivFinRank K).symm ⟨i, e⟩)) (by simp), by simp [unit,
    notMem_of_isUnit]⟩, 0))) (linearIndependent_cols_of_det_ne_zero (Eq.trans_ne (congr(det $(by
    ext ⟨⟩ ⟨⟩ <;> try rfl
    aesop (add simp [fromBlocks, notMem_of_isUnit]))).trans (det_fromBlocks_zero₂₁' ..))
      (mul_ne_zero
    (det_ne_zero_of_sum_col_lt_diag (by simp_all [Finset.sum_eq_zero])) (right_ne_zero_of_mul (mt
    (congr(det $(by aesop)).trans (det_mul_row ..)).trans (abs_pos.1 ((finrank_mul_regulator_eq_det
    K _ (equivFinRank K).symm).subst (by simp [regulator_pos, finrank_pos]))))))))

variable [Algebra K Ω] [MulSemiringAction G Ω] [IsProGalois G K Ω]

/-- Given places A_v of Ω above each prime v of K, there are infinite places of Ω above those of
K which, with the A_v for v dividing N, meet every G-orbit of places above N and infinity in
exactly one index. -/
lemma PlaceAboveS.bijective_orbits {A : _ → _} (hA : ∀ v, IsPlaceOver (A v) v) :
  Bijective (Quotient.mk (orbitRel G (PlaceAboveS N)) ∘ .map (fun v : {v : FinPlace K | ↑N ∈ v.1} ↦
  ⟨_, (hA _).valuation_natCast_lt_one_iff.2 v.2⟩) (surjInv (comap_surjective (k := K)))) := ⟨by
  rintro ⟨⟩ ⟨j⟩ e <;> cases' Quotient.exact e with g <;> injections
  grind [((hA j).smul g).unique]
  grind [surjInv_eq, mem_orbit_iff.1 ⟨MulSemiringAction.toAlgEquiv K _ g, ‹_›⟩], ind (Sum.rec (fun B
    ↦ (exists_isPlaceOver_of_val_ne_one K out B.2.ne).rec fun v h ↦
  ⟨.inl ⟨v, h.valuation_natCast_lt_one_iff.1 B.2⟩, sound ((h.exists_smul
  G (hA _)).imp fun _ ↦ congrArg _ ∘ Subtype.ext)⟩) fun u ↦ ⟨.inr _, sound (((toAlgAut_surjective
  G).exists.1 (mem_orbit_iff.2 (surjInv_eq comap_surjective _).symm)).imp fun _ ↦ congrArg _)⟩)⟩

include K

/-- Equivariant Dirichlet theorem: with X the places above N∞ of the field of Q, its N-units E
are finitely generated, rank(E × ℤ) ≤ #X, and there are ℝ-linearly independent additive maps
Λ_z : E × ℤ → ℝ (z ∈ X) with Λ_z(g⁻¹y) = Λ_{gz}(y). -/
lemma dirichlet_fixedSUnits (Q :
  OpenNormalSubgroup G) : let X := orbitRel.Quotient Q.1.1 (PlaceAboveS N)
  Module.Finite ℤ (fixedSUnits N Q) ∧ ∃ Λ : X → _ →ₗ[ℤ] ℝ, (∀ g z y,
    Λ z ((fixedSUnitsRep N Q).prod (.trivial _ _ ℤ)
    g⁻¹ y) = Λ (g • z) y) ∧ LinearIndependent ℝ Λ ∧ finrank ℤ (fixedSUnits N Q × ℤ) ≤ .card X := by
  have := (@finite_natCast_mem (fixedFieldOf Q.1.1) _ _ N _).fintype
  let ⟨_, rk⟩ := SUnit.dirichlet_unit_theorem this.finite
  let e := Equiv.ofBijective _ (PlaceAboveS.bijective_orbits Q.1.1 N FinPlace.isPlaceOver_placeOver)
  let ε : Additive (unit ..) →+ fixedSUnits N Q :=
    .mk' (⟨_, ofBase_mem_sUnits.2 ·.2, Subtype.prop _⟩) (by tauto)
  have hε : Surjective ε.toIntLinearMap := fun ⟨y, h, k⟩ ↦ by
    obtain ⟨x, ⟨⟩⟩ := (DiscreteUnits.ofBase_bijective _).2 ⟨y, k⟩; exists ⟨x,
      ofBase_mem_sUnits (G := Q.1.1).1 h⟩
  let lg y n : PlaceAboveS N → ℝ := Sum.rec (ordRat K ·.1 y) fun w ↦ (w y.toMul.1).log + n
  have hl (g : G) y n : ∀ z, lg (unitsRep g⁻¹ y) n z = lg y n (g • z) := by rintro ⟨B⟩; simp [lg,
    ← (exists_isPlaceOver_of_val_ne_one K out B.2.ne).choose_spec.ordRat_smul g]; repeat rfl
  use .of_surjective _ hε, fun x ↦ AddMonoidHom.toIntLinearMap (.mk' (fun (y, n) ↦ x.lift (lg y n)
    (by rintro _ _ ⟨g, rfl⟩; erw [← hl, y.2.2 g⁻¹])) (by obtain ⟨⟨⟩⟩ := x <;> simp [Real.log_mul,
    lg, add_add_add_comm])), Quotient.ind₂ (by tauto), (linearIndependent_equiv e).1 (.of_comp (pi
    (applyₗ' ℝ <| ·.map ε id)) (linearIndependent_sUnit_log (fun v _ ↦ Rat.cast_eq_zero.trans
    (v.1.isPlaceOver_placeOver.isPlaceOver_below.ordRat_eq_zero_iff.trans
    v.1.isPlaceOver_placeOver.valuationVia_eq_one_iff)) fun w _ ↦ congr(($(
    surjInv_eq comap_surjective w) _).log + _))), Nat.card_congr e ▸ finrank_le_of_rank_le ?_
  grw [rank_eq_of_surjective fst_surjective, ker_fst, rank_range_le, rank_le_of_surjective _ hε]
  simp [← rk]
