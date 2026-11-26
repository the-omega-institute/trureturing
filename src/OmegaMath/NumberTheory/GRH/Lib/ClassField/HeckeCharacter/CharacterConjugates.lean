import OmegaMath.NumberTheory.GRH.Lib.ClassField.GreenbergWiles.ExtendCharacter
import OmegaMath.NumberTheory.GRH.Lib.ClassField.Places.UnramifiedCharacters
import OmegaMath.NumberTheory.GRH.Lib.ClassField.HeckeCharacter.CharacterLevels
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Algebraic Hecke characters (type A₀); extension of the quadratic character of a CM
field (known result; see Lib.ClassField.HeckeCharacter.SplittingCharExists).

This file: Existence, finiteness and algebraicity of tame algebraic characters of the norm-one
torus. p-adic absolute value of an algebraic Hecke character is given by its weights. Conjugates of
algebraic characters: modulus one, permuted weight, conjugated tame part. -/

open NumberField Units QuotientGroup Unitary Subgroup Circle CStarRing Function
section

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {ψ ψ' : ∀ w : FinPlace E, MulChar
  (ResField w) ℂ} (u : unitary (𝔸 E)) (φ : E →+* ℂ) (γ : unitary E) {S : Finset (FinPlace E)}

@[simp↓] lemma isUnit_reduceAt_unitary h w : IsUnit (reduceAt w ⟨u.1.2, h⟩) :=
  (reduceU1 w ⟨u, h, nofun⟩).isUnit

lemma norm_map_unitary : ‖φ γ‖ = 1 := norm_coe_unitary (map ⟨φ.1, by simp⟩ γ)

@[simp] lemma norm_unitary_fst v : ‖u.1.1 v‖ = 1 :=
  norm_of_mem_unitary (mem_iff_star_mul_self.2 congr($(u.2.1).1 v))

/-- Kronecker's theorem in a CM field E: an algebraic integer γ of E with γγ̄ = 1 satisfies γⁿ =
1, n the number of roots of unity in E. -/
lemma pow_torsionOrder_eq_one (h : IsIntegral ℤ γ.1) : γ.1 ^ torsionOrder E = 1 :=
  congr($(@pow_card_eq_one' (torsion E) _ ⟨toUnits ⟨⟨γ, h⟩, γ.2.imp Subtype.ext Subtype.ext⟩,
    (mem_torsion E).2 fun ⟨_, _, rfl⟩ ↦ norm_map_unitary ..⟩).1.1.1)

lemma finprod_tame_eq_prod_reduceU1 (hS : ∀ w ∉ S, ψ w = 1) h : ∏ᶠ w, ψ w (reduceAt w ⟨_, h⟩) =
  ∏ w ∈ S, ψ w (reduceU1 w ⟨u, h,
  nofun⟩) := finprod_eq_prod_of_mulSupport_subset _ (by simp_all [not_imp_comm, MulChar.one_apply])

end

variable {E : Type*} [Field E] [CMType E] {ψ ψ' : ∀ w : FinPlace E, MulChar (ResField w) ℂ}
  (u : unitary (𝔸 E)) (φ : E →+* ℂ) (γ : unitary E) {S : Finset (FinPlace E)} {μ ν : AutChar E}
  {e : NumberField.InfinitePlace E → ℤ} {e' : NumberField.InfinitePlace E → ℤ}

lemma exists_unitary_of_mem_rationalU1 {u} : u ∈ rationalU1 → ∃ y : unitary E, toAdele (y : E) =
  u.1 := fun ⟨_, e⟩ ↦
  ⟨⟨_, mem_iff_star_mul_self.2 (toAdele.injective (by simp_all [← star_toAdele, u.2.1]))⟩, e⟩

namespace AutChar

lemma eq_of_mem_integralU1 {f g : _ → ℂ} (hS : ∀ w ∉ S, ψ w = 1) (k : ∀ u a, f u = g u * ∏ᶠ w,
  ψ w (reduceAt w ⟨u.1.2, a⟩)) u (a : u ∈ integralU1 S) : f u =
  g u := by simp_all [a.1, finprod_tame_eq_prod_reduceU1 _ hS, reduceU1, a.2]

instance HasWeight.one : HasWeight (E := E) 1 0 1 := ⟨by simp, by simp [MulChar.one_apply]⟩

lemma HasWeight.mul : μ.HasWeight e ψ → ν.HasWeight e' ψ' → (μ * ν).HasWeight (e + e') (ψ * ψ') :=
  fun ⟨a, _⟩ ⟨b, _⟩ ↦ ⟨(a.union b).subset (by grind [Pi.mul_def]), by simp_all
  [↓finprod_tame_eq_prod_reduceU1 (S := (a.union b).toFinset), zpow_add₀, ← norm_pos_iff, field]⟩

instance HasWeight.inv [h : μ.HasWeight e ψ] : μ⁻¹.HasWeight (-e) ψ⁻¹ := ⟨by simp [h.1], by
  simp +contextual [apply_eq, MulChar.inv_apply_eq_inv', finprod_inv_distrib, field]⟩

lemma HasWeight.zpow (h : μ.HasWeight e ψ) (n : ℤ) : (μ ^ n).HasWeight (n • e) (ψ ^ n) := by
  induction n <;> simp_all [zpow_add, add_mul, sub_eq_add_neg, one, mul]

/-- Let ψ be trivial off a finite set. A homomorphism χ : U(1)(𝔸) → ℂ, trivial on rational
points and equal to ∏_v u_v^{e(v)} · ∏_w ψ_w(u mod w) on integral u, is a continuous unitary
character of weight e and tame part ψ. -/
lemma exists_hasWeight (χ : _ →* ℂ) (h : rationalU1 ≤ χ.ker) (hS : ∀ w ∉ S, ψ w = 1) (k : ∀ u a, χ u
  = (∏ v, u.1.1 v ^ e v) * ∏ᶠ w, ψ w (reduceAt w ⟨u.1.2, a⟩)) : ∃ μ, HasWeight μ e ψ ∧ ∀ u, μ.1 u =
  χ u := ⟨⟨⟨χ.codRestrict _ fun u ↦ mem_sphere_zero_iff_norm.2 (((lift (rationalU1 ⊔ integralU1 S)
  (normHom.toMonoidHom.comp χ) (by simp_all [LE.le, eq_of_mem_integralU1 hS k])).isOfFinOrder
  (isOfFinOrder_of_finite ↑u)).eq_one (by simp)), .subtype_mk (continuous_of_continuousAt_one _
  (.congr (by fun_prop (disch := simp)) (.symm (.mono ((isOpen_integralU1 S).mem_nhds (by simp))
  (eq_of_mem_integralU1 hS k))))) _⟩, (ext <| @h · ·)⟩,
  ⟨S.finite_toSet.subset (by grind), k⟩, by tauto⟩

/-- Let ψ be trivial off a finite set S. If ∏_v Φ_v(u)^{e(v)} · ∏_{w∈S} ψ_w(u mod w) = 1 for
every integer u of E with uū = 1, then some character of U(1)(𝔸), trivial on rational
points, has weight e and tame part ψ.

Known result: Algebraic Hecke characters (type A₀); extension of the quadratic character of a CM
field. -/
lemma exists_hasWeight_of_prod_eq_one (hS : ∀ w ∉ S, ψ w = 1) (h : ∀ (u : unitary E) a,
  (∏ v, Φ v ↑u ^ e v) * ∏ w ∈ S, ψ w (reduceAt w ⟨u, a⟩) = 1) : ∃ μ, HasWeight μ e ψ :=
  (exists_monoidHom_extend (integralU1 ∅).subtype (.toHomUnits ⟨⟨fun u ↦ (∏ v, u.1.1.1 v ^ e v) *
  ∏ w ∈ S, ψ w (reduceU1 w u), by simp⟩, by simp [mul_zpow, field]⟩) rationalU1 fun ⟨⟨_, _⟩,
  _⟩ a ↦ by obtain ⟨y, rfl⟩ := exists_unitary_of_mem_rationalU1 a; use ext (h ..)).elim fun χ H ↦
  ⟨_, (exists_hasWeight (.comp (coeHom ℂ) χ) (by simp_all [LE.le]) hS
  (finprod_tame_eq_prod_reduceU1 _ hS _ ▸ congr($(H.2 ⟨·, ·, nofun⟩).1))).choose_spec.1⟩

/-- For a finite set S of finite places, the group of pairs (μ, ψ): μ a character of U(1)(𝔸) of
weight 0 with tame part ψ, and ψ trivial outside S. -/
noncomputable def tameChars (S : Finset (FinPlace E)) := ofDiv {μ : _ × _ | HasWeight μ.1 0 μ.2 ∧
  ∀ w ∉ S, μ.2 w = 1} ⟨1, .one, by simp⟩ fun _ a _ b ↦ ⟨a.1.mul b.1.inv, by simp_all⟩

/-- Every complex character of the class group of U(1) of tame level S, pulled back to U(1)(𝔸), is a
character of weight 0 with tame part trivial outside S. -/
lemma exists_mem_tameChars (χ : _ ⧸ rationalU1 ⊔ integralU1 S →* ℂ) : ∃ μ : tameChars S, ∀ u,
  μ.1.1.1 u = χ u := by apply ((reindex_equiv (Pi.monoidHomMulEquiv ..).symm).2.1.1
  (exists_monoidHom_extend (.pi fun w : S ↦ reduceU1 w.1)
  ((χ.toHomUnits.comp _).domRestrict _) ⊥ fun u a ↦ ext (le_comap_mk' _ χ.ker (mem_sup_right
  ⟨u.2.1, (congr($a ⟨·, ·⟩))⟩)))).elim fun φ H ↦ (exists_hasWeight (ψ := updateFinset 1 S
  (.ofUnitHom <| φ ·)) (χ.comp _) (le_sup_left.trans (le_comap_mk' _ χ.ker)) ?h (congr($(H.2 ⟨·, ·,
  nofun⟩).1).symm.trans ?_)).elim fun _ ⟨h, k⟩ ↦ ⟨⟨(_, _), h, ?h⟩, k⟩ <;> simp_all
  [finprod_tame_eq_prod_reduceU1 (S := S), updateFinset, ← S.prod_attach, Pi.monoidHomMulEquiv]

/-- There are finitely many characters of weight `0` and given tame level. -/
instance finite_tameChars : Finite (tameChars S) :=
  .of_injective (fun χ ↦ (toUnits.comp (lift (rationalU1 ⊔ integralU1 S)
  _ (sup_le χ.1.1.2 (ext <| by simp [eq_of_mem_integralU1 χ.2.2 χ.2.1.2 · ·]))), S.restrict χ.1.2))
  fun a b h ↦ by ext u; congrm $h.1 u; by_cases u ∈ S <;> simp_all [funext_iff, a.2.2, b.2.2]

/-- Let μ have weight e and tame part ψ, and let u ∈ U(1)(𝔸) have archimedean component 1. Then
there are n > 0 and γ ∈ E with γγ̄ = 1, uⁿγ integral at all finite places, and μ(u)ⁿ = ∏_v
Φ_v(γ)^{e(v)}. -/
lemma HasWeight.exists_pow_eq_prod (h : μ.HasWeight e ψ) (hu : u.1.1 = 1) : ∃ n > 0, ∃ γ :
  unitary E, (∀ w, Valued.v ((u.1.2 ^ n * ↑γ) w) = 1) ∧ μ.1 u ^ n = ∏ v, Φ v ↑γ ^ e v :=
  (mem_sup.1 (pow_index_mem (_ ⊔ integralU1 h.1.toFinset) u)).elim fun _ ⟨a, _, b, e⟩ ↦
  ⟨_, Nat.card_pos, (exists_unitary_of_mem_rationalU1 (inv_mem a)).imp fun _ ↦
  (by simpa [← ·, hu, μ.2 _ a, mul_comm, eq_inv_mul_of_mul_eq e] using! And.intro (fun w ↦ (mem_Ô.1
  b.1 w).antisymm (by simpa using
  (isUnit_reduceAt_unitary _ b.1 w).ne_zero)) (eq_of_mem_integralU1 (by simp) h.2 _ b))⟩

end AutChar

/-- If μ has weight e and a tame part, then for ι : ℂ → ℂ_p and every norm-one adele u trivial
at infinity, |ι μ(u)| = ∏_τ |u_τ|^{−e(τ)}, u_τ the image of u at the prime induced by ι∘τ. -/
lemma AutChar.HasWeight.norm_padic_eq_prod {E} [Field E] [CMType E] {μ : AutChar E} {e ψ p}
  [Fact p.Prime] (h : μ.HasWeight e ψ) (ι : ℂ →+* ℂ_[p]) u : u.1.1 = 1 → ‖ι (μ.1 u)‖ = ∏ τ,
  ‖adeleExtension (ι.comp (Φ τ)) u.1.2‖ ^ (-e τ) := (let ⟨n, _, _, g, h⟩ := h.exists_pow_eq_prod u ·
  by simpa (disch := positivity) [zpow_left_inj₀, -zpow_neg, zpow_comm _ n, Finset.prod_zpow,
               ← zpow_natCast, fun σ ↦ eq_inv_of_mul_eq_one_right (by
               simpa using (norm_adeleExtension_eq_iff (ι.comp σ) 1).2 ((g _).trans (by simp)))]
    using congr(‖ι $h‖))

variable {E : Type _} [Field E] [CMType E] {μ : AutChar E} {e : NumberField.InfinitePlace E → ℤ}
  {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ}

/-- Let μ have weight e and tame part ψ. If u ∈ U(1)(𝔸) has archimedean component 1, then
|σ(μ(u))| = 1 for every ring homomorphism σ : ℂ → ℂ. -/
lemma AutChar.HasWeight.norm_map_eq_one [h : μ.HasWeight e ψ] u (hu : u.1.1 = 1) {F} [FunLike F ℂ ℂ]
  [RingHomClass F ℂ ℂ] (σ : F) : ‖σ (μ.1 u)‖ = 1 := (h.exists_pow_eq_prod u hu).elim fun _ ⟨n, _, _,
  H⟩ ↦ by simpa [pow_eq_one_iff_of_nonneg, n.ne', by simpa using
  (norm_map_unitary <| .comp σ <| @Φ E _ _ ·)] using congr(‖σ $H‖)

/-- Let μ have weight e and tame part ψ, and let σ ∈ Aut ℂ permute the CM type: σ∘Φ_v =
Φ_{p(v)}. Then some ν has weight e∘p⁻¹, tame part σ∘ψ, and ν(u) = σ(μ(u)) whenever u has
archimedean component 1. -/
lemma AutChar.HasWeight.exists_conj (h : μ.HasWeight e ψ) {σ : ℂ ≃+* ℂ} {p : _ ≃ _} (he : ∀ v x,
  σ (Φ v x) = Φ (p v) x) : ∃ ν, HasWeight ν (e ∘ p.symm) (ψ · |>.ringHomComp σ) ∧ ∀ u, u.1.1 = 1 →
  ν.1 u = σ (μ.1 u) := by refine (exists_hasWeight ⟨⟨fun u ↦ (∏ v, u.1.1 (p v) ^ e v) * σ
  (μ.1 u / ∏ v, u.1.1 v ^ e v), ?_⟩, ?_⟩ (fun u a ↦ (exists_unitary_of_mem_rationalU1 a).elim
  (by simp [μ.2 u a, he, norm_map_unitary _ ·, ← ·, ← norm_pos_iff])) (S := h.1.toFinset) ?_ fun u
  a ↦ congr($(Finset.prod_equiv p ?_ ?_) * $(?_))).imp fun _ ↦ .imp_right ?_ <;> simp +contextual
  [h.2, ← norm_pos_iff, mul_zpow, MulEquivClass.map_finprod, *]; grind
