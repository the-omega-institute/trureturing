import OmegaMath.NumberTheory.GRH.Lib.Weil.MixedModel.Names
import OmegaMath.NumberTheory.GRH.Lib.Weil.Construction.FinitePart
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Coordinate changes keeping the vacuum intertwine Heisenberg and Weil operators (negation,
conjugation). Schrödinger data are compatible with direct sums and changes of space. Weil action in
the Schrödinger model at split finite places; products over disjoint places. -/

open Heisenberg stdLattice Matrix IsVacuum NumberField Finset Submodule Space

section

variable {E} [Field E] [CMType E] [WeilData E] {n : Type*}
  [Fintype n] {s} {n₁ : Type*} [Fintype n₁]

variable (E) in
/-- A change of adelic coordinates φ = A × B keeping β up to σ, where the real part A keeps the
Gaussian and the finite part B keeps Ô^n and turns x*x into −x*x. -/
structure Std (σ : ℂ →+* ℂ) s₁ s where
  φ : (n → 𝔸 E) ≃ₜ+ (n₁ → 𝔸 E)
  realEquiv : (_ → ℂ) ≃ₜ+ (_ → ℂ)
  finEquiv : (n → 𝔸f E) ≃ₜ+ (_ → 𝔸f E)
  apply_adelicSum y : φ ((adelicSum E s).equiv y) =
    (adelicSum E s₁).equiv (realEquiv y.1, finEquiv y.2)
  beta_realEquiv x y : σ ((realHeis (realSigns E s₁)).β (realEquiv x) (realEquiv y)) =
    (realHeis (realSigns E s)).β x y
  vac_realEquiv x : realVac (realEquiv x) = realVac x
  psi₀_finEquiv x y : σ (psi₀ E (half * star (finEquiv y) ⬝ᵥ finEquiv x)) =
    psi₀ E (half * star y ⬝ᵥ x)
  dot_finEquiv x : star (finEquiv x) ⬝ᵥ finEquiv x = -star x ⬝ᵥ x
  finEquiv_mem x : finEquiv x ∈ stdLattice .. ↔ x ∈ stdLattice ..

variable {s₁ σ} [RingHomIsometric σ] (D : Std E σ s₁ s) {V : Space E n s} {V₁ : Space E n₁ s₁}

section

omit [RingHomIsometric σ]

/-- A change of adelic coordinates φ as in `Std` keeps the bicharacter up to σ: σ(β₁(φx,
φy)) = β(x,y) for all x, y. -/
lemma Std.beta_phi : ∀ x y, σ ((adelicHeis E s₁).β (D.φ x) (D.φ y)) = (adelicHeis E s).β x y := by
  simp [reindex_equiv (adelicSum E s).equiv, OrthogonalSum.beta_equiv, finHeis, apply_adelicSum,
    beta_realEquiv, psi₀_finEquiv]

/-- A change of adelic coordinates φ as in `Std` keeps the vacuum function e = `vacuumFn`:
e(φx) = e(x) for all x. -/
lemma Std.vacuumFn_apply : ∀ x, vacuumFn (D.φ x) = vacuumFn x := by
  simpa [reindex_equiv (adelicSum E s).equiv, OrthogonalSum.vac_equiv, apply_adelicSum,
    vac_realEquiv] using fun _ x ↦ isVacuum_finVac.4 x ▸ by aesop (add simp [stdLattice.finVac,
    dot_finEquiv, finEquiv_mem, Complex.inv_eq_conj, AddChar.map_neg_eq_inv])

lemma Std.apply_finVec x : D.φ (finVec x) =
  finVec (D.finEquiv x) := by convert D.apply_adelicSum (0, x) <;> aesop (add simp adelicSum)

end

/-- For a change of coordinates φ with twist σ, the continuous σ-semilinear map from 𝒮(V₁) to
𝒮(V) sending the coefficient function c to σ∘c∘φ. -/
noncomputable def Std.map : 𝒮 V₁ →SL[σ] 𝒮 V := transport D.beta_phi D.vacuumFn_apply

/-- For a vacuum-preserving change of coordinates D with underlying map φ, the induced map from
𝒮(V₁) to 𝒮(V) intertwines the Heisenberg operators: it sends ϱ(φx)f to ϱ(x) applied to the
image of f, for all x and f. -/
lemma Std.map_ϱ x f : D.map (V₁.ϱ (D.φ x) f) = V.ϱ x (D.map f) := IsVacuum.ext fun _ ↦ by
  repeat erw [heisOp_apply, transport_apply]
  simp [beta_phi]

/-- The transport c ↦ c^φ from 𝒮(V₁) to 𝒮(V) attached to a change of coordinates D sends the
vacuum of V₁ to the vacuum of V. -/
@[simp] lemma Std.map_vacElem : D.map V₁.vacElem = V.vacElem :=
  IsVacuum.ext (map_integral_and_map_vacuum D.beta_phi D.vacuumFn_apply).2

/-- Let φ be a vacuum-preserving change of coordinates with twist σ. If φ(gx) = g₁φ(x) for all x
and σ(Δ(g₁)) = c·Δ(g), then (ω(g₁)f)^φ = c·ω(g)(f^φ) for all f in 𝒮(V₁). -/
lemma Std.ω_map {g g₁} (h : ∀ x, D.φ (g.mat *ᵥ x) = g₁.mat *ᵥ D.φ x) {c} (hc : σ (weilMultiplier
  g₁) = c * weilMultiplier g) f : D.map (V₁.ω g₁ f) = c • V.ω g (D.map f) := IsVacuum.ext fun _ ↦ by
  erw [transport_apply]; show _ =
    c * _; repeat erw [Space.ω, weilRep, IsVacuum.smul_apply, integrated_apply_eq_integral]
  simp [hc, ← h, ← map_sub, beta_phi,
    map_integral_and_map_vacuum D.beta_phi D.vacuumFn_apply]; ring!

/-- For a change of coordinates with archimedean part A and twist σ, the continuous σ-semilinear
map of Fock spaces sending v to σ∘v∘A. -/
noncomputable def Std.realMap := transport D.beta_realEquiv D.vac_realEquiv

lemma Std.map_integrated v f : D.map (V₁.integrated v f) = V.integrated (D.realMap v) (D.map f) :=
  IsVacuum.ext fun _ ↦ by
  erw [transport_apply, ← valueAt_apply, Rep.map_integrated_eq_integral,
    (map_integral_and_map_vacuum D.beta_realEquiv D.vac_realEquiv).1, ← valueAt_apply,
    Rep.map_integrated_eq_integral]
  congr! 2; erw [← map_ϱ, apply_adelicSum]; aesop

/-- For a bijection e, units u_i of a topological ring R and a continuous involution τ, the
topological additive isomorphism sending x to (u_i τ(x_{e(i)}))_i. -/
def Std.starCoordEquiv {ι κ R} [Ring R] [TopologicalSpace R] [ContinuousMul R] [StarRing R]
  [ContinuousStar R] (e : κ ≃ ι) (u : κ → Rˣ) : (ι → R) ≃ₜ+ (κ → R) := .mk (by
  use! fun x i ↦ u i * star x (e i), fun x ↦ star (fun i ↦ (u i)⁻¹ * x i) ∘ e.symm <;> cat_disch)

variable {E : _} [Field E] [CMType E] [WeilData E] {n : _} [Fintype n]
  {s n₁ : _} {n₂} [Fintype n₁] [Fintype n₂] {s₁ : _} {s₂} {V : Space E n s} {V₁ : Space E n₁ s₁} {V₂
  : Space E n₂ s₂} {S Ψ Ψ'} {e : n₁ ⊕ n₂ ≃ n} (hs : s ∘ e = s₁ ⊕ᵥ s₂)

attribute [local simp] funext_iff mem_integralBox finVec name_schrodingerAct_boxIndicator
  Finsupp.sum

omit [Fintype n] in
@[simp] lemma finVec_zero : finVec (0 : n → 𝔸f E) = 0 := by simp

/-- Let S ∩ S̄ = S' ∩ S̄' = ∅, and let the finite part B of D carry S'-parts to S-parts and (S'
∪ S̄')-parts to (S ∪ S̄)-parts. For Ψ Schwartz–Bruhat above S, D sends Ψ⊗vac, named at S, to
(σ∘Ψ∘B)⊗vac, named at S'. -/
lemma Std.map_name {σ} [RingHomIsometric σ] (D : Std E σ _ s) {S'} (h : ∀ x, D.finEquiv (idem S' •
  x) = idem S • D.finEquiv x) (h' : ∀ x, D.finEquiv (idem S'.conjClosure • x) = idem S.conjClosure •
  D.finEquiv x) (hS : S.IsConjDisjoint) (hS' : S'.IsConjDisjoint) [hΨ : IsSchwartzBruhat S Ψ] :
  D.map (V₁.name S Ψ V₁.vacElem) = V.name S' (σ <| Ψ <| D.finEquiv ·) V.vacElem := by
  obtain ⟨c, ⟨⟩⟩ := exists_schrodingerComb_eq hS hΨ
  rw [(_ : (fun x ↦ _) = c.sum fun y ↦
    (σ · • schrodingerAct S' (D.finEquiv.symm y) (boxIndicator n S')))]
  simp [*, apply_finVec, ← D.map_vacElem ▸ D.map_ϱ _ V₁.vacElem]
  simp [schrodingerAct, integralBox, ↓← D.psi₀_finEquiv, h, apply_ite, ← D.finEquiv_mem]

/-- Along a splitting of the coordinates, the product of data respects the vacuum projections above
S at the base point: P^S f₁ ⊠ P^S f₂ = P^S (f₁ ⊠ f₂). -/
lemma Space.boxProd_projOn f₁ f₂ : V.boxProd hs (V₁.projOn S f₁) (V₂.projOn S f₂) =
  V.projOn S (V.boxProd hs f₁ f₂) := IsVacuum.ext fun _ ↦ by
  erw [projOn_val, OrthogonalSum.tmul_apply, OrthogonalSum.tmul_apply]
  simpa [projOn_val, reindex_equiv e, ← ite_and] using! if_congr and_comm rfl rfl

/-- For any set S of finite places and any function Ψ on finite adelic vectors, the operator Ψ⊗
named by Ψ at S (`Space.name`) maps the finite part 𝒲_f of 𝒮(V) into itself. -/
lemma Space.name_mem_finitePart S Ψ {f} (h : f ∈ V.finitePart := by simp) :
  V.name S Ψ f ∈ V.finitePart := by
  simp [name, heisenbergComb, sum_smul_mem, rho_finVec_mem_finitePart, projOn_mem_finitePart h]

/-- Names multiply on vacua: for S disjoint from S̄ and Ψ, Ψ′ Schwartz–Bruhat above S, (Ψ⊗vac) ⊠
(Ψ′⊗vac) = Θ⊗vac, where Θ(x) = Ψ(x₁)Ψ′(x₂) for the two blocks x₁, x₂ of coordinates. -/
lemma Space.boxProd_name {Θ} (hS : S.IsConjDisjoint) [hΨ : IsSchwartzBruhat S Ψ] [hΨ' :
  IsSchwartzBruhat S Ψ'] (h : Θ = fun x ↦ Ψ (x ∘ e ∘ .inl) * Ψ' (x ∘ e ∘ .inr)) :
  V.boxProd hs (V₁.name S Ψ V₁.vacElem) (V₂.name S Ψ' V₂.vacElem) = V.name S Θ V.vacElem := by
  obtain ⟨⟨_, ⟨⟩⟩, _, ⟨⟩⟩ := exists_schrodingerComb_eq hS hΨ, exists_schrodingerComb_eq hS hΨ'
  simp [*, ← sum_fn, boxProd_rho, sum_mul, mul_sum, -smul_eq_mul, ← Pi.smul_def]
  congr! 4
  convert ← V.name_schrodingerAct_boxIndicator hS ((‹_› ⊕ᵥ ‹_›) ∘ e.symm) _ |>.symm <;>
  simp [reindex_equiv e, dotProduct, ← e.sum_comp, AddChar.map_add_eq_mul, schrodingerAct,
    mul_add]; grind

end

attribute [local simp ↓] Finsupp.lift_apply Finsupp.sum Function.comp_def LinearMap.funLeft
  Space.name_projOn idem_apply

variable {E : Type*} [Field E] [CMType E] [WeilData E] {n}
  [Fintype n] {s} {S : Set (FinPlace E)} (hS : S.IsConjDisjoint) (V : Space E n s) {Ψ} [hΨ :
  IsSchwartzBruhat (n := n) S Ψ]

/-- Let S, T be disjoint, with S ∪ T disjoint from its conjugate, and let Ψ, Ψ' be
Schwartz–Bruhat on S, T respectively. Then naming ΨΨ' at S ∪ T is naming Ψ' at T followed by
Ψ at S: (ΨΨ')⊗f = Ψ⊗(Ψ'⊗f). -/
lemma Space.name_union {Ψ' T} (h : (S ∪ T).IsConjDisjoint) (d : Disjoint S T) [b :
  IsSchwartzBruhat T Ψ'] f : V.name (S ∪ T) (Ψ * Ψ') f = V.name S Ψ (V.name T Ψ' f) := by
  rw [← (exists_schrodingerComb_eq _ hΨ).choose_spec, ← (exists_schrodingerComb_eq _ b).choose_spec]
  simp [sum_mul, mul_sum]; congr! 4 with y - z -
  rw [(funext _ : _ * _ = schrodingerAct _ (idem S.conjClosure • z)
    (schrodingerAct (S ∪ T) (idem T.conjClosure • y) (boxIndicator _ (S ∪ T)))),
    ← ϱ_name] <;> repeat rw [name_schrodingerAct_boxIndicator]
  rw [projOn_union, projOn_ϱ]
  all_goals simp_all [schrodingerAct, ← ite_and, Set.disjoint_left] <;> congr! 3 <;>
    simp [funext_iff, DFunLike.ext_iff, mem_integralBox, idem_mul_mem_Ô, finVec] <;> grind

include hS

/-- Let S be disjoint from its conjugate, Ψ Schwartz–Bruhat above S, and u = ω(g)(𝟙(g·)⊗f), 𝟙
the indicator of vectors integral at S. Then P^S u = u and ω(g)(Ψ⊗f) = Ψ(g⁻¹·)⊗u, g acting
on functions through its finite part. -/
lemma Space.omega_name g f : let u := V.ω g (V.name S (boxIndicator n S <| g.2 *ᵥ ·) f)
  V.projOn S u = u ∧ V.ω g (V.name S Ψ f) = V.name S (Ψ <| ↑g.2⁻¹ *ᵥ ·) u := by
  let T := (V.ω g ∘L .apply ℂ _ f).1 ∘ₗ V.name S ∘ₗ .funLeft ℂ ℂ g.2.1.1.mulVec
  intro u
  have A y : T (schrodingerAct S y (boxIndicator n S)) = V.ϱ (finVec (idem S.conjClosure • y))
    u := by erw [← (mulVec_surjective_of_invertible g.2 y).choose_spec, ← mulVec_smul,
    ← mulVec_finVec g.mat, ← ω_ϱ, ϱ_name hS]; simp [T, schrodingerAct, LinearMap.pi]
  exact (exists_schrodingerComb_eq hS (.comp_mulVec _)).rec fun _ e ↦
    (iff_self_and.2 fun _ ↦ .trans (by simp [T]) <| congr(T $e).symm.trans <|
    e ▸ by simp [*, name_schrodingerAct_boxIndicator]).1 (V.map_projOn_eq_const 1 fun y h ↦ by
    simpa [A] using! congr(T $(schrodingerAct_boxIndicator hS (integralBox_compl_inter.ge h).2)))

/-- Let S be disjoint from its conjugate and Ψ Schwartz–Bruhat on S. For a finite unitary g
supported on S ∪ S̄, ω(g)(Ψ⊗f) = υ(det g_S)⁻¹ |det g_S|^(−1/2) Ψ(g⁻¹·)⊗f. -/
lemma Space.ω_name_on {g} (hg : g ∈ Gf.supportedOn n S) f : V.ω g (V.name S Ψ f) = starRingEnd ℂ
    (chiAdelic (detOn S g.1)) • V.name S (Ψ <| ↑g⁻¹ *ᵥ ·) f :=
  (V.omega_name hS (Ψ := Ψ) g f).rec fun h _ ↦ by
  obtain _ := finMultiplier_ne_zero g,
    V.eq_zero_of_dataInner_self (by rw [← dataInner_projOn, map_sub _ _ ((_ : ℂ) • _), ←
    name_boxIndicator, dataInner_name hS (Ψ' := (boxIndicator n S <| g *ᵥ ·)),
    localInner_boxIndicator_mulVec, name_boxIndicator] <;> aesop), (V.projOn_ω (inv_mem hg) h).symm
  simp_all [finMultiplier_eq_of_supportedOn hS, rep_apply_apply, chiFin, detOn, mul_comm, mul_smul,
    inv_smul_eq_iff₀]
