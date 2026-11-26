import GRH.Lib.PadicHodge.WachKisin.HodgeFrame
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Potentially crystalline representations, Hodge–Tate weights, Weil–Deligne Frobenius
(known result; see Lib.PadicHodge.Crystalline.RegularityFrobenius).

This file: Base change of a bilinear pairing and its naturality. Admissibility passes to cyclotomic
twists, subgroups, images; basic rules of the period action. Potentially crystalline representations
are Hodge–Tate: frame over C_p and rank-many jumps. -/

open Module Filter Finset LinearMap Matrix Multiplicative Submodule TensorProduct

variable {p : ℕ} [ThePrime p] {T T' T'' A A' : Type} [AddCommGroup T] [Module ℤ_[p] T]
  [AddCommGroup T'] [Module ℤ_[p] T'] [AddCommGroup T''] [Module ℤ_[p] T''] [CommRing A]
  [CommRing A'] [Algebra ℤ_[p] A] [Algebra ℤ_[p] A'] (b : T →ₗ[ℤ_[p]] T' →ₗ[ℤ_[p]] T'')

noncomputable instance Lift.instLinearOrderIdealOb : LinearOrder (Ideal OFlat) := by infer_instance

/-- The base change to A of a ℤ_p-bilinear map b : T × T' → T'': the A-bilinear map (A ⊗ T) × (A
⊗ T') → A ⊗ T'' extending b. -/
noncomputable def Lift.baseChangePairing := (baseChangeHom _ A .. ∘ₗ b).liftBaseChange A

lemma Lift.baseChangePairing_map {ψ : A →ₗ[ℤ_[p]] A'} {f f' f''} (h : ∀ t t', b (f t) (f' t') =
  f'' (b t t')) x y (hψ : ∀ a b, ψ (a * b) = ψ a * ψ b := by simp) : baseChangePairing b
  (TensorProduct.map ψ f x) (TensorProduct.map ψ f' y) = TensorProduct.map ψ f'' (baseChangePairing
  b x y) := by induction x <;> induction y <;> simp_all [baseChangePairing, smul_tmul']

variable {Γ : Type*} {R} {T : Type*} {R'} {T' : Type*} [Group Γ] [CommRing R] [AddCommGroup T]
  [Module R T] [Algebra ℤ_[p] R] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [CommRing R']
  [AddCommGroup T'] [Module R' T'] [Algebra ℤ_[p] R'] [Module ℤ_[p] T'] [IsScalarTower ℤ_[p] R' T']
  [𝒥 : OverGp Γ p] {ρ σ : Representation R Γ T} {ρ' : Representation R' Γ T'} {F F' B} (B') {M}
  [CommRing B] [Algebra ℤ_[p] B] [Monoid M] [MulSemiringAction M B] [SMulCommClass M ℤ_[p] B]
  [CommRing B'] [Algebra ℤ_[p] B'] [MulSemiringAction M B'] [SMulCommClass M ℤ_[p] B']
  [Algebra B B'] [IsScalarTower ℤ_[p] B B'] [SMulDistribClass M B B'] (h : IsAdmissible ρ F)
  {f : T →ₗ[ℤ_[p]] T'} (hf : ∀ᶠ g in F, ∀ x, f (ρ g x) = ρ' g (f x)) (c : ℤ) {Γ'} [Group Γ']
  (φ : Γ' →* Γ) (e : ∀ g x, σ g x = (χ g ^ c).1 • ρ g x) (m n : M) (g k : End R T)

/-- A representation of Γ on a module T over a Z_p-algebra R, regarded as a Z_p-linear
representation. -/
noncomputable abbrev overZp (ρ : Representation R Γ T) := actionRep ℤ_[p] T ρ

instance : IsTorsionFree Bcris (Bcris ⊗[ℤ_[p]] T) :=
    (Free.of_equiv (AlgebraTensorModule.cancelBaseChange _ ℚ_[p] ..)).instIsTorsionFree

variable (B f) in
/-- `b ⊗ x ↦ b ⊗ f x` along a map `B → B'` of period rings -/
noncomputable def periodTensorMap := AlgebraTensorModule.map (Algebra.linearMap B B') f

lemma baseChange_eq_periodTensorMap : f.baseChange B = periodTensorMap B B f := rfl

attribute [-simp] map_smul smul_assoc

attribute [local simp] mul_smul smul_tmul' tensorAction periodTensorMap

lemma tensorAction_smul (b : B) x : tensorAction B m g (b • x) =
  (m • b) • tensorAction _ m g x := by induction x <;> simp_all

variable {B' g} in
lemma tensorAction_periodTensorMap {g' : End R' _} (hf : ∀ x, f (g x) = g' (f x)) (m : M) x :
    tensorAction _ m g' (periodTensorMap B B' f x) =
  periodTensorMap B _ f (tensorAction B m g x) := by induction x <;> simp_all

lemma tensorAction_tensorAction x : tensorAction B m g (tensorAction _ n k x) =
  tensorAction _ (m * n) (g * k) x := by induction x <;> simp_all

/-- If every 1⊗x, x in T, lies in the B-span of the elements of B⊗T fixed by F-almost all g,
then these fixed elements span B⊗T over B. -/
lemma isAdmissible_of_one_tmul_mem_span (h : ∀ x, 1 ⊗ₜ x ∈ span Bcris (fixedPeriods ρ Bcris F)) :
    IsAdmissible ρ F :=
  top_unique (by simpa [← baseChange_top, baseChange_eq_span, span_le, Set.subset_def])

include hf in
lemma fixedPeriods.map [MulSemiringAction (Gp p) B] [SMulCommClass (Gp p) ℤ_[p] B] [Algebra B Bcris]
    [IsScalarTower ℤ_[p] B Bcris] [SMulDistribClass (Gp p) B Bcris] {x} : x ∈ fixedPeriods ρ B F →
  periodTensorMap B Bcris f
  x ∈ fixedPeriods ρ' Bcris F := (·.mp (hf.mono (by grind [tensorAction_periodTensorMap])))

include e in
lemma exists_tate_twist_unit : ∃ t P : Bcrisˣ, P.1 = p ∧ ∀ (n : ℕ) g y, tensorAction Bcris (ofAdd n,
  toGp g) (σ g) (t.1 • y) = (t * P ^ (n * -c)).1 • tensorAction _ (ofAdd n, toGp g) (ρ g) y :=
  exists_tPeriod.rec fun τ ⟨A, B, _⟩ ↦ BPlus.isUnit_p.map (algebraMap ..) |> fun P ↦
  ((A.map (algebraMap ..)).isUnit (by simpa [-isUnit_map_iff] using!
  (isUnit_smul_of_dvd_mu 1 dvd_rfl).mul P)).rec fun t _ ↦ ⟨t ^ (-c), P.unit, by simp, fun n g
  y ↦ by rw [_root_.zpow_mul, ← mul_zpow, eq_mul_inv_of_mul_eq (Units.ext _ : t * _ * (χ g).map
  (algebraMap ..).1 = t.map (MulDistribMulAction.toMonoidHom _ (ofAdd n, toGp g)))] <;> induction y
  <;> simp_all [mul_zpow, ← map_zpow, Algebra.smul_def, FrobGal.smul_def n _ τ ▸
  Function.Commute.iterate_eq_of_map_eq (map_nsmul _ p) n (by simp [B, ← smul_frobEnd])] <;> ring!⟩

include h e in
/-- Tate twists: if B⊗T is spanned over B by the elements fixed under ρ by F-almost all g, the
same holds for the twist σ = χ^c ρ, for any integer c. -/
lemma IsAdmissible.tate_twist : IsAdmissible σ F :=
  (exists_tate_twist_unit c e).elim fun _ ⟨_, _, H⟩ ↦ eq_top_mono (span_le.2 fun _
  a ↦ (smul_mem_iff'' _).1 (subset_span (a.mono fun _ _ ↦ (H ..).trans (by simpa)))) h

/-- If B⊗T is spanned over B by the elements fixed by F-almost all g, the same holds for every
finer filter F' ≤ F on Γ. -/
lemma IsAdmissible.mono (h : IsAdmissible ρ F) (h' : F' ≤ F) : IsAdmissible ρ F' :=
  eq_top_mono (by gcongr; tauto) h

lemma IsAdmissible.baseChange_mem_span_fixedPeriods (h : IsAdmissible ρ F) {f :
  T →ₗ[ℤ_[p]] T'} (hf : ∀ᶠ g in F, ∀ x, f (ρ g x) = ρ' g (f x)) x : periodTensorMap Bcris _ f x ∈
  span Bcris (fixedPeriods ρ' Bcris F) := mapsTo_span (fun _ ↦ .map hf) (h.ge ⟨⟩)

lemma IsCrystalline.isPotCrys : IsCrystalline ρ → IsPotCrys ρ := (·.mono le_top)

lemma isAdmissible_of_cyclotomicGp_zpow : (∀ g x, ρ g x = (χ g ^ c).1 • x) → IsAdmissible ρ F :=
  (isAdmissible_of_one_tmul_mem_span (ρ := 1) (by simp [fixedPeriods, mem_span_of_mem])).tate_twist
  _

/-- For a homomorphism φ: Γ' → Γ and a filter F on Γ', the invariants along F for (j∘φ, ρ∘φ)
span B⊗T if and only if the invariants along the image filter φ(F) for (j, ρ) do. -/
lemma isAdmissible_comp_iff h {F} : IsAdmissible (𝒥 := ⟨toGp.comp φ, h⟩) (ρ.comp φ) F ↔
  IsAdmissible ρ (F.map φ) := .rfl

lemma map_nearOne (hi : Function.Injective 𝒥.toGp) h : nearOne _ (𝒥 := ⟨toGp.comp φ, h⟩).map φ =
  nearOne Γ := (comap_map hi).symm.trans (map_comap_of_mem (h.1.mem_nhds (one_mem _)) ▸ rfl)

/-- If ρ is potentially crystalline for j: Γ → G_p and φ: Γ' → Γ is a homomorphism such that j∘φ
has open image in G_p, then ρ∘φ is potentially crystalline for j∘φ. -/
lemma IsPotCrys.comp {h} : IsPotCrys ρ → IsPotCrys (𝒥 := ⟨toGp.comp φ, h⟩) (ρ.comp φ) := .mono
    (h' := tendsto_comap_iff.2 map_comap_le)

variable {p : ℕ} [ThePrime p] {Γ R T : Type*} [Group Γ] [CommRing R] [AddCommGroup T] [Module R T]
  [Algebra ℤ_[p] R] [Algebra.IsAlgebraic ℤ_[p] R] [OverGp Γ p] {ρ : Representation R Γ T} {ι}
  [Fintype ι] (e : Basis ι R T)

/-- If N·g(P)·diag(χ(g)^{k_i}) = P for matrices N, P over C_p with P invertible and g in G_p,
then the (i,l) entry of P⁻¹N is χ(g)^{−k_i} times g applied to the (i,l) entry of P⁻¹. -/
lemma inv_mul_apply_of_isHodgeTateFrame {N k g} {P : GL ι _} (h : IsHodgeTateFrame N P.1 k g) i l :
  (P⁻¹.1 * N) i l = (cyclotomicGp g ^ (-k i)).1 • g • P⁻¹ i l := by simpa [↓mulVec_mulVec,
  one_apply, mulVec_apply_eq_sum] using congr((P.2 *ᵥ $(h (P.2 *ᵥ col 1 l))) i).symm

/-- For j of open image, R algebraic over Z_p, T with finite basis e: if Q is invertible over
C_p and Q·γ(ρ(g)) = diag(χ(g)^(−k_i))·gQ near 1, the k_i are the jumps at γ and the rows of
Q give a basis of γ-semilinear forms, the i-th in `hodgeTateMaps` for k_i. -/
lemma hasJumps_of_rows {γ} (Q : GL ι _) k (h : ∀ᶠ g in nearOne Γ, ∀ i l,
    (Q.1 * ((ρ g).toMatrix e e).map γ) i l = (χ g ^ (-k i)).1 • toGp g • Q i l) : HasJumps ρ γ
  (univ.1.map k) ∧ ∃ b : Basis ι ℂ_[p] _, (∀ i, b i ∈ hodgeTateMaps ρ γ (k i)) ∧ ∀ i l, b i (e l) =
  Q i l := have he i l : Basis.ofEquivFun (evalOnBasis e ≪≫ₗ toLinearEquivRight'OfInv Q.3 Q.4) i _ =
    _ := congr($((evalOnBasis e).4 _) l).trans (by simp)
  (fun H ↦ ⟨hasJumps_of_basis (F := .of_basis e) H, _, H, he⟩) fun i ↦
    mem_hodgeTateMaps_of_span e.span_eq
  fun l ↦ h.mono fun g ↦ toLin_toMatrix e e (ρ g) ▸ by simp_all [↓toLin_self, mul_apply, mul_comm]

variable [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T]

omit [Algebra.IsAlgebraic ℤ_[p] R] in
lemma IsPotCrys.top_le_span_fixed (h : IsPotCrys ρ) (δ : R →ₐ[ℤ_[p]] PadicAlgCl p) : ⊤ ≤ span BdR
  {v | ∀ᶠ g in nearOne Γ, (((ρ g).toMatrix e e).map δ).map (algebraMap _ BdR) *ᵥ toGp g • v = v} :=
    ((eq_top_iff_forall_basis_mem (Pi.basisFun ..)).2
    (((liftBaseChange Bcris (((IsScalarTower.toAlgHom _ _ BdR).comp δ).toLinearMap.compLeft ι ∘ₗ
    e.equivFun.1)).map_span_le _ (restrictScalars ..)).2 (fun y h ↦ subset_span (by
    apply EventuallyEq.trans _ (h.out.mono fun _ ↦ congrArg _)
    exact y.inductionOn (fun _ x ↦
      .mono (.all (eventually_nearOne_apply_eq Γ <| δ <| e.1 x ·)) (by
      simp [funext_iff, tensorAction, ← toMatrix_mulVec_repr e, mulVec_eq_sum, Algebra.smul_def,
        mul_sum]
      grind)) fun _ _ ↦ by simpa using .add)) ⟨1 ⊗ₜ e ·, h.ge ⟨⟩, by aesop⟩)).ge

/-- For j of open image, R algebraic over Z_p, T potentially crystalline with finite basis: some
invertible P over C_p has γ(ρ(g))·gP·diag(χ(g)^k_i) = P near 1, the k_i are the jumps at γ,
and the rows of P⁻¹ give a basis of γ-semilinear forms, the i-th in `hodgeTateMaps` for k_i. -/
lemma IsPotCrys.exists_isHodgeTateFrame (h : IsPotCrys ρ) (γ : R →ₐ[_] _) : ∃ P : GL ι _, ∃ k,
  (∀ᶠ g in nearOne Γ, IsHodgeTateFrame (((ρ g).toMatrix e e).map γ) P.1 k (toGp g)) ∧
  HasJumps ρ γ (univ.1.map k) ∧ ∃ b : Basis ι ℂ_[p] _, (∀ i, b i ∈ hodgeTateMaps ρ γ (k i)) ∧ ∀ i l,
  b i (e l) = P⁻¹ i l := (exists_GL_col_mem_of_span _ (h.top_le_span_fixed ..)).rec
  fun U u ↦ (exists_hodge_frame Γ le_rfl U.isUnit (.mono (.all u) fun _ ↦ ext_col)).elim fun _ ⟨_,
  k, P, _, _, E, _⟩ ↦ (fun H ↦ ⟨.map thetaBdR P.unit, k, H, hasJumps_of_rows e _ _ (H.mono fun _ ↦
  inv_mul_apply_of_isHodgeTateFrame)⟩) (funext (exists_algHom_lift γ).choose_spec ▸ E.mono fun _ ↦
  isHodgeTateFrame_of_hodgeMatrix)

/-- Let j have open image, R be algebraic over Z_p, and T be finite free over R and potentially
crystalline. Then at each γ: R → C_p the jumps of T, with multiplicity, form a multiset of
cardinality the rank of T.

Known result: Potentially crystalline representations, Hodge–Tate weights, Weil–Deligne
Frobenius. -/
lemma IsPotCrys.exists_hasJumps (h : IsPotCrys ρ) [Free R T] [Module.Finite R T] γ : ∃ J, J.card =
  finrank R T ∧ HasJumps ρ γ J := let :=
    γ.domain_nontrivial; (h.exists_isHodgeTateFrame (finBasis ..) γ).rec (by bound)
