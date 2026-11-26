import OmegaMath.NumberTheory.GRH.Lib.Weil.GaussSum.ShearInvariance
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Exchange theorem for theta integrals of complementary rank (see
New.Exchange.ExchangeTheorem).

Part of: Exchange of theta kernels with explicit determinant polynomials (see New.Rows.Carrier).

This file: Sections over cosets; matched pairs are GL-stable and determined by one side. Block
determinant functions on the open cell are partners, by Jacobi's complementary minors. -/

noncomputable section

open Matrix schwartzBruhat SemilocalField Classical Finsupp MatMul MulChar Function
variable {F : Type} [SemilocalField F] {a b n : Type} [Fintype a] [Fintype b] [Fintype n] (χ :
  MulChar F ℂ) (e : b ⊕ a ≃ n) (y : Matrix n b F)

/-- There are matrices r_q, q ∈ GL_b(F)/GL_b(O), and a linear functional ℓ equal to f ↦ ∑_q
f(r_q) when that sum is finite, such that each left invertible y has y·r_q primitive for
exactly one q, and y·r_q⁻¹ primitive for exactly one q. -/
lemma exists_common_coset_reps : ∃ (ℓ : (_ → ℂ) →ₗ[ℂ] ℂ) (r : GL b F ⧸ intGL b O → GL b F), (∀ t f,
  (∀ q, f (r q) ≠ 0 → q ∈ t) → ℓ f = ∑ q ∈ t, f (r q)) ∧ ∀ y : Matrix n b F, HasLeftInv y → (∃! q,
  IsPrimitiveMatrix O (y * (r q).1)) ∧ ∃! q, IsPrimitiveMatrix O (y * (r q).1⁻¹) := match skolem.1
  (exists_invTransposeGL_inv_eq valPair ·.out),
  lcoeFun.dualMap_surjective_of_injective DFunLike.coe_injective (lsum ℂ 1)
  with | ⟨k, _⟩, ⟨ℓ, L⟩ => ⟨ℓ ∘ₗ .funLeft .., (·.out) * k, fun t f h ↦ congr($L (onFinset t _
  h)).trans (by simp), fun y h ↦ (valPair.exists_isPrimitiveMatrix_mul h).elim fun u p ↦ by
  have := (p.2.mul_iff.trans <| isPrimitiveMatrix_iff_mem_intGL <| u⁻¹ * ·)
  simp_all [← coe_units_inv, -Pi.mul_apply]
  simp_all [↓← invTransposeGL_mem_intGL (_ * _⁻¹), ← QuotientGroup.eq, mul_assoc]⟩

/-- The functional Ψ ↦ ℓ(g ↦ χ(det g)Ψ(yg)), with ℓ chosen from `exists_common_coset_reps`: the sum
of χ(det r_q)Ψ(y·r_q) over the representatives r_q whenever finitely many terms are non-zero. -/
def localSection :=
  (@exists_common_coset_reps F _ b n).choose ∘ₗ .mulLeft ℂ (χ ·.1.det) ∘ₗ .funLeft ℂ ℂ (y * ·.1)

/-- Pairs of Schwartz–Bruhat functions Φ on surjective, Ψ on injective matrices whose
χ(det)-averages over GL_a(F), GL_b(F) satisfy Φˇ(x_k) = χ(det k)Ψˇ(y_k) for all k in
GL_n(F), x_k the rows of k⁻¹ indexed by a, y_k the columns of k indexed by b. -/
def matchingPairs := .prod (schwartzBruhat (HasLeftInv ·ᵀ)) (schwartzBruhat HasLeftInv) ⊓
  (LinearMap.pi fun k ↦ (localSection χ (invLastRows e k)ᵀ ∘ₗ .funLeft ℂ ℂ transpose).coprod
  (-(χ k.1.det • localSection χ (firstCols e k)))).ker

omit [Fintype a] [Fintype b] in
lemma mul_firstCols (g k : GL n F) : g.1 * firstCols e k = firstCols e (g * k) := rfl

lemma matchingPairs.translate_mem {p} (h : p ∈ matchingPairs χ e) (g : GL n F) :
  (χ g.1.det • (p.1 <| · * g.1), (p.2 <| g⁻¹.1 * ·)) ∈ matchingPairs χ e := ⟨⟨(schwartzBruhat
  _).smul_mem _ (schwartzBruhat.comp h.1.1 (· * g.2) fun _ ↦ .imp' (· * g.1ᵀ) (by simp
  [← transpose_mul])), schwartzBruhat.comp h.1.2 (g.1 * ·) fun _ ↦ .imp' (· * g.2) (by simp)⟩, by
  simpa [↓funext_iff, mul_add, localSection, Pi.mul_def, ← mul_firstCols, ← mul_assoc, ← map_mul,
    ← det_mul] using! congr(χ g.det • $(h.2) ∘ (g⁻¹ * ·))⟩

/-- For left invertible y there is g in GL_b(F) with yg primitive such that `localSection` χ y Ψ =
χ(det g)Ψ(yg) for every Ψ supported on primitive matrices. -/
lemma localSection_of_primitive (hy : HasLeftInv y) : ∃ g : GL b F, IsPrimitiveMatrix O (y * g.1) ∧
  ∀ Ψ, (∀ x, Ψ x ≠ 0 → IsPrimitiveMatrix O x) → localSection χ y Ψ = χ g.1.det * Ψ (y * g.1) :=
  exists_common_coset_reps.choose_spec.elim fun _ ⟨S,
  R⟩ ↦ (R y hy).1.imp' _ fun p ↦ .imp_right (by intros; erw [S {p}] <;> aesop)

lemma TameLocalChar.isClopen_primitive (_ : TameLocalChar χ) (e : b ⊕ a ≃ n) :
  IsClopen {y : Matrix n a F | IsPrimitiveMatrix O y} := ⟨by simpa [Set.image, eq_comm,
  valPair.exists_firstCols_iff] using ((isCompact_intGL isCompact_O).image_auto (firstCols (.trans
  (.sumComm ..) e))).isClosed, isOpen_iff_forall_mem_open.2 fun _ ⟨_, _, h, _⟩ ↦
  ⟨_ ⁻¹' {0}ᶜ, isPrimitiveMatrix_of_stdColDatum_ne_zero h,
  (stdColDatum_mem_schwartzBruhat χ h).1 _, by simp [stdColDatum, invOnUnits, *]⟩⟩

/-- Let χ be tame and Λ linear with χ(det g)Λ(Φ(g·)) = Λ(Φ) for all g in GL_a(F) and
Schwartz–Bruhat Φ supported on surjective matrices. Then some linear T has T(Ψ) = Λ(Φ) for
all pairs (Φ,Ψ) in `matchingPairs`. -/
lemma matchingPairs.exists_linear_factor {X} (hχ : TameLocalChar χ) (Λ : _ →ₗ[ℂ] X → ℂ) (hΛ :
  ∀ g : GL a F, ∀ Φ ∈ schwartzBruhat (HasLeftInv ·ᵀ), χ g.1.det • Λ (Φ <| g.1 * ·) = Λ Φ) : ∃ T :
  _ →ₗ[ℂ] _, ∀ p ∈ matchingPairs χ e, T p.2 = Λ p.1 := by
  choose! k _ K using
    (exists_invLastRows_iff_transpose e (x := ·).2 ∘ ((@valPair F _).exists_firstCols_iff _).2)
  use Λ ∘ₗ .pi fun x ↦
    ite (IsPrimitiveMatrix O xᵀ) (χ (k x).det) 0 • localSection χ (firstCols e (k x))
  rintro _ ⟨⟨m⟩, h⟩
  choose r S R using (@exists_common_coset_reps F _ a n).choose_spec
  have o q : _ ∈ schwartzBruhat _ :=
    ⟨(LocallyConstant.indicator ⟨_, m.1⟩ ((hχ.isClopen_primitive _ e).preimage
    (f := (·ᵀ * (r q).2)) (by fun_prop))).2, m.2.imp (·.mono (by simp)) (.trans (by simp))⟩
  choose! _ p _ U using (R _ ∘ @m.2.2 ·)
  let ⟨t, ht⟩ := ((m.1 {0}).isClosed_compl.closure_eq.subst m.2.1).elim_finite_subcover _
    (o · |>.1 {0}ᶜ) fun _ ↦ by simp; tauto
  convert congr(∑ q ∈ t, $(hΛ (transposeGL (r q)) _ (o q))) <;> simp only [← map_smul, ← map_sum,
    Λ.comp_apply] <;> congr with x <;> simp [-ite_smul, Set.indicator, Set.subset_def] at ht U ⊢
  split
  apply (sub_eq_zero.1 congr($h _) ▸ S t ..).trans <;> simp [← K _ ‹_›]
  repeat grind [t.sum_eq_single (p x), fun q _ ↦ (U ((r q).1ᵀ * x) · q (by simpa))]

/-- For any function f, the functions Φ(x₁ x₂) = χ⁻¹(det x₂)f(x₂⁻¹x₁) and Ψ(y₁; y₂) = χ⁻¹(det
y₁)f(−y₂y₁⁻¹), with blocks cut by e and x₂, y₁ square, are partners for χ over R
(`IsPartner`). -/
lemma partner_block {n a b R} [Fintype n] [Fintype a] [Fintype b] [CommRing R] (e : b ⊕ a ≃
    n) (χ : MulChar R ℂ) (f : _ → ℂ) : IsPartner ⊤ e χ (fun x ↦ let x := x.submatrix id e
  χ⁻¹ x.toCols₂.det * f (x.toCols₂⁻¹ * x.toCols₁)) fun y ↦ let y := y.submatrix e id
  χ⁻¹ y.toRows₁.det * f (-(y.toRows₂ * y.toRows₁⁻¹)) := by
  use fun x h ↦ let x := x.submatrix id e; ⟨reindexGL e (.mk'' (fromBlocks 1 0 x.toCols₁ x.toCols₂)
    ?_)⁻¹, ?_⟩, fun y h ↦ let y := y.submatrix e id; ⟨reindexGL e (.mk'' (y.toRows₁.fromBlocks 0
    y.toRows₂ 1) ?_), ?_⟩, (reindex_equiv (reindexGL e)).1.2 fun k ↦ ?_
  any_goals simp_all +zetaDelta [apply_eq_zero_iff, mem_intGL, ← ext_iff, reindex_equiv e,
    ← comp_assoc]
  rcases (det_fromRows_invLastRows (.refl _) k (fromCols 1 0)).symm,
    invLastRows_mul_firstCols (.refl _) k
  rw [← (invLastRows _ k).fromCols_toCols, ← (firstCols _ k).fromRows_toRows] at *
  simp_all [-fromCols_toCols, -fromRows_toRows, inv_apply_eq_inv', apply_eq_zero_iff, mul_assoc,
    or_iff_not_imp_right, invLastRows, firstCols, add_eq_zero_iff_eq_neg']
  exact (nonsing_inv_mul_cancel_left _ (toRows₂ _) · ▸ by simp [*])
