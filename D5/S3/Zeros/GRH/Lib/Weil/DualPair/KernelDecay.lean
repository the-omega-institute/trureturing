/- GID: D5/S3/Zeros/GRH/Lib/Weil/DualPair/KernelDecay
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/DualPair/KernelDecay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.DualPair.KernelDecay. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/DualPair/KernelDecay.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.DescentsVanishDef
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Functoriality, seesaw, growth and rapid decay for theta kernels of unitary dual
pairs. Here both spaces are hermitian and act on the maps between them. Decay is proved for data
supported on maps of full rank at split places, by small shifts along a short isotropic vector
instead of Siegel sets. Source: S. Kudla, Seesaw dual reductive pairs, Progr. Math. 46 (1984);
Harris, Kudla, Sweet, Theta dichotomy for unitary groups, J. Amer. Math. Soc. 9 (1996), section 1
(local splittings and their seesaw compatibility); decay: Kudla, Rallis, A regularized Siegel-Weil
formula: the first term identity, Ann. Math. 140 (1994).

This file: Rapid decay of theta kernels for data supported on full-rank maps at split places. -/


open MeasureTheory Matrix Kronecker WeilData Space Prod G IsDualFamily Heisenberg ENNReal MatMul
variable {E : Type} [Field E] [CMType E] {n n' p q : Type} [Fintype n] [Fintype n'] {s s'}
  (S : Space E n s) (T : Space E n' s') (a b) (g : G E s) (c : Matrix n q E)

/-- For a matrix c over E and an adelic point g, the adelic matrix g⁻¹x⁻¹c, where x carries the
form of S to the standard form. -/
noncomputable def Space.coordMatrix := g⁻¹.mat * (S.x⁻¹.1 * c.map toAdele)

variable {g c R} [CommRing R] [Nontrivial R] {φ : 𝔸f E →+* R} [Fintype p]

/-- Let c ≠ 0 be an n×q matrix over E, X in GL_p(𝔸), M a p×n finite adelic matrix, left
invertible after a ring map φ: 𝔸_f → R ≠ 0. Then X_f* M (g⁻¹x⁻¹c)_f ≠ 0 for g in G, x the
point of S. -/
lemma Space.mul_coordMatrix_ne_zero (hc : c ≠ 0) (X : GL p (𝔸 E)) {M : Matrix p n _} :
  HasLeftInv (M.map φ) →
  (X.1.map snd)ᴴ * (M * (S.coordMatrix g c).map snd) ≠ 0 := fun ⟨_, h⟩ e ↦ let ψ := φ.comp (.snd ..)
  hc (map_injective (ψ.comp _).injective (mul_right_injective_of_inv _ _ ((S.x * g.toUnitary).map
    ψ).3 (mul_right_injective_of_inv _ _ h (mul_right_injective_of_inv _ _ ((star X).map ψ).4 (by
         simpa [coordMatrix, ← RingHom.coe_snd, -coe_units_inv] using! congr(($e).map φ))))))

lemma Space.coordMatrix_mul_ne_zero (hc : c ≠ 0) (X : GL p (𝔸 E)) {M : Matrix n p _} (h :
  HasLeftInv (M.map φ)ᵀ) :
  ((S.coordMatrix g c).map snd)ᴴ * (M * X.1.map snd) ≠ 0 := fun e ↦ S.mul_coordMatrix_ne_zero (φ :=
  φ.comp starRingAut.toRingHom) hc X (M := Mᴴ) (by convert h; aesop) (by simpa using congr($eᴴ))

/-- If ht(g) > 2, the lattice L_g of S contains a nonzero isotropic vector x (x*Jx = 0) whose
real coordinates at g have Euclidean norm at most 2/ht(g). -/
lemma Space.exists_short_isotropic (h : 2 < S.height g) : ∃ x ≠ 0, xᴴ * S.J * x = 0 ∧ ∀ j : Unit,
  x.col j ∈ (S.move g).latticeBall (2 / S.height g) := by
  have := (S.move g).firstMinimum_pos; simp [height, field] at *
  obtain ⟨x, hx, _,
    e⟩ := by simpa [h.le] using le_firstMinimum_iff.2.mt (lt_two_mul_self this).not_ge
  use replicateCol _ x, by simpa, funext₂ fun _ _ ↦ (form_eq_zero_of_norm_mul_lt_one hx hx (by
    simp [← sq, e.trans h]) :), by bound

variable [WeilData E] [Fintype q] {P} (hP' : Set.IsConjDisjoint P) {Ψ} [hΨ :
  IsSchwartzBruhat (E := E) (n := n' × n) P Ψ] {S T}

@[simp] lemma apply_vecAtPoint (f : 𝒮 S) γ : f (S.vecAtPoint γ) =
  f 0 := by simp [← S.apply_vecAtPoint_add f γ 0]

include hP' hΨ

/-- Let P ∩ P̄ = ∅, Ψ Schwartz–Bruhat above P on Hom(S,T), X, Y adelic matrices, ℓ a bounded
functional invariant under ϱ(XzY*ε) for all adelic z, ε the standard form. If X_f* y Y_f ≠ 0
whenever Ψ(y) ≠ 0, then ℓ(Ψ⊗f) = 0. -/
lemma name_eq_zero_of_invariant (X : Matrix _ p (𝔸 E)) (Y : Matrix n q (𝔸 E)) {ℓ : _ →L[ℂ] ℂ} (h :
  ∀ z f, ℓ ((S.hom T).ϱ (X ⊗ₖ (Yᴴ * stdForm E s)ᵀ *ᵥ z) f) = ℓ f) (hK : ∀ y, Ψ y ≠ 0 → (X.map snd)ᴴ
  * (vecToMat y * Y.map snd) ≠ 0) f : ℓ (name _ P Ψ f) = 0 := hΨ.mem_of_cosets ((ℓ ∘L .apply ℂ _
  f).ker.comap _) fun y hy ↦ (hK y hy).imp_symm fun N ↦ ext fun i j ↦ let K x := (X x.1 i *
  star (Y x.2 j)).2; .trans (by
    simp [K, entrywise, Fintype.sum_prod_type, vecToMat, Finset.mul_sum]; ac_rfl)
    (eq_zero_of_forall_mul_integral (a := star K ⬝ᵥ y) fun u ↦
    (stdLattice.forall_psi₀_mul_eq_one_iff _).1 fun v _ ↦ by_contra (N ⟨_, .symm ⟨fun _ _ _ e ↦
    eq_zero_of_mul_eq_self_left · (.trans (by erw [ϱ_name hP', IsSchwartzBruhat.schrodingerAct_star
    hP' (star (u * v) • K), mul_right_comm, funext fun x ↦ mul_eq_mul_right_iff.2
    (or_not.imp (e x) (ite_eq_right ·)), LinearMap.map_smul]; simp; rfl) (congr(ℓ (ϱ _ $(by
    ext <;> simp [finVec, stdForm]; ring) _)).trans (h (Pi.single (i, j) (0, α.1 * idem _ * star
    (_ * u * v))) _))), (isLocallyConstant_psi₀.comp_continuous (by fun_prop)).eventually_eq _⟩⟩))

/-- Decay estimate. For P ∩ P̄ = ∅, Ψ Schwartz–Bruhat above P, f₀ in 𝒲_f, some C gives
|L(v⊗Ψ⊗f₀)|·H^N ≤ C·mom_{N+A}(v)·ρ^{N+2A}, L = ℓ∘ω_{a,b}(g,h), whenever the moment is
finite, ρ ≥ 1, H > 0, ‖L‖ ≤ Y(ρH)^A and, if H > 2, there are matrices d, c with columns in
L_h, L_g, one of them isotropic, |d_i||c_j|H ≤ 2Zρ, ℓ invariant under the rational maps z
c*J_S, and, for d′ = h⁻¹x_T⁻¹d, c′ = g⁻¹x_S⁻¹c, either d′_f* y c′_f ≠ 0 whenever Ψ(y) ≠ 0,
or |Lf| ≤ sup_z |L(f − ϱ(d′zc′*ε)f)| (z adelic, ε the standard form) for all f. -/
lemma exists_norm_name_le {f₀} (hf : f₀ ∈ finitePart _) N A Y Z : ∃ C, ∀ v g h (ℓ : _ →L[ℂ] ℂ) ρ H,
  let L := ℓ ∘L pairWeil S T a b (g, h); weightedNorm (N + A) v ≠ ⊤ → 1 ≤ ρ → 0 < H → (∀ f, ‖L f‖ ≤
    Y * ‖f‖ * (ρ * H) ^ A) → (2 < H → ∃ d c x y, (∀ i : p, d.col i ∈ (T.move h).latticeBall x) ∧
    (∀ j : q, c.col j ∈ (S.move g).latticeBall y) ∧ x * y ≤ Z * ρ * (2 / H) ∧ (dᴴ * T.J * d = 0 ∨
    cᴴ * S.J * c = 0) ∧ (∀ (z : Matrix _ q E) f, ℓ (ϱ _ (matToVec (T.ratMap S (z * cᴴ * S.J))) f) =
    ℓ f) ∧ ((∀ y, Ψ y ≠ 0 → ((T.coordMatrix h d).map snd)ᴴ * (vecToMat y * (S.coordMatrix g c).map
    snd) ≠ 0) ∨ ∀ f B, (∀ z, ‖L (f - ϱ _ (T.coordMatrix h d ⊗ₖ ((S.coordMatrix g c)ᴴ *
  stdForm E s)ᵀ *ᵥ z) f)‖ ≤ B) → ‖L f‖ ≤ B)) → ‖L (integrated _ v (name _ P Ψ f₀))‖ * H ^ N ≤
    C * (weightedNorm (N + A) v).toReal * ρ ^ (N + 2 * A) := by
  obtain ⟨⟨C, hC⟩, ⟨M, hM, hL⟩, R, _, -, _, hb, -, -, hA⟩ :=
    @exists_enorm_le_mul_weightedNorm_of_sub .., exists_natCast_smul_mem_of_isCompact E
    (stdLattice.isCompact_stdLattice.smul (α (E := E))⁻¹.1) ((isLocallyConstant_rho_finVec
    (name_mem_finitePart P Ψ hf)).eventually_eq 0), exists_hasFundDomain_toAdele (E := E)
  use ?_
  intro v g h ℓ ρ t L hv hρ _ hY H; grw [le_abs_self Y, (mul_right_comm ..).le] at hY
  grw (transparency := .default) [← toReal_enorm, toReal_mono (mul_ne_top ofReal_ne_top hv) (hC
    (max 2 _ * ρ / t) (L ∘L (integrated _).flip _) (by positivity) fun l v B o ↦ ?_),
    toReal_ofReal_mul, L.opNorm_comp_le, L.opNorm_le_bound (by positivity) hY]
  simp [field, mul_pow, pow_add, div_pow, two_mul]; rw [mul_comm]; congr!; positivity
  obtain ⟨d, c, _, _, h₀, h₁, h₅, h₂, h₃, h₄⟩ := H (by grw [hρ] at l; field_simp at l; grind)
  set K := T.coordMatrix h d ⊗ₖ _
  have mul x y f : ϱ _ (K *ᵥ x) (ϱ _ (K *ᵥ y) f) = (S.hom T).ϱ (K *ᵥ (x + y)) f := by
    simp [adelicHeis, star_mulVec, dotProduct_mulVec, K, -Matrix.mul_assoc]
    cases h₂ <;> simp only [coordMatrix, gram_mul (mat _), mat_preserves_stdForm,
      gram_at_point_eq_map, *] <;> simp
  have hp f : IsContPeriodic (_root_.ratVectors ..) fun d ↦ L (ϱ _ (K *ᵥ d) f) := ⟨by fun_prop, by
    rintro _ ⟨ξ, ⟨⟩⟩ _; simpa [↓← mul, K, L, ↓kronecker_mulVec_eq_matToVec, pairWeil, ω_ϱ, -Rep.mul,
      coordMatrix, Space.ratMap, ← h.mat.mul_assoc, ← mat_mul, S.map_J,
      g⁻¹.mat_preserves_stdForm] using! h₃ (d * vecToMat ξ) _⟩
  clear_value L
  have e := by simpa using strongIntegral_apply _ (fun _ ↦ L ∘L _) (hp · |>.integrable_out)
  refine h₄.elim (fun h₄ k ↦ ?_) (· _ B)
    (((by simpa : (M : E) ≠ 0).isUnit.map toAdele).smul_bijective.2.forall.2 fun d ↦ ?_)
  simpa [quotMean, integral_sub, (hp _).integrable_out, ← e, integrated_name,
    name_eq_zero_of_invariant hP' _ _
    (fun z f ↦ (e _).trans (by simpa [e, ↓← mul] using! quotMean_translate (hp f) z))
    h₄] using norm_quotMean_le (_root_.ratVectors ..) k
  choose a hc _ using hA ∘' d
  have b i := hb (hc i)
  simp [-mulVec_add, -mulVec_smul, IsContPeriodic, finVec.eq_unfold, Set.mem_smul_set, baseLattice,
    archCoords, move_vecAtPoint,
    forall_and, Nat.cast_smul_eq_nsmul, -nsmul_eq_mul] at hL hp h₀ h₁ b ⊢
  erw [← hp.2 _ _ ⟨_, map_nsmul _ M a⟩, ← smul_add, mulVec_smul, rho_integrated_realCoord, hL,
    Rep.rho_zero_apply]
  refine o _ ((pi_norm_le_iff_of_nonneg (by positivity)).2 ?_)
  all_goals simp_intro .. [↓mulVec_eq_sum, fst_sum, snd_sum, K, stdForm, realCoord]
  grw [norm_sum_le, division_def, ← norm_inv, ← Pi.inv_apply, norm_le_pi_norm _⁻¹]
  simp; grw (transparency := .default) [(norm_le_pi_norm ..).trans (b.1 ..), (norm_mul ..).ge,
    norm_mul_le_of_le ((PiLp.norm_apply_le _ (_, _)).trans (h₀.2 _)) ((PiLp.norm_apply_le _
    (_, _)).trans (h₁.2 _)), h₅]
  exact .trans (b := (M * ∑ _ : p × q, Z * 2 * R) * ‖(scaleIdele E).1.1⁻¹‖ * ρ / t)
    (le_of_eq (by simp; ring)) (by gcongr; exact le_max_right ..)
  intro; apply sum_mem; intros; apply_rules [mul_mem, star_mem_Ô, b.2, h₀.1, h₁.1]

variable (S T φ hΨ)

/-- Let P ∩ P̄ = ∅, Ψ Schwartz–Bruhat above P, supported on matrices right invertible after a
ring map φ: 𝔸_f → R ≠ 0. Each N has B, M, C with |θ_{a,b}(v⊗Ψ⊗vac)(g,h)|·ht(h)^N ≤
C·mom_M(v)·ht(g)^B for all g, h and v with mom_M(v) finite.

Known result: Theta kernels of unitary dual pairs: functoriality, seesaw, growth, rapid decay. -/
lemma pairTheta_decay_of_onto (h : ∀ y, Ψ y ≠ 0 → HasLeftInv ((vecToMat y).map φ)ᵀ) N : ∃ B M C,
  ∀ v g h, weightedNorm M v ≠ ⊤ → ‖pairTheta S T a b (integrated _ v (name _ P Ψ (vacElem _))) (g,
  h)‖ * T.height h ^ N ≤ C * (weightedNorm M v).toReal * S.height g ^
  B := (pairThetaKer ..).moderate_growth.elim fun _ ⟨_, H⟩ ↦ ⟨_, _,
  (exists_norm_name_le a b hP' vacElem_mem_finitePart ..).imp fun _ D v g k ↦ (D v g k (θ _) _
  _ · (one_le_height g) (height_pos k) (H g k) (T.exists_short_isotropic · |>.imp fun x ⟨o, i, e⟩ ↦
  (S.exists_short_basis_matrix.choose_spec g).rec fun Y u ↦ ⟨_, _, _, e, u, (mul_comm ..).le, .inl
  i, by simp [← vecAtPoint_hom], .inl (T.coordMatrix_mul_ne_zero o (_ * (_ * Y.map _)) ∘ h · :)⟩))⟩
