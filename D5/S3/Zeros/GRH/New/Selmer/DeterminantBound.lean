/- GID: D5/S3/Zeros/GRH/New/Selmer/DeterminantBound
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/DeterminantBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.DeterminantBound. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/DeterminantBound.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.BlocksAndCocycles
import D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin.HodgeFrame
import D5.S3.Zeros.GRH.New.Data.Weights
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Denominator of projection to lifts, without the even part (see
New.Selmer.DenominatorBound).

Part of: Crystalline losses above ℓ are affordable (see New.Selmer.RibetElement).

Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes (known
result; see Lib.ClassField.Places.LocalFrobenius).

This file: Bloch–Kato finite condition at places above ℓ as relations on global cocycles. Conditions
on Hodge-Tate jumps of a row; explicit crystalline loss per prime. Dictionary between complex
embeddings, places above l and cosets of local Galois groups. Operators clearing denominators at
each eigenvector combine to bound the Gram determinant. -/

noncomputable section

open Module Finset IsAlgClosed Matrix MvPolynomial Real Submodule Algebra.IsAlgebraic

instance localChart (ℓ : ℕ) [ThePrime ℓ] (E) [Field E] [UnramCMField E] (v : placesDividing E ℓ)
             : PadicPlaceEmbedding E (placeOver v.1) ℓ := have loc := (exists_inducesPlace E _
                    (exists_comap_intQpBar_eq
    (v.1.isPlaceOver_placeOver.valuation_natCast_lt_one_iff.2 v.2)).choose_spec).choose_spec
  {isOpen_range := ⟨loc.2.1.2⟩, inducesPlace := loc, ..}

variable {ℓ : ℕ} [ThePrime ℓ] {n} [Fintype n] {E} [Field E] [UnramCMField E] (v :
  placesDividing E ℓ) {O : CoeffRing ℓ}
  (u : Gal(Ω/E) →* Matrix n n O) (O' : CoeffRing ℓ) (g : Gp ℓ) {E'} [Field E'] {P} (D : Data P)

/-- For g in Gal(ℚ̄_ℓ over ℚ_ℓ), the embedding of the coefficient ring O in ℂ_ℓ sending x to
g(x). -/
def coeffEmb :=
  ((IsScalarTower.toAlgHom _ _ ℂ_[ℓ]).comp (g.toAlgHom.restrictScalars _)).comp O'.1.val

/-- The O-module Z_f at v: crystalline cocycles (`crysCocycles`) of the decomposition group of the
chosen place above v, with values in O^n acted on through u. -/
def ZfAt := crysCocycles (actionRep O (n → ↑O) (u.comp (decompGroup _ (placeOver v.1)).subtype))

/-- The linear relations holding on the crystalline cocycles Z_f of u on the chosen
decomposition group at some v above ℓ, read as relations on functions on Gal(Ω/E). -/
def crysRels := ⋃ v, Finsupp.mapDomain Subtype.val '' relationsOn (ZfAt v u)

/-- The loss of the block u modulo ℓ^M: the length of the cocycles obeying the relations among
the w_x(g) − 1, modulo those that obey `crysRels`. -/
abbrev blockLoss {X σ} [Fintype σ] (w : X → Gal(Ω/E) →* Matrix σ σ O) (M : ℕ) := relLength
    (obeyingCocycles w u (ℓ ^ M)) (obeying (crysRels u) _)

lemma obeying_crysRels {a : ↑O} : obeying (crysRels u) (QuotSpan a) = ⨅ v : placesDividing E ℓ,
  (obeying (relationsOn (ZfAt v u))
  _).comap (.funLeft O _ (↑)) := by ext; simp [crysRels, obeying, @forall_comm (_ →₀ _)]; rfl

/-- Function of a complex embedding σ of E returning 1 if σ is the embedding the CM type chooses
at its place, and −1 otherwise. -/
def cmSign {E} [Field E] [c : PlaceEmbedding E] σ := ite (σ = c.1 (.mk σ)) 1 (-1 : ℤˣ)

/-- The complex embedding ι⁻¹ ∘ g⁻¹ ∘ e of E, for e: E → ℚ̄_ℓ and g in G_ℓ. -/
def complexEmbOf {ℓ} [Fact ℓ.Prime] [PadicIso ℓ] e (g : Gp ℓ) := ιℓ.symm.toRingHom.comp
    (g⁻¹.toRingHom.comp (α := E') e)

/-- Jumps of a row, 1 ≤ r ≤ D.r, t ≤ D.t: each low (h₂/2 ≤ |u| ≤ h₂²) or within D.t of ∓w_j, one
j ≤ m; at most rm/k per embedding with |u| ≤ 2h₂²; at most r negative at σ, σ̄ together. -/
structure IsRowType (r t) (J : _ → Multiset ℤ) where
  rank_mem : r ∈ Set.Icc 1 D.r
  t_le : t ≤ D.t
  low_or_high : ∃ j ≤ D.m, ∀ σ, ∀ u ∈ J σ,
    D.h₂ ≤ 2 * u.natAbs ∧ u.natAbs ≤ D.h₂ ^ 2 ∨ |cmSign σ * u + D.w j (.mk σ)| ≤ D.t
  card_low_le σ : (J σ).countP (·.natAbs ≤ 2 * D.h₂ ^ 2) * D.k ≤ r * D.m
  card_neg_le σ : (J σ).countP (· < 0) + (J (star σ)).countP (· < 0) ≤ r

/-- The l-adic valuation of (2b)! times the h³-th power of the product of the natural numbers k
with max(b − 30h³, 0) < k ≤ b + 30h³. -/
@[irreducible] def lambdaLoss (h b l : ℕ) := padicValNat l
    ((2 * b).factorial * (∏ k ∈ .Ioc (b - 30 * h ^ 3) (b + 30 * h ^ 3), k) ^ h ^ 3)

/-- The local loss at l: 10⁶(m/k)(b₁·v_l(g) + lam), with lam = `lambdaLoss` at h₂, b₁ and l. -/
def loss (l : ℕ) :
  NNReal := 10 ^ 6 * (D.m / D.k * (D.b₁ * padicValNat l D.gProd + lambdaLoss D.h₂ D.b₁ l))

lemma coeffEmb_surjective : (coeffEmb O).Surjective := (let := ·.toAlgebra
                have := isAlgebraic_iff_top ℤ_[ℓ] O (A := PadicAlgCl ℓ).1 inferInstance
                have := (faithfulSMul_tower_top ℤ_[ℓ] O ℂ_[ℓ]).to_isTorsionFree
                (exists_gp_eq_algHom (lift.restrictScalars (S := O) _)).imp fun _ h ↦ AlgHom.ext
                  ((h _).symm.trans <| lift.2 ·))

lemma tateTwist_smul {A} {h : PadicPlaceEmbedding E A ℓ} c g (x : Unit → ↑O) :
  tateTwist ℓ E O c g.1 • x = cyclotomicGp (h.toGp g) ^ (-c : ℤ) • x := by simp [_root_.funext_iff,
  h.cyclotomicGp_eq_cycChar, tateTwist, cycInv, Units.smul_def, Algebra.smul_def]

lemma IsCompletionGroup.complexEmbOf_eq_iff {E Γ} [Field E] [Group Γ] [TopologicalSpace Γ] {e :
  E →+* PadicAlgCl ℓ} {j : Γ →* Gp ℓ} [PadicIso ℓ] (hj : IsCompletionGroup e j) {g g'} :
  complexEmbOf e g = complexEmbOf e g' ↔ g * g'⁻¹ ∈ j.range := by
  simp [complexEmbOf, g.symm_apply_eq, eq_comm, RingHom.ext_iff, hj.2]

variable {Γ} [Group Γ] [TopologicalSpace Γ] {e : E' →+* PadicAlgCl ℓ} {j : Γ →* Gp ℓ} [PadicIso ℓ]

lemma IsCompletionGroup.index_eq_card_range (hj : IsCompletionGroup e j) : j.range.index =
  .card (Set.range (complexEmbOf e)) := Nat.card_congr ((Quotient.congr (.inv _) (by
  simp [hj.complexEmbOf_eq_iff, QuotientGroup.leftRel_eq])).trans (Setoid.quotientKerEquivRange _))

lemma sum_complexEmbOf_le (a : _ → ℕ) : ∑ v, ∑ σ with ∃ g, complexEmbOf
  ((localChart ℓ E v).e.comp (algebraMap E Ω)) g = σ, a σ ≤ ∑ σ, a σ := (sum_biUnion fun _ _ _ _ ↦
  (disjoint_filter.2 fun _ _ ⟨_, H⟩ ⟨_, K⟩ ↦ · (by ext; simpa [← ((localChart ℓ E
  _).inducesPlace.1.1 ▸ FinPlace.isPlaceOver_placeOver _) _, val_comap_lt_one, complexEmbOf,
  ← smul_coe_Cp] using congr(‖(ιℓ ($(H.trans K.symm) _) : ℂ_[ℓ])‖ < 1)))).ge.trans (by gcongr; simp)

/-- Let A span Z, of finite dimension, x_b ∈ Z. Suppose each nonzero p ∈ A has a map G, a multiple
of j on each v ∈ A, whose scalars ι⁻¹(l) at p have ‖lm‖ ≥ e^{−γ}, and ‖m·ιη_a(w)‖ ≤ 1 if w ∈ Z,
jw = Gx_b. Then ‖ι det η_a(x_b)‖ ≤ e^{γ dim Z}. -/
lemma norm_gram_det_le_of_operators {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] {A Z} (hZ : span ℂ A = Z) [Module.Finite ℂ Z] (j : V →ₗ[ℂ] W) (η : Fin (finrank ℂ
  Z) → Dual ℂ V) {x : _ → V} (hx : ∀ b, x b ∈ Z) {γ} m (h : ∀ p ∈ A, p ≠ 0 → ∃ G : V →ₗ[ℂ] W, (∀ v ∈
  A, ∃ l : ℂ, G v = l • j v) ∧ (∀ l, G p = l • j p → exp (-γ) ≤ ‖ιℓ l * m‖) ∧ ∀ a b, ∀ w ∈ Z, j w =
  G (x b) → ‖m * ιℓ (η a w)‖ ≤ 1) : ‖ιℓ (of fun a b ↦ η a (x b)).det‖ ≤ exp (finrank ℂ Z * γ) := by
  subst Z; let ⟨ω, hω, e, i⟩ := exists_fun_fin_finrank_span_eq ℂ A
  choose G l hl h using (h _ (hω _) <| i.ne_zero ·); choose l hG using (l · _ <| hω ·)
  let ⟨d, hd⟩ := exists_val_coeff_le_val_eval NormedField.valuation (∑ p, (ιℓ ∘ l p) · • C m * X p)
  have hd k := by simpa [coeff_sum, ← norm_mul] using NNReal.coe_mono (hd k (.single k 1))
  choose P hP using by simpa [← e, mem_span_range_iff_exists_fun] using hx
  have t : ‖_‖ ≤ 1 := IsIntMatrix.det_mem (M := of (ιℓ ∘ η · ∘ ω) * diagonal
    (fun k ↦ ∑ p, ιℓ (l p k) * (m * d p)) * (of P)ᵀ.map ιℓ) fun a b ↦ by
    convert Subring.sum_mem _ (t := univ) fun p _ ↦ mul_mem (d p).2 (h p a b
      (∑ k, P b k • l p k • ω k) (sum_mem (by bound)) (by simp [← hP, hG]))
    simpa [mul_apply, diagonal, mul_sum, sum_mul] using sum_comm.trans (by ac_rfl)
  grw [det_mul_right_comm, det_mul, det_diagonal, norm_mul, norm_prod, ← hd, ← hl _ _ (hG ..)] at t
  simpa [det_apply', ← hP, mul_apply, exp_neg, exp_nat_mul, field, mul_comm (P ..)] using t
