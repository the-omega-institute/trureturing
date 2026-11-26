import GRH.Lib.General.LinearAlgebra.Base
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of real and complex analysis (textbook or folklore).

This file: Elementary lower bound n ≤ φ(n)(2 log n + 1) for Euler's totient. Schur polynomials in
polynomial coefficients; bialternant formula with the Vandermonde determinant. Tube lemma for a
jointly continuous map over a compact set. Strong integral of a family of bounded operators; small
calculus helpers. Ostrowski-Taussky determinant inequality; operator norm versus matrix entries. -/

open Finset Real Nat Prime Matrix Polynomial Fin Lagrange MeasureTheory Function

lemma le_totient_mul_log {n} (h : 0 < n) : n ≤ φ n * (2 * Real.log n + 1) := by
  have A (S : Finset ℕ) : ∀ a, (∀ p ∈ S, a < p) → a / (a + #S) ≤ ∏ p ∈ S, (1 - (p : ℚ)⁻¹) :=
    S.induction_on_min (by simp; bound) fun b S m i a h ↦ by
    obtain ⟨_, rfl⟩ := (h b (by simp)).dest
    grw [prod_insert, ← i _ m] <;> simp [field, (m _).mt] <;> nlinarith
  grw [← (pow_card_le_prod _ _ 2 _).trans (le_of_dvd h n.prod_primeFactors_dvd), ← Rat.cast_natCast
    (φ _), totient_eq_mul_prod_factors, ← A _ 1] <;> simp +contextual [field, one_lt, two_le]
  nlinarith [log_two_gt_d9]

variable {a} (l : Fin a → ℕ) {R S : Type} [CommRing R] [CommRing S] (r : Fin a → R)
  (s : Multiset R)

/-- For l in ℕ^a, the determinant of the coefficients of the X^(l j) modulo the generic monic
polynomial of degree a: an integer polynomial in the generic coefficients. -/
noncomputable def genericSchur := (of fun k j ↦ (X ^ l j %ₘ freeMonic ℤ a).coeff k.1).det

/-- The ring homomorphism from integer polynomials in a variables to R sending the i-th variable
to the coefficient of X^i in ∏ (X − r), r running over the multiset s. -/
noncomputable def rootCoeffEval := MvPolynomial.aeval (R := ℤ) fun i : Fin a ↦
  (s.map (X - C ·)).prod.coeff i

lemma rootCoeffEval_map (f : R →+* S) q : @rootCoeffEval a _ _ (s.map f) q = f (rootCoeffEval s
  q) := by simp [rootCoeffEval, ← coeff_map, Polynomial.map_multiset_prod, RingHom.eq_intCast']; rfl

lemma rootCoeffEval_genericSchur_mul_det [IsDomain R] :
  rootCoeffEval (univ.1.map r) (genericSchur l) * (vandermonde r).det = (of (r · ^ l ·)).det := by
  erw [mul_comm, rootCoeffEval, AlgHom.map_det, ← det_mul]; rcongr i
  simpa [mul_comm, -univ_val_map, eval₂_finsetSum] using! (sum_modByMonic_coeff
    (monic_freeMonic ..) (degree_freeMonic ℤ a).le ▸ eval₂_modByMonic_eq_self_of_root
    ((eval₂_eq_eval_map _).trans (congr($((MvPolynomial.mapEquivMonic ..).4 (.mk _ nodal_monic
    (by simp))).1.eval (r i)).trans (eval_nodal_at_node (mem_univ i)))) (p := X ^ _) :)

/-- The subgroup U of G is an open subset of G. -/
@[to_additive] protected abbrev Subgroup.IsOpen {G} [Group G] [TopologicalSpace G]
  (U : Subgroup G) := @IsOpen G _ U

/-- Tube lemma for a jointly continuous f: if W is a neighbourhood of f(x₀, y) for each y in a
compact set K, then f(x, y) ∈ W for all y in K and all x near x₀. -/
lemma IsCompact.eventually_forall_mem {X Y Z} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] {K x₀} (hK : IsCompact K) (f : X → Y → Z) W (h : ∀ y ∈ K, W ∈ nhds (f x₀ y))
    (hf : Continuous f.uncurry := by fun_prop) : ∀ᶠ x in nhds x₀, ∀ y ∈ K, f x y ∈ W :=
  hK.eventually_forall_of_forall_eventually (hf.continuousAt <| h · ·)

lemma Ideal.mk_span_eq_iff_dvd_sub {R} [CommRing R] {a x y : R} :
    Quotient.mk (span {a}) x = Quotient.mk _ y ↔ a ∣ x - y := Quotient.eq.trans mem_span_singleton

variable {Y X Z : Type*} [MeasurableSpace Y] [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z] (μ : Measure Y) (F : Y → X →L[ℂ] Z)

/-- The strong integral of a family F of bounded operators: the bounded operator x ↦ ∫ F(y)x
dμ(y) if this map is one, an unspecified operator otherwise. -/
noncomputable def strongIntegral : X →L[ℂ] Z := invFun (⇑) (∫ y, F y · ∂μ)

/-- For a monoid homomorphism ρ from G to the bounded operators on X, ρ(g)(ρ(h)v) = ρ(gh)v. -/
lemma rep_apply_apply {G} [Monoid G] (ρ : G →* X →L[ℂ] X) g h v : ρ g (ρ h v) =
  ρ (g * h) v := by simp

lemma HasDerivAt.map_clm {f f'} {t : ℝ} (h : HasDerivAt f f' t) (L : X →L[ℂ] Z) :
    HasDerivAt (L <| f ·) (L f') t := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h

/-- For Banach spaces X, Z and a family F of bounded operators with y ↦ F(y)x integrable for
every x, the strong integral of F sends x to the integral of F(y)x. -/
lemma strongIntegral_apply [CompleteSpace X] [CompleteSpace Z] (h : ∀ x, Integrable (F · x) μ) x :
    strongIntegral μ F x = ∫ y, F y x ∂μ := congrFun (invFun_eq ⟨_ ∘L .ofSeqClosedGraph (g :=
  ⟨⟨(h · |>.toL1), by aesop⟩, by aesop⟩) fun _ x _ hu hg ↦ have ⟨_, a, b⟩ :=
    ((tendstoInMeasure_of_tendsto_Lp hg).congr_left fun _ ↦ (h _).coeFn_toL1).exists_seq_tendsto_ae'
  Lp.ext (.symm ((h x).coeFn_toL1.trans (b.mono fun y ↦ tendsto_nhds_unique
  ((F y).2.seqContinuous (hu.comp a))))), by simp [integral, *, L1.integral_eq' ℂ]; rfl⟩) x

open Norms.L2Operator ComplexOrder Fintype
variable {m n} [Fintype m] [Fintype n] {A : Matrix m n ℂ}

lemma l2_opNorm_single {i : m} {j : n} {c : ℂ} : ‖single i j c‖ = ‖c‖ := by
  simp [← _root_.mul_self_inj, ← l2_opNorm_conjTranspose_mul_self, ← diagonal_single,
    Pi.norm_single]

lemma l2_opNorm_le_of_apply {M} (h : ∀ i j, ‖A i j‖ ≤ M) : ‖A‖ ≤
  Fintype.card m * Fintype.card n * M := by
  grw [A.matrix_eq_sum_single, norm_sum_le, norm_sum_le, l2_opNorm_single.le, h]; simp [field]

lemma norm_apply_le_l2_opNorm i j : ‖A i j‖ ≤ ‖A‖ := by
  simpa using (PiLp.norm_apply_le ..).trans (A.l2_opNorm_mulVec (.single j 1))

/-- Ostrowski–Taussky inequality: if H is a positive semidefinite complex n × n matrix and
Θ + Θ* − H is positive semidefinite, then |det H| ≤ 2^n |det Θ|. -/
lemma ostrowski_taussky {Θ H : Matrix n n ℂ} (hH : H.PosSemidef)
    (h : (Θ + Θᴴ - H).PosSemidef) : ‖H.det‖ ≤ 2 ^ Fintype.card n * ‖Θ.det‖ := by
  by_cases H.det = 0; simp [*]
  have k := (H⁻¹ * (2 : ℂ) • Θ).charpoly.roots.prod_induction (1 ≤ ‖·‖)
  simp [← det_eq_prod_roots_charpoly, field, eval_charpoly, ← exists_mulVec_eq_zero_iff] at k
  refine k (by bound) fun l _ v o e ↦ ?_
  apply_fun (star v ⬝ᵥ H *ᵥ · |>.re) at e
  cases h.dotProduct_mulVec_nonneg v
  simp_all [← star_mulVec_dotProduct, star_dotProduct (Θ *ᵥ v)]
  nlinarith! [l.re_le_norm, (hH.posDef_iff_det_ne_zero.2 ‹_›).re_dotProduct_pos o]
