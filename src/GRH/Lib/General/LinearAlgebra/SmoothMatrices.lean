import GRH.Lib.General.LinearAlgebra.CommonEigenvectors
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of linear algebra and matrices (textbook or folklore).

General lemmas of real and complex analysis (textbook or folklore).

This file: A twisted trace identity between commuting families transfers eigensystems. Double
counting of moves between weighted class sums gives proportional traces. Non-stationary phase:
uniform rapid Fourier decay with polynomial loss in a parameter. Smoothness of matrix operations and
exponential; global smooth extension of an analytic germ. -/

open Module End LinearMap Submodule
variable {V V' I I' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [FiniteDimensional ℂ V'] {p : Submodule ℂ V} [FiniteDimensional ℂ p] {b}

lemma trace_restrict_ne_zero {c} (hc : c ≠ 0) (h0 : p ≠ ⊥) (hW : p ≤ maxGenEigenspace b c) h : trace
  ℂ p (restrict b h) ≠ 0 := have := isNilpotent_trace_of_isNilpotent (isNilpotent_iff_of_finite.2
    (mem_genEigenspace_top.1 <| (genEigenspace_restrict _ _ _ _ h).ge <| hW ·.2))
  by aesop

/-- For commuting families A, A', b commuting with A of nonzero trace on the generalised
θ-eigenspace, and tr(A'_{j(w)} A'_i s) = c tr(A_w b) for all words w, c ≠ 0: A' has an
eigenvector in the image of A'_i with s-invariant eigenvalues extending θ. -/
lemma exists_eigenvector_of_trace_identity {J} {B : J → End ℂ V} (st : ∀ a, ∀ v ∈ p,
  B a v ∈ p) {A} (eA : (fun a ↦
  (B a).restrict (st a)) = A) {A' : I' → End ℂ V'} (k : I → J) j b i θ {s} (hA : ∀ a b, Commute (A
  a) (A b)) (hA' : ∀ a b, Commute (A' a) (A' b)) (pos : ∀ h, trace ℂ ↥(p ⊓ ⨅ a, maxGenEigenspace (B
  (k a)) (θ a)) (restrict (B b) h) ≠ 0) {c} (hc : c ≠ 0) (Q : Set _) (q₀ : (A b, A' i) ∈ Q) (q : ∀ t
  ∈ Q, trace ℂ _ (t.2 * s) = c * trace ℂ p t.1 ∧ ∀ a, (A (k a), A' (j a)) * t ∈ Q) : ∃ Θ v w, (∀ a
  b, s * A' a = A' b * s → Θ a = Θ b) ∧ Θ ∘ j = θ ∧ v = A' i w ∧ v ≠ 0 ∧ ∀ a, A' a v = Θ a • v := by
  have hU {g} (hg : ∀ b, Commute g (A b)) {v} (hv : v ∈ _) a :=
    mapsTo_maxGenEigenspace_of_comm ((hg _).mul_left (hA b (k a))).symm (θ a) ((mem_iInf _).1 hv a)
  let S : Submodule ℂ _ := by
    use! {(x, y) | (∀ a, Commute x (A a)) ∧ (∀ a, Commute y (A' a))
      ∧ ∀ t ∈ Q, (∀ a, Commute t.2 (A' a)) → trace ℂ _ (y * t.2 * s) = c * trace ℂ _ (x * t.1)}
      <;> simp_all [add_mul, mul_add, Commute.smul_left, mul_left_comm, -Prod.forall]
  obtain ⟨χ, ⟨⟨⟨x, y⟩, h1, h2, h4⟩, ⟨_, h5⟩, h6⟩, -⟩ := by simpa only [Classical.skolem, mem_iInf,
    genEigenspace_restrict, IsConcreteLE.not_le_iff_exists, mem_comap, mem_maxGenEigenspace,
    ← map_smul, ← map_sub, ← (map_one (Algebra.lmul ..)), ← map_pow] using
      (exists_eigenvector_of_commute
    (S := S) (Algebra.lmul ℂ _ <| Sum.elim (fun a ↦ (A (k a), A' (j a))) (fun b :
    Σ' a b, s * A' a = A' b * s ↦ (0, A' b.1 - A' b.2.1)) ·) (by
    rintro (a | a) x ⟨h1, h2, h4⟩ <;> simp [S, *, sub_mul] <;> intro _ _ e m
    simpa [*, ← mul_assoc, (h1 _).eq, (h2 _).eq] using h4 _ ((q _ e).2 a)
    simp [mul_assoc, (A' _).trace_mul_comm, (m _).left_comm, (h2 _).left_comm, a.2.2])
    (by simp [Commute.left_comm, *, Prod.ext_iff, sub_mul, mul_sub]) (U :=
    (trace .. ∘ₗ ⟨⟨(restrict _ fun _ ↦ (mem_iInf _).2 ∘ hU ·.2.1), by tauto⟩, by tauto⟩).ker)
    (by subst eA; exact ((inf_iInf_maxGenEigenspace_of_forall_mapsTo _ _ (st <| k ·) ▸ pos)
    (by simpa +contextual [*] using! @hU 1) <| (trace_conj' _ (equivSubtypeMap ..)).trans <|
    eq_top_iff'.1 · ⟨1, by simp_all [S, -Prod.forall]⟩)))
  have E a v := mem_genEigenspace_top.2 ⟨_, congr($(h5 a).1 v)⟩
  obtain rfl : χ = Sum.elim θ 0 := funext fun a ↦ by_contra fun m ↦ h6 (ker_le_ker_comp _ _ (ext
    fun v ↦ Subtype.ext ((disjoint_genEigenspace _ m ..).le_bot ⟨E a _,
      a.rec (hU h1 v.2) fun _ ↦ by simpa using ⟨1, rfl⟩⟩)))
  choose Θ _ v n hΘ using by simpa using (exists_eigenvector_of_commute A' (by simpa using fun a ↦
    (⟨_, congr($((h2 a).mul_left (hA' ..)) ·)⟩)) (fun _ _ _ _ ↦ congr($(hA' ..) _))
    (mt (comap_subtype_eq_top.trans (y * A' i).range_le_bot_iff).1 fun _ ↦ h6 (.trans
    (trace_restrict_eq_of_forall_mem _ _ (by aesop)) (by simpa [*] using h4 _ q₀))))
  have r a {z} h := @by_contra (z = _) (n <| disjoint_genEigenspace _ · 1 _ |>.le_bot
    ⟨h, mem_genEigenspace_nat.2 congr($(h5 a).2 _)⟩)
  refine ⟨Θ, _, _, fun a b e ↦ sub_eq_zero.1 (r (.inr ⟨a, b, e⟩) ?_), funext fun a ↦
    r (.inl a) ?_, congr($(h2 i) v), n, hΘ⟩ <;> simp [*, sub_smul]

open Set Finsupp MvPolynomial

/-- a = ∑ w_i F(p_i) for finitely many weighted points p_i, and ∑ w_i #M(p_i, y) = c for every y
such that F(x) ≠ 0 whenever M(x, y) is nonempty. -/
def IsSampleTotal {P A} (M : P → P → Set A) F c a := ∃ w, a = w.lift ℂ ℂ P F ∧
  ∀ y, (∀ x, ∀ g ∈ M x y, F x ≠ 0) → lift ℂ ℂ P (fun x ↦ (M x y).ncard) w = c

/-- Comparison of weighted orbit sums a, b with total weights c, d: let F vanish off S, and
F' = F(x) on the orbit of m(x), x ∈ S. If, whenever F'(y) ≠ 0, the moves from y to the m(x) biject
with those from the x to some z, then bc = da. -/
lemma IsSampleTotal.mul_eq_of_double_count {P Q A B c d a b M N F} F' (H :
  @IsSampleTotal P A M F c a) (H' : @IsSampleTotal Q B N F' d b)
  (m : _ → _) (S : Set _) (o : ∀ x, F x ≠ 0 → x ∈ S) (v : ∀ x ∈ S, ∀ y, ∀ g ∈ N y (m x), F' y = F x)
  (s : ∀ y, F' y ≠ 0 → ∃ z J, ∀ x, BijOn J (M x z) {g ∈ N y (m x) | x ∈ S}) : b * c = d * a := by
  rcases H, H' with ⟨⟨_, rfl, hw⟩, u, rfl, hw'⟩
  simp [mul_comm d, sum_mul, mul_sum, mul_assoc, u.sum_comm, ← fun y ↦ mul_eq_mul_left_iff.2 ((em'
    _).imp_left (s y · |>.elim fun z ⟨_, b⟩ ↦ by simpa [(b _).ncard_eq] using hw z (by grind [BijOn,
    MapsTo]))), ← fun x ↦ mul_eq_mul_left_iff.2 ((em' (F x = 0)).imp_left (hw' (m x) ∘ by grind))]
  congr! 4
  by_cases ‹P› ∈ S <;> simp [*] <;>
    grind [→ nonempty_of_ncard_ne_zero, nonempty_def, Nat.cast_eq_zero]

/-- If the images of p : κ → ι and q : κ' → ι cover ι, every complex polynomial in the variables
ι is a sum of products of a polynomial in the variables p(κ) with one in the variables
q(κ'). -/
lemma mem_rename_range_mul {ι κ κ'} (p : κ → ι) (q : κ' → ι) (h : ∀ i, i ∈ Set.range p ∪ Set.range
  q) P : P ∈ (rename p).range.toSubmodule * (rename (R := ℂ) q).range.toSubmodule := by
  simp_rw [rename_eq_aeval, aeval_range]
  simp [← Algebra.adjoin_union_coe_submodule, Set.range_comp, ← image_union, eq_univ_of_forall h]

open Complex Real SchwartzMap FourierTransform ContDiff MeasureTheory LineDeriv

/-- Let c, q be smooth on T × V, c vanishing for x outside a compact K. For each M some C has
(|a|(1+‖b‖))^M |𝓕(c(s,·)e^{q(s,·)/a})(b)| ≤ CD whenever a ≠ 0, ‖(s,a)‖ ≤ 1 and
|e^{q(s,x)/a}| ≤ D on K. -/
lemma exists_pow_mul_norm_fourier_le {n T : Type} [Fintype n] [NormedAddCommGroup T]
  [NormedSpace ℝ T] [ProperSpace T] {K} (hK : IsCompact K) M {c q : T × EuclideanSpace ℂ n → ℂ}
  (hc : ContDiff ℝ ∞ c) (hq : ContDiff ℝ ∞ q) (h : ∀ p, p.2 ∉ K → c p = 0) : ∃ C, ∀ b s a D,
  ‖(s, a)‖ ≤ 1 → a ≠ 0 → (∀ x ∈ K, ‖(q (s, x) / a).exp‖ ≤ D) →
  (‖a‖ * (1 + ‖b‖)) ^ M * ‖𝓕 (fun x ↦ c (s, x) * (q (s, x) / a).exp) b‖ ≤ C * D := by
  induction' M with M ih generalizing T
  apply (((isCompact_closedBall 0 1).prod hK).exists_bound_of_continuousOn
    hc.continuous.continuousOn).imp' (· * _)
  simp_intro ..
  grw [fourier_eq, mul_right_comm, ← setIntegral_eq_integral_of_forall_compl_eq_zero,
    norm_setIntegral_le_of_norm_le_const hK.measure_lt_top] <;>
    simp_all [norm_mul_le_of_le, -norm_mul, -Complex.norm_mul]
  refine (ih (c := fun ((s, v, a), x) ↦ a * (I * c (s, x) + fderiv ℝ (c ⟨s, ·⟩) x v) + c (s, x) *
    fderiv ℝ (q ⟨s, ·⟩) x v) (by fun_prop) (hq.comp (contDiff_fst.prodMap contDiff_id)) fun _ o ↦ by
    simp [*, (Filter.eventuallyEq_of_mem (hK.isClosed.compl_mem_nhds o) (h ⟨_, ·⟩)).fderiv_eq]).imp
    fun C H b s a D n o k ↦ ?_
  let F := ((HasCompactSupport.intro hK (h ⟨s, ·⟩)).smul_right
    (f' := (q ⟨s, ·⟩ / a |>.exp))).toSchwartzMap (by fun_prop)
  grw [← H b (s, ‖b‖⁻¹ • b, a) a D (by simpa [norm_smul, inv_mul_le_one] using n) o k,
    _root_.funext fun x ↦ (?_ : (_ + _) * _ = (a • (I • F + ∂_{‖b‖⁻¹ • b} F)) x), ← fourier_coe] <;>
    simp (disch := fun_prop (maxTransitionDepth := 2) (disch := simp)) [fourier_lineDerivOp_eq,
    -smul_add, ← add_mul, pow_succ, ← mul_assoc, lineDerivOp_apply, lineDeriv, F, inner_smul_right,
    ↓← DifferentiableAt.lineDeriv_eq_fderiv]
  gcongr
  exacts [(im_le_norm _).trans' (by simp; nlinarith [norm_nonneg b, two_le_pi]), le_rfl, by
    field]

open Matrix Norms.Elementwise NormedSpace
variable {X l m o N} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype l] [Fintype m]

/-- A map from a finite-dimensional real normed space to a real normed space that is analytic at
x agrees near x with a globally smooth map. -/
lemma exists_contDiff_eventuallyEq {Y} [FiniteDimensional ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] {f : X → Y} {x} (hf : ContDiffAt ℝ ω f x) : ∃ g, ContDiff ℝ ∞ g ∧ g =ᶠ[nhds x]
    f := ((SmoothBumpFunction.nhds_basis_tsupport x).mem_iff.1 (hf.eventually nofun)).imp' _
    fun b h ↦ ⟨(contMDiff_of_tsupport fun _ y ↦ b.contMDiffAt.smul ((h.2 (by
    cat_disch)).contMDiffAt.of_le le_top)).contDiff, b.eventuallyEq_one.mono (by aesop)⟩

@[fun_prop] lemma contDiff_star : ContDiff ℝ N (starRingEnd ℂ) := (starL' ℝ).contDiff

@[fun_prop] lemma contDiff_matrix_mul [Fintype o] : ContDiff ℝ N fun p : Matrix l m ℂ × Matrix m o ℂ
    ↦ p.1 * p.2 := by unfold_projs; fun_prop [dotProduct]

@[fun_prop] lemma contDiff_conjTranspose : ContDiff ℝ N (@conjTranspose l m ℂ _) :=
  contDiff_pi' (by simp [contDiff_pi]; fun_prop)

@[fun_prop] lemma contDiff_matrix_exp : ContDiff ℝ N (NormedSpace.exp (𝔸 := Matrix m m ℂ)) :=
  open Norms.Operator in let e : (m → m → ℂ) ≃L[ℝ] Matrix m m ℂ := .refl ..
  (e.comp_contDiff_iff.1 ((AnalyticOnNhd.contDiff fun _ _ ↦ exp_analytic _).comp e.contDiff) :)
