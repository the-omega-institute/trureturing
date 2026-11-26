import OmegaMath.NumberTheory.GRH.Lib.GaloisRep.Pseudocharacter.SemisimpleReps
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: pseudocharacters, Brauer–Nesbitt, Clifford, and the fact that compact subgroups of
GL_n stabilise a lattice. The hypothesis of `exists_rep_of_pseudo` asks for all polynomial
identities among traces, not only the Frobenius
identity, so no invariant theory is needed. Semisimple means a non-degenerate trace form on the span
of the image, in characteristic 0, and limits of traces and continuity from the trace are added.
Source: R. Taylor, Galois representations associated to Siegel modular forms of low weight, Duke
Math. J. 63 (1991), Theorem 1; R. Rouquier, Caractérisation des caractères et pseudo-caractères, J.
Algebra 180 (1996); K. Conrad, Compact subgroups of GL_n(Qbar_p) (note).

This file: Cancelling disjoint sets of characters from two semisimple representations with equal
trace differences. Traces of powers determine eigenvalues and characteristic polynomials in
characteristic zero. Functions obeying all trace identities are traces of semisimple
representations. det(1 - cN) as product over eigenvalues. A vanishing finite sum descends along a
map, weighted by fibre sizes. -/

section

variable {k G m : Type} [Field k] [Group G] [Fintype m] (μ : G →* kˣ) (R : G →* GL m k)

/-- For a character μ of G and a matrix representation R over k, the representation g ↦
μ(g)R(g). -/
noncomputable abbrev twistByChar := MonoidHom.mk' (fun g ↦ μ g • R g) (by aesop (add simp
        smul_mul_smul))

lemma IsTraceNondeg.twist {R : G →* GL m k} (h : IsTraceNondeg R) μ :
  IsTraceNondeg (twistByChar μ R) := by simp_all [IsTraceNondeg, Submodule.mem_span, Units.smul_def]

/-- Over algebraically closed k of characteristic 0, let r₀, r₁ be semisimple of rank n+t with
tr r₀ − Σψ₀ⱼ = tr r₁ − Σψ₁ⱼ, no character ψ₀ᵢ being a ψ₁ⱼ. Then some semisimple s of rank n
has tr rᵢ = tr s + Σψᵢⱼ. -/
lemma IsTraceNondeg.exists_cancel_chars {n t : Type} [Fintype n] [Fintype t] [CharZero k]
  [IsAlgClosed k] (hN : Fintype.card m = Fintype.card n + Fintype.card t) {r : _ → G →* GL m k} (h :
  ∀ i, IsTraceNondeg (r i))
  {ψ : Fin 2 → t → G →* kˣ} (hne : ∀ i j, ψ 0 i ≠ ψ 1 j) {T : G → k} (ht : ∀ i g, (r i g).1.trace
  = T g + ∑ j, (ψ i j g).1) : ∃ s : G →* GL n k, IsTraceNondeg s ∧ ∀ g, T g = (s g).1.trace := by
  choose _ _ _ s f _ u a using exists_wedderburn (k := k) ⟨⟨fun g i ↦ ((r i g).1, (ψ i · g |>.1)),
    by aesop⟩, by bound⟩ (.id _) fun x m ↦ by simp_all [funext_iff, Prod.ext_iff, forall_and,
    fun i ↦
    (h i).hasSemiprimeSpan (x i).1 (by induction m using Submodule.span_induction <;> aesop)]
  let τ i := (Matrix.traceLinearMap ..).coprod (-∑ j, .proj j) ∘ₗ .proj i ∘ₗ f.toLinearMap
  exact (exists_rep_of_trace u (τ 0) (by simp [τ]; grind [Matrix.trace_mul_comm]) (fun i ↦ by
    by_contra H; choose j _ using fun o ↦ Function.ne_iff.1 fun E : (f (piMatrixUnit i) o).2 = 0 ↦
      H (by simp [τ, E, trace_of_idempotent congr(($(isIdempotentElem_map_piMatrixUnit f i) o).1),
      (LinearMap.ext_on_range u (by simp_all) : τ 0 = τ o)])
    have (g) o := congr((f $(show piMatrixUnit i * (s g - s g i 0 0 • 1) * piMatrixUnit i = 0 by
      simp [← Pi.single_mul_left]) o).2 (j o))
    exact hne (j 0) (j 1) (by ext; simp_all)) (by aesop)).imp (by aesop)

open Matrix Polynomial IsAlgClosed
variable {k : _} {n} [Field k] [IsAlgClosed k] [Fintype n] (A : Matrix n n k)

/-- For a square matrix A over an algebraically closed field and a polynomial q, det q(−A) is
the product of q(−x) over the roots x of the characteristic polynomial of A, counted with
multiplicity. -/
lemma det_aeval_neg_eq_prod_roots q : (aeval (-A) q).det = (A.charpoly.roots.map (q.eval <|
  -·)).prod := by refine Submonoid.closure_induction_left ?_ ?_ (splits q) <;> simp_all [or_imp,
  forall_and, ← (splits _).eval_eq_prod_roots_of_monic, charpoly_monic, card_roots_eq_natDegree,
  neg_add_eq_sub, eval_charpoly, algebraMap]

lemma trace_pow_eq_sum_roots m : (A ^ m).trace = (A.charpoly.roots.map (· ^ m)).sum := by
  rw [trace_eq_sum_roots_charpoly, (charpoly _).funext, roots_multiset_prod_X_sub_C]
  simpa [eval_charpoly, eval_multiset_prod] using!
    (det_aeval_neg_eq_prod_roots A <| C · - (-X) ^ m :)

/-- Over an algebraically closed field of characteristic 0, if tr A^m = tr B^m + ∑_{e∈S} α_e^m
for all m ≥ 0, with S finite, then the characteristic polynomial of A is that of B times
∏_{e∈S} (X − α_e). -/
lemma charpoly_eq_mul_of_trace_pow_add [CharZero k] {r ι} [Fintype r] {B : Matrix r r k} S
  (α : ι → k) (h : ∀ m, (A ^ m).trace = (B ^ m).trace + ∑ e ∈ S, α e ^ m) : A.charpoly = B.charpoly
  * ∏ e ∈ S, (X - C (α e)) := have H s t := by simpa [Finsupp.linearCombination, Finsupp.sum,
    -nsmul_eq_mul, ← Finset.sum_multiset_map_count] using (Multiset.toFinsupp.injective <| ((
  linearIndependent_monoidHom ..).comp _ (powersHom k).injective).restrict_scalars' ℕ · : _ → s = t)
  funext (by simp [eval_prod, (splits _).eval_eq_prod_roots_of_monic, charpoly_monic, H _
    (_ + S.1.map α) (funext (by simpa [Pi.multiset_sum_apply, trace_pow_eq_sum_roots] using! h))])

end

open Filter MvPolynomial Finset Submodule Metric Matrix MonoidAlgebra Ideal.Quotient LinearMap
  Module IsAlgClosed IsUniformAddGroup
variable {k K G n ι : Type} [Field k] [NormedField K] [Group G] [Fintype n] (S : Set (ι → K))

/-- For a set S of functions ι → K, K a normed field, the closure of the K-span of S in the topology
of uniform convergence. -/
def uniformClosure : Submodule K (ι → K) := (topologicalClosure (M := UniformFun ..) (span K S) :)

variable {S f}

lemma mem_uniformClosure : f ∈ uniformClosure S ↔ ∀ ε > 0, ∃ g ∈ span K S, ∀ x, ‖f x - g x‖ ≤
  ε := by simpa [dist_eq_norm] using!
  mem_closure_iff_nhds_basis (UniformFun.hasBasis_nhds_of_basis _ _ f uniformity_basis_dist_le)

/-- The submonoid N of pairs (t, (x_{η,i})) is closed, and Σ_i c_{η,i} x_{η,i} → t as η → 0⁺,
uniformly over N. -/
def IsApproximatingMonoid (s : Set.Ioi (0 : ℝ) → ℕ) (c : ∀ _, _ → K) (N :
  Submonoid (K × ((Σ η, Fin (s η)) → K))) :=
  IsClosed N.carrier ∧ TendstoUniformly (fun η (p : N) ↦ ∑ i, c η i * p.1.2 ⟨η, i⟩) (·.1.1) atBot

/-- Let f ≠ 0 be a uniform limit of combinations of functions in S. There are y_i in S,
coefficients c and a monoid N with `IsApproximatingMonoid`, containing (λ, (λ_i)) whenever a linear
T preserving sup-norm bounds has Tf = λf and Ty_i = λ_i y_i. -/
lemma isApproximatingMonoid_of_mem_closure (hf : f ≠ 0) (h : f ∈ uniformClosure S) : ∃ s c N,
  IsApproximatingMonoid s c N ∧ ∃ y : _ → S, ∀ p : K ×
  (_ → K), (∃ T : End K (ι → K), (∀ f r, (∀ x, ‖f x‖ ≤ r) → ∀ x, ‖T f x‖ ≤ r) ∧ T f = p.1 • f ∧
  ∀ i, T (y i) = p.2 i • y i) → p ∈ N := (Function.ne_iff.1 hf).elim fun z (o : _ ≠ 0) ↦ by
  choose s a y b using Subtype.forall'.1 (by
    simpa [mem_span_set', mem_uniformClosure, ↓← Pi.sub_apply] using smul_mem _ (f z)⁻¹ h)
  refine ⟨s, _, .topologicalClosure ⟨⟨_, (·.rec fun T _ ↦ .imp' (· * T) (by simp_all [mul_smul]))⟩,
    .intro 1 (by simp)⟩, ⟨isClosed_closure, tendstoUniformly_iff.2 (eventually_lt_atBot ⟨·, ·⟩
    |>.mono fun η e p ↦ (le_on_closure (by rintro q ⟨T, t, _, v⟩; simpa [v ⟨η, _⟩, *,
    ← dist_eq_norm, mul_comm, ← mul_assoc] using t _ _ (b η) z) ?_ ?_ p.2).trans_lt e)⟩,
    (·.rec y), subset_closure⟩ <;> fun_prop

attribute [local simp] Multiset.esymm det_apply DFunLike.ext_iff Finsupp.sum lift_apply
  Function.comp_def mul_assoc Prod.fst_prod Prod.snd_prod eval_monomial mul_sum Finsupp.prod

lemma IsApproximatingMonoid.tendstoUniformly_eval {P s c N} (h : IsApproximatingMonoid s c N) (B :
  MvPolynomial ι K) (f : P → ι → N) : TendstoUniformly (fun η p ↦ ∑ i, c η i * B.eval
  (f p · |>.1.2 ⟨η, i⟩)) (fun p ↦ B.eval (f p · |>.1.1)) atBot := B.induction_on' (fun m a ↦ by
    simpa [mul_left_comm] using (uniformContinuous_mul_left' a).comp_tendstoUniformly (h.2.comp
    fun p ↦ m.prod (f p · ^ ·))) fun _ _ ↦ by simpa [mul_add] using .add

/-- Polynomials N(j,m) over k in X_0, X_1, … with N(0,m) = 1, N(j+1,m) = X_m N(j,1) − j
N(j,m+1); N(j,1) expresses j!·e_j in power sums. -/
noncomputable def newtonPoly : ℕ → ℕ → MvPolynomial ℕ k := Nat.rec 1 fun j b m ↦
  X m * b 1 - j • b (m + 1)

lemma eval_newtonPoly (s : Multiset k) : ∀ j, eval (fun m ↦ (s.map (· ^ m)).sum) (newtonPoly j 1) =
  j.factorial * s.esymm
  j := have (a : k) p j : ∀ m, eval (fun m ↦ a ^ m + p m) (newtonPoly j.succ m) = eval p (newtonPoly
    j.succ m + j • a • newtonPoly j m + a ^ m • newtonPoly j 1) ∧ (newtonPoly j.succ
    m).constantCoeff = (0 : k) := by induction j with (simp_all [newtonPoly]; grind)
  by induction s using Multiset.induction with rintro ⟨⟩ <;> simp! [*, this 0 0, newtonPoly.eq_1 0,
    Multiset.sum_map_mul_left, Multiset.powersetCard_zero_right] <;> ring

/-- Pseudo-representations (Procesi, Taylor): over an algebraically closed field k of characteristic
0, a function T: G → k satisfying every polynomial identity that holds among traces of homomorphisms
G → GL_n(k) is the trace of a semisimple representation G → GL_n(k). -/
lemma exists_rep_of_pseudo [IsAlgClosed k] [CharZero k] {T} (h : ∀ B, (∀ x : G →* GL n k, eval (x ·
    |>.1.trace) B = 0) → eval T B = 0) : ∃ r, IsTraceNondeg (n := n) r ∧ ∀ g, (r g).1.trace =
  T g := by
  let t := (aeval T).toLinearMap ∘ₗ Finsupp.lift _ k G X ∘ₗ (coeffLinearEquiv k).1
  have h B (b : ∀ ρ : _ →ₐ[k] _, eval (trace <| ρ ·) B = 0) : B.eval t = 0 := B.aeval_bind₁ T _
    ▸ h _ (by simpa [← aeval_eq_eval, aeval_bind₁] using b <| lift _ _ _ <| (Units.coeHom _).comp ·)
  have c x y := by simpa [@trace_mul_comm n n] using h (X (x * y - y * x))
  let I : Ideal _ := ⟨((mul k _).compr₂ t).ker.1, (by simp_all [c ·])⟩
  have : I.IsTwoSided := ⟨by aesop⟩
  let τ : _ ⧸ I →ₗ[k] _ := liftQ _ t (mul_one · ▸ congr($(·) 1))
  have hN l : ∀ x, (∀ m, x ^ m.succ = l ^ m • x) → ∃ j : ℕ, τ x = j * l := mk_surjective.forall.2
    fun x _ ↦ have e j : ∀ m, (newtonPoly j.succ m.succ).eval (τ <| x ^ ·) =
      l ^ m * ∏ i ∈ range (j + 1), (τ x - i * l) := by induction j with simp_all [newtonPoly,
      prod_range_succ] <;> grind [‹∀ _, _› 0]
    by grind [e (Fintype.card n) 0 ▸ eval_rename (x ^ ·) t _ ▸ h _ (by simp [eval_rename,
      eval_newtonPoly, trace_pow_eq_sum_roots, card_roots_eq_natDegree]), prod_eq_zero_iff]
  have : Module.Finite k (_ ⧸ I) :=
    rank_lt_aleph0_iff.1 (.trans' Cardinal.natCast_lt_aleph0 (not_le.1
    ((le_rank_iff.trans mk_surjective.comp_left.exists).not.2 (·.rec fun (s : Fin (Module.finrank k
    (Matrix n n k) + 1) → _) l ↦ minors_eq_zero_iff.1 (fun b ↦
    by simpa using! h (of (X <| s · * b ·))ᵀ.det (by simpa using! minors_eq_zero_iff.2 (mt
    (·.of_comp (pi (traceLinearMap n k k ∘ₗ mulRight k ·)) |>.fintype_card_le_finrank) (by simpa
    using .refl)) <| · ∘ b)) ((l.map' _ (ker_liftQ_eq_bot' _ _ rfl)).map' (ltoFun ..)
      (by aesop))))))
  choose _ _ _ s f _ u _ using exists_wedderburn (k := k) ((mk I).1.comp (of ..))
    (.id G) (mk_surjective.forall.2 fun x _ _ ↦ eq_zero_iff_mem.2 (by
    ext; simpa using! hN 0 ↑(x * _) (by cases · with simp_all [pow_succ', ← mul_assoc])))
  peel exists_rep_of_trace u (τ ∘ₗ f) (by simpa using fun x y ↦ (f x).ind₂ c (f y)) (by
    simpa using hN 1 _ <| by simp [isIdempotentElem_map_piMatrixUnit f · |>.pow_succ_eq])
      (by simpa using! (h (X 1 - ∑ _ : n, 1):))
  simp_all; show t _ = _; aesop

/-- Given `IsApproximatingMonoid` s c N and continuous r_x, suppose for each g a proper filter on N
has first coordinate eventually in a complete L, second tending to (tr r_x(g))_x. Then (tr R(g), (tr
r_x(g))_x) ∈ N for all g, some continuous semisimple R. -/
lemma exists_trace_limit [TopologicalSpace G] [IsTopologicalGroup G] [IsAlgClosed K] [CharZero K] {s
  c N} (h : IsApproximatingMonoid s c N) (F : G → Filter N) [∀ g, (F g).NeBot] {L} (hL : IsComplete
  L) (w : ∀ g, ∀ᶠ p in F g, p.1.1 ∈ L) {r : _ → G →* GL n K} (hr : ∀ x, Continuous (r x)) (hφ : ∀
  g x, (F g).Tendsto (·.1.2 x) (nhds (r x g).1.trace)) : ∃ R : G →* GL n K, Continuous R ∧
  IsTraceNondeg R ∧ ∀ g, ((R g).1.trace, (r · g |>.1.trace)) ∈ N := by
  choose T _ hT using fun g ↦ hL _ ((cauchy_map_iff_tendsto ..).2 ⟨map_neBot, ((h.2.comp _).sub
    (h.2.comp _)).tendsto_of_eventually_tendsto (univ_mem' fun _ ↦ ((cauchy_map_iff_tendsto ..).1
    (tendsto_finsetSum _ fun _ _ ↦ (hφ g _).const_mul _).cauchy_map).2) (by simp)⟩)
    (tendsto_principal.2 (w g))
  have m g := h.1.mem_of_tendsto (.prodMk_nhds (hT g) (tendsto_pi_nhds.2 (hφ g))) (by simp)
  refine (exists_rep_of_pseudo fun D _ ↦ ?_).imp fun R ⟨n, e⟩ ↦ ⟨n.continuous_of_trace (funext e ▸
    (h.2.comp (⟨_, m ·⟩)).continuous (.of_forall (by fun_prop))), n, (e · ▸ m _)⟩
  simpa [*, eq_comm] using (h.tendstoUniformly_eval D ![(⟨_, m ·⟩)]).tendsto_at 0

lemma det_one_sub_smul_eq_prod_roots {n} [Fintype n] (N : Matrix n n ℂ) c : (1 - c • N).det =
    (N.charpoly.roots.map (1 - c * ·)).prod := by simpa using! det_aeval_neg_eq_prod_roots N (1 +
  c • .X)

lemma finsum_image_eq_zero_of_fibers {T C S} (hS : S.Finite) ψ {G : T → ℂ} {F :
  C → ℂ} {D} (h₀ : ∑ᶠ t ∈ S, G t =
  0) (hN : ∀ t ∈ S, F (ψ t) / Nat.card {s ∈ S | ψ s = ψ t} = G t / D) : ∑ᶠ c ∈ ψ '' S, F c = 0 := by
  lift S to Finset T using hS; rw_mod_cast [finsum_mem_finset_eq_sum] at *
  rw [S.sum_image', ← S.sum_div, h₀, zero_div D]
  intros; rw [Finset.sum_eq_card_nsmul, nsmul_eq_mul, mul_div_cancel₀] <;> simp_all [← hN]; tauto
