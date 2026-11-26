/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/Division/MultiplicityFreeSum
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/Division/MultiplicityFreeSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.Division.MultiplicityFreeSum. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/Division/MultiplicityFreeSum.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.Main.HeckeOperatorOfFunction
import D5.S3.Zeros.GRH.Lib.PadicHodge.Characters.LocalCharacters
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! In one step of a known theorem
(Galois representations for definite unitary groups),
degree-n polynomials kill most Frobenius elements and a cocharacter with very different exponents
forces rank n. In the literature, Frobenius polynomial relations on a dense set determine a
representation when the n-dimensional one is known and large. Related work: Boston–Lenstra–Ribet
1991; Nekovář, Eichler–Shimura relations and semisimplicity, 2018; Fayad–Nekovář 2019; Harris–Taylor
2001, VII.1.8.

Part of: ℓ-adic avatar of an algebraic Hecke character and its local behaviour (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

Part of: Galois representations attached to forms on definite unitary groups (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

This file: Degree-n killing polynomials and free cocharacter weights force rank n and characteristic
polynomials. Twisting a Galois representation by an algebraic Hecke character shifts weights and
Hecke polynomials. Sum of distinct irreducible constituents keeps goodness, occurring weights and
killing polynomial. -/

section

attribute [-simp] Matrix.map_mul LaurentPolynomial.single_eq_C_mul_T LaurentPolynomial.T_pow
  det_classical

open Matrix MvPolynomial Polynomial Finset Algebra Fintype Submodule Function ConjAct
  LaurentPolynomial Fin Filter
variable {k K N R S A : Type} [NormedField k] [Fintype N] [CommRing R] [CommRing S] {m n}
  {e : Fin n → ℤ} (y : Matrix N N R) [NormedField K] [NormedAlgebra K k] [CommRing A] [Algebra A R]
  [Algebra A S]

attribute [local simp high] mvPolynomialX_mapMatrix_aeval Matrix.sum_apply coeff_X_mul' comp_def sq
  units_smul_def mul_assoc LaurentPolynomial.algebraMap_apply map_mul ofId
  Finsupp.weight_single isHomogeneous_C_mul_X IsHomogeneous.sum IsHomogeneous.mul

/-- For a square matrix y and m positions a(i), the determinant of the m×m matrix whose (i,j)
entry is the a(i) entry of y^j, 0 ≤ j < m. -/
noncomputable abbrev powMinor m a := (of (flip (uncurry <| y ^ @Fin.val m ·) ∘ a)).det

@[simp] lemma map_powMinor a (φ : R →ₐ[A] S) : φ (powMinor y m a) = powMinor (φ.mapMatrix y) m a :=
  by simp [powMinor, ↓← map_pow, φ.map_det]; rfl

/-- Let e be free integers indexed by n, c: N → n surjective, x ∈ GL_N(k), m ≤ |n|+1. If all
`powMinor` of order m of diag(T^{e∘c})x vanish in k[T,T⁻¹], then |n| < m and x⁻¹ is
scalar on each fibre block of c. -/
lemma FreeInts.inv_scalar_on_blocks {c} (he : FreeInts e) (hc : Surjective c) {x : GL N k} (hm : m ≤
  n + 1) (h : ∀ a, powMinor (diagonal (T ∘ e ∘ c) * x.1.map .C) m a = 0) : n < m ∧
  ∀ {a b}, c a = c b → a ≠ b → x⁻¹ a b = 0 ∧ x⁻¹ a a = x⁻¹ b b := by
  let y := diagonal (X ∘ c) * x.1.map .C
  have hy j : ∀ a b, ((y ^ j) a b).IsHomogeneous j := by induction j <;>
    simp_all [← totalDegree_zero_iff_isHomogeneous, y, pow_add, mul_apply, diagonal, mul_comm (X _),
      apply_ite]
  let z := (ofId _ (FractionRing (MvPolynomial (Fin n) k))).mapMatrix y
  have (o : m ≤ _) := minors_eq_zero_iff.1 (fun a ↦ (map_powMinor ..).symm.trans (by
    simpa [-map_powMinor] using congr($((map_powMinor y a (AddMonoidAlgebra.mapDomainAlgHom k k
      _)).trans (.trans (by simp [y, MvPolynomial.X, ← single_eq_monomial, T, ↓algHom_C]) (h
      a))).coeff.support).symm.trans (Finsupp.mapDomain_support_of_injOn _ (.mono
      ((homogeneousSubmodule_eq_finsupp_supported ..).le (by simpa [det_apply'] using (.sum _ _ _
      fun _ _ ↦ .C_mul (.prod _ _ _ (by tauto)) _))) (he _ (by grw [isLt, ← hm]; simp))))))
    (((linearIndependent_pow z).comp _ (castLEEmb o).2).of_comp (LinearEquiv.curry ..).1)
  obtain ⟨M, D⟩ := minpoly.monic z.isIntegral, z.minpoly_dvd_charpoly.trans (charpoly_map ..).dvd
  choose s hq _ U using lifts_and_natDegree_eq_and_monic (by
    simpa [M] using! IsIntegrallyClosed.eq_map_mul_C_of_dvd _ y.charpoly_monic D) M
  have ⟨w, hw⟩ := (map_dvd_map _ (IsFractionRing.injective ..) U).1 (hq ▸ D)
  obtain ⟨⟨α, v⟩⟩ := by simpa [det_eq_sign_charpoly_coeff, hw, ne_zero_iff] using
    (by simpa [y, prod_eq_zero_iff] using (x.map _).det_ne_zero : y.det ≠ 0)
  have : ((optionEquivLeft ..).symm y.charpoly).totalDegree ≤ card N := by
    simp [charpoly, det_apply, y, charmatrix, diagonal_apply, apply_ite]
    grw (transparency := .default) [totalDegree_finsetSum, totalDegree_smul_le,
      totalDegree_finsetProd, totalDegree_sub, totalDegree_mul]; simp [ite_apply, apply_ite]
  grw [← y.charpoly_natDegree_eq_dim, hw, map_mul, totalDegree_mul_of_isDomain (by aesop)
    (by aesop), natDegree_mul_le, ← totalDegree_coeff_optionEquivLeft_le, ← le_totalDegree
    (by simpa), ← degreeOf_le_totalDegree, ← natDegree_optionEquivLeft] at this
  have hr := s.X_mul_divX_add ▸ (ext (by
    simpa [z, ↓aeval_algHom_apply,
      ↓Polynomial.aeval_map_algebraMap] using congrFun₂ congr(aeval z $hq)) : s.aeval y = 0)
  have h2 a b := congr((($((s.divX.divX_mul_X_add ▸ hr :)) * x.1⁻¹.map .C :) a b).coeff α)
  simp [y, add_mul, mul_add, algebraMap, α.sum_fintype, ↓map_add] at *
  simp [← mul_assoc, coeff_mul_X', mul_comm (s.coeff _), ← @eq_of_le_of_not_lt _ _ 1 ⇑α (hc.forall.2
    fun a ↦ Nat.pos_of_ne_zero fun z ↦ by simpa [*] using congr(($hr a a).coeff α))
    (by bound [by simpa using sum_strictMono ·])] at *
  grind [diagonal_apply, MvPolynomial.coeff_zero]

/-- Division: let continuous r: G_E → GL_N(K) span all diagonal matrices and monic P_y of degree n
kill r at most Frobenii y. If polynomials vanishing at Q·r(g) near 1 vanish at diag(T^κ)Q over
k[T,T⁻¹], with n free integers among the κ_a, then N = n and P_y = charpoly at most Frobenii. -/
lemma rank_eq_and_charpoly_eq [NeZero n] {E} [Field E] [NumberField E] [Algebra E Ω]
  (r : Gal(Ω/E) →* GL N K) (c : Continuous r) (d : ∀ v, diagonal v ∈ span K (.range (r · |>.1)))
  {P : _ → K[X]} (h₁ : ∀ᶠ y in mostFrobenii E, (P y).aeval (r y.frob).1 = 0 ∧
  (P y).IsMonicOfDegree n) (Q : GL N k) κ (he : FreeInts e) (l : ∀ i, e i ∈ Set.range κ) (t : ∀ h :
  MvPolynomial _ k, (∀ᶠ g in nhds 1, h.aeval (Q.1 * (r g).1.map (algebraMap ..)).uncurry = 0) →
  h.aeval (diagonal (T ∘ κ) * Q.1.map LaurentPolynomial.C).uncurry = 0) : card N =
  n ∧ ∀ᶠ y in mostFrobenii E, (r y.frob).1.charpoly = P y := by
  delta uncurry at t
  let φ := (MulSemiringAction.toAlgHom K (Matrix N ..) (toConjAct Q)).comp (ofId K k).mapMatrix
  have W {m g} {p : K[X]} (o : p ≠ 0) (e : p.aeval (r g).1 = 0) (h : p.natDegree < m) :
    powMinor (φ _) m = 0 := funext (minors_eq_zero_iff.2 ((·.restrict_scalars' K).mt (by
    exact not_linearIndependent_iff.2 ⟨_, funext (by simpa [aeval_eq_sum_range' h, sum_range]
      using! (congr(φ $e · ·))), ⟨_, h⟩, by simpa⟩)))
  have : e.Injective := fun i j h ↦ Finsupp.basisSingleOne.injective (by apply he 1 <;> simp [*])
  have Z {m} x h a := t (powMinor (mvPolynomialX N N k * (Q⁻¹ * Units.map φ (r x)).1.map C) m a)
    (.mono ((map_mul_right_nhds_one x).le ((isClosed_eq (f := fun g ↦ powMinor (φ (r g)) m) (by
    simp [φ]; fun_prop [flip]) continuous_zero).closure_eq.subst h))
    (by simp_all [φ, Matrix.map_mul]))
  simp [-diagonal_mul, -Units.coe_map, ← Matrix.map_mul] at Z
  have H x := Z x (univ_mem' (dense_of_mostFrobenii (h₁.mono fun g h ↦
    W h.2.ne_zero h.1 congr($(h.2.1) + 1).le)))
  choose l L using l
  choose c hc using fun j ↦ ((det_vandermonde_eq_zero_iff.1 (by simpa [det_classical, diagonal_pow,
    flip_def, uncurry] using! (H 1 (Function.diag ∘ cons j l)))).elim (by
    simp [T, forall_fin_succ, AddMonoidAlgebra.single_inj]; grind) : ∃ i, e i = κ j)
  obtain ⟨rfl, hs⟩ := funext hc, (⟨l ·, by grind⟩ : Surjective c)
  have hN := card_of_bijective ⟨fun a b h ↦ by_contra fun o ↦ by simpa using ((congrFun₂ Q.3 a
    a).symm.trans (sum_eq_zero fun t _ ↦ by apply ((span_induction (p := fun x _ ↦ φ x a b = 0 ∧
    φ x a a = φ x b b) (by simpa using (H ·⁻¹ |> he.inv_scalar_on_blocks hs .refl |>.2 h o)) _ _ _
    (d (Pi.single t 1))).elim
    (by simp [φ, mul_apply, diagonal, apply_ite]; grind)) <;> simp +contextual)), hs⟩
  use by simp [*], h₁.mp fun V a ⟨x, b⟩ ↦ ⟨_, sdiff_le, a.sdiff (by simp), Set.not_subset.1
    (mem_nhds_iff.2 ⟨V, ·, a, b⟩ |> Z x |> he.inv_scalar_on_blocks hs (by simp) |>.1.false),
    .of_forall fun _ _ _
    _ _ _ g h ↦ (sub_eq_zero.1 (by_contra (g.2 <| subset_closure <| W · (by simp [*,
    aeval_self_charpoly]) (h.2.natDegree_sub_lt NeZero.out ⟨by simp [*], charpoly_monic _⟩)))).symm⟩

end

variable {E K₀ ℓ} [Field E] [EmbeddedNumberField E] [Field K₀] [NumberField K₀] [ThePrime ℓ]

open Polynomial Units Fintype Matrix Metric Filter Submodule

/-- Base change ω ∘ N to E of an algebraic Hecke character ω of K₀; its exponent at an embedding
σ of E is that of ω at σ|K₀. -/
noncomputable def AlgHeckeChar.baseChange [Algebra K₀ E] (ω : AlgHeckeChar K₀) : AlgHeckeChar E :=
  ⟨(ω.1.1.comp (Units.map (adeleNorm ..)), .ofAdd (ω.1.2.toAdd <| ·.comp (algebraMap ..))),
  ω.2.1.preimage_of_continuous, fun x ↦ by
  simp [map_adeleNorm_principalIdele, ω.2.2]
  convert ← prod_fiberwise (RingHom.comp · (algebraMap ..)) _ with s
  let := s.toAlgebra
  erw [Algebra.norm_eq_prod_embeddings, ← Finset.prod_zpow]
  apply prod_equiv (.mk (⟨_, RingHom.congr_fun ·.2⟩) (⟨_, ·.comp_algebraMap⟩)); aesop⟩

@[fun_prop] lemma continuous_cycCharIn : Continuous (cycCharIn (Γ := Gal(Ω/E)) (PadicAlgCl ℓ) Ω
  ℓ) := (continuous_algebraMap ..).units_map.comp (continuous_cycChar ℓ)

/-- Twisting by an algebraic Hecke character ω of E of type n: for continuous ρ, some continuous
ρ' inherits `SphericalClause` at each w where ω is unramified and n = d at the embeddings
inducing w; jumps shift by −n, eigenvalues t_j c^(−j) become t_j, c = ω(ϖ_w). -/
lemma exists_twist_algHeckeChar [PadicIso ℓ] [CMType E] (ω : AlgHeckeChar E) (d : ℕ) {ρ :
  PadicRep _ ℓ} (hρ : Continuous ρ.rep) : ∃ ρ' : PadicRep _ ℓ, Continuous ρ'.rep ∧ ∀ w,
  (∀ σ, inducedPrime σ = w → ω.1.2.toAdd σ = d) → CharUnramifiedAt ω.1.1 w → let c :=
    (ω.1.1 (locIdele w (uniformizer w))).1; ∀ {R J q a t}, SphericalClause ρ.rep R J w
    (heckePoly q a fun j ↦ ιℓ (t j * c⁻¹ ^ j)) → SphericalClause ρ'.rep R (fun τ ↦
    (J τ).map (· + -ω.1.2.toAdd τ)) w ((heckePoly q a t).map ιℓ) := by
  let θ := ω / show IsHeckeOfType 1 _ by simp [IsHeckeOfType, isOpen_iff_nhds].toAlgebraic (m :=
    d) (by tauto)
  let ν := cycCharIn _ Ω ℓ ^ d * θ.avatar
  use ⟨twistByChar ν ρ.rep⟩, .of_coeHom_comp (.smul (by fun_prop) (by fun_prop))
  intro w hd hω c R J q a t h A hA
  have ⟨x, b, p⟩ := show heckeCoeff θ.1.1 ∅ w = w.q ^ d * c by simp [heckeCoeff, θ, ← two_mul,
    _root_.zpow_mul, ← Complex.ofReal_pow, field] ▸ (avatarCompatAt_of_type_eq_zero θ
    (by aesop)).sphericalClause_of_unramified (fun _ ↦ by aesop) hA
  refine (local_clauses_twist A (μ := ν) (by tauto)).2.elim fun T ⟨U, V⟩ ↦ (h hA).imp (T · ⟨by
    simpa +contextual [ν, cycChar_of_mem_inertiaGroup (A := A)] using x.1, x.2.tate_twist d ?_⟩)
    (.imp (U · fun l γ τ t u ↦ (jump_twist_cyclotomicGp (-d) ?_).subst
    (.trans (by simp [Multiset.count_singleton, θ, IsHeckeOfType.toAlgebraic, ← eq_sub_iff_add_eq])
    (b t _))) fun h s hs ↦ V (c := ιℓ c) ((h s hs).of_dvd ⟨C _,
    by simp +contextual [Polynomial.ext_iff, c, apply_ite, pow_sub₀, field]⟩) (.of_dvd ⟨fun l ↦ by
    obtain := congr(algebraMap _ (PadicAlgCl ℓ) $(hs.cycChar_eq ℓ l)).symm, (p s hs).1
    simp_all [Matrix.algebraMap_eq_diagonal, ν, Matrix.diagonal_pow, funext_iff],
    @fun l h k hk ↦ ((p s hs).2 hk).elim fun o q ↦ (And.intro · ?_) (o.tate_twist d ?_)⟩
    ((C_mul_dvd (a := ↑w.q ^ d) (by simp)).2 dvd_rfl)))
  rotate_right 2
  rw [C_mul', eval₂_smul, ← q, eq_comm, linearFrob_twist_cyclotomicGp ‹_› hk d]
  simp [hk.eq_pow_of_isFrob (by rwa [← map_inv, l.isFrob_iff]), ↓eval₂_sub, ↓eval₂_C, pow_mul,
    Algebra.smul_def, mul_sub]
  all_goals simp [ν, PadicPlaceEmbedding.cyclotomicGp_eq_cycChar, mul_smul, ← map_pow,
    ← Units.smul_def]

attribute [local simp] tendstoUniformly_iff trace_blockDiagonal' Finset.mul_sum

/-- Suppose that for each τ some continuous ρ_τ is, along the filter F of places w, unramified
or crystalline, with J(τ) occurring among its jumps at τ and P_w killing geometric
Frobenius. Then one continuous r, whose image spans all diagonal matrices, does this for all
τ. -/
lemma exists_rep_span_diagonal {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E} [Field E] [EmbeddedNumberField E]
  (F : Filter (FinPlace E)) J (P : FinPlace E → (PadicAlgCl ℓ)[X]) (h : ∀ τ, ∃ ρ : PadicRep Gal(Ω/E)
  ℓ, Continuous ρ.rep ∧ ∀ᶠ w in F, SphericalClause ρ.rep OccursIn (Set.indicator {τ} J) w (P w)) :
  ∃ b, ∃ r : GalRep ℓ E (Fin b), Continuous r ∧ (∀ v, diagonal v ∈ span (PadicAlgCl ℓ)
  (.range fun g ↦ (r g).1)) ∧ ∀ᶠ w in F, SphericalClause r OccursIn J w (P w) := by
  choose ρ hρ H using h
  choose σ n t using exists_rep_of_pseudo fun _ ↦
    (· (.toHomUnits (.comp blockDiagonalAlgHom.1.1 (.pi ((Units.coeHom _).comp <| ρ · |>.rep)))))
  choose b d _ s f j u a using exists_wedderburn _ (.id _) n.hasSemiprimeSpan
  let f' :=
    (reindexAlgEquiv _ (PadicAlgCl ℓ) (@finSigmaFinEquiv _ d)).toAlgHom.comp blockDiagonalAlgHom
  have ht i : (f' (piMatrixUnit i)).trace = 1 := by
    simp_all [f', -coe_reindexAlgEquiv, Fintype.sum_eq_single i]
  choose B C e hB using exists_piMat_retract f f'
    (by simp_all [trace_of_idempotent, isIdempotentElem_map_piMatrixUnit]; grind)
  simp [trace] at ht a
  have := n.continuous_of_trace (by simp [t]; fun_prop)
  refine ⟨∑ i, d i, .toHomUnits (.comp f' s), .of_coeHom_comp (.congr (by fun_prop) (congr(C * $(a ·
    ▸ hB _)).trans (by simp [← C.mul_assoc, e]))), fun v ↦ (f'.toLinearMap.map_span_le ..).2 (by
    aesop) ⟨fun i ↦ diagonal (v <| finSigmaFinEquiv ⟨i, ·⟩), u.ge ⟨⟩, by aesop⟩,
    .mono (.all H) fun _ H A hA ↦ ?_⟩
  choose U K z using local_clauses_of_trace_limit this n OccursIn (pure ()) 1 _ _ (by simpa)
    (by grind [SphericalClause]) (fun _ ↦ (H · hA |>.2.1)) (.inl inferInstance) (by simp [t])
    fun τ _ _ _ h _ a _ ↦ h () τ (by aesop) (by simp_all [Tendsto, ← Nat.cast_sum])
  refine (local_clauses_of_retract (φ := .id _) 1 1 (by simp) (by simp) .id univ_mem (by simp [← hB,
    a]) e).elim fun _ y ↦ ⟨by aesop (add simp isGoodAt_iff), fun l _ _ t ↦ (mt ?_ ∘ K t ·),
    fun s i ↦ y.2 s ⟨⟩ (z .refl (fun _ τ ↦ ⟨.refl, (H τ hA).2.2 s i⟩) (by simp [t]))⟩
  simpa [jump_eq_zero_iff] using fun h g hg ↦ g.ext fun w ↦ by
    simpa [-mulVec_single, intertwiner_mul_piMatrixUnit, mul_vecMulVec, vecMulVec_mul,
      vecMulVec_mulVec, ← map_mul, ht, ← Finset.sum_mul, ← Pi.single_mul, ← sum_mulVec, ← map_sum,
      sum_piMatrixUnit, hodgeTateMaps.pull] using congr(∑ i, ∑ c, ∑ x, $(h _ (hodgeTateMaps.pull
      (intertwiner f f' fun _ ↦ vecMulVec (f (piMatrixUnit i 0 c) *ᵥ w) (Pi.single x 1)).toLin'
      (by simp [← a, mul_intertwiner]) ⟨g, hg⟩).2) (f' (piMatrixUnit i c) *ᵥ Pi.single x 1))
