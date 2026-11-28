/- GID: D5/S3/Zeros/GRH/Lib/SiegelWeil/SingularForms/AdaptedHom
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/SiegelWeil/SingularForms/AdaptedHom
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.SiegelWeil.SingularForms.AdaptedHom. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/SiegelWeil/SingularForms/AdaptedHom.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.SiegelWeil.Mass.TorusMajorant
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.PairSplitting
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Witt's extension theorem for hermitian forms, unimodular lattices, and the Iwasawa
decomposition. Over fields the result is proved in full, by quasi-reflections. Over the integral
finite adeles it is proved by a polar decomposition, for primitive frames of the identity form over
a CM field containing the roots of unity of order 5040. Source: U. A. First, Witt's extension
theorem for quadratic spaces over semiperfect rings, J. Pure Appl. Algebra 219 (2015), Cor. 4.9,
4.11 (fields: Dieudonné, La géométrie des groupes classiques, 1955; lattices: Jacobowitz, Amer. J.
Math. 84 (1962)).

Part of: Singular forms are governed by their coefficients at unimodular indices (known result; see
Lib.SiegelWeil.SingularForms.SingularForms).

This file: Adelic Iwasawa decomposition for unitary parabolics; centre of radical and Fourier
coefficients. Fourier coefficients of automorphic functions along centre of a radical: basic laws,
inversion. Radical of a line stabiliser: modulus on hermitian matrices, cocompact rational points.
Adapted splittings pass to Hom spaces; slices there written in Kronecker frames. -/

noncomputable section

namespace Space.Splitting

open Matrix WeilData ComplexOrder MatMul G MeasureTheory QuotientAddGroup IsDualFamily
variable {E : Type*} [Field E] [CMType E] [WeilData E] {n n₀ p} [Fintype n] [Fintype n₀] [Fintype p]
  {s s₀} {W : Space E n s} {W₀ : Space E n₀ s₀} (H : W.Splitting W₀ p)

/-- For an adelic p×p matrix M, the element 1 + k(M − M*)k*ε of the centre of the unipotent
radical of the stabiliser of the isotropic frame k. -/
def radicalCentre := AddChar.mk (H.radicalElt 0 <| -toAdele (j * 2 : E) • ·)
  (ext_mat (by simp [radicalElt])) (by simp [radicalElt_mul])

@[simp] lemma mat_radicalCentre M : (H.radicalCentre M).mat = 1 + H.kAdelic * (M - Mᴴ) *
  H.lCoord := by simp [radicalCentre, radicalElt, smul_smul, ← map_mul]; abel

lemma mul_radicalCentre {g c} (h : H.ActsOnFrame g c) M : g * H.radicalCentre M = H.radicalCentre
  (c * M * cᴴ) * g := ext_mat (have := congr(($g.mat_preserves_stdForm * H.kAdelic)ᴴ); by simp_all
    [← g.mat.mul_assoc, lCoord, -coord_mul_frame_mul])

@[simp] lemma radicalCentre_mem : ∀ M ∈ ratMatrices .., H.radicalCentre M ∈ W.Γ
  | _, ⟨a, rfl⟩ => by simpa using! H.radicalElt_mem_Gamma 0 ⟨-(j * 2 : E) • a, by aesop⟩

@[fun_prop] lemma continuous_radicalCentre :
  Continuous H.radicalCentre := by rw [AddChar.coe_mk]; fun_prop

/-- The Fourier coefficient at T of a function D at g: the mean of ψ(tr TM)·D(z(M)g) over adelic
matrices M modulo rational ones, z = `Space.Splitting.radicalCentre`. -/
def centreCoeff (T : Matrix ..) (D : _ → ℂ) g := quotMean (ratMatrices ..) fun M ↦
  stdAddChar E (T.map toAdele * M).trace * D (H.radicalCentre M * g)

omit [WeilData E] in
lemma iwasawa_of_witt {wt : p → ℕ} {S} [CommRing S] [StarRing S] {A : Matrix n n S} {P : Set _} {C :
  Set (U A)} (f : _ →+* S) u (hP : ∀ {X : Matrix n p S}, HasLeftInv X → ∃ b ∈ parabolic (R := S) wt,
  P (X * b.1)) (hW : ∀ {X Y}, P X → P Y → Xᴴ * A * X = 0 → Yᴴ * A * Y = 0 → ∃ κ ∈ C, κ.1.1 * X =
  Y) (hA : H.lCoord.map f = (H.kAdelic.map f)ᴴ * A := by simp [← ext_iff, lCoord, stdForm,
  signMatrix]) : ∃ κ ∈ C, ∃ b ∈ parabolic wt, (u * κ).1.1 * H.kAdelic.map f =
  H.kAdelic.map f * b.1 := by choose b _ p using (fun g : U A ↦ @hP (g⁻¹.1.1 * H.kAdelic.map f)
  ⟨H.kCoord.map f * g.1.1, by simp [← Matrix.map_mul]⟩); refine ((hW (p 1) (p
  u) ?_ ?_).imp fun κ ⟨c, e⟩ ↦ ⟨c, b u * (b 1)⁻¹, by bound, by simpa using! congr(u.1.1 * $e * (b
  1).2)⟩) <;> rw [gram_mul, U.gram_invariant, ← hA, ← Matrix.map_mul] <;> simp

/-- Iwasawa decomposition: for g in G(W) there are κ in K_∞K₀ and b in GL_p(𝔸), block upper
triangular for the ordering wt, with gκk = kb for the isotropic frame k, and gκ a unipotent
element times the Levi element of (b, u) for some u. -/
lemma iwasawa g (wt : p → ℕ := 0) : ∃ κ ∈ maxCompact E s, ∃ b, b.1.BlockTriangular wt ∧
    H.ActsOnFrame (g * κ) b.1 ∧ ∃ c z u, g * κ = H.radicalElt c z * H.levi (b, u) := by
  choose a _ b _ _ using fun w ↦ H.iwasawa_of_witt (evalInf w) (g.1 w) (exists_orthonormal_mul wt)
    fun {A B} (_ : Aᴴ * A = 1) _ _
    _ ↦ let F (x : Matrix n p ℂ) := x.fromCols (signMatrix s * x); by refine ((witt ⟨.I, ?_⟩ ?_
      IsHermInvolution.isUnit ⟨(F A)ᴴ, ?_⟩ ⟨(F B)ᴴ, ?_⟩ ?_).elim fun (g : USign s) (e : _ * F A =
      F B) ↦ (exists_polar g).elim fun κ ⟨z, p@⟨(_ : _ = _), _⟩, _⟩ ↦ have := congr($g.prop * F A)
      ⟨κ, κ.2, mul_right_injective_of_inv _ _ ((p.add .one).isUnit.unit * κ⁻¹).4 ?_⟩) <;> simp_all
             [F, fromCols_ext_iff, ← (signMatrix s).mul_assoc (signMatrix s), @eq_comm _ _ B,
      ← maxCompactU.coe_inv, add_comm]
  refine (H.iwasawa_of_witt (.snd ..) g.2 (isValuationPair_Ohat.exists_isPrimitiveMatrix_mul · wt)
    (fun _ _ ↦ witt_Ô · ·
    (by aesop))).elim fun c ⟨_, d, _, _⟩ ↦ ⟨(a, c), by tauto, mkAdelicGL (b, d), by aesop_cat, ?e,
    (H.exists_eq_radicalElt_mul_levi ?e).imp (by simp [↓Units.val_inj]; tauto)⟩
  apply matrix_ext_𝔸 <;> simpa only [Matrix.map_mul]

variable {E : _} [Field E] [CMType E] [WeilData E] {n p n₀ : _} [Fintype n] [Fintype p] [Fintype n₀]
  {s : _} (W : Space E n s) (D : _ → ℂ)

/-- D is a continuous function on the adelic unitary group of W that is left invariant under the
rational points. -/
def _root_.IsAutFunction := Continuous D ∧ W.Γ.FixesLeft D

variable {W D} {s₀ : _} {W₀ : Space E n₀ s₀} (H : W.Splitting W₀ p) (hD : IsAutFunction W D) {T}
include hD

attribute [local simp] mul_assoc centreCoeff AddChar.map_add_eq_mul

lemma isContPeriodic_radicalCentre g : IsContPeriodic (ratMatrices ..) (D <|
  H.radicalCentre · * g) := ⟨hD.rec (by fun_prop), by simp_all [hD.2]⟩

seal stdAddChar

@[fun_prop] lemma continuous_centreCoeff : Continuous (H.centreCoeff T D) := .congr
  (continuous_parametric_integral_of_continuous ((isQuotientMap_mk _).continuous_lift_prod_right
  (hD.rec (by simp [(isContPeriodic_mul (H.isContPeriodic_radicalCentre hD _)
  T).apply_out_mk]; fun_prop))) isCompact_univ) fun _ ↦ setIntegral_univ

lemma centreCoeff_radicalCentre_mul M g : stdAddChar E (T.map toAdele * M).trace * H.centreCoeff T D
  (H.radicalCentre M * g) = H.centreCoeff T D g := by
  simp [← mul_quotMean_translate (H.isContPeriodic_radicalCentre hD g) T M]

lemma centreCoeff_rat_mul T {γ} (hγ : γ ∈ W.Γ) c (h : H.ActsOnFrame γ (c.map toAdele)) g :
  H.centreCoeff T D (γ * g) =
  H.centreCoeff (cᴴ * T * c) D g := h.isUnit.rec fun a e ↦ .trans (quotMean_comp _
  (.comp (.mulLeft ↑a) (.mulRight aᴴ)) (isContPeriodic_mul (H.isContPeriodic_radicalCentre hD _) T)
  (by simp_all [ratMatrices, ← Matrix.map_mul]) (⟨a.2 * · * aᴴ⁻¹, by simp⟩)).symm (congrArg _ (by
  simp [← hD.2 _ hγ (_ * g), ← mul_assoc γ, H.mul_radicalCentre h, (_ᴴ.map _).trace_mul_comm, e]))

/-- For automorphic D, D' on the group of W, F(g) = D(gY) − c·D'(g) is automorphic, and along
every splitting H its Fourier coefficient at T and g is that of D at gY minus c times that
of D' at g. -/
lemma centreCoeff_sub {D'} (h' : IsAutFunction W D') c Y : let F := (D <| · * Y) - c •
    D'; IsAutFunction W F ∧ ∀ (H : W.Splitting W₀ p) T g, H.centreCoeff T F g = H.centreCoeff T D
    (g * Y) - c * H.centreCoeff T D' g := ⟨⟨hD.rec (h'.rec (by fun_prop)), by simp_all [hD.2,
  h'.2]⟩, by simp_intro .. [mul_sub, ← quotMean_const_mul, mul_left_comm _ c]; refine
  integral_sub ?_ (.const_mul ?_ _) <;> exact (isDualFamily_ratMatrices.isContPeriodic_mul
  (isContPeriodic_radicalCentre _ ‹_› _) _).integrable_out⟩

end Space.Splitting

open MeasureTheory Measure WeilData MatMul Matrix Kronecker Space Splitting Equiv
variable {E} [Field E] [CMType E] [WeilData E] {n m} [Fintype n] [Fintype m] {s t}
  {V' : Space E m t} {V : Space E n s} (D : V'.Splitting V Unit)

instance : CompactSpace (maxCompact E t) := isCompact_maxCompact.compactSpace

lemma map_conjugate_selfAdjoint {a : GL Unit (𝔸 E)} μ [IsAddHaarMeasure μ] :
  μ.map (β := selfAdjoint _) (⟨_, .conjugate ·.2 a.1⟩) = ENNReal.ofReal (ideleAbs a.det)⁻¹ • μ := by
  have := prod.instIsAddHaarMeasure μ μ; ext
  rw [← (ENNReal.pow_right_strictMono two_ne_zero).injective.eq_iff, sq, ← prod_prod, map_prod_map,
    map_haar_eq_smul_of_semiconj (μ.prod μ) (.mk ⟨⟨fun (p, q) ↦
    toAdele (2⁻¹ : E) • (toAdele (j⁻¹ : E) • q + p), fun z ↦ (⟨_, .add_star_self z⟩,
    ⟨_, .add_star_self (toAdele (j : E) • z)⟩), ?_, ?_⟩, ?_⟩) ?_ (volume_map_mul_mul_adele
    _ (star a))] <;> first | fun_prop | (repeat intro); simp [Subtype.ext_iff, sq, mul_mul_mul_comm
    _ (μ _), Prod.ext_iff] <;> and_intros <;> match_scalars <;> grind

/-- For a splitting of V' over V along an isotropic line, the radical is cocompact modulo its
rational points: some compact set K has n(y,z)·n(c,b) ∈ K for every n(c,b) and a suitable
rational n(y,z), with n = `Space.Splitting.radicalElt`. -/
lemma exists_isCompact_rat_mul_radicalElt_mem : ∃ K, IsCompact K ∧ ∀ c b, ∃ y z,
  D.radicalElt y z ∈ V'.Γ ∧ D.radicalElt y z * D.radicalElt c b ∈ K := by
  obtain ⟨⟨_, c, H⟩, _, d, K⟩ := IsCovolOneLattice.exists_compact_cover (ratMatrices E n Unit),
    IsCovolOneLattice.exists_compact_cover (ratMatrices E Unit Unit)
  simpa [D.radicalElt_mul, add_assoc] using ⟨_, (c.prod d).image_auto ↿(D.radicalElt <|
    V.x⁻¹.1 * ·), fun x _ ↦ let ⟨_, ⟨y, rfl⟩, h⟩ := H (V.x.1 * x); ⟨_, (K _).imp fun _ ↦ .imp
    (D.radicalElt_mem_Gamma y) (⟨(_, _), ⟨h, ·⟩, congr(D.radicalElt $(by simp) _)⟩)⟩⟩

variable {E : _} [Field E] [CMType E] {n : _} {n' r} (p) [Fintype n] [Fintype n']
  [Fintype r] [Fintype p] {s : _} {s'} {t : _} {W : Space E n s} {W' : Space E n' s'} (A :
  W'.Splitting W p) (T : Space E r t)

/-- The invertible adelic matrix (x⁻¹)ᴴ ⊗ 1, a Kronecker product of the adjoint of the inverse
adelic frame x of T with the p×p identity. -/
def adaptedHomBasis := kroneckerGL (n := p) (star T.x⁻¹) 1

variable {p} {M : Matrix n' n (𝔸 E)}

attribute [local simp] adaptedHomBasis kroneckerGL star_eq_conjTranspose stdForm diagonal_apply
  homSource_lAdelic homSource_kAdelic IsOrthoIntegral

attribute [local simp ←] conjTranspose_mul

lemma frameAt_homSource : (A.homSource T).frameAt 1 (adaptedHomBasis p T) =
  ((1 ⊗ₖ A.kCoordᵀ).fromCols (stdForm E t ⊗ₖ A.lCoordᵀ)).fromCols
  (1 ⊗ₖ A.iCoordᵀ) := by simp [Splitting.frameAt, homSource_iAdelic, mul_assoc, dualFrame]

lemma sourceTerm_eq_adapted_mixedTerm [WeilData E] x : A.sourceTerm T x =
  (A.homSource T).mixedTerm ((adaptedHomBasis p T)⁻¹.1ᴴ *ᵥ matToVec x) := by
  simp [mixedTerm, sourceTerm, kronecker_mulVec_eq_matToVec]

omit [Fintype n] [Fintype p] in
lemma IsOrthoIntegral.kronecker {B : Matrix r p _} : IsOrthoIntegral M → IsOrthoIntegral B →
  IsOrthoIntegral (M ⊗ₖ Bᴴᵀ) := by
  simp_all [mul_mem, map_kronecker, B.conjTranspose_map (evalInf _) (by tauto), star_mem_Ô]

lemma isAdapted_homSource [h : IsBaseAdapted A] : (A.homSource T).IsAdapted 1
  (adaptedHomBasis p T) := .of_eq_submatrix_mul (.mul (.of_stdForm (s' ·.2)) (.kronecker .one h.1))
  ((prodSumDistrib ..).2 ∘ .map (prodSumDistrib ..).2 id) (.of_stdForm (1 ⊕ᵥ (t ·.1) ⊕ᵥ (s ·.2)))
  (Matrix.ext (by simp [↓frameAt_homSource, kCoord, lCoord, iCoord, ← Pi.one_def]; grind))
