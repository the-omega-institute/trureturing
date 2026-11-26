import GRH.Lib.Weil.MixedModel.HyperbolicSpace
import GRH.Lib.Weil.MixedModel.NameWeilAction
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: Splittings along isotropic subspaces, Levi and unipotent radical of the parabolic,
adapted points. Heisenberg law in split coordinates; real vacuum becomes the Gaussian of the mixed
model. Finite vacuum and Schwartz-Bruhat data in the mixed model: partial Fourier transform. Zero
term and mixed Schrödinger model; theta expansion; vacuum is Gaussian times lattice indicator. -/

noncomputable section

section

attribute [-simp] map_inv₀ smul_mul'

open NumberField Matrix WeilData Fintype G MatMul Function

attribute [local simp] Space.ratMap Space.vecAtPoint conjTranspose_nonsing_inv RingHom.map_mulVec
  comp_def

attribute [-instance] instCoeTOfCoeHTCT

attribute [-simp] Algebra.smul_mul_assoc inv_mul_cancel inv_mul_cancel₀ mul_zero zero_mul

section

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n n₁ : Type*} [Fintype n] {s : n → _}
  [Fintype n₁] {s₁ : n₁ → ℤˣ} (g : G E s)

lemma G.mat_preserves_stdForm : g.matᴴ * stdForm E s * g.mat = stdForm E s := g.toUnitary.2

omit [IsCMField E] [Fintype n₁] in
@[simp] lemma stdForm_mul_stdForm_mul (a : Matrix n n₁ (𝔸 E)) : stdForm E s * (stdForm E s * a) =
  a := by simp [← Matrix.mul_assoc]

lemma G.mat_inv : g⁻¹.mat = stdForm E s * g.matᴴ * stdForm E s := U.coe_inv (by simp) g.toUnitary

end

variable {E : Type*} [Field E] [CMType E] {n n₁ : Type*} [Fintype n] {s : n → _} [Fintype n₁]
  {s₁ : n₁ → ℤˣ} (g : G E s) {V₁ : Space E n₁ s₁} (V : Space E n s)

lemma Space.ratMap_mulVec_vecAtPoint i y : V.ratMap V₁ i *ᵥ V₁.vecAtPoint y =
  V.vecAtPoint (i *ᵥ y) := by simp

lemma Space.gram_at_point_eq_map {a b} (A : Matrix n a E) (B : Matrix n b E) :
  (V.x⁻¹.1 * A.map toAdele)ᴴ *
  stdForm E s * (V.x⁻¹.1 * B.map toAdele) = (Aᴴ * V.J * B).map toAdele := by simp [map_J]

seal dotProduct

variable [WeilData E] {n₀ p q : Type*} [Fintype n₀] [Fintype p] {s₀ : n₀ → ℤˣ} (V₀ : Space E n₀ s₀)

/-- A decomposition V = (lE^p ⊕ kE^p) ⊥ iV₀ over E: isotropic frames l, k with l*Jk = 1, an
isometry i from V₀ orthogonal to both, and rk V = rk V₀ + 2p. -/
structure Space.Splitting p [Fintype p] where
  (k l : Matrix n p E) i : Matrix n _ E
  gram_kk : kᴴ * V.J * k = 0
  gram_ll : lᴴ * V.J * l = 0
  gram_lk : lᴴ * V.J * k = 1
  gram_ii : iᴴ * V.J * i = V₀.J
  gram_ik : iᴴ * V.J * k = 0
  gram_il : iᴴ * V.J * l = 0
  protected card_eq : card n = card n₀ + 2 * card p

variable (p) in
/-- The orthogonal sum of hyperbolic space of rank 2p and V₀. -/
def hypSum := (hypSpace E p).sum V₀

variable {V V₀ g} (D : V.Splitting V₀ p) {a : Matrix p p (𝔸 E)} (c : Matrix n₀ p (𝔸 E))
  (b : Matrix p p (𝔸 E))

/-- The splitting of V whose l, k, i are the three column blocks of a matrix M, when M*JM is the
Gram matrix of hyperbolic space plus V₀ and ranks agree. -/
def splittingOfGram (M : Matrix n _ E) (h : Mᴴ * V.J * M = (hypSum p V₀).J)
    (c : card n = card n₀ + 2 * card p) : V.Splitting V₀ p := by
  use M.toCols₁.toCols₂, M.toCols₁.toCols₁, M.toCols₂ <;> ext <;> apply congrFun₂ h

namespace Space.Splitting

/-- For a splitting of V, the adelic n×p matrix x⁻¹k, x the adelic frame of V: the isotropic
frame k in standard coordinates. -/
def kAdelic := V.x⁻¹.1 * D.k.map toAdele

/-- For a splitting of V, the adelic n×p matrix x⁻¹l, x the adelic frame of V: the isotropic
frame l in standard coordinates. -/
def lAdelic := V.x⁻¹.1 * D.l.map toAdele

/-- For a splitting of V over V₀, the adelic matrix ι = x⁻¹ i x₀, with x, x₀ the adelic frames:
the embedding i in standard coordinates. -/
def iAdelic := V.ratMap V₀ D.i

section

omit [WeilData E]

lemma gram_kl : D.kᴴ * V.J * D.l = 1 := by simpa [conjTranspose_J] using congr($D.gram_lkᴴ)

lemma gram_ki : D.kᴴ * V.J * D.i = 0 := by simpa [conjTranspose_J] using congr($D.gram_ikᴴ)

/-- The splitting of V obtained from a given one by exchanging the two isotropic frames k and l
and keeping the embedding i. -/
def symm := mk _ _ _ D.gram_ll D.gram_kk D.gram_kl D.gram_ii D.gram_il D.gram_ik D.card_eq

lemma gram_li : D.lᴴ * V.J * D.i = 0 := D.symm.gram_ki

end

attribute [simp high] gram_kk gram_ll gram_lk gram_kl gram_ii gram_ik gram_il gram_ki gram_li

/-- For a splitting, the adelic p×n matrix l*ε (l the adelic frame, ε the standard form), which
sends la + ιw + kb to b. -/
def kCoord := D.lAdelicᴴ * stdForm E s

/-- For a splitting, the adjoint ε₀ ι* ε of the adelic embedding ι for the standard forms, which
sends la + ιw + kb to w. -/
def iCoord := stdForm E s₀ * D.iAdelicᴴ * stdForm E s

/-- For a splitting, the adelic p×n matrix k*ε (k the adelic frame, ε the standard form), which
sends la + ιw + kb to a. -/
def lCoord := D.kAdelicᴴ * stdForm E s

omit [WeilData E] in
/-- For a splitting, the three coordinate matrices along k, l and V₀ are dual to the adelic
frames k, l, ι: each times its own frame is the identity, and times either other frame is
zero. -/
@[simp] lemma coord_mul_frame : (D.kCoord * D.kAdelic = 1 ∧ D.kCoord * D.lAdelic = 0 ∧ D.kCoord *
  D.iAdelic = 0) ∧ (D.lCoord * D.kAdelic = 0 ∧ D.lCoord * D.lAdelic = 1 ∧ D.lCoord * D.iAdelic =
  0) ∧ D.iCoord * D.kAdelic = 0 ∧ D.iCoord * D.lAdelic = 0 ∧ D.iCoord * D.iAdelic = 1 := by
  simp [kCoord, lCoord, iCoord, kAdelic, lAdelic, iAdelic, ← V.gram_point]
  simp [← Matrix.mul_assoc, ← Matrix.map_mul, gram_point]

omit [WeilData E] in
@[local simp] lemma conjTranspose_coord : D.kCoordᴴ = stdForm E s * D.lAdelic ∧
    D.lCoordᴴ = stdForm E s * D.kAdelic ∧ D.iCoordᴴ =
  stdForm E s * D.iAdelic * stdForm E s₀ := by simp [kCoord, iCoord, lCoord]

section

omit [WeilData E]

/-- For any matrix X, each coordinate matrix (along k, l, V₀) recovers X from its own frame
times X and kills the other frames times X. Also k*εX, l*εX, ι*εX are the l-coordinate, the
k-coordinate, and ε₀ times the V₀-coordinate of X. -/
@[simp] lemma coord_mul_frame_mul {m} : (∀ X : Matrix p m (𝔸 E), D.kCoord * (D.kAdelic * X) = X ∧
  D.iCoord * (D.kAdelic * X) = 0 ∧ D.lCoord * (D.kAdelic * X) = 0 ∧ D.kCoord * (D.lAdelic * X) = 0 ∧
  D.iCoord * (D.lAdelic * X) = 0 ∧ D.lCoord * (D.lAdelic * X) = X) ∧ (∀ X : Matrix n₀ m (𝔸 E),
  D.kCoord * (D.iAdelic * X) = 0 ∧ D.iCoord * (D.iAdelic * X) = X ∧ D.lCoord *
  (D.iAdelic * X) = 0) ∧ ∀ X : Matrix n m (𝔸 E), D.kAdelicᴴ * (stdForm E s * X) = D.lCoord * X ∧
  D.lAdelicᴴ * (stdForm E s * X) = D.kCoord * X ∧ D.iAdelicᴴ * (stdForm E s * X) = stdForm E s₀ *
  (D.iCoord * X) := by simp [↓ ← Matrix.mul_assoc, ↓coord_mul_frame, kCoord, iCoord, lCoord]

lemma sum_frame_mul_coord_eq_one : D.kAdelic * D.kCoord + D.iAdelic * D.iCoord + D.lAdelic *
  D.lCoord = 1 := by simp +arith [D.card_eq,
  ← fromCols_mul_fromRows, ↓fromRows_mul_fromCols, mul_eq_one_comm_of_card_eq]

/-- g preserves the span of the isotropic frame k of D and acts on the frame by the matrix c:
gk = kc in adelic coordinates. -/
@[simp] abbrev ActsOnFrame (g : G E s) (c : Matrix p p (𝔸 E)) := g.mat * D.kAdelic = D.kAdelic * c

lemma lCoord_mul_mat {a : GL p _} (hk : D.ActsOnFrame g a.1) : D.lCoord * g.mat =
  a⁻¹.1ᴴ * D.lCoord := by simpa [*] using! congr(($g.mat_preserves_stdForm * D.kAdelic * a⁻¹.1)ᴴ)

lemma ActsOnFrame.isUnit (hk : D.ActsOnFrame g a) : IsUnit a :=
  .of_mul_eq_one_right (D.kCoord * g.mat⁻¹ * D.kAdelic) (by simp [← hk, mat])

end

/-- The homomorphism GL_p(𝔸) × G(V₀) → G(V) sending (m, g₀) to the element with k ↦ km, ι ↦ ιg₀,
l ↦ l m*⁻¹. -/
@[local simp] def levi : GL p (𝔸 E) × G E s₀ →* G E s := .mk' (fun x ↦
  ofMat (D.kAdelic * x.1.1 * D.kCoord + D.iAdelic * x.2.mat * D.iCoord + D.lAdelic * x.1⁻¹.1ᴴ *
  D.lCoord) (by simp [← Matrix.mul_assoc]; simp [↓mat_preserves_stdForm,
  eq_sub_of_add_eq' D.sum_frame_mul_coord_eq_one])) fun _ _ ↦ ext_mat (by simp)

section

omit [WeilData E]

lemma levi_mul_lAdelic a g : (D.levi (a, g)).mat * D.lAdelic = D.lAdelic * a⁻¹.1ᴴ := by simp

lemma levi_mul_iAdelic a g : (D.levi (a, g)).mat * D.iAdelic = D.iAdelic * g.mat := by simp

/-- The Levi element of a splitting attached to a in GL_p(𝔸) and g in the group of V₀ sends the
adelic isotropic frame k to ka. -/
lemma levi_mul_kAdelic a g : D.ActsOnFrame (D.levi (a, g)) a.1 := by simp

end

/-- From splittings of V over V₀ (rank p) and V₀ over V₁ (rank q), the splitting of V over V₁
with frames (k, ik'), (l, il') and embedding ii'. -/
def comp [Fintype q] (D' : V₀.Splitting V₁ q) : V.Splitting V₁ (p ⊕ q) := by
  use D.k.fromCols (D.i * D'.k), D.l.fromCols (D.i * D'.l), D.i * D'.i <;>
  simp +arith [D.card_eq, D'.card_eq, ← Matrix.mul_assoc] <;> simp

lemma gram_eq_hypSum : let M := (D.l.fromCols D.k).fromCols D.i; Mᴴ * V.J * M =
    (hypSum p V₀).J := by aesop

/-- For adelic c (n₀×p) and hermitian b (p×p), the element of G with k ↦ k, ι ↦ ι + kc*ε₀, l ↦ l
− ιc − k(ȷ⁻¹b + ½c*ε₀c). -/
@[local simp] def radicalElt : G E s :=
  ofMat (1 - D.iAdelic * c * D.lCoord + D.kAdelic * (cᴴ * stdForm E s₀) * D.iCoord - D.kAdelic *
  toAdele (2⁻¹ : E) • (toAdele (j⁻¹ : E) • (b + bᴴ) + cᴴ * stdForm E s₀ * c) * D.lCoord) (by
  simp [↓coord_mul_frame_mul, iCoord, lCoord]; match_scalars <;> grind)

@[fun_prop] lemma continuous_radicalElt : Continuous fun q : _ × _ ↦ D.radicalElt q.1 q.2 := by
  simp [↓continuous_iff]; fun_prop

/-- The radical element n(c, b) of a splitting, for c an adelic n₀×p matrix and b a hermitian
adelic p×p matrix, fixes the adelic isotropic frame k. -/
lemma radicalElt_mul_kAdelic : D.ActsOnFrame (D.radicalElt c b) 1 := by simp

/-- The radical element n(c, b) of a splitting sends the adelic embedding ι of V₀ to ι + k c*
ε₀, where ε₀ is the standard form for the signs of V₀. -/
lemma radicalElt_mul_iAdelic : (D.radicalElt c b).mat * D.iAdelic =
  D.iAdelic + D.kAdelic * (cᴴ * stdForm E s₀) := by simp

@[local simp↓] lemma radicalElt_mul c' b' : D.radicalElt c b * D.radicalElt c' b' =
  D.radicalElt (c + c') (b + toAdele (j : E) • cᴴ *
  stdForm E s₀ * c' + b') := ext_mat (by simp; match_scalars <;> grind)

lemma radicalElt_inv : (D.radicalElt c b)⁻¹ = D.radicalElt (-c) (-b) :=
  inv_eq_of_mul_eq_one_right (ext_mat (by simp))

lemma levi_conj_radicalElt a g : D.levi (a, g) * D.radicalElt c b = D.radicalElt (g.mat * c * a.1ᴴ)
  (a.1 * b * a.1ᴴ) * D.levi (a, g) := ext_mat (by simp [mat, ofMat, ← U.form_mul_inv_eq]; abel)

lemma exists_levi_mul_radicalElt_eq : ∃ a b', D.levi (a, 1) * D.radicalElt c b' =
  D.radicalElt c b' * D.radicalElt c b * D.levi (a, 1) := by
  use ⟨1 + 1, toAdele (2⁻¹ : E) • 1, ?_, ?_⟩, toAdele (3⁻¹ : E) • b, ext_mat ?_ <;>
  simp [-coe_units_inv] <;> match_scalars <;> norm_num [mul_two, ← map_add, ← map_mul] <;> ring_nf

lemma radicalElt_zero_mul b' : D.radicalElt 0 b * D.radicalElt c b' =
  D.radicalElt c (b + b') := by simp

/-- If g in G satisfies gk = ka for some adelic p×p matrix a, then g is a unipotent element
`Space.Splitting.radicalElt` times an element of the Levi subgroup `Space.Splitting.levi`. -/
lemma exists_eq_radicalElt_mul_levi (hk : D.ActsOnFrame g a) : ∃ c b t g₀,
    g = D.radicalElt c b * D.levi (t, g₀) ∧ t.1 = a ∧ g₀.mat = D.iCoord * (g.mat * D.iAdelic) := by
  obtain ⟨⟨a, ⟨⟩⟩, e, k, l⟩ := hk.isUnit, congr($D.sum_frame_mul_coord_eq_one * g.mat).symm,
    congr($g.mat_preserves_stdForm * D.iAdelic), congr($g.mat_preserves_stdForm *
    D.lAdelic); simp [D.lCoord_mul_mat hk] at e
  generalize D.kCoord * g.mat = X, D.iCoord * g.mat = Y at e; simp [e, ← eq_sub_iff_add_eq'] at k l
  use -Y * D.lAdelic * a.1ᴴ, -toAdele (j : E) • X * D.lAdelic * a.1ᴴ, a,
    ofMat (Y * D.iAdelic) (by aesop), ext_mat (g.mat.mul_one ▸
    D.sum_frame_mul_coord_eq_one ▸ ?_) <;> simp [← Matrix.mul_assoc] <;> simp_all
  match_scalars <;> grind

/-- The law of a mixed Schrödinger model for maps T(x): 𝒮(V) → 𝒮(V₀), x in 𝔸^p: T(x)ϱ(la + ιw +
kb) = ψ(½ȷ b*(2x + a)) ϱ(w) T(x + a). -/
abbrev IsMixedLaw (T : _ → 𝒮 V →L[ℂ] 𝒮 V₀) := ∀ x y f, T x (V.ϱ y f) = (adelicHeis E 1).β
  (x + (x + D.lCoord *ᵥ y)) (D.kCoord *ᵥ y) • V₀.ϱ (D.iCoord *ᵥ y) (T (x + D.lCoord *ᵥ y) f)

variable (g : G E s) (t : GL p (𝔸 E))

/-- For g in G and t in GL_p(𝔸), the adelic matrix g⁻¹(l t*⁻¹, kt, ι) with three column blocks. -/
def frameAt := g⁻¹.mat * ((D.lAdelic * t⁻¹.1ᴴ).fromCols (D.kAdelic * t.1)).fromCols D.iAdelic

omit [WeilData E] in
lemma gram_frameAt : (D.frameAt g t)ᴴ * stdForm E s * D.frameAt g t =
  fromBlocks (fromBlocks 0 1 1 0) 0 0 (stdForm E s₀) := (U.gram_invariant ..).trans (by aesop)

/-- g in G is adapted to t in GL_p(𝔸): the matrix g⁻¹(l t*⁻¹, kt, ι) has orthonormal columns at
every infinite place and integral finite entries. -/
def IsAdapted := IsOrthoIntegral (D.frameAt g t)

/-- For a splitting of V with adelic frames l, k, ι and t in GL_p(𝔸), some g in G adapted to t
equals (l t*⁻¹, kt, ι)(x ⊕ 1) after a sign-matching reordering of its columns, x the point
of `hypSpace`. -/
lemma exists_isAdapted_and_frame_eq : ∃ g, D.IsAdapted g t ∧ ∃ e : _ ≃ n, s ∘ e = hypSigns p ⊕ᵥ s₀ ∧
  D.frameAt 1 t * fromBlocks (o := n₀) (hypSpace E p).x.1 0 0 1 = g.mat.submatrix id e :=
  let m := D.frameAt 1 t * (hypSpace E p).x.1.fromBlocks (o := n₀) 0 0 1
  have h : mᴴ * stdForm E s * m = stdForm E (hypSigns p ⊕ᵥ s₀) := by
    simp [m, ↓gram_mul, ↓gram_frameAt, ← stdForm_sum, ← (hypSpace ..).3]
  have e := equivOfCardEq (by simp +arith [D.card_eq])
  let M := m.map (evalInf Classical.ofNonempty)
  have H : Mᴴ * signMatrix s * M = signMatrix (hypSigns p ⊕ᵥ s₀) := by
    simpa [stdForm] using! congr(($h).map
             (evalInf Classical.ofNonempty))
  (sylvester_law_of_inertia (s := s) (t := (hypSigns p ⊕ᵥ s₀) ∘ e) (h := M.submatrix id e)
    (Matrix.ext fun i j ↦ (congrFun₂ H (e i) (e j)).trans (by
    simp [signMatrix, diagonal]))).elim fun τ _ ↦ let f := e.symm.trans τ
    let g := ofMat (m.reindex 1 f) (congr(($h).reindex f f).trans (by simp [stdForm]; grind))
    have h := by aesop
    ⟨g, .of_eq_submatrix_mul .one f (isOrthoIntegral_hypSpace.2.block_diag .one)
      (g.toUnitary.1.inv_mul ▸ .trans (by simp [frameAt]) congr(g⁻¹.mat * $(h.2) * _)), f, h⟩

attribute [local simp] kAdelic lAdelic iAdelic kCoord iCoord lCoord mem_Γ_iff_range

omit [WeilData E] in
lemma levi_mem_Γ a {g₀} : g₀ ∈ V₀.Γ → D.levi (.map toAdele a, g₀) ∈ V.Γ
  | ⟨_, h⟩ => h ▸ by simp [-coe_units_inv, mat_ratEmbed, ← map_inv, ← Matrix.mul_assoc]
                     simp [↓ ← map_J_inv, ← Matrix.map_mul, ← map_add, ← V.gram_point]

attribute [-simp] Matrix.one_apply coe_units_inv in
/-- The unipotent element `Space.Splitting.radicalElt` with parameters x₀⁻¹c and b, for c a matrix
over E, x₀ the adelic frame of V₀ and b a rational hermitian matrix, lies in the rational group Γ
of V. -/
lemma radicalElt_mem_Gamma (c : Matrix n₀ p E) {b} : b ∈ ratMatrices E p p →
  D.radicalElt (V₀.x⁻¹.1 * c.map toAdele) b ∈ V.Γ
  | ⟨_, h⟩ => by simp [← h, ↓ ← map_J]
                 simp [← Matrix.map_mul, ← map_add, ← map_sub, ← map_mul, coe_units_inv,
                   ← Matrix.map_one toAdele, ← V₀.gram_point]

omit [WeilData E] in
lemma kAdelic_mulVec_mem_ratVectors {b} : b ∈ _root_.ratVectors E p →
  D.kAdelic *ᵥ b ∈ V.ratVectors := .imp' D.k.mulVec (by aesop)

end Space.Splitting

end

namespace Space.Splitting

section

open NumberField Matrix Prod Complex Fintype ComplexOrder MeasureTheory Heisenberg Rep IsVacuum
variable {E : Type _} [Field E] [CMType E] [WeilData E]
  {n n₀ p : Type _} [Fintype n] [Fintype n₀] [Fintype p] {s : n → ℤˣ} {s₀ : n₀ → ℤˣ}
  {V : Space E n s} {V₀ : Space E n₀ s₀} {D : V.Splitting V₀ p} (L : 𝒮 V →L[ℂ] 𝒮 V₀)
  (A : Matrix n p (𝔸 E)) {T : (p → 𝔸 E) → 𝒮 V →L[ℂ] 𝒮 V₀} (hT : D.IsMixedLaw T) {g : G E s}
  {t : GL p (𝔸 E)} (h : D.IsAdapted g t)

/-- The archimedean part of an adelic matrix A as one complex matrix, block diagonal over the
infinite places, whose block at τ is the τ-component of A. -/
def realMatrix {E : Type _} [Field E] [NumberField E] {n p : Type _} (A : Matrix n p (𝔸 E)) :=
  (blockDiagonal (A.map <| evalInf ·)).submatrix swap swap

lemma realVec_realCoordSum x : realVec ((realCoordSum (realSigns_comp_split (E :=
  E) (@signs_comp_refl _ (s ⊕ᵥ s₀)))).equiv x) = realVec x.1 ⊕ᵥ realVec x.2 := by bound

attribute [local simp] blockDiagonal AddChar.map_add_eq_mul ω_ϱ sum_prod_type
  realVec_realCoordSum

omit [Fintype n] in
lemma realVec_realMatrix_mulVec y : realVec (realMatrix A *ᵥ y) = A *ᵥ realVec y := by
  ext <;> simp [realVec, realMatrix, mulVec_eq_sum, mul_assoc, fst_sum, snd_sum]

omit [WeilData E] [Fintype p] in
lemma realMatrix_orthonormal (h : IsOrthoIntegral A) : (realMatrix A)ᴴ * realMatrix A = 1 := by
  simp_all [realMatrix, ← ext_iff, mul_apply, IsOrthoIntegral]; aesop

/-- For a splitting of V over V₀, write y = la + ιw + kb and y' = la' + ιw' + kb'. Then β(y,y')
= ψ(½ȷ(a'*b + b'*a)) β₀(w,w'), with β₀ the bicharacter for the signs of V₀. -/
lemma beta_eq_coords y y' : (adelicHeis E s).β y y' =
  (adelicHeis E 1).β (D.kCoord *ᵥ y) (D.lCoord *ᵥ y') * (adelicHeis E 1).β (D.lCoord *ᵥ y)
  (D.kCoord *ᵥ y') * (adelicHeis E s₀).β (D.iCoord *ᵥ y) (D.iCoord *ᵥ y') := by
  rw [← one_mulVec y, ← D.sum_frame_mul_coord_eq_one]
  simp [star_mulVec_dotProduct, conjTranspose_coord, field, Matrix.mul_assoc, mul_add, adelicHeis]

lemma isMixedLaw_comp_rho (hk : ∀ b f, L (V.ϱ (D.kAdelic *ᵥ b) f) = L f) (hi : ∀ w f,
  L (V.ϱ (D.iAdelic *ᵥ w) f) =
  V₀.ϱ w (L f)) : D.IsMixedLaw fun x ↦ L ∘L V.ϱ (D.lAdelic *ᵥ x) := fun x y f ↦ by
  erw [← one_mulVec y, ← D.sum_frame_mul_coord_eq_one, ← hk (D.kCoord *ᵥ -y), ← hi]
  simp [D.beta_eq_coords, mulVec_neg, add_left, smul_smul]; abel

include hT h

/-- Let g be adapted to t, T obey `Space.Splitting.IsMixedLaw`, and u = ω(g)P^∞f, P^∞ the real
vacuum projection. For a real vector x = `realVec` a with Fock coordinates a, T(t*⁻¹x)u =
exp(−|a|²)·P^∞T(0)u. -/
lemma IsAdapted.omega_projReal_of_isMixedLaw a f : T (t.1⁻¹ᴴ *ᵥ realVec a) (V.ω g (V.projReal f)) =
    exp (-(star a ⬝ᵥ a)) • V₀.projReal (T 0 (V.ω g (V.projReal f))) := by
  have r := realMatrix_orthonormal _ h
  have o y : realVac (realMatrix (D.frameAt g t) *ᵥ y) =
    realVac y := by simp [realVac, star_mulVec_dotProduct, r]
  have k := (measurePreserving_equiv (realHeis 1) (realHeis 1) (φ :=
    {toLin'OfInv r (by simp +arith [D.card_eq, r, mul_eq_one_comm_of_card_eq]) with}) o).comp
    (realCoordSum (realSigns_comp_split (@signs_comp_refl _ (1 ⊕ᵥ s₀)))).measurePreserving_equiv
  have γ y := And.intro ((integral_add_right_eq_self _ y).trans (integral_gauss (A := scalar _ 2⁻¹)
    (by simp [IsAccretive, add_pos]) (y + y))) ((adelicSum E (n := p) 1).2 (y, 0) ⟨·, 0⟩)
  simp [realHeis, signMatrix, adelicHeis] at γ
  let N x := T (t.1⁻¹ᴴ *ᵥ realVec x) ∘L V.ω g
  have i x (M : _ →L[ℂ] 𝒮 V₀) : M (N x (V.projReal f)) = (-star x ⬝ᵥ x).exp • ∫ a,
    (realVac a ^ 2 * 2 ^ .card (InfinitePlace E × p)) • M (V₀.projReal (N a f)) ∂realMeasure _ := by
    erw [← integral_add_left_eq_self _ x, ← integral_smul, map_integrated_eq_integral _ (M ∘L _),
      ← (k.fubini ?i).2, ← ((realCoordSum (realSigns_comp_split (@signs_comp_refl _
      (hypSigns p)))).measurePreserving_equiv.fubini (k.fubini ?i).1.integral_prod_left).2]
    congr! with a; simp [o, toLin'OfInv, OrthogonalSum.vac_equiv]; simp [*, N,
      realVec_realMatrix_mulVec, frameAt, ← g.mat.mul_assoc, adelicHeis,
      ← G.mat_mul, star_mulVec_dotProduct, ← conjTranspose_mul, mul_add]
    simp_rw [smul_comm (_ * realVac _), mul_smul, integral_smul, projReal, integrated,
      map_integrated_eq_integral, smul_smul, integral_smul_const]
    convert congr((_ * (_ * $((γ (x + x + a)).1))) • _) <;>
      simp [realVac, sq, ← exp_add, ← integral_const_mul]; clear * -; grind
    exact vacVector.2.1.smul_bdd _ (by fun_prop) (by grw [(M ∘L _).le_opNorm]; aesop)
  erw [i a 1]; simpa [realVac, N] using (i 0 V₀.projReal).symm

seal adelicHeis in
/-- If g is adapted to t and T obeys `Space.Splitting.IsMixedLaw`, some bounded linear L between the
Fock spaces of V and V₀ has T(0)ω(g)(v ⊗ f) = Lv ⊗ T(0)ω(g)P^∞f for all v, f, P^∞ the real
vacuum projection. -/
lemma IsAdapted.exists_real_zeroTerm : ∃ L : _ →L[ℂ] _, ∀ v f,
    T 0 (V.ω g (V.integrated v f)) = V₀.integrated (L v) (T 0 (V.ω g (V.projReal f))) := by
  apply (exists_lift ..).imp fun _ H v f ↦
    .symm (H (V₀.integrated.flip _) (_ ∘L _ ∘L V.integrated.flip f) (by
      have := h.omega_projReal_of_isMixedLaw hT <| realMatrix (t.1ᴴ * D.lCoord * g.mat) *ᵥ ·
      simp_all [realVec_realMatrix_mulVec, integrated_realHeisOp, smul_smul, ← Matrix.mul_assoc,
        ← conjTranspose_mul]
      rw [← realVec_realMatrix_mulVec (D.iCoord * _), ← integrated_realHeisOp,
        ← V₀.integrated.map_smul₂]) v)
  fun_prop
  swap; simp_intro .. [norm_smul]; grw [← norm_sq_le_re_star_dot, ← sq_nonneg]

end

section

attribute [-simp] map_add map_mul Set.compl_union

open MeasureTheory Matrix stdLattice Prod Finset IsIntMatrix RingHom Complex MatMul
variable {E n n₀ p : Type _} [Field E] [CMType E] [WeilData E] [Fintype n] {s : n → ℤˣ} [Fintype n₀]
  [Fintype p] {s₀ : n₀ → ℤˣ} {V : Space E n s} {V₀ : Space E n₀ s₀} (D : V.Splitting V₀ p)
  (S : Set (FinPlace E)) (g : G E s) (t : GL p (𝔸 E)) (Ψ : _ → ℂ) (a : p → 𝔸f E) (w : n₀ → 𝔸f E)
  (b : p → 𝔸f E)

/-- The finite adelic vector g⁻¹(l t*⁻¹a + ιw + ktb), formed with the finite parts of the
matrices g⁻¹l t*⁻¹, g⁻¹ι and g⁻¹kt. -/
def finFrameVector := (D.frameAt g t).map snd *ᵥ (a ⊕ᵥ b ⊕ᵥ w)

/-- The function Ψ_x(y) = ∫ ψ_f(ȷαᾱ x*b_S) Ψ(g⁻¹(l t*⁻¹x + ιy + ktb)) db, over finite adelic b
integral off S, b_S its S-part, Ô^p of mass one. -/
def sliceDatum x y := ∫ b in integralBox p Sᶜ,
  psi₀ E (star x ⬝ᵥ idem S • b) * Ψ (D.finFrameVector g t x y b) ∂latticeMeasure ..

attribute [local simp] mul_add mul_sum snd_sum fst_sum star_mulVec sliceDatum finHeisOp integralBox
  idem_compl sub_smul semichar frameAt smul_smul idem_mul_self funext_iff
  name_schrodingerAct_boxIndicator smul_mem_stdLattice G.mat

attribute [local simp ←] mul_assoc integral_const_mul conjTranspose_mul Matrix.map_mul
  AddChar.map_add_eq_mul mulVec_finVec sub_eq_add_neg dataInner_vacElem_smul_vacElem mulVec_add
  exp_add

omit [WeilData E] in
@[local simp] lemma smul_finFrameVector (c : 𝔸f E) : c • D.finFrameVector g t a w b =
  D.finFrameVector g t (c • a) (c • w) (c • b) := by simp [finFrameVector]

omit [WeilData E] in
lemma adjoint_mulVec_finFrameVector : ((D.frameAt g t).map snd)ᴴ *ᵥ D.finFrameVector g t a w b = b
  ⊕ᵥ a ⊕ᵥ w := by simpa [finFrameVector, stdForm, fromBlocks_mulVec, ↓Matrix.map_mul, -frameAt]
  using! congr(.map $(D.gram_frameAt ..) (snd _ _) *ᵥ _)

omit [WeilData E] in
lemma exists_eq_finFrameVector y : ∃ a w b, y =
  D.finFrameVector g t a w b := have k v := (D.adjoint_mulVec_finFrameVector ..).trans (by aesop)
  ⟨_, _, _, (OrzechProperty.bijective_of_surjective_of_finrank_le (toLin' _) (⟨_, k ·⟩)
                               (by simp +arith [D.card_eq])).1 (k _).symm⟩

omit [WeilData E] in
@[local simp] lemma star_dot_finFrameVector a' w' b' :
  star (D.finFrameVector g t a w b) ⬝ᵥ D.finFrameVector g t a' w' b' = star a ⬝ᵥ b' + star b ⬝ᵥ a' +
  star w ⬝ᵥ w' := by erw [star_mulVec_dotProduct, adjoint_mulVec_finFrameVector]; simp [dotProduct]

variable {D} {S} {g} {t} {Ψ} {T : (p → 𝔸 E) → 𝒮 V →L[ℂ] 𝒮 V₀} (h : D.IsAdapted g t)
  (hT : D.IsMixedLaw T) (x : p → 𝔸f E) (f : 𝒮 V)
include h

omit [WeilData E] in
lemma IsAdapted.finFrameVector_mem_integralBox S : D.finFrameVector g t a w b ∈ integralBox n S ↔
  a ∈ integralBox p S ∧ w ∈ integralBox _ S ∧ b ∈ integralBox p S := by
  simp [mem_stdLattice]
  use ?_ ∘ (isInt_conjTranspose (M := .map _ snd) h.2).mulVec,
    mulVec h.2 ∘ ?_ <;> simp_all [↓adjoint_mulVec_finFrameVector, intVectors]

include hT

omit h in
lemma IsMixedLaw.apply_omega_rho_finFrameVector :
  T (t.1⁻¹ᴴ *ᵥ finVec x) (V.ω g (V.ϱ (finVec (D.finFrameVector g t a w b)) f)) = psi₀ E
  (half * star b ⬝ᵥ (x + (x + a))) • V₀.ϱ (finVec w) (T (t.1⁻¹ᴴ *ᵥ finVec (x + a)) (V.ω g f)) := by
  rw [finFrameVector, ← mulVec_finVec, ω_ϱ, hT]
  simp [dotProduct_mulVec, ↓mulVec_mulVec, adelicHeis]
  congr! <;> simp [finVec, stdAddChar, psi₀_apply, half, dotProduct]; grind

/-- Let g be adapted to t, T obey `Space.Splitting.IsMixedLaw`, x be finite adelic, x′ its part off
S ∪ S̄, u = ω(g)P^S f. Then T(t*⁻¹αx)u is P^S T(t*⁻¹αx′)u if x is integral on S ∪ S̄, else 0. -/
lemma IsAdapted.omega_projOn_of_isMixedLaw : T (t.1⁻¹ᴴ *ᵥ finVec x) (V.ω g (V.projOn S f)) =
  boxIndicator p S.conjClosure x •
  V₀.projOn S (T (t.1⁻¹ᴴ *ᵥ finVec (idem S.conjClosureᶜ • x)) (V.ω g (V.projOn S f))) := by
  simp; split
  refine (V₀.map_projOn_eq_const 1 fun y _ ↦ ?_).symm
  nth_rw 2 [← V.finHeisOp_projOn ((h.finFrameVector_mem_integralBox (-x) y 0 S.conjClosure).2 _)]
  rotate_right; refine by_contra (‹¬_› <| mem_stdLattice_iff_psi₀.2 fun b _ ↦
    smul_left_injective ℂ · ?_)
  nth_rw 2 [← V.finHeisOp_projOn ((h.finFrameVector_mem_integralBox 0 0 b ⊤).2 _)]
  all_goals simp_all [hT.apply_omega_rho_finFrameVector]
  grind

lemma IsAdapted.exists_omega_vacElem_of_isMixedLaw : ∃ c : ℂ, ∀ x, T x (V.ω g V.vacElem) =
  (c * ‖vacuumFn (t.1ᴴ *ᵥ x)‖ ^ 2) • V₀.vacElem :=
  ⟨_, fun x ↦ have ⟨(a, z), e⟩ := (adelicSum E 1).equiv.surjective (t.1ᴴ *ᵥ x)
  by rcases h.omega_projOn_of_isMixedLaw hT z V.vacElem (S := ⊤),
       h.omega_projReal_of_isMixedLaw hT a (V.finHeisOp (D.finFrameVector g t z 0 0) V.vacElem)
     by_cases z ∈ stdLattice .. <;> simp_all [e ▸ (adelicSum ..).3 _, ↓integrated_finHeisOp,
       finFrameVector, ↓star_dot_finFrameVector, ↓idem_compl,
      stdLattice.finVac, sq, ω_ϱ, star_dot_self_eq_sum, realVac, show realVec a + finVec z =
       _ by simpa [realVec, finVec] using! e]; ring⟩

/-- For S disjoint from S̄, Ψ Schwartz–Bruhat above S, g adapted to t, T obeying
`Space.Splitting.IsMixedLaw`, x finite adelic: T(t*⁻¹αx)ω(g)(Ψ⊗f) = Ψ_x ⊗ T(t*⁻¹αx′)ω(g)P^S f, with
Ψ_x = `Space.Splitting.sliceDatum` and x′ the part of x off S ∪ S̄. -/
lemma IsAdapted.omega_name_of_isMixedLaw (hS : S.IsConjDisjoint) (hΨ : IsSchwartzBruhat S Ψ) :
  T (t.1⁻¹ᴴ *ᵥ finVec x) (V.ω g (V.name S Ψ f)) = V₀.name S (D.sliceDatum S g t Ψ x)
  (T (t.1⁻¹ᴴ *ᵥ finVec (idem S.conjClosureᶜ • x)) (V.ω g (V.projOn S f))) := by
  obtain ⟨c, rfl : ∑ _ ∈ _, _ = _⟩ := exists_schrodingerComb_eq hS hΨ
  rw [show D.sliceDatum S g t _ x = ∑ y ∈ _, c y • D.sliceDatum S g t _ x by
    simpa [mul_left_comm (psi₀ E _), finFrameVector, add_comm (_ *ᵥ x), add_assoc] using fun _ ↦
      integral_finsetSum _ fun y _ ↦ (IsSchwartzBruhat.comp ((t⁻¹.1 * D.kCoord * g.mat).map snd)
      (by simp [← coe_snd]) _).integrableOn (by fun_prop)]
  simp [*]; congr!; obtain ⟨a, w, b, rfl⟩ := D.exists_eq_finFrameVector g t ‹_›
  simp_rw [smul_finFrameVector, hT.apply_omega_rho_finFrameVector, h.omega_projOn_of_isMixedLaw hT
    (x + _), map_smul, ← name_schrodingerAct_boxIndicator hS, smul_name]
  congr; ext; rw [smul_comm, eq_comm]; apply fourier_boxIndicator b
  any_goals simp_intro .. [schrodingerAct, -integralBox]
  simp [finFrameVector, -frameAt,
    ← Sum.elim_add_add]; erw [h.finFrameVector_mem_integralBox]; simp [ite_and]
  rw [psi₀_congr (half * idem S * star (x + x + a) ⬝ᵥ b) (zero_mem _)]; congr!; swap; simp
  repeat grind [star_dotProduct, idem_mul_self, idem_conjClosure_eq_add_star, idem_mul_star]

end

open Matrix IsDualFamily NumberField Heisenberg.IsVacuum ContinuousLinearMap
variable {E : Type _} [Field E] [CMType E] [WeilData E] {n : Type _}
  [Fintype n] {s : n → ℤˣ} {n₀ p : Type _} [Fintype n₀] [Fintype p] {s₀ : n₀ → ℤˣ} {V : Space E n s}
  {V₀ : Space E n₀ s₀} {D : V.Splitting V₀ p} (x) (f : 𝒮 V)

attribute [local simp] ω_ϱ

lemma isContPeriodic_along_k y : IsContPeriodic (_root_.ratVectors ..) (f <| D.iAdelic *ᵥ y +
  D.kAdelic *ᵥ ·) := ⟨by fun_prop, fun _ h _ ↦ .trans (by erw [ϱ_apply]; simp [D.beta_eq_coords,
  add_left_comm]) (V.isThetaFunctional_rawTheta.1 _ (D.kAdelic_mulVec_mem_ratVectors h) _)⟩

lemma exists_zeroTerm : ∃ L : 𝒮 V →L[ℂ] 𝒮 V₀,
    ∀ f y, L f y = quotMean (_root_.ratVectors ..) (f <| D.iAdelic *ᵥ y + D.kAdelic *ᵥ ·) := by
  have ⟨g, _, e, hs, h⟩ := D.exists_isAdapted_and_frame_eq 1
  have H := strongIntegral_apply _ (fun _ ↦ _ ∘L _ ∘L V.ω g) fun _ ↦
    (D.isContPeriodic_along_k _ 0).integrable_out
  have k := (by simpa [submatrix_mulVec_equiv, frameAt] using congr($h *ᵥ Sum.elim 0 ·))
  apply (exists_lift ..).imp' (· ∘L V.ω g⁻¹) fun _ hT f y ↦ (hT (_ ∘L _) _ (fun _ ↦
    (map_smul ..).trans (congr($(V₀.isThetaFunctional_rawTheta.exists_eq_apply_smul.choose_spec
    (_ ∘L boxProd hs (V₂ := V₀) (ϱ (hypSpace
    ..) 0 _)) (by rintro _ ⟨_, ⟨⟩⟩ v; erw [H, H, boxProd_rho]; congr! 2; simpa [← k,
    D.beta_eq_coords, ← iAdelic.eq_1, ← V₀.ratMap_mulVec_vecAtPoint, add_comm (D.kAdelic *ᵥ _)]
    using! V.apply_vecAtPoint_add _ (D.i *ᵥ _) (D.kAdelic *ᵥ _))) _).symm.trans
    (by erw [(strongIntegral ..).comp_apply, boxProd_rho, ← rho_boxProd, boxProd_vacElem,
          ← (strongIntegral ..).comp_apply]
        rfl))) _).trans (by erw [H]; simp [← k, D.beta_eq_coords, rep_apply_apply]; ac_nf)
  fun_prop; swap; intro
  erw [norm_smul, (strongIntegral ..).comp_apply, ← (boxProd hs (V₂ := V₀)).flip_apply]
  grw [le_opNorm, le_opNorm]; aesop

/-- The zero term along k: the bounded map 𝒮(V) → 𝒮(V₀) with (ev f)(y) the mean of f(ιy + kb)
over b in 𝔸^p modulo E^p. -/
def zeroTerm := D.exists_zeroTerm.choose

/-- For a splitting of V and f in 𝒮(V), the value of (ev f)~ at y is the mean of f̃(ιy + kb)
over b in 𝔸^p modulo E^p. -/
lemma zeroTerm_apply y : D.zeroTerm f y =
  quotMean (_root_.ratVectors ..) (f <| D.iAdelic *ᵥ y + D.kAdelic *ᵥ ·) := by grind [zeroTerm]

lemma zeroTerm_rho_kAdelic : D.zeroTerm (V.ϱ (D.kAdelic *ᵥ x) f) = D.zeroTerm f := by
  ext; simp [zeroTerm_apply, D.beta_eq_coords, ← quotMean_translate (isContPeriodic_along_k ..) x,
    add_assoc]

lemma zeroTerm_rho_iAdelic : D.zeroTerm (V.ϱ (D.iAdelic *ᵥ x) f) = V₀.ϱ x (D.zeroTerm f) := by
  ext; simp [zeroTerm_apply, D.beta_eq_coords, add_right_comm]

/-- The mixed model: for x in 𝔸^p, the bounded map f ↦ f[x] = ev(ϱ(lx)f) from 𝒮(V) to 𝒮(V₀). -/
def mixedTerm := D.zeroTerm ∘L V.ϱ (D.lAdelic *ᵥ x)

lemma mixedTerm_zero : D.mixedTerm 0 = D.zeroTerm := by ext; simp [mixedTerm]

/-- Heisenberg action in the mixed model: (ϱ(la + ιw + kb)f)[x] = ψ(½ȷ b*(2x + a)) ϱ(w) f[x +
a], for x, a, b in 𝔸^p, w an adelic vector of V₀ and f in 𝒮(V). -/
@[simp] lemma isMixedLaw_mixedTerm : D.IsMixedLaw D.mixedTerm :=
  isMixedLaw_comp_rho _ zeroTerm_rho_kAdelic zeroTerm_rho_iAdelic

/-- There are a compact set B in 𝔸^p and a constant M with ∑_ξ ‖f[φ(ξ)]‖ ≤ #φ⁻¹(B)·M·‖f‖ for
every additive homomorphism φ into 𝔸^p and every f in 𝒮(V), where f[x] is the mixed model
along the splitting D. -/
lemma exists_tsum_mixedTerm_le : ∃ B, IsCompact B ∧ ∃ M : NNReal,
  ∀ {ι} [AddGroup ι] (φ : ι →+ _) f, ∑' ξ, ‖D.mixedTerm (φ ξ) f‖ₑ ≤ (φ ⁻¹' B).encard * M * ‖f‖ₑ :=
  ((D.exists_isAdapted_and_frame_eq 1).choose_spec.1.exists_omega_vacElem_of_isMixedLaw
  D.isMixedLaw_mixedTerm).elim fun c hc ↦ (wiener_bound D.zeroTerm (right_ne_zero_of_mul_eq_one
  (conj_delta_mul_weilRep_vacElem ..)) (⟨D.lAdelic.toLin', by simp; fun_prop⟩ : _ →L[_] _)
  (((integrable_norm_sq (stdSpace ..).vacElem).ofReal.const_mul c).smul_const V₀.vacElem)
  D.lCoord.mulVec (by intros; erw [← mixedTerm_zero, isMixedLaw_mixedTerm, hc]; simp [← ofReal_norm,
  norm_smul, vacElem]) :)

lemma tsum_enorm_mixedTerm_le : ∃ M : NNReal, ∀ f, ∑' ξ, ‖D.mixedTerm (toAdele ∘ ξ) f‖ₑ ≤
  M * ‖f‖ₑ := D.exists_tsum_mixedTerm_le.elim fun _ ⟨k, M, h⟩ ↦
  ⟨_, (isCovolOneLattice_ratVectors.finite_preimage k).cast_ncard_eq ▸ h _⟩

lemma summable_norm_mixedTerm : Summable fun ξ ↦ ‖D.mixedTerm (toAdele ∘ ξ) f‖ :=
  (ENNReal.summable_toReal ((D.tsum_enorm_mixedTerm_le.choose_spec f).trans_lt (by tauto)).ne :)

/-- For a splitting of V and f in 𝒮(V), the family θ_{V₀}(f[ξ]), ξ in E^p, is summable with sum
θ_V(f).

Known result: Schrödinger and mixed models of the Weil representation; action of parabolic
subgroups. -/
lemma hasSum_theta_mixedTerm : HasSum (fun x ↦ V₀.θ (D.mixedTerm (toAdele ∘ x) f)) (V.θ f) := by
  convert fourier_inversion
    (hχ := by convert (stdSpace E p).isDualFamily_beta_sq; ext; simp [mem_ratVectors_iff])
    (D.isContPeriodic_along_k f 0) (V₀.θ.summable (D.summable_norm_mixedTerm f).of_norm) (by
    intro; erw [zeroTerm_apply]; congr!
    erw [← θ_ϱ, theta_eq_rawTheta, ϱ_swap, map_smul,
      V.isThetaFunctional_rawTheta.1 _ (D.symm.kAdelic_mulVec_mem_ratVectors ⟨_, rfl⟩)]
    simp [D.beta_eq_coords, vecAtPoint]; rfl) 0 <;> simp

/-- If g is adapted to t in the splitting D, there is c ≠ 0 with (ω(g)vac)[x] = c·|e(t*x)|²·vac,
the vacuum of V₀, for all x in 𝔸^p; here f[x] is the mixed model and e = `vacuumFn`. -/
lemma IsAdapted.mixedTerm_omega_vacElem {g t} (h : D.IsAdapted g t) : ∃ c ≠ (0 : ℂ), ∀ x,
  D.mixedTerm x (V.ω g V.vacElem) = (c * ‖vacuumFn (t.1ᴴ *ᵥ x)‖ ^ 2) • V₀.vacElem := by
  peel h.exists_omega_vacElem_of_isMixedLaw D.isMixedLaw_mixedTerm
  use (by simpa [·, *, ← (D.hasSum_theta_mixedTerm _).tsum_eq, dataInner_eq_quotMean,
    ← θ_ϱ, -θ_apply] using (V.dataInner_omega g ..).trans V.dataInner_vacElem_vacElem)
