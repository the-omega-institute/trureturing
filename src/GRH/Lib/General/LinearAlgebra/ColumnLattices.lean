import GRH.Lib.General.LinearAlgebra.AdelicRingDefs
import GRH.Lib.Adelic.Hecke.HeckeBasic
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of linear algebra and matrices (textbook or folklore).

Known result: commutativity of the spherical Hecke algebra of GL_n and the Eichler commutation
relation. Only split places of unitary groups are treated, and commutativity is proved by Gelfand's
trick. The relation is an identity of Hecke polynomials on the unramified datum, obtained by summing
over subspaces of the residue space, without the Satake transform. Source: T. Tamagawa, On the zeta
functions of a division algebra, Ann. Math. 77 (1963); S. Rallis, Langlands' functoriality and the
Weil representation, Amer. J. Math. 104 (1982); R. Howe, Theta series and invariant theory,
Corvallis 1979.

This file: Smith normal form over rings that are valuation rings up to idempotents. Integral and
unimodular matrices, congruence subgroups of unitary groups: basic lemmas. Inverse transpose,
adjoints of spherical Hecke operators, commutativity by Gelfand's trick. Basic facts on integral
lattices, column spans and generalised index over a subring. -/

open Matrix Submodule Fintype GeneralLinearGroup

/-- Smith normal form: if the subring R of a commutative ring A satisfies `IsValuationPair`, every
square matrix y over A is k·D·k' with k, k' in GL_n(R) and D diagonal with entries in A. -/
lemma IsValuationPair.smith_normal_form {A n} [CommRing A] {R} [Fintype n] (val : @IsValuationPair A
  _ R) y : ∃ᵉ (k ∈ intGL n R) (k' ∈ intGL n R) (d), y = k.1 * diagonal d * k'.1 := by
  simp [intGL, -val_map_apply]
  induction' h : card n with _ ih generalizing n
  simp_all [card_eq_zero_iff, ← ext_iff]
  obtain ⟨p⟩ := Finset.card_eq_succ.1 h
  let B (c : Fin 2 → GL n R) := map R.subtype (c 0) * y * map R.subtype (c 1)
  choose c H using (id fun c d ↦ (val (B c p p) (B d p p)).elim fun e h ↦ ⟨c * cutGL (Subtype.ext
    h.1) ∘
    (c⁻¹ * d), by simp [B, cutGL, mul_add, add_mul, Matrix.map_smul, Matrix.map_add,
    R.smul_def] at h ⊢; grind⟩ : Directed LE.le (R ∙ B · p p)).finite_le (.swap _ p ∘ ·)
  choose w W using (mem_span_singleton (x := B c · ·).1 (Set.mem_of_eq_of_mem
    (dotProduct_comm ..) (by repeat apply @sum_smul_mem R; intros
                             simpa [B, -val_map_apply] using H ![_, _])))
  let e := Equiv.sumCompl (· = p)
  choose k l d E using ih ((B c - of (w · p • B c p)).toBlock (· ≠ p) _) (by simp_all)
  use c⁻¹ 0 * .mk'' (reindex e e (fromBlocks 1 0 (of (w · ·)) k)) (by simp), .mk'' (reindex e e
    (fromBlocks 1 (of (w · ·)) 0 l)) (by simp) * c⁻¹ 1, ((B c p ·.1) ⊕ᵥ d) ∘ e.2
  simp [mul_assoc, Units.eq_inv_mul_iff_mul_eq, -coe_units_inv]
  simp_all only [← mul_assoc, Units.eq_mul_inv_iff_mul_eq, R.smul_def, smul_eq_mul]
  apply (B c).ext; simp [e.surjective.forall₂, e, entrywise, ← e.sum_comp, apply_ite,
    ↓mul_diagonal] at E ⊢; grind-linarith

open MatMul QuotientGroup Units

section

variable {A l n μ} [CommRing A] {R : Subring A} {M : Matrix l μ A} [Fintype n] {𝔰 : Shape} {k}

lemma Membership.mem.isIntMatrix : k ∈ intGL n R → IsIntMatrix R k.1 := (mem_intGL.1 ·|>.1)

lemma Membership.mem.isIntMatrix_inv : k ∈ intGL n R → IsIntMatrix R k⁻¹.1 :=
  (inv_mem ·|>.isIntMatrix)

lemma mulVec_mem_intVectors_iff (h : k ∈ intGL n R) {w} : k *ᵥ w ∈ intVectors R n ↔
  w ∈ intVectors R n := ⟨(by simpa using h.isIntMatrix_inv.mulVec ·), h.isIntMatrix.mulVec⟩

variable {u} [StarRing A] {J : Matrix n n A} {T : 𝔰.Form A} {x}

lemma IsIntMatrix.isInt_conjTranspose [i : IsStarStable R] : IsIntMatrix R M → IsIntMatrix R Mᴴ :=
  i.rec (by tauto)

/-- The integral points of U(J) normalise the principal congruence subgroup of U(J) of level u. -/
lemma unitaryLevel_one_le_normalizer {y} : y ∈ unitaryLevel R 1 J → x ∈ unitaryLevel R u J →
  y * x * y⁻¹ ∈ unitaryLevel R u J
  | ⟨h, _⟩ => .imp (by aesop) (by simpa using h.isIntMatrix.mul · |>.mul h.isIntMatrix_inv)

lemma mem_besselU : x ∈ T.besselU ↔ ∀ i j, FI.level j ≤ FI.level i → x.1 i j =
  (1 : Matrix ..) i j := .rfl

attribute [local simp] IsIntMatrix splitGram IsUnimodular unitaryLevel mem_intGL

omit [StarRing A] in
lemma IsIntMatrix.neg : IsIntMatrix R M → IsIntMatrix R (-M) := by simp

omit [StarRing A] in
lemma splitGram_mul {T'} : T * T' = 1 → T.splitGram * T'.splitGram = 1 := by aesop

lemma unitaryLevel_one : unitaryLevel R 1 J = (intGL n R).subgroupOf _ := by aesop

lemma IsUnimodular.isIntMatrix : IsUnimodular R J → IsIntMatrix R J := by aesop

lemma IsUnimodular.isUnit_det_and_isIntMatrix_inv : IsUnimodular R J → IsUnit J.det ∧
  IsIntMatrix R J⁻¹ := by aesop

/-- Let J be unimodular hermitian over a conjugation-stable subring R and u ∈ R a unit of A. An
isometry x of J with u⁻¹(x − 1) integral lies in the principal congruence subgroup of level
u. -/
lemma IsUnimodular.mem_unitaryLevel [IsStarStable R] (H : IsUnimodular R J) (hu : u.1 ∈ R) (h :
  IsIntMatrix R (u⁻¹ • (x.1.1 - 1))) :
  x ∈ unitaryLevel R u J := have i := by simpa [← u.smul_def] using (h.smul hu).add .one
  ⟨by simpa [i, ← U.form_mul_inv_eq, H.isUnit_det_and_isIntMatrix_inv] using
    H.isUnit_det_and_isIntMatrix_inv.2.mul (.mul (.isInt_conjTranspose i) H.isIntMatrix), h⟩

/-- If the Gram matrix T on V_ϱ is hermitian and invertible over the subring R, then so is the
Gram matrix of the whole space obtained by adding ϱ hyperbolic planes. -/
lemma IsUnimodular.splitGram : IsUnimodular R T → IsUnimodular R T.splitGram :=
  .imp (by simp) fun ⟨u, _⟩ ↦ ⟨⟨_, _, splitGram_mul u.3, splitGram_mul u.4⟩, by aesop⟩

end

section

variable {n} [Fintype n] {R} [CommRing R] {O : Subring R}

/-- The automorphism g ↦ (gᵀ)⁻¹ of the group GL_n(R). -/
noncomputable def invTransposeGL :=
  (⟨.mk (transposeGL ·⁻¹) (transposeGL ·⁻¹), by simp [← val_inj]⟩ : GL n R ≃* _)

@[simp] lemma invTransposeGL_mem_intGL k : invTransposeGL k ∈ intGL n O ↔
  k ∈ intGL n O := by simp_rw [mem_intGL]; tauto

/-- For a subring O of R satisfying `IsValuationPair` and g in GL_n(R), there is k in GL_n(O) with
gᵀ = (kᵀ)⁻¹gk, that is, with gk symmetric. -/
lemma exists_invTransposeGL_inv_eq (h : IsValuationPair O) g : ∃ k ∈ intGL n O, invTransposeGL g⁻¹ =
  invTransposeGL k * g * k := let ⟨k, _, l, _, _, _⟩ := h.smith_normal_form g
  ⟨l⁻¹ * transposeGL k, by simp_all [mul_mem, mem_intGL, invTransposeGL, transposeGL, ← val_inj,
    mul_assoc, -coe_units_inv]⟩

variable {A W W' F} [CommSemiring A] [AddCommMonoid W] [Module A W] [AddCommMonoid W'] [Module A W']
  [Field F] {O : ValuationSubring F} {π π'} {f f' : GL n F → A} {v : W} (hb : IsBiInvariant (intGL n
  O.1) f) (h' : IsBiInvariant (intGL n O.1) f') {σ : A →+* A} {Z} [AddCommMonoid Z] [Module A Z]
  (B : W →ₛₗ[σ] W' →ₗ[A] Z) {v'} (h1 : v ∈ levelSpace (A := A) π (intGL n O.1))
include h1 hb

/-- Let O be a valuation subring of a field F, K = GL_n(O), f K-bi-invariant on finitely many
cosets, B a GL_n(F)-invariant pairing, σ-semilinear in the first variable. For K-fixed v,
v', f*(g) = σ(f(g⁻¹)) has the same property and B(fv, v') = B(v, f*v'). -/
lemma IsBiInvariant.heckeFun_adjoint (hB : ∀ g x y, B (π g x) (π' g y) =
  B x y) : letI K := intGL n O.1; v' ∈ levelSpace π' K → IsBiInvariant K (σ <| f ·⁻¹) ∧
    B (heckeFun π K f v) v' = B v (heckeFun π' K (σ <| f ·⁻¹) v') := fun h ↦ by
  choose b _ using fun q : _ ⧸ intGL n O.1 ↦
    exists_invTransposeGL_inv_eq (isValuationPair_valuationSubring O) q.out⁻¹
  simp_all [heckeFun_eq_sum_pullback _ h hb.1.toFinset invTransposeGL (fun _ ↦
    ⟨invTransposeGL⁻¹ ·, _⟩) (by grind [=_ invTransposeGL_mem_intGL]),
    ← fun g y ↦ hB g⁻¹ v (π' g y), IsBiInvariant, heckeFun_sum]

include h'

/-- Gelfand's trick: for a valuation subring O of a field F and K = GL_n(O), K-bi-invariant
functions f, f' on GL_n(F), supported on finitely many cosets, commute in their action `heckeFun` on
a K-fixed vector v.

Known result: Commutativity of the spherical Hecke algebra of GL_n. -/
lemma IsBiInvariant.heckeFun_comm : letI T := heckeFun π (intGL n O.1); T f (T f' v) =
    T f' (T f v) := by
  choose b _ using exists_invTransposeGL_inv_eq (n := n) (isValuationPair_valuationSubring O)
  simp_all [↓heckeFun_heckeFun, ← finsum_eq_sum_of_support_subset, not_imp_not]; congr with x
  convert! finsum_comp_equiv (Quotient.congr (invTransposeGL.1.trans (.mulLeft (x * b x))) _) with
    _ q
  erw [← q.out_eq, (mk_out_eq_mul (intGL ..) (_ * _)).choose_spec,
    (_ : ∀ g, f' g = f' (invTransposeGL g⁻¹))]
  all_goals simp_all [leftRel_apply,
    ← mul_assoc] <;> simp_all [mul_assoc] <;> grind [=_ invTransposeGL_mem_intGL]

end

variable {A} [CommRing A] {R : Subring A} {m n} [Fintype n] {M : Matrix m n A}

/-- For π : R → B, the ℂ-linear map sending a function f on matrices over B to the function on
matrices S over A that is f(πS) for S integral, else 0. -/
noncomputable def liftIntegralFn {B} (π : R → B) [Fintype m] :=
  IsLinearMap.mk' (R := ℂ) (fun (f : _ → ℂ) (S
  : Matrix m n A) ↦ if h : ∀ i j, S i j ∈ R then f (of (π ⟨_, h · ·⟩)) else 0) ⟨by aesop, by aesop⟩

lemma isOpen_intVectors [TopologicalSpace A] (h : @IsOpen A _ R := by tauto) :
  IsOpen (intVectors R n).carrier := isOpen_pi_iff'.2 (by tauto)

lemma colLattice_le {L} (h : ∀ j, M.col j ∈ L) : colLattice R M ≤ L
  | _, ⟨_, y, rfl⟩ => by simpa [mulVec_eq_sum] using! L.sum_smul_mem (⟨_, y ·⟩) (by tauto)

/-- For π : R → B, a ∈ GL_n(R), b ∈ GL_m(R) and an m × n matrix M over A, the value of
`liftIntegralFn` π f at bMa equals the value at M of the lift of X ↦ f(π(b)Xπ(a)). -/
lemma liftIntegralFn_mul {B} [CommRing B] (π : R →+* B) [Fintype m] f (a : GL n R)
    (b : GL m R) : liftIntegralFn π f ((b.map R.subtype).1 * M * (a.map R.subtype).1) =
    liftIntegralFn π (f <| (b.map π).1 * · * (a.map π).1) M := by
  wlog h : IsIntMatrix R M
  exact (dite_eq_right fun H ↦ h (by simpa [liftIntegralFn, ← Matrix.mul_assoc, H,
    -GeneralLinearGroup.val_map_apply] using! this π 1 a⁻¹ b⁻¹ H)).trans (.symm (dite_eq_right h))
  rw [show M = (of (⟨_, h · ·⟩)).map R.subtype by rfl]
  simp [liftIntegralFn, ← Matrix.map_mul, -Subring.coe_subtype, ← Matrix.map.eq_1, -of_apply]

omit [Fintype n] in
lemma single_mem_intVectors j : Pi.single j 1 ∈ intVectors R n := by aesop_cat

lemma col_mem_colLattice j : M.col j ∈ colLattice R M := ⟨_, single_mem_intVectors j, by simp⟩
