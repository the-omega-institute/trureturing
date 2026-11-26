import GRH.Lib.General.LinearAlgebra.AdelicRingDefs
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of linear algebra and matrices (textbook or folklore).

Part of: Gauss sums of a character of the determinant over matrix rings (known result; see
Lib.Weil.GaussSum.ShearInvariance).

This file: Finite Fourier inversion on matrices; Gauss sums of primitive determinant characters.
GL_n transitive on unimodular vectors, index of stabiliser; iterated composition of maps. Iterated
tensor products, pure tensors, multilinear extension of a composite of maps. Local ring
homomorphisms reflect invertibility of matrices. -/

open AddChar Finset Function Matrix MulAction TensorProduct

/-- Let O be a subring of F, π: O → R a surjective ring homomorphism with kernel {x : gx ∈ O},
and ψ an additive character of F with ψ(tO) = 1 exactly for t in O. Then π(x) ↦ ψ(gx) is a
primitive additive character of R. -/
lemma exists_primitive_residue_addChar {R F} [CommRing R] [CommRing F] {O : Subring F} {π : O →+* R}
  {g} {ψ : AddChar F ℂ} (h : Surjective π ∧ ∀ x, π x = 0 ↔ g * x.1 ∈ O) (hψ : ∀ t, (∀ s ∈ O,
  ψ (t * s) = 1) ↔ t ∈ O) : ∃ φ : AddChar R ℂ, φ.IsPrimitive ∧ ∀ x, φ (π x) = ψ (g * x) := by
  have e := FactorsThrough.extend_apply (f := π) (fun x y k ↦ eq_of_div_eq_one
    (by simpa [mul_sub, map_sub_eq_div] using (hψ (g * ↑(x - y))).2 (by grind) 1)) 1
  use ⟨_, by simpa using e 0, ?_⟩ <;> simp [AddChar.IsPrimitive, h.1.forall, *, AddChar.ext_iff,
    ← map_mul, ← mul_assoc, ← map_add, mul_add, map_add_eq_mul, -not_forall]

variable {R a N} [CommRing R] [Fintype R] [Fintype a] [Fintype N] {ψ : AddChar R ℂ} (ψ' : AddChar R
  ℂ) {χ : MulChar R ℂ} {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive) (f : Matrix N a R → ℂ) {n} [Fintype n]

/-- The finite Fourier transform: for an additive character ψ of a finite ring R and D on n×m
matrices, the function ρ ↦ ∑_v D(v) ψ(tr ρv) on m×n matrices. -/
noncomputable def matrixFourier (f : Matrix N a R → ℂ) (ρ : Matrix a N R) := ∑ v,
  f v * ψ' (ρ * v).trace

/-- Primitivity of χ: for every a ≠ 0 in R, some unit of the form 1 + ca has χ(1 + ca) ≠ 1 (and
≠ 0). -/
def IsPrimitiveMulChar (χ : MulChar R ℂ) := ∀ a ≠ 0, ∃ c, χ (1 + c * a) ≠ 0 ∧ χ (1 + c * a) ≠ 1

include hψ

/-- Orthogonality of characters: for a primitive additive character ψ of a finite ring R and z ∈
R^a, the sum of ψ (z ⬝ x) over x ∈ R^a is |R^a| if z = 0 and 0 otherwise. -/
lemma sum_addChar_dotProduct (z : a → R) : ∑ x, ψ (z ⬝ᵥ x) =
  ite (z = 0) (Fintype.card (a → R)) 0 := by
  convert (Fintype.prod_sum (ψ <| z · * ·)).symm
  erw [← map_prod ψ.toMonoidHom]; rfl'
  simp [mul_comm, sum_mulShift, hψ, Fintype.prod_ite_zero, funext_iff]

lemma sum_addChar_trace_mul (ρ : Matrix a N R) : ∑ v : Matrix N a R, ψ (ρ * v).trace = ite (ρ = 0)
  (Fintype.card
  (Matrix N a R)) 0 := by simpa [← vec_bijective.sum_comp, vec_dotProduct_vec,
  Fintype.card_of_bijective vec_bijective] using sum_addChar_dotProduct hψ ρᵀ.vec

/-- Fourier inversion for matrices over a finite commutative ring R with a primitive additive
character ψ: applying the transform `matrixFourier` twice to f gives y ↦ f(−y) times the
number of matrices. -/
lemma matrixFourier_matrixFourier y : matrixFourier ψ (matrixFourier ψ f) y =
  f (-y) * Fintype.card (Matrix a N R) := by simp [matrixFourier, sum_mul, mul_assoc,
  ← map_add_eq_mul, @trace_mul_comm a, ← trace_add, sum_comm,
  ← Matrix.add_mul, ← mul_sum, sum_addChar_trace_mul hψ, add_eq_zero_iff_eq_neg]

/-- For a primitive additive character ψ of a finite commutative ring R, every complex function
f on N × a matrices over R is a linear combination of the characters y ↦ ψ(tr(yu)), u an a ×
N matrix. -/
lemma exists_sum_smul_addChar_trace_eq : ∃ c : Matrix a N R → ℂ, ∑ u, c u • (ψ <| trace <| · * u) =
  f := ⟨_, funext (by simpa using!
  matrixFourier_matrixFourier hψ fun t ↦ f (-t) / Fintype.card (Matrix a N R))⟩

/-- Matrix Gauss sums over a finite ring: let ψ and χ be primitive, and S(gd) = χ(det g)S(d) on
square matrices d for invertible g. Then Ŝ(y) = χ⁻¹(det y)Ŝ(1), and Ŝ(1) times the conjugate
of ∑_v χ(det v)ψ(tr v) equals S(1)·#{matrices}.

Known result: Gauss sums of a character of the determinant over matrix rings. -/
lemma matrix_gauss_sum (hχ : IsPrimitiveMulChar χ) S (h : ∀ (g : GL a R) d, S (g.1 * d) =
  χ g.1.det * S d) : (∀ y, matrixFourier ψ S y = χ⁻¹ y.det * matrixFourier ψ S 1) ∧
  star (matrixFourier ψ (a := a) (χ ·.det) 1) * matrixFourier ψ S 1 = S 1 * Fintype.card (Matrix a a
  R) := have h y (g : GL a R) : χ g.det * matrixFourier ψ S (y * g) = matrixFourier ψ S y :=
    .trans (by simp_all [matrixFourier, mul_sum, mul_assoc]) (g.mulLeft_bijective.sum_comp
    _); (⟨·, by simpa [matrixFourier, sum_mul, mul_right_comm, ← χ.star_eq_inv,
    ψ.map_neg_eq_conj] using (funext ‹_› ▸ matrixFourier_matrixFourier hψ S (-1) :)⟩) fun y ↦ by
  by_contra
  obtain ⟨y, rfl⟩ := (isLeftRegular_of_non_zero_divisor y fun v _ ↦ Matrix.ext fun i j ↦ by_contra
    (hχ _ · |>.elim fun u _ ↦ by specialize h y (.mk'' (1 + v * single j () (1 : R) * single () i
    u) ?_) <;> simp_all [mul_add, det_one_add_mul_comm, ← y.mul_assoc, MulChar.apply_eq_zero_iff,
    mul_left_eq_self₀, ← isUnit_iff_isUnit_det, IsUnit.mul_right_eq_zero])).isUnit_of_finite
  simp_all [χ.inv_apply, ← h y y⁻¹]

/-- For linear maps L_i : M_i → M_{i+1}, the composite L_{j−1} ∘ ⋯ ∘ L_0 : M_0 → M_j; the
identity for j = 0. -/
def compUpTo {M : ℕ → _} [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
    (L : ∀ j, M j →ₗ[R] M (j + 1)) : ∀ j, M 0 →ₗ[R] M j | 0 => .id | j + 1 => L j ∘ₗ compUpTo L j

omit [Fintype R] hψ

/-- Over a commutative ring, a vector with a unit entry is, for any i, the i-th column of an
invertible matrix. -/
lemma exists_GL_smul_single {v : n → R} (h : ∃ j, IsUnit (v j)) i : ∃ g :
    GL n R, g • Pi.single i 1 = v := h.rec fun j _ ↦ by
  use .mk'' (updateCol 1 j v) (by simpa [← cramer_apply]) * .swap _ j i
  simp [funext_iff, Units.smul_def]

/-- For a finite field F and a nonzero vector u in F^n, the stabiliser of u in GL_n(F) has index
|F|^n − 1. -/
lemma index_stabilizer_GL_vector {F} [Field F] [Finite F] {u : n → F} (h : u ≠ 0) : (stabilizer (GL
  n F) u).index = .card F ^ Fintype.card n - 1 := have t : {0}ᶜ ⊆ orbit _ (_ : n → F) := fun _ ↦
  (exists_GL_smul_single · (ne_iff.1 h).choose) ∘ by simp [funext_iff]
  by rw [index_stabilizer, orbit_eq_iff.2 (t h), ← t.antisymm, Set.ncard_compl] <;>
    simp [Nat.card_pi, orbit, smul_eq_zero_iff_eq]

variable {S : ℕ → Type} {M : ℕ → Type*} [∀ j, AddCommGroup (S j)] [∀ j, Module ℂ (S j)]
  [∀ j, AddCommGroup (M j)] [∀ j, Module ℂ (M j)] (b : ∀ j, S j →ₗ[ℂ] M j →ₗ[ℂ] M (j + 1))
  (t : ∀ j, S j →ₗ[ℂ] S j) (f : ∀ j, S j) {g h : ∀ j, S j}

variable (S) in
/-- The complex tensor product S_{j−1} ⊗ ⋯ ⊗ S_0, equal to ℂ for j = 0. -/
def TensorChain : ℕ → ModuleCat ℂ | 0 => .of ℂ ℂ | j + 1 => .of ℂ (S j ⊗[ℂ] TensorChain j)

/-- For a family of vectors f i in S i, the pure tensor f (j−1) ⊗ ⋯ ⊗ f 0 in S (j−1) ⊗ ⋯ ⊗ S 0;
it is 1 ∈ ℂ for j = 0. -/
def TensorChain.pure j :=
  compUpTo (M := (TensorChain S ·)) (TensorProduct.mk _ _ _ <| f ·) j (1 : ℂ)

/-- Two steps at once: the linear map S_{2i} ⊗ S_{2i+1} → Hom(M_{2i}, M_{2i+2}) sending s ⊗ s'
to b_{2i+1}(s') ∘ b_{2i}(s). -/
def TensorChain.liftInPairs i : S (2 * i) ⊗[ℂ] S (2 * i + 1) →ₗ[ℂ] M (2 * i) →ₗ[ℂ] M (2 *
  (i + 1)) := lift ((LinearMap.llcomp ..).compl₁₂ (b _) (b _)).flip

/-- For x in M_0, the linear map S_{j−1} ⊗ ⋯ ⊗ S_0 → M_j sending s_{j−1} ⊗ ⋯ ⊗ s_0 to
b_{j−1}(s_{j−1}) ⋯ b_0(s_0) x; it is c ↦ cx for j = 0. -/
def TensorChain.lift (x : M 0) : ∀ j, TensorChain S j →ₗ[ℂ] M j
  | 0 => .toSpanSingleton _ _ x | j + 1 => TensorProduct.lift ((b j).compl₂ (lift x j))

/-- For bilinear maps b_i : S_i × M_i → M_{i+1}, f_i in S_i and x in M_0, the map `TensorChain.lift`
b x j takes the pure tensor f_{j−1} ⊗ ⋯ ⊗ f_0 to (b_{j−1}(f_{j−1}) ∘ ⋯ ∘ b_0(f_0))(x). -/
@[simp] lemma TensorChain.lift_pure x j :
    lift b x j (pure f j) = compUpTo (b · (f _)) j x := j.rec (one_smul ..) fun _ ↦ congrArg _

/-- For endomorphisms t i of S i, the endomorphism t (j−1) ⊗ ⋯ ⊗ t 0 of S (j−1) ⊗ ⋯ ⊗ S 0; the
identity of ℂ for j = 0. -/
def TensorChain.map := lift (M := (TensorChain S ·)) (TensorProduct.mk .. ∘ₗ t ·) (1 : ℂ)

@[simp] lemma TensorChain.map_pure j : map t j (pure f j) = pure (t · (f _)) j := lift_pure ..

lemma TensorChain.pure_smul (c : ℕ → ℂ) m : (∀ j < m, g j = c j • f j) → pure g m =
  (range m).prod c • pure f m := m.rec (by aesop) fun m i h ↦ by
  erw [prod_range_succ_comm, ← smul_tmul_smul, ← h, ← i] <;> bound

@[congr] lemma TensorChain.pure_congr {m} : (∀ j < m, g j = h j) → pure g m = pure h m := by
  simpa using pure_smul h 1 m

/-- The composite of the first p double steps (`TensorChain.liftInPairs`) at the pure tensors f_{2i}
⊗ f_{2i+1} agrees at every x with the composite of the first 2p single steps b_j(f_j). -/
lemma TensorChain.liftInPairs_pure p x : compUpTo (liftInPairs b · (f _ ⊗ₜ f _)) p x =
  compUpTo (b · (f _)) _ x := p.rec rfl fun _ ↦ congrArg (_ ∘ _)

lemma isUnit_of_mapMatrix {R n} [CommRing R] [Fintype n] {S} [CommRing S] (f : R →+* S)
    [IsLocalHom f] {M} : IsUnit (f.mapMatrix (m := n) M) → IsUnit M := by
    simp [↓isUnit_iff_isUnit_det, ↓← f.map_det]
