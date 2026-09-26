/- GID: D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.claim; result=D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.result; claim=D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.claim
   digest: Answers Question 11.3 of Eidesen, arXiv:2506.01843v3, in the affirmative: in the paper's own projective error model C2 x D_4 (Proposition 8.1, n = 2) on C^4 the code W = C(1,1,1,1) has |L(W)| |S(W)| = |G| = 16 while S(W) is not normal. -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: the irreducibility of the error
  model over every invariant subspace (`hirr`, from the matrix-unit expansion `hspan`), its
  projective faithfulness (`hfaith`, from trace orthogonality `htr`), and the identification of
  the orthogonal projection with the averaging matrix (`hPW`) giving the characterizations `hLchar`
  and `hSchar` of L(W) and S(W)
admission_basis: open-problem-resolution (issue #10156)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer

open Matrix

/-!
Eidesen, *Projective error models: Stabilizer codes, Clifford codes, and weak stabilizer codes*,
arXiv:2506.01843v3, §11, Question 11.3: does there exist a Hilbert space `V`, a subspace `W`
and a projective error model `(G, π)` on `V` with `|G| = (dim V)^2` such that
`|G| = |L_{(G,π)}(W)| · |S_{(G,π)}(W)|` but `S_{(G,π)}(W)` is not normal in `G`? Here
`L(W) = {x : P_W π(x) = π(x) P_W}`, `S(W) = {x : P_W π(x) P_W ∈ 𝕋 P_W}` and a projective
error model is a projectively faithful irreducible projective representation of a finite
group. In the model of Proposition 8.1 with `n = 2`, `G = C₂ × D_{2n}` (the dihedral factor of
order 8) acting on `ℂ^4`, the code
`W = ℂ (1, 1, 1, 1)` has `L(W) = S(W) = ⟨b, c⟩` of order 4, and `a b a⁻¹ ∉ ⟨b, c⟩`.
-/

variable {G : Type} [Group G] {d : ℕ}

/-- `π` is a projective representation by unitary matrices: `π x π y = c π (x y)` with
`|c| = 1`. -/
def IsProjRep (π : G → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ x, π x ∈ Matrix.unitaryGroup (Fin d) ℂ) ∧
    ∀ x y, ∃ c : ℂ, ‖c‖ = 1 ∧ π x * π y = c • π (x * y)

/-- `q ∘ π` is injective, `q` the quotient by scalars. -/
def ProjFaithful (π : G → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ x y, (∃ c : ℂ, π x = c • π y) → x = y

/-- The only subspaces invariant under every `π x` are `0` and `V`. -/
def IrredProj (π : G → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin d)),
    (∀ x, ∀ v ∈ U, Matrix.toEuclideanLin (π x) v ∈ U) → U = ⊥ ∨ U = ⊤

/-- A projective error model on `V = ℂ^d`: a projectively faithful irreducible projective
representation. -/
def IsPEM (π : G → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  IsProjRep π ∧ ProjFaithful π ∧ IrredProj π

/-- `L_{(G,π)}(W) = {x : P_W π(x) = π(x) P_W}`. -/
noncomputable def logicalOps (π : G → Matrix (Fin d) (Fin d) ℂ)
    (W : Submodule ℂ (EuclideanSpace ℂ (Fin d))) : Set G :=
  {x | ∀ v, W.starProjection (Matrix.toEuclideanLin (π x) v) =
    Matrix.toEuclideanLin (π x) (W.starProjection v)}

/-- `S_{(G,π)}(W) = {x : P_W π(x) P_W ∈ 𝕋 P_W}`. -/
noncomputable def stabilizers (π : G → Matrix (Fin d) (Fin d) ℂ)
    (W : Submodule ℂ (EuclideanSpace ℂ (Fin d))) : Set G :=
  {x | ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v,
    W.starProjection (Matrix.toEuclideanLin (π x) (W.starProjection v)) = c • W.starProjection v}

/-- The negative answer to Question 11.3 of arXiv:2506.01843v3: whenever `(G, π)` is a projective
error model on `ℂ^d` with `|G| = d^2` and `|L(W)| · |S(W)| = |G|`, the set `S(W)` is closed under
conjugation. -/
def claim : Prop :=
  ∀ (d : ℕ) (G : Type) [Group G] [Fintype G] (π : G → Matrix (Fin d) (Fin d) ℂ)
    (W : Submodule ℂ (EuclideanSpace ℂ (Fin d))),
    IsPEM π → Fintype.card G = d ^ 2 →
    (logicalOps π W).ncard * (stabilizers π W).ncard = Fintype.card G →
    ∀ g : G, ∀ s ∈ stabilizers π W, g * s * g⁻¹ ∈ stabilizers π W

/-- The group `C₂ × D_{2n}` of Proposition 8.1 with `n = 2`; the dihedral factor has order 8. -/
private abbrev GG := Multiplicative (ZMod 2) × DihedralGroup 4

/-- The block swap `C`. -/
private def Cm : Matrix (Fin 4) (Fin 4) GaussianInt :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
/-- `X ⊕ X`, `X` the Pauli matrix. -/
private def XXm : Matrix (Fin 4) (Fin 4) GaussianInt :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
/-- `P ⊕ (-P)` with `P = diag(1, i)`. -/
private def PPm : Matrix (Fin 4) (Fin 4) GaussianInt :=
  !![1, 0, 0, 0; 0, ⟨0, 1⟩, 0, 0; 0, 0, -1, 0; 0, 0, 0, ⟨0, -1⟩]
/-- `π(cᵏ bˡ aᵐ) = Cᵏ (X ⊕ X)ˡ (P ⊕ -P)ᵐ` with entries in `ℤ[i]`; the element `b aᵐ` is
`sr m`. -/
private def piZ : GG → Matrix (Fin 4) (Fin 4) GaussianInt
  | (c, DihedralGroup.r m) => Cm ^ (Multiplicative.toAdd c).val * PPm ^ m.val
  | (c, DihedralGroup.sr m) => Cm ^ (Multiplicative.toAdd c).val * XXm * PPm ^ m.val

/-- The all-ones matrix. -/
private def Jz : Matrix (Fin 4) (Fin 4) GaussianInt := Matrix.of fun _ _ => 1

/-- The error model over `ℂ`. -/
private noncomputable def piC (x : GG) : Matrix (Fin 4) (Fin 4) ℂ :=
  (piZ x).map GaussianInt.toComplex

/-- The vector `(1, 1, 1, 1)`. -/
private noncomputable def uu : EuclideanSpace ℂ (Fin 4) := WithLp.toLp 2 (fun _ => 1)

/-- The matrix of the orthogonal projection onto `ℂ (1, 1, 1, 1)`. -/
private noncomputable def Pm : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun _ _ => (1 / 4 : ℂ)

/-- Every `π(x)` is a monomial matrix with entries in `{0, ±1, ±i}`; unitarity, the projective
relation with phases in `{±1, ±i}`, trace orthogonality of distinct elements, the matrix-unit
expansion `4 E_{kl} = Σ_x conj(π(x)_{kl}) π(x)`, and the column-sum and total-sum criteria for
`L(W)` and `S(W)` are checked over `ℤ[i]`. The expansion gives irreducibility, trace
orthogonality gives projective faithfulness, and `P_W v = (Σ v_i / 4)(1, 1, 1, 1)` reduces
`L(W)` and `S(W)` to the subgroup `⟨b, c⟩`, which is not normal. -/
theorem result : ¬ claim := by
  intro h
  have hUnitZ : ∀ x : GG, star (piZ x) * piZ x = 1 := by
    set_option maxRecDepth 100000 in decide +kernel
  have hProjZ : ∀ x y : GG, ∃ σ ∈ [(1 : GaussianInt), -1, ⟨0, 1⟩, ⟨0, -1⟩],
    piZ x * piZ y = σ • piZ (x * y) := by
    set_option maxRecDepth 100000 in decide +kernel
  have hTrZ : ∀ x y : GG, x ≠ y → trace (star (piZ y) * piZ x) = 0 := by
    set_option maxRecDepth 100000 in decide +kernel
  have hLZ : ∀ x : GG, (Jz * piZ x = piZ x * Jz) ↔
    (x.2 = DihedralGroup.r 0 ∨ x.2 = DihedralGroup.sr 0) := by
    set_option maxRecDepth 100000 in decide +kernel
  have hSZ : ∀ x : GG, (∑ i, ∑ j, piZ x i j).norm = 16 ↔
    (x.2 = DihedralGroup.r 0 ∨ x.2 = DihedralGroup.sr 0) := by
    set_option maxRecDepth 100000 in decide +kernel
  have hSpanZ : ∀ k l : Fin 4,
      ∑ x : GG, star (piZ x k l) • piZ x = (4 : GaussianInt) • Matrix.single k l 1 := by
    set_option maxRecDepth 100000 in decide +kernel
  have hPW : ∀ v : EuclideanSpace ℂ (Fin 4),
      (Submodule.span ℂ {uu}).starProjection v = Matrix.toEuclideanLin Pm v := by
    intro v
    rw [Submodule.starProjection_singleton]
    have hn : ‖uu‖ ^ 2 = 4 := by
      rw [EuclideanSpace.norm_eq]
      simp [uu]
    have hi : inner ℂ uu v = ∑ i, v i := by
      simp [uu, PiLp.inner_apply]
    rw [hn, hi]
    ext i
    simp [uu, Pm, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
    rw [Finset.sum_div, Finset.sum_congr rfl fun j _ => div_eq_inv_mul (v.ofLp j) 4]
  have hLchar : ∀ M : Matrix (Fin 4) (Fin 4) ℂ,
      (∀ v, (Submodule.span ℂ {uu}).starProjection (Matrix.toEuclideanLin M v) =
      Matrix.toEuclideanLin M ((Submodule.span ℂ {uu}).starProjection v)) ↔
        Pm * M = M * Pm := by
    intro M
    simp only [hPW]
    constructor
    · intro h
      apply Matrix.toEuclideanLin.injective
      ext1 v
      simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
      exact h v
    · intro h v
      have := congrArg (fun A => Matrix.toEuclideanLin A v) h
      simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply] using this
  have hPMP : ∀ M : Matrix (Fin 4) (Fin 4) ℂ,
      Pm * M * Pm = ((∑ i, ∑ j, M i j) / 4) • Pm := by
    intro M
    ext i j
    simp only [Pm, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hSchar : ∀ M : Matrix (Fin 4) (Fin 4) ℂ,
      (∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, (Submodule.span ℂ {uu}).starProjection
      (Matrix.toEuclideanLin M ((Submodule.span ℂ {uu}).starProjection v)) =
        c • (Submodule.span ℂ {uu}).starProjection v) ↔
        ‖(∑ i, ∑ j, M i j) / 4‖ = 1 := by
    intro M
    simp only [hPW]
    have key : ∀ c : ℂ, (∀ v, Matrix.toEuclideanLin Pm (Matrix.toEuclideanLin M
        (Matrix.toEuclideanLin Pm v)) = c • Matrix.toEuclideanLin Pm v) ↔
        (∑ i, ∑ j, M i j) / 4 = c := by
      intro c
      have e : ∀ v,
          Matrix.toEuclideanLin Pm (Matrix.toEuclideanLin M (Matrix.toEuclideanLin Pm v)) =
          ((∑ i, ∑ j, M i j) / 4) • Matrix.toEuclideanLin Pm v := by
        intro v
        have := congrArg (fun A => Matrix.toEuclideanLin A v) (hPMP M)
        simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply,
          map_smul, LinearMap.smul_apply] using this
      simp only [e]
      constructor
      · intro h
        have h1 := congrArg (fun w : EuclideanSpace ℂ (Fin 4) => w.ofLp 0) (h uu)
        simp [Pm, uu, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct] at h1
        exact h1
      · intro h v
        rw [h]
    constructor
    · rintro ⟨c, hc, h⟩
      rw [(key c).mp h]; exact hc
    · intro h
      exact ⟨_, h, (key _).mpr rfl⟩
  have hmap : ∀ A B : Matrix (Fin 4) (Fin 4) GaussianInt,
      (A * B).map GaussianInt.toComplex =
        A.map GaussianInt.toComplex * B.map GaussianInt.toComplex :=
    fun A B => Matrix.map_mul
  have hstar : ∀ A : Matrix (Fin 4) (Fin 4) GaussianInt,
      (star A).map GaussianInt.toComplex = star (A.map GaussianInt.toComplex) := by
    intro A; ext i j; simp [Matrix.star_apply, GaussianInt.toComplex_star]
  have hinj : Function.Injective (fun A : Matrix (Fin 4) (Fin 4) GaussianInt =>
      A.map GaussianInt.toComplex) := Matrix.map_injective GaussianInt.toComplex_injective
  -- unitary
  have hunit : ∀ x, star (piC x) * piC x = 1 := by
    intro x
    rw [piC, ← hstar, ← hmap, hUnitZ x]
    simp
  -- projective relation
  have hproj : ∀ x y, ∃ c : ℂ, ‖c‖ = 1 ∧ piC x * piC y = c • piC (x * y) := by
    intro x y
    obtain ⟨σ, hσ, he⟩ := hProjZ x y
    refine ⟨GaussianInt.toComplex σ, ?_, ?_⟩
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hσ
      rcases hσ with rfl | rfl | rfl | rfl <;> simp [GaussianInt.toComplex_def']
    · rw [piC, piC, ← hmap, he]
      ext i j; simp [piC]
  -- trace orthogonality
  have htr : ∀ x y, x ≠ y → trace (star (piC y) * piC x) = 0 := by
    intro x y hxy
    rw [piC, piC, ← hstar, ← hmap]
    have := hTrZ x y hxy
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply] at this ⊢
    rw [← map_sum, this, map_zero]
  have hfaith : ∀ x y, (∃ c : ℂ, piC x = c • piC y) → x = y := by
    rintro x y ⟨c, hc⟩
    by_contra hxy
    have h1 := htr x y hxy
    rw [hc, Matrix.mul_smul, hunit, Matrix.trace_smul, Matrix.trace_one] at h1
    simp at h1
    have h2 := hunit x
    rw [hc, h1, zero_smul, mul_zero] at h2
    exact absurd (congrFun (congrFun h2 0) 0) (by simp)
  -- irreducibility
  have hspan : ∀ k l : Fin 4, Matrix.single k l (1 : ℂ) =
      (1 / 4 : ℂ) • ∑ x : GG, star (piC x k l) • piC x := by
    intro k l
    have := congrArg (fun A => A.map GaussianInt.toComplex) (hSpanZ k l)
    ext i j
    have hij := congrFun (congrFun this i) j
    simp [Matrix.sum_apply, piC, GaussianInt.toComplex_star, Matrix.single_apply] at hij ⊢
    rw [hij]
    split_ifs
    · rw [map_ofNat]; norm_num
    · rw [map_zero, mul_zero]
  have hirr : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin 4)),
      (∀ x, ∀ v ∈ U, Matrix.toEuclideanLin (piC x) v ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    by_cases hb : U = ⊥
    · exact Or.inl hb
    right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    have hvl : ∃ l, v.ofLp l ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hv0 (by ext i; simp [hno i])
    obtain ⟨l, hl⟩ := hvl
    have hE : ∀ k, Matrix.toEuclideanLin (Matrix.single k l (1 : ℂ)) v ∈ U := by
      intro k
      rw [hspan, map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply]
      refine U.smul_mem _ (U.sum_mem fun x _ => ?_)
      rw [map_smul, LinearMap.smul_apply]
      exact U.smul_mem _ (hU x v hv)
    have hbasis : ∀ k, EuclideanSpace.single k (1 : ℂ) ∈ U := by
      intro k
      have hk := U.smul_mem (v.ofLp l)⁻¹ (hE k)
      convert hk using 1
      ext i
      simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.single_apply]
      rcases eq_or_ne i k with rfl | hik
      · simp [hl]
      · simp [hik, Ne.symm hik]
    rw [eq_top_iff, ← (EuclideanSpace.basisFun (Fin 4) ℂ).toBasis.span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    simpa using hbasis k
  have hPEM : IsPEM piC := ⟨⟨fun x => Matrix.mem_unitaryGroup_iff'.mpr (hunit x), hproj⟩,
    hfaith, hirr⟩
  -- the logical operators and stabilizers of W = ℂ(1,1,1,1)
  set W : Submodule ℂ (EuclideanSpace ℂ (Fin 4)) := Submodule.span ℂ {uu} with hW
  set H : Finset GG :=
    Finset.univ.filter fun x => x.2 = DihedralGroup.r 0 ∨ x.2 = DihedralGroup.sr 0
  have hPmJ : Pm = (1 / 4 : ℂ) • Jz.map GaussianInt.toComplex := by
    ext i j; simp [Pm, Jz]
  have hL : logicalOps piC W = ↑H := by
    ext x
    simp only [logicalOps, Set.mem_ofPred_eq, hW, hLchar, H, Finset.coe_filter, Finset.mem_univ,
      true_and]
    rw [← hLZ x, hPmJ, Matrix.smul_mul, Matrix.mul_smul, piC, ← hmap, ← hmap]
    constructor
    · intro he
      apply hinj
      have := congrArg (fun A => (4 : ℂ) • A) he
      simpa [smul_smul] using this
    · intro he; rw [he]
  have hS : stabilizers piC W = ↑H := by
    ext x
    simp only [stabilizers, Set.mem_ofPred_eq, hW, hSchar, H, Finset.coe_filter, Finset.mem_univ,
      true_and]
    rw [← hSZ x]
    have hsum : ∑ i, ∑ j, piC x i j = GaussianInt.toComplex (∑ i, ∑ j, piZ x i j) := by
      simp [piC, map_sum]
    rw [hsum, norm_div, Complex.norm_ofNat, div_eq_one_iff_eq (by norm_num)]
    have hn := GaussianInt.intCast_real_norm (∑ i, ∑ j, piZ x i j)
    constructor
    · intro h4
      have : Complex.normSq (GaussianInt.toComplex (∑ i, ∑ j, piZ x i j)) = 16 := by
        rw [Complex.normSq_eq_norm_sq, h4]; norm_num
      rw [← hn] at this
      exact_mod_cast this
    · intro h16
      have : Complex.normSq (GaussianInt.toComplex (∑ i, ∑ j, piZ x i j)) = 16 := by
        rw [← hn, h16]; norm_num
      rw [Complex.normSq_eq_norm_sq] at this
      nlinarith [norm_nonneg (GaussianInt.toComplex (∑ i, ∑ j, piZ x i j))]
  have hH : H.card = 4 := by decide
  have hcard : Fintype.card GG = 4 ^ 2 := by decide
  have hprod : (logicalOps piC W).ncard * (stabilizers piC W).ncard = Fintype.card GG := by
    rw [hL, hS, Set.ncard_coe_finset, hH, hcard]
    norm_num
  have hs : ((1 : Multiplicative (ZMod 2)), DihedralGroup.sr 0) ∈ stabilizers piC W := by
    rw [hS, Finset.mem_coe]; decide
  have hn := h 4 GG piC W hPEM hcard hprod ((1 : Multiplicative (ZMod 2)), DihedralGroup.r 1) _ hs
  rw [hS, Finset.mem_coe] at hn
  revert hn
  decide

#print axioms claim
#print axioms result

end D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer
