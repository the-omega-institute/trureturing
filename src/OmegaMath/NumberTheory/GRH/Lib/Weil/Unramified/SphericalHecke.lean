import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.CommonEigenvectors
import OmegaMath.NumberTheory.GRH.Lib.Weil.Unramified.HeckeGL
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Commutativity of the spherical Hecke algebra of GL_n; Eichler commutation relation
(known result; see Lib.General.LinearAlgebra.ColumnLattices).

This file: Spherical Hecke operators at split places commute, are adjoint, and are simultaneously
diagonalisable. Weights, Hecke polynomials, eigenforms, labels and expected Hodge-Tate jumps. Hecke
polynomial at a split place, as operator; spherical eigenvectors. Lifts of finite reductions to K;
action of normalising finite group on level vectors. -/

section

open Matrix NumberField Gf Set RingHom Polynomial
variable {n A W W' E : Type*} [Fintype n] [Field E] [NumberField E] [IsCMField E] [CommRing A]
  [AddCommGroup W] [Module A W] [AddCommGroup W'] [Module A W'] {w u : FinPlace E}
  (π : Representation A (Gf E n) W) {π' : Representation A (Gf E n) W'} {v : W} (hw : w.IsSplit)
  (hu : _ ≠ u) (i : ℕ) (j : ℕ)

variable (n w) in
/-- The subgroup of K₀ of elements whose components away from w and w̄ are 1. -/
noncomputable abbrev maxCompactAt := Kf .. ⊓ supportedOn n {w}

/-- The Hecke operator T_{w,j} at a split place w: the operator of the double coset of diag(ϖ
1_j, 1), GL_n(E_w) acting through `atSplit`. -/
noncomputable def heckeSplit := heckeGL (π.comp (atSplit hw)) j

/-- For a representation π of G_f, the vectors spherical at w: those fixed by all elements of K₀
whose components away from w and w̄ are 1. -/
noncomputable abbrev sphericalAt w := levelSpace π (maxCompactAt n w)

variable {π} {σ : A →+* A} {Z : Type _} [AddCommMonoid Z] [Module A Z] (B : W →ₛₗ[σ] W' →ₗ[A] Z)
  {v' : W'} (hv : v ∈ sphericalAt π w)

lemma FinPlace.IsSplit.star : w.IsSplit → (Star.star w).IsSplit := star_injective.ne

lemma Gf.supportedOn_star : supportedOn n {star w} = supportedOn n {w} := by aesop

/-- For a finite set S of places containing neither w nor w̄, every vector of π fixed by the
elements of K₀ with component 1 at all places of S is spherical at w. -/
lemma levelSpace_le_sphericalAt {S : Finset _} : w ∉ S → star w ∉ S →
  levelSpace π (Kf .. ⊓ trivialOn n S) ≤ sphericalAt π w := by aesop_cat

lemma mem_sphericalAt_iff : v ∈ sphericalAt π w ↔ v ∈ levelSpace (π.comp (atSplit hw)) (Kw ..) := by
  simp [inf_comm (Kf ..), ← range_atSplit hw]

lemma map_heckeSplit (L : W →ₛₗ[σ] W') (hL : ∀ g ∈ supportedOn n {w}, L (π g v) =
  π' g (L v) := by tauto) : L (heckeSplit π hw j v) = heckeSplit (A :=
  A) π' hw j (L v) := by simp [heckeSplit, heckeGL, heckeFun_sum, map_indicator, *]

@[local simp] lemma heckeSplit_comm_of_trivialOn {g} (hg : g ∈ trivialOn n {w}) :
  π g (heckeSplit π hw j v) = heckeSplit π hw j (π g v)
  := map_heckeSplit _ _ _ fun _ h ↦ congr($((commute_supportedOn_trivialOn h hg).map π) v).symm

include hv

/-- For w split and v fixed by the maximal compact group at w, w̄, T_{w̄,j} v is the action on
v, through GL_n(E_w) at w, of the function g ↦ indicator of the double coset of diag(ϖ 1_j,
1) at g⁻¹. -/
lemma heckeSplit_star : heckeSplit π hw.star j v =
  heckeFun (π.comp (atSplit hw)) (Kw ..) ((basicDoubleCoset n w j).indicator 1
  ·⁻¹) v := have R := (range_atSplit hw.star).trans (supportedOn_star.trans (range_atSplit hw).symm)
  heckeFun_comp ((atPlace w).comp (atSplit hw.star)) (by simp) ((mem_sphericalAt_iff _).1 hv) (by
    simp) (R.ge ⟨·, rfl⟩ |>.imp (by aesop)) (by simp [← atPlace_star_mem_iff]) (R.le ⟨·, rfl⟩ |>.rec
  fun _ ↦ (by simp [← ·])) (by simp [basicDoubleCoset, ← map_inv, indicator,
    atPlace_star (star_star _), -coe_units_inv, ← mapMatrix_apply, ← map_det]; aesop)

lemma heckeSplit_dual {ϖ} : Valued.v ϖ.1 = .exp (-1) → Fintype.card n = i + j →
  π (atSplit hw (.scalar n ϖ)) (heckeSplit π hw.star i v) = heckeSplit π hw j v :=
  heckeSplit_star hw _ hv ▸ heckeGL_dual ((mem_sphericalAt_iff _).1 hv)

lemma heckeSplit_comm_of_atPlace_mem {g} (hg : g.atPlace w ∈ Kw ..) : heckeSplit π hw j (π g v) =
  π g (heckeSplit π hw j v) := by
  rw [← div_mul_cancel g (atSplit hw (g.atPlace w)), map_mul, mem_sphericalAt_iff hw] at *
  have : heckeSplit π hw j v ∈ _ := (isBiInvariant_basicDoubleCoset j).heckeFun_mem hv; simp_all

/-- The adjoint of T_{w,j} is T_{w̄,j}: for w split, v, v' fixed by the part of K₀ at w, w̄, and
B a G_f-invariant pairing, σ-semilinear in the first variable, B(T_{w,j}v, v') = B(v,
T_{w̄,j}v'). -/
lemma heckeSplit_adjoint (hv' : v' ∈ sphericalAt π' w) (hB : ∀ g x y, B (π g x) (π' g y) = B x y) :
    B (heckeSplit π hw j v) v' = B v (heckeSplit (A := A) π' hw.star j v') := by apply
  ((isBiInvariant_basicDoubleCoset j).heckeFun_adjoint B _ _ ((mem_sphericalAt_iff _).1
  hv')).2.trans <;> simp [heckeSplit_star, *, indicator, ↓← mem_sphericalAt_iff]

/-- Let w be split, v spherical at w, K a subgroup of K₀ and χ a character of K. Then T_{w,j} maps
v, of level (K, χ), to a vector of level (K, χ). -/
lemma heckeSplit_mem_levelSpace {K χ} (hK : K ≤ Kf ..) (h : v ∈ levelSpace π K χ) :
  heckeSplit π hw j v ∈ levelSpace π K χ := by
  simp_all [← heckeSplit_comm_of_atPlace_mem, LE.le, mem_Kf_iff, -mem_supportedOn]

/-- For split places w and u and a vector v fixed by the maximal compact groups at w, w̄ and at
u, ū, the Hecke operators commute on v: T_{w,i} T_{u,j} v = T_{u,j} T_{w,i} v. -/
lemma heckeSplit_comm (hv' : v ∈ sphericalAt π u) : heckeSplit π hw i (heckeSplit π hu j v) =
  heckeSplit π hu j (heckeSplit π hw i v) := by
  obtain ⟨h, _ | rfl | rfl⟩ := (mem_sphericalAt_iff hw).1 hv, em' (w = u ∨ star w = u)
  exacts [map_heckeSplit _ _ _ (by simp_all), (isBiInvariant_basicDoubleCoset i).heckeFun_comm
    (isBiInvariant_basicDoubleCoset j) h, by simpa [↓heckeSplit_mem_levelSpace, heckeSplit_star, *]
    using! ((isBiInvariant_basicDoubleCoset i).heckeFun_comm ((isBiInvariant_basicDoubleCoset
    j).heckeFun_adjoint (0 : _ →ₗ[A] _ →ₗ[A] A) h (by simp) h).1 h)]

omit hv

/-- Spectral theorem for Hecke operators: in a unitary representation of G_f, a
finite-dimensional subspace U that is spherical at a conjugation-stable set of split places
w and stable under all T_{w,j} there is spanned by joint eigenvectors of these operators. -/
lemma IsUnitary.le_span_hecke_eigenvectors [Module ℂ W] {π B} (hB : IsUnitary π B) {p} (hp : ∀ w,
  p w → w.IsSplit ∧ p (star w)) {U : Submodule ℂ W} [Module.Finite ℂ U] (hU : ∀ w : FinPlace E,
  p w → U ≤ levelSpace π (maxCompactAt n w)) (h : ∀ w h j, ∀ x ∈ U,
  heckeSplit π (hp w h).1 j x ∈ U) : U ≤ .span ℂ {x ∈ U | ∃ c : Subtype p × ℕ
  → ℂ, ∀ i, heckeSplit π (hp _ i.1.2).1 i.2 x = c i • x} := U.comap_subtype_eq_top.1 (Not.imp_symm
  (exists_eigenvector_of_commute _ (fun i ↦ h _ (hp _ i.1.2).2 i.2) (by grind [heckeSplit_comm,
  IsConcreteLE.le_iff])) fun ⟨c, H, _⟩ ↦ H fun x a ↦ Submodule.subset_span ⟨x.2, star c,
    fun ⟨⟨w, o⟩, i⟩
  ↦ ((by simpa using a :) _ o i).elim (·.rec (by simp) (fun _ r x s ↦ sub_eq_zero.1 ((hB.1 _ ·
  |>.1.ne).mtr (by simp [heckeSplit_adjoint _ i B _ (hU w o _) hB.2, heckeSplit_comm, ↓hU _ _ _,
  hp w o, *, by simpa [sub_eq_iff_eq_add] using r _ s]; ring))) x)⟩)

/-- Weights: at each infinite place of E, the number of columns of each height of a Young
diagram, and an integer exponent of the determinant. -/
abbrev Weight (E : Type) [Field E] := (InfinitePlace E → ℕ → ℕ) × (InfinitePlace E → ℤ)

/-- For natural numbers q, N and a sequence t in a commutative ring, the polynomial Σ_{j=0}^{N}
(−1)^j q^{j(j−1)/2} t_j X^{N−j}. -/
noncomputable def heckePoly {R : Type} [CommRing R] (q N : ℕ) (t : ℕ → R) := ∑ j ∈ .range (N + 1), C
    ((-1) ^ j * q ^ j.choose 2 * t j) * X ^ (N - j)

variable {E n M : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] (f : Gf E n → M → ℂ)

/-- At the split place w, K_w fixes f, each Hecke operator T_{w,j} acts on f by a scalar t_j,
and P = Σ(−1)^j q_w^{j(j−1)/2} t_j X^{n−j}. -/
def HasHeckePolyAt w (hw : _ ≠ w) (P : ℂ[X]) :=
  f ∈ levelSpace (rightRegular ℂ ..) (maxCompactAt n w) ∧ ∃ t, P = heckePoly w.q
  (Fintype.card n) t ∧ ∀ j, heckeSplit (rightRegular ℂ ..) hw j f = t j • f

/-- f is an eigenform for the system P: f ≠ 0, and almost all places w of prime norm are split
with f of Hecke polynomial P(w) there (`HasHeckePolyAt`). -/
def IsEigenform (P : _ → _) := f ≠ 0 ∧ ∀ᶠ w in .cofinite, w.q.Prime → ∃ hw,
  HasHeckePolyAt f w hw (P w)

/-- f is nonzero, fixed by the integral points trivial at S, and has Hecke polynomial P(w) at
every split w with w, w̄ ∉ S. -/
def IsSphericalOff (S : Finset _) f (P : FinPlace E → _) := f ≠ 0 ∧ (∀ k ∈ Kf .. ⊓ Gf.trivialOn n S,
  rightRegular ℂ _ (M → ℂ) k f = f) ∧ ∀ w hw, w ∉ S → star w ∉ S → HasHeckePolyAt f w hw (P w)

/-- At the split place w, GL_n(O_w) translates f through GL_n(k_w), and the element Σ Ξ̄(x) x of
the group algebra does not kill f. -/
def HasLabel {w} (hw : _ ≠ w) (Ξ : _ → ℂ) :=
  (∀ k, reduceGL k = 1 → rightRegular ℂ _ _ (atSplit hw k.1) f = f) ∧ ∑ᶠ x,
  star (Ξ x) • rightRegular ℂ _ _ (atSplit hw (Function.surjInv reduceGL_surjective x).1) f ≠ 0

/-- The multiset, over 1 ≤ j ≤ N, of j − 1 − λ_j if σ = Φ_v, else λ_j + N − j; v the place of σ,
λ_j = κ.2 v + ∑_{j≤h<N} κ.1 v h. -/
noncomputable def jumps {E : Type} [Field E] [CMType E] (κ : Weight E) N σ :=
  (Multiset.range N).map fun j ↦ let u := κ.2 (.mk σ) + ∑ h ∈ .Ioo j N, κ.1 (.mk σ) h + (N - 1 - j)
  ite (σ = Φ (.mk σ)) (N - 1 - u) u

variable (n : Type _) {W E : Type _} [Fintype n] [AddCommGroup W] [Module ℂ W] [Field E]
  [NumberField E] (w : FinPlace E) (t : ℕ → W) (X : ℂ)

/-- For a sequence t_i in a complex vector space and X ∈ ℂ, the sum ∑_{i=0}^{n} (−X)^i
q^{binom(i,2)} t_i, with q the norm of w. -/
noncomputable def heckePolyEval := ∑ i ∈ .range (Fintype.card n + 1),
  ((-X) ^ i * w.q ^ i.choose 2) • t i

variable {n} [NumberField.IsCMField E] (π : Representation ℂ (Gf E n) W) {w : FinPlace E} (hw :
  _ ≠ w)

/-- The Hecke polynomial at w as an operator on π: X ↦ ∑_{i=0}^{n} (−X)^i q^{binom(i,2)}
T_{w,i}, with q the norm of w. -/
noncomputable def heckePolyOp := heckePolyEval n w (heckeSplit π hw)

/-- The vector y is fixed by the part of K₀ above w and w̄, and the Hecke polynomial
`heckePolyOp` at each X ∈ ℂ acts on it by p(X). -/
def IsSphericalWith (p : _ → ℂ) y := y ∈ sphericalAt π w ∧ ∀ T, heckePolyOp π hw T y = p T • y

end

variable {n ι A W E : Type*} [Fintype n] [Field E] [NumberField E] [NumberField.IsCMField E]
  {w : ι → FinPlace E} [CommRing A] [AddCommGroup W] [Module A W] {π : Representation A (Gf E n) W}
  {H : Subgroup (∀ i, GL n (ResField (w i)))} {χ : H →* A}

lemma levelSpace_levelOf_apply {v} (hv : v ∈ levelSpace π _ (χ.comp (levelOf.reduction ..))) k (x :
  H) (e : Kf.reduceFamily w k = x.1) : π k v = χ x • v := by cases x; aesop (add simp mem_levelOf)

variable [Finite ι] [IsConjApart w] (s : ∀ i, GL n (ResField (w i)))

/-- For distinct places w_i, none conjugate to another or itself, a chosen element of K₀
supported above the w_i and their conjugates whose reductions modulo the w_i are s. -/
@[local grind] noncomputable def liftResidue := (exists_reduceFamily_eq s).choose

lemma liftResidue_mem_supportedOn : (liftResidue s).1 ∈ Gf.supportedOn n (.range w) := by grind

/-- Let E be a CM field and w_i finitely many distinct finite places with w̄_i ≠ w_j for all i,
j. For s in ∏_i GL_n(k_{w_i}), the element `liftResidue` of K₀ attached to s has reductions
modulo the w_i equal to s. -/
@[local simp] lemma reduceFamily_liftResidue : Kf.reduceFamily w (liftResidue s) = s := by grind

lemma apply_liftResidue_eq (v : levelSpace π _ (χ.comp (levelOf.reduction ..))) k {s} (e :
  Kf.reduceFamily w k = s) : π (liftResidue s).1 v =
  π k v := by simpa using congr(π k $(levelSpace_levelOf_apply v.2 (k⁻¹ * _) 1 (by aesop)))

variable (π χ) in
/-- For φ : S → ∏ GL_n(k_{w_i}) normalising H and fixing χ, the representation s ↦ π(`liftResidue`
φ(s)) of S on vectors of level `levelOf` w H and character χ. -/
noncomputable def levelRep {S} [Group S] (φ : S →* _) (h : ∀ s (x : H), ∃ hx, χ ⟨(φ s)⁻¹ * x * φ s,
    hx⟩ = χ x) : Representation A S (levelSpace π _ (χ.comp (levelOf.reduction ..))) :=
  ⟨⟨fun s ↦ (π (liftResidue (φ s))).restrict fun v hv g ↦ by erw [← map_smul, ← (h ..).2,
  ← levelSpace_levelOf_apply hv ((liftResidue (φ s))⁻¹ * ⟨_,
  levelOf_le_Kf g.2⟩ * _)] <;> aesop, by ext; simp [apply_liftResidue_eq _ 1]⟩,
  by intros; ext; simpa using! apply_liftResidue_eq _ (_ * _) (by simp)⟩

open Finset PowerSeries Polynomial Classical NumberField
variable {E n W W' : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] {π : Representation ℂ (Gf E n) W} {w : FinPlace E}
  {p : ℂ → ℂ} {y : W} {π' : Representation ℂ (Gf E n) W'} {hw : _ ≠ w} {σ : ℂ →+* ℂ}
  (L : W →ₛₗ[σ] W')

attribute [local simp] heckeGL heckePolyOp heckePolyEval IsSphericalWith mul_smul

lemma isSphericalWith_of_heckeSplit (hy : y ∈ sphericalAt π w) {t} (h : ∀ i, heckeSplit π hw i y =
  t i • y) : IsSphericalWith π hw (heckePolyEval n w t) y := by simp_all [sum_smul]

lemma IsSphericalWith.smul {a : ℂ} (h : IsSphericalWith π hw p y) :
  IsSphericalWith π hw p (a • y) := by simp_all [smul_comm a]

lemma map_heckePolyOp T (hL : ∀ g ∈ Gf.supportedOn n {w}, L (π g y) = π' g (L y) := by tauto) :
    L (heckePolyOp π hw T y) = heckePolyOp π' hw (σ T) (L y) := by simp [map_heckeSplit _ _ L hL]

/-- Let w be split and B a G_f-invariant pairing of π and π', σ-semilinear in the first
variable. On vectors spherical at w, the adjoint of the Hecke polynomial H_w(X) is
H_{w̄}(σX): B(H_w(X)y, z) = B(y, H_{w̄}(σX)z). -/
lemma heckePolyOp_adjoint (hw : w.IsSplit) {Z} [AddCommGroup Z] [Module ℂ Z] {z} (B :
  W →ₛₗ[σ] W' →ₗ[ℂ] Z) (hy : y ∈ sphericalAt π w) (hz : z ∈ sphericalAt π' w) (hB : ∀ g x y,
  B (π g x) (π' g y) = B x y) X : B (heckePolyOp π hw X y) z =
  B y (heckePolyOp π' hw.star (σ X) z) := by simp [← heckeSplit_adjoint (π := π), *]

/-- Let Q be a polynomial over R with Q(0) = 1, r ∈ s. If ∑_{i∈t} U^i b_i = Q(U)∑_{i∈s} U^i a_i
for all complex U, then a_r is the coefficient of X^r in the power series Q(X)⁻¹∑_{i∈t} X^i
b_i. -/
lemma sum_coeff_invOfUnit_smul_eq {R V} [CommRing R] [Algebra R ℂ] [AddCommGroup V] [Module ℂ V] {a
  b : ℕ → V} {s t r} {Q : R[X]} (hQ : Q.coeff 0 = 1) (h : r ∈ s) (H : ∀ U : ℂ, ∑ i ∈ t, U ^ i • b i
  = Q.aeval U • ∑ i ∈ s, U ^ i • a i) : ∑ i ∈ t, algebraMap R ℂ (coeff r (invOfUnit Q 1 * .X ^ i)) •
  b i = a r := Module.eval_apply_injective ℂ (by ext f; simpa [← mul_assoc, mul_sum, mul_comm (f _),
  *, ← PowerSeries.coeff_map, ← RingHom.map_mul] using congr(((invOfUnit Q 1).map (algebraMap R ℂ) *
  coeToPowerSeries.ringHom $((funext (by simpa [eval_finsetSum, mul_comm] using congr(f $(H ·))) :
  ∑ i ∈ t, f _ • .X ^ i = Q.map (algebraMap R ℂ) * ∑ i ∈ s, f _ • .X ^ i))).coeff r))

lemma heckeSplit_mem_of_heckePolyOp (N : Submodule ℂ _) (h : ∀ T, heckePolyOp π hw T ∈ N) i :
  heckeSplit π hw i ∈ N := byCases (by simpa using (@sum_coeff_invOfUnit_smul_eq ℂ _ _ _ _ _ _ 0 _ ∅
  i 1 (by simp) · (fun U ↦ by simpa using (N.ker_mkQ.ge (h (-U))).symm) |>.symm :))
  (by simp_all [heckeSplit, heckeFun, le_card_of_mem_basicDoubleCoset.mt])

/-- At a split place w, for every p there are scalars t_i such that each vector y with Hecke
eigensystem p at w satisfies T_{w,i} y = t_i y for all i. -/
lemma exists_heckeSplit_eq_smul p : ∃ t : ℕ → ℂ, ∀ y, IsSphericalWith π hw p y → ∀ i,
  heckeSplit π hw i y = t i • y := (skolem.1 (heckeSplit_mem_of_heckePolyOp ((LinearMap.id.smulRight
  (@Subtype.val _ (IsSphericalWith π hw p))).range.comap (.pi (.applyₗ ·.1))) fun T ↦
  ⟨_, funext (·.2.2 T |>.symm)⟩)).imp (by simp_all [funext_iff, -IsSphericalWith])
