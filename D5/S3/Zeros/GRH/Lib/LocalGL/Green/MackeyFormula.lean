/- GID: D5/S3/Zeros/GRH/Lib/LocalGL/Green/MackeyFormula
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/LocalGL/Green/MackeyFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.LocalGL.Green.MackeyFormula. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/LocalGL/Green/MackeyFormula.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Groups.IrreducibleCharacters
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Green's characters of GL_n(F_q) and the parabolic-induction ring (known result; see
Lib.LocalGL.Green.LabelDegree).

This file: Similarity classes of matrices, class functions, parabolic induction product, rank parts,
means. Class functions under parabolic induction form a commutative ring; constant one is
invertible. Block means (coproduct), cuspidality, inner product, adjoints, Brauer lift, cuspidal
function. Group order times a central idempotent of the group algebra is a character. Mackey
formula: block means are multiplicative for parabolic induction. -/

noncomputable section

open Submodule ComplexConjugate Fint Fintype Function LinearEquiv LinearMap Module MonoidAlgebra
  Polynomial Quot QuotientAddGroup Ring LinearMap.BilinForm

variable (k) [Field k]

/-- Similarity classes of square matrices over k of all sizes: pairs (n, endomorphism of kⁿ)
modulo intertwining by linear isomorphisms. -/
def SimClass := Quot fun a b : Σ n, End k (Fin n → k) ↦ ∃ e : _ ≃ₗ[k] _, e.conj a.2 = b.2

/-- The complex functions on similarity classes of square matrices over k of all sizes; the
product is induction, (F∗H)(g) = ∑ F(g|W)H(g|V/W) over the g-stable subspaces W. -/
@[implicit_reducible] def Hall := SimClass k → ℂ deriving AddCommGroup, Module ℂ, TopologicalSpace,
    T2Space, IsTopologicalAddGroup

variable {k} {V} [AddCommGroup V] [Module k V] [Module.Finite k V] (g : Module.End k V) (c :
  SimClass k)

/-- The similarity class of an endomorphism g of a finite-dimensional k-vector space V, obtained
by choosing a basis of V. -/
def simClassOf : SimClass k := .mk _ ⟨_, (finBasis ..).equivFun.conj g⟩

@[simp] lemma simClassOf_out : simClassOf c.out.2 = c := (Quot.sound ⟨_, rfl⟩).symm.trans c.out_eq

/-- The subspaces W of V that are stable under the endomorphism g. -/
abbrev StableSubspace := {W : Submodule k V // ∀ x ∈ W, g x ∈ W}

/-- The endomorphism of a g-stable subspace W obtained by restricting g. -/
def StableSubspace.endOnSub {g : End k V} (W : StableSubspace g) : End k W := g.restrict W.2

/-- The endomorphism of the quotient of V by a g-stable subspace W induced by g. -/
def StableSubspace.endOnQuot {g : End k V} (W : StableSubspace g) := W.1.mapQ _ g W.2

/-- The function sending the class of an endomorphism of k^n to the dimension n. -/
abbrev SimClass.dim := c.out.1

/-- The function sending the similarity class of a k-linear endomorphism of k^n to its
characteristic polynomial in k[X]. -/
def SimClass.charpoly : SimClass k → Polynomial k :=
  Quot.lift (·.2.charpoly) fun _ _ ⟨_, h⟩ ↦ by simp [← h]

instance : Mul (Hall k) := ⟨fun f h ↦
  (∑ᶠ W : StableSubspace ·.out.2, f (simClassOf W.endOnSub) * h (simClassOf W.endOnQuot))⟩

/-- The function 𝟙 on similarity classes of square matrices over k that takes the value 1 on
every class, in every size. -/
@[simp] def Hall.constOne : Hall k := fun _ ↦ 1

/-- The function on similarity classes equal to F on classes of dimension n and zero on the
others. -/
@[simp] def Hall.rankPart (n : ℕ) (F : Hall k) : Hall k := fun c ↦ ite (c.dim = n) (F c) 0

instance : One (Hall k) := ⟨.rankPart 0 .constOne⟩

/-- For a complex function F on similarity classes and an invertible matrix g in GL_n(k), the
value of F at the class of the endomorphism g. -/
def Hall.evalGL (F : Hall k) {n} [Fintype n] (g : GL n k) := F (simClassOf g.1.toLin')

variable {k V V' : Type*} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V] [AddCommGroup
  V'] [Module k V'] [Module.Finite k V'] {g : Module.End k V} {g' : End k V'} (e : V
  ≃ₗ[k] V') (g₁ : End k V) {f h : Hall k} (c : SimClass k) (p : V →ₗ[k] _) (hp : ∀ x, p (g x) =
  g' (p x))

lemma simClassOf_eq_iff : simClassOf g = simClassOf g' ↔ ∃ e : V ≃ₗ[k] _, ∀ x, e (g x) =
  g' (e x) := by
  delta simClassOf
  generalize (finBasis k V).equivFun = a, (finBasis k V').equivFun = b
  refine (Equivalence.quot_mk_eq_iff ⟨fun _ ↦ ⟨1, rfl⟩, .imp' .symm ?_, fun ⟨e, _⟩ ↦ .imp' e.trans
    ?_⟩ ..).trans ⟨.imp' (a ≪≫ₗ · ≪≫ₗ b.symm) ?_, .imp' (a.symm ≪≫ₗ · ≪≫ₗ b) ?_⟩ <;>
  simp_all [DFunLike.ext_iff] <;> grind [symm_apply_eq]

lemma simClassOf_eq_of_equiv (h : ∀ x, e (g x) = g' (e x) := by aesop) : simClassOf g =
  simClassOf g' := simClassOf_eq_iff.2 ⟨e, h⟩

lemma exists_equiv_simClassOf_out : ∃ e : _ ≃ₗ[k] V, ∀ x, e ((simClassOf g₁).out.2 x) = g₁ (e x) :=
  simClassOf_eq_iff.1 (simClassOf_out _)

@[simp] lemma dim_simClassOf : (simClassOf g).dim =
  finrank k V := by simp [← (exists_equiv_simClassOf_out g).choose.finrank_eq]

@[simp] lemma charpoly_simClassOf : (simClassOf g).charpoly = g.charpoly := charpoly_conj ..

@[ext] lemma Hall.ext (H : ∀ n (g : End _ (Fin n → k)), f (simClassOf g) = h (simClassOf g)) :
    f = h := funext (simClassOf_out · ▸ H ..)

lemma Hall.mul_apply_eq_zero_of_dim_lt {m n} (F : ∀ c, c.dim < m → f c = 0) (H : ∀ c, c.dim < n →
  h c = 0) c (e : c.dim < m + n) : (f * h) c = 0 := finsum_eq_zero_of_forall_eq_zero fun W ↦ by
    grind [W.1.finrank_quotient_add_finrank, simClassOf_out c, dim_simClassOf]

@[simp] lemma Hall.add_apply : (f + h) c = f c + h c := rfl

@[simp] lemma Hall.zero_apply : (0 : Hall k) c = 0 := rfl

@[simp] lemma Hall.neg_apply : (-f) c = -f c := rfl

@[simp] lemma Hall.smul_apply a c : (a • f) c = a * f c := rfl

@[simp] lemma Hall.one_apply : (1 : Hall k) c = if c.dim = 0 then 1 else 0 := rfl

/-- For endomorphisms a of V and b of W and a linear map x : W → V, the block triangular
endomorphism (w, v) ↦ (bw, xw + av) of W × V. -/
abbrev blockTriangularEnd (a : End k V) (b : End k V') x := (b.prod x).coprod (.prod 0 a)

instance fintypeStableSubspace [Finite k] :
  Fintype (StableSubspace g) := have := @finite_of_finite k V; .ofFinite _

instance fintypeLinearHom [Finite k] : Fintype (V →ₗ[k] V') := @.ofFinite _ (finite_of_finite k)

lemma simClassOf_endOnQuot (hp : ∀ x, p (g x) = g' (p x)) (W : StableSubspace g) (s :
  Surjective p) (h : W = p.ker) : simClassOf W.endOnQuot = simClassOf g' :=
  simClassOf_eq_of_equiv (quotEquivOfEq _ _ h ≪≫ₗ p.quotKerEquivOfSurjective s) (ind hp)

lemma simClassOf_endOnSub (hp : ∀ x, p (g x) = g' (p x)) {U : StableSubspace g'} (i :
  Injective p) (h : p.range = U) : simClassOf U.endOnSub = simClassOf g :=
  (simClassOf_eq_of_equiv (LinearEquiv.ofInjective p i ≪≫ₗ ofEq ..)).symm

/-- For a k-linear map p intertwining g and g', the preimage p⁻¹(W) of a g'-stable subspace W,
as a g-stable subspace. -/
def StableSubspace.comap (U : StableSubspace g') : StableSubspace g := ⟨.comap p U, by aesop⟩

variable {f h : Hall k} (n) (F : Hall k) (H : Hall k)

@[simp] lemma simClassOf_endOnSub_comap (i : p.ker = ⊥) (U : StableSubspace g') (h : U ≤ p.range) :
  simClassOf (StableSubspace.comap p hp U).endOnSub = simClassOf U.endOnSub :=
  simClassOf_eq_of_equiv (comap_equiv_self_of_inj_of_le (ker_eq_bot.1 i) h) (by bound)

variable [Finite k]

lemma StableSubspace.sum_comap (F : _ → ℂ) : ∑ W with p.ker ≤ W.1, F W = ∑ W with W.1 ≤ p.range, F
    (comap p hp W) := by apply Finset.sum_nbij' (⟨.map p ·, by aesop⟩) (comap p _) <;>
  simp_all [comap, comap_map_eq, map_comap_eq, map_le_range]

section

attribute [local simp] Finset.mul_sum Finset.sum_filter Finset.sum_mul injective_id range_eq_top
  finrank_zero_iff mkQ_surjective range_dualMap_mkQ_eq subsingleton_iff_eq_bot
  Subspace.dualCoannihilator_dualAnnihilator_eq Subtype.coe_eq_iff add_mul mul_add

omit [Finite k] in
@[simp] lemma simClassOf_endOnQuot_comap (s : p.range = ⊤) U : simClassOf (StableSubspace.comap p hp
  U).endOnQuot = simClassOf U.endOnQuot := by apply simClassOf_endOnQuot (mkQ _ ∘ₗ p) <;> aesop

/-- For an endomorphism g of a finite-dimensional vector space V over the finite field k, the
induction product satisfies (f ∗ h)(g) = ∑_W f(g|W) · h(g|V/W), the sum over the g-stable
subspaces W of V. -/
@[local simp] lemma Hall.mul_simClassOf : (f * h) (simClassOf g) = ∑ᶠ W : StableSubspace g,
  f (simClassOf W.endOnSub) * h (simClassOf W.endOnQuot) := by simp [HMul.hMul,
  Mul.mul, by simpa using StableSubspace.sum_comap _ (exists_equiv_simClassOf_out g).choose_spec]

/-- An endomorphism is similar to its transpose. -/
lemma simClassOf_eq_dualMap : simClassOf g = simClassOf g.dualMap := let ⟨_, _, _, _, _, ⟨e⟩⟩ :=
    (equiv_directSum_of_isTorsion (AEval.isTorsion_of_finiteDimensional k V g))
  let E := AEval'.of g ≪≫ₗ (e ≪≫ₗ DFinsupp.linearEquivFunOnFintype).restrictScalars k
  have := Finite.pi_iff.1 (.equiv E)
  simClassOf_eq_of_equiv
    (E ≪≫ₗ piCongrRight (fun _ ↦ have L := (@exists_ker_toSpanSingleton_eq_annihilator
      _ _ _ _ _ (compHom _ (R := _ᵈᵐᵃ) (.toOpposite (.id k[X]) .all)) _ _)
    toDual ((mul k _).compr₂ L.choose) (.ofSeparatingLeft (ind fun q h ↦ mul_one q ▸
      (forall_dual_apply_eq_zero_iff ..).1 (congr($(L.choose_spec.le (LinearMap.ext h)) · 1))))) ≪≫ₗ
    lsum ..
    ≪≫ₗ E.dualMap) (by simp [toDual, DFunLike.ext_iff, E, ← AEval'.X_smul_of, -map_smul_of_tower])

instance : CommRing (Hall k) := by
  refine' { mul_assoc := _, .. } <;> intros <;> ext _ g
  any_goals solve | simp [simClassOf_endOnQuot (g' := g) 1 _ ⟨⊥, _⟩ surjective_id rfl,
    simClassOf_endOnSub (g := g) .id]
  have (W : StableSubspace g) := And.intro (StableSubspace.sum_comap (g :=
    W.endOnSub) W.1.subtype (congrFun rfl)) (StableSubspace.sum_comap (g' :=
    W.endOnQuot) W.1.mkQ (by aesop)); simp_all [mul_assoc, Finset.sum_comm]
  congr!; apply simClassOf_endOnQuot ((mkQ _).submoduleComap _) (by tauto) _ (by rintro ⟨⟨⟩⟩; tauto)
  simp [submoduleComap, ker_restrict]; rfl
  nth_rw 2 [simClassOf_eq_dualMap]; simp; apply Finset.sum_nbij' (⟨dualAnnihilator ·, by aesop⟩)
    (⟨dualCoannihilator ·, by grind [mem_dualCoannihilator, g.dualMap_apply]⟩) <;> simp_intro W
  rw [simClassOf_eq_dualMap, mul_comm, simClassOf_eq_dualMap, simClassOf_endOnSub W.1.mkQ.dualMap,
    simClassOf_endOnQuot W.1.subtype.dualMap] <;> aesop

lemma Hall.one_sub_constOne_pow_eq_zero m : ∀ c, c.dim < m → ((1 - constOne : Hall k) ^ m) c = 0 :=
  m.recAux nofun fun _ ↦ (mul_apply_eq_zero_of_dim_lt · (by simp_all [sub_eq_add_neg]))

instance : Algebra ℂ (Hall k) := by apply Algebra.ofModule <;> aesop (add 1% (by ring))

/-- Over a finite field k, the constant function 𝟙 on similarity classes of square matrices of
all sizes is invertible for the induction product. -/
lemma Hall.isUnit_constOne : IsUnit (constOne : Hall k) := ⟨.mkOfMulEqOne _ _
  (@Summable.one_sub_mul_tsum_pow (Hall k) _ _ {continuous_mul := continuous_pi (simClassOf_out
  · ▸ by simp [-simClassOf_out]; fun_prop)} _ _ (Pi.summable.2 (.comp_nat_add (k := ·.dim + 1)
  (by simp +arith [one_sub_constOne_pow_eq_zero])))), sub_sub_self ..⟩

end

/-- For F on similarity classes, the function of two classes a, b averaging F over block upper
triangular endomorphisms with diagonal blocks a, b and arbitrary off-diagonal block. -/
def Hall.blockAverage (F : Hall k) : SimClass k → Hall k :=
  (finMean fun x ↦ F <| simClassOf <| blockTriangularEnd ·.out.2 ·.out.2 x)

/-- The inverse μ of the constant function 1 for the induction product; μ(g) is the Möbius
function μ(0, V) of the lattice of g-stable subspaces of V. -/
abbrev Hall.moebius : Hall k := constOne⁻¹ʳ

/-- The pointwise product F·μ, where μ is the inverse, for the parabolic-induction product, of
the constant class function 1. -/
abbrev Hall.mulMu (F : Hall k) : Hall k := fun c ↦ F c * moebius c

/-- F is cuspidal: its average over block triangular endomorphisms with diagonal blocks a, b
vanishes whenever both a and b have nonzero dimension. -/
def Hall.IsCuspidal (F : Hall k) := ∀ a b, a.dim ≠ 0 → b.dim ≠ 0 → F.blockAverage a b = 0

/-- For n and complex functions F, H on similarity classes, the average over GL_n(k) of the
conjugate of F times H. -/
def Hall.rankInner :=
  @finMean (End k (Fin n → k))ˣ fun g ↦ conj (F (simClassOf g.1)) * H (simClassOf g.1)

/-- The function sending a class a to the mean over b in GL_n(k) of conj F(b) times the block
average `Hall.blockAverage` of H at (a, b). -/
def Hall.skew : Hall k := (F.rankInner n <| H.blockAverage ·)

variable (k) {K} [Field K] [Algebra k K] (η : K → ℂ)

/-- The class function β_η sending an endomorphism to the sum of η over the roots in K of its
characteristic polynomial, counted with multiplicity. -/
@[simp] def Hall.brauerLift : Hall k := (·.charpoly.aroots K |>.map η |>.sum)

/-- The class function C_η = (β_η·μ) ∗ 𝟙: the pointwise product of the eigenvalue sum β_η with
the inverse μ of 𝟙, multiplied in the induction product by the constant function 𝟙. -/
def Hall.greenCuspidal := (brauerLift k η).mulMu * constOne

/-- If e is a central self-adjoint idempotent in the complex group algebra of a finite group G,
then g ↦ |G|·e(g), with e(g) the coefficient of g, is the character of a finite-dimensional
representation of G. -/
lemma IsCentralProj.isChar {G} [Group G] [Finite G] {e : ℂ[G]} (h : IsCentralProj e) :
    IsChar (Nat.card G * e.coeff ·) := isChar_of_mem_virtualChars
  ((irreducible_criteria_of_isClassFunction _ (by simp [h.2])).2.1 fun _ ↦ (·.star.imp' _ fun ρ e ↦
  .trans (by simp [classInner, finMean, ← congrFun e, asAlgebraHom_eq_sum, FDRep.character,
  Finset.sum_div, mul_rotate']) (h.1.map (Representation.asAlgebraHom ρ.ρ)).isProj_range.trace))

attribute [local simp] Hall.blockAverage LinearMap.toMatrix_apply SetLike.ext_iff

variable {k V W : Type*} [Field k] [Finite k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  [AddCommGroup W] [Module k W] [Module.Finite k W] (F : Hall k) (a : End k V) (b : End k W)

lemma Hall.blockAverage_simClassOf : F.blockAverage (simClassOf a) (simClassOf b) =
  finMean (F <| simClassOf <| blockTriangularEnd a b ·) := match exists_equiv_simClassOf_out a,
  exists_equiv_simClassOf_out b with | ⟨e, _⟩, ⟨f, _⟩ => (finMean_equiv
  (f.arrowCongr e).symm.toEquiv fun _ ↦ congrArg F (simClassOf_eq_of_equiv (f.prodCongr e)))

/-- Mackey formula: the block averaging map δ of `Hall.blockAverage` is multiplicative, δ(F * H) =
δF * δH, with the Hall product taken in each of the two variables on the right. -/
lemma Hall.blockAverage_mul (H : Hall k) (a : End k V) (b : End k W) :
  (F * H).blockAverage (simClassOf a) (simClassOf b) = ∑ A : StableSubspace a, (F.blockAverage
  (simClassOf A.endOnSub) * H.blockAverage (simClassOf A.endOnQuot)) (simClassOf b) := by
  let S (P : StableSubspace a × StableSubspace b) := P.2.1.compatibleMaps P.1.1
  let φ : (Σ P, S P × _ ⧸ S P) → Σ x, StableSubspace (blockTriangularEnd a b x) | ⟨⟨A, B⟩, y, s⟩ => ⟨a ∘ₗ s.out - s.out ∘ₗ
                             b + y, StableSubspace.comap (LinearEquiv.skewProd 1 1 s.out).1 (g' := blockTriangularEnd a b y) (by simp; grind)
                             ⟨.prod B A, by aesop⟩⟩
  have : φ.Bijective := ⟨fun ⟨P, _, s⟩ ⟨Q, _, t⟩ h ↦ ?_, fun ⟨_, U, u⟩ ↦ ?_⟩
  simp [mul_simClassOf, ↓blockAverage_simClassOf, finMean, div_mul_div_comm, ← Nat.cast_mul,
    sum_mul_sum, ← sum_prod_type', ← sum_sigma', ← this.sum_comp]
  rw [sum_sigma, Finset.sum_div]; congr with ⟨⟨A⟩, ⟨B⟩⟩
  simp_rw [S, by simpa using (B.compatibleMaps A).card_eq_card_quotient_mul_card, ← card_prod,
    ← finMean_eq]
  refine (congrArg finMean ?_).trans (finMean_comp_surjective (.mk' (fun (⟨y, h⟩, _) ↦
    (y.restrict (id h), B.mapQ A y (id h))) (by clear * -; aesop)) (fun ⟨α, β⟩ ↦ by
    obtain ⟨⟨r, rfl⟩, c, rfl⟩ := projective_lifting_property _ β A.mkQ_surjective, α.exists_extend
    use (⟨A.subtype ∘ₗ c + r ∘ₗ B.mkQ, fun _ ↦ ?_⟩, 0); ext
    all_goals simp_all [(Quotient.mk_eq_zero _).2]) _)
  ext; rw [simClassOf_endOnSub_comap, simClassOf_endOnQuot_comap,
    simClassOf_endOnSub (B.subtype.prodMap A.subtype), simClassOf_endOnQuot (B.mkQ.prodMap A.mkQ)]
    <;> simp [StableSubspace.endOnSub, StableSubspace.endOnQuot, ← ker_eq_bot, ← range_eq_top]
  simp [φ, StableSubspace.comap, Sigma.subtype_ext_iff] at h
  cases show P = Q by ext w; simpa using h.2 0 w; rcases h.2 w (-s.out w), h.2 w (-t.out w); aesop
  simp_all [s.out_equiv_out.1 (leftRel_apply.2 fun _ _ ↦ ((h.2 ..).1 (by simpa)).2)]
  have ⟨r, R⟩ := projective_lifting_property _ .id ((LinearMap.fst ..).submoduleMap_surjective U)
  obtain ⟨t, rfl⟩ := r.exists_extend
  let s := (S ⟨StableSubspace.comap (inr ..) (by simp) ⟨U, u⟩,
    U.map (LinearMap.fst ..), by aesop⟩).mkQ (-LinearMap.snd .. ∘ₗ U.subtype ∘ₗ t)
  have e : (φ ⟨_, 0, s⟩).2 = U := SetLike.ext fun z ↦ (and_congr_right fun h ↦ by
    simpa [Prod.sub_def, (congr($R ⟨_, h⟩) : (t z.1).1.1 = _)] using! U.sub_mem_iff_left
      (x := z) (add_mem (t z.1).2 (QuotientAddGroup.eq.1 s.out_eq h))).trans (by tauto)
  exact ⟨⟨_, ⟨_, fun w h ↦ by simpa [sub_add, ← sub_eq_add_neg] using (e.ge (u (w, -_)
    (e.le ⟨h, by simp⟩))).2⟩, s⟩, Sigma.subtype_ext (add_sub_cancel ..) ‹_›⟩

lemma Hall.blockAverage_of_dim_eq_zero {o} (h : o.dim = 0) a : F.blockAverage o a = F a ∧
  F.blockAverage a o = F a := by
  have := (Fin.cast h).isEmpty; simp [finMean]
  rw [simClassOf_eq_of_equiv .prodUnique, simClassOf_out, simClassOf_eq_of_equiv .uniqueProd,
    simClassOf_out]; simp

omit [Finite k] in
lemma Hall.charpoly_endOnSub_mul_endOnQuot (U : StableSubspace a) :
  U.endOnSub.charpoly * U.endOnQuot.charpoly = a.charpoly := by
  erw [← charpoly_fromBlocks_zero₂₁', ← a.charpoly_toMatrix ((Free.chooseBasis k U).sumQuot
    (Free.chooseBasis ..))]; congr with ⟨⟩ ⟨⟩ <;> simp [U.2, (Quotient.mk_eq_zero _).2] <;> congr
  rw [← Basis.sumQuot_inr]; rfl
