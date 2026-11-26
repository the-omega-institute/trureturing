import GRH.Lib.Adelic.Witt.SpaceOperations
import GRH.Lib.LocalGL.Green.LabelDegree
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Shintani descent for GL_n(F_q), with the lift named (known result; see
Lib.LocalGL.Shintani.ShintaniLifting).

Part of: Green's characters of GL_n(F_q) and the parabolic-induction ring (known result; see
Lib.LocalGL.Green.LabelDegree).

This file: Shintani norm via `IsRootChoice`: descent keeps inner products, commutes with induction;
extension. Frobenius reciprocity for parabolic induction from several diagonal blocks. Shintani
lifts for GL_n: definition, stability under parabolic induction and pointwise operations.
Torus-induced character lifts to the semidirect product; Brauer lift has a virtual lift. Green's
characters with squarefree labels are orthonormal irreducible characters of GL_r(F_q). -/

section

open Finset Function Subgroup ComplexConjugate Fint SemidirectProduct AddMonoidAlgebra ZMod
variable {E E' Γ G G'} [Group E] [Group E'] [Group Γ] [Group G] [Group G'] [Finite E] [Finite E']
  [Finite Γ] [Finite G] [Finite G'] (π : E →* Γ) (σ : Γ)

/-- For every s in E with π(s) = σ and every γ in G with s^{ord σ} = j(γ), h(s) = f(γ). -/
def DescendsOnCoset (j : G → E) (h : E → ℂ) (f : G → ℂ) := ∀ s γ, π s = σ → s ^ orderOf σ = j γ →
  h s = f γ

/-- The number of x in the kernel of π with xtx⁻¹ = s, as a complex number. -/
noncomputable def conjCount s t := ∑ x, ite (π x = 1 ∧ x * t * x⁻¹ = s) (1 : ℂ) 0

/-- Induction of f along ρ over Γ: at s, the index of ker(π∘ρ) times the mean over t ∈ E' of
f(t)·#{x ∈ ker π : xρ(t)x⁻¹ = s}. -/
noncomputable def induceClassFn (ρ : E' →* E) f s :=
  (π.comp ρ).ker.index * classInner (conjCount π s ∘ ρ) f

/-- j is injective and r(γ) is a conjugation-equivariant (ord σ)-th root of j(γ) over σ, such
that any x ∈ ker π conjugating one r(δ) to an r(γ) lies in j(G). -/
@[local grind] structure IsRootChoice (j : G →* E) (r : G → E) where
  injective : Injective j
  pow_eq γ : π (r γ) = σ ∧ r γ ^ orderOf σ = j γ
  map_conj v γ : r (v * γ * v⁻¹) = j v * r γ * (j v)⁻¹
  mem_range_of_conj x γ δ : π x = 1 → x * r δ * x⁻¹ = r γ → x ∈ j.range

variable {π σ} {j : G →* E} {r ρ h g α Y} (R : IsRootChoice π σ j r)

attribute [local simp] classInner mul_sum sum_mul Fintype.sum_prod_type Semiconj mem_centralizer_iff

omit [Finite Γ] in
lemma conjCount_conj {u y} (e : π u = π y) s t : conjCount π (y * s * y⁻¹) (u * t * u⁻¹) =
  conjCount π s t := .symm
  (sum_equiv (.mulLeft y * .mulRight u⁻¹) (by simp) (by simp [e, ← mul_assoc]; simp [mul_assoc]))

lemma induceClassFn_mem_virtualChars {Z} [CommSemiring Z] [Algebra Z ℂ] (o :
  Surjective (π.comp ρ)) (v : h ∈ virtualChars Z E') : induceClassFn π ρ h ∈ virtualChars Z E :=
  (irreducible_criteria_of_isClassFunction _ fun s y ↦ (o (π y)).elim fun x _ ↦ congrArg (_ * ·)
  (finMean_equiv (MulAut.conj x) (by simp_all [conjCount_conj, isClassFunction_of_mem_virtualChars
  v]))).2.1 fun χ c ↦ ((c.comp ρ).exists_classInner_eq v).imp fun _ ↦
  .trans (by simpa [apply_ite conj, o.of_comp (f := π), sum_comm, field, card_filter, conjCount,
  mul_div, induceClassFn, c.isClassFunction, ↓o, ite_and, -sum_boole, finMean, Fintype.card_subtype,
  mul_left_comm, index_ker] using congr($π.ker.index_mul_card * classInner _ h))

attribute [-simp] mk_eq_inl_mul_inr

/-- Let S be an algebra over the finite field k', σ ∈ Gal(k'/k) act on S^× through a
σ-semilinear ring endomorphism, j embed a finite G onto the σ-fixed units. Then `IsRootChoice`
holds for some r : G → S^×⋊Gal(k'/k), r(γ) having S^×-component in every k'-subalgebra
containing j(γ). -/
theorem exists_isRootChoice {k k' S} [Field k] [Field k'] [Algebra k k'] [Ring S] [Finite k']
  [Algebra k' S] {β : Gal(k'/k) →* MulAut Sˣ} {σ} (τ : S →+* S) (hβ : ∀ u, β σ u = τ u) (hτ :
  Semiconj (algebraMap k' S) σ τ) {j : G →* _} (i : Injective j) (f : ∀ u, u ∈ j.range ↔ β σ u =
  u) : ∃ r : _ → _ ⋊[β] _, IsRootChoice rightHom σ (inl.comp j) r ∧ ∀ (B : Subalgebra k' S) γ,
  ↑(j γ) ∈ B → (r γ).1.1 ∈ B := by
  let C := ZMod (.card G); let s := (mapAlgAut k C σ).toRingHom
  let L γ := lift k' S C ⟨⟨(j <| γ ^ ·.toAdd.val), by simp⟩, by simp [C, val_add, pow_add]⟩
  have e γ z : τ (L γ z) = L γ (s z) := by induction z using induction_linear <;>
    simp_all [L, s, Algebra.smul_def, ← hβ, (f _).1, -f]
  have ⟨z, _⟩ := ((isTameAtLevel_gal σ).of_map (θ := s) (algebraMap ..) (by simp [s])
    (by ext <;> simp [s, ← AlgEquiv.coe_pow, ← map_pow, -mapAlgAut_apply])).exists_norm (.inl
    (Module.finite_of_finite k')) ((of ..).toHomUnits (.ofAdd 1)).isUnit (by aesop) (one_dvd _)
  have W γ m : (⟨z.map (L γ), σ⟩ : _ ⋊[β] _) ^ m = ⟨.map (L γ) (∏ i ∈ range m, z.map (s ^ i).1),
    σ ^ m⟩ := by induction m <;> ext <;> simp [pow_succ', prod_range_succ', mul_comm, *]
  have P γ : _ = inl (j γ) := (W γ (orderOf σ)).trans (by
    ext <;> simp_all [L, val_one_eq_one_mod, -map_pow])
  have N {γ} δ u (h : j γ = u * j δ * u⁻¹) : z.map (L γ) = u * z.map (L δ) * u⁻¹ :=
    Units.ext (by simp [L, lift_apply, Finsupp.sum, h, u.conj_pow])
  exact ⟨_, ⟨inl_injective.comp i, (⟨rfl, P ·⟩), fun v γ ↦ by ext <;> simp [(f _).1, N γ (j v)],
    fun | ⟨u, .(1)⟩, γ, δ, rfl, h => ((f u).2
    (by simpa [N _ u (by simpa [P] using congr(($h.symm ^ orderOf σ).1))]
    using congr($h.1))).imp (by bound)⟩, fun _ _ _ ↦ sum_mem (by aesop)⟩

instance : Finite (G ⋊[α] Γ) := .of_equiv _ equivProd.symm

@[simp] lemma finMean_ite (u w : G ⋊[α] Γ → ℂ) : finMean (fun x ↦ ite (x.2 = 1) (u x) (w x)) =
  finMean w + (finMean (u <| inl ·) - finMean (w <| inl ·)) / Nat.card Γ := by simp [↓finMean_equiv
  equivProd.symm, finMean, ite_sub, ← sub_eq_iff_eq_add', ← sum_sub_distrib, field]; rfl

/-- Let Y be a Γ-invariant irreducible character of G, Φ a virtual character of G⋊Γ with
|Γ|⟨Φ,Φ⟩ = ⟨Φ|G,Φ|G⟩+|Γ|−1 and ⟨Y,Φ|G⟩ = 1+|Γ|m, m ∈ ℤ. Then the function equal to Y on G
and Φ off G is an irreducible character of G⋊Γ. -/
lemma IsIrrChar.extend_semidirect (hY : IsIrrChar Y) (hs : ∀ σ g, Y (α σ g) = Y g) {Φ} (v :
  Φ ∈ virtualChars ℤ _) (h1 : Nat.card Γ * classInner Φ Φ =
  classInner (Φ ∘ inl) (Φ ∘ inl) + (Nat.card Γ - 1)) (m : ℤ) (ha : classInner Y (Φ ∘
  inl) = 1 + Nat.card Γ * m) : IsIrrChar fun x : G ⋊[α] Γ ↦ ite (x.2 = 1) (Y x.1) (Φ x) := by
  have ⟨A, n, B⟩ := hY
  apply (irreducible_criteria_of_isClassFunction ℤ _).1 (fun x ↦ ite (x.2 = 1) (Y x.1) 0) _ _ _
    (A.rec (by aesop)) fun χ a z r ↦ ((a.comp inl).exists_classInner_eq A.mem_virtualChars).elim
    fun N b ↦ (a.exists_classInner_eq v).imp' (· - N * m) fun M d ↦ ?_
  iterate 4 simp +contextual [A.isClassFunction, isClassFunction_of_mem_virtualChars v,
    field] at *; grind
  have e g : χ (inl g) = χ 1 / Y 1 * Y g := by
    obtain ⟨r, q⟩ := r (inl g), finMean_equiv (.mulRight g) (congrFun rfl) ▸ congr(conj $(B _
      (a.comp inl).isClassFunction g⁻¹))
    simp [← finMean_conj, ← A.apply_inv, field] at r z q
    grind [B Y A.isClassFunction, finMean_eq, sum_eq_zero]
  simp [*, mul_assoc, field] at *; grind

include R

omit [Finite E] [Finite Γ] [Finite G] in
lemma IsRootChoice.apply_emb_eq_one γ : π (j γ) = 1 := by grind [pow_orderOf_eq_one]

lemma IsRootChoice.classInner_eq_fibre_mean : (∀ s, π s = σ → ∃ x γ, π x = 1 ∧ x * r γ * x⁻¹ = s) ∧
  ∀ {h f g f'}, DescendsOnCoset π σ j h f → DescendsOnCoset π σ j g f' →
  (∀ s x, π x = 1 → h (x * s * x⁻¹) = h s ∧ g (x * s * x⁻¹) = g s) →
  π.ker.index * finMean (fun s ↦ ite (π s = σ) (conj (h s) * g s) 0) = classInner f f' := by
  let i := (j.codRestrict π.ker R.apply_emb_eq_one).range
  obtain ⟨n, o⟩ := (R.pow_eq 1).1 ▸ Nat.card_congr (π.fiberEquivKer _), fun x : π.ker ↦
    π.mem_ker.1 x.2
  have b := @Injective.bijective_of_nat_card_le ((_ ⧸ i) × G) (π ⁻¹' {σ}) _ (fun (x, γ) ↦ ⟨x.out *
    r γ * x.out.1⁻¹, by simp [*, R.pow_eq]⟩) (fun ⟨_, δ⟩ ⟨x, γ⟩ h ↦ by simp_all [
       x.out_equiv_out.1 (QuotientGroup.leftRel_apply.2 ((R.mem_range_of_conj _ γ _ (o _)
    (by simpa [mul_assoc] using congr(x.out⁻¹ * $h.1 * x.out))).imp fun _ ↦ Subtype.ext))]; grind)
    (n ▸ i.index_mul_card ▸ Nat.card_prod _ G ▸ mul_le_mul_right (Finite.card_range_le _) _)
  use (by grind [b.2 ⟨·, ·⟩]); intros
  erw [finMean, finsum_eq_sum_of_fintype, ← sum_filter, sum_subtype _ mem_filter_univ,
    ← b.sum_comp, ← π.ker.index_mul_card, ← n]
  simp [← Fintype.card_of_bijective b, *, finMean, field]; grind [DescendsOnCoset]

omit [Finite E] [Finite Γ] [Finite G] in
lemma IsRootChoice.restrict_subgroup H {H₀} (c : comap j H = H₀) (m : ∀ γ ∈ H₀, r γ ∈ H) :
  IsRootChoice (G := H₀) (π.comp H.subtype) σ (j.restrict c.ge) (⟨_, m _ ·.2⟩) := by constructor <;>
  simp [Injective, ← c, ← SetLike.coe_eq_coe, MonoidHom.restrict] <;> grind [j.mem_range]

lemma IsRootChoice.descendsOnCoset_comp (c : ∀ s x, π x = 1 → g (x * s * x⁻¹) = g s) :
  DescendsOnCoset π σ j g (g ∘ r) := fun s γ q e ↦
  by obtain ⟨x, δ, u, ⟨⟩⟩ := (R.restrict_subgroup (centralizer {j γ}) rfl (by simp_all [← map_mul,
       R.injective.eq_iff, ← R.map_conj, ← mul_inv_eq_iff_eq_mul])).classInner_eq_fibre_mean.1
       ⟨s, by simp [← e, pow_mul_comm']⟩ q
     simp_all [R.pow_eq, mul_inv_eq_iff_eq_mul, x.2 _, R.injective.eq_iff]

lemma DescendsOnCoset.induce (c : IsClassFunction h) ρ₀ {j' : G' →* E'} (e : ∀ γ, ρ (j' γ) =
  j (ρ₀ γ)) {f r'} (S : IsRootChoice (π.comp ρ) σ j' r') (l : DescendsOnCoset (π.comp ρ) σ j' h f)
  {F} (C : IsClassFunction F) (hF : ∀ χ, IsClassFunction χ → classInner F χ =
  classInner f (χ ∘ ρ₀)) : DescendsOnCoset π σ j (induceClassFn π ρ h) F := fun s γ a b ↦ by
  have q t x (m : π x = π 1) :=
    And.intro (conjCount_conj m s t) (conjCount_conj m.symm t); simp [forall_and] at q
  refine .trans congr(_ * finMean $(by simp +contextual [funext_iff, conjCount,
    ne_of_apply_ne π, *])) ((S.classInner_eq_fibre_mean.2 (fun _ δ a _ ↦
    R.descendsOnCoset_comp q.1 _ (ρ₀ δ) a (by grind)) l (by aesop)).trans ?_)
  simpa [fun δ ↦ (R.descendsOnCoset_comp (g := (conjCount π · (r δ))) (by grind) s γ a b).trans
    (Fintype.sum_of_injective j R.injective (fun v ↦ ite (δ = (MulAut.conj v)⁻¹ • γ) 1 0) _
    (by grind [j.mem_range]) (by
    simp [R.apply_emb_eq_one, ← R.map_conj, ↓eq_inv_smul_iff]; grind)).symm, finMean,
    apply_ite conj, -sum_boole, @sum_comm G, ← map_inv, C, -inv_inv] using
    congr(conj $(hF (conjCount π s ∘ r) (by grind [R.apply_emb_eq_one]))).symm

omit R

open Matrix Hall GeneralLinearGroup Fintype Equiv Submodule
variable {k m n ι} [Field k] [Fintype m] [Fintype n] [LinearOrder ι] (b : n → ι)
  (F : ι → Hall k)

lemma simClassOf_submatrix (e : m ≃ n) (M : Matrix n n k) : simClassOf (M.submatrix e e).toLin' =
  simClassOf M.toLin' := simClassOf_eq_of_equiv (.piCongrLeft' _ _ e)

lemma exists_eq_evalGL {Y : GL n k → ℂ} (c : IsClassFunction Y) : ∃ X, Y = Hall.evalGL X :=
  (factorsThrough_iff Y).1 fun _ _ h ↦ by
    cases simClassOf_eq_iff.1 h.symm; convert c _ (toLin.symm (.ofLinearEquiv ‹_›))
    simp_all [← toLin.apply_eq_iff_eq, eq_mul_inv_iff_mul_eq, Units.ext_iff, DFunLike.ext_iff]

/-- Frobenius reciprocity: if each F_a is concentrated in the dimension of block a and Y is a
class function on GL_n(k), the inner product of ∏F_a with Y is the mean over block upper
triangular g of conj(∏F_a(g_a))·Y(g), g_a the diagonal blocks. -/
lemma classInner_evalGL_prod [Finite k] {s} (hs : ∀ i, b i ∈ s) Y : IsClassFunction Y →
  classInner (∏ a ∈ s, (F a).rankPart (Fintype.card {i // b i = a})).evalGL Y =
  classInner (∏ a ∈ s, (F a).evalGL ∘ blockHom b a) (Y ·.1) := (by
  rintro ⟨X, rfl⟩
  induction' s using induction_on_max with m s hm ih generalizing n X
  simp_all [← isEmpty_iff, classInner, Hall.evalGL, simClassOf_eq_of_dim_zero]
  let e := sumCompl (b · = m)
  have h (g : parabolic (R := k) b) := (Matrix.ext fun _ _ ↦ g.2 (by simp [e]; grind) :
    toBlocks₁₂ (g.1.1.submatrix e e) = 0) ▸ fromBlocks_toBlocks _
  have u g := isUnit_fromBlocks_zero₁₂'.1 ((h g).substr (by simp))
  rw [classInner_evalGL, prod_insert, ← card_congr e, card_sum, rankInner_mul_eq_rankInner_skew,
    ← classInner_evalGL, s.prod_congr rfl fun a h ↦ by rw [← card_congr
    (subtypeSubtypeEquivSubtype (· ▸ (hm a h).ne))], ih] <;> try grind [rankPart]
  simp [skew, ← classInner_evalGL, classInner, blockAverage_simClassOf, ← finMean_const_mul,
    ← finMean_prod (Prod.rec _), Hall.evalGL]
  apply finMean_equiv ⟨fun g ↦ (⟨(u g).2.unit, g.2.submatrix⟩, (u g).1.unit,
    (submatrix g.1 e e).toBlocks₂₁.toLin'), fun t ↦ ⟨(by simp : IsUnit (reindex e e (fromBlocks
    t.2.1 0 t.2.2.toMatrix' t.1.1))).unit, blockTriangular_reindex_iff.2 (by
    simp [e, BlockTriangular]; grind [t.1.2 _])⟩, by aesop_cat, by aesop_cat⟩
  simp_intro _ [mul_left_comm, ← mul_assoc, mt (hm m)]; symm; congr!
  exact (simClassOf_submatrix (subtypeSubtypeEquivSubtype (by grind)) _).symm
  rw [← simClassOf_submatrix e, ← h, simClassOf_eq_iff]
  use .sumArrowLequivProdArrow .., by simp [fromBlocks_mulVec]; tauto) ∘ exists_eq_evalGL

variable (k k' Z : Type*) {k₀} {R : _} [Field k] [Field k'] [Field k₀] [Algebra k k']
  [Algebra k₀ k'] [Finite k₀] [CommSemiring Z] [Algebra Z ℂ] [CommRing R] [Algebra R ℂ]
  {F G : Hall k} {F' G' : Hall k'} {σ : Gal(k'/k)} (n : _) [Fintype n]

/-- The action of Gal(k'/k) on GL_n(k') by group automorphisms, applying the field automorphism
to each matrix entry. -/
noncomputable def galActionGL : Gal(k'/k) →* MulAut (GL n k') := .mk' (Units.mapEquiv
    ·.mapMatrix.toMulEquiv) (by tauto)

/-- The semidirect product GL_n(k') ⋊ Gal(k'/k), the Galois group acting on matrix entries. -/
abbrev GalSemidirect := _ ⋊[galActionGL k k' n] _

variable {k k' n} (Φ : GalSemidirect k k' n → ℂ) (X : Hall k₀)

variable (k₀) in
/-- The fixed field of σ ∈ Gal(k'/k) is k₀: the image of k₀ in k' is exactly the set of elements
fixed by σ. -/
abbrev HasFixedField (σ : Gal(k'/k)) := .range (algebraMap k₀ _) = fixedPoints σ

/-- For each σ ∈ Gal(k'/k) with fixed field k₀ and each s over σ in GL_n(k')⋊Gal(k'/k) whose
power s^{ord σ} is γ ∈ GL_n(k₀), Φ(s) = X(γ). -/
def DescendsTo := ∀ σ, HasFixedField k₀ σ →
  DescendsOnCoset rightHom σ (inl <| ·.map (algebraMap ..)) Φ X.evalGL

variable (F F' n)

/-- Some Z-combination Φ of characters of GL_n(k') ⋊ Gal(k'/k) descends, in the sense of
`DescendsTo`, both to F over k and to F' over k'. -/
def HasCommonLift := ∃ Φ ∈ virtualChars Z (GalSemidirect k k' n), DescendsTo Φ F ∧ DescendsTo Φ F'

/-- F lifts to F' over Z: for every m, one Z-combination Φ of characters of GL_m(k')⋊Gal(k'/k)
satisfies `DescendsTo` for both F (over k) and F' (over k'). -/
def Lift := ∀ m, HasCommonLift Z F F' (Fin m)

variable {Φ Z F F' n}

/-- If (F, F') is a lift with coefficients in Z, then for every finite index set n some
Z-combination of characters of GL_n(k')⋊Gal(k'/k) descends (`DescendsTo`) to F over k and to F'
over k'. -/
lemma Lift.exists_descendsTo [Finite k']
    (h : Lift Z F F') n [Fintype n] : HasCommonLift Z F F' n := (h _).rec
  fun _ ⟨v, l⟩ ↦ ⟨_, comp_mem_virtualChars v (SemidirectProduct.map (reindexGL (equivFin
  n)).toMonoidHom (.id _) (by tauto)), by apply l.imp <;> exact fun l σ s _ γ a b ↦ .trans (l σ s _
  (reindexGL _ γ) a (by rw [← map_pow, b]; rfl)) (congrArg _ (simClassOf_submatrix ..))⟩

lemma evalGL_conj : IsClassFunction (F.evalGL (n := n)) := fun _ x ↦
  congrArg F (simClassOf_eq_of_equiv x.toLin.toLinearEquiv).symm

lemma exists_isRootChoice_GL [Finite k']
    (s : HasFixedField k₀ σ) : ∃ r : GL n k₀ → GalSemidirect ..,
  IsRootChoice rightHom σ (inl.comp (GeneralLinearGroup.map (algebraMap ..))) r ∧
  ∀ (B : Subalgebra k' _) γ,
  (γ.map (algebraMap ..)).1 ∈ B → (r γ).1.1 ∈ B := exists_isRootChoice (.mapMatrix σ) (by tauto)
  (by simp [algebraMap, Semiconj]) (by simp [Injective, GeneralLinearGroup.ext_iff]) fun _ ↦ ⟨(·.rec
  (by bound [s.le])), exists_gl_map_eq_of_fixed (σ := σ.toRingHom) (RingHom.injective _) s.ge⟩

attribute [local simp] DescendsTo DescendsOnCoset Hall.evalGL HasCommonLift

@[simp] lemma DescendsTo.iff_comp_inl_eq_evalGL : DescendsTo Φ F' ↔ (Φ <| inl ·) = F'.evalGL :=
  ⟨by bound, fun h σ s ↦ by simp_all [funext_iff, σ.ext (g := 1) (s.le ⟨·, rfl⟩)]⟩

lemma Lift.exists_lift_of_descendsTo [Finite k']
    (h : ∀ m, ∃ Φ ∈ virtualChars Z (GalSemidirect k k' (Fin m)),
  DescendsTo Φ F) : ∃ G : Hall k', Lift Z F G := by
  choose Φ v e using h; choose X x using fun m ↦
    exists_eq_evalGL (isClassFunction_of_mem_virtualChars (comp_mem_virtualChars (v m) inl))
  use fun c ↦ X c.dim c, (⟨Φ ·, by simp_all [funext_iff, -DescendsTo]⟩)

/-- Suppose Gal(k'/k) is trivial, F' on GL_n(k') lies in the Z-span of characters, and F' agrees
with F on GL_n(k). Then some Φ in the Z-span of characters of GL_n(k') ⋊ Gal(k'/k) descends
(`DescendsTo`) to F over k and to F' over k'. -/
lemma exists_descendsTo_of_gal_trivial [Finite k']
    (u : ∀ σ : Gal(k'/k), σ = 1) (h : F'.evalGL ∈ virtualChars Z
  (GL n k')) (e : ∀ g : GL n k, F'.evalGL (g.map (algebraMap ..)) = F.evalGL g) :
  HasCommonLift Z F F' n := ⟨_, comp_mem_virtualChars h (.mk' left (by aesop)), by aesop⟩

/-- If one Z-combination Φ of characters of GL_m(k')⋊Gal(k'/k) descends (`DescendsTo`) to F over k
and to F' over k', then the dimension m parts of F and F' form a lift over Z in all ranks. -/
lemma Lift.rankPart_of_descendsTo {m} (l : HasCommonLift Z F F' (Fin m)) : Lift Z (rankPart m F)
  (rankPart m F') := (eq_or_ne · m |>.rec (·.symm ▸ by simpa) (⟨0, by simp [·]⟩))

lemma Lift.lift_constOne : Lift Z (@constOne k _) (@constOne k' _) := fun _ ↦ by aesop

@[simp] lemma Lift.one : Lift (k := k) (k' := k') Z 1 1 := rankPart_of_descendsTo (lift_constOne 0)

lemma Lift.evalGL_mem_virtualChars [Finite k] (h : Lift Z F G) :
  F.evalGL ∈ virtualChars Z (GL n k) := have ⟨_, v, e⟩ := h.exists_descendsTo n
  DescendsTo.iff_comp_inl_eq_evalGL.1 e.1 ▸ comp_mem_virtualChars v _

lemma Lift.sub (h : Lift R F F') (h' : Lift R G G') : Lift R (F - G) (F' - G') := fun n ↦
  (h' n).rec fun Ψ _ ↦ (h n).imp' (· - Ψ) (by simp_all [sub_eq_add_neg, add_mem]; grind)

variable [Finite k']

/-- Lifting is multiplicative: if F lifts to F' and G lifts to G' with coefficients in Z
(`Lift`), then the parabolic-induction product F * G lifts to F' * G'. -/
lemma Lift.mul [Finite k]
    (h : Lift Z F F') (h' : Lift Z G G') : Lift Z (F * G) (F' * G') := fun m ↦ by
  choose Φ v e f using fun i n (_ : Fintype n) ↦
    (i.rec h' h : Lift Z (cond i F G) (cond i F' G')).exists_descendsTo n
  refine ⟨∑ a ≤ m, induceClassFn rightHom (Subgroup.subtype ⟨⟨⟨left ⁻¹' (parabolic (decide <| ·.1 <
  a)).carrier, @fun x ↦ (·.mul <| ·.map x.2)⟩, by simp⟩, @fun x ↦ .map x.2⁻¹ ∘ (parabolic _).2⟩)
  (∏ i, _ ∘ MonoidHom.mk' (fun ⟨s, h⟩ ↦ ⟨blockHom _ i ⟨_, h⟩, s.2⟩) fun x y ↦ congrArg₂ _ ((blockHom
  ..).2 ⟨_, _⟩ ⟨_, y.2.map x.1.2⟩) rfl), sum_mem fun a _ ↦
    induceClassFn_mem_virtualChars (⟨⟨inr ·, (parabolic _).1.2⟩,
  rfl⟩) (prod_mem fun i _ ↦ comp_mem_virtualChars (v i _ _) _), ?_, ?_⟩ <;> intro σ s t γ p w <;>
  rw [Finset.sum_apply, funext fun a ↦ have ⟨_, R, B⟩ := exists_isRootChoice_GL s
    DescendsOnCoset.induce R (isClassFunction_of_mem_virtualChars (prod_mem fun i _ ↦
      comp_mem_virtualChars (v i _ _) _)) _ (by tauto) (R.restrict_subgroup _ (by
  ext; simp [parabolic, BlockTriangular]) (B (blockTriangularSubalgebra ..) · ∘ .map _))
      (fun _ _ p w ↦ by simp_rw [Finset.prod_apply]; congr!; apply_rules; rw [← map_pow, w]; rfl)
      evalGL_conj (classInner_evalGL_prod
  _ _ (by grind)) t γ p w] <;> simp +contextual [mul_simClassOf, -not_lt, -mul_ite, -Nat.not_lt,
    sum_comm, card_fin_lt_of_le ∘ mem_Iic.1, finrank_quotient, (finrank_le _).trans]

lemma Lift.mulMu [Finite k]
    (h : Lift R F F') : Lift R F.mulMu F'.mulMu := fun m ↦ ((by induction m <;> grind
  [isUnit_constOne, one, sub ‹_› (sub (lift_constOne.mul ‹_›) one)] : Lift R (moebius + (1 -
  constOne) ^ m.succ * -moebius) (moebius + (1 - constOne) ^ m.succ * -moebius)) m).rec fun Φ _ ↦
  (h m).imp' (· * Φ) (by simp_all [mul_mem,
  mul_apply_eq_zero_of_dim_lt (n := 0) (one_sub_constOne_pow_eq_zero _)]; grind)

lemma Lift.rankPart_mulMu_mul_constOne [Finite k]
    {m} (h : Lift R F F') : Lift R ((-1 : ℂ) ^ m • rankPart m
  (F.mulMu * constOne)) ((-1 : ℂ) ^ m • rankPart m (F'.mulMu * constOne)) := by
  obtain ⟨l, _ | _⟩ := rankPart_of_descendsTo (h.mulMu.mul lift_constOne m),
    m.even_or_odd <;> simp [*]
  simpa using (l.sub l).sub l

seal Finset.univ Finset.sum Finset.prod in
lemma exists_norm_char_semidirect {S} [Monoid S] [Finite S] α (ν : S →* ℂ) : ∃ ϑ, IsChar ϑ ∧
  (∀ s : Sˣ ⋊[α] Gal(k'/k), ϑ s
  = ∏ τ, ν (α τ s.1)) ∧ ∀ σ, HasFixedField k σ → DescendsOnCoset rightHom σ inl ϑ (ν ·.1) :=
  ⟨_, isChar_monoidHom ⟨⟨_, by simp⟩, fun a b ↦ by simp [← Equiv.prod_comp (.mulRight a.2) (ν <| α ·
  b.1)]⟩, fun _ ↦ rfl, fun σ s t _ e p ↦ .trans (by
  simp [pow_injOn_Iio_orderOf, ← IsCyclic.image_range_orderOf fun τ ↦
    (IntermediateField.fixingSubgroup_fixedField _).le fun x ↦
    (s.ge (x.2 ⟨σ, 1, rfl⟩)).rec (by bound)]; induction orderOf σ <;> cases e <;>
  simp_all [pow_add, prod_range_succ, ↓← map_pow]) (congrArg (ν ·.1) p)⟩

open Module Algebra TensorProduct LinearMap FiniteField
variable (k k' : Type*) {K L} {m : _} [Field k] [Field k'] [Algebra k k'] [Finite k] [Finite k']
  [Field K] [Algebra k K] [Algebra k' K] [IsScalarTower k k' K] (θ : MulChar K ℂ)
  [Field L] [Finite L] [Algebra k L]

omit [Finite k] in
lemma simClassOf_leftMulMatrix {m : ℕ} {A} [Ring A] [Algebra k A] [Finite A]
  (b : Basis (Fin m) k A) t : simClassOf (leftMulMatrix b t).toLin' = simClassOf (mulLeft k t) :=
  (simClassOf_eq_of_equiv b.equivFun (by simp [leftMulMatrix_mulVec_repr])).symm

attribute [local simp] classInner simClassOf_leftMulMatrix Hall.evalGL leftMulMatrix_eq_repr_mul
  DescendsOnCoset add_eq_zero_iff_neg_eq DescendsTo

seal Finset.univ Finset.sum Finset.prod in
/-- Let [L:k] = m and φ : k'⊗L → K be a k'-algebra map. Some character Φ of GL_m(k')⋊Gal(k'/k)
descends (`DescendsTo`) to C_θ·μ over k, and to every X over k' with ⟨X, B⟩ in rank m the mean
over units t of conj θ(φ(∏_τ τt))·B(t), for all B. -/
lemma exists_torus_induced_descendsTo (r : finrank k L = m) (φ : k' ⊗[k] L →ₐ[k'] K) : ∃ Φ :
  GalSemidirect k k' (Fin m) → ℂ, IsChar Φ ∧ DescendsTo Φ (greenCuspidal k θ).mulMu ∧ ∀ X, (∀ B,
  rankInner m X B = finMean fun t : _ˣ ↦ conj (θ (φ (∏ τ : Gal(k'/k), Algebra.TensorProduct.map
  τ.toAlgHom (.id k L) t.1))) * B (simClassOf (mulLeft k' t.1))) → DescendsTo Φ X := by
  let b := finBasisOfFinrankEq k L r; let B := TensorProduct.basis k' b; have := fintypeOfFintype B
  let g (σ : Gal(k'/k)) := congr σ (1 : Gal(L/k))
  have q σ x j : B.repr (g σ x) j = σ (B.repr x j) := by induction x <;> aesop
  let β := MonoidHom.mk' (Units.mapEquiv <| g · |>.toMulEquiv) (by aesop (add simp B.ext_elem_iff))
  let ⟨ϑ, a, u, w⟩ := exists_norm_char_semidirect β (θ.comp φ)
  refine ⟨induceClassFn _ (SemidirectProduct.map (Units.map (leftMulMatrix B).1.1) (.id _)
    fun σ ↦ by ext; simp [galActionGL, β, ← q, B, g, Units.mapEquiv]) ϑ, isChar_of_mem_virtualChars
    (induceClassFn_mem_virtualChars rightHom_surjective a.mem_virtualChars), fun σ s ↦ .induce
    (exists_isRootChoice_GL s).choose_spec.1 a.isClassFunction (Units.map (leftMulMatrix b).1.1)
    (fun _ ↦ by ext <;> simp [B]) (exists_isRootChoice (g σ) (by tauto) (by tauto)
    (Units.map_injective includeRight.injective) fun x ↦ ⟨by rintro ⟨_, rfl⟩; ext; simp [β, g],
    fun h ↦ ?_⟩).choose_spec.1 (w σ s · <| ·.map _) evalGL_conj fun _ c ↦ (exists_eq_evalGL
    c).choose_spec ▸ classInner_evalGL.trans ?_, fun X h σ s ↦ .induce (exists_isRootChoice_GL
    s).choose_spec.1 a.isClassFunction (·.map (leftMulMatrix B)) (f := ϑ ∘ inl) ?_ (r' :=
    inl) ⟨inl_injective, ?_, ?_, ?_⟩ ?_ evalGL_conj fun _ c ↦
    (exists_eq_evalGL c).choose_spec ▸ classInner_evalGL.trans (by aesop)⟩
  · choose c hc using (s.ge <| q σ x · ▸ congr(B.repr $h _))
    have : 1 ⊗ₜ ∑ i, c i • b i = x.1 := B.ext_elem (by simpa [B, Finsupp.single_apply])
    exact ⟨.mk0 _ (x.ne_zero <| by simp [← this, ·]), Units.ext this⟩
  iterate 5 simp_all [range_inl_eq_ker_rightHom, σ.ext (g := 1) (s.le ⟨·, rfl⟩)]
  simpa [← r, rankInner.eq_1, mul_right_comm, mul_assoc] using
    rankInner_greenCuspidal_mulMu θ ((AlgHom.liftEquiv ..).2 φ) _

/-- Known result: The Brauer lift is a virtual character; cuspidal times Steinberg is induced from a
torus. -/
lemma exists_lift_brauerLift [IsAlgClosed K] : ∃ B : Hall k', Lift ℤ (brauerLift k θ) B :=
  ⟨_, by simpa using ((Lift.exists_lift_of_descendsTo (F := -greenCuspidal k θ) fun m ↦ (m.succ.rec
  ⟨_, _, .lift_constOne, nofun⟩ fun _ ⟨_, _, h, e⟩ ↦ ⟨_, _, .mul ((Lift.exists_lift_of_descendsTo
  (·.casesOn ⟨0, by simp [greenCuspidal_eq_zero_of_dim_lt_one]⟩ fun _ ↦
  (exists_torus_induced_descendsTo _ _ θ (finrank_extension ..)
  ((AlgHom.liftEquiv ..).1 IsAlgClosed.lift)).imp fun _ ↦ .imp (·.mem_virtualChars)
  (·.1))).choose_spec.sub ((h.mul .lift_constOne).sub h).mulMu) .lift_constOne,
  add_mul (brauerLift k θ).mulMu .. ▸ mul_apply_eq_zero_of_dim_lt (n := 0) (by
  peel mul_apply_eq_zero_of_dim_lt e (one_sub_constOne_pow_eq_zero 1); simp_all [sub_eq_add_neg,
    add_mul, mul_add, mulMu]; grind) nofun⟩
  : ∃ J J', Lift (k' := k') ℤ J J' ∧ ∀ c, c.dim < m.succ → (greenCuspidal k θ + J :) c = 0).elim
  fun _ ⟨_, l⟩ ↦ (l.1 m).imp (by aesop)).choose_spec.mul .lift_constOne)⟩

end

open Polynomial Hall Classical
variable {k K n r} [Field k] [Finite k] [Field K] [Algebra k K] (T) [IsFaithfulMulChar K T]
  [Fintype n] {c P : k[X]} (hc : IsLabel r c)

attribute [local simp] skew_mul skew_of_isCuspidal isCuspidal_greenTau rankInner_greenTau IsLabel
  Irreducible.ne_one Monic.def irreducible_X_sub_C

/-- For T injective and χ a multiplicative character of k, the class function attached to the
label X − x_χ equals χ∘det in dimension 1 and zero in other dimensions. -/
lemma labelChar_X_sub_C χ : labelChar T (Polynomial.X - C (charName T χ).1 : k[X]) =
  (detChar χ).rankPart 1 := by
  ext _ g
  have (η : K → ℂ) := mul_apply_eq_zero_of_dim_lt (greenCuspidal_eq_zero_of_dim_lt_one η)
    (one_sub_constOne_pow_eq_zero 1) (simClassOf g)
  simp_all [greenTau, epsilon_singleton, detChar, -map_mul, mul_sub, add_eq_zero_iff_eq_neg,
    ← map_neg, aroots, thetaChar_charName,
    g.charpoly_natDegree, congr(aroots $(g.charpoly_monic.eq_X_add_C _) K)]

include hc

/-- For T injective, a label c of degree r that splits over k is the product of X − x_{χ_i} for
some r multiplicative characters χ_i of k, where x_χ is the element naming χ. -/
lemma IsLabel.exists_eq_prod_of_splits (h : ∀ x : K, aeval x c = 0 → x ^ .card k = x) : ∃ χ :
  Fin r → _, c = ∏ i, (Polynomial.X - C (charName T (χ i)).1) :=
  h |> hc.induction_irreducible_mul K (by bound) fun _ _ _ _ m i z e h _ ↦ (h (by aesop)).imp'
  (Fin.append fun _ ↦ (charName T).symm (-.mk0 _ z)) (by simp +contextual [Fin.prod_univ_add,
  ← m.eq_X_add_C, Nat.dvd_one.1 ((root_pow_card_pow_eq_self_iff i e).1 (by aesop))])

lemma rankPart_labelChar : (labelChar T c).rankPart r = labelChar T c := funext
  (hc.induction_irreducible_mul K (by simp) (by
  intro _ _ _ _ _ _ _ _ _ x; simp_all; exact fun _ ↦ .symm (finsum_eq_zero_of_forall_eq_zero
  fun U ↦ by grind [U.1.finrank_quotient_add_finrank, dim_simClassOf, greenTau_eq_zero_of_dim_ne,
  simClassOf_out x])))

lemma skew_greenTau_labelChar_eq_zero {d e} (i : Irreducible P) : IsLabel e P → e = d → ¬P ∣ c →
    skew d (greenTau T P) (labelChar T c) = 0 := hc.induction_irreducible_mul K (by grind [skew_mul
  (F := 1), isCuspidal_greenTau, i.natDegree_pos, IsLabel]) (by aesop (add simp i.prime.dvd_mul))

lemma rankInner_labelChar_mul_constOne : c.eval 1 ≠ 0 → ∀ A, rankInner r (labelChar T c)
  (A * constOne) = rankInner r (labelChar T c) A := hc.induction_irreducible_mul K
  (by simp [rankInner]) (by simp_all [rankInner_mul_eq_rankInner_skew greenTau_eq_zero_of_dim_ne])

/-- Orthonormality: for T injective and labels c, c' of degree r, the inner product in dimension
r of Ξ_c and Ξ_{c'} is 1 if c = c' and 0 otherwise.

Known result: Green's characters of GL_n(F_q) and the parabolic-induction ring. -/
lemma rankInner_labelChar : ∀ c', IsLabel r c' → rankInner r (labelChar T c) (labelChar T c') =
  ite (c = c') 1 0 := hc.induction_irreducible_mul K
  (by simp_all [rankInner]) fun P _ _ _ _ i _ _ _ c' ↦ by
  obtain _ | ⟨_, rfl⟩ := em' (P ∣ c') <;> simp_all [rankInner_mul_eq_rankInner_skew
    greenTau_eq_zero_of_dim_ne, skew_greenTau_labelChar_eq_zero, squarefree_mul_iff,
    i.ne_zero, i.isRelPrime_iff_not_dvd, natDegree_mul']
  simp [rankInner]; tauto

omit hc in
/-- Green's theorem: for T an injective multiplicative character of the algebraically closed K
and c a label of degree |n|, the class function Ξ_c is an irreducible character of GL_n(k).

Known result: Green's characters of GL_n(F_q) and the parabolic-induction ring. -/
lemma IsLabel.isIrrChar_labelChar (hc : IsLabel (Fintype.card n) c) :
  IsIrrChar ((labelChar T c).evalGL (n := n)) := by
  apply (irreducible_criteria_of_isClassFunction ℤ evalGL_conj).1 (labelChar T c).evalGL evalGL_conj
    _ _ (labelChar_degree_bounds K hc).1 fun _ a _ _ ↦ a.exists_classInner_eq
    (hc.induction_irreducible_mul K ⟨1, by simp⟩ (by
    intros; simp_all; casesm Exists _; exact ⟨_, (exists_lift_brauerLift
    ..).choose_spec.rankPart_mulMu_mul_constOne.mul ‹_›⟩) : Exists (Lift _ (labelChar T
    c))).choose_spec.evalGL_mem_virtualChars <;> grind [rankInner_labelChar, classInner_evalGL]

/-- For T injective and c a label, the class function Ξ_c, the product of the τ_P over the monic
irreducible factors P of c, is in every dimension a combination of characters with natural
number coefficients. -/
lemma lift_labelChar_self : Lift ℕ (labelChar T c) (labelChar T c) :=
  rankPart_labelChar T hc ▸ .rankPart_of_descendsTo (exists_descendsTo_of_gal_trivial
  (by subsingleton) (IsLabel.isIrrChar_labelChar _ (by simpa)).1.mem_virtualChars (by simp))

lemma skew_detChar_labelChar_eq_zero {χ} : c.eval (charName T χ).1 ≠ 0 →
  skew 1 ((detChar χ).rankPart 1) (labelChar T c) = 0 :=
  by simp_all [← labelChar_X_sub_C T, dvd_iff_isRoot, skew_greenTau_labelChar_eq_zero]
