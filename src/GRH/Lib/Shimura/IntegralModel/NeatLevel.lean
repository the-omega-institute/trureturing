import GRH.Lib.General.NumberTheory.QuadFieldSplitting
import GRH.Lib.Adelic.Adeles.OneSidedPoisson
import GRH.Lib.Adelic.Adeles.NormAbsValue
import GRH.Lib.Shimura.TraceFormula.TraceFormula
import GRH.Lib.Adelic.Reduction.MahlerForms
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Integral Kuga–Sato models for GU(1,n−1) with level covers and congruence relation
(known result; see Lib.Shimura.IntegralModel.ModelExistence).

Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number (known
result; see Lib.Shimura.Uniformisation.AppellHumbert).

This file: Marked triples, orbital counts, local embeddings, Hecke operators at split places, local
terms. Frames determine forms, automorphisms are similitudes, levels of large norm are neat. -/

noncomputable section

open NumberField Cardinal Polynomial Classical Module Matrix.GeneralLinearGroup Prod MulAction
section

variable (E : Type) [Field.{0} E] [NumberField E] [IsCMField E] {n : Type} [Fintype.{0} n] {d : ℕ}
  {d₀ : ℕ} [Fact (d % 4 = 3)]

/-- The prime u of ℚ(√−d) contains an element x = (1 + √−d)/2 − b, b ∈ ℤ, that is coprime to its
conjugate x̄. -/
def IsSplitPrimeToDisc (u : FinPlace (QuadField d)) :=
  ∃ b : ℤ, let x := QuadField.c₀ d - b; x ∈ u.1 ∧ IsCoprime x (star x)

/-- Let the place w of K₀ = ℚ(√−d) satisfy `IsSplitPrimeToDisc` and lie above the prime l.
Then the residue field of w has order l, and the places of K₀ above l are exactly w and w̄. -/
lemma IsSplitPrimeToDisc.star_ne_and_prime_norm {w : FinPlace (QuadField d)} : IsSplitPrimeToDisc
  w → w.IsSplit ∧ w.q.Prime ∧ ∀ u, u = w ∨ u = star w ↔ ↑w.q ∈ u.1 := by grind [IsSplitPrimeToDisc,
  =_ mem_star_place, star_natCast, (@QuadField.prime_inert_or_eq_mul _ · _ ⟨·⟩ w),
  → w.2.notMem_of_isCoprime_of_mem, w.1.exists_prime_and_absNorm_eq_pow]

/-- The number d is 3 mod 4, and the field E is an algebra over the imaginary quadratic field
ℚ(i√d). -/
class HasQuadSubfield (d : outParam ℕ) (E : semiOutParam Type) [semiOutParam (Field E)] extends
  Fact (d % 4 = 3), Algebra (QuadField d) E

/-- The finite places w of the CM field E that are split over the maximal real subfield, that
is, differ from their complex conjugate. -/
abbrev SplitFinPlace := {w : FinPlace E // w.IsSplit}

end

variable {E : Type} [Field.{0} E] [CMBase E] {n : Type} [Fintype.{0} n] {d₀ : ℕ}
  [HasQuadSubfield d₀ E] (t : E →+* ℂ) (K : Subgroup (GL n (𝔸f E))) (ε : Prop) (y : GL n E) {ν : ℕ}
  (α : Fin ν → 𝓞 E) (P : E[X]) (μ : ℂ) (k : Type _) [CommRing k] (v : SplitFinPlace E) (𝔑 : 𝓞 E)

/-- A chosen injection from n to ℂ that lists the roots of t(P) if these are |n| distinct
numbers, and is arbitrary otherwise. -/
def numberedRoots : n ↪ ℂ := @epsilon _ (mk_le_aleph0.trans (aleph0_le_mk ℂ))
  fun r ↦ (P.map t).roots = Finset.univ.1.map r

/-- If ε holds, Q(Φ_{v₀}(y)) with Q interpolating 1 at the i-th listed root (`numberedRoots`) of the
characteristic polynomial of y under Φ_{v₀} and −1 at the others; otherwise the identity matrix. -/
def eigenReflection (i : n) := aeval (y.1.map (Φ v₀)) (ite ε
  (Lagrange.interpolate .univ (numberedRoots (Φ v₀) y.1.charpoly) (if · = i then 1 else -1)) 1)

section

variable {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] {n : Type} [Fintype.{0} n]
  (K : Subgroup (GL n (𝔸f E))) (y : GL n E) (v : SplitFinPlace E)

/-- Triples (xK, y, z) of a coset of K in GL_n of the finite adeles, an element y of GL_n(E) and
an element z of a type Z, by default ℂ. -/
def MarkedTriple (Z := ℂ) := (_ ⧸ K) × GL n E × Z

instance {Z} : MulAction (GL n E) (MarkedTriple K Z) := @mulAction _ _ _ _ (.compHom _ toFinGL)
  (@mulAction _ _ _ _ (.compHom _ MulAut.conj) (ofEndHom 1))

/-- For y in GL_n(E) and x in GL_n of the finite adeles of E, the element x⁻¹y⁻¹x of that adelic
group, with y embedded diagonally. -/
abbrev γ x := x⁻¹ * toFinGL y⁻¹ * x

/-- For a split place v, the homomorphism sending g in GL_n(E_v) to the adelic matrix that is
g⁻ᵀ at v, the conjugate of g at v̄, and 1 elsewhere. -/
def conjAtSplit :=
  (@invTransposeGL n _).toMonoidHom.comp (.comp (N := Gf ..) (U 1).subtype (atSplit v.2))

/-- For a split place v, the homomorphism sending an adelic matrix to the inverse transpose of
its component at v; a left inverse of `conjAtSplit` at v. -/
def dualComponent := (@invTransposeGL n _).symm.toMonoidHom.comp (map (evalAt v.1))

end

/-- Cuspidality of χ: for every idempotent matrix ε ≠ 0, 1, χ is non-trivial on the elements of
J lying in the unipotent group 1 + εM_n(1 − ε). -/
def IsCuspidalType {F} [Field F] (J : Subgroup (GL n F)) (χ : J →* ℂ) :=
  ∀ ε, IsIdempotentElem ε → ε ≠ 0 → ε ≠ 1 → ∃ j Y, 1 + ε * Y * (1 - ε) = j.1.1 ∧ χ j ≠ 1

section

variable {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] {n : Type} [Fintype.{0} n] {d₀ : ℕ}
  [HasQuadSubfield d₀ E] (v : SplitFinPlace E)

/-- The norm from E to K₀ = ℚ(√−d₀) of the finite idele that is the chosen uniformiser at v and 1
elsewhere. -/
abbrev unifNorm := (locIdele _ (uniformizer v)).map (adeleNorm (QuadField d₀) E)

/-- The homomorphism sending a finite idele x of K₀ to the scalar matrix x̄·1 in GL_n of the
finite adeles of E. -/
abbrev centralScalar :=
  (scalar n).comp (Units.map ((starRingEnd _).comp (finAdeleIncl (QuadField d₀) E)).1)

end

/-- Safe places w of E: the place u of ℚ(√−d₀) below w satisfies `IsSplitPrimeToDisc`, and 𝔑 lies
neither in w nor in any place above ū. -/
def IsSafe (w : FinPlace E) := IsSplitPrimeToDisc (w.below (QuadField d₀)) ∧ 𝔑 ∉ w.1 ∧
  ∀ v, .below _ v = star (w.below (QuadField d₀)) → 𝔑 ∉ v.1

section

variable {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] {n : Type} [Fintype.{0} n] {d₀ : ℕ}
  [HasQuadSubfield d₀ E] (v : SplitFinPlace E) (𝔑 : 𝓞 E)

/-- The split places of E that are safe for K₀ and the level 𝔑, in the sense of
`IsSafe`. -/
abbrev SafePlace := {w : SplitFinPlace E // IsSafe 𝔑 w}

/-- For a subspace U of k_vⁿ of dimension r, the conjugate of the r-th power of `unifNorm`
at v, inverted, times `conjAtSplit` of the transpose of `basicCosetRep` U. -/
def heckeIsogeny U := centralScalar (n := n) (unifNorm v ^ finrank (ResField v.1)
  (SubmoduleElem U))⁻¹ * conjAtSplit v (transposeGL (basicCosetRep U))

end

variable (n)

section

variable {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] (n : Type) [Fintype.{0} n] {d₀ : ℕ}
  [HasQuadSubfield d₀ E] (k : Type _) [CommRing k] (v : SplitFinPlace E) (𝔑 : 𝓞 E)

/-- The principal level K(𝔑): the similitudes in GL_n(Ô) that are congruent to 1 modulo 𝔑Ô. -/
def levelGU := GU E n ⊓ congruenceGL (Ô E ∙ algebraMap _ _ 𝔑) id

/-- The element τ_{v,j} of the group ring over k: the sum of the elements `heckeIsogeny` over
all j-dimensional subspaces U of k_vⁿ. -/
def heckeSum j := ∑ U with finrank (ResField v.1) (SubmoduleElem U) = j,
  MonoidAlgebra.of k (GL n _) (heckeIsogeny v U)

/-- The Hecke algebra: the subalgebra of elements ∑ a_g [g] of k[G] supported on GUPlus E n whose
function ∑ a_g 1_{gK} is left K-invariant. -/
def heckeAlgebra := (spanOn k (GUPlus E n) ⊓ fixedToEigen (levelGU n 𝔑) (.id _)
  (levelGU n 𝔑)).toSubalgebra ⟨Submodule.subset_span ⟨1, by simp, rfl⟩, by simp [fixedToEigen]⟩
  (by simp_all [fixedToEigen, -mem_levelSpace, spanOn.mul _ _ fun _ h _ ↦ mul_mem h])

end

variable {n 𝔑} (f : heckeAlgebra n ℂ 𝔑) (ω : _ → n → ℂ)

/-- For an element f = ∑ a_g [g] of the Hecke algebra of level 𝔑, the combination of cosets ∑
a_g [gK], K = K(𝔑): the function ∑ a_g 1_{gK}. -/
abbrev heckeCosetFn {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] {n : Type}
    [Fintype.{0} n] {𝔑 : 𝓞 E} (f : heckeAlgebra n ℂ 𝔑) := cosetFn (levelGU n 𝔑) f.1

/-- On a GL_n(E)-orbit of triples, with chosen representative (xK, y, i): f(x⁻¹y⁻¹xK)·ω(P_y, i),
P_y the characteristic polynomial, if x satisfies `IsSignedFrame` at v₀ for J =
`eigenReflection` at Φ(v₀); else 0. -/
def countTerm (c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n)) := let (q, y, μ) :=
    c.out
  ite (IsSignedFrame q.out (eigenReflection ε y μ))
    (heckeCosetFn f (γ y q.out) * ω y.1.charpoly μ) 0

/-- Regularity of f: whenever f(x⁻¹y⁻¹x) ≠ 0 with y in GL_n(E) and x adelic, the characteristic
polynomial of y is separable. -/
def IsRegularHecke {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] {n : Type} [Fintype.{0} n]
    {𝔑 : 𝓞 E} (f : heckeAlgebra n ℂ 𝔑) :=
  ∀ ⦃y : GL n E⦄ ⦃x⦄, heckeCosetFn f (γ y x) ≠ 0 → y.1.charpoly.Separable

/-- The root r at the embedding t belongs to the Lie algebra: r = μ at t = Φ_{v₀}, r ≠ μ̄ at its
conjugate, and t = Φ_v above any other place v. -/
def IsLieRoot (r : ℂ) := if .mk t = v₀ then if t = Φ v₀ then r = μ else r ≠ star μ else t =
  Φ (.mk t)

/-- The roots r of σP, as rX or r: rX for r = μ if σ = Φ v₀, for r ≠ μ̄ if σ is its conjugate,
for all r if σ = Φ v, v ≠ v₀. -/
def lieRoots σ := (P.map σ).roots.map fun r ↦ (if IsLieRoot σ μ r then X else 1) * C r

/-- With μ the j-th listed root of Φ_{v₀}(P): ∏ (r − μX)/(r − μ) over the other listed roots r,
times ∏ (1 − σ(α_i)η) over i, σ and η in `lieRoots` P μ σ. -/
def localTerm (j : n) := let r := numberedRoots (Φ v₀) P; (Lagrange.basis .univ r j).comp
    (X * C (r j)) * ∏ i, ∏ σ, ((lieRoots P (r j) σ).map (1 - C (σ (α i)) * ·)).prod

open Fintype Matrix Multiset Ideal ComplexOrder AddMonoidHom Rat RingHom Algebra

attribute [local simp] map_smul' IsIntegrallyClosed.isIntegral_iff mul_smul trace_mul_cycle

section

variable {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] {n : Type} [Fintype.{0} n]
  {x : GL n (𝔸f E)} {ℓ : Matrix n n ℂ} {y : GL n E} {β : Matrix n n E} {x' : GL n (𝔸f E)}
  {ℓ' : Matrix n n ℂ} {β' : Matrix n n E} {𝔑 : 𝓞 E}

instance [h : StablyUnram E] : Nontrivial (InfinitePlace E) :=
  h.1.rec fun _ h ↦ by grind [finrank_eq_two_mul_card_infinitePlace, one_lt_card_iff_nontrivial,
  (totient_mul_totient_le_finrank _ 1 rfl .one h).trans' (by decide +kernel : 3 ≤ _)]

/-- If xᴴx = a·1 with a a finite idele of ℚ, then x is a unitary similitude, and x is a frame
for the scalar form c·1 whenever the rational number c equals the module |a|. -/
lemma mem_GU (a : (𝔸f ℚ)ˣ) (h : xᴴ * x.1 = finAdeleIncl ℚ E a • 1) :
    x ∈ GU E n ∧ ∀ c : ℚ, c = finIdeleAbs a → IsScalarFrame x c := by
  obtain ⟨s, u, hu, rfl⟩ := by simpa [Subgroup.mem_sup, classNumber_eq] using
    pow_classNumber_mem_principal_sup a
  let ν : (Ô ℚ)ˣ := (Ô ℚ).unitsEquivUnitsType ⟨u, coe_idelesUnitOff_empty.le (by simpa)⟩
  simp [↓map_mul, ↓finIdeleAbs_principalIdele, finIdeleAbs, ideleAbs_eq_prod_of_v_eq_one,
    hu, -cast_inv]
  erw [and_iff_right_of_imp (⟨_, by simp, ·⟩)]
  cases abs_choice s.1 <;> [use ν; use -ν] <;> simp [*, ν, ↓map_smul']

lemma mem_GUPlus_of_mem_levelGU : x ∈ levelGU n 𝔑 → x ∈ GUPlus E n :=
  .imp_right (·.1.isIntMatrix_inv)

lemma IsFrameFor.isHermitian_map {f : E →+* ℂ} : IsFrameFor β x → (β.map f).IsHermitian
  | ⟨_, h⟩ => .map ((isHermitian_map_iff (star_algebraMap_finAdele · |>.symm) (RingHom.injective
    _)).1 (by simp [IsHermitian, ← gram_inv_of_gram_eq h, star_eq_adeleMap]; congr; aesop)) _
    (map_star_complex f)

end

variable {E : Type} [Field.{0} E] [Ψ : CMBase E] {n : Type} [Fintype.{0} n] {x : GL n (𝔸f E)}
  {ℓ : Matrix n n ℂ} {y : GL n E} {β : Matrix n n E} {x' : GL n (𝔸f E)} {ℓ' : Matrix n n ℂ}
  {β' : Matrix n n E} {𝔑 : 𝓞 E} [Nonempty n] {c : ℚ} {ι : Type _} [Fintype ι] {w : ι → FinPlace E}

omit [Nonempty n] in
lemma isSignedFrameFor_one (g : Gf E n) : IsSignedFrameFor g.1 1 1 :=
  ⟨⟨1, by simpa [U] using g.2⟩, by simpa using .one⟩

lemma IsFrameFor.exists_intCast_eq (h : x ∈ GUPlus E n) : IsFrameFor ((c : E) • 1) x → ∃ z : ℤ, z =
  c | ⟨_, e⟩ => by simpa [isIntegral_ratCast_iff] using fun i ↦
    congr($(gram_inv_of_gram_eq e) i i ∈ Ô E).mp (sum_mem (by
  simp [mul_mem, h.2, -coe_units_inv, star_eq_adeleMap]))

lemma IsScalarFrame.eq_one_of_mem_levelGU (h : x ∈ levelGU n 𝔑) (e : IsScalarFrame x⁻¹ c) :
  c = 1 := by
  obtain ⟨w, rfl⟩ := e.2.exists_intCast_eq (mem_GUPlus_of_mem_levelGU (inv_mem h))
  simp_all [IsScalarFrame]; obtain ⟨left, right⟩ := e; grind
  [inv_intCast_den, Rat.den_intCast, (right.mul_iff.1 ⟨1, by simp [left.ne']⟩).exists_intCast_eq
  (c := w⁻¹) (mem_GUPlus_of_mem_levelGU h)]

lemma levelGU.isScalarFrame_inv_one (h : x ∈ levelGU n 𝔑) : IsScalarFrame x⁻¹ 1 :=
  (inv_mem h).1.rec fun _ e ↦ e.eq_one_of_mem_levelGU h ▸ e

/-- If x is a frame for both β and β', and both are positive definite at one complex embedding σ
of E, then β' = β. -/
lemma IsFrameFor.unique w : IsFrameFor β x → IsFrameFor β' x → (β.map (Φ w)).PosDef →
  (β'.map (Φ w)).PosDef → β' = β
  | ⟨ε, h⟩, ⟨δ, h'⟩, P, P' => by
    obtain ⟨⟨u, rfl⟩, b⟩ := mul_right_surjective ε δ, integralBasis E
    obtain ⟨⟨k, a⟩, e⟩ := by simpa [← map_trace, b.ext_elem_iff] using P.trace_pos.ne', by
      simpa [by simpa using gram_inv_of_gram_eq h] using gram_inv_of_gram_eq h'
    have ⟨s, q⟩ : ∃ s : ℚ, u.1.1 = s := ⟨_ * _, by
      simpa [← adeleCombination_repr b, adeleBasis, algebraMap_eq_smul_one, ← map_trace,
      ← smul_toAlgebra, ← eq_inv_smul_iff₀ a] using congr((adeleBasis b).repr (trace $e) k)⟩
    cases (Matrix.map_injective (RingHom.injective _) (.trans (by aesop) e) : (s : E) • β = β')
    simp [IsScalarFrame.eq_one_of_mem_levelGU (levelGU n (0 : 𝓞 E)).one_mem
      ⟨by simpa [← Complex.ofReal_ratCast, P.trace_pos] using P'.trace_pos, u, by aesop⟩]

/-- Let E have at least two infinite places, `IsSignedFrameFor` hold for (x, ℓ, β) and (x', ℓ',
β'), c > 0 be rational, y ∈ GL_n(E). If (x'⁻¹yx)⁻¹ is a frame for the scalar form c·1, then
yᴴβ'y = cβ. -/
lemma IsSignedFrameFor.conj_eq_smul (h : IsSignedFrameFor x ℓ β) (h' :
  IsSignedFrameFor x' ℓ' β') (H : IsScalarFrame (x'⁻¹ * toFinGL y * x)⁻¹ c) :
  yᴴ * β' * y.1 = (c : E) • β := (exists_ne Ψ.v₀).rec fun w _ ↦ by
  apply (h.1.mul_iff.2 H.2).unique w (by simp [IsFrameFor.conj_iff, *]) <;>
    simp [↓map_conjTranspose_mul_mul, ↓map_smul', cast_smul_eq_qsmul]
  exacts [.smul (by grind) H.1, (y.map _).isUnit.posDef_star_left_conjugate_iff.2 (by grind)]

/-- Let E have at least two infinite places, `IsSignedFrameFor` hold for (x, ℓ, β), c > 0 be
rational, y ∈ GL_n(E) fix ℓ, and (x⁻¹yx)⁻¹ be a frame for c·1. Then yᴴβy = cβ, and |r|² = c
for all eigenvalues r of all σy. -/
lemma IsSignedFrameFor.similitude_and_root_norm (h : IsSignedFrameFor x ℓ β) (H :
  IsScalarFrame (x⁻¹ * toFinGL y * x)⁻¹ c) (l : ratConj y ℓ = ℓ) : yᴴ * β * y.1 = (c : E) • β ∧ ∀ᵉ
  (w) (r ∈ (y.1.charpoly.map (Φ w)).roots), r * star r = c := ⟨h.conj_eq_smul h H, fun w r q ↦ by
  have P := h.2 w; set J := ite (w = v₀) ..
  obtain ⟨l, -, u, a, hu⟩ := by simpa using
    (Units.mul_inv_eq_iff_eq_mul _).1 (by aesop : ConjAct.toConjAct (y.map (Φ w)) • J = J), by
    simpa [← charpoly_map, eval_charpoly, ← exists_mulVec_eq_zero_iff] using q
  simpa [↓map_conjTranspose_mul_mul, ← vecMul_vecMul, ← star_mulVec, ← dotProduct_mulVec,
    ← J.mulVec_mulVec, ← hu, l, field, (P.dotProduct_mulVec_pos a).ne'] using
    congr(star u ᵥ* $(h.conj_eq_smul h H).map (Φ w) ⬝ᵥ J *ᵥ u)⟩

/-- Neatness: let E⁺ ≠ ℚ, (x, ℓ) a frame, y ∈ GL_n(E) preserving ℓ, with x⁻¹yx an integral
similitude of unit multiplier congruent to 1 modulo J ⊂ Ô. If J ∩ O_E lies in an ideal I of
norm exceeding (2n)^{[E:ℚ]}, then y = 1. -/
lemma IsSignedFrameFor.eq_one_of_congr_large_norm (h : IsSignedFrameFor x ℓ β) {I} J (f :
  IsScalarFrame (x⁻¹ * toFinGL y * x)⁻¹ 1) (k : x⁻¹ * toFinGL y * x ∈
  congruenceGL (.map (Algebra.linearMap (Ô E) _) J) id) (hℓ : ratConj y ℓ = ℓ)
  (b : (2 * card n) ^ finrank ℚ E < absNorm I) (c : under (𝓞 E) J ≤ I) : y = 1 := by
  obtain ⟨⟨q, H⟩, ⟨w, P⟩, ⟨_, A⟩, a, ⟨⟩⟩ := h.similitude_and_root_norm f hℓ,
    (exists_ne v₀).imp fun w ↦ (by simpa [·] using h.2 w), (by simp [map_trace] : Matrix.trace _ =
    ↑(y.1 - 1).trace).subst (sum_mem fun i _ ↦ k.2 i i)
  have := by simpa using congr($(norm_eq_zero_iff.1 (Int.eq_zero_of_abs_lt_dvd
    (absNorm_dvd_norm_of_mem (@c ⟨_, algebraMap_mem_Ô.1 A⟩ a)) (by
    rify at *; grw [← b]; erw [← cast_intCast, coe_norm_int, abs_norm_eq_prod_norm_sq,
      finrank_eq_two_mul_card_infinitePlace, pow_mul, ← Finset.prod_const]; gcongr; simp [map_trace]
    grw [trace_eq_sum_roots_charpoly, charpoly_map, norm_sub_le, norm_multiset_sum_le, two_mul,
      sum_map_le_sum_map _ 1 (by simpa using congr(√‖$(H _ · ·)‖).le)]
    simp [IsAlgClosed.card_roots_eq_natDegree]))).val)
  use Units.ext (map_injective (Φ w).injective (by simpa [kronecker_mulVec_vec,
    star_vec_dotProduct_vec, sub_mul, ← mul_assoc, ← map_conjTranspose_mul_mul, -vec_sub,
    P.det_pos.ne', ← map_trace,
    *] using (P.inv.transpose.kronecker P).dotProduct_mulVec_pos (x := vec (y.map (Φ w) - 1))))

variable (n 𝔑) in
/-- 𝔑 ≠ 0 and, whenever `IsSignedFrame x ℓ` holds, every y in GL_n(E) with x⁻¹yx in K(𝔑) and
Φ_{v₀}(y) commuting with ℓ (`ratConj y ℓ = ℓ`) equals 1. -/
def IsNeat := 𝔑 ≠ 0 ∧ ∀ {x ℓ y}, IsSignedFrame x ℓ → x⁻¹ * toFinGL y * x ∈ levelGU n 𝔑 →
  ratConj y ℓ = ℓ → y = 1

/-- If E⁺ ≠ ℚ and n ≥ 1, then for all but finitely many finite places w of E, every non-zero
integer 𝔑 in w is a neat level. -/
lemma eventually_isNeat : ∀ᶠ w : FinPlace E in .cofinite, ∀ 𝔑 ≠ 0, 𝔑 ∈ w.1 → IsNeat n 𝔑 := .mono
  (Northcott.finite_le (h := FinPlace.q) _).compl_mem_cofinite fun w b _ h₀ a ↦
  ⟨h₀, fun ⟨_, h⟩ k l ↦ h.eq_one_of_congr_large_norm (span _) (levelGU.isScalarFrame_inv_one k)
  (by simpa [Submodule.map_span] using! k.2) l
  (by aesop) fun _ c ↦ mem_of_dvd _ ((dvd_iff_Ô h₀).1 (mem_span_singleton.1 c)) a⟩

omit [Nonempty n] Ψ

/-- Neatness, for E with at least two infinite places:
let w_i be distinct finite places with (2n)^[E:ℚ] < ∏ q_{w_i}, and K ⊂ G_f ∩
GL_n(Ô) a subgroup reducing to 1 modulo every w_i. Then Γ_f ∩ gKg⁻¹ is trivial for all g,
Γ_f the rational unitary group of the definite space I_n. -/
lemma classAut_eq_bot {E : Type} [Field.{0} E] [CMType E] {w : ι → FinPlace E}
    [Nontrivial (InfinitePlace E)] (hw : w.Injective) (b :
  (2 * card n) ^ finrank ℚ E < ∏ i, (w i).q) {K} (hK : K ≤ levelOf w ⊥) g :
  classAut (stdSpace E n).Γf K g = ⊥ := bot_unique (by
  rintro _ ⟨⟨γ, rfl⟩, k⟩; obtain ⟨⟨hk, h⟩, _ : CMBase E⟩ := mem_levelOf.1 (hK k),
    ⟨Classical.ofNonempty⟩
  simp [((isEmpty_or_nonempty n).rec (by subsingleton) fun _ ↦ Subtype.ext ((isSignedFrameFor_one
    g).eq_one_of_congr_large_norm (⨅ i, ker (reduceAt (w i))) (by simpa [← stdSpace_embFin]
    using mod_cast (isSignedFrameFor_one _).1) (stdSpace_embFin γ ▸ ⟨hk, (⟨_,
    mem_iInf.2 fun a ↦ intGL.map_eq_one.1 congr($h a) · ·, rfl⟩)⟩) _ (by rwa [map_prod]) _) :
    γ = 1), ratConj, IsConcreteLE.le_iff, mem_prod_finPlace_iff hw])
