/- GID: D5/S3/Zeros/GRH/Lib/Weil/MixedModel/AdelicSum
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/MixedModel/AdelicSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.MixedModel.AdelicSum. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/MixedModel/AdelicSum.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Construction.FiniteVacuum
import D5.S3.Zeros.GRH.Lib.Weil.Fock.FockTensor
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: Schwartz–Bruhat functions at split places, Schrödinger action, spanned by translates of
the lattice indicator. Adelic Heisenberg datum with vacuum splits as real part plus finite part. -/

noncomputable section

open NumberField Filter MeasureTheory Matrix ComplexConjugate AddSubgroup QuotientAddGroup
  OpenAddSubgroup Quotient stdLattice Submodule AddChar Set Prod WeilData Finset Fintype Complex
  Real

section

section

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] (n : Type _) [Fintype n]
  (S : Set (FinPlace E))

attribute [-instance] instIsCharPOfIsLeftCancelAddOfCharP

attribute [-simp] map_smul map_add

/-- The additive group of finite adelic n-vectors that are integral at every place of S. -/
def integralBox := (stdLattice E n).comap (idem S • .id _)

/-- The complex-valued indicator function of the finite adelic n-vectors that are integral at
every place of S. -/
def boxIndicator x := ite (x ∈ integralBox n S) (1 : ℂ) 0

variable {n}

/-- Ψ is Schwartz–Bruhat above S: it depends only on the components at S, is locally constant,
and the S-parts of its support lie in a compact set. -/
@[local grind] class IsSchwartzBruhat (Ψ : (n → 𝔸f E) → ℂ) where
  idem_smul x : Ψ (idem S • x) = Ψ x
  locally_constant : IsLocallyConstant Ψ
  compact_support : ∃ C, IsCompact C ∧ ∀ x, Ψ x ≠ 0 → idem S • x ∈ C

/-- The homomorphism sending g in GL_n of the finite adeles to the idele equal to det g at the
places of S and 1 elsewhere. -/
@[simps! apply_val_fst] def detOn : GL n (𝔸f E) →* (𝔸 E)ˣ := finIdeleIncl.comp
  (GeneralLinearGroup.det.comp (cutGL (idem_mul_self S)))

/-- The indicator function of the finite adelic vectors x such that t⁻¹(x − z) is integral at
every place of S. -/
abbrev cosetIndicator (t : (𝔸f E)ˣ) z x := boxIndicator n S (t⁻¹.1 • (x - z))

variable {S} (g : Gf E n) (hS : S.IsConjDisjoint) {Φ Ψ : (n → _) → ℂ} [hΨ : IsSchwartzBruhat S Ψ]

omit [IsCMField E] [Fintype n] in
@[simp] lemma boxIndicator_apply x : boxIndicator n S x = ite (x ∈ integralBox n S) 1 0 := rfl

attribute [local simp ↓, local grind .] idem_mul_self smul_smul smul_add idem_apply idem_mul_mem_Ô
  mul_add cutGL RingHom.map_det

omit [IsCMField E] [Fintype n] in
lemma mem_integralBox {x} : x ∈ integralBox n S ↔ ∀ i, idem S * x i ∈ Ô E := .rfl

omit [IsCMField E] in
lemma isOpen_integralBox : (integralBox n S).IsOpen := isOpen_stdLattice.preimage (by continuity)

@[simp] lemma detOn_apply w : (detOn S g.1).1.2 w = ite (w ∈ S) (g.atPlace w).1.det 1 := by
  simp [detOn, ← evalAt_apply, map_add, Matrix.map_smul']
  aesop

lemma detOn_eq_prod (S : Finset _) : detOn S g.1 = ∏ w ∈ S, locFullIdele w (g.atPlace w).det := by
  ext v <;> simp [locFullIdele, fst_prod, snd_prod, ← evalAt_apply]
  simp_all [S.prod_eq_ite v, eq_comm]

end

attribute [-instance] instIsCharPOfIsLeftCancelAddOfCharP

attribute [-simp] map_smul map_add

attribute [local grind] IsSchwartzBruhat

attribute [local simp ↓, local grind .] idem_mul_self smul_smul smul_add idem_apply idem_mul_mem_Ô
  mul_add cutGL RingHom.map_det

variable {E : Type*} [Field E] [CMType E] {n : Type _} [Fintype n] (S : Set (FinPlace E))
  (g : Gf E n) (hS : S.IsConjDisjoint) {Φ Ψ : (n → _) → ℂ} [hΨ : IsSchwartzBruhat S Ψ]

/-- The Schrödinger model above S: y acts on functions by Ψ ↦ (x ↦ χ(½ y*(2x + y)_S) Ψ(x + y)),
where χ(z) = ψ_f(ȷ α ᾱ z). -/
def schrodingerAct [WeilData E] (y : n → 𝔸f E) : Module.End ℂ ((n → 𝔸f E) → ℂ) :=
  .pi fun x ↦ psi₀ E (half * star y ⬝ᵥ idem S • (x + (x + y))) • .proj (x + y)

/-- The linear map sending finitely supported coefficients c_y to the function ∑ c_y
`schrodingerAct` S y applied to the indicator of vectors integral on S. -/
abbrev schrodingerComb [WeilData E] := Finsupp.lift _ ℂ _ (schrodingerAct S · (boxIndicator n S))

/-- The inner product ∫ conj(Ψ) Ψ′ over the finite adelic vectors integral off S, for the Haar
measure giving Ô^n mass one. -/
def localInner (Ψ Ψ' : _ → ℂ) := ∫ x in integralBox n Sᶜ, conj (Ψ x) * Ψ' x ∂latticeMeasure E n

variable {S}

omit [Fintype n] in
lemma integralBox_compl_inter : SetLike.coe (integralBox n Sᶜ) ∩ integralBox n S =
  stdLattice E n := by grind [mem_integralBox, mem_stdLattice, mem_Ô, SetLike.mem_coe]

lemma isLocallyConstant_psi₀ [WeilData E] :
    IsLocallyConstant (psi₀ E) := isLocallyConstant_of_eventually_add
  ((isOpen_Ô.eventually_mem (by simp)).mono (by simp_all [map_add_eq_mul, psi₀_eq_one_of_mem]))

instance isSchwartzBruhat_boxIndicator : IsSchwartzBruhat S (boxIndicator n S) :=
  ⟨by simp [integralBox], (LocallyConstant.charFn _
  (isClopen ⟨_, isOpen_integralBox⟩)).2, _, isCompact_stdLattice, by simp [integralBox]⟩

namespace IsSchwartzBruhat

lemma comp {m} [Fintype m] {A : Matrix n m _} B (k : ∀ y, B *ᵥ A *ᵥ y = y) y :
    IsSchwartzBruhat S (Ψ <| A *ᵥ · + y) := by use ?_, hΨ.2.comp_continuous (by fun_prop) <;> grind
  [mulVec_smul, → IsCompact.image, show Continuous fun z ↦ B *ᵥ (z - idem S • y) by fun_prop]

instance comp_add y :
  IsSchwartzBruhat S (Ψ <| · + y) := by simpa using comp (A := diagonal 1) 1 (by simp) y

instance comp_mulVec (g : GL n _) :
  IsSchwartzBruhat S (Ψ <| g.1 *ᵥ ·) := by simpa using comp g.2 (by simp) 0

/-- Let Ψ be Schwartz–Bruhat above S and t a finite idele, with Ψ(x+y) = Ψ(x) when Ψ(x) ≠ 0 and
t⁻¹y is integral on S. Then Ψ is a finite sum of Ψ(q) times the coset functions `cosetIndicator`
S t q, all Ψ(q) ≠ 0. -/
lemma eq_sum_cosetIndicator t (per : ∀ x, Ψ x ≠ 0 → ∀ y, t⁻¹.1 • (y - x) ∈ integralBox n S → Ψ y =
  Ψ x) :
  ∃ A, (∀ q ∈ A, Ψ q ≠ 0) ∧ Ψ = ∑ q ∈ A, Ψ q • cosetIndicator S t q := hΨ.3.elim fun _ ⟨c, h⟩ ↦ by
  have k {x} : t⁻¹.1 • x ∈ integralBox n S ↔ x ∈ (comap (smulAddHom _ _ t⁻¹.1)
    (continuous_const_smul _) ⟨integralBox n S, isOpen_integralBox⟩).1 := .rfl
  use .image out ((c.image continuous_mk).finite_of_discrete.subset (t := (Ψ ∘ out).support) fun _ ↦
    (⟨_, h _ ·,
    mk_eq_iff_out.2 (leftRel_apply.2 (k.1 (by simp_all [mem_integralBox])))⟩)).toFinset, by simp
  simp_all [← eq_iff_sub_mem, funext_iff]
  intro x; split_ifs with h
  exacts [by_contra fun k ↦ k ((per x k _ (QuotientAddGroup.out_eq' _)).symm.trans h),
    per _ h x (QuotientAddGroup.out_eq' _).symm]

lemma integrableOn {F} (f : Continuous F) : IntegrableOn (fun x ↦ F x * Ψ x) (integralBox n Sᶜ)
  (latticeMeasure ..) := hΨ.3.elim fun _ ⟨c, k⟩ ↦ .of_inter_support isOpen_integralBox.measurableSet
  (((c.add isCompact_stdLattice).integrableOn _ (f.mul hΨ.2.continuous)).mono_set fun _ h ↦ ⟨_, k _
  (right_ne_zero_of_mul h.2), _, h.1, by aesop⟩)

/-- A Schwartz–Bruhat function Ψ above S lies in a subspace P if each y with Ψ(y) ≠ 0 has a
neighbourhood U such that P contains every coset function for (t, z), t an integral idele,
whose coset has S-parts in U. -/
lemma mem_of_cosets (P : Submodule ℂ _) (h : ∀ y, Ψ y ≠ 0 → ∃ U ∈ nhds y, ∀ t z, t.1 ∈ Ô E → (∀ x,
  t⁻¹.1 • (x - z) ∈ integralBox n S → idem S • x ∈ U) → cosetIndicator S t z ∈ P) : Ψ ∈ P := by
  have ⟨_, c, o⟩ := hΨ.3
  choose _ hU h using h
  let := IsTopologicalAddGroup.rightUniformSpace
  choose! _ w y H using lebesgue_number_lemma_nhds c fun y _ ↦
    inter_mem (iInter_mem.2 (hU y)) (hΨ.2.eventually_eq y)
  have ⟨_, hN, L⟩ := exists_natCast_smul_mem_of_isCompact E isCompact_stdLattice (mem_comap'.1 w)
  have ⟨t, ht⟩ := isUnit_natCast_finAdele (E := E) hN
  have k q h x (b : t⁻¹.1 • (x - q) ∈ integralBox _ S) := @H _ (o q h)
    (idem S • x) (L _ b (by simp [← ht, mul_left_comm t.1, sub_eq_add_neg]))
  refine' (hΨ.eq_sum_cosetIndicator t _).elim fun _ e ↦ e.2 ▸ sum_smul_mem _ _ fun q _ ↦
    h (y (idem S • q)) .. <;> grind [natCast_mem, mem_iInter, UniformSpace.mem_ball_self]

end IsSchwartzBruhat

instance (t) (z : n → _) : IsSchwartzBruhat S (cosetIndicator S t z ·) := by
  simpa [sub_eq_add_neg] using! (isSchwartzBruhat_boxIndicator.comp_add _).comp_mulVec (.scalar _ _)

include hS

attribute [local simp] Set.disjoint_left funext_iff

lemma idem_mul_star : idem S * star (idem S) = 0 := by aesop

lemma idem_conjClosure_eq_add_star : idem S.conjClosure = idem S + star (idem S) := by aesop

variable [WeilData E]

attribute [local simp, local grind .] schrodingerAct idem_mul_star idem_conjClosure_eq_add_star

lemma schrodingerAct_schrodingerAct y y' Ψ : schrodingerAct S y (schrodingerAct S y' Ψ) =
  (stdLattice.finHeis E n).β
  (idem S.conjClosure • y) (idem S.conjClosure • y') • schrodingerAct S (y + y') Ψ := by
  simp [stdLattice.finHeis, ← mul_assoc, ← map_add_eq_mul, add_assoc]
  grind [psi₀_congr (half * idem S * star y ⬝ᵥ y') (zero_mem _), star_dotProduct, star_mul]

lemma schrodingerAct_boxIndicator {y} (hy : y ∈ integralBox n S.conjClosure) :
  semichar (idem S.conjClosure • y) • schrodingerAct S y (boxIndicator n S) = boxIndicator n S := by
  have := smul_mem_stdLattice (idem_mem_Ô S) hy
  simp_all [integralBox, add_mem_cancel_right, semichar, ← map_add_eq_mul, ite_eq_iff']
  exact fun _ h ↦ (psi₀ E).2 ▸ psi₀_congr
    (star stdLattice.traceOneAdele * half * idem S ^ 2 * star y ⬝ᵥ y) (dot_mem (add_mem h
    (smul_mem_stdLattice traceOneAdele_mem this)) hy) (by simp; grind [star_dotProduct])

namespace IsSchwartzBruhat

/-- Let S be disjoint from its conjugate and Ψ Schwartz–Bruhat above S. In the Schrödinger model
above S, the part of y at the places of S acts on Ψ by translation, giving x ↦ Ψ(x + y). -/
lemma schrodingerAct_idem y : schrodingerAct S (idem S • y) Ψ = (Ψ <| · + y) := by
  simp
  grind [map_zero_eq_one]

/-- Let S be disjoint from its conjugate and Ψ Schwartz–Bruhat above S. In the Schrödinger model
above S, the part of y at the conjugate places multiplies Ψ(x) by ψ_f(ȷαᾱ y*x_S), x_S the
part of x at S. -/
lemma schrodingerAct_star y : schrodingerAct S (star (idem S) • y) Ψ = fun x ↦
  psi₀ E (star y ⬝ᵥ idem S • x) * Ψ x := by
  simp
  grind [zero_smul]

instance (y) : IsSchwartzBruhat S (schrodingerAct S y Ψ) := have := hΨ.comp_add y
  by use ?_, (isLocallyConstant_psi₀.comp_continuous (by fun_prop)).mul this.2 <;> simp <;> grind

/-- If S is disjoint from S̄, every Schwartz–Bruhat function Ψ above S is a finite linear
combination of the functions `schrodingerAct` S y applied to the indicator of the vectors integral
on S. -/
lemma _root_.Space.exists_schrodingerComb_eq (h : IsSchwartzBruhat S Φ) :
  Φ ∈ (schrodingerComb S).range := mem_of_cosets _ fun _ _ ↦ ⟨_, univ_mem, fun t z ht _ ↦ by
  let B := comap (star t⁻¹.1 • .id _) (by continuity) ⟨stdLattice E n, isOpen_stdLattice⟩
  have := fintypeOfIndexNeZero (isCompact_stdLattice.relIndex_ne_zero_add B.2)
  refine (funext ((add_right_surjective z).forall.2 fun x ↦ ?_)).symm.subst (smul_mem _ ?_ (sum_mem
    (t := @.univ _ this) fun q _ ↦ (schrodingerAct_schrodingerAct hS (idem S • -z) (star (idem S) •
    -(star t⁻¹.1 • q.out)) _).symm.subst ⟨_, Finsupp.lsum_single ℕ ..⟩))
  simp only [↓schrodingerAct_idem, schrodingerAct_star, *, psi₀_star, star_dotProduct (-_)]
  by_cases hx : x ∈ integralBox n S
  simpa [*, -smul_smul, mul_left_comm] using! (integral_psi₀_stdLattice (idem S • t⁻¹.1 • x) ▸
    setIntegral_eq_finsum isCompact_stdLattice B.2 fun _ _ h ↦
    psi₀_congr 0 (dot_mem h hx) (by aesop) :)
  simpa [*] using! (smul_mem_stdLattice ht).mt (by simpa [mul_left_comm t.1])⟩

end IsSchwartzBruhat

end

variable (E : Type*) [Field E] [CMType E] [WeilData E] {n : Type*}
  [Fintype n] (s : n → ℤˣ)

lemma WeilData.conj_scaleIdele_mul w :
  starRingEnd ℂ ((scaleIdele E).1.1 w) * (scaleIdele E).1.1 w * (2 * π * (Φ w j).im) =
  1 := by simp [val_scaleIdele_fst, field, ← ofReal_pow, pi_pos, im_pos, le_of_lt, (im_pos ..).ne']

attribute [-simp] mul_re

attribute [local simp] dotProduct mul_sum fst_sum snd_sum val_scaleIdele_snd psi₀_apply sum_div half
  sum_prod_type

/-- The sign function on pairs (infinite place, coordinate) that returns the sign of the
coordinate, ignoring the place. -/
abbrev realSigns : InfinitePlace E × n → ℤˣ := fun p ↦ s p.2

/-- The isomorphism (y,z) ↦ κ·(y,z) from complex coordinates times finite adelic vectors onto
𝔸^n, under which β is the product of the real and finite bicharacters. -/
def adelicSum :
  (adelicHeis E s).OrthogonalSum (realHeis (realSigns E s)) (stdLattice.finHeis E n) vacuumFn where
  equiv.toAddEquiv := by use! fun y i ↦ scaleIdele E * ((y.1 ⟨·, i⟩), y.2 i), fun x ↦
    (fun p ↦ ((scaleIdele E)⁻¹ * x p.2).1 p.1,
    ((scaleIdele E)⁻¹ * x · |>.2)) <;> simp_intro _ [funext_iff, ← mul_add, -fst_mul, -snd_mul]
  beta_equiv := by simp [adelicHeis, realHeis, stdLattice.finHeis, stdAddChar, fourierChar, stdForm,
    signMatrix, ← sum_sub_distrib, map_ofNat, ← sum_neg_distrib, re_eq_add_conj, sum_mul]; grind
    [conj_scaleIdele_mul, im_eq_sub_conj, I_sq, =_ map_star_complex, star_j, starRingEnd_apply]
  vac_equiv := by simp [vacuumFn, finVac, realVac, neg_div, mul_pow, ← conj_mul', mem_stdLattice,
        ↓sum_prod_type_right]; grind [conj_scaleIdele_mul, stdLattice.traceOneAdele]

variable {E s}

lemma mat_mulVec_adelicSum (g : G E s) y : g.mat *ᵥ (adelicSum E s).equiv y =
  (adelicSum E s).equiv ((blockU g.1).1.1 *ᵥ
  y.1, g.2.1.1 *ᵥ y.2) := by ext <;> simp [adelicSum, mulVec, mul_left_comm, blockDiagonal]
