/- GID: D5/S3/Zeros/GRH/Lib/Weil/Construction/PairDefs
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Construction/PairDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Construction.PairDefs. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Construction/PairDefs.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Theta.OscillatorDefs
import D5.S3.Zeros.GRH.Lib.Weil.Construction.ThetaFunctional
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

Part of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth, rapid decay (known
result; see Lib.Weil.DualPair.KernelDecay).

This file: Space of data, Heisenberg and Weil operators, vacuum, theta functional, projections.
Heisenberg law, unitarity, continuity, vacuum coefficients, theta product formula for the Weil
representation. Space of maps between hermitian spaces, Weil action of the pair, theta kernel. -/

noncomputable section

open Circle Classical Complex Equiv Heisenberg Matrix NumberField Space WeilData IsVacuum Kronecker
variable {E : Type*} [Field E] [CMType E] [WeilData E] {n : Type _}
  [Fintype n] {s : n → ℤˣ} (V : Space E n s) (x y : n → 𝔸 E) {n' : Type _} [Fintype n']
  {s' : n' → ℤˣ}

/-- The Banach space 𝒮(V) of integrable functions c on 𝔸^n with c(x) = ∫ c(y)β(y,x)e(x−y) dy,
under the L¹ norm; it depends only on the signs of V. -/
def 𝒮 (_ : Space E n s) := Model (adelicHeis E s) deriving NormedAddCommGroup, NormedSpace ℂ,
  CompleteSpace

/-- The additive map from ℂ^{places × n} to 𝔸^n that multiplies the coordinates at τ by (2π Im
τȷ)^(−1/2) and puts zero at the finite places. -/
def realVec : (InfinitePlace E × n → ℂ) →+ n → 𝔸 E :=
  .mk' (fun y i ↦ ((scaleIdele E).1.1 * (y ⟨·, i⟩), 0)) (by simp [mul_add, funext_iff])

/-- The archimedean part of an adelic vector y in Fock coordinates: the complex numbers (2π Im
τ(ȷ))^{1/2}·y_{i,τ}, indexed by infinite places τ and coordinates i. -/
def realCoord (p : _ × _) := (y p.2).1 p.1 / (scaleIdele E).1.1 p.1

/-- For an adelic vector y, the finite adelic vector with coordinates α⁻¹ times the finite part
of y_i, α the finite idele of the Weil data. -/
abbrev finCoord i := α⁻¹.1 * (y i).2

/-- The adelic vector with finite part αx and zero real part, for a finite adelic vector x. -/
def finVec (x : n → _) i := ((0, α.1 * x i) : 𝔸 E)

attribute [local simp] Finset.mul_sum Space.vecAtPoint adelicSum dotProduct realCoord realVec

omit [Fintype n] in
lemma realVec_realCoord_add : realVec (realCoord y) + (0, y · |>.2) =
  y := by ext <;> simp; grind [conj_scaleIdele_mul]

@[simp] lemma adelicSum_real_eq_realVec s y : (adelicSum E (n := n) s).equiv (y, 0) =
  realVec y := by bound

lemma adelicHeis_beta_eq_prod : (adelicHeis E s).β x y = ∏ i, (adelicHeis E fun _ : Unit ↦
  s i).β (fun _ ↦ x i) fun _ ↦ y i := by simp [adelicHeis, stdForm]; erw
  [← map_prod (coeHom.comp (stdAddChar E).toMonoidHom)]; rfl'

lemma vacuumFn_eq_prod : vacuumFn x = ∏ i, vacuumFn fun _ : Unit ↦ x i := by
  simp [vacuumFn, Finset.prod_ite_zero, ← exp_sum]
  congr; erw [← map_prod (coeHom.comp (ψf E).toMonoidHom)]; rfl'

/-- For a sign c and an adele a, the number θ(ϱ(a)vac), with θ a chosen theta functional of the
standard hermitian line of sign c. -/
def lineTheta c a :=
  (signedSpace E fun _ ↦ c).exists_isThetaFunctional.choose (heisOp (fun () ↦ a) IsVacuum.vacElem)

/-- The standard space of signs s has a theta functional θ with θ(ϱ(x)vac) = ∏_i θ_i(ϱ(x_i)vac)
for all adelic x, where θ_i is the theta functional chosen on the line of sign s_i. -/
lemma exists_isThetaFunctional_signedSpace : ∃ θ, (signedSpace E s).IsThetaFunctional θ ∧ ∀ x,
  θ (heisOp x IsVacuum.vacElem) = ∏ i,
  lineTheta (s i) (x i) := have ⟨θ, h, m⟩ := (signedSpace E s).exists_isThetaFunctional
  let a x := θ (heisOp x IsVacuum.vacElem)
  have k x y : ∏ i, lineTheta _ (x i) * star (lineTheta _ (y i)) = a x * star (a y) :=
    tendsto_nhds_unique (tendsto_finsetProd _ fun i _ ↦ (piUnique _).symm.hasSum_iff.2
    (exists_isThetaFunctional.choose_spec.elim (fun p ↦ p.hasSum_modelInner p) _ _))
    (.congr (Finset.sum_prod_piFinset · _) (((h.hasSum_modelInner h m ..).congr_fun fun _ ↦ by
    simp [adelicHeis_beta_eq_prod (s := s), vacuumFn_eq_prod (n := n), signedSpace,
      ← map_inv]; rfl).comp
    (Filter.tendsto_atTop_finset_of_monotone (by aesop_cat) (⟨Finset.univ.image ·, by simp⟩))))
  have ⟨y, _⟩ : ∃ y, a y ≠ 0 := by_contra (by aesop)
  ⟨((∏ i, lineTheta (s i) (y i)) / a y) •
    θ, by simp_all [IsThetaFunctional, Space.IsRatInvariant]; grind [map_ne_zero]⟩

namespace Space

lemma IsThetaFunctional.comp {V₁ : Space E _ s'} {θ σ} [RingHomIsometric σ] [RingHomInvPair σ σ]
  (h : V.IsThetaFunctional θ) (T : _ →SL[σ] _) (φ : _ ≃ₜ+ _) (hφ : ∀ x ∈ V₁.ratVectors,
  φ x ∈ V.ratVectors) (hρ : ∀ x v, T (heisOp x v) = heisOp (φ x) (T v)) (h1 :
  modelInner (T IsVacuum.vacElem) (T IsVacuum.vacElem) = 1) : V₁.IsThetaFunctional
  (σ.toSemilinearMap.mkContinuous 1 (by simp) ∘SL θ ∘SL T) := ⟨by simp_all [IsRatInvariant,
  IsThetaFunctional], by rw [← (one_mul _).trans h1, ← h.1.quotMean_eq _ h.2, ← quotMean_comp _
  (.mk' φ _) _ hφ φ.surjective] <;> simp [*, mul_conj', ↓IsRatInvariant.isContPeriodic, h.1]⟩

/-- The Heisenberg representation y ↦ ϱ(y) of (𝔸^n, β) on the Banach space 𝒮(V). -/
def heisRep : (adelicHeis E s).Rep (𝒮 V) := IsVacuum.heisRep

/-- For an adelic vector y, the Heisenberg operator ϱ(y) on 𝒮(V): the bounded operator sending c
to x ↦ β(y,x)c(x−y). -/
abbrev ϱ := V.heisRep.ρ y

/-- The Weil representation: the homomorphism from the adelic unitary group G to bounded
operators on 𝒮(V) given by ω(g)c = Δ(g) ∫ c(y) ϱ(gy)vac dy. -/
def ω : G E s →* 𝒮 V →L[ℂ] 𝒮 V := weilRep adelicAction

/-- The bounded sesquilinear form ⟨c, c′⟩ = ∫ c̄ c′ over 𝔸^n on 𝒮(V), conjugate-linear in the
first variable. -/
def dataInner : 𝒮 V →L⋆[ℂ] 𝒮 V →L[ℂ] ℂ := modelInner

/-- The vacuum: the function e (Gaussian times twisted lattice indicator) as an element of 𝒮(V). -/
def vacElem : 𝒮 V := IsVacuum.vacElem

/-- The functional θ_s∘ω(g) on 𝒮(V), g a chosen element carrying rational vectors of V to those
of the standard space of signs s; any chosen theta functional if none exists. -/
def rawTheta : 𝒮 V →L[ℂ] ℂ := if h : ∃ g, ∀ γ ∈ V.ratVectors,
  G.mat g *ᵥ γ ∈ (signedSpace E s).ratVectors then exists_isThetaFunctional_signedSpace.choose ∘L
  V.ω h.choose else V.exists_isThetaFunctional.choose

/-- The theta functional of V: the bounded functional `Space.rawTheta` composed with the
Heisenberg operator ϱ(0), which is the identity. -/
def θ := V.rawTheta ∘L V.ϱ 0

/-- The theta functional θ of V equals the functional `Space.rawTheta`, that is, composing the
latter with the Heisenberg operator ϱ(0) changes nothing. -/
lemma theta_eq_rawTheta : V.θ = V.rawTheta := by ext; simp [θ]

/-- The functional `rawTheta` of V is a theta functional for the rational vectors of V: bounded,
invariant under their Heisenberg operators, with |rawTheta(ϱ(x)vac)|² of mean one over the
quotient. -/
lemma isThetaFunctional_rawTheta : V.IsThetaFunctional V.rawTheta :=
  dite_mem (s := {θ | V.IsThetaFunctional θ}).2 ⟨fun h ↦ exists_isThetaFunctional_signedSpace (E :=
  E) (s := s).choose_spec.1.comp _ _ (.mk' (.smul h.choose) (by simp))
  h.choose_spec (weilRep_heisOp adelicAction _) (by simp [vacuumFn]), fun _ ↦ choose_spec _⟩

instance : FunLike (𝒮 V) (n → 𝔸 E) ℂ :=
  ⟨fun f x ↦ V.rawTheta (V.ϱ x f), V.isThetaFunctional_rawTheta.injective_apply_heisOp⟩

/-- The bounded bilinear map (v, f) ↦ v ⊗ f = ∫ v(y) ϱ(y)f dy, for v in the Fock space, f in
𝒮(V), y over real vectors in Fock coordinates. -/
def integrated : Model (realHeis (realSigns E s)) →L[ℂ] 𝒮 V →L[ℂ] 𝒮 V :=
  (V.heisRep.left (adelicSum ..)).integrated

/-- For a finite adelic vector x, the operator ψ(½c₀ȷαᾱ x*x) ϱ(αx) on 𝒮(V). -/
def finHeisOp x := stdLattice.semichar x • V.ϱ (finVec x)

/-- For a set S of finite places, the operator P^S on 𝒮(V): the mean over y in Ô^n of
`Space.finHeisOp` at the part of y above S ∪ S̄. -/
def projOn (S : Set (FinPlace E)) := strongIntegral ((latticeMeasure E n).restrict (stdLattice E n))
  fun y ↦ V.finHeisOp (idem S.conjClosure • y)

/-- The real vacuum projection: the bounded operator f ↦ ∫ exp(−|y|²/2) ϱ(y)f dy on 𝒮(V), y over
real vectors in Fock coordinates with measure `realMeasure`. -/
abbrev projReal := V.integrated vacVector

/-- For a matrix i over E and spaces V, V' with adelic frames x, x', the adelic matrix x⁻¹ i x'. -/
def ratMap (V' : Space E _ s') (i : Matrix n n' _) := V.x⁻¹.1 * i.map (toAdele (E := E)) * V'.x.1

open ComplexConjugate IsVacuum
variable {E : Type _} [Field E] [CMType E] [WeilData E]
  {n : Type _} [Fintype n] {s : n → ℤˣ} (V : Space E n s) (g : G E s) (c : ℂ) (x : n → 𝔸 E)
  (y : n → 𝔸 E) (f f' : 𝒮 V)

lemma ϱ_apply : V.ϱ y f x = (adelicHeis E s).β x y * f (x + y) := (by aesop : V.rawTheta _ = _)

lemma θ_apply : V.θ f = f 0 := rfl

lemma add_apply : (f + f') x = f x + f' x := map_add (_ ∘L _) ..

lemma smul_apply : (c • f) x = c * f x := map_smul (_ ∘L _) ..

lemma zero_apply : (0 : 𝒮 V) x = 0 := map_zero (_ ∘L _)

@[ext] lemma data_ext {f f' : 𝒮 V} : (∀ x, f x = f' x) → f = f' := DFunLike.ext _ _

instance : ContinuousEval (𝒮 V) _ ℂ := ⟨V.rawTheta.2.comp (by fun_prop)⟩

/-- Quasi-periodicity under rational vectors: for γ in E^n, with image γ′ in standard adelic
coordinates of V, and any adelic x, β(γ′, x) f̃(γ′ + x) = f̃(x), where f̃(x) = θ(ϱ(x)f). -/
lemma apply_vecAtPoint_add γ x : (adelicHeis E s).β (V.vecAtPoint γ) x * f (V.vecAtPoint γ + x) =
  f x := V.ϱ_apply .. ▸ V.isThetaFunctional_rawTheta.1 _ ⟨γ, rfl⟩ _

/-- The Weil representation is jointly continuous: the map (g, f) ↦ ω(g)f from G × 𝒮(V) to 𝒮(V)
is continuous. -/
@[fun_prop] lemma continuous_ω : Continuous fun p ↦ V.ω (.fst p) p.2 := continuous_weilRep ..

/-- The Weil operators intertwine the Heisenberg operators: ω(g)ϱ(x)f = ϱ(gx)ω(g)f for g in G, x
an adelic vector and f in 𝒮(V). -/
lemma ω_ϱ : V.ω g (V.ϱ x f) = V.ϱ (g.mat *ᵥ x) (V.ω g f) := weilRep_heisOp ..

/-- The form ⟨f, f'⟩ on 𝒮(V) equals the mean of conj(f(x)) f'(x) over adelic vectors x modulo
the rational vectors of V, data being read as functions by f(x) = θ(ϱ(x)f). -/
lemma dataInner_eq_quotMean : V.dataInner f f' = quotMean V.ratVectors fun x ↦ f' x * conj (f x) :=
  V.isThetaFunctional_rawTheta.elim (·.quotMean_eq ‹_›) _ _ ▸ (one_mul _).symm

lemma dataInner_rho : V.dataInner (V.ϱ x f) (V.ϱ x f') = V.dataInner f f' := modelInner_heisOp ..

/-- The Weil operators preserve the inner product: ⟨ω(g)f, ω(g)f′⟩ = ⟨f, f′⟩ for g in G and f,
f′ in 𝒮(V). -/
lemma dataInner_omega : V.dataInner (V.ω g f) (V.ω g f') = V.dataInner f f' := modelInner_weilRep ..

lemma eq_zero_of_dataInner_self {f} : V.dataInner f f = 0 → f = 0 := eq_zero_of_modelInner_self

lemma dataInner_vacElem_vacElem : V.dataInner V.vacElem V.vacElem = 1 :=
  (modelInner_vacElem ..).trans (by simp [vacElem, vacuumFn])

/-- For every adelic vector y, ⟨vac, ϱ(y)vac⟩ = e(y), where e is the vacuum function `vacuumFn`. -/
lemma dataInner_rho_of_vacElem : V.dataInner V.vacElem (V.ϱ y V.vacElem) = vacuumFn y := by
  erw [← conj_modelInner, modelInner_heisOp_vacElem, (adelicSum E s).isVacuum.4]

/-- For every g in G, the matrix coefficient ⟨vac, ω(g)vac⟩ is the inverse of the complex
conjugate of Δ(g). -/
lemma dataInner_omega_of_vacElem : V.dataInner V.vacElem (V.ω g V.vacElem) =
  (conj (weilMultiplier g))⁻¹ := by erw [modelInner_vacElem,
  eq_inv_of_mul_eq_one_right (conj_delta_mul_weilRep_vacElem ..), adelicAction]

attribute [simp] ϱ_apply θ_apply add_apply smul_apply zero_apply dataInner_rho dataInner_omega
  dataInner_vacElem_vacElem dataInner_rho_of_vacElem dataInner_omega_of_vacElem Prod.mk_one_one
  Circle.norm_coe WeilData.j_ne_zero v_uniformizer U.norm_det

/-- For f in 𝒮(V) and an adelic vector y, θ(ϱ(y)f) is the value f̃(y) of the function on 𝔸^n
attached to f. -/
lemma θ_ϱ : V.θ (V.ϱ y f) = f y := by simp

lemma norm_apply_le : ‖f x‖ ≤ ‖V.θ‖ * ‖f‖ := by simpa using V.θ.le_opNorm (V.ϱ x f)

/-- For f, f' in 𝒮(V), the family ⟨f', ϱ(γ)f⟩, γ running over the rational vectors of V, is
summable with sum θ(f) times the complex conjugate of θ(f'). -/
lemma hasSum_dataInner : HasSum (fun γ ↦ V.dataInner f' (V.ϱ (V.vecAtPoint γ) f)) (V.θ f * conj
  (V.θ f')) := by simpa [θ] using! V.isThetaFunctional_rawTheta.elim (·.hasSum_modelInner ‹_›) _ f

lemma ext_of_vacElem {Y} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y] {T T' :
  _ →L[ℂ] Y} (h : ∀ y, T (V.ω g (V.ϱ y V.vacElem)) = T' (V.ω g (V.ϱ y V.vacElem))) : T = T' :=
  (ContinuousLinearEquiv.arrowCongr (.ofUnit (V.ω.toHomUnits g⁻¹)) 1).injective (hom_ext h)

end Space

variable {n n' : Type} [Fintype n] [Fintype n'] {s : n → ℤˣ} {s' : n' → ℤˣ} (S : Space E n s)
  (T : Space E n' s') {m m' R : Type*} (a b : AutChar E) {E' : Type*} [Field E'] [NumberField E']

/-- For sign vectors s on n and s′ on n′, the sign vector on n′ × n given by the products
s′(i)s(j). -/
abbrev homSigns s s' := (pairSign 1 s' s : n' × n → _)

/-- A matrix x read as the function (i, j) ↦ x_{ij} on pairs (row, column). -/
def matToVec (x : Matrix m' m R) p := x (Prod.fst p) p.2

/-- Turns a function y on pairs of indices into the matrix with entries y(i,j). -/
def vecToMat (y : m' × m → R) := of fun i j ↦ y (i, j)

omit [Fintype n] [Fintype n'] in
@[simp] lemma stdForm_homSigns : stdForm _ (homSigns s s') = stdForm E' s' ⊗ₖ (stdForm _ s)ᵀ := by
  aesop (add simp [stdForm, pairSign, diagonal])

section

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n n' : Type} [Fintype n] [Fintype n']
  {s : n → ℤˣ} {s' : n' → ℤˣ}

/-- The homomorphism from G(s) × G(s′) to the adelic unitary group of the product signs sending
(g, h) to x ↦ hxg⁻¹ on n′ × n matrices. -/
def G.onHom := (toUnitary : G E (homSigns s s') ≃* _).symm.toMonoidHom.comp ((U.kron
  stdForm_mul_self stdForm_homSigns).comp (toUnitary.toMonoidHom.prodMap toUnitary.toMonoidHom))

/-- The determinant, as a homomorphism from the adelic unitary group of signs s to the group of
adeles x of E with x x̄ = 1. -/
def G.det := (U.det (isUnit_stdForm.map detMonoidHom)).comp (toUnitary : G E s ≃* _).toMonoidHom

/-- For g in the finite adelic unitary group, the determinant of the element (1, g) of G, as an
adele of norm one. -/
@[simp] abbrev detFin s (g : Gf E n) := G.det (s := s) (1, g)

end

/-- For hermitian spaces S, T, the space Hom(S,T), with rational Gram matrix J_T ⊗ J_S^{-T} and
adelic frame the Kronecker product x_T ⊗ x_S^{-T}. -/
@[simps -isSimp J] def Space.hom : Space E _ (homSigns s s') := by
  use! T.J ⊗ₖ S.J⁻¹ᵀ, T.x ⊗ₖ S.x⁻¹.1ᵀ, ↑T.x⁻¹ ⊗ₖ S.xᵀ
  repeat simp [gram_point, map_J_inv, map_kronecker, conjTranspose_nonsing_inv]

/-- The restriction of υ to the norm-one ideles, as a character of U(1)(𝔸) trivial on rational
points. -/
def WeilData.upsilonU1 :
    AutChar E := ⟨υ.1.comp ⟨Unitary.toUnits, .of_coeHom_comp (by fun_prop)⟩, fun _ ↦ (υ.2 _ ·)⟩

/-- For a character a of [U(1)] and a natural number k, the Hecke character x ↦ a(x/x̄)
υ(x)^(−k) of E. -/
def AutChar.spaceChar (k : ℕ) := a.baseChange * SplittingChar.υ⁻¹ ^ k

/-- For a character a of [U(1)] and a finite index set of size n, the character a·υ^⌊n/2⌋ of
[U(1)], υ restricted to norm-one ideles. -/
def rankTwist n [Fintype n] := a * WeilData.upsilonU1 ^ (Fintype.card n / 2)

/-- For characters a, b of [U(1)], the complex character (g, h) ↦ a(det h) b(det g)⁻¹ of G(s) ×
G(s′). -/
def pairChar : G E s × G E s' →* ℂ :=
  Circle.coeHom.comp ((b⁻¹.1.1.comp G.det).coprod (a.1.1.comp G.det))

/-- The representation (g,h) ↦ a(det h) b(det g)⁻¹ ω(x ↦ hxg⁻¹) of the product of the two adelic
unitary groups on the data space of Hom(S,T). -/
def pairWeil := MonoidHom.mk ⟨fun p ↦ pairChar a b p • (S.hom T).ω (.onHom p), by simp⟩
    (by simp [← smul_mul_smul])

/-- The theta kernel θ^{S,T}_{a,b}(f)(g, h) = θ(ω_{a,b}(g,h)f), for f in 𝒮(Hom(S,T)) and θ the
theta functional of Hom(S,T). -/
def pairTheta f p := Space.θ _ (pairWeil S T a b p f)
