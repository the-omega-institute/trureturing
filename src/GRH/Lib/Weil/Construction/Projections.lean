import GRH.Lib.Weil.Construction.PairDefs
import GRH.Lib.Weil.Fock.FockHarmonicCoeff
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Lattice vacuum projections at finite places and their interaction with the Weil
action. -/

namespace Space

open MeasureTheory Matrix Set AddChar Prod Heisenberg Rep Gf Circle stdLattice _root_.Sum
  OrthogonalSum Set.Sum IsVacuum
variable {E : Type*} [Field E] [CMType E] [WeilData E] {n}
  [Fintype n] {s} (V : Space E n s) {S : Set (FinPlace E)} {Y} [NormedAddCommGroup Y]
  [NormedSpace ℂ Y] [CompleteSpace Y] (g x y v w f f') (L : 𝒮 V →L[ℂ] Y)

@[simp] lemma heisRep_left_rho : (V.heisRep.left (adelicSum E s)).ρ y =
  V.ϱ (realVec y) := by simp [left]

attribute [local simp] IsOpen.measurableSet isOpen_stdLattice fst_sum snd_sum Measure.real
  mem_integralBox finVec idem_mul_self smul_smul idem_apply smul_mem_stdLattice idem_mul_mem_Ô
  realVec rep_apply_apply stdForm finMultiplier_ne_zero finMultiplier_inv weilMultiplier
  realMultiplier stdAddChar ω_ϱ finHeisOp

lemma heisRep_right_rho : (V.heisRep.right (adelicSum E s)).ρ y =
  V.ϱ (finVec y) := congr(V.ϱ ($(mul_zero _), _ * y ·))

lemma rho_finVec : V.ϱ (finVec x) (V.ϱ (finVec y) f) = psi₀ E (half * star y ⬝ᵥ x) • V.ϱ
  (finVec (x + y)) f := by simp [← heisRep_right_rho, stdLattice.finHeis]

lemma finHeisOp_finHeisOp : V.finHeisOp x (V.finHeisOp y f) = psi₀ E (star traceOneAdele * star y ⬝ᵥ
  x) • V.finHeisOp (x + y) f := by simp [↓rho_finVec, ← semichar_add]; ac_rfl

lemma dataInner_finHeisOp : V.dataInner (V.finHeisOp x f) (V.finHeisOp x f') =
  V.dataInner f f' := by simp [semichar, psi₀_apply, ← coe_inv_eq_conj]

@[simp] lemma semichar_ne_zero : semichar (x : n → 𝔸f E) ≠ 0 := coe_ne_zero _

lemma ϱ_swap : V.ϱ x (V.ϱ y f) = (adelicHeis E s).β x y ^ 2 • V.ϱ y (V.ϱ x f) := by
  simp [add_comm, sq, mul_assoc]

lemma rho_integrated {y} (hy : ∀ i, (y i).1 = 0) : V.ϱ y (V.integrated v f) = V.integrated v
  (V.ϱ y f) := by apply map_integrated; simp_all [left, adelicHeis, dotProduct, add_comm]

lemma integrated_realHeisOp : V.integrated (realHeisOp y v) f =
  V.ϱ (realVec y) (V.integrated v f) := by simp [integrated]

lemma rho_integrated_realCoord : V.ϱ y (V.integrated v f) =
  V.integrated (realHeisOp (realCoord y) v) (V.ϱ (0, y · |>.2) f) := by rw [integrated_realHeisOp,
  ← rho_integrated, mul, realVec_realCoord_add] <;> simp [adelicHeis, dotProduct]

lemma exists_rho_integrated_eq : ∃ w, ∀ f, V.ϱ y (V.integrated v f) =
  V.integrated w (V.finHeisOp (finCoord y) f) := ⟨(semichar (finCoord y))⁻¹ • realHeisOp
  (realCoord y) v, by simp [rho_integrated_realCoord, finVec.eq_unfold]⟩

omit [Fintype n] in
lemma _root_.mulVec_finVec {n₁} [Fintype n₁] (m : Matrix n n₁ (𝔸 E)) y : m *ᵥ finVec y = finVec
    (m.map (·.2) *ᵥ y) := by ext <;> simp [mulVec_eq_sum, Finset.mul_sum, mul_assoc]

@[simp] lemma omega_finHeisOp : V.ω g (V.finHeisOp x f) =
  V.finHeisOp (g.2 *ᵥ x) (V.ω g f) := by simp [semichar, mulVec_finVec]; rfl

omit [WeilData E] in
@[simp] lemma idem_univ : idem univ = (1 : 𝔸f E) := by aesop

omit [WeilData E] in
lemma _root_.Gf.mulVec_mem_integralBox (g : Gf E n) (h : ∀ w ∈ S, atPlace w g ∈ Kw ..) {x} :
  g.1.1 *ᵥ x ∈ integralBox n S ↔ x ∈ integralBox n S := by
  simpa [@forall_comm n, ← evalAt_apply, RingHom.map_mulVec] using!
    forall₂_congr (mulVec_mem_intVectors_iff <| h · ·)

lemma map_projOn {f} {F : _ → _} (h : ∀ y ∈ stdLattice E n, L (V.finHeisOp (idem S.conjClosure • y)
  f) = F y := by tauto) : L (V.projOn S f) = ∫ y in stdLattice E n, F y ∂latticeMeasure E n := by
  erw [← setIntegral_congr_fun (by simp) h, strongIntegral_apply _ _ fun _ ↦ ?_,
    L.integral_comp_comm] <;>
    exact isCompact_stdLattice.integrableOn _ (by simp; fun_prop [finVec, semichar])

@[simp] lemma projOn_ϱ {y} (h : ∀ i, ∀ w ∈ S.conjClosure, (y i).2 w = 0) f : V.projOn S (V.ϱ y f) =
  V.ϱ y (V.projOn S f) := (V.map_projOn 1).trans (V.map_projOn _ (by simp [adelicHeis,
  ϱ_swap _ y, dotProduct, ← mul_rotate, show ∀ i, (y i).2 * idem S.conjClosure = 0 by aesop])).symm

@[simp] lemma projOn_integrated : V.projOn S (V.integrated v f) =
  V.integrated v (V.projOn S f) := by apply map_integrated; bound

@[simp] lemma integrated_integrated : V.integrated v (V.integrated w f) = w 0 • V.integrated v
  f := by erw [← map_integrated _ (V.integrated.flip f), integrated_eq_smul] <;> simp [integrated]

/-- For g = (g_∞, g_f) in the adelic unitary group, ω(g)(v⊗f) = (ω(g_∞)v) ⊗ ω(g_f)f, where g_∞
acts on the real datum v in the Fock model. -/
lemma omega_integrated : V.ω g (V.integrated v f) = V.integrated (realWeil (blockU g.1) v)
  (V.ω g.2 f) := have k g := weilRep_tmul _ adelicAction (realAction _)
                   finAction congr($(realMultiplier_blockU _) * _).symm (mat_mulVec_adelicSum g)
  by congrm $((V.ext_of_vacElem 1 fun _ ↦ ?_ : _ * _ =
    V.integrated _ * _)) f; simp [-ω_ϱ]; erw [vacElem, ← (adelicSum ..).tmul_vacElem, heisOp_tmul,
    integrated_integrated, k, map_smul, k, eq_comm, integrated_integrated]; simp; rfl

/-- For f in 𝒮(V), ⟨vac, f⟩vac = P^∞P^all f, where P^∞ = `Space.projReal` is the projection on
real vacua and P^all is `Space.projOn` for the set of all finite places. -/
lemma dataInner_vacElem_smul_vacElem : V.dataInner V.vacElem f • V.vacElem =
  V.projReal (V.projOn univ f) := by
  erw [modelInner_vacElem, ← integrated_eq_smul, vacElem, ← (adelicSum ..).tmul_vacElem,
    integrated_tmul, map_projOn, map_integrated_eq_integral]
  simp [← integral_indicator, indicator_smul_left, ← heisRep_right_rho]; rfl

lemma integrated_finHeisOp : V.integrated v (V.finHeisOp y f) =
  V.finHeisOp y (V.integrated v f) := by simp [rho_integrated, finVec.eq_unfold]

attribute [-simp] finHeisOp

lemma finHeisOp_comm : V.finHeisOp x (V.finHeisOp y f) =
  psi₀ E (star y ⬝ᵥ x) • V.finHeisOp y (V.finHeisOp x f) := by simp [finHeisOp_finHeisOp,
  add_comm, star_dotProduct x, ← star_mul', -star_mul, psi₀_star, ← map_add_eq_mul]; grind

@[local simp] lemma finHeisOp_add {x y} : x ∈ stdLattice E n → y ∈ stdLattice E n → ∀ f,
  V.finHeisOp (x + y) f = V.finHeisOp x (V.finHeisOp y f) := by simp_all [finHeisOp_finHeisOp,
  psi₀_eq_one_of_mem ∘ mul_mem (star_mem_Ô traceOneAdele_mem), dot_mem]

lemma map_projOn_eq_const {f c} : (∀ y ∈ stdLattice E n, L (V.finHeisOp (idem S.conjClosure • y)
  f) = c) → L (V.projOn S f) = c := (by simp [V.map_projOn L ·])

lemma finHeisOp_projOn {y} (hy : y ∈ stdLattice E n) f :
  V.finHeisOp (idem S.conjClosure • y) (V.projOn S f) = V.projOn S f :=
  by rw [@map_projOn, setIntegral_add_mem, ← V.map_projOn 1] <;> aesop

lemma dataInner_projOn : V.dataInner (V.projOn S f) f' = V.dataInner f (V.projOn S f') := by
  have k f f' := V.map_projOn_eq_const (S := S) _ fun _ ↦
    (V.finHeisOp_projOn · f ▸ V.dataInner_finHeisOp _ _ f')
  erw [← k, ← conj_modelInner, k, conj_modelInner]; rfl

@[simp] lemma finHeisOp_vacElem {V : Space E n s} {y} (h : y ∈ stdLattice ..) :
  V.finHeisOp y V.vacElem = V.vacElem := by
  simpa [integrated_finHeisOp, ← dataInner_vacElem_smul_vacElem]
    using congr(V.projReal $(V.finHeisOp_projOn (S := ⊤) h V.vacElem))

@[simp] lemma projOn_vacElem : V.projOn S V.vacElem = V.vacElem :=
  V.map_projOn_eq_const 1 (by aesop)

@[simp] lemma projReal_vacElem : V.projReal V.vacElem = V.vacElem := by simpa using
  (V.dataInner_vacElem_smul_vacElem V.vacElem).symm

lemma dataInner_omega_left : V.dataInner (V.ω g f) f' =
  V.dataInner f (V.ω g⁻¹ f') := by simp [← V.dataInner_omega g f]

seal integrated
variable {g f} (hg : g ∈ supportedOn n S) (h : V.projOn S f = f)

include h in
lemma projOn_finHeisOp y : V.projOn S (V.finHeisOp y f) =
  boxIndicator n S.conjClosure y • V.finHeisOp y f := by
  erw [boxIndicator, ← integral_psi₀_stdLattice, ← integral_smul_const, ← h]
  exact V.map_projOn 1 (by simp +contextual [finHeisOp_comm, finHeisOp_projOn])

/-- The operator P^S = `Space.projOn` S multiplies the coefficient function c(y) of an
element of 𝒮(V) by the indicator that the finite part of y lies in αÔ^n at all places of S ∪
S̄. -/
lemma projOn_val f y : (V.projOn S f).1 y = boxIndicator n S.conjClosure (finCoord y) * f.1 y := by
  erw [← modelInner_heisOp_vacElem, ← modelInner_heisOp_vacElem, ← dataInner_projOn,
    (V.projReal_vacElem ▸ (exists_rho_integrated_eq ..).choose_spec _ :)]
  simp [projOn_finHeisOp, -ite_smul]; rfl

lemma projOn_empty f : V.projOn ∅ f = f := IsVacuum.ext (by simp [projOn_val])

lemma projOn_union {S'} f : V.projOn (S ∪ S') f = V.projOn S (V.projOn S' f) :=
  IsVacuum.ext (by simp [projOn_val]; grind)

/-- If g in G has component in GL_n(O_w) at every place w of S, then ω(g) commutes with P^S =
`Space.projOn` S. -/
lemma ω_projOn {g : G E s} (h : ∀ w ∈ S, g.2.atPlace w ∈ Kw ..) f :
    V.ω g (V.projOn S f) = V.projOn S (V.ω g f) := sub_eq_zero.1 (V.eq_zero_of_dataInner_self (by
  have A g h f := V.map_projOn_eq_const (.id ..) fun y
    l ↦ by simpa using congrArg (V.ω g) (V.finHeisOp_projOn (S :=
    S) ((g.2⁻¹.mulVec_mem_integralBox h).2 (smul_mem_stdLattice (idem_mem_Ô S.conjClosure) l)) f)
  simp_all [dataInner_projOn, dataInner_omega_left, ← projOn_union, ← inv_mk, or_imp,
    atPlace_star_mem_iff.1 ∘ h _]))

include h

/-- Let P^S f = f (`Space.projOn`), and let L be a bounded linear map from 𝒮(V) to a complex Banach
space Y killing v_P ⊗ ϱ_f(y)vac (`Space.finHeisOp`) for all polynomials P and all finite y zero
above S ∪ S̄. Then L(f) = 0. -/
lemma ext_integrated {L : _ →L[ℂ] Y} (H : ∀ P y, (∀ i, ∀ w ∈ S.conjClosure, y i w = 0) →
  L (V.integrated (polyVector _ P)
  (V.finHeisOp y V.vacElem)) = 0) : L f = 0 := h ▸ congr($((V.ext_of_vacElem 1 fun y ↦ by
  simp [-mem_integralBox, projOn_finHeisOp, apply_ite,
    V.projReal_vacElem ▸ (exists_rho_integrated_eq ..).choose_spec _]; intro k
  erw [← finHeisOp_vacElem (neg_mem k), finHeisOp_finHeisOp, map_smul, map_smul, isClosed_property
    denseRange_polyVector (L ∘L .flip _ _).isClosed_ker (H · _ _)] <;> aesop : L ∘L _ = 0)) f)

include hg

/-- If g in G_f is supported on S ∪ S̄ and P^S f = f, where P^S = `Space.projOn` S, then P^S
ω(g)f = Δ_f(g⁻¹)⁻¹ f. -/
@[local simp] lemma projOn_ω : V.projOn S (V.ω g f) = (finMultiplier g⁻¹)⁻¹ • f :=
  sub_eq_zero.1 (V.ext_integrated (L := _ * V.ω _ - (_ : ℂ) • 1) h fun P y _ ↦ by
  have e := congr(V.integrated P
    (V.finHeisOp y $(V.dataInner_vacElem_smul_vacElem (V.ω g V.vacElem))))
  erw [projOn, (by grind : conjClosure _ = conjClosure (S ∪ S.conjClosureᶜ)), projOn_union] at e
  simp_all [← ω_projOn, omega_integrated, ← integrated_finHeisOp]
  simp_all [finHeisOp, realVac, show g *ᵥ y = y by ext _ w; by_cases w ∈ S.conjClosure <;> simp_all
              [Gf.atPlace, mulVec_eq_sum, ← evalAt_apply, GeneralLinearGroup.ext_iff]])

/-- If the finite unitary g is supported on S ∪ S̄ and stabilises the standard lattice, and P^S
f = f, then ω(g)f = f. -/
lemma ω_of_mem_Kf (hk : g ∈ Kf ..) : V.ω g f = f :=
  h ▸ by simp_all [↓ω_projOn, finMultiplier_eq_one_of_mem, mem_Kf_iff]

omit h hg

lemma omega_vacElem : V.ω g V.vacElem =
  finMultiplier g • V.ω g (V.projOn univ (V.ω ↑g⁻¹ V.vacElem)) := by simp

/-- For g in G_f, ω(g)vac equals Δ_f(g)|Δ_f(g)|⁻² times the sum of ϱ_f(gy)vac over coset
representatives y of Ô^n ∩ g⁻¹Ô^n in Ô^n, where ϱ_f = `Space.finHeisOp`. -/
lemma omega_vacElem_sum : V.ω g V.vacElem = (finMultiplier g / ‖finMultiplier g‖ ^ 2) • ∑ᶠ q :
  _ ⧸ ((stdLattice E n).comap g.1.1.mulVecLin).addSubgroupOf (stdLattice E n), V.finHeisOp (g *ᵥ
  q.out.1) V.vacElem := by erw [omega_vacElem, map_projOn, setIntegral_eq_finsum (L := (stdLattice E
  n).comap g.1.1.mulVecLin) isCompact_stdLattice (isOpen_stdLattice.preimage (by continuity))
  (add_left_surjective · |>.forall.2 _), latticeMeasure_inter_eq_glMultiplier] <;> simp_all
  [finMultiplier, division_def, ← Complex.coe_smul]
