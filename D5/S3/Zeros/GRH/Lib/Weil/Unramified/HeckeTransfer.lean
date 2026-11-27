/- GID: D5/S3/Zeros/GRH/Lib/Weil/Unramified/HeckeTransfer
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Unramified/HeckeTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Unramified.HeckeTransfer. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Unramified/HeckeTransfer.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Unramified.UniformiserScalar
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.PairSumNegation
import D5.S3.Zeros.GRH.Lib.Weil.Lift.Arrow
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Commutativity of the spherical Hecke algebra of GL_n; Eichler commutation relation
(known result; see Lib.General.LinearAlgebra.ColumnLattices).

This file: Eichler commutation relation of Hecke polynomials through theta lifts at split places. -/


open Matrix Fintype WeilData AutChar HeckeChar Valued Space G CharUnramifiedAt
open Finset hiding card

/-- Maximum principle: if v is bounded above, ∑|a_i| < l, and l·v(g) ≤ ∑|a_i|·v(r g i) for all g
(a finite sum), then v ≤ 0 everywhere. -/
lemma maximum_principle {G ι : Type*} [Fintype ι] {v} (hb : BddAbove (.range v)) {l} (a :
  ι → ℂ) (r : G → ι → G) (hl : ∑ i, ‖a i‖ < l) (h : ∀ g, l * v g ≤ ∑ i, ‖a i‖ * v (r g i)) g : v g ≤
  0 := by nlinarith [le_ciSup hb g, Real.mul_iSup_of_nonneg (hl.le.trans' (by positivity)) v ▸
  @ciSup_le _ _ _ ⟨g⟩ _ _ (by grw [h ·, le_ciSup hb, ← sum_mul])]

variable {E n m W Z : Type} [Field E] [CMType E] [Fintype n] [Fintype m] {w} [AddCommGroup W]
  [Module ℂ W] [AddCommGroup Z] [Module ℂ Z] {π : Representation ℂ (Gf E n) W} {a b : AutChar E} {k}
  (hk : card m = card n + k) (ha : CharUnramifiedAt a.baseChange.finPart w) (hb :
  CharUnramifiedAt b.baseChange.finPart w) (hw : w.IsSplit)

lemma FinPlace.q_eq_sqrt_sq : (w.q : ℂ) = √w.q ^ 2 := mod_cast by simp

lemma CharUnramifiedAt.apply_locFullIdele {χ} (h : CharUnramifiedAt (finPart χ) w) x :
  χ.1 (locFullIdele w x) =
  χ.atUnif w ^ (-(v x.1).log) := by simpa using! congr($(h.apply_locIdele_eq_zpow x).1)

lemma heckePolyOp_eq_sum {v} (hv : v ∈ sphericalAt π w) X : heckePolyOp π hw X v = ∑ U,
  heckePolyCoeff X U • π (atSplit hw (transposeGL (basicCosetRep U))) v ∧
  heckePolyOp π hw.star X v = ∑ U, heckePolyCoeff X U • π (atSplit hw (basicCosetRep U)⁻¹)
  v := by simp [heckePolyOp, heckePolyEval, ↓← mem_sphericalAt_iff, heckeSplit_star, *,
  heckeFun_basicDoubleCoset_inv, heckeSplit.eq_1 _ hw, heckeGL_eq_sum, sum_filter, smul_sum,
  sum_comm, heckePolyCoeff, card_ResField, le_card_of_mem_basicDoubleCoset (basicCosetRep_spec _).1]

@[simp] lemma HeckeChar.norm_atUnif (χ : HeckeChar E) w : ‖χ.atUnif w‖ = 1 := Circle.norm_coe _

/-- At a split place w of norm q, a vector fixed by the finite adelic unitary group of rank n is
spherical, and the Hecke polynomial acts on it by ∏_{l<n}(1 − q^l X). -/
lemma isSphericalWith_trivialHecke {v} (hv : ∀ g, π g v = v) : IsSphericalWith π hw
  (trivialHecke w.q (card n)) v := by simp [IsSphericalWith, heckePolyOp_eq_sum, *,
  ← sum_smul, by simpa [card_ResField] using q_binomial_submodule n (ResField w) ⊤]

include ha hw

lemma CharUnramifiedAt.det_maxCompactAt_eq_one {g s} (hg : g ∈ maxCompactAt n w) :
  a.1 (detFin s g) = 1 := by ext; erw [det_of_supportedOn, detOn_eq_prod, prod_singleton,
  ha.apply_locFullIdele] <;> simp_all [mem_intGL_iff_det.1 (mem_Kf_iff.1 ..)]


variable [WeilData E] {s t} {S : Space E n s} {T : Space E m t} {f p}
  (hf : (S.hom T).projOn {w} f = f)
include hb hf

/-- Let w be split, f vacuum at w, a, b unramified there. The Hecke sum at X of U(T), or U(S),
sends f to f named at w by `trivialHecke`(d − rk(x mod w), νX) on integral x; (d, ν) = (m,
a.frobValue n w), or (n, b.frobValue m w) (`AutChar.frobValue`). -/
lemma sum_heckePolyCoeff_smul_pairWeil X : let N d c :=
    (name _ {w} (residueDatum (fun _ ↦ w) fun x ↦ trivialHecke w.q (d - (x ()).rank)
    (X * c)) f); ∑ U, heckePolyCoeff X U • pairWeil S T a b ((1, 1), 1, atSplit hw (transposeGL
    (basicCosetRep U))) f = N (card m) (a.frobValue n w) ∧ ∑ U, heckePolyCoeff X U • pairWeil S T a
    b ((1, atSplit hw (basicCosetRep U)⁻¹), 1, 1) f = N (card n) (b.frobValue m w) := by
  nth_rw 2 3 [← hf]
  simp (disch := simp [*]) only [← name_boxIndicator, pairWeil_name_on, smul_name,
    ← _root_.sum_apply, ← map_sum, ← coe_singleton, detOn_eq_prod, frobValue, AutChar.spaceChar]
  constructor <;> congr with <;> simp [*, apply_locFullIdele, atUnif, ideleAbs_locFullIdele,
    charUnramifiedAt_upsilon, norm_locField_eq_q_zpow, basicCosetRep_spec, (basicCosetRep_spec
    _).1.2, -coe_units_inv, Real.sqrt_eq_rpow, ← Real.rpow_pow_comm, mem_integralBox,
    Real.inv_rpow, idem_mul_mem_Ô, ← evalAt_apply, matToVec, RingHom.map_matrix_mul, ite_and,
    ← transpose_apply (_ * Matrix.map _ _), -transpose_apply, @forall_comm m, ← card_ResField,
    residueDatum, v_mul_inv_le_one_iff
    (basicCosetRep_spec _).1, -rank_transpose, -mulVecLin_transpose, sum_filter, ↓card_sub_rank,
    ← rank_transpose (.map _ _), ← q_binomial_submodule, atSplit, Gf.atPlace, evalAt_star_locGL,
    ← GeneralLinearGroup.val_map_apply, -Units.coe_star] <;> congr! 3 <;> ring

include hk

/-- Hecke transfer: w split, ranks n of S, n + k of T, a, b unramified and f the vacuum at w, Λ
linear, Λ(ω(g,h)f) = π(g)ρ(h)Λf for finite g, h. Then Λf is K_w-fixed for π and ρ, and
P_w^ρ(X)Λf = ∏_{l<k}(1 − q^{l+n/2}χ_S(w)X)·P_{w̄}^π(q^{k/2}χ_Sχ_T⁻¹(w)X)Λf.

Known result: Commutativity of the spherical Hecke algebra of GL_n; Eichler commutation relation. -/
lemma hecke_transfer_of_equivariant (Λ : _ →ₗ[ℂ] W) π ρ (hΛ : ∀ g h,
  Λ (pairWeil S T a b ((1, g), 1, h) f) = π g (ρ h (Λ f))) : Λ f ∈ sphericalAt π w ∧
  Λ f ∈ sphericalAt ρ w ∧ ∀ X, heckePolyOp ρ hw X (Λ f) = trivialHecke w.q k (a.frobValue n w * X) •
  heckePolyOp π hw.star (w.q ^ k * a.frobValue n w / b.frobValue m w * X) (Λ f) := by
  simp [heckePolyOp_eq_sum, *, -hΛ, -map_inv, -map_smul, ← by simpa using And.intro (hΛ · 1) (hΛ 1),
    ← Prod.mk_one_one, pairWeil_eq_smul_of_projOn_eq {w}, det_maxCompactAt_eq_one _
    hw, -LinearMap.map_smulₛₗ, ← map_sum, sum_heckePolyCoeff_smul_pairWeil, smul_name,
    ← LinearMap.map_smul_of_tower]
  congr!
  simp [funext_iff, residueDatum, add_comm, prod_range_add, Nat.add_sub_assoc, rank_le_card_width]
  congr! 4 <;> simp [frobValue, atUnif, field, pow_add]

/-- Let w be split, ranks n of S, n + k of T, a, b unramified and f the vacuum at w, B bilinear,
ρ(h)B(f,v) = B(ω(g,h)f, π(g)v) for finite g, h, and v K_w-fixed. Then B(f,v) is K_w-fixed
and P_w^ρ(X)B(f,v) = ∏_{l<k}(1 − q^{l+n/2}χ_S(w)X)·B(f, P_w^π(q^{k/2}χ_Sχ_T⁻¹(w)X)v). -/
lemma hecke_transfer_of_pairing {ρ} {M : Submodule ℂ _} (B : M →ₗ[ℂ] W →ₗ[ℂ] Z) o (hB : ∀ g h v,
  ∃ Ψ, Ψ.1 = pairWeil S T a b ((1, g), 1, h) f ∧ ρ h (B ⟨f, o⟩ v) = B Ψ (π g v)) {v} (hv :
  v ∈ sphericalAt π w) : B ⟨f, o⟩ v ∈ sphericalAt ρ w ∧ ∀ X, heckePolyOp ρ hw X (B ⟨f, o⟩ v) =
  trivialHecke w.q k (a.frobValue n w * X) • B ⟨f, o⟩ (heckePolyOp π hw
  (w.q ^ k * a.frobValue n w / b.frobValue m w * X) v) := by
  obtain ⟨B, ⟨⟩⟩ := B.exists_extend
  have ⟨h, K, H⟩ := hecke_transfer_of_equivariant hk ha hb hw hf B (π.linHom 1) (.linHom 1 ρ)
    (by simp [DFunLike.ext_iff, by simpa using hB ·])
  use (congr($(K ·) v)), (by erw [← map_heckePolyOp (.applyₗ v) _ ?_, H ·,
    heckePolyOp_adjoint _ .applyₗ hv h] <;> simp)

/-- Let w be split, ranks n of S, n + k of T, a, b unramified and f the vacuum at w, f an arrow
e → e' (`IsArrow`). If y is spherical at w with Hecke eigenvalue p(X), so is its lift, with
∏_{l<k}(1 − q^{l+n/2}χ_S(w)X)·p(q^{k/2}χ_Sχ_T⁻¹(w)X). -/
lemma isSphericalWith_formLift {e e' y} (A : IsArrow (pairThetaKer S T a b) e e' f) (h :
  IsSphericalWith (S.formRep e) hw p y) : IsSphericalWith (T.formRep e') hw (fun X ↦ trivialHecke
  w.q k (a.frobValue n w * X) * p (w.q ^ k * a.frobValue n w / b.frobValue m w * X)) (formLift
  (pairThetaKer S T a b) e _ f y) := (hecke_transfer_of_pairing hk ha hb hw hf (.domRestrict _ ⊤) ⟨⟩
  (by simp [← A.formRep_formLift]) h.1).imp_right (by simp [h.2, mul_smul])
