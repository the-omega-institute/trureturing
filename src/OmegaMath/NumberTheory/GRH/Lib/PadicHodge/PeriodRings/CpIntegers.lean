import OmegaMath.NumberTheory.GRH.Lib.General.Algebra.AdicRingHomExt
import OmegaMath.NumberTheory.GRH.Lib.General.Algebra.RingActions
import OmegaMath.NumberTheory.GRH.Lib.ClassField.Places.ProfiniteGalois
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Fontaine's period rings and the fundamental exact sequence (known result; see
Lib.PadicHodge.PeriodRings.BdR).

This file: C_p, its integers, isometric Galois action; functoriality of tilt, untilt and Fontaine's
θ. -/

open Ideal Metric NeZero PadicComplex Perfection ValuationRing Valued UniformSpace.Completion

attribute [-simp] IsUnit.dvd RCLike.norm_natCast

variable {p : ℕ} [Fact p.Prime] {R R' : Type} [CommRing R] [CommRing R'] [Fact ¬IsUnit (p : R)]
  [Fact ¬IsUnit (p : R')] (f : R →+* R') (x : PreTilt R p)

/-- For a ring homomorphism f: R → R', the induced ring homomorphism between the inverse limits
of R/p and R'/p along x ↦ x^p. -/
def tiltMap : PreTilt R p →+* PreTilt R' p := Perfection.map p (quotientMap _ f (by simp))

lemma coeff_tiltMap {x : PreTilt R p} {n} {y : R} (h : y = coeff _ p n x) :
    f y = coeff _ p n (tiltMap f x) := .symm (congrArg _ h.symm)

lemma tiltMap_id : tiltMap (.id R) x = x := congrArg (x.map p ·) Quotient.factor_eq

lemma tiltMap_comp {R''} [CommRing R''] [Fact ¬IsUnit (p : R'')] f
    (g : R' →+* R'') (x : PreTilt R p) : tiltMap (g.comp f) x = tiltMap g (tiltMap f x) :=
    Perfection.ext (by (repeat erw [coeff_map]); rcases coeff _ _ · x; rfl)

/-- Let b be a perfect ring of characteristic p and R a p-adically separated commutative ring.
Two ring homomorphisms W(b) → R that agree on all Teichmüller lifts are equal. -/
lemma witt_hom_ext {b R} [CommRing b] [CharP b p] [PerfectRing b p] [CommRing R]
    [IsHausdorff (span {(p : R)}) R] {f g : _ →+* R} (h : ∀ x : b, f (WittVector.teichmuller p x) =
    g (.teichmuller p x)) : f = g := ringHom_ext_of_approx (⟨_, by simp [h], .trans
    ⟨_, pow_succ ..⟩ <| WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff · ·⟩)

variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : R')}) R']

@[simp] lemma untilt_tiltMap : (tiltMap f x).untilt = f x.untilt := teichmuller_spec
    (⟨f <| (powMulEquiv _ p).symm^[·] x |>.untilt, coeff_tiltMap f (by aesop), by simp [← map_pow]⟩)

lemma fontaineTheta_map_tiltMap x : WittVector.fontaineTheta _ p (.map (tiltMap f) x) =
  f (WittVector.fontaineTheta
  R p x) := by simp_rw [← RingHom.comp_apply]; congrm $(witt_hom_ext (by simp)) _

/-- Let R be a p-adically complete, integrally closed domain in which p is not a unit. For x, y
in the tilt of R, x^♯ divides y^♯ in R if and only if x divides y. -/
lemma untilt_dvd_iff [IsDomain R] [IsIntegrallyClosed R] : ∀ {x y : PreTilt R p}, x.untilt ∣
  y.untilt ↔ x ∣ y := @((quotientMulEquiv ..).surjective.forall₂.2 fun x y ↦ ⟨fun h ↦ map_dvd _ (by
  repeat erw [teichmuller₀_mapMonoidHom_idealQuotientMk] at h
  have K := @coeffMonoidHom_pow_p_pow_self R _ p
  choose e he using ((IsIntegrallyClosed.pow_dvd_pow_iff out).1 <| K y · ▸ K .. ▸ h)
  by_cases ∀ n, x.coeffMonoidHom _ _ n ≠ 0
  use ⟨e, by simpa [*, mul_pow] using y.coeffMonoidHom_pow_p⟩, extMonoid he
  use 1, extMonoid (by grind [pow_eq_zero_iff, ne p])), map_dvd _⟩)

lemma untilt_surjective_of_isAIC [h : IsAIC R] :
    (PreTilt.untilt : PreTilt R p → R).Surjective := (⟨_, teichmuller₀_mapMonoidHom_idealQuotientMk
    (x := ⟨Nat.rec · _, fun _ ↦ Function.surjInv_eq (h.exists_pow_eq p) _⟩)⟩)

lemma fontaineTheta_surjective_of_isAIC [IsAIC R] : (⇑(WittVector.fontaineTheta R p)).Surjective :=
  untilt_surjective_of_isAIC.forall.2 (⟨_, WittVector.fontaineTheta_teichmuller ·⟩)

variable [IsDomain R] [ValuationRing R]

/-- the tilt of a complete valuation ring is a domain -/
instance : IsDomain (PreTilt R p) := @NoZeroDivisors.to_isDomain _ _ (coeff _ p 0).domain_nontrivial
    ⟨by simp [← zero_dvd_iff, ← untilt_dvd_iff]; simp [← WittVector.fontaineTheta_teichmuller]⟩

instance : ValuationRing (PreTilt R p) := iff_dvd_total.2 ⟨by simp [← untilt_dvd_iff, dvd_total]⟩

/-- The absolute Galois group G_p = Gal(Q̄_p over Q_p). -/
abbrev Gp (p : ℕ) [Fact p.Prime] := Gal(PadicAlgCl p/ℚ_[p])

/-- The ring of integers O_C of the field C_p of p-adic complex numbers. -/
abbrev OC {p} [ThePrime p] := ↥𝓞_ℂ_[p]

/-- The valuation ring of ℚ̄_p. -/
noncomputable abbrev intQpBar (p : ℕ) [Fact p.Prime] := (PadicAlgCl.valued p).v.valuationSubring

@[simp] lemma mem_OC {x} : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by simp [norm_eq_norm, Valuation.norm_def]; rfl

lemma valuation_intQpBar_le_iff x y : intQpBar p x ≤ intQpBar p y ↔ ‖x‖ ≤ ‖y‖ :=
  v.isEquiv_valuation_valuationSubring.symm ..

@[simp] lemma valuation_intQpBar_lt_one_iff {z} : intQpBar p z < 1 ↔ ‖z‖ < 1 := by simpa using
  (valuation_intQpBar_le_iff 1 z).not

instance : IsIsometricSMul (Gp p) (PadicAlgCl p) :=
    ⟨(AddMonoidHomClass.isometry_of_norm · (spectralNorm_eq_of_equiv _ · |>.symm))⟩

instance :
    UniformContinuousConstSMul (Gp p) (PadicAlgCl p) := ⟨(isometry_smul _ · |>.uniformContinuous)⟩

instance : IsIsometricSMul (Gp p) ℂ_[p] := ⟨(isometry_smul _ · |>.completion_map)⟩

@[simp] lemma smul_coe_Cp (g : Gp p) x : g • x = (g x : ℂ_[p]) := mod_cast rfl

/-- The action of `Gp p` on `ℂ_p` is continuous. -/
instance : ContinuousSMul (Gp p) ℂ_[p] := ⟨continuous_prod_of_dense_continuous_lipschitzWith' _ 1
    denseRange_coe (isometry_smul _ · |>.lipschitz) (by
  simpa using! (isLocallyConstant_smul · |>.comp coe' |>.continuous))⟩

noncomputable instance completionAction : MulSemiringAction (Gp p) ℂ_[p] :=
  let f g := mapRingHom (MulSemiringAction.toRingHom ..) (continuous_const_smul g)
  ⟨(f · |>.map_one), (f · |>.map_mul)⟩

@[simp] lemma norm_smul_Cp (g : Gp p) (x : ℂ_[p]) : ‖g • x‖ = ‖x‖ := by simpa using dist_smul g x 0

instance : UniformContinuousConstSMul ℤ_[p] (PadicAlgCl p) := ⟨(uniformContinuous_const_smul ·.1)⟩

variable {p : ℕ} [ThePrime p] (x y : OC)

@[local simp] lemma OC.dvd_iff_norm_le : x ∣ y ↔ ‖y.1‖ ≤ ‖x.1‖ := by
  simp [norm_eq_norm, Valuation.norm_def, (PadicComplexInt.integers p).dvd_iff_le]

noncomputable instance :
    MulSemiringAction (Gp p) OC := (IsInvariantSubring.mk (by simp)).toMulSemiringAction

@[simp] lemma OC.coe_smul (g : Gp p) (x : OC) : (g • x).1 = g • x := rfl

/-- The p-adic cyclotomic character of the absolute Galois group of Q_p, obtained from its
action on the algebraic closure of Q_p. -/
noncomputable abbrev cyclotomicGp := cycChar (Γ := Gp p) (PadicAlgCl p) p

instance : Fact ¬IsUnit (p : OC) := ⟨by simp [isUnit_iff_dvd_one, norm_p_lt_one]⟩

lemma OC.exists_dvd_pow {s t : OC} : ¬IsUnit s → t ≠ 0 → ∃ n, t ∣ s ^ n := by
  simp_all [isUnit_iff_dvd_one, exists_pow_lt_of_lt_one, le_iff_lt_or_eq, exists_or, or_imp]

instance : IsLocalization.Away (p : OC) ℂ_[p] := .mk _ (by simp [ne]) (pow_unbounded_of_one_lt ‖·‖
    (by simp [Fact.out] : 1 < (p : ℝ)) |>.imp (by simp [norm_p_eq_inv]; clear x y; bound)) (by simp)

instance : IsAdicComplete (span {(p : OC)}) OC := (IsAdic.isAdicComplete_iff <|
    IsTopologicalAddGroup.ext ⟨⟩ inferInstance <| (nhds_basis_closedBall_pow (by simp [ne])
    (norm_p_lt_one
  (F := ℂ_[p]))).eq_of_same_basis <| by convert hasBasis_nhds_zero_adic _; ext; simp [
  span_singleton_pow, mem_span_singleton]).2 ⟨(isClosed_integer _).completeSpace_coe, inferInstance⟩

instance : IsAIC OC := .of_isIntegrallyClosedIn ℂ_[p]
