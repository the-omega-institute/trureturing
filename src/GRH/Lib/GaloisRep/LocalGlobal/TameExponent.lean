import GRH.Lib.ClassField.Local.ArtinMapAtPlace
import GRH.Lib.LocalGL.Green.GreenTau
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Local-global compatibility at tame level, away from and at l (known result; see
Lib.GaloisRep.LocalGlobal.LabelCompatibility).

This file: Fundamental tame characters of inertia; existence of exponents; link with local
reciprocity. -/


open NumberField Polynomial Ideal Quotient IsAlgClosed Fint IsLocalRing RingHom algebraMap
variable {E : Type} [Field E] [EmbeddedNumberField E] (w : FinPlace E) (A : ClosurePlace) {K : Type}
  [Field K] [Algebra (ResField w) K] (T) [IsFaithfulMulChar K T] (f) (s : Gal(Ω/E)) (a)

lemma exists_resField_hom {R} [Field R] (g : _ →+* R) (h : w.1 ≤ ker g) : ∃ j : ResField w →+* R,
    ∀ x, j (algebraMap _ _ x) = g x :=
  ⟨_, liftOfSurjective_comp_apply _ (algebraMap_ResField_surjective w) ⟨g, by simpa [LE.le]⟩⟩

/-- With Q = q_w^f > 1: s lies in inertia at A and T(residue in K of sz/z) = exp(2πi/(Q−1))^a,
for some z with z^{Q−1} in E a uniformiser. -/
def IsTameExponent := IsPlaceOver A w ∧ f ≠ 0 ∧ s ∈ inertiaGroup _ A ∧ ∃ (φ : 𝓞 Ω →+* K) (π : E)
  (z : Ω) (t : 𝓞 Ω), centrePrime Ω A ≤ ker φ ∧ (∀ x : 𝓞 E, φ x = (x : ResField w)) ∧ IsUniformiser A
  π ∧ z ^ (w.q ^ f - 1) = π ∧ t = s z / z ∧ T (φ t) = .exp (2 * Real.pi * .I / (w.q ^ f - 1 :)) ^ a

variable {w A f s a}
open Nat

/-- Whenever `IsTameExponent` relates s to the exponent a, P holds for s and ∏_x (X −
ι(T(x)^a)), over the roots x of c in K with multiplicity. -/
def IsLabelledAt {ℓ} [ThePrime ℓ] [PadicIso ℓ] A T f (P : _ → _ → Prop) (c : (ResField w)[X]) :=
  ∀ ⦃s a⦄, IsTameExponent w A T f s a → P s ((c.aroots K).map fun x ↦ X - C (ιℓ ((T ^ a) x))).prod

/-- Let `IsTameExponent` relate s to the exponent a at A above w, T injective, and let u be a
local unit with local Artin image s. Then (T^a)(x_χ) = χ(residue of u) for every character χ
of k_w^×, x_χ = `charName` T χ. -/
lemma IsTameExponent.pow_apply_charName {d} (h : IsTameExponent w A T f s a) {u} (hu :
  Valued.v u.1 = 1) (b : localArtin _ A w u =
  ⟦⟨s, d⟩⟧) χ : (T ^ a) ((charName T χ).1 : ResField w) = χ (residue _ ⟨u, hu.le⟩) := by
  obtain ⟨⟨c, q, _, ρ, π, z, t, o, _, p, r, _, e⟩, ⟨k, l⟩, x, g⟩ := h,
    w.q.sub_one_dvd_pow_sub_one f, algebraMap_ResField_surjective w (residue _ ⟨u, hu.le⟩)
  rw [l, pow_mul'] at r
  grind [thetaChar_charName, card_ResField, =_ (thetaChar_apply_pow T w.one_lt_q · (by simp [q,
    ne_of_gt]) l e), algebraMap_pow_card_pred_eq_one, mem_ker, @o (t ^ k - x) (by
    simpa [*, div_pow, mem_centrePrime] using!
      (c.localArtin_tame_symbol p hu b r).1 (residue_eq_iff_valuation_sub_lt_one.1 g.symm))]

/-- Let c be a label of degree r over the residue field k_w and x a root of c in K. Then
x^{q_w^{r!} − 1} = 1, and x^{q_w^d − 1} = 1 for some d with 1 ≤ d ≤ r. -/
lemma IsLabel.root_pow_eq_one {c : (ResField w)[X]} {r} (h : IsLabel r c) {x : K} (hx : aeval x c =
    0) : x ^ (w.q ^ (r)! - 1) = 1 ∧ ∃ d ∈ Set.Icc 1 r, x ^ (w.q ^ d - 1) = 1 :=
  have i := minpoly.irreducible ⟨c, h.1, hx⟩
  by grind [card_ResField, aroots_pow_eq_frobenius_orbit i (j := 1) (K := K), aeval_def,
    eval₂_at_zero, map_eq_zero,
    IsLabel, pow_pred_eq_one_iff, root_pow_card_pow_eq_self_iff, minpoly.aeval, dvd_factorial,
    i.natDegree_pos, natDegree_le_natDegree, minpoly.min, one_lt_pow₀ w.one_lt_q]

/-- For A above w, T injective and Q = q_w^{f!}: every s in the inertia group of A has a tame
exponent a (`IsTameExponent`), which can be taken coprime to Q − 1 for the chosen tame
generator, and some s has exponent 1. -/
lemma exists_isTameExponent (hA : IsPlaceOver A w) f :
  (∃ s : inertiaGroup _ A, IsTameExponent w A T (f)! s.1 1) ∧ ∀ s ∈ inertiaGroup _ A, ∃ a,
  IsTameExponent w A T (f)! s a ∧ (s = hA.tameGenerator → a.Coprime (w.q ^ (f)! - 1)) := by
  obtain ⟨_, H : NeZero ((w.q ^ (f)! - 1 :) : ResField w)⟩ := hA.centrePrime_liesOver,
    ⟨by simp [← card_ResField, Fin.pos']⟩
  let := Quotient.field w.1
  let := Algebra.compHom K (lift w.1 (algebraMap _ (ResField w)) (by simp))
  let ρ := (lift : _ →ₐ[_ ⧸ w.1] K).1.comp (mk (centrePrime Ω A))
  obtain ⟨_, n, hv⟩ := H.of_faithfulSMul _ K, H.of_neZero_natCast,
    hA.valuation_natCast_eq_one_iff.2 (mt algebraMap_ResField_eq_zero.2 (mod_cast H.1))
  choose π z u hz g using hA.exists_tameGenerator.choose_spec _ hv
  choose j _ G k using ((isRoot_cyclotomic_iff.1 (map_cyclotomic _ ρ ▸ (isRoot_cyclotomic_iff.2
    g.toInteger_isPrimitiveRoot).map)).map_of_injective
    IsFaithfulMulChar.injective).isPrimitiveRoot_iff.1 (Complex.isPrimitiveRoot_exp _ n.1)
  apply g.pow_of_coprime at G
  have r s h {a} e : IsTameExponent w A T _ s a := ⟨hA, by simp, h, ρ, π, z, (g.toInteger ^ j) ^
     a, by grw [← comap_ker, ← ker_le_comap, mk_ker], (lift.2 <| mk _ ·), u, hz, e, by aesop⟩
  use ⟨_, r _ (hA.tameGenerator ^ j).2 (inertia_pow_smul_div hA.tameGenerator.2 hv hz _ ▸ pow_one
    _)⟩, ((G.eq_pow_of_pow_eq_one (by simp_all [div_pow, ← map_pow])).imp fun a ⟨_, e⟩ ↦ ⟨r · · e,
    (by rwa [← G.pow_iff_coprime n.pos, e, ·])⟩)
