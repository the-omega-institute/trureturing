import GRH.Lib.Adelic.Hecke.ClassMean
import GRH.Lib.GaloisRep.Hilbert90.UnitaryHilbert90
import GRH.Lib.Adelic.Adeles.LocalComponents
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Auxiliary definitions and lemmas for base change (norm roots, matching pairs and cocycle
splitting for unitary matrices, a CM-field lemma), plus one general group-action lemma on class sums
of orbit counts.

Part of: Cyclic base change of prime degree for definite unitary groups (weak lift, local matching)
(known result; see Lib.GaloisRep.BaseChange.BaseChangeEigenchar).

This file: Polynomial roots inverting the norm, matched pairs of test functions, splitting of
cocycles. Matching of unit functions at a principal tame level. Units with invertible skew part.
Class sum of orbit counts equals the mass of the stabiliser's classes. -/
seal Finset.univ Finset.sum Finset.prod

section

open Matrix U Function Polynomial Set
variable {R n A} [CommRing R] [Fintype n] (σ : R →+* R) [StarRing R] (h : ∀ _, σ _
  = _) (q) (u : R) (D : Subgroup Rˣ) (γ : U (1 : Matrix n n R)) (P z : Polynomial R) (j : A → _)

/-- The relation a·z(γ)* = z(γ) between a matrix a, a polynomial z and a unitary γ; when z(γ) is
invertible it says a = z(γ)/z(γ)*. -/
abbrev IsRootQuotient a := a * (z.aeval γ.1.1)ᴴ = z.aeval ↑γ

variable (n) in
/-- (1−u)z = 1−u and, for unitary γ of characteristic polynomial P: det z(A) ∈ D whenever P(A) =
0, and (uγ+1−u)·(Nz)(γ)* = (Nz)(γ), N the σ-norm. -/
def IsNormRoot := (1 - u) • z = (1 - u) • 1 ∧ ∀ γ : type_of% γ, γ.1.1.charpoly = P →
  (∀ m (A : Matrix (Fin m) (Fin m) R), P.aeval A = 0 → (z.aeval A).det ∈ D.1.map (Units.coeHom R)) ∧
  IsRootQuotient γ (twistedNorm (.map σ) q z) (1 + u • (γ - 1))

variable {σ} (K : Subgroup (type_of% γ))

/-- φ is twisted K-invariant and, over each σ-fixed characteristic polynomial, f and φ vanish or
a root z gives a = uz(γ)/uz(γ)* with φ(a) = f(g) if jg = γ = Nm a, and δ ∈ aK if Nm δ = γ,
φ(δ) ≠ 0. -/
def IsMatchingPair f (φ : _ → ℂ) := (∀ k ∈ K, ∀ δ, φ (k⁻¹ * δ * mapEnd h k) = φ δ) ∧
  ∀ P ∈ (·.1.1.charpoly) '' (j '' Function.support f ∪ twistedNorm (mapEnd h) q '' Function.support
  φ), P.map σ = P → ∃ z, IsNormRoot n σ q u D P z ∧ ∀ γ a, γ.1.1.charpoly = P →
  IsRootQuotient γ (u • z) a.1 → (∀ g, j g = γ → twistedNorm (mapEnd h) q a = γ → f g = φ a) ∧ ∀ δ,
  twistedNorm (mapEnd h) q δ = γ → φ δ ≠ 0 → a⁻¹ * δ ∈ K

/-- Every s in K of twisted norm 1 admits t in K with (1−u)t = (1−u)·1 and u·t⁻¹sτ(t) = u·1. -/
def CocyclesSplit τ := ∀ s ∈ K, twistedNorm τ q s = 1 →
  ∃ t ∈ K, (1 - u) • t.1.1 = (1 - u) • 1 ∧ u • (t⁻¹ * s * τ t).1.1 = u • 1

attribute [-simp] IsUnit.dvd Polynomial.map_add _root_.map_eq_zero

attribute [local simp] Function.comp_def charpolyRev Matrix.map_add map_smul' reverse_charpoly
  aeval_comp map_comp indicator star cutAt cutGL mul_add mul_sub smul_smul sub_mul

/-- Unit pairs: O profinite, integrally closed in R; τ commutes with bar, is tame at 0 and at m
= m̄ = uM, fixes c with c − c̄ a unit; σ extends τ; in R, mv = u, uv = v. If L = {g unitary
: v(g − 1) has entries in O} is σ-stable and D contains every d with d, d⁻¹ ∈ 1 + MO, then
`CocyclesSplit` holds for L and (1_L∘j, 1_L) satisfies `IsMatchingPair`. -/
lemma isMatchingPair_congruence_level {O R n : Type} [CommRing O] [CommRing R] [Algebra O R]
  [StarRing O] {τ p m c} u (hO : IsProfiniteRing O) (he : IsTameAtLevel τ p 0) (hc : τ c = c) (uc :
  IsUnit (c - star c)) (sM : star m = m) (t : IsTameAtLevel τ p m) (hτ : ∀ x, τ (star x) = star (τ
  x)) [Fintype n] [StarRing R] (_ : StarModule O R) (ic : IsIntegrallyClosedIn O R) {σ} hσ {v M L D
  A j} (em : u * M = m) (hφ : ∀ k ∈ L, mapEnd (n := n) (σ := σ) hσ k ∈ L) : let ι := algebraMap O R
  (∀ x, ι (τ x) = σ (ι x)) → ι m * v = ι u → ι u * v = v → (∀ g, g ∈ L ↔ ∃ Y, map Y ι = v • (g.1.1 -
    1)) → (∀ y z h, .mkOfMulEqOne (1 + ι (M * y)) (1 + ι (M * z)) h ∈ D) → CocyclesSplit p (ι u) L
    (mapEnd hσ) ∧ IsMatchingPair (A := A) hσ p (ι u) D j L (indicator L 1 ∘ j) (indicator L 1) := by
  intro ι hιτ hv hv' hL hD
  obtain ⟨hι : ∀ x, ι _ = _, inj : (⇑ι).Injective, ic⟩ := algebraMap_star_comm, ic
  choose iu su sv using show ι u * ι u = ι u ∧ star (ι u) = ι u ∧ star v = v ∧
    ι u * ι m = ι m ∧ σ v = v ∧ σ (ι u) = ι u by grind [IsTameAtLevel, star_mul]
  choose Y hY using (hL · |>.1)
  choose S hS eS using fun s hs ↦ mem_range_map hι inj isUnit_one (by simp) (M := 1 + m • Y _ hs)
    (g := cutAt iu su s) (by simp [*]; module)
  use fun s hs hN ↦ ?_, by simp +contextual [mul_mem_cancel_left, mul_mem_cancel_right,
    hφ], fun | _, ⟨g, h, rfl⟩, _ => ?_
  · set e := map (n := n) ι hι _
    choose t W ht hW using unitary_hilbert90_at_level hO he hc uc hτ _ sM t (hS s hs)
      (map_injective inj congr($(show e _ = e 1 by rw [map_twistedNorm (σ := mapEnd hσ), eS,
      ← map_twistedNorm, hN] <;> simp [Units.ext_iff, *, e, U.map])))
    refine ⟨e t, (hL _).2 ⟨u • W, ?_⟩, ?_, by simpa [e, U.map, *, -hW, add_mul, mul_assoc, smul_sub]
      using (congr(ι u • (e (t⁻¹ * $ht)).1.1))⟩ <;> simp [e, U.map, *, mul_comm v]
  have hg : g ∈ L := by simp at h; clear * - hφ h; grind [twistedNorm_mem]
  let q := (compRingHom (v • (X - 1))).comp (mapRingHom ι)
  have F {B} [Ring B] [Algebra R B] (A : B) r := by simpa [q, ← hY g hg,
    ← map_aeval_matrix, charpoly_map] using aeval_dvd A (charpoly_dvd_charpoly_aeval_comp (Y :=
    g.1.1) (q r))
  choose y z z' H using exists_twisted_root hO he hc uc hτ sM t.1 rfl (ext fun i ↦ inj (by
    simp [*]; simp [← coeff_map, ← charpoly_map, *, charpoly_smul_coeff, Polynomial.map_add,
      by simpa using g.1.1.charpoly_sub_scalar 1])) .refl (map_injective inj (by simp [*,
    conjTranspose_map _ hι, Matrix.map_neg, ← inv_val_eq_conjTranspose, ← mul_assoc, smul_sub])) ⟨_,
    hS g hg⟩
  use q (1 + m • z), ⟨by simp [*, q, Polynomial.map_add], fun γ e ↦ ⟨fun _ A h ↦ ?_, ?_⟩⟩, fun γ
    a e d ↦ ?_ <;> choose _ c b using H (by simpa [ι, ← e, aeval_self_charpoly] using F γ.1.1 X)
  · choose w d using fun r ↦ ((mem_lifts _).1 ((reverse _).lifts_iff_coeff_lifts.2 fun i ↦ ic.1 (by
      simpa [reverse] using isIntegral_coeff_of_dvd _ _ ((charpoly_monic _).pow _) (charpoly_monic
      _) (by simpa using
        (zero_dvd_iff.1 (h ▸ F A (-r)) ▸ charpoly_dvd_charpoly_aeval_comp _ :)) _))).elim fun Q e
      ↦ ((Dvd.intro_left u (by simpa)).trans (Q.sub_dvd_eval_sub m 0)).imp fun y h ↦ by simpa [←
      eval_map_apply, e, eval_det, sub_eq_iff_eq_add', ι, ← smul_eq_mul_diagonal] using congr(ι $h)
    exact ⟨_, hD _ _ (mul_eq_one_symm (by simpa [-mul_add, d] using congr($(((H (by simpa
      [ι, h] using (F A X) :)).2.1 t).1).det))), by simp [q, ι, *]⟩
  · erw [← map_twistedNorm q.1 (τ := map τ) (by simp [q, *]; congr!; aesop)]
    convert b (by simp [← inv_val_eq_conjTranspose]; match_scalars <;> clear * - hv hv' sv <;>
      grind) <;> simp [← hv, q, mul_smul, -smul_smul, ι, c t]
  have k h := (hL a).2 ⟨(fun b ↦ u • (b z + b (1 + m • z) * (b z')ᴴ)) (aeval (Y γ h)), by
    simp [sM, conjTranspose_map _ hι, map_aeval_matrix, ι, smul_sub, ← hv, hY, add_assoc, mul_smul,
    -smul_smul, smul_comm
      v, by simpa [*, ι, -algebraMap_smul, mul_comm v, ← map_mul, q, mul_assoc, -mul_add, -map_add,
      ← conjTranspose_mul] using congr(v • $d * (aeval γ.1.1 (q (1 + m • z')))ᴴ)]⟩
  simp; clear * - hφ k; grind [twistedNorm_mem, mul_mem, inv_mem]

variable {E} [Field E] [NumberField E]

lemma exists_isUnit_sub_star [h : NumberField.IsCMField E] : ∃ z : E, IsUnit (z - star z) := by
  simpa [DFunLike.ne_iff] using! h.complexConj_ne_one.symm

end

open MulAction DoubleCoset Function Finset HasFiniteType

/-- Let G act on X, ι embed H with image the stabiliser of e, and Δ, L be the preimages of Γ, K.
If f(g) counts the y in Γe with g⁻¹y in Ke, the class sum of f for (Γ, K) equals that of 1
for (Δ, L). -/
lemma classSum_card_orbit G H {X} [Group G] [Group H] [MulAction G X] [TopologicalSpace G]
    [TopologicalSpace H] {Γ K Δ L} [HasFiniteType Γ K]
    [HasFiniteType Δ L] e (ι : H →* G) {f} (S : G → Set X) (hι : Injective ι) (he : stabilizer G e =
  ι.range) (hΔ : Δ = Γ.comap ι) (hL : L = K.comap ι) (hf : ∀ g, ((S g).ncard : ℝ) = f g) (hS : ∀ g
  y, y ∈ S g ↔ y ∈ orbit Γ e ∧ g⁻¹ • y ∈ orbit K e) : classSum Γ K f = classSum Δ L 1 := by
  simp [SetLike.ext_iff] at *
  choose T _ _ using exists_transporter Γ (K := K)
  choose s _ _ using exists_transporter Δ (K := L)
  have {g} := (tsum_subtype (S g) 1).trans ((hasSum_sum (s := ⊤) fun (d : DoubleCosets Δ L) _ ↦
    hasSum_sum (s := T g (ι d.out)) fun γ _ ↦ hasSum_ite_eq (γ • e)
    (#(s d.out d.out) : ℝ)⁻¹).congr_fun fun _ ↦ ite_eq_iff'.2 ⟨by
    rw [hS]; rintro ⟨⟨⟨a⟩, ⟨⟩⟩, ⟨⟨k⟩⟩⟩
    cases' (he (a⁻¹ * g * k)).1 (by simp_all [mul_smul]) with h
    simp [*, sum_ite, out_eq', ↓card_classAut_out h, fun d ↦ (ext ((mul_left_surjective a).forall.2
      (by simp_all [smul_left_cancel_iff, mul_smul, mul_mem_cancel_left, mul_assoc]; grind)) :
      {γ ∈ T g (ι d) | a • e = γ • e} = (s h d).map ⟨_, (mul_right_injective a).comp hι⟩),
      -mem_classAut], by simp_all [orbit]; grind [mul_smul, sum_eq_zero]⟩).tsum_eq
  simp_all [classSum, out_eq', -mem_classAut, sum_comm, Rat.smul_def, mul_sum]
