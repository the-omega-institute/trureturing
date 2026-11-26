import OmegaMath.NumberTheory.GRH.Lib.LocalGL.Iwahori.IwahoriConjugation
import OmegaMath.NumberTheory.GRH.Lib.GaloisRep.Main.HeckeOperatorOfFunction
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Exponents, U-operators and spherical vectors at pro-p Iwahori level; conjugacy in I t I
(known result; see Lib.LocalGL.Tadic.ChainLemma).

This file: Conjugation of parahorics by monomial matrices; quadratic relation of the Iwahori Hecke
algebra. Some strictly dominant U-operator is injective; values of exponents on monomial
translates. -/

open Finset Equiv Fint Function IsLocalRing Matrix OrderDual Units Valued WithZero

attribute [local simp] Pi.mulSingle_apply transvectionGL_mem_proIwahori

variable {F W} [Field F] [Valued F ℤᵐ⁰] [CompactSpace 𝒪[F]] [AddCommGroup W] [Module ℂ W] {N} {ρ :
  Rep ℂ (GL (Fin N) F)} [IsSmoothRep ρ.ρ] {x c d} {g : GL (Fin N) F} {a b : Fin N} {φ : ρ →ₗ[ℂ] W}
  (h : a ⋖ b) {h' : a ≠ b} {ϖ : Fˣ} (hϖ : v ϖ.1 = exp (-1)) {y z ξ l t K} (hl : IsExponent ρ ξ l)

omit [CompactSpace 𝒪[F]] in
@[grind] lemma mem_blockParahoric {c : ℕ → ℕ} : g ∈ blockParahoric c ↔ g ∈ intGL _ 𝒪[F] ∧
  ∀ i j, c j.1 < c i.1 → v (g i j) < 1 := .rfl

omit [CompactSpace 𝒪[F]] in
lemma mem_proIwahori_iff_blockParahoric : g ∈ proIwahori ↔ g ∈ blockParahoric id ∧ ∀ i,
  g i i ∈ {x | v (x - 1) < 1} := and_assoc.symm

omit [CompactSpace 𝒪[F]] in
/-- Let g lie in the parahoric of d, with diagonal entries in S, and h = σ·diag(t). If g_{σa,σb}
≠ 0 implies log|t_b| + [c(b)<c(a)] ≤ log|t_a| + [d(σb)<d(σa)] (integer logarithms), then
h⁻¹gh lies in the parahoric of c, with diagonal entries in S. -/
lemma conj_monomial_mem_blockParahoric {c d : ℕ → ℕ} t (σ : Equiv.Perm (Fin N)) (S : Set F) (hk :
  g ∈ blockParahoric d ∧ ∀ i, g i i ∈ S) (h : ∀ a b, g (σ a) (σ b) = 0 ∨
  log (v (t b).1) + ite (c b < c a) 1 0 ≤ log (v (t a).1) + ite (d (σ b) < d (σ a)) 1 0) : let k :=
    (permGL σ * diagGL t)⁻¹ * g * (permGL σ * diagGL t); k ∈ blockParahoric c ∧ ∀ i, k i i ∈ S := by
  simp_all only [mem_blockParahoric, mem_intGL_iff_det]; erw [det_units_conj']
  simp [← map_inv, mul_apply, symm_apply_eq, diagonal, mul_assoc]; grind [ne_zero, one_pos,
    =_ log_le_log, =_ log_lt_log, map_eq_zero, log_mul, log_inv, mul_eq_zero]

omit [CompactSpace 𝒪[F]] [IsSmoothRep ρ.ρ] in
lemma transvectionGL_apply_permGL_inv {σ} {x : ρ} (hx : x ∈ levelSpace ρ.ρ proIwahori) (e :
  σ a < σ b) c (hc : v c ≤ 1) : ρ (transvectionGL h' c) (ρ (permGL σ⁻¹) x) = ρ (permGL σ⁻¹) x :=
  cast (by simp_all) congr(ρ $(permGL_mul_transvectionGL σ⁻¹ e.ne c) x).symm

omit [CompactSpace 𝒪[F]] in
lemma proIwahori_le_blockParahoric {c : ℕ → ℕ} (h : ∀ i j, c j < c i → j < i := by grind) :
    proIwahori ≤ @blockParahoric F _ _ N c := fun _ ↦ by grind [mem_proIwahori_iff_blockParahoric]

omit [Valued F ℤᵐ⁰] [CompactSpace 𝒪[F]] in
@[local simp] lemma swap_mul_transvectionGL (h : a ≠ b) (u : Fˣ) : permGL (swap a b) *
  transvectionGL h u.1 = transvectionGL h u.1⁻¹ * diagGL (Pi.mulSingle a (-u⁻¹) * Pi.mulSingle b
  u) * transvectionGL h.symm u.1⁻¹ := by ext; simp [PEquiv.toMatrix_mul_apply, transvection,
  mul_add, add_mul, single_apply, diagonal_apply, @apply_ite Fˣ]; grind

omit [CompactSpace 𝒪[F]] in
lemma exists_swap_conj_mem_proIwahori (hg : g ∈ proIwahori) : ∃ c : 𝒪[F],
  MulAut.conj (permGL (swap a b)) (g * transvectionGL h.ne c.1) ∈ proIwahori :=
  have : v (-g a b / g a a) ≤ 1 := by simp_all [v_diag_eq_one_of_mem_proIwahori, mem_proIwahori]
  ⟨⟨_, this⟩, by cases h; simpa using!
    mem_proIwahori_iff_blockParahoric.2 (conj_monomial_mem_blockParahoric 1 (swap a b) _
    (mem_proIwahori_iff_blockParahoric.1 (by aesop))
    (by simp; grind [mul_transvection_apply_same, v_diag_eq_one_of_mem_proIwahori, one_pos]))⟩

/-- Quadratic relation: b = a+1, s the transposition (a b), φ invariant under I₁, 1 + 𝒪E_{ba}
fixing y, φ(ρ(d)y) = c for d with −u⁻¹ at a, u at b, 1 elsewhere, u any unit. Then qφ(s·mean
of y over I₁) = φ(sy) + (q−1)c. -/
lemma quadratic_relation c (hφ : ∀ k ∈ proIwahori, ∀ z, φ (ρ k z) = φ z) (hx : ∀ c, v c ≤ 1 →
  ρ (transvectionGL h.ne' c) x = x)
  (hc : ∀ u, v u.1 = 1 → letI t := Pi.mulSingle a (-u⁻¹) * Pi.mulSingle b u
  (∀ i, v (t i).1 = 1) → φ (ρ (diagGL t) x) = c) : letI s := ρ (permGL (swap a b))
  Nat.card 𝓀[F] • φ (s (compactMean ρ.ρ proIwahori x)) = φ (s x) + (.card 𝓀[F] - 1) • c := by
  have A (k : proIwahori) {w} (o : v w ≤ 1) : φ (ρ (k.1 * (permGL (swap a b) * transvectionGL h.ne
    w)) x) = ite (v w < 1) (φ (ρ (permGL (swap a b)) x)) c := by
    cases h; cases o.lt_or_eq
    simp_all [permGL_mul_transvectionGL]
    lift w to Fˣ <;> aesop
  simpa [h.1, ← v.mem_integer_iff] using (map_compactMean_of_const (φ ∘ₗ _) fun _ k ↦
    (exists_swap_conj_mem_proIwahori h k).rec
    fun z o ↦ by simpa [h.ne, ↓← residue_eq_zero_iff_lt, sum_ite, mul_assoc, ← map_sum,
    (Units.ext (transvection_mul_transvection_same ..) : transvectionGL .. * transvectionGL .. =
    transvectionGL ..), surjInv_eq,
    filter_ne', card_filter] using congr(∑ r, $(A ⟨_, o⟩ (surjInv residue_surjective r - z).2)) :)

/-- For F with a uniformiser and a smooth representation of GL_N(F), there is a strictly
dominant t such that U_t is injective on the vectors fixed by the pro-p Iwahori subgroup I₁. -/
lemma exists_iwahoriHeckeHom_injective (ρ : Rep ℂ (GL (Fin N) F)) [IsSmoothRep ρ.ρ] (hϖ : v ϖ.1 =
  exp (-1)) : ∃ t, ∃ h :
  StrictMono _, Injective (iwahoriHeckeHom ρ ⟨t, h.monotone⟩) := let s a : dominantTorus := ⟨(if a ≤
    · then ϖ⁻¹ else 1), by simp_all +decide [dominantTorus, Monotone, apply_ite, ite_apply]; lia⟩
  ⟨(∏ a, s a).1, by simp_all [StrictMono, prod_ite, filter_ge_eq_Iic, s], .of_ker _
    (((nonZeroSMulDivisors ..).comap (iwahoriHeckeHom ρ)).prod_mem fun a _ x h ↦ have := a.neZero
    let n := permGL (finCycle a)⁻¹ * diagGL (s a)
    have hy : ρ n x ∈ levelSpace _ _ := by simpa using fun k h ↦ x.2 ⟨n⁻¹ * k * n,
      mem_proIwahori_iff_blockParahoric.2 (conj_monomial_mem_blockParahoric _
      _ _ (mem_proIwahori_iff_blockParahoric.1 h)
      (by simp_all [s, @apply_ite Fˣ, apply_ite v, apply_ite log]; fin_omega))⟩
    by simpa [Perm.monotone_iff, *, (ρ.ρ.apply_bijective n).1] using (exists_antitone_of_swap toDual
      (fun σ ↦ compactMean ρ.ρ proIwahori (ρ (permGL σ⁻¹) (ρ n x)) = 0)
      ⟨(finCycle a)⁻¹, by simp [n]; injection h⟩ fun σ _ _ c e _ ↦ by simpa [*, -map_inv] using
      (quadratic_relation c 0 (fun _ ↦ compactMean_apply) (transvectionGL_apply_permGL_inv hy e)
      (by intros; rw [← map_compactMean_of_factor _ (⟨·, diagGL_conj_mem_proIwahori · fun _ ↦ _,
      _⟩)] <;> simp_all)).symm))⟩

lemma IsExponent.apply_compactMean (hl : IsExponent ρ ξ l) : l (compactMean ρ.ρ proIwahori z) =
  l z := by simpa using hl (one_mem _) z

lemma IsExponent.apply_proIwahori (hl : IsExponent ρ ξ l) k (hk : k ∈ proIwahori) z : l (ρ k z) =
  l z := by simp [← hl.apply_compactMean, hk]

include hl in
lemma IsExponent.apply_diagGL_unit (ht : ∀ a, v (t a).1 = 1) z : l (ρ (diagGL t) z) =
  ξ t * l z := by rw [← map_compactMean_of_factor hl.apply_proIwahori (⟨·,
  diagGL_conj_mem_proIwahori · fun _ ↦ _, _⟩), hl] <;> aesop_cat

/-- Let (ξ, l) be an exponent, y fixed by a group containing the elements of the parahoric of c
with diagonal ≡ 1 mod ϖ. Then l(ρ(t)ρ(σ)y) = ξ(t) l(ρ(σ)y) if σb < σa implies |t_{σb}| ≤
|t_{σa}|, or c(a) ≤ c(b) and |ϖt_{σb}| ≤ |t_{σa}|. -/
lemma IsExponent.apply_monomial_translate {ρ : Rep ℂ (GL (Fin N) F)} [IsSmoothRep ρ.ρ] (hϖ : v ϖ.1 =
  exp (-1)) {y ξ l t K c} (hl : IsExponent ρ ξ l) (hz : y ∈ levelSpace ρ.ρ K) (o : ∀ {g},
  g ∈ blockParahoric c ∧ (∀ i, v (g i i - 1) < 1) → g ∈
  K) σ (H : ∀ a b, σ b < σ a → v (t (σ b)).1 ≤ v (t (σ a)).1 ∨ c a.1 ≤ c b.1 ∧ v (t (σ b)).1 ≤ v
  (t (σ a)).1 * exp 1) : l (ρ (diagGL t * permGL σ) y) = ξ t * l (ρ (permGL σ) y) := by
  have key {d} hd s (e : s = 1 ∨ s = t) := (map_compactMean_of_factor hl.apply_proIwahori fun g k ↦
    (exists_iwasawa_bruhat g).imp fun _ _ ↦ ⟨conj_unitriangular_mem_proIwahori hd (by tauto), by
    simpa using hz ⟨_, o (diagGL_mul_permGL s σ ▸ conj_monomial_mem_blockParahoric _ σ
      _ (mem_proIwahori_iff_blockParahoric.1 (mul_mem (inv_mem (by tauto)) k)) (by
      cases e <;> simp_all [← log_le_log] <;> grind [σ.injective, le_total]))⟩⟩) ▸ @hl d hd _
  have ⟨s, hs, _⟩ := exists_iwahoriHeckeHom_injective ρ hϖ
  have ⟨k, h⟩ := (eventually_pow_mul_mem_dominantTorus hs t).exists
  simpa [key (pow_mem hs.monotone k), mul_assoc, -map_pow] using key h 1
