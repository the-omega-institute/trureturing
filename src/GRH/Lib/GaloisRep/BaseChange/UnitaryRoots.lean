import GRH.Lib.GaloisRep.BaseChange.BaseChangePlaces
import GRH.Lib.Adelic.Landherr.Landherr
import GRH.Lib.ClassField.Global.Avatars
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching) (known result; see Lib.GaloisRep.BaseChange.BaseChangeEigenchar).

Part of: Landherr's Hasse principle for hermitian forms; weak approximation for unitary groups
(known result; see Lib.Adelic.Landherr.Landherr).

This file: Hasse principle for norms in one CM field via reciprocity and Hasse's norm theorem.
Adelically split unitary cocycles split rationally (Landherr); normal matrices are semisimple.
Polynomial roots inverting the norm map; products of local matching pairs. -/

open Subgroup NumberField Algebra IntermediateField IsGalois ComplexEmbedding Finset
variable {E E' : Type} {L} [Field L] [NumberField L] [IsCMField L] [Field E] [Field E']
  [Algebra E L]

lemma exists_star_principalIdele_mul_eq (x : L) {w : 𝔸f L} (h : w = x * star w) : ∃ y, IsSelfAdjoint
  ((principalIdele y).1 * w) :=
  ⟨(by grind [@exists_isUnit_sub_star L, star_one L, Ne.isUnit] : ∃ z, IsUnit (z + x *
  star z)).choose_spec.star.unit, by simp [IsSelfAdjoint]; grind [by simpa using congr(star $h)]⟩

/-- Hasse principle for a step E'/E and a CM field L = E'(x), xx̄ = 1, g any element of Gal(L/E)
fixing x (its norm N runs over orderOf g steps): an idele u with μ(N_{L/E}u) = 1 whose g-norm N
satisfies N = xN̄ has c̄·z·u·g(c) = s, z in L, c invertible, s̄ = s. -/
lemma IsStep.exists_selfAdjoint_of_norm [NumberField E] [IsCMField E] [Algebra E E'] [Algebra E' L]
  [IsScalarTower E E' L] {μ} (hμ : IsStep (E := E) E' μ) {g : Gal(L/E)} {x} (hx : g x = x) (hL :
  E'[x] = ⊤) u (hu : u ∈ normKer L μ) (hN : let N := (u.1 * adeleMap g ·)^[orderOf g] 1; N =
    x • star N) :
  ∃ z c, IsUnit c ∧ IsSelfAdjoint (star c * ((principalIdele z * u).1 * adeleMap g c)) := by
  let K := fixedField (zpowers g)
  algebraize [Ω.fieldEmb L, (Ω.fieldEmb L).comp (algebraMap E L),
    (Ω.fieldEmb L).comp (algebraMap E' L)]
  lift x to K using (smul_eq_self_of_mem_zpowers ·.2 hx)
  rcases IsScalarTower.to₁₂₄ E E' L Ω, @id (IsGalois K L) (of_fixed_field ..),
    (subgroupEquivAlgEquiv _).isCyclic.1 (isCyclic_zpowers g), isCMField_of_forall_exists_conj E
    fun y : K ↦ ⟨⟨_, fun a ↦ (map_star_CM a.1.toRingHom y).trans (congrArg _ (y.2 a))⟩,
    (by simp [← lift_algebraMap_apply L ·])⟩
  have nm w := (finAdeleIncl_adeleNorm K L w).trans (((finEquivZPowers
    (isOfFinOrder_of_finite g)).trans (subgroupEquivAlgEquiv _).1).prod_comp _).symm
  obtain ⟨⟨y, a, w, -, e⟩, ⟨χ, i⟩, ψ, j⟩ := (exists_star_principalIdele_mul_eq x (adeleMap_injective
    _ ((nm u).trans (by simpa [adeleMap_star, nm, iterate_mul_apply, adeleMap_gal_pow,
    prod_range] using! hN)))).imp ((@exists_eq_principalIdele_mul_norm K _ {}).1 (t :=
    principalIdele · * u.map _) · 1 (by simp)), exists_char_of_isCyclic (isCyclic_of_prime_card
    (card_aut_eq_finrank E E')), exists_char_of_isCyclic ‹_›
  obtain ⟨c, s, -, ⟨⟩⟩ := (char_artinMap_eq_one_iff ψ w).1 ((artinMap _ w).exists_rep.elim
    fun f r ↦ r ▸ eq_fixingSubgroup_of_isProGalois (J := j).1.ge fun ⟨_, _, rfl⟩ ↦ hL.ge.trans
    (AlgHom.adjoin_le_equalizer ⟨f.toRingHom.comp _, (eq_fixingSubgroup_of_isProGalois (J := i).1.le
    (artinMap_adeleNorm (g := f.restrictScalars E) r.symm 1 (by tauto) ▸ (char_artinMap_eq_one_iff
    ..).2 (by simpa [← (((adeleNorm E K).comp (adeleNorm K L)).ext adeleNorm_adeleNorm),
    isTotallyPositive_of_isTotallyComplex, ← hμ.apply_norm_eq_one_iff, hμ.apply_principal,
    map_adeleNorm_principalIdele, units_map_adeleNorm_star, eq_inv_mul_of_mul_eq e] using
    hu)) ⟨_, ·, rfl⟩)⟩ (algHom ..) (forall_eq.2 (f.4 x))) ⟨⟩)
  have ⟨k, H⟩ : (s * star s / u).map (adeleNorm ..) ∈ principalIdele.range :=
    ⟨y / (a * c * star c), by simp [div_eq_div_iff_mul_eq_mul, e, Units.ext_iff]; ring⟩
  obtain ⟨z, rfl⟩ :=
    hasse_norm k (congr($H.1 ·) ▸ adeleNorm_mem_closure) (isTotallyPositive_of_isTotallyComplex _)
  exact ⟨z, (hilbert90_finite_idele (u := ↑(principalIdele z / _)) (by
    erw [prod_range, ← nm, ← Units.coe_map, map_div, ← H, map_adeleNorm_principalIdele]; simp)).imp
    fun _ ↦ .imp_right (by nth_rw 1 [← ·]; simp [IsSelfAdjoint, division_def]; ring)⟩

open Matrix Polynomial UniqueFactorizationMonoid Classical ComplexOrder Module Function U
variable {E E' n : Type} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Algebra E E'] [IsGalois E E'] [Fintype n] {σ : Gal(E'/E)} (hσ : σ ≠ 1)
  [Fact (finrank E E').Prime]

/-- A normal matrix over a CM field (one commuting with its conjugate transpose) is killed by
the radical of its characteristic polynomial. -/
@[simp] lemma aeval_radical_charpoly [IsCMField E]
    {M : Matrix n n E} [IsStarNormal M] : aeval M (radical
  M.charpoly) = 0 := have := Matrix.isNilpotent_trace_of_isNilpotent ((commute_conjTranspose_aeval M
    (w := radical M.charpoly).isNilpotent_mul_left
    ⟨_, by simpa [aeval_self_charpoly] using aeval_dvd M (Classical.choose_spec
    (exists_dvd_radical_self_pow M.charpoly_monic.ne_zero))⟩).map (Φ ofNonempty).mapMatrix)
  by simpa [conjTranspose_map _ (map_star_complex _), ← ext_iff,
    trace_conjTranspose_mul_self_eq_zero_iff]

include hσ

/-- For E'/E Galois of prime degree and σ ≠ 1 in its Galois group, every element of E' fixed by
σ lies in E. -/
lemma galois_descent_prime ⦃x⦄ (h : σ x = x) : x ∈ (algebraMap E _).range :=
  (mem_bot_iff_fixed x).2 (by simp [(bijective_pow_gal hσ).2.forall, iterate_fixed h])

/-- For E'/E Galois of prime degree and σ ≠ 1 in its Galois group, every finite adele of E'
fixed by σ comes from a finite adele of E. -/
lemma adeleMap_galois_descent ⦃x⦄ (h : adeleMap σ x = x) : x ∈ (finAdeleIncl E E').range := by
  simp [↓mem_range_finAdeleIncl_iff, (bijective_pow_gal hσ).2.forall, ← adeleMap_gal_pow,
    iterate_fixed h]

omit hσ in
/-- Hasse principle for cocycles: for E stably unramified, E'/E Galois of prime degree, σ ≠ 1, a
rational point s of the standard definite U(n) over E' with twisted norm 1 that equals
uσ(u)⁻¹ over the finite adeles equals gσ(g)⁻¹ with g rational. -/
lemma U.hasse_principle_coboundary [IsCMField E']
    {E : Type} [Field E] [CMType E] [Algebra E E'] [IsGalois E E']
    {σ : Gal(E'/E)} (hσ : σ ≠ 1) [Fact (finrank E E').Prime] [StablyUnram E] {s} (u : Gf _ n) (hs :
  (map (algebraMap E' _)) s = u * (galoisGf σ u)⁻¹) (hN : twistedNorm (mapEnd (map_star_CM σ))
  (finrank E E') s = 1) : ∃ g, mapEnd (map_star_CM σ) g = s⁻¹ * g := by
  let a := algebraMap E' (𝔸f E')
  choose g _ hg _ using (isTameAtLevel_gal σ).hilbert90_gl (by tauto) s.1 (Y :=
    s - 1) (by simp) (by erw [← map_twistedNorm (U 1).subtype,
    orderOf_eq_prime (card_aut_eq_finrank E E' ▸ pow_card_eq_one')] <;> aesop)
  obtain ⟨⟨y, hy⟩, J, hJ⟩ := exists_gl_map_eq_of_fixed (adeleMap_injective _)
    (adeleMap_galois_descent hσ) (g := u.1⁻¹ * g.map a) (by ext1; simpa [a, (congr($hs.1.1) :
    s.1.1.map _ = _), comp_def, mul_assoc] using! congr(u⁻¹ * ($hg).map a)),
    exists_gl_map_eq_of_fixed (RingHom.injective _) (galois_descent_prime hσ) (g :=
    star g * 1 * g) (by ext1; simpa [star, conjTranspose_map _ (map_star_CM _),
    ← inv_val_eq_conjTranspose, mul_assoc, -RingHom.coe_coe] using congr($hgᴴ * $hg))
  choose l hl using Space.landherr ⟨J, _, gram_mkAdelicGL (fun w ↦ gram_inv_of_gram_eq (x :=
    g.map _) (by simpa [entrywise] using congr($hJ.symm.1.map (ComplexEmbedding.lift _ (Φ w)))))
    (gram_inv_of_gram_eq (Matrix.map_injective (adeleMap_injective (algebraMap _ E'))
    (by simpa [← hy, ↓map_conjTranspose_mul_mul, adeleMap_star] using (gram_mul_of_gram_eq u⁻¹.2
    (y := g.map a) (by simpa [entrywise, a] using congr($hJ.symm.1.map a))))))⟩ (stdSpace E n)
  use ⟨g * l.map (algebraMap ..),
    gram_mul_of_gram_eq congr($hJ.symm) (by simp [← map_conjTranspose_mul_mul, map_star_CM,
    hl])⟩, eq_inv_mul_of_mul_eq (by ext; simp_all [map, ← mul_assoc, comp_def])

omit hσ
variable {R S n : Type _} [CommRing R] [StarRing R] [Fintype n] {γ γ' a c : U (1 : Matrix n n R)}
  {σ : R →+* R} {z : Polynomial R} {w : Polynomial R} {p : ℕ} {u : R} {v : R} {D : Subgroup Rˣ}
  {x : Matrix n n R} {y : Matrix n n R} [CommRing S] [StarRing S] {hσ : ∀ x, σ _ = _}

instance : IsStarNormal γ.1.1 := ⟨by simp [commute_iff_eq, star, ← inv_val_eq_conjTranspose]⟩

attribute [local simp] mul_assoc mul_add conjTranspose_nonsing_inv map_aeval_matrix IsRootQuotient

lemma U.isRootQuotient_conj (h : γ * c = c * γ') : IsRootQuotient γ' z a → IsRootQuotient γ z
  ↑(c * a * c⁻¹) := by simp [← c.1.mul_inv_eq_iff_eq_mul.2 (aeval_semiconj congr($h.1.1).symm _),
  ← inv_val_eq_conjTranspose]; grind

lemma U.isRootQuotient_map {f : R →+* S} hf (h : IsRootQuotient γ z a) : IsRootQuotient ((map f hf)
  γ) (z.map f) ((map f hf) a : U 1) := by simpa [conjTranspose_map _ hf] using! congr(($h).map f)

lemma U.existsUnique_isRootQuotient (h : IsUnit (aeval γ.1.1 z)) : ∃! a : U 1,
  IsRootQuotient γ z a.1.1 :=
  have := h.invertible; ⟨of isUnit_one _ (by simp [commute_conjTranspose_aeval, Commute.left_comm]),
    invOf_mul_cancel_right .., by aesop (add simp mul_right_eq_iff_eq_mul_invOf)⟩

lemma IsRootQuotient.mul : IsRootQuotient γ z x → IsRootQuotient γ w y → IsRootQuotient γ (z * w)
  (x * y) := by grind [(commute_conjTranspose_aeval γ.1.1).eq, conjTranspose_mul]

lemma IsMatchingPair.mul {A j K L f f' φ φ'} (h : IsMatchingPair (A := A) (n := n) hσ p u D j K f φ)
  (h' : IsMatchingPair hσ p v D j L f' φ') : u * v = 0 → u * u = u → v * v = v → star u = u →
  star v = v → IsMatchingPair hσ p (u + v) D j (K ⊓ L) (f * f') (φ *
  φ') := by intros; refine ⟨by simp +contextual [h.1, h'.1, -mul_assoc], fun P H e ↦ match h.2 P ?_
  e, h'.2 P ?_ e with | ⟨z, ⟨a, A⟩, a'⟩, ⟨w, ⟨b, B⟩, b'⟩ => ⟨z * w, ⟨by grind [congr($a * $b),
  smul_mul_smul], fun γ c ↦ ⟨by grind [mul_mem, det_mul], by
  convert (A γ c).2.mul (B γ c).2 <;> simp [twistedNorm_map_eq_prod, add_mul]
  match_scalars <;> grind⟩⟩, fun γ r
  _ hr ↦ by simp +contextual [a' γ r, b' γ r, *, by simpa [↓smul_smul, mul_sub, mul_comm, *] using
  congr((u • $hr, v • $hr, z * u • $b.symm, v • $a.symm * w))]⟩⟩ <;> revert H <;> gcongr <;> simp

lemma IsRootQuotient.twistedNorm_eq_mul (h : IsRootQuotient γ (twistedNorm (.map σ) p z) γ) (hc :
  γ * c = c * mapEnd hσ γ) (ha : IsRootQuotient γ z a) (hu : IsUnit (aeval γ.1.1 z)) : twistedNorm
  (mapEnd hσ) p c = γ * twistedNorm (mapEnd hσ) p (a⁻¹ * c) := eq_mul_of_mul_inv_eq (And.elim
  (existsUnique_isRootQuotient · |>.unique · h) (p.rec (by simp [twistedNorm]) fun _ ih ↦ by
  erw [twistedNorm_succ' (mapRingHom σ).1, mul_comm]
  simpa [*, aeval_semiconj (x := γ.1.1.map σ) congr($hc.1.1).symm, twistedNorm_succ']
  using! ih.imp (c.1.isUnit.mul ∘ .map σ.mapMatrix)
    (isRootQuotient_map hσ · |> isRootQuotient_conj hc |>.mul ha)))
