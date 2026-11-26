import GRH.Lib.ClassField.Places.LocalBasics
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Stickelberger's factorisation of Gauss sums and the Davenport–Hasse product
relation. Only prime fields are treated, and characters are named by the valuation of their Gauss
sum. The product relation is proved for Jacobi-type quotients of Gauss sums and only up to a root of
unity. Source: L. Washington, Introduction to Cyclotomic Fields, 2nd ed. 1997, 6.2 and Thm 15.1; for
the product relation, H. Davenport, H. Hasse, J. reine angew. Math. 172 (1935).

This file: Valuations of Gauss sums, Jacobi-type quotients, distribution relation up to roots of
unity. -/

open AddChar Int MulChar NeZero NumberField QZ QuotientAddGroup ValuationSubring ZMod
  ComplexEmbedding Embeddings

attribute [local simp ←] map_nsmul_eq_pow Finset.mul_sum cast_sum self_sub_fract pow_apply_coe
  QZ.fracRep_mk RingHom.map_pow Submodule.Quotient.mk_eq_zero valuation_le_one_iff map_nsmul
  mul_assoc

attribute [local simp] map_add_eq_mul ne add_div div_sub_one map_eq_zero_iff

variable {r m p : ℕ} [NeZero r] [hp : Fact p.Prime] {B : ClosurePlace} (hB :
  B.valuation p < 1) {v} (c : ℕ) {ψ : AddChar (ZMod p) (𝓞 Ω)} {χ :
  AddChar (ZMod r) (MulChar (ZMod p) (𝓞 Ω))} (g : ZMod r → DiscreteUnits Ω)

/-- For c in ℕ and x in ℚ/ℤ, the integer ⌊c⟨x⟩⌋ − ⌊c⟨−x⟩⌋, where ⟨·⟩ is the representative in
[0,1). -/
noncomputable def floorDiff x := ⌊c * QZ.fracRep x⌋ - ⌊c * (-x).fracRep⌋

lemma sum_floorDiff : m.Coprime r → ∀ x, IsUnit v → ∑ b, floorDiff m (x + ofZMod r (v * b)) =
  floorDiff m (r • x) := by
  have (x) v (h : IsUnit v) := Fintype.sum_equiv (h.unit.mulLeft.trans (.addLeft ↑⌊r * QZ.fracRep
    x⌋)) (fun b ↦ (x + ofZMod r (v * b)).fracRep) (fun b ↦ (b.val + fract (r * x.fracRep)) / r)
    fun _ ↦ .trans (by simp [← ofZMod_apply, -natCast_val, ofZMod, ← map_zsmul, add_assoc,
    ← division_def, sub_div, ↓floor_div_natCast, ↓floor_natCast_add, ↓floor_fract,
    ediv_eq_zero_of_lt, val_lt]) (floor_add_fract _)
  qify; simp [floorDiff, map_nsmul, ← nsmul_eq_mul, ← isUnit_iff_coprime] at *
  simp_all [smul_comm r, ← map_neg, ← neg_mul, add_comm, mul_div_cancel₀]; grind

/-- Kronecker's theorem in an algebraic extension of `ℚ`: an element that lies in every
valuation ring and has absolute value one in every complex embedding is a root of unity. -/
lemma isOfFinOrder_of_norm_eq_one {x} (h : ∀ A : ClosurePlace, x ∈ A) (N : ∀ τ : Ω →+* ℂ, ‖τ
  x‖ = 1) : IsOfFinOrder x := by simpa [isOfFinOrder_iff_pow_eq_one, Subtype.ext_iff] using (
  pow_eq_one_of_norm_eq_one (fixedFieldOf (id (OpenSubgroup.mk _ (stabilizer_isOpen_of_isIntegral
  (K := ℚ) x))).1) ℂ (x := ⟨x, (·.2)⟩) (IntermediateField.coe_isIntegral_iff.1 ((integralClosure ..
  ).toSubring.eq_iInf_of_isIntegrallyClosedIn.ge (by aesop))) (lift_algebraMap_apply Ω · _ ▸ N _))

/-- Galois action on non-zero Gauss sums g(t) of χ_t and ψ over 𝔽_p, with t ↦ χ_t a homomorphism
on ℤ/r: there are homomorphisms K_σ from ℤ/r to Ω^× with σg(t) = K_σ(at)·g(at), where a is
the cyclotomic character of σ modulo r. -/
lemma smul_gaussSum (hg : ∀ t, (g t).toMul.1 = gaussSum (χ t) ψ) : ∃ K :
    _ → ZMod r →+ DiscreteUnits Ω, ∀ σ t, galUnitsRep σ (g t) = (K σ + g) (cycCharMod Ω r σ * t) :=
    ⟨fun σ ↦ AddMonoidHom.mk' (fun t ↦ .ofNeZero ((χ t)⁻¹ (cycCharMod Ω p σ))
  (by simp [apply_eq_zero_iff])) (by simp [DiscreteUnits.ext_iff, field]), fun σ t ↦
  DiscreteUnits.ext (by simpa [cycCharMod_spec (N := p), cycCharMod_spec (N := r), *, gaussSum,
  sum_eq_add_sum_units, Finset.smul_sum] using congr($(gaussSum_mulShift_eq _ ψ _).val))⟩

include hB

/-- Let B be a place of Ω above the prime p. An algebraic integer x with x^p = 1 is congruent to
1 modulo the prime ideal that B defines. -/
lemma residue_eq_one_of_pow_prime_eq_one {x : 𝓞 Ω} (e : x ^ p = 1) : ↑x =
  (1 : _ ⧸ centrePrime Ω B) := by_contra (orderOf_eq_prime (congrArg _ e) · ▸
  IsPrimitiveRoot.orderOf _ |>.neZero'.1 (Ideal.mk_ker.ge (mem_centrePrime.2 hB)))

/-- Weak form of Stickelberger's theorem: for the Gauss sums g(t) of χ^t over 𝔽_p (χ of order r
prime to p, ψ non-trivial) and B above p with ord p = 1, 0 ≤ ord g(t) < 1, and t ↦ ord g(t)
is an injective homomorphism ℤ/r → ℚ/ℤ.

Known result: Stickelberger's factorisation of Gauss sums; Davenport–Hasse product relation. -/
lemma stickelberger (hg : ∀ t, (g t).toMul.1 = gaussSum (χ t) ψ) (hψ : ψ.IsPrimitive)
    (w : χ.IsPrimitive) (cp : p.Coprime r) : ∃ S :
    _ →+ QZ, (⇑S).Injective ∧ ∀ t, (S t).fracRep = ordRat ℚ B (g t) := by
  obtain ⟨⟨v, hv, _⟩, K, H⟩ := exists_isPlaceOver_prime hB, smul_gaussSum g hg
  let S := AddMonoidHom.mk' (QZ.mk <| ordRat ℚ B <| g ·) fun a b ↦ eq_iff_sub_mem.2 (by
    simpa [← map_add, ← map_sub, ← range_castAddHom, eq_comm] using
      hv.ordRat_int_of_inertia_fixed fun σ :
      Gal(Ω/ℚ) ↦ (by simp [H, cycCharMod_of_mem_inertiaGroup ·, cp.valuation_eq_one hB]; abel))
  have lt u {χ : MulChar (ZMod p) (𝓞 Ω)} {ψ} e h := ((hv.ordRat_nonneg_iff u).2 (Eq.subst (.symm e)
    (algebraMap_ringOfIntegers_mem B (gaussSum χ ψ)))).lt_of_ne' (hv.ordRat_eq_zero_iff.1.mt
    (e ▸ (mem_centrePrime.1 (by
    simpa [gaussSum, residue_eq_one_of_pow_prime_eq_one hB, -ne]
      using congr($(gaussSum_one_right h) ∈ centrePrime ..))).ne))
  have L t : (S t).fracRep = _ := (toIcoMod_eq_self _).2 (by_cases (by simp_all
    [hv.ordRat_eq_zero_iff.2, gaussSum_one_left (by simpa using @hψ 1)]) fun h ↦
    ⟨(lt _ (hg t) h).le, by simpa [*] using lt (.ofNeZero p out - g t) (by
    simpa [field, ← hg] using congr($((gaussSum_mul_gaussSum_eq_card h hψ).symm).val)) (by simpa)⟩)
  use S, .of_ker S fun t e ↦ by
    simpa [w.zmod_char_eq_one_iff, ← L, e, QZ.mk.map_zero ▸ QZ.fracRep_mk 0] using lt _ (hg t)

/-- Stickelberger: for B above p, some J : ℚ/ℤ → ℚ̄^× satisfies, if M ∣ p−1 and Mx = 0: σJ(x) =
J(cyc_M(σ)x); J(x) is a unit off p, of order `floorDiff` c x at B, of absolute value 1 in
all complex embeddings; J(x+b)/J(x) ≡ 1 above primes q ∣ p−1 if qb = 0; ∏_{b mod r}
J(x+b/r)/J(rx) is a root of unity for r ∣ M prime to c.

Known result: Stickelberger's factorisation of Gauss sums; Davenport–Hasse product relation. -/
lemma exists_jacobi_family : ∃ J : _ → _, ∀ {M} [NeZero M], p ≡ 1 [MOD M] → ∀ ⦃x⦄, M • x = 0 →
  (∀ r [NeZero r], r ∣ M → c.Coprime r → IsOfFinAddOrder (∑ b, J (x + ofZMod r b) - J (r • x))) ∧
  (∀ σ (a : ℕ), (cycCharMod Ω M σ).1 = a → galUnitsRep σ (J x) = J (a • x)) ∧ (∀ A : ClosurePlace,
  A.valuation p = 1 → A.valuation (J x).toMul.1 = 1) ∧ ordRat ℚ B (J x) = floorDiff c x ∧ (∀ τ :
  Ω →+* ℂ, ‖τ (J x).toMul.1‖ = 1) ∧ ∀ q [Fact q.Prime] A b, q • b = 0 → q ∣ p - 1 →
  A.valuation q < 1 → J (x + b) - J x ∈ principalUnits A := by
  let n := p.pred; have := of_pos hp.1.pred_pos
  have {m} [NeZero m] := (@HasEnoughRootsOfUnity.prim Ω _ m).choose_spec.toInteger_isPrimitiveRoot
  obtain ⟨hψ, ⟨χ, w⟩, cp, _, _, _, R⟩ := zmodChar_primitive_of_primitive_root p this, PSigma.mk _
    (zmodChar_primitive_of_primitive_root n (.iff_orderOf.2 (exists_mulChar_orderOf (ZMod p)
    (by aesop) this).choose_spec)), n.coprime_of_lt_prime out (p.pred_lt out) Fact.out,
    exists_rat_place_of_prime hp.1
  have := gaussSum_one_left (@hψ 1 out)
  have gn t := by_cases (by aesop) (Dvd.intro _ <| gaussSum_mul_gaussSum_eq_card (χ := χ t) · hψ)
  let G t := DiscreteUnits.ofNeZero _ (RingOfIntegers.ext.mt (ne_zero_of_dvd_ne_zero out (gn t)))
  have {A} h t : valuation A (G t).toMul.1 = 1 := (valuation_eq_one_iff ..).1
    (by_contra (h ∘ mem_centrePrime.1 ∘ (centrePrime ..).mem_of_dvd (gn t)))
  obtain ⟨⟨K, H⟩, S, hS, L⟩ := smul_gaussSum G (by tauto), stickelberger hB G (by tauto) hψ w cp
  have {x m} h d : x ∈ S.range := ((bijective_ofZMod_comp (by simp)).2 S).rec (fun _ e ↦ e ▸
    (·.of_comp (f := ofZMod _).bijective_of_finite.2.exists.1
    (exists_ofZMod (Submodule.torsionBy_le_torsionBy_of_dvd m _ d h)))) hS
  let j := c • G - G ∘ (c • ·)
  use (⇑S).extend (j - j ∘ (-·)) 0, fun hM ↦ forall₂_and.2 ((fun E ↦ ⟨?_, E⟩) fun _ h ↦ ?_)
  obtain ⟨t, ⟨⟩⟩ := this h hM.symm.dvd'
  simp_rw [← map_nsmul, hS.extend_apply]
  and_intros <;> intros; simp [j, H, (rootPowHom ..).2.1 ((map_cycCharMod_mul _ _ t).trans
    (by rw [cycCharMod_eq_iff_unitsRep.1 ‹_› (by simp_all), map_nsmul])), -nsmul_eq_mul]
  simp [*, j, valuationVia]; simp [floorDiff, map_nsmul, ← nsmul_eq_mul, ← L, j]
  obtain ⟨g, e⟩ := exists_smul_emb_eq Gal(Ω/ℚ) ‹_› (star ‹_›) (by bound)
  simp [e, -AlgEquiv.smul_def, (by simp [j, H, IsComplexConj.cycCharMod_eq_neg_one ⟨_, e⟩] :
    j (-t) = galUnitsRep g (j t))]
  obtain ⟨_, ⟨⟩⟩ := this ‹_› ‹_›
  have (t) s (_ : ‹ℕ› • s = 0) : G (t + s) - G t ∈ principalUnits ‹_› := show valuation _ _ < 1 by
    simp [*, valuationVia, (cp.symm.of_dvd_left ‹_›).valuation_eq_one]; exact mem_centrePrime (x :=
    (_ - _ : 𝓞 Ω)).1 (by simp [gaussSum, residue_eq_one_of_pow_prime_eq_one ‹_›, *,
      sum_eq_add_sum_units])
  simp_all [← map_add, ← eq_iff_sub_mem, add_comm, mul_add, mul_right_comm, j]
  rintro x _ r _ ⟨_, ⟨⟩⟩ k
  apply Units.isOfFinOrder_val.1 (isOfFinOrder_of_norm_eq_one (fun A ↦ (A.valuation_le_one
    p).eq_or_lt.rec ?_ ((fun h ↦ (h.ordRat_nonneg_iff _).1 ((h.exists_smul Gal(Ω/ℚ) (R B hB)).rec
    (by simp +contextual [← h.ordRat_smul ·, (E ..).1 _ _ zmod_eq_natCast_val, isUnit_cast_of_dvd,
    smul_comm (r * _), *, smul_comm r, sum_floorDiff k]))) ∘ R A)) ?_) <;> erw
    [toMul_sub] <;> simp +contextual [*, smul_comm]
