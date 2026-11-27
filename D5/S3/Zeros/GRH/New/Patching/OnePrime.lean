/- GID: D5/S3/Zeros/GRH/New/Patching/OnePrime
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Patching/OnePrime
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Patching.OnePrime. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Patching/OnePrime.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.LocalGL.Iwahori.HeckeOnLineStabiliser
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Deformed trace at one auxiliary level bounds the denominator (see
New.Patching.OnePrimeTie).

This file: Transfer to finite GL_n of a line-stabiliser character factors through the determinant.
First-order deformation of the trace at one prime via logarithm and transfer, abstract ring form. -/

open Nat Valued Finset IsLocalRing Units Matrix Pi GeneralLinearGroup SpecialLinearGroup

/-- Let m ∣ q − 1 and u generate k_w^×. The stabiliser H of the first coordinate line in
GL_N(k_w) has a character a to Z/m, a function of the first entry sending u to 1; its
transfer is a function d of det; both kill the pro-p Iwahori group; some γ has transfer
d(u), and N!·d(u) = N!. -/
lemma exists_line_stabilizer_log {E} [Field E] [NumberField E] {w : FinPlace E} N [NeZero N] {m}
  (hm : m ∣ w.q - 1) {u h} (hu : ∀ z, z ∈ Subgroup.zpowers ((LocInt w).unitGroupToResidueFieldUnits
  ⟨u, h⟩)) : ∃ (H : Subgroup (GL (Fin N) (ResField w))) (a : H →* Multiplicative (ZMod m)) (lg d :
  _ → _), ∃ γ, (∀ g : Kw _ w, (reduceGL g ∈ H ↔ g.1 ∈ blockParahoric (min 1)) ∧
  (∀ h, a ⟨reduceGL g, h⟩ = lg (g.1 0 0)) ∧ a.transfer (reduceGL g) = d g.1.1.det ∧
  (g.1 ∈ proIwahori → a.transfer (reduceGL g) = 1 ∧ ∀ h, a ⟨reduceGL g, h⟩ = 1)) ∧
  lg u = .ofAdd 1 ∧ a.transfer γ = d u ∧ N ! * (a.transfer γ).toAdd = N ! := by
  let H := parabolic (R := ResField w) (min 1 ∘ @Fin.val N)
  choose! Λ L using (@id <| IsUnit <| residueOrZero (w := w) ·)
  have K {x y z} : residue _ y = x.1 → ↑y = z → x =
    Λ z := by grind [residueOrZero_coe, x.ext, IsUnit]
  have ⟨l, hz⟩ : ∃ l : _ →* Multiplicative (ZMod m), l (Λ u) = .ofAdd 1 :=
    ⟨_, (@K _ _ u rfl rfl).rec (monoidHomOfForallMemZpowers_apply_gen hu
    (by simpa [orderOf_eq_card_of_forall_mem_zpowers hu, card_units, ← card_ResField] using! hm))⟩
  let a := l.comp (⟨⟨(·.1 0 0), by simp⟩, fun _ h ↦ mul_apply.trans
    (Fintype.sum_eq_single 0 fun x hx ↦ by
    simp [@h.2 x 0 (by simpa [Fin.pos_iff_ne_zero] using hx)])⟩ : H →* _).toHomUnits; let d :=
      a.transfer.comp (diagGL.comp (.mulSingle _ 0))
  simp [← card_ResField, ← ZMod.natCast_eq_zero_iff] at hm
  have D {g} : g ∈ a.transfer.eqLocusM (d.comp det) := (Submonoid.mem_map_iff_mem
    coeHom_injective).1 (diagonal_transvection_induction_of_det_ne_zero _ _ g.det_ne_zero (fun D h ↦
    ⟨_, mulSingle_induction (diagGL · ∈ _) (fun i ↦ mk0 (D i) (by simp_all [prod_eq_zero_iff])) (by
    simp) (by simp_all) fun i x ↦ .trans (by simp [mul_assoc, d, mulSingle_comp_equiv,
    eq_mul_inv_of_mul_eq (diagGL_mul_permGL (mulSingle i _) (.swap 0 i))]) congr(d $(x.ext (by
    simp [← Units.coe_prod]))), rfl⟩) (fun t ↦ ⟨t.toSpecialLinearGroup, by simpa [*, ↓map_nsmul]
    using! (congr(AddMonoidHom.mk' (fun c ↦ (a.transfer (toGL (transvection t.3 c))).toAdd) (by
    simp [transvection_add]) $card_nsmul_eq_zero')), rfl⟩) (by bound))
  refine ⟨_, a, l ∘ Λ, d ∘ Λ, _, fun g ↦ by
    simpa [blockParahoric, proIwahori, residuePreimage, ↓Subgroup.copy_eq] using ⟨by bound, fun _ ↦
      congrArg l (K rfl rfl), D.trans (congrArg d (K (RingHom.map_det ..) (𝒪[_].subtype.map_det
      _))), fun _ k ↦ ⟨D.trans (d.map_one ▸ congrArg d (ext (det_eq_one_of_unitriangular k))),
      fun _ ↦ l.map_one ▸ congrArg l (ext (by simpa using! k 0 0))⟩⟩, hz, rfl, ?_⟩
  simpa [*, index_stabilizer_line 0 (H := H) fun _ ↦ forall_congr' (by grind), mul_assoc,
    ← mul_factorial_pred NeZero.out, mul_comm N] using! congr(_ * ($(D.symm.trans
    ((a.transfer_eq_pow (scalar _ _) (by simp [← map_pow, ← GeneralLinearGroup.scalar_commute])
    ).trans congr(l $(ext (v := Λ u ^ H.index) (by simp [← map_pow])))))).toAdd)

open Subgroup IsComplement MulAction leftTransversals ZMod

attribute [-simp] zsmul_eq_mul zsmul_one

variable {Γ R} [Group Γ] [Fintype Γ] [Ring R] {m} [NeZero m] (ρ : Γ →* R) {H : Subgroup Γ}
  (c : Γ →* Multiplicative (ZMod m)) {S} [Ring S] (σ : R →+* S) (hm : (m : S) = 0)

/-- The additive map sending an integer-valued function f on Z/m to the weighted sum ∑_g f(c(g))
ρ(g) in R. -/
def weightedSum : (ZMod m → ℤ) →+ R := .mk' (∑ g, · (c g).toAdd • ρ g) (by simp [add_smul])

omit [NeZero m] in
lemma mul_weightedSum f g : ρ g * weightedSum ρ c f = weightedSum ρ c (f <| · - (c g).toAdd) :=
  (mul_sum ..).trans (sum_equiv (.mulLeft g) (by simp) (by simp))

include hm

omit [NeZero m] in
/-- Let σ: R → S be a ring homomorphism with m = 0 in S, and B an additive map from
integer-valued functions to R. If f ≡ g modulo m pointwise, then σ(B(f)) = σ(B(g)). -/
lemma map_eq_of_weights_modEq {ι} (B : _ →+ R) (f g : ι → ℤ) (h : ∀ x, (g x : ZMod m) = f x) :
    σ (B f) = σ (B g) := by simpa [hm, ↓map_nsmul] using congr(σ (B $((funext
    (h · |> (intCast_eq_intCast_iff ..).1 |>.dvd.choose_spec) : f - g = m • _))))

omit [NeZero m] in
/-- Let σ kill m, N = ∑ρ(g), |Γ| regular, ρ(H) fix B1, LB1 = 0, Lρ(g) = L, ∑_H ρ(p⁻¹)Ψρ(p) = n,
k·transfer(a)(γ) = k, B shift by a under H, 𝒜 contain ρ(Γ), im B and commute with ac. Then some
F ∈ 𝒜 has σ(nF(ρ(g) − 1)) = σ(NZ_g), LZ_g = 0, and 2kσ(F·ac t) = 2kσ(Nr) under two weighted-sum
identities linking t, t', r. -/
lemma one_prime_first_order (a : H →* Multiplicative (ZMod m)) (B : _ →+ R) (hB : ∀ f (p : H),
  B f * ρ p = B (f <| · - (a p).toAdd)) (𝒜 : Subring R) (hρ : ∀ g, ρ g ∈ 𝒜) (h𝒜 : ∀ f, B f ∈ 𝒜) {A}
  {ac : A → R} (hc : ∀ {x}, x ∈ 𝒜 → ∀ t, Commute (ac t) x) {Ψ L γ} {n k : ℕ} (hΨ : ∑ p : H,
  ρ ↑p⁻¹ * Ψ * ρ p = n) (hX : ∀ p ∈ H, ρ p * B 1 = B 1) (h : L * B 1 = 0) (hL : ∀ g, L * ρ g =
  L) (tf : IsSMulRegular R (Fintype.card Γ)) (hn : k * (a.transfer γ).toAdd = k) : ∃ F ∈ 𝒜, (∀ g,
  ∃ Z, σ (n • (F * (ρ g - 1))) = σ ((∑ g, ρ g) * Z) ∧ L * Z = 0) ∧ ∀ {t t' r}, (∀ f : ZMod m → ℤ,
  B ((f <| · - k) - f) * ac t = weightedSum (ρ.comp H.subtype) a ((f <| · - k) - f) * ac t') →
  (∀ f, weightedSum ρ a.transfer f * ac t' = (ρ γ - 1) * weightedSum ρ a.transfer f * r) →
  (2 * k) • (σ F * σ (ac t)) = (2 * k) • (σ (∑ g, ρ g) * σ r) := by
  let T := ∑ η : Γ ⧸ H, ρ η.out
  let U := ∑ η : Γ ⧸ H, ρ η.out⁻¹
  let v := @valMinAbs m
  -- the component in H with respect to the representatives
  let w (g x : Γ) : H := ⟨_, QuotientGroup.eq.1 (g • x : Γ ⧸ H).out_eq⟩
  have key (f : H → ℤ) x : T * (∑ p, f p • ρ p) * ρ x⁻¹ = ∑ g, f (w g x) • ρ g := by
    rw [sum_mul_sum, ← sum_product', sum_mul, sum_nbij' (fun (η, p) ↦ η.out * p * x⁻¹)
      fun g ↦ (↑(g * x), w g x)] <;> simp [w]
  have e : (∑ g, ρ g) * (Ψ * B 1) = n • T * B 1 := by simpa [← by simpa using key 1 1, hX, ←
    (Equiv.sum_comp (.inv H) (ρ ·)), sum_mul, mul_assoc, ← nsmul_eq_mul] using congr(T * $hΨ * B 1)
  use T * B (-v) * U, by grind [mul_mem, sum_mem], fun g ↦ ⟨Ψ * B 1 * ∑ η : Γ ⧸ H,
    v (a (w g η.out)).toAdd • ρ η.out⁻¹, ?_, by simp [← mul_assoc, @tf _ 0
    (by simpa [T, mul_sum, ← mul_assoc, hL, h, -nsmul_eq_mul] using congr(L * $e))]⟩,
    fun h₁ h₂ ↦ .trans ?_ (congr(-σ $(h₂ ((2 * k) • v))).trans ?_)
  · rw [← mul_assoc, e, mul_sub, mul_assoc, sum_mul _ _ (ρ g), ← Fintype.sum_equiv (toPerm
      g) (fun η ↦ ρ (w g η.out * η.out⁻¹)) _ (by simp [w, mul_assoc])]
    simp [mul_sum, mul_assoc, ← mul_assoc (B _), hB, sub_mul, mul_sub, U, v, fun y ↦
      map_eq_of_weights_modEq σ hm B (v <| · - y) (v - v y • 1)]
  · have e₂ : σ (T * weightedSum (ρ.comp H.subtype) a v * U) = σ (weightedSum ρ a.transfer v) := by
      -- conjugating by the representatives sums the weights over the cosets
      erw [mul_sum, funext fun _ ↦ key .., ← map_sum (Fintype.linearCombination ..).toAddMonoidHom]
      apply map_eq_of_weights_modEq σ hm; simp [v, diff, fun g ↦ a.transfer_def (g⁻¹ • default) g,
        mul_assoc, smul_apply_eq_smul_apply_inv_smul, leftQuotientEquiv_apply _]; congr!; simp
    -- small orders: the weight a (a + k) and its translate (a - k) a differ by 2 k a
    simpa (disch := simp_intro x [v]; ring) [← e₂, mul_assoc, (@hc U (sum_mem (by tauto)) _).eq,
      -map_sub, -nsmul_eq_mul, map_eq_of_weights_modEq σ hm _ _ ((2 * k) • v)]
      using congr(σ (T * $(h₁ fun x ↦ -v x * (v x + k)) * U))
  rw [sub_one_mul, mul_weightedSum, ← map_sub, map_mul, map_eq_of_weights_modEq σ hm _ _ (-2 *
    k)] <;> simp [weightedSum, v, ← mul_sum, mul_sub, mul_assoc, @zsmul_eq_mul S, hn]
