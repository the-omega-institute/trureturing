import GRH.New.Selmer.Corepresentable
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Tied conditions at new primes shrink Selmer groups (see New.Selmer.TwistTheorem).

Part of: Roots of unity keeping polynomial valuations low, in any degree (see
New.Selmer.RootsOfUnityPoints).

This file: Mirror lemma: relations isotropic on a coset are few, killed by a scalar difference. One
polynomial bounds twisted Selmer lengths everywhere, sharply at a chosen point. Points on the line
through a root of unity are almost roots of unity. -/

open Submodule commutatorElement AddMonoidHom Matrix.Module QuotientAddGroup

/-- Let ρ(G) span all matrices, c be an involution, y a cocycle mod I with a unit entry, γ and
(cγ)⁻¹ act by s with s² − 1 a unit, χ(γ) = χ(cγ) = 1, y(γ) = 0. Let U act trivially mod I, H
≤ U be normal, c-stable, containing all [g, γ], and z, cz ∈ U. If distinct χ-equivariant
homomorphisms x_w (w ∈ W) from U to the dual have ⟨x_w, ty⟩ c-invariant on zH, and ρ(g) = α,
ρ(cg)⁻¹ = α' are scalars, then |W| ≤ #(O mod I)^n[α − χ(cg)α']. -/
lemma card_le_torsion_of_isotropic {O G n} [CommRing O] [Group G] [Fintype n] {I : Ideal O}
  [Finite (O ⧸ I)] {ρ : G →* Matrix n n O} (hρ : span O (.range ρ) = ⊤) (χ : G →* O) {c : G →* G}
  (_hc : ∀ g, c (c g) = g) (H U : Subgroup G) [hN : H.Normal] γ {g₀ z} {s : O} {y : G → n → O ⧸ I}
  {W} (x : W → G → _ →+ QZ) (hi : ∀ w v, (∀ g ∈ U, x w g = x v g) → w = v) (hU : ∀ g ∈ U, ∀ m : n →
  O ⧸ I, ρ g • m = m) (hH : ∀ g ∈ H, c g ∈ H ∧ g ∈ U) (κ : ∀ g : G, ⁅g, γ⁆ ∈ H) (p : IsUnit (s - 1))
  (s₂ : IsUnit (s + 1)) (hγ : ρ (c γ)⁻¹ = s • 1 ∧ ρ γ = s • 1 ∧ χ (c γ) = 1 ∧ χ γ = 1 ∧ y γ = 0) (hz
  : z ∈ U ∧ c z ∈ U) (hy : ∀ g h, y (g * h) = y g + ρ g • y h) {i} (hu : IsUnit (y g₀ i)) (hW : ∀ᵉ
  (w) (g) (a ∈ U) (b ∈ U) (m), x w (a * (g * b * g⁻¹)) m = x w a m + x w b (χ g • ρ g⁻¹ • m)) (hq :
  ∀ᵉ (w) (h ∈ H) (t : O), x w (z * h) (t • y (z * h)) = x w (c (z * h)) (t • y (c (z * h))))
  {g α α'} (hδ : ρ g = α • 1 ∧ ρ (c g)⁻¹ = α' • 1) : Nat.card W ≤ .card (torsionBy O (n → O ⧸ I) (α
  - χ (c g) * α')) := have cj g a := eq_sub_of_add_eq (hy (a * g⁻¹) g).symm
  have J k (h : ρ k⁻¹ = s • 1) := by simpa [*, ↓map_mul] using hU (k⁻¹ * k)
  have ⟨τ, hτ, u⟩ : ∃ τ ∈ H, IsUnit (y τ i) := ⟨_, κ g₀, by simpa [map_mul_eq_one, cj, *,
    commutatorElement_def, sub_smul] using (hu.smul (-p.unit))⟩
  have C w {b} v : ∀ t k, x w b (t • ρ k • y τ) = x w (c τ) (χ (c k) • t • ρ (c k)⁻¹ • y (c b))
    := (p.mul s₂).unit.mulRight.forall_congr_right.1 fun r k ↦ by
    have F {b} v t := congr($(hq w b v (r * s * t)) -
      $(hq w _ (mul_mem v (hN.1 _ hτ k)) (r * s * t)))
    linear_combination (norm := simp (maxDischargeDepth := 6) [cj, hW, ↓hU, hy, hz, v, hH, hγ, J,
      hτ, mul_mem, hN.1, by simpa using hW w 1, mul_smul, sub_eq_add_neg, add_smul,
      ↓smul_comm (ρ _), ↓smul_add])
      F (mul_mem v (hN.1 b v γ)) 1 - F v (s + 1) + F H.one_mem s
    abel
  have V {f} h := functions_ext _ f 0 fun j m ↦ by
    simpa [Algebra.smul_def, mul_assoc] using closure_induction (p := fun A _ ↦ f (A • y τ) = 0)
      (by simp) (by grind [add_smul]) h (eq_top_iff'.1 hρ (.single j i (m * u.unit⁻¹).out))
  (Nat.card_le_card_of_injective (fun w ↦ lift _ (x w (c τ)) ((range_le_ker_iff
   (DistribSMul.toAddMonoidHom _ _) _).2
   (V (by simpa [smul_smul, ↓sub_smul, *, -_hc, mul_comm α, mul_comm α', mul_assoc] using (C w (hH _
    hτ).1 · <| · * g))))) fun w v e ↦ hi w v fun g o ↦ ext (p.smul_bijective.2.forall.2 fun m ↦
    have Z w := sub_eq_of_eq_add (hW w γ ⁅g, γ⁆ (by simp [*]) g o (ρ γ • m))
    by simpa [commutatorElement_def, *, mul_assoc, sub_smul, sub_mul, mul_sub, sub_eq_zero,
      ↓smul_smul] using ((Z
      w).congr (Z v)).2 congr($(sub_eq_zero.1 (V (by simp [*, by simpa [DFunLike.ext_iff, forall_mk]
      using e]))) _))).trans_eq ((card_hom_QZ _).trans AddSubgroup.index_range)

open IsDiscreteValuationRing Matrix Module Ideal MvPolynomial NeZero Finsupp

attribute [local simp] MulAction.compHom_smul_def mapRel linearCombination_apply twistAtPoint
  Module.smul_def sum_mapRange_index mem_obeying _root_.funext_iff mem_selmerModule_iff
  Algebra.smul_def algebraMap_eq_diagonal

/-- Let ρ modulo ℓ^M and h: Gal(Ω/E) → (ℤ/q)^σ be continuous. For each tuple y₀ over O some
polynomial F bounds the Selmer length of y^h·ρ modulo ℓ^M by v(F(y)) at every tuple y over every
discrete valuation ring over O, with equality at y₀. -/
lemma exists_sharp_fitting_poly {ℓ M q E n σ O₀ O} [NeZero ℓ] [Field E] [EmbeddedNumberField E]
  [Fintype n] [Fintype σ] [CommRing O₀] [CommRing O] [DVR O] [CharZero O] {ρ : Gal(Ω/E) →* Matrix n
  n O₀} e₀ (S : Finset (FinPlace E)) {h} (hh : ∀ j : σ, IsLocallyConstant (h j)) (hρ :
  IsLocallyConstant (reduceModPow ℓ M ρ)) L y₀ : ∃ F, addVal O (MvPolynomial.eval y₀ F) ≤ length O
  (selmerModule (twistAtPoint (q := q) h y₀ e₀ ρ) S (mapRel e₀ '' L) (QuotSpan (ℓ ^ M : O))) ∧
  ∀ O' [CommRing O'] [DVR O'] e y, length O' (selmerModule (twistAtPoint h y (e.comp e₀) ρ) S
  (mapRel (e.comp e₀) '' L) (QuotSpan (ℓ ^ M : O'))) ≤ addVal O' (eval₂Hom e y F) := by
  choose ι _ γ R r H using
    exists_corepresenting_coords (ℓ ^ M) (twistAtPoint h X (C.comp e₀) ρ) ((hρ.eventually_eq 1).and
    (.all (hh · |>.eventually_eq 1))) S.finite_toSet (mapRel (C.comp e₀) '' L)
  choose A W hu hW k using exists_matrix_addVal_det_le_length (.map ((aeval y₀).toLinearMap.compLeft
    _) (R.restrictScalars O)) (ne (ℓ.cast ^ M)) (⟨_, r <| C ∘ ·, by simp⟩)
  choose u hu hu' using hu
  have K {O'} [CommRing O'] (e : O →+* O') y :=
    @H (O' ⧸ _) _ (.compHom _ (eval₂Hom e y)) nsmul_quot_eq_zero
   fun g ⟨a, b⟩ ↦ by simpa [b] using! congr((($a).map (quotientMap _ (e.comp e₀) (by simp))).mulVec)
  use det u, ?_, fun O _ _ e y ↦ ?_ <;> erw [RingHom.map_det]
  exact (funext hu' ▸ k).trans (length_le_of_le_map ⟨⟨(↿· ∘ γ), by tauto⟩, by tauto⟩ _ fun w h ↦ by
    simpa using (K ..).2.2 ((hW _).1 ⟨·, ·, rfl⟩ w h))
  grw [← length_ker_le_addVal_det, ← relLength_bot,
    relLength_le_of_inj ⟨⟨(↿· ∘ γ), by tauto⟩, by tauto⟩, relLength_bot]
  simpa using! (@(K e y).1 · · _ <| hu ·)
  simpa using! (@(K e y).2.1 · · 0)

lemma dvd_one_add_mul_pow_sub_one {ℓ O k N} [p : ThePrime ℓ] [CommRing O] t {u : O} (h :
  u ^ ℓ ^ k = 1) M (a : k + M ≤
  N) : ↑ℓ ∣ (1 + t * (u - 1) - 1) ^ ℓ ^ k ∧ (ℓ : O) ^ M ∣ (1 + t * (u - 1)) ^ ℓ ^ N - 1 := by
  have H a := congr((ℓ : O) ∣ $(add_pow_prime_pow_eq' p.out 1 a k) - 1)
  simp [add_assoc, dvd_add_left] at H
  refine ⟨?t, by simpa [← pow_mul, ← pow_add, a.trans'] using
    (pow_dvd_pow _ (by lia)).trans (dvd_sub_pow_of_dvd_sub ((H _).2 ?t) (N - k))⟩
  simp [mul_pow, Dvd.dvd.mul_left, ← H, h]
