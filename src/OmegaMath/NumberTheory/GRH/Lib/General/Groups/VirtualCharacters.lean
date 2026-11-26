import OmegaMath.NumberTheory.GRH.Lib.General.Combinatorics.Average
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of group theory (textbook or folklore).

This file: Basic properties of characters and virtual characters of finite groups. -/


open ComplexConjugate Submodule AddChar LinearMap IsMulCommutative Classical Finset Fint Subgroup
variable {S} [CommSemiring S] [Algebra S ℂ] {G} [Group G] {χ ψ f : G → ℂ}

lemma IsChar.mul : IsChar χ → IsChar ψ → IsChar (χ * ψ) := by grind [IsChar, =_ FDRep.char_tensor]

lemma isChar_monoidHom (l : G →* ℂ) : IsChar l :=
  ⟨.of (.comp .smulOneHom l), funext (Algebra.trace_self_apply <| l ·)⟩

variable (S G) in
/-- For a group G and a commutative semiring S acting on ℂ, the S-subalgebra of functions G → ℂ
spanned over S by the characters of G. -/
def virtualChars := (span S {f | @IsChar G _ f}).toSubalgebra (subset_span (isChar_monoidHom 1))
  (BilinMap.apply_apply_mem_of_mem_span _ _ _ (.mul ..) fun _ a _ b ↦ subset_span (a.mul b))

/-- A function on a group G in the ℕ-span of the characters of G is itself a character. -/
lemma isChar_of_mem_virtualChars (h : f ∈ virtualChars ℕ G) : IsChar f := (span_nat_eq ⟨⟨IsChar,
  fun ⟨ρ, a⟩ ⟨σ, b⟩ ↦ ⟨.of (.prod ρ.ρ σ.ρ), a ▸ b ▸ by ext; apply trace_prodMap'⟩⟩,
  ⟨default, 1⟩, by ext; apply map_zero⟩).le h

variable [Finite G] (h : IsChar χ) (v : f ∈ _root_.virtualChars S G) {H} [Group H]
include h

section

omit [Finite G]

lemma IsChar.comp (p : H →* G) : IsChar (χ ∘ p) := h.imp' (.of <| ·.ρ.comp p) (by aesop)

/-- Every character of a group G lies in the S-span `virtualChars S G` of the characters of G. -/
lemma IsChar.mem_virtualChars : χ ∈ _root_.virtualChars S G := subset_span h

lemma IsChar.isClassFunction : IsClassFunction χ := h.rec (by aesop)

end

lemma IsChar.exists_finMean_eq_natCast : ∃ m : ℕ, finMean χ = m := h.rec fun ρ e ↦
  ⟨_, .trans (by simp [finMean, e, field]) ρ.average_char_eq_finrank_invariants⟩

lemma IsChar.exists_sum_addChar_zpowers (g : G) : ∃ m : AddChar (Additive (zpowers g)) ℂ → ℕ, ∀ u h,
  ∑ l, m l • l (.ofMul ⟨u, h⟩) = χ u := .imp (fun _ e ↦ by simp [← e, finMean, div_eq_inv_mul,
  sum_comm, sum_mul, mul_assoc, ← mul_sum, field, ← map_add_eq_mul, sum_apply_eq_ite,
  neg_add_eq_zero]) (skolem.1 fun l ↦ ((h.comp (zpowers g).subtype).mul
  (isChar_monoidHom (.toAdditive.2 l⁻¹.toAddMonoidHom))).exists_finMean_eq_natCast)

lemma IsChar.apply_inv g : χ g⁻¹ = conj (χ g) := by
  simp [← (h.exists_sum_addChar_zpowers g).choose_spec, ← map_neg_eq_conj]; rfl

lemma IsChar.isIntegral g : IsIntegral ℤ (χ g) :=
  (h.exists_sum_addChar_zpowers g).choose_spec g (by simp) ▸ .sum _
  fun l _ ↦ .nsmul (.of_pow (orderOf_pos l) (by simp [← pow_apply, isIntegral_one])) _

lemma IsChar.star : IsChar (conj <| χ ·) :=
  h.imp' (.of <| .dual ·.ρ) (by aesop (add simp apply_inv))

include v

lemma IsChar.exists_classInner_eq : ∃ m, classInner χ f =
  algebraMap S ℂ m := let ⟨_, a, ψ, e⟩ := mem_span_set'.1 v
  (skolem.1 (ψ · |>.2.mul h.star |>.exists_finMean_eq_natCast)).elim fun m u ↦ ⟨a ⬝ᵥ (m ·), by
                         simp [classInner, dotProduct, ← e, ← u, mul_sum, finMean_sum,
                           ← finMean_const_mul, Algebra.smul_def, mul_rotate']⟩

omit h

omit [Finite G] in
lemma comp_mem_virtualChars [Finite H] (p : H →* G) : f ∘ p ∈ virtualChars S H :=
  mapsTo_span (f := funLeft ..) (fun _ ↦ (·.comp p)) v

omit [Finite G] in
lemma isClassFunction_of_mem_virtualChars : IsClassFunction f := by induction v using
  span_induction <;> simp_all [IsChar.isClassFunction]
