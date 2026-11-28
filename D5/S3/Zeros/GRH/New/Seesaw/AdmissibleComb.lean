/- GID: D5/S3/Zeros/GRH/New/Seesaw/AdmissibleComb
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/AdmissibleComb
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.AdmissibleComb. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/AdmissibleComb.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Seesaw.IntegralAway
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: size bookkeeping for the data of this proof.

This file: Calculus of finite combinations tracking support, denominator and size of conjugates. -/

open Finsupp Function
variable {α α' Z Z'} [AddCommGroup Z] [Module ℂ Z] [AddCommGroup Z'] [Module ℂ Z'] (v : α → Z)

/-- The statement that z = ∑ r(x) v(x) for some finitely supported r that is admissible
(`IsAdmissibleCoeffs`) for A, n, d, p, B. -/
def IsAdmissibleComb A n d p B z := ∃ r, IsAdmissibleCoeffs A n d p B r ∧ z = r.sum fun x ↦
  (· • v x)

namespace IsAdmissibleComb

variable {v A} {A' : Set α'} {n d p B z v' d' B' z' s} (h : IsAdmissibleComb v A n d p B z)
attribute [local simp] single_apply smul_smul smul_sum IsAdmissibleCoeffs.mk

lemma of_sum {c : α → ℂ} (hc : ∀ i ∈ s, d * c i ∈ integralAway n) (hB : p → ∀ σ : ℂ ≃+* ℂ, ∑ i ∈ s,
  ‖σ (c i)‖ ≤ B) : IsAdmissibleComb v s n d p B (∑ i ∈ s, c i • v i) :=
  ⟨indicator s (fun _ ↦ c ·), by simp_all [↓sum_indicator_index, apply_ite]⟩

lemma single x (hx : x ∈ A) : IsAdmissibleComb v A n d p 1 (v x) :=
  ⟨.single x 1, by simp_all [apply_ite]⟩

include h

/-- If z is an admissible combination of the v x, x ∈ A (denominator d, size B), and each such v
x is an admissible combination of the v' (d', B'), then so is z, with any denominator e divisible by
dd' and, under p, any size C ≥ B|B'|. -/
lemma bind {e C} d' B' (H : ∀ x ∈ A, IsAdmissibleComb v' A' n d' p B' (v x)) (hd :
  d * d' ∣ e := by simp) (hB : p → B * |B'| ≤ C := by simp) : IsAdmissibleComb v' A' n e p C z := by
  obtain ⟨⟨c, hc, ⟨⟩⟩, ⟨⟩⟩ := h, hd; choose! r hr e using H
  use c.support.sum (⇑c • r), ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all [↓← @linearCombination_apply α',
    sum, hc.1, Finset.mul_sum] <;> (try apply sum_mem) <;> try grind [IsAdmissibleCoeffs,
    Finset.sum_eq_zero, mul_mem, natCast_mem, mul_comm, mul_assoc]
  grw [← hB, ← hc.3 ⟨⟩, sum_mul, sum, ← le_abs_self, norm_sum_le, Finset.sum_comm, norm_mul_le]
  gcongr
  grw [← (hr _ (hc.1 _ ‹_›)).3 ⟨⟩, mul_sum, ← Finset.sum_filter_ne_zero, sum]; gcongr; aesop_cat

lemma map (L : Z →ₗ[ℂ] Z') : IsAdmissibleComb (L ∘ v) A n d p B (L z) := h.imp (by simp_all [sum])

lemma smul {c} (hc : c ∈ integralAway n) (hc' : p → ∀ σ : ℂ ≃+* ℂ, ‖σ c‖ ≤ 1) :
  IsAdmissibleComb v A n d p B (c • z) := (h.map (c • 1)).bind 1 1
  (fun _ ↦ ⟨.single · c, by simp_all [apply_ite]⟩)

lemma smul_of_eq_zero_or_isOfFinOrder {ζ : ℂ} (o : ζ = 0 ∨ IsOfFinOrder ζ) : IsAdmissibleComb v A n
  d p B (ζ • z) := have {R} [NormedField R] (f : ℂ →+* R) := o.elim (by aesop) (f.1.isOfFinOrder ·
    |>.norm_eq_one.le); h.smul (by tauto) fun _ σ ↦ this σ.toRingHom

lemma of_eq_isOfFinOrder_smul : (∀ x ∈ A, ∃ ζ : ℂ, IsOfFinOrder ζ ∧ ∃ y ∈ A', v x = ζ • v' y) →
    IsAdmissibleComb v' A' n d p B z :=
  (h.bind 1 1 ·) ∘ by grind [smul_of_eq_zero_or_isOfFinOrder, single]

lemma map_bilinear {W} [AddCommGroup W] [Module ℂ W] (b : Z →ₗ[ℂ] Z' →ₗ[ℂ] W) (g :
  IsAdmissibleComb v' A' n d' p B'
  z') : IsAdmissibleComb (fun x ↦ b (v x.1) (v' x.2)) (A ×ˢ A') n (d * d') p (B * |B'|) (b z z') :=
  (h.map (b.flip _)).bind d' B' fun _ a ↦ (g.map _).bind 1 1 fun _ ↦ (single (_, _) ⟨a, ·⟩)

/-- Let z be a combination (`IsAdmissibleComb`) of the v x, x ∈ A, with coefficients integral
away from n up to the denominator d; l a prime not dividing n, ι : ℂ → ℂ_l. Then dz lies in
every module over ι⁻¹(𝒪_{ℂ_l}) containing all v x. -/
lemma smul_mem {l} [Fact l.Prime] [PadicPlace l] (hq : l.Coprime n) {M : Submodule embValRing Z}
    (hv : ∀ x ∈ A, v x ∈ M) : (d : ℂ) • z ∈ M := by
  obtain ⟨r, h, ⟨⟩⟩ := h
  simpa using! sum_mem (M.smul_mem ⟨_, h.2 _ l hq _⟩ ∘ hv · ∘ h.1 _)

omit h

lemma pure {α F : ℕ → _} [∀ j, AddGroup (α j)] [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] {v :
  ∀ i, α (2 * i) × α (2 * i + 1) → F i} {A : ∀ _, AddSubgroup _} {f} d B m :
  (∀ i < m, IsAdmissibleComb (v i) (A _ ×ˢ A _) n d p B (f i)) → IsAdmissibleComb (fun y : ∀ _, _ ↦
  TensorChain.pure (v · (y _, y _)) m) {y | ∀ j, y j ∈ A j} n (d ^ m) p (|B| ^ m) (TensorChain.pure
  f m) := m.rec (single 0 ∘ by simp) fun m i h ↦ ((i (by grind)).map_bilinear (TensorProduct.mk
  ..).flip (h m .refl)).of_eq_isOfFinOrder_smul fun (s, t, u) _ ↦ ⟨1, .one, update (update s _ t) _
  u, by grind [SetLike.mem_coe], congr($(by simp) ⊗ₜ $(TensorChain.pure_congr (by grind)))⟩

lemma normUnit_smul {C : ℂ} a (hd : d ≠ 0) : IsAdmissibleComb (C • v ·) A n d p B z →
  IsAdmissibleComb v A n 1 p (d * B) ((normUnit (a * C / d)).1 • a • z) := by
  rintro ⟨r, ⟨⟩, ⟨⟩⟩; convert smul_of_eq_zero_or_isOfFinOrder (ζ := normalize (a * C / d)) ⟨d • r,
    _, rfl⟩ _ using 1 <;> simp_all
    [sum_smul_index', ← mul_sum, hd.pos, or_iff_not_imp_left, normalize]; field_simp
