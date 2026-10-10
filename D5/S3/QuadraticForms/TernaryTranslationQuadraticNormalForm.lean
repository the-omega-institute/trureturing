/- GID: D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ternary translation quadratic forms split into binary bilinear blocks. -/

/-
Per-declaration judgement:
  F: proof_shape: bind-only; escape_witness: none.
    consumer: enc_quadratic, ternary_translation_quadratic_normal_form,
      StabilizerMultiEntropyCollapse.graph_count, StabilizerMultiEntropyCollapse.graph_replica_form,
      StabilizerMultiEntropyCollapse.quadratic_sum.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  C: proof_shape: bind-only; escape_witness: none.
    consumer: enc_quadratic, ternary_translation_quadratic_normal_form,
      StabilizerMultiEntropyCollapse.entropy_formula,
      StabilizerMultiEntropyCollapse.entropy_partition, StabilizerMultiEntropyCollapse.graph_count,
      StabilizerMultiEntropyCollapse.quadratic_sum, StabilizerMultiEntropyCollapse.rank_partition,
      StabilizerMultiEntropyCollapse.result,
      StabilizerMultiEntropyCollapse.stabilizer_replica_count,
      StabilizerMultiEntropyCollapse.stabilizer_replica_positive.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  K: proof_shape: bind-only; escape_witness: none.
    consumer: chi_laws, chi_orthogonal, chi_product, edge_cut_sum, edge_pair_sum, enc_injective,
      enc_linear, f4_frobenius, fourier_inverse, fourier_shift_real, ft, hat, phase_cut,
      trace_cross, tw, χ.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  f4_frobenius: proof_shape: bind-only; escape_witness: none.
    consumer: trace_cross.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  χ: proof_shape: bind-only; escape_witness: none.
    consumer: chi_laws, chi_orthogonal, chi_product, edge_cut_sum, edge_pair_sum, enc_injective,
      enc_linear, fourier_inverse, fourier_shift_real, ft, tw.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  ft: proof_shape: bind-only; escape_witness: none.
    consumer: edge_pair_sum, enc_injective, fourier_inverse, fourier_shift_real, hat.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  hat: proof_shape: bind-only; escape_witness: none.
    consumer: edge_cut_sum, edge_pair_sum, enc_injective, enc_linear, fourier_shift_real, tw.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  tw: proof_shape: bind-only; escape_witness: none.
    consumer: edge_cut_sum, enc, enc_injective, enc_linear, enc_quadratic.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  T: proof_shape: bind-only; escape_witness: none.
    consumer: W, edge_cut_sum, edge_pair_sum, enc, enc_bijective, enc_injective, enc_linear,
      enc_quadratic, pair_index, ternary_translation_quadratic_normal_form.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  V: proof_shape: bind-only; escape_witness: none.
    consumer: enc, enc_bijective, enc_injective, enc_linear, enc_quadratic,
      ternary_translation_quadratic_normal_form.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  W: proof_shape: bind-only; escape_witness: none.
    consumer: enc, enc_bijective, enc_injective, enc_linear,
      ternary_translation_quadratic_normal_form.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  Rep: proof_shape: bind-only; escape_witness: none.
    consumer: edge_cut_sum, edge_pair_sum, enc_bijective, enc_injective, enc_quadratic, pair_index.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  enc: proof_shape: bind-only; escape_witness: none.
    consumer: enc_bijective, enc_injective, enc_linear, enc_quadratic,
      ternary_translation_quadratic_normal_form.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  phase_table: proof_shape: bind-only; escape_witness: none.
    consumer: chi_laws, chi_orthogonal, edge_cut_sum.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  chi_laws: proof_shape: bind-only; escape_witness: none.
    consumer: edge_pair_sum, enc_injective, fourier_inverse, fourier_shift_real.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  chi_product: proof_shape: bind-only; escape_witness: none.
    consumer: chi_orthogonal.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  chi_orthogonal: proof_shape: bind-only; escape_witness: none.
    consumer: fourier_inverse.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  fourier_inverse: proof_shape: bind-only; escape_witness: none.
    consumer: edge_pair_sum, enc_injective.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  fourier_shift_real: proof_shape: bind-only; escape_witness: none.
    consumer: edge_pair_sum, enc_injective.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  pair_index: proof_shape: bind-only; escape_witness: none.
    consumer: edge_pair_sum, enc_bijective, enc_injective.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  enc_linear: proof_shape: bind-only; escape_witness: none.
    consumer: ternary_translation_quadratic_normal_form.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  enc_injective: proof_shape: bind-only; escape_witness: none.
    consumer: enc_bijective.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  enc_bijective: proof_shape: bind-only; escape_witness: none.
    consumer: ternary_translation_quadratic_normal_form.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  phase_cut: proof_shape: bind-only; escape_witness: none.
    consumer: edge_cut_sum.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  trace_cross: proof_shape: bind-only; escape_witness: none.
    consumer: edge_cut_sum.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  edge_pair_sum: proof_shape: bind-only; escape_witness: none.
    consumer: edge_cut_sum.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  edge_cut_sum: proof_shape: bind-only; escape_witness: none.
    consumer: enc_quadratic.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  triangle_bilinear: proof_shape: bind-only; escape_witness: none.
    consumer: enc_quadratic.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  enc_quadratic: proof_shape: bind-only; escape_witness: none.
    consumer: ternary_translation_quadratic_normal_form.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
  ternary_translation_quadratic_normal_form: proof_shape: bind-only; escape_witness: none.
    consumer: StabilizerMultiEntropyCollapse.graph_count,
      StabilizerMultiEntropyCollapse.quadratic_sum.
    admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
Utility: none. The declarations give general mathematical identities and constructions;
fixed field and mode checks occur only inside parameterized proofs. No declaration
is an instance certificate, bounded enumeration result, checker or numeric reduction.
Direct frozen dependencies:
  none (Mathlib only).
-/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

open scoped BigOperators

namespace D5.S3.QuadraticForms.TernaryTranslationQuadraticNormalForm

noncomputable section

def F {N d : ℕ} (A : Matrix (Fin N) (Fin N) (ZMod 2))
    (δ : Fin N → (Fin d → ZMod 3)) (x : (Fin d → ZMod 3) → Fin N → ZMod 2) : ZMod 2 :=
  ∑ r, ∑ u, ∑ v, if u < v then
    A u v * (x r u * x r v + x (r + δ u) u * x (r + δ v) v) else 0

def C {N d : ℕ} (A : Matrix (Fin N) (Fin N) (ZMod 2))
    (δ : Fin N → (Fin d → ZMod 3)) (t : (Fin d → ZMod 3)) : Matrix (Fin N) (Fin N) (ZMod 2) :=
  fun u v => if (∑ i, t i * δ u i) = (∑ i, t i * δ v i) then 0 else A u v

private abbrev K := QuadraticAlgebra (ZMod 2) 1 1
private lemma f4_frobenius (z : K) :
    star z = z ^ 2 ∧ z ^ 4 = z ∧ (z ^ 2 = z ↔ z.im = 0) := by
  rcases z with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> decide

private def χ {d : ℕ} (t r : (Fin d → ZMod 3)) : K := (AddChar.zmodChar 3 (by decide :
  (QuadraticAlgebra.omega : K) ^ 3 = 1)) (dotProduct t r)
private def ft {d : ℕ} (f : (Fin d → ZMod 3) → K) (t : (Fin d → ZMod 3)) : K := ∑ r, χ t r * f r
private def hat {d : ℕ} (f : (Fin d → ZMod 3) → ZMod 2) (t : (Fin d → ZMod 3)) : K := ft (fun r =>
  (algebraMap (ZMod 2) K) (f r)) t
private def tw {d : ℕ} (f : (Fin d → ZMod 3) → ZMod 2) (p t : (Fin d → ZMod 3)) : K := χ t p * hat f
  t
private abbrev T {d : ℕ} (P : Finset (Fin d → ZMod 3)) := {t : (Fin d → ZMod 3) // t ∈ P}
private abbrev V (N d : ℕ) := (Fin d → ZMod 3) → Fin N → ZMod 2
private abbrev W (N : ℕ) {d : ℕ} (P : Finset (Fin d → ZMod 3)) :=
  (Fin N → ZMod 2) × (T P → ((Fin N → ZMod 2) × (Fin N → ZMod 2)))
private def Rep {d : ℕ} (P : Finset (Fin d → ZMod 3)) : Prop :=
  (0 : (Fin d → ZMod 3)) ∉ P ∧ ∀ t : (Fin d → ZMod 3), t ≠ 0 → (t ∈ P ↔ -t ∉ P)
private def enc {N d : ℕ} (δ : Fin N → (Fin d → ZMod 3)) (P : Finset (Fin d → ZMod 3))
    (x : V N d) : W N P :=
  ((fun u => ∑ r, x r u), fun t =>
    ((fun u => (tw (fun r => x r u) (δ u) t.val).re),
      (fun u => (tw (fun r => x r u) (δ u) t.val).im)))

variable {N d : ℕ}

private lemma phase_table (a : ZMod 3) :
    (AddChar.zmodChar 3 (by decide : (QuadraticAlgebra.omega : K) ^ 3 = 1)) (-a) = star
      ((AddChar.zmodChar 3 (by decide : (QuadraticAlgebra.omega : K) ^ 3 = 1)) a) ∧
      (AddChar.zmodChar 3 (by decide : (QuadraticAlgebra.omega : K) ^ 3 = 1)) a * (AddChar.zmodChar
      3 (by decide : (QuadraticAlgebra.omega : K) ^ 3 = 1)) (-a) = 1 ∧
    (∑ b : ZMod 3, (AddChar.zmodChar 3 (by decide : (QuadraticAlgebra.omega : K) ^ 3 = 1)) (a * b))
      = if a = 0 then 1 else 0 := by
  refine ⟨?_, ?_, ?_⟩
  · change (QuadraticAlgebra.omega : K) ^ (-a).val =
      star ((QuadraticAlgebra.omega : K) ^ a.val)
    fin_cases a <;> decide
  · rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  · change (∑ b : ZMod 3, (QuadraticAlgebra.omega : K) ^ (a * b).val) =
      if a = 0 then 1 else 0
    fin_cases a <;> decide

private lemma chi_laws (t r s : (Fin d → ZMod 3)) : χ t 0 = 1 ∧ χ 0 r = 1 ∧
    χ t r = χ r t ∧ χ t (r + s) = χ t r * χ t s ∧
    χ (t + r) s = χ t s * χ r s ∧ χ (-t) r = star (χ t r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [χ, dotProduct_zero, AddChar.map_zero_eq_one]
  · rw [χ, zero_dotProduct, AddChar.map_zero_eq_one]
  · exact congrArg (AddChar.zmodChar 3 (by decide : (QuadraticAlgebra.omega : K) ^ 3 = 1))
      (dotProduct_comm t r)
  · rw [χ, dotProduct_add]
    exact AddChar.map_add_eq_mul _ _ _
  · rw [χ, add_dotProduct]
    exact AddChar.map_add_eq_mul _ _ _
  · rw [χ, neg_dotProduct]
    exact (phase_table _).1

private lemma chi_product (t r : (Fin d → ZMod 3)) : χ t r = ∏ i : Fin d, (AddChar.zmodChar 3 (by
  decide : (QuadraticAlgebra.omega : K) ^ 3 = 1)) (t i * r i) := by
  change (AddChar.zmodChar 3 (by decide : (QuadraticAlgebra.omega : K) ^ 3 = 1))
    (∑ i, t i * r i) = _
  have h := congrArg Additive.toMul
    (map_sum (AddChar.toAddMonoidHom
      (AddChar.zmodChar 3 (by decide : (QuadraticAlgebra.omega : K) ^ 3 = 1)))
      (fun i : Fin d => t i * r i) Finset.univ)
  rw [toMul_sum] at h
  exact h

private lemma chi_orthogonal (t : (Fin d → ZMod 3)) :
    (∑ r : (Fin d → ZMod 3), χ t r) = if t = 0 then 1 else 0 := by
  classical
  have hp : (∑ r : (Fin d → ZMod 3), χ t r) =
      ∑ r : (Fin d → ZMod 3), ∏ i : Fin d,
        (AddChar.zmodChar 3 (by decide : (QuadraticAlgebra.omega : K) ^ 3 = 1))
          (t i * r i) :=
    Finset.sum_congr rfl (fun r _ => chi_product t r)
  rw [hp]
  rw [← Fintype.prod_sum (fun i (a : ZMod 3) => (AddChar.zmodChar 3 (by decide :
    (QuadraticAlgebra.omega : K) ^ 3 = 1)) (t i * a))]
  have hs : (∏ i : Fin d, ∑ a : ZMod 3,
      (AddChar.zmodChar 3 (by decide : (QuadraticAlgebra.omega : K) ^ 3 = 1)) (t i * a)) =
      ∏ i : Fin d, if t i = 0 then (1 : K) else 0 :=
    Finset.prod_congr rfl (fun i _ => (phase_table (t i)).2.2)
  rw [hs]
  by_cases ht : t = 0
  · subst t
    simp
  · rw [if_neg ht]
    obtain ⟨i, hi⟩ : ∃ i, t i ≠ 0 :=
      not_forall.mp (fun hh => ht (funext hh))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

private lemma fourier_inverse (f : (Fin d → ZMod 3) → K) (r : (Fin d → ZMod 3)) :
    (∑ t : (Fin d → ZMod 3), χ t (-r) * ft f t) = f r := by
  classical
  simp only [ft.eq_1, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ s : (Fin d → ZMod 3), ∑ t : (Fin d → ZMod 3), χ t (-r) * (χ t s * f s)) =
        ∑ s : (Fin d → ZMod 3), (∑ t : (Fin d → ZMod 3), χ (s - r) t) * f s := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      rw [← mul_assoc, ← (chi_laws t (-r) s).2.2.2.1,
        (chi_laws t (-r + s) 0).2.2.1]
      simp only [sub_eq_add_neg, add_comm]
    _ = ∑ s : (Fin d → ZMod 3), (if s = r then 1 else 0) * f s := by
      simp_rw [chi_orthogonal, sub_eq_zero]
    _ = f r := by simp

private lemma fourier_shift_real (f : (Fin d → ZMod 3) → K) (b : (Fin d → ZMod 3) → ZMod 2) (s t :
  (Fin d → ZMod 3)) :
    ft (fun r => f (r + s)) t = χ t (-s) * ft f t ∧
    hat b (-t) = star (hat b t) ∧ hat b 0 = (algebraMap (ZMod 2) K) (∑ r, b r) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · unfold ft
    calc
      (∑ r : (Fin d → ZMod 3), χ t r * f (r + s)) = ∑ r : (Fin d → ZMod 3), χ t (r - s) * f r := by
        exact Fintype.sum_equiv (Equiv.addRight s) _ _ (fun r => by simp)
      _ = χ t (-s) * ∑ r : (Fin d → ZMod 3), χ t r * f r := by
        simp only [sub_eq_add_neg, (chi_laws t _ (-s)).2.2.2.1, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
  · simp only [hat.eq_1, ft, star_sum, star_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [(chi_laws t r 0).2.2.2.2.2]
    have hi : star ((algebraMap (ZMod 2) K) (b r)) = (algebraMap (ZMod 2) K) (b r) := by
      ext <;> simp [QuadraticAlgebra.algebraMap_eq]
    rw [hi]
    exact mul_comm _ _
  · simp only [hat, ft, (chi_laws (0 : (Fin d → ZMod 3)) _ 0).2.1, one_mul, map_sum]

private lemma pair_index (P : Finset (Fin d → ZMod 3)) (h : Rep P) :
    ∃ eqv : (Unit ⊕ (T P × Bool)) ≃ (Fin d → ZMod 3), eqv (Sum.inl ()) = 0 ∧
      (∀ t, eqv (Sum.inr (t, false)) = t.val) ∧
      (∀ t, eqv (Sum.inr (t, true)) = -t.val) := by
  classical
  have hn (t : T P) : t.val ≠ 0 := fun hz => h.1 (hz ▸ t.property)
  have hneg (t : T P) : -t.val ∉ P := (h.2 t.val (hn t)).mp t.property
  let f : (Unit ⊕ (T P × Bool)) → (Fin d → ZMod 3) :=
    Sum.elim (fun _ => 0) (fun z => if z.2 then -z.1.val else z.1.val)
  have hinj : Function.Injective f := by
    intro a b hab
    rcases a with a | ⟨t, a⟩ <;> rcases b with b | ⟨s, b⟩
    · cases a
      cases b
      rfl
    · cases b
      · exact False.elim (hn s hab.symm)
      · exact False.elim (hn s (neg_eq_zero.mp hab.symm))
    · cases a
      · exact False.elim (hn t hab)
      · exact False.elim (hn t (neg_eq_zero.mp hab))
    · cases a <;> cases b <;>
        simp only [f, Sum.elim_inr, Bool.false_eq_true, if_false, if_true] at hab
      · cases Subtype.ext hab
        rfl
      · exact False.elim (hneg s (hab ▸ t.property))
      · exact False.elim (hneg t (hab.symm ▸ s.property))
      · cases Subtype.ext (neg_injective hab)
        rfl
  have hsurj : Function.Surjective f := by
    intro v
    by_cases hv : v = 0
    · exact ⟨Sum.inl (), by simpa [f] using hv.symm⟩
    · by_cases hp : v ∈ P
      · exact ⟨Sum.inr (⟨v, hp⟩, false), rfl⟩
      · have hm : -v ∈ P := by
          by_contra hh
          exact hp ((h.2 v hv).mpr hh)
        exact ⟨Sum.inr (⟨-v, hm⟩, true), by simp [f]⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, rfl, fun _ => rfl, fun _ => rfl⟩

private lemma enc_linear (δ : Fin N → (Fin d → ZMod 3)) (P : Finset (Fin d → ZMod 3)) :
    (∀ x y : V N d, enc δ P (x + y) = enc δ P x + enc δ P y) ∧
    (∀ (c : ZMod 2) (x : V N d), enc δ P (c • x) = c • enc δ P x) := by
  classical
  constructor
  · intro x y
    ext <;> simp [enc.eq_1, tw, hat, ft, mul_add, Finset.sum_add_distrib]
  · intro c x
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · rw [zero_smul, zero_smul]
      ext <;> simp [enc, tw, hat, ft]
    · rw [one_smul, one_smul]

private lemma enc_injective (δ : Fin N → (Fin d → ZMod 3)) (P : Finset (Fin d → ZMod 3)) (h : Rep P)
  :
    Function.Injective (enc δ P) := by
  classical
  intro x y hxy
  have hm (t : T P) (u : Fin N) :
      hat (fun r => x r u) t.val = hat (fun r => y r u) t.val := by
    have hw : tw (fun r => x r u) (δ u) t.val =
        tw (fun r => y r u) (δ u) t.val := by
      apply QuadraticAlgebra.ext
      · exact congrArg (fun w : W N P => (w.2 t).1 u) hxy
      · exact congrArg (fun w : W N P => (w.2 t).2 u) hxy
    have hi : χ t.val (-δ u) * χ t.val (δ u) = 1 := by
      rw [← (chi_laws t.val (-δ u) (δ u)).2.2.2.1, neg_add_cancel,
        (chi_laws t.val 0 0).1]
    have he := congrArg (fun z => χ t.val (-δ u) * z) hw
    simp only [tw] at he
    rw [← mul_assoc, ← mul_assoc] at he
    simpa only [hi, one_mul] using he
  have hall (t : (Fin d → ZMod 3)) (u : Fin N) :
      hat (fun r => x r u) t = hat (fun r => y r u) t := by
    obtain ⟨eqv, hz, hp, hn⟩ := pair_index P h
    obtain ⟨a, rfl⟩ := eqv.surjective t
    rcases a with a | ⟨t, b⟩
    · cases a
      rw [hz, (fourier_shift_real 0 (fun r => x r u) 0 0).2.2,
        (fourier_shift_real 0 (fun r => y r u) 0 0).2.2]
      exact congrArg (algebraMap (ZMod 2) K) (congrArg (fun w : W N P => w.1 u) hxy)
    · cases b
      · rw [hp]
        exact hm t u
      · rw [hn, (fourier_shift_real 0 (fun r => x r u) 0 t.val).2.1,
          (fourier_shift_real 0 (fun r => y r u) 0 t.val).2.1, hm t u]
  ext r u
  apply QuadraticAlgebra.algebraMap_injective (a := (1 : ZMod 2)) (b := (1 : ZMod 2))
  change (algebraMap (ZMod 2) K) (x r u) = (algebraMap (ZMod 2) K) (y r u)
  rw [← fourier_inverse (fun r => (algebraMap (ZMod 2) K) (x r u)) r,
    ← fourier_inverse (fun r => (algebraMap (ZMod 2) K) (y r u)) r]
  apply Finset.sum_congr rfl
  intro t _
  change χ t (-r) * hat (fun r => x r u) t = χ t (-r) * hat (fun r => y r u) t
  rw [hall t u]

private lemma enc_bijective (δ : Fin N → (Fin d → ZMod 3)) (P : Finset (Fin d → ZMod 3)) (h : Rep P)
  :
    Function.Bijective (enc δ P) := by
  classical
  obtain ⟨eqv, _, _, _⟩ := pair_index P h
  have hc : Fintype.card ((Fin d → ZMod 3)) = 1 + Fintype.card (T P) * 2 := by
    simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_unit,
      Fintype.card_bool] using (Fintype.card_congr eqv).symm
  apply (Fintype.bijective_iff_injective_and_card (enc δ P)).mpr
  refine ⟨enc_injective δ P h, ?_⟩
  simp only [V, W, Fintype.card_fun, Fintype.card_prod, hc]
  rw [pow_add, pow_one, Nat.mul_comm (Fintype.card (T P)) 2, pow_mul, pow_two]

private lemma phase_cut (a b : ZMod 3) :
    (AddChar.zmodChar 3 (by decide : (QuadraticAlgebra.omega : K) ^ 3 = 1)) (-a) * (if a = b then (0
      : K) else 1) * (AddChar.zmodChar 3 (by decide : (QuadraticAlgebra.omega : K) ^ 3 = 1)) b = 1 +
      (AddChar.zmodChar 3 (by decide : (QuadraticAlgebra.omega : K) ^ 3 = 1)) (a - b) := by
  change (QuadraticAlgebra.omega : K) ^ (-a).val * (if a = b then 0 else 1) *
    (QuadraticAlgebra.omega : K) ^ b.val =
      1 + (QuadraticAlgebra.omega : K) ^ (a - b).val
  fin_cases a <;> fin_cases b <;> decide

private lemma trace_cross (z w : K) :
    star z * w + star w * z = (algebraMap (ZMod 2) K) (z.re * w.im + w.re * z.im) := by
  rw [(f4_frobenius z).1, (f4_frobenius w).1]
  rcases z with ⟨a, b⟩
  rcases w with ⟨c, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;> decide

private lemma edge_pair_sum (P : Finset (Fin d → ZMod 3)) (h : Rep P)
    (f g : (Fin d → ZMod 3) → ZMod 2) (p q : (Fin d → ZMod 3)) :
    (algebraMap (ZMod 2) K) (∑ r, (f r * g r + f (r + p) * g (r + q))) =
      ∑ t : T P, ((1 + χ t.val (p - q)) * star (hat f t.val) * hat g t.val +
        (1 + χ t.val (q - p)) * star (hat g t.val) * hat f t.val) := by
  classical
  have hflip (t r : (Fin d → ZMod 3)) : χ (-t) r = χ t (-r) := by
    rw [χ, χ, neg_dotProduct, dotProduct_neg]
  have parseval (a b : (Fin d → ZMod 3) → K) :
      (∑ r, a r * b r) = ∑ t, ft a (-t) * ft b t := by
    calc
      (∑ r, a r * b r) = ∑ r, a r * (∑ t, χ t (-r) * ft b t) := by
        simp_rw [fourier_inverse]
      _ = ∑ t, ft a (-t) * ft b t := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        simp only [ft, Finset.sum_mul, hflip]
        apply Finset.sum_congr rfl
        intro r _
        ring
  have shifted (f g : (Fin d → ZMod 3) → ZMod 2) (p q : (Fin d → ZMod 3)) :
      (algebraMap (ZMod 2) K) (∑ r, f (r + p) * g (r + q)) =
        ∑ t, χ t (p - q) * star (hat f t) * hat g t := by
    rw [map_sum]
    simp only [map_mul]
    rw [parseval]
    apply Finset.sum_congr rfl
    intro t _
    rw [(fourier_shift_real (fun r => (algebraMap (ZMod 2) K) (f r)) f p (-t)).1,
      (fourier_shift_real (fun r => (algebraMap (ZMod 2) K) (g r)) g q t).1]
    change χ (-t) (-p) * hat f (-t) * (χ t (-q) * hat g t) = _
    rw [hflip, neg_neg, (fourier_shift_real 0 f 0 t).2.1]
    simp only [sub_eq_add_neg, (chi_laws t p (-q)).2.2.2.1]
    ring
  let S : (Fin d → ZMod 3) → K := fun t => (1 + χ t (p - q)) * star (hat f t) * hat g t
  have hpair : (∑ t : (Fin d → ZMod 3), S t) =
      S 0 + ∑ t : T P, (S t.val + S (-t.val)) := by
    obtain ⟨eqv, hz, hp, hn⟩ := pair_index P h
    rw [← eqv.sum_comp S, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_unique, hz, Fintype.sum_bool, hp, hn]
    exact congrArg (fun z => S 0 + z)
      (Finset.sum_congr rfl (fun t _ => add_comm (S (-t.val)) (S t.val)))
  have hzero : S 0 = 0 := by
    dsimp [S]
    rw [(chi_laws (0 : (Fin d → ZMod 3)) (p - q) 0).2.1, (by decide : (1 : K) + 1 = 0)]
    simp
  calc
    (algebraMap (ZMod 2) K) (∑ r, (f r * g r + f (r + p) * g (r + q))) =
        (algebraMap (ZMod 2) K) (∑ r, f r * g r) + (algebraMap (ZMod 2) K) (∑ r, f (r + p) * g (r +
          q)) := by
      rw [Finset.sum_add_distrib, map_add]
    _ = ∑ t : (Fin d → ZMod 3), S t := by
      have hu := shifted f g 0 0
      simp only [add_zero, sub_self, (chi_laws _ 0 0).1, one_mul] at hu
      rw [hu, shifted f g p q, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      dsimp [S]
      ring
    _ = ∑ t : T P, (S t.val + S (-t.val)) := by rw [hpair, hzero, zero_add]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      dsimp [S]
      rw [hflip, neg_sub, (fourier_shift_real 0 f 0 t.val).2.1,
        (fourier_shift_real 0 g 0 t.val).2.1, star_star]
      ring

private lemma edge_cut_sum (P : Finset (Fin d → ZMod 3)) (h : Rep P)
    (f g : (Fin d → ZMod 3) → ZMod 2) (p q : (Fin d → ZMod 3)) :
    (∑ r, (f r * g r + f (r + p) * g (r + q))) =
      ∑ t : T P, (if (∑ i, t.val i * p i) = (∑ i, t.val i * q i) then 0 else
        (tw f p t.val).re * (tw g q t.val).im +
          (tw g q t.val).re * (tw f p t.val).im) := by
  classical
  apply QuadraticAlgebra.algebraMap_injective (a := (1 : ZMod 2)) (b := (1 : ZMod 2))
  change (algebraMap (ZMod 2) K) _ = (algebraMap (ZMod 2) K) _
  rw [edge_pair_sum P h f g p q, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  have hs (p q : (Fin d → ZMod 3)) : χ t.val (p - q) =
      (AddChar.zmodChar 3 (by decide : (QuadraticAlgebra.omega : K) ^ 3 = 1)) ((∑ i, t.val i * p i)
        - (∑ i, t.val i * q i)) := by
    change (AddChar.zmodChar 3 (by decide : (QuadraticAlgebra.omega : K) ^ 3 = 1)) (dotProduct t.val
      (p - q)) = (AddChar.zmodChar 3 (by decide : (QuadraticAlgebra.omega : K) ^ 3 = 1)) (dotProduct
      t.val p - dotProduct t.val q)
    rw [dotProduct_sub]
  have hb (p : (Fin d → ZMod 3)) : star (χ t.val p) = (AddChar.zmodChar 3 (by decide :
    (QuadraticAlgebra.omega : K) ^ 3 = 1)) (-(∑ i, t.val i * p i)) :=
    (phase_table _).1.symm
  calc
    (1 + χ t.val (p - q)) * star (hat f t.val) * hat g t.val +
        (1 + χ t.val (q - p)) * star (hat g t.val) * hat f t.val =
      (if (∑ i, t.val i * p i) = (∑ i, t.val i * q i) then (0 : K) else 1) *
        (star (tw f p t.val) * tw g q t.val +
          star (tw g q t.val) * tw f p t.val) := by
      rw [hs, hs, ← phase_cut, ← phase_cut]
      rw [tw, tw, star_mul, star_mul, hb, hb]
      dsimp only [χ, dotProduct]
      by_cases he : (∑ i, t.val i * p i) = (∑ i, t.val i * q i)
      · rw [he, if_pos rfl]
        ring
      · rw [if_neg he, if_neg (Ne.symm he)]
        ring
    _ = _ := by
      rw [trace_cross]
      by_cases he : (∑ i, t.val i * p i) = (∑ i, t.val i * q i) <;> simp [he]

private lemma triangle_bilinear {R : Type*} [CommSemiring R]
    (M : Matrix (Fin N) (Fin N) R) (hs : ∀ u v, M u v = M v u)
    (hd : ∀ u, M u u = 0) (a b : Fin N → R) :
    (∑ u, ∑ v, if u < v then M u v * (a u * b v + a v * b u) else 0) =
      ∑ u, ∑ v, a u * M u v * b v := by
  classical
  have hterm (u v : Fin N) : a u * M u v * b v =
      (if u < v then M u v * (a u * b v) else 0) +
        (if v < u then M u v * (a u * b v) else 0) := by
    rcases lt_trichotomy u v with huv | he | hvu
    · rw [if_pos huv, if_neg (not_lt_of_ge (le_of_lt huv))]
      ring
    · subst v
      simp [hd]
    · rw [if_neg (not_lt_of_ge (le_of_lt hvu)), if_pos hvu]
      ring
  have hlower : (∑ u, ∑ v, if v < u then M u v * (a u * b v) else 0) =
      ∑ u, ∑ v, if u < v then M u v * (a v * b u) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [hs v u]
  symm
  calc
    (∑ u, ∑ v, a u * M u v * b v) =
        (∑ u, ∑ v, if u < v then M u v * (a u * b v) else 0) +
          (∑ u, ∑ v, if v < u then M u v * (a u * b v) else 0) := by
      simp_rw [hterm, Finset.sum_add_distrib]
    _ = _ := by
      rw [hlower, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      by_cases huv : u < v
      · simp only [if_pos huv]
        ring
      · simp [huv]

private lemma enc_quadratic (A : Matrix (Fin N) (Fin N) (ZMod 2))
    (hA : ∀ u v, A u v = A v u) (δ : Fin N → (Fin d → ZMod 3))
    (P : Finset (Fin d → ZMod 3)) (h : Rep P) (x : V N d) :
    F A δ x = ∑ t : T P, ∑ u, ∑ v,
      ((enc δ P x).2 t).1 u * C A δ t.val u v * ((enc δ P x).2 t).2 v := by
  classical
  let a : T P → Fin N → ZMod 2 := fun t => ((enc δ P x).2 t).1
  let b : T P → Fin N → ZMod 2 := fun t => ((enc δ P x).2 t).2
  change F A δ x = ∑ t : T P, ∑ u, ∑ v, a t u * C A δ t.val u v * b t v
  have hedge (u v : Fin N) :
      A u v * (∑ r, (x r u * x r v + x (r + δ u) u * x (r + δ v) v)) =
        ∑ t : T P, C A δ t.val u v * (a t u * b t v + a t v * b t u) := by
    rw [edge_cut_sum P h (fun r => x r u) (fun r => x r v) (δ u) (δ v),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    dsimp [a, b, enc, C]
    by_cases he : (∑ i, t.val i * δ u i) = (∑ i, t.val i * δ v i)
    · simp [he]
    · simp only [if_neg he]
  calc
    F A δ x = ∑ u, ∑ v, if u < v then
        A u v * (∑ r, (x r u * x r v + x (r + δ u) u * x (r + δ v) v))
          else 0 := by
      unfold F
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      by_cases huv : u < v
      · simp only [if_pos huv, Finset.mul_sum]
      · simp [huv]
    _ = ∑ u, ∑ v, ∑ t : T P, if u < v then
        C A δ t.val u v * (a t u * b t v + a t v * b t u) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      by_cases huv : u < v
      · simp only [if_pos huv]
        exact hedge u v
      · simp [huv]
    _ = ∑ u, ∑ t : T P, ∑ v, if u < v then
        C A δ t.val u v * (a t u * b t v + a t v * b t u) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    _ = ∑ t : T P, ∑ u, ∑ v, if u < v then
        C A δ t.val u v * (a t u * b t v + a t v * b t u) else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      apply triangle_bilinear (C A δ t.val) ?_ ?_ (a t) (b t)
      · intro u v
        dsimp [C]
        by_cases he : (∑ i, t.val i * δ u i) = (∑ i, t.val i * δ v i)
        · rw [if_pos he, if_pos he.symm]
        · rw [if_neg he, if_neg (Ne.symm he)]
          exact hA u v
      · intro u
        simp [C.eq_1]

theorem ternary_translation_quadratic_normal_form
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (hA : ∀ u v, A u v = A v u)
    (δ : Fin N → (Fin d → ZMod 3)) (P : Finset (Fin d → ZMod 3))
    (h0 : (0 : (Fin d → ZMod 3)) ∉ P)
    (hP : ∀ t : (Fin d → ZMod 3), t ≠ 0 → (t ∈ P ↔ -t ∉ P)) :
    ∃ E : ((Fin d → ZMod 3) → Fin N → ZMod 2) ≃ₗ[ZMod 2]
        ((Fin N → ZMod 2) ×
          ({t : (Fin d → ZMod 3) // t ∈ P} → ((Fin N → ZMod 2) × (Fin N → ZMod 2)))),
      ∀ x, F A δ x = ∑ t : {t : (Fin d → ZMod 3) // t ∈ P}, ∑ u : Fin N, ∑ v : Fin N,
        ((E x).2 t).1 u * C A δ t.val u v * ((E x).2 t).2 v := by
  classical
  let L : V N d →ₗ[ZMod 2] W N P :=
    { toFun := enc δ P
      map_add' := (enc_linear δ P).1
      map_smul' := (enc_linear δ P).2 }
  let E : V N d ≃ₗ[ZMod 2] W N P :=
    { L, Equiv.ofBijective L (enc_bijective δ P ⟨h0, hP⟩) with }
  exact ⟨E, enc_quadratic A hA δ P ⟨h0, hP⟩⟩

end

end D5.S3.QuadraticForms.TernaryTranslationQuadraticNormalForm
