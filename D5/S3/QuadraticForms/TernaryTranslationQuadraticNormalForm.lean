/- GID: D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ternary translation quadratic forms split into binary bilinear blocks. -/

/-
proof_shape (definitions): F, C (`B` and `G` are local notations for `ZMod 2` and
  `Fin d → ZMod 3`); private K, χ, ft, hat, tw, T, V, W, Rep, enc;
  `ι` and `ζ` are local notations for `algebraMap B K` and Mathlib's
  `AddChar.zmodChar 3 f4_basics.2.2.2.1`; χ composes this character with
  Mathlib's dotProduct.
proof_shape (theorems, same-delivery helpers inlined): ternary_translation_quadratic_normal_form
  is content. Its escape witness is enc_injective: the binary replica vector x is recovered
  from its constant mode and from one twisted F₄-Fourier mode per pair {t, -t}, t ≠ 0, so the
  encoding enc is injective. No Mathlib or repository declaration supplies this encoding or
  its inverse; the equivalence E of the conclusion is built from it through enc_bijective
  (injectivity plus equal cardinality) and Equiv.ofBijective. enc_bijective is content for
  the same reason. Every other private theorem is bind-only and is used on the proof path of
  the main theorem (CLAUDE.md §3.2, consumed helpers): f4_basics, f4_frobenius, phase_table,
  chi_laws, chi_product, chi_orthogonal, fourier_inverse, fourier_shift_real, pair_index,
  enc_linear, phase_cut, trace_cross, edge_pair_sum, edge_cut_sum, triangle_bilinear,
  enc_quadratic.
escape_witness: enc_injective.
admission_basis: escape-witness (research line #13575, route step 2).
Direct frozen dependencies: none; Mathlib only.
-/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Data.Matrix.Mul
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

open scoped BigOperators

namespace D5.S3.QuadraticForms.TernaryTranslationQuadraticNormalForm

noncomputable section

/-- Local notation for the binary field. -/
local notation "B" => ZMod 2
/-- Local notation for the ternary group of rank `d`. -/
local notation "G" d:max => Fin d → ZMod 3

def F {N d : ℕ} (A : Matrix (Fin N) (Fin N) B)
    (δ : Fin N → G d) (x : G d → Fin N → B) : B :=
  ∑ r, ∑ u, ∑ v, if u < v then
    A u v * (x r u * x r v + x (r + δ u) u * x (r + δ v) v) else 0

def C {N d : ℕ} (A : Matrix (Fin N) (Fin N) B)
    (δ : Fin N → G d) (t : G d) : Matrix (Fin N) (Fin N) B :=
  fun u v => if (∑ i, t i * δ u i) = (∑ i, t i * δ v i) then 0 else A u v

private abbrev K := QuadraticAlgebra B 1 1
/-- Mathlib's root `QuadraticAlgebra.omega` of `K`. -/
local notation "ω" => (QuadraticAlgebra.omega : K)
local notation "ι" => algebraMap B K
private lemma f4_basics :
    (∀ z : K, ι z.re + ω * ι z.im = z) ∧
    (∃ b : Module.Basis (Fin 2) B K, b 0 = 1 ∧ b 1 = ω) ∧
    ω ^ 2 + ω + 1 = 0 ∧ ω ^ 3 = 1 ∧ (3 : K) = 1 ∧ (∀ z : K, z + z = 0) := by
  refine ⟨?_, ⟨QuadraticAlgebra.basis 1 1, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro z
    simpa only [Algebra.smul_def, mul_comm] using
      (QuadraticAlgebra.mk_eq_add_smul_omega (a := (1 : B)) (b := (1 : B))
        z.re z.im).symm
  · simp [QuadraticAlgebra.basis, Module.Basis.coe_ofEquivFun]
    rfl
  · simp [QuadraticAlgebra.basis, Module.Basis.coe_ofEquivFun, QuadraticAlgebra.omega]
  · decide
  · decide
  · decide
  · rintro ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> decide

private lemma f4_frobenius (z : K) :
    star z = z ^ 2 ∧ z ^ 4 = z ∧ (z ^ 2 = z ↔ z.im = 0) := by
  rcases z with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> decide

local notation "ζ" =>
  AddChar.zmodChar 3 (And.left (And.right (And.right (And.right f4_basics))))
private def χ {d : ℕ} (t r : G d) : K := ζ (dotProduct t r)
private def ft {d : ℕ} (f : G d → K) (t : G d) : K := ∑ r, χ t r * f r
private def hat {d : ℕ} (f : G d → B) (t : G d) : K := ft (fun r => ι (f r)) t
private def tw {d : ℕ} (f : G d → B) (p t : G d) : K := χ t p * hat f t
private abbrev T {d : ℕ} (P : Finset (G d)) := {t : G d // t ∈ P}
private abbrev V (N d : ℕ) := G d → Fin N → B
private abbrev W (N : ℕ) {d : ℕ} (P : Finset (G d)) :=
  (Fin N → B) × (T P → ((Fin N → B) × (Fin N → B)))
private def Rep {d : ℕ} (P : Finset (G d)) : Prop :=
  (0 : G d) ∉ P ∧ ∀ t : G d, t ≠ 0 → (t ∈ P ↔ -t ∉ P)
private def enc {N d : ℕ} (δ : Fin N → G d) (P : Finset (G d))
    (x : V N d) : W N P :=
  ((fun u => ∑ r, x r u), fun t =>
    ((fun u => (tw (fun r => x r u) (δ u) t.val).re),
      (fun u => (tw (fun r => x r u) (δ u) t.val).im)))

variable {N d : ℕ}

private lemma phase_table : ζ 0 = 1 ∧
    (∀ a b : ZMod 3, ζ (a + b) = ζ a * ζ b) ∧
    (∀ a : ZMod 3, ζ (-a) = star (ζ a)) ∧
    (∀ a : ZMod 3, ζ a * ζ (-a) = 1) ∧
    (∀ a : ZMod 3, (∑ b : ZMod 3, ζ (a * b)) = if a = 0 then 1 else 0) := by
  refine ⟨AddChar.map_zero_eq_one ζ, AddChar.map_add_eq_mul ζ, ?_, ?_, ?_⟩
  · intro a
    simp only [AddChar.zmodChar_apply]
    fin_cases a <;> decide
  · intro a
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  · intro a
    simp only [AddChar.zmodChar_apply]
    fin_cases a <;> decide

private lemma chi_laws (t r s : G d) : χ t 0 = 1 ∧ χ 0 r = 1 ∧
    χ t r = χ r t ∧ χ t (r + s) = χ t r * χ t s ∧
    χ (t + r) s = χ t s * χ r s ∧ χ (-t) r = star (χ t r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [χ, phase_table.1]
  · simp [χ, phase_table.1]
  · exact congrArg ζ (dotProduct_comm t r)
  · simp only [χ, dotProduct_add]
    exact phase_table.2.1 _ _
  · simp only [χ, add_dotProduct]
    exact phase_table.2.1 _ _
  · simp only [χ, neg_dotProduct]
    exact phase_table.2.2.1 _

private lemma chi_product (t r : G d) : χ t r = ∏ i : Fin d, ζ (t i * r i) := by
  simpa only [χ, dotProduct, AddChar.toAddMonoidHom_apply, toMul_sum,
    toMul_ofMul] using
    congrArg Additive.toMul (map_sum (AddChar.toAddMonoidHom ζ) (fun i : Fin d => t i * r i)
      Finset.univ)

private lemma chi_orthogonal (t : G d) :
    (∑ r : G d, χ t r) = if t = 0 then 1 else 0 := by
  classical
  simp_rw [chi_product]
  rw [← Fintype.prod_sum (fun i (a : ZMod 3) => ζ (t i * a))]
  simp_rw [phase_table.2.2.2.2]
  by_cases ht : t = 0
  · subst t
    simp
  · rw [if_neg ht]
    obtain ⟨i, hi⟩ : ∃ i, t i ≠ 0 :=
      not_forall.mp (fun hh => ht (funext hh))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

private lemma fourier_inverse (f : G d → K) (r : G d) :
    (∑ t : G d, χ t (-r) * ft f t) = f r := by
  classical
  simp only [ft, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ s : G d, ∑ t : G d, χ t (-r) * (χ t s * f s)) =
        ∑ s : G d, (∑ t : G d, χ (s - r) t) * f s := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      rw [← mul_assoc, ← (chi_laws t (-r) s).2.2.2.1,
        (chi_laws t (-r + s) 0).2.2.1]
      simp only [sub_eq_add_neg, add_comm]
    _ = ∑ s : G d, (if s = r then 1 else 0) * f s := by
      simp_rw [chi_orthogonal, sub_eq_zero]
    _ = f r := by simp

private lemma fourier_shift_real (f : G d → K) (b : G d → B) (s t : G d) :
    ft (fun r => f (r + s)) t = χ t (-s) * ft f t ∧
    hat b (-t) = star (hat b t) ∧ hat b 0 = ι (∑ r, b r) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · unfold ft
    calc
      (∑ r : G d, χ t r * f (r + s)) = ∑ r : G d, χ t (r - s) * f r := by
        exact Fintype.sum_equiv (Equiv.addRight s) _ _ (fun r => by simp)
      _ = χ t (-s) * ∑ r : G d, χ t r * f r := by
        simp only [sub_eq_add_neg, (chi_laws t _ (-s)).2.2.2.1, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
  · simp only [hat, ft, star_sum, star_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [(chi_laws t r 0).2.2.2.2.2]
    have hi : star (ι (b r)) = ι (b r) := by
      ext <;> simp [QuadraticAlgebra.algebraMap_eq]
    rw [hi]
    exact mul_comm _ _
  · simp only [hat, ft, (chi_laws (0 : G d) _ 0).2.1, one_mul, map_sum]

private lemma pair_index (P : Finset (G d)) (h : Rep P) :
    ∃ eqv : (Unit ⊕ (T P × Bool)) ≃ G d, eqv (Sum.inl ()) = 0 ∧
      (∀ t, eqv (Sum.inr (t, false)) = t.val) ∧
      (∀ t, eqv (Sum.inr (t, true)) = -t.val) := by
  classical
  have hn (t : T P) : t.val ≠ 0 := fun hz => h.1 (hz ▸ t.property)
  have hneg (t : T P) : -t.val ∉ P := (h.2 t.val (hn t)).mp t.property
  let f : (Unit ⊕ (T P × Bool)) → G d :=
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

private lemma enc_linear (δ : Fin N → G d) (P : Finset (G d)) :
    (∀ x y : V N d, enc δ P (x + y) = enc δ P x + enc δ P y) ∧
    (∀ (c : B) (x : V N d), enc δ P (c • x) = c • enc δ P x) := by
  classical
  constructor
  · intro x y
    ext <;> simp [enc, tw, hat, ft, mul_add, Finset.sum_add_distrib]
  · intro c x
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · rw [zero_smul, zero_smul]
      ext <;> simp [enc, tw, hat, ft]
    · rw [one_smul, one_smul]

private lemma enc_injective (δ : Fin N → G d) (P : Finset (G d)) (h : Rep P) :
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
    simpa only [tw, ← mul_assoc, hi, one_mul] using he
  have hall (t : G d) (u : Fin N) :
      hat (fun r => x r u) t = hat (fun r => y r u) t := by
    obtain ⟨eqv, hz, hp, hn⟩ := pair_index P h
    obtain ⟨a, rfl⟩ := eqv.surjective t
    rcases a with a | ⟨t, b⟩
    · cases a
      rw [hz, (fourier_shift_real 0 (fun r => x r u) 0 0).2.2,
        (fourier_shift_real 0 (fun r => y r u) 0 0).2.2]
      exact congrArg ι (congrArg (fun w : W N P => w.1 u) hxy)
    · cases b
      · rw [hp]
        exact hm t u
      · rw [hn, (fourier_shift_real 0 (fun r => x r u) 0 t.val).2.1,
          (fourier_shift_real 0 (fun r => y r u) 0 t.val).2.1, hm t u]
  ext r u
  apply QuadraticAlgebra.algebraMap_injective (a := (1 : B)) (b := (1 : B))
  change ι (x r u) = ι (y r u)
  rw [← fourier_inverse (fun r => ι (x r u)) r,
    ← fourier_inverse (fun r => ι (y r u)) r]
  apply Finset.sum_congr rfl
  intro t _
  change χ t (-r) * hat (fun r => x r u) t = χ t (-r) * hat (fun r => y r u) t
  rw [hall t u]

private lemma enc_bijective (δ : Fin N → G d) (P : Finset (G d)) (h : Rep P) :
    Function.Bijective (enc δ P) := by
  classical
  obtain ⟨eqv, _, _, _⟩ := pair_index P h
  have hc : Fintype.card (G d) = 1 + Fintype.card (T P) * 2 := by
    simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_unit,
      Fintype.card_bool] using (Fintype.card_congr eqv).symm
  apply (Fintype.bijective_iff_injective_and_card (enc δ P)).mpr
  refine ⟨enc_injective δ P h, ?_⟩
  simp only [V, W, Fintype.card_fun, Fintype.card_prod, hc]
  rw [pow_add, pow_one, Nat.mul_comm (Fintype.card (T P)) 2, pow_mul, pow_two]

private lemma phase_cut (a b : ZMod 3) :
    ζ (-a) * (if a = b then (0 : K) else 1) * ζ b = 1 + ζ (a - b) := by
  simp only [AddChar.zmodChar_apply]
  fin_cases a <;> fin_cases b <;> decide

private lemma trace_cross (z w : K) :
    star z * w + star w * z = ι (z.re * w.im + w.re * z.im) := by
  rw [(f4_frobenius z).1, (f4_frobenius w).1]
  rcases z with ⟨a, b⟩
  rcases w with ⟨c, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;> decide

private lemma edge_pair_sum (P : Finset (G d)) (h : Rep P)
    (f g : G d → B) (p q : G d) :
    ι (∑ r, (f r * g r + f (r + p) * g (r + q))) =
      ∑ t : T P, ((1 + χ t.val (p - q)) * star (hat f t.val) * hat g t.val +
        (1 + χ t.val (q - p)) * star (hat g t.val) * hat f t.val) := by
  classical
  have hflip (t r : G d) : χ (-t) r = χ t (-r) := by
    simp only [χ, neg_dotProduct, dotProduct_neg]
  have parseval (a b : G d → K) :
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
  have shifted (f g : G d → B) (p q : G d) :
      ι (∑ r, f (r + p) * g (r + q)) =
        ∑ t, χ t (p - q) * star (hat f t) * hat g t := by
    rw [map_sum]
    simp only [map_mul]
    rw [parseval]
    apply Finset.sum_congr rfl
    intro t _
    rw [(fourier_shift_real (fun r => ι (f r)) f p (-t)).1,
      (fourier_shift_real (fun r => ι (g r)) g q t).1]
    change χ (-t) (-p) * hat f (-t) * (χ t (-q) * hat g t) = _
    rw [hflip, neg_neg, (fourier_shift_real 0 f 0 t).2.1]
    simp only [sub_eq_add_neg, (chi_laws t p (-q)).2.2.2.1]
    ring
  let S : G d → K := fun t => (1 + χ t (p - q)) * star (hat f t) * hat g t
  have hpair : (∑ t : G d, S t) =
      S 0 + ∑ t : T P, (S t.val + S (-t.val)) := by
    obtain ⟨eqv, hz, hp, hn⟩ := pair_index P h
    rw [← eqv.sum_comp S, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_unique, hz, Fintype.sum_bool, hp, hn]
    exact congrArg (fun z => S 0 + z)
      (Finset.sum_congr rfl (fun t _ => add_comm (S (-t.val)) (S t.val)))
  have hzero : S 0 = 0 := by
    dsimp [S]
    rw [(chi_laws (0 : G d) (p - q) 0).2.1, f4_basics.2.2.2.2.2 1]
    simp
  calc
    ι (∑ r, (f r * g r + f (r + p) * g (r + q))) =
        ι (∑ r, f r * g r) + ι (∑ r, f (r + p) * g (r + q)) := by
      rw [Finset.sum_add_distrib, map_add]
    _ = ∑ t : G d, S t := by
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

private lemma edge_cut_sum (P : Finset (G d)) (h : Rep P)
    (f g : G d → B) (p q : G d) :
    (∑ r, (f r * g r + f (r + p) * g (r + q))) =
      ∑ t : T P, (if (∑ i, t.val i * p i) = (∑ i, t.val i * q i) then 0 else
        (tw f p t.val).re * (tw g q t.val).im +
          (tw g q t.val).re * (tw f p t.val).im) := by
  classical
  apply QuadraticAlgebra.algebraMap_injective (a := (1 : B)) (b := (1 : B))
  change ι _ = ι _
  rw [edge_pair_sum P h f g p q, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  have hs (p q : G d) : χ t.val (p - q) =
      ζ ((∑ i, t.val i * p i) - (∑ i, t.val i * q i)) := by
    change ζ (dotProduct t.val (p - q)) = ζ (dotProduct t.val p - dotProduct t.val q)
    rw [dotProduct_sub]
  have hb (p : G d) : star (χ t.val p) = ζ (-(∑ i, t.val i * p i)) :=
    (phase_table.2.2.1 _).symm
  calc
    (1 + χ t.val (p - q)) * star (hat f t.val) * hat g t.val +
        (1 + χ t.val (q - p)) * star (hat g t.val) * hat f t.val =
      (if (∑ i, t.val i * p i) = (∑ i, t.val i * q i) then (0 : K) else 1) *
        (star (tw f p t.val) * tw g q t.val +
          star (tw g q t.val) * tw f p t.val) := by
      rw [hs, hs, ← phase_cut, ← phase_cut]
      simp only [tw, star_mul, hb]
      simp only [χ, dotProduct]
      by_cases he : (∑ i, t.val i * p i) = (∑ i, t.val i * q i)
      · simp [he]
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

private lemma enc_quadratic (A : Matrix (Fin N) (Fin N) B)
    (hA : ∀ u v, A u v = A v u) (δ : Fin N → G d)
    (P : Finset (G d)) (h : Rep P) (x : V N d) :
    F A δ x = ∑ t : T P, ∑ u, ∑ v,
      ((enc δ P x).2 t).1 u * C A δ t.val u v * ((enc δ P x).2 t).2 v := by
  classical
  let a : T P → Fin N → B := fun t => ((enc δ P x).2 t).1
  let b : T P → Fin N → B := fun t => ((enc δ P x).2 t).2
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
        simp [C]

theorem ternary_translation_quadratic_normal_form
    (A : Matrix (Fin N) (Fin N) B) (hA : ∀ u v, A u v = A v u)
    (δ : Fin N → G d) (P : Finset (G d))
    (h0 : (0 : G d) ∉ P)
    (hP : ∀ t : G d, t ≠ 0 → (t ∈ P ↔ -t ∉ P)) :
    ∃ E : (G d → Fin N → B) ≃ₗ[B]
        ((Fin N → B) ×
          ({t : G d // t ∈ P} → ((Fin N → B) × (Fin N → B)))),
      ∀ x, F A δ x = ∑ t : {t : G d // t ∈ P}, ∑ u : Fin N, ∑ v : Fin N,
        ((E x).2 t).1 u * C A δ t.val u v * ((E x).2 t).2 v := by
  classical
  let L : V N d →ₗ[B] W N P :=
    { toFun := enc δ P
      map_add' := (enc_linear δ P).1
      map_smul' := (enc_linear δ P).2 }
  let E : V N d ≃ₗ[B] W N P :=
    { L, Equiv.ofBijective L (enc_bijective δ P ⟨h0, hP⟩) with }
  exact ⟨E, enc_quadratic A hA δ P ⟨h0, hP⟩⟩

end

end D5.S3.QuadraticForms.TernaryTranslationQuadraticNormalForm
