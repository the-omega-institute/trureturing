/- GID: D5/S3/Quantum/Algebra/QuantitativeWordOrthonormalExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/QuantitativeWordOrthonormalExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Threshold orthonormal extension with simultaneous short-word coefficient control. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finsupp.SMul
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace
open Finset

namespace D5.S3.Quantum.Algebra.QuantitativeWordOrthonormalExtension

/-- Every finite contraction family admits a threshold-stable orthonormal extension of
an arbitrary orthonormal seed, with a common quantitative chronological-word certificate. -/
theorem quantitative_word_orthonormal_extension
    (D r M : ℕ) (hr : 2 ≤ r) (hrD : r ≤ D) (_hM : M ≤ D ^ 2)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (A : Fin M → Module.End ℂ (EuclideanSpace ℂ (Fin D)))
    (hA : ∀ a x, ‖A a x‖ ≤ ‖x‖)
    (η : Fin r → EuclideanSpace ℂ (Fin D)) (hη : Orthonormal ℂ η) :
    ∃ (m : ℕ) (hrm : r ≤ m), m ≤ D ∧
      ∃ e : Fin m → EuclideanSpace ℂ (Fin D),
        Orthonormal ℂ e ∧ (∀ b, e (Fin.castLE hrm b) = η b) ∧
        (∀ a j, ‖A a (e j) -
          (Submodule.span ℂ (Set.range e)).starProjection (A a (e j))‖ ≤ δ) ∧
        ∃ c : Fin m → (List (Fin M) × Fin r →₀ ℂ),
          (∀ j, ∀ p ∈ (c j).support, p.1.length ≤ m - r) ∧
          (∀ j, e j = (c j).sum fun p z => z • (p.1.reverse.map A).prod (η p.2)) ∧
          (∀ j, (c j).sum (fun _ z => ‖z‖) ≤ ((D : ℝ) / δ) ^ (m - r)) := by
  classical
  let H := EuclideanSpace ℂ (Fin D)
  let word : List (Fin M) × Fin r → H := fun p => (p.1.reverse.map A).prod (η p.2)
  let ev : (List (Fin M) × Fin r →₀ ℂ) →ₗ[ℂ] H := Finsupp.linearCombination ℂ word
  let mass : (List (Fin M) × Fin r →₀ ℂ) → ℝ := fun c => c.sum fun _ z => ‖z‖
  let short : ℕ → (List (Fin M) × Fin r →₀ ℂ) → Prop := fun k c => ∀ p, k < p.1.length → c p = 0
  let proj := fun {n : ℕ} (e : Fin n → H) (x : H) =>
    ∑ i, inner ℂ (e i) x • e i
  have mass_zero : mass 0 = 0 := by simp [mass]
  have mass_nonneg (c : (List (Fin M) × Fin r →₀ ℂ)) : 0 ≤ mass c := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have mass_add (c d : (List (Fin M) × Fin r →₀ ℂ)) : mass (c + d) ≤ mass c + mass d := by
    dsimp [mass]
    rw [Finsupp.sum_of_support_subset _ Finsupp.support_add _ (by simp),
      Finsupp.sum_of_support_subset c Finset.subset_union_left _ (by simp),
      Finsupp.sum_of_support_subset d Finset.subset_union_right _ (by simp),
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun p _ => norm_add_le (c p) (d p)
  have mass_smul (z : ℂ) (c : (List (Fin M) × Fin r →₀ ℂ)) : mass (z • c) = ‖z‖ * mass c := by
    dsimp only [mass]
    rw [Finsupp.sum_smul_index (by simp)]
    simp only [norm_mul, Finsupp.sum, Finset.mul_sum]
  have mass_sum {ι : Type} (s : Finset ι) (c : ι → (List (Fin M) × Fin r →₀ ℂ)) :
      mass (∑ i ∈ s, c i) ≤ ∑ i ∈ s, mass (c i) :=
    Finset.le_sum_of_subadditive mass mass_zero.le mass_add s c
  have short_mono {k l : ℕ} (hkl : k ≤ l) {c : (List (Fin M) × Fin r →₀ ℂ)} (hc : short k c) : short l c := by
    intro p hp
    exact hc p (lt_of_le_of_lt hkl hp)
  have short_smul {k : ℕ} (z : ℂ) {c : (List (Fin M) × Fin r →₀ ℂ)} (hc : short k c) : short k (z • c) := by
    intro p hp
    simp [Finsupp.smul_apply, hc p hp]
  have short_add {k : ℕ} {c d : (List (Fin M) × Fin r →₀ ℂ)} (hc : short k c) (hd : short k d) :
      short k (c + d) := by
    intro p hp
    simp [hc p hp, hd p hp]
  have short_sum {ι : Type} {k : ℕ} (s : Finset ι) (c : ι → (List (Fin M) × Fin r →₀ ℂ))
      (hc : ∀ i ∈ s, short k (c i)) : short k (∑ i ∈ s, c i) := by
    intro p hp
    simp only [Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero fun i hi => hc i hi p hp
  have proj_inner {n : ℕ} (e : Fin n → H) (he : Orthonormal ℂ e) (x : H) (i : Fin n) :
      inner ℂ (e i) (x - proj e x) = 0 := by
    rw [inner_sub_right, he.inner_right_fintype]
    exact sub_self _
  have proj_eq {n : ℕ} (e : Fin n → H) (he : Orthonormal ℂ e) (x : H) :
      (Submodule.span ℂ (Set.range e)).starProjection x = proj e x := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro y hy
      have hz : inner ℂ y (x - proj e x) = 0 := by
        induction hy using Submodule.span_induction with
        | mem y hy => obtain ⟨i, rfl⟩ := hy; exact proj_inner e he x i
        | zero => simp
        | add y z _ _ hy hz => simp [inner_add_left, hy, hz]
        | smul a y _ hy => simp [inner_smul_left, hy]
      exact inner_eq_zero_symm.mp hz
  let B : ℝ := (D : ℝ) / δ
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hB : 1 ≤ B := (le_div_iff₀ hδ).mpr (by linarith)
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have push_data (a : Fin M) (c : (List (Fin M) × Fin r →₀ ℂ)) :
      ∃ d : (List (Fin M) × Fin r →₀ ℂ), ev d = A a (ev c) ∧ mass d = mass c ∧
        (∀ k, short k c → short (k + 1) d) := by
    let f : (List (Fin M) × Fin r) ↪ (List (Fin M) × Fin r) :=
      ⟨fun p => (p.1 ++ [a], p.2), by
        rintro ⟨w, b⟩ ⟨u, d⟩ hpq
        simp only [Prod.mk.injEq] at hpq
        exact Prod.ext (List.append_left_injective [a] hpq.1) hpq.2⟩
    refine ⟨c.embDomain f, ?_, ?_, ?_⟩
    · simp only [ev, Finsupp.linearCombination_apply, Finsupp.sum_embDomain]
      simp only [word, f, Function.Embedding.coeFn_mk, List.reverse_append, List.reverse_singleton, List.map_cons,
        List.map_append, List.map_singleton, List.prod_cons, List.prod_singleton,
        Module.End.mul_apply, List.map_reverse]
      simp only [map_finsuppSum, map_smul]
      apply Finsupp.sum_congr
      intro p hp
      change c p • ((List.map A (p.1 ++ [a])).reverse.prod (η p.2)) =
        c p • (A a) ((List.map A p.1).reverse.prod (η p.2))
      simp [List.map_append, List.reverse_append, Module.End.mul_apply]
    · simp [mass, Finsupp.sum_embDomain]
    · intro k hc p hp
      by_contra hne
      have hm : p ∈ (c.embDomain f).support := Finsupp.mem_support_iff.mpr hne
      rw [Finsupp.support_embDomain, Finset.mem_map] at hm
      obtain ⟨q, hq, rfl⟩ := hm
      have hlen : k < q.1.length := by
        change k + 1 < (q.1 ++ [a]).length at hp
        simp only [List.length_append, List.length_singleton] at hp
        omega
      exact (Finsupp.mem_support_iff.mp hq) (hc q hlen)
  let Goal : Prop := ∃ (m : ℕ) (hrm : r ≤ m), m ≤ D ∧ ∃ e : Fin m → H,
    Orthonormal ℂ e ∧ (∀ b, e (Fin.castLE hrm b) = η b) ∧
      (∀ a j, ‖A a (e j) - proj e (A a (e j))‖ ≤ δ) ∧
      ∃ c : Fin m → (List (Fin M) × Fin r →₀ ℂ), (∀ j, short (m - r) (c j)) ∧
        (∀ j, ev (c j) = e j) ∧ (∀ j, mass (c j) ≤ B ^ (m - r))
  have construct : ∀ k m, D - m = k → (hrm : r ≤ m) → m ≤ D →
      ∀ (e : Fin m → H) (c : Fin m → (List (Fin M) × Fin r →₀ ℂ)), Orthonormal ℂ e →
        (∀ b, e (Fin.castLE hrm b) = η b) →
        (∀ j, short (m - r) (c j)) → (∀ j, ev (c j) = e j) →
        (∀ j, mass (c j) ≤ B ^ (m - r)) → Goal := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro m hmk hrm hmD e c he heη hc hev hmass
      by_cases hterm : ∀ a j, ‖A a (e j) - proj e (A a (e j))‖ ≤ δ
      · exact ⟨m, hrm, hmD, e, he, heη, hterm, c, hc, hev, hmass⟩
      push Not at hterm
      obtain ⟨a, j, hbad⟩ := hterm
      let x := A a (e j)
      let z := x - proj e x
      let β := ‖z‖
      have hβ : 0 < β := hδ.trans hbad
      let v : H := (β : ℂ)⁻¹ • z
      have hv : ‖v‖ = 1 := by
        simp [v, norm_smul, Complex.norm_real, abs_of_pos hβ, β, hβ.ne']
      have hcross (i : Fin m) : inner ℂ (e i) v = 0 := by
        simp [v, z, inner_smul_right, proj_inner e he x i]
      let e' : Fin (m + 1) → H := Fin.snoc e v
      have he' : Orthonormal ℂ e' := by
        apply orthonormal_iff_ite.mpr
        intro i l
        refine Fin.lastCases ?_ (fun i => ?_) i <;>
          refine Fin.lastCases ?_ (fun l => ?_) l
        · simp [e', inner_self_eq_norm_sq_to_K, hv]
        · simp [e', inner_eq_zero_symm.mpr (hcross l), (Fin.castSucc_ne_last l).symm]
        · simp [e', hcross i]
        · simpa [e', Fin.castSucc_inj] using (orthonormal_iff_ite.mp he i l)
      have hstepD : m + 1 ≤ D := by
        simpa [H] using he'.linearIndependent.fintype_card_le_finrank
      have hgap : m + 1 - r = (m - r) + 1 := by omega
      have hold (i : Fin m) : short (m + 1 - r) (c i) := short_mono (by omega) (hc i)
      obtain ⟨d, hd, hdm, hdshort⟩ := push_data a (c j)
      let cn : (List (Fin M) × Fin r →₀ ℂ) := (β : ℂ)⁻¹ • (d + ∑ i, (-inner ℂ (e i) x) • c i)
      have hcnshort : short (m + 1 - r) cn := by
        apply short_smul
        apply short_add
        · rw [hgap]; exact hdshort (m - r) (hc j)
        · exact short_sum _ _ fun i _ => short_smul _ (hold i)
      have hcn : ev cn = v := by
        simp only [cn, map_smul, map_add, map_sum, hd, hev]
        simp [v, z, x, proj, sub_eq_add_neg, Finset.sum_neg_distrib]
      have hx : ‖x‖ ≤ 1 := (hA a (e j)).trans_eq (he.norm_eq_one j)
      have hcoeff (i : Fin m) : ‖inner ℂ (e i) x‖ ≤ 1 := by
        exact (norm_inner_le_norm (e i) x).trans (by simpa [he.norm_eq_one i] using hx)
      have hsum : mass (∑ i, (-inner ℂ (e i) x) • c i) ≤ (m : ℝ) * B ^ (m - r) := by
        calc
          _ ≤ ∑ i, mass ((-inner ℂ (e i) x) • c i) := mass_sum _ _
          _ ≤ ∑ _i : Fin m, B ^ (m - r) := by
            apply Finset.sum_le_sum
            intro i _
            rw [mass_smul, norm_neg]
            exact (mul_le_mul_of_nonneg_right (hcoeff i) (mass_nonneg _)).trans (by simpa using hmass i)
          _ = _ := by simp
      have hcnmass : mass cn ≤ B ^ (m + 1 - r) := by
        have hβinv : ‖(β : ℂ)⁻¹‖ ≤ δ⁻¹ := by
          simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
          exact (inv_le_inv₀ hβ hδ).mpr (le_of_lt hbad)
        calc
          mass cn = ‖(β : ℂ)⁻¹‖ * mass (d + ∑ i, (-inner ℂ (e i) x) • c i) := mass_smul _ _
          _ ≤ δ⁻¹ * (B ^ (m - r) + (m : ℝ) * B ^ (m - r)) :=
            mul_le_mul hβinv ((mass_add _ _).trans (add_le_add (hdm ▸ hmass j) hsum))
              (mass_nonneg _) (inv_nonneg.mpr hδ.le)
          _ ≤ δ⁻¹ * ((D : ℝ) * B ^ (m - r)) := by
            gcongr
            nlinarith [pow_nonneg hB0 (m - r), show (m : ℝ) + 1 ≤ D by exact_mod_cast hstepD]
          _ = B ^ (m + 1 - r) := by rw [hgap, pow_succ]; dsimp [B]; ring
      let c' : Fin (m + 1) → (List (Fin M) × Fin r →₀ ℂ) := Fin.snoc c cn
      apply ih (D - (m + 1)) (by omega) (m + 1) rfl (by omega) hstepD e' c' he'
      · intro b
        have hb : (Fin.castLE (by omega : r ≤ m + 1) b) =
            (Fin.castLE hrm b).castSucc := by ext; rfl
        rw [hb]
        change (Fin.snoc e v : Fin (m + 1) → H) (Fin.castLE hrm b).castSucc = η b
        rw [Fin.snoc_castSucc]
        exact heη b
      · intro i
        refine Fin.lastCases ?_ (fun l => ?_) i
        · simpa [c'] using hcnshort
        · simpa [c'] using hold l
      · intro i
        refine Fin.lastCases ?_ (fun l => ?_) i
        · simpa [c', e'] using hcn
        · simpa [c', e'] using hev l
      · rw [Fin.forall_fin_succ']
        constructor
        · intro i
          simp only [c', Fin.snoc_castSucc]
          exact (hmass i).trans (pow_le_pow_right₀ hB (by omega))
        · simpa [c'] using hcnmass
  have hgoal : Goal := by
    let c : Fin r → (List (Fin M) × Fin r →₀ ℂ) := fun b => Finsupp.single ([], b) 1
    apply construct (D - r) r rfl le_rfl hrD η c hη
    · intro b; rfl
    · intro b p hp
      simp only [c, Finsupp.single_apply]
      split_ifs with heq
      · subst p; simp at hp
      · rfl
    · intro b
      simp [ev, Finsupp.linearCombination_apply, c, word]
    · intro b
      simp [c, mass]
  obtain ⟨m, hrm, hmD, e, he, heη, hterm, c, hc, hev, hmass⟩ := hgoal
  refine ⟨m, hrm, hmD, e, he, heη, ?_, c, ?_, ?_, hmass⟩
  · intro a j
    simpa only [proj_eq e he] using hterm a j
  · intro j p hp
    by_contra h
    exact (Finsupp.mem_support_iff.mp hp) (hc j p (by omega))
  · intro j
    exact (hev j).symm

#print axioms quantitative_word_orthonormal_extension

end D5.S3.Quantum.Algebra.QuantitativeWordOrthonormalExtension
