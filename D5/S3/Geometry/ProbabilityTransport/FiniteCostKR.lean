/- GID: D5/S3/Geometry/ProbabilityTransport/FiniteCostKR
   generality: G
   mirror-B: D5/B/S3/Geometry/ProbabilityTransport/FiniteCostKR
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: General cost Kantorovich Rubinstein transport -/
import D5.S3.Geometry.ProbabilityTransport.CostCoupling
import Mathlib.Basic.Real.Basic
import D5.S3.Analytic.Convexity.FiniteStrongDuality
open D5.S3.Analytic.Convexity.FarkasAlternative
open D5.S3.Analytic.Convexity.ExtendedFarkas
open D5.S3.Analytic.Convexity.FiniteStrongDuality
open scoped Matrix
/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/brooks-suppliers/lean-pool-LICENSE.txt.
Authors: Joseph K. Miller
Selected optimal-transport declarations from LeanPool/Vlasov/OT/Coupling.lean
and LeanPool/Vlasov/OT/Wasserstein.lean, lean-pool commit
edbe5bd56f476cc2965564676b66199f281ab714.
The complete supplier NOTICE is retained verbatim in the owning
CostCoupling.scribe.cs. Modified: native imports and namespace, native simple
approximation with the original sigma-algebra, native finite strong duality,
and explicit finite attainment with a single c-transform potential.
-/

namespace FiniteTransportInterface
noncomputable section
universe u v

private lemma e_ne_bot (x : ℝ) : toE x ≠ (⊥ : Extend ℝ) := WithBot.coe_ne_bot
private lemma e_ne_top (x : ℝ) : toE x ≠ (⊤ : Extend ℝ) := by
  intro h
  exact WithTop.coe_ne_top (WithBot.coe_eq_coe.mp h)
private lemma e_le (x y : ℝ) : toE x ≤ toE y ↔ x ≤ y :=
  (WithBot.coe_strictMono.comp WithTop.coe_strictMono).le_iff_le
private lemma e_inj (x y : ℝ) : toE x = toE y ↔ x = y :=
  (WithBot.coe_strictMono.comp WithTop.coe_strictMono).injective.eq_iff
private lemma e_neg (x : ℝ) : -(toE x) = toE (-x) := rfl
private lemma e_dot {K : Type*} [Fintype K] (c : K → ℝ) (x : K → NNeg ℝ) :
    (fun k => toE (c k)) ᵥ⬝ x = toE (∑ k, c k * (x k).val) := by
  change (∑ k, toE ((x k).val * c k)) = _
  calc
    (∑ k, toE ((x k).val * c k)) = ∑ k, toE (c k * (x k).val) := by
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg toE (mul_comm _ _)
    _ = toE (∑ k, c k * (x k).val) :=
      (map_sum (RatAddHom (F := ℝ)) (fun k => c k * (x k).val) Finset.univ).symm

private def realLP {I J : Type*} (A : I → J → ℝ) (b : I → ℝ) (c : J → ℝ) :
    ValidELP I J ℝ where
  A i j := toE (A i j)
  b i := toE (b i)
  c j := toE (c j)
  hAi := by rintro ⟨i, ⟨j, h⟩, _⟩; exact e_ne_bot _ h
  hAj := by rintro ⟨j, ⟨i, h⟩, _⟩; exact e_ne_bot _ h
  hbA := by rintro ⟨i, ⟨j, h⟩, _⟩; exact e_ne_bot _ h
  hcA := by rintro ⟨j, ⟨i, h⟩, _⟩; exact e_ne_top _ h
  hAb := by rintro ⟨i, ⟨j, h⟩, _⟩; exact e_ne_top _ h
  hAc := by rintro ⟨j, ⟨i, h⟩, _⟩; exact e_ne_bot _ h

private lemma real_solution {I J : Type*} [Fintype J]
    (A : I → J → ℝ) (b : I → ℝ) (c : J → ℝ) (x : J → NNeg ℝ) :
    (realLP A b c).IsSolution x ↔ ∀ i, ∑ j, A i j * (x j).val ≤ b i := by
  change (∀ i, (fun j => toE (A i j)) ᵥ⬝ x ≤ toE (b i)) ↔ _
  simp only [e_dot, e_le]

private lemma real_dual_solution {I J : Type*} [Fintype I]
    (A : I → J → ℝ) (b : I → ℝ) (c : J → ℝ) (y : I → NNeg ℝ) :
    (realLP A b c).dualize.IsSolution y ↔ ∀ j, ∑ i, -(A i j) * (y i).val ≤ c j := by
  change (∀ j, (fun i => -(toE (A i j))) ᵥ⬝ y ≤ toE (c j)) ↔ _
  simp only [e_neg, e_dot, e_le]

private lemma paired_solution {K J : Type*} [Fintype J]
    (B : K → J → ℝ) (d : K → ℝ) (c : J → ℝ) (x : J → NNeg ℝ) :
    (realLP (Sum.elim B (fun k j => -B k j))
      (Sum.elim d (fun k => -d k)) c).IsSolution x ↔
      ∀ k, ∑ j, B k j * (x j).val = d k := by
  rw [real_solution]
  constructor
  · intro h k
    have hp := h (Sum.inl k)
    have hm := h (Sum.inr k)
    change (∑ j, B k j * (x j).val) ≤ d k at hp
    change (∑ j, -(B k j) * (x j).val) ≤ -(d k) at hm
    simp only [neg_mul, Finset.sum_neg_distrib] at hm
    linarith
  · intro h s
    cases s with
    | inl k => exact le_of_eq (h k)
    | inr k =>
      change (∑ j, -(B k j) * (x j).val) ≤ -(d k)
      simp only [neg_mul, Finset.sum_neg_distrib]
      exact le_of_eq (congrArg Neg.neg (h k))

private lemma paired_dual_sum {K J : Type*} [Fintype K]
    (B : K → J → ℝ) (y : K ⊕ K → NNeg ℝ) (j : J) :
    (∑ s : K ⊕ K, -(Sum.elim B (fun k j => -B k j) s j) * (y s).val) =
      ∑ k, B k j * ((y (Sum.inr k)).val - (y (Sum.inl k)).val) := by
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib, mul_sub, Finset.sum_sub_distrib]
  ring

private lemma paired_objective {K : Type*} [Fintype K]
    (d : K → ℝ) (y : K ⊕ K → NNeg ℝ) :
    (∑ s : K ⊕ K, Sum.elim d (fun k => -d k) s * (y s).val) =
      -(∑ k, d k * ((y (Sum.inr k)).val - (y (Sum.inl k)).val)) := by
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib, mul_sub, Finset.sum_sub_distrib]
  ring

variable {m : Type u} {n : Type v} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

private def incidence : (m ⊕ n) → (m × n) → ℝ := fun s ij =>
  match s with
  | Sum.inl i => if i = ij.1 then 1 else 0
  | Sum.inr j => if j = ij.2 then 1 else 0

private lemma incidence_row (x : m × n → ℝ) (i : m) :
    (∑ ij, incidence (Sum.inl i) ij * x ij) = ∑ j, x (i,j) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [incidence]

private lemma incidence_col (x : m × n → ℝ) (j : n) :
    (∑ ij, incidence (Sum.inr j) ij * x ij) = ∑ i, x (i,j) := by
  simp [incidence, Fintype.sum_prod_type]

private lemma incidence_dual (z : m ⊕ n → ℝ) (ij : m × n) :
    (∑ s, incidence s ij * z s) = z (Sum.inl ij.1) + z (Sum.inr ij.2) := by
  simp [incidence, Fintype.sum_sum_type]

end
noncomputable section
universe u v

private theorem finite_transport_attained {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (a : m → ℝ) (b : n → ℝ) (Cost : m → n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (ha1 : ∑ i, a i = 1) (hb1 : ∑ j, b j = 1)
    (hCost : ∀ i j, 0 ≤ Cost i j) :
    ∃ (P : m → n → ℝ) (u : m → ℝ) (v : n → ℝ),
      (∀ i j, 0 ≤ P i j) ∧
      (∀ i, ∑ j, P i j = a i) ∧
      (∀ j, ∑ i, P i j = b j) ∧
      (∀ i j, u i + v j ≤ Cost i j) ∧
      (∑ i, ∑ j, Cost i j * P i j) = (∑ i, a i * u i) + ∑ j, b j * v j := by
  classical
  let B : (m ⊕ n) → (m × n) → ℝ := incidence
  let d : (m ⊕ n) → ℝ := Sum.elim a b
  let A : ((m ⊕ n) ⊕ (m ⊕ n)) → (m × n) → ℝ :=
    Sum.elim B (fun k j => -B k j)
  let rhs : ((m ⊕ n) ⊕ (m ⊕ n)) → ℝ := Sum.elim d (fun k => -d k)
  let c : (m × n) → ℝ := fun ij => Cost ij.1 ij.2
  let L := realLP A rhs c
  let x0 : (m × n) → NNeg ℝ := fun ij => ⟨a ij.1 * b ij.2, mul_nonneg (ha _) (hb _)⟩
  have hx0 : L.IsSolution x0 := by
    apply (paired_solution B d c x0).mpr
    intro k
    cases k with
    | inl i =>
      change (∑ ij, incidence (Sum.inl i) ij * (a ij.1 * b ij.2)) = a i
      rw [incidence_row]
      change (∑ j, a i * b j) = a i
      rw [← Finset.mul_sum, hb1, mul_one]
    | inr j =>
      change (∑ ij, incidence (Sum.inr j) ij * (a ij.1 * b ij.2)) = b j
      rw [incidence_col]
      change (∑ i, a i * b j) = b j
      rw [← Finset.sum_mul, ha1, one_mul]
  have hP : L.IsFeasible :=
    ⟨toE (∑ ij, c ij * (x0 ij).val), ⟨x0, hx0, e_dot c x0⟩, e_ne_top _⟩
  let y0 : ((m ⊕ n) ⊕ (m ⊕ n)) → NNeg ℝ := fun _ => 0
  have hy0 : L.dualize.IsSolution y0 := by
    apply (real_dual_solution A rhs c y0).mpr
    intro ij
    change (∑ k : ((m ⊕ n) ⊕ (m ⊕ n)), -(A k ij) * (0 : ℝ)) ≤ Cost ij.1 ij.2
    simpa only [mul_zero, Finset.sum_const_zero] using hCost ij.1 ij.2
  have hQ : L.dualize.IsFeasible := by
    refine ⟨toE 0, ⟨y0, hy0, ?_⟩, e_ne_top 0⟩
    change (fun k => toE (rhs k)) ᵥ⬝ y0 = toE 0
    rw [e_dot]
    congr 1
    change (∑ k, rhs k * (0 : ℝ)) = 0
    simp only [mul_zero, Finset.sum_const_zero]
  obtain ⟨r, ⟨x, hx, hcx⟩, ⟨y, hy, hdy⟩⟩ :=
    L.strong_duality_of_both_feasible hP hQ
  let z : (m ⊕ n) → ℝ := fun k => (y (Sum.inr k)).val - (y (Sum.inl k)).val
  have hxeq : ∀ k, ∑ ij, B k ij * (x ij).val = d k :=
    (paired_solution B d c x).mp hx
  have hrow (i : m) : ∑ j, (x (i,j)).val = a i := by
    have h := hxeq (Sum.inl i)
    change (∑ ij, incidence (Sum.inl i) ij * (x ij).val) = a i at h
    rwa [incidence_row] at h
  have hcol (j : n) : ∑ i, (x (i,j)).val = b j := by
    have h := hxeq (Sum.inr j)
    change (∑ ij, incidence (Sum.inr j) ij * (x ij).val) = b j at h
    rwa [incidence_col] at h
  have hpot (i : m) (j : n) : z (Sum.inl i) + z (Sum.inr j) ≤ Cost i j := by
    have h := (real_dual_solution A rhs c y).mp hy (i,j)
    change (∑ k, -(Sum.elim B (fun k j => -B k j) k (i,j)) * (y k).val) ≤ Cost i j at h
    rw [paired_dual_sum] at h
    change (∑ k, incidence k (i,j) * z k) ≤ Cost i j at h
    rwa [incidence_dual] at h
  have hcx_real : (∑ ij, c ij * (x ij).val) = -r := by
    change (fun ij => toE (c ij)) ᵥ⬝ x = toE (-r) at hcx
    rw [e_dot] at hcx
    exact (e_inj _ _).mp hcx
  have hdy_real : (∑ k, rhs k * (y k).val) = r := by
    change (fun k => toE (rhs k)) ᵥ⬝ y = toE r at hdy
    rw [e_dot] at hdy
    exact (e_inj _ _).mp hdy
  have hobj : (∑ ij, c ij * (x ij).val) = ∑ k, d k * z k := by
    have hsign : (∑ k, rhs k * (y k).val) = -(∑ k, d k * z k) :=
      paired_objective d y
    linarith
  refine ⟨(fun i j => (x (i,j)).val), (fun i => z (Sum.inl i)),
    (fun j => z (Sum.inr j)), (fun i j => (x (i,j)).property), hrow, hcol, hpot, ?_⟩
  simpa only [c, d, Fintype.sum_prod_type, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr] using hobj

end
end FiniteTransportInterface

noncomputable section
open MeasureTheory ProbabilityTheory ENNReal Filter Topology
open scoped ProbabilityTheory
namespace CostTransport

private def finiteCTransform {α : Type*} (A : Finset α) (hA : A.Nonempty)
    (c : α → α → ℝ) (u : α → ℝ) (x : α) : ℝ :=
  A.sup' hA (fun a => u a - c x a)

private theorem finiteCTransform_properties {α : Type*}
    (A : Finset α) (hA : A.Nonempty) (c : α → α → ℝ)
    (hc_self : ∀ x, c x x = 0) (hc_symm : ∀ x y, c x y = c y x)
    (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z) (u v : α → ℝ) :
    (∀ x y, |finiteCTransform A hA c u x - finiteCTransform A hA c u y| ≤ c x y) ∧
    (∀ a ∈ A, u a ≤ finiteCTransform A hA c u a) ∧
    (∀ b, (∀ a ∈ A, u a + v b ≤ c a b) → finiteCTransform A hA c u b ≤ -v b) := by
  let g := finiteCTransform A hA c u
  have key (x y : α) : g x ≤ g y + c x y := by
    apply Finset.sup'_le
    intro a ha
    have h1 : u a - c y a ≤ g y := Finset.le_sup' (fun a => u a - c y a) ha
    have h2 := hc_triangle y x a
    have h3 := hc_symm x y
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    rw [abs_sub_le_iff]
    exact ⟨by linarith [key x y], by linarith [key y x, hc_symm x y]⟩
  · intro a ha
    have h := Finset.le_sup' (fun b => u b - c a b) ha
    simpa only [hc_self, sub_zero] using h
  · intro b hb
    apply Finset.sup'_le
    intro a ha
    have h := hb a ha
    have hs := hc_symm b a
    linarith

private theorem finite_transport_balance {I : Type*} [Fintype I]
    (a b : I → ℝ) (P : I → I → ℝ)
    (hrow : ∀ i, ∑ j, P i j = a i) (hcol : ∀ j, ∑ i, P i j = b j)
    (f : I → ℝ) :
    (∑ i, a i * f i) - ∑ j, b j * f j = ∑ i, ∑ j, (f i - f j) * P i j := by
  have hr : (∑ i, ∑ j, f i * P i j) = ∑ i, a i * f i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum, hrow, mul_comm]
  have hc : (∑ i, ∑ j, f j * P i j) = ∑ j, b j * f j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum, hcol, mul_comm]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [hr, hc]

private theorem finite_transport_weak {I : Type*} [Fintype I]
    (a b : I → ℝ) (c P : I → I → ℝ)
    (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = a i) (hcol : ∀ j, ∑ i, P i j = b j)
    (f : I → ℝ) (hf : ∀ i j, |f i - f j| ≤ c i j) :
    (∑ i, a i * f i) - ∑ j, b j * f j ≤ ∑ i, ∑ j, c i j * P i j := by
  rw [finite_transport_balance a b P hrow hcol f]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hf i j)) (hP i j)

/-- Finite KR duality with an actual optimal matrix and an attained single-potential maximum. -/
theorem finite_kr_attained {I : Type*} [Fintype I]
    (a b : I → ℝ) (c : I → I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (ha1 : ∑ i, a i = 1) (hb1 : ∑ j, b j = 1)
    (hc : ∀ i j, 0 ≤ c i j) (hc_self : ∀ i, c i i = 0)
    (hc_symm : ∀ i j, c i j = c j i)
    (hc_triangle : ∀ i j k, c i k ≤ c i j + c j k) :
    ∃ (P : I → I → ℝ) (f : I → ℝ),
      (∀ i j, 0 ≤ P i j) ∧ (∀ i, ∑ j, P i j = a i) ∧
      (∀ j, ∑ i, P i j = b j) ∧ (∀ i j, |f i - f j| ≤ c i j) ∧
      (∑ i, ∑ j, c i j * P i j) = (∑ i, a i * f i) - ∑ j, b j * f j ∧
      (∀ Q : I → I → ℝ, (∀ i j, 0 ≤ Q i j) →
        (∀ i, ∑ j, Q i j = a i) → (∀ j, ∑ i, Q i j = b j) →
        (∑ i, ∑ j, c i j * P i j) ≤ ∑ i, ∑ j, c i j * Q i j) ∧
      (∀ g : I → ℝ, (∀ i j, |g i - g j| ≤ c i j) →
        (∑ i, a i * g i) - ∑ j, b j * g j ≤ (∑ i, a i * f i) - ∑ j, b j * f j) := by
  classical
  have hne : (Finset.univ : Finset I).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hz : (∑ i, a i) = 0 := by rw [he]; rfl
    linarith
  obtain ⟨P, u, v, hP, hrow, hcol, hfeas, hobj⟩ :=
    FiniteTransportInterface.finite_transport_attained a b c ha hb ha1 hb1 hc
  let f := finiteCTransform Finset.univ hne c u
  obtain ⟨hf, hfu, hfv⟩ := finiteCTransform_properties Finset.univ hne c hc_self hc_symm hc_triangle u v
  have hge : (∑ i, a i * u i) + ∑ j, b j * v j ≤
      (∑ i, a i * f i) - ∑ j, b j * f j := by
    have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (hfu i (Finset.mem_univ i)) (ha i))
    have hv := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_left (hfv j (fun i _ => hfeas i j)) (hb j))
    have h := add_le_add hu hv
    simpa only [mul_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg] using h
  have heq : (∑ i, ∑ j, c i j * P i j) =
      (∑ i, a i * f i) - ∑ j, b j * f j := by
    exact le_antisymm (hobj.trans_le hge) (finite_transport_weak a b c P hP hrow hcol f hf)
  refine ⟨P, f, hP, hrow, hcol, hf, heq, ?_, ?_⟩
  · intro Q hQ hQr hQc
    rw [heq]
    exact finite_transport_weak a b c Q hQ hQr hQc f hf
  · intro g hg
    rw [← heq]
    exact finite_transport_weak a b c P hP hrow hcol g hg


private theorem finiteRange_transportation_dual
    {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T S : α → α) (hT : Measurable T) (hS : Measurable S)
    (hTfin : (Set.range T).Finite) (hSfin : (Set.range S).Finite)
    :
    ∃ u v : α → ℝ, Measurable u ∧ Measurable v ∧
      (∀ a ∈ Set.range T, ∀ b ∈ Set.range S, u a + v b ≤ c a b) ∧
      wassersteinCostCoupling c (Measure.map T μ) (Measure.map S ν)
        ≤ ENNReal.ofReal ((∫ x, u x ∂(Measure.map T μ)) + ∫ x, v x ∂(Measure.map S ν))
          := by
  classical
  have hαne : Nonempty α := nonempty_of_isProbabilityMeasure μ
  obtain ⟨t₀, ht₀⟩ := Set.range_nonempty T
  obtain ⟨s₀, hs₀⟩ := Set.range_nonempty S
  have : Nonempty (hTfin.toFinset) :=
    ⟨⟨t₀, by rw [Set.Finite.mem_toFinset]; exact ht₀⟩⟩
  have : Nonempty (hSfin.toFinset) :=
    ⟨⟨s₀, by rw [Set.Finite.mem_toFinset]; exact hs₀⟩⟩
  set a : hTfin.toFinset → ℝ := fun i => ((Measure.map T μ) {(i : α)}).toReal with ha_def
  set b : hSfin.toFinset → ℝ := fun j => ((Measure.map S ν) {(j : α)}).toReal with hb_def
  set Cost : hTfin.toFinset → hSfin.toFinset → ℝ := fun i j => c (i : α) (j : α) with hCost_def
  have ha_nn : ∀ i, 0 ≤ a i := fun _ => ENNReal.toReal_nonneg
  have hb_nn : ∀ j, 0 ≤ b j := fun _ => ENNReal.toReal_nonneg
  have hμP : IsProbabilityMeasure (Measure.map T μ) :=
    (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  have hνP : IsProbabilityMeasure (Measure.map S ν) :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).mpr inferInstance
  have hμmap : Measure.map T μ
      = ∑ x ∈ hTfin.toFinset, (Measure.map T μ {x}) • Measure.dirac x := by
    refine (Measure.ae_mem_finset_iff (μ := Measure.map T μ) (s := hTfin.toFinset)).mp ?_
    rw [ae_iff, show {a | ¬ (a ∈ hTfin.toFinset)} = (↑hTfin.toFinset : Set α)ᶜ from by ext a; simp,
      Measure.map_apply hT (hTfin.toFinset.measurableSet.compl), Set.preimage_compl]
    have huniv : T ⁻¹' (↑hTfin.toFinset : Set α) = Set.univ := by
      ext y; simp only [Set.mem_preimage, Set.mem_univ, iff_true, Finset.mem_coe,
        Set.Finite.mem_toFinset]; exact Set.mem_range_self y
    rw [huniv, Set.compl_univ, measure_empty]
  have hνmap : Measure.map S ν
      = ∑ y ∈ hSfin.toFinset, (Measure.map S ν {y}) • Measure.dirac y := by
    refine (Measure.ae_mem_finset_iff (μ := Measure.map S ν) (s := hSfin.toFinset)).mp ?_
    rw [ae_iff, show {a | ¬ (a ∈ hSfin.toFinset)} = (↑hSfin.toFinset : Set α)ᶜ from by ext a; simp,
      Measure.map_apply hS (hSfin.toFinset.measurableSet.compl), Set.preimage_compl]
    have huniv : S ⁻¹' (↑hSfin.toFinset : Set α) = Set.univ := by
      ext y; simp only [Set.mem_preimage, Set.mem_univ, iff_true, Finset.mem_coe,
        Set.Finite.mem_toFinset]; exact Set.mem_range_self y
    rw [huniv, Set.compl_univ, measure_empty]
  have hμmass : (∑ x ∈ hTfin.toFinset, (Measure.map T μ {x})) = 1 := by
    have h1 : (∑ x ∈ hTfin.toFinset, (Measure.map T μ {x}) • Measure.dirac x) Set.univ = 1 := by
      rw [← hμmap]; exact measure_univ
    simpa only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one] using h1
  have hνmass : (∑ y ∈ hSfin.toFinset, (Measure.map S ν {y})) = 1 := by
    have h1 : (∑ y ∈ hSfin.toFinset, (Measure.map S ν {y}) • Measure.dirac y) Set.univ = 1 := by
      rw [← hνmap]; exact measure_univ
    simpa only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one] using h1
  have ha_sum : ∑ i, a i = 1 := by
    have hcoe : (∑ i, a i) = ∑ x ∈ hTfin.toFinset, ((Measure.map T μ) {x}).toReal :=
      Finset.sum_coe_sort hTfin.toFinset (fun x => ((Measure.map T μ) {x}).toReal)
    rw [hcoe, ← ENNReal.toReal_sum (fun x _ => measure_ne_top _ _), hμmass, ENNReal.toReal_one]
  have hb_sum : ∑ j, b j = 1 := by
    have hcoe : (∑ j, b j) = ∑ y ∈ hSfin.toFinset, ((Measure.map S ν) {y}).toReal :=
      Finset.sum_coe_sort hSfin.toFinset (fun y => ((Measure.map S ν) {y}).toReal)
    rw [hcoe, ← ENNReal.toReal_sum (fun y _ => measure_ne_top _ _), hνmass, ENNReal.toReal_one]
  obtain ⟨P, u, v, hPnn, hProw, hPcol, hfeas, hval⟩ :=
    FiniteTransportInterface.finite_transport_attained a b Cost ha_nn hb_nn ha_sum hb_sum (fun i j => hc_nonneg i j)
  set ulift : α → ℝ := fun x => if h : x ∈ hTfin.toFinset then u ⟨x, h⟩ else 0 with hulift_def
  set vlift : α → ℝ := fun y => if h : y ∈ hSfin.toFinset then v ⟨y, h⟩ else 0 with hvlift_def
  have hulift_eq : ulift = fun x => ∑ i ∈ hTfin.toFinset.attach,
      Set.indicator {(i : α)} (fun _ => u i) x := by
    funext x
    simp only [hulift_def, Set.indicator_apply, Set.mem_singleton_iff]
    by_cases hx : x ∈ hTfin.toFinset
    · rw [dite_eq_left hx, Finset.sum_eq_single (⟨x, hx⟩ : hTfin.toFinset)]
      · simp
      · intro i _ hi; rw [ite_eq_right (fun h => hi (Subtype.ext h.symm))]
      · intro h; exact absurd (Finset.mem_attach _ _) h
    · rw [dite_eq_right hx]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [ite_eq_right (fun (h : x = (↑i : α)) => hx (h.symm ▸ i.2))]
  have hvlift_eq : vlift = fun y => ∑ j ∈ hSfin.toFinset.attach,
      Set.indicator {(j : α)} (fun _ => v j) y := by
    funext y
    simp only [hvlift_def, Set.indicator_apply, Set.mem_singleton_iff]
    by_cases hy : y ∈ hSfin.toFinset
    · rw [dite_eq_left hy, Finset.sum_eq_single (⟨y, hy⟩ : hSfin.toFinset)]
      · simp
      · intro j _ hj; rw [ite_eq_right (fun h => hj (Subtype.ext h.symm))]
      · intro h; exact absurd (Finset.mem_attach _ _) h
    · rw [dite_eq_right hy]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      rw [ite_eq_right (fun (h : y = (↑j : α)) => hy (h.symm ▸ j.2))]
  have hulift_meas : Measurable ulift := by
    rw [hulift_eq]
    exact Finset.measurable_sum _ fun i _ =>
      (measurable_const).indicator (measurableSet_singleton _)
  have hvlift_meas : Measurable vlift := by
    rw [hvlift_eq]
    exact Finset.measurable_sum _ fun j _ =>
      (measurable_const).indicator (measurableSet_singleton _)
  refine ⟨ulift, vlift, hulift_meas, hvlift_meas, ?_, ?_⟩
  · -- feasibility on supports
    intro a' ha' b' hb'
    have hia : a' ∈ hTfin.toFinset := by rw [Set.Finite.mem_toFinset]; exact ha'
    have hjb : b' ∈ hSfin.toFinset := by rw [Set.Finite.mem_toFinset]; exact hb'
    have hua : ulift a' = u ⟨a', hia⟩ := dite_eq_left hia
    have hvb : vlift b' = v ⟨b', hjb⟩ := dite_eq_left hjb
    rw [hua, hvb]
    exact hfeas ⟨a', hia⟩ ⟨b', hjb⟩
  · -- the matrix→measure bridge bound
    have hint_u : ∫ x, ulift x ∂(Measure.map T μ) = ∑ i, a i * u i := by
      rw [hulift_eq, integral_finsetSum _
        (fun i _ => (integrable_const (u i)).indicator (measurableSet_singleton _))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_indicator_const _ (measurableSet_singleton _), smul_eq_mul]
      simp only [ha_def, measureReal_def]
    have hint_v : ∫ y, vlift y ∂(Measure.map S ν) = ∑ j, b j * v j := by
      rw [hvlift_eq, integral_finsetSum _
        (fun j _ => (integrable_const (v j)).indicator (measurableSet_singleton _))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_indicator_const _ (measurableSet_singleton _), smul_eq_mul]
      simp only [hb_def, measureReal_def]
    have hcoup : wassersteinCostCoupling c (Measure.map T μ) (Measure.map S ν)
        ≤ ENNReal.ofReal (∑ i, ∑ j, Cost i j * P i j) := by
      set π : Measure (α × α) := ∑ i, ∑ j,
        ENNReal.ofReal (P i j) • Measure.dirac ((↑i : α), (↑j : α)) with hπ_def
      have hofw : ∀ i : hTfin.toFinset, ENNReal.ofReal (a i) = Measure.map T μ {↑i} := fun i => by
        rw [ha_def]; exact ENNReal.ofReal_toReal (measure_ne_top _ _)
      have hofb : ∀ j : hSfin.toFinset, ENNReal.ofReal (b j) = Measure.map S ν {↑j} := fun j => by
        rw [hb_def]; exact ENNReal.ofReal_toReal (measure_ne_top _ _)
      have hfst : Measure.map Prod.fst π = Measure.map T μ := by
        ext E hE
        rw [Measure.map_apply measurable_fst hE, hπ_def, hμmap]
        simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
          Measure.dirac_apply]
        rw [← Finset.sum_coe_sort hTfin.toFinset
          (fun x => Measure.map T μ {x} * Set.indicator E 1 x)]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hind : ∀ j : hSfin.toFinset,
            Set.indicator (Prod.fst ⁻¹' E) (1 : α × α → ℝ≥0∞) (↑i, ↑j)
              = Set.indicator E 1 (↑i : α) :=
          fun j => by simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
        simp_rw [hind, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hPnn i j),
          hProw, hofw]
      have hsnd : Measure.map Prod.snd π = Measure.map S ν := by
        ext E hE
        rw [Measure.map_apply measurable_snd hE, hπ_def, hνmap]
        simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
          Measure.dirac_apply]
        rw [Finset.sum_comm, ← Finset.sum_coe_sort hSfin.toFinset
          (fun y => Measure.map S ν {y} * Set.indicator E 1 y)]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hind : ∀ i : hTfin.toFinset,
            Set.indicator (Prod.snd ⁻¹' E) (1 : α × α → ℝ≥0∞) (↑i, ↑j)
              = Set.indicator E 1 (↑j : α) :=
          fun i => by simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
        simp_rw [hind, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hPnn i j),
          hPcol, hofb]
      have hπ_cost : ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π
          = ENNReal.ofReal (∑ i, ∑ j, Cost i j * P i j) := by
        rw [hπ_def]
        simp only [lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
          smul_eq_mul, hCost_def]
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (hc_nonneg _ _) (hPnn i j))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hc_nonneg _ _) (hPnn i j))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← ENNReal.ofReal_mul (hPnn i j), mul_comm (P i j) (c (↑i) (↑j))]
      unfold wassersteinCostCoupling
      exact le_trans (iInf_le_of_le π (iInf_le _ ⟨hfst, hsnd⟩)) (le_of_eq hπ_cost)
    rw [hint_u, hint_v]
    exact hcoup.trans_eq (congrArg ENNReal.ofReal hval)

private theorem cTransform_dual_witness
    {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x) (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (hc_meas : Measurable (fun p : α × α => c p.1 p.2))
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T S : α → α) (hT : Measurable T) (hS : Measurable S)
    (hTfin : (Set.range T).Finite) (hSfin : (Set.range S).Finite)
    (u v : α → ℝ) (hu : Measurable u) (hv : Measurable v)
    (hdual : ∀ a ∈ Set.range T, ∀ b ∈ Set.range S, u a + v b ≤ c a b) :
    ∃ g : α → ℝ, (∀ x y, |g x - g y| ≤ c x y) ∧
      (∫ x, u x ∂(Measure.map T μ)) + (∫ x, v x ∂(Measure.map S ν))
        ≤ ∫ x, g x ∂(Measure.map T μ) - ∫ x, g x ∂(Measure.map S ν) := by
  classical
  have : Nonempty α := nonempty_of_isProbabilityMeasure μ
  set A : Finset α := hTfin.toFinset with hA_def
  set B : Finset α := hSfin.toFinset with hB_def
  have hmemA : ∀ a ∈ Set.range T, a ∈ A := fun a ha => by
    rw [hA_def, Set.Finite.mem_toFinset]; exact ha
  have hmemB : ∀ b ∈ Set.range S, b ∈ B := fun b hb => by
    rw [hB_def, Set.Finite.mem_toFinset]; exact hb
  have hAne : A.Nonempty := by
    obtain ⟨a, ha⟩ := Set.range_nonempty T; exact ⟨a, hmemA a ha⟩
  have hBne : B.Nonempty := by
    obtain ⟨b, hb⟩ := Set.range_nonempty S; exact ⟨b, hmemB b hb⟩
  set g : α → ℝ := finiteCTransform A hAne c u with hg_def
  have hpair : ∀ a : α, Measurable (fun x : α => (x, a)) := fun a => by fun_prop
  have hF_meas : ∀ a, Measurable (fun x => u a - c x a) := fun a =>
    measurable_const.sub (hc_meas.comp (hpair a))
  have hg_meas : Measurable g := by
    have heq : g = A.sup' hAne (fun a x => u a - c x a) := by
      funext x; exact (Finset.sup'_apply hAne (fun a x => u a - c x a) x).symm
    rw [heq]; exact Finset.measurable_sup' hAne (fun a _ => hF_meas a)
  obtain ⟨hg_adm, hgu, hgv⟩ :=
    finiteCTransform_properties A hAne c hc_self hc_symm hc_triangle u v
  have hg_ge_u : ∀ a ∈ Set.range T, u a ≤ g a :=
    fun a ha => hgu a (hmemA a ha)
  have hg_le_negv : ∀ b ∈ Set.range S, g b ≤ -v b := by
    intro b hb
    apply hgv b
    intro a ha
    exact hdual a (by rwa [hA_def, Set.Finite.mem_toFinset] at ha) b hb
  have bdd_integ : ∀ (m : Measure α) [IsFiniteMeasure m] (f : α → ℝ) (C : ℝ),
      Measurable f → (∀ y, |f y| ≤ C) → Integrable f m := by
    intro m _ f C hf hC
    exact (integrable_const C).mono' hf.aestronglyMeasurable
      (ae_of_all m (fun y => by rw [Real.norm_eq_abs]; exact hC y))
  have hu_int : Integrable (fun y => u (T y)) μ :=
    bdd_integ μ _ (A.sup' hAne (fun a => |u a|)) (hu.comp hT)
      (fun y => Finset.le_sup' (fun a => |u a|) (hmemA (T y) (Set.mem_range_self y)))
  have hgT_int : Integrable (fun y => g (T y)) μ :=
    bdd_integ μ _ (A.sup' hAne (fun a => |g a|)) (hg_meas.comp hT)
      (fun y => Finset.le_sup' (fun a => |g a|) (hmemA (T y) (Set.mem_range_self y)))
  have hv_int : Integrable (fun y => v (S y)) ν :=
    bdd_integ ν _ (B.sup' hBne (fun b => |v b|)) (hv.comp hS)
      (fun y => Finset.le_sup' (fun b => |v b|) (hmemB (S y) (Set.mem_range_self y)))
  have hgnegS_int : Integrable (fun y => -(g (S y))) ν :=
    (bdd_integ ν _ (B.sup' hBne (fun b => |g b|)) (hg_meas.comp hS)
      (fun y => Finset.le_sup' (fun b => |g b|) (hmemB (S y) (Set.mem_range_self y)))).neg
  refine ⟨g, hg_adm, ?_⟩
  rw [integral_map hT.aemeasurable hu.aestronglyMeasurable,
      integral_map hS.aemeasurable hv.aestronglyMeasurable,
      integral_map hT.aemeasurable hg_meas.aestronglyMeasurable,
      integral_map hS.aemeasurable hg_meas.aestronglyMeasurable]
  have hmono1 : (∫ y, u (T y) ∂μ) ≤ ∫ y, g (T y) ∂μ :=
    integral_mono hu_int hgT_int (fun y => hg_ge_u (T y) (Set.mem_range_self y))
  have hmono2 : (∫ y, v (S y) ∂ν) ≤ ∫ y, -(g (S y)) ∂ν :=
    integral_mono hv_int hgnegS_int
      (fun y => by have := hg_le_negv (S y) (Set.mem_range_self y); linarith)
  rw [integral_neg] at hmono2
  linarith

private theorem wassersteinCostCoupling_le_dual_of_finiteRange
    {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y) (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x) (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (hc_meas : Measurable (fun p : α × α => c p.1 p.2))
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T S : α → α) (hT : Measurable T) (hS : Measurable S)
    (hTfin : (Set.range T).Finite) (hSfin : (Set.range S).Finite) :
    wassersteinCostCoupling c (Measure.map T μ) (Measure.map S ν)
      ≤ wassersteinCost c (Measure.map T μ) (Measure.map S ν) := by
  obtain ⟨u, v, hu, hv, hdual, hval⟩ :=
    finiteRange_transportation_dual c hc_nonneg μ ν T S hT hS hTfin hSfin
  obtain ⟨g, hg_adm, hg_val⟩ :=
    cTransform_dual_witness c hc_self hc_symm hc_triangle hc_meas μ ν T S hT hS
      hTfin hSfin u v hu hv hdual
  refine hval.trans ((ENNReal.ofReal_le_ofReal hg_val).trans ?_)
  exact le_iSup_of_le g (le_iSup_of_le hg_adm le_rfl)

theorem wassersteinCostCoupling_le_dual
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
    [SecondCountableTopology α] [StandardBorelSpace α]
    (c : α → α → ℝ)
    (hc_nonneg : ∀ x y, 0 ≤ c x y)
    (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x)
    (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (hc_cont : Continuous (fun p : α × α => c p.1 p.2))
    (hc_le_dist : ∀ x y, c x y ≤ dist x y)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x₀ : α)
    (hμ_cm : Integrable (fun y => c y x₀) μ)
    (hν_cm : Integrable (fun y => c y x₀) ν) :
    wassersteinCostCoupling c μ ν ≤ wassersteinCost c μ ν := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _hb => ?_
  have hε4 : (0 : ℝ) < (ε : ℝ) / 4 := by positivity
  obtain ⟨T, hT, hTfin, hTcost⟩ :=
    exists_finiteRange_map_cost_le c hc_nonneg hc_self hc_symm hc_triangle hc_cont hc_le_dist μ x₀ hμ_cm
      ((ε : ℝ) / 4) hε4
  obtain ⟨S, hS, hSfin, hScost⟩ :=
    exists_finiteRange_map_cost_le c hc_nonneg hc_self hc_symm hc_triangle hc_cont hc_le_dist ν x₀ hν_cm
      ((ε : ℝ) / 4) hε4
  have : IsProbabilityMeasure (Measure.map T μ) :=
    (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (Measure.map S ν) :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).mpr inferInstance
  set q : ℝ≥0∞ := ENNReal.ofReal ((ε : ℝ) / 4) with hq
  have htri1 := wassersteinCostCoupling_triangle c hc_triangle hc_cont.measurable
    μ ν (Measure.map T μ)
  have htri2 := wassersteinCostCoupling_triangle c hc_triangle hc_cont.measurable
    (Measure.map T μ) ν (Measure.map S ν)
  have hμμ' : wassersteinCostCoupling c μ (Measure.map T μ) ≤ q :=
    (wassersteinCostCoupling_map_le c hc_cont μ T hT).trans hTcost
  have hν'ν : wassersteinCostCoupling c (Measure.map S ν) ν ≤ q := by
    rw [wassersteinCostCoupling_comm c hc_symm hc_cont.measurable (Measure.map S ν) ν]
    exact (wassersteinCostCoupling_map_le c hc_cont ν S hS).trans hScost
  have hmid : wassersteinCostCoupling c (Measure.map T μ) (Measure.map S ν)
      ≤ wassersteinCost c μ ν + q + q :=
    (wassersteinCostCoupling_le_dual_of_finiteRange c hc_nonneg hc_self hc_symm hc_triangle
        hc_cont.measurable μ ν T S hT hS hTfin hSfin).trans
      ((wassersteinCost_dual_le_add_map c hc_nonneg hc_self hc_symm hc_cont μ ν T S hT hS
          x₀ hμ_cm hν_cm).trans
        (add_le_add (add_le_add le_rfl hTcost) hScost))
  have hq4 : q + q + q + q = (ε : ℝ≥0∞) := by
    have h4 : q + q + q + q
        = ENNReal.ofReal ((ε : ℝ) / 4 + (ε : ℝ) / 4 + (ε : ℝ) / 4 + (ε : ℝ) / 4) := by
      rw [hq, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [h4, show (ε : ℝ) / 4 + (ε : ℝ) / 4 + (ε : ℝ) / 4 + (ε : ℝ) / 4 = (ε : ℝ) from by ring,
      ENNReal.ofReal_coe_nnreal]
  calc wassersteinCostCoupling c μ ν
      ≤ wassersteinCostCoupling c μ (Measure.map T μ)
          + wassersteinCostCoupling c (Measure.map T μ) ν := htri1
    _ ≤ q + (wassersteinCostCoupling c (Measure.map T μ) (Measure.map S ν)
          + wassersteinCostCoupling c (Measure.map S ν) ν) := add_le_add hμμ' htri2
    _ ≤ q + ((wassersteinCost c μ ν + q + q) + q) := add_le_add le_rfl (add_le_add hmid hν'ν)
    _ = wassersteinCost c μ ν + (q + q + q + q) := by ring
    _ = wassersteinCost c μ ν + (ε : ℝ≥0∞) := by rw [hq4]

end CostTransport
