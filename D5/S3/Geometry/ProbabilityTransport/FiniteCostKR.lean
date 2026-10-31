/- GID: D5/S3/Geometry/ProbabilityTransport/FiniteCostKR
   generality: G
   mirror-B: D5/B/S3/Geometry/ProbabilityTransport/FiniteCostKR
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: General cost Kantorovich Rubinstein transport -/
import D5.S3.Geometry.ProbabilityTransport.CostCoupling
import D5.S3.Analytic.Convexity.FiniteStrongDuality
/-! # Finite and general-cost Kantorovich-Rubinstein transport. -/

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
    simpa only [hc_self, sub_zero, finiteCTransform] using h
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
  obtain ⟨hf, hfu, hfv⟩ :=
    finiteCTransform_properties Finset.univ hne c hc_self hc_symm hc_triangle u v
  have hge : (∑ i, a i * u i) + ∑ j, b j * v j ≤
      (∑ i, a i * f i) - ∑ j, b j * f j := by
    have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (hfu i (Finset.mem_univ i)) (ha i))
    have hv := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_left (hfv j (fun i _ => hfeas i j)) (hb j))
    have h := add_le_add hu hv
    simp only [mul_neg, Finset.sum_neg_distrib] at h
    dsimp only [f]
    linarith
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


private theorem finiteRange_optimal_coupling
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y) (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x) (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T S : α → α) (hT : Measurable T) (hS : Measurable S)
    (hTfin : (Set.range T).Finite) (hSfin : (Set.range S).Finite) :
    ∃ (π : Measure (α × α)) (g : α → ℝ),
      IsCoupling π (Measure.map T μ) (Measure.map S ν) ∧
      (∀ x y, |g x - g y| ≤ c x y) ∧
      (∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π) =
        ENNReal.ofReal (∫ x, g x ∂(Measure.map T μ) - ∫ x, g x ∂(Measure.map S ν)) := by
  classical
  have : Nonempty α := nonempty_of_isProbabilityMeasure μ
  let A := hTfin.toFinset ∪ hSfin.toFinset
  have hTA : ∀ x, T x ∈ A := fun x => Finset.mem_union_left _ (by simp)
  have hSA : ∀ x, S x ∈ A := fun x => Finset.mem_union_right _ (by simp)
  have hA : A.Nonempty := ⟨T (Classical.arbitrary α), hTA _⟩
  have : IsProbabilityMeasure (Measure.map T μ) :=
    (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (Measure.map S ν) :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).mpr inferInstance
  have hμmap : Measure.map T μ = ∑ x ∈ A, (Measure.map T μ {x}) • Measure.dirac x := by
    refine (Measure.ae_mem_finset_iff (μ := Measure.map T μ) (s := A)).mp ?_
    rw [ae_iff, show {a | ¬ (a ∈ A)} = (↑A : Set α)ᶜ from by ext a; simp,
      Measure.map_apply hT A.measurableSet.compl, Set.preimage_compl]
    have huniv : T ⁻¹' (↑A : Set α) = Set.univ := by ext y; simp [hTA y]
    rw [huniv, Set.compl_univ, measure_empty]
  have hνmap : Measure.map S ν = ∑ y ∈ A, (Measure.map S ν {y}) • Measure.dirac y := by
    refine (Measure.ae_mem_finset_iff (μ := Measure.map S ν) (s := A)).mp ?_
    rw [ae_iff, show {a | ¬ (a ∈ A)} = (↑A : Set α)ᶜ from by ext a; simp,
      Measure.map_apply hS A.measurableSet.compl, Set.preimage_compl]
    have huniv : S ⁻¹' (↑A : Set α) = Set.univ := by ext y; simp [hSA y]
    rw [huniv, Set.compl_univ, measure_empty]
  let a : A → ℝ := fun i => ((Measure.map T μ) {(i : α)}).toReal
  let b : A → ℝ := fun i => ((Measure.map S ν) {(i : α)}).toReal
  have hμmass : (∑ x ∈ A, (Measure.map T μ {x})) = 1 := by
    have h1 : (∑ x ∈ A, (Measure.map T μ {x}) • Measure.dirac x) Set.univ = 1 := by
      rw [← hμmap]; exact measure_univ
    simpa only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one] using h1
  have hνmass : (∑ x ∈ A, (Measure.map S ν {x})) = 1 := by
    have h1 : (∑ x ∈ A, (Measure.map S ν {x}) • Measure.dirac x) Set.univ = 1 := by
      rw [← hνmap]; exact measure_univ
    simpa only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one] using h1
  have ha1 : ∑ i, a i = 1 := by
    rw [show (∑ i, a i) = ∑ x ∈ A, ((Measure.map T μ) {x}).toReal from
      Finset.sum_coe_sort A (fun x => ((Measure.map T μ) {x}).toReal),
      ← ENNReal.toReal_sum (fun x _ => measure_ne_top _ _), hμmass, ENNReal.toReal_one]
  have hb1 : ∑ i, b i = 1 := by
    rw [show (∑ i, b i) = ∑ x ∈ A, ((Measure.map S ν) {x}).toReal from
      Finset.sum_coe_sort A (fun x => ((Measure.map S ν) {x}).toReal),
      ← ENNReal.toReal_sum (fun x _ => measure_ne_top _ _), hνmass, ENNReal.toReal_one]
  obtain ⟨P, f, hP, hrow, hcol, hf, hval, _hmin, _hmax⟩ :=
    finite_kr_attained a b (fun i j => c i j) (fun _ => ENNReal.toReal_nonneg)
      (fun _ => ENNReal.toReal_nonneg) ha1 hb1 (fun i j => hc_nonneg i j)
      (fun i => hc_self i) (fun i j => hc_symm i j) (fun i j k => hc_triangle i j k)
  let u : α → ℝ := fun x => if hx : x ∈ A then f ⟨x, hx⟩ else 0
  let g := finiteCTransform A hA c u
  obtain ⟨hg, hgu, hgv⟩ := finiteCTransform_properties A hA c hc_self hc_symm hc_triangle u (-u)
  have hgf : ∀ i : A, g i = f i := by
    intro i
    have hui : u i = f i := dite_eq_left i.2
    apply le_antisymm
    · have h := hgv i (fun j hj => ?_)
      · simpa only [Pi.neg_apply, neg_neg, hui] using h
      · have huj : u j = f ⟨j, hj⟩ := dite_eq_left hj
        rw [Pi.neg_apply, huj, hui]
        exact (le_abs_self _).trans (hf ⟨j, hj⟩ i)
    · simpa only [hui] using hgu i i.2
  have hint : ∀ (m : Measure α) [IsFiniteMeasure m],
      m = ∑ x ∈ A, m {x} • Measure.dirac x →
      (∫ x, g x ∂m) = ∑ i : A, (m {(i : α)}).toReal * f i := by
    intro m _ hm
    have hi : ∀ x ∈ A, Integrable g ((m {x}) • Measure.dirac x) := fun x _ =>
      (integrable_dirac (by simp)).smul_measure (measure_ne_top _ _)
    conv_lhs => rw [hm]
    rw [integral_finsetSum_measure hi]
    simp_rw [integral_smul_measure, integral_dirac, smul_eq_mul]
    rw [← Finset.sum_coe_sort A (fun x => (m {x}).toReal * g x)]
    exact Finset.sum_congr rfl fun i _ => congrArg ((m {(i : α)}).toReal * ·) (hgf i)
  set π : Measure (α × α) := ∑ i : A, ∑ j : A,
    ENNReal.ofReal (P i j) • Measure.dirac ((↑i : α), (↑j : α)) with hπ_def
  have hofa : ∀ i : A, ENNReal.ofReal (a i) = Measure.map T μ {↑i} :=
    fun i => ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hofb : ∀ i : A, ENNReal.ofReal (b i) = Measure.map S ν {↑i} :=
    fun i => ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hfst : Measure.map Prod.fst π = Measure.map T μ := by
    ext E hE
    rw [Measure.map_apply measurable_fst hE, hπ_def, hμmap]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply]
    rw [← Finset.sum_coe_sort A (fun x => Measure.map T μ {x} * Set.indicator E 1 x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hind : ∀ j : A,
        Set.indicator (Prod.fst ⁻¹' E) (1 : α × α → ℝ≥0∞) (↑i, ↑j)
          = Set.indicator E 1 (↑i : α) :=
      fun j => by simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
    simp_rw [hind, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hP i j),
      hrow, hofa]
  have hsnd : Measure.map Prod.snd π = Measure.map S ν := by
    ext E hE
    rw [Measure.map_apply measurable_snd hE, hπ_def, hνmap]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply]
    rw [Finset.sum_comm, ← Finset.sum_coe_sort A
      (fun y => Measure.map S ν {y} * Set.indicator E 1 y)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hind : ∀ i : A,
        Set.indicator (Prod.snd ⁻¹' E) (1 : α × α → ℝ≥0∞) (↑i, ↑j)
          = Set.indicator E 1 (↑j : α) :=
      fun i => by simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
    simp_rw [hind, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hP i j),
      hcol, hofb]
  have hcost : ∫⁻ z, ENNReal.ofReal (c z.1 z.2) ∂π
      = ENNReal.ofReal (∑ i : A, ∑ j : A, c i j * P i j) := by
    simp only [π, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
      smul_eq_mul]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hc_nonneg _ _) (hP i j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hc_nonneg _ _) (hP i j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ENNReal.ofReal_mul (hP i j), mul_comm (P i j) (c (↑i) (↑j))]
  refine ⟨π, g, ⟨hfst, hsnd⟩, hg, ?_⟩
  rw [hcost, hint _ hμmap, hint _ hνmap]
  exact congrArg ENNReal.ofReal hval

private theorem wassersteinCostCoupling_le_dual_of_finiteRange
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (c : α → α → ℝ) (hc_nonneg : ∀ x y, 0 ≤ c x y) (hc_self : ∀ x, c x x = 0)
    (hc_symm : ∀ x y, c x y = c y x) (hc_triangle : ∀ x y z, c x z ≤ c x y + c y z)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T S : α → α) (hT : Measurable T) (hS : Measurable S)
    (hTfin : (Set.range T).Finite) (hSfin : (Set.range S).Finite) :
    wassersteinCostCoupling c (Measure.map T μ) (Measure.map S ν)
      ≤ wassersteinCost c (Measure.map T μ) (Measure.map S ν) := by
  obtain ⟨π, g, hπ, hg, hcost⟩ :=
    finiteRange_optimal_coupling c hc_nonneg hc_self hc_symm hc_triangle μ ν T S hT hS hTfin hSfin
  exact (iInf_le_of_le π (iInf_le _ hπ)).trans
    (hcost.trans_le (le_iSup_of_le g (le_iSup_of_le hg le_rfl)))

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
    exists_finiteRange_map_cost_le c hc_nonneg hc_self hc_symm hc_triangle hc_cont
      hc_le_dist μ x₀ hμ_cm
      ((ε : ℝ) / 4) hε4
  obtain ⟨S, hS, hSfin, hScost⟩ :=
    exists_finiteRange_map_cost_le c hc_nonneg hc_self hc_symm hc_triangle hc_cont
      hc_le_dist ν x₀ hν_cm
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
        μ ν T S hT hS hTfin hSfin).trans
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
