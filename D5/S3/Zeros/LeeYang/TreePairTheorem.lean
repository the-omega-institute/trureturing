/- GID: D5/S3/Zeros/LeeYang/TreePairTheorem
   generality: G
   mirror-B: D5/B/S3/Zeros/LeeYang/TreePairTheorem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The complete arbitrary finite tree physical pair coefficient theorem. -/
import D5.S3.Zeros.LeeYang.TreePairSource
import D5.S3.Zeros.LeeYang.TreePairStability
import D5.S3.Zeros.LeeYang.TreePairStability
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace FiolArbitraryTreePair

section Incidences
variable {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]

def incidenceVertex (src tgt : E → V) (i : E × Bool) : V :=
  if i.2 then src i.1 else tgt i.1

def receivingAdjacency (src tgt : E → V) (u v : V) : ℕ :=
  ∑ e, if (src e = u ∧ tgt e = v) ∨ (tgt e = u ∧ src e = v) then 1 else 0

theorem incidence_degree (src tgt : E → V) (v : V) :
    (∑ i : E × Bool, if incidenceVertex src tgt i = v then 1 else 0) =
      sourceDegree src tgt v := by
  simp only [incidenceVertex, Fintype.sum_prod_type, Fintype.sum_bool,
    Bool.false_eq_true, ↓reduceIte, Finset.sum_add_distrib, sourceDegree, add_comm]

theorem receivingAdjacency_symm (src tgt : E → V) (u v : V) :
    receivingAdjacency src tgt u v = receivingAdjacency src tgt v u := by
  apply Finset.sum_congr rfl
  intro e _
  have h : ((src e = u ∧ tgt e = v) ∨ (tgt e = u ∧ src e = v)) ↔
      ((src e = v ∧ tgt e = u) ∨ (tgt e = v ∧ src e = u)) := by tauto
  simp only [h]

theorem receivingAdjacency_diag (src tgt : E → V) (hloop : ∀ e, src e ≠ tgt e)
    (v : V) : receivingAdjacency src tgt v v = 0 := by
  apply Finset.sum_eq_zero
  intro e _
  have hn : ¬ ((src e = v ∧ tgt e = v) ∨ (tgt e = v ∧ src e = v)) := by
    rintro (⟨h1,h2⟩ | ⟨h2,h1⟩) <;> exact hloop e (h1.trans h2.symm)
  simp [hn]

theorem receivingAdjacency_le_one (src tgt : E → V)
    (hsimple : ∀ e f, (src e = src f ∧ tgt e = tgt f) ∨
      (src e = tgt f ∧ tgt e = src f) → e = f) (u v : V) :
    receivingAdjacency src tgt u v ≤ 1 := by
  unfold receivingAdjacency
  rw [← Finset.card_filter]
  apply Finset.card_le_one.mpr
  intro e he f hf
  have he := (Finset.mem_filter.mp he).2
  have hf := (Finset.mem_filter.mp hf).2
  apply hsimple e f
  rcases he with he | he <;> rcases hf with hf | hf <;> aesop

private theorem receiving_edge_indicator (src tgt : E → V)
    (hloop : ∀ e, src e ≠ tgt e) (e : E) (u v : V) :
    (if (src e = u ∧ tgt e = v) ∨ (tgt e = u ∧ src e = v) then 1 else 0 : ℕ) =
      (if src e = u ∧ tgt e = v then 1 else 0) +
        (if tgt e = u ∧ src e = v then 1 else 0) := by
  by_cases h1 : src e = u ∧ tgt e = v
  · have h2 : ¬ (tgt e = u ∧ src e = v) := by
      rintro ⟨h2,h3⟩
      exact hloop e (h1.1.trans h2.symm)
    rw [if_pos (Or.inl h1), if_pos h1, if_neg h2]
  · by_cases h2 : tgt e = u ∧ src e = v
    · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2]
    · rw [if_neg (by tauto), if_neg h1, if_neg h2]

theorem receivingAdjacency_row [Fintype V] (src tgt : E → V)
    (hloop : ∀ e, src e ≠ tgt e) (u : V) :
    (∑ v, receivingAdjacency src tgt u v) = sourceDegree src tgt u := by
  unfold receivingAdjacency
  rw [Finset.sum_comm]
  simp_rw [receiving_edge_indicator src tgt hloop, Finset.sum_add_distrib]
  simp [sourceDegree, ite_and, Finset.sum_add_distrib, eq_comm]

theorem sourceDegree_sum [Fintype V] (src tgt : E → V) :
    (∑ v, sourceDegree src tgt v) = 2 * Fintype.card E := by
  unfold sourceDegree
  rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_comm (f := fun v e =>
    if tgt e = v then 1 else 0)]
  simp [eq_comm, two_mul]

private theorem same_edge_indicator (src tgt : E → V) (hloop : ∀ e, src e ≠ tgt e)
    (e : E) (u v : V) :
    (∑ b : Bool, ∑ c : Bool,
      if (if b then src e else tgt e) = u ∧ (if c then src e else tgt e) = v
      then 1 else 0 : ℕ) =
      if u = v then (if src e = u then 1 else 0) + (if tgt e = u then 1 else 0)
      else if (src e = u ∧ tgt e = v) ∨ (tgt e = u ∧ src e = v) then 1 else 0 := by
  have hl := hloop e
  by_cases huv : u = v
  · subst v
    by_cases hs : src e = u <;> by_cases ht : tgt e = u <;>
      simp_all [Fintype.sum_bool, -Finset.sum_boole]
  · by_cases hs1 : src e = u <;> by_cases hs2 : src e = v <;>
      by_cases ht1 : tgt e = u <;> by_cases ht2 : tgt e = v <;>
      simp_all [Fintype.sum_bool, -Finset.sum_boole]

theorem same_edge_receiving_count (src tgt : E → V)
    (hloop : ∀ e, src e ≠ tgt e) (u v : V) :
    (∑ i : E × Bool, ∑ j : E × Bool,
      if i.1 = j.1 ∧ incidenceVertex src tgt i = u ∧ incidenceVertex src tgt j = v
        then 1 else 0 : ℕ) =
      if u = v then sourceDegree src tgt u else receivingAdjacency src tgt u v := by
  have he (e : E) := same_edge_indicator src tgt hloop e u v
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, incidenceVertex,
    Bool.false_eq_true, ↓reduceIte, ite_and,
    Finset.sum_add_distrib] at he ⊢
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  by_cases huv : u = v
  · simp only [if_pos huv, sourceDegree] at he ⊢
    simpa only [Finset.sum_add_distrib] using
      Finset.sum_congr (s₁ := (univ : Finset E)) rfl (fun e _ => he e)
  · simp only [if_neg huv, receivingAdjacency] at he ⊢
    simpa only [Finset.sum_add_distrib] using
      Finset.sum_congr (s₁ := (univ : Finset E)) rfl (fun e _ => he e)

def receivingPairCount (src tgt : E → V) (u v : V) : ℕ :=
  ∑ i : E × Bool, ∑ j : E × Bool,
    if i.1 ≠ j.1 ∧ incidenceVertex src tgt i = u ∧ incidenceVertex src tgt j = v
      then 1 else 0

theorem receivingPairCount_add (src tgt : E → V)
    (hloop : ∀ e, src e ≠ tgt e) (u v : V) :
    receivingPairCount src tgt u v +
        (if u = v then sourceDegree src tgt u else receivingAdjacency src tgt u v) =
      sourceDegree src tgt u * sourceDegree src tgt v := by
  rw [← same_edge_receiving_count src tgt hloop u v]
  unfold receivingPairCount
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  have he (i j : E × Bool) :
      (if i.1 ≠ j.1 ∧ incidenceVertex src tgt i = u ∧ incidenceVertex src tgt j = v
        then 1 else 0 : ℕ) +
      (if i.1 = j.1 ∧ incidenceVertex src tgt i = u ∧ incidenceVertex src tgt j = v
        then 1 else 0) =
      (if incidenceVertex src tgt i = u then 1 else 0) *
        (if incidenceVertex src tgt j = v then 1 else 0) := by
    by_cases h1 : i.1 = j.1 <;> by_cases h2 : incidenceVertex src tgt i = u <;>
      by_cases h3 : incidenceVertex src tgt j = v <;> simp [h1, h2, h3]
  simp_rw [he, ← Finset.mul_sum, ← Finset.sum_mul, incidence_degree]

theorem sum_by_receivers {R : Type*} [CommRing R] [Fintype V]
    (src tgt : E → V) (F : V → V → R) :
    (∑ i : E × Bool, ∑ j : E × Bool,
      if i.1 ≠ j.1 then F (incidenceVertex src tgt i) (incidenceVertex src tgt j) else 0) =
      ∑ u, ∑ v, (receivingPairCount src tgt u v : R) * F u v := by
  let D : Finset ((E × Bool) × (E × Bool)) :=
    univ.filter fun p => p.1.1 ≠ p.2.1
  let g (p : (E × Bool) × (E × Bool)) : V × V :=
    (incidenceVertex src tgt p.1, incidenceVertex src tgt p.2)
  have hf (uv : V × V) : (D.filter fun p => g p = uv).card =
      receivingPairCount src tgt uv.1 uv.2 := by
    rcases uv with ⟨u,v⟩
    simp [D, g, receivingPairCount, Finset.card_filter, Fintype.sum_prod_type,
      Finset.sum_filter, ite_and, Prod.mk.injEq, -Finset.sum_boole]
  have hs := Finset.sum_fiberwise' D g (fun uv => F uv.1 uv.2)
  simp only [Finset.sum_const, nsmul_eq_mul, hf] at hs
  simpa only [D, g, Fintype.sum_prod_type, Finset.sum_filter] using hs.symm

end Incidences
end FiolArbitraryTreePair

open scoped BigOperators
open Polynomial

namespace FiolArbitraryTreePair

section Grouped
variable {V : Type*} [Fintype V] [DecidableEq V]

def groupedPolynomial (d : V → ℕ) (a : V → V → ℝ) : ℝ[X] :=
  (∑ v, C (kappa (d v)) * vertexFactor (d v) 2 *
    ∏ w ∈ Finset.univ.erase v, vertexFactor (d w) 0) +
  (∑ u, ∑ v, if u = v then 0 else
    C (pairWeight d a u v) * vertexFactor (d u) 1 * vertexFactor (d v) 1 *
      ∏ w ∈ (Finset.univ.erase u).erase v, vertexFactor (d w) 0) * C (1 / 2)

private theorem pair_prod_erase (b : V → ℂ) (u v : V) (huv : u ≠ v) :
    b u * b v * (∏ w ∈ (Finset.univ.erase u).erase v, b w) = ∏ w, b w := by
  rw [mul_assoc, Finset.mul_prod_erase _ _ (by simp [Ne.symm huv]),
    Finset.mul_prod_erase _ _ (Finset.mem_univ u)]

private theorem kappa_complex (d : ℕ) : ((kappa d : ℝ) : ℂ) = (kappa d : ℂ) := by
  simp [kappa]
private theorem pairWeight_complex (d : V → ℕ) (a : V → V → ℝ) (u v : V) :
    ((pairWeight d a u v : ℝ) : ℂ) =
      pairWeight d (fun x y => (a x y : ℂ)) u v := by
  simp [pairWeight]

/- The transform retains the physical powers, with the leaf parameters constrained. -/
theorem grouped_cayley (d : V → ℕ) (a : V → V → ℝ)
    (hd : ∀ v, 1 ≤ d v) (x : ℂ) (hx : ‖x‖ < 1) :
    complexEval (groupedPolynomial d a) x =
      ((1 - x) / 2) ^ 2 * (∏ v, complexEval (vertexFactor (d v) 0) x) *
        (pairQuadratic d (fun u v => (a u v : ℂ)) (cayley (-x)) (physicalEta d x) +
          ((∑ v, (kappa (d v) : ℝ)) : ℂ)) := by
  let z := cayley (-x)
  let eta := physicalEta d x
  let beta := (1 - x) / 2
  let b (v : V) := complexEval (vertexFactor (d v) 0) x
  have hx1 : x ≠ 1 := by intro h; simpa [h] using hx
  have hb (v : V) : 1 + (-1 : ℂ) ^ d v * x ^ d v ≠ 0 := by
    apply cayley_denominator_ne_zero
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx (by have := hd v; omega)
  have hz : (1 + x) / (1 - x) = z := by simp [z, cayley, sub_eq_add_neg]
  have hlocal (v : V) := cayley_vertex_local x ((-1 : ℂ) ^ d v * x ^ d v) hx1 (hb v)
  have h1 (v : V) : complexEval (vertexFactor (d v) 1) x = beta * (z + eta v) * b v := by
    have h := (hlocal v).1
    rw [hz] at h
    simpa [beta, eta, physicalEta, b, vertexFactor_eval, pow_add, mul_assoc] using h.symm
  have h2 (v : V) : complexEval (vertexFactor (d v) 2) x =
      beta ^ 2 * (z ^ 2 + 2 * z * eta v + 1) * b v := by
    have h := (hlocal v).2
    rw [hz] at h
    simpa [beta, eta, physicalEta, b, vertexFactor_eval, pow_add, mul_assoc] using h.symm
  have hs (v : V) : (kappa (d v) : ℂ) * complexEval (vertexFactor (d v) 2) x *
      (∏ w ∈ Finset.univ.erase v, b w) =
      beta ^ 2 * (∏ w, b w) * (kappa (d v) * (z ^ 2 + 2 * z * eta v + 1)) := by
    rw [h2]
    have hp := Finset.mul_prod_erase (Finset.univ : Finset V) b (Finset.mem_univ v)
    linear_combination (kappa (d v) * beta ^ 2 * (z ^ 2 + 2 * z * eta v + 1)) * hp
  have hp (u v : V) (huv : u ≠ v) :
      pairWeight d (fun u v => (a u v : ℂ)) u v *
        complexEval (vertexFactor (d u) 1) x * complexEval (vertexFactor (d v) 1) x *
        (∏ w ∈ (Finset.univ.erase u).erase v, b w) =
      beta ^ 2 * (∏ w, b w) *
        (pairWeight d (fun u v => (a u v : ℂ)) u v * (z + eta u) * (z + eta v)) := by
    rw [h1, h1]
    have he := pair_prod_erase b u v huv
    linear_combination (pairWeight d (fun u v => (a u v : ℂ)) u v *
      beta ^ 2 * (z + eta u) * (z + eta v)) * he
  change _ = beta ^ 2 * (∏ v, b v) *
    (pairQuadratic d (fun u v => (a u v : ℂ)) z eta + _)
  have halgebraMap : ∀ r : ℝ, algebraMap ℝ ℂ r = (r : ℂ) := fun _ => rfl
  simp only [complexEval, groupedPolynomial, apply_ite, eval₂_zero, eval₂_add, eval₂_finsetSum, eval₂_mul,
    eval₂_C, eval₂_finsetProd, halgebraMap, Complex.ofReal_inv, Complex.ofReal_ofNat, one_div, Complex.ofReal_sum,
    kappa_complex, pairWeight_complex]
  change (∑ v, (kappa (d v) : ℂ) * complexEval (vertexFactor (d v) 2) x *
      ∏ w ∈ Finset.univ.erase v, b w) +
    (∑ u, ∑ v, if u = v then 0 else
      pairWeight d (fun u v => (a u v : ℂ)) u v *
        complexEval (vertexFactor (d u) 1) x * complexEval (vertexFactor (d v) 1) x *
        ∏ w ∈ (Finset.univ.erase u).erase v, b w) / 2 = _
  simp_rw [hs]
  have hpair : (∑ u, ∑ v, if u = v then (0 : ℂ) else
      pairWeight d (fun u v => (a u v : ℂ)) u v *
        complexEval (vertexFactor (d u) 1) x * complexEval (vertexFactor (d v) 1) x *
        ∏ w ∈ (Finset.univ.erase u).erase v, b w) =
      beta ^ 2 * (∏ w, b w) *
      (∑ u, ∑ v, if u = v then 0 else
        pairWeight d (fun u v => (a u v : ℂ)) u v * (z + eta u) * (z + eta v)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : u = v
    · simp [h]
    · simp only [if_neg h]
      exact hp u v h
  have hk : (∑ v, (kappa (d v) : ℂ) * (z ^ 2 + 2 * z * eta v + 1)) =
      (∑ v, (kappa (d v) : ℂ) * (z ^ 2 + 2 * z * eta v)) + ∑ v, kappa (d v) := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib]
  rw [hpair, ← Finset.mul_sum, hk]
  unfold pairQuadratic
  ring

theorem grouped_nonzero_in_disk (d : V → ℕ) (a : V → V → ℝ)
    (hd : ∀ v, 1 ≤ d v) (ha : ∀ u v, 0 ≤ a u v ∧ a u v ≤ 1)
    (hsymm : ∀ u v, a u v = a v u)
    (hrow : ∀ u, ∑ v, a u v = (d u : ℝ)) (hdiag : ∀ v, a v v = 0)
    (hi : ∃ v, 2 ≤ d v) (x : ℂ) (hx : ‖x‖ < 1) :
    complexEval (groupedPolynomial d a) x ≠ 0 := by
  rw [grouped_cayley d a hd x hx]
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply pow_ne_zero
      exact div_ne_zero (sub_ne_zero.mpr (by intro h; simpa [← h] using hx)) (by norm_num)
    · apply Finset.prod_ne_zero_iff.mpr
      intro v _
      rw [vertexFactor_eval, add_zero]
      apply cayley_denominator_ne_zero
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
      exact pow_lt_one₀ (norm_nonneg x) hx (by have := hd v; omega)
  · rw [← Complex.ofReal_sum]
    apply physical_pairQuadratic_nonzero d a hd ha hsymm hrow hdiag hi x hx
    apply Finset.sum_nonneg
    intro v _
    have hv : (1 : ℝ) ≤ d v := by exact_mod_cast hd v
    unfold kappa
    exact div_nonneg (mul_nonneg (sq_nonneg _) (by nlinarith)) (by norm_num)

theorem grouped_eval_neg_one (d : V → ℕ) (a : V → V → ℝ) [Nonempty V] :
    (groupedPolynomial d a).eval (-1) =
      2 ^ Fintype.card V * ∑ v, (kappa (d v) : ℝ) := by
  simp only [groupedPolynomial, apply_ite, eval_zero, eval_add, eval_finsetSum, eval_mul, eval_C,
    eval_prod, vertexFactor_eval_neg_one]
  norm_num only [pow_zero, pow_one, neg_one_sq, add_neg_cancel, add_zero, zero_mul,
    mul_zero, ite_self, Finset.sum_const_zero, zero_div, one_add_one_eq_two]
  have hn : Fintype.card V ≠ 0 := Fintype.card_ne_zero
  have he : (2 : ℝ) * 2 ^ (Fintype.card V - 1) = 2 ^ Fintype.card V := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]
  simp_rw [mul_assoc, he]
  rw [← Finset.sum_mul, mul_comm]


end Grouped
end FiolArbitraryTreePair

open scoped BigOperators
open Finset Polynomial

namespace FiolArbitraryTreePair

section Receiving
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem pairReceived_diagonal (d : V → ℕ) (u : V) :
    pairReceivedPolynomial d u u =
      C (vertexRatio (d u) 2) * vertexFactor (d u) 2 *
        ∏ w ∈ univ.erase u, vertexFactor (d w) 0 := by
  let f (w : V) := C (vertexRatio (d w)
      ((if u = w then 1 else 0) + (if u = w then 1 else 0))) *
    vertexFactor (d w) ((if u = w then 1 else 0) + (if u = w then 1 else 0))
  change (∏ w, f w) = _
  rw [← Finset.mul_prod_erase univ f (Finset.mem_univ u)]
  have hu : f u = C (vertexRatio (d u) 2) * vertexFactor (d u) 2 := by simp [f]
  rw [hu]
  congr 1
  apply Finset.prod_congr rfl
  intro w hw
  have h : u ≠ w := Ne.symm (Finset.mem_erase.mp hw).1
  simp [f, h, vertexRatio]

theorem pairReceived_off_diagonal (d : V → ℕ) (u v : V) (huv : u ≠ v) :
    pairReceivedPolynomial d u v =
      C (vertexRatio (d u) 1 * vertexRatio (d v) 1) *
        vertexFactor (d u) 1 * vertexFactor (d v) 1 *
          ∏ w ∈ (univ.erase u).erase v, vertexFactor (d w) 0 := by
  let f (w : V) := C (vertexRatio (d w)
      ((if u = w then 1 else 0) + (if v = w then 1 else 0))) *
    vertexFactor (d w) ((if u = w then 1 else 0) + (if v = w then 1 else 0))
  change (∏ w, f w) = _
  rw [← Finset.mul_prod_erase univ f (Finset.mem_univ u),
    ← Finset.mul_prod_erase (univ.erase u) f (show v ∈ univ.erase u from by simp [Ne.symm huv])]
  have hu : f u = C (vertexRatio (d u) 1) * vertexFactor (d u) 1 := by
    simp [f, Ne.symm huv]
  have hv : f v = C (vertexRatio (d v) 1) * vertexFactor (d v) 1 := by
    simp [f, huv]
  have hp : (∏ w ∈ (univ.erase u).erase v, f w) =
      ∏ w ∈ (univ.erase u).erase v, vertexFactor (d w) 0 := by
    apply Finset.prod_congr rfl
    intro w hw
    have h1 : u ≠ w := Ne.symm (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
    have h2 : v ≠ w := Ne.symm (Finset.mem_erase.mp hw).1
    simp [f, h1, h2, vertexRatio]
  rw [hu, hv, hp, map_mul]
  ring

theorem diagonal_receiving_weight (src tgt : E → V) (hloop : ∀ e, src e ≠ tgt e)
    (v : V) :
    (receivingPairCount src tgt v v : ℝ) * vertexRatio (sourceDegree src tgt v) 2 =
      2 * kappa (sourceDegree src tgt v) := by
  have h := receivingPairCount_add src tgt hloop v v
  simp only [if_pos rfl] at h
  have hc : (receivingPairCount src tgt v v : ℝ) + sourceDegree src tgt v =
      (sourceDegree src tgt v : ℝ) * sourceDegree src tgt v := by exact_mod_cast h
  rw [show (receivingPairCount src tgt v v : ℝ) =
    (sourceDegree src tgt v : ℝ) ^ 2 - sourceDegree src tgt v by nlinarith]
  norm_num [vertexRatio, kappa]
  ring

theorem off_diagonal_receiving_weight (src tgt : E → V)
    (hloop : ∀ e, src e ≠ tgt e) (u v : V) (huv : u ≠ v) :
    (receivingPairCount src tgt u v : ℝ) *
        (vertexRatio (sourceDegree src tgt u) 1 * vertexRatio (sourceDegree src tgt v) 1) =
      pairWeight (sourceDegree src tgt) (fun u v => (receivingAdjacency src tgt u v : ℝ)) u v := by
  have h := receivingPairCount_add src tgt hloop u v
  simp only [if_neg huv] at h
  have hc : (receivingPairCount src tgt u v : ℝ) + receivingAdjacency src tgt u v =
      (sourceDegree src tgt u : ℝ) * sourceDegree src tgt v := by exact_mod_cast h
  rw [show (receivingPairCount src tgt u v : ℝ) =
    (sourceDegree src tgt u : ℝ) * sourceDegree src tgt v - receivingAdjacency src tgt u v
    by linarith]
  norm_num [vertexRatio, pairWeight]
  ring

theorem treeAllocation_twice_receiving (d : V → ℕ) (src tgt : E → V) :
    2 * treeAllocationPolynomial d src tgt =
      ∑ u, ∑ v, (receivingPairCount src tgt u v : ℝ[X]) * pairReceivedPolynomial d u v := by
  rw [treeAllocation_twice]
  rw [← sum_by_receivers src tgt (pairReceivedPolynomial d)]
  have ho : (univ : Finset E).offDiag =
      (univ : Finset (E × E)).filter (fun p => p.1 ≠ p.2) := by
    ext p
    simp
  rw [ho, Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  have hs : (∑ b : Bool, ∑ f : E, ∑ c : Bool,
      if e ≠ f then pairReceivedPolynomial d (incidenceVertex src tgt (e,b))
        (incidenceVertex src tgt (f,c)) else 0) =
    ∑ f : E, ∑ b : Bool, ∑ c : Bool,
      if e ≠ f then pairReceivedPolynomial d (incidenceVertex src tgt (e,b))
        (incidenceVertex src tgt (f,c)) else 0 := Finset.sum_comm
  rw [hs]
  apply Finset.sum_congr rfl
  intro f _
  by_cases h : e ≠ f <;> simp [h, incidenceVertex]

theorem treeAllocation_grouped (src tgt : E → V) (hloop : ∀ e, src e ≠ tgt e) :
    treeAllocationPolynomial (sourceDegree src tgt) src tgt =
      groupedPolynomial (sourceDegree src tgt)
        (fun u v => (receivingAdjacency src tgt u v : ℝ)) := by
  let d := sourceDegree src tgt
  let a (u v : V) : ℝ := receivingAdjacency src tgt u v
  let D (u : V) : ℝ[X] := C (kappa (d u)) * vertexFactor (d u) 2 *
    ∏ w ∈ univ.erase u, vertexFactor (d w) 0
  let P (u v : V) : ℝ[X] := C (pairWeight d a u v) *
    vertexFactor (d u) 1 * vertexFactor (d v) 1 *
      ∏ w ∈ (univ.erase u).erase v, vertexFactor (d w) 0
  have hc (u v : V) : (receivingPairCount src tgt u v : ℝ[X]) *
      pairReceivedPolynomial d u v = if u = v then 2 * D u else P u v := by
    have hn : (receivingPairCount src tgt u v : ℝ[X]) =
        C (receivingPairCount src tgt u v : ℝ) := by simp
    rw [hn]
    by_cases huv : u = v
    · subst v
      rw [if_pos rfl, pairReceived_diagonal]
      dsimp [D]
      rw [← mul_assoc, ← mul_assoc, ← map_mul,
        diagonal_receiving_weight src tgt hloop u, map_mul]
      simp only [map_ofNat]
      dsimp only [d]
      ring
    · rw [if_neg huv, pairReceived_off_diagonal d u v huv]
      dsimp [P]
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← map_mul,
        off_diagonal_receiving_weight src tgt hloop u v huv]
  have he := treeAllocation_twice_receiving d src tgt
  simp_rw [hc] at he
  have hsplit (u v : V) : (if u = v then 2 * D u else P u v) =
      (if u = v then 2 * D u else 0) + (if u = v then 0 else P u v) := by
    split_ifs <;> simp
  simp_rw [hsplit, Finset.sum_add_distrib] at he
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at he
  rw [← Finset.mul_sum] at he
  apply mul_left_cancel₀ (show (2 : ℝ[X]) ≠ 0 by norm_num)
  change 2 * treeAllocationPolynomial d src tgt =
    2 * groupedPolynomial d a
  rw [he]
  unfold groupedPolynomial
  change 2 * (∑ u, D u) + (∑ u, ∑ v, if u = v then 0 else P u v) =
    2 * ((∑ u, D u) + (∑ u, ∑ v, if u = v then 0 else P u v) * C (1 / 2))
  have hhalf : (2 : ℝ[X]) * C (1 / 2 : ℝ) = 1 := by
    calc
      _ = C ((2 : ℝ) * (1 / 2)) := by simp only [map_mul, map_ofNat]
      _ = 1 := by norm_num
  linear_combination -(∑ u, ∑ v, if u = v then 0 else P u v) * hhalf

end Receiving
end FiolArbitraryTreePair

open scoped BigOperators
open Finset Polynomial

namespace FiolArbitraryTreePair

section GraphRoots
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem treeAllocation_disk_nonzero (src tgt : E → V)
    (hloop : ∀ e, src e ≠ tgt e)
    (hsimple : ∀ e f, (src e = src f ∧ tgt e = tgt f) ∨
      (src e = tgt f ∧ tgt e = src f) → e = f)
    (hd : ∀ v, 1 ≤ sourceDegree src tgt v)
    (hi : ∃ v, 2 ≤ sourceDegree src tgt v) (x : ℂ) (hx : ‖x‖ < 1) :
    complexEval (treeAllocationPolynomial (sourceDegree src tgt) src tgt) x ≠ 0 := by
  rw [treeAllocation_grouped src tgt hloop]
  apply grouped_nonzero_in_disk _ _ hd _ _ _ _ hi x hx
  · intro u v
    constructor
    · positivity
    · exact_mod_cast receivingAdjacency_le_one src tgt hsimple u v
  · intro u v
    exact_mod_cast receivingAdjacency_symm src tgt u v
  · intro u
    exact_mod_cast receivingAdjacency_row src tgt hloop u
  · intro v
    exact_mod_cast receivingAdjacency_diag src tgt hloop v

theorem treeAllocation_unit_circle (src tgt : E → V)
    (hloop : ∀ e, src e ≠ tgt e)
    (hsimple : ∀ e f, (src e = src f ∧ tgt e = tgt f) ∨
      (src e = tgt f ∧ tgt e = src f) → e = f)
    (hd : ∀ v, 1 ≤ sourceDegree src tgt v)
    (hi : ∃ v, 2 ≤ sourceDegree src tgt v)
    (x : ℂ) (hx : complexEval (treeAllocationPolynomial (sourceDegree src tgt) src tgt) x = 0) :
    ‖x‖ = 1 := by
  apply allocation_roots_on_circle (sourceDegree src tgt) (allocationIncrements src tgt)
    (fun c => allocationWeight (sourceDegree src tgt) src tgt c.1.val c.2.val)
    (2 * Fintype.card E + 2) _ _ _ x hx
  · intro c
    simp only [Finset.sum_add_distrib, allocationIncrements_sum, sourceDegree_sum]
  · exact ⟨Fintype.card E, by rw [sourceDegree_sum]; omega⟩
  · exact treeAllocation_disk_nonzero src tgt hloop hsimple hd hi

theorem treeAllocation_neg_one_pos (src tgt : E → V)
    (hloop : ∀ e, src e ≠ tgt e) (hd : ∀ v, 1 ≤ sourceDegree src tgt v)
    (hi : ∃ v, 2 ≤ sourceDegree src tgt v) :
    0 < (treeAllocationPolynomial (sourceDegree src tgt) src tgt).eval (-1) := by
  letI : Nonempty V := ⟨hi.choose⟩
  rw [treeAllocation_grouped src tgt hloop, grouped_eval_neg_one]
  apply mul_pos (by positivity)
  have hk (v : V) : 0 ≤ (kappa (sourceDegree src tgt v) : ℝ) := by
    have hv : (1 : ℝ) ≤ sourceDegree src tgt v := by exact_mod_cast hd v
    unfold kappa
    exact div_nonneg (mul_nonneg (sq_nonneg _) (by nlinarith)) (by norm_num)
  obtain ⟨v,hv⟩ := hi
  have hvR : (2 : ℝ) ≤ sourceDegree src tgt v := by exact_mod_cast hv
  have hkv : 0 < (kappa (sourceDegree src tgt v) : ℝ) := by
    unfold kappa
    exact div_pos (mul_pos (by positivity) (by nlinarith)) (by norm_num)
  exact lt_of_lt_of_le hkv
    (Finset.single_le_sum (fun u _ => hk u) (Finset.mem_univ v))

end GraphRoots
end FiolArbitraryTreePair

open scoped BigOperators
open Finset Polynomial SimpleGraph

attribute [local instance] Classical.propDecidable

namespace FiolArbitraryTreePair

abbrev treeGraph {V E : Type*} (src tgt : E → V) : SimpleGraph V :=
  D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport.treeSupport src tgt Set.univ

section TreeFacts
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (src tgt : E → V)
variable (ht : D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport.NamedSpanningTree
  src tgt Set.univ)
include ht

theorem named_tree_nonloop (e : E) : src e ≠ tgt e := ht.nonloop e (Set.mem_univ e)

theorem named_tree_edge_injective : Function.Injective (fun e : E => s(src e,tgt e)) := by
  intro e f h
  have hh : (⟨e,Set.mem_univ e⟩ : (Set.univ : Set E)) = ⟨f,Set.mem_univ f⟩ :=
    ht.distinct h
  exact congrArg Subtype.val hh

theorem named_tree_simple (e f : E) (h : (src e = src f ∧ tgt e = tgt f) ∨
    (src e = tgt f ∧ tgt e = src f)) : e = f :=
  named_tree_edge_injective src tgt ht (Sym2.eq_iff.mpr h)

theorem named_tree_adj_iff (u v : V) :
    (treeGraph src tgt).Adj u v ↔
      ∃ e, (src e = u ∧ tgt e = v) ∨ (tgt e = u ∧ src e = v) := by
  constructor
  · intro h
    obtain ⟨e,he⟩ := ((SimpleGraph.fromEdgeSet_adj _).mp h).1
    have hh := Sym2.eq_iff.mp he
    exact ⟨e.val, by aesop⟩
  · rintro ⟨e,he⟩
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    constructor
    · refine ⟨⟨e,Set.mem_univ e⟩, ?_⟩
      exact Sym2.eq_iff.mpr (by aesop)
    · intro huv
      have hl := named_tree_nonloop src tgt ht e
      rcases he with ⟨h1,h2⟩ | ⟨h2,h1⟩ <;> apply hl <;> aesop

theorem named_tree_adjacency_indicator (u v : V) :
    receivingAdjacency src tgt u v = if (treeGraph src tgt).Adj u v then 1 else 0 := by
  classical
  have hle := receivingAdjacency_le_one src tgt (named_tree_simple src tgt ht) u v
  by_cases h : (treeGraph src tgt).Adj u v
  · rw [if_pos h]
    obtain ⟨e,he⟩ := (named_tree_adj_iff src tgt ht u v).mp h
    have hge : 1 ≤ receivingAdjacency src tgt u v := by
      have hs := Finset.single_le_sum
        (f := fun i : E => if (src i = u ∧ tgt i = v) ∨ (tgt i = u ∧ src i = v)
          then 1 else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
      simpa only [receivingAdjacency, if_pos he] using hs
    omega
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro e _
    have hn : ¬ ((src e = u ∧ tgt e = v) ∨ (tgt e = u ∧ src e = v)) := by
      intro he
      exact h ((named_tree_adj_iff src tgt ht u v).mpr ⟨e,he⟩)
    simp only [if_neg hn]

theorem named_tree_source_degree (v : V) :
    sourceDegree src tgt v = (treeGraph src tgt).degree v := by
  classical
  rw [← receivingAdjacency_row src tgt (named_tree_nonloop src tgt ht) v]
  simp_rw [named_tree_adjacency_indicator src tgt ht]
  simpa using (SimpleGraph.degree_eq_sum_if_adj (treeGraph src tgt) (R := ℕ) v).symm

theorem named_tree_card_vertices : Fintype.card V = Fintype.card E + 1 := by
  classical
  let F : E → (treeGraph src tgt).edgeSet := fun e => ⟨s(src e,tgt e), by
    rw [treeGraph, D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport.treeSupport,
      SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨⟨⟨e,Set.mem_univ e⟩,rfl⟩, ?_⟩
    simpa using named_tree_nonloop src tgt ht e⟩
  have hinj : Function.Injective F := by
    intro e f hef
    exact named_tree_edge_injective src tgt ht (congrArg Subtype.val hef)
  have hsurj : Function.Surjective F := by
    intro a
    have ha := a.property
    change a.val ∈ (SimpleGraph.fromEdgeSet (Set.range
      (fun e : (Set.univ : Set E) => s(src e,tgt e)))).edgeSet at ha
    rw [SimpleGraph.edgeSet_fromEdgeSet] at ha
    obtain ⟨e,he⟩ := ha.1
    exact ⟨e.val, Subtype.ext he⟩
  have hc : Fintype.card E = Fintype.card (treeGraph src tgt).edgeSet :=
    Fintype.card_of_bijective ⟨hinj,hsurj⟩
  have hfin : (treeGraph src tgt).edgeFinset.card = Fintype.card E := by
    simpa [SimpleGraph.edgeFinset] using hc.symm
  have htree : (treeGraph src tgt).edgeFinset.card + 1 = Fintype.card V :=
    ht.isTree.card_edgeFinset
  rw [hfin] at htree
  exact htree.symm

theorem named_tree_degree_positive (he : 2 ≤ Fintype.card E) (v : V) :
    1 ≤ sourceDegree src tgt v := by
  classical
  rw [named_tree_source_degree src tgt ht]
  let e : E := (Fintype.equivFin E).symm ⟨0,by omega⟩
  have hends := named_tree_nonloop src tgt ht e
  have hex : ∃ w : V, v ≠ w := by
    by_cases hs : v = src e
    · exact ⟨tgt e, by simpa [hs] using hends⟩
    · exact ⟨src e,hs⟩
  obtain ⟨w,hvw⟩ := hex
  obtain ⟨p,_,_⟩ := ht.isTree.existsUnique_path v w
  have hp : 0 < (treeGraph src tgt).degree v := by
    cases p with
    | nil => exact (hvw rfl).elim
    | cons h p => exact h.degree_pos_left
  omega

theorem named_tree_internal_vertex (he : 2 ≤ Fintype.card E) :
    ∃ v, 2 ≤ sourceDegree src tgt v := by
  have hd := named_tree_degree_positive src tgt ht he
  have hs := sourceDegree_sum src tgt
  have hc := named_tree_card_vertices src tgt ht
  by_contra h
  push_neg at h
  have hone : ∀ v, sourceDegree src tgt v = 1 := fun v => by have := hd v; have := h v; omega
  simp only [hone, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  have hsNat : Fintype.card V = 2 * Fintype.card E := by exact_mod_cast hs
  omega

end TreeFacts
end FiolArbitraryTreePair

open scoped BigOperators
open Finset Polynomial SimpleGraph

attribute [local instance] Classical.propDecidable

namespace FiolArbitraryTreePair

section Complete
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def automorphismFintype (G : SimpleGraph V) : Fintype (G ≃g G) :=
  Fintype.ofInjective (fun f : G ≃g G => (f : V → V)) (by
    intro f g h
    ext v
    exact congrFun h v)

def automorphismOrder (G : SimpleGraph V) : ℕ :=
  @Fintype.card (G ≃g G) (automorphismFintype G)

def physicalScalar (src tgt : E → V) : ℝ :=
  50 * (-1 : ℝ) ^ Fintype.card E * 12 ^ Fintype.card E *
    (∏ v, (Nat.factorial (sourceDegree src tgt v - 1) : ℝ)) /
      automorphismOrder (treeGraph src tgt)

def physicalCoefficient (src tgt : E → V) : ℝ[X] :=
  (allVertexSource src tgt (automorphismOrder (treeGraph src tgt)) 3).coeff
    (pairKey (Fintype.card E))

def physicalBinaryCoefficient (src tgt : E → V) : MvPolynomial (Fin 2) ℝ :=
  (fullVertexSource src tgt (automorphismOrder (treeGraph src tgt)) 3).coeff
    (pairKey (Fintype.card E))

def physicalQuotient (src tgt : E → V) : ℝ[X] :=
  C (physicalScalar src tgt) * allocationQuotient (sourceDegree src tgt)
    (allocationIncrements src tgt)
    (fun c => allocationWeight (sourceDegree src tgt) src tgt c.1.val c.2.val)

theorem automorphismOrder_pos (G : SimpleGraph V) : 0 < automorphismOrder G := by
  letI := automorphismFintype G
  letI : Nonempty (G ≃g G) := ⟨SimpleGraph.Iso.refl⟩
  change 0 < Fintype.card (G ≃g G)
  exact Fintype.card_pos

theorem physicalScalar_ne_zero (src tgt : E → V) : physicalScalar src tgt ≠ 0 := by
  unfold physicalScalar
  apply div_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))
        (pow_ne_zero _ (by norm_num))
    · exact Finset.prod_ne_zero_iff.mpr (fun v _ => by
        exact_mod_cast Nat.factorial_ne_zero (sourceDegree src tgt v - 1))
  · exact_mod_cast ne_of_gt (automorphismOrder_pos (treeGraph src tgt))

/-- The literal all-vertex source coefficient, for one arbitrary finite simple tree.
The two displayed source coordinates are the second and first coupling, respectively.
No simplicity assertion for the roots is made. -/
theorem complete_named_tree_pair (src tgt : E → V)
    (ht : D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport.NamedSpanningTree
      src tgt Set.univ) (he : 2 ≤ Fintype.card E) :
    let p := physicalCoefficient src tgt
    let q := physicalQuotient src tgt
    let N := 2 * Fintype.card E + 2
    let h := oddCount (fun v => (treeGraph src tgt).degree v)
    p = C (physicalScalar src tgt) * treeAllocationPolynomial (sourceDegree src tgt) src tgt ∧
    physicalBinaryCoefficient src tgt = p.homogenize N ∧
    p.natDegree = N ∧ p ≠ 0 ∧ p.leadingCoeff = p.coeff 0 ∧
    p.rootMultiplicity 1 = h ∧ (p.map (algebraMap ℝ ℂ)).rootMultiplicity 1 = h ∧
    p.eval 0 ≠ 0 ∧ p.eval (-1) ≠ 0 ∧
    (∀ x : ℂ, complexEval p x = 0 → ‖x‖ = 1) ∧
    p = (1 - X) ^ h * q ∧ q.natDegree = N - h ∧
    q.eval 1 ≠ 0 ∧ q.eval (-1) ≠ 0 ∧
    (∀ x : ℂ, complexEval q x = 0 → ‖x‖ = 1 ∧ x ≠ 1 ∧ x ≠ -1) ∧
    MvPolynomial.eval ![(1 : ℝ),0] (physicalBinaryCoefficient src tgt) ≠ 0 ∧
    (∀ x : ℂ, x ≠ 0 →
      MvPolynomial.eval₂ (algebraMap ℝ ℂ) ![x,0] (physicalBinaryCoefficient src tgt) ≠ 0) ∧
    (∀ x : Fin 2 → ℂ, x 1 ≠ 0 →
      MvPolynomial.eval₂ (algebraMap ℝ ℂ) x (physicalBinaryCoefficient src tgt) = 0 →
        ‖x 0 / x 1‖ = 1) := by
  dsimp only
  let d := sourceDegree src tgt
  let R := treeAllocationPolynomial d src tgt
  let r := allocationIncrements src tgt
  let w (c : PairAllocation E) := allocationWeight d src tgt c.1.val c.2.val
  let Q := allocationQuotient d r w
  let c := physicalScalar src tgt
  have hc : c ≠ 0 := physicalScalar_ne_zero src tgt
  have hC : C c ≠ 0 := by simpa using hc
  have hd := named_tree_degree_positive src tgt ht he
  have hi := named_tree_internal_vertex src tgt ht he
  have hloop := named_tree_nonloop src tgt ht
  have hsimple := named_tree_simple src tgt ht
  have hcard := named_tree_card_vertices src tgt ht
  have haut : automorphismOrder (treeGraph src tgt) ≠ 0 :=
    ne_of_gt (automorphismOrder_pos _)
  have hp : physicalCoefficient src tgt = C c * R :=
    exact_source_coefficient src tgt _ 3 haut (by omega) he hcard hd
  have hb : physicalBinaryCoefficient src tgt = (physicalCoefficient src tgt).homogenize
      (2 * Fintype.card E + 2) := by
    rw [hp,homogenize_C_mul]
    exact exact_full_source_coefficient src tgt _ 3 haut (by omega) he hcard hd
  have hR := treeAllocation_degree_multiplicity d src tgt he hd (sourceDegree_sum src tgt)
  have hodd : oddCount d = oddCount (fun v => (treeGraph src tgt).degree v) := by
    congr 1
    funext v
    exact named_tree_source_degree src tgt ht v
  letI : Nonempty (PairAllocation E) := pairAllocation_nonempty he
  have hw : ∀ a, 0 < w a := allocationWeight_pos d src tgt hd
  have hdp : ∀ v, 0 < d v := fun v => hd v
  have hQpos : 0 < Q.eval 1 := allocation_quotient_at_one_pos d r w hdp hw
  have hQ : Q ≠ 0 := by intro hz; rw [hz, eval_zero] at hQpos; linarith
  have hfactor : R = (1 - X) ^ oddCount d * Q := allocation_factor_at_one d r w
  have hmult : (C c * R).rootMultiplicity 1 = oddCount d := by
    rw [rootMultiplicity_mul (mul_ne_zero hC hR.2.1)]
    have hz : (C c).rootMultiplicity 1 = 0 := rootMultiplicity_eq_zero (by simpa using hc)
    rw [hz, zero_add]
    exact hR.2.2.2.1
  have hnegR : R.eval (-1) ≠ 0 := ne_of_gt (treeAllocation_neg_one_pos src tgt hloop hd hi)
  have hnegQ : Q.eval (-1) ≠ 0 := by
    intro hz
    apply hnegR
    rw [hfactor, eval_mul, hz, mul_zero]
  have hlead : (C c * R).leadingCoeff = (C c * R).coeff 0 := by
    rw [leadingCoeff_mul, leadingCoeff_C, coeff_C_mul, hR.2.2.1]
  have hconst : (C c * R).eval 0 ≠ 0 := by
    rw [eval_mul, eval_C, ← coeff_zero_eq_eval_zero]
    exact mul_ne_zero hc (ne_of_gt hR.2.2.2.2)
  have hdeg : (C c * R).natDegree = 2 * Fintype.card E + 2 := by
    rw [natDegree_C_mul hc]
    exact hR.1
  have hqdeg : (C c * Q).natDegree = 2 * Fintype.card E + 2 - oddCount d := by
    rw [natDegree_C_mul hc]
    exact allocation_quotient_degree d r w _ hdp hw hR.1
  refine ⟨hp, hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp]; exact hdeg
  · rw [hp]; exact mul_ne_zero hC hR.2.1
  · rw [hp]; exact hlead
  · rw [hp, hmult, hodd]
  · have hmreal : (physicalCoefficient src tgt).rootMultiplicity 1 =
        oddCount (fun v => (treeGraph src tgt).degree v) := by rw [hp,hmult,hodd]
    have heq := Polynomial.eq_rootMultiplicity_map (p := physicalCoefficient src tgt)
      (f := algebraMap ℝ ℂ) (RingHom.injective _) (1 : ℝ)
    simpa only [map_one] using heq.symm.trans hmreal
  · rw [hp]; exact hconst
  · rw [hp, eval_mul, eval_C]; exact mul_ne_zero hc hnegR
  · intro x hx
    rw [hp] at hx
    have heval : complexEval R x = 0 := by
      have hx' : (c : ℂ) * complexEval R x = 0 := by simpa [complexEval] using hx
      exact (mul_eq_zero.mp hx').resolve_left (by exact_mod_cast hc)
    exact treeAllocation_unit_circle src tgt hloop hsimple hd hi x heval
  · rw [hp, ← hodd]
    change C c * R = (1 - X) ^ oddCount d * (C c * Q)
    rw [hfactor]; ring
  · change (C c * Q).natDegree = _
    rw [hqdeg, hodd]
  · change (C c * Q).eval 1 ≠ 0
    rw [eval_mul, eval_C]; exact mul_ne_zero hc (ne_of_gt hQpos)
  · change (C c * Q).eval (-1) ≠ 0
    rw [eval_mul, eval_C]; exact mul_ne_zero hc hnegQ
  · intro x hx
    have hzero : complexEval (C c * Q) x = 0 := hx
    have hQzero : complexEval Q x = 0 := by
      have hh : (c : ℂ) * complexEval Q x = 0 := by simpa [complexEval] using hzero
      exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast hc)
    have hz : complexEval R x = 0 := by
      rw [hfactor]
      simp only [complexEval,eval₂_mul]
      change complexEval ((1 - X) ^ oddCount d) x * complexEval Q x = 0
      rw [hQzero,mul_zero]
    refine ⟨treeAllocation_unit_circle src tgt hloop hsimple hd hi x hz, ?_, ?_⟩
    · intro hxone
      rw [hxone] at hQzero
      have hcast : complexEval Q ((1 : ℝ) : ℂ) = 0 := by
        simpa only [Complex.ofReal_one] using hQzero
      rw [complexEval_real] at hcast
      exact (ne_of_gt hQpos) (by exact_mod_cast hcast)
    · intro hxneg
      rw [hxneg] at hQzero
      have hcast : complexEval Q ((-1 : ℝ) : ℂ) = 0 := by
        simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hQzero
      rw [complexEval_real] at hcast
      exact hnegQ (by exact_mod_cast hcast)
  · rw [hb, homogenize_axis, ← hdeg, ← hp, coeff_natDegree]
    intro hz
    have hleadne : (physicalCoefficient src tgt).leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero.mpr (by rw [hp]; exact mul_ne_zero hC hR.2.1)
    exact hleadne hz

  · intro x hx
    rw [hb, homogenize_complex_infinity]
    apply mul_ne_zero _ (pow_ne_zero _ hx)
    have heq : (physicalCoefficient src tgt).coeff (2 * Fintype.card E + 2) ≠ 0 := by
      rw [← hdeg, ← hp, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (by rw [hp]; exact mul_ne_zero hC hR.2.1)
    exact_mod_cast heq
  · intro x hx hz
    have hdegree : (physicalCoefficient src tgt).natDegree ≤ 2 * Fintype.card E + 2 := by
      rw [hp,hdeg]
    rw [hb, homogenize_complex_eval _ _ hdegree x hx] at hz
    have hz' := (mul_eq_zero.mp hz).resolve_right (pow_ne_zero _ hx)
    rw [hp] at hz'
    have hr : complexEval R (x 0 / x 1) = 0 := by
      have hh : (c : ℂ) * complexEval R (x 0 / x 1) = 0 := by
        simpa [complexEval] using hz'
      exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast hc)
    exact treeAllocation_unit_circle src tgt hloop hsimple hd hi _ hr

end Complete
end FiolArbitraryTreePair
