/- SOURCE PREPARATION ONLY. Entire file UNCOMPILED, including the reused candidates.
   No axiom-closure or elaboration claim is made. No canonical module is proposed.
   Original: CFMP 42.1, occurrence maps in 41, actual pairing in 42.3.
   mathlib manifest pin: 56a005855ea17e0b0958f73ec801ae140b0a1679.
   Candidate averaging SHA256: 0f7bddacadb1fc839ebe6ae80dc3570c3160d91999996b9919bb32fd819d069f.
   Candidate endpoint SHA256: 7ea8587833423ea7adafe05115e29bd1f574cd69a6c5432caa8c85be51e3bda3.
   Each candidate body is included ONCE below. Only imports are hoisted;
   the endpoint anonymous example receives a transient name and namespace.
   The new bridge starts after END REUSED ENDPOINT CANDIDATE.
-/

import D5.S3.Geometry.Hyperideal.ActualCornerTransport
import Mathlib.Order.Setoid.Basic
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max

-- BEGIN REUSED AVERAGING CANDIDATE

/-! Temporary exact application on every actual same-fiber ordered pair. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open D5.S3.Geometry.Hyperideal.ActualCornerTransport

namespace CFMPExactComponentAverage435Transient

variable {T K : Type*} [Fintype T]
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

abbrev Fiber (q : Pairing T) (z : Vertex q) := {c : Corner T // label q c = z}
abbrev Index (q : Pairing T) := Σ z : Vertex q, Fiber q z × Fiber q z

def source (q : Pairing T) (s : Index q) : Corner T := s.2.1.val
def target (q : Pairing T) (s : Index q) : Corner T := s.2.2.val

def size (q : Pairing T) (z : Vertex q) : ℕ := by
  classical
  exact Fintype.card (Fiber q z)

def deficit (q : Pairing T) (d : Corner T → K) (z : Vertex q) : K := by
  classical
  exact ∑ c : Fiber q z, d c.val

def weight (q : Pairing T) (d : Corner T → K) (tau : K) (s : Index q) : K :=
  tau * d (target q s) / (size q s.1 : K)

theorem fiber_nonempty (q : Pairing T) (z : Vertex q) : Nonempty (Fiber q z) := by
  obtain ⟨c,hc⟩ := Quotient.exists_rep z
  exact ⟨⟨c,hc⟩⟩

theorem size_pos (q : Pairing T) (z : Vertex q) : 0 < size q z := by
  classical
  letI : Nonempty (Fiber q z) := fiber_nonempty q z
  exact Fintype.card_pos

theorem sum_fiber (q : Pairing T) (z : Vertex q) (f : Corner T → K) :
    (∑ c : Fiber q z, f c.val) =
      ∑ c : Corner T, if label q c = z then f c else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

theorem sum_fiber_indicator (q : Pairing T) (z : Vertex q) (c : Corner T)
    (f : Corner T → K) :
    (∑ u : Fiber q z, if u.val = c then f u.val else 0) =
      if label q c = z then f c else 0 := by
  classical
  rw [sum_fiber q z (fun u : Corner T => if u = c then f u else 0)]
  have he (u : Corner T) :
      (if label q u = z then (if u = c then f u else 0) else 0) =
        if u = c then (if label q c = z then f c else 0) else 0 := by
    by_cases hu : u = c <;> simp [hu]
  simp_rw [he]
  simp

theorem sum_weights (q : Pairing T) (d : Corner T → K) (tau : K)
    (z : Vertex q) :
    (∑ u : Fiber q z, ∑ v : Fiber q z,
      tau * d v.val / (size q z : K)) = tau * deficit q d z := by
  classical
  have hf : (size q z : K) ≠ 0 := by exact_mod_cast (size_pos q z).ne'
  have hin : (∑ v : Fiber q z, tau * d v.val / (size q z : K)) =
      tau * deficit q d z / (size q z : K) := by
    rw [← Finset.sum_div,← Finset.mul_sum]
    rfl
  simp_rw [hin]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change (size q z : K) * (tau * deficit q d z / (size q z : K)) = _
  field_simp

theorem exact_mass (q : Pairing T) (d : Corner T → K) (tau : K)
    (z : Vertex q) :
    mass q (source q) (weight q d tau) z = tau * deficit q d z := by
  classical
  unfold mass
  rw [Fintype.sum_sigma]
  have hi (a : Vertex q) (p : Fiber q a × Fiber q a) :
      (if label q (source q ⟨a,p⟩) = z then weight q d tau ⟨a,p⟩ else 0) =
        if a = z then tau * d p.2.val / (size q a : K) else 0 := by
    simp only [source,weight,target,p.1.property]
  simp_rw [hi,Fintype.sum_prod_type]
  simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  exact sum_weights q d tau z

theorem exact_demand (q : Pairing T) (d : Corner T → K) (tau : K)
    (c : Corner T) :
    (∑ s : Index q, weight q d tau s *
      ((if source q s = c then 1 else 0) - (if target q s = c then 1 else 0))) =
      tau * (deficit q d (label q c) / (size q (label q c) : K) - d c) := by
  classical
  have source_sum :
      (∑ s : Index q, weight q d tau s * (if source q s = c then 1 else 0)) =
        tau * deficit q d (label q c) / (size q (label q c) : K) := by
    rw [Fintype.sum_sigma]
    simp only [Fintype.sum_prod_type]
    have hterm (z : Vertex q) (u v : Fiber q z) :
        weight q d tau ⟨z,(u,v)⟩ *
          (if source q ⟨z,(u,v)⟩ = c then 1 else 0) =
        if u.val = c then tau * d v.val / (size q z : K) else 0 := by
      by_cases hu : u.val = c
      · have hs : source q ⟨z,(u,v)⟩ = c := hu
        rw [if_pos hs,if_pos hu,mul_one]
        rfl
      · have hs : source q ⟨z,(u,v)⟩ ≠ c := hu
        rw [if_neg hs,if_neg hu,mul_zero]
    simp_rw [hterm]
    conv_lhs =>
      arg 2; ext z
      rw [Finset.sum_comm]
      arg 2; ext v
      rw [sum_fiber_indicator q z c (fun _ => tau * d v.val / (size q z : K))]
    simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
    simp only [← Finset.sum_div,← Finset.mul_sum,deficit]
  have target_sum :
      (∑ s : Index q, weight q d tau s * (if target q s = c then 1 else 0)) =
        tau * d c := by
    rw [Fintype.sum_sigma]
    simp only [Fintype.sum_prod_type]
    have hterm (z : Vertex q) (u v : Fiber q z) :
        weight q d tau ⟨z,(u,v)⟩ *
          (if target q ⟨z,(u,v)⟩ = c then 1 else 0) =
        if v.val = c then tau * d v.val / (size q z : K) else 0 := by
      by_cases hv : v.val = c
      · have ht : target q ⟨z,(u,v)⟩ = c := hv
        rw [if_pos ht,if_pos hv,mul_one]
        rfl
      · have ht : target q ⟨z,(u,v)⟩ ≠ c := hv
        rw [if_neg ht,if_neg hv,mul_zero]
    simp_rw [hterm]
    conv_lhs =>
      arg 2; ext z
      arg 2; ext u
      rw [sum_fiber_indicator q z c (fun v => tau * d v / (size q z : K))]
    simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
    have hf : (size q (label q c) : K) ≠ 0 := by
      exact_mod_cast (size_pos q (label q c)).ne'
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    change (size q (label q c) : K) * (tau * d c / (size q (label q c) : K)) = _
    field_simp
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  rw [source_sum,target_sum]
  ring

theorem actual_component_average (q : Pairing T) (d : Corner T → K)
    (hd : ∀ c, 0 ≤ d c) (tau : K) (htau : 0 ≤ tau)
    (Dmax : K) (hmax : ∀ z, deficit q d z ≤ Dmax) :
    ∃ paths : Index q → List (Slot T),
      (∀ s, Follows q (source q s) (target q s) (paths s)) ∧
      (∀ s, (source q s :: (paths s).map (fun i => b (J q i))).Nodup) ∧
      (∀ s, source q s = target q s → paths s = []) ∧
      (∀ s i, (paths s).count i ≤ 1) ∧
      (∀ s i, chi q paths s (J q i) = -chi q paths s i) ∧
      (∀ s i, |chi q paths s i| ≤ 1) ∧
      (∀ s i, label q (b i) ≠ label q (source q s) → chi q paths s i = 0) ∧
      (∀ s c, ∑ i : Slot T, (chi q paths s i : K) * (if b i = c then 1 else 0) =
        (if source q s = c then 1 else 0) - (if target q s = c then 1 else 0)) ∧
      (∀ i, load q paths (weight q d tau) (J q i) = -load q paths (weight q d tau) i) ∧
      (∀ i, |load q paths (weight q d tau) i| ≤ tau * deficit q d (label q (b i))) ∧
      (∀ e, M q (lift q paths (weight q d tau)) e = 0) ∧
      (∀ c, -Q (lift q paths (weight q d tau)) c =
        tau * (deficit q d (label q c) / (size q (label q c) : K) - d c)) ∧
      (∀ o, |lift q paths (weight q d tau) o| ≤ 3 * tau * Dmax) := by
  classical
  have hs (s : Index q) : label q (source q s) = label q (target q s) :=
    s.2.1.property.trans s.2.2.property.symm
  have hw (s : Index q) : 0 ≤ weight q d tau s :=
    div_nonneg (mul_nonneg htau (hd _)) (Nat.cast_nonneg _)
  have hm (z : Vertex q) : mass q (source q) (weight q d tau) z ≤ tau * Dmax := by
    rw [exact_mass]
    exact mul_le_mul_of_nonneg_left (hmax z) htau
  have h := actual_corner_transport q (source q) (target q) (weight q d tau) hs hw
    (tau * Dmax) hm
  rcases h with ⟨paths,hfollow,hnodup,hnil,hcount,hanti,hchi,hsupport,hdiv,
    hloadanti,hload,hM,hQ,hbound⟩
  refine ⟨paths,hfollow,hnodup,hnil,hcount,hanti,hchi,hsupport,hdiv,hloadanti,?_,hM,?_,?_⟩
  · intro i
    simpa only [exact_mass] using hload i
  · intro c
    rw [hQ,exact_demand]
  · intro o
    simpa only [mul_assoc] using hbound o

theorem total_weight_bound {S : Type*} [Fintype S] (q : Pairing T)
    (u v : S → Corner T) (w : S → K)
    (hs : ∀ s, label q (u s) = label q (v s)) (hw : ∀ s, 0 ≤ w s) :
    Transport q u v w (∑ s, w s) := by
  classical
  apply actual_corner_transport q u v w hs hw
  intro z
  unfold mass
  apply Finset.sum_le_sum
  intro s _
  split_ifs
  · exact le_rfl
  · exact hw s

theorem empty_tetrahedra {S : Type*} [Fintype S] [IsEmpty T] (q : Pairing T)
    (u v : S → Corner T) (w : S → K)
    (hs : ∀ s, label q (u s) = label q (v s)) (hw : ∀ s, 0 ≤ w s) (B : K) :
    Transport q u v w B := by
  apply actual_corner_transport q u v w hs hw
  intro z
  induction z using Quotient.inductionOn with
  | h c => exact isEmptyElim c.1

theorem rational_component_average (q : Pairing T) (d : Corner T → ℚ)
    (hd : ∀ c, 0 ≤ d c) (tau : ℚ) (htau : 0 ≤ tau)
    (Dmax : ℚ) (hmax : ∀ z, deficit q d z ≤ Dmax) :
    ∃ a : Occurrence T → ℚ,
      (∀ e, M q a e = 0) ∧
      (∀ c, -Q a c =
        tau * (deficit q d (label q c) / (size q (label q c) : ℚ) - d c)) ∧
      (∀ o, |a o| ≤ 3 * tau * Dmax) := by
  obtain ⟨paths,_,_,_,_,_,_,_,_,_,_,hM,hQ,hbound⟩ :=
    actual_component_average q d hd tau htau Dmax hmax
  exact ⟨lift q paths (weight q d tau),hM,hQ,hbound⟩

#print axioms actual_component_average
#print axioms rational_component_average
end CFMPExactComponentAverage435Transient

-- END REUSED AVERAGING CANDIDATE

-- BEGIN REUSED ENDPOINT CANDIDATE
/- Transient anonymous application check. UNCOMPILED.
   No GID, canonical declaration, Scribe addition, or registration is proposed.
   Source target: exact ACT Pairing; mathlib manifest pin 56a005855ea17e0b0958f73ec801ae140b0a1679.
   All local steps are prospective bind-only applications/normalizations.
   The existing ACT Scribe paragraphs 42.1 already give the mathematical exposition. -/


set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open D5.S3.Geometry.Hyperideal.ActualCornerTransport

-- The multiset computation rule retains both entries even when their labels agree.
-- Conservation quantifies over arbitrary signed h. Necessity quantifies over any a.
namespace CFMPActualEndpoint435Transient

theorem endpoint_multiplicity {T K : Type*} [Fintype T]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] (q : Pairing T) :
    ∃ E : GlobalEdge q → Multiset (Vertex q),
      (∀ o : Occurrence T, E (P q o) =
        label q (o.1, (endpoints o.2).1) ::ₘ
          label q (o.1, (endpoints o.2).2) ::ₘ 0) ∧
      (∀ (h : Occurrence T → K) (z : Vertex q),
        (∑ c : Corner T, if label q c = z then Q h c else 0) =
          ∑ e : GlobalEdge q, ((E e).count z : K) * M q h e) ∧
      (∀ (a a0 : Occurrence T → K), M q a = M q a0 →
        (∀ c : Corner T, Q a c < 1) → ∀ z : Vertex q,
          0 < ∑ c : Corner T with label q c = z, (1 - Q a0 c)) := by
  classical
  let E0 : Occurrence T → Multiset (Vertex q) := fun o =>
    label q (o.1, (endpoints o.2).1) ::ₘ
      label q (o.1, (endpoints o.2).2) ::ₘ 0

  -- Only closed Fin 4 / Fin 3 table normalization occurs here.
  have table (f : Fin 4) (r : Fin 3) :
      ((endpoints (faceEdge f r)).1 ::ₘ
        (endpoints (faceEdge f r)).2 ::ₘ (0 : Multiset (Fin 4))) =
      ((Finset.univ.erase r).val.map (faceVertex f)) := by
    fin_cases f <;> fin_cases r <;> decide
  have local_form (x : Corner T) (r : Fin 3) :
      E0 (edge (x, r)) =
        (Finset.univ.erase r).val.map (fun s => label q (b (x, s))) := by
    have ht := congrArg
      (Multiset.map (fun v : Fin 4 => label q (x.1, v))) (table x.2 r)
    simpa only [E0, edge, b, Multiset.map_cons, Multiset.map_zero,
      Multiset.map_map, Function.comp_apply] using ht

  -- The same arbitrary sigma transports the opposite slot and its complement.
  have complement (π : Equiv.Perm (Fin 3)) (r : Fin 3) :
      (Finset.univ.erase r).val.map π =
        (Finset.univ.erase (π r)).val := by
    have hc : (Finset.univ.erase r).map π.toEmbedding =
        Finset.univ.erase (π r) := by
      rw [Finset.map_erase, Finset.map_univ_equiv, Equiv.toEmbedding_apply]
    exact (Finset.map_val π.toEmbedding (Finset.univ.erase r)).symm.trans
      (congrArg Finset.val hc)
  have paired_label (x : Corner T) (s : Fin 3) :
      label q (b (x, s)) = label q (b (q.p x, q.sigma x s)) :=
    Quotient.sound (Relation.EqvGen.rel _ _ ⟨(x, s), rfl, rfl⟩)
  have generator (i : Slot T) : E0 (edge i) = E0 (edge (J q i)) := by
    change E0 (edge (i.1, i.2)) =
      E0 (edge (q.p i.1, q.sigma i.1 i.2))
    rw [local_form, local_form]
    calc
      _ = (Finset.univ.erase i.2).val.map
          (fun s => label q (b (q.p i.1, q.sigma i.1 s))) :=
        Multiset.map_congr rfl (fun s _ => paired_label i.1 s)
      _ = ((Finset.univ.erase i.2).val.map (q.sigma i.1)).map
          (fun s => label q (b (q.p i.1, s))) := by
        rw [Multiset.map_map]
        rfl
      _ = _ := by rw [complement]

  -- Apply the generic generated-equivalence theorem; do not reprove its induction.
  have respects : ∀ o p : Occurrence T,
      Relation.EqvGen (edgeRel q) o p → E0 o = E0 p := by
    letI : IsEquiv (Occurrence T) (fun o p => E0 o = E0 p) :=
      (Setoid.ker E0).iseqv.isEquiv
    exact Relation.EqvGen.eqvGen_le
      (r' := fun o p => E0 o = E0 p) (by
        rintro o p ⟨i, rfl, rfl⟩
        exact generator i)
  let E : GlobalEdge q → Multiset (Vertex q) := Quotient.lift E0 respects
  have E_eval (o : Occurrence T) : E (P q o) = E0 o := rfl
  let n : Vertex q → GlobalEdge q → ℕ := fun z e => (E e).count z
  have n_eval (z : Vertex q) (o : Occurrence T) :
      n z (P q o) =
        (if label q (o.1, (endpoints o.2).1) = z then 1 else 0) +
        (if label q (o.1, (endpoints o.2).2) = z then 1 else 0) := by
    change (E (P q o)).count z = _
    rw [E_eval]
    simp [E0, Multiset.count_cons, Multiset.count_singleton, eq_comm, add_comm]

  -- The two endpoints are distinct locally; no quotient-label inequality is used.
  have distinct (j : Fin 6) : (endpoints j).1 ≠ (endpoints j).2 := by
    fin_cases j <;> decide
  have incidence_one (L : Fin 4 → Vertex q) (x y : Fin 4)
      (hxy : x ≠ y) (z : Vertex q) (k : K) :
      (∑ v : Fin 4, if L v = z then
        (if v = x ∨ v = y then k else 0) else 0) =
      (((if L x = z then 1 else 0) +
        (if L y = z then 1 else 0) : ℕ) : K) * k := by
    have separate (v : Fin 4) :
        (if L v = z then (if v = x ∨ v = y then k else 0) else 0) =
        (if v = x then (if L x = z then k else 0) else 0) +
        (if v = y then (if L y = z then k else 0) else 0) := by
      by_cases hx : v = x
      · subst v
        simp [hxy]
      · by_cases hy : v = y
        · subst v
          simp [hx]
        · simp [hx, hy]
    simp_rw [separate, Finset.sum_add_distrib]
    by_cases hx : L x = z <;> by_cases hy : L y = z <;> simp [hx, hy, two_mul]
  have incidence (h : Occurrence T → K) (z : Vertex q) :
      (∑ c : Corner T, if label q c = z then Q h c else 0) =
        ∑ o : Occurrence T, (n z (P q o) : K) * h o := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    calc
      _ = ∑ v : Fin 4, ∑ j : Fin 6,
          if label q (t, v) = z then
            (if v = (endpoints j).1 ∨ v = (endpoints j).2 then h (t, j) else 0)
          else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : label q (t, v) = z <;> simp [Q, hv]
      _ = ∑ j : Fin 6, ∑ v : Fin 4,
          if label q (t, v) = z then
            (if v = (endpoints j).1 ∨ v = (endpoints j).2 then h (t, j) else 0)
          else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [n_eval]
        exact incidence_one (fun v => label q (t, v))
          (endpoints j).1 (endpoints j).2 (distinct j) z (h (t, j))
  have regroup (h : Occurrence T → K) (z : Vertex q) :
      (∑ e : GlobalEdge q, (n z e : K) * M q h e) =
        ∑ o : Occurrence T, (n z (P q o) : K) * h o := by
    calc
      _ = ∑ e : GlobalEdge q,
          ∑ o : Occurrence T with P q o = e, (n z (P q o) : K) * h o := by
        apply Finset.sum_congr rfl
        intro e _
        change (n z e : K) * (∑ o, if P q o = e then h o else 0) = _
        rw [← Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro o ho
        rw [(Finset.mem_filter.mp ho).2]
      _ = _ := Finset.sum_fiberwise Finset.univ (P q)
        (fun o => (n z (P q o) : K) * h o)
  have conservation (h : Occurrence T → K) (z : Vertex q) :
      (∑ c : Corner T, if label q c = z then Q h c else 0) =
        ∑ e : GlobalEdge q, (n z e : K) * M q h e :=
    (incidence h z).trans (regroup h z).symm

  refine ⟨E, (fun o => E_eval o), conservation, ?_⟩
  intro a a0 same strict z
  have summed :
      (∑ c : Corner T with label q c = z, Q a c) =
        ∑ c : Corner T with label q c = z, Q a0 c := by
    have hs := calc
      (∑ c : Corner T, if label q c = z then Q a c else 0) =
          ∑ e : GlobalEdge q, (n z e : K) * M q a e := conservation a z
      _ = ∑ e : GlobalEdge q, (n z e : K) * M q a0 e := by rw [same]
      _ = (∑ c : Corner T, if label q c = z then Q a0 c else 0) :=
        (conservation a0 z).symm
    simpa only [Finset.sum_filter] using hs
  have deficits :
      (∑ c : Corner T with label q c = z, (1 - Q a c)) =
        ∑ c : Corner T with label q c = z, (1 - Q a0 c) := by
    simp only [Finset.sum_sub_distrib]
    rw [summed]
  rw [← deficits]
  apply Finset.sum_pos
  · intro c _
    exact sub_pos.mpr (strict c)
  · obtain ⟨c, hc⟩ := Quotient.mk_surjective z
    exact ⟨c, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hc⟩

end CFMPActualEndpoint435Transient

-- END REUSED ENDPOINT CANDIDATE

/- The remaining declarations are transient consumed bridges/application checks.
   They do not propose new canonical declarations or duplicate the ACT Scribe.
   All proofs below, as well as both candidate dependencies above, are UNCOMPILED. -/

namespace CFMPActualStrictification435Transient

open CFMPExactComponentAverage435Transient
open CFMPActualEndpoint435Transient

variable {T K : Type*} [Fintype T]
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

-- Additivity of the actual finite occurrence sums over an ordered field.
-- The same identities apply over the real and rational fields.
private theorem add_M (q : Pairing T) (a h : Occurrence T → K)
    (e : GlobalEdge q) :
    M q (fun o => a o + h o) e = M q a e + M q h e := by
  classical
  unfold M
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : P q o = e <;> simp [ho]

private theorem add_Q (a h : Occurrence T → K) (c : Corner T) :
    Q (fun o => a o + h o) c = Q a c + Q h c := by
  classical
  unfold Q
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : c.2 = (endpoints j).1 ∨ c.2 = (endpoints j).2 <;> simp [hj]

private theorem deficit_filter (q : Pairing T) (d : Corner T → K)
    (z : Vertex q) :
    deficit q d z = ∑ c : Corner T with label q c = z, d c := by
  classical
  unfold deficit
  rw [sum_fiber, Finset.sum_filter]

-- This is the actual local incidence bridge, without a new combinatorial carrier.
private theorem occurrence_le_Q (a : Occurrence T → K)
    (ha : ∀ o, 0 ≤ a o) (o : Occurrence T) :
    a o ≤ Q a (o.1, (endpoints o.2).1) := by
  classical
  have h := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun j : Fin 6 =>
      if (endpoints o.2).1 = (endpoints j).1 ∨
          (endpoints o.2).1 = (endpoints j).2 then a (o.1, j) else 0)
    (fun j _ => by
      split_ifs
      · exact ha (o.1, j)
      · exact le_rfl)
    (Finset.mem_univ o.2)
  simpa [Q] using h

-- Nonemptiness belongs only to this helper and to the branch calling it.
-- Both extrema are attained, so their signs follow from the original data.
private theorem attained_extrema [Nonempty T] (q : Pairing T)
    (a0 : Occurrence T → K) (d : Corner T → K) :
    ∃ (omin : Occurrence T) (zmax : Vertex q),
      (∀ o, a0 omin ≤ a0 o) ∧
      (∀ z, deficit q d z ≤ deficit q d zmax) := by
  classical
  letI : Nonempty (Vertex q) :=
    ⟨label q (Classical.choice (inferInstance : Nonempty T), 0)⟩
  obtain ⟨omin, _, hmin⟩ :=
    (Finset.univ : Finset (Occurrence T)).exists_min_image a0 Finset.univ_nonempty
  obtain ⟨zmax, _, hmax⟩ :=
    (Finset.univ : Finset (Vertex q)).exists_max_image (deficit q d) Finset.univ_nonempty
  exact ⟨omin, zmax, (fun o => hmin o (Finset.mem_univ o)),
    (fun z => hmax z (Finset.mem_univ z))⟩

-- One parameter, one actual lift, and one resulting vector throughout.
-- The parameter can be any admissible element of the ordered field, including Q.
theorem strictification_at_parameter (q : Pairing T) (a0 : Occurrence T → K)
    (base_corner : ∀ c, Q a0 c ≤ 1)
    (classes : ∀ z, 0 < deficit q (fun c => 1 - Q a0 c) z)
    (m Dstar tau : K) (hm : 0 < m) (hDstar : 0 < Dstar)
    (hmin : ∀ o, m ≤ a0 o)
    (hmax : ∀ z, deficit q (fun c => 1 - Q a0 c) z ≤ Dstar)
    (htau : 0 < tau) (htau_half : tau ≤ 1 / 2)
    (htau_m : tau ≤ m / (6 * Dstar)) :
    ∃ (a : Occurrence T → K) (paths : Index q → List (Slot T)),
      a = (fun o => a0 o +
        lift q paths (weight q (fun c => 1 - Q a0 c) tau) o) ∧
      M q a = M q a0 ∧
      (∀ o, m / 2 ≤ a o) ∧
      (∀ o, 0 < a o ∧ a o < 1) ∧
      (∀ c,
        1 - Q a c = (1 - tau) * (1 - Q a0 c) +
          tau * (deficit q (fun u => 1 - Q a0 u) (label q c) /
            (size q (label q c) : K)) ∧
        tau * (deficit q (fun u => 1 - Q a0 u) (label q c) /
            (size q (label q c) : K)) ≤ 1 - Q a c ∧
        0 < 1 - Q a c) ∧
      (∀ o, |a o - a0 o| ≤ 3 * tau * Dstar) := by
  classical
  let d : Corner T → K := fun c => 1 - Q a0 c
  have hd (c : Corner T) : 0 ≤ d c := sub_nonneg.mpr (base_corner c)
  have hsmall : 3 * tau * Dstar ≤ m / 2 := by
    have hden : 0 < 6 * Dstar := mul_pos (by norm_num) hDstar
    have hmul := (le_div_iff₀ hden).mp htau_m
    nlinarith
  obtain ⟨paths, _, _, _, _, _, _, _, _, _, _, hM, hQ, hbound⟩ :=
    actual_component_average q d hd tau htau.le Dstar hmax
  let delta : Occurrence T → K := lift q paths (weight q d tau)
  let a : Occurrence T → K := fun o => a0 o + delta o
  have sameM : M q a = M q a0 := by
    funext e
    change M q (fun o => a0 o + delta o) e = M q a0 e
    rw [add_M, hM, add_zero]
  have lower (o : Occurrence T) : m / 2 ≤ a o := by
    have hb : |delta o| ≤ m / 2 := (hbound o).trans hsmall
    have hl := (abs_le.mp hb).1
    have ha0 := hmin o
    dsimp only [a]
    linarith
  have positive (o : Occurrence T) : 0 < a o :=
    (div_pos hm (by norm_num)).trans_le (lower o)
  have formula (c : Corner T) :
      1 - Q a c = (1 - tau) * d c +
        tau * (deficit q d (label q c) / (size q (label q c) : K)) := by
    calc
      1 - Q a c = d c + -Q delta c := by
        change 1 - Q (fun o => a0 o + delta o) c = (1 - Q a0 c) + -Q delta c
        rw [add_Q]
        ring
      _ = _ := by
        rw [show -Q delta c =
          tau * (deficit q d (label q c) / (size q (label q c) : K) - d c)
          from hQ c]
        ring
  have strict_deficit (c : Corner T) :
      tau * (deficit q d (label q c) / (size q (label q c) : K)) ≤
          1 - Q a c ∧ 0 < 1 - Q a c := by
    have hf : 0 < (size q (label q c) : K) := by
      exact_mod_cast size_pos q (label q c)
    have hp : 0 < tau * (deficit q d (label q c) / (size q (label q c) : K)) :=
      mul_pos htau (div_pos (classes _) hf)
    have hnonneg : 0 ≤ (1 - tau) * d c :=
      mul_nonneg (by linarith [htau_half]) (hd c)
    have hl : tau * (deficit q d (label q c) / (size q (label q c) : K)) ≤
        1 - Q a c := by
      rw [formula]
      exact le_add_of_nonneg_left hnonneg
    exact ⟨hl, hp.trans_le hl⟩
  have strict_corner (c : Corner T) : Q a c < 1 :=
    sub_pos.mp (strict_deficit c).2
  have angles (o : Occurrence T) : 0 < a o ∧ a o < 1 :=
    ⟨positive o, (occurrence_le_Q a (fun u => (positive u).le) o).trans_lt
      (strict_corner (o.1, (endpoints o.2).1))⟩
  refine ⟨a, paths, rfl, sameM, lower, angles, ?_, ?_⟩
  · intro c
    exact ⟨formula c, (strict_deficit c).1, (strict_deficit c).2⟩
  · intro o
    simpa only [a, add_sub_cancel_left] using hbound o

-- Pinned finite-Pi norm APIs require a nonnegative/positive real bound.
-- These statements remain valid when the occurrence type is empty.
private theorem finite_pi_distance_le_iff (a a0 : Occurrence T → ℝ)
    (r : ℝ) (hr : 0 ≤ r) :
    ‖a - a0‖ ≤ r ↔ ∀ o, |a o - a0 o| ≤ r := by
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    (pi_norm_le_iff_of_nonneg hr : ‖a - a0‖ ≤ r ↔ ∀ o, ‖(a - a0) o‖ ≤ r)

private theorem finite_pi_distance_lt_iff (a a0 : Occurrence T → ℝ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ‖a - a0‖ < epsilon ↔ ∀ o, |a o - a0 o| < epsilon := by
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    (pi_norm_lt_iff hepsilon :
      ‖a - a0‖ < epsilon ↔ ∀ o, ‖(a - a0) o‖ < epsilon)

-- This is the original real iff, including positive coordinates, strict upper
-- angles, strict corners, the same M, arbitrary real epsilon, and the empty case.
theorem real_strictification_iff (q : Pairing T) (a0 : Occurrence T → ℝ)
    (base_positive : ∀ o, 0 < a0 o) (base_corner : ∀ c, Q a0 c ≤ 1) :
    (∀ z : Vertex q,
      0 < ∑ c : Corner T with label q c = z, (1 - Q a0 c)) ↔
    ∀ epsilon : ℝ, 0 < epsilon → ∃ a : Occurrence T → ℝ,
      M q a = M q a0 ∧
      (∀ o, 0 < a o ∧ a o < 1) ∧
      (∀ c, Q a c < 1) ∧
      ‖a - a0‖ < epsilon := by
  classical
  constructor
  · intro classes epsilon hepsilon
    by_cases hT : Nonempty T
    · letI : Nonempty T := hT
      let d : Corner T → ℝ := fun c => 1 - Q a0 c
      have hD (z : Vertex q) : 0 < deficit q d z := by
        rw [deficit_filter]
        exact classes z
      obtain ⟨omin, zmax, hmin, hmax⟩ := attained_extrema q a0 d
      let m : ℝ := a0 omin
      let Dstar : ℝ := deficit q d zmax
      have hm : 0 < m := base_positive omin
      have hDs : 0 < Dstar := hD zmax
      have hden : 0 < 6 * Dstar := mul_pos (by norm_num) hDs
      let tau : ℝ := min (1 / 2) (min (m / (6 * Dstar)) (epsilon / (6 * Dstar)))
      have htau : 0 < tau :=
        lt_min (by norm_num) (lt_min (div_pos hm hden) (div_pos hepsilon hden))
      have htau_half : tau ≤ 1 / 2 := min_le_left _ _
      have htau_m : tau ≤ m / (6 * Dstar) :=
        (min_le_right _ _).trans (min_le_left _ _)
      have htau_epsilon : tau ≤ epsilon / (6 * Dstar) :=
        (min_le_right _ _).trans (min_le_right _ _)
      have hclose : 3 * tau * Dstar ≤ epsilon / 2 := by
        have hmul := (le_div_iff₀ hden).mp htau_epsilon
        nlinarith
      obtain ⟨a, paths, _ha, hM, _hlower, hangles, hdeficit, hbound⟩ :=
        strictification_at_parameter q a0 base_corner hD m Dstar tau
          hm hDs hmin hmax htau htau_half htau_m
      have hnorm_bound : ‖a - a0‖ ≤ 3 * tau * Dstar :=
        (finite_pi_distance_le_iff a a0 _ (by positivity)).mpr hbound
      refine ⟨a, hM, hangles, ?_, ?_⟩
      · intro c
        exact sub_pos.mp (hdeficit c).2.2
      · exact (hnorm_bound.trans hclose).trans_lt (by linarith)
    · letI : IsEmpty T := ⟨fun t => hT ⟨t⟩⟩
      refine ⟨a0, rfl, ?_, ?_, ?_⟩
      · intro o
        exact isEmptyElim o.1
      · intro c
        exact isEmptyElim c.1
      · simpa only [sub_self, norm_zero] using hepsilon
  · intro near
    obtain ⟨a, sameM, _angles, strict, _distance⟩ := near 1 (by norm_num)
    obtain ⟨_E, _endpoint, _conservation, necessary⟩ :=
      endpoint_multiplicity (K := ℝ) q
    exact necessary a a0 sameM strict

-- Cast the actual defining finite sums. Neither quotient nor occurrence carrier
-- changes with the scalar field, and repeated quotient labels remain repeated.
private theorem cast_M (q : Pairing T) (a : Occurrence T → ℚ) (e : GlobalEdge q) :
    M (K := ℝ) q (fun o => (a o : ℝ)) e =
      ((M (K := ℚ) q a e : ℚ) : ℝ) := by
  classical
  unfold M
  simp only [Rat.cast_sum, apply_ite, Rat.cast_zero]

private theorem cast_Q (a : Occurrence T → ℚ) (c : Corner T) :
    Q (K := ℝ) (fun o => (a o : ℝ)) c =
      ((Q (K := ℚ) a c : ℚ) : ℝ) := by
  classical
  unfold Q
  simp only [Rat.cast_sum, apply_ite, Rat.cast_zero]

-- Rational output is constructed by strictification_at_parameter at K=Q.
-- epsilon is an arbitrary positive REAL number, and tau is chosen in Q by density.
theorem rational_strictification_near (q : Pairing T) (a0 : Occurrence T → ℚ)
    (base_positive : ∀ o, 0 < a0 o) (base_corner : ∀ c, Q a0 c ≤ 1)
    (classes : ∀ z : Vertex q,
      0 < ∑ c : Corner T with label q c = z, (1 - Q a0 c))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ a : Occurrence T → ℚ,
      M q a = M q a0 ∧
      (∀ o, 0 < a o ∧ a o < 1) ∧
      (∀ c, Q a c < 1) ∧
      M q (fun o => (a o : ℝ)) = M q (fun o => (a0 o : ℝ)) ∧
      (∀ o, 0 < (a o : ℝ) ∧ (a o : ℝ) < 1) ∧
      (∀ c, Q (fun o => (a o : ℝ)) c < 1) ∧
      ‖(fun o => (a o : ℝ)) - (fun o => (a0 o : ℝ))‖ < epsilon := by
  classical
  by_cases hT : Nonempty T
  · letI : Nonempty T := hT
    let d : Corner T → ℚ := fun c => 1 - Q a0 c
    have hD (z : Vertex q) : 0 < deficit q d z := by
      rw [deficit_filter]
      exact classes z
    obtain ⟨omin, zmax, hmin, hmax⟩ := attained_extrema q a0 d
    let m : ℚ := a0 omin
    let Dstar : ℚ := deficit q d zmax
    have hm : 0 < m := base_positive omin
    have hDs : 0 < Dstar := hD zmax
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hDsR : 0 < (Dstar : ℝ) := by exact_mod_cast hDs
    have hden : 0 < 6 * (Dstar : ℝ) := mul_pos (by norm_num) hDsR
    let rho : ℝ := min (1 / 2)
      (min ((m : ℝ) / (6 * (Dstar : ℝ))) (epsilon / (6 * (Dstar : ℝ))))
    have hrho : 0 < rho :=
      lt_min (by norm_num) (lt_min (div_pos hmR hden) (div_pos hepsilon hden))
    obtain ⟨tau, htauR, htau_rho⟩ := exists_rat_btwn hrho
    have htau : (0 : ℚ) < tau := by exact_mod_cast htauR
    have htau_halfR : (tau : ℝ) ≤ 1 / 2 :=
      htau_rho.le.trans (min_le_left _ _)
    have htau_mR : (tau : ℝ) ≤ (m : ℝ) / (6 * (Dstar : ℝ)) :=
      htau_rho.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    have htau_epsilon : (tau : ℝ) ≤ epsilon / (6 * (Dstar : ℝ)) :=
      htau_rho.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have htau_half : tau ≤ (1 : ℚ) / 2 := by
      apply (Rat.cast_le (K := ℝ)).mp
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using htau_halfR
    have htau_m : tau ≤ m / (6 * Dstar) := by exact_mod_cast htau_mR
    have hclose : 3 * (tau : ℝ) * (Dstar : ℝ) ≤ epsilon / 2 := by
      have hmul := (le_div_iff₀ hden).mp htau_epsilon
      nlinarith
    obtain ⟨a, paths, _ha, hM, _hlower, hangles, hdeficit, hbound⟩ :=
      strictification_at_parameter q a0 base_corner hD m Dstar tau
        hm hDs hmin hmax htau htau_half htau_m
    have hcastM : M q (fun o => (a o : ℝ)) = M q (fun o => (a0 o : ℝ)) := by
      funext e
      rw [cast_M, cast_M, hM]
    have hcast_angles (o : Occurrence T) : 0 < (a o : ℝ) ∧ (a o : ℝ) < 1 := by
      constructor
      · exact_mod_cast (hangles o).1
      · exact_mod_cast (hangles o).2
    have hstrict (c : Corner T) : Q a c < 1 :=
      sub_pos.mp (hdeficit c).2.2
    have hcast_strict (c : Corner T) : Q (fun o => (a o : ℝ)) c < 1 := by
      rw [cast_Q]
      exact_mod_cast hstrict c
    have hcast_bound (o : Occurrence T) :
        |(a o : ℝ) - (a0 o : ℝ)| ≤ 3 * (tau : ℝ) * (Dstar : ℝ) := by
      exact_mod_cast hbound o
    have hnorm : ‖(fun o => (a o : ℝ)) - (fun o => (a0 o : ℝ))‖ < epsilon := by
      apply (finite_pi_distance_lt_iff _ _ epsilon hepsilon).mpr
      intro o
      exact ((hcast_bound o).trans hclose).trans_lt (by linarith)
    exact ⟨a, hM, hangles, hstrict, hcastM, hcast_angles, hcast_strict, hnorm⟩
  · letI : IsEmpty T := ⟨fun t => hT ⟨t⟩⟩
    refine ⟨a0, rfl, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · intro o
      exact isEmptyElim o.1
    · intro c
      exact isEmptyElim c.1
    · intro o
      exact isEmptyElim o.1
    · intro c
      exact isEmptyElim c.1
    · simpa only [sub_self, norm_zero] using hepsilon

#print axioms strictification_at_parameter
#print axioms real_strictification_iff
#print axioms rational_strictification_near

end CFMPActualStrictification435Transient
