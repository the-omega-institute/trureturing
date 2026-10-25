/- UNCOMPILED source-only assembly. No validation claim. -/
import D5.S3.Geometry.Hyperideal.ActualCornerTransport
import Mathlib.Order.Setoid.Basic
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Submodule.Map

-- BEGIN unchanged averaging source body (imports hoisted).

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

-- END averaging source body.

namespace CFMPActualEndpointMultiplicity435Transient
-- BEGIN endpoint source body (imports hoisted; anonymous head bound only).
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
theorem endpoint_source {T K : Type*} [Fintype T]
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
      rw [Finset.map_erase, Finset.map_univ_equiv]
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
    simp [E0, Multiset.count_cons, eq_comm, add_comm]

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
    by_cases hx : L x = z <;> by_cases hy : L y = z <;> simp [hx, hy]
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

-- END endpoint source body.
end CFMPActualEndpointMultiplicity435Transient

-- UNCOMPILED anonymous exact application on the original ACT carriers.
-- The two provisional dependencies are mechanically included once above.
example {T K : Type*} [Fintype T]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] (q : Pairing T) :
    let m := FunOnFinite.linearMap K K (P q)
    let s := FunOnFinite.linearMap K K (label q)
    ∃ qlin : (Occurrence T → K) →ₗ[K] (Corner T → K),
      (∀ a, qlin a = Q a) ∧
      (∀ a, m a = M q a) ∧
      (∀ h z, s h z = ∑ c : Corner T, if label q c = z then h c else 0) ∧
      Function.Surjective m ∧ Function.Surjective s ∧
      m.ker.map qlin = s.ker ∧
      (∀ h : Corner T → K,
        (∃ a : Occurrence T → K, M q a = 0 ∧ Q a = h) ↔
          ∀ z : Vertex q, (∑ c : Corner T, if label q c = z then h c else 0) = 0) ∧
      Module.finrank K m.range = Fintype.card (GlobalEdge q) ∧
      Module.finrank K s.range = Fintype.card (Vertex q) ∧
      Module.finrank K m.ker + Fintype.card (GlobalEdge q) = 6 * Fintype.card T ∧
      Module.finrank K s.ker + Fintype.card (Vertex q) = 4 * Fintype.card T ∧
      Module.finrank K m.ker = 6 * Fintype.card T - Fintype.card (GlobalEdge q) ∧
      Module.finrank K (qlin.domRestrict m.ker).range + Fintype.card (Vertex q) =
        4 * Fintype.card T ∧
      Module.finrank K (qlin.domRestrict m.ker).range =
        4 * Fintype.card T - Fintype.card (Vertex q) ∧
      Module.finrank K (m.ker ⊓ qlin.ker) + Fintype.card (GlobalEdge q) =
        2 * Fintype.card T + Fintype.card (Vertex q) ∧
      Module.finrank K (m.ker ⊓ qlin.ker) =
        (2 * Fintype.card T + Fintype.card (Vertex q)) - Fintype.card (GlobalEdge q) ∧
      (Module.finrank K (m.ker ⊓ qlin.ker) : ℤ) =
        2 * (Fintype.card T : ℤ) - (Fintype.card (GlobalEdge q) : ℤ) +
          (Fintype.card (Vertex q) : ℤ) := by
  classical
  dsimp only
  let m := FunOnFinite.linearMap K K (P q)
  let s := FunOnFinite.linearMap K K (label q)
  let qlin : (Occurrence T → K) →ₗ[K] (Corner T → K) := {
    toFun := Q
    map_add' := by
      intro a a'
      funext c
      change Q (a + a') c = Q a c + Q a' c
      simp only [Q, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    map_smul' := by
      intro r a
      funext c
      change Q (r • a) c = r * Q a c
      simp only [Q, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp }
  have q_eval (a : Occurrence T → K) : qlin a = Q a := rfl
  have m_eval (a : Occurrence T → K) : m a = M q a := by
    funext e
    rw [FunOnFinite.linearMap_apply_apply]
    exact Finset.sum_filter _ _
  have s_eval (h : Corner T → K) (z : Vertex q) :
      s h z = ∑ c : Corner T, if label q c = z then h c else 0 := by
    rw [FunOnFinite.linearMap_apply_apply]
    exact Finset.sum_filter _ _

  -- Generic finite pushforward surjectivity, bound locally from the pinned API.
  have pushforward_surjective {X Y : Type*} [Finite X] [Finite Y]
      (f : X → Y) (hf : Function.Surjective f) :
      Function.Surjective (FunOnFinite.linearMap K K f) := by
    intro v
    obtain ⟨u, hu⟩ := Finsupp.mapDomain_surjective (M := K) hf
      ((Finsupp.linearEquivFunOnFinite K K Y).symm v)
    refine ⟨(Finsupp.linearEquivFunOnFinite K K X) u, ?_⟩
    change (Finsupp.linearEquivFunOnFinite K K Y)
      (Finsupp.mapDomain f
        ((Finsupp.linearEquivFunOnFinite K K X).symm
          ((Finsupp.linearEquivFunOnFinite K K X) u))) = v
    rw [LinearEquiv.symm_apply_apply, hu, LinearEquiv.apply_symm_apply]
  have m_surjective : Function.Surjective m :=
    pushforward_surjective (P q) (fun z => Quotient.exists_rep z)
  have s_surjective : Function.Surjective s :=
    pushforward_surjective (label q) (fun z => Quotient.exists_rep z)

  -- One application of the mechanically bound endpoint source; its proof is unchanged.
  obtain ⟨E, _E_eval, conservation, _necessity⟩ :=
    CFMPActualEndpointMultiplicity435Transient.endpoint_source (K := K) q
  have signed_image (h : Corner T → K) :
      (∃ a : Occurrence T → K, M q a = 0 ∧ Q a = h) ↔
        ∀ z : Vertex q, (∑ c : Corner T, if label q c = z then h c else 0) = 0 := by
    constructor
    · rintro ⟨a, hM, rfl⟩ z
      rw [conservation a z, hM]
      simp
    · intro hz
      let C : K := ∑ c : Corner T, |h c|
      let d : Corner T → K := fun c => C + h c
      have hd (c : Corner T) : 0 ≤ d c := by
        have hb : |h c| ≤ C :=
          Finset.single_le_sum (fun c _ => abs_nonneg (h c)) (Finset.mem_univ c)
        have hn := neg_abs_le (h c)
        dsimp only [d]
        linarith
      have deficit_eq (z : Vertex q) :
          CFMPExactComponentAverage435Transient.deficit q d z =
            (CFMPExactComponentAverage435Transient.size q z : K) * C := by
        unfold CFMPExactComponentAverage435Transient.deficit
        simp only [d, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
        have hh : (∑ c : CFMPExactComponentAverage435Transient.Fiber q z, h c.val) = 0 := by
          rw [CFMPExactComponentAverage435Transient.sum_fiber]
          exact hz z
        simpa only [hh, add_zero, CFMPExactComponentAverage435Transient.size]
      have hmax (z : Vertex q) :
          CFMPExactComponentAverage435Transient.deficit q d z ≤ ∑ c : Corner T, d c := by
        change (∑ c : CFMPExactComponentAverage435Transient.Fiber q z, d c.val) ≤ _
        rw [CFMPExactComponentAverage435Transient.sum_fiber]
        apply Finset.sum_le_sum
        intro c _
        split_ifs
        · exact le_rfl
        · exact hd c
      obtain ⟨paths, _, _, _, _, _, _, _, _, _, _, hM, hQ, _⟩ :=
        CFMPExactComponentAverage435Transient.actual_component_average
          q d hd (1 : K) (by positivity) (∑ c : Corner T, d c) hmax
      let a : Occurrence T → K :=
        lift q paths (CFMPExactComponentAverage435Transient.weight q d (1 : K))
      refine ⟨a, funext hM, ?_⟩
      funext c
      have hf : (CFMPExactComponentAverage435Transient.size q (label q c) : K) ≠ 0 := by
        exact_mod_cast (CFMPExactComponentAverage435Transient.size_pos q (label q c)).ne'
      have he : -Q a c = -h c := by
        calc
          -Q a c = (1 : K) *
              (CFMPExactComponentAverage435Transient.deficit q d (label q c) /
                (CFMPExactComponentAverage435Transient.size q (label q c) : K) - d c) :=
            hQ c
          _ = -h c := by
            rw [deficit_eq]
            dsimp only [d]
            field_simp [hf] <;> ring
      exact neg_injective he

  have image_eq : m.ker.map qlin = s.ker := by
    ext h
    change (∃ a, a ∈ m.ker ∧ qlin a = h) ↔ s h = 0
    constructor
    · rintro ⟨a, ha, hqa⟩
      have hM : M q a = 0 := (m_eval a).symm.trans (LinearMap.mem_ker.mp ha)
      have hQ : Q a = h := (q_eval a).symm.trans hqa
      funext z
      rw [s_eval]
      exact (signed_image h).mp ⟨a, hM, hQ⟩ z
    · intro hs
      have hz (z : Vertex q) : (∑ c : Corner T, if label q c = z then h c else 0) = 0 := by
        calc
          _ = s h z := (s_eval h z).symm
          _ = 0 := congrFun hs z
      obtain ⟨a, hM, hQ⟩ := (signed_image h).mpr hz
      refine ⟨a, LinearMap.mem_ker.mpr ?_, ?_⟩
      · exact (m_eval a).trans hM
      · exact (q_eval a).trans hQ

  have m_rank : Module.finrank K m.range = Fintype.card (GlobalEdge q) := by
    rw [LinearMap.range_eq_top.mpr m_surjective, finrank_top, Module.finrank_pi]
  have s_rank : Module.finrank K s.range = Fintype.card (Vertex q) := by
    rw [LinearMap.range_eq_top.mpr s_surjective, finrank_top, Module.finrank_pi]
  have m_nullity : Module.finrank K m.ker + Fintype.card (GlobalEdge q) =
      6 * Fintype.card T := by
    have hr := m.finrank_range_add_finrank_ker
    rw [m_rank, Module.finrank_pi] at hr
    simpa only [Occurrence, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm,
      Nat.add_comm] using hr
  have s_nullity : Module.finrank K s.ker + Fintype.card (Vertex q) =
      4 * Fintype.card T := by
    have hr := s.finrank_range_add_finrank_ker
    rw [s_rank, Module.finrank_pi] at hr
    simpa only [Corner, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm,
      Nat.add_comm] using hr

  let common : Submodule K (Occurrence T → K) := m.ker ⊓ qlin.ker
  have restricted_kernel : (qlin.domRestrict m.ker).ker = common.comap m.ker.subtype := by
    rw [LinearMap.ker_domRestrict]
    ext a
    change (a.val ∈ qlin.ker) ↔ (a.val ∈ m.ker ∧ a.val ∈ qlin.ker)
    exact ⟨fun ha => ⟨a.property, ha⟩, fun ha => ha.2⟩
  have restricted_finrank : Module.finrank K (qlin.domRestrict m.ker).ker =
      Module.finrank K common := by
    rw [restricted_kernel]
    exact (Submodule.comapSubtypeEquivOfLe
      (show common ≤ m.ker from inf_le_left)).finrank_eq
  have restricted_nullity : Module.finrank K s.ker + Module.finrank K common =
      Module.finrank K m.ker := by
    have hr := (qlin.domRestrict m.ker).finrank_range_add_finrank_ker
    rw [LinearMap.range_domRestrict, image_eq, restricted_finrank] at hr
    exact hr
  have m_natural_nullity : Module.finrank K m.ker =
      6 * Fintype.card T - Fintype.card (GlobalEdge q) := by
    omega
  have image_additive_dimension : Module.finrank K (qlin.domRestrict m.ker).range +
      Fintype.card (Vertex q) = 4 * Fintype.card T := by
    rw [LinearMap.range_domRestrict, image_eq]
    exact s_nullity
  have image_natural_dimension : Module.finrank K (qlin.domRestrict m.ker).range =
      4 * Fintype.card T - Fintype.card (Vertex q) := by
    omega
  have additive_dimension : Module.finrank K common + Fintype.card (GlobalEdge q) =
      2 * Fintype.card T + Fintype.card (Vertex q) := by
    omega
  have natural_dimension : Module.finrank K common =
      (2 * Fintype.card T + Fintype.card (Vertex q)) - Fintype.card (GlobalEdge q) := by
    omega
  have integer_dimension : (Module.finrank K common : ℤ) =
      2 * (Fintype.card T : ℤ) - (Fintype.card (GlobalEdge q) : ℤ) +
        (Fintype.card (Vertex q) : ℤ) := by
    have hadd : (Module.finrank K common : ℤ) + (Fintype.card (GlobalEdge q) : ℤ) =
        2 * (Fintype.card T : ℤ) + (Fintype.card (Vertex q) : ℤ) := by
      exact_mod_cast additive_dimension
    omega
  exact ⟨qlin, q_eval, m_eval, s_eval, m_surjective, s_surjective, image_eq,
    signed_image, m_rank, s_rank, m_nullity, s_nullity, m_natural_nullity,
    image_additive_dimension, image_natural_dimension, additive_dimension, natural_dimension, integer_dimension⟩
