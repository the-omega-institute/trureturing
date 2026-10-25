import D5.S3.Geometry.Hyperideal.ActualCornerTransport

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
