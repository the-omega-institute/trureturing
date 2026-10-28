/- GID: D5/S3/Observer/Linear/GainRayWordGeometry
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayWordGeometry
   mirror-E: none(waiver:literal-mixed-word-source-geometry)
   anchors: []
   utility: none
   digest: Both chronological switch orientations force three independent cumulative source directions. -/

import D5.S3.Observer.Linear.GainRayHistory

set_option autoImplicit false
noncomputable section
open scoped Matrix Classical
namespace D5.S3.Observer.Linear.GainRay

theorem action_m_shape : action false = !![0,1;1,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [action,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
    D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM]
theorem action_j_shape : action true = !![0,1;1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [action,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic]

theorem m_power_coordinates (k : ℕ) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 < b ∧
      action false ^ (k+1) = a • (1 : Mat) + b • action false := by
  have packet := (D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.result.2
    1 (by omega) (D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.atomicBlock (k+1))).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    (k+1) rfl
  have hv := packet.2.2.2.2.1 (by omega)
  have hp := packet.2.2.2.2.2.1
  refine ⟨(Nat.fib k : ℝ), (Nat.fib (k+1) : ℝ), Nat.cast_nonneg _,
    Nat.cast_pos.mpr (Nat.fib_pos.mpr (by omega)), ?_⟩
  have hm := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ =>
    A.map (Int.castRingHom ℝ)) hp.symm
  rw [Matrix.map_pow] at hm
  change action false ^ (k+1) = _ at hm
  rw [hm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.blockMatrix,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.step, hv, action_m_shape]

private theorem independent_IM (B : Mat) (hB : B 0 1 ≠ B 1 0) :
    LinearIndependent ℝ ![(1 : Mat), action false, B] := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have h00 := congrArg (fun X : Mat => X 0 0) hc
  have h01 := congrArg (fun X : Mat => X 0 1) hc
  have h10 := congrArg (fun X : Mat => X 1 0) hc
  simp [Fin.sum_univ_three, action_m_shape] at h00 h01 h10
  have hc2 : c 2 = 0 := by
    have hp : c 2 * (B 0 1 - B 1 0) = 0 := by nlinarith
    exact (mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr hB)
  have hc1 : c 1 = 0 := by simp [hc2] at h01; exact h01
  have hc0 : c 0 = 0 := by simp [hc2] at h00; exact h00
  intro i
  fin_cases i <;> simp [hc0,hc1,hc2]

private theorem independent_IJ (B : Mat)
    (hB : B 0 0 ≠ B 1 1 ∨ B 0 1 ≠ B 1 0) :
    LinearIndependent ℝ ![(1 : Mat), action true, B] := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have h00 := congrArg (fun X : Mat => X 0 0) hc
  have h01 := congrArg (fun X : Mat => X 0 1) hc
  have h10 := congrArg (fun X : Mat => X 1 0) hc
  have h11 := congrArg (fun X : Mat => X 1 1) hc
  simp [Fin.sum_univ_three, action_j_shape] at h00 h01 h10 h11
  have hc2 : c 2 = 0 := by
    rcases hB with hB | hB
    · have hp : c 2 * (B 0 0 - B 1 1) = 0 := by nlinarith
      exact (mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr hB)
    · have hp : c 2 * (B 0 1 - B 1 0) = 0 := by nlinarith
      exact (mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr hB)
  have hc1 : c 1 = 0 := by simp [hc2] at h01; exact h01
  have hc0 : c 0 = 0 := by simp [hc2] at h00; exact h00
  intro i
  fin_cases i <;> simp [hc0,hc1,hc2]

theorem first_switch_independent (a : Bool) (k : ℕ) (hk : 0 < k) :
    LinearIndependent ℝ ![(1 : Mat), action a, action (!a) * action a ^ k] := by
  cases a with
  | false =>
    obtain ⟨b,c,hb,hc,hp⟩ := m_power_coordinates (k-1)
    have hke : k-1+1 = k := by omega
    rw [hke] at hp
    apply independent_IM
    rw [hp]
    simpa [action_j_shape, action_m_shape, Matrix.mul_apply, Fin.sum_univ_two] using ne_of_gt hc
  | true =>
    have hj : action true ^ 2 = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [action_j_shape, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
    rw [pow_eq_pow_mod k hj]
    apply independent_IJ
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · left
      simp [h, action_m_shape]
    · right
      norm_num [h, action_j_shape, action_m_shape, Matrix.mul_apply, Fin.sum_univ_two]

theorem switch_decomposition (w : List Bool) (hM : false ∈ w) (hJ : true ∈ w) :
    ∃ a : Bool, ∃ k : ℕ, ∃ r : List Bool,
      0 < k ∧ w = List.replicate k a ++ ((!a) :: r) := by
  rcases List.eq_replicate_or_eq_replicate_append_cons w with
    h | ⟨k,a,h,hk⟩ | ⟨k,a,b,r,h,hk,hab⟩
  · simp [h] at hM
  · cases a <;> simp_all
  · have hb : b = !a := by cases a <;> cases b <;> simp_all
    exact ⟨a,k,r,hk,by simpa [hb] using h⟩

theorem first_switch_generators_mem (w : List Bool) (a : Bool) (k : ℕ)
    (r : List Bool) (hk : 0 < k) (hw : w = List.replicate k a ++ ((!a) :: r)) :
    let K := Submodule.span ℝ
      (Set.range (fun i : Fin (w.length+1) => acquisition (w.take i.val)))
    (1 : Mat) ∈ K ∧ action a ∈ K ∧ action (!a) * action a ^ k ∈ K := by
  let K := Submodule.span ℝ
    (Set.range (fun i : Fin (w.length+1) => acquisition (w.take i.val)))
  have hlen : k+1 ≤ w.length := by simp [hw]
  have h0 : (1 : Mat) ∈ K := by
    apply Submodule.subset_span
    exact ⟨⟨0,by omega⟩,by simp [acquisition,Raw,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word]⟩
  have h1 : action a ∈ K := by
    apply Submodule.subset_span
    refine ⟨⟨1,by omega⟩,?_⟩
    have he : w.take 1 = [a] := by
      rw [hw, List.take_append_of_le_length (by simp; omega)]
      simp [List.take_replicate, Nat.min_eq_left (by omega : 1 ≤ k)]
    change acquisition (w.take 1) = action a
    rw [he]
    simpa using acquisition_pure a 1
  have hswitch : action (!a) * action a ^ k ∈ K := by
    apply Submodule.subset_span
    refine ⟨⟨k+1,by omega⟩,?_⟩
    have he : w.take (k+1) = List.replicate k a ++ [!a] := by
      simp [hw, List.take_append]
    change acquisition (w.take (k+1)) = action (!a) * action a ^ k
    rw [he, acquisition_append, acquisition_pure]
  exact ⟨h0,h1,hswitch⟩

/-- A mixed literal trajectory has at least three source-observation directions. -/
theorem mixed_cumulative_span (w : List Bool) (hM : false ∈ w) (hJ : true ∈ w) :
    3 ≤ Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i : Fin (w.length+1) => acquisition (w.take i.val)))) := by
  classical
  obtain ⟨a,k,r,hk,hw⟩ := switch_decomposition w hM hJ
  let K := Submodule.span ℝ
    (Set.range (fun i : Fin (w.length+1) => acquisition (w.take i.val)))
  obtain ⟨h0,h1,hswitch⟩ := first_switch_generators_mem w a k r hk hw
  let v : Fin 3 → K := ![⟨1,h0⟩, ⟨action a,h1⟩,
    ⟨action (!a) * action a ^ k,hswitch⟩]
  have hv : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp K.subtype
    have he : (K.subtype ∘ v) = ![(1 : Mat),action a,action (!a)*action a^k] := by
      funext i
      fin_cases i <;> rfl
    rw [he]
    exact first_switch_independent a k hk
  simpa using hv.fintype_card_le_finrank

#print axioms mixed_cumulative_span

theorem acquisition_unit (v : List Bool) : IsUnit (acquisition v) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have hd := (D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.raw_word_signed_bound v).2.2.1
  have he : (acquisition v).det = (-1 : ℝ)^v.length := by
    change ((Raw v).map (Int.castRingHom ℝ)).det = _
    calc
      _ = ((Raw v).det : ℝ) := by
        simpa only [RingHom.mapMatrix_apply, Int.coe_castRingHom] using ((Int.castRingHom ℝ).map_det (Raw v)).symm
      _ = (-1 : ℝ)^v.length := by rw [hd]; simp
  rw [he]
  exact (isUnit_one.neg).pow _

/-- Consecutive native cumulative matrices never lie on the same matrix ray. -/
theorem cumulative_not_proportional_adjacent (w : List Bool) (i : ℕ) (hi : i < w.length)
    (c : ℝ) : acquisition (w.take (i+1)) ≠ c • acquisition (w.take i) := by
  intro he
  have hp : w.take (i+1) = w.take i ++ [w[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]
    rfl
  rw [hp, acquisition_append] at he
  have hh : action w[i] = c • (1 : Mat) := (acquisition_unit (w.take i)).mul_right_cancel
    (by simpa [Matrix.smul_mul] using he)
  have h01 := congrArg (fun X : Mat => X 0 1) hh
  cases h : w[i] <;> simp [h, action_m_shape, action_j_shape] at h01

/-- A proportionality class occupies at most the ceiling of half the initial-inclusive reads. -/
theorem cumulative_proportionality_card (w : List Bool) (L : Mat) :
    (Finset.univ.filter (fun i : Fin (w.length+1) =>
      ∃ c : ℝ, acquisition (w.take i.val) = c • L)).card ≤ (w.length+2)/2 := by
  classical
  let Q : Finset (Fin (w.length+1)) := Finset.univ.filter
    (fun i => ∃ c : ℝ, acquisition (w.take i.val) = c • L)
  have hsep (i j : Fin (w.length+1)) (hi : i ∈ Q) (hj : j ∈ Q) : i.val+1 ≠ j.val := by
    intro hij
    obtain ⟨c,hc⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨b,hb⟩ := (Finset.mem_filter.mp hj).2
    have hcn : c ≠ 0 := by
      intro hz
      have hzero : acquisition (w.take i.val) = 0 := by simpa [hz] using hc
      exact (acquisition_unit (w.take i.val)).ne_zero hzero
    have he : acquisition (w.take (i.val+1)) = (b/c) • acquisition (w.take i.val) := by
      rw [hij, hb, hc, smul_smul, div_mul_cancel₀ _ hcn]
    exact cumulative_not_proportional_adjacent w i.val (by omega) (b/c) he
  have hinj : Set.InjOn (fun i : Fin (w.length+1) => i.val/2) (Q : Set (Fin (w.length+1))) := by
    intro i hi j hj he
    apply Fin.ext
    have h1 := hsep i j hi hj
    have h2 := hsep j i hj hi
    change i.val/2 = j.val/2 at he
    omega
  have hsub : Q.image (fun i => i.val/2) ⊆ Finset.range ((w.length+2)/2) := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
    simp only [Finset.mem_range]
    omega
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hh
  exact hh

#print axioms cumulative_not_proportional_adjacent
#print axioms cumulative_proportionality_card

private theorem cumulative_not_proportional_pair (w : List Bool) (i : ℕ)
    (hi : i+2 ≤ w.length) (hM : w[i] = false ∨ w[i+1] = false) (c : ℝ) :
    acquisition (w.take (i+2)) ≠ c • acquisition (w.take i) := by
  intro he
  have h1 : w.take (i+1) = w.take i ++ [w[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
    rfl
  have h2 : w.take (i+2) = w.take (i+1) ++ [w[i+1]] := by
    rw [show i+2 = (i+1)+1 by omega, List.take_add_one,
      List.getElem?_eq_getElem (by omega)]
    rfl
  rw [h2, h1, acquisition_append, acquisition_append, ← mul_assoc] at he
  have hh : action w[i+1] * action w[i] = c • (1 : Mat) :=
    (acquisition_unit (w.take i)).mul_right_cancel (by simpa [Matrix.smul_mul] using he)
  have h00 := congrArg (fun X : Mat => X 0 0) hh
  have h01 := congrArg (fun X : Mat => X 0 1) hh
  have h10 := congrArg (fun X : Mat => X 1 0) hh
  cases ha : w[i] <;> cases hb : w[i+1] <;>
    simp_all [action_m_shape, action_j_shape, Matrix.mul_apply, Fin.sum_univ_two]

/-- An even-length word containing M has no maximal alternating proportionality class. -/
theorem cumulative_proportionality_card_even (w : List Bool) (m : ℕ)
    (hlen : w.length = 2*m) (hM : false ∈ w) (L : Mat) :
    (Finset.univ.filter (fun i : Fin (w.length+1) =>
      ∃ c : ℝ, acquisition (w.take i.val) = c • L)).card ≤ m := by
  classical
  obtain ⟨r,hr,hrM⟩ := List.mem_iff_getElem.mp hM
  let k := 2*(r/2)
  have hk : k+2 ≤ w.length := by dsimp [k]; omega
  have hMk : w[k] = false ∨ w[k+1] = false := by
    have hrk : r = k ∨ r = k+1 := by dsimp [k]; omega
    rcases hrk with h | h
    · left; simpa [← h] using hrM
    · right; simpa [← h] using hrM
  let Q : Finset (Fin (w.length+1)) := Finset.univ.filter
    (fun i => ∃ c : ℝ, acquisition (w.take i.val) = c • L)
  have hsep (i j : Fin (w.length+1)) (hi : i ∈ Q) (hj : j ∈ Q) :
      i.val+1 ≠ j.val ∧ ¬ (i.val = k ∧ j.val = k+2) := by
    obtain ⟨c,hc⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨b,hb⟩ := (Finset.mem_filter.mp hj).2
    have hcn : c ≠ 0 := by
      intro hz
      exact (acquisition_unit (w.take i.val)).ne_zero (by simpa [hz] using hc)
    have he : acquisition (w.take j.val) = (b/c) • acquisition (w.take i.val) := by
      rw [hb,hc,smul_smul,div_mul_cancel₀ _ hcn]
    constructor
    · intro hij
      rw [← hij] at he
      exact cumulative_not_proportional_adjacent w i.val (by omega) (b/c) he
    · rintro ⟨hi,hj⟩
      rw [hi,hj] at he
      exact cumulative_not_proportional_pair w k hk hMk (b/c) he
  let bucket (i : Fin (w.length+1)) := if i.val ≤ k then i.val/2 else (i.val-1)/2
  have hinj : Set.InjOn bucket (Q : Set (Fin (w.length+1))) := by
    intro i hi j hj he
    have h1 := hsep i j hi hj
    have h2 := hsep j i hj hi
    apply Fin.ext
    dsimp [bucket] at he
    have hke : k = 2*(r/2) := rfl
    split_ifs at he <;> omega
  have hsub : Q.image bucket ⊆ Finset.range m := by
    intro b hb
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
    simp only [Finset.mem_range]
    dsimp [bucket]
    split_ifs <;> omega
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hh
  exact hh

#print axioms cumulative_proportionality_card_even
end D5.S3.Observer.Linear.GainRay
