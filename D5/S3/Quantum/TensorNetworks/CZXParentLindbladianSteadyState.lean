/- GID: D5/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The CZX parent Lindbladian has the conjectured even-ring limit. -/

import D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
import D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation
import D5.S3.Combinatorics.Graph.CycleItalianDominationRecurrence

/-! The limiting state of the CZX parent Lindbladian on even rings. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState

open D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging
open D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel
open Matrix Filter
attribute [local instance low] Classical.propDecidable
open scoped Topology ComplexConjugate

private lemma window_commute (n : ℕ) (_hn : Even n) (hsize : 4 ≤ n)
    (i j : Fin n) (_hi : i.val % 2 = 0) (_hj : j.val % 2 = 0) :
    Commute (windowSuperoperator n i) (windowSuperoperator n j) := by
  change windowSuperoperator n i * windowSuperoperator n j =
    windowSuperoperator n j * windowSuperoperator n i
  ext x y
  change (windowSuperoperator n i).mulVec
      (fun p => windowChannel n j (Matrix.single y.1 y.2 1) p.1 p.2) x =
    (windowSuperoperator n j).mulVec
      (fun p => windowChannel n i (Matrix.single y.1 y.2 1) p.1 p.2) x
  rw [window_superoperator_action, window_superoperator_action,
    window_channels_commute n hsize]


set_option backward.isDefEq.respectTransparency false in
private lemma exponential_idempotent {k : Type} [Fintype k] [DecidableEq k]
    (e : Matrix k k ℂ) (he : IsIdempotentElem e) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (e - 1)) =
      (Real.exp (-t) : ℂ) • (1 : Matrix k k ℂ) +
        (1 - (Real.exp (-t) : ℂ)) • e := by
  have h := D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation.expIdempotent
    (1 - e) he.one_sub.eq (-(t : ℂ))
  have hi : (-(t : ℂ)) • (1 - e) = (t : ℂ) • (e - 1) := by module
  have hexp : NormedSpace.exp (-(t : ℂ)) = (Real.exp (-t) : ℂ) := by
    rw [← Complex.ofReal_neg, ← NormedSpace.ofReal_exp_ℝ_ℝ, ← Real.exp_eq_exp_ℝ]
  rw [hi, hexp] at h
  rw [h]
  module

private lemma finite_projection_limit {k : Type} [Fintype k] [DecidableEq k]
    (es : List (Matrix k k ℂ))
    (hi : ∀ e ∈ es, IsIdempotentElem e) (hc : es.Pairwise Commute) :
    Tendsto (fun t : ℝ => NormedSpace.exp
      ((t : ℂ) • (es.map (fun e => e - 1)).sum)) atTop (𝓝 es.prod) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := hi e (List.mem_cons_self ..)
    have hes : ∀ f ∈ es, IsIdempotentElem f := fun f hf => hi f (List.mem_cons_of_mem _ hf)
    have hcs := List.pairwise_cons.mp hc
    have hlim := ih hes hcs.2
    have hsingle : Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • (e - 1)))
        atTop (𝓝 e) := by
      have hr : Tendsto (fun t : ℝ => (Real.exp (-t) : ℂ)) atTop (𝓝 0) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp
          Real.tendsto_exp_neg_atTop_nhds_zero
      simpa only [exponential_idempotent e he, zero_smul, sub_zero, one_smul,
        zero_add] using (hr.smul_const (1 : Matrix k k ℂ)).add
          (((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℂ)) atTop (𝓝 1)).sub hr).smul_const e)
    have hcomm : Commute (e - 1) (es.map (fun f => f - 1)).sum := by
      apply Commute.list_sum_right
      intro f hf
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      exact ((hcs.1 g hg).sub_right (Commute.one_right e)).sub_left
        (Commute.one_left (g - 1))
    have heq (t : ℝ) : NormedSpace.exp
        ((t : ℂ) • ((e :: es).map (fun f => f - 1)).sum) =
        NormedSpace.exp ((t : ℂ) • (e - 1)) *
          NormedSpace.exp ((t : ℂ) • (es.map (fun f => f - 1)).sum) := by
      simp only [List.map_cons, List.sum_cons, smul_add]
      exact Matrix.exp_add_of_commute _ _ (hcomm.smul_left (t : ℂ) |>.smul_right (t : ℂ))
    simpa only [heq, List.prod_cons] using hsingle.mul hlim

private def evenStarts (n : ℕ) : List (Fin n) :=
  (List.finRange n).filter (fun i => i.val % 2 == 0)

private noncomputable def projection (n : ℕ) :
    Matrix ((Fin n → Fin 2) × (Fin n → Fin 2))
      ((Fin n → Fin 2) × (Fin n → Fin 2)) ℂ :=
  ((evenStarts n).map (windowSuperoperator n)).prod

private lemma exponential_limit (n : ℕ) (hn : Even n) (hsize : 4 ≤ n) :
    Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • parentLindbladian n))
      atTop (𝓝 (projection n)) := by
  let sites := evenStarts n
  have hsum : ((sites.map (windowSuperoperator n)).map (fun e => e - 1)).sum =
      parentLindbladian n := by
    change (((((List.finRange n).filter (fun i => i.val % 2 == 0)).map
      (windowSuperoperator n)).map (fun e => e - 1)).sum) = _
    rw [List.map_map, ← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
    change ∑ i ∈ ((List.finRange n).filter _).toFinset, _ = _
    simp only [List.toFinset_filter, List.toFinset_finRange, beq_iff_eq]
    rfl
  have hi : ∀ e ∈ sites.map (windowSuperoperator n), IsIdempotentElem e := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    exact window_idempotent n hsize i
  have hc : (sites.map (windowSuperoperator n)).Pairwise Commute := by
    apply List.pairwise_map.mpr
    apply List.pairwise_of_forall_mem_list
    intro i hi j hj
    have hei : i.val % 2 = 0 := by simpa only [beq_iff_eq] using (List.mem_filter.mp hi).2
    have hej : j.val % 2 = 0 := by simpa only [beq_iff_eq] using (List.mem_filter.mp hj).2
    exact window_commute n hn hsize i j hei hej
  have hp : (sites.map (windowSuperoperator n)).prod = projection n := rfl
  simpa only [hsum, hp] using finite_projection_limit (sites.map (windowSuperoperator n)) hi hc

private lemma mem_evenStarts (n : ℕ) (i : Fin n) :
    i ∈ evenStarts n ↔ i.val % 2 = 0 := by
  delta evenStarts
  simp

private lemma all_good_iff_constant (n : ℕ) (hn : 4 ≤ n) (δ : Fin n → Fin 2) :
    (∀ i ∈ evenStarts n, goodWindow i δ) ↔ ∃ e : Fin 2, δ = fun _ => e := by
  constructor
  · intro h
    have hedge (j : Fin n) (hnext : j.val + 1 < n) :
        δ j = δ ⟨j.val + 1, hnext⟩ := by
      by_cases he : j.val % 2 = 0
      · have hg := h j ((mem_evenStarts n j).mpr he)
        have hs : site j 1 = ⟨j.val + 1, hnext⟩ := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt hnext
        have heq : δ (site j 1) = δ j := hg 1
        rw [hs] at heq
        exact heq.symm
      · let i : Fin n := ⟨j.val - 1, by omega⟩
        have hi : i.val % 2 = 0 := by dsimp [i]; omega
        have hg := h i ((mem_evenStarts n i).mpr hi)
        have h1 : site i 1 = j := by
          apply Fin.ext
          change (j.val - 1 + 1) % n = j.val
          rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt j.isLt]
        have h2 : site i 2 = ⟨j.val + 1, hnext⟩ := by
          apply Fin.ext
          change (j.val - 1 + 2) % n = j.val + 1
          rw [show j.val - 1 + 2 = j.val + 1 by omega, Nat.mod_eq_of_lt hnext]
        have heq1 : δ (site i 1) = δ i := hg 1
        have heq2 : δ i = δ (site i 2) := (hg 2).symm
        rw [h1] at heq1
        rw [h2] at heq2
        exact heq1.trans heq2
    have hval (k : ℕ) (hk : k < n) : δ ⟨k, hk⟩ = δ ⟨0, by omega⟩ := by
      induction k with
      | zero => rfl
      | succ k ih =>
        exact (hedge ⟨k, by omega⟩ hk).symm.trans (ih (by omega))
    exact ⟨δ ⟨0, by omega⟩, funext (fun j => hval j.val j.isLt)⟩
  · rintro ⟨e, rfl⟩ i hi k
    rfl

private lemma middle_sites_cover (n : ℕ) (hn : Even n) (hsize : 4 ≤ n) :
    (evenStarts n).toFinset.biUnion (fun i => {site i 1, site i 2}) = Finset.univ := by
  have hnmod : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hn.two_dvd
  apply Finset.eq_univ_of_forall
  intro j
  by_cases hodd : j.val % 2 = 1
  · let i : Fin n := ⟨j.val - 1, by omega⟩
    have hi : i ∈ evenStarts n := (mem_evenStarts n i).mpr (by dsimp [i]; omega)
    have hs : site i 1 = j := by
      apply Fin.ext
      change (j.val - 1 + 1) % n = j.val
      rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt j.isLt]
    exact Finset.mem_biUnion.mpr ⟨i, List.mem_toFinset.mpr hi, by simp [hs]⟩
  · by_cases hz : j.val = 0
    · let i : Fin n := ⟨n - 2, by omega⟩
      have hi : i ∈ evenStarts n := (mem_evenStarts n i).mpr (by dsimp [i]; omega)
      have hs : site i 2 = j := by
        apply Fin.ext
        change (n - 2 + 2) % n = j.val
        rw [Nat.sub_add_cancel (by omega), Nat.mod_self, hz]
      exact Finset.mem_biUnion.mpr ⟨i, List.mem_toFinset.mpr hi, by simp [hs]⟩
    · let i : Fin n := ⟨j.val - 2, by omega⟩
      have hi : i ∈ evenStarts n := (mem_evenStarts n i).mpr (by dsimp [i]; omega)
      have hs : site i 2 = j := by
        apply Fin.ext
        change (j.val - 2 + 2) % n = j.val
        rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt j.isLt]
      exact Finset.mem_biUnion.mpr ⟨i, List.mem_toFinset.mpr hi, by simp [hs]⟩

private lemma window_list_action (n : ℕ) (l : List (Fin n))
    (a : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    (fun x y => ((l.map (windowSuperoperator n)).prod).mulVec (fun p => a p.1 p.2) (x, y)) =
      ((l.map (windowLM n)).prod) a := by
  induction l with
  | nil =>
    funext x y
    simp only [List.map_nil, List.prod_nil, Matrix.one_mulVec]
    rfl
  | cons i l ih =>
    have hv : ((l.map (windowSuperoperator n)).prod).mulVec (fun p => a p.1 p.2) =
        fun p => (((l.map (windowLM n)).prod) a) p.1 p.2 := by
      funext p
      exact congrFun (congrFun ih p.1) p.2
    funext x y
    simp only [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, hv,
      window_superoperator_action]
    rfl

private lemma window_word_gauged (n : ℕ) (hn : 4 ≤ n) (l : List (Fin n))
    (δ x : Fin n → Fin 2) :
    ((l.map (windowLM n)).prod) (gaugedUnit n δ x) =
      if ∀ i ∈ l, goodWindow i δ then
        avg n (l.toFinset.biUnion (fun i => {site i 1, site i 2})) (gaugedUnit n δ) x
      else 0 := by
  have hact (k : Fin n) (δ x : Fin n → Fin 2) :
      windowLM n k (gaugedUnit n δ x) = if goodWindow k δ then
        avg n {site k 1, site k 2} (gaugedUnit n δ) x else 0 := by
    change windowChannel n k (gaugedUnit n δ x) = _
    rw [gauged_window_sector n hn]
    split_ifs
    · have h12 : site k 1 ≠ site k 2 := fun h =>
        (by decide : (1 : Fin 4) ≠ 2) ((site_injective n hn k 1 2).mp h)
      rw [avg_pair_apply n _ _ h12]
      rfl
    · rfl
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.toFinset_nil, Finset.biUnion_empty]
    rw [ite_eq_left (by intro j hj; cases hj), avg_empty]
    rfl
  | cons i l ih =>
    change windowLM n i (((l.map (windowLM n)).prod) (gaugedUnit n δ x)) = _
    rw [ih]
    by_cases hl : ∀ j ∈ l, goodWindow j δ
    · simp only [ite_eq_left hl]
      rw [avg_map]
      simp only [hact]
      by_cases hi : goodWindow i δ
      · have hc : ∀ j ∈ i :: l, goodWindow j δ := by
          intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact hi
          · exact hl j hj
        rw [ite_eq_left hc]
        simp only [ite_eq_left hi, List.toFinset_cons, Finset.biUnion_insert]
        have he := congrArg (fun a => a (gaugedUnit n δ) x)
          (avg_mul (V := Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) n
            (l.toFinset.biUnion (fun j => {site j 1, site j 2})) {site i 1, site i 2})
        simpa only [Module.End.mul_apply, Finset.union_comm] using he
      · simp only [List.mem_cons,
          forall_eq_or_imp, hi, false_and, ite_false]
        exact congrFun (map_zero (avg n (l.toFinset.biUnion (fun j => {site j 1, site j 2})))) x
    · have hc : ¬ ∀ j ∈ i :: l, goodWindow j δ := by
        intro h
        exact hl (fun j hj => h j (List.mem_cons_of_mem i hj))
      simp only [ite_eq_right hl, ite_eq_right hc, map_zero]

private lemma gauge_flip (n : ℕ) (hn : Even n) (x : Fin n → Fin 2) :
    gauge n 1 (x + fun _ => 1) = gauge n 1 x := by
  have hlocal (a b : Fin 2) :
      (a + 1).val * (b + 1).val + a.val + b.val = a.val * b.val + 1 := by
    fin_cases a <;> fin_cases b <;> norm_num
  have hs : (∑ j : Fin n, (x (site j 1)).val) = ∑ j : Fin n, (x j).val := by
    exact Fintype.sum_bijective (fun j : Fin n => site j 1)
      ⟨site_succ_injective n, Finite.surjective_of_injective (site_succ_injective n)⟩
      _ _ (fun _ => rfl)
  have hq : (∑ j : Fin n, ((x j + 1).val * (x (site j 1) + 1).val)) +
        2 * ∑ j : Fin n, (x j).val =
      (∑ j : Fin n, (x j).val * (x (site j 1)).val) + n := by
    have he := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun (j : Fin n) _ => hlocal (x j) (x (site j 1)))
    simp only [Finset.sum_add_distrib, hs, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one] at he
    omega
  have he := congrArg (fun k : ℕ => (-1 : ℂ) ^ k) hq
  simp only [pow_add, pow_mul, hn.neg_one_pow, mul_one] at he
  norm_num at he
  change (-1 : ℂ) ^ (1 * ∑ j : Fin n, (x j + 1).val * (x (site j 1) + 1).val) =
    (-1 : ℂ) ^ (1 * ∑ j : Fin n, (x j).val * (x (site j 1)).val)
  simpa only [one_mul] using he

private lemma sum_gauged_zero (n : ℕ) :
    (∑ x : Fin n → Fin 2, gaugedUnit n (fun _ => 0) x) =
      (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) := by
  delta gaugedUnit
  simp only [sectorGauge_const]
  delta D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel.gauge
  simp only [Fin.val_zero, zero_mul, pow_zero,
    one_smul]
  simp only [show (fun _ : Fin n => (0 : Fin 2)) = 0 from rfl, add_zero]
  exact Matrix.sum_single_one

private lemma sum_gauged_one (n : ℕ) (hn : Even n) :
    (∑ x : Fin n → Fin 2, gaugedUnit n (fun _ => 1) x) = czxUnitary n := by
  ext u v
  change (∑ x : Fin n → Fin 2,
    sectorGauge n (fun _ => 1) x • Matrix.single (x + fun _ => 1) x 1) u v =
      (cz n * tensorX n) u v
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply,
    sectorGauge_const]
  rw [show cz n = Matrix.diagonal (fun x => gauge n 1 x) by
    change Matrix.diagonal _ = Matrix.diagonal _
    congr 1
    funext z
    change (-1 : ℂ) ^ _ = (-1 : ℂ) ^ (1 * _)
    rw [one_mul], Matrix.diagonal_mul]
  change _ = gauge n 1 u * (if u = v + (fun _ => 1) then 1 else 0)
  rw [Finset.sum_eq_single v]
  · by_cases h : u = v + fun _ => 1
    · subst u
      simp only [and_self, ite_true, mul_one]
      exact (gauge_flip n hn v).symm
    · simp [h, eq_comm]
  · intro x hx hxv
    simp only [hxv, and_false, ite_false, mul_zero]
  · simp

private lemma trace_gauged (n : ℕ) (δ x : Fin n → Fin 2) :
    Matrix.trace (gaugedUnit n δ x) = if δ = 0 then 1 else 0 := by
  have he : x + δ = x ↔ δ = 0 := by
    change x + δ = x ↔ δ = (fun _ => 0)
    simpa only [show (fun _ : Fin n => (0 : Fin 2)) = 0 from rfl, add_zero]
      using (add_right_inj x : x + δ = x + (fun _ => 0) ↔ δ = fun _ => 0)
  change Matrix.trace (sectorGauge n δ x • Matrix.single (x + δ) x 1) = _
  rw [Matrix.trace_smul]
  by_cases h : δ = 0
  · subst δ
    simp only [add_zero, Matrix.trace_single_eq_same, smul_eq_mul, mul_one,
      ite_true]
    change (-1 : ℂ) ^ (∑ j : Fin n, (0 : Fin 2).val * (x j).val *
      (x (site j 1)).val) = 1
    simp only [Fin.val_zero, zero_mul, Finset.sum_const_zero, pow_zero]
  · have hne : x + δ ≠ x := mt he.mp h
    rw [Matrix.trace_single_eq_of_ne _ _ _ hne, smul_zero, ite_eq_right h]

private lemma trace_symmetry_gauged (n : ℕ) (hn : Even n)
    (δ x : Fin n → Fin 2) :
    Matrix.trace ((czxUnitary n)ᴴ * gaugedUnit n δ x) =
      if δ = (fun _ => 1) then 1 else 0 := by
  have hu (u v : Fin n → Fin 2) :
      czxUnitary n u v = gauge n 1 u * (if u = v + (fun _ => 1) then 1 else 0) := by
    change (cz n * tensorX n) u v = _
    rw [show cz n = Matrix.diagonal (fun z => gauge n 1 z) by
      change Matrix.diagonal _ = Matrix.diagonal _
      congr 1
      funext z
      change (-1 : ℂ) ^ _ = (-1 : ℂ) ^ (1 * _)
      rw [one_mul], Matrix.diagonal_mul]
    rfl
  change Matrix.trace ((czxUnitary n)ᴴ *
    (sectorGauge n δ x • Matrix.single (x + δ) x 1)) = _
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_mul_single]
  simp only [MulOpposite.op_one, one_smul, Matrix.conjTranspose_apply,
    smul_eq_mul, hu]
  by_cases h : δ = (fun _ => 1)
  · subst δ
    simp only [ite_true, mul_one, sectorGauge_const, gauge_flip n hn]
    have hs : star (gauge n 1 x) = gauge n 1 x := by
      change star ((-1 : ℂ) ^ _) = (-1 : ℂ) ^ _
      simp only [star_pow, star_neg, star_one]
    rw [hs]
    simpa only [sectorGauge_const] using sectorGauge_mul_self n (fun _ => 1) x
  · rw [ite_eq_right (mt (add_right_inj x).mp h), ite_eq_right h]
    simp only [mul_zero, star_zero]

private lemma projection_formula (n : ℕ) (hn : Even n) (hsize : 4 ≤ n)
    (a : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    (fun x y => (projection n).mulVec (fun p => a p.1 p.2) (x, y)) =
      ((2 : ℂ) ^ n)⁻¹ • (Matrix.trace a • (1 : Matrix _ _ ℂ) +
        Matrix.trace ((czxUnitary n)ᴴ * a) • czxUnitary n) := by
  let f : Module.End ℂ (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :=
    { toFun := fun b x y => (projection n).mulVec (fun p => b p.1 p.2) (x, y)
      map_add' := by
        intro b c
        funext x y
        exact congrFun (Matrix.mulVec_add (projection n)
          (fun p => b p.1 p.2) (fun p => c p.1 p.2)) (x, y)
      map_smul' := by
        intro c b
        funext x y
        exact congrFun (Matrix.mulVec_smul (projection n) c (fun p => b p.1 p.2)) (x, y) }
  let g : Module.End ℂ (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :=
    { toFun := fun b => ((2 : ℂ) ^ n)⁻¹ •
        (Matrix.trace b • (1 : Matrix _ _ ℂ) + Matrix.trace ((czxUnitary n)ᴴ * b) • czxUnitary n)
      map_add' := by
        intro b c
        simp only [Matrix.trace_add, Matrix.mul_add, add_smul, smul_add]
        module
      map_smul' := by
        intro c b
        simp only [Matrix.trace_smul, Matrix.mul_smul, smul_smul, smul_add,
          RingHom.id_apply, smul_eq_mul]
        module }
  have heq : f = g := by
    apply matrix_linearMap_ext_gauged n
    intro δ x
    change (fun u v => (projection n).mulVec (fun p => gaugedUnit n δ x p.1 p.2) (u, v)) = _
    have hp : projection n = ((evenStarts n).map (windowSuperoperator n)).prod := rfl
    rw [hp, window_list_action, window_word_gauged n hsize]
    change (if ∀ i ∈ evenStarts n, goodWindow i δ then
      avg n ((evenStarts n).toFinset.biUnion (fun i => {site i 1, site i 2})) (gaugedUnit n δ) x
      else 0) = ((2 : ℂ) ^ n)⁻¹ •
        (Matrix.trace (gaugedUnit n δ x) • (1 : Matrix _ _ ℂ) +
          Matrix.trace ((czxUnitary n)ᴴ * gaugedUnit n δ x) • czxUnitary n)
    rw [trace_gauged, trace_symmetry_gauged n hn]
    by_cases hd : ∃ e : Fin 2, δ = fun _ => e
    · have hg := (all_good_iff_constant n hsize δ).mpr hd
      rw [ite_eq_left hg, middle_sites_cover n hn hsize, avg_univ]
      obtain ⟨e, rfl⟩ := hd
      fin_cases e
      · change ((2 : ℂ) ^ n)⁻¹ • (∑ y, gaugedUnit n (fun _ => 0) y) = _
        rw [sum_gauged_zero]
        have hne : (fun _ : Fin n => (0 : Fin 2)) ≠ fun _ => 1 := by
          intro h
          have he := congrFun h ⟨0, by omega⟩
          exact (by decide : (0 : Fin 2) ≠ 1) he
        simp [hne]
        rfl
      · change ((2 : ℂ) ^ n)⁻¹ • (∑ y, gaugedUnit n (fun _ => 1) y) = _
        rw [sum_gauged_one n hn]
        have hne : (fun _ : Fin n => (1 : Fin 2)) ≠ 0 := by
          intro h
          have he := congrFun h ⟨0, by omega⟩
          exact (by decide : (1 : Fin 2) ≠ 0) he
        change ((2 : ℂ) ^ n)⁻¹ • czxUnitary n = ((2 : ℂ) ^ n)⁻¹ •
          ((if (fun _ : Fin n => (1 : Fin 2)) = 0 then 1 else 0) • 1 +
            (if (fun _ : Fin n => (1 : Fin 2)) = (fun _ => 1) then 1 else 0) • czxUnitary n)
        simp only [ite_eq_right hne, ite_true, zero_smul, one_smul, zero_add]
    · have hg : ¬ ∀ i ∈ evenStarts n, goodWindow i δ :=
        mt (all_good_iff_constant n hsize δ).mp hd
      have h0 : δ ≠ 0 := fun h => hd ⟨0, h⟩
      have h1 : δ ≠ (fun _ => 1) := fun h => hd ⟨1, h⟩
      simp only [ite_eq_right hg, ite_eq_right h0, ite_eq_right h1, zero_smul, add_zero, smul_zero]
  exact congrArg (fun l => l a) heq


private lemma flip_diagonal (n : ℕ) (hn : 0 < n) (x : Fin n → Fin 2) :
    tensorX n x x = 0 := by
  change (if x = (fun j => x j + 1) then (1 : ℂ) else 0) = 0
  apply ite_eq_right
  intro h
  have hj := congrArg Fin.val (congrFun h (⟨0, hn⟩ : Fin n))
  change (x ⟨0, hn⟩).val = ((x ⟨0, hn⟩).val + 1) % 2 at hj
  have hx := (x (⟨0, hn⟩ : Fin n)).isLt
  omega

private lemma symmetry_trace (n : ℕ) (hn : 0 < n) :
    Matrix.trace (czxUnitary n) = 0 := by
  change ∑ x : Fin n → Fin 2, (cz n * tensorX n) x x = 0
  apply Finset.sum_eq_zero
  intro x _
  rw [show cz n = Matrix.diagonal (fun z => (-1 : ℂ) ^
    ∑ j : Fin n, (z j).val * (z (site j 1)).val) from rfl]
  rw [Matrix.diagonal_mul, flip_diagonal n hn, mul_zero]

private lemma tensor_x_unitary (n : ℕ) : tensorX n * (tensorX n)ᴴ = 1 := by
  have hf (x : Fin n → Fin 2) : (fun j => (x j + 1) + 1) = x := by
    funext j
    exact (open scoped Fin.CommRing in CharTwo.add_cancel_right (x j) 1)
  let f : Equiv.Perm (Fin n → Fin 2) := Equiv.addRight 1
  have hx : tensorX n = f.permMatrix ℂ := by
    ext x y
    have hi : x = f y ↔ f x = y := by
      constructor
      · rintro rfl
        exact hf y
      · intro h
        calc
          x = f (f x) := (hf x).symm
          _ = f y := congrArg f h
    change (if x = f y then (1 : ℂ) else 0) = f.toPEquiv.toMatrix x y
    rw [PEquiv.toMatrix_toPEquiv_apply]
    simp only [Pi.single_apply, hi, eq_comm]
  rw [hx, Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
    Matrix.permMatrix_one]

private lemma coefficient_partition (n : ℕ) :
    Matrix.trace ((czxUnitary n)ᴴ * tensorX n) =
      ∑ x : Fin n → Fin 2, (-1 : ℂ) ^
        ∑ j : Fin n, (x j).val * (x (site j 1)).val := by
  change Matrix.trace ((cz n * tensorX n)ᴴ * tensorX n) = _
  rw [Matrix.conjTranspose_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    tensor_x_unitary, one_mul, Matrix.trace_conjTranspose]
  rw [show cz n = Matrix.diagonal (fun x => (-1 : ℂ) ^
    ∑ j : Fin n, (x j).val * (x (site j 1)).val) from rfl, Matrix.trace_diagonal]
  simp only [star_sum, star_pow, star_neg, star_one]

private lemma transfer_path (h : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) (a b : Fin 2) :
    ((h.map (Int.castRingHom ℂ)) ^ (m + 1)) a b =
      ∑ x : Fin m → Fin 2, ∏ j : Fin (m + 1),
        (h.map (Int.castRingHom ℂ)) (Fin.cons (α := fun _ => Fin 2) a x j)
          (Fin.snoc (α := fun _ => Fin 2) x b j) := by
  rw [← Matrix.map_pow]
  change (Int.castRingHom ℂ) ((h ^ (m + 1)) a b) = _
  rw [← D5.S3.Combinatorics.Graph.CycleItalianDominationRecurrence.sum_pathWeight, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [D5.S3.Combinatorics.Graph.CycleItalianDominationRecurrence.pathWeight,
    map_mul, map_prod, Fin.prod_univ_castSucc, Fin.cons_succ, Fin.snoc_castSucc,
    Fin.snoc_last]
  rfl

private lemma partition_transfer (n : ℕ) (hn : 0 < n) :
    (∑ x : Fin n → Fin 2, (-1 : ℂ) ^
      ∑ j : Fin n, (x j).val * (x (site j 1)).val) =
      Matrix.trace ((!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) ^ n) := by
  let h : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]
  let hZ : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, -1]
  have hcast : hZ.map (Int.castRingHom ℂ) = h := by
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [hZ, h]
  have he (a b : Fin 2) : h a b = (-1 : ℂ) ^ (a.val * b.val) := by
    fin_cases a <;> fin_cases b <;> norm_num [h]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  symm
  calc
    Matrix.trace (h ^ (m + 1)) = ∑ a : Fin 2, ∑ x : Fin m → Fin 2,
        ∏ j : Fin (m + 1), h (Fin.cons (α := fun _ => Fin 2) a x j)
          (Fin.snoc (α := fun _ => Fin 2) x a j) := by
      change (∑ a, (h ^ (m + 1)) a a) = _
      simp_rw [← hcast, transfer_path]
    _ = ∑ p : Fin 2 × (Fin m → Fin 2),
        ∏ j : Fin (m + 1), h (Fin.cons (α := fun _ => Fin 2) p.1 p.2 j)
          (Fin.snoc (α := fun _ => Fin 2) p.2 p.1 j) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ x : Fin (m + 1) → Fin 2, (-1 : ℂ) ^
        ∑ j : Fin (m + 1), (x j).val * (x (site j 1)).val := by
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 2))
      intro p
      change (∏ j : Fin (m + 1), h (Fin.cons (α := fun _ => Fin 2) p.1 p.2 j)
          (Fin.snoc (α := fun _ => Fin 2) p.2 p.1 j)) =
        (-1 : ℂ) ^ ∑ j : Fin (m + 1), (Fin.cons (α := fun _ => Fin 2) p.1 p.2 j).val *
          (Fin.cons (α := fun _ => Fin 2) p.1 p.2 (site j 1)).val
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro j _
      have hj : Fin.cons (α := fun _ => Fin 2) p.1 p.2 (site j 1) =
          Fin.snoc (α := fun _ => Fin 2) p.2 p.1 j := by
        cases j using Fin.lastCases with
        | last =>
          have hs : site (Fin.last m) 1 = 0 := by
            apply Fin.ext
            change (m + 1) % (m + 1) = 0
            exact Nat.mod_self _
          rw [hs, Fin.cons_zero, Fin.snoc_last]
        | cast j =>
          have hs : site j.castSucc 1 = j.succ := by
            apply Fin.ext
            change (j.val + 1) % (m + 1) = j.val + 1
            exact Nat.mod_eq_of_lt (by omega)
          rw [hs, Fin.cons_succ, Fin.snoc_castSucc]
      rw [hj, he]

private lemma transfer_coefficient (n : ℕ) (hn : Even n) (hsize : 4 ≤ n) :
    Matrix.trace ((czxUnitary n)ᴴ * tensorX n) = (2 : ℂ) ^ (n / 2 + 1) := by
  let h : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]
  have hs : h ^ 2 = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      norm_num [h, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hm : n = 2 * (n / 2) := by
    obtain ⟨m, hm⟩ := hn
    omega
  have hp : h ^ n = (2 : ℂ) ^ (n / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    calc
      h ^ n = h ^ (2 * (n / 2)) := congrArg (h ^ ·) hm
      _ = (h ^ 2) ^ (n / 2) := pow_mul _ _ _
      _ = _ := by rw [hs, smul_pow, one_pow]
  rw [coefficient_partition n, partition_transfer n (by omega)]
  change Matrix.trace (h ^ n) = _
  rw [hp, Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul, pow_succ]

private lemma projection_initial (n : ℕ) (hn : Even n) (hsize : 4 ≤ n) :
    (fun x y => (projection n).mulVec
      (fun p => (((2 : ℂ) ^ n)⁻¹ •
        ((1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) + tensorX n)) p.1 p.2) (x, y)) =
      ((2 : ℂ) ^ n)⁻¹ •
        ((1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) +
          (2 : ℂ) ^ (1 - (n / 2 : ℕ) : ℤ) • czxUnitary n) := by
  have hnpos : 0 < n := by omega
  have htx : Matrix.trace (tensorX n) = 0 := by
    change ∑ x, tensorX n x x = 0
    exact Finset.sum_eq_zero (fun x _ => flip_diagonal n hnpos x)
  have hu : Matrix.trace (czxUnitary n)ᴴ = 0 := by
    rw [Matrix.trace_conjTranspose, symmetry_trace n hnpos, star_zero]
  have hcard : (Fintype.card (Fin n → Fin 2) : ℂ) = (2 : ℂ) ^ n := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  have ht : Matrix.trace (((2 : ℂ) ^ n)⁻¹ •
      ((1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) + tensorX n)) = 1 := by
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, htx, add_zero, hcard]
    exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))
  have hm : n = n / 2 + n / 2 := by
    obtain ⟨m, hm⟩ := hn
    omega
  have hcoef : ((2 : ℂ) ^ n)⁻¹ * (2 : ℂ) ^ (n / 2 + 1) =
      (2 : ℂ) ^ (1 - (n / 2 : ℕ) : ℤ) := by
    rw [zpow_sub₀ (by norm_num), zpow_one, zpow_natCast]
    rw [show (2 : ℂ) ^ n = (2 : ℂ) ^ (n / 2) * (2 : ℂ) ^ (n / 2) by
      rw [← pow_add, ← hm], pow_add, pow_one]
    let p : ℂ := 2 ^ (n / 2)
    have hp : p ≠ 0 := pow_ne_zero _ (by norm_num)
    change (p * p)⁻¹ * (p * 2) = 2 * p⁻¹
    rw [_root_.mul_inv_rev]
    calc
      p⁻¹ * p⁻¹ * (p * 2) = (p⁻¹ * p) * (p⁻¹ * 2) := by ring
      _ = 2 * p⁻¹ := by rw [inv_mul_cancel₀ hp, one_mul, mul_comm]
  rw [projection_formula n hn hsize, ht]
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.mul_one,
    Matrix.trace_add, hu, transfer_coefficient n hn hsize, zero_add]
  rw [one_smul, smul_eq_mul, hcoef]

private lemma evolution_limit (n : ℕ)
    (h : Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • parentLindbladian n))
      atTop (𝓝 (projection n))) :
    Tendsto (fun t : ℝ => evolution n t
      (((2 : ℂ) ^ n)⁻¹ • (1 + tensorX n))) atTop
      (𝓝 (fun x y => (projection n).mulVec
        (fun p => (((2 : ℂ) ^ n)⁻¹ • (1 + tensorX n)) p.1 p.2) (x, y))) := by
  apply tendsto_pi_nhds.mpr
  intro x
  apply tendsto_pi_nhds.mpr
  intro y
  change Tendsto (fun t : ℝ => ∑ p,
    NormedSpace.exp ((t : ℂ) • parentLindbladian n) (x, y) p *
      (((2 : ℂ) ^ n)⁻¹ • (1 + tensorX n)) p.1 p.2) _ _
  exact tendsto_finsetSum _ fun p _ =>
    ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h (x, y))) p).mul tendsto_const_nhds

/-- The conjecture for every even ring on which the four window sites are distinct. -/
def claim : Prop := ∀ n : ℕ, Even n → 4 ≤ n →
  Tendsto (fun t : ℝ => evolution n t (((2 : ℂ) ^ n)⁻¹ • (1 + tensorX n))) atTop
    (𝓝 (((2 : ℂ) ^ n)⁻¹ •
      (1 + (2 : ℂ) ^ (1 - (n / 2 : ℕ) : ℤ) • czxUnitary n)))

/-- The steady-state conjecture for every even N at least four. -/
theorem result : claim := by
  intro n hn hsize
  have happly := evolution_limit n (exponential_limit n hn hsize)
  rw [projection_initial n hn hsize] at happly
  exact happly


end D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState
