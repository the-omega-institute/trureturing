/- GID: D5/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The CZX parent Lindbladian has the conjectured even-ring limit. -/

import D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState

open Matrix Filter
open scoped Topology ComplexConjugate

private lemma window_commute (n : ℕ) (hn : Even n) (hsize : 4 ≤ n)
    (i j : Fin n) (hi : i.val % 2 = 0) (hj : j.val % 2 = 0) :
    Commute (windowSuperoperator n i) (windowSuperoperator n j) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
private lemma exponential_idempotent {k : Type*} [Fintype k] [DecidableEq k]
    (e : Matrix k k ℂ) (he : IsIdempotentElem e) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (e - 1)) =
      (Real.exp (-t) : ℂ) • (1 : Matrix k k ℂ) +
        (1 - (Real.exp (-t) : ℂ)) • e := by
  let f : (ℂ × ℂ) →+* Matrix k k ℂ :=
    { toFun := fun z => z.1 • e + z.2 • (1 - e)
      map_zero' := by simp
      map_one' := by simp
      map_add' := by
        intro z w
        simp only [Prod.fst_add, Prod.snd_add, add_smul]
        abel
      map_mul' := by
        intro z w
        simp only [Prod.fst_mul, Prod.snd_mul, add_mul, mul_add,
          smul_mul_assoc, mul_smul_comm, smul_smul, he.eq, he.one_sub.eq,
          he.mul_one_sub_self, he.one_sub_mul_self, smul_zero, zero_add, add_zero,
          mul_comm] }
  have hf : Continuous f :=
    (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)
  have hi : f ((0 : ℂ), -(t : ℂ)) = (t : ℂ) • (e - 1) := by
    change (0 : ℂ) • e + (-(t : ℂ)) • (1 - e) = _
    simp only [zero_smul, zero_add, smul_sub, neg_smul]
    module
  have h := (open scoped Matrix.Norms.Operator in
    NormedSpace.map_exp f hf ((0 : ℂ), -(t : ℂ)))
  rw [hi] at h
  rw [← h]
  change (NormedSpace.exp ((0 : ℂ), -(t : ℂ))).1 • e +
    (NormedSpace.exp ((0 : ℂ), -(t : ℂ))).2 • (1 - e) = _
  rw [Prod.fst_exp, Prod.snd_exp]
  simp only [NormedSpace.exp_zero, one_smul]
  have hexp : NormedSpace.exp (-(t : ℂ)) = (Real.exp (-t) : ℂ) := by
    rw [← Complex.ofReal_neg, ← NormedSpace.ofReal_exp_ℝ_ℝ, ← Real.exp_eq_exp_ℝ]
  rw [hexp]
  module

private lemma finite_projection_limit {k : Type*} [Fintype k] [DecidableEq k]
    (es : List (Matrix k k ℂ))
    (hi : ∀ e ∈ es, IsIdempotentElem e) (hc : es.Pairwise Commute) :
    Tendsto (fun t : ℝ => NormedSpace.exp
      ((t : ℂ) • (es.map (fun e => e - 1)).sum)) atTop (𝓝 es.prod) := by
  induction es with
  | nil => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ =>
      (1 : Matrix k k ℂ)) atTop (𝓝 1))
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

private noncomputable def projection (n : ℕ) :
    Matrix ((Fin n → Fin 2) × (Fin n → Fin 2))
      ((Fin n → Fin 2) × (Fin n → Fin 2)) ℂ :=
  (((List.finRange n).filter (fun i => i.val % 2 == 0)).map
    (windowSuperoperator n)).prod

private lemma exponential_limit (n : ℕ) (hn : Even n) (hsize : 4 ≤ n) :
    Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • parentLindbladian n))
      atTop (𝓝 (projection n)) := by
  let sites := (List.finRange n).filter (fun i => i.val % 2 == 0)
  have hsum : ((sites.map (windowSuperoperator n)).map (fun e => e - 1)).sum =
      parentLindbladian n := by
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
    have hei : i.val % 2 = 0 := by simpa [sites] using (List.mem_filter.mp hi).2
    have hej : j.val % 2 = 0 := by simpa [sites] using (List.mem_filter.mp hj).2
    exact window_commute n hn hsize i j hei hej
  have hp : (sites.map (windowSuperoperator n)).prod = projection n := rfl
  simpa only [hsum, hp] using finite_projection_limit (sites.map (windowSuperoperator n)) hi hc

private lemma projection_formula (n : ℕ) (hn : Even n) (hsize : 4 ≤ n)
    (a : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    (fun x y => (projection n).mulVec (fun p => a p.1 p.2) (x, y)) =
      ((2 : ℂ) ^ n)⁻¹ • (Matrix.trace a • (1 : Matrix _ _ ℂ) +
        Matrix.trace ((czxUnitary n)ᴴ * a) • czxUnitary n) := by
  sorry

private lemma flip_diagonal (n : ℕ) (hn : 0 < n) (x : Fin n → Fin 2) :
    tensorX n x x = 0 := by
  change (if x = (fun j => x j + 1) then (1 : ℂ) else 0) = 0
  apply if_neg
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
    apply Fin.ext
    change (((x j).val + 1) % 2 + 1) % 2 = (x j).val
    have := (x j).isLt
    omega
  let f : Equiv.Perm (Fin n → Fin 2) :=
    { toFun := fun x j => x j + 1
      invFun := fun x j => x j + 1
      left_inv := hf
      right_inv := hf }
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

private lemma transfer_path (h : Matrix (Fin 2) (Fin 2) ℂ) (m : ℕ) (a b : Fin 2) :
    (h ^ (m + 1)) a b = ∑ x : Fin m → Fin 2, ∏ j : Fin (m + 1),
      h (Fin.cons (α := fun _ => Fin 2) a x j) (Fin.snoc (α := fun _ => Fin 2) x b j) := by
  induction m generalizing b with
  | zero => simp <;> rfl
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih, Finset.sum_mul]
    rw [← Fintype.sum_prod_type']
    apply Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (m + 1) => Fin 2))
    intro p
    change (∏ j : Fin (m + 1), h (Fin.cons (α := fun _ => Fin 2) a p.2 j) (Fin.snoc (α := fun _ => Fin 2) p.2 p.1 j)) * h p.1 b =
      ∏ j : Fin (m + 2), h (Fin.cons (α := fun _ => Fin 2) a (Fin.snoc (α := fun _ => Fin 2) p.2 p.1) j)
        (Fin.snoc (α := fun _ => Fin 2) (Fin.snoc (α := fun _ => Fin 2) p.2 p.1) b j)
    conv_rhs => rw [Fin.prod_univ_castSucc]
    simp only [Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc, Fin.snoc_last]

private lemma partition_transfer (n : ℕ) (hn : 0 < n) :
    (∑ x : Fin n → Fin 2, (-1 : ℂ) ^
      ∑ j : Fin n, (x j).val * (x (site j 1)).val) =
      Matrix.trace ((!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) ^ n) := by
  let h : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]
  have he (a b : Fin 2) : h a b = (-1 : ℂ) ^ (a.val * b.val) := by
    fin_cases a <;> fin_cases b <;> norm_num [h]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  symm
  calc
    Matrix.trace (h ^ (m + 1)) = ∑ a : Fin 2, ∑ x : Fin m → Fin 2,
        ∏ j : Fin (m + 1), h (Fin.cons (α := fun _ => Fin 2) a x j) (Fin.snoc (α := fun _ => Fin 2) x a j) := by
      change (∑ a, (h ^ (m + 1)) a a) = _
      simp_rw [transfer_path]
    _ = ∑ p : Fin 2 × (Fin m → Fin 2),
        ∏ j : Fin (m + 1), h (Fin.cons (α := fun _ => Fin 2) p.1 p.2 j) (Fin.snoc (α := fun _ => Fin 2) p.2 p.1 j) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ x : Fin (m + 1) → Fin 2, (-1 : ℂ) ^
        ∑ j : Fin (m + 1), (x j).val * (x (site j 1)).val := by
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 2))
      intro p
      change (∏ j : Fin (m + 1), h (Fin.cons (α := fun _ => Fin 2) p.1 p.2 j) (Fin.snoc (α := fun _ => Fin 2) p.2 p.1 j)) =
        (-1 : ℂ) ^ ∑ j : Fin (m + 1), (Fin.cons (α := fun _ => Fin 2) p.1 p.2 j).val *
          (Fin.cons (α := fun _ => Fin 2) p.1 p.2 (site j 1)).val
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro j _
      have hj : Fin.cons (α := fun _ => Fin 2) p.1 p.2 (site j 1) = Fin.snoc (α := fun _ => Fin 2) p.2 p.1 j := by
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
    field_simp
    <;> ring
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
  exact tendsto_finset_sum _ fun p _ =>
    ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h (x, y))) p).mul tendsto_const_nhds

/-- The steady-state conjecture for every even N at least four. -/
theorem result : claim := by
  intro n hn hsize
  have happly := evolution_limit n (exponential_limit n hn hsize)
  rw [projection_initial n hn hsize] at happly
  exact happly


end D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState
