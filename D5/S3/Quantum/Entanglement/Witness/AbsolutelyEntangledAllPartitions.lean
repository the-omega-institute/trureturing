/- GID: D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A finite set has a common entangled state for all partitions in every frame. -/

import D5.S3.Quantum.PureState.PureStateHandshake

/-! Finite grids of pure states and simultaneous entanglement in fixed tensor coordinates. -/

open Matrix BigOperators
open scoped ComplexOrder

namespace D5.S3.Quantum.Entanglement.Witness.AbsolutelyEntangledAllPartitions

open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

/-- Ordered factorizations into at least two factors, each of dimension at least two. -/
def Partition (d : ℕ) :=
  {p : (Σ k : ℕ, Fin k → ℕ) //
    2 ≤ p.1 ∧ (∀ i, 2 ≤ p.2 i) ∧ ∏ i, p.2 i = d}

/-- The fixed mixed-radix identification for an ordered factorization. -/
def partitionEquiv {d : ℕ} (p : Partition d) :
    ((i : Fin p.val.1) → Fin (p.val.2 i)) ≃ Fin d :=
  finPiFinEquiv.trans (finCongr p.property.2.2)

/-- Tensor products of local matrices in the fixed coordinate identification. -/
def productState {d : ℕ} (p : Partition d)
    (ρ : (i : Fin p.val.1) → Matrix (Fin (p.val.2 i)) (Fin (p.val.2 i)) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun x y => ∏ i, ρ i (partitionEquiv p |>.symm x i) (partitionEquiv p |>.symm y i)

/-- Separable states are the real convex hull of products of local density matrices. -/
def Separable {d : ℕ} (p : Partition d) (ρ : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ρ ∈ convexHull ℝ {σ | ∃ τ, (∀ i, (τ i).PosSemidef ∧ (τ i).trace = 1) ∧
    σ = productState p τ}

/-- In every frame one member of a fixed finite set is entangled for all factorizations. -/
def claim : Prop :=
  ∀ d a b : ℕ, 2 ≤ a → 2 ≤ b → d = a * b →
    ∃ s : Finset (Matrix (Fin d) (Fin d) ℂ),
      (∀ ρ ∈ s, ρ.PosSemidef ∧ ρ.trace = 1) ∧
      ∀ u ∈ Matrix.specialUnitaryGroup (Fin d) ℂ,
        ∃ ρ ∈ s, ∀ p : Partition d, ¬ Separable p (u * ρ * star u)

private def corner {d : ℕ} (p : Partition d) (x : Fin 2 × Fin 2) : Fin d :=
  partitionEquiv p fun i =>
    ⟨if i.val = 0 then x.1.val else if i.val = 1 then x.2.val else 0, by
      have hi := p.property.2.1 i
      split_ifs <;> omega⟩

private def minor {d : ℕ} (c : Fin 2 × Fin 2 → Fin d) (v : Fin d → ℂ) : ℂ :=
  v (c (0, 0)) * v (c (1, 1)) - v (c (0, 1)) * v (c (1, 0))

private lemma corner_injective {d : ℕ} (p : Partition d) :
    Function.Injective (corner p) := by
  intro x y h
  have h' := (partitionEquiv p).injective h
  have h0 := congrArg (fun f => (f ⟨0, by have := p.property.1; omega⟩).val) h'
  have h1 := congrArg (fun f => (f ⟨1, by have := p.property.1; omega⟩).val) h'
  exact Prod.ext (Fin.ext (by simpa using h0)) (Fin.ext (by simpa using h1))

private noncomputable def minorPolynomial {d : ℕ} (u : Matrix (Fin d) (Fin d) ℂ)
    (c : Fin 2 × Fin 2 ↪ Fin d) : MvPolynomial (Fin d) ℂ :=
  let l := fun i => ∑ j, MvPolynomial.C (u i j) * MvPolynomial.X j
  l (c (0, 0)) * l (c (1, 1)) - l (c (0, 1)) * l (c (1, 0))

private lemma minorPolynomial_eval {d : ℕ} (u : Matrix (Fin d) (Fin d) ℂ)
    (c : Fin 2 × Fin 2 ↪ Fin d) (v : Fin d → ℂ) :
    MvPolynomial.eval v (minorPolynomial u c) = minor c (u *ᵥ v) := by
  simp only [minorPolynomial, map_sub, map_mul, map_sum, MvPolynomial.eval_C,
    MvPolynomial.eval_X, minor, Matrix.mulVec, dotProduct]

private lemma minorPolynomial_nonzero {d : ℕ} (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u ∈ Matrix.specialUnitaryGroup (Fin d) ℂ) (c : Fin 2 × Fin 2 ↪ Fin d) :
    minorPolynomial u c ≠ 0 := by
  classical
  let z : Fin d → ℂ := Pi.single (c (0, 0)) 1 + Pi.single (c (1, 1)) 1
  have hu' : u * star u = 1 := Matrix.mem_unitaryGroup_iff.mp
    (Matrix.specialUnitaryGroup_le_unitaryGroup hu)
  intro hz
  have h := congrArg (MvPolynomial.eval (star u *ᵥ z)) hz
  rw [minorPolynomial_eval, Matrix.mulVec_mulVec, hu', Matrix.one_mulVec] at h
  simp [minor, z, Pi.single_apply, c.injective.eq_iff] at h

private lemma minorPolynomial_degree {d : ℕ} (u : Matrix (Fin d) (Fin d) ℂ)
    (c : Fin 2 × Fin 2 ↪ Fin d) : (minorPolynomial u c).totalDegree ≤ 2 := by
  have h (i : Fin d) :
      (∑ j, MvPolynomial.C (u i j) * MvPolynomial.X j).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      linarith [h (c (0, 0)), h (c (1, 1))])
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      linarith [h (c (0, 1)), h (c (1, 0))])

private noncomputable def gridBound (d : ℕ) : ℕ :=
  2 * Fintype.card ((Fin 2 × Fin 2) ↪ Fin d)

private noncomputable def grid (d : ℕ) : Finset (Fin d → ℂ) := by
  classical
  exact (Fintype.piFinset fun _ =>
    (Finset.range (gridBound d + 1)).image (fun n => (n : ℂ))).filter (· ≠ 0)

private lemma grid_eval_nonzero {d m : ℕ} (f : MvPolynomial (Fin d) ℂ)
    (hf : f ≠ 0) (hdeg : f.totalDegree ≤ m) :
    ∃ v ∈ Fintype.piFinset (fun _ : Fin d =>
      (Finset.range (m + 1)).image (fun n : ℕ => (n : ℂ))), MvPolynomial.eval v f ≠ 0 := by
  classical
  let s : Finset ℂ := (Finset.range (m + 1)).image (fun n : ℕ => (n : ℂ))
  have hcard : s.card = m + 1 := by
    exact (Finset.card_image_of_injective _ (Nat.cast_injective (R := ℂ))).trans
      (Finset.card_range _)
  by_contra! hz
  have hfilter : {v ∈ Fintype.piFinset (fun _ : Fin d => s) |
      MvPolynomial.eval v f = 0} = Fintype.piFinset (fun _ : Fin d => s) :=
    Finset.filter_eq_self.mpr hz
  have hb := MvPolynomial.schwartz_zippel_totalDegree hf s
  have hpos : 0 < (s.card : ℚ≥0) := by exact_mod_cast (by omega : 0 < s.card)
  rw [hfilter, Fintype.card_piFinset_const, Nat.cast_pow,
    div_self (pow_ne_zero d hpos.ne')] at hb
  have hle : (s.card : ℚ≥0) ≤ (f.totalDegree : ℚ≥0) := by
    simpa using (le_div_iff₀ hpos).mp hb
  have hlt : (f.totalDegree : ℚ≥0) < (s.card : ℚ≥0) := by
    exact_mod_cast (by omega : f.totalDegree < s.card)
  exact (not_le_of_gt hlt) hle

private noncomputable def framePolynomial {d : ℕ} (u : Matrix (Fin d) (Fin d) ℂ) :
    MvPolynomial (Fin d) ℂ := ∏ c : Fin 2 × Fin 2 ↪ Fin d, minorPolynomial u c

private lemma framePolynomial_nonzero {d : ℕ} (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u ∈ Matrix.specialUnitaryGroup (Fin d) ℂ) : framePolynomial u ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr fun c _ => minorPolynomial_nonzero u hu c

private lemma framePolynomial_degree {d : ℕ} (u : Matrix (Fin d) (Fin d) ℂ) :
    (framePolynomial u).totalDegree ≤ gridBound d := by
  classical
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _c : Fin 2 × Fin 2 ↪ Fin d, 2 :=
      Finset.sum_le_sum fun c _ => minorPolynomial_degree u c
    _ = gridBound d := by simp only [gridBound, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_comm]

set_option maxHeartbeats 800000 in
private lemma common_grid {d : ℕ} (hd : 4 ≤ d) (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u ∈ Matrix.specialUnitaryGroup (Fin d) ℂ) :
    ∃ v ∈ grid d, ∀ c : Fin 2 × Fin 2 ↪ Fin d, minor c (u *ᵥ v) ≠ 0 := by
  classical
  obtain ⟨v, hv, hfv⟩ := grid_eval_nonzero (framePolynomial u)
    (framePolynomial_nonzero u hu) (framePolynomial_degree u)
  have hc : ∀ c : Fin 2 × Fin 2 ↪ Fin d, minor c (u *ᵥ v) ≠ 0 := by
    have hprod : (∏ c : Fin 2 × Fin 2 ↪ Fin d,
        MvPolynomial.eval v (minorPolynomial u c)) ≠ 0 := by
      simpa only [framePolynomial, map_prod] using hfv
    intro c
    rw [← minorPolynomial_eval]
    exact Finset.prod_ne_zero_iff.mp hprod c (Finset.mem_univ c)
  have hv0 : v ≠ 0 := by
    intro h
    let c : Fin 2 × Fin 2 ↪ Fin d :=
      (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).toEmbedding.trans (Fin.castLEEmb hd)
    have hz := hc c
    simp only [h, Matrix.mulVec_zero, minor, Pi.zero_apply, mul_zero, sub_zero] at hz
    exact hz rfl
  exact ⟨v, Finset.mem_filter.mpr ⟨hv, hv0⟩, hc⟩

private def mass {d : ℕ} (v : Fin d → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

private noncomputable def pure {d : ℕ} (v : Fin d → ℂ) :
    Matrix (Fin d) (Fin d) ℂ := (mass v)⁻¹ • rankOneDensity v

private lemma mass_pos {d : ℕ} (v : Fin d → ℂ) (hv : v ≠ 0) : 0 < mass v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  exact (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j))
    (Finset.mem_univ i)).trans_lt' (Complex.normSq_pos.mpr hi)

private lemma pure_density {d : ℕ} (v : Fin d → ℂ) (hv : v ≠ 0) :
    (pure v).PosSemidef ∧ (pure v).trace = 1 := by
  refine ⟨(Matrix.posSemidef_vecMulVec_self_star v).smul (inv_nonneg.mpr
    (mass_pos v hv).le), ?_⟩
  have htr : (rankOneDensity v).trace = (mass v : ℂ) := by
    simp only [rankOneDensity, Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply,
      Pi.star_apply, Complex.star_def, Complex.mul_conj, mass, Complex.ofReal_sum]
  rw [pure, Matrix.trace_smul, htr, Complex.real_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (mass_pos v hv).ne', Complex.ofReal_one]

private lemma pure_transform {d : ℕ} (u : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    u * pure v * star u = (mass v)⁻¹ • rankOneDensity (u *ᵥ v) := by
  rw [pure, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [rankOneDensity, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.star_eq_conjTranspose, ← Matrix.star_mulVec]
  rfl

private lemma productState_density {d : ℕ} (p : Partition d)
    (τ : (i : Fin p.val.1) → Matrix (Fin (p.val.2 i)) (Fin (p.val.2 i)) ℂ)
    (hτ : ∀ i, (τ i).PosSemidef ∧ (τ i).trace = 1) :
    (productState p τ).PosSemidef ∧ (productState p τ).trace = 1 := by
  classical
  constructor
  · have h (s : Finset (Fin p.val.1)) :
        Matrix.PosSemidef (fun x y : Fin d => ∏ i ∈ s,
          τ i ((partitionEquiv p).symm x i) ((partitionEquiv p).symm y i)) := by
      induction s using Finset.induction_on with
      | empty =>
        simpa only [Finset.prod_empty, Matrix.vecMulVec_apply, Pi.star_apply, star_one,
          mul_one] using Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin d => (1 : ℂ))
      | @insert i s hi ih =>
        simpa only [Finset.prod_insert hi, Matrix.hadamard_apply] using
          ((hτ i).1.submatrix (fun x => (partitionEquiv p).symm x i)).hadamard ih
    exact h Finset.univ
  · change (∑ x : Fin d, ∏ i,
      τ i ((partitionEquiv p).symm x i) ((partitionEquiv p).symm x i)) = 1
    rw [← (partitionEquiv p).sum_comp (fun x : Fin d =>
      ∏ i, τ i ((partitionEquiv p).symm x i) ((partitionEquiv p).symm x i))]
    simp only [Equiv.symm_apply_apply]
    exact (Fintype.prod_sum (fun i (x : Fin (p.val.2 i)) => τ i x x)).symm.trans
      (Finset.prod_eq_one fun i _ => (hτ i).2)

private lemma productState_column_minor {d : ℕ} (p : Partition d)
    (τ : (i : Fin p.val.1) → Matrix (Fin (p.val.2 i)) (Fin (p.val.2 i)) ℂ)
    (j : Fin d) : minor (corner p) (fun i => productState p τ i j) = 0 := by
  classical
  simp only [minor, productState, corner, Equiv.symm_apply_apply]
  apply sub_eq_zero.mpr
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h0 : i.val = 0
  · simp only [h0, ↓reduceIte]
  · by_cases h1 : i.val = 1 <;> simp [h0, h1]

private lemma summand_kernel {d : ℕ} {ι : Type} [Fintype ι]
    (w : ι → ℝ) (a : ι → Matrix (Fin d) (Fin d) ℂ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, (a i).PosSemidef)
    (v : Fin d → ℂ) (t : ℝ) (hs : ∑ i, w i • a i = t • rankOneDensity v)
    (j : ι) (hj : 0 < w j) (x : Fin d → ℂ) (hx : star v ⬝ᵥ x = 0) :
    a j *ᵥ x = 0 := by
  have hsum : ∑ i, (w i : ℂ) * (star x ⬝ᵥ a i *ᵥ x) = 0 := by
    calc
      _ = star x ⬝ᵥ (∑ i, w i • a i) *ᵥ x := by
        simp only [Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec,
          dotProduct_smul, Complex.real_smul]
      _ = 0 := by
        rw [hs, Matrix.smul_mulVec, rankOneDensity, Matrix.vecMulVec_mulVec, hx]
        simp
  have hjzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    mul_nonneg (Complex.zero_le_real.mpr (hw i)) ((ha i).dotProduct_mulVec_nonneg x))).mp
      hsum j (Finset.mem_univ j)
  apply (ha j).dotProduct_mulVec_zero_iff.mp
  exact (mul_eq_zero.mp hjzero).resolve_left (by exact_mod_cast hj.ne')

private lemma supported_column {d : ℕ} (v : Fin d → ℂ) (hv : v ≠ 0)
    (a : Matrix (Fin d) (Fin d) ℂ) (ha : a.IsHermitian)
    (hker : ∀ x, star v ⬝ᵥ x = 0 → a *ᵥ x = 0) (j : Fin d) :
    ∃ z : ℂ, (fun k => a k j) = z • v := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  refine ⟨a i j / v i, ?_⟩
  funext k
  have hx : star v ⬝ᵥ (Pi.single k (star (v i)) - Pi.single i (star (v k))) = 0 := by
    simp only [dotProduct_sub, dotProduct_single, Pi.star_apply]
    ring
  have h := congrFun (hker _ hx) j
  simp only [Matrix.mulVec_sub, Matrix.mulVec_single, Pi.sub_apply, Pi.zero_apply,
    Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Matrix.col_apply] at h
  have h' := congrArg star h
  simp only [star_sub, star_mul, star_star, star_zero, ha.apply] at h'
  change a k j = a i j / v i * v k
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hi).mpr
  linear_combination h'

private lemma separable_pure_minor {d : ℕ} (p : Partition d) (v : Fin d → ℂ)
    (t : ℝ) (hs : Separable p (t • rankOneDensity v)) :
    minor (corner p) v = 0 := by
  classical
  by_cases hv : v = 0
  · simp only [hv, minor, Pi.zero_apply, mul_zero, sub_zero]
  obtain ⟨ι, inst, w, a, hw, h1, ha, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hs
  let := inst
  choose τ hτ hτa using ha
  have hapsd : ∀ i, (a i).PosSemidef := by
    intro i
    rw [hτa i]
    exact (productState_density p (τ i) (hτ i)).1
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hw i)).mp
    (show 0 < ∑ i, w i by rw [h1]; norm_num)
  have htrace : (a j).trace = 1 := by
    rw [hτa j]
    exact (productState_density p (τ j) (hτ j)).2
  obtain ⟨k, hk⟩ : ∃ k, a j k k ≠ 0 := by
    by_contra! h
    simp only [Matrix.trace, Matrix.diag, h, Finset.sum_const_zero] at htrace
    exact zero_ne_one htrace
  obtain ⟨z, hz⟩ := supported_column v hv (a j) (hapsd j).1
    (fun x hx => summand_kernel w a hw hapsd v t hsum j hj x hx) k
  have hz0 : z ≠ 0 := by
    intro h
    have he := congrFun hz k
    simp only [h, zero_smul, Pi.zero_apply] at he
    exact hk he
  have hm : minor (corner p) (fun i => a j i k) = 0 := by
    rw [hτa j]
    exact productState_column_minor p (τ j) k
  rw [hz] at hm
  have he : minor (corner p) (z • v) = z ^ 2 * minor (corner p) v := by
    simp only [minor, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he] at hm
  exact (mul_eq_zero.mp hm).resolve_left (pow_ne_zero 2 hz0)

theorem result : claim := by
  classical
  intro d a b ha hb hd
  have hd4 : 4 ≤ d := by nlinarith
  refine ⟨(grid d).image pure, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hρ
    exact pure_density v (Finset.mem_filter.mp hv).2
  · intro u hu
    obtain ⟨v, hv, hminor⟩ := common_grid hd4 u hu
    refine ⟨pure v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
    intro p hs
    rw [pure_transform] at hs
    exact hminor ⟨corner p, corner_injective p⟩
      (separable_pure_minor p (u *ᵥ v) (mass v)⁻¹ hs)

end D5.S3.Quantum.Entanglement.Witness.AbsolutelyEntangledAllPartitions
