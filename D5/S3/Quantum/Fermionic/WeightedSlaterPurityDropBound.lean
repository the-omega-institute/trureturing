/- GID: D5/S3/Quantum/Fermionic/WeightedSlaterPurityDropBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/WeightedSlaterPurityDropBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pivot-column lower bound for a strict purity drop of an ordered Slater marginal. -/

import D5.S3.Quantum.Fermionic.WeightedSlaterPairCut

/-! Quantitative purity decrease from balancing a retained endpoint pair. -/

open scoped BigOperators Matrix

namespace D5.S3.Quantum.Fermionic.WeightedSlaterPurityDropBound

private def realSign : AddChar (ZMod 2) ℝ :=
  AddChar.zmodChar 2 (ζ := (-1 : ℝ)) (by simp)

private def diffMass (p : ℝ) (b : ZMod 2) : ℝ :=
  if b = 0 then (1 - p) ^ 2 + p ^ 2 else 2 * p * (1 - p)

private def squaredBias (p : ℝ) : ℝ := (1 - 2 * p) ^ 2

private def parityFactor (p : ℝ) (a : ZMod 2) : ℝ :=
  if a = 0 then 1 else squaredBias p

open Classical in
private noncomputable def puritySum {U V : Type*} [Fintype U] [Fintype V]
    (A : Matrix U V (ZMod 2)) (p : U → ℝ) (q : V → ℝ) : ℝ :=
  ∑ z : U → ZMod 2, (∏ k, diffMass (p k) (z k)) *
    ∏ j, parityFactor (q j) ((Aᵀ *ᵥ z) j)

private theorem sum_difference_moment (p : ℝ) (a : ZMod 2) :
    ∑ b : ZMod 2, diffMass p b * realSign (a * b) = parityFactor p a := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have hone : realSign (1 : ZMod 2) = -1 := by
    have hval : (1 : ZMod 2).val = 1 := rfl
    norm_num [realSign, AddChar.zmodChar_apply, hval]
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) a with rfl | rfl <;>
    simp [huniv, diffMass, parityFactor, squaredBias, hone] <;> ring

open Classical in
private theorem sum_product_difference_moment {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (a : ι → ZMod 2) :
    ∑ w : ι → ZMod 2, (∏ i, diffMass (p i) (w i)) * realSign (a ⬝ᵥ w) =
      ∏ i, parityFactor (p i) (a i) := by
  have hchar (w : ι → ZMod 2) : realSign (a ⬝ᵥ w) = ∏ i, realSign (a i * w i) := by
    change (realSign.toAddMonoidHom (∑ i, a i * w i)).toMul =
      ∏ i, (realSign.toAddMonoidHom (a i * w i)).toMul
    rw [map_sum, toMul_sum]
  simp_rw [hchar, ← Finset.prod_mul_distrib, ← sum_difference_moment]
  exact (Fintype.prod_sum (fun i b => diffMass (p i) b * realSign (a i * b))).symm

open Classical in
private theorem exchange_difference_side {U V : Type*}
    [Fintype U] [Fintype V]
    (A : Matrix U V (ZMod 2)) (p : U → ℝ) (q : V → ℝ) :
    (∑ z : U → ZMod 2, (∏ i, diffMass (p i) (z i)) *
        (∏ j, parityFactor (q j) ((Aᵀ *ᵥ z) j))) =
      ∑ w : V → ZMod 2, (∏ j, diffMass (q j) (w j)) *
        (∏ i, parityFactor (p i) ((A *ᵥ w) i)) := by
  simp_rw [← sum_product_difference_moment, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => ?_
  have hdot : (Aᵀ *ᵥ z) ⬝ᵥ w = (A *ᵥ w) ⬝ᵥ z := by
    rw [dotProduct_comm (Aᵀ *ᵥ z) w, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  rw [hdot]
  ring

private theorem diffMass_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (w : ZMod 2) :
    0 ≤ diffMass p w := by
  by_cases h : w = 0
  · simp only [diffMass, h, ite_true]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · simp only [diffMass, h, ite_false]
    exact mul_nonneg (mul_nonneg (by norm_num) h0) (sub_nonneg.mpr h1)

open Classical in
private theorem difference_from_balancing {U V : Type*}
    [Fintype U] [DecidableEq U] [Fintype V]
    (A : Matrix U V (ZMod 2)) (p : U → ℝ) (q : V → ℝ) (i : U) :
    puritySum A p q - puritySum A (Function.update p i (1 / 2)) q =
      ∑ w : V → ZMod 2, if (A *ᵥ w) i = 0 then 0 else
        (∏ j, diffMass (q j) (w j)) * squaredBias (p i) *
          ∏ k ∈ Finset.univ.erase i, parityFactor (p k) ((A *ᵥ w) k) := by
  rw [puritySum, puritySum, exchange_difference_side, exchange_difference_side,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  have heq : (∏ k ∈ Finset.univ.erase i,
        parityFactor ((Function.update p i (1 / 2)) k) ((A *ᵥ w) k)) =
      ∏ k ∈ Finset.univ.erase i, parityFactor (p k) ((A *ᵥ w) k) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [← Finset.mul_prod_erase _ (fun k => parityFactor (p k) ((A *ᵥ w) k)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun k =>
      parityFactor ((Function.update p i (1 / 2)) k) ((A *ᵥ w) k)) (Finset.mem_univ i),
    heq, Function.update_self]
  by_cases hi : (A *ᵥ w) i = 0
  · simp [parityFactor, hi]
  · simp [parityFactor, hi, squaredBias]
    ring

open OrderedSlaterCut SlaterPairCutRank

private def endpointMass (p : ℝ) (e : Bool) : ℂ := if e then (p : ℂ) else ↑(1 - p)

private theorem endpointMass_difference (p : ℝ) (z : ZMod 2) :
    ∑ v : ZMod 2, endpointMass p (pickEndpoint v) * endpointMass p (pickEndpoint (v + z)) =
      (diffMass p z : ℂ) := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have hsum : (1 : ZMod 2) + 1 = 0 := by decide
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) z with rfl | rfl <;>
    norm_num [huniv, hsum, endpointMass, pickEndpoint, diffMass] <;> ring

private theorem endpointMass_parity (p : ℝ) (a : ZMod 2) :
    (∑ v : ZMod 2, endpointMass p (pickEndpoint v) * binarySign (a * v)) ^ 2 =
      (parityFactor p a : ℂ) := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have hone : binarySign (1 : ZMod 2) = -1 := by
    have hval : (1 : ZMod 2).val = 1 := rfl
    norm_num [binarySign, AddChar.zmodChar_apply, hval]
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) a with rfl | rfl
  · norm_num [huniv, endpointMass, pickEndpoint, parityFactor]
  · norm_num [huniv, endpointMass, pickEndpoint, parityFactor, squaredBias, hone]
    ring

open Classical in
private theorem marginal_eq_real {ι : Type*} [LinearOrder ι] [Fintype ι]
    {m n : ℕ} {I : Set ι} (left : (Fin m × Bool) ↪ I) (right : (Fin n × Bool) ↪ ↥(Iᶜ))
    (hl : ∀ k, (left (k, false) : ι) < left (k, true))
    (hr : ∀ j, (right (j, false) : ι) < right (j, true))
    (weight : Fin (m + n) → Bool → ℂ) (p : Fin m → ℝ) (q : Fin n → ℝ)
    (hp : ∀ k e, weight (Fin.castAdd n k) e * star (weight (Fin.castAdd n k) e) =
      endpointMass (p k) e)
    (hq : ∀ j e, weight (Fin.natAdd m j) e * star (weight (Fin.natAdd m j) e) =
      endpointMass (q j) e) :
    let A := alternationMatrix (fun k e => (left (k, e) : ι)) (fun j e => (right (j, e) : ι))
    let B := orderedCut I (cutPairOrbitals left right weight)
    (((B * Bᴴ) ^ 2).trace).re = puritySum A p q := by
  intro A B
  have h := WeightedSlaterPairCut.orderedMarginal_purity left right hl hr weight
  dsimp only at h
  change (((B * Bᴴ) ^ 2).trace).re = _
  rw [h]
  simp_rw [hp, hq, endpointMass_difference, ← Finset.prod_pow, endpointMass_parity]
  simp only [← Complex.ofReal_prod, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  unfold puritySum
  apply Finset.sum_congr
  · ext z
    simp only [Finset.mem_univ]
  · intro z _
    rfl

open Classical in
private theorem pivot_fiber_mass_ge {P F W : Type*} [Fintype P] [Fintype F] [AddCommGroup W]
    (pivot : (P → ZMod 2) →+ W) (free : (F → ZMod 2) →+ W) (target : W)
    (covered : ∀ y, ∃ x, pivot x = free y) (feasible : ∃ x, pivot x = target)
    (p : P → ZMod 2 → ℝ) (q : F → ZMod 2 → ℝ) (a : P → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hp : ∀ j bit, a j ≤ p j bit)
    (hq : ∀ j bit, 0 ≤ q j bit) (hqsum : ∀ j, ∑ bit, q j bit = 1) :
    (∏ j, a j) ≤ ∑ y : F → ZMod 2, ∑ x : P → ZMod 2,
      if pivot x + free y = target then (∏ j, p j (x j)) * ∏ j, q j (y j) else 0 := by
  obtain ⟨x₀, hx₀⟩ := feasible
  calc
    (∏ j, a j) = ∑ y : F → ZMod 2, (∏ j, a j) * ∏ j, q j (y j) := by
      rw [← Finset.mul_sum, ← Fintype.prod_sum]
      simp_rw [hqsum, Finset.prod_const_one, mul_one]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro y _
      obtain ⟨x₁, hx₁⟩ := covered y
      let x := x₀ - x₁
      have hx : pivot x + free y = target := by
        dsimp [x]
        rw [map_sub, hx₀, hx₁, sub_add_cancel]
      have hqprod : 0 ≤ ∏ j, q j (y j) := Finset.prod_nonneg fun j _ => hq j (y j)
      calc
        (∏ j, a j) * ∏ j, q j (y j) ≤ (∏ j, p j (x j)) * ∏ j, q j (y j) :=
          mul_le_mul_of_nonneg_right
            (Finset.prod_le_prod₀ (fun j _ => ha j) (fun j _ => hp j (x j))) hqprod
        _ ≤ _ := by
          let term (z : P → ZMod 2) :=
            if pivot z + free y = target then (∏ j, p j (z j)) * ∏ j, q j (y j) else 0
          have hterm (z : P → ZMod 2) : 0 ≤ term z := by
            unfold term
            split
            · exact mul_nonneg (Finset.prod_nonneg fun j _ => (ha j).trans (hp j (z j))) hqprod
            · exact le_rfl
          have hsingle : term x ≤ ∑ z, term z :=
            Finset.single_le_sum (fun z _ => hterm z) (Finset.mem_univ x)
          simpa only [term, hx, ite_true] using hsingle
private theorem diffMass_sum (q : ℝ) : ∑ b : ZMod 2, diffMass q b = 1 := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  simp [huniv, diffMass]
  ring

private theorem diffMass_lower (q : ℝ) (b : ZMod 2) :
    2 * q * (1 - q) ≤ diffMass q b := by
  by_cases hb : b = 0
  · simp only [diffMass, hb, ite_true]
    nlinarith [sq_nonneg (1 - 2 * q)]
  · simp [diffMass, hb]

private theorem squaredBias_le_one {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    squaredBias p ≤ 1 := by
  unfold squaredBias
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

private theorem parityFactor_nonneg (p : ℝ) (a : ZMod 2) : 0 ≤ parityFactor p a := by
  by_cases ha : a = 0
  · simp [parityFactor, ha]
  · simpa only [parityFactor, ha, ite_false, squaredBias] using sq_nonneg (1 - 2 * p)

private theorem deterministic_probability {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (h : ¬ (0 < q ∧ q < 1)) : q = 0 ∨ q = 1 := by
  by_cases hz : q = 0
  · exact Or.inl hz
  · have hpos : 0 < q := lt_of_le_of_ne h0 (fun heq => hz heq.symm)
    exact Or.inr (le_antisymm h1 (le_of_not_gt fun hlt => h ⟨hpos, hlt⟩))

open Classical in
private theorem mulVec_restrict_active {U V : Type*} [Fintype V]
    (A : Matrix U V (ZMod 2)) (q : V → ℝ) (w : V → ZMod 2)
    (hsupport : ∀ j, ¬ (0 < q j ∧ q j < 1) → w j = 0) (k : U) :
    (A *ᵥ w) k = ∑ j : {j : V // 0 < q j ∧ q j < 1}, A k j * w j := by
  change (∑ j : V, A k j * w j) = _
  rw [← Finset.subtype_univ, Finset.sum_subtype_eq_sum_filter (fun j => A k j * w j)]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j _ hj
  rw [hsupport j (by simpa using hj), mul_zero]

open Classical in
private theorem split_fiber_mass_ge {R L P F : Type*}
    [Fintype L] [DecidableEq L] [Fintype P]
    (C : Matrix R L (ZMod 2)) (split : P ⊕ F ≃ L) (target : R → ZMod 2)
    (q : L → ℝ) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1)
    (hspan : Submodule.span (ZMod 2) (Set.range fun j : P => C.col (split (.inl j))) =
      Submodule.span (ZMod 2) (Set.range C.col))
    (hsol : ∃ w, C *ᵥ w = target) :
    (∏ j : P, 2 * q (split (.inl j)) * (1 - q (split (.inl j)))) ≤
      ∑ w : L → ZMod 2, if C *ᵥ w = target then ∏ j, diffMass (q j) (w j) else 0 := by
  let : Finite F := Finite.of_injective (fun j => split (.inr j))
    (fun _ _ h => Sum.inr.inj (split.injective h))
  let := Fintype.ofFinite F
  let Cp : Matrix R P (ZMod 2) := fun r j => C r (split (.inl j))
  let Cf : Matrix R F (ZMod 2) := fun r j => C r (split (.inr j))
  have hrange : LinearMap.range Cp.mulVecLin = LinearMap.range C.mulVecLin := by
    rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
    exact hspan
  have hfree : LinearMap.range Cf.mulVecLin ≤ LinearMap.range Cp.mulVecLin := by
    rw [hrange, Matrix.range_mulVecLin, Matrix.range_mulVecLin]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨split (.inr j), rfl⟩
  have hcovered (y : F → ZMod 2) : ∃ x, Cp *ᵥ x = Cf *ᵥ y :=
    LinearMap.mem_range.mp (hfree (LinearMap.mem_range_self Cf.mulVecLin y))
  have hfeasible : ∃ x, Cp *ᵥ x = target := by
    have h : target ∈ LinearMap.range C.mulVecLin := LinearMap.mem_range.mpr hsol
    exact LinearMap.mem_range.mp (hrange.symm ▸ h)
  let splitBits : (L → ZMod 2) ≃ (P → ZMod 2) × (F → ZMod 2) :=
    (split.symm.arrowCongr (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow P F _)
  have hsum (w : L → ZMod 2) : C *ᵥ w =
      Cp *ᵥ (splitBits w).1 + Cf *ᵥ (splitBits w).2 := by
    funext r
    change (∑ j : L, C r j * w j) =
      (∑ j : P, C r (split (.inl j)) * w (split (.inl j))) +
        ∑ j : F, C r (split (.inr j)) * w (split (.inr j))
    rw [← Fintype.sum_sum_type (fun j : P ⊕ F => C r (split j) * w (split j))]
    exact Fintype.sum_equiv split.symm _ _ fun j => by rw [split.apply_symm_apply]
  have hprod (w : L → ZMod 2) : (∏ j, diffMass (q j) (w j)) =
      (∏ j : P, diffMass (q (split (.inl j))) ((splitBits w).1 j)) *
        ∏ j : F, diffMass (q (split (.inr j))) ((splitBits w).2 j) := by
    change (∏ j : L, diffMass (q j) (w j)) =
      (∏ j : P, diffMass (q (split (.inl j))) (w (split (.inl j)))) *
        ∏ j : F, diffMass (q (split (.inr j))) (w (split (.inr j)))
    rw [← Fintype.prod_sum_type (fun j : P ⊕ F => diffMass (q (split j)) (w (split j)))]
    exact Fintype.prod_equiv split.symm _ _ fun j => by rw [split.apply_symm_apply]
  rw [Fintype.sum_equiv splitBits _
    (fun xy => if Cp *ᵥ xy.1 + Cf *ᵥ xy.2 = target then
      (∏ j : P, diffMass (q (split (.inl j))) (xy.1 j)) *
        ∏ j : F, diffMass (q (split (.inr j))) (xy.2 j) else 0)
    (fun w => by rw [hsum, hprod])]
  rw [Fintype.sum_prod_type_right]
  exact pivot_fiber_mass_ge Cp.mulVecLin.toAddMonoidHom Cf.mulVecLin.toAddMonoidHom
    target hcovered hfeasible _ _ _ (fun j => by
      exact mul_nonneg (mul_nonneg (by norm_num) (hq0 _)) (sub_nonneg.mpr (hq1 _)))
    (fun j b => diffMass_lower _ b)
    (fun j b => diffMass_nonneg (hq0 _) (hq1 _) b) (fun j => diffMass_sum _)

open Classical in
private theorem balancing_difference_ge_fiber {U V : Type*}
    [Fintype U] [DecidableEq U] [Fintype V]
    (A : Matrix U V (ZMod 2)) (p : U → ℝ) (q : V → ℝ) (i : U)
    (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1) :
    let R := {k : U // k = i ∨ p k = 1 / 2}
    let L := {j : V // 0 < q j ∧ q j < 1}
    let C : Matrix R L (ZMod 2) := fun k j => A k j
    let target : R → ZMod 2 := fun k => if k.val = i then 1 else 0
    let drop := puritySum A p q - puritySum A (Function.update p i (1 / 2)) q
    0 < drop →
      (∃ w, C *ᵥ w = target) ∧
      squaredBias (p i) * (∏ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ p k ≠ 1 / 2),
        squaredBias (p k)) *
        (∑ w : L → ZMod 2,
          if C *ᵥ w = target then ∏ j : L, diffMass (q j) (w j) else 0) ≤ drop := by
  intro R L C target drop hdrop
  let term (w : V → ZMod 2) :=
    if (A *ᵥ w) i = 0 then 0 else
      (∏ j, diffMass (q j) (w j)) * squaredBias (p i) *
        ∏ k ∈ Finset.univ.erase i, parityFactor (p k) ((A *ᵥ w) k)
  have hidentity : drop = ∑ w, term w := difference_from_balancing A p q i
  have hmass (w : V → ZMod 2) : 0 ≤ ∏ j, diffMass (q j) (w j) :=
    Finset.prod_nonneg fun j _ => diffMass_nonneg (hq0 j) (hq1 j) (w j)
  have hterm (w : V → ZMod 2) : 0 ≤ term w := by
    unfold term
    split
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg (hmass w) (sq_nonneg _))
        (Finset.prod_nonneg fun k _ => parityFactor_nonneg _ _)
  constructor
  · rw [hidentity, Finset.sum_pos_iff_of_nonneg (fun w _ => hterm w)] at hdrop
    obtain ⟨w, _, hw⟩ := hdrop
    have hi : (A *ᵥ w) i ≠ 0 := fun hz => by simp [term, hz] at hw
    have hsupport (j : V) (hj : ¬ (0 < q j ∧ q j < 1)) : w j = 0 := by
      by_contra hz
      have hzero : diffMass (q j) (w j) = 0 := by
        rcases deterministic_probability (hq0 j) (hq1 j) hj with h | h <;>
          simp [diffMass, h, hz]
      have hprod := Finset.prod_eq_zero (f := fun s => diffMass (q s) (w s))
        (Finset.mem_univ j) hzero
      simp [term, hi, hprod] at hw
    refine ⟨fun j => w j, funext fun k => ?_⟩
    change (∑ j : L, A k j * w j) = target k
    rw [← mulVec_restrict_active A q w hsupport]
    by_cases hk : k.val = i
    · have hone : (A *ᵥ w) i = 1 :=
        (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) _ |>.resolve_left hi
      simpa [target, hk] using hone
    · have hb := k.property.resolve_left hk
      have hzero : (A *ᵥ w) k = 0 := by
        by_contra hz
        have hfactor : parityFactor (p k) ((A *ᵥ w) k) = 0 := by
          norm_num [parityFactor, hz, squaredBias, hb]
        have hprod := Finset.prod_eq_zero (f := fun s : U => parityFactor (p s) ((A *ᵥ w) s))
          (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩) hfactor
        simp [term, hi, hprod] at hw
      simpa [target, hk] using hzero
  · let extend (w : L → ZMod 2) (j : V) :=
      if h : 0 < q j ∧ q j < 1 then w ⟨j, h⟩ else 0
    have extend_active (w : L → ZMod 2) (j : L) : extend w j = w j := by
      simp [extend, j.property]
    have extend_injective : Function.Injective extend := by
      intro w v he
      funext j
      simpa only [extend_active] using congrFun he (j : V)
    have extend_mass (w : L → ZMod 2) :
        (∏ j : L, diffMass (q j) (w j)) = ∏ j : V, diffMass (q j) (extend w j) := by
      simp_rw [← extend_active w]
      rw [← Finset.subtype_univ,
        Finset.prod_subtype_eq_prod_filter (fun j => diffMass (q j) (extend w j))]
      apply Finset.prod_subset (Finset.filter_subset _ _)
      intro j _ hj
      have hja : ¬ (0 < q j ∧ q j < 1) := by simpa using hj
      rcases deterministic_probability (hq0 j) (hq1 j) hja with h | h <;>
        simp [extend, diffMass, h]
    let biased := Finset.univ.filter (fun k => k ≠ i ∧ p k ≠ 1 / 2)
    let factor := squaredBias (p i) * ∏ k ∈ biased, squaredBias (p k)
    change factor * (∑ w : L → ZMod 2, if C *ᵥ w = target then
      ∏ j : L, diffMass (q j) (w j) else 0) ≤ drop
    rw [Finset.mul_sum, hidentity]
    refine Finset.sum_le_sum_of_injOn extend extend_injective.injOn (Finset.subset_univ _) ?_ ?_
    · intro w _
      by_cases hw : C *ᵥ w = target
      · have hrow (k : R) : (A *ᵥ extend w) k = target k := by
          rw [mulVec_restrict_active A q (extend w) (fun j h => by simp [extend, h])]
          have hvalue := congrFun hw k
          change (∑ j : L, A k j * w j) = target k at hvalue
          simpa only [extend_active] using hvalue
        have hi : (A *ᵥ extend w) i = 1 := by
          simpa [target] using hrow ⟨i, Or.inl rfl⟩
        have hfactor : (∏ k ∈ biased, squaredBias (p k)) ≤
            ∏ k ∈ Finset.univ.erase i, parityFactor (p k) ((A *ᵥ extend w) k) := by
          calc
            _ ≤ ∏ k ∈ biased, parityFactor (p k) ((A *ᵥ extend w) k) := by
              apply Finset.prod_le_prod₀ (fun k _ => sq_nonneg _)
              intro k _
              by_cases hk : (A *ᵥ extend w) k = 0
              · simpa only [parityFactor, hk, ite_true] using squaredBias_le_one (hp0 k) (hp1 k)
              · simp [parityFactor, hk]
            _ = _ := by
              apply Finset.prod_subset
              · intro k hk
                exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hk).2.1, Finset.mem_univ _⟩
              · intro k hk hkb
                have hki := Finset.ne_of_mem_erase hk
                have hb : p k = 1 / 2 := by simpa [biased, hki] using hkb
                have hz : (A *ᵥ extend w) k = 0 := by
                  simpa [target, hki] using hrow ⟨k, Or.inr hb⟩
                simp [parityFactor, hz]
        simp only [hw, ite_true, extend_mass, term, hi, one_ne_zero, ite_false, factor]
        rw [mul_comm _ (∏ j, diffMass (q j) (extend w j)), ← mul_assoc]
        exact mul_le_mul_of_nonneg_left hfactor (mul_nonneg (hmass _) (sq_nonneg _))
      · simpa only [hw, ite_false, mul_zero] using hterm (extend w)
    · intro w _ _
      exact hterm w

set_option maxHeartbeats 800000 in
open Classical in
/-- A strict purity drop from balancing a retained pair is bounded below by its squared bias,
the product of the other nonzero squared biases, and the one-bit masses of any pivot column
basis on the nondeterministic discarded pairs. The row restriction consists of the selected
pair and all initially balanced retained pairs. -/
theorem orderedMarginal_purity_drop_lower_bound {ι : Type*} [LinearOrder ι] [Fintype ι]
    {m n : ℕ} {I : Set ι} (left : (Fin m × Bool) ↪ I) (right : (Fin n × Bool) ↪ ↥(Iᶜ))
    (hl : ∀ k, (left (k, false) : ι) < left (k, true))
    (hr : ∀ j, (right (j, false) : ι) < right (j, true))
    (before after : Fin (m + n) → Bool → ℂ) (p : Fin m → ℝ) (q : Fin n → ℝ) (i : Fin m)
    (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1)
    (hp : ∀ k e, before (Fin.castAdd n k) e * star (before (Fin.castAdd n k) e) =
      (if e then (p k : ℂ) else ↑(1 - p k)))
    (hq : ∀ j e, before (Fin.natAdd m j) e * star (before (Fin.natAdd m j) e) =
      (if e then (q j : ℂ) else ↑(1 - q j)))
    (hp' : ∀ k e, after (Fin.castAdd n k) e * star (after (Fin.castAdd n k) e) =
      (if e then (Function.update p i (1 / 2) k : ℂ) else ↑(1 - Function.update p i (1 / 2) k)))
    (hq' : ∀ j e, after (Fin.natAdd m j) e * star (after (Fin.natAdd m j) e) =
      (if e then (q j : ℂ) else ↑(1 - q j)))
    {P F : Type*} [Fintype P]
    (split : P ⊕ F ≃ {j : Fin n // 0 < q j ∧ q j < 1}) :
    let A := alternationMatrix (fun k e => (left (k, e) : ι)) (fun j e => (right (j, e) : ι))
    let R := {k : Fin m // k = i ∨ p k = 1 / 2}
    let L := {j : Fin n // 0 < q j ∧ q j < 1}
    let C : Matrix R L (ZMod 2) := fun k j => A k j
    let purity (weight : Fin (m + n) → Bool → ℂ) :=
      let B := orderedCut I (cutPairOrbitals left right weight)
      (((B * Bᴴ) ^ 2).trace).re
    LinearIndependent (ZMod 2) (fun j : P => C.col (split (.inl j))) →
    Submodule.span (ZMod 2) (Set.range fun j : P => C.col (split (.inl j))) =
      Submodule.span (ZMod 2) (Set.range C.col) →
    purity after < purity before →
    (1 - 2 * p i) ^ 2 *
      (∏ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ p k ≠ 1 / 2), (1 - 2 * p k) ^ 2) *
      (∏ j : P, 2 * q (split (.inl j)) * (1 - q (split (.inl j)))) ≤
        purity before - purity after := by
  intro A R L C purity _ hspan hstrict
  have hbefore : purity before = puritySum A p q :=
    marginal_eq_real left right hl hr before p q hp hq
  have hafter : purity after = puritySum A (Function.update p i (1 / 2)) q :=
    marginal_eq_real left right hl hr after _ q hp' hq'
  rw [hbefore, hafter] at hstrict ⊢
  obtain ⟨hsol, hdrop⟩ :=
    balancing_difference_ge_fiber A p q i hp0 hp1 hq0 hq1 (sub_pos.mpr hstrict)
  let target : R → ZMod 2 := fun k => if k.val = i then 1 else 0
  let activeDecidableEq : DecidableEq {j : Fin n // 0 < q j ∧ q j < 1} :=
    @Subtype.instDecidableEq (Fin n) _ (fun _ _ => Classical.propDecidable _)
  have hpivot := @split_fiber_mass_ge R {j : Fin n // 0 < q j ∧ q j < 1} P F
    inferInstance activeDecidableEq inferInstance C split target
    (fun j => q j) (fun j => hq0 j) (fun j => hq1 j) hspan hsol
  refine (mul_le_mul_of_nonneg_left hpivot
    (mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun _ _ => sq_nonneg _))).trans ?_
  convert hdrop using 2
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : C *ᵥ w = target
  · simp [C, target] at hw ⊢
    simp [hw]
  · simp [C, target] at hw ⊢
    simp [hw]

end D5.S3.Quantum.Fermionic.WeightedSlaterPurityDropBound
