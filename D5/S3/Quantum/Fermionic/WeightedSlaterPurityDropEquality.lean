/- GID: D5/S3/Quantum/Fermionic/WeightedSlaterPurityDropEquality
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/WeightedSlaterPurityDropEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equality and strict excess in the positive weighted binary fiber bound. -/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Equality in the weighted binary fiber bound

A positive free-assignment law detects every strict increase in a pivot mass or a retained
row factor. On the affine fiber, constancy of a linear form is tested by the span of the
homogeneous constraints. -/

namespace D5.S3.Quantum.Fermionic.WeightedSlaterPurityDropEquality

open scoped Matrix

public section

private theorem weighted_product_excess_of_lt {Y I : Type*} [Fintype Y] [Fintype I]
    (weight : Y → ℝ) (lower : I → ℝ) (factor : Y → I → ℝ)
    (hweight : ∀ y, 0 < weight y) (hnorm : ∑ y, weight y = 1)
    (hlower : ∀ i, 0 < lower i) (hle : ∀ y i, lower i ≤ factor y i)
    (y : Y) (i : I) (hlt : lower i < factor y i) :
    (∏ j, lower j) < ∑ z, weight z * ∏ j, factor z j := by
  calc
    (∏ j, lower j) = ∑ z, weight z * ∏ j, lower j := by
      rw [← Finset.sum_mul, hnorm, one_mul]
    _ < _ := Finset.sum_lt_sum
      (fun z _ => mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod₀ (fun j _ => (hlower j).le) (fun j _ => hle z j)) (hweight z).le)
      ⟨y, Finset.mem_univ _, mul_lt_mul_of_pos_left
        (Finset.prod_lt_prod₀ (fun j _ => hlower j) (fun j _ => hle y j)
          ⟨i, Finset.mem_univ _, hlt⟩) (hweight y)⟩

/-- A positive law on free assignments gives equality exactly when each untied pivot
bit and each row with bias factor below one is one throughout the assignment space. -/
theorem weighted_product_eq_iff {Y P R : Type*} [Fintype Y] [Fintype P] [Fintype R]
    (weight : Y → ℝ) (mass : P → ZMod 2 → ℝ) (bias : R → ℝ)
    (pivotBit : P → Y → ZMod 2) (rowBit : R → Y → ZMod 2)
    (hweight : ∀ y, 0 < weight y) (hnorm : ∑ y, weight y = 1)
    (hmass : ∀ j, 0 < mass j 1) (hpivot : ∀ j, mass j 1 ≤ mass j 0)
    (hbias : ∀ k, 0 < bias k) (hrow : ∀ k, bias k ≤ 1) :
    (∑ y, weight y * ((∏ j, mass j (pivotBit j y)) *
      ∏ k, if rowBit k y = 1 then bias k else 1)) =
      (∏ j, mass j 1) * (∏ k, bias k) ↔
      (∀ j, mass j 1 < mass j 0 → ∀ y, pivotBit j y = 1) ∧
      (∀ k, bias k < 1 → ∀ y, rowBit k y = 1) := by
  let lower : P ⊕ R → ℝ := Sum.elim (fun j => mass j 1) bias
  let factor (y : Y) : P ⊕ R → ℝ := Sum.elim (fun j => mass j (pivotBit j y))
    (fun k => if rowBit k y = 1 then bias k else 1)
  have binary : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  have hlower (i : P ⊕ R) : 0 < lower i := by
    cases i with
    | inl j => exact hmass j
    | inr k => exact hbias k
  have hle (y : Y) (i : P ⊕ R) : lower i ≤ factor y i := by
    cases i with
    | inl j =>
      rcases binary (pivotBit j y) with h | h
      · simpa [lower, factor, h] using hpivot j
      · simp [lower, factor, h]
    | inr k =>
      by_cases h : rowBit k y = 1
      · simp [lower, factor, h]
      · simpa [lower, factor, h] using hrow k
  have hlowerProd : (∏ i, lower i) = (∏ j, mass j 1) * ∏ k, bias k := by
    rw [Fintype.prod_sum_type]
    rfl
  have hfactorProd (y : Y) : (∏ i, factor y i) =
      (∏ j, mass j (pivotBit j y)) * ∏ k, if rowBit k y = 1 then bias k else 1 := by
    rw [Fintype.prod_sum_type]
    rfl
  simp_rw [← hlowerProd, ← hfactorProd]
  constructor
  · intro heq
    have noExcess (y : Y) (i : P ⊕ R) : ¬ lower i < factor y i := by
      intro hlt
      have h := weighted_product_excess_of_lt weight lower factor
        hweight hnorm hlower hle y i hlt
      exact (ne_of_lt h) heq.symm
    constructor
    · intro j hj y
      rcases binary (pivotBit j y) with h | h
      · exact False.elim (noExcess y (.inl j) (by simpa [lower, factor, h] using hj))
      · exact h
    · intro k hk y
      by_contra h
      exact noExcess y (.inr k) (by simpa [lower, factor, h] using hk)
  · rintro ⟨hp, hr⟩
    have heq (y : Y) (i : P ⊕ R) : factor y i = lower i := by
      cases i with
      | inl j =>
        by_cases hj : mass j 1 < mass j 0
        · simp [lower, factor, hp j hj y]
        · rcases binary (pivotBit j y) with h | h
          · simpa [lower, factor, h] using le_antisymm (le_of_not_gt hj) (hpivot j)
          · simp [lower, factor, h]
      | inr k =>
        by_cases hk : bias k < 1
        · simp [lower, factor, hr k hk y]
        · simp [lower, factor, le_antisymm (hrow k) (le_of_not_gt hk)]
    simp_rw [heq]
    rw [← Finset.sum_mul, hnorm, one_mul]

private theorem eq_one_on_fiber_iff_sub_mem {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) V)) (a r : Module.Dual (ZMod 2) V)
    (x₀ : V) (ha₀ : a x₀ = 1) (hS₀ : x₀ ∈ S.dualCoannihilator) :
    (∀ x, a x = 1 → x ∈ S.dualCoannihilator → r x = 1) ↔ r - a ∈ S := by
  constructor
  · intro h
    have hr₀ := h x₀ ha₀ hS₀
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := S), Submodule.mem_dualAnnihilator]
    intro v hv
    change r v - a v = 0
    have binary : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    rcases binary (a v) with ha | ha
    · have hr := h (x₀ + v) (by rw [map_add, ha₀, ha, add_zero]) (Submodule.add_mem _ hS₀ hv)
      rw [map_add, hr₀] at hr
      have hrv : r v = 0 := add_left_cancel (hr.trans (add_zero _).symm)
      rw [hrv, ha, sub_zero]
    · rw [h v ha hv, ha, sub_self]
  · intro h x hx hS
    have hz : (r - a) x = 0 := (Submodule.mem_dualCoannihilator x).mp hS _ h
    change r x - a x = 0 at hz
    exact (sub_eq_zero.mp hz).trans hx

/-- For a parametrization of the nonempty affine fiber, equality holds precisely when
each untied pivot coordinate and each strictly penalized row differs from the selected
row by an element of the span of the homogeneous constraints. -/
theorem weighted_affine_fiber_eq_iff {F P R V : Type*}
    [Fintype F] [DecidableEq F] [Fintype P] [Fintype R]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) V)) (a : Module.Dual (ZMod 2) V)
    (param : (F → ZMod 2) ≃ {x : V // a x = 1 ∧ x ∈ S.dualCoannihilator})
    (weight : (F → ZMod 2) → ℝ) (mass : P → ZMod 2 → ℝ) (bias : R → ℝ)
    (pivotBit : P → Module.Dual (ZMod 2) V) (rowBit : R → Module.Dual (ZMod 2) V)
    (hweight : ∀ y, 0 < weight y) (hnorm : ∑ y, weight y = 1)
    (hmass : ∀ j, 0 < mass j 1) (hpivot : ∀ j, mass j 1 ≤ mass j 0)
    (hbias : ∀ k, 0 < bias k) (hrow : ∀ k, bias k ≤ 1) :
    (∑ y, weight y * ((∏ j, mass j (pivotBit j (param y).val)) *
      ∏ k, if rowBit k (param y).val = 1 then bias k else 1)) =
      (∏ j, mass j 1) * (∏ k, bias k) ↔
      (∀ j, mass j 1 < mass j 0 → pivotBit j - a ∈ S) ∧
      (∀ k, bias k < 1 → rowBit k - a ∈ S) := by
  rw [weighted_product_eq_iff weight mass bias _ _ hweight hnorm hmass hpivot hbias hrow]
  let x₀ := param 0
  have hconst (r : Module.Dual (ZMod 2) V) :
      (∀ y, r (param y).val = 1) ↔ r - a ∈ S := by
    rw [← eq_one_on_fiber_iff_sub_mem S a r x₀.val x₀.property.1 x₀.property.2]
    constructor
    · intro h x ha hS
      obtain ⟨y, hy⟩ := param.surjective ⟨x, ha, hS⟩
      exact (congrArg (fun z => r z.val) hy).symm.trans (h y)
    · exact fun h y => h _ (param y).property.1 (param y).property.2
  simp_rw [hconst]

private noncomputable def fiberFreeEquiv {L P F T : Type*}
    [Fintype L] [Fintype P] [Fintype F]
    (C : Matrix T L (ZMod 2)) (split : P ⊕ F ≃ L) (target : T → ZMod 2)
    (hlin : LinearIndependent (ZMod 2) (fun j : P => C.col (split (.inl j))))
    (hspan : Submodule.span (ZMod 2) (Set.range fun j : P => C.col (split (.inl j))) =
      Submodule.span (ZMod 2) (Set.range C.col))
    (hsol : ∃ x, C *ᵥ x = target) :
    {x : L → ZMod 2 // C *ᵥ x = target} ≃ (F → ZMod 2) :=
  Equiv.ofBijective (fun x j => x.val (split (.inr j))) (by
    let Cp := C.submatrix id (split ∘ Sum.inl)
    let Cf := C.submatrix id (split ∘ Sum.inr)
    let join (p : P → ZMod 2) (f : F → ZMod 2) := Sum.elim p f ∘ split.symm
    have hjoin (p : P → ZMod 2) (f : F → ZMod 2) :
        C *ᵥ join p f = Cp *ᵥ p + Cf *ᵥ f := by
      funext t
      change (∑ j : L, C t j * join p f j) =
        (∑ j : P, C t (split (.inl j)) * p j) + ∑ j : F, C t (split (.inr j)) * f j
      rw [Fintype.sum_equiv split.symm _ (fun j => C t (split j) * Sum.elim p f j)
        (fun j => by simp [join]), Fintype.sum_sum_type]
      rfl
    have hdecomp (x : L → ZMod 2) :
        join (fun j => x (split (.inl j))) (fun j => x (split (.inr j))) = x := by
      funext j
      obtain ⟨j, rfl⟩ := split.surjective j
      cases j <;> simp [join]
    refine ⟨?_, ?_⟩
    · intro x x' hfree
      change (fun j => x.val (split (.inr j))) = (fun j => x'.val (split (.inr j))) at hfree
      have hval (v : {x : L → ZMod 2 // C *ᵥ x = target}) :
          Cp *ᵥ (fun j => v.val (split (.inl j))) + Cf *ᵥ (fun j => v.val (split (.inr j))) =
            target := by
        rw [← hjoin, hdecomp]
        exact v.property
      have h := hval x
      rw [hfree] at h
      have hp := (Matrix.mulVec_injective_iff (M := Cp)).mpr hlin
        (add_right_cancel (h.trans (hval x').symm))
      apply Subtype.ext
      calc
        x.val = join (fun j => x.val (split (.inl j))) (fun j => x.val (split (.inr j))) :=
          (hdecomp _).symm
        _ = x'.val := by rw [hp, hfree, hdecomp]
    · intro f
      have hf : Cf *ᵥ f ∈ LinearMap.range C.mulVecLin := by
        refine ⟨join 0 f, ?_⟩
        rw [Matrix.mulVecLin_apply, hjoin, Matrix.mulVec_zero, zero_add]
      have hp : target - Cf *ᵥ f ∈ LinearMap.range Cp.mulVecLin := by
        rw [Matrix.range_mulVecLin, show Cp.col = (fun j : P => C.col (split (.inl j))) from rfl,
          hspan, ← Matrix.range_mulVecLin]
        exact Submodule.sub_mem _ (LinearMap.mem_range.mpr hsol) hf
      obtain ⟨p, hp⟩ := LinearMap.mem_range.mp hp
      refine ⟨⟨join p f, ?_⟩, funext fun j => ?_⟩
      · rw [hjoin, ← Matrix.mulVecLin_apply, hp, sub_add_cancel]
      · simp [join])

open Classical in
/-- On the support of a positive binary law, the weighted lower bound for an affine
matrix fiber is attained exactly when every untied pivot unit row and every strictly
penalized row belongs to the selected row's coset of the span of the homogeneous rows.
The pivot columns can be any basis of the column space. -/
theorem weighted_pivot_fiber_eq_iff {L P F T R : Type*}
    [Fintype L] [DecidableEq L] [Fintype P] [Fintype F] [DecidableEq F]
    [DecidableEq T] [Fintype R]
    (C : Matrix T L (ZMod 2)) (i : T) (split : P ⊕ F ≃ L)
    (hlin : LinearIndependent (ZMod 2) (fun j : P => C.col (split (.inl j))))
    (hspan : Submodule.span (ZMod 2) (Set.range fun j : P => C.col (split (.inl j))) =
      Submodule.span (ZMod 2) (Set.range C.col))
    (hsol : ∃ x, C *ᵥ x = Pi.single i 1)
    (weight : (F → ZMod 2) → ℝ) (mass : P → ZMod 2 → ℝ) (bias : R → ℝ)
    (row : R → L → ZMod 2)
    (hweight : ∀ y, 0 < weight y) (hnorm : ∑ y, weight y = 1)
    (hmass : ∀ j, 0 < mass j 1) (hpivot : ∀ j, mass j 1 ≤ mass j 0)
    (hbias : ∀ k, 0 < bias k) (hrow : ∀ k, bias k ≤ 1) :
    let S := Submodule.span (ZMod 2) (Set.range fun k : {t : T // t ≠ i} => C k.val)
    (∑ x : L → ZMod 2, if C *ᵥ x = Pi.single i 1 then
      weight (fun j => x (split (.inr j))) *
        ((∏ j : P, mass j (x (split (.inl j)))) *
          ∏ k, if row k ⬝ᵥ x = 1 then bias k else 1) else 0) =
      (∏ j, mass j 1) * (∏ k, bias k) ↔
      (∀ j, mass j 1 < mass j 0 → Pi.single (split (.inl j)) 1 - C i ∈ S) ∧
      (∀ k, bias k < 1 → row k - C i ∈ S) := by
  intro S
  let d : (L → ZMod 2) →ₗ[ZMod 2] Module.Dual (ZMod 2) (L → ZMod 2) :=
    dotProductBilin (ZMod 2) (ZMod 2)
  have hd : Function.Injective d := by
    intro u v he
    funext j
    have hj := congrArg (fun f : Module.Dual (ZMod 2) (L → ZMod 2) => f (Pi.single j 1)) he
    change u ⬝ᵥ Pi.single j 1 = v ⬝ᵥ Pi.single j 1 at hj
    simpa only [dotProduct_single_one] using hj
  have hmapped (r : L → ZMod 2) : d r - d (C i) ∈ S.map d ↔ r - C i ∈ S := by
    rw [← map_sub, ← Submodule.mem_comap, Submodule.comap_map_eq_of_injective hd]
  have hfiber (x : L → ZMod 2) :
      C *ᵥ x = Pi.single i 1 ↔ d (C i) x = 1 ∧ x ∈ (S.map d).dualCoannihilator := by
    have hhom : x ∈ (S.map d).dualCoannihilator ↔
        ∀ k : {t : T // t ≠ i}, (C *ᵥ x) k.val = 0 := by
      change x ∈ ((S.map d).dualCoannihilator : Set (L → ZMod 2)) ↔ _
      simp only [S, Submodule.map_span, ← Set.range_comp, Submodule.coe_dualCoannihilator_span,
        Set.mem_ofPred_eq, Set.forall_mem_range, Function.comp_def]
      rfl
    rw [hhom]
    change _ ↔ (C *ᵥ x) i = 1 ∧ _
    constructor
    · intro hx
      rw [hx]
      exact ⟨Pi.single_eq_same i 1, fun k => Pi.single_eq_of_ne k.property 1⟩
    · rintro ⟨hi, hzero⟩
      funext k
      by_cases hk : k = i
      · subst k
        simpa using hi
      · simpa [Pi.single_eq_of_ne hk] using hzero ⟨k, hk⟩
  let freeEquiv := fiberFreeEquiv C split (Pi.single i 1) hlin hspan hsol
  let param := freeEquiv.symm.trans (Equiv.subtypeEquivRight hfiber)
  have hfree (x : {x : L → ZMod 2 // C *ᵥ x = Pi.single i 1}) :
      freeEquiv x = fun j => x.val (split (.inr j)) := rfl
  let summand (x : L → ZMod 2) := weight (fun j => x (split (.inr j))) *
    ((∏ j : P, mass j (x (split (.inl j)))) *
      ∏ k, if row k ⬝ᵥ x = 1 then bias k else 1)
  change (∑ x : L → ZMod 2, if C *ᵥ x = Pi.single i 1 then summand x else 0) = _ ↔ _
  have hsum :
      (∑ x : L → ZMod 2, if C *ᵥ x = Pi.single i 1 then summand x else 0) =
      ∑ y : F → ZMod 2, summand (param y).val := by
    rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
    exact Fintype.sum_equiv freeEquiv _ _ (fun x => by simp [param])
  rw [hsum]
  have hsingle (j : P) (x : L → ZMod 2) : d (Pi.single (split (.inl j)) 1) x =
      x (split (.inl j)) := single_one_dotProduct _ _
  have hparam (y : F → ZMod 2) : (fun j => (param y).val (split (.inr j))) = y := by
    change (fun j => (freeEquiv.symm y).val (split (.inr j))) = y
    rw [← hfree, Equiv.apply_symm_apply]
  have h := weighted_affine_fiber_eq_iff (S.map d) (d (C i)) param weight mass bias
    (fun j => d (Pi.single (split (.inl j)) 1)) (fun k => d (row k))
    hweight hnorm hmass hpivot hbias hrow
  simp only [hmapped, hsingle] at h
  have hdot (r x : L → ZMod 2) : d r x = r ⬝ᵥ x := rfl
  simpa only [summand, hparam, hdot] using h

end

end D5.S3.Quantum.Fermionic.WeightedSlaterPurityDropEquality
