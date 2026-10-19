/- GID: D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.claim; result=D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.result; claim=D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.claim
   digest: A normalized three-qubit pure state refutes l1 correlated-coherence monogamy. -/

import D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum

/-! A pure three-qubit counterexample to the l₁ correlated-coherence conjecture of
Basso–Maziero, arXiv:2006.14037v2, Section III.A, with the gap defined by Eq. (33).
The computational-basis amplitudes are `(-16, 1, 128, -16, -128, -16, 1, -128) / √49922`.
The seven coherences have common denominator `49922` and numerators
`138434, 8416, 288, 288, 48928, 48928, 50336`; the gap is `-383 / 24961`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation

open D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum
open D5.S3.Quantum.Information.PartialTraceMutualInformation

/-- The l₁ coherence in the fixed matrix basis. -/
noncomputable def l1Coherence {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, if i = j then 0 else ‖ρ i j‖

/-- The monogamy difference in Eq. (33) of Basso–Maziero, arXiv:2006.14037v2. -/
noncomputable def monogamyGap (ψ : (Fin 3 → Fin 2) → ℂ) : ℝ :=
  l1Coherence (reducedState Finset.univ ψ) + l1Coherence (reducedState {0} ψ) +
    l1Coherence (reducedState {1} ψ) + l1Coherence (reducedState {2} ψ) -
    (l1Coherence (reducedState {0, 1} ψ) + l1Coherence (reducedState {0, 2} ψ) +
      l1Coherence (reducedState {1, 2} ψ))

/-- The conjectured monogamy inequality, restricted to pure three-qubit states. -/
def claim : Prop := ∀ ψ : (Fin 3 → Fin 2) → ℂ,
  ∑ x, Complex.normSq (ψ x) = 1 → 0 ≤ monogamyGap ψ

private def weight (x : Fin 3 → Fin 2) : ℝ :=
  if x 0 = 0 then
    if x 1 = 0 then (if x 2 = 0 then -16 else 1)
    else (if x 2 = 0 then 128 else -16)
  else if x 1 = 0 then (if x 2 = 0 then -128 else -16)
    else (if x 2 = 0 then 1 else -128)

private noncomputable def psi (x : Fin 3 → Fin 2) : ℂ :=
  ((weight x / Real.sqrt 49922 : ℝ) : ℂ)

private theorem sum_single (p : Fin 3 → Prop) [DecidablePred p] (a : Fin 3)
    (hp : ∀ i, p i ↔ i = a) (f : ({i // p i} → Fin 2) → ℝ) :
    ∑ x, f x = ∑ b : Fin 2, f (fun _ => b) := by
  let e : ({i // p i} → Fin 2) ≃ Fin 2 :=
    { toFun := fun x => x ⟨a, (hp a).mpr rfl⟩
      invFun := fun b _ => b
      left_inv := fun x => by
        funext ⟨i, hi⟩
        rcases (hp i).mp hi with rfl
        rfl
      right_inv := fun _ => rfl }
  exact Fintype.sum_equiv e f (fun b => f (fun _ => b)) (fun x => by
    congr 1
    exact (e.left_inv x).symm)

private theorem sum_pair (p : Fin 3 → Prop) [DecidablePred p] (a b : Fin 3)
    (hab : a ≠ b) (hp : ∀ i, p i ↔ i = a ∨ i = b)
    (f : ({i // p i} → Fin 2) → ℝ) :
    ∑ x, f x = ∑ u : Fin 2, ∑ v : Fin 2, f (fun i => if i.val = a then u else v) := by
  let e : ({i // p i} → Fin 2) ≃ Fin 2 × Fin 2 :=
    { toFun := fun x => (x ⟨a, (hp a).mpr (Or.inl rfl)⟩,
        x ⟨b, (hp b).mpr (Or.inr rfl)⟩)
      invFun := fun x i => if i.val = a then x.1 else x.2
      left_inv := fun x => by
        funext ⟨i, hi⟩
        rcases (hp i).mp hi with rfl | rfl <;> simp [Ne.symm hab]
      right_inv := fun x => by simp [Ne.symm hab] }
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  rfl

private theorem sum_full
    (f : (↥(Finset.univ : Finset (Fin 3)) → Fin 2) → ℝ) :
    ∑ x, f x = ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2,
      f (fun i => ![a, b, c] i.val) := by
  rw [← Equiv.sum_comp (Equiv.arrowCongr
    (Equiv.subtypeUnivEquiv (fun i : Fin 3 => Finset.mem_univ i)).symm
    (Equiv.refl (Fin 2))),
    ← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 3 => Fin 2)),
    Fintype.sum_prod_type]
  congr 1
  funext a
  rw [← Equiv.sum_comp (finTwoArrowEquiv (Fin 2)).symm, Fintype.sum_prod_type]
  rfl

private theorem sum_empty (f : (Outside (Finset.univ : Finset (Fin 3)) → Fin 2) → ℝ) :
    ∑ x, f x = f (fun _ => 0) := by
  apply Fintype.sum_eq_single (fun _ => 0)
  intro x hx
  exact (hx (by funext i; exact (i.property (Finset.mem_univ i.val)).elim)).elim

private theorem sqrt_product : Real.sqrt 49922 * Real.sqrt 49922 = 49922 :=
  Real.mul_self_sqrt (by norm_num)

private theorem weight_square_sum : ∑ x, weight x * weight x = 49922 := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 3 => Fin 2)),
    Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp (finTwoArrowEquiv (Fin 2)).symm, Fintype.sum_prod_type]
  norm_num [weight.eq_1, Fin.sum_univ_two]

private theorem normalized : ∑ x, Complex.normSq (psi x) = 1 := by
  simp only [psi.eq_1, Complex.normSq_ofReal, div_mul_div_comm, sqrt_product]
  rw [← Finset.sum_div, weight_square_sum]
  norm_num

private theorem entry_norm (A : Finset (Fin 3)) (i j : A → Fin 2) :
    ‖reducedState A psi i j‖ =
      |∑ z : Outside A → Fin 2, weight (join A i z) * weight (join A j z)| / 49922 := by
  have hp (x y : Fin 3 → Fin 2) :
      psi x * star (psi y) = ((weight x * weight y / 49922 : ℝ) : ℂ) := by
    simp only [psi.eq_1, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      div_mul_div_comm, sqrt_product]
  simp only [reducedState, partialTraceRight, Matrix.of_apply, hp,
    ← Complex.ofReal_sum, ← Finset.sum_div, Complex.norm_real, Real.norm_eq_abs, abs_div]
  norm_num

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coherence_A : l1Coherence (reducedState {0} psi) = 8416 / 49922 := by
  classical
  change (∑ i : (↥({0} : Finset (Fin 3)) → Fin 2),
    ∑ j : (↥({0} : Finset (Fin 3)) → Fin 2),
      if i = j then (0 : ℝ) else ‖reducedState {0} psi i j‖) = _
  rw [sum_single (fun i => i ∈ ({0} : Finset (Fin 3))) 0 (by simp)]
  simp_rw [sum_single (fun i => i ∈ ({0} : Finset (Fin 3))) 0 (by simp)]
  simp only [entry_norm]
  simp_rw [sum_pair (fun i => i ∉ ({0} : Finset (Fin 3))) 1 2 (by decide)
    (by intro i; fin_cases i <;> simp)]
  norm_num [weight.eq_1, join, Equiv.piEquivPiSubtypeProd_symm_apply, Fin.sum_univ_two,
    funext_iff]

private theorem coherence_B : l1Coherence (reducedState {1} psi) = 288 / 49922 := by
  classical
  change (∑ i : (↥({1} : Finset (Fin 3)) → Fin 2),
    ∑ j : (↥({1} : Finset (Fin 3)) → Fin 2),
      if i = j then (0 : ℝ) else ‖reducedState {1} psi i j‖) = _
  rw [sum_single (fun i => i ∈ ({1} : Finset (Fin 3))) 1 (by simp)]
  simp_rw [sum_single (fun i => i ∈ ({1} : Finset (Fin 3))) 1 (by simp)]
  simp only [entry_norm]
  simp_rw [sum_pair (fun i => i ∉ ({1} : Finset (Fin 3))) 0 2 (by decide)
    (by intro i; fin_cases i <;> simp)]
  norm_num [weight.eq_1, join, Equiv.piEquivPiSubtypeProd_symm_apply, Fin.sum_univ_two,
    funext_iff]

private theorem coherence_C : l1Coherence (reducedState {2} psi) = 288 / 49922 := by
  classical
  change (∑ i : (↥({2} : Finset (Fin 3)) → Fin 2),
    ∑ j : (↥({2} : Finset (Fin 3)) → Fin 2),
      if i = j then (0 : ℝ) else ‖reducedState {2} psi i j‖) = _
  rw [sum_single (fun i => i ∈ ({2} : Finset (Fin 3))) 2 (by simp)]
  simp_rw [sum_single (fun i => i ∈ ({2} : Finset (Fin 3))) 2 (by simp)]
  simp only [entry_norm]
  simp_rw [sum_pair (fun i => i ∉ ({2} : Finset (Fin 3))) 0 1 (by decide)
    (by intro i; fin_cases i <;> simp)]
  norm_num [weight.eq_1, join, Equiv.piEquivPiSubtypeProd_symm_apply, Fin.sum_univ_two,
    funext_iff]

private theorem coherence_AB : l1Coherence (reducedState {0, 1} psi) = 48928 / 49922 := by
  classical
  change (∑ i : (↥({0, 1} : Finset (Fin 3)) → Fin 2),
    ∑ j : (↥({0, 1} : Finset (Fin 3)) → Fin 2),
      if i = j then (0 : ℝ) else ‖reducedState {0, 1} psi i j‖) = _
  rw [sum_pair (fun i => i ∈ ({0, 1} : Finset (Fin 3))) 0 1 (by decide) (by simp)]
  simp_rw [sum_pair (fun i => i ∈ ({0, 1} : Finset (Fin 3))) 0 1 (by decide) (by simp)]
  simp only [entry_norm]
  simp_rw [sum_single (fun i => i ∉ ({0, 1} : Finset (Fin 3))) 2
    (by intro i; fin_cases i <;> simp)]
  norm_num [weight.eq_1, join, Equiv.piEquivPiSubtypeProd_symm_apply, Fin.sum_univ_two,
    funext_iff, Fin.forall_fin_succ]

private theorem coherence_AC : l1Coherence (reducedState {0, 2} psi) = 48928 / 49922 := by
  classical
  change (∑ i : (↥({0, 2} : Finset (Fin 3)) → Fin 2),
    ∑ j : (↥({0, 2} : Finset (Fin 3)) → Fin 2),
      if i = j then (0 : ℝ) else ‖reducedState {0, 2} psi i j‖) = _
  rw [sum_pair (fun i => i ∈ ({0, 2} : Finset (Fin 3))) 0 2 (by decide) (by simp)]
  simp_rw [sum_pair (fun i => i ∈ ({0, 2} : Finset (Fin 3))) 0 2 (by decide) (by simp)]
  simp only [entry_norm]
  simp_rw [sum_single (fun i => i ∉ ({0, 2} : Finset (Fin 3))) 1
    (by intro i; fin_cases i <;> simp)]
  norm_num [weight.eq_1, join, Equiv.piEquivPiSubtypeProd_symm_apply, Fin.sum_univ_two,
    funext_iff, Fin.forall_fin_succ]

private theorem coherence_BC : l1Coherence (reducedState {1, 2} psi) = 50336 / 49922 := by
  classical
  change (∑ i : (↥({1, 2} : Finset (Fin 3)) → Fin 2),
    ∑ j : (↥({1, 2} : Finset (Fin 3)) → Fin 2),
      if i = j then (0 : ℝ) else ‖reducedState {1, 2} psi i j‖) = _
  rw [sum_pair (fun i => i ∈ ({1, 2} : Finset (Fin 3))) 1 2 (by decide) (by simp)]
  simp_rw [sum_pair (fun i => i ∈ ({1, 2} : Finset (Fin 3))) 1 2 (by decide) (by simp)]
  simp only [entry_norm]
  simp_rw [sum_single (fun i => i ∉ ({1, 2} : Finset (Fin 3))) 0
    (by intro i; fin_cases i <;> simp)]
  norm_num [weight.eq_1, join, Equiv.piEquivPiSubtypeProd_symm_apply, Fin.sum_univ_two,
    funext_iff, Fin.forall_fin_succ]

set_option maxHeartbeats 2000000 in -- The full coherence expands all 64 matrix entries.
private theorem coherence_ABC : l1Coherence (reducedState Finset.univ psi) =
    138434 / 49922 := by
  classical
  change (∑ i : (↥(Finset.univ : Finset (Fin 3)) → Fin 2),
    ∑ j : (↥(Finset.univ : Finset (Fin 3)) → Fin 2),
      if i = j then (0 : ℝ) else ‖reducedState Finset.univ psi i j‖) = _
  rw [sum_full]
  simp_rw [sum_full]
  simp only [entry_norm, sum_empty]
  norm_num [weight.eq_1, join, Equiv.piEquivPiSubtypeProd_symm_apply, Fin.sum_univ_two,
    funext_iff, Fin.forall_fin_succ]

private theorem gap_value : monogamyGap psi = -383 / 24961 := by
  unfold monogamyGap
  rw [coherence_ABC, coherence_A, coherence_B, coherence_C,
    coherence_AB, coherence_AC, coherence_BC]
  norm_num

/-- The l₁ correlated-coherence monogamy conjecture fails for a pure three-qubit state. -/
theorem result : ¬ claim := by
  intro h
  have hnonneg := h psi normalized
  rw [gap_value] at hnonneg
  norm_num at hnonneg

end D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation
