import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicOscillatorBasis
import D5.S3.VertexAlgebra.Lattice.Orbifold.NativeStandardThirdLift

/-! The neutral Sugawara grade in cubic oscillator coordinates. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicOscillatorTrace

open Module MvPolynomial LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeThetaCharacter
open LatticeSugawaraCurrents (gramComplex)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qCubicOscillatorBasis NativeStandardThirdLift
open D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation (integerEnergy)
open ThirdTwistedChargeAction (nativeStandardEta_fixed)
open private oscillatorCoordinates_X colourEquiv inverseMatrix from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicOscillatorBasis
open private cutoffActualGrade_eq_supported from
  D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter

noncomputable section

private def weight {ι : Type*} (x : ι × ℕ) : ℤ := (x.2 : ℤ) + 1

private theorem integer_weight {ι : Type*} (d : (ι × ℕ) →₀ ℕ) :
    Finsupp.weight weight d = (integerEnergy ι d : ℤ) := by
  simp [integerEnergy, Finsupp.weight_apply, Finsupp.sum, weight]

private theorem weight_mapDomain {ι κ : Type*} (f : ι × ℕ → κ × ℕ)
    (hf : ∀ i, (f i).2 = i.2) (d : (ι × ℕ) →₀ ℕ) :
    Finsupp.weight weight (d.mapDomain f) = Finsupp.weight weight d := by
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index (h := fun i e => e • weight i)
    (fun _ => zero_nsmul _) (fun _ _ _ => add_nsmul _ _ _)]
  simp only [weight, hf]

private theorem map_homogeneous {ι κ : Type*}
    (f : MvPolynomial (ι × ℕ) ℂ →ₐ[ℂ] MvPolynomial (κ × ℕ) ℂ)
    (hf : ∀ i : ι × ℕ, IsWeightedHomogeneous weight (f (X i)) (weight i))
    {p : MvPolynomial (ι × ℕ) ℂ} {n : ℤ} (hp : IsWeightedHomogeneous weight p n) :
    IsWeightedHomogeneous weight (f p) n := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using isWeightedHomogeneous_zero ℂ weight n
  | add p q _ _ ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial d c hd =>
    have he : aeval (fun i => f (X i)) = f := by
      apply MvPolynomial.algHom_ext
      intro i
      exact aeval_X _ _
    rw [← he, aeval_monomial, algebraMap_eq, ← hd]
    apply IsWeightedHomogeneous.C_mul
    rw [Finsupp.weight_apply, Finsupp.prod, Finsupp.sum]
    exact IsWeightedHomogeneous.prod _ _ _ (fun i _ => (hf i).pow (d i))

private theorem columns_homogeneous {ι κ : Type*} [Fintype ι]
    (c : ι → ℂ) (r : κ × ℕ) :
    IsWeightedHomogeneous weight (∑ i, c i • (X (i, r.2) : MvPolynomial (ι × ℕ) ℂ))
      (weight r) := by
  apply IsWeightedHomogeneous.sum
  intro i _
  exact (weightedHomogeneousSubmodule ℂ weight (weight r)).smul_mem _
    (isWeightedHomogeneous_X ℂ weight (i, r.2))

private theorem forward_homogeneous {p : MvPolynomial CubicIndex ℂ} {n : ℤ}
    (hp : IsWeightedHomogeneous weight p n) :
    IsWeightedHomogeneous weight (oscillatorCoordinates p) n :=
  map_homogeneous oscillatorCoordinates.toAlgHom
    (fun ⟨i, r⟩ => by
      change IsWeightedHomogeneous weight (oscillatorCoordinates (X (i, r))) (weight (i, r))
      rw [oscillatorCoordinates_X]
      exact columns_homogeneous (cubicBasis i) (i, r)) hp

private theorem backward_homogeneous {p : Oscillator lattice} {n : ℤ}
    (hp : IsWeightedHomogeneous weight p n) :
    IsWeightedHomogeneous weight (oscillatorCoordinates.symm p) n := by
  apply map_homogeneous oscillatorCoordinates.symm.toAlgHom _ hp
  rintro ⟨i, r⟩
  change IsWeightedHomogeneous weight
    (rename (colourEquiv.symm.prodCongr (Equiv.refl ℕ))
      (OriginalCurrentMetric.substitution (fun _ => inverseMatrix) (X (i, r)))) (weight (i, r))
  rw [OriginalCurrentMetric.substitution_X]
  simp only [OriginalCurrentMetric.variableImage, map_sum, map_smul, rename_X,
    Equiv.prodCongr_apply]
  apply IsWeightedHomogeneous.sum
  intro j _
  exact (weightedHomogeneousSubmodule ℂ weight (weight (i, r))).smul_mem _
    (isWeightedHomogeneous_X ℂ weight (colourEquiv.symm j, r))

variable (H : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ)
variable (hHG : H * gramComplex lattice = 1) (hGH : gramComplex lattice * H = 1)

private abbrev Grade := cutoffActualGrade lattice H {0}
private abbrev CubicGrade := weightedHomogeneousSubmodule ℂ (weight (ι := Fin 3 × Fin 16))

include hHG hGH in
private theorem mem_grade (n : ℤ) (v : Carrier lattice) :
    v ∈ Grade H n ↔ (∀ a : Charge lattice, a ≠ 0 → v a = 0) ∧
      IsWeightedHomogeneous weight (v 0) n := by
  change v ∈ cutoffActualGrade lattice H {0} n ↔ _
  rw [cutoffActualGrade_eq_supported lattice H hHG hGH]
  change (carrierCoeffEquiv lattice v ∈ Finsupp.supported ℂ ℂ _) ↔ _
  rw [Finsupp.mem_supported']
  constructor
  · intro hv
    refine ⟨?_, ?_⟩
    · intro a ha
      apply MvPolynomial.ext
      intro d
      change (v a).coeff d = 0
      exact hv (a, d) (by simp [ha])
    · intro d hd
      by_contra h
      apply hd
      apply hv (0, d)
      simpa [energy, chargeEnergy_zero, integer_weight, integerEnergy, oscillatorEnergy] using h
  · rintro ⟨ha, hn⟩ ⟨a, d⟩ h
    change (v a).coeff d = 0
    by_cases h0 : a = 0
    · subst a
      by_contra hd
      apply h
      refine ⟨by simp, ?_⟩
      simpa [energy, chargeEnergy_zero, integer_weight, integerEnergy, oscillatorEnergy] using hn hd
    · simp [ha a h0]

private def gradeCoordinates (n : ℤ) : CubicGrade n ≃ₗ[ℂ] Grade H n where
  toFun p := ⟨Finsupp.single 0 (oscillatorCoordinates p.1),
    (mem_grade H hHG hGH n _).mpr ⟨by
      intro a ha
      simp [Finsupp.single_eq_of_ne ha], by simpa using forward_homogeneous p.2⟩⟩
  invFun v := ⟨oscillatorCoordinates.symm (v.1 0),
    backward_homogeneous ((mem_grade H hHG hGH n v.1).mp v.2).2⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv v := by
    apply Subtype.ext
    apply Finsupp.ext
    intro a
    change Finsupp.single (0 : Charge lattice)
      (oscillatorCoordinates (oscillatorCoordinates.symm (v.1 0))) a = v.1 a
    rw [AlgEquiv.apply_symm_apply]
    by_cases ha : a = 0
    · simp [ha]
    · rw [Finsupp.single_eq_of_ne ha, ((mem_grade H hHG hGH n v.1).mp v.2).1 a ha]
  map_add' p q := by
    apply Subtype.ext
    change Finsupp.single (0 : Charge lattice) (oscillatorCoordinates (p.1 + q.1)) = _
    rw [map_add, Finsupp.single_add]
    rfl
  map_smul' c p := by
    apply Subtype.ext
    change Finsupp.single (0 : Charge lattice) (oscillatorCoordinates (c • p.1)) = _
    change _ = c • Finsupp.single (0 : Charge lattice) (oscillatorCoordinates p.1)
    rw [map_smul, Finsupp.smul_single]

private abbrev Label (n : ℤ) := {d : CubicIndex →₀ ℕ // Finsupp.weight weight d = n}

private def monomialBasis (n : ℤ) : Basis (Label n) ℂ (CubicGrade n) :=
  Basis.ofRepr ((LinearEquiv.ofEq _ _
    (weightedHomogeneousSubmodule_eq_finsupp_supported ℂ weight n)).trans
      (AddMonoidAlgebra.supportedEquivFinsupp _))

private theorem monomialBasis_apply (n : ℤ) (d : Label n) :
    (monomialBasis n d).1 = monomial d.1 1 := by
  simp only [monomialBasis, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply,
    LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]
  apply MvPolynomial.ext
  intro e
  change (((Finsupp.supportedEquivFinsupp (M := ℂ) (R := ℂ) _).symm (Finsupp.single d 1) :
    (CubicIndex →₀ ℕ) →₀ ℂ) e) = Finsupp.single d.1 1 e
  rw [Finsupp.supportedEquivFinsupp_symm_single]

private def rotateLabel (n : ℤ) (d : Label n) : Label n :=
  ⟨d.1.mapDomain rotate, (weight_mapDomain rotate (fun _ => rfl) d.1).trans d.2⟩

private def gradeBasis (n : ℤ) : Basis (Label n) ℂ (Grade H n) :=
  (monomialBasis n).map (gradeCoordinates H hHG hGH n)

private theorem gradeBasis_rotate (n : ℤ) (d : Label n) :
    cutoffStandardLift lattice g g_cube g_isometry H hHG {0} n (by simp)
      (gradeBasis H hHG hGH n d) = gradeBasis H hHG hGH n (rotateLabel n d) := by
  apply Subtype.ext
  rw [gradeBasis, Basis.map_apply, Basis.map_apply]
  change standardLift lattice g g_cube g_isometry
    (Finsupp.single 0 (oscillatorCoordinates (monomialBasis n d).1)) =
    Finsupp.single 0 (oscillatorCoordinates (monomialBasis n (rotateLabel n d)).1)
  rw [monomialBasis_apply, monomialBasis_apply, standardLift_single,
    nativeStandardEta_fixed lattice g g_isometry 0 (map_zero g), Units.val_one,
    one_smul, map_zero, oscillator_cubicMonomial]
  rfl

private theorem label_finite (n : ℤ) : Finite (Label n) := by
  let : Finite (CutoffIndex lattice {0} n) := cutoffIndex_finite lattice {0} n
  let e := colourEquiv.prodCongr (Equiv.refl ℕ)
  let f (d : Label n) : CutoffIndex lattice {0} n :=
    ⟨(0, d.1.mapDomain e), by simp, by
      simp only [energy, chargeEnergy_zero, zero_add]
      change (integerEnergy (Fin lattice.rank) (d.1.mapDomain e) : ℤ) = n
      rw [← integer_weight]
      exact (weight_mapDomain e (fun _ => rfl) d.1).trans d.2⟩
  exact Finite.of_injective f fun d d' h => Subtype.ext
    (Finsupp.mapDomain_injective e.injective (congrArg (fun x => x.1.2) h))

include hGH in
private theorem standardOscillatorTrace_eq_fixed (n : ℤ) :
    standardOscillatorTrace lattice g g_cube g_isometry H hHG n =
      (Nat.card {d : Label n // rotateLabel n d = d} : ℂ) := by
  classical
  let : Finite (Label n) := label_finite n
  let : Fintype (Label n) := Fintype.ofFinite _
  let : Finite (CutoffIndex lattice {0} n) := cutoffIndex_finite lattice {0} n
  let : Fintype (CutoffIndex lattice {0} n) := Fintype.ofFinite _
  unfold standardOscillatorTrace cutoffStandardLiftTrace
  rw [LinearMap.trace_eq_matrix_trace ℂ (gradeBasis H hHG hGH n)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, gradeBasis_rotate,
    Basis.repr_self, Finsupp.single_apply]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

private def cycleSlot (k : Fin 3) (x : Fin 16 × ℕ) : CubicIndex :=
  ((k, x.1), x.2)

private theorem cycleSlot_injective (k : Fin 3) : Function.Injective (cycleSlot k) := by
  intro x y h
  exact Prod.ext (congrArg (fun z => z.1.2) h) (congrArg (fun z : CubicIndex => z.2) h)

private def repeatOccupation (d : (Fin 16 × ℕ) →₀ ℕ) : CubicIndex →₀ ℕ :=
  ∑ k : Fin 3, d.mapDomain (cycleSlot k)

private theorem repeatOccupation_apply (d : (Fin 16 × ℕ) →₀ ℕ) (k : Fin 3)
    (x : Fin 16 × ℕ) : repeatOccupation d (cycleSlot k x) = d x := by
  classical
  simp only [repeatOccupation, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single k, Finsupp.mapDomain_apply_of_injective (cycleSlot_injective k)]
  · intro j _ hj
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨y, hy⟩
    exact hj (congrArg (fun z => z.1.1) hy)
  · simp

private theorem repeatOccupation_weight (d : (Fin 16 × ℕ) →₀ ℕ) :
    Finsupp.weight weight (repeatOccupation d) = 3 * (integerEnergy (Fin 16) d : ℤ) := by
  simp only [repeatOccupation, map_sum]
  have h (k : Fin 3) : Finsupp.weight weight (d.mapDomain (cycleSlot k)) =
      (integerEnergy (Fin 16) d : ℤ) :=
    (weight_mapDomain (cycleSlot k) (fun _ => rfl) d).trans (integer_weight d)
  simp [h]

private theorem repeatOccupation_fixed (d : (Fin 16 × ℕ) →₀ ℕ) :
    (repeatOccupation d).mapDomain rotate = repeatOccupation d := by
  apply Finsupp.ext
  intro j
  obtain ⟨x, hx⟩ := rotate.surjective j
  rcases x with ⟨⟨k, i⟩, r⟩
  subst j
  rw [Finsupp.mapDomain_apply_of_injective rotate.injective]
  change repeatOccupation d (cycleSlot k (i, r)) =
    repeatOccupation d (cycleSlot (k + 1) (i, r))
  rw [repeatOccupation_apply, repeatOccupation_apply]

private def firstOccupation (d : CubicIndex →₀ ℕ) : (Fin 16 × ℕ) →₀ ℕ :=
  d.comapDomain (cycleSlot 0) (cycleSlot_injective 0).injOn

private theorem firstOccupation_apply (d : CubicIndex →₀ ℕ) (x : Fin 16 × ℕ) :
    firstOccupation d x = d (cycleSlot 0 x) := rfl

private theorem repeat_first (d : CubicIndex →₀ ℕ) (hd : d.mapDomain rotate = d) :
    repeatOccupation (firstOccupation d) = d := by
  have step (k : Fin 3) (x : Fin 16 × ℕ) : d (cycleSlot (k + 1) x) = d (cycleSlot k x) := by
    have h := congrArg (fun e : CubicIndex →₀ ℕ => e (rotate (cycleSlot k x))) hd
    rw [Finsupp.mapDomain_apply_of_injective rotate.injective] at h
    exact h.symm
  apply Finsupp.ext
  rintro ⟨⟨k, i⟩, r⟩
  change repeatOccupation (firstOccupation d) (cycleSlot k (i, r)) = d (cycleSlot k (i, r))
  rw [repeatOccupation_apply, firstOccupation_apply]
  fin_cases k
  · rfl
  · exact (step 0 (i, r)).symm
  · exact ((step 1 (i, r)).trans (step 0 (i, r))).symm

private def fixedOccupationEquiv (n : ℤ) :
    {d : (Fin 16 × ℕ) →₀ ℕ // 3 * (integerEnergy (Fin 16) d : ℤ) = n} ≃
      {d : Label n // rotateLabel n d = d} where
  toFun d := ⟨⟨repeatOccupation d.1, (repeatOccupation_weight d.1).trans d.2⟩,
    Subtype.ext (repeatOccupation_fixed d.1)⟩
  invFun d := by
    have h := repeat_first d.1.1 (congrArg Subtype.val d.2)
    exact ⟨firstOccupation d.1.1, by rw [← repeatOccupation_weight, h, d.1.2]⟩
  left_inv d := by
    apply Subtype.ext
    apply Finsupp.ext
    intro x
    exact repeatOccupation_apply d.1 0 x
  right_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    change repeatOccupation (firstOccupation d.1.1) = d.1.1
    exact repeat_first d.1.1 (congrArg Subtype.val d.2)

/-- At every integral Sugawara grade, the standard cubic lift's neutral trace
counts sixteen-coloured integer-mode occupations whose energy, multiplied by three,
equals the grade. -/
theorem standardOscillatorTrace_eq_occupationCount (n : ℤ) :
    standardOscillatorTrace lattice g g_cube g_isometry H hHG n =
      (Nat.card {d : (Fin 16 × ℕ) →₀ ℕ // 3 * (integerEnergy (Fin 16) d : ℤ) = n} : ℂ) := by
  rw [standardOscillatorTrace_eq_fixed H hHG (mul_eq_one_comm.mp hHG),
    Nat.card_congr (fixedOccupationEquiv n).symm]

run_cmd do
  for name in [``standardOscillatorTrace_eq_occupationCount,
      ``cutoff_standardLift_trace_fixed_charges] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
      throwError "Unexpected axiom closure for {name}: {axioms}"
    Lean.logInfo m!"{name} depends on axioms: {axioms}"

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicOscillatorTrace
