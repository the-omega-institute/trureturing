/- GID: D5/S3/VertexAlgebra/Characters/LatticeFourCurrentTrace
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/LatticeFourCurrentTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite four-current cycle traces and the bounded labeled partial-matching coefficient.
-/

import D5.S3.VertexAlgebra.Characters.LatticeTwoCurrentTrace
import D5.S3.VertexAlgebra.Energy.LatticeCoefficientEnergy
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators VertexOperator
open MvPolynomial

namespace D5.S3.VertexAlgebra.LatticeFourCurrentTrace
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeAllStateField
open LatticeActualConformalState LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeThetaCharacter LatticeTwoCurrentTrace

open private sum_fullFiber
  from D5.S3.VertexAlgebra.Characters.LatticeTwoCurrentTrace

abbrev Four := Fin 4

/-- The ten labeled partial matchings of four ordered slots. -/
inductive PM4 where
  | empty
  | p12 | p13 | p14 | p23 | p24 | p34
  | p12_34 | p13_24 | p14_23
  deriving DecidableEq, Fintype

private def e12 : Four × Four := (0, 1)
private def e13 : Four × Four := (0, 2)
private def e14 : Four × Four := (0, 3)
private def e23 : Four × Four := (1, 2)
private def e24 : Four × Four := (1, 3)
private def e34 : Four × Four := (2, 3)

/-- The labeled edge set of a partial matching. -/
def PM4.edges : PM4 → Finset (Four × Four)
  | .empty => ∅
  | .p12 => {e12}
  | .p13 => {e13}
  | .p14 => {e14}
  | .p23 => {e23}
  | .p24 => {e24}
  | .p34 => {e34}
  | .p12_34 => {e12, e34}
  | .p13_24 => {e13, e24}
  | .p14_23 => {e14, e23}

private abbrev edgeParam (M : PM4) := M.edges

private def PM4.unpaired (M : PM4) : Finset Four :=
  Finset.univ.filter fun j =>
    ∀ e ∈ M.edges, j ≠ e.1 ∧ j ≠ e.2

private def arcMem (e : Four × Four) (j : Four) : Prop :=
  e.1.1 < j.1 ∧ j.1 ≤ e.2.1

private def sideMem (ε : Fin 2) (e : Four × Four) (j : Four) : Prop :=
  if ε.1 = 0 then arcMem e j else ¬ arcMem e j

private def min4 (n : Four → ℕ) : ℕ :=
  min (min (n 0) (n 1)) (min (n 2) (n 3))

private def max4 (n : Four → ℕ) : ℕ :=
  max (max (n 0) (n 1)) (max (n 2) (n 3))

private def matchingShift (M : PM4) (ell : edgeParam M → ℕ)
    (ε : edgeParam M → Fin 2) (k : edgeParam M → ℕ) (j : Four) : ℕ := by
  classical
  exact ∑ e : edgeParam M, ell e * (k e + if sideMem (ε e) e.1 j then 1 else 0)

private def gradeShift (D : LatticeData) (n : Four → ℕ) (β : Charge D) (M : PM4)
    (ell : edgeParam M → Fin (max4 n + 1))
    (ε : edgeParam M → Fin 2) (k : edgeParam M → Fin (min4 n + 1))
    (j : Four) : ℕ :=
  matchingShift M (fun e => (ell e).1) ε (fun e => (k e).1) j

/-- The literal finite trace of the original four current blocks. -/
def actualFourCurrentCycleTrace (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) : ℂ := by
  letI := grade_finiteDimensional D hD (n 0 : ℤ)
  exact LinearMap.trace ℂ (grade D (n 0 : ℤ))
    ((actualCurrentBlock D (i 0) (n 0) (n 1)).comp
      ((actualCurrentBlock D (i 1) (n 1) (n 2)).comp
        ((actualCurrentBlock D (i 2) (n 2) (n 3)).comp
          (actualCurrentBlock D (i 3) (n 3) (n 0)))))

private def chargeWeight (D : LatticeData) (i : Four → Fin D.rank) (n : Four → ℕ)
    (β : Charge D) (M : PM4)
    (ell : edgeParam M → Fin (max4 n + 1))
    (ε : edgeParam M → Fin 2) (k : edgeParam M → Fin (min4 n + 1))
    (t : Fin (min4 n + 1)) : ℂ := by
  classical
  exact if (∀ j : Four,
        n j = (chargeEnergy D β).toNat + t.1 +
          gradeShift D n β M ell ε k j) ∧
      (∀ e : edgeParam M, 0 < (ell e).1) then
    (Nat.card (IntegerFiber D t.1) : ℂ) *
      (∏ j ∈ M.unpaired, (bilinear D (unitCharge D (i j)) β : ℂ)) *
      ∏ e : edgeParam M,
        ((ell e).1 : ℂ) * (D.G (i e.1.1) (i e.1.2) : ℂ)
  else 0

/-- Explicit bounded ten-matching coefficient, with labeled repeated-frequency slots. -/
def boundedFourCurrentCoefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) : ℂ := by
  classical
  exact ∑ β ∈ positiveChargeCutoff D hD ((min4 n : ℕ) : ℤ),
    ∑ M : PM4,
      ∑ ell : edgeParam M → Fin (max4 n + 1),
        ∑ ε : edgeParam M → Fin 2,
          ∑ k : edgeParam M → Fin (min4 n + 1),
            ∑ t : Fin (min4 n + 1), chargeWeight D i n β M ell ε k t

/-- There are exactly ten labeled partial matchings; in particular the empty assignment is unique. -/
private theorem pm4_card : Fintype.card PM4 = 10 := by decide

private theorem pm4_empty_edges : PM4.empty.edges = ∅ := rfl

private theorem pm4_empty_unpaired : PM4.empty.unpaired = Finset.univ := by
  classical
  ext j
  simp [PM4.unpaired, PM4.edges]

private theorem projection_basis (D : LatticeData) (n : ℤ) (a : Label D)
    (ha : energy D a = n) : gradeProjection D n (carrierBasis D a) = carrierBasis D a := by
  classical
  apply (carrierCoeffEquiv D).injective
  ext b
  rw [gradeProjection_coeff]
  change (if energy D b = n then Finsupp.single a (1 : ℂ) b else 0) =
    Finsupp.single a (1 : ℂ) b
  by_cases h : a = b
  · subst b
    simp [ha]
  · simp [Finsupp.single_apply, h]

private theorem basis_value (D : LatticeData) (n : ℤ) (a : EnergyFiber D n) :
    (gradeBasis D n a : Carrier D) = carrierBasis D a.1 := by
  run_tac
    let supplier := (Lean.Name.num
      `_private.D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades 0).append
      `D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades.gradeBasis_coe
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($(Lean.mkIdent supplier)) _ _ _))

private theorem block_zero_basis (D : LatticeData) (i : Fin D.rank) (n : ℕ)
    (a : EnergyFiber D (n : ℤ)) :
    actualCurrentBlock D i n n (gradeBasis D (n : ℤ) a) =
      (bilinear D (unitCharge D i) a.1.1 : ℂ) • gradeBasis D (n : ℤ) a := by
  apply Subtype.ext
  change gradeProjection D (n : ℤ) (((Y D (currentState D i))[[ (n : ℤ) - n ]])
    (gradeBasis D (n : ℤ) a)) = _
  rw [basis_value, current_state_field, neutralField_ncoeff, sub_self,
    carrierBasis_apply, neutralMode_single]
  simp only [neutralPolynomialMode, lt_self_iff_false, ↓reduceIte,
    LinearMap.smul_apply, LinearMap.id_apply, ← Finsupp.smul_single, map_smul]
  rw [← carrierBasis_apply, projection_basis D _ _ a.2]
  rw [Submodule.coe_smul, basis_value]

private theorem zero_diag (D : LatticeData) (n : ℕ) (i : Four → Fin D.rank)
    (a : EnergyFiber D (n : ℤ)) :
    (gradeBasis D (n : ℤ)).repr
      (((actualCurrentBlock D (i 0) n n).comp
        ((actualCurrentBlock D (i 1) n n).comp
          ((actualCurrentBlock D (i 2) n n).comp
            (actualCurrentBlock D (i 3) n n))))
        (gradeBasis D (n : ℤ) a)) a =
      ∏ j : Four, (bilinear D (unitCharge D (i j)) a.1.1 : ℂ) := by
  classical
  simp [LinearMap.comp_apply, block_zero_basis, map_smul, smul_eq_mul,
    Fin.prod_univ_succ, mul_assoc, mul_comm, mul_left_comm]
  ring

/-- The equal-grade specialization is the literal four zero-mode trace on the original basis.
This is the finite source bridge used by the full signed-mode induction. -/
private theorem actual_four_zero_grade_trace
    (D : LatticeData) (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : ℕ) [Finite (EnergyFiber D (n : ℤ))] :
    letI := Fintype.ofFinite (EnergyFiber D (n : ℤ))
    actualFourCurrentCycleTrace D hD i (fun _ => n) =
      ∑ a : EnergyFiber D (n : ℤ),
        ∏ j : Four, (bilinear D (unitCharge D (i j)) a.1.1 : ℂ) := by
  classical
  letI := grade_finiteDimensional D hD (n : ℤ)
  letI := Fintype.ofFinite (EnergyFiber D (n : ℤ))
  rw [actualFourCurrentCycleTrace,
    LinearMap.trace_eq_matrix_trace ℂ (gradeBasis D (n : ℤ))]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, zero_diag]

/- Integer grades are the original coefficient-support submodules, including
the negative grades. No oscillator truncation is introduced here. -/

private theorem projection_on_grade (D : LatticeData) (N : ℤ)
    (v : Carrier D) (hv : v ∈ grade D N) : gradeProjection D N v = v := by
  classical
  apply (carrierCoeffEquiv D).injective
  ext a
  rw [gradeProjection_coeff]
  by_cases ha : energy D a = N
  · simp [ha]
  · have hz := (mem_grade_iff D N v).mp hv a ha
    change (if energy D a = N then (v a.1).coeff a.2 else 0) = (v a.1).coeff a.2
    simp [ha, hz]

private theorem negative_grade_value (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (N : ℤ) (hN : N < 0) (v : Carrier D) (hv : v ∈ grade D N) : v = 0 := by
  apply (carrierCoeffEquiv D).injective
  ext a
  have hq := chargeEnergy_nonneg D hD a.1
  have ha : energy D a ≠ N := by
    dsimp only [energy]
    omega
  have hz := (mem_grade_iff D N v).mp hv a ha
  change (v a.1).coeff a.2 = 0
  exact hz

private theorem current_grade_one (D : LatticeData) (i : Fin D.rank) :
    currentState D i ∈ grade D 1 := by
  let a : EnergyFiber D 1 := ⟨(0, Finsupp.single (i, 0) 1), by
    simp [energy, oscillatorEnergy, Finsupp.weight_single]⟩
  have h := (gradeBasis D 1 a).property
  rw [basis_value] at h
  simpa [a, carrierBasis_apply, currentState, MvPolynomial.X] using h

private def HasGrade (D : LatticeData) (f : Module.End ℂ (Carrier D)) (d : ℤ) : Prop :=
  ∀ (N : ℤ) (v : Carrier D), v ∈ grade D N → f v ∈ grade D (N - d)

private theorem mode_hasGrade (D : LatticeData) (i : Fin D.rank) (m : ℤ) :
    HasGrade D (neutralMode D i m) m := by
  intro N v hv
  have h := LatticeCoefficientEnergy.actual_mode_grade D 1 N m
    (currentState D i) v (current_grade_one D i) hv
  rw [current_state_field, neutralField_ncoeff] at h
  convert h using 1 <;> congr 1 <;> omega

private theorem hasGrade_mul (D : LatticeData) (f g : Module.End ℂ (Carrier D))
    (a b : ℤ) (hf : HasGrade D f a) (hg : HasGrade D g b) :
    HasGrade D (f * g) (a + b) := by
  intro N v hv
  have h := hf (N - b) (g v) (hg N v hv)
  change f (g v) ∈ grade D (N - (a + b))
  convert h using 1 <;> congr 1 <;> omega

private def cutMap (D : LatticeData) (f : Module.End ℂ (Carrier D)) (N M : ℤ) :
    grade D M →ₗ[ℂ] grade D N :=
  (((gradeProjection D N).comp f).domRestrict (grade D M)).codRestrict
    (grade D N) (fun _ => gradeProjection_mem D N _)

private theorem cutMap_mul (D : LatticeData) (f g : Module.End ℂ (Carrier D))
    (N K M : ℤ) (hg : ∀ v : Carrier D, v ∈ grade D M → g v ∈ grade D K) :
    cutMap D (f * g) N M = (cutMap D f N K).comp (cutMap D g K M) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change gradeProjection D N (f (g v.1)) =
    gradeProjection D N (f (gradeProjection D K (g v.1)))
  rw [projection_on_grade D K (g v.1) (hg v.1 v.2)]

private def cutEnd (D : LatticeData) (N : ℤ) :
    Module.End ℂ (Carrier D) →ₗ[ℂ] Module.End ℂ (grade D N) where
  toFun f := cutMap D f N N
  map_add' f g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp [cutMap, map_add]
  map_smul' c f := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp [cutMap, map_smul]

private def gradeTrace (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (N : ℤ) :
    Module.End ℂ (Carrier D) →ₗ[ℂ] ℂ := by
  letI := grade_finiteDimensional D hD N
  exact (LinearMap.trace ℂ (grade D N)).comp (cutEnd D N)

private theorem gradeTrace_negative (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (N : ℤ) (hN : N < 0)
    (f : Module.End ℂ (Carrier D)) : gradeTrace D hD N f = 0 := by
  have hz : cutMap D f N N = 0 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact negative_grade_value D hD N hN _ (gradeProjection_mem D N _)
  change LinearMap.trace ℂ (grade D N) (cutMap D f N N) = 0
  rw [hz, map_zero]

/- Rectangular trace cyclicity is applied only to finite original grades.
The shifted grade may be negative; positive energy then proves its trace zero. -/
private theorem gradeTrace_cyclic (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (f g : Module.End ℂ (Carrier D)) (N b : ℤ)
    (hf : HasGrade D f (-b)) (hg : HasGrade D g b) :
    gradeTrace D hD N (f * g) = gradeTrace D hD (N - b) (g * f) := by
  letI := grade_finiteDimensional D hD N
  letI := grade_finiteDimensional D hD (N - b)
  change LinearMap.trace ℂ (grade D N) (cutMap D (f * g) N N) =
    LinearMap.trace ℂ (grade D (N - b)) (cutMap D (g * f) (N - b) (N - b))
  rw [cutMap_mul D f g N (N - b) N (hg N)]
  rw [cutMap_mul D g f (N - b) N (N - b) (by
    intro v hv
    simpa only [sub_neg_eq_add, sub_add_cancel] using hf (N - b) v hv)]
  exact LinearMap.trace_comp_comm' (cutMap D g (N - b) N) (cutMap D f N (N - b))

private theorem original_block (D : LatticeData) (i : Fin D.rank) (N M : ℕ) :
    actualCurrentBlock D i N M = cutMap D (neutralMode D i ((M : ℤ) - N)) N M := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change gradeProjection D (N : ℤ)
    (((Y D (currentState D i))[[ (M : ℤ) - N ]]) v.1) =
    gradeProjection D (N : ℤ) (neutralMode D i ((M : ℤ) - N) v.1)
  rw [current_state_field, neutralField_ncoeff]

private theorem original_four_word (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) :
    actualFourCurrentCycleTrace D hD i n = gradeTrace D hD (n 0)
      (neutralMode D (i 0) ((n 1 : ℤ) - n 0) *
        (neutralMode D (i 1) ((n 2 : ℤ) - n 1) *
          (neutralMode D (i 2) ((n 3 : ℤ) - n 2) *
            neutralMode D (i 3) ((n 0 : ℤ) - n 3)))) := by
  let A := fun a b c => neutralMode D a ((b : ℤ) - (c : ℤ))
  have h3 : ∀ v : Carrier D, v ∈ grade D (n 0 : ℤ) →
      A (i 3) (n 0) (n 3) v ∈ grade D (n 3 : ℤ) := by
    intro v hv
    simpa [A] using mode_hasGrade D (i 3) ((n 0 : ℤ) - n 3) (n 0) v hv
  have h23 : ∀ v : Carrier D, v ∈ grade D (n 0 : ℤ) →
      (A (i 2) (n 3) (n 2) * A (i 3) (n 0) (n 3)) v ∈ grade D (n 2 : ℤ) := by
    intro v hv
    simpa [A] using mode_hasGrade D (i 2) ((n 3 : ℤ) - n 2) (n 3) _ (h3 v hv)
  have h123 : ∀ v : Carrier D, v ∈ grade D (n 0 : ℤ) →
      (A (i 1) (n 2) (n 1) * (A (i 2) (n 3) (n 2) *
        A (i 3) (n 0) (n 3))) v ∈ grade D (n 1 : ℤ) := by
    intro v hv
    simpa [A] using mode_hasGrade D (i 1) ((n 2 : ℤ) - n 1) (n 2) _ (h23 v hv)
  unfold actualFourCurrentCycleTrace gradeTrace
  change LinearMap.trace ℂ (grade D (n 0 : ℤ)) _ =
    LinearMap.trace ℂ (grade D (n 0 : ℤ)) (cutMap D _ (n 0) (n 0))
  simp_rw [original_block]
  rw [cutMap_mul D _ _ (n 0) (n 1) (n 0) h123,
    cutMap_mul D _ _ (n 1) (n 2) (n 0) h23,
    cutMap_mul D _ _ (n 2) (n 3) (n 0) h3]

private def contraction (D : LatticeData) (i j : Fin D.rank) (m n : ℤ) : ℂ :=
  if m + n = 0 then (m : ℂ) * (D.G i j : ℂ) else 0

private theorem four_commutator (D : LatticeData) (i j k s : Fin D.rank)
    (m p q r : ℤ) :
    neutralMode D i m * (neutralMode D j p * (neutralMode D k q * neutralMode D s r)) -
      (neutralMode D j p * (neutralMode D k q * neutralMode D s r)) * neutralMode D i m =
    contraction D i j m p • (neutralMode D k q * neutralMode D s r) +
      contraction D i k m q • (neutralMode D j p * neutralMode D s r) +
        contraction D i s m r • (neutralMode D j p * neutralMode D k q) := by
  have h (a b : Fin D.rank) (u v : ℤ) :
      neutralMode D a u * neutralMode D b v - neutralMode D b v * neutralMode D a u =
      contraction D a b u v • (1 : Module.End ℂ (Carrier D)) :=
    neutralMode_heisenberg D a b u v
  calc
    _ = (neutralMode D i m * neutralMode D j p - neutralMode D j p * neutralMode D i m) *
          (neutralMode D k q * neutralMode D s r) +
        neutralMode D j p * (neutralMode D i m * neutralMode D k q -
          neutralMode D k q * neutralMode D i m) * neutralMode D s r +
        (neutralMode D j p * neutralMode D k q) * (neutralMode D i m * neutralMode D s r -
          neutralMode D s r * neutralMode D i m) := by noncomm_ring
    _ = _ := by rw [h, h, h]; simp [smul_mul_assoc, mul_smul_comm, mul_assoc]

private theorem four_trace_recurrence (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j k s : Fin D.rank) (m p q r N : ℤ) (ht : m + (p + (q + r)) = 0) :
    gradeTrace D hD N
        (neutralMode D i m * (neutralMode D j p * (neutralMode D k q * neutralMode D s r))) -
      gradeTrace D hD (N - m)
        (neutralMode D i m * (neutralMode D j p * (neutralMode D k q * neutralMode D s r))) =
    contraction D i j m p * gradeTrace D hD N (neutralMode D k q * neutralMode D s r) +
      contraction D i k m q * gradeTrace D hD N (neutralMode D j p * neutralMode D s r) +
        contraction D i s m r * gradeTrace D hD N (neutralMode D j p * neutralMode D k q) := by
  have hV : HasGrade D (neutralMode D j p * (neutralMode D k q * neutralMode D s r)) (-m) := by
    have h := hasGrade_mul D _ _ p (q + r) (mode_hasGrade D j p)
      (hasGrade_mul D _ _ q r (mode_hasGrade D k q) (mode_hasGrade D s r))
    convert h using 1 <;> omega
  have hc := gradeTrace_cyclic D hD
    (neutralMode D j p * (neutralMode D k q * neutralMode D s r)) (neutralMode D i m)
    N m hV (mode_hasGrade D i m)
  rw [← hc, ← map_sub, four_commutator, map_add, map_add, map_smul, map_smul, map_smul]
  rfl

private theorem finite_difference_sum (F H : ℤ → ℂ) (ell N : ℕ) (hl : 0 < ell)
    (hneg : ∀ z : ℤ, z < 0 → F z = 0)
    (hstep : ∀ z : ℤ, F z - F (z - ell) = H z) :
    F N = ∑ k ∈ Finset.range (N / ell + 1), H ((N : ℤ) - (k : ℤ) * ell) := by
  have hs : ∀ K : ℕ,
      (∑ k ∈ Finset.range K, H ((N : ℤ) - (k : ℤ) * ell)) =
        F N - F ((N : ℤ) - (K : ℤ) * ell) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ih, ← hstep]
      have he : (N : ℤ) - (K : ℤ) * ell - ell =
          (N : ℤ) - ((K + 1 : ℕ) : ℤ) * ell := by push_cast; ring
      rw [he]
      ring
  have hb : N < (N / ell + 1) * ell :=
    (Nat.div_lt_iff_lt_mul hl).mp (Nat.lt_succ_self (N / ell))
  have hb' : (N : ℤ) - ((N / ell + 1 : ℕ) : ℤ) * ell < 0 := by
    have hc : (N : ℤ) < ((N / ell + 1 : ℕ) : ℤ) * ell := by exact_mod_cast hb
    omega
  have h := hs (N / ell + 1)
  rw [hneg _ hb', sub_zero] at h
  exact h.symm

private theorem four_trace_finite_sum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j k s : Fin D.rank) (ell N : ℕ) (hl : 0 < ell) (p q r : ℤ)
    (ht : (ell : ℤ) + (p + (q + r)) = 0) :
    gradeTrace D hD N
        (neutralMode D i ell * (neutralMode D j p * (neutralMode D k q * neutralMode D s r))) =
      ∑ a ∈ Finset.range (N / ell + 1),
        (contraction D i j ell p *
            gradeTrace D hD ((N : ℤ) - (a : ℤ) * ell)
              (neutralMode D k q * neutralMode D s r) +
          contraction D i k ell q *
            gradeTrace D hD ((N : ℤ) - (a : ℤ) * ell)
              (neutralMode D j p * neutralMode D s r) +
          contraction D i s ell r *
            gradeTrace D hD ((N : ℤ) - (a : ℤ) * ell)
              (neutralMode D j p * neutralMode D k q)) := by
  exact finite_difference_sum _ _ ell N hl
    (fun z hz => gradeTrace_negative D hD z hz _)
    (fun z => four_trace_recurrence D hD i j k s ell p q r z ht)

private def rotateFour {α : Type*} (x : Four → α) : Four → α := fun a => x (a + 1)

private theorem original_four_rotate (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) :
    actualFourCurrentCycleTrace D hD i n =
      actualFourCurrentCycleTrace D hD (rotateFour i) (rotateFour n) := by
  letI := grade_finiteDimensional D hD (n 0 : ℤ)
  letI := grade_finiteDimensional D hD (n 1 : ℤ)
  change LinearMap.trace ℂ (grade D (n 0 : ℤ))
      ((actualCurrentBlock D (i 0) (n 0) (n 1)).comp
        ((actualCurrentBlock D (i 1) (n 1) (n 2)).comp
          ((actualCurrentBlock D (i 2) (n 2) (n 3)).comp
            (actualCurrentBlock D (i 3) (n 3) (n 0))))) =
    LinearMap.trace ℂ (grade D (n 1 : ℤ))
      ((actualCurrentBlock D (i 1) (n 1) (n 2)).comp
        ((actualCurrentBlock D (i 2) (n 2) (n 3)).comp
          ((actualCurrentBlock D (i 3) (n 3) (n 0)).comp
            (actualCurrentBlock D (i 0) (n 0) (n 1)))))
  simpa only [LinearMap.comp_assoc] using LinearMap.trace_comp_comm'
    ((actualCurrentBlock D (i 1) (n 1) (n 2)).comp
      ((actualCurrentBlock D (i 2) (n 2) (n 3)).comp
        (actualCurrentBlock D (i 3) (n 3) (n 0))))
    (actualCurrentBlock D (i 0) (n 0) (n 1))

private theorem original_pair_word (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (N M : ℕ) :
    gradeTrace D hD N
      (neutralMode D i ((M : ℤ) - N) * neutralMode D j ((N : ℤ) - M)) =
      actualCurrentCycleTrace D hD i j N M := by
  change LinearMap.trace ℂ (grade D (N : ℤ)) (cutMap D _ N N) = _
  rw [cutMap_mul D _ _ N M N (by
    intro v hv
    simpa using mode_hasGrade D j ((N : ℤ) - M) N v hv)]
  unfold actualCurrentCycleTrace
  rw [original_block, original_block]

private theorem pair_trace_low_middle (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (N q r : ℤ) (hr : q + r = 0) (hN : N + q < 0) :
    gradeTrace D hD N (neutralMode D i q * neutralMode D j r) = 0 := by
  have hz : cutMap D (neutralMode D i q * neutralMode D j r) N N = 0 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change gradeProjection D N (neutralMode D i q (neutralMode D j r v.1)) = 0
    have h := negative_grade_value D hD (N - r) (by omega) _
      (mode_hasGrade D j r N v.1 v.2)
    rw [h, map_zero, map_zero]
  change LinearMap.trace ℂ (grade D N) (cutMap D _ N N) = 0
  rw [hz, map_zero]

private theorem pair_trace_signed (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (N q r : ℤ) (hr : q + r = 0) :
    gradeTrace D hD N (neutralMode D i q * neutralMode D j r) =
      if 0 ≤ N ∧ 0 ≤ N + q then
        actualCurrentCycleTrace D hD i j N.toNat (N + q).toNat
      else 0 := by
  split_ifs with h
  · have hN : (N.toNat : ℤ) = N := Int.toNat_of_nonneg h.1
    have hM : ((N + q).toNat : ℤ) = N + q := Int.toNat_of_nonneg h.2
    have hq : ((N + q).toNat : ℤ) - N.toNat = q := by omega
    have hr' : (N.toNat : ℤ) - (N + q).toNat = r := by omega
    have he := original_pair_word D hD i j N.toNat (N + q).toNat
    rwa [hq, hr', hN] at he
  · by_cases hN : N < 0
    · exact gradeTrace_negative D hD N hN _
    · exact pair_trace_low_middle D hD i j N q r hr (by omega)

private theorem original_four_zero_charge_trace (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (N : ℕ) :
    actualFourCurrentCycleTrace D hD i (fun _ => N) =
      ∑ β ∈ positiveChargeCutoff D hD (N : ℤ),
        (∏ a : Four, (bilinear D (unitCharge D (i a)) β : ℂ)) *
          (Nat.card (IntegerFiber D (N - (chargeEnergy D β).toNat)) : ℂ) := by
  classical
  letI := energyFiber_finite D hD (N : ℤ)
  letI := Fintype.ofFinite (EnergyFiber D (N : ℤ))
  rw [actual_four_zero_grade_trace]
  rw [sum_fullFiber D hD N (fun β _ =>
    ∏ a : Four, (bilinear D (unitCharge D (i a)) β : ℂ))]
  simp [Nat.card_eq_fintype_card, mul_comm]

private theorem original_four_finite_sum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) (h : n 0 < n 1) :
    let ell := n 1 - n 0
    let p := (n 2 : ℤ) - n 1
    let q := (n 3 : ℤ) - n 2
    let r := (n 0 : ℤ) - n 3
    actualFourCurrentCycleTrace D hD i n =
      ∑ a ∈ Finset.range (n 0 / ell + 1),
        (contraction D (i 0) (i 1) ell p *
            gradeTrace D hD ((n 0 : ℤ) - (a : ℤ) * ell)
              (neutralMode D (i 2) q * neutralMode D (i 3) r) +
          contraction D (i 0) (i 2) ell q *
            gradeTrace D hD ((n 0 : ℤ) - (a : ℤ) * ell)
              (neutralMode D (i 1) p * neutralMode D (i 3) r) +
          contraction D (i 0) (i 3) ell r *
            gradeTrace D hD ((n 0 : ℤ) - (a : ℤ) * ell)
              (neutralMode D (i 1) p * neutralMode D (i 2) q)) := by
  dsimp only
  rw [original_four_word, show (n 1 : ℤ) - n 0 = ((n 1 - n 0 : ℕ) : ℤ) by omega]
  exact four_trace_finite_sum D hD (i 0) (i 1) (i 2) (i 3)
    (n 1 - n 0) (n 0) (by omega) _ _ _ (by omega)

private theorem edges_ordered : ∀ (M : PM4) (e : Four × Four),
    e ∈ M.edges → e.1.1 < e.2.1 := by decide

private theorem le_max4 (n : Four → ℕ) (j : Four) : n j ≤ max4 n := by
  fin_cases j <;> dsimp [max4] <;> omega

private theorem matching_parameter_bounds (n : Four → ℕ) (Q t : ℕ) (M : PM4)
    (ell : edgeParam M → ℕ) (ε : edgeParam M → Fin 2) (k : edgeParam M → ℕ)
    (hpos : ∀ e, 0 < ell e)
    (heq : ∀ j, n j = Q + t + matchingShift M ell ε k j) :
    Q ≤ min4 n ∧ t ≤ min4 n ∧
      ∀ e, ell e ≤ max4 n ∧ k e ≤ min4 n := by
  classical
  have hQ (j : Four) : Q ≤ n j := by have h := heq j; omega
  have ht (j : Four) : t ≤ n j := by have h := heq j; omega
  refine ⟨le_min (le_min (hQ 0) (hQ 1)) (le_min (hQ 2) (hQ 3)),
    le_min (le_min (ht 0) (ht 1)) (le_min (ht 2) (ht 3)), ?_⟩
  intro e
  have hterm (j : Four) :
      ell e * (k e + if sideMem (ε e) e.1 j then 1 else 0) ≤
        matchingShift M ell ε k j := by
    unfold matchingShift
    exact Finset.single_le_sum
      (fun (x : edgeParam M) _ => Nat.zero_le
        (ell x * (k x + if sideMem (ε x) x.1 j then 1 else 0))) (Finset.mem_univ e)
  have hwind (j : Four) : k e ≤ n j := by
    have hmul : k e ≤ ell e * k e := by
      simpa using Nat.mul_le_mul_right (k e) (show 1 ≤ ell e from hpos e)
    have hpart : ell e * k e ≤
        ell e * (k e + if sideMem (ε e) e.1 j then 1 else 0) :=
      Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    have hs := hterm j
    have hn := heq j
    omega
  have hside : ∃ j : Four, sideMem (ε e) e.1 j := by
    by_cases h : (ε e).1 = 0
    · refine ⟨e.1.2, ?_⟩
      simp [sideMem, h, arcMem, edges_ordered M e.1 e.2]
    · refine ⟨e.1.1, ?_⟩
      simp [sideMem, h, arcMem]
  obtain ⟨j, hj⟩ := hside
  have hs := hterm j
  rw [if_pos hj] at hs
  have hl : ell e ≤ ell e * (k e + 1) := by
    simpa using Nat.mul_le_mul_left (ell e) (show 1 ≤ k e + 1 by omega)
  have hn := heq j
  have hm := le_max4 n j
  exact ⟨by omega,
    le_min (le_min (hwind 0) (hwind 1)) (le_min (hwind 2) (hwind 3))⟩

private theorem bounded_matching_assignment (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (n : Four → ℕ) (β : Charge D) (t : ℕ) (M : PM4)
    (ell : edgeParam M → ℕ) (ε : edgeParam M → Fin 2) (k : edgeParam M → ℕ)
    (hpos : ∀ e, 0 < ell e)
    (heq : ∀ j, n j = (chargeEnergy D β).toNat + t + matchingShift M ell ε k j) :
    β ∈ positiveChargeCutoff D hD (min4 n : ℤ) ∧
      ∃ (ell' : edgeParam M → Fin (max4 n + 1))
        (k' : edgeParam M → Fin (min4 n + 1)) (t' : Fin (min4 n + 1)),
        (∀ e, (ell' e).1 = ell e) ∧ (∀ e, (k' e).1 = k e) ∧ t'.1 = t ∧
        (∀ j, n j = (chargeEnergy D β).toNat + t'.1 +
          gradeShift D n β M ell' ε k' j) := by
  have hb := matching_parameter_bounds n (chargeEnergy D β).toNat t M ell ε k hpos heq
  have hq := chargeEnergy_nonneg D hD β
  have hcast := Int.toNat_of_nonneg hq
  have hQ : chargeEnergy D β ≤ (min4 n : ℤ) := by omega
  constructor
  · simpa [positiveChargeCutoff] using hQ
  · refine ⟨(fun e => ⟨ell e, Nat.lt_succ_of_le (hb.2.2 e).1⟩),
      (fun e => ⟨k e, Nat.lt_succ_of_le (hb.2.2 e).2⟩),
      ⟨t, Nat.lt_succ_of_le hb.2.1⟩, (fun _ => rfl), (fun _ => rfl), rfl, ?_⟩
    exact heq

private def signedPairCoefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (N q : ℤ) : ℂ := by
  classical
  let a := N.toNat
  let b := (N + q).toNat
  exact if 0 ≤ N ∧ 0 ≤ N + q then
    if a = b then
      ∑ β ∈ positiveChargeCutoff D hD (a : ℤ),
        (bilinear D (unitCharge D i) β : ℂ) * (bilinear D (unitCharge D j) β : ℂ) *
          occupationMultiplicity D (a - (chargeEnergy D β).toNat)
    else
      (Nat.dist a b : ℂ) * (D.G i j : ℂ) *
        ∑ β ∈ positiveChargeCutoff D hD ((min a b : ℕ) : ℤ),
          ∑ k ∈ Finset.range ((min a b - (chargeEnergy D β).toNat) / Nat.dist a b + 1),
            occupationMultiplicity D (min a b - (chargeEnergy D β).toNat - k * Nat.dist a b)
  else 0

private theorem pair_trace_coefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j : Fin D.rank) (N q r : ℤ) (hr : q + r = 0) :
    gradeTrace D hD N (neutralMode D i q * neutralMode D j r) =
      signedPairCoefficient D hD i j N q := by
  rw [pair_trace_signed D hD i j N q r hr]
  simp only [signedPairCoefficient, actual_two_current_grade_trace]

private theorem contracted_pair_coefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i j k s : Fin D.rank) (m p q r N : ℤ) (ht : m + (p + (q + r)) = 0) :
    contraction D i j m p * gradeTrace D hD N (neutralMode D k q * neutralMode D s r) =
      contraction D i j m p * signedPairCoefficient D hD k s N q := by
  by_cases h : m + p = 0
  · rw [pair_trace_coefficient D hD k s N q r (by omega)]
  · simp [contraction, h]

private theorem original_four_finite_coefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Four → Fin D.rank) (n : Four → ℕ) (h : n 0 < n 1) :
    let ell := n 1 - n 0
    let p := (n 2 : ℤ) - n 1
    let q := (n 3 : ℤ) - n 2
    let r := (n 0 : ℤ) - n 3
    actualFourCurrentCycleTrace D hD i n =
      ∑ a ∈ Finset.range (n 0 / ell + 1),
        (contraction D (i 0) (i 1) ell p *
            signedPairCoefficient D hD (i 2) (i 3) ((n 0 : ℤ) - (a : ℤ) * ell) q +
          contraction D (i 0) (i 2) ell q *
            signedPairCoefficient D hD (i 1) (i 3) ((n 0 : ℤ) - (a : ℤ) * ell) p +
          contraction D (i 0) (i 3) ell r *
            signedPairCoefficient D hD (i 1) (i 2) ((n 0 : ℤ) - (a : ℤ) * ell) p) := by
  dsimp only
  rw [original_four_finite_sum D hD i n h]
  apply Finset.sum_congr rfl
  intro a ha
  rw [contracted_pair_coefficient D hD (i 0) (i 1) (i 2) (i 3) _ _ _ _ _ (by omega),
    contracted_pair_coefficient D hD (i 0) (i 2) (i 1) (i 3) _ _ _ _ _ (by omega),
    contracted_pair_coefficient D hD (i 0) (i 3) (i 1) (i 2) _ _ _ _ _ (by omega)]

end D5.S3.VertexAlgebra.LatticeFourCurrentTrace
