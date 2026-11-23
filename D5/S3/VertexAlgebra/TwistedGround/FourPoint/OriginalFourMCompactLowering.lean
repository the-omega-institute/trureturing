/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The four actual inverse lowering words in the compact physical Wick readout. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAssignmentPolynomial
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPartitionProduct

/-! The correction endpoint partitions and surviving native creators
assemble into the product of the four lowered oscillator words. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCompactLowering

open LatticeGeneratingFieldLocality LatticeHalfFock
open FourPoint.OriginalFourMActualChart
open OriginalFourMOccupationTransport (flags)
open OriginalFourMPhysicalCovariance (relative)
open OriginalFourMPhysicalProduct (physicalChargeSummand)
open OriginalFourMChartProduct (chartTau)
open OriginalFourMSpatialWick (spatialCoefficient)
open OriginalFourMFixedChargeWick (Mode modeMatrix physical_marked_coefficient_assign)
open OriginalFourMInverseJets (inverseJetWeight)
open OriginalFourMOccurrenceWick (liftedScale)
open OriginalFourMSlotCorrectionLowering (slot_lowering_partition)
open OriginalFourMAssignedOccupation (compactMode compactCovariance compactMean)
open OriginalFourMAssignmentPolynomial (assignmentPolynomial affineReadout native_part_polynomial)
open OriginalFourMPartitionProduct (filterParts partition_products)
open OriginalGaussianSourceRestriction (CompactExternal)
open OriginalFourMWickLowering (pairWeight eval_word_partition)
open HalfFock.OriginalHalfCurrentWickPolynomial (word creator)
open AffineOccurrenceWick (wick)
open AffineWickConvolution (partitions)

variable {X : Type*} [Fintype X] [DecidableEq X]

private abbrev Compact (D : LatticeData) (F : Finset (Index D)) :=
  CompactExternal D F ⊕ CompactExternal D F

/-- Embed the oscillator variables of a given puncture into the compact
joint polynomial, sending oscillator indices outside the support to zero. -/
def tagOscillators (D : LatticeData) (c : Chart) (i : Puncture) (F : Finset (Index D)) :
    Oscillator D →ₐ[ℂ] MvPolynomial (Compact D F) ℂ :=
  MvPolynomial.aeval fun a => if h : a ∈ F then
    let b : {j // j ∈ F} := ⟨a, h⟩
    let e : CompactExternal D F := if (flags c i).2 then .inr b else .inl b
    MvPolynomial.X (if (flags c i).1 then .inr e else .inl e)
  else 0

open private sum_mode from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMFixedChargeWick

private theorem creator_to_compact (D : LatticeData) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) (a : X) :
    (∑ k, modeMatrix c x slot n a k •
      MvPolynomial.X (compactMode D c slot colour F hF k)) =
      liftedScale c x (slot a) (n a) •
        tagOscillators D c (slot a) F
          ((creator D (colour a, n a)).eval (MvPolynomial.C (-loweringParameter c (slot a)))) := by
  classical
  let m := n a
  let i := slot a
  let θ := -loweringParameter c i
  let T := tagOscillators D c i F
  let W : ℕ → MvPolynomial (Compact D F) ℂ := fun k =>
    Ring.choose ((m : ℂ) + 1 / 2) k •
      (θ ^ k • T (MvPolynomial.X (colour a, m - k)))
  have hT : T ((creator D (colour a, m)).eval (MvPolynomial.C θ)) =
      ∑ k ∈ Finset.range (m + 1), W k := by
    simp only [T, creator, W, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      map_sum, map_mul, map_pow, MvPolynomial.C_eq_algebraMap, AlgHom.commutes,
      MvPolynomial.smul_eq_C_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hT, ← Finset.sum_range_reflect W (m + 1)]
  simp only [liftedScale, Finset.smul_sum, MvPolynomial.smul_eq_C_mul,
    modeMatrix, Matrix.of_apply, Fintype.sum_sigma, apply_ite, map_zero, ite_mul, zero_mul]
  rw [Finset.sum_eq_single a]
  · simp only [ite_true]
    have he : (∑ k : Fin (m + 1),
        MvPolynomial.C (relative c i * inverseJetWeight c x i m k) *
          MvPolynomial.X (compactMode D c slot colour F hF ⟨a, k⟩)) =
        ∑ k : Fin (m + 1), MvPolynomial.C (liftedScale c x i m) * W (m - k) := by
      apply Finset.sum_congr rfl
      intro k _
      have hk : m - (m - k.val) = k.val := by omega
      simp only [W, hk, T, tagOscillators, MvPolynomial.aeval_X,
        dite_eq_left (hF ⟨a, k⟩), compactMode, θ, MvPolynomial.smul_eq_C_mul,
        inverseJetWeight, liftedScale, map_mul, map_pow]
      ring
    change _ = ∑ k ∈ Finset.range (m + 1),
      MvPolynomial.C (liftedScale c x i m) * W (m + 1 - 1 - k)
    rw [he, Fin.sum_univ_eq_sum_range
      (fun k => MvPolynomial.C (liftedScale c x i m) * W (m - k)) (m + 1)]
    simp only [Nat.add_sub_cancel]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

private theorem word_scales {Y : Type*} {R : Type*} [CommMonoid R]
    (s : Y → R) (l : List Y) (p : List Y × List Y) (hp : p ∈ partitions l) :
    (p.1.map s).prod * (p.2.map s).prod = (l.map s).prod := by
  induction l generalizing p with
  | nil =>
    simp [partitions] at hp
    subst p
    simp
  | cons a l ih =>
    simp only [partitions, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ <;>
      simp only [List.map_cons, List.prod_cons] <;>
      rw [← ih q hq] <;> ac_rfl

private theorem word_slots {Y S R : Type*} [DecidableEq S] [CommMonoid R]
    (slot : Y → S) (slots : Finset S) (v : Y → R) (l : List Y)
    (h : ∀ a ∈ l, slot a ∈ slots) :
    (l.map v).prod = ∏ i ∈ slots, ((l.filter fun a => decide (slot a = i)).map v).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    have ha : slot a ∈ slots := h a List.mem_cons_self
    conv_lhs => rw [← Finset.insert_erase ha, Finset.prod_insert (Finset.notMem_erase _ _)]
    conv_rhs => rw [← Finset.insert_erase ha, Finset.prod_insert (Finset.notMem_erase _ _)]
    rw [← mul_assoc]
    congr 1
    · simp
    · apply Finset.prod_congr rfl
      intro j hj
      simp [Finset.ne_of_mem_erase hj |>.symm]

private theorem list_prod_scale {Y I : Type*} (s : Y → ℂ) (v : Y → MvPolynomial I ℂ)
    (l : List Y) : (l.map fun a => s a • v a).prod = (l.map s).prod • (l.map v).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, ih, smul_mul_smul_comm]

/-- A physical fixed-charge marked jet is the readout of the four actual
lowering words in the tagged compact algebra, with one lifted scale per occurrence. -/
theorem physical_marked_compact_lowering (D : LatticeData) (hu : IsUnit D.G.det)
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool) (c : Chart)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hc : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D ∧ upperA = true)
    (q : Charge D) (n : X → ℕ) (l : List X) (hl : l.Nodup)
    (F : Finset (Index D)) (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) :
    spatialCoefficient (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
      (physicalChargeSummand D slot colour upperA c x q) 0 =
    Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
      ((l.map fun a => liftedScale c x (slot a) (n a)).prod *
        affineReadout (compactCovariance D c x F) (compactMean D q c x F)
          (open Classical in ∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture),
            tagOscillators D c i F
              ((word D ((l.filter fun a => decide (slot a = i)).map fun a => (colour a, n a))).eval
                (MvPolynomial.C (-loweringParameter c i))))) := by
  classical
  let slots : Finset Puncture := {.P, .Q, .R, .S}
  let s a := liftedScale c x (slot a) (n a)
  let B i a := tagOscillators D c i F
    ((creator D (colour a, n a)).eval (MvPolynomial.C (-loweringParameter c i)))
  let R := affineReadout (compactCovariance D c x F) (compactMean D q c x F)
  let C (i : Puncture) := Matrix.of fun a b => pairWeight D (-loweringParameter c i)
    (colour a, n a) (colour b, n b)
  let G (i : Puncture) (p : List X × List X) :=
    MvPolynomial.C (wick (C i) 0 p.1) * (p.2.map (B i)).prod
  have hcols (a : X) : slot a ∈ slots := by cases slot a <;> simp [slots]
  have hc' : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D :=
    hc.imp id And.left
  rw [physical_marked_coefficient_assign D hu slot colour upperA c hx hx₁ hc q n l hl]
  congr 1
  simp only [native_part_polynomial D q c hx hx₁ hc' slot colour n F hF,
    assignmentPolynomial, creator_to_compact D c x slot colour n F hF]
  have hp (p : List X × List X) (hp : p ∈ partitions l) :
      (p.1.map s).prod *
        (∏ i ∈ slots, wick (C i) 0 (p.1.filter fun a => decide (slot a = i))) *
        R ((p.2.map fun a => s a • B (slot a) a).prod) =
      (l.map s).prod * R (∏ i ∈ slots, G i (filterParts (fun a => decide (slot a = i)) p)) := by
    rw [list_prod_scale, map_smul, smul_eq_mul]
    have hscale := word_scales s l p hp
    calc
      _ = (l.map s).prod * ((∏ i ∈ slots, wick (C i) 0
          (p.1.filter fun a => decide (slot a = i))) * R (p.2.map fun a => B (slot a) a).prod) := by
        rw [← hscale]
        ring
      _ = _ := by
        have he (i : Puncture) :
            ((p.2.filter fun a => decide (slot a = i)).map fun a => B (slot a) a).prod =
            ((p.2.filter fun a => decide (slot a = i)).map (B i)).prod := by
          apply congrArg List.prod
          apply List.map_congr_left
          intro a ha
          exact congrArg (fun j => B j a) (of_decide_eq_true (List.mem_filter.mp ha).2)
        rw [word_slots slot slots (fun a => B (slot a) a) p.2 (fun a _ => hcols a)]
        simp only [he, G, filterParts, Finset.prod_mul_distrib]
        rw [← map_prod (MvPolynomial.C (σ := Compact D F)), ← MvPolynomial.smul_eq_C_mul,
          map_smul, smul_eq_mul]
  change ((partitions l).map fun p => (p.1.map s).prod *
      (∏ i ∈ slots, wick (C i) 0 (p.1.filter fun a => decide (slot a = i))) *
      R ((p.2.map fun a => s a • B (slot a) a).prod)).sum = _
  rw [show ((partitions l).map fun p => (p.1.map s).prod *
        (∏ i ∈ slots, wick (C i) 0 (p.1.filter fun a => decide (slot a = i))) *
        R ((p.2.map fun a => s a • B (slot a) a).prod)).sum =
        ((partitions l).map fun p => (l.map s).prod *
          R (∏ i ∈ slots, G i (filterParts (fun a => decide (slot a = i)) p))).sum from
        congrArg List.sum (List.map_congr_left hp)]
  rw [List.sum_map_mul_left]
  let H (p : List X × List X) := ∏ i ∈ slots, G i (filterParts (fun a => decide (slot a = i)) p)
  have hsum : ((partitions l).map fun p => R (H p)).sum =
      R (((partitions l).map H).sum) := by
    rw [map_list_sum, List.map_map]
    rfl
  rw [hsum]
  have hparts := partition_products slot slots l (fun a _ => hcols a) G
  change ((partitions l).map H).sum = _ at hparts
  rw [hparts]
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  have h := congrArg (tagOscillators D c i F)
    (eval_word_partition D hu (-loweringParameter c i) (fun a => (colour a, n a))
      (l.filter fun a => decide (slot a = i)))
  simpa only [map_list_sum, List.map_map, Function.comp_def, map_mul, map_list_prod,
    MvPolynomial.C_eq_algebraMap, AlgHom.commutes, G, B, C] using h.symm

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCompactLowering
