/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFourHHomogeneousExtension
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFourHHomogeneousExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite extension of the native four-H A/B comparison on homogeneous states. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHUpperProduct

/-! The four-H overlap on homogeneous states in the actual even twisted Fock space. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension

open ActualLeechHyperbolic (leechData)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven leechUnit paritySign)
open Orbifold.NativeFullMixedField (project)
open Orbifold.NativeFixedPairField (nu)
open Orbifold.NativeFixedUpperRightSkew (rightField)
open LatticeGeneratingFieldLocality (Index)
open LatticeHalfFockGradedTrace
open LatticeHalfFockChargedTensorCoefficients (ActualGround ActualTensor groundRank)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeTwistedGroundRealization (Half)
open LatticeHalfFockParityT (actualParity actualParity_on_actualGrade)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open ActualChargedAdjoint (actualForm)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open NativeMixedWickChartTransport (doubledOccupation laurentRoot sigma)
open NativeFourHUpperProduct (fixedBProductCoeff fixedBProduct_hasSum fourH_actual_A_eq_B)
open NativeFixedPairAIterate (fixedAIterateCoeff fixedAIterate_hasSum_on_overlap)
open NativeAffineExternalCoefficient (jetOccupation)

open private punctureModes punctureExcitation punctureExcitation_cast from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
open private word_monomial word_weight from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMVariableSupport
open private doubledWeight_cast from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient
open private project_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFullMixedField
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField

local notation "ℒ" => leechData
private abbrev BasisIndex := OddMonomial ℒ × Half (groundRank ℒ leechUnit)
private abbrev ambientBasis := actualAmbientBasis ℒ leechUnit
private abbrev HSpace := paritySpace ℒ leechUnit (paritySign false)

/-- Positive oscillator parity forces a homogeneous state in an odd grade to vanish. -/
theorem homogeneousH_zero_of_odd_grade (N : ℕ) (u : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit N) (hN : ¬ Even N) : u = 0 := by
  have hp : actualParity ℒ leechUnit u.val = u.val := by
    have hu' : u.val ∈ HSpace := u.property
    simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero, paritySign, Bool.false_eq_true, ↓reduceIte, one_smul]
      using hu'
  have he := actualParity_on_actualGrade ℒ leechUnit N ⟨u.val, hu⟩
  change actualParity ℒ leechUnit u.val = (-1 : ℂ) ^ N • u.val at he
  rw [neg_one_pow_eq_ite, ite_eq_right hN, neg_one_smul, hp] at he
  have hz : (2 : ℂ) • u.val = 0 := by
    rw [two_smul]
    nth_rw 1 [he]
    exact neg_add_cancel _
  exact Subtype.ext ((smul_eq_zero.mp hz).resolve_left (by norm_num))

/-- Every supported ambient basis coordinate of a homogeneous H state has
the state's grade, which is even whenever the support is nonempty. -/
theorem homogeneousH_support (N : ℕ) (u : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit N) :
    ∀ i ∈ (ambientBasis.repr u.val).support, oddWeight ℒ i.1 = N ∧ Even N := by
  intro i hi
  refine ⟨(actual_grade_mem_iff_repr_support ℒ leechUnit N u.val).mp hu i hi, ?_⟩
  by_contra hN
  have hz : u.val = 0 :=
    congrArg Subtype.val (homogeneousH_zero_of_odd_grade N u hu hN)
  exact (Finsupp.mem_support_iff.mp hi) (by rw [hz, map_zero, Finsupp.zero_apply])

private theorem basis_mem_grade (i : BasisIndex) :
    ambientBasis i ∈ actualGrade ℒ leechUnit (oddWeight ℒ i.1) := by
  simpa only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero, Prod.eta]
    using actual_basis_eigenvalue ℒ leechUnit i.1 i.2

private abbrev projectedBasis (i : BasisIndex) : TwistedEven := project false (ambientBasis i)

private theorem projectedBasis_val (i : BasisIndex) (hi : Even (oddWeight ℒ i.1)) :
    (projectedBasis i).val = ambientBasis i := by
  have hp := actualParity_on_actualGrade ℒ leechUnit _
    ⟨ambientBasis i, basis_mem_grade i⟩
  change actualParity ℒ leechUnit (ambientBasis i) =
    (-1 : ℂ) ^ oddWeight ℒ i.1 • ambientBasis i at hp
  rw [hi.neg_one_pow, one_smul] at hp
  change (project false (ambientBasis i)).val = ambientBasis i
  rw [project_val, hp]
  simp only [paritySign, Bool.false_eq_true, ↓reduceIte, one_smul]
  rw [← two_smul ℂ, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

/-- The supported basis terms of a homogeneous H state retain their actual
oscillator monomial and ground coordinate after projection. -/
theorem homogeneousH_basis_expansion (N : ℕ) (u : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit N) :
    (∑ i ∈ (ambientBasis.repr u.val).support,
      ambientBasis.repr u.val i • projectedBasis i) = u ∧
    ∀ i ∈ (ambientBasis.repr u.val).support,
      (projectedBasis i).val =
        MvPolynomial.monomial i.1 (1 : ℂ) ⊗ₜ[ℂ] Pi.single i.2 (1 : ℂ) ∧
      (projectedBasis i).val ∈ actualGrade ℒ leechUnit N := by
  refine ⟨sum_projectedBasis false u, ?_⟩
  intro i hi
  obtain ⟨hgrade, heven⟩ := homogeneousH_support N u hu i hi
  have hiEven : Even (oddWeight ℒ i.1) := by rwa [hgrade]
  rw [projectedBasis_val i hiEven]
  exact ⟨actual_basis_apply ℒ leechUnit i.1 i.2, by simpa only [hgrade] using basis_mem_grade i⟩

private theorem jetOccupation_toList (d : OddMonomial ℒ) :
    jetOccupation d.toMultiset.toList = d := by
  classical
  have count (l : List (Index ℒ)) (a : Index ℒ) :
      jetOccupation l a = (l : Multiset (Index ℒ)).count a := by
    induction l with
    | nil => simp [jetOccupation]
    | cons i l ih =>
      by_cases h : i = a
      · subst i
        simp [jetOccupation, ih, Multiset.coe_count]
      · simp [jetOccupation, ih, h, Ne.symm h, Multiset.coe_count]
  ext a
  rw [count, Multiset.coe_toList, Finsupp.count_toMultiset]

/-- A joint list of distinct marks realizes four arbitrary occupations and
records their exact doubled grades. Repeated oscillator modes use distinct marks. -/
theorem occupation_monomials_have_marked_words (d : Puncture → OddMonomial ℒ) :
    ∃ (m : ℕ) (slot : Fin m → Puncture) (colour : Fin m → Fin leechData.rank) (n : Fin m → ℕ),
      ∀ i : Puncture,
        wordAt ℒ slot colour n (List.finRange m) i = MvPolynomial.monomial (d i) 1 ∧
        doubledOccupation slot n (List.finRange m) i = (oddWeight ℒ (d i) : ℤ) := by
  classical
  let L (i : Puncture) := (d i).toMultiset.toList
  let block (i : Puncture) := (L i).map fun a => (i, a)
  let marks := block .P ++ block .Q ++ block .R ++ block .S
  let label : Fin marks.length → Puncture × Index ℒ := marks.get
  let slot (j : Fin marks.length) := (label j).1
  let colour (j : Fin marks.length) := (label j).2.1
  let n (j : Fin marks.length) := (label j).2.2
  let l := List.finRange marks.length
  have hblock (i j : Puncture) :
      (((block i).filter fun a => decide (a.1 = j)).map Prod.snd) =
        if i = j then L i else [] := by
    by_cases hij : i = j <;> simp [block, List.filter_map, List.map_map, Function.comp_def, hij]
  have hmarks (i : Puncture) :
      ((marks.filter fun a => decide (a.1 = i)).map Prod.snd) = L i := by
    dsimp only [marks]
    simp only [List.filter_append, List.map_append, hblock]
    cases i <;> simp
  have hmode (i : Puncture) :
      ((l.filter fun a => decide (slot a = i)).map fun a => (colour a, n a)) = L i := by
    calc
      _ = (((l.filter fun a => decide (slot a = i)).map label).map Prod.snd) := by
        rw [List.map_map]
        rfl
      _ = _ := by
        have hmap : l.map label = marks := List.map_get_finRange marks
        rw [show ((l.filter fun a => decide (slot a = i)).map label) =
            ((l.map label).filter fun a => decide (a.1 = i)) by
          rw [List.filter_map]
          rfl, hmap]
        exact hmarks i
  refine ⟨marks.length, slot, colour, n, fun i => ⟨?_, ?_⟩⟩
  · unfold wordAt
    rw [hmode i, word_monomial]
    change MvPolynomial.monomial (jetOccupation (d i).toMultiset.toList) 1 = _
    rw [jetOccupation_toList]
  · rw [← punctureExcitation_cast slot colour n l i]
    unfold punctureExcitation
    have hm : punctureModes slot colour n l i = L i := hmode i
    rw [hm]
    have h := word_weight ℒ (d i).toMultiset.toList
    rw [doubledWeight_cast, jetOccupation_toList (d i)] at h
    exact h.symm

private abbrev FourLinear :=
  TwistedEven →ₗ[ℂ] TwistedEven →ₗ[ℂ] TwistedEven →ₗ[ℂ] TwistedEven →ₗ[ℂ] ℂ

private def coeffAt {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : ℤ) :
    HVertexOperator ℤ ℂ V W →ₗ[ℂ] V →ₗ[ℂ] W :=
  (LinearMap.proj e).comp HVertexOperator.coeff

private def pairWithH : ActualTensor ℒ leechUnit →ₗ[ℂ] TwistedEven →ₗ[ℂ] ℂ :=
  (actualForm ℒ leechUnit).flip.compl₂ HSpace.subtype

private def aSummand (M K L N : ℕ) (y : ℝ) (j : ℤ) : FourLinear :=
  let inner := (coeffAt j).comp (nu false)
  let outer := ((coeffAt ((N : ℤ) - (L : ℤ) - (j + ((M : ℤ) + (K : ℤ) + 6)))).comp
    (correctedField ℒ leechUnit)).compl₁₂ (LatticeInvolution.fixedSpace ℒ).subtype HSpace.subtype
  (laurentRoot .A y ^ j) • inner.compr₂ (outer.compr₂ pairWithH)

private def bSummand (M K L N : ℕ) (y : ℝ) (E : ℕ) : FourLinear :=
  let inner := (coeffAt (2 * (E : ℤ) - (6 + (K : ℤ) + L))).comp (nu false)
  let outer := ((coeffAt ((N : ℤ) - M - 2 * (E : ℤ))).comp
    (rightField ℒ leechUnit false)).flip
  let product := inner.compr₂ (outer.compr₂ (pairWithH.comp HSpace.subtype))
  let swap : (TwistedEven →ₗ[ℂ] TwistedEven →ₗ[ℂ] TwistedEven →ₗ[ℂ] ℂ) →ₗ[ℂ]
      TwistedEven →ₗ[ℂ] TwistedEven →ₗ[ℂ] TwistedEven →ₗ[ℂ] ℂ :=
    LinearMap.lflip.toLinearMap
  (Real.sqrt y : ℂ) ^ (2 * (E : ℤ) - (6 + (K : ℤ) + L)) • (swap.comp product).flip

private theorem aSummand_apply (M K L N : ℕ) (y : ℝ) (j : ℤ) (u v w b : TwistedEven) :
    aSummand M K L N y j u v w b =
      fixedAIterateCoeff false M K L N j u v w.val b.val * laurentRoot .A y ^ j := by
  exact mul_comm _ _

private theorem bSummand_apply (M K L N : ℕ) (y : ℝ) (E : ℕ) (u v w b : TwistedEven) :
    bSummand M K L N y E u v w b =
      fixedBProductCoeff false false M K L N v w u b E *
        (Real.sqrt y : ℂ) ^ (2 * (E : ℤ) - (6 + (K : ℤ) + L)) := by
  exact mul_comm _ _

private theorem fourH_basis_comparison (g : Puncture → ℕ) (d : Puncture → BasisIndex)
    (hd : ∀ i, oddWeight ℒ (d i).1 = g i ∧ Even (g i))
    {y : ℝ} (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) :
    let U := projectedBasis ∘ d
    let A := fun j => aSummand (g .P) (g .Q) (g .R) (g .S) y j (U .P) (U .Q) (U .R) (U .S)
    let B := fun E => bSummand (g .P) (g .Q) (g .R) (g .S) y E (U .P) (U .Q) (U .R) (U .S)
    Summable A ∧ Summable B ∧
      (∑' j, A j) = (y : ℂ) ^ sigma (g .P : ℤ) (g .Q) (g .R) (g .S) * ∑' E, B E := by
  classical
  obtain ⟨m, slot, colour, n, hmarks⟩ :=
    occupation_monomials_have_marked_words (fun i => (d i).1)
  let l := List.finRange m
  let U := projectedBasis ∘ d
  let W := wordAt ℒ slot colour n l
  let G (i : Puncture) : ActualGround ℒ leechUnit := Pi.single (d i).2 1
  have hG (i : Puncture) : doubledOccupation slot n l i = (g i : ℤ) := by
    rw [(hmarks i).2, (hd i).1]
  have hEven (i : Puncture) : Even (g i : ℤ) := by
    obtain ⟨k, hk⟩ := (hd i).2
    exact ⟨(k : ℤ), by exact_mod_cast hk⟩
  have hpar (i : Puncture) : Even (doubledOccupation slot n l i) := by
    rw [hG i]
    exact hEven i
  have heven (i : Puncture) : Even (oddWeight ℒ (d i).1) := by
    rw [(hd i).1]
    exact (hd i).2
  have hU (i : Puncture) : (U i).val = W i ⊗ₜ[ℂ] G i := by
    calc
      (U i).val = ambientBasis (d i) := projectedBasis_val (d i) (heven i)
      _ = _ := by
        change ambientBasis (d i) = wordAt ℒ slot colour n l i ⊗ₜ[ℂ] Pi.single (d i).2 1
        rw [(hmarks i).1]
        exact actual_basis_apply ℒ leechUnit (d i).1 (d i).2
  have hgrade (i : Puncture) : (U i).val ∈ actualGrade ℒ leechUnit (g i) := by
    change (projectedBasis (d i)).val ∈ actualGrade ℒ leechUnit (g i)
    rw [projectedBasis_val (d i) (heven i)]
    simpa only [(hd i).1] using basis_mem_grade (d i)
  have hwordGrade (i : Puncture) : W i ⊗ₜ[ℂ] G i ∈ actualGrade ℒ leechUnit (g i) :=
    hU i ▸ hgrade i
  have ha := fixedAIterate_hasSum_on_overlap false (g .P) (g .Q) (g .R) (g .S)
    (U .P) (U .Q) (W .P) (W .Q) (W .R) (W .S) (G .P) (G .Q) (G .R) (G .S)
    (hgrade .P) (hgrade .Q) (hU .P) (hU .Q) (hwordGrade .R) (hwordGrade .S)
    ((hEven .P).add (hEven .Q)) hy hy₁
  have hb := fixedBProduct_hasSum false false (g .P) (g .Q) (g .R) (g .S)
    (U .Q) (U .R) (U .P) (U .S) (W .P) (W .Q) (W .R) (W .S) (G .P) (G .Q) (G .R) (G .S)
    (hgrade .Q) (hgrade .R) (hgrade .P) (hgrade .S) (hU .Q) (hU .R) (hU .P) (hU .S)
    ((hEven .Q).add (hEven .R)) ((hEven .S).sub (hEven .P)) (by linarith) hy₁
  have heq := fourH_actual_A_eq_B slot colour n l (List.nodup_finRange m) hpar
    (U .P) (U .Q) (U .R) (U .S) (G .P) (G .Q) (G .R) (G .S)
    (hU .P) (hU .Q) (hU .R) (hU .S) hy hy₁
  dsimp only at ha heq ⊢
  simp only [aSummand_apply, bSummand_apply]
  refine ⟨?_, hb.summable, ?_⟩
  · rw [hU .R, hU .S]
    exact ha.summable
  · simpa only [hG, Int.toNat_natCast] using heq

/-- On the real overlap, the genuine A iterate and B product for four
homogeneous H states are summable. Their sums differ by the chart power
determined by the four doubled excitation grades. -/
theorem fourH_actual_A_eq_B_of_homogeneous (M K L N : ℕ) (u v w b : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    {y : ℝ} (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) :
    let A := fun j : ℤ => fixedAIterateCoeff false M K L N j u v w.val b.val *
      laurentRoot .A y ^ j
    let B := fun E : ℕ => fixedBProductCoeff false false M K L N v w u b E *
      (Real.sqrt y : ℂ) ^ (2 * (E : ℤ) - (6 + (K : ℤ) + L))
    Summable A ∧ Summable B ∧
      (∑' j, A j) = (y : ℂ) ^ sigma (M : ℤ) K L N * ∑' E, B E := by
  classical
  let a := aSummand M K L N y
  let c := bSummand M K L N y
  let scale : ℂ := (y : ℂ) ^ sigma (M : ℤ) K L N
  let coord (x : TwistedEven) := ambientBasis.repr x.val
  let combine (F : BasisIndex → BasisIndex → BasisIndex → BasisIndex → ℂ) :=
    ∑ i ∈ (coord u).support, coord u i *
      (∑ j ∈ (coord v).support, coord v j *
        (∑ k ∈ (coord w).support, coord w k *
          (∑ l ∈ (coord b).support, coord b l * F i j k l)))
  have expand (F : FourLinear) :
      F u v w b = combine (fun i j k l =>
        F (projectedBasis i) (projectedBasis j) (projectedBasis k) (projectedBasis l)) := by
    conv_lhs =>
      rw [← (homogeneousH_basis_expansion M u hu).1]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← (homogeneousH_basis_expansion K v hv).1]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← (homogeneousH_basis_expansion L w hw).1]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← (homogeneousH_basis_expansion N b hb).1]
      simp only [map_sum, map_smul, smul_eq_mul]
  have hasSum_combine {ι : Type} (F : ι → FourLinear)
      (h : ∀ i ∈ (coord u).support, ∀ j ∈ (coord v).support,
        ∀ k ∈ (coord w).support, ∀ l ∈ (coord b).support,
        Summable (fun e => F e (projectedBasis i) (projectedBasis j)
          (projectedBasis k) (projectedBasis l))) :
      HasSum (fun e => F e u v w b) (combine fun i j k l =>
        ∑' e, F e (projectedBasis i) (projectedBasis j) (projectedBasis k) (projectedBasis l)) := by
    unfold combine
    refine (hasSum_sum (s := (coord u).support) fun i hi => ?_).congr_fun
      (fun e => expand (F e))
    refine HasSum.mul_left (coord u i) <| hasSum_sum (s := (coord v).support) fun j hj => ?_
    refine HasSum.mul_left (coord v j) <| hasSum_sum (s := (coord w).support) fun k hk => ?_
    refine HasSum.mul_left (coord w k) <| hasSum_sum (s := (coord b).support) fun l hl => ?_
    exact (h i hi j hj k hk l hl).hasSum.mul_left (coord b l)
  let g : Puncture → ℕ
    | .P => M
    | .Q => K
    | .R => L
    | .S => N
  have hBasis (i : BasisIndex) (hi : i ∈ (coord u).support)
      (j : BasisIndex) (hj : j ∈ (coord v).support) (k : BasisIndex) (hk : k ∈ (coord w).support)
      (l : BasisIndex) (hl : l ∈ (coord b).support) :
      let A := fun e => a e (projectedBasis i) (projectedBasis j) (projectedBasis k) (projectedBasis l)
      let B := fun e => c e (projectedBasis i) (projectedBasis j) (projectedBasis k) (projectedBasis l)
      Summable A ∧ Summable B ∧ (∑' e, A e) = scale * ∑' e, B e := by
    let d : Puncture → BasisIndex
      | .P => i
      | .Q => j
      | .R => k
      | .S => l
    exact fourH_basis_comparison g d (fun
      | .P => homogeneousH_support M u hu i hi
      | .Q => homogeneousH_support K v hv j hj
      | .R => homogeneousH_support L w hw k hk
      | .S => homogeneousH_support N b hb l hl) hy hy₁
  have hA := hasSum_combine (ι := ℤ) a (fun i hi j hj k hk l hl => (hBasis i hi j hj k hk l hl).1)
  have hB := hasSum_combine (ι := ℕ) c (fun i hi j hj k hk l hl => (hBasis i hi j hj k hk l hl).2.1)
  suffices h :
      Summable (fun e => a e u v w b) ∧ Summable (fun e => c e u v w b) ∧
        (∑' e, a e u v w b) = scale * ∑' e, c e u v w b by
    simpa only [a, c, scale, aSummand_apply, bSummand_apply] using h
  refine ⟨hA.summable, hB.summable, ?_⟩
  rw [hA.tsum_eq, hB.tsum_eq]
  dsimp only [combine]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj =>
    Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
  rw [(hBasis i hi j hj k hk l hl).2.2]
  ring

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension
