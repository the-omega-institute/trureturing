/- GID: D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockOddCyclicExtraction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/LatticeHalfFockOddCyclicExtraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native fixed modes extract a nonzero one-oscillator tensor in negative parity. -/

/- proof_shape: nonzero_fixedParitySlice_stable_submodule_contains_one_oscillator: content
admission_basis: escape-witness
escape_witness: An even word of partial derivatives leaves a nonzero linear oscillator
coordinate and forces every surviving exponent in every ground coordinate to have
degree one. A number operator then isolates a nonzero pure tensor in the submodule.
Literature status: classical twisted lattice orbifold theory; no novelty claim.
-/
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockFixedCyclicReduction
import D5.S3.VertexAlgebra.ActualTensorGroundIntersection

/-! Extraction of a one-oscillator tensor from native fixed-mode stability in the odd sector. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockOddCyclicExtraction

open LatticeGeneratingFieldLocality
open LatticeAllStateField (occurrences vacuum)
open LatticeHalfFock (tensorCurrent tensorEnd)
open LatticeHalfFockChargedTensorCoefficients (ActualGround ActualTensor groundRank)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockCurrentBorcherds (current_coeff)
open LatticeHalfFockParityField (fixedParitySlice paritySpace)
open LatticeHalfFockParityT (actualParity)
open LatticeHalfFockFixedCyclicReduction (current_after_odd_coeff_mem_fixedParitySlice_span)
open LatticeInvolution (FixedCarrier sigma sigmaLinear sigma_monomial sigma_smul theta
  theta_neutralMode theta_vacuum)
open LatticeTwistedGroundRealization (Half)
open ActualTensorGroundIntersection (coordinates coordinates_tmul coordinates_tensorEnd
  partialEnd coordinates_partialEnd partialEnd_eq_sum_currents)
open MvPolynomial
open scoped BigOperators TensorProduct VertexOperator

noncomputable section

/-- The native occurrence list counts the total degree of its exponent. -/
theorem occurrences_length (D : LatticeData) (d : Index D →₀ ℕ) :
    (occurrences D d).length = d.degree := by
  simpa only [occurrences, Multiset.length_toList] using
    (show Multiset.card (Finsupp.toMultiset d) = d.degree from Finsupp.card_toMultiset d)

private theorem coeff_sigma (D : LatticeData) (p : Oscillator D) (d : Index D →₀ ℕ) :
    (sigma D p).coeff d = (-1 : ℂ)^d.degree * p.coeff d := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    have hc : c • (monomial m 1 : Oscillator D) = monomial m c := by
      simp only [smul_monomial, smul_eq_mul, mul_one]
    have hsign : sigma D (monomial m c) = (-1 : ℂ)^m.degree • monomial m c := by
      rw [← hc, sigma_smul, sigma_monomial, occurrences_length]
      exact smul_comm c ((-1 : ℂ)^m.degree) (monomial m 1 : Oscillator D)
    rw [hsign, coeff_smul, smul_eq_mul]
    by_cases h : m = d
    · subst d
      rfl
    · simp [coeff_monomial, h]
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, mul_add]

/-- Each monomial in a ground coordinate of an actual negative-parity tensor has odd degree. -/
theorem odd_of_mem_coordinate_support
    (D : LatticeData) (hu : IsUnit D.G.det) (t : ActualTensor D hu)
    (ht : t ∈ paritySpace D hu (-1)) (b : Half (groundRank D hu))
    (d : Index D →₀ ℕ) (hd : d ∈ (coordinates D hu t b).support) : Odd d.degree := by
  have hparity : actualParity D hu t = -t := by
    simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero, neg_one_smul, LinearMap.neg_apply] using ht
  have h := congrArg (fun r => coordinates D hu r b) hparity
  change coordinates D hu (tensorEnd D (ActualGround D hu) (sigmaLinear D) t) b =
    coordinates D hu (-t) b at h
  rw [coordinates_tensorEnd, map_neg, Pi.neg_apply] at h
  change sigma D (coordinates D hu t b) = -(coordinates D hu t b) at h
  have hs := congrArg (fun p : Oscillator D => p.coeff d) h
  change (sigma D (coordinates D hu t b)).coeff d = (-(coordinates D hu t b)).coeff d at hs
  rw [coeff_sigma, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply] at hs
  apply Nat.not_even_iff_odd.mp
  intro he
  rw [he.neg_one_pow, one_mul] at hs
  have hz : (2 : ℂ) * (coordinates D hu t b).coeff d = 0 := by
    linear_combination hs
  exact (mem_support_iff.mp hd) ((mul_eq_zero.mp hz).resolve_left (by norm_num))

private def partialWord (D : LatticeData) (hu : IsUnit D.G.det)
    (w : List (Index D)) (t : ActualTensor D hu) : ActualTensor D hu :=
  match w with
  | [] => t
  | x :: tail => partialEnd D hu x (partialWord D hu tail t)

private def wordExponent (D : LatticeData) (w : List (Index D)) : Index D →₀ ℕ :=
  Multiset.toFinsupp (w : Multiset (Index D))

private theorem wordExponent_cons (D : LatticeData) (a : Index D) (w : List (Index D)) :
    wordExponent D (a :: w) = Finsupp.single a 1 + wordExponent D w := by
  change Multiset.toFinsupp (a ::ₘ (w : Multiset (Index D))) =
    Finsupp.single a 1 + Multiset.toFinsupp (w : Multiset (Index D))
  rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

private theorem wordExponent_occurrences (D : LatticeData) (d : Index D →₀ ℕ) :
    wordExponent D (occurrences D d) = d := by
  simp only [wordExponent, occurrences, Multiset.coe_toList, Finsupp.toMultiset_toFinsupp]

/-- Each derivative contributes a nonzero factor. Its target coefficient reads exactly
one original monomial, at the target exponent plus the derivative multiplicities. -/
private theorem coeff_partialWord_ne_zero
    (D : LatticeData) (hu : IsUnit D.G.det) (w : List (Index D))
    (t : ActualTensor D hu) (b : Half (groundRank D hu)) (m : Index D →₀ ℕ) :
    (coordinates D hu (partialWord D hu w t) b).coeff m ≠ 0 ↔
      (coordinates D hu t b).coeff (m + wordExponent D w) ≠ 0 := by
  induction w generalizing m with
  | nil =>
    simp only [partialWord, wordExponent, Multiset.coe_nil, Multiset.toFinsupp_zero, add_zero]
  | cons a w ih =>
    rw [partialWord, coordinates_partialEnd, coeff_pderiv]
    have hfactor : (m a : ℂ) + 1 ≠ 0 := by
      exact_mod_cast (Nat.add_one_ne_zero (m a))
    rw [mul_ne_zero_iff, and_iff_left hfactor, ih, wordExponent_cons, add_assoc]

private theorem partialWord_mem_of_even
    (D : LatticeData) (hu : IsUnit D.G.det) (S : Submodule ℂ (ActualTensor D hu))
    (hpair : ∀ a b : Index D, ∀ t ∈ S,
      partialEnd D hu a (partialEnd D hu b t) ∈ S)
    (w : List (Index D)) (hw : Even w.length) (t : ActualTensor D hu) (ht : t ∈ S) :
    partialWord D hu w t ∈ S := by
  induction w using List.twoStepInduction with
  | nil => exact ht
  | singleton a =>
    simp only [List.length_cons, List.length_nil, Nat.even_iff] at hw
    omega
  | cons_cons a b w ih _ =>
    change partialEnd D hu a (partialEnd D hu b (partialWord D hu w t)) ∈ S
    apply hpair
    apply ih
    rw [List.length_cons, List.length_cons, Nat.even_iff] at hw
    rw [Nat.even_iff]
    omega

private theorem pderiv_eq_C_of_degree_le_one (D : LatticeData)
    (p : Oscillator D) (a : Index D)
    (hdegree : ∀ m, p.coeff m ≠ 0 → m.degree ≤ 1) :
    pderiv a p = C (p.coeff (Finsupp.single a 1)) := by
  classical
  ext m
  rw [coeff_pderiv]
  by_cases hm : m = 0
  · subst m
    simp [coeff_C]
  · rw [coeff_C_of_ne_zero hm]
    have hp : p.coeff (m + Finsupp.single a 1) = 0 := by
      by_contra h
      have hd := hdegree _ h
      rw [map_add, Finsupp.degree_single] at hd
      exact hm ((Finsupp.degree_eq_zero_iff m).mp (by omega))
    rw [hp, zero_mul]

set_option maxHeartbeats 1000000 in
-- The finite-coordinate descent and the tensor identification share the same witness.
/-- A nonzero submodule of the actual odd tensor space closed under pairs of partials
and the oscillator number operators contains a nonzero one-oscillator pure tensor. -/
private theorem extract_one_oscillator_of_paired_partials
    (D : LatticeData) (hu : IsUnit D.G.det) (S : Submodule ℂ (ActualTensor D hu))
    (hS : S ≠ ⊥) (hodd : S ≤ paritySpace D hu (-1))
    (hpair : ∀ a b : Index D, ∀ t ∈ S,
      partialEnd D hu a (partialEnd D hu b t) ∈ S)
    (hnumber : ∀ a : Index D, ∀ t ∈ S,
      tensorEnd D (ActualGround D hu) (LinearMap.mulLeft ℂ (X a))
        (partialEnd D hu a t) ∈ S) :
    ∃ a : Index D, ∃ g : ActualGround D hu, g ≠ 0 ∧
      ((X a : Oscillator D) ⊗ₜ[ℂ] g) ≠ 0 ∧ ((X a : Oscillator D) ⊗ₜ[ℂ] g) ∈ S := by
  classical
  obtain ⟨t, ht, ht0⟩ := S.ne_bot_iff.mp hS
  obtain ⟨b, hb⟩ : ∃ b, coordinates D hu t b ≠ 0 := by
    by_contra! h
    apply ht0
    apply (coordinates D hu).injective
    funext b
    simpa only [map_zero, Pi.zero_apply] using h b
  let support : Finset (Index D →₀ ℕ) :=
    Finset.univ.biUnion (fun b : Half (groundRank D hu) => (coordinates D hu t b).support)
  have hsupport (m : Index D →₀ ℕ) :
      m ∈ support ↔ ∃ b, (coordinates D hu t b).coeff m ≠ 0 := by
    simp only [support, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_support_iff]
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hb
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image support Finsupp.degree
    ⟨m, (hsupport m).mpr ⟨b, hm⟩⟩
  obtain ⟨b₀, hb₀⟩ := (hsupport d).mp hd
  have hdodd := odd_of_mem_coordinate_support D hu t (hodd ht) b₀ d (mem_support_iff.mpr hb₀)
  have hd0 : d ≠ 0 := by
    intro hz
    rw [hz, map_zero, Nat.odd_iff] at hdodd
    omega
  obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr hd0
  let e := d - Finsupp.single a 1
  have hsplit : e + Finsupp.single a 1 = d :=
    Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp ha)
  have hdegree : e.degree + 1 = d.degree := by
    simpa only [map_add, Finsupp.degree_single] using congrArg Finsupp.degree hsplit
  have heven : e.degree % 2 = 0 := by
    rw [Nat.odd_iff] at hdodd
    omega
  let w := occurrences D e
  have hweven : Even w.length := by
    simpa only [w, occurrences_length, Nat.even_iff] using heven
  let u := partialWord D hu w t
  have huS : u ∈ S := partialWord_mem_of_even D hu S hpair w hweven t ht
  have hexponent : wordExponent D w = e := wordExponent_occurrences D e
  have hchosen : (coordinates D hu u b₀).coeff (Finsupp.single a 1) ≠ 0 := by
    apply (coeff_partialWord_ne_zero D hu w t b₀ _).mpr
    rw [hexponent, add_comm, hsplit]
    exact hb₀
  have hulinear (b : Half (groundRank D hu)) (m : Index D →₀ ℕ)
      (hm : (coordinates D hu u b).coeff m ≠ 0) : m.degree = 1 := by
    have horiginal := (coeff_partialWord_ne_zero D hu w t b m).mp hm
    rw [hexponent] at horiginal
    have hbound := hmax _ ((hsupport _).mpr ⟨b, horiginal⟩)
    have hparity := odd_of_mem_coordinate_support D hu t (hodd ht) b (m + e)
      (mem_support_iff.mpr horiginal)
    rw [map_add] at hbound hparity
    rw [Nat.odd_iff] at hparity
    omega
  let g : ActualGround D hu := fun b => (coordinates D hu u b).coeff (Finsupp.single a 1)
  have hg : g ≠ 0 := by
    intro hz
    exact hchosen (congrFun hz b₀)
  have hisolate :
      tensorEnd D (ActualGround D hu) (LinearMap.mulLeft ℂ (X a))
          (partialEnd D hu a u) = (X a : Oscillator D) ⊗ₜ[ℂ] g := by
    apply (coordinates D hu).injective
    funext b
    rw [coordinates_tensorEnd, LinearMap.mulLeft_apply, coordinates_partialEnd,
      pderiv_eq_C_of_degree_le_one D _ a (fun m hm => le_of_eq (hulinear b m hm)),
      coordinates_tmul]
    change (X a : Oscillator D) * C (g b) = g b • X a
    rw [mul_comm, C_mul']
  have hne : ((X a : Oscillator D) ⊗ₜ[ℂ] g) ≠ 0 := by
    intro hz
    have h := congrArg (fun v : ActualTensor D hu =>
      (coordinates D hu v b₀).coeff (Finsupp.single a 1)) hz
    change (coordinates D hu ((X a : Oscillator D) ⊗ₜ[ℂ] g) b₀).coeff
      (Finsupp.single a 1) = (coordinates D hu 0 b₀).coeff (Finsupp.single a 1) at h
    rw [coordinates_tmul, coeff_smul, coeff_X_same, smul_eq_mul, mul_one,
      map_zero, Pi.zero_apply, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h
    exact hchosen h
  exact ⟨a, g, hg, hne, hisolate ▸ hnumber a u huS⟩

set_option maxHeartbeats 1000000 in
-- The fixed-mode span and its transport through the parity subtype add elaboration work.
/-- Products of two actual tensor currents preserve the image of a native
fixed-mode-stable submodule of the negative-parity space. -/
theorem fixedParitySlice_stable_current_pair_mem
    (D : LatticeData) (hu : IsUnit D.G.det)
    (S : Submodule ℂ (paritySpace D hu (-1)))
    (hfixed : ∀ (a : FixedCarrier D) (n : ℤ), ∀ x ∈ S,
      ((fixedParitySlice D hu (-1) a)[[n]]) x ∈ S)
    (i j : Fin D.rank) (k l : ℤ) (t : ActualTensor D hu)
    (ht : t ∈ S.map (paritySpace D hu (-1)).subtype) :
    tensorCurrent D (ActualGround D hu) i k
        (tensorCurrent D (ActualGround D hu) j l t) ∈
      S.map (paritySpace D hu (-1)).subtype := by
  classical
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp ht
  let b := LatticeFiniteNegativeGeneration.neutralMode D j (-1) (vacuum D)
  have hb : theta D b = -b := by
    dsimp only [b]
    rw [theta_neutralMode, theta_vacuum]
  obtain ⟨y, hy, hyspan⟩ :=
    current_after_odd_coeff_mem_fixedParitySlice_span ⟨D, hu⟩ i b hb k (-2 * l - 3) x
  have hspan : Submodule.span ℂ (Set.range (fun index : FixedCarrier D × ℤ =>
      ((fixedParitySlice D hu (-1) index.1)[[index.2]]) x)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, n⟩, rfl⟩
    exact hfixed a n x hx
  change y.val = tensorCurrent D (ActualGround D hu) i k
    ((correctedField D hu (LatticeFiniteNegativeGeneration.neutralMode D j (-1) (vacuum D))).coeff
      (-2 * l - 3) x.val) at hy
  rw [current_coeff] at hy
  exact Submodule.mem_map.mpr ⟨y, hspan hyspan, hy⟩

/-- A tensor current after an inverse-Gram partial preserves the same image. -/
theorem fixedParitySlice_stable_current_partial_mem
    (D : LatticeData) (hu : IsUnit D.G.det)
    (S : Submodule ℂ (paritySpace D hu (-1)))
    (hfixed : ∀ (a : FixedCarrier D) (n : ℤ), ∀ x ∈ S,
      ((fixedParitySlice D hu (-1) a)[[n]]) x ∈ S)
    (i : Fin D.rank) (k : ℤ) (a : Index D) (t : ActualTensor D hu)
    (ht : t ∈ S.map (paritySpace D hu (-1)).subtype) :
    tensorCurrent D (ActualGround D hu) i k (partialEnd D hu a t) ∈
      S.map (paritySpace D hu (-1)).subtype := by
  let T := S.map (paritySpace D hu (-1)).subtype
  change _ ∈ T
  rw [partialEnd_eq_sum_currents, map_sum]
  apply T.sum_mem
  intro j _
  simp only [map_smul]
  exact T.smul_mem _ (T.smul_mem _
    (fixedParitySlice_stable_current_pair_mem D hu S hfixed i j k (a.2 : ℤ) t ht))

set_option maxHeartbeats 1000000 in
-- The native mode span is transported through the negative-parity subtype map.
/-- Each nonzero submodule stable under all native fixed-sector integer modes contains
a nonzero one-oscillator pure tensor in the original negative-parity module. -/
theorem nonzero_fixedParitySlice_stable_submodule_contains_one_oscillator
    (data : {D : LatticeData // IsUnit D.G.det})
    (S : Submodule ℂ (paritySpace data.val data.property (-1))) (hS : S ≠ ⊥)
    (hfixed : ∀ (a : FixedCarrier data.val) (n : ℤ), ∀ x ∈ S,
      ((fixedParitySlice data.val data.property (-1) a)[[n]]) x ∈ S) :
    ∃ a : Index data.val, ∃ g : ActualGround data.val data.property,
      ∃ x : paritySpace data.val data.property (-1),
        g ≠ 0 ∧ x ≠ 0 ∧ x ∈ S ∧
          x.val = (X a : Oscillator data.val) ⊗ₜ[ℂ] g := by
  classical
  rcases data with ⟨D, hu⟩
  let T := S.map (paritySpace D hu (-1)).subtype
  have hT : T ≠ ⊥ := by
    obtain ⟨x, hx, hn⟩ := S.ne_bot_iff.mp hS
    refine T.ne_bot_iff.mpr ⟨x.val, Submodule.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
    intro hz
    exact hn (Subtype.ext hz)
  have hodd : T ≤ paritySpace D hu (-1) := by
    intro t ht
    obtain ⟨x, _, rfl⟩ := Submodule.mem_map.mp ht
    exact x.property
  have hcurrentPartial := fixedParitySlice_stable_current_partial_mem D hu S hfixed
  have hpair (a b : Index D) (t : ActualTensor D hu) (ht : t ∈ T) :
      partialEnd D hu a (partialEnd D hu b t) ∈ T := by
    rw [partialEnd_eq_sum_currents D hu a (partialEnd D hu b t)]
    exact T.sum_mem (fun i _ => T.smul_mem _ (T.smul_mem _
      (hcurrentPartial i (a.2 : ℤ) b t ht)))
  have hnumber (a : Index D) (t : ActualTensor D hu) (ht : t ∈ T) :
      tensorEnd D (ActualGround D hu) (LinearMap.mulLeft ℂ (X a))
        (partialEnd D hu a t) ∈ T := by
    rcases a with ⟨i, n⟩
    rw [← LatticeHalfFock.current_negative D i n]
    exact hcurrentPartial i (-(n : ℤ) - 1) (i, n) t ht
  obtain ⟨a, g, hg, hne, hmem⟩ :=
    extract_one_oscillator_of_paired_partials D hu T hT hodd hpair hnumber
  obtain ⟨x, hx, hval⟩ := Submodule.mem_map.mp hmem
  change x.val = (X a : Oscillator D) ⊗ₜ[ℂ] g at hval
  refine ⟨a, g, x, hg, ?_, hx, hval⟩
  intro hz
  exact hne (hval.symm.trans (congrArg Subtype.val hz))

#check nonzero_fixedParitySlice_stable_submodule_contains_one_oscillator
#print axioms ActualTensorGroundIntersection.partialEnd_eq_sum_currents
#print axioms extract_one_oscillator_of_paired_partials
#print axioms nonzero_fixedParitySlice_stable_submodule_contains_one_oscillator

end
end D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockOddCyclicExtraction
