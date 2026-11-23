/- GID: D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockEvenFixedModeIrreducibility
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/LatticeHalfFockEvenFixedModeIrreducibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native fixed-sector modes act irreducibly on the actual even half-Fock module. -/

/- proof_shape: fixedParitySlice_even_irreducible: content
admission_basis: escape-witness
escape_witness: Paired partials read a maximal-total-degree coefficient as a vacuum
tensor in the stable submodule. The literal fixed charge pair then gives the selected
irreducible ground action, and paired creations recover every even oscillator monomial.
Literature status: classical twisted lattice orbifold theory, no novelty claim.
-/
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockOddFixedModeIrreducibility

/-! Irreducibility of the actual positive-parity twisted module under fixed-sector modes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockEvenFixedModeIrreducibility

open LatticeGeneratingFieldLocality
open LatticeAllStateField (occurrences occurrences_product vacuum)
open LatticeFiniteNegativeGeneration (neutralMode)
open LatticeHalfFock (tensorCurrent tensorEnd)
open LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockChargedMonodromy (ground_neg norm_neg norm_even)
open LatticeHalfFockCorrectedField (correctedField corrected_singleton_coeff_charged)
open LatticeHalfFockParityField (fixedParitySlice paritySpace)
open LatticeHalfFockParityT (actualParity)
open LatticeHalfFockOddCyclicExtraction (occurrences_length)
open ActualFieldIrreducible (groundSubrepresentation)
open ActualTensorGroundIntersection (coordinates coordinates_tmul coordinates_tensorEnd
  partialEnd partialEnd_eq_sum_currents)
open LatticeInvolution (FixedCarrier mem_fixedSpace sigma sigmaLinear theta thetaLinear
  theta_neutralMode theta_single theta_vacuum)
open LatticeTwistedGroundRealization (Half actual_twisted_ground_representation)
open MvPolynomial
open scoped BigOperators TensorProduct VertexOperator

open private odd_coeff_descent from
  D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockFixedCyclicReduction
open private coeff_sigma partialWord wordExponent wordExponent_occurrences
  coeff_partialWord_ne_zero partialWord_mem_of_even current_coeff from
  D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockOddCyclicExtraction
open private halfCreationCoeff_zero create create_eq_current create_tmul from
  D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockOddFixedModeIrreducibility

noncomputable section

/-- The signed current descent uses fixed iterates on an input in any target eigenspace. -/
private theorem current_pair_mem_of_fixed_stable
    (D : LatticeData) (hu : IsUnit D.G.det) (s : ℂ)
    (S : Submodule ℂ (paritySpace D hu s))
    (stable : ∀ (a : FixedCarrier D) (n : ℤ), ∀ x ∈ S,
      ((fixedParitySlice D hu s a)[[n]]) x ∈ S)
    (i j : Fin D.rank) (k l : ℤ) (t : ActualTensor D hu)
    (ht : t ∈ S.map (paritySpace D hu s).subtype) :
    tensorCurrent D (ActualGround D hu) i k (tensorCurrent D (ActualGround D hu) j l t) ∈
      S.map (paritySpace D hu s).subtype := by
  classical
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp ht
  let b := neutralMode D j (-1) (vacuum D)
  have hb : theta D b = -b := by
    dsimp only [b]
    rw [theta_neutralMode, theta_vacuum]
  have hiterates (r n : ℤ) :
      (correctedField D hu (neutralMode D i r b)).coeff (-2 * n - 2) x.val ∈
        S.map (paritySpace D hu s).subtype := by
    let a : FixedCarrier D := ⟨neutralMode D i r b, by
      rw [mem_fixedSpace, theta_neutralMode, hb, map_neg, neg_neg]⟩
    refine Submodule.mem_map.mpr ⟨((fixedParitySlice D hu s a)[[n]]) x, stable a n x hx, ?_⟩
    change (correctedField D hu a.val).coeff (2 * (-n - 1)) x.val = _
    rw [show 2 * (-n - 1) = -2 * n - 2 by omega]
  have hpair := odd_coeff_descent D hu i b x.val _ hiterates k l
  change tensorCurrent D (ActualGround D hu) i k
    ((correctedField D hu (neutralMode D j (-1) (vacuum D))).coeff (-2 * l - 3) x.val) ∈ _ at hpair
  rw [current_coeff] at hpair
  exact hpair

private theorem even_of_mem_coordinate_support
    (D : LatticeData) (hu : IsUnit D.G.det) (t : ActualTensor D hu)
    (ht : t ∈ paritySpace D hu 1) (b : Half (groundRank D hu))
    (d : Index D →₀ ℕ) (hd : d ∈ (coordinates D hu t b).support) : Even d.degree := by
  have hparity : actualParity D hu t = t := by
    simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero, one_smul] using ht
  have h := congrArg (fun v => coordinates D hu v b) hparity
  change coordinates D hu (tensorEnd D (ActualGround D hu) (sigmaLinear D) t) b =
    coordinates D hu t b at h
  rw [coordinates_tensorEnd] at h
  change sigma D (coordinates D hu t b) = coordinates D hu t b at h
  have hs := congrArg (fun p : Oscillator D => p.coeff d) h
  change (sigma D (coordinates D hu t b)).coeff d = (coordinates D hu t b).coeff d at hs
  rw [coeff_sigma] at hs
  by_contra he
  have hodd := Nat.not_even_iff_odd.mp he
  rw [hodd.neg_one_pow, neg_one_mul] at hs
  have hz : (2 : ℂ) * (coordinates D hu t b).coeff d = 0 := by
    linear_combination hs.symm
  exact (mem_support_iff.mp hd) ((mul_eq_zero.mp hz).resolve_left (by norm_num))

set_option maxHeartbeats 1000000 in
-- Coefficient extraction elaborates polynomials indexed by the lattice and ground module.
/-- Differentiate a maximal-total-degree monomial to a nonzero constant coordinate. -/
private theorem extract_vacuum_of_paired_partials
    (D : LatticeData) (hu : IsUnit D.G.det) (T : Submodule ℂ (ActualTensor D hu))
    (hT : T ≠ ⊥) (heven : T ≤ paritySpace D hu 1)
    (hpair : ∀ a b : Index D, ∀ t ∈ T, partialEnd D hu a (partialEnd D hu b t) ∈ T) :
    ∃ g : ActualGround D hu, g ≠ 0 ∧ ((1 : Oscillator D) ⊗ₜ[ℂ] g) ∈ T := by
  classical
  obtain ⟨t, ht, ht0⟩ := T.ne_bot_iff.mp hT
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
  let w := occurrences D d
  have hweven : Even w.length := by
    simpa only [w, occurrences_length] using
      even_of_mem_coordinate_support D hu t (heven ht) b₀ d (mem_support_iff.mpr hb₀)
  let u := partialWord D hu w t
  have huT : u ∈ T := partialWord_mem_of_even D hu T hpair w hweven t ht
  have hexponent : wordExponent D w = d := wordExponent_occurrences D d
  have hchosen : (coordinates D hu u b₀).coeff 0 ≠ 0 := by
    apply (coeff_partialWord_ne_zero D hu w t b₀ 0).mpr
    simpa only [hexponent, zero_add] using hb₀
  have honly (b : Half (groundRank D hu)) (m : Index D →₀ ℕ)
      (hm : (coordinates D hu u b).coeff m ≠ 0) : m = 0 := by
    have horiginal := (coeff_partialWord_ne_zero D hu w t b m).mp hm
    rw [hexponent] at horiginal
    have hbound := hmax _ ((hsupport _).mpr ⟨b, horiginal⟩)
    rw [map_add] at hbound
    exact (Finsupp.degree_eq_zero_iff m).mp (by omega)
  let g : ActualGround D hu := fun b => (coordinates D hu u b).coeff 0
  have hg : g ≠ 0 := by
    intro hz
    exact hchosen (congrFun hz b₀)
  have hconstant (b : Half (groundRank D hu)) : coordinates D hu u b = C (g b) := by
    apply MvPolynomial.ext
    intro m
    by_cases hm : m = 0
    · subst m
      exact (coeff_zero_C (g b)).symm
    · rw [coeff_C_of_ne_zero hm]
      by_contra h
      exact hm (honly b m h)
  have hisolate : u = (1 : Oscillator D) ⊗ₜ[ℂ] g := by
    apply (coordinates D hu).injective
    funext b
    rw [coordinates_tmul, hconstant b, smul_eq_C_mul, mul_one]
  exact ⟨g, hg, hisolate ▸ huT⟩

/-- At the leading charged exponent the two literal charge summands induce the same
ground action on the vacuum tensor, with their native normalization. -/
private theorem correctedField_charge_pair_vacuum
    (D : LatticeData) (hu : IsUnit D.G.det) (charge : Charge D) (g : ActualGround D hu) :
    (correctedField D hu (Finsupp.single charge (1 : Oscillator D) +
      Finsupp.single (-charge) 1)).coeff (-chargeNorm D charge)
        ((1 : Oscillator D) ⊗ₜ[ℂ] g) =
      (2 * chargeScalar D charge) • ((1 : Oscillator D) ⊗ₜ[ℂ] groundAction D hu charge g) := by
  have hpos := charged_vacuum_coefficient D hu charge (-chargeNorm D charge) g
  have hneg := charged_vacuum_coefficient D hu (-charge) (-chargeNorm D (-charge)) g
  rw [neg_add_cancel, halfCreationCoeff_zero] at hpos hneg
  have hscalar_neg : chargeScalar D (-charge) = chargeScalar D charge := by
    simp only [chargeScalar, norm_neg]
  rw [norm_neg, hscalar_neg, ground_neg] at hneg
  simp only [map_add, Pi.add_apply, LinearMap.add_apply, corrected_singleton_coeff_charged,
    chargedField, HVertexOperator.coeff_of_coeff]
  rw [hpos, hneg, two_mul, add_smul]

/-- Pair the letters of the occurrence list down to the vacuum. -/
private theorem even_monomial_tmul_mem (D : LatticeData) (hu : IsUnit D.G.det)
    (T : Submodule ℂ (ActualTensor D hu))
    (hpair : ∀ a b : Index D, ∀ t ∈ T, create D hu a (create D hu b t) ∈ T)
    (g : ActualGround D hu) (hvacuum : ((1 : Oscillator D) ⊗ₜ[ℂ] g) ∈ T)
    (d : Index D →₀ ℕ) (hd : Even d.degree) :
    ((monomial d 1 : Oscillator D) ⊗ₜ[ℂ] g) ∈ T := by
  have hword (w : List (Index D)) (hw : Even w.length) :
      ((w.map (fun a => (X a : Oscillator D))).prod ⊗ₜ[ℂ] g) ∈ T := by
    induction w using List.twoStepInduction with
    | nil => simpa only [List.map_nil, List.prod_nil] using hvacuum
    | singleton a =>
      simp only [List.length_cons, List.length_nil, Nat.even_iff] at hw
      omega
    | cons_cons a b w ih _ =>
      have hw' : Even w.length := by
        rw [List.length_cons, List.length_cons, Nat.even_iff] at hw
        rw [Nat.even_iff]
        omega
      simpa only [create_tmul, List.map_cons, List.prod_cons] using hpair a b _ (ih hw')
  rw [← occurrences_product D d]
  exact hword _ (by rwa [occurrences_length])

set_option maxHeartbeats 1000000 in
-- Ground irreducibility and tensor reconstruction use the dependent ground representation.
/-- Native fixed-sector integer modes act irreducibly on the actual positive-parity
twisted module. -/
theorem fixedParitySlice_even_irreducible (D : LatticeData) (hu : IsUnit D.G.det)
    (S : Submodule ℂ (paritySpace D hu 1))
    (stable : ∀ (a : FixedCarrier D) (n : ℤ), ∀ x ∈ S,
      ((fixedParitySlice D hu 1 a)[[n]]) x ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  classical
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  let T := S.map (paritySpace D hu 1).subtype
  have hT : T ≠ ⊥ := by
    obtain ⟨x, hx, hn⟩ := S.ne_bot_iff.mp hS
    refine T.ne_bot_iff.mpr ⟨x.val, Submodule.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
    intro hz
    exact hn (Subtype.ext hz)
  have heven : T ≤ paritySpace D hu 1 := by
    intro t ht
    obtain ⟨x, _, rfl⟩ := Submodule.mem_map.mp ht
    exact x.property
  have hcurrents := current_pair_mem_of_fixed_stable D hu 1 S stable
  have hcurrentPartial (i : Fin D.rank) (k : ℤ) (a : Index D)
      (t : ActualTensor D hu) (ht : t ∈ T) :
      tensorCurrent D (ActualGround D hu) i k (partialEnd D hu a t) ∈ T := by
    rw [partialEnd_eq_sum_currents, map_sum]
    apply T.sum_mem
    intro j _
    simp only [map_smul]
    exact T.smul_mem _ (T.smul_mem _ (hcurrents i j k (a.2 : ℤ) t ht))
  have hpartials (a b : Index D) (t : ActualTensor D hu) (ht : t ∈ T) :
      partialEnd D hu a (partialEnd D hu b t) ∈ T := by
    rw [partialEnd_eq_sum_currents D hu a (partialEnd D hu b t)]
    exact T.sum_mem (fun i _ => T.smul_mem _ (T.smul_mem _
      (hcurrentPartial i (a.2 : ℤ) b t ht)))
  obtain ⟨g₀, hg₀, hseed⟩ := extract_vacuum_of_paired_partials D hu T hT heven hpartials
  let U := T.comap (TensorProduct.mk ℂ (Oscillator D) (ActualGround D hu) 1)
  have hground (charge : Charge D) (g : ActualGround D hu) (hg : g ∈ U) :
      groundAction D hu charge g ∈ U := by
    change ((1 : Oscillator D) ⊗ₜ[ℂ] g) ∈ T at hg
    obtain ⟨x, hx, hval⟩ := Submodule.mem_map.mp hg
    let a : FixedCarrier D := ⟨Finsupp.single charge 1 + Finsupp.single (-charge) 1, by
      rw [mem_fixedSpace, map_add]
      change thetaLinear D (Finsupp.single charge (1 : Oscillator D)) +
        thetaLinear D (Finsupp.single (-charge) 1) = _
      simpa only [theta_single, map_one, neg_neg] using
        (add_comm (Finsupp.single (-charge) (1 : Oscillator D)) (Finsupp.single charge 1))⟩
    obtain ⟨halfNorm, hhalfNorm⟩ := norm_even D charge
    let n : ℤ := halfNorm - 1
    have exponent : 2 * (-n - 1) = -chargeNorm D charge := by
      dsimp only [n]
      omega
    let y := ((fixedParitySlice D hu 1 a)[[n]]) x
    have hread : y.val = (2 * chargeScalar D charge) •
        ((1 : Oscillator D) ⊗ₜ[ℂ] groundAction D hu charge g) := by
      change (correctedField D hu a.val).coeff (2 * (-n - 1)) x.val = _
      change x.val = (1 : Oscillator D) ⊗ₜ[ℂ] g at hval
      rw [exponent, hval]
      exact correctedField_charge_pair_vacuum D hu charge g
    have hscaled : (2 * chargeScalar D charge) •
        ((1 : Oscillator D) ⊗ₜ[ℂ] groundAction D hu charge g) ∈ T :=
      Submodule.mem_map.mpr ⟨y, stable a n x hx, hread⟩
    have hcharge : chargeScalar D charge ≠ 0 := zpow_ne_zero _ (by norm_num)
    have hscalar : (2 : ℂ) * chargeScalar D charge ≠ 0 := mul_ne_zero (by norm_num) hcharge
    change ((1 : Oscillator D) ⊗ₜ[ℂ] groundAction D hu charge g) ∈ T
    simpa only [smul_smul, inv_mul_cancel₀ hscalar, one_smul] using
      T.smul_mem (((2 : ℂ) * chargeScalar D charge)⁻¹) hscaled
  have hU : U = ⊤ := by
    let V := groundSubrepresentation D hu U hground
    let : (groundRepresentation D hu).IsIrreducible :=
      (Classical.choose_spec
        (Classical.choose_spec (actual_twisted_ground_representation D hu))).2.1
    rcases eq_bot_or_eq_top V with bottom | top
    · have member : g₀ ∈ V := hseed
      rw [bottom] at member
      exact (hg₀ member).elim
    · exact congrArg (fun W : Subrepresentation (groundRepresentation D hu) => W.toSubmodule) top
  have hvacuum (g : ActualGround D hu) : ((1 : Oscillator D) ⊗ₜ[ℂ] g) ∈ T := by
    change g ∈ U
    rw [hU]
    exact Submodule.mem_top
  have hcreations (a b : Index D) (t : ActualTensor D hu) (ht : t ∈ T) :
      create D hu a (create D hu b t) ∈ T := by
    rw [create_eq_current D hu a, create_eq_current D hu b]
    exact hcurrents a.1 b.1 (-(a.2 : ℤ) - 1) (-(b.2 : ℤ) - 1) t ht
  apply top_unique
  intro x _
  let t : ActualTensor D hu := x.val
  have ht : t ∈ paritySpace D hu 1 := x.property
  have hdecompose :
      t = ∑ b : Half (groundRank D hu),
        coordinates D hu t b ⊗ₜ[ℂ] (Pi.single b (1 : ℂ) : ActualGround D hu) := by
    let q := coordinates D hu t
    calc
      t = (coordinates D hu).symm q := ((coordinates D hu).symm_apply_apply t).symm
      _ = (coordinates D hu).symm (∑ b, Pi.single b (q b)) :=
        congrArg (fun f => (coordinates D hu).symm f)
          (LinearMap.sum_single_apply (fun _ : Half (groundRank D hu) => Oscillator D) q).symm
      _ = _ := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun b _ =>
          TensorProduct.piScalarRight_symm_single ℂ ℂ (Oscillator D)
            (Half (groundRank D hu)) (q b) b
  have hm : t ∈ T := by
    rw [hdecompose]
    apply T.sum_mem
    intro b _
    rw [MvPolynomial.as_sum (coordinates D hu t b), TensorProduct.sum_tmul]
    apply T.sum_mem
    intro d hd
    let g : ActualGround D hu := Pi.single b 1
    have hterm := even_monomial_tmul_mem D hu T hcreations g (hvacuum g) d
      (even_of_mem_coordinate_support D hu t ht b d hd)
    simpa only [g, TensorProduct.smul_tmul', smul_monomial, smul_eq_mul, mul_one] using
      T.smul_mem ((coordinates D hu t b).coeff d) hterm
  obtain ⟨y, hy, hyval⟩ := Submodule.mem_map.mp hm
  have hyx : y = x := Subtype.ext hyval
  exact hyx ▸ hy

end
end D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockEvenFixedModeIrreducibility
