/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTLightConeBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTLightConeBPZ
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous]
   utility: none
   digest: Opposite light-cone degree selection and the scalar on native quartet ground states. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTShellBPZ
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeShellQuartet

/-! The inserted BPZ form on the original relative mass shells pairs opposite
light-cone degrees in any common normalized null frame. The quartet ground
inclusions carry the negative of the transverse orbifold form. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTLightConeBPZ

open OriginalOrbifoldCriticalMatter
open OriginalOrbifoldRelativeQuartet (Frame UCharge transverseBasis inclusion orbifoldGrade)
open OriginalOrbifoldRelativeMassShell (relativeMassShell)
open OriginalOrbifoldBRSTZeroEnergy (orbifoldBasis)
open OriginalOrbifoldBRSTShellBPZ (shellBPZ)
open OriginalOrbifoldBRSTBPZWard (betaTotal)
open OriginalOrbifoldMatterBPZ (orbifoldBPZ matterBPZ_charge)
open OriginalOrbifoldBRSTGhostBPZ
  (beta betaRel betaRel_charge_selection P P_ket bpzPhase)
open OriginalOrbifoldBRSTGhostBilinear (Brel Brel_ket_coefficient)
open LatticeGeneratingFieldLocality (Index Oscillator)
open LatticeLightConeCoordinates (g lin)
open LatticeLightConeCoordinates.NullFrame (plus minus Label)
open LatticeQuartetContraction (actualBasis actualBasis_apply sector Exponents)
open LatticeBRSTModeFiltration (degree exponentDegree variableWeight weight_plus weight_minus)
open SourceBPZ.OriginalSourcePairing (integerWick integerWick_apply retune retune_X)
open SignedOscillatorWick
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket phase lowerCount)
open BcGhostFock (c)
open BcGhostCharge (charge)
open BcGhostHermitian (Relative relativeKet relativePartner relativeEps partner eps epsList tau)
open MvPolynomial

open private completeBasis_plus completeBasis_minus polynomialEquiv_symm_X lin_single from
  D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
open private frameBasis frameBasis_apply FrameLabel slice_frame_support frameBasis_coeff from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeShellQuartet
open private c0 betaTotal_tmul ket_homogeneous from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZWard

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev frameOscillator (F : Frame) :=
  (F.coordinateEquiv (transverseBasis F)).symm

private abbrev Coordinate := Fin hyperbolicData.rank

private theorem gram_diagonal (i : Coordinate) :
    LatticeHalfFock.gramComplex hyperbolicData i i = 0 := by
  change (hyperbolicData.G i i : ℂ) = 0
  rw [hyperbolic_gram]
  simp

private theorem g_hyperbolic (u v : Coordinate → ℂ) :
    g hyperbolicData u v = u 0 * v 1 + u 1 * v 0 := by
  change (∑ i : Fin 2, ∑ j : Fin 2, u i * (hyperbolicData.G i j : ℂ) * v j) = _
  rw [hyperbolic_gram]
  simp [Fin.sum_univ_two]

private theorem null_coordinate (u : Coordinate → ℂ) (hu : g hyperbolicData u u = 0) :
    u 0 = 0 ∨ u 1 = 0 := by
  rw [g_hyperbolic] at hu
  exact mul_eq_zero.mp (by linear_combination (1 / 2 : ℂ) * hu)

private theorem frame_coordinates (F : Frame) :
    ∃ i j : Coordinate, i ≠ j ∧ F.ePlus = Pi.single i (F.ePlus i) ∧
      F.eMinus = Pi.single j (F.eMinus j) := by
  have hcross : F.ePlus 0 * F.eMinus 1 + F.ePlus 1 * F.eMinus 0 = 1 :=
    (g_hyperbolic F.ePlus F.eMinus).symm.trans F.plus_minus
  rcases null_coordinate _ F.plus_null with hp | hp
  · rcases null_coordinate _ F.minus_null with hm | hm
    · simp [hp, hm] at hcross
    · refine ⟨1, 0, by decide, ?_, ?_⟩
      · funext i; fin_cases i <;> simp [hp]
      · funext i; fin_cases i <;> simp [hm]
  · rcases null_coordinate _ F.minus_null with hm | hm
    · refine ⟨0, 1, by decide, ?_, ?_⟩
      · funext i; fin_cases i <;> simp [hp]
      · funext i; fin_cases i <;> simp [hm]
    · simp [hp, hm] at hcross

private def originalWeight (i : Coordinate) (x : Index hyperbolicData) : ℤ :=
  if x.1 = i then 1 else -1

private theorem originalWeight_opposite (i j l : Coordinate) (h : j ≠ l) (k : ℕ) :
    originalWeight i (j, k) = -originalWeight i (l, k) := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all [originalWeight]

private theorem modeSubstitution_X (i : Coordinate) (x : Index hyperbolicData) :
    IsWeightedHomogeneous (originalWeight i)
      (OriginalCurrentMetric.substitution (modeMatrix hyperbolicData) (X x))
      (-originalWeight i x) := by
  rw [OriginalCurrentMetric.substitution_X, OriginalCurrentMetric.variableImage]
  apply IsWeightedHomogeneous.sum
  intro j _
  by_cases hj : j = x.1
  · subst j
    have hdiag : modeMatrix hyperbolicData x.2 x.1 x.1 = 0 := by
      rw [modeMatrix, Matrix.smul_apply, gram_diagonal, smul_zero]
    rw [hdiag, zero_smul]
    exact isWeightedHomogeneous_zero ℂ _ _
  · rw [← originalWeight_opposite i j x.1 hj x.2]
    exact (weightedHomogeneousSubmodule ℂ _ _).smul_mem _ (isWeightedHomogeneous_X ℂ _ _)

private theorem frameOscillator_X (F : Frame) (i j : Coordinate) (hij : i ≠ j)
    (hp : F.ePlus = Pi.single i (F.ePlus i)) (hm : F.eMinus = Pi.single j (F.eMinus j))
    (x : Label 0 × ℕ) :
    IsWeightedHomogeneous (originalWeight i) (frameOscillator F (X x)) (variableWeight x) := by
  have hlin (l : Coordinate) (a : ℂ) (k : ℕ) :
      lin k (Pi.single l a) = a • (X (l,k) : Oscillator hyperbolicData) := by
    have hs : (Pi.single l a : Coordinate → ℂ) = a • Pi.single l (1 : ℂ) := by
      simpa using (Pi.single_smul' l a (1 : ℂ))
    rw [hs, map_smul, lin_single]
  have hlabel (l : Label 0) : l = plus 0 ∨ l = minus 0 := by
    rcases l with ⟨⟩ | (⟨⟩ | l)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Fin.elim0 l
  rcases x with ⟨l,k⟩
  rcases hlabel l with rfl | rfl
  · rw [frameOscillator, polynomialEquiv_symm_X, completeBasis_plus, hp, hlin, weight_plus]
    apply (weightedHomogeneousSubmodule ℂ _ _).smul_mem
    simpa [originalWeight] using
      (isWeightedHomogeneous_X ℂ (originalWeight i) (i,k))
  · rw [frameOscillator, polynomialEquiv_symm_X, completeBasis_minus, hm, hlin, weight_minus]
    apply (weightedHomogeneousSubmodule ℂ _ _).smul_mem
    simpa [originalWeight, Ne.symm hij] using
      (isWeightedHomogeneous_X ℂ (originalWeight i) (j,k))

private theorem weight_map_monomial {σ τ : Type} (A : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ)
    (w : σ → ℤ) (v : τ → ℤ) (hA : ∀ x, IsWeightedHomogeneous v (A (X x)) (w x))
    (d : σ →₀ ℕ) (a : ℂ) :
    IsWeightedHomogeneous v (A (monomial d a)) (Finsupp.weight w d) := by
  rw [monomial_eq, map_mul, show A (C a) = C a from A.commutes a]
  simp only [Finsupp.prod, map_prod, map_pow]
  apply IsWeightedHomogeneous.C_mul
  simpa only [Finsupp.weight_apply, Finsupp.sum] using
    (IsWeightedHomogeneous.prod d.support (fun x => A (X x) ^ d x)
      (fun x => d x • w x) (fun x _ => (hA x).pow (d x)))

private theorem weight_map {σ τ : Type} (A : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ)
    (w : σ → ℤ) (v : τ → ℤ) (hA : ∀ x, IsWeightedHomogeneous v (A (X x)) (w x))
    (p : MvPolynomial σ ℂ) (n : ℤ) (hp : IsWeightedHomogeneous w p n) :
    IsWeightedHomogeneous v (A p) n := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [← hp (mem_support_iff.mp hd)]
  exact weight_map_monomial A w v hA d (p.coeff d)

private theorem weight_neg {σ : Type} (w : σ → ℤ) (d : σ →₀ ℕ) :
    Finsupp.weight (fun x => -(w x)) d = -(Finsupp.weight w d) := by
  simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_neg_distrib]

private theorem frame_weight (m : Exponents 0) :
    Finsupp.weight variableWeight m = exponentDegree m := by
  simp [Finsupp.weight_apply, exponentDegree]

private theorem factorial_opposite_weight (i : Coordinate)
    (p q : Oscillator hyperbolicData) (n m : ℤ)
    (hp : IsWeightedHomogeneous (originalWeight i) p (-n))
    (hq : IsWeightedHomogeneous (originalWeight i) q m) (h : n + m ≠ 0) :
    FactorialBilinear.form (Index hyperbolicData) p q = 0 := by
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  rw [FactorialBilinear.symmetric, FactorialBilinear.monomial_left,
    hp.coeff_eq_zero d (by rw [hq (mem_support_iff.mp hd)]; omega)]
  simp

/-- The actual integer-mode oscillator form pairs opposite null-frame degrees. -/
theorem integerWick_frame_degree (F : Frame) (d e : Exponents 0)
    (h : exponentDegree d + exponentDegree e ≠ 0) :
    integerWick hyperbolicData (frameOscillator F (monomial d 1))
      (frameOscillator F (monomial e 1)) = 0 := by
  obtain ⟨i, j, hij, hp, hm⟩ := frame_coordinates F
  have hframe (m : Exponents 0) :
      IsWeightedHomogeneous (originalWeight i) (frameOscillator F (monomial m 1))
        (exponentDegree m) := by
    rw [← frame_weight]
    exact weight_map_monomial (frameOscillator F).toAlgHom _ _
      (frameOscillator_X F i j hij hp hm) m 1
  have hretune (x : Index hyperbolicData) :
      IsWeightedHomogeneous (originalWeight i) (retune hyperbolicData (X x))
        (originalWeight i x) := by
    rcases x with ⟨l,k⟩
    rw [retune_X]
    exact (weightedHomogeneousSubmodule ℂ _ _).smul_mem _ (isWeightedHomogeneous_X ℂ _ _)
  have hd := weight_map (retune hyperbolicData).toAlgHom _ _ hretune _ _ (hframe d)
  have hneg : IsWeightedHomogeneous (fun x => -originalWeight i x)
      (retune hyperbolicData (frameOscillator F (monomial d 1))) (-exponentDegree d) := by
    intro z hz
    rw [weight_neg, hd hz]
  have hs := weight_map (OriginalCurrentMetric.substitution (modeMatrix hyperbolicData))
    _ _ (modeSubstitution_X i) _ _ hneg
  rw [integerWick_apply]
  exact factorial_opposite_weight i _ _ _ _ hs (hframe e) h

private theorem inserted_tmul (u v : Matter) (s t : Fock) :
    betaTotal (u ⊗ₜ[ℂ] s) (c0 (v ⊗ₜ[ℂ] t)) =
      OriginalOrbifoldMatterBPZ.matterBPZ u v * beta s (c 0 t) := by
  change betaTotal (u ⊗ₜ[ℂ] s) (v ⊗ₜ[ℂ] c 0 t) = _
  exact betaTotal_tmul u v s (c 0 t)

private theorem frameBasis_inserted_degree (F : Frame) (i j : FrameLabel)
    (hi : 3 ∉ i.2.2) (hj : 3 ∉ j.2.2) (h : degree i.2 + degree j.2 ≠ 0) :
    betaTotal (frameBasis F i) (c0 (frameBasis F j)) = 0 := by
  rcases i with ⟨u, ⟨a,d⟩, S⟩
  rcases j with ⟨v, ⟨b,e⟩, T⟩
  rw [frameBasis_apply, frameBasis_apply]
  simp only [actualBasis_apply, sector, TensorProduct.assoc_symm_tmul, inserted_tmul,
    matterBPZ_charge]
  by_cases hST : charge S + charge T = 2
  · have hde : exponentDegree d + exponentDegree e ≠ 0 := by
      change exponentDegree d + charge S - 1 + (exponentDegree e + charge T - 1) ≠ 0 at h
      omega
    have hw := integerWick_frame_degree F d e hde
    change (if b = -a then orbifoldBPZ (orbifoldBasis u) (orbifoldBasis v) *
      integerWick hyperbolicData (frameOscillator F (monomial d 1))
        (frameOscillator F (monomial e 1)) else 0) * _ = 0
    simp [hw]
  · have hg : beta (ket S) (c 0 (ket T)) = 0 :=
      betaRel_charge_selection (x := relativeKet S hi) (y := relativeKet T hj)
        (ket_homogeneous S) (ket_homogeneous T) hST
    rw [hg, mul_zero]

/-- Homogeneity in the light-cone degree of the native tensor basis. -/
def Homogeneous (F : Frame) (n : ℤ) (x : State) : Prop :=
  ∀ i : FrameLabel, (frameBasis F).repr x i ≠ 0 → degree i.2 = n

/-- On opposite relative mass shells, native BPZ is zero unless the two
light-cone degrees sum to zero. The frame on both shells is the same. -/
theorem shellBPZ_degree_selection (F : Frame) (a : UCharge)
    (x : relativeMassShell a) (y : relativeMassShell (-a)) (n m : ℤ)
    (hx : Homogeneous F n (x : State)) (hy : Homogeneous F m (y : State))
    (h : n + m ≠ 0) : shellBPZ a x y = 0 := by
  classical
  change betaTotal (x : State) (c0 (y : State)) = 0
  rw [← (frameBasis F).linearCombination_repr (x : State),
    ← (frameBasis F).linearCombination_repr (y : State)]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hxi := Finsupp.mem_support_iff.mp hi
  have hyj := Finsupp.mem_support_iff.mp hj
  have hdeg : degree i.2 + degree j.2 ≠ 0 := by rw [hx i hxi, hy j hyj]; exact h
  have hrel (p : UCharge) (z : relativeMassShell p) (k : FrameLabel)
      (hk : (frameBasis F).repr (z : State) k ≠ 0) : 3 ∉ k.2.2 := by
    rcases k with ⟨u, l⟩
    rw [frameBasis_coeff] at hk
    exact (slice_frame_support F p z z.property u l hk).2.1
  rw [frameBasis_inserted_degree F i j (hrel a x i hxi) (hrel (-a) y j hyj) hdeg]
  simp

private def groundGhost : Relative := relativeKet {1} (by decide)

/-- The phase on the first ghost input gives the native ground scalar `-1`. -/
theorem beta_ground_ghost : beta (ket {1}) (c 0 (ket {1})) = -1 := by
  have hcharge : charge ({1} : Finset ℕ) = 1 := by decide
  have hP : P (ket {1}) = -ket {1} := by
    rw [P_ket, hcharge]
    norm_num [bpzPhase]
  have hpartner : partner ({1} : Finset ℕ) = {1,3} := by decide
  have hE : partner (∅ : Finset ℕ) = {1,3,5} := by decide
  have hp3 : lowerCount 3 ({1,3} : Finset ℕ) = 1 := by decide
  have hp5 : lowerCount 5 ({1,3,5} : Finset ℕ) = 2 := by decide
  have heps : relativeEps ({1} : Finset ℕ) = 1 := by
    norm_num [relativeEps, eps, epsList, tau, hE, hpartner, phase, hp3, hp5]
  have hB : Brel groundGhost groundGhost = 1 := by
    change Brel (relativeKet {1} (by decide)) groundGhost = 1
    rw [Brel_ket_coefficient, heps]
    have hrelative : relativePartner ({1} : Finset ℕ) = {1} := by decide
    rw [hrelative]
    simp [groundGhost, relativeKet, ket]
  have hPr : OriginalOrbifoldBRSTGhostBPZ.PRel groundGhost = -groundGhost :=
    Subtype.ext hP
  change betaRel groundGhost groundGhost = -1
  change Brel (OriginalOrbifoldBRSTGhostBPZ.PRel groundGhost) groundGhost = -1
  rw [hPr, map_neg, LinearMap.neg_apply, hB]

private theorem integerWick_ground :
    integerWick hyperbolicData 1 1 = 1 := by
  rw [integerWick_apply, show retune hyperbolicData 1 = 1 from map_one _]
  rw [← MvPolynomial.C_1, wick_constant_left]
  simp

/-- The native ground inclusions on opposite shells pair by minus the orbifold form. -/
theorem shellBPZ_inclusion (a : UCharge)
    (ha : LatticePositiveEnergy.chargeEnergy hyperbolicData a ≤ 1)
    (hb : LatticePositiveEnergy.chargeEnergy hyperbolicData (-a) ≤ 1)
    (u : orbifoldGrade (LatticeRelativeMassShell.massShellCutoff hyperbolicData a))
    (v : orbifoldGrade (LatticeRelativeMassShell.massShellCutoff hyperbolicData (-a))) :
    shellBPZ a (inclusion a ha u) (inclusion (-a) hb v) =
      -orbifoldBPZ (u : Orbifold) (v : Orbifold) := by
  change betaTotal
    (((u : Orbifold) ⊗ₜ[ℂ] Finsupp.single a (1 : Oscillator hyperbolicData)) ⊗ₜ[ℂ] ket {1})
    (c0 (((v : Orbifold) ⊗ₜ[ℂ] Finsupp.single (-a) (1 : Oscillator hyperbolicData)) ⊗ₜ[ℂ]
      ket {1})) = _
  rw [inserted_tmul, matterBPZ_charge, ite_eq_left rfl, integerWick_ground, mul_one,
    beta_ground_ghost]
  ring

#print axioms integerWick_frame_degree
#print axioms shellBPZ_degree_selection
#print axioms beta_ground_ghost
#print axioms shellBPZ_inclusion

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTLightConeBPZ
