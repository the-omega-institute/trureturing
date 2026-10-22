/- GID: D5/S3/VertexAlgebra/LatticeHalfFockLeftCurrentTransport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockLeftCurrentTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual three-field clearing on arbitrary half-Fock tensor inputs. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
import D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality
import D5.S3.VertexAlgebra.StateFieldResidueReconstruction
import D5.S3.VertexAlgebra.SupportedWordRationalCollision

/-! Pairwise physical locality supplies a common six-order coefficient array.
The original state carrier and the acted-on tensor carrier remain distinct.
Classical local-field calculus: Matsuo--Nagatomo, On Axioms for a Vertex Algebra
and Locality of Quantum Fields. Twisted lattice setting: Bakalov--Kac,
math/0402315. Hahn composition is due to Scott Carnahan, Apache 2.0. -/

set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockCorrectedField
open LatticeHalfFockPhysicalRescaling LatticeHalfFockCurrentBorcherds
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open FieldNormalProductLocality UniformGradedLocalCorrelator
open SupportedFieldWords.OrderedWords
open SupportedFieldWords.ActualFieldWordAdapter
open SupportedWordRationalCollision.ActualPolynomialBridge
open CollisionRationalExpansions.OrderedRationalExpansion
open scoped BigOperators VertexOperator
noncomputable section

/-- An actual original-source slice; the signed lift is unreduced. -/
def targetSlice (D : LatticeData) (hu : IsUnit D.G.det) (a : Carrier D) (s : ℤ) :
    VertexOperator ℂ (ActualTensor D hu) := physicalSlice D hu (correctedField D hu a) s

/-- The physical current with the exact half-frequency normalization. -/
def targetCurrent (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) :
    VertexOperator ℂ (ActualTensor D hu) := physicalJet D hu (i, 0)

private theorem target_current_mode (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (n : ℤ) :
    (targetCurrent D hu i)[[n]] = LatticeHalfFock.tensorCurrent D (ActualGround D hu) i n := by
  simp [targetCurrent, physicalJet_mode, jetCurrent, jetScalar]

private theorem current_slice_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (b : Carrier D) (delta : ℤ) :
    (deltaEnd ^ (vectorFrequencyBound D b + 1))
      (FieldNormalProductLocality.commutator (targetCurrent D hu i) (targetSlice D hu b delta)) = 0 := by
  funext p q
  apply LinearMap.ext
  intro x
  let cutoff := vectorFrequencyBound D b + 1
  have zero : (∑ᶠ j : ℕ, currentLeftTerm D hu i b delta p q cutoff x j) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    have vanishes := neutralMode_vanish D i b ((cutoff : ℤ) + j) (by dsimp [cutoff]; omega)
    simp [currentLeftTerm, vanishes]
  have law := (current_borcherds D hu i b delta p q cutoff x).2.2.2
  have ordered := D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds.positive_ordered_commutators D hu i b delta p q cutoff x
  rw [← law, zero] at ordered
  rw [FieldDeltaBinomial.delta_binomial]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, FieldNormalProductLocality.commutator,
    target_current_mode, targetSlice, physicalSlice_mode,
    LinearMap.sub_apply, Module.End.mul_apply, Pi.zero_apply, LinearMap.zero_apply]
  exact ordered.symm

private theorem source_slice_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) : ∃ order : ℕ, ∀ gamma delta : ℤ,
      (deltaEnd ^ order) (FieldNormalProductLocality.commutator (targetSlice D hu a gamma)
        (targetSlice D hu b delta)) = 0 := by
  obtain ⟨order, law⟩ :=
    LatticeHalfFockAllStatePhysicalLocality.correctedField_physical_locality D hu a b
  refine ⟨order, ?_⟩
  intro gamma delta
  funext left right
  apply LinearMap.ext
  intro x
  rw [FieldDeltaBinomial.delta_binomial]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, FieldNormalProductLocality.commutator,
    targetSlice, physicalSlice_mode, LinearMap.sub_apply, Module.End.mul_apply,
    Pi.zero_apply, LinearMap.zero_apply]
  convert law (-2 * left - gamma - 2) (-2 * right - delta - 2) x using 1
  apply Finset.sum_congr rfl
  intro offset member
  have bound : offset ≤ order := Nat.le_of_lt_succ (Finset.mem_range.mp member)
  rw [Int.natCast_sub bound]
  rw [show -2 * (left + (order : ℤ) - (offset : ℤ)) - gamma - 2 =
      -2 * left - gamma - 2 - 2 * ((order : ℤ) - offset) by omega,
    show -2 * (right + (offset : ℤ)) - delta - 2 =
      -2 * right - delta - 2 - 2 * (offset : ℤ) by omega]

section Residues
universe v
variable {M : Type v} [AddCommGroup M] [Module ℂ M]
open StateFieldResidueReconstruction

/-- Multiplication by the Laurent monomial z^(-amount). -/
def modeShift (amount : ℤ) (A : VertexOperator ℂ M) : VertexOperator ℂ M :=
  VertexOperator.of_coeff (fun e => A.coeff (e + amount)) (by
    intro x
    refine ⟨((HahnModule.of ℂ).symm (A x)).order - amount, ?_⟩
    intro e he
    by_contra h
    apply he
    exact VertexOperator.coeff_eq_zero_of_lt_order A (e + amount) x (by omega))

private theorem modeShift_mode (amount : ℤ) (A : VertexOperator ℂ M) (n : ℤ) :
    (modeShift amount A)[[n]] = A[[n - amount]] := by
  rw [modeShift, VertexOperator.ncoeff_of_coeff, VertexOperator.coeff_eq_ncoeff]
  rw [show -(-n - 1 + amount) - 1 = n - amount by omega]

/-- The ordinary complete residue, including both ordered halves. -/
def ordinaryResidue (r : ℤ) (A B : VertexOperator ℂ M) : VertexOperator ℂ M :=
  (fieldResidue r A B).operator

/-- The finite fractional product. Its second lift is its output label. -/
def qField (s r : ℤ) (K : ℕ) (A B : VertexOperator ℂ M) : VertexOperator ℂ M :=
  ∑ ell ∈ Finset.range ((K : ℤ) - r).toNat,
    Ring.choose (-(s : ℂ) / 2) ell • modeShift ell (ordinaryResidue (r + ell) A B)

theorem qField_mode (s r : ℤ) (K : ℕ) (A B : VertexOperator ℂ M)
    (n : ℤ) (x : M) :
    ((qField s r K A B)[[n]]) x =
      ∑ ell ∈ Finset.range ((K : ℤ) - r).toNat,
        Ring.choose (-(s : ℂ) / 2) ell •
          fieldResidueCoefficient (r + ell) (n - ell) A B x := by
  simp only [qField, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply, modeShift_mode, ordinaryResidue,
    (fieldResidue _ A B).coefficient]

theorem ordinaryResidue_tail (A B : VertexOperator ℂ M) (K : ℕ)
    (locality : (deltaEnd ^ K) (FieldNormalProductLocality.commutator A B) = 0)
    (r : ℤ) (high : (K : ℤ) ≤ r) : ordinaryResidue r A B = 0 := by
  obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ r by omega)
  have bound : K ≤ degree := by omega
  have killed : (deltaEnd ^ degree) (FieldNormalProductLocality.commutator A B) = 0 := by
    rw [show degree = (degree - K) + K by omega, pow_add, Module.End.mul_apply,
      locality, map_zero]
  apply HVertexOperator.coeff_inj
  funext e
  apply LinearMap.ext
  intro x
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  change ((fieldResidue (degree : ℤ) A B).operator[[-e - 1]]) x = _
  rw [(fieldResidue (degree : ℤ) A B).nonnegative_modes degree rfl, killed]
  rfl

private theorem qField_pad (s r : ℤ) (A B : VertexOperator ℂ M) (K L : ℕ)
    (locality : (deltaEnd ^ K) (FieldNormalProductLocality.commutator A B) = 0)
    (enlarges : K ≤ L) : qField s r K A B = qField s r L A B := by
  classical
  unfold qField
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro ell hL hK
  have high : (K : ℤ) ≤ r + ell := by
    simp only [Finset.mem_range, not_lt] at hK
    omega
  rw [ordinaryResidue_tail A B K locality (r + ell) high]
  suffices modeShift (ell : ℤ) (0 : VertexOperator ℂ M) = 0 by simp [this]
  apply HVertexOperator.coeff_inj
  funext e
  apply LinearMap.ext
  intro x
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff, modeShift_mode]
  simp

private theorem current_residue_identification (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a : Carrier D) (s r n : ℤ) (x : ActualTensor D hu) :
    fieldResidueCoefficient r n (targetCurrent D hu i) (targetSlice D hu a s) x =
      currentResidue D hu i (correctedField D hu a) s r n x := by
  have choose (ell : ℕ) : integerBinomial r ell = Ring.choose (r : ℂ) ell := by
    exact (Ring.map_choose (Int.castRingHom ℂ) r ell)
  simp only [fieldResidueCoefficient, fieldResidueLeft, fieldResidueRight,
    currentResidue, StateFieldResidueReconstruction.epsilon, choose,
    target_current_mode, targetSlice, physicalSlice_mode]

theorem current_q (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a : Carrier D) (s r : ℤ) :
    targetSlice D hu (neutralMode D i r a) (s + 1) =
      qField 1 r (vectorFrequencyBound D a + 1) (targetCurrent D hu i)
        (targetSlice D hu a s) := by
  apply HVertexOperator.coeff_inj
  funext e
  apply LinearMap.ext
  intro x
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    qField_mode, targetSlice, physicalSlice_mode]
  simp only [current_residue_identification, Int.cast_one]
  have law := D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds.inverse_all D hu i a s r (-e - 1) x
    (((vectorFrequencyBound D a + 1 : ℕ) : ℤ) - r).toNat (by omega)
  convert law using 1 <;> congr 1 <;> ring

private theorem ordinaryResidue_local (A B C : VertexOperator ℂ M)
    (hAC : FiniteFieldLocality.Local A C) (hBC : FiniteFieldLocality.Local B C)
    (hAB : FiniteFieldLocality.Local A B) (r : ℤ) :
    FiniteFieldLocality.Local (ordinaryResidue r A B) C := by
  by_cases hr : 0 ≤ r
  · obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le hr
    obtain ⟨L, hL⟩ := hAC
    obtain ⟨N, hN⟩ := hBC
    obtain ⟨K, hK⟩ := hAB
    have power (U W : VertexOperator ℂ M) (k : ℕ)
        (h : delta^[k] (FieldNormalProductLocality.commutator U W) = 0) :
        (deltaEnd ^ k) (FieldNormalProductLocality.commutator U W) = 0 := by
      rw [Module.End.pow_apply]
      exact h
    exact ⟨_, D5.S3.VertexAlgebra.StateFieldResidueReconstruction.fieldResidue_nonnegative_locality A B C L N K degree
      (power A C L hL) (power B C N hN) (power A B K hK)⟩
  · let degree := (-r - 1).toNat
    rw [ordinaryResidue, show r = -(degree : ℤ) - 1 by dsimp [degree]; omega,
      D5.S3.VertexAlgebra.StateFieldResidueReconstruction.fieldResidue_negative_normal A B degree]
    exact FiniteFieldLocality.localNormal _ _ _
      (FiniteFieldLocality.localDerivative A C degree hAC) hBC
      (FiniteFieldLocality.localDerivative A B degree hAB)

private theorem modeShift_local (amount : ℤ) (A B : VertexOperator ℂ M)
    (hAB : FiniteFieldLocality.Local A B) :
    FiniteFieldLocality.Local (modeShift amount A) B := by
  obtain ⟨K, hK⟩ := hAB
  let shiftPair : (ℤ → ℤ → Module.End ℂ M) → (ℤ → ℤ → Module.End ℂ M) :=
    fun F left right => F (left - amount) right
  have comm : FieldNormalProductLocality.commutator (modeShift amount A) B =
      shiftPair (FieldNormalProductLocality.commutator A B) := by
    funext left right
    simp only [FieldNormalProductLocality.commutator, modeShift_mode]
    rfl
  have intertwine (F : ℤ → ℤ → Module.End ℂ M) :
      delta (shiftPair F) = shiftPair (delta F) := by
    funext left right
    dsimp [delta, shiftPair]
    rw [show left + 1 - amount = left - amount + 1 by omega]
  have powers (n : ℕ) (F : ℤ → ℤ → Module.End ℂ M) :
      delta^[n] (shiftPair F) = shiftPair (delta^[n] F) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, intertwine,
        Function.iterate_succ_apply']
  refine ⟨K, ?_⟩
  rw [comm, powers, hK]
  rfl

private theorem qField_local (s r : ℤ) (K : ℕ) (A B C : VertexOperator ℂ M)
    (hAC : FiniteFieldLocality.Local A C) (hBC : FiniteFieldLocality.Local B C)
    (hAB : FiniteFieldLocality.Local A B) :
    FiniteFieldLocality.Local (qField s r K A B) C := by
  apply FiniteFieldLocality.localSum
  intro ell _
  apply FiniteFieldLocality.localSmul
  exact modeShift_local ell _ _ (ordinaryResidue_local A B C hAC hBC hAB (r + ell))


end Residues

section OrderedReadouts
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
open CollisionLaurentKernels.LaurentCollision
open OrderedCollisionCoordinates.ContextualLaurentKernel
open StateFieldResidueReconstruction

theorem binary_kernel_coeff (r a b : ℤ) :
    (contextPair ℂ 0 0 (kernelZX ℂ r)).coeff (pairIndex 0 0 (toLex (a, b))) =
      if 0 ≤ a then if b = r - a then
        BinomialKernelDelta.chooseSign r a.toNat else 0 else 0 := by
  change (HahnSeries.embDomain (pairEmbedding 0 0) (HahnSeries.ofIterate (kernelZX ℂ r))).coeff
    ((pairEmbedding 0 0) (toLex (a, b))) = _
  rw [HahnSeries.embDomain_coeff]
  change ((kernelZX ℂ r).coeff a).coeff b = _
  by_cases ha : 0 ≤ a
  · rw [if_pos ha, ← Int.toNat_of_nonneg ha, kernelZX_coeff_nat, HahnSeries.coeff_single]
    simp only [Int.toNat_of_nonneg ha, BinomialKernelDelta.chooseSign]
  · rw [if_neg ha, kernelZX_coeff_neg ℂ r a (by omega)]
    rfl

private theorem binary_word_coeff (A B : VertexOperator ℂ M) (x : M)
    (phi : M →ₗ[ℂ] ℂ) (a b : ℤ) :
    (scalarWordCarrier 2 ![A, B] id x phi).coeff
      (pairIndex 0 0 (toLex (a, b))) =
      phi ((A[[-b - 1]]) ((B[[-a - 1]]) x)) := by
  have h := scalarOrdered_coeff 2 ![A, B] ![b, a] x phi
  have base : (0 : Indices 0) = () := by
    change (0 : Unit) = (); exact Subsingleton.elim _ _
  simpa [scalarWordCarrier, exponents, actualWord, Fin.last, pairIndex, base] using h

/-- Coefficient extraction in the genuine supported forward order. The
finite interval is determined by the actual rightmost input, before applying
the left field. -/
private theorem binary_ordered_extract (A B : VertexOperator ℂ M) (x : M)
    (phi : M →ₗ[ℂ] ℂ) (r z w : ℤ) :
    (contextPair ℂ 0 0 (kernelZX ℂ r) *
      scalarWordCarrier 2 ![A, B] id x phi).coeff
        (pairIndex 0 0 (toLex (w, z))) =
      ∑ᶠ j : ℕ, BinomialKernelDelta.chooseSign r j *
        phi ((A[[-z + r - j - 1]]) ((B[[-w + j - 1]]) x)) := by
  classical
  let U := contextPair ℂ 0 0 (kernelZX ℂ r)
  let W := scalarWordCarrier 2 ![A, B] id x phi
  let target := pairIndex 0 0 (toLex (w, z))
  let terms (j : ℕ) := BinomialKernelDelta.chooseSign r j *
    phi ((A[[-z + r - j - 1]]) ((B[[-w + j - 1]]) x))
  have finite : Function.HasFiniteSupport terms := by
    apply (Finset.range ((w - ((HahnModule.of ℂ).symm (B x)).order).toNat + 1)).finite_toSet.subset
    intro j hj
    apply Finset.mem_range.mpr
    by_contra outside
    have zero : (B[[-w + j - 1]]) x = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    exact hj (by simp [terms, zero])
  have wordCoeff (j : ℕ) :
      U.coeff (pairIndex 0 0 (toLex ((j : ℤ), r - j))) *
        W.coeff (target - pairIndex 0 0 (toLex ((j : ℤ), r - j))) = terms j := by
    rw [show target - pairIndex 0 0 (toLex ((j : ℤ), r - j)) =
      pairIndex 0 0 (toLex (w - j, z - (r - j))) by rfl]
    dsimp only [U, W]
    rw [binary_kernel_coeff, if_pos (by omega), if_pos rfl, Int.toNat_natCast,
      binary_word_coeff]
    dsimp only [terms]
    rw [show -(z - (r - (j : ℤ))) - 1 = -z + r - j - 1 by omega,
      show -(w - (j : ℤ)) - 1 = -w + j - 1 by omega]
  rw [show (contextPair ℂ 0 0 (kernelZX ℂ r) *
      scalarWordCarrier 2 ![A, B] id x phi).coeff
      (pairIndex 0 0 (toLex (w, z))) = (U * W).coeff target by rfl,
    HahnSeries.coeff_mul, finsum_eq_sum terms finite]
  apply Finset.sum_bij_ne_zero
    (fun pair _ _ => (ofLex pair.1).1.toNat)
  · intro pair hp hn
    obtain ⟨hu, hw, ht⟩ := Finset.mem_antidiagonal.mp hp
    have hc := hu
    change U.coeff pair.1 ≠ 0 at hc
    have rep : pair.1 = pairIndex 0 0
        (toLex ((ofLex pair.1).1, (ofLex (ofLex pair.1).2).1)) := by
      rfl
    rw [rep] at hc
    dsimp only [U] at hc
    rw [binary_kernel_coeff] at hc
    split_ifs at hc with nonneg diagonal
    · rw [Set.Finite.mem_toFinset]
      change terms (ofLex pair.1).1.toNat ≠ 0
      have indices : pair.1 = pairIndex 0 0
          (toLex (((ofLex pair.1).1.toNat : ℤ), r - (ofLex pair.1).1.toNat)) := by
        rw [Int.toNat_of_nonneg nonneg]
        exact rep.trans (by rw [diagonal])
      have second : pair.2 = target - pair.1 := by rw [← ht]; abel
      rw [second, indices, wordCoeff] at hn
      exact hn
    all_goals contradiction
  · intro pair hp hn other ho hno equal
    obtain ⟨hu, hw, ht⟩ := Finset.mem_antidiagonal.mp hp
    obtain ⟨ou, ow, ot⟩ := Finset.mem_antidiagonal.mp ho
    have shape (g : Indices 2) (hg : U.coeff g ≠ 0) :
        g = pairIndex 0 0 (toLex (((ofLex g).1.toNat : ℤ),
          r - (ofLex g).1.toNat)) := by
      have rep : g = pairIndex 0 0 (toLex ((ofLex g).1, (ofLex (ofLex g).2).1)) := by rfl
      have hc := hg
      rw [rep] at hc
      dsimp only [U] at hc
      rw [binary_kernel_coeff] at hc
      split_ifs at hc with ha hb
      · rw [Int.toNat_of_nonneg ha]
        exact rep.trans (by rw [hb])
      all_goals contradiction
    have first : pair.1 = other.1 := by rw [shape pair.1 hu, shape other.1 ou, equal]
    exact Prod.ext first (by rw [first] at ht; exact add_left_cancel (ht.trans ot.symm))
  · intro j hj hn
    let first := pairIndex 0 0 (toLex ((j : ℤ), r - j))
    refine ⟨(first, target - first), ?_, ?_, ?_⟩
    · apply Finset.mem_antidiagonal.mpr
      have ne := wordCoeff j
      have nz : U.coeff first * W.coeff (target - first) ≠ 0 := by
        exact ne.trans_ne hn
      exact ⟨(mul_ne_zero_iff.mp nz).1, (mul_ne_zero_iff.mp nz).2, by simp [sub_eq_add_neg, add_left_comm]⟩
    · exact (wordCoeff j).trans_ne hn
    · simp only [first, pairIndex, ofLex_toLex, Int.toNat_natCast]
  · intro pair hp hn
    obtain ⟨hu, hw, ht⟩ := Finset.mem_antidiagonal.mp hp
    have hc := hu
    have rep : pair.1 = pairIndex 0 0
        (toLex ((ofLex pair.1).1, (ofLex (ofLex pair.1).2).1)) := by rfl
    change U.coeff pair.1 ≠ 0 at hc
    rw [rep] at hc
    dsimp only [U] at hc
    rw [binary_kernel_coeff] at hc
    split_ifs at hc with ha hb
    · have first : pair.1 = pairIndex 0 0
          (toLex (((ofLex pair.1).1.toNat : ℤ), r - (ofLex pair.1).1.toNat)) := by
        rw [Int.toNat_of_nonneg ha]
        exact rep.trans (by rw [hb])
      have second : pair.2 = target - pair.1 := by rw [← ht]; abel
      calc
        _ = terms (ofLex pair.1).1.toNat := by
          conv_lhs => rw [second, first, wordCoeff]
        _ = _ := rfl
    all_goals contradiction

theorem reverse_kernel (r : ℤ) :
    kernelXZ ℂ r = (HahnSeries.C (HahnSeries.C (StateFieldResidueReconstruction.epsilon r))) * kernelZX ℂ r := by
  unfold kernelXZ kernelZX StateFieldResidueReconstruction.epsilon
  rw [neg_eq_neg_one_mul, mul_zpow, map_mul]
  simp only [map_zpow₀, map_neg, map_one]
  ring

/-- Both signed chambers are read on their own supported words, before taking
their difference. No locality or truncation of a single ordered residue is used. -/
theorem binary_residue_readout (A B : VertexOperator ℂ M) (x : M)
    (phi : M →ₗ[ℂ] ℂ) (r n : ℤ) :
    phi (((ordinaryResidue r A B)[[n]]) x) =
      (contextPair ℂ 0 0 (kernelZX ℂ r) *
        scalarWordCarrier 2 ![A, B] id x phi).coeff
          (pairIndex 0 0 (toLex (-n - 1, -1))) -
      (contextPair ℂ 0 0 (kernelXZ ℂ r) *
        scalarWordCarrier 2 ![B, A] id x phi).coeff
          (pairIndex 0 0 (toLex (-1, -n - 1))) := by
  have left := binary_ordered_extract A B x phi r (-1) (-n - 1)
  have right := binary_ordered_extract B A x phi r (-n - 1) (-1)
  have constant : contextPair ℂ 0 0 (HahnSeries.C (HahnSeries.C (StateFieldResidueReconstruction.epsilon r))) =
      HahnSeries.C (StateFieldResidueReconstruction.epsilon r) := by
    simp only [StateFieldResidueReconstruction.epsilon, map_zpow₀, map_neg, map_one]
  rw [reverse_kernel, map_mul, constant, mul_assoc, HahnSeries.C_apply,
    HahnSeries.coeff_single_zero_mul, left, right]
  rw [ordinaryResidue, (fieldResidue r A B).coefficient]
  simp only [fieldResidueCoefficient, fieldResidueLeft, fieldResidueRight,
    map_sub, map_smul]
  rw [map_finsum phi ((fieldResidue r A B).left_finite n x),
    map_finsum phi ((fieldResidue r A B).right_finite n x)]
  simp only [map_smul, smul_eq_mul]
  congr 1
  · apply finsum_congr
    intro j
    rw [show - -1 + r - (j : ℤ) - 1 = r - j by omega,
      show -(-n - 1) + (j : ℤ) - 1 = n + j by omega]
    rfl
  · congr 1
    apply finsum_congr
    intro j
    rw [show -(-n - 1) + r - (j : ℤ) - 1 = r + n - j by omega,
      show - -1 + (j : ℤ) - 1 = j by omega]
    rfl

/-- The finite fractional readout uses the two genuine supported chambers.
The coefficient of the remaining variable shifts by ell in both chambers. -/
def orderedQReadout (s r n : ℤ) (K : ℕ) (A B : VertexOperator ℂ M)
    (x : M) (phi : M →ₗ[ℂ] ℂ) : ℂ :=
  ∑ ell ∈ Finset.range ((K : ℤ) - r).toNat,
    Ring.choose (-(s : ℂ) / 2) ell *
      ((contextPair ℂ 0 0 (kernelZX ℂ (r + ell)) *
        scalarWordCarrier 2 ![A, B] id x phi).coeff
          (pairIndex 0 0 (toLex (-(n - ell) - 1, -1))) -
      (contextPair ℂ 0 0 (kernelXZ ℂ (r + ell)) *
        scalarWordCarrier 2 ![B, A] id x phi).coeff
          (pairIndex 0 0 (toLex (-1, -(n - ell) - 1))))

private theorem qField_ordered_readout (s r n : ℤ) (K : ℕ)
    (A B : VertexOperator ℂ M) (x : M) (phi : M →ₗ[ℂ] ℂ) :
    phi (((qField s r K A B)[[n]]) x) = orderedQReadout s r n K A B x phi := by
  rw [qField_mode, map_sum]
  unfold orderedQReadout
  apply Finset.sum_congr rfl
  intro ell member
  rw [map_smul]
  rw [← (fieldResidue (r + ell) A B).coefficient (n - ell) x, smul_eq_mul]
  exact congrArg (Ring.choose (-(s : ℂ) / 2) ell * ·)
    (binary_residue_readout A B x phi (r + ell) (n - ell))

end OrderedReadouts

section TwoPoles
open CollisionLaurentKernels.LaurentCollision
open CollisionRationalExpansions.RationalCoefficientCollision
open CollisionRationalExpansions.SpectatorPole
open CollisionRationalExpansions.PartialFractionCollision
open CollisionLaurentKernels.RationalFusedResidue

/-- A finite list of poles, with coefficients in the genuine rational x-field.
The Boolean selects the diagonal pole or the integration-variable pole. -/
def twoPoleValue (diagonalSide : Bool) (terms : List (RatFunc ℂ × ℕ)) : Rational ℂ :=
  (terms.map (fun term => rationalX ℂ term.1 *
    if diagonalSide then diagonal ℂ ^ (-(term.2 : ℤ))
    else rationalZ ℂ (RatFunc.X ^ (-(term.2 : ℤ))))).sum

private theorem twoPoleValue_scale (side : Bool) (terms : List (RatFunc ℂ × ℕ))
    (c : RatFunc ℂ) :
    twoPoleValue side (terms.map (fun term => (c * term.1, term.2))) =
      rationalX ℂ c * twoPoleValue side terms := by
  induction terms with
  | nil => simp [twoPoleValue]
  | cons term terms ih =>
    simp only [twoPoleValue, List.map_cons, List.sum_cons, List.map_map] at ih ⊢
    rw [map_mul, mul_assoc, ih, mul_add]

private theorem twoPoleValue_append (side : Bool) (u v : List (RatFunc ℂ × ℕ)) :
    twoPoleValue side (u ++ v) = twoPoleValue side u + twoPoleValue side v := by
  simp only [twoPoleValue, List.map_append, List.sum_append]

theorem rational_x : rationalX ℂ RatFunc.X = x ℂ := by
  rw [← RatFunc.algebraMap_X, rationalX, IsFractionRing.lift_algebraMap]
  rfl

theorem rational_z : rationalZ ℂ RatFunc.X = z ℂ := by
  rw [← RatFunc.algebraMap_X, rationalZ, IsFractionRing.lift_algebraMap]
  simp [zPolynomial, z]

private theorem two_pole_form (p q : ℕ) :
    ∃ first second : List (RatFunc ℂ × ℕ),
      z ℂ ^ (-(p : ℤ)) * diagonal ℂ ^ (-(q : ℤ)) =
        twoPoleValue true first + twoPoleValue false second := by
  have nz : z ℂ ≠ 0 := by
    unfold z
    simpa only [map_zero] using
      (IsFractionRing.injective (Bivariate ℂ) (Rational ℂ)).ne Polynomial.X_ne_zero
  have nd : diagonal ℂ ≠ 0 := by
    intro h
    have hc := congrArg (iotaFused ℂ) h
    rw [iotaFused_diagonal, map_zero] at hc
    simpa using hc
  have nx : x ℂ ≠ 0 := by
    rw [← rational_x]
    simpa only [map_zero] using (rationalX ℂ).injective.ne RatFunc.X_ne_zero
  induction p generalizing q with
  | zero =>
    refine ⟨[(1, q)], [], ?_⟩
    simp [twoPoleValue]
  | succ p ih =>
    induction q with
    | zero =>
      refine ⟨[], [(1, p + 1)], ?_⟩
      simp only [twoPoleValue, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Bool.false_eq_true, ite_false, map_one, one_mul, add_zero, zero_add, zpow_zero,
        mul_one, map_zpow₀, rational_z, Nat.cast_zero, neg_zero]
    | succ q iq =>
      obtain ⟨f, g, hf⟩ := ih (q + 1)
      obtain ⟨h, k, hh⟩ := iq
      let c : RatFunc ℂ := RatFunc.X⁻¹
      refine ⟨f.map (fun term => (c * term.1, term.2)) ++
          h.map (fun term => (-c * term.1, term.2)),
        g.map (fun term => (c * term.1, term.2)) ++
          k.map (fun term => (-c * term.1, term.2)), ?_⟩
      have step : z ℂ ^ (-((p + 1 : ℕ) : ℤ)) * diagonal ℂ ^ (-((q + 1 : ℕ) : ℤ)) =
          rationalX ℂ c * (z ℂ ^ (-(p : ℤ)) * diagonal ℂ ^ (-((q + 1 : ℕ) : ℤ))) +
          rationalX ℂ (-c) * (z ℂ ^ (-((p + 1 : ℕ) : ℤ)) * diagonal ℂ ^ (-(q : ℤ))) := by
        simp only [c, map_inv₀, rational_x, map_neg, zpow_neg, zpow_natCast,
          pow_succ, mul_inv_rev]
        unfold diagonal at *
        field_simp
        <;> ring
      rw [step, hf, hh]
      rw [twoPoleValue_append, twoPoleValue_append]
      rw [twoPoleValue_scale, twoPoleValue_scale, twoPoleValue_scale, twoPoleValue_scale]
      ring

/-- The finite two-pole decomposition is constructed before the collision
theorem is used; both negative exponents are unrestricted. -/
theorem negative_laurent_collision (p q : ℕ) :
    (∃ first second : List (RatFunc ℂ × ℕ),
      z ℂ ^ (-(p : ℤ)) * diagonal ℂ ^ (-(q : ℤ)) =
        twoPoleValue true first + twoPoleValue false second) ∧
    expandX ℂ (localResidue ℂ (z ℂ ^ (-(p : ℤ)) * diagonal ℂ ^ (-(q : ℤ)))) =
      resZ_ZX ℂ (iotaZX ℂ (z ℂ ^ (-(p : ℤ)) * diagonal ℂ ^ (-(q : ℤ)))) -
      resZ_XZ ℂ (iotaXZ ℂ (z ℂ ^ (-(p : ℤ)) * diagonal ℂ ^ (-(q : ℤ)))) := by
  obtain ⟨first, second, form⟩ := two_pole_form p q
  refine ⟨⟨first, second, form⟩, ?_⟩
  have diagonalSum : twoPoleValue true first =
      ∑ j : Fin first.length, rationalX ℂ (first.get j).1 *
        (z ℂ ^ (0 : ℕ) * diagonal ℂ ^ (-((first.get j).2 : ℤ))) := by
    change (first.map (fun term => rationalX ℂ term.1 *
      diagonal ℂ ^ (-(term.2 : ℤ)))).sum = _
    have h := List.sum_ofFn (f := fun j : Fin first.length =>
      rationalX ℂ (first.get j).1 * diagonal ℂ ^ (-((first.get j).2 : ℤ)))
    change (List.ofFn ((fun term : RatFunc ℂ × ℕ =>
      rationalX ℂ term.1 * diagonal ℂ ^ (-(term.2 : ℤ))) ∘ first.get)).sum = _ at h
    rw [← List.map_ofFn, List.ofFn_get] at h
    simpa only [pow_zero, one_mul] using h
  have separatedSum : twoPoleValue false second =
      ∑ j : Fin second.length, rationalX ℂ (second.get j).1 *
        rationalZ ℂ (RatFunc.X ^ (-((second.get j).2 : ℤ))) := by
    change (second.map (fun term => rationalX ℂ term.1 *
      rationalZ ℂ (RatFunc.X ^ (-(term.2 : ℤ))))).sum = _
    have h := List.sum_ofFn (f := fun j : Fin second.length =>
      rationalX ℂ (second.get j).1 * rationalZ ℂ (RatFunc.X ^ (-((second.get j).2 : ℤ))))
    change (List.ofFn ((fun term : RatFunc ℂ × ℕ => rationalX ℂ term.1 *
      rationalZ ℂ (RatFunc.X ^ (-(term.2 : ℤ)))) ∘ second.get)).sum = _ at h
    rw [← List.map_ofFn, List.ofFn_get] at h
    exact h
  have decomposition := form.trans (congrArg₂ (· + ·) diagonalSum separatedSum)
  simpa only [zpow_zero, one_mul] using weighted_normal_form_collision ℂ
    (Finset.univ : Finset (Fin first.length)) (Finset.univ : Finset (Fin second.length))
    (fun j => (first.get j).1) (fun _ => 0) (fun j => (first.get j).2)
    (fun j => RatFunc.X ^ (-((second.get j).2 : ℤ))) (fun j => (second.get j).1)
    (z ℂ ^ (-(p : ℤ)) * diagonal ℂ ^ (-(q : ℤ))) 0
    (by simpa only [zpow_zero, one_mul] using decomposition)

end TwoPoles

/-- The three labels are J,A,B; every permutation keeps these labels fixed. -/
def threeFields (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (gamma delta : ℤ) : Fin 3 → VertexOperator ℂ (ActualTensor D hu) :=
  ![targetCurrent D hu i, targetSlice D hu a gamma, targetSlice D hu b delta]

/-- Independent current/source, current/source and source/source locality orders. -/
def threeOrders (D : LatticeData) (a b : Carrier D) (K : ℕ) (pair : Fin 3 × Fin 3) : ℕ :=
  if pair.1 = 0 then if pair.2 = 1 then vectorFrequencyBound D a + 1
    else vectorFrequencyBound D b + 1 else K

/-- The common array is an actual polynomial action on the JAB ordering. -/
def actualNumerator (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (gamma delta : ℤ) (K : ℕ) (x : ActualTensor D hu) :
    Distribution 3 (ActualTensor D hu) :=
  polynomialAction (weightedClearingPolynomial (threeOrders D a b K))
    (coefficientDistribution (threeFields D hu i a b gamma delta) x 1 [0, 1, 2])

/- proof_shape: actual_three_field_numerator: content
   admission_basis: escape-witness
   escape_witness: The all-signed current identity supplies the exact two current
   pair orders. Genuine doubled-coefficient physical locality supplies the third.
   Contextual adjacent exchanges identify all six operator orders. Moving each
   field to the right proves simultaneous input-dependent coordinate lower bounds;
   a fixed total exponent then lies in a finite Laurent simplex. -/
/-- Common six-order clearing and finite Laurent windows on every actual input. -/
theorem actual_three_field_numerator (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a b : Carrier D) :
    ∃ K : ℕ, ∀ gamma delta : ℤ,
      (deltaEnd ^ K) (FieldNormalProductLocality.commutator (targetSlice D hu a gamma) (targetSlice D hu b delta)) = 0 ∧
      (∀ d : ℤ, targetSlice D hu (neutralMode D i d a) (gamma + 1) =
        qField 1 d (vectorFrequencyBound D a + 1)
          (targetCurrent D hu i) (targetSlice D hu a gamma)) ∧
      (∀ d : ℤ, targetSlice D hu (neutralMode D i d b) (delta + 1) =
        qField 1 d (vectorFrequencyBound D b + 1)
          (targetCurrent D hu i) (targetSlice D hu b delta)) ∧
      (∀ L : ℕ, (deltaEnd ^ L) (FieldNormalProductLocality.commutator
          (targetSlice D hu a gamma) (targetSlice D hu b delta)) = 0 →
        ∀ s r : ℤ, qField s r K (targetSlice D hu a gamma) (targetSlice D hu b delta) =
          qField s r L (targetSlice D hu a gamma) (targetSlice D hu b delta)) ∧
      (∀ r : ℤ,
        FiniteFieldLocality.Local
          (qField gamma r K (targetSlice D hu a gamma) (targetSlice D hu b delta))
          (targetCurrent D hu i) ∧
        FiniteFieldLocality.Local
          (qField 1 r (vectorFrequencyBound D a + 1)
            (targetCurrent D hu i) (targetSlice D hu a gamma)) (targetSlice D hu b delta) ∧
        FiniteFieldLocality.Local
          (qField 1 r (vectorFrequencyBound D b + 1)
            (targetCurrent D hu i) (targetSlice D hu b delta)) (targetSlice D hu a gamma)) ∧
      ∀ x : ActualTensor D hu,
        (∀ order : List (Fin 3), [0, 1, 2].Perm order →
          polynomialAction (weightedClearingPolynomial (threeOrders D a b K))
            (coefficientDistribution (threeFields D hu i a b gamma delta) x 1 order) =
          actualNumerator D hu i a b gamma delta K x) ∧
        (∀ label : Fin 3, LowerBoundIn (actualNumerator D hu i a b gamma delta K x) label
          (((HahnModule.of ℂ).symm (threeFields D hu i a b gamma delta label x)).order)) ∧
        (∀ total : ℤ, {e : Exponent 3 | totalExponent e = total ∧
          actualNumerator D hu i a b gamma delta K x e ≠ 0}.Finite) ∧
        (∀ (phi : ActualTensor D hu →ₗ[ℂ] ℂ) (sigma : Equiv.Perm (Fin 3)),
          ∃ cleared : HahnSeries (Indices 3) ℂ,
            (∀ e : Exponent 3, cleared.coeff (orderExponents 3 sigma e) =
              phi (actualNumerator D hu i a b gamma delta K x e)) ∧
            scalarWordCarrier 3 (threeFields D hu i a b gamma delta) sigma x phi =
              (orderedPolynomialFor ℂ 3 sigma
                (weightedClearingPolynomial (threeOrders D a b K)))⁻¹ * cleared) := by
  obtain ⟨K, pairLocal⟩ := source_slice_locality D hu a b
  refine ⟨K, ?_⟩
  intro gamma delta
  have locally (U W : VertexOperator ℂ (ActualTensor D hu)) (n : ℕ)
      (h : (deltaEnd ^ n) (FieldNormalProductLocality.commutator U W) = 0) :
      FiniteFieldLocality.Local U W := by
    refine ⟨n, ?_⟩
    rw [Module.End.pow_apply] at h
    exact h
  have ja := locally _ _ _ (current_slice_locality D hu i a gamma)
  have jb := locally _ _ _ (current_slice_locality D hu i b delta)
  have ab := locally _ _ _ (pairLocal gamma delta)
  refine ⟨pairLocal gamma delta, (fun d => current_q D hu i a gamma d),
    (fun d => current_q D hu i b delta d), ?_, ?_, ?_⟩
  · intro L hL s r
    exact (qField_pad s r _ _ K (max K L) (pairLocal gamma delta)
      (Nat.le_max_left K L)).trans
        (qField_pad s r _ _ L (max K L) hL (Nat.le_max_right K L)).symm
  · intro r
    exact ⟨qField_local gamma r K _ _ _
        (FiniteFieldLocality.localSymm _ _ ja) (FiniteFieldLocality.localSymm _ _ jb) ab,
      qField_local 1 r (vectorFrequencyBound D a + 1) _ _ _ jb ab ja,
      qField_local 1 r (vectorFrequencyBound D b + 1) _ _ _ ja
        (FiniteFieldLocality.localSymm _ _ ab) jb⟩
  intro x
  have locality : ∀ first second : Fin 3, first < second →
      (deltaEnd ^ threeOrders D a b K (first, second))
        (FieldNormalProductLocality.commutator (threeFields D hu i a b gamma delta first)
          (threeFields D hu i a b gamma delta second)) = 0 := by
    intro first second less
    fin_cases first <;> fin_cases second <;> norm_num at less
    · exact current_slice_locality D hu i a gamma
    · exact current_slice_locality D hu i b delta
    · exact pairLocal gamma delta
  obtain ⟨permutations, lower, finite⟩ := common_cleared_fields
    (threeFields D hu i a b gamma delta) x 1 (threeOrders D a b K) locality
      [0, 1, 2] (by decide) (by intro label; fin_cases label <;> simp)
  refine ⟨(fun order hp => (permutations order hp).symm), lower, finite, ?_⟩
  intro phi sigma
  let Q := weightedClearingPolynomial (threeOrders D a b K)
  let W := scalarWordCarrier 3 (threeFields D hu i a b gamma delta) sigma x phi
  have uniformNonzero : UniformGradedLocalCorrelator.clearingPolynomial 3 1 ≠ 0 :=
    SupportedWordRationalCollision.ActualRationalReconstruction.originalQ_ne_zero 3 0 1
  have pairNonzero : ∀ p ∈ labelledPairs 3, pairPolynomial p.1 p.2 ≠ 0 := by
    simpa only [UniformGradedLocalCorrelator.clearingPolynomial, pow_one] using
      (Finset.prod_ne_zero_iff.mp uniformNonzero)
  have Qnonzero : Q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact pow_ne_zero _ (pairNonzero p hp)
  have embeddedNonzero : orderedPolynomialFor ℂ 3 sigma Q ≠ 0 := by
    simpa only [map_zero] using (orderedPolynomialFor_injective ℂ 3 sigma).ne Qnonzero
  refine ⟨orderedPolynomialFor ℂ 3 sigma Q * W, ?_, ?_⟩
  · intro e
    have hp : [0, 1, 2].Perm (List.ofFn sigma) :=
      SupportedWordRationalCollision.ActualRationalReconstruction.supplier_order_perm
        [0, 1, 2] (by decide) (by intro label; fin_cases label <;> simp) sigma
    have coefficients : (fun e' => W.coeff (orderExponents 3 sigma e')) =
        (fun e' => phi (coefficientDistribution (threeFields D hu i a b gamma delta)
          x 1 (List.ofFn sigma) e')) := by
      funext e'
      change (scalarWordCarrier 3 (threeFields D hu i a b gamma delta) sigma x phi).coeff
        (exponents 3 (fun label => e' (sigma label))) = _
      rw [scalarWordCarrier_coeff]
      rfl
    rw [ordered_mul_coeff, coefficients, ← scalar_action]
    exact congrArg phi (congrFun (permutations _ hp).symm e)
  · rw [← mul_assoc, inv_mul_cancel₀ embeddedNonzero, one_mul]

/-- Actual binary readouts for arbitrary original sources, and their current
consumers. The pair order is supplied by the same six-order numerator theorem. -/
theorem actual_ordered_q_coefficients (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a b : Carrier D) :
    ∃ K : ℕ, ∀ gamma delta : ℤ,
      (deltaEnd ^ K) (FieldNormalProductLocality.commutator
        (targetSlice D hu a gamma) (targetSlice D hu b delta)) = 0 ∧
      (∀ (s r n : ℤ) (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ),
        phi (((qField s r K (targetSlice D hu a gamma)
          (targetSlice D hu b delta))[[n]]) x) =
        orderedQReadout s r n K (targetSlice D hu a gamma) (targetSlice D hu b delta) x phi) ∧
      (∀ (d n : ℤ) (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ),
        phi (((targetSlice D hu (neutralMode D i d a) (gamma + 1))[[n]]) x) =
          orderedQReadout 1 d n (vectorFrequencyBound D a + 1)
            (targetCurrent D hu i) (targetSlice D hu a gamma) x phi) ∧
      (∀ (d n : ℤ) (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ),
        phi (((targetSlice D hu (neutralMode D i d b) (delta + 1))[[n]]) x) =
          orderedQReadout 1 d n (vectorFrequencyBound D b + 1)
            (targetCurrent D hu i) (targetSlice D hu b delta) x phi) := by
  obtain ⟨K, accepted⟩ := actual_three_field_numerator D hu i a b
  refine ⟨K, ?_⟩
  intro gamma delta
  obtain ⟨locality, first, second, rest⟩ := accepted gamma delta
  refine ⟨locality, ?_, ?_, ?_⟩
  · intro s r n x phi
    exact qField_ordered_readout s r n K _ _ x phi
  · intro d n x phi
    rw [first d]
    exact qField_ordered_readout 1 d n _ _ _ x phi
  · intro d n x phi
    rw [second d]
    exact qField_ordered_readout 1 d n _ _ _ x phi

end
end D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport
