import GRH.Lib.GLn.SchurModule.Nabla
import GRH.Lib.DiscreteSeries.Theta.OscillatorDefs
import GRH.Lib.DiscreteSeries.Rigidity.HighestVectors
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Theta correspondence of discrete series for real unitary dual pairs; joint harmonics
(known result; see Lib.DiscreteSeries.Theta.LocalThetaCorrespondence).

This file: Swap symmetry, vacuum weight, Laplacians and Fischer inner product for Howe's
argument. -/

noncomputable section


open MvPolynomial Finset InnerProductSpace Submodule Int Complex ComplexOrder Pi

section

variable {R C ι} [Fintype R] [Fintype C] {ε ε'} {T : @FockDualPair R C ε ε' ι}
  {l' a η i N G j ν b} {l : HCParam ε} {P Q : MvPolynomial ι ℂ}

/-- If l, l' match for the data (σ, ε, ε', γ, γ'), then l', l match for the swapped data (−σ, ε', ε,
γ', γ). -/
lemma IsMatch.swap : IsMatch T l l' → IsMatch T.swap l' l := by
  grind [IsMatch, pairSign, Units.val_neg, units_natAbs, Units.val_mul]

/-- A joint harmonic P for (σ, ε, ε', γ, γ', l, l') is, with rows and columns exchanged, a joint
harmonic for (−σ, ε', ε, γ', γ, l', l). -/
lemma IsJointHarmonic.swap (h : IsJointHarmonic T l l' P) : IsJointHarmonic T.swap l' l P :=
  ⟨h.1.swap, by grind [FockDualPair.IsJointHighest, T.swap_swap, h.2]⟩

namespace Fischer

attribute [scoped simp] raiseOp lowerOp GlModule.E units_ne_iff_eq_neg DFunLike.ite_apply
  HCParam.IsKHighest IsHarmonic
  mem_restrictSupport_iff Set.subset_def coeff_pderiv pairSign coeff_X_mul' ite_and fockLaplacian

/-- For ε_a = ε_b, the row operator E_ab sends P to Σ X_ac ∂_bc P over the columns c of sign +1,
minus Σ X_bc ∂_ac P over those of sign −1, plus δ_ab times the vacuum weight times P. -/
lemma oscRows_E_eq_polarisation_sub (q : ε a = ε b) : T.oscRows.E a b P =
  T.polarisation P a b 1 - T.polarisation P b a (-1) + ite (a =
  b) (T.vacuumWeight (ε a) : ℂ) 0 • P := by simp [q, oscRows]; split <;> simp +contextual [glOp,
  *, sum_ite, vacuumWeight, polarisation, ← C_mul'] <;> ring

scoped instance : NormedAddCommGroup (MvPolynomial ι ℂ) := Core.toNormedAddCommGroup (cd :=
  ⟨⟨⟨(fockPairing ℂ <| map (starRingEnd ℂ) ·)⟩, by simp [map_fockPairing, fockPairing_comm,
  map_leftInverse conj_conj _], by simp; grind [fockPairing_star_self_pos, zero_re, pos_iff], by
  simp, by simp [← C_mul']; simp [C_mul']⟩, by grind [fockPairing_star_self_pos, inner]⟩)

scoped instance : InnerProductSpace ℂ (MvPolynomial ι ℂ) := .ofCore _

@[scoped simp] lemma inner_X_mul : ⟪X b * P, Q⟫_ℂ = ⟪P, pderiv b Q⟫_ℂ ∧ ⟪P,
  X b * Q⟫_ℂ = ⟪pderiv b P,
  Q⟫_ℂ := by simp [inner, fockPairing_mul_X, mul_comm (X b), fockPairing_comm (map _ _), pderiv_map]

/-- For an integer j, the space of complex polynomials of total degree at most j in variables
indexed by ι. -/
def polyDegreeLE (j : ℤ) := @restrictSupport ι ℂ _ {d | d.degree ≤ j}

instance [Fintype ι] : Module.Finite ℂ (@polyDegreeLE ι j) := finiteDimensional_of_le
  (S₂ := restrictTotalDegree ..) (restrictSupport_mono _ fun _ ↦ toNat_le_toNat)

lemma glOp_mem_polyDegreeLE : P ∈ polyDegreeLE j → j + η a ≤ i + η b →
  glOp η a b P ∈ polyDegreeLE i := by intros; simp [glOp]; split_ifs <;>
  simp_all [polyDegreeLE] <;> grind [Finsupp.degree_single, Finsupp.sub_add_single_one_cancel]

/-- The polynomials of degree at most j that are orthogonal, for the Fischer inner product, to
all elements of G of degree at most j. -/
abbrev perpInDegree j G := (@polyDegreeLE ι j ⊓ G)ᗮ ⊓ polyDegreeLE j

lemma eq_zero_of_mem_perpInDegree (h : P ∈ perpInDegree j N) : P ∈ N → P = 0 := by simpa using
  (h.1 P ⟨h.2, ·⟩)

/-- Fischer decomposition: let G contain the polynomials of degree ≤ j−1 and the row-action images
of those of degree ≤ j−2. If P of degree ≤ j is orthogonal to G in degree ≤ j, then the Laplacian
`FockDualPair.fockLaplacian` a b of P vanishes whenever ε_a ≠ ε_b. -/
lemma fockLaplacian_eq_zero (ih : ∀ k < j, polyDegreeLE k ≤ G) (h : P ∈ perpInDegree j G) (o :
  ε a ≠ ε b) (s : Q = T.fockLaplacian a b P) (g : Q ∈ G → T.oscRows.E b a Q ∈ G) : Q = 0 := by
  simp [-pairSign] at s
  have q : Q ∈ polyDegreeLE (j - 2) := s ▸ sum_mem fun _ _ ↦
    glOp_mem_polyDegreeLE h.2 (by simp_all; lia)
  rw [← @inner_self_eq_zero ℂ, s, inner_sum, ← s, ← neg_zero, ← h.1 _ ⟨sum_mem _, by
    simpa [oscRows, o, eq_comm, smul_mem_iff, ne_of_apply_ne ε] using g (ih _ (by lia) q)⟩,
    sum_filter, sum_inner, ← sum_neg_distrib]; congr! 1; split; simp_all [glOp, -s]; rw [h.1]
  all_goals simp <;> grind [glOp_mem_polyDegreeLE, units_natAbs, Units.coe_neg_one, Units.ext_iff,
    IsConcreteLE.le_iff]

/-- Let P be K-highest of weight ν for the oscillator action on rows, Q_ab = Σ ∂_{ac}∂_{bc}P
over c with σε_aε'_c = +. If no nonzero Q_ab, ε_a ≠ ε_b, is K-highest of weight ν − e_a +
e_b, all these Q_ab vanish. -/
lemma fockLaplacian_eq_zero_of_isKHighest (W : l.IsKHighest T.oscRows ν P) (H : ∀ a b, ε a ≠ ε b →
  l.IsKHighest T.oscRows (ν + single a 1 - single b 1) (T.fockLaplacian a b P) →
  T.fockLaplacian a b P = 0) : T.IsRowHarmonic P :=
  have C x z a b (h : ε x = ε z) : T.oscRows.E x z (T.fockLaplacian a b P) = T.fockLaplacian a b
    (T.oscRows.E x z P) + ite (z = a) (T.fockLaplacian x b P) 0 - ite (b = x) (T.fockLaplacian a z
    P) 0 := by simp +contextual [oscRows, h, glOp, canonical_commutation, -raiseOp, -lowerOp,
    -zsmul_eq_mul, apply_ite (raiseOp ..), apply_ite (lowerOp ..), sum_comm (t := univ)]; abel
  Prod.forall'.1 (Finite.int_weight_induction (fun i ↦ l i.2 - l i.1) fun i m o ↦
    H _ _ o (by simp_all [add_smul, sub_smul, -fockLaplacian, -H]; grind))

lemma mapsTo_perpInDegree (h : ε a = ε b) (S : N ≤ G.comap (T.oscRows.E b a)) :
  Set.MapsTo (T.oscRows.E a b) (perpInDegree j G) (perpInDegree j N) :=
  fun y k ↦ by use fun z p ↦ .trans (by by_cases a = b <;> simp [oscRows_E_eq_polarisation_sub,
  polarisation, *, eq_comm, mul_comm]) (k.1 _ ⟨?_, S p.2⟩) <;> simp_all [oscRows,
  ← cast_smul_eq_zsmul ℂ] <;> grind [sum_mem, smul_mem, glOp_mem_polyDegreeLE, pairSign, add_mem]
