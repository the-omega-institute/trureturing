import D5.S3.FiniteGroups.ExtremalC48.ExtremalC48Complexification
import D5.S3.FiniteGroups.ExtremalC48.ExtremalC48GroupStep
import D5.S3.FiniteGroups.ExtremalC48.PhaseKernelOddPrimeDraft
import D5.S3.VertexAlgebra.Lattice.Automorphisms.ReducibleActionWeightTwo
import D5.S3.VertexAlgebra.Lattice.Automorphisms.PhaseCharacterDraft
import D5.S3.VertexAlgebra.Lattice.Automorphisms.P48qLiftAnomaly

/-! Conditional obstruction for finite monomial automorphism actions on the actual
lattice carrier.

The external P48q input is the identification of its lattice isometry group
with SL(2,47), rank 48, central inversion, positive definite Gram form, and
the fixed rank 16 of an order-three element (Nebe, arXiv:1312.3780,
Tables 1 and 2). The standard-lift twisted lowest-weight formula is supplied
as a hypothesis (Gemünden–Keller, arXiv:1909.09626, equations (113) and (24)).
The twisted lowest weight and its cyclic type are represented by the supplied
rational and the residue of nine times that rational, respectively.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.P48qFiniteActionObstruction

open LatticeGeneratingFieldLocality LatticeAllStateField LatticePositiveEnergy
open LatticeActualConformalState LatticeSugawaraCurrents
open ReducibleActionWeightTwo PhaseCharacterDraft P48qLiftAnomaly
open ExtremalC48 Module
open scoped Matrix VertexOperator

noncomputable section

private abbrev ground (D : LatticeData) (a : Charge D) : Carrier D :=
  Finsupp.single a (1 : Oscillator D)

private theorem identity_of_trivial_charge (D : LatticeData) (g : AddAut (Charge D))
    (hg : ∀ a, g a = a) : (realChargeAction D g).toLinearMap = 1 := by
  have hM : realMixingMatrix D g = 1 := by
    ext i j
    simp [realMixingMatrix, hg, unitCharge, Matrix.one_apply]
  change Matrix.toLin' (realMixingMatrix D g) = 1
  rw [hM, Matrix.toLin'_one]
  rfl

private theorem charge_fixed_of_identity (D : LatticeData) (g : AddAut (Charge D))
    (eta : Charge D → ℂˣ)
    (h : ∀ a, ground D a = (eta a : ℂ) • ground D (g a)) :
    ∀ a, g a = a := by
  classical
  intro a
  by_contra hne
  have he := congrArg (fun v : Carrier D => v a) (h a)
  simp [ground, Finsupp.single_apply, hne] at he

set_option maxHeartbeats 1000000 in
/-- For any finite group acting by actual monomial mode-preserving equivalences,
either two independent actual weight-two states are fixed, or an actual
order-three equivalence has fixed charge rank sixteen, standard phase on its
fixed charges, twisted lowest weight 16/9 and cyclic type one. The action map
may have a kernel: the proof uses the finite image of the joint projection
and action, on which kernel inversion follows from the actual modes. -/
theorem p48q_finite_action_dichotomy
    (D : LatticeData) {G : Type*} [Group G] [Finite G]
    (pi : G →* SL47)
    (mu : Additive SL47 →+ AddAut (Charge D))
    (rho : Representation ℝ SL47 (Fin D.rank → ℝ))
    (hReal : ∀ s, rho s = (realChargeAction D (mu s)).toLinearMap)
    (U : G →* (Carrier D ≃ₗ[ℂ] Carrier D))
    (eta : G → Charge D → ℂˣ)
    (hGround : ∀ g a, U g (ground D a) = (eta g a : ℂ) • ground D (mu (pi g) a))
    (hMode : ∀ g, PreservesModes D (U g))
    (hGram : ∀ s a b, bilinear D (mu s a) (mu s b) = bilinear D a b)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hRank : D.rank = 48)
    (i c : SL47) (hi : orderOf i = 2) (hNeg : ∀ a, mu i a = -a)
    (hc : orderOf c = 3)
    (hFixed : finrank ℝ (LinearMap.ker (rho c - 1)) = 16)
    (lowest : (Carrier D ≃ₗ[ℂ] Carrier D) → ℚ)
    (hStandardLiftLowestWeight : ∀ g : G, orderOf (U g) = 3 →
      (∀ a, mu (pi g) a = a → eta g a = 1) →
      lowest (U g) =
        ((D.rank : ℚ) - (finrank ℝ (LinearMap.ker (rho (pi g) - 1)) : ℚ)) / 18) :
    (∃ (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (v : Carrier D),
      H.IsSymm ∧ H * gramComplex D = 1 ∧
      omega D H ∈ grade D 2 ∧ v ∈ grade D 2 ∧
      ((Y D (omega D H))[[1]]) (omega D H) = (2 : ℂ) • omega D H ∧
      ((Y D (omega D H))[[1]]) v = (2 : ℂ) • v ∧
      (∀ g, U g (omega D H) = omega D H ∧ U g v = v) ∧
      LinearIndependent ℂ ![v, omega D H]) ∨
    (∃ g t : G, orderOf (U g) = 3 ∧ orderOf (pi g) = 3 ∧ pi t = i ∧
      Commute (U g) (U t) ∧ finrank ℝ (LinearMap.ker (rho (pi g) - 1)) = 16 ∧
      (∀ a, mu (pi g) a = a → eta g a = 1) ∧
      lowest (U g) = 16 / 9 ∧ (3 : ℚ)^2 * lowest (U g) = 16 ∧
      (∀ z : ℤ, (3 : ℚ)^2 * lowest (U g) = (z : ℚ) → (z : ZMod 3) = 1)) := by
  classical
  let sigma : Representation ℝ pi.range (Fin D.rank → ℝ) := rho.comp pi.range.subtype
  have hDim : finrank ℝ (Fin D.rank → ℝ) = 48 := by
    simpa using hRank
  by_cases hIrred : sigma.IsIrreducible
  · right
    let : sigma.IsIrreducible := hIrred
    obtain ⟨W, hW, hDegree⟩ := exists_irreducible_complexification_rank48 sigma hDim
    let : W.toRepresentation.IsIrreducible := hW
    let : Fact (Nat.Prime 47) := ⟨by decide⟩
    obtain ⟨a, b, ha, hb, haNeg, hab⟩ := subgroup_witnesses
      (by decide : (2 : ZMod 47) ≠ 0) pi.range.subtype Subtype.val_injective
      W.toRepresentation hDegree
    have haAmbient : orderOf (a : SL47) = 2 :=
      (orderOf_injective pi.range.subtype Subtype.val_injective a).trans ha
    have hbAmbient : orderOf (b : SL47) = 3 :=
      (orderOf_injective pi.range.subtype Subtype.val_injective b).trans hb
    have haI : (a : SL47) = i := by
      apply Subtype.ext
      exact haNeg.trans (SL2_orderTwo_negOne (by decide : (2 : ZMod 47) ≠ 0) i hi).1.symm
    obtain ⟨x, hx⟩ := a.property
    obtain ⟨y, hy⟩ := b.property
    have hxI : pi x = i := hx.trans haI
    have hOrderY : orderOf (pi y) = 3 := by rw [hy]; exact hbAmbient
    have hCommXY : Commute (pi x) (pi y) := by
      rw [hx, hy]
      exact hab.map pi.range.subtype
    -- The joint image makes the two coordinates faithful, even for a
    -- nonfaithful abstract action. Its projection is the lattice projection.
    let E := (pi.prod U).range
    let f : E →* SL47 := (MonoidHom.fst _ _).comp E.subtype
    let A : E →* (Carrier D ≃ₗ[ℂ] Carrier D) := (MonoidHom.snd _ _).comp E.subtype
    let inc : G →* E := (pi.prod U).rangeRestrict
    have hsurj : Function.Surjective inc := by
      intro e
      obtain ⟨k, hk⟩ := e.property
      exact ⟨k, Subtype.ext hk⟩
    let : Finite E := Finite.of_surjective inc hsurj
    have hInv : ∀ u : E, f u = f (inc x) → ∀ z ∈ f.ker, u * z * u⁻¹ = z⁻¹ := by
      intro u hu z hz
      obtain ⟨r, rfl⟩ := hsurj u
      obtain ⟨k, rfl⟩ := hsurj z
      have hr : pi r = i := hu.trans hxI
      have hk : pi k = 1 := hz
      have hrGround : ∀ a, U r (ground D a) = (eta r a : ℂ) • ground D (-a) := by
        intro a
        rw [hGround, hr, hNeg]
      have hkGround : ∀ a, U k (ground D a) = (eta k a : ℂ) • ground D a := by
        intro a
        rw [hGround, hk]
        have hm : mu (1 : SL47) = 0 := mu.map_zero
        rw [hm]
        rfl
      have hConj := negation_conjugates_inverse D (U r) (U k)
        (hMode r) (hMode k) (eta r) (eta k) hrGround hkGround
      apply Subtype.ext
      apply Prod.ext
      · change pi r * pi k * (pi r)⁻¹ = (pi k)⁻¹
        simp [hk]
      · change U r * U k * (U r)⁻¹ = (U k)⁻¹
        exact hConj
    obtain ⟨y', x', hy', hx', hPow, hComm, hOrder⟩ :=
      PhaseKernelOddPrimeDraft.exists_commuting_odd_prime_lifts f (inc y) (inc x)
        (by decide : Nat.Prime 3) (by decide : Odd 3) hOrderY hCommXY hInv
    obtain ⟨g, hg⟩ := hsurj y'
    obtain ⟨t, ht⟩ := hsurj x'
    have hgPi : pi g = pi y := by
      change f (inc g) = f (inc y)
      rw [hg, hy']
    have htPi : pi t = i := by
      change f (inc t) = i
      rw [ht, hx']
      exact hxI
    have hgOrderPi : orderOf (pi g) = 3 := by rw [hgPi]; exact hOrderY
    have hRank16 := SL47_orderThree_fixedRank rho c (pi g) hc hgOrderPi hFixed
    have hgPow : U g ^ 3 = 1 := by
      change A (inc g) ^ 3 = 1
      rw [hg, ← map_pow, hPow, map_one]
    have hgComm : Commute (U g) (U t) := by
      change Commute (A (inc g)) (A (inc t))
      rw [hg, ht]
      exact hComm.map A
    have hgOrder : orderOf (U g) = 3 := by
      let : Fact (Nat.Prime 3) := ⟨by decide⟩
      apply orderOf_eq_prime_iff.mpr
      refine ⟨hgPow, ?_⟩
      intro hId
      have hCharge := charge_fixed_of_identity D (mu (pi g)) (eta g) (by
        intro a
        simpa [hId] using hGround g a)
      have hIdReal : rho (pi g) = 1 :=
        (hReal _).trans (identity_of_trivial_charge D _ hCharge)
      have hAll : LinearMap.ker (rho (pi g) - 1) = ⊤ := by
        rw [hIdReal, sub_self, LinearMap.ker_zero]
      have hFull : finrank ℝ (LinearMap.ker (rho (pi g) - 1)) = 48 := by
        rw [hAll, finrank_top, hDim]
      omega
    have hTGround : ∀ a, U t (ground D a) = (eta t a : ℂ) • ground D (-a) := by
      intro a
      rw [hGround, htPi, hNeg]
    have hStandard : ∀ a, mu (pi g) a = a → eta g a = 1 :=
      fixed_charge_phase_eq_one_of_odd_period D (mu (pi g)) (U g) (U t)
        (eta g) (eta t) (hGround g) hTGround (fun u v m => hMode g u m v)
        hgComm 3 (by decide) hgPow
    have hFormula : (∀ a, mu (pi g) a = a → eta g a = 1) →
        lowest (U g) = (1 * (3 - 1) * (16 : ℚ) + 2 * (3 - 2) * (16 : ℚ)) / (4 * 3^2) := by
      intro h
      rw [hStandardLiftLowestWeight g hgOrder h, hRank16, hRank]
      norm_num
    obtain ⟨_, hLowest, hScaled, hType⟩ := p48q_order_three_type_one D (mu (pi g))
      (U g) (U t) (eta g) (eta t) (hGround g) hTGround
      (fun u v m => hMode g u m v) hgComm hgPow
      (finrank ℝ (LinearMap.ker (rho (pi g) - 1))) 16 hRank hRank16
      (by omega) (lowest (U g)) hFormula
    exact ⟨g, t, hgOrder, hgOrderPi, htPi, hgComm, hRank16, hStandard, hLowest, hScaled, hType⟩
  · left
    have hNontrivial : Nontrivial (Subrepresentation sigma) := by
      have hV : Nontrivial (Fin D.rank → ℝ) := by
        rw [hRank]
        infer_instance
      let := hV
      refine ⟨⟨⊥, ⊤, ?_⟩⟩
      intro h
      exact bot_ne_top (congrArg Subrepresentation.toSubmodule h :
        (⊥ : Submodule ℝ (Fin D.rank → ℝ)) = ⊤)
    let := hNontrivial
    have hProper : ∃ W : Subrepresentation sigma, W ≠ ⊥ ∧ W ≠ ⊤ := by
      by_contra! hn
      exact hIrred (IsSimpleOrder.mk' (fun W => or_iff_not_imp_right.mpr (hn W)))
    obtain ⟨W, hW0, hW1⟩ := hProper
    have hW0' : W.toSubmodule ≠ ⊥ :=
      fun h => hW0 (Subrepresentation.toSubmodule_injective h)
    have hW1' : W.toSubmodule ≠ ⊤ :=
      fun h => hW1 (Subrepresentation.toSubmodule_injective h)
    have hInvariant : ∀ g x, x ∈ W.toSubmodule →
        realChargeAction D (mu (pi g)) x ∈ W.toSubmodule := by
      intro g x hx
      have hh := W.apply_mem_toSubmodule (pi.rangeRestrict g) hx
      change rho (pi g) x ∈ W.toSubmodule at hh
      rw [hReal] at hh
      exact hh
    obtain ⟨H, P, hSymm, hInverse, _, hGradeH, hGradeP, hEigH, hEigP, hLift, hLI⟩ :=
      reducible_action_fixed_weight_two D hPos (fun g : G => mu (pi g))
        (fun g => hGram (pi g)) W.toSubmodule hW0' hW1' hInvariant
    refine ⟨H, omega D (P * H), hSymm, hInverse, hGradeH, hGradeP, hEigH, hEigP, ?_, hLI⟩
    intro g
    have hNeutral := monomial_neutral D (mu (pi g)) (hGram (pi g)) (U g) (hMode g)
      (eta g) (hGround g)
    constructor
    · exact (hNeutral (conformalPolynomial D H)).trans (hLift g).1
    · exact (hNeutral (conformalPolynomial D (P * H))).trans (hLift g).2

#print axioms p48q_finite_action_dichotomy
#check @p48q_finite_action_dichotomy

end
end D5.S3.VertexAlgebra.Lattice.P48qFiniteActionObstruction
