import D5.S3.VertexAlgebra.Lattice.Automorphisms.ConformalGroundTransport
import D5.S3.VertexAlgebra.Lattice.Automorphisms.P48qFiniteActionObstruction
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificateDraft

/-! The type-zero obstruction for an actual finite conformal action on the P48q carrier. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.P48qPhysicalActionObstruction

open LatticeGeneratingFieldLocality LatticeAllStateField LatticePositiveEnergy
open LatticeActualConformalState LatticeSugawaraCurrents
open ReducibleActionWeightTwo PhaseCharacterDraft ExtremalC48 Module
open P48qFixedRankCertificateDraft P48qGramCertificateDraft
open scoped Matrix VertexOperator

noncomputable section

private abbrev ground (D : LatticeData) (a : Charge D) : Carrier D :=
  Finsupp.single a (1 : Oscillator D)

private theorem inversion_witness (D : LatticeData) (hRank : D.rank = 48)
    (mu : Additive SL47 →+ AddAut (Charge D)) (hFaithful : Function.Injective mu)
    (hExhaustive : ∀ s : AddAut (Charge D),
      (∀ a b, bilinear D (s a) (s b) = bilinear D a b) → ∃ k, mu k = s) :
    ∃ i : SL47, orderOf i = 2 ∧ ∀ a, mu i a = -a := by
  let negation : AddAut (Charge D) := AddEquiv.neg _
  have hIsometry : ∀ a b, bilinear D (negation a) (negation b) = bilinear D a b := by
    intro a b
    change bilinear D (-a) (-b) = bilinear D a b
    simp [bilinear, neg_mul]
  obtain ⟨k, hk⟩ := hExhaustive negation hIsometry
  let i : SL47 := k.toMul
  have hi : mu i = negation := hk
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  refine ⟨i, orderOf_eq_prime_iff.mpr ⟨?_, ?_⟩, fun a => ?_⟩
  · change (Additive.ofMul (i ^ 2)) = (0 : Additive SL47)
    apply hFaithful
    rw [show Additive.ofMul (i ^ 2) = 2 • Additive.ofMul i from rfl, map_nsmul, map_zero]
    change 2 • mu i = 0
    rw [hi]
    apply AddEquiv.ext
    intro a
    change -(-a) = a
    exact neg_neg a
  · intro h
    have hNegZero : negation = 0 := by rw [← hi, h]; exact mu.map_zero
    let j : Fin D.rank := Fin.cast hRank.symm 0
    have hEval := congrArg (fun s : AddAut (Charge D) => s (fun _ => 1) j) hNegZero
    change (-1 : ℤ) = 1 at hEval
    norm_num at hEval
  · rw [hi]
    rfl

/-- Exhaustivity identifies the certified integer isometry with some element of
the supplied action. Its order and its real fixed rank follow in the same basis. -/
private theorem order_three_witness (D : LatticeData) (hRank : D.rank = 48)
    (hNebeGram : ∀ i j : Fin D.rank,
      D.G i j = nebeGram (Fin.cast hRank i) (Fin.cast hRank j))
    (mu : Additive SL47 →+ AddAut (Charge D)) (hFaithful : Function.Injective mu)
    (hExhaustive : ∀ s : AddAut (Charge D),
      (∀ a b, bilinear D (s a) (s b) = bilinear D a b) → ∃ k, mu k = s)
    (rho : Representation ℝ SL47 (Fin D.rank → ℝ))
    (hReal : ∀ s, rho s = (realChargeAction D (mu s)).toLinearMap) :
    ∃ c : SL47, orderOf c = 3 ∧ finrank ℝ (LinearMap.ker (rho c - 1)) = 16 := by
  obtain ⟨rank, gram, symmetric, even_diagonal⟩ := D
  dsimp at hRank
  subst rank
  let D : LatticeData := ⟨48, gram, symmetric, even_diagonal⟩
  have hGram : D.G = nebeGram := by
    ext i j
    exact hNebeGram i j
  let A := nebeOrderThreeᵀ
  have hCube : A ^ 3 = 1 := by
    dsimp [A]
    rw [← Matrix.transpose_pow, nebeOrderThree_cube, Matrix.transpose_one]
  have hLeft : A ^ 2 * A = 1 := by rw [← pow_succ]; exact hCube
  have hRight : A * A ^ 2 = 1 := by rw [← pow_succ']; exact hCube
  let s : AddAut (Charge D) := (Matrix.toLin'OfInv hLeft hRight).toAddEquiv
  have hIsometry : ∀ a b, bilinear D (s a) (s b) = bilinear D a b := by
    intro a b
    have hCongr : Aᵀ * D.G * A = D.G := by
      rw [hGram]
      simpa only [A, Matrix.transpose_transpose] using gram_isometry_certificate
    have hForm := Matrix.toBilin'_comp D.G A A
    rw [hCongr] at hForm
    have hEval := congrArg (fun f : LinearMap.BilinForm ℤ (Charge D) => f a b) hForm
    change D.G.toBilin' (s a) (s b) = D.G.toBilin' a b at hEval
    simpa only [Matrix.toBilin'_apply, bilinear] using hEval
  obtain ⟨k, hk⟩ := hExhaustive s hIsometry
  let c : SL47 := k.toMul
  have hc : mu c = s := hk
  have hRho : rho c = rowAction ℝ nebeOrderThree := by
    rw [hReal, hc]
    change (realMixingMatrix D s).toLin' = (A.map (Int.castRingHom ℝ)).toLin'
    apply congrArg Matrix.toLin'
    ext i j
    have hu : unitCharge D j = Pi.single j (1 : ℤ) := by
      ext k
      simp [unitCharge, Pi.single_apply]
    change (A.mulVec (unitCharge D j) i : ℝ) = (A i j : ℝ)
    rw [hu, Matrix.mulVec_single_one]
    rfl
  have hFixed : finrank ℝ (LinearMap.ker (rho c - 1)) = 16 := by
    rw [hRho]
    exact nebeOrderThree_fixedRank16
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  refine ⟨c, orderOf_eq_prime_iff.mpr ⟨?_, ?_⟩, hFixed⟩
  · change (Additive.ofMul (c ^ 3)) = (0 : Additive SL47)
    apply hFaithful
    rw [show Additive.ofMul (c ^ 3) = 3 • Additive.ofMul c from rfl, map_nsmul, map_zero]
    change 3 • mu c = 0
    rw [hc]
    apply AddEquiv.ext
    intro a
    have hEnd : (A.toLin' : Module.End ℤ (Fin 48 → ℤ)) ^ 3 = 1 := by
      rw [← Matrix.toLin'_pow, hCube, Matrix.toLin'_one]
      rfl
    exact congrArg (fun f : Module.End ℤ (Fin 48 → ℤ) => f a) hEnd
  · intro h
    have hIdentity : rho c = 1 := by rw [h, map_one]
    have hDim : finrank ℝ (Fin D.rank → ℝ) = 48 := by simp [D]
    rw [hIdentity, sub_self, LinearMap.ker_zero, finrank_top, hDim] at hFixed
    norm_num at hFixed

/-- A type-zero finite conformal action on the actual P48q lattice carrier
fixes two independent weight-two vectors, one of them the conformal vector.

The supplied lowest weight is that of the twisted module of the indicated
actual carrier automorphism. In Gemünden–Keller (arXiv:1909.09626,
Appendix C.3 and Theorems 6.3–6.4), a standard lift fixes the ground vectors
of the fixed charges and has a zero-momentum ground contribution. Each
nontrivial order-three eigenvalue has multiplicity `(rank - fixedRank) / 2`,
giving the stated specialization of equation (113). The type-zero premise
is the vanishing cyclic residue in their equation (24).
The Gram comparison is in the basis of Nebe's saved integral certificates. -/
theorem p48q_type_zero_fixed_weight_two
    (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hRootless : ∀ a : Charge D, bilinear D a a ≠ 2)
    (hRank : D.rank = 48)
    (hNebeGram : ∀ i j : Fin D.rank,
      D.G i j = nebeGram (Fin.cast hRank i) (Fin.cast hRank j))
    (mu : Additive SL47 →+ AddAut (Charge D)) (hFaithful : Function.Injective mu)
    (hIsometry : ∀ s a b, bilinear D (mu s a) (mu s b) = bilinear D a b)
    (hExhaustive : ∀ s : AddAut (Charge D),
      (∀ a b, bilinear D (s a) (s b) = bilinear D a b) → ∃ k, mu k = s)
    (rho : Representation ℝ SL47 (Fin D.rank → ℝ))
    (hReal : ∀ s, rho s = (realChargeAction D (mu s)).toLinearMap)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)
    {G : Type*} [Group G] [Finite G]
    (U : G →* (Carrier D ≃ₗ[ℂ] Carrier D))
    (hMode : ∀ g, PreservesModes D (U g))
    (hConformal : ∀ g, U g (omega D H) = omega D H)
    (lowest : (Carrier D ≃ₗ[ℂ] Carrier D) → ℚ)
    (hStandardLiftLowestWeight : ∀ (g : G) (s : SL47),
      orderOf (U g) = 3 → orderOf s = 3 →
      (∀ a : Charge D,
        U g (Finsupp.single a 1) ∈ ℂ ∙ Finsupp.single (mu s a) (1 : Oscillator D)) →
      (∀ a : Charge D, mu s a = a → U g (Finsupp.single a 1) = Finsupp.single a 1) →
      lowest (U g) = ((D.rank : ℚ) -
        (finrank ℝ (LinearMap.ker (rho s - 1)) : ℚ)) / 18)
    (hTypeZero : ∀ g : G, orderOf (U g) = 3 →
      ∃ z : ℤ, (3 : ℚ)^2 * lowest (U g) = (z : ℚ) ∧ (z : ZMod 3) = 0) :
    ∃ v : Carrier D, omega D H ∈ grade D 2 ∧ v ∈ grade D 2 ∧
      ((Y D (omega D H))[[1]]) (omega D H) = (2 : ℂ) • omega D H ∧
      ((Y D (omega D H))[[1]]) v = (2 : ℂ) • v ∧
      (∀ g, U g (omega D H) = omega D H ∧ U g v = v) ∧
      LinearIndependent ℂ ![v, omega D H] := by
  have hGH := mul_eq_one_comm.mp hHG
  obtain ⟨pi, eta, hGround⟩ :=
    Automorphisms.ConformalGroundTransport.conformal_ground_projection D hPos hRootless H hHG
      mu hFaithful hExhaustive U hMode hConformal
  obtain ⟨i, hi, hNeg⟩ := inversion_witness D hRank mu hFaithful hExhaustive
  obtain ⟨c, hc, hFixed⟩ := order_three_witness D hRank hNebeGram
    mu hFaithful hExhaustive rho hReal
  have hPiOfIdentity (g : G) (hg : U g = 1) : pi g = 1 := by
    change Additive.ofMul (pi g) = (0 : Additive SL47)
    apply hFaithful
    rw [map_zero]
    apply AddEquiv.ext
    intro a
    change mu (pi g) a = a
    by_contra hne
    have he := congrArg (fun v : Carrier D => v a) (hGround g a)
    simp [hg, hne] at he
  have hLowest (g : G) (hg : orderOf (U g) = 3)
      (hStd : ∀ a, mu (pi g) a = a → eta g a = 1) :
      lowest (U g) = ((D.rank : ℚ) -
        (finrank ℝ (LinearMap.ker (rho (pi g) - 1)) : ℚ)) / 18 := by
    have hFixedGround (a : Charge D) (ha : mu (pi g) a = a) :
        U g (ground D a) = ground D a := by
      rw [hGround g a, hStd a ha, Units.val_one, one_smul, ha]
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    obtain ⟨hPow, hNe⟩ := orderOf_eq_prime_iff.mp hg
    have hPiPow : pi g ^ 3 = 1 := by
      rw [← map_pow]
      exact hPiOfIdentity (g ^ 3) (by rwa [map_pow])
    have hPiNe : pi g ≠ 1 := by
      intro hId
      have hMu : mu (pi g) = 0 := by rw [hId]; exact mu.map_zero
      have hFixAll (a : Charge D) : mu (pi g) a = a := by rw [hMu]; rfl
      have hU := eq_diagonal D (U g) (hMode g) (fun _ => 1) (fun a => by
        simpa using hFixedGround a (hFixAll a))
      have hOne := eq_diagonal D 1 (by intro u n v; rfl) (fun _ => 1)
        (fun a => by simp)
      exact hNe (hU.trans hOne.symm)
    apply hStandardLiftLowestWeight g (pi g) hg (orderOf_eq_prime_iff.mpr ⟨hPiPow, hPiNe⟩)
    · intro a
      rw [hGround g a]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · exact hFixedGround
  rcases P48qFiniteActionObstruction.p48q_finite_action_dichotomy
      D pi mu rho hReal U eta hGround hMode hIsometry hPos hRank
      i c hi hNeg hc hFixed lowest hLowest with
    ⟨H', v, _, hInv, hGrade, hv, hEig, hvEig, hFix, hLI⟩ | hAnomaly
  · have hEq : H' = H := by
      calc
        H' = H' * (gramComplex D * H) := by rw [hGH, mul_one]
        _ = H := by rw [← mul_assoc, hInv, one_mul]
    subst H'
    exact ⟨v, hGrade, hv, hEig, hvEig, hFix, hLI⟩
  · obtain ⟨g, t, hg, _, _, _, _, _, _, _, hTypeOne⟩ := hAnomaly
    obtain ⟨z, hz, hZero⟩ := hTypeZero g hg
    have hOne := hTypeOne z hz
    exfalso
    exact zero_ne_one (hZero.symm.trans hOne)

#print axioms p48q_type_zero_fixed_weight_two
#check @p48q_type_zero_fixed_weight_two

end
end D5.S3.VertexAlgebra.Lattice.P48qPhysicalActionObstruction
