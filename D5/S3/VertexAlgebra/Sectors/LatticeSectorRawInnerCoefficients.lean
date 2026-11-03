/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorRawInnerCoefficients
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorRawInnerCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual raw inner coefficients from the original infinite three-field numerator. -/
import D5.S3.VertexAlgebra.Sectors.LatticeSectorThreeFieldInnerIterate
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldInnerInverseCoefficients

/-!
proof_shape: actual_three_field_raw_inner_coefficients: content
admission_basis: escape-witness
escape_witness: nested supported cancellation identifies the actual inner
channel with its finite three-index native inverse, with every signed branch
and the original numerator. The coupled kernel and finite reindexing are
proved without assuming a raw inverse or a raw substitution.

The original locality order precedes the fourth charge and state. The
same bounds and numerator retain all six signed product identities. The raw
inner reconstruction uses only the two actual canonical truncations in its
b << z << x chamber. Bakalov--Kac, Matsuo--Nagatomo and Carnahan attribution
remains in the suppliers; the canonical normalization is unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorRawInnerCoefficients
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticeSectorIntertwiner LatticeSectorChannelTransport
open LatticeSectorThreeFieldCommonSeries LatticeSectorThreeFieldInnerIterate
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision
open ThreeFieldInnerPolynomial ThreeFieldInnerNativeInverse SupportedFinalRInjectivity
open ThreeFieldInnerLaurentFiber ThreeFieldInnerInverseCoefficients
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators VertexOperator
noncomputable section

private theorem actual_inner_support (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ) :
    NestedSupport (rotate
      (fun e => innerIterate D α β γ δ u v t w (e 0) (e 1) (e 2))) := by
  obtain ⟨B, hb⟩ := canonical_truncation D β γ v t
  constructor
  · refine ⟨B.toNat, ?_⟩
    intro b z x h
    simp only [rotate, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    unfold innerIterate iterate
    rw [hb (-b - 1) (by omega)]
    simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply]
  · intro b
    obtain ⟨Z, hz⟩ := canonical_truncation D (β + γ) δ
      (canonical D β γ v (-b - 1) t) w
    refine ⟨Z.toNat, ?_⟩
    intro z x h
    simp only [rotate, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    unfold innerIterate iterate
    rw [hz (-z - 1) (by omega), map_zero]

private theorem actual_inner_action (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) :
    polynomialAction (innerPolynomial k a)
      (fun e => innerIterate D α β γ δ u v t w (e 0) (e 1) (e 2)) e =
        clearedInnerIterate D α β γ δ u v t w k a e := by
  have ee : (![e 0, e 1, e 2] : Exponent 3) = e := by
    funext i
    fin_cases i <;> rfl
  have h := inner_action_expansion k a
    (fun e => innerIterate D α β γ δ u v t w (e 0) (e 1) (e 2))
    (e 0) (e 1) (e 2)
  simpa only [ee, clearedInnerIterate, clearIterate, Nat.cast_add,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using h

/-- Raw canonical inner reconstruction with the same original witnesses. -/
theorem actual_three_field_raw_inner_coefficients
    (D : LatticeData) (α β γ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) :
    let c : Fin 3 → Charge D := ![α, β, γ]
    let s : Fin 3 → Oscillator D := ![u, v, t]
    ∃ k : ℕ,
      (∀ i j : Fin 3, i < j →
        (deltaEnd ^ k) (commutator (labelledFields D c s i) (labelledFields D c s j)) = 0) ∧
      ∀ (δ : Charge D) (w : Sector D δ), ∃ a : Fin 3 → ℕ,
        ∃ P : MvPowerSeries (Fin 3) (Oscillator D),
        (∀ (i : Fin 3) (n : ℤ), (a i : ℤ) ≤ n →
          canonical D (c i) δ (s i) n w = 0) ∧
        (∀ e : Exponent 3,
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 0 1 2)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 0 2 1)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 1 0 2)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 1 2 0)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 2 0 1)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c s δ w 2 1 0)
            (fun i => e i - a i) = signedExtend P e) ∧
        (∀ e : Exponent 3,
          clearedInnerIterate D α β γ δ u v t w k a e =
            signedExtend (innerCollision P) e) ∧
        (∀ e : Exponent 3,
          polynomialAction (innerPolynomial k a)
            (fun e => innerIterate D α β γ δ u v t w (e 0) (e 1) (e 2)) e =
              signedExtend (innerCollision P) e) ∧
        ∀ x b z : ℤ,
          innerIterate D α β γ δ u v t w x b z =
            ∑ i ∈ innerFiber k a x b z, innerWeight k a i •
              signedExtend (innerCollision P) (innerInput k a x b z i) := by
  classical
  dsimp only
  obtain ⟨k, locality, rest⟩ := actual_three_field_inner_iterate_transport D α β γ u v t
  refine ⟨k, locality, ?_⟩
  intro δ w
  obtain ⟨a, P, truncation, six, cleared⟩ := rest δ w
  let F : Distribution 3 (Oscillator D) :=
    fun e => innerIterate D α β γ δ u v t w (e 0) (e 1) (e 2)
  have action (e : Exponent 3) : polynomialAction (innerPolynomial k a) F e =
      signedExtend (innerCollision P) e :=
    (actual_inner_action D α β γ δ u v t w k a e).trans (cleared e)
  have eq : F = rawInnerCoefficient (innerCollision P) k a := by
    apply inner_injective k a _ _ (actual_inner_support D α β γ δ u v t w)
      (raw_inner_support _ k a)
    funext e
    exact (action e).trans (raw_inner_action _ k a e).symm
  refine ⟨a, P, truncation, six, cleared, action, ?_⟩
  intro x b z
  exact (congrFun eq ![x, b, z]).trans
    (raw_inner_coefficients (innerCollision P) k a ![x, b, z])

#print actual_three_field_raw_inner_coefficients
#print axioms actual_three_field_raw_inner_coefficients
end
end D5.S3.VertexAlgebra.LatticeSectorRawInnerCoefficients
