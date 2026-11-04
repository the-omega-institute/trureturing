/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorRawBalancedCoefficients
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorRawBalancedCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual raw balanced finite-fiber reconstruction with the original numerator. -/
import D5.S3.VertexAlgebra.Sectors.LatticeSectorThreeFieldBalancedTransport
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldBalancedInverseCoefficients
import Batteries.Tactic.OpenPrivate

/-! The original locality, truncation, six product laws and preceding channel
facts retain their original witnesses. Balanced reconstruction cancels the
literal finite polynomial on the real supported channel. Bakalov--Kac,
Matsuo--Nagatomo and Carnahan attributions and normalization remain in suppliers.
proof_shape: actual_three_field_raw_balanced_coefficients: content
admission_basis: escape-witness
escape_witness: supported balanced cancellation and a finite three-index native
inverse recover the actual channel at every signed target for infinite P. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorRawBalancedCoefficients
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticeSectorIntertwiner LatticeSectorChannelTransport LatticeSectorThreeFieldCommonSeries
open LatticeSectorThreeFieldInnerIterate LatticeSectorBalancedBorcherds
open LatticeSectorThreeFieldBalancedTransport
open UniformGradedLocalCorrelator UngradedLocalWordSeries
open SupportedThreeFieldCollision SupportedBalancedCollision SupportedFinalRInjectivity
open ThreeFieldInnerPolynomial ThreeFieldInnerLaurentFiber
open ThreeFieldBalancedPolynomial ThreeFieldBalancedNativeInverse
open ThreeFieldBalancedLaurentFiber ThreeFieldBalancedInverseCoefficients
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators VertexOperator
noncomputable section
open private weight from D5.S3.VertexAlgebra.Sectors.LatticeSectorBalancedBorcherds

private theorem actual_balanced_action (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) :
    polynomialAction (balancedPolynomial k a)
      (fun e => balanced D α β γ δ u v t w (e 0) (e 1) (e 2)) e =
        clearedBalanced D α β γ δ u v t w k a e := by
  have ee : (![e 0, e 1, e 2] : Exponent 3) = e := by
    funext i
    fin_cases i <;> rfl
  have h := balanced_action_expansion
    (fun e => balanced D α β γ δ u v t w (e 0) (e 1) (e 2)) k a
    (e 0) (e 1) (e 2)
  simpa only [ee, clearedBalanced, clearIterate, weight,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using h

theorem actual_three_field_raw_balanced_coefficients
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
        (∀ x b z : ℤ,
          innerIterate D α β γ δ u v t w x b z =
            ∑ i ∈ innerFiber k a x b z, innerWeight k a i •
              signedExtend (innerCollision P) (innerInput k a x b z i) ) ∧
        (∃ S Z : ℕ,
          (∀ s x z : ℤ, s < -(S : ℤ) → balanced D α β γ δ u v t w s x z = 0) ∧
          (∀ s x z : ℤ, z < -(Z : ℤ) → balanced D α β γ δ u v t w s x z = 0)) ∧
        (∀ e : Exponent 3,
          clearedBalanced D α β γ δ u v t w k a e =
            signedExtend (balancedCollision P) e) ∧
        (∀ e : Exponent 3,
          polynomialAction (balancedPolynomial k a)
            (fun e => balanced D α β γ δ u v t w (e 0) (e 1) (e 2)) e =
              signedExtend (balancedCollision P) e) ∧
        ∀ s x z : ℤ,
          balanced D α β γ δ u v t w s x z =
            ∑ i ∈ balancedFiber k a s x z, balancedWeight k a i •
              signedExtend (balancedCollision P) (balancedInput k a s x z i) := by
  classical
  dsimp only
  obtain ⟨k, locality, rest⟩ := actual_three_field_balanced_transport D α β γ u v t
  refine ⟨k, locality, ?_⟩
  intro δ w
  obtain ⟨a, P, truncation, six, innercleared, inneraction, innerraw, support, cleared⟩ := rest δ w
  let F : Distribution 3 (Oscillator D) :=
    fun e => balanced D α β γ δ u v t w (e 0) (e 1) (e 2)
  have hF : NestedSupport (balancedRotate F) := by
    obtain ⟨S, Z, hs, hz⟩ := support
    constructor
    · refine ⟨S, ?_⟩
      intro s z x h
      exact hs s x z h
    · intro s
      refine ⟨Z, ?_⟩
      intro z x h
      exact hz s x z h
  have action (e : Exponent 3) : polynomialAction (balancedPolynomial k a) F e =
      signedExtend (balancedCollision P) e :=
    (actual_balanced_action D α β γ δ u v t w k a e).trans (cleared e)
  have eq : F = rawBalancedCoefficient (balancedCollision P) k a := by
    apply balanced_injective k a _ _ hF (raw_balanced_support _ k a)
    funext e
    exact (action e).trans (raw_balanced_action _ k a e).symm
  refine ⟨a, P, truncation, six, innercleared, inneraction, innerraw,
    support, cleared, action, ?_⟩
  intro s x z
  exact (congrFun eq ![s, x, z]).trans
    (raw_balanced_coefficients (balancedCollision P) k a ![s, x, z])

#print actual_three_field_raw_balanced_coefficients
#print axioms actual_three_field_raw_balanced_coefficients
end
end D5.S3.VertexAlgebra.LatticeSectorRawBalancedCoefficients
