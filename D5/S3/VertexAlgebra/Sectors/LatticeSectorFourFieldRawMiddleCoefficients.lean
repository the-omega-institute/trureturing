/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldRawMiddleCoefficients
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldRawMiddleCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual middle four-field reconstruction from the original numerator. -/
import D5.S3.VertexAlgebra.Sectors.LatticeSectorFourFieldMiddleSpectator
import D5.S3.VertexAlgebra.FormalSeries.FourFieldMiddleInverseCoefficients

/-! The one original supplier chooses k before delta,w and retains the same
a,P and all six pair localities, four original truncations, twenty-four
labelled products and the earlier actual inner and middle identities.
Bakalov--Kac, Matsuo--Nagatomo and Carnahan attribution remains in suppliers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorFourFieldRawMiddleCoefficients
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticeSectorIntertwiner LatticeSectorChannelTransport
open LatticeSectorFourFieldCommonSeries LatticeSectorFourFieldInnerIterate
open LatticeSectorFourFieldMiddleSpectator
open UniformGradedLocalCorrelator UngradedLocalWordSeries
open FourFieldInnerPolynomial FourFieldMiddlePolynomial SupportedFourFieldMiddleCollision
open SupportedFourFieldMiddleInjectivity FourFieldMiddleNativeInverse
open FourFieldMiddleLaurentFiber FourFieldMiddleInverseCoefficients
open FieldNormalProductLocality (deltaEnd commutator)
noncomputable section

private theorem actual_middle_support (D : LatticeData) (α β γ η δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (q : Sector D η)
    (w : Sector D δ) (Y : ℕ)
    (hq : ∀ n : ℤ,(Y : ℤ)≤n → canonical D η δ q n w=0) :
    MiddleSupport (fun e => middleIterate D α β γ η δ u v t q w
      (e 0) (e 1) (e 2) (e 3)) := by
  obtain ⟨B,hB⟩ := canonical_truncation D β γ v t
  refine ⟨⟨B.toNat,?_⟩,?_,?_⟩
  · intro x b z y h
    change middleIterate D α β γ η δ u v t q w x b z y = 0
    unfold middleIterate
    rw [hB (-b-1) (by omega)]
    simp only [map_zero,Pi.zero_apply,LinearMap.zero_apply]
  · intro b
    refine ⟨Y,?_⟩
    intro x z y h
    change middleIterate D α β γ η δ u v t q w x b z y = 0
    unfold middleIterate
    rw [hq (-y-1) (by omega),map_zero,map_zero]
  · intro b y
    obtain ⟨Z,hZ⟩ := canonical_truncation D (β+γ) (η+δ)
      (canonical D β γ v (-b-1) t) (canonical D η δ q (-y-1) w)
    refine ⟨Z.toNat,?_⟩
    intro x z h
    change middleIterate D α β γ η δ u v t q w x b z y = 0
    unfold middleIterate
    rw [hZ (-z-1) (by omega),map_zero]

theorem actual_four_field_raw_middle_coefficients
    (D : LatticeData) (α β γ η : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (q : Sector D η) :
    let c : Fin 4 → Charge D := ![α,β,γ,η]
    let s : Fin 4 → Oscillator D := ![u,v,t,q]
    ∃ k : ℕ,
      (∀ i j : Fin 4, i < j →
        (deltaEnd ^ k) (commutator (labelledFields D c s i) (labelledFields D c s j)) = 0) ∧
      ∀ (δ : Charge D) (w : Sector D δ), ∃ a : Fin 4 → ℕ,
        ∃ P : MvPowerSeries (Fin 4) (Oscillator D),
        (∀ (i : Fin 4) (n : ℤ), (a i : ℤ) ≤ n → canonical D (c i) δ (s i) n w = 0) ∧
        (∀ (i j l m : Fin 4), ([0,1,2,3] : List (Fin 4)).Perm [i,j,l,m] →
          ∀ e : Exponent 4,
            polynomialAction (clearingPolynomial 4 k) (nestedCanonical D c s δ w i j l m)
              (fun n => e n - a n) = signedExtend P e) ∧
        (∀ e : Exponent 4,
          polynomialAction (innerPolynomial k a)
            (fun d => innerIterate D α β γ η δ u v t q w (d 0) (d 1) (d 2) (d 3)) e =
              signedExtend (MvPowerSeries.subst
                (SupportedFourFieldCollision.fourInnerArguments (Oscillator D)) P) e) ∧
        (∀ e : Exponent 4,
          polynomialAction (middlePolynomial k a)
            (fun d => middleIterate D α β γ η δ u v t q w (d 0) (d 1) (d 2) (d 3)) e =
              signedExtend (MvPowerSeries.subst (middleFourArguments (Oscillator D)) P) e) ∧
        ∀ e : Exponent 4,
          middleIterate D α β γ η δ u v t q w (e 0) (e 1) (e 2) (e 3) =
            middleCoefficient (MvPowerSeries.subst (middleFourArguments (Oscillator D)) P) k a e := by
  classical
  dsimp only
  obtain ⟨k,locality,rest⟩ := actual_four_field_middle_spectator_transport D α β γ η u v t q
  refine ⟨k,locality,?_⟩
  intro δ w
  obtain ⟨a,P,truncation,allOrders,inner,middle⟩ := rest δ w
  let N := MvPowerSeries.subst (middleFourArguments (Oscillator D)) P
  let F : Distribution 4 (Oscillator D) := fun e =>
    middleIterate D α β γ η δ u v t q w (e 0) (e 1) (e 2) (e 3)
  have equal : F=rawMiddleCoefficient N k a := by
    apply middle_injective k a _ _
      (actual_middle_support D α β γ η δ u v t q w (a 3) (truncation 3))
      (raw_middle_support N k a)
    funext e
    exact (middle e).trans (raw_middle_action N k a e).symm
  refine ⟨a,P,truncation,allOrders,inner,middle,?_⟩
  intro e
  exact (congrFun equal e).trans (raw_middle_coefficients N k a e)

set_option pp.proofs false in
#print actual_four_field_raw_middle_coefficients
#print axioms actual_four_field_raw_middle_coefficients
end
end D5.S3.VertexAlgebra.LatticeSectorFourFieldRawMiddleCoefficients
