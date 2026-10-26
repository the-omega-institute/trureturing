/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldMiddleSpectator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldMiddleSpectator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual middle spectator transport with the original four-field numerator. -/
import D5.S3.VertexAlgebra.Sectors.LatticeSectorFourFieldInnerIterate
import D5.S3.VertexAlgebra.Sectors.LatticeSectorThreeFieldBalancedTransport
import D5.S3.VertexAlgebra.FormalSeries.FourFieldMiddlePolynomial
import D5.S3.VertexAlgebra.FormalSeries.SupportedFourFieldMiddleCollision
import Batteries.Tactic.OpenPrivate

/-! The original canonical normalization and Bakalov--Kac,
Matsuo--Nagatomo and Carnahan attributions are preserved.
The middle and inner channels share all original four-field witnesses.
proof_shape: actual_four_field_middle_spectator_transport: content
admission_basis: escape-witness
escape_witness: finite spectator recombination of the original balanced
Borcherds residue with a uniform active-coordinate cutoff identifies the
same four-variable numerator on the original u,q slice.
No cutoff on a fused state or a varying q-mode input is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorFourFieldMiddleSpectator
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticeSectorIntertwiner LatticeSectorChannelTransport
open LatticeSectorFourFieldCommonSeries LatticeSectorFourFieldInnerIterate
open LatticeSectorBalancedBorcherds
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedChannelSeries
open FourFieldInnerPolynomial FourFieldMiddlePolynomial SupportedFourFieldMiddleCollision
open SupportedBalancedCollision
open StateFieldResidueReconstruction (integerBinomial)
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators VertexOperator
noncomputable section
open private finite_first cross_lower from
  D5.S3.VertexAlgebra.Sectors.LatticeSectorThreeFieldBalancedTransport

/-- Actual u_x((v_b t)_z(q_y w)), with true input charges and signed modes. -/
def middleIterate (D : LatticeData) (α β γ η δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (q : Sector D η)
    (w : Sector D δ) (x b z y : ℤ) : Oscillator D :=
  canonical D α ((β + γ) + (η + δ)) u (-x - 1)
    (canonical D (β + γ) (η + δ) (canonical D β γ v (-b - 1) t) (-z - 1)
      (canonical D η δ q (-y - 1) w))

private theorem core_finite (D : LatticeData) (β γ η δ : Charge D)
    (v : Sector D β) (t : Sector D γ) (q : Sector D η) (w : Sector D δ)
    (k : ℕ) (A : Fin 3 → ℕ)
    (lvq : (deltaEnd ^ k) (commutator (Y D (inclusion D β v)) (Y D (inclusion D η q))) = 0)
    (ltq : (deltaEnd ^ k) (commutator (Y D (inclusion D γ t)) (Y D (inclusion D η q))) = 0)
    (hv : ∀ n : ℤ, (A 0 : ℤ) ≤ n → canonical D β δ v n w = 0)
    (ht : ∀ n : ℤ, (A 1 : ℤ) ≤ n → canonical D γ δ t n w = 0)
    (e : Exponent 3) :
    clearedBalanced D β γ η δ v t q w k A e =
      ∑ i ∈ Finset.range ((e 1).toNat + 1),
        (((-1 : ℂ)^i) * integerBinomial ((k : ℤ) - e 0 - 1) i) •
          balancedCross k (LatticeSectorThreeFieldCommonSeries.nestedCanonical
            D ![β,γ,η] ![v,t,q] δ w 0 1 2)
            (e 0 - A 0 - k + i) (e 1 - A 1 - i) (e 2 - A 2) := by
  rw [finite_first D β γ η δ v t q w k A lvq hv]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra hout
  apply hi
  have large : e 1 < i := by
    simp only [Finset.mem_coe,Finset.mem_range,not_lt] at hout
    omega
  dsimp only
  rw [cross_lower D β γ η δ v t q w k (A 1) ltq ht _ _ _ (by omega),smul_zero]

private theorem middle_lower (D : LatticeData) (α β γ η δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (q : Sector D η)
    (w : Sector D δ) (k B : ℕ)
    (ltq : (deltaEnd ^ k) (commutator (Y D (inclusion D γ t)) (Y D (inclusion D η q))) = 0)
    (ht : ∀ n : ℤ, (B : ℤ) ≤ n → canonical D γ δ t n w = 0)
    (x v0 t0 y : ℤ) (h : t0 < -(B : ℤ)) :
    middleCross k (nestedCanonical D ![α,β,γ,η] ![u,v,t,q] δ w 0 1 2 3) x v0 t0 y = 0 := by
  classical
  unfold middleCross
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro r hr
  apply Finset.sum_eq_zero
  intro s hs
  have cutoff : ∀ n : ℤ, ((B+r : ℕ) : ℤ) ≤ n → canonical D γ δ t n w = 0 := by
    intro n hn
    apply ht n
    omega
  have low := cross_lower D β γ η δ v t q w k (B+r) ltq cutoff
    (v0-p) (t0-r) (y-s) (by omega)
  let L : Oscillator D →ₗ[ℂ] Oscillator D :=
    canonical D α (β+(γ+(η+δ))) u (-(x-3*k+p+r+s)-1)
  have mapped := congrArg (fun z : Oscillator D =>
    weight k p • (weight k r • (weight k s • L z))) low
  simp only [balancedCross,map_sum,map_smul,map_zero,Finset.smul_sum,smul_zero] at mapped
  exact mapped

set_option maxHeartbeats 2000000 in
private theorem finite_spectator_reconstruction
    (D : LatticeData) (α β γ η δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (q : Sector D η)
    (w : Sector D δ) (k : ℕ) (a : Fin 4 → ℕ)
    (lvq : (deltaEnd ^ k) (commutator (Y D (inclusion D β v)) (Y D (inclusion D η q))) = 0)
    (ltq : (deltaEnd ^ k) (commutator (Y D (inclusion D γ t)) (Y D (inclusion D η q))) = 0)
    (hv : ∀ n : ℤ, (a 1 : ℤ) ≤ n → canonical D β δ v n w = 0)
    (ht : ∀ n : ℤ, (a 2 : ℤ) ≤ n → canonical D γ δ t n w = 0)
    (e : Exponent 4) :
    middleClearing k a (fun d => middleIterate D α β γ η δ u v t q w (d 0) (d 1) (d 2) (d 3)) e =
      ∑ i ∈ Finset.range ((e 2).toNat+1),
        (((-1 : ℂ)^i) * integerBinomial ((k : ℤ)-e 1-1) i) •
          middleCross k (nestedCanonical D ![α,β,γ,η] ![u,v,t,q] δ w 0 1 2 3)
            (e 0-a 0) (e 1-a 1-k+i) (e 2-a 2-i) (e 3-a 3) := by
  classical
  have hv' (p : ℕ) : ∀ n : ℤ, ((a 1+p : ℕ) : ℤ) ≤ n →
      canonical D β δ v n w = 0 := by
    intro n hn
    apply hv n
    simp only [Nat.cast_add] at hn
    omega
  have ht' (r : ℕ) : ∀ n : ℤ, ((a 2+r : ℕ) : ℤ) ≤ n →
      canonical D γ δ t n w = 0 := by
    intro n hn
    apply ht n
    simp only [Nat.cast_add] at hn
    omega
  have core (p r s : ℕ) := core_finite D β γ η δ v t q w k
    ![a 1+p,a 2+r,a 3+s] lvq ltq (hv' p) (ht' r) ![e 1,e 2,e 3]
  have mapped (p r s : ℕ) :
      (∑ j ∈ Finset.range (k+1), ∑ l ∈ Finset.range (k+1),
        weight k j • (weight k l •
          clearIterate k (a 1+p+k-j) (a 2+r+k-l)
            (fun b z => middleIterate D α β γ η δ u v t q w
              (e 0-a 0-3*k+p+r+s) b z (e 3-a 3-s-j-l)) (e 1) (e 2))) =
      ∑ i ∈ Finset.range ((e 2).toNat+1),
        (((-1 : ℂ)^i) * integerBinomial ((k : ℤ)-e 1-1) i) •
          canonical D α (β+(γ+(η+δ))) u (-(e 0-a 0-3*k+p+r+s)-1)
            (balancedCross k (LatticeSectorThreeFieldCommonSeries.nestedCanonical
              D ![β,γ,η] ![v,t,q] δ w 0 1 2)
              (e 1-(a 1+p : ℕ)-k+i) (e 2-(a 2+r : ℕ)-i) (e 3-(a 3+s : ℕ))) := by
    let L : Oscillator D →ₗ[ℂ] Oscillator D :=
      canonical D α (β+(γ+(η+δ))) u (-(e 0-a 0-3*k+p+r+s)-1)
    have h := congrArg L (core p r s)
    simp only [map_sum,map_smul] at h
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons,L] at h
    refine Eq.trans ?_ h
    simp only [clearedBalanced,clearIterate,map_sum,map_smul]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    apply congrArg (fun z : Oscillator D => weight k j • (weight k l • z))
    apply Finset.sum_congr rfl
    intro h hh
    apply congrArg (fun z : Oscillator D => ((a 1+p+k-j).choose h : ℂ) • z)
    dsimp only [middleIterate,balanced,L]
    rw [← add_assoc β γ (η+δ)]
    have hy : e 3-((a 3+s : ℕ) : ℤ)-j-l = e 3-a 3-s-j-l := by
      simp only [Nat.cast_add]
      omega
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons,hy]
  unfold middleClearing
  change (∑ p ∈ Finset.range (k+1), ∑ r ∈ Finset.range (k+1),
    ∑ s ∈ Finset.range (k+1), weight k p • (weight k r • (weight k s •
      (∑ j ∈ Finset.range (k+1), ∑ l ∈ Finset.range (k+1),
        weight k j • (weight k l •
          clearIterate k (a 1+p+k-j) (a 2+r+k-l)
            (fun b z => middleIterate D α β γ η δ u v t q w
              (e 0-a 0-3*k+p+r+s) b z (e 3-a 3-s-j-l)) (e 1) (e 2)))))) = _
  simp_rw [mapped,Finset.smul_sum]
  simp_rw [Finset.sum_comm (s := Finset.range (k+1)) (t := Finset.range ((e 2).toNat+1))]
  apply Finset.sum_congr rfl
  intro i hi
  unfold middleCross
  simp only [balancedCross,Finset.smul_sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  have base : canonical D α (β+(γ+(η+δ))) u (-(e 0-a 0-3*k+p+r+s)-1)
      (LatticeSectorThreeFieldCommonSeries.nestedCanonical D ![β,γ,η] ![v,t,q] δ w 0 1 2
        ![e 1-(a 1+p : ℕ)-k+i-k+j,e 2-(a 2+r : ℕ)-i-k+l,e 3-(a 3+s : ℕ)-j-l]) =
      nestedCanonical D ![α,β,γ,η] ![u,v,t,q] δ w 0 1 2 3
        ![e 0-a 0-3*k+p+r+s,e 1-a 1-k+i-p-k+j,e 2-a 2-i-r-k+l,e 3-a 3-s-j-l] := by
    have idx : (![e 1-(a 1+p : ℕ)-k+i-k+j,
        e 2-(a 2+r : ℕ)-i-k+l,e 3-(a 3+s : ℕ)-j-l] : Exponent 3) =
        ![e 1-a 1-k+i-p-k+j,e 2-a 2-i-r-k+l,e 3-a 3-s-j-l] := by
      funext d
      fin_cases d <;> simp [Nat.cast_add] <;> omega
    rw [idx]
    rfl
  simp only [Nat.cast_add] at base ⊢
  rw [base]
  simp only [smul_smul,weight]
  congr 1
  ring

/-- All original witnesses and the previous inner action are retained. -/
theorem actual_four_field_middle_spectator_transport
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
        ∀ e : Exponent 4,
          polynomialAction (middlePolynomial k a)
            (fun d => middleIterate D α β γ η δ u v t q w (d 0) (d 1) (d 2) (d 3)) e =
              signedExtend (MvPowerSeries.subst (middleFourArguments (Oscillator D)) P) e := by
  classical
  dsimp only
  obtain ⟨k,locality,rest⟩ := actual_four_field_inner_iterate_transport D α β γ η u v t q
  refine ⟨k,locality,?_⟩
  intro δ w
  obtain ⟨a,P,truncation,allOrders,inner⟩ := rest δ w
  refine ⟨a,P,truncation,allOrders,inner,?_⟩
  have lvq : (deltaEnd ^ k) (commutator (Y D (inclusion D β v)) (Y D (inclusion D η q))) = 0 :=
    locality 1 3 (by decide)
  have ltq : (deltaEnd ^ k) (commutator (Y D (inclusion D γ t)) (Y D (inclusion D η q))) = 0 :=
    locality 2 3 (by decide)
  intro e
  let F : Distribution 4 (Oscillator D) := nestedCanonical D ![α,β,γ,η] ![u,v,t,q] δ w 0 1 2 3
  let G : ℤ → ℤ → Oscillator D := fun v t => middleCross k F (e 0-a 0) v t (e 3-a 3)
  have lower (v0 t0 : ℤ) (ht0 : t0 < -(a 2 : ℤ)) : G v0 t0 = 0 :=
    middle_lower D α β γ η δ u v t q w k (a 2) ltq (truncation 2) _ _ _ _ ht0
  have commonSlice (v0 t0 : ℤ) :
      clear k G (v0-a 1) (t0-a 2) = extend (middleSlice P (e 0) (e 3)) v0 t0 := by
    have h := allOrders 0 1 2 3 (by decide) ![e 0,v0,t0,e 3]
    rw [clearing_four_middle] at h
    change clear k G (v0-a 1) (t0-a 2) = signedExtend P ![e 0,v0,t0,e 3] at h
    exact h.trans (middleSlice_extend P (e 0) (e 3) v0 t0).symm
  have signed := SupportedThreeFieldCollision.signed_cleared_collision G k (a 1) (a 2)
    lower (middleSlice P (e 0) (e 3)) commonSlice (e 1) (e 2)
  have finiteSum :
      (∑ᶠ i : ℕ, (((-1 : ℂ)^i) * integerBinomial ((k : ℤ)-e 1-1) i) •
        G (e 1-a 1-k+i) (e 2-a 2-i)) =
      ∑ i ∈ Finset.range ((e 2).toNat+1),
        (((-1 : ℂ)^i) * integerBinomial ((k : ℤ)-e 1-1) i) •
          G (e 1-a 1-k+i) (e 2-a 2-i) := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra hout
    apply hi
    have large : e 2 < i := by
      simp only [Finset.mem_coe,Finset.mem_range,not_lt] at hout
      omega
    dsimp only
    rw [lower _ _ (by omega),smul_zero]
  rw [middle_action_expansion]
  calc
    _ = ∑ i ∈ Finset.range ((e 2).toNat+1),
        (((-1 : ℂ)^i) * integerBinomial ((k : ℤ)-e 1-1) i) •
          G (e 1-a 1-k+i) (e 2-a 2-i) :=
      finite_spectator_reconstruction D α β γ η δ u v t q w k a lvq ltq
        (truncation 1) (truncation 2) e
    _ = extend (collision (middleSlice P (e 0) (e 3))) (e 1) (e 2) := finiteSum.symm.trans signed.2
    _ = signedExtend (MvPowerSeries.subst (middleFourArguments (Oscillator D)) P)
        ![e 0,e 1,e 2,e 3] :=
      (middleCollision_signed P (e 0) (e 1) (e 2) (e 3)).symm
    _ = signedExtend (MvPowerSeries.subst (middleFourArguments (Oscillator D)) P) e := by
      congr 1
      funext i
      fin_cases i <;> rfl

set_option pp.proofs false in
#print actual_four_field_middle_spectator_transport
#print axioms actual_four_field_middle_spectator_transport
end
end D5.S3.VertexAlgebra.LatticeSectorFourFieldMiddleSpectator
