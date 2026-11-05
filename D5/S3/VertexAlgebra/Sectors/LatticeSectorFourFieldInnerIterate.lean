/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldInnerIterate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldInnerIterate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The same infinite four-field numerator clears the actual inner iterate. -/
import D5.S3.VertexAlgebra.Sectors.LatticeSectorFourFieldCommonSeries
import D5.S3.VertexAlgebra.Sectors.LatticeSectorThreeFieldInnerIterate
import D5.S3.VertexAlgebra.FormalSeries.FourFieldInnerPolynomial
import D5.S3.VertexAlgebra.FormalSeries.SupportedFourFieldCollision
import Batteries.Tactic.OpenPrivate

/-!
Original canonical fields on arbitrary oscillator descendants and lattice data.
The Bakalov--Kac, Matsuo--Nagatomo and Carnahan suppliers retain their original
normalization and attributions. Only the t,q inner collision is asserted.
proof_shape: actual_four_field_inner_iterate_transport: content
admission_basis: escape-witness
escape_witness: five finite cross-factor fibers are reconstructed using the
original t,q,w Borcherds law before both outer linear canonical modes. The
original q-on-w bound is uniform in both spectator modes. Signed common-series
cancellation on a fixed two-spectator slice identifies the same native P.
No cutoff on the varying intermediate state or enlarged locality is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorFourFieldInnerIterate
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeSectorIntertwiner LatticeAllStateField
open LatticeSectorFourFieldCommonSeries LatticeSectorChannelTransport
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedChannelSeries
open FourFieldInnerPolynomial SupportedFourFieldCollision
open StateFieldResidueReconstruction (integerBinomial)
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators VertexOperator
noncomputable section
open private outer_borcherds from
  D5.S3.VertexAlgebra.Sectors.LatticeSectorThreeFieldInnerIterate

/-- Actual u_x(v_y((t_b q)_z w)), with every mode indexed by -exponent-1
and every canonical operator carrying its true input charge. -/
def innerIterate (D : LatticeData) (α β γ η δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (q : Sector D η)
    (w : Sector D δ) (x y b z : ℤ) : Oscillator D :=
  canonical D α (β + ((γ + η) + δ)) u (-x - 1)
    (canonical D β ((γ + η) + δ) v (-y - 1)
      (canonical D (γ + η) δ (canonical D γ η t (-b - 1) q) (-z - 1) w))

private theorem two_outer_borcherds (D : LatticeData) (α β γ η δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (q : Sector D η)
    (w : Sector D δ) (k A B P Q : ℕ)
    (hA : ∀ n : ℤ, (A : ℤ) ≤ n → canonical D γ δ t n w = 0)
    (hB : ∀ n : ℤ, (B : ℤ) ≤ n → canonical D η δ q n w = 0)
    (x y b z : ℤ) :
    clearIterate k (A + P) (B + Q) (innerIterate D α β γ η δ u v t q w x y) b z =
      ∑ i ∈ Finset.range (z.toNat + 1),
        (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - b - 1) i) •
          canonical D α (β + (γ + (η + δ))) u (-x - 1)
            (canonical D β (γ + (η + δ)) v (-y - 1)
              (product D γ η δ t q w (b - A - P - k + i) (z - B - Q - i))) := by
  classical
  let L : Oscillator D →ₗ[ℂ] Oscillator D :=
    canonical D α (β + (γ + (η + δ))) u (-x - 1)
  have bor := outer_borcherds D β γ η δ v t q w k A B P Q hA hB y b z
  have mapped := congrArg L bor
  simp only [map_sum, map_smul] at mapped
  have left : L (clearIterate k (A + P) (B + Q)
      (LatticeSectorThreeFieldInnerIterate.innerIterate D β γ η δ v t q w y) b z) =
      clearIterate k (A + P) (B + Q)
        (innerIterate D α β γ η δ u v t q w x y) b z := by
    simp only [clearIterate, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    dsimp only [LatticeSectorThreeFieldInnerIterate.innerIterate, innerIterate, iterate, L]
    rw [← add_assoc γ η δ]
  rw [left] at mapped
  exact mapped

private theorem cross_lower (D : LatticeData) (α β γ η δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (q : Sector D η)
    (w : Sector D δ) (k B : ℕ)
    (hB : ∀ n : ℤ, (B : ℤ) ≤ n → canonical D η δ q n w = 0)
    (x y b z : ℤ) (hz : z < -(B : ℤ)) :
    cross k (nestedCanonical D ![α,β,γ,η] ![u,v,t,q] δ w 0 1 2 3) x y b z = 0 := by
  classical
  unfold cross
  apply Finset.sum_eq_zero
  intro s hs
  apply Finset.sum_eq_zero
  intro r hr
  apply Finset.sum_eq_zero
  intro q0 hq0
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro h hh
  have zeroInner : canonical D η δ q (-(z - q0 - s) - 1) w = 0 := hB _ (by omega)
  change weight k h • (weight k p • (weight k q0 • (weight k r • (weight k s •
    canonical D α (β + (γ + (η + δ))) u (-(x - 3 * k + h + p + q0) - 1)
      (canonical D β (γ + (η + δ)) v (-(y - 2 * k - h + r + s) - 1)
        (canonical D γ (η + δ) t (-(b - p - r) - 1)
          (canonical D η δ q (-(z - q0 - s) - 1) w))))))) = 0
  rw [zeroInner, map_zero, map_zero, map_zero, smul_zero, smul_zero,
    smul_zero, smul_zero, smul_zero]

private theorem finite_outer_reconstruction (D : LatticeData) (α β γ η δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (q : Sector D η)
    (w : Sector D δ) (k : ℕ) (a : Fin 4 → ℕ)
    (hA : ∀ n : ℤ, (a 2 : ℤ) ≤ n → canonical D γ δ t n w = 0)
    (hB : ∀ n : ℤ, (a 3 : ℤ) ≤ n → canonical D η δ q n w = 0)
    (e : Exponent 4) :
    finiteClearing k a (fun d => innerIterate D α β γ η δ u v t q w (d 0) (d 1) (d 2) (d 3)) e =
      ∑ i ∈ Finset.range ((e 3).toNat + 1),
        (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - e 2 - 1) i) •
          cross k (nestedCanonical D ![α,β,γ,η] ![u,v,t,q] δ w 0 1 2 3)
            (e 0 - a 0) (e 1 - a 1) (e 2 - a 2 - k + i) (e 3 - a 3 - i) := by
  classical
  have bor (P Q : ℕ) (x y b z : ℤ) :=
    two_outer_borcherds D α β γ η δ u v t q w k (a 2) (a 3) P Q hA hB x y b z
  unfold finiteClearing
  change (∑ s ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k + 1),
    ∑ q0 ∈ Finset.range (k + 1), ∑ p ∈ Finset.range (k + 1),
    ∑ h ∈ Finset.range (k + 1),
      weight k h • (weight k p • (weight k q0 • (weight k r • (weight k s •
        clearIterate k (a 2 + p + r) (a 3 + q0 + s)
          (innerIterate D α β γ η δ u v t q w
            (e 0 - a 0 - 3 * k + h + p + q0)
            (e 1 - a 1 - 2 * k - h + r + s)) (e 2) (e 3)))))) = _
  simp only [show ∀ P r : ℕ, a 2 + P + r = a 2 + (P + r) by omega,
    show ∀ Q s : ℕ, a 3 + Q + s = a 3 + (Q + s) by omega]
  simp_rw [bor, Finset.smul_sum]
  simp_rw [Finset.sum_comm (s := Finset.range (k + 1))
    (t := Finset.range ((e 3).toNat + 1))]
  apply Finset.sum_congr rfl
  intro i hi
  unfold cross
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro q0 hq0
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro h hh
  have base : canonical D α (β + (γ + (η + δ))) u
      (-(e 0 - a 0 - 3 * k + h + p + q0) - 1)
      (canonical D β (γ + (η + δ)) v
        (-(e 1 - a 1 - 2 * k - h + r + s) - 1)
        (product D γ η δ t q w
          (e 2 - a 2 - (p + r) - k + i) (e 3 - a 3 - (q0 + s) - i))) =
      nestedCanonical D ![α,β,γ,η] ![u,v,t,q] δ w 0 1 2 3
        ![e 0 - a 0 - 3 * k + h + p + q0,
          e 1 - a 1 - 2 * k - h + r + s,
          e 2 - a 2 - k + i - p - r, e 3 - a 3 - i - q0 - s] := by
    change canonical D α (β + (γ + (η + δ))) u
      (-(e 0 - a 0 - 3 * k + h + p + q0) - 1)
      (canonical D β (γ + (η + δ)) v
        (-(e 1 - a 1 - 2 * k - h + r + s) - 1)
        (product D γ η δ t q w
          (e 2 - a 2 - (p + r) - k + i) (e 3 - a 3 - (q0 + s) - i))) =
      canonical D α (β + (γ + (η + δ))) u
      (-(e 0 - a 0 - 3 * k + h + p + q0) - 1)
      (canonical D β (γ + (η + δ)) v
        (-(e 1 - a 1 - 2 * k - h + r + s) - 1)
        (product D γ η δ t q w
          (e 2 - a 2 - k + i - p - r) (e 3 - a 3 - i - q0 - s)))
    congr 1
    congr 1
    congr 1 <;> omega
  simp only [Nat.cast_add]
  rw [base]
  simp only [smul_smul]
  congr 1
  ring

/-- All original truncations and all twenty-four original labelled products
are retained with the same k,a,P. The conclusion is literal polynomial action
on the actual five-state inner channel at every signed multi-index. -/
theorem actual_four_field_inner_iterate_transport
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
        ∀ e : Exponent 4,
          polynomialAction (innerPolynomial k a)
            (fun d => innerIterate D α β γ η δ u v t q w (d 0) (d 1) (d 2) (d 3)) e =
              signedExtend (MvPowerSeries.subst (fourInnerArguments (Oscillator D)) P) e := by
  classical
  dsimp only
  obtain ⟨k, locality, rest⟩ := actual_four_field_common_series D α β γ η u v t q
  refine ⟨k, locality, ?_⟩
  intro δ w
  obtain ⟨a,P,truncation,allOrders⟩ := rest δ w
  have common (e : Exponent 4) := allOrders 0 1 2 3 (by decide) e
  refine ⟨a,P,truncation,allOrders,?_⟩
  intro e
  let F : Distribution 4 (Oscillator D) :=
    nestedCanonical D ![α,β,γ,η] ![u,v,t,q] δ w 0 1 2 3
  let G : ℤ → ℤ → Oscillator D := cross k F (e 0 - a 0) (e 1 - a 1)
  have lower : ∀ x y : ℤ, y < -(a 3 : ℤ) → G x y = 0 := by
    intro x y hy
    exact cross_lower D α β γ η δ u v t q w k (a 3) (truncation 3) _ _ x y hy
  have commonSlice (x y : ℤ) :
      clear k G (x - a 2) (y - a 3) = extend (slice P (e 0) (e 1)) x y := by
    have h := common ![e 0,e 1,x,y]
    rw [clearing_four] at h
    change clear k G (x - a 2) (y - a 3) = signedExtend P ![e 0,e 1,x,y] at h
    exact h.trans (slice_extend P (e 0) (e 1) x y).symm
  have signed := SupportedThreeFieldCollision.signed_cleared_collision G k (a 2) (a 3)
    lower (slice P (e 0) (e 1)) commonSlice (e 2) (e 3)
  have finiteSum :
      (∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - e 2 - 1) i) •
        G (e 2 - a 2 - k + i) (e 3 - a 3 - i)) =
      ∑ i ∈ Finset.range ((e 3).toNat + 1),
        (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - e 2 - 1) i) •
          G (e 2 - a 2 - k + i) (e 3 - a 3 - i) := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra hout
    apply hi
    have hib : e 3 < i := by
      simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hout
      omega
    change (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - e 2 - 1) i) •
      G (e 2 - a 2 - k + i) (e 3 - a 3 - i) = 0
    rw [lower _ _ (by omega),smul_zero]
  rw [inner_action_expansion]
  calc
    _ = ∑ i ∈ Finset.range ((e 3).toNat + 1),
        (((-1 : ℂ) ^ i) * integerBinomial ((k : ℤ) - e 2 - 1) i) •
          G (e 2 - a 2 - k + i) (e 3 - a 3 - i) :=
      finite_outer_reconstruction D α β γ η δ u v t q w k a (truncation 2) (truncation 3) e
    _ = extend (collision (slice P (e 0) (e 1))) (e 2) (e 3) := finiteSum.symm.trans signed.2
    _ = signedExtend (fourInnerCollision P) ![e 0,e 1,e 2,e 3] :=
      (fourInnerCollision_signed P (e 0) (e 1) (e 2) (e 3)).symm
    _ = signedExtend (fourInnerCollision P) e := by
      congr 1
      funext i
      fin_cases i <;> rfl

set_option pp.proofs false in
#print actual_four_field_inner_iterate_transport
#print axioms actual_four_field_inner_iterate_transport
end
end D5.S3.VertexAlgebra.LatticeSectorFourFieldInnerIterate
