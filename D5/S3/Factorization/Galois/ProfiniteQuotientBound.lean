/- GID: D5/S3/Factorization/Galois/ProfiniteQuotientBound
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/ProfiniteQuotientBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform bounds on continuous finite quotients make closed normal quotients finite. -/
import D5.S3.Factorization.Galois.ProfinitePowerTransfer
import Mathlib.Data.Nat.Find

set_option autoImplicit false

open D5.S3.Factorization.Galois.NormalCorePower
  D5.S3.Factorization.Galois.PowerCompactness
  D5.S3.Factorization.Galois.ProfinitePowerTransfer

namespace D5.S3.Factorization.Galois.ProfiniteQuotientBound

universe u

/-- Restricted Burnside's finite order-bound input, stated as an ordinary proposition.
It concerns finite groups with at most `d` generators and exponent dividing `m`. -/
def FiniteExponentBound (d m B : ℕ) : Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q], GeneratedByAtMost Q d →
    (∀ q : Q, q ^ m = 1) → Nat.card Q ≤ B

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A closed normal subgroup has finite quotient if the orders of all its continuous finite
quotients are uniformly bounded. We maximize the bounded indices, then use finite-quotient
separation of the closed subgroup. No topology is assigned to an abstract finite quotient. -/
theorem closed_normal_finite_quotient_of_bound (P : Subgroup G) [P.Normal]
    (hP : IsClosed (P : Set G)) (B : ℕ)
    (hbound : ∀ N : OpenNormalSubgroup G, P ≤ N.toSubgroup → N.toSubgroup.index ≤ B) :
    Finite (G ⧸ P) := by
  classical
  let T : OpenNormalSubgroup G := { toSubgroup := ⊤, isOpen' := isOpen_univ }
  let R : ℕ → Prop := fun k => ∃ N : OpenNormalSubgroup G,
    P ≤ N.toSubgroup ∧ N.toSubgroup.index = k
  have hR : R T.toSubgroup.index := ⟨T, le_top, rfl⟩
  obtain ⟨N, hPN, hNi⟩ := Nat.findGreatest_spec (hbound T le_top) hR
  have hmax (M : OpenNormalSubgroup G) (hPM : P ≤ M.toSubgroup) :
      M.toSubgroup.index ≤ N.toSubgroup.index := by
    rw [hNi]
    exact Nat.le_findGreatest (hbound M hPM) ⟨M, hPM, rfl⟩
  have hleast (M : OpenNormalSubgroup G) (hPM : P ≤ M.toSubgroup) :
      N.toSubgroup ≤ M.toSubgroup := by
    let V : OpenNormalSubgroup G := N ⊓ M
    have hPV : P ≤ V.toSubgroup := le_inf hPN hPM
    have : V.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hVN : V.toSubgroup ≤ N.toSubgroup := inf_le_left
    have heq : V.toSubgroup = N.toSubgroup := by
      by_contra hne
      exact (not_lt_of_ge (hmax V hPV))
        (Subgroup.index_strictAnti (lt_of_le_of_ne hVN hne))
    rw [← heq]
    exact inf_le_right
  have hNP : N.toSubgroup ≤ P := by
    intro g hg
    apply mem_closed_of_finite_quotients (P : Set G) hP g
    intro U
    let M : OpenNormalSubgroup G :=
      { toSubgroup := P ⊔ U.toSubgroup
        isOpen' := Subgroup.isOpen_mono le_sup_right U.toOpenSubgroup.isOpen }
    have hgM : g ∈ P ⊔ U.toSubgroup := hleast M le_sup_left hg
    obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup_of_normal_right.mp hgM
    refine ⟨x, hx, (QuotientGroup.mk'_eq_mk' U.toSubgroup).mpr ?_⟩
    refine ⟨y⁻¹, U.toSubgroup.inv_mem hy, ?_⟩
    rw [← hxy, mul_assoc, mul_inv_cancel, mul_one]
  have heq : P = N.toSubgroup := le_antisymm hPN hNP
  rw [heq]
  infer_instance

/-- The restricted Burnside order bound transfers through the now-closed power subgroup.
The finite quotients have exponent dividing `m` by the algebraic universal property. -/
theorem finite_power_quotient_of_exponent_bound (S : Finset G)
    (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤) (m B : ℕ)
    (hclosed : IsClosed (powerSubgroup G m : Set G))
    (hbound : FiniteExponentBound.{u} S.card m B) :
    Finite (G ⧸ powerSubgroup G m) := by
  apply closed_normal_finite_quotient_of_bound (powerSubgroup G m) hclosed B
  intro N hPN
  exact hbound (G ⧸ N.toSubgroup) (finite_quotient_generated S hS N)
    ((powerSubgroup_le_iff m N.toSubgroup).mp hPN)

/-- The two finite-group inputs imply power-subgroup openness. Both inputs are hypotheses,
and neither is assumed to assert openness or strong completeness. -/
theorem isOpen_powerSubgroup_of_finite_inputs (S : Finset G)
    (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤) (m w B : ℕ)
    (hwidth : FinitePowerWidth.{u} S.card m w)
    (hbound : FiniteExponentBound.{u} S.card m B) :
    IsOpen (powerSubgroup G m : Set G) := by
  have hclosed := isClosed_powerSubgroup_of_finite_width S hS m w hwidth
  exact isOpen_powerSubgroup_of_closed_finite m hclosed
    (finite_power_quotient_of_exponent_bound S hS m B hclosed hbound)

/-- Arbitrary finite-index subgroups are open, conditional solely on finite-group width and
order-bound inputs at the positive normal-core index. -/
theorem finiteIndex_isOpen_of_finite_inputs (S : Finset G)
    (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤)
    (H : Subgroup G) [H.FiniteIndex] (w B : ℕ)
    (hwidth : FinitePowerWidth.{u} S.card H.normalCore.index w)
    (hbound : FiniteExponentBound.{u} S.card H.normalCore.index B) :
    IsOpen (H : Set G) := by
  exact Subgroup.isOpen_mono ((powerSubgroup_le_normalCore H).trans H.normalCore_le)
    (isOpen_powerSubgroup_of_finite_inputs S hS H.normalCore.index w B hwidth hbound)

end D5.S3.Factorization.Galois.ProfiniteQuotientBound
