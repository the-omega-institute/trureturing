/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIITypeATransitiveSupplier
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIITypeATransitiveSupplier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Products.PartIITypeAProjectiveSupplier

/-! Original uniform Proposition10.2 interface on the COMPLETE untwisted
projective type-A family, all fields and all ranks above one group cutoff.
The newly proved uniform scalar PRODUCT and its q=1 twisted consequence
feed the accepted actual Hall-selected/typeI/typeII forest reconstruction.
Other finite-simple families and their exhaustion remain unproved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace NikolovSegal.PartIITypeATransitiveSupplier
open Matrix
universe u

/-- Actual full original prescribed VALUE coverage on arbitrary finite
nonempty factor ranks over PSLn, at one positive m(q) and C(q) BEFORE
all fields/matrix ranks/action/component tuples. All genuine coordinate
laws and q/e powers are consumed; corrections precede ALL targets.
No scalar/twisted/coverage/classification premise remains for this family. -/
theorem actual_uniform_PSLn_transitive_coverage (q : ℕ) (hq : 0<q) :
    ∃ m C : ℕ, 0<m ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F], ∀ n : ℕ,
      C<Nat.card (ProjectiveSpecialLinearGroup (Fin n) F) →
      ∀ (I : Type u) [Finite I] [Nonempty I],
      ∀ (k : Fin m → MulAut (I → ProjectiveSpecialLinearGroup (Fin n) F))
        (sigma : Fin m → Equiv.Perm I)
        (beta : Fin m → I → MulAut (ProjectiveSpecialLinearGroup (Fin n) F)),
      (∀ j z i, k j z (sigma j i)=beta j i (z i)) →
      PrescribedCommutatorCoverage (I → ProjectiveSpecialLinearGroup (Fin n) F) q m k := by
  obtain ⟨M,Cq,hM,hqscalar⟩ := PartIITypeAProjectiveSupplier.actual_uniform_PSLn_scalar_product q hq
  obtain ⟨D,C1,hD,hscalar1⟩ := PartIITypeAProjectiveSupplier.actual_uniform_PSLn_scalar_product 1 (by decide)
  let K := 4+2*D
  let m := M*K*(q+K)
  refine ⟨m,max Cq C1,?_,?_⟩
  · dsimp only [m,K]
    exact Nat.mul_pos (Nat.mul_pos hM (by omega)) (by omega)
  · intro F _ _ _ n hcard I _ _ k sigma beta hcoord
    classical
    letI : Fintype I := Fintype.ofFinite I
    have hqcard : Cq<Nat.card (ProjectiveSpecialLinearGroup (Fin n) F) :=
      (le_max_left _ _).trans_lt hcard
    have h1card : C1<Nat.card (ProjectiveSpecialLinearGroup (Fin n) F) :=
      (le_max_right _ _).trans_lt hcard
    have htwisted := twisted_input_of_scalar_one
      (fun b => hscalar1 F n h1card b (fun _ => 1))
    exact prescribed_coverage_from_published_products (M := M) (D := D) hq hM (by rfl)
      k sigma beta hcoord (hqscalar F n hqcard) htwisted
end NikolovSegal.PartIITypeATransitiveSupplier
