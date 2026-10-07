/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIILemma41
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIILemma41
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar-one correction absorption and conditional uniform supplier reduction. -/

import D5.S3.FiniteGroups.NikolovSegal.Proposition102Assembly

set_option autoImplicit false

/-! Nikolov--Segal Part II, printed pp247--248, Lemma4.1. Exact ordered
algebra: scalar commutator PRODUCT coverage implies twisted PRODUCT coverage.
The finite-simple scalar existence theorem is NOT proved by this deduction. -/
namespace NikolovSegal
open Equation47WordCoupling
universe u
variable {S : Type u} [Group S]

private theorem shift_scalar (gamma : MulAut S) (x a : S) :
    a * ((x*a)⁻¹ * gamma (x*a)) = (x⁻¹ * gamma x) * gamma a := by
  simp only [mul_inv_rev,map_mul]
  group

/-- Move all constants through the ordered scalar VALUES. The final constant
is chosen before all witnesses. No factor is commuted across another. -/
private theorem ordered_scalar_constants {d : ℕ}
    (gamma : Fin d → MulAut S) (A B : Fin d → S) :
    ∃ b : S, ∀ c : Fin d → S, ∃ z : Fin d → S,
      orderedProduct (fun j => A j * ((z j)⁻¹ * gamma j (z j)) * B j) =
        orderedProduct (fun j => (c j)⁻¹ * gamma j (c j)) * b := by
  induction d with
  | zero =>
    refine ⟨1,fun c => ⟨c,?_⟩⟩
    simp [orderedProduct]
  | succ d ih =>
    obtain ⟨b,hb⟩ := ih (fun j => gamma j.castSucc) (fun j => A j.castSucc) (fun j => B j.castSucc)
    refine ⟨gamma (Fin.last d) (b*A (Fin.last d)) * B (Fin.last d),?_⟩
    intro c
    obtain ⟨z,hz⟩ := hb (fun j => c j.castSucc)
    let z' : Fin (d+1) → S := Fin.snoc (α := fun _ => S) z (c (Fin.last d) * (b*A (Fin.last d)))
    refine ⟨z',?_⟩
    have hp : orderedProduct (fun j : Fin d => A j.castSucc *
        ((z' j.castSucc)⁻¹ * gamma j.castSucc (z' j.castSucc)) * B j.castSucc) =
        orderedProduct (fun j : Fin d => (c j.castSucc)⁻¹ * gamma j.castSucc (c j.castSucc)) * b := by
      simpa only [z',Fin.snoc_castSucc] using hz
    have hlast : z' (Fin.last d) = c (Fin.last d) * (b*A (Fin.last d)) := by simp [z']
    have hprod : ∀ f : Fin (d+1) → S, orderedProduct f =
        orderedProduct (fun j => f j.castSucc) * f (Fin.last d) := by
      intro f
      simp only [orderedProduct,List.ofFn_succ',List.prod_concat]
    rw [hprod,hprod,hp,hlast]
    have hs := shift_scalar (gamma (Fin.last d)) (c (Fin.last d)) (b*A (Fin.last d))
    simpa only [mul_assoc] using congrArg
      (fun t => orderedProduct (fun j : Fin d => (c j.castSucc)⁻¹ * gamma j.castSucc (c j.castSucc)) * t * B (Fin.last d)) hs

private theorem twisted_scalar_identity (a beta : MulAut S) (g z : S) :
    twistedValue a beta (a.symm ((beta g)⁻¹)) (z * beta g) =
      (a.symm (beta g) * (beta g)⁻¹) *
        (z⁻¹ * (beta * MulAut.conj g⁻¹) z) * ((beta g)⁻¹ * beta (beta g)) := by
  simp only [twistedValue,MulAut.mul_apply,MulAut.conj_inv_apply,mul_inv_rev,map_inv,map_mul,
    MulEquiv.apply_symm_apply,inv_inv]
  group

/-- The actual Lemma4.1 with our forward automorphism convention. Given the
corrected scalar PRODUCT witnesses, every prescribed alpha/beta tuple has
ordered twisted PRODUCT coverage. Constants and scalar corrections are fixed
before the target; the proof constructs the genuine two twisted witnesses. -/
theorem twisted_product_of_corrected_scalar {d : ℕ}
    (beta : Fin d → MulAut S) (g : Fin d → S)
    (hcover : ∀ t : S, ∃ c : Fin d → S,
      orderedProduct (fun j => (c j)⁻¹ * (beta j * MulAut.conj (g j)⁻¹) (c j)) = t)
    (a : Fin d → MulAut S) :
    ∀ t : S, ∃ xi eta : Fin d → S,
      orderedProduct (fun j => twistedValue (a j) (beta j) (xi j) (eta j)) = t := by
  let gamma := fun j => beta j * MulAut.conj (g j)⁻¹
  let A := fun j => (a j).symm (beta j (g j)) * (beta j (g j))⁻¹
  let B := fun j => (beta j (g j))⁻¹ * beta j (beta j (g j))
  obtain ⟨b,hb⟩ := ordered_scalar_constants gamma A B
  intro t
  obtain ⟨c,hc⟩ := hcover (t*b⁻¹)
  obtain ⟨z,hz⟩ := hb c
  refine ⟨fun j => (a j).symm ((beta j (g j))⁻¹),fun j => z j * beta j (g j),?_⟩
  have heq : (fun j => twistedValue (a j) (beta j)
      ((a j).symm ((beta j (g j))⁻¹)) (z j * beta j (g j))) =
      (fun j => A j * ((z j)⁻¹ * gamma j (z j)) * B j) :=
    funext (fun j => twisted_scalar_identity (a j) (beta j) (g j) (z j))
  calc
    _ = orderedProduct (fun j => A j * ((z j)⁻¹ * gamma j (z j)) * B j) := congrArg orderedProduct heq
    _ = orderedProduct (fun j => (c j)⁻¹ * gamma j (c j)) * b := hz
    _ = (t*b⁻¹)*b := congrArg (fun s => s*b) hc
    _ = t := by group

/-- Consume exactly the scalar PRODUCT theorem at q=1, including its genuine
pre-target inner corrections, to prove the twisted PRODUCT theorem at that
same length. This is the published Section4 algebra, without a CFSG premise. -/
theorem twisted_input_of_scalar_one {d : ℕ}
    (scalar : ∀ beta : Fin d → MulAut S,
      PartIIScalarProductInput 1 d beta (fun _ => 1)) :
    PartIITwistedProductInput S d := by
  intro a beta
  obtain ⟨g,hg⟩ := scalar beta (by
    change ∀ j : Fin d, 0 < (1 : ℕ) ∧ 1 ∣ 1
    intro j
    exact ⟨Nat.zero_lt_one,dvd_refl 1⟩)
  apply twisted_product_of_corrected_scalar beta g _ a
  intro t
  obtain ⟨c,hc⟩ := hg t
  exact ⟨c,by simpa only [Nat.div_one,pow_one] using hc⟩

/-- For the literal large-simple supplier, a fixed q=1 scalar length and
cutoff supply its twisted input by Lemma4.1. Taking max of the two cutoffs
avoids any small-group assumption. The SINGLE remaining unproved premise is
precisely the uniform PartII Theorem1.2 scalar PRODUCT statement. -/
theorem uniform_transitive_supplier_of_scalar_products
    (scalar : ∀ q : ℕ, 0 < q → ∃ M C : ℕ, 0 < M ∧
      ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
        ¬IsMulCommutative S → C < Nat.card S →
        ∀ b : Fin M → MulAut S, ∀ e : Fin M → ℕ, PartIIScalarProductInput q M b e) :
    UniformTransitiveSimpleCommutatorSupplier.{u} := by
  obtain ⟨D,C1,hD,hs1⟩ := scalar 1 (by omega)
  intro q hq
  obtain ⟨M,Cq,hM,hsq⟩ := scalar q hq
  let K := 4+2*D
  let m := M*K*(q+K)
  refine ⟨m,max Cq C1,by dsimp [m,K]; positivity,?_⟩
  intro S _ _ _ hnS hcard I _ _ k sigma beta hcoord htrans
  classical
  letI : Fintype I := Fintype.ofFinite I
  have h1 : C1 < Nat.card S := (le_max_right Cq C1).trans_lt hcard
  have hqcard : Cq < Nat.card S := (le_max_left Cq C1).trans_lt hcard
  exact prescribed_coverage_from_published_products hq hM (by rfl) k sigma beta hcoord
    (hsq S hnS hqcard) (twisted_input_of_scalar_one (fun b => hs1 S hnS h1 b (fun _ => 1)))

end NikolovSegal
