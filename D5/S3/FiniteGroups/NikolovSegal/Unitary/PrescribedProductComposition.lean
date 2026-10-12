/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PrescribedProductComposition
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PrescribedProductComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.CosetPowerBridge
import Mathlib.Algebra.Group.Pointwise.Set.Basic

set_option autoImplicit false
namespace NikolovSegal.PrescribedProductComposition
open scoped Pointwise
universe u
variable {G : Type u} [Group G]

/-- One genuine right-inner correction is selected before all targets in T.
The full prescribed tuple and original divisor powers are retained. -/
def Covers {m : ℕ} (q : ℕ) (beta : Fin m → MulAut G)
    (e : Fin m → ℕ) (T : Set G) : Prop :=
  ∃ y : Fin m → G, ∀ b ∈ T, ∃ x : Fin m → G,
    orderedProduct (fun j => (x j)⁻¹ *
      ((beta j * MulAut.conj ((y j)⁻¹)) ^ (q / e j)) (x j)) = b

/-- Consume two consecutive coverage blocks without reordering their values.
The resulting correction still precedes every target of the set product. -/
theorem covers_append {A B : ℕ} (q : ℕ)
    (beta : Fin (A+B) → MulAut G) (e : Fin (A+B) → ℕ) (S T : Set G)
    (hS : Covers q (fun j => beta (j.castAdd B)) (fun j => e (j.castAdd B)) S)
    (hT : Covers q (fun j => beta (j.natAdd A)) (fun j => e (j.natAdd A)) T) :
    Covers q beta e (S*T) := by
  obtain ⟨yS,hyS⟩ := hS
  obtain ⟨yT,hyT⟩ := hT
  refine ⟨Fin.append yS yT,?_⟩
  rintro b ⟨s,hs,t,ht,rfl⟩
  obtain ⟨xS,hxS⟩ := hyS s hs
  obtain ⟨xT,hxT⟩ := hyT t ht
  refine ⟨Fin.append xS xT,?_⟩
  have hf : (fun j => ((Fin.append xS xT) j)⁻¹ *
      ((beta j * MulAut.conj (((Fin.append yS yT) j)⁻¹)) ^ (q / e j))
        ((Fin.append xS xT) j)) =
      Fin.append
        (fun j => (xS j)⁻¹ * ((beta (j.castAdd B) * MulAut.conj ((yS j)⁻¹)) ^
          (q / e (j.castAdd B))) (xS j))
        (fun j => (xT j)⁻¹ * ((beta (j.natAdd A) * MulAut.conj ((yT j)⁻¹)) ^
          (q / e (j.natAdd A))) (xT j)) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
  rw [hf]
  simp only [orderedProduct] at hxS hxT
  simpa only [orderedProduct,List.ofFn_fin_append,List.prod_append,hxS,hxT]

/-- A genuine left inner change of the supplied automorphisms can be absorbed
into right-inner corrections, before any target is chosen. -/
theorem covers_of_left_inner {m : ℕ} (q : ℕ)
    (beta gamma : Fin m → MulAut G) (e : Fin m → ℕ)
    (c : Fin m → G) (T : Set G)
    (hgamma : ∀ j, gamma j = MulAut.conj (c j) * beta j)
    (hcover : Covers q gamma e T) : Covers q beta e T := by
  obtain ⟨y,hy⟩ := hcover
  let z : Fin m → G := fun j => y j * (beta j).symm ((c j)⁻¹)
  have haction : ∀ j, beta j * MulAut.conj ((z j)⁻¹) =
      gamma j * MulAut.conj ((y j)⁻¹) := by
    intro j
    rw [hgamma j]
    apply MulEquiv.ext
    intro g
    simp only [z,MulAut.mul_apply,MulAut.conj_apply,map_mul,map_inv,
      mul_inv_rev,inv_inv,MulEquiv.apply_symm_apply]
  refine ⟨z,?_⟩
  intro b hb
  obtain ⟨x,hx⟩ := hy b hb
  exact ⟨x,by simpa only [haction] using hx⟩

end NikolovSegal.PrescribedProductComposition
