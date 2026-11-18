/- GID: D5/S3/VertexAlgebra/TwistedGround/SignedFinite/Polynomial
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/SignedFinite/Polynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite polynomial multipliers extract guarded joint coefficient shifts. -/
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.JointSeries

noncomputable section
open scoped BigOperators
namespace D5.S3.VertexAlgebra.TwistedGround.SignedFinite

abbrev Poly := Fin 3 → Fin 3 → ℂ

def evalPoly (P : Poly) (u v : ℂ) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, P i j * u ^ i.val * v ^ j.val

def mulPoly (P : Poly) (a : ℕ → ℕ → ℂ) (p q : ℕ) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, P i j * SignedFinite.shift i.val j.val a p q

theorem JointSeries.finSum {ι : Type*} (s : Finset ι)
    (F : ι → ℂ → ℂ → ℂ) (a : ι → ℕ → ℕ → ℂ)
    (h : ∀ i ∈ s, JointSeries (F i) (a i)) :
    JointSeries (fun u v => ∑ i ∈ s, F i u v) (fun p q => ∑ i ∈ s, a i p q) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : atom 0 0 0 = (fun _ _ => (0 : ℂ)) := by funext p q; simp [atom]
    simpa only [he, zero_mul, Finset.sum_empty] using jointSeries_atom 0 0 0
  | @insert i s hi ih =>
    have hh := (h i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using hh

theorem JointSeries.polynomial_mul {F a} (h : JointSeries F a) (P : Poly) :
    JointSeries (fun u v => evalPoly P u v * F u v) (mulPoly P a) := by
  have hh := JointSeries.finSum Finset.univ
    (fun i u v => ∑ j : Fin 3, P i j * (u ^ i.val * v ^ j.val * F u v))
    (fun i p q => ∑ j : Fin 3, P i j * SignedFinite.shift i.val j.val a p q) (by
      intro i _
      exact JointSeries.finSum Finset.univ _ _ (fun j _ => (h.mul_monomial i.val j.val).scale (P i j)))
  convert hh using 1
  · funext u v
    simp only [evalPoly, Finset.sum_mul, mul_assoc]
  · rfl

end D5.S3.VertexAlgebra.TwistedGround.SignedFinite
