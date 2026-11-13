/- GID: D5/S3/Quantum/Tomography/Hadamard/BanicaCycleForestIncidence
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/Hadamard/BanicaCycleForestIncidence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integrating edge data on a cyclic group after removing a vertex gives a surjective incidence map. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace D5.S3.Quantum.Tomography.Hadamard.BanicaCycleForestIncidence

private theorem val_succ_of_ne_zero {p : ℕ} [NeZero p] (z : ZMod p)
    (h : z + 1 ≠ 0) : (z + 1).val = z.val + 1 := by
  have hz := z.val_lt
  have hlt : z.val + 1 < p := by
    by_contra hn
    have he : z.val + 1 = p := by omega
    apply h
    calc
      z + 1 = ((z.val + 1 : ℕ) : ZMod p) := by simp
      _ = 0 := by rw [he]; exact ZMod.natCast_self p
  have he : z + 1 = ((z.val + 1 : ℕ) : ZMod p) := by simp
  rw [he, ZMod.val_natCast_of_lt hlt]

/-- The edges of the step-a circle whose two endpoints lie in S. -/
abbrev Edges {p : ℕ} (S : Finset (ZMod p)) (a : ZMod p) :=
  {s : S // s.1 + a ∈ S}

/-- Every edge assignment on a proper subset of a cyclic group integrates to vertex values.
The step is a unit, so its orbit is the whole cyclic group. -/
theorem cycle_incidence_surjective {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S ≠ Finset.univ) (a : (ZMod p)ˣ)
    {W : Type*} [AddCommGroup W] :
    Function.Surjective (fun x : S → W =>
      fun e : Edges S (a : ZMod p) => x e.1 - x ⟨e.1.1 + a, e.2⟩) := by
  classical
  obtain ⟨o, ho⟩ : ∃ o : ZMod p, o ∉ S := by
    by_contra hn
    apply hS
    ext x
    simp only [Finset.mem_univ, iff_true]
    by_contra hx
    exact hn ⟨x, hx⟩
  intro f
  let F : ZMod p → W := fun x =>
    if hx : x ∈ S then
      if hy : x + a ∈ S then f ⟨⟨x, hx⟩, hy⟩ else 0
    else 0
  let r : ZMod p → ℕ := fun x => ((x - o) * (↑a⁻¹ : ZMod p)).val
  let R : S → W := fun x => - ∑ k ∈ Finset.range (r x), F (o + (k : ZMod p) * a)
  refine ⟨R, funext fun e => ?_⟩
  have ha : (↑a : ZMod p) * ↑a⁻¹ = 1 := by simp
  have hb : (↑a⁻¹ : ZMod p) * ↑a = 1 := by simp
  have hnext : (e.1.1 + a - o) * (↑a⁻¹ : ZMod p) =
      (e.1.1 - o) * (↑a⁻¹ : ZMod p) + 1 := by
    calc
      _ = (e.1.1 - o) * (↑a⁻¹ : ZMod p) + ↑a * ↑a⁻¹ := by ring
      _ = _ := by rw [ha]
  have hne : (e.1.1 - o) * (↑a⁻¹ : ZMod p) + 1 ≠ 0 := by
    rw [← hnext]
    intro he
    have : e.1.1 + a = o := by
      have := congrArg (fun x : ZMod p => x * a) he
      simpa [mul_assoc, hb, sub_eq_zero] using this
    exact ho (this ▸ e.2)
  have hr : r (e.1.1 + a) = r e.1.1 + 1 := by
    dsimp [r]
    rw [hnext, val_succ_of_ne_zero _ hne]
  have hrecover : o + (r e.1.1 : ZMod p) * a = e.1.1 := by
    dsimp [r]
    rw [ZMod.natCast_zmod_val, mul_assoc, hb, mul_one]
    ring
  change -(∑ k ∈ Finset.range (r e.1.1), F (o + (k : ZMod p) * a)) -
    -(∑ k ∈ Finset.range (r (e.1.1 + a)), F (o + (k : ZMod p) * a)) = f e
  rw [hr, Finset.sum_range_succ, hrecover]
  have hf : F e.1.1 = f e := by
    simp [F, e.1.2, e.2]
  rw [hf]
  abel

end D5.S3.Quantum.Tomography.Hadamard.BanicaCycleForestIncidence
