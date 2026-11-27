/- GID: D5/S3/FiniteGroups/Cyclic/CubicLiftKernelInversion
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Cyclic/CubicLiftKernelInversion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.OrderOfElement]
   utility: none
   digest: Order-three lifts through an abelian kernel inverted by a conjugation. -/

module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

/-! Order-three lifts through an abelian kernel on which a conjugation acts by inversion. -/

set_option autoImplicit false

namespace CubicLiftKernelInversion

private theorem mul_cube {E : Type*} [Group E] (k g : E) :
    (k * g) ^ 3 = k * (g * k * g⁻¹) * (g * (g * k * g⁻¹) * g⁻¹) * g ^ 3 := by
  simp only [pow_succ, pow_zero, one_mul]
  group

/-- An order-three image element lifts to order three when some lift of a commuting
image element acts by inversion on the abelian kernel. -/
public theorem exists_orderThree_lift {E Q : Type*} [Group E] [Group Q]
    (f : E →* Q) (s x : E)
    (hcomm : ∀ {u v : E}, u ∈ f.ker → v ∈ f.ker → Commute u v)
    (hs : Commute (f s) (f x))
    (hinv : ∀ k ∈ f.ker, s * k * s⁻¹ = k⁻¹)
    (hx : orderOf (f x) = 3) : ∃ z : E, f z = f x ∧ orderOf z = 3 := by
  let y := s * x * s⁻¹
  let d := y * x⁻¹
  let a := x * d * x⁻¹
  let b := x * a * x⁻¹
  have hxCube : f x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one (f x)
  have hyImage : f y = f x := by
    simp only [y, map_mul, map_inv]
    rw [hs.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hd : d ∈ f.ker := by
    simp [MonoidHom.mem_ker, d, hyImage]
  have ha : a ∈ f.ker := by
    have hdImage := MonoidHom.mem_ker.mp hd
    simp [MonoidHom.mem_ker, a, hdImage]
  have hxKer : x ^ 3 ∈ f.ker := by
    simp [MonoidHom.mem_ker, hxCube]
  have hbConj : x * b * x⁻¹ = d := by
    calc
      x * b * x⁻¹ = x ^ 3 * d * (x ^ 3)⁻¹ := by
        dsimp only [b, a]
        simp only [pow_succ, pow_zero, one_mul]
        group
      _ = d := by rw [(hcomm hxKer hd).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hy : y = d * x := by
    dsimp only [d]
    group
  have hyCube : y ^ 3 = d * a * b * x ^ 3 := by
    calc
      y ^ 3 = (d * x) ^ 3 := by rw [hy]
      _ = d * a * b * x ^ 3 := mul_cube d x
  have haConj : x ^ 2 * a * (x ^ 2)⁻¹ = d := by
    calc
      x ^ 2 * a * (x ^ 2)⁻¹ = x * b * x⁻¹ := by
        dsimp only [b]
        simp only [pow_succ, pow_zero, one_mul]
        group
      _ = d := hbConj
  have hdConj : x ^ 2 * d * (x ^ 2)⁻¹ = b := by
    dsimp only [b, a]
    simp only [pow_succ, pow_zero, one_mul]
    group
  have hxy : x * y = a * x ^ 2 := by
    calc
      x * y = x * (d * x) := by rw [hy]
      _ = a * x ^ 2 := by
        dsimp only [a]
        group
  have hxyCube : (x * y) ^ 3 = 1 := by
    calc
      (x * y) ^ 3 = (a * x ^ 2) ^ 3 := by rw [hxy]
      _ = a * (x ^ 2 * a * (x ^ 2)⁻¹) *
            (x ^ 2 * (x ^ 2 * a * (x ^ 2)⁻¹) * (x ^ 2)⁻¹) * (x ^ 2) ^ 3 :=
        mul_cube a (x ^ 2)
      _ = a * d * b * x ^ 6 := by rw [haConj, hdConj, ← pow_mul]
      _ = y ^ 3 * x ^ 3 := by
        rw [(hcomm ha hd).eq, hyCube, mul_assoc (d * a * b) (x ^ 3) (x ^ 3), ← pow_add]
      _ = 1 := by
        have hyInv : y ^ 3 = (x ^ 3)⁻¹ := by
          calc
            y ^ 3 = s * x ^ 3 * s⁻¹ := by
              dsimp only [y]
              simp only [pow_succ, pow_zero, one_mul]
              group
            _ = (x ^ 3)⁻¹ := hinv _ hxKer
        rw [hyInv, inv_mul_cancel]
  have hzImage : f ((x * y) ^ 2) = f x := by
    rw [map_pow, map_mul, hyImage, ← pow_two, ← pow_mul]
    change f x ^ (3 + 1) = f x
    rw [pow_succ, hxCube, one_mul]
  refine ⟨(x * y) ^ 2, hzImage, ?_⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime
  · rw [pow_right_comm, hxyCube, one_pow]
  · intro hz
    have hxOne : f x = 1 := by rw [← hzImage, hz, map_one]
    rw [hxOne, orderOf_one] at hx
    exact (by decide : (1 : ℕ) ≠ 3) hx

#print axioms exists_orderThree_lift

end CubicLiftKernelInversion
