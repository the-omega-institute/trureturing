import D5.S1.Dynamics.PeriodicOrbits.SkewZModOrder
import D5.S1.Dynamics.PeriodicOrbits.OrbitCounting
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

/-! Fixed-point counts for cyclic additive skew products. -/

namespace D5.S1.Dynamics.PeriodicOrbits.SkewZModFixedCount

open Function
open D5.S1.Dynamics.PeriodicOrbits.OrbitCounting
open D5.S1.Dynamics.PeriodicOrbits.SkewAdditiveReturn

variable {X : Type*} {q : ℕ}

noncomputable instance fixedSubtypeFintype (f : X → X) (c : X → ZMod q) (n : ℕ)
    [Fintype X] : Fintype {x : X // f^[n] x = x ∧ birkhoffSum f c n x = 0} :=
  Fintype.ofFinite _

/-- A cyclic additive fiber contributes all `q` phases exactly when its Birkhoff
holonomy vanishes. Thus the fixed-point table of the skew product is a weighted
zero-holonomy return table on the base. -/
theorem fixed_count_skew_zmod (f : X → X) (c : X → ZMod q) [Fintype X]
    [NeZero q] (n : ℕ) :
    fixedCount (skewStep f c) n =
      q * Fintype.card {x : X // f^[n] x = x ∧ birkhoffSum f c n x = 0} := by
  classical
  unfold fixedCount
  rw [← Fintype.card_subtype]
  let e :
      {z : X × ZMod q // (skewStep f c)^[n] z = z} ≃
        ({x : X // f^[n] x = x ∧ birkhoffSum f c n x = 0} × ZMod q) :=
    { toFun := fun z =>
        let hpair :
            (f^[n] z.1.1, z.1.2 + birkhoffSum f c n z.1.1) = z.1 :=
          (skew_iterate f c n z.1.1 z.1.2).symm.trans z.2
        let hbase : f^[n] z.1.1 = z.1.1 := congrArg Prod.fst hpair
        let hsum : birkhoffSum f c n z.1.1 = 0 := by
          have hsnd := congrArg Prod.snd hpair
          exact add_left_cancel (hsnd.trans (add_zero z.1.2).symm)
        ⟨⟨z.1.1, hbase, hsum⟩, z.1.2⟩
      invFun := fun z =>
        ⟨(z.1.1, z.2), by
          rw [skew_iterate]
          exact Prod.ext z.1.2.1 (by simp [z.1.2.2])⟩
      left_inv := by
        intro z
        exact Subtype.ext (Prod.ext rfl rfl)
      right_inv := by
        intro z
        exact Prod.ext (Subtype.ext rfl) rfl }
  rw [Fintype.card_congr e, Fintype.card_prod]
  simp [ZMod.card, NeZero.ne q, Nat.mul_comm]

#print axioms fixed_count_skew_zmod

end D5.S1.Dynamics.PeriodicOrbits.SkewZModFixedCount
