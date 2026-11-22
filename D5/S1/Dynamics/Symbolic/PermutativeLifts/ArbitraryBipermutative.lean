/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/ArbitraryBipermutative
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/ArbitraryBipermutative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-sided output and literal-prefix recovery over arbitrary alphabets. -/

module

public import D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativeLift

/-! Literal-prefix inversion and full two-sided recovery without finiteness. -/

set_option autoImplicit false

public section

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.ArbitraryBipermutative

open Function BipermutativeLift

variable {A : Type*} {k : ℕ} {h : (Fin (k + 2) → A) → A}

private noncomputable def leftLetter (bh : Bipermutative h) (a : A)
    (v : Prefix A k) : A :=
  (Equiv.ofBijective (fun b => h (Fin.cons (α := fun _ => A) b v)) (bh.left v)).symm a

private theorem left_letter_spec (bh : Bipermutative h) (a : A)
    (v : Prefix A k) : h (Fin.cons (leftLetter bh a v) v) = a :=
  (Equiv.ofBijective (fun b => h (Fin.cons (α := fun _ => A) b v)) (bh.left v)).apply_symm_apply a

private theorem prefix_step_surjective (bh : Bipermutative h) (a : A) :
    Surjective (prefixStep bh a) := by
  intro v
  let b := leftLetter bh a v
  let u : Prefix A k := Fin.cons b (Fin.init v)
  have hblock : Fin.snoc u (v (Fin.last k)) = Fin.cons (α := fun _ => A) b v := by
    dsimp [u]
    rw [← Fin.cons_snoc_eq_snoc_cons, Fin.snoc_init_self]
  have hr : rightLetter bh a u = v (Fin.last k) := by
    apply (rightEquiv bh u).symm_apply_eq.mpr
    change a = h (Fin.snoc u (v (Fin.last k)))
    rw [hblock]
    exact (left_letter_spec bh a v).symm
  refine ⟨u, ?_⟩
  simp only [prefixStep, hr, u, Fin.tail_cons, Fin.snoc_init_self]

/-- Full output and the literal source prefix determine exactly one two-sided
configuration, for every alphabet, including empty and infinite alphabets. -/
theorem coordinates_bijective (bh : Bipermutative h) : Bijective (coordinates h) := by
  let π : A → Equiv.Perm (Prefix A k) := fun a =>
    Equiv.ofBijective (prefixStep bh a)
      ⟨prefix_step_injective bh a, prefix_step_surjective bh a⟩
  exact (BipermutativeLift.Recovery.equivOfPrefixPerm bh π (fun _ _ => rfl)).bijective

end D5.S1.Dynamics.Symbolic.PermutativeLifts.ArbitraryBipermutative
