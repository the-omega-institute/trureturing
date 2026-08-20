/- GID: D5/S0/History/Coding/MinimumRollbackAlphabet
   generality: G
   mirror-B: D5/B/S0/History/Coding/MinimumRollbackAlphabet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact finite rollback logs need as many labels as the largest process fiber. -/

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.SetTheory.Cardinal.NatCard

/- Library-search audit trail (2026-08-20):
   * Repository and pinned-Mathlib searches found no theorem packaging the
     complete minimum rollback-alphabet result.
   * Pinned Mathlib exact hits `Nat.card_le_card_of_injective`,
     `Finite.equivFin`, `Fin.castLEEmb`, `Finset.le_sup`, and
     `Finset.sup_le` supply the finite-cardinality and fiber-labeling steps and
     are applied below.
   * The `loogle` and `leansearch` executables were unavailable on PATH. -/

noncomputable section

namespace D5.S0.History.Coding.MinimumRollbackAlphabet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- For a finite process, the largest fiber size is both a lower bound for
every exact rollback alphabet and the size of a fiberwise labeling alphabet
that attains the bound. -/
theorem minimum_rollback_alphabet
    {X Y : Type*} [Finite X] [Fintype Y] (U : X -> Y) :
    let maximumFiberSize :=
      Finset.univ.sup (fun y : Y => Nat.card {x : X // U x = y})
    (forall (M : Type*) [Finite M] (L : X -> M),
        Function.Injective (fun x => (U x, L x)) ->
          maximumFiberSize <= Nat.card M) /\
      exists L : X -> Fin maximumFiberSize,
        Function.Injective (fun x => (U x, L x)) := by
  classical
  dsimp only
  constructor
  · intro M _ L record_injective
    apply Finset.sup_le
    intro y _
    apply Nat.card_le_card_of_injective
      (fun x : {x : X // U x = y} => L x.1)
    intro a b hlabel
    apply Subtype.ext
    exact record_injective (Prod.ext (a.2.trans b.2.symm) hlabel)
  · have fiber_le_maximum : forall y : Y,
        Nat.card {x : X // U x = y} <=
          Finset.univ.sup (fun z : Y => Nat.card {x : X // U x = z}) := by
      intro y
      exact Finset.le_sup (f := fun z : Y => Nat.card {x : X // U x = z})
        (Finset.mem_univ y)
    let fiberEmbedding (y : Y) :
        {x : X // U x = y} ↪
          Fin (Finset.univ.sup (fun z : Y => Nat.card {x : X // U x = z})) :=
      (Finite.equivFin {x : X // U x = y}).toEmbedding.trans
        (Fin.castLEEmb (fiber_le_maximum y))
    let sourceCode (x : X) : Sigma (fun y : Y => {z : X // U z = y}) :=
      ⟨U x, ⟨x, rfl⟩⟩
    let fiberCode
        (p : Sigma (fun y : Y => {x : X // U x = y})) :
        Sigma (fun _ : Y =>
          Fin (Finset.univ.sup (fun y : Y => Nat.card {x : X // U x = y}))) :=
      ⟨p.1, fiberEmbedding p.1 p.2⟩
    have sourceCode_injective : Function.Injective sourceCode := by
      intro a b h
      exact congrArg (fun p : Sigma (fun y : Y => {x : X // U x = y}) => p.2.1) h
    have fiberCode_injective : Function.Injective fiberCode := by
      intro p q h
      rcases p with ⟨py, px⟩
      rcases q with ⟨qy, qx⟩
      have hprocess : py = qy := congrArg Sigma.fst h
      subst qy
      simp only [fiberCode, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h ⊢
      exact (fiberEmbedding py).injective h
    let label : X -> Fin
        (Finset.univ.sup (fun y : Y => Nat.card {x : X // U x = y})) :=
      fun x => (fiberCode (sourceCode x)).2
    refine ⟨label, ?_⟩
    intro a b hrecord
    apply sourceCode_injective
    apply fiberCode_injective
    exact Sigma.ext (congrArg Prod.fst hrecord)
      (heq_of_eq (congrArg Prod.snd hrecord))

/-- The public hypotheses and both conclusions are jointly inhabited. -/
example :
    let maximumFiberSize :=
      Finset.univ.sup (fun y : Unit => Nat.card {x : Unit // (fun _ : Unit => ()) x = y})
    (forall (M : Type*) [Finite M] (L : Unit -> M),
        Function.Injective (fun x => ((fun _ : Unit => ()) x, L x)) ->
          maximumFiberSize <= Nat.card M) /\
      exists L : Unit -> Fin maximumFiberSize,
        Function.Injective (fun x => ((fun _ : Unit => ()) x, L x)) := by
  exact minimum_rollback_alphabet (fun _ : Unit => ())

/-- The finite process carrier used by the witness is inhabited. -/
example : Unit := ()

#print axioms minimum_rollback_alphabet

end D5.S0.History.Coding.MinimumRollbackAlphabet
