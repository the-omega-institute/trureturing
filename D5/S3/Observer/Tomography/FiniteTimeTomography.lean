/- GID: D5/S3/Observer/Tomography/FiniteTimeTomography
   generality: G
   mirror-B: D5/B/S3/Observer/Tomography/FiniteTimeTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite complete observation towers separate states within their rank budget. -/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-15):
   * LeanSearch query `A finite-dimensional increasing sequence of subspaces which,
     once equal at consecutive indices, remains stable and whose supremum is the whole
     space reaches the whole space within the dimension bound.` found
     `Submodule.FG.stabilizes_of_iSup_eq`. The proof imports and applies that exact
     finite-generation stabilization theorem.
   * Loogle queries `Submodule.finrank_strictMono` and
     `Submodule.eq_top_of_finrank_eq` found the exact rank-growth and maximal-rank
     declarations applied below.
   * Repository and digestion-receipt searches for finite-time tomography,
     dynamic observation towers, and bounded submodule stabilization found no
     equal-or-stronger D5 declaration.
-/

namespace D5.S3.Observer.Tomography.FiniteTimeTomography

/-- If a complete increasing observation tower gains a strict subspace at every
proper stage, then a state-separating readout occurs within the remaining rank budget. -/
theorem finite_time_tomography
    {K V State Observation : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (layers : Nat →o Submodule K V)
    (readout : Nat → State → Observation)
    (hcomplete : iSup layers = ⊤)
    (hprogress : ∀ m, layers m ≠ ⊤ → layers m < layers (m + 1))
    (hseparates : ∀ m, layers m = ⊤ → Function.Injective (readout m)) :
    ∃ m ≤ Module.finrank K V - Module.finrank K (layers 0),
      Function.Injective (readout m) := by
  have hreach : ∃ m, layers m = ⊤ := by
    obtain ⟨m, hm⟩ :=
      Submodule.FG.stabilizes_of_iSup_eq Module.Finite.fg_top layers hcomplete
    exact ⟨m, hm.symm⟩
  let m := Nat.find hreach
  have hmtop : layers m = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Nat.find_spec hreach]
    exact finrank_top K V
  have hbefore : ∀ k < m, layers k ≠ ⊤ := by
    intro k hk
    exact Nat.find_min hreach hk
  have hgrowth : ∀ k ≤ m,
      Module.finrank K (layers 0) + k ≤ Module.finrank K (layers k) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hklt : k < m := Nat.lt_of_succ_le hk
        have ih' := ih (Nat.le_of_lt hklt)
        have hstrict := hprogress k (hbefore k hklt)
        have hrank := Submodule.finrank_strictMono hstrict
        change Module.finrank K (layers k) <
          Module.finrank K (layers (k + 1)) at hrank
        omega
  refine ⟨m, ?_, hseparates m hmtop⟩
  have hmrank := hgrowth m (le_refl m)
  rw [hmtop, finrank_top] at hmrank
  omega

/-- The hypotheses are jointly satisfiable for the constant complete tower. -/
example :
    let layers : Nat →o Submodule Rat Rat :=
      ⟨fun _ => ⊤, fun _ _ _ => le_refl ⊤⟩
    ∃ m ≤ Module.finrank Rat Rat - Module.finrank Rat (layers 0),
      Function.Injective ((fun _ : Nat => (id : Rat → Rat)) m) := by
  dsimp
  apply finite_time_tomography (State := Rat) (Observation := Rat)
      (⟨fun _ => ⊤, fun _ _ _ => le_refl ⊤⟩ : Nat →o Submodule Rat Rat)
      (fun _ => (id : Rat → Rat))
  · change (⨆ _ : Nat, (⊤ : Submodule Rat Rat)) = ⊤
    exact iSup_const
  · intro k hk
    exact False.elim (hk rfl)
  · intro k hk
    exact Function.injective_id

end D5.S3.Observer.Tomography.FiniteTimeTomography
