/- GID: D5/S3/SpinModels/KingDefects/HardinA229572
   generality: I
   mirror-B: D5/B/S3/SpinModels/KingDefects/HardinA229572
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact registered one-defect king-colouring identities for OEIS A229572. -/
/-
admission_basis: open-problem-resolution (#30641; Proved)
escape_witness: bind-only; the registered assertion follows from the structural counts.
result: proof_shape=bind-only; consumers=HardinA229578.result
The index is unbounded. No bounded enumeration, checker, numerical reduction
or certified instance is asserted.
-/
import D5.S3.SpinModels.KingDefects.KingClosedForm

/-! The literal OEIS assertion with its published threshold. -/
namespace D5.S3.SpinModels.KingDefects.HardinA229572

theorem result :
    (∀ n : ℕ, 3 < n → (KingGrid.T n 2 : ℤ) =
      4*(KingGrid.T (n-1) 2 : ℤ)-4*(KingGrid.T (n-2) 2 : ℤ)) ∧
    (∀ n : ℕ, 1 < n → (KingGrid.T n 2 : ℤ) =
      (2 : ℤ)^(n-2)*(7*(n : ℤ)-8)) := by
  constructor
  · intro n hn
    obtain ⟨m,rfl⟩ : ∃ m, n=m+4 := ⟨n-4,by omega⟩
    have h0 := KingClosedForm.width_two (m+4) (by omega)
    have h1 := KingClosedForm.width_two (m+3) (by omega)
    have h2 := KingClosedForm.width_two (m+2) (by omega)
    push_cast at h0 h1 h2 ⊢
    norm_num [pow_succ] at h0 h1 h2 ⊢
    linear_combination h0-4*h1+4*h2
  · intro n hn
    rw [KingClosedForm.width_two n (by omega)]
    ring

#check @result
#print axioms result
end D5.S3.SpinModels.KingDefects.HardinA229572
