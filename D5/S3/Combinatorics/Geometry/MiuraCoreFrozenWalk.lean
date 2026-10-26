/- GID: D5/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraCoreFrozenWalk
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Extremum-free unit-step walks have opposite and uniform side slopes. -/

/- Finite proofs adapted from Chakshu Gupta, https://github.com/ChakshuGupta13/lab,
commit 0bf8c67f7f5a2e8d44fb88c19fb80337221bbc11,
math/gupta2026degseq/lean/OrigamiCone/OrigamiCone/.
SequelEdFrozenForward.lean: 887afe6968436125cffd8eae84b643308aba9fb4.
CC BY 4.0; see docs/reports/miura-suppliers/lab-NOTICE.txt and lab-LICENSE.txt.
Namespaces, imports and selected declaration boundaries are adapted.
Retire these transplants when equivalent suppliers exist in pinned mathlib. -/

module

public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Set

/-! Finite signed contraction and its exact full-grid invariants. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraCoreFrozenWalk

noncomputable section

def alignedExt (M : ℕ) (e dL dR : ℕ → ℤ) (σ : ℤ) (i : ℕ) : Prop :=
  (0 < i → e (i - 1) = -σ) ∧ (i < M → e i = σ) ∧ dL i = σ ∧ dR i = σ

variable {M : ℕ} {e dL dR : ℕ → ℤ}

theorem cascade_down (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (he : ∀ i, i < M → e i = 1 ∨ e i = -1)
    (hdL : ∀ i, i ≤ M → dL i = 1 ∨ dL i = -1)
    (hdR : ∀ i, i ≤ M → dR i = 1 ∨ dR i = -1)
    (hLwalk : ∀ i, i < M → e i + (dL (i + 1) - dL i) = 1 ∨ e i + (dL (i + 1) - dL i) = -1)
    (hRwalk : ∀ i, i < M → e i + (dR (i + 1) - dR i) = 1 ∨ e i + (dR (i + 1) - dR i) = -1)
    (hef : ∀ i, i ≤ M → ¬ alignedExt M e dL dR σ i)
    (i0 : ℕ) (hi0M : i0 < M)
    (hL0 : dL i0 = σ) (hR0 : dR i0 = σ) (he0 : e i0 = -σ) :
    False := by
  have claim : ∀ k, i0 + k ≤ M →
      dL (i0+k) = σ ∧ dR (i0+k) = σ ∧ (i0+k < M → e (i0+k) = -σ) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨hL0, hR0, fun _ => he0⟩
    | succ k IH =>
      intro hle
      have hk : i0 + k ≤ M := by omega
      obtain ⟨hLj, hRj, hej_imp⟩ := IH hk
      set j := i0 + k with hjdef
      have hjM : j < M := by omega
      have hej : e j = -σ := hej_imp hjM
      have hLj1 : dL (j + 1) = σ := by
        have hw := hLwalk j hjM
        have hv := hdL (j + 1) (by omega)
        rcases hσ with h | h <;> rcases hw with hh | hh <;> rcases hv with hv1 | hv1 <;> omega
      have hRj1 : dR (j + 1) = σ := by
        have hw := hRwalk j hjM
        have hv := hdR (j + 1) (by omega)
        rcases hσ with h | h <;> rcases hw with hh | hh <;> rcases hv with hv1 | hv1 <;> omega
      have hidx : i0 + (k + 1) = j + 1 := by omega
      rw [hidx]
      refine ⟨hLj1, hRj1, ?_⟩
      intro hlt
      by_contra hcontra
      have hene : e (j + 1) = σ := by
        have := he (j + 1) hlt
        rcases hσ with h | h <;> omega
      apply hef (j + 1) (by omega)
      refine ⟨fun _ => ?_, fun _ => hene, hLj1, hRj1⟩
      rw [Nat.add_sub_cancel]; exact hej

  have hLM : dL M = σ := by
    have := (claim (M - i0) (by omega)).1; rwa [show i0 + (M - i0) = M from by omega] at this
  have hRM : dR M = σ := by
    have := (claim (M - i0) (by omega)).2.1; rwa [show i0 + (M - i0) = M from by omega] at this
  have heM : e (M - 1) = -σ := by
    have := (claim (M - 1 - i0) (by omega)).2.2 (by omega)
    rwa [show i0 + (M - 1 - i0) = M - 1 from by omega] at this
  exact hef M ((by omega)) ⟨fun _ => heM, fun h => absurd h (by omega), hLM, hRM⟩

theorem cascade_up (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (he : ∀ i, i < M → e i = 1 ∨ e i = -1)
    (hdL : ∀ i, i ≤ M → dL i = 1 ∨ dL i = -1)
    (hdR : ∀ i, i ≤ M → dR i = 1 ∨ dR i = -1)
    (hLwalk : ∀ i, i < M → e i + (dL (i + 1) - dL i) = 1 ∨ e i + (dL (i + 1) - dL i) = -1)
    (hRwalk : ∀ i, i < M → e i + (dR (i + 1) - dR i) = 1 ∨ e i + (dR (i + 1) - dR i) = -1)
    (hef : ∀ i, i ≤ M → ¬ alignedExt M e dL dR σ i)
    (i0 : ℕ) (hi0 : 0 < i0) (hi0M : i0 ≤ M)
    (hL0 : dL i0 = σ) (hR0 : dR i0 = σ) (he0 : e (i0-1) = σ) :
    False := by
  have claim : ∀ k, k ≤ i0 →
      dL (i0-k) = σ ∧ dR (i0-k) = σ ∧ (0 < i0-k → e (i0-k-1) = σ) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨hL0, hR0, fun _ => he0⟩
    | succ k IH =>
      intro hle
      have hk : k ≤ i0 := by omega
      obtain ⟨hLj, hRj, hej_imp⟩ := IH hk
      set j := i0 - k with hjdef
      have hjpos : 0 < j := by omega
      have hej : e (j-1) = σ := hej_imp hjpos
      have hjM : j - 1 < M := by omega
      have hLj1 : dL (j-1) = σ := by
        have hw := hLwalk (j-1) hjM
        have hv := hdL (j-1) (by omega)
        have hsj : j - 1 + 1 = j := by omega
        rw [hsj] at hw
        rcases hσ with h | h <;> rcases hw with hh | hh <;> rcases hv with hv1 | hv1 <;> omega
      have hRj1 : dR (j-1) = σ := by
        have hw := hRwalk (j-1) hjM
        have hv := hdR (j-1) (by omega)
        have hsj : j - 1 + 1 = j := by omega
        rw [hsj] at hw
        rcases hσ with h | h <;> rcases hw with hh | hh <;> rcases hv with hv1 | hv1 <;> omega
      have hidx : i0 - (k + 1) = j - 1 := by omega
      rw [hidx]
      refine ⟨hLj1, hRj1, ?_⟩
      intro hpos
      by_contra hcontra
      have hene : e (j-1-1) = -σ := by
        have := he (j-1-1) (by omega)
        rcases hσ with h | h <;> omega
      exact hef (j-1) (by omega)
        ⟨fun _ => hene, fun _ => hej, hLj1, hRj1⟩
  have hL0' : dL 0 = σ := by
    have := (claim i0 ((by omega))).1; rwa [show i0 - i0 = 0 from by omega] at this
  have hR0' : dR 0 = σ := by
    have := (claim i0 ((by omega))).2.1; rwa [show i0 - i0 = 0 from by omega] at this
  have he0' : e 0 = σ := by
    have := (claim (i0-1) (by omega)).2.2 (by omega)
    rwa [show i0 - (i0-1) - 1 = 0 from by omega] at this
  exact hef 0 (by omega) ⟨fun h => absurd h (by omega), fun _ => he0', hL0', hR0'⟩

theorem extremumFree_rainbow
    (he : ∀ i, i < M → e i = 1 ∨ e i = -1)
    (hdL : ∀ i, i ≤ M → dL i = 1 ∨ dL i = -1)
    (hdR : ∀ i, i ≤ M → dR i = 1 ∨ dR i = -1)
    (hLwalk : ∀ i, i < M → e i + (dL (i + 1) - dL i) = 1 ∨ e i + (dL (i + 1) - dL i) = -1)
    (hRwalk : ∀ i, i < M → e i + (dR (i + 1) - dR i) = 1 ∨ e i + (dR (i + 1) - dR i) = -1)
    (hef : ∀ σ, (σ = 1 ∨ σ = -1) → ∀ i, i ≤ M → ¬ alignedExt M e dL dR σ i) :
    ∀ i, i ≤ M → dL i + dR i = 0 := by
  intro i0 hi0M
  by_contra hne
  have hLv := hdL i0 hi0M
  have hRv := hdR i0 hi0M
  have hσ : dL i0 = dR i0 := by rcases hLv with h|h <;> rcases hRv with h'|h' <;> omega
  set σ := dL i0 with hσdef
  have hσv : σ = 1 ∨ σ = -1 := hLv
  have hR0 : dR i0 = σ := hσ.symm
  have hefσ := hef σ hσv
  by_cases hd : i0 < M ∧ e i0 = -σ
  · exact cascade_down σ hσv he hdL hdR hLwalk hRwalk hefσ i0 hd.1 rfl hR0 hd.2
  · by_cases hu : 0 < i0 ∧ e (i0-1) = σ
    · exact cascade_up σ hσv he hdL hdR hLwalk hRwalk hefσ i0 hu.1 hi0M rfl hR0 hu.2
    · push Not at hd hu
      apply hefσ i0 hi0M
      refine ⟨fun hpos => ?_, fun hlt => ?_, rfl, hR0⟩
      · have hne1 := hu hpos
        have hev := he (i0-1) (by omega)
        rcases hσv with h|h <;> omega
      · have hne2 := hd hlt
        have hev := he i0 hlt
        rcases hσv with h|h <;> omega

theorem rainbow_dL_const
    (he : ∀ i, i < M → e i = 1 ∨ e i = -1)
    (hLwalk : ∀ i, i < M → e i + (dL (i + 1) - dL i) = 1 ∨ e i + (dL (i + 1) - dL i) = -1)
    (hRwalk : ∀ i, i < M → e i + (dR (i + 1) - dR i) = 1 ∨ e i + (dR (i + 1) - dR i) = -1)
    (rainbow : ∀ i, i ≤ M → dL i + dR i = 0) :
    ∀ i, i < M → dL (i + 1) = dL i := by
  intro i hi
  have hr_i := rainbow i (by omega)
  have hr_i1 := rainbow (i + 1) (by omega)
  have hL := hLwalk i hi
  have hR := hRwalk i hi
  have hei := he i hi
  rcases hL with hL|hL <;> rcases hR with hR|hR <;> rcases hei with he'|he' <;> omega

end

end D5.S3.Combinatorics.Geometry.MiuraCoreFrozenWalk
