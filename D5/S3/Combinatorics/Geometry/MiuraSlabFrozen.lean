/- GID: D5/S3/Combinatorics/Geometry/MiuraSlabFrozen
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraSlabFrozen
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: Extrema-free rows have uniform signed cuts and physical ends are occupied. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraSlabIncidence

/-! Finite frozen-cut and boundary suppliers for canonical occupied slabs. -/

/- Selected proofs adapted from Chakshu Gupta, CC BY 4.0,
https://github.com/ChakshuGupta13/lab, commit
0bf8c67f7f5a2e8d44fb88c19fb80337221bbc11,
math/gupta2026degseq/lean/OrigamiCone/OrigamiCone/SequelEdFrozenForward.lean,
SequelEdFrozenCol.lean, SequelEdFrozenBridge.lean, SequelEdFrozenSlope.lean,
and SequelEdBoundary.lean. Full license and attribution are retained in
docs/reports/miura-suppliers/. The selected finite proof bodies are preserved;
namespaces, narrow imports and private visibility are adapted. Retire these
transplants when the project's pinned mathlib supplies equivalent finite
frozen-cut and boundary-occupancy results, and use those declarations directly. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraSlabFrozen

open MiuraHeightEnvelope MiuraSlabExtrema MiuraSlabNeutral MiuraSlabIncidence

private def IsStrictLocalExtremum {m n : ℕ} (h : Cell m n → ℤ) (v : Cell m n) : Prop :=
  IsStrictLocalMax h v ∨ IsStrictLocalMin h v

private def activeColumn {m n : ℕ} (h : Cell m n → ℤ) (j : Fin n) : Prop :=
  ∃ i, IsStrictLocalExtremum h (i, j)


def alignedExt (M : ℕ) (e dL dR : ℕ → ℤ) (σ : ℤ) (i : ℕ) : Prop :=
  (0 < i → e (i - 1) = -σ) ∧ (i < M → e i = σ) ∧ dL i = σ ∧ dR i = σ

variable {M : ℕ} {e dL dR : ℕ → ℤ}

private theorem cascade_down (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (he : ∀ i, i < M → e i = 1 ∨ e i = -1)
    (hdL : ∀ i, i ≤ M → dL i = 1 ∨ dL i = -1)
    (hdR : ∀ i, i ≤ M → dR i = 1 ∨ dR i = -1)
    (hLwalk : ∀ i, i < M → e i + (dL (i+1) - dL i) = 1 ∨ e i + (dL (i+1) - dL i) = -1)
    (hRwalk : ∀ i, i < M → e i + (dR (i+1) - dR i) = 1 ∨ e i + (dR (i+1) - dR i) = -1)
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
      have hLj1 : dL (j+1) = σ := by
        have hw := hLwalk j hjM
        have hv := hdL (j+1) (by omega)
        rcases hσ with h | h <;> rcases hw with hh | hh <;> rcases hv with hv1 | hv1 <;> omega
      have hRj1 : dR (j+1) = σ := by
        have hw := hRwalk j hjM
        have hv := hdR (j+1) (by omega)
        rcases hσ with h | h <;> rcases hw with hh | hh <;> rcases hv with hv1 | hv1 <;> omega
      have hidx : i0 + (k+1) = j + 1 := by omega
      rw [hidx]
      refine ⟨hLj1, hRj1, ?_⟩
      intro hlt
      by_contra hcontra
      have hene : e (j+1) = σ := by
        have := he (j+1) hlt
        rcases hσ with h | h <;> omega
      apply hef (j+1) (by omega)
      refine ⟨fun _ => ?_, fun _ => hene, hLj1, hRj1⟩
      rw [Nat.add_sub_cancel]; exact hej

  have hLM : dL M = σ := by
    have := (claim (M - i0) (by omega)).1; rwa [show i0 + (M - i0) = M from by omega] at this
  have hRM : dR M = σ := by
    have := (claim (M - i0) (by omega)).2.1; rwa [show i0 + (M - i0) = M from by omega] at this
  have heM : e (M - 1) = -σ := by
    have := (claim (M - 1 - i0) (by omega)).2.2 (by omega)
    rwa [show i0 + (M - 1 - i0) = M - 1 from by omega] at this
  exact hef M (le_refl M) ⟨fun _ => heM, fun h => absurd h (by omega), hLM, hRM⟩

private theorem cascade_up (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (he : ∀ i, i < M → e i = 1 ∨ e i = -1)
    (hdL : ∀ i, i ≤ M → dL i = 1 ∨ dL i = -1)
    (hdR : ∀ i, i ≤ M → dR i = 1 ∨ dR i = -1)
    (hLwalk : ∀ i, i < M → e i + (dL (i+1) - dL i) = 1 ∨ e i + (dL (i+1) - dL i) = -1)
    (hRwalk : ∀ i, i < M → e i + (dR (i+1) - dR i) = 1 ∨ e i + (dR (i+1) - dR i) = -1)
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
      have hidx : i0 - (k+1) = j - 1 := by omega
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
    have := (claim i0 (le_refl i0)).1; rwa [show i0 - i0 = 0 from by omega] at this
  have hR0' : dR 0 = σ := by
    have := (claim i0 (le_refl i0)).2.1; rwa [show i0 - i0 = 0 from by omega] at this
  have he0' : e 0 = σ := by
    have := (claim (i0-1) (by omega)).2.2 (by omega)
    rwa [show i0 - (i0-1) - 1 = 0 from by omega] at this
  exact hef 0 (by omega) ⟨fun h => absurd h (by omega), fun _ => he0', hL0', hR0'⟩

private theorem extremumFree_rainbow
    (he : ∀ i, i < M → e i = 1 ∨ e i = -1)
    (hdL : ∀ i, i ≤ M → dL i = 1 ∨ dL i = -1)
    (hdR : ∀ i, i ≤ M → dR i = 1 ∨ dR i = -1)
    (hLwalk : ∀ i, i < M → e i + (dL (i+1) - dL i) = 1 ∨ e i + (dL (i+1) - dL i) = -1)
    (hRwalk : ∀ i, i < M → e i + (dR (i+1) - dR i) = 1 ∨ e i + (dR (i+1) - dR i) = -1)
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

private theorem rainbow_dL_const
    (he : ∀ i, i < M → e i = 1 ∨ e i = -1)
    (hLwalk : ∀ i, i < M → e i + (dL (i+1) - dL i) = 1 ∨ e i + (dL (i+1) - dL i) = -1)
    (hRwalk : ∀ i, i < M → e i + (dR (i+1) - dR i) = 1 ∨ e i + (dR (i+1) - dR i) = -1)
    (rainbow : ∀ i, i ≤ M → dL i + dR i = 0) :
    ∀ i, i < M → dL (i+1) = dL i := by
  intro i hi
  have hr_i := rainbow i (by omega)
  have hr_i1 := rainbow (i+1) (by omega)
  have hL := hLwalk i hi
  have hR := hRwalk i hi
  have hei := he i hi
  rcases hL with hL|hL <;> rcases hR with hR|hR <;> rcases hei with he'|he' <;> omega



open MiuraHeightEnvelope Finset

variable {m n : ℕ}

def frozenColumn (h : Cell m n → ℤ) (j : Fin n) : Prop :=
  ∃ (_ : 0 < j.val) (hj1 : j.val + 1 < n),
    ∀ i : Fin m,
      h (i, ⟨j.val - 1, by omega⟩) + h (i, ⟨j.val + 1, hj1⟩) = 2 * h (i, j)



open MiuraHeightEnvelope Finset

variable {m n : ℕ}

private theorem adj_interior_cases (i : Fin m) (j : Fin n) (hj0 : 0 < j.val)
    (hj1 : j.val + 1 < n) (u : Cell m n) (hu : adj ((i, j) : Cell m n) u) :
    (∃ (_ : 0 < i.val), u = (⟨i.val - 1, by omega⟩, j))
    ∨ (∃ (hp : i.val + 1 < m), u = (⟨i.val + 1, hp⟩, j))
    ∨ (u = (i, ⟨j.val - 1, by omega⟩))
    ∨ (u = (i, ⟨j.val + 1, hj1⟩)) := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := u
  unfold adj gdist at hu
  have hu' : ((i.val : ℤ) - p).natAbs + ((j.val : ℤ) - q).natAbs = 1 := by exact_mod_cast hu
  by_cases hcol : q = j.val
  ·
    subst hcol
    have hrow : ((i.val : ℤ) - p).natAbs = 1 := by simpa using hu'
    rcases (Int.natAbs_eq_iff).mp hrow with hpi | hpi
    · left; exact ⟨by omega, by ext <;> simp <;> omega⟩
    · right; left; exact ⟨by omega, by ext <;> simp <;> omega⟩
  ·
    have hcz : ((j.val : ℤ) - q).natAbs = 1 ∧ ((i.val : ℤ) - p).natAbs = 0 := by
      constructor
      · by_contra hc
        have hjq0 : ((j.val : ℤ) - q).natAbs = 0 := by omega
        exact hcol (by have := Int.natAbs_eq_zero.mp hjq0; omega)
      · omega
    have hpi : p = i.val := by have := Int.natAbs_eq_zero.mp hcz.2; omega
    have hqc : q = j.val - 1 ∨ q = j.val + 1 := by
      rcases (Int.natAbs_eq_iff).mp hcz.1 with h | h
      · left; omega
      · right; omega
    rcases hqc with hq1 | hq1
    · right; right; left; ext <;> simp <;> omega
    · right; right; right; ext <;> simp <;> omega

private theorem inactive_imp_frozenColumn (h : Cell m n → ℤ) (hh : IsHeight h)
    (j : Fin n) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n) (hm : 0 < m)
    (hnact : ¬ activeColumn h j) : frozenColumn h j := by
  set jL : Fin n := ⟨j.val - 1, by omega⟩ with hjLdef
  set jR : Fin n := ⟨j.val + 1, hj1⟩ with hjRdef
  set v : ℕ → ℤ := fun k => h (⟨min k (m-1), by omega⟩, j) with hvdef
  set Lc : ℕ → ℤ := fun k => h (⟨min k (m-1), by omega⟩, jL) with hLdef
  set Rc : ℕ → ℤ := fun k => h (⟨min k (m-1), by omega⟩, jR) with hRdef
  have hvk : ∀ k (hk : k < m), v k = h (⟨k, hk⟩, j) := by
    intro k hk; have hmin : min k (m-1) = k := by omega
    simp only [hvdef, hmin]
  have hLk : ∀ k (hk : k < m), Lc k = h (⟨k, hk⟩, jL) := by
    intro k hk; have hmin : min k (m-1) = k := by omega
    simp only [hLdef, hmin]
  have hRk : ∀ k (hk : k < m), Rc k = h (⟨k, hk⟩, jR) := by
    intro k hk; have hmin : min k (m-1) = k := by omega
    simp only [hRdef, hmin]
  set e : ℕ → ℤ := fun k => v (k+1) - v k with hedef
  set dL : ℕ → ℤ := fun k => Lc k - v k with hdLdef
  set dR : ℕ → ℤ := fun k => Rc k - v k with hdRdef

  have hev : ∀ k (hk1 : k + 1 < m), e k = h (⟨k+1, hk1⟩, j) - h (⟨k, by omega⟩, j) := by
    intro k hk1; simp only [hedef]; rw [hvk (k+1) hk1, hvk k (by omega)]
  have hdLv : ∀ k (hk : k < m), dL k = h (⟨k, hk⟩, jL) - h (⟨k, hk⟩, j) := by
    intro k hk; simp only [hdLdef]; rw [hLk k hk, hvk k hk]
  have hdRv : ∀ k (hk : k < m), dR k = h (⟨k, hk⟩, jR) - h (⟨k, hk⟩, j) := by
    intro k hk; simp only [hdRdef]; rw [hRk k hk, hvk k hk]

  have he_pm : ∀ i, i < m - 1 → e i = 1 ∨ e i = -1 := by
    intro i hi
    rw [hev i (by omega)]
    have hadj : adj ((⟨i+1, by omega⟩, j) : Cell m n) (⟨i, by omega⟩, j) := by
      unfold adj gdist; simp only [Fin.val_mk]; omega
    have hv := hh _ _ hadj
    rcases abs_cases (h (⟨i+1, by omega⟩, j) - h (⟨i, by omega⟩, j)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  have hdL_pm : ∀ i, i ≤ m - 1 → dL i = 1 ∨ dL i = -1 := by
    intro i hi
    rw [hdLv i (by omega)]
    have hadj : adj ((⟨i, by omega⟩, j) : Cell m n) (⟨i, by omega⟩, jL) := by
      unfold adj gdist; simp only [hjLdef, Fin.val_mk]; omega
    have hv := hh _ _ hadj
    rcases abs_cases (h (⟨i, by omega⟩, j) - h (⟨i, by omega⟩, jL)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  have hdR_pm : ∀ i, i ≤ m - 1 → dR i = 1 ∨ dR i = -1 := by
    intro i hi
    rw [hdRv i (by omega)]
    have hadj : adj ((⟨i, by omega⟩, j) : Cell m n) (⟨i, by omega⟩, jR) := by
      unfold adj gdist; simp only [hjRdef, Fin.val_mk]; omega
    have hv := hh _ _ hadj
    rcases abs_cases (h (⟨i, by omega⟩, j) - h (⟨i, by omega⟩, jR)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega

  have hLwalk : ∀ i, i < m - 1 →
      e i + (dL (i+1) - dL i) = 1 ∨ e i + (dL (i+1) - dL i) = -1 := by
    intro i hi
    have hstep : e i + (dL (i+1) - dL i)
        = h (⟨i+1, by omega⟩, jL) - h (⟨i, by omega⟩, jL) := by
      rw [hev i (by omega), hdLv (i+1) (by omega), hdLv i (by omega)]; ring
    rw [hstep]
    have hadj : adj ((⟨i+1, by omega⟩, jL) : Cell m n) (⟨i, by omega⟩, jL) := by
      unfold adj gdist; simp only [hjLdef, Fin.val_mk]; omega
    have hv := hh _ _ hadj
    rcases abs_cases (h (⟨i+1, by omega⟩, jL) - h (⟨i, by omega⟩, jL)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  have hRwalk : ∀ i, i < m - 1 →
      e i + (dR (i+1) - dR i) = 1 ∨ e i + (dR (i+1) - dR i) = -1 := by
    intro i hi
    have hstep : e i + (dR (i+1) - dR i)
        = h (⟨i+1, by omega⟩, jR) - h (⟨i, by omega⟩, jR) := by
      rw [hev i (by omega), hdRv (i+1) (by omega), hdRv i (by omega)]; ring
    rw [hstep]
    have hadj : adj ((⟨i+1, by omega⟩, jR) : Cell m n) (⟨i, by omega⟩, jR) := by
      unfold adj gdist; simp only [hjRdef, Fin.val_mk]; omega
    have hv := hh _ _ hadj
    rcases abs_cases (h (⟨i+1, by omega⟩, jR) - h (⟨i, by omega⟩, jR)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega

  have hbridge : ∀ σ, (σ = 1 ∨ σ = -1) → ∀ i (hi' : i < m),
      alignedExt (m-1) e dL dR σ i → IsStrictLocalExtremum h (⟨i, hi'⟩, j) := by
    intro σ hσ i hi' hae
    obtain ⟨hae_up, hae_dn, hae_L, hae_R⟩ := hae

    have hLval : h (⟨i, hi'⟩, jL) = h (⟨i, hi'⟩, j) + σ := by
      have hd := hdLv i hi'; rw [hae_L] at hd; omega
    have hRval : h (⟨i, hi'⟩, jR) = h (⟨i, hi'⟩, j) + σ := by
      have hd := hdRv i hi'; rw [hae_R] at hd; omega
    have hup_val : ∀ (hpos : 0 < i) (P : i - 1 < m),
        h (⟨i - 1, P⟩, j) = h (⟨i, hi'⟩, j) + σ := by
      intro hpos P
      have hk1 : (i - 1) + 1 < m := by omega
      have hst : e (i - 1) = v ((i - 1) + 1) - v (i - 1) := by simp only [hedef]
      rw [hvk ((i - 1) + 1) hk1, hvk (i - 1) P, hae_up hpos] at hst
      have hc : h (⟨(i - 1) + 1, hk1⟩, j) = h (⟨i, hi'⟩, j) := by
        rw [show (⟨(i - 1) + 1, hk1⟩ : Fin m) = ⟨i, hi'⟩ from
          Fin.ext (show (i - 1) + 1 = i by omega)]
      rw [hc] at hst
      omega
    have hdn_val : ∀ (hlt : i < m - 1) (P : i + 1 < m),
        h (⟨i + 1, P⟩, j) = h (⟨i, hi'⟩, j) + σ := by
      intro hlt P
      have hst : e i = v (i + 1) - v i := by simp only [hedef]
      rw [hvk (i + 1) P, hvk i hi', hae_dn hlt] at hst
      omega
    rcases hσ with hσ1 | hσ1
    ·
      subst hσ1; right
      intro u hu
      rcases adj_interior_cases ⟨i, hi'⟩ j hj0 hj1 u hu with
        ⟨hup, rfl⟩ | ⟨hdn, rfl⟩ | rfl | rfl
      · exact hup_val hup _
      · exact hdn_val (by have h2 : i + 1 < m := hdn; omega) hdn
      · exact hLval
      · exact hRval
    ·
      subst hσ1; left
      intro u hu
      rcases adj_interior_cases ⟨i, hi'⟩ j hj0 hj1 u hu with
        ⟨hup, rfl⟩ | ⟨hdn, rfl⟩ | rfl | rfl
      · exact hup_val hup _
      · exact hdn_val (by have h2 : i + 1 < m := hdn; omega) hdn
      · exact hLval
      · exact hRval

  have hef : ∀ σ, (σ = 1 ∨ σ = -1) → ∀ i, i ≤ m - 1 →
      ¬ alignedExt (m-1) e dL dR σ i := by
    intro σ hσ i hi hae
    have hi' : i < m := by omega
    exact hnact ⟨⟨i, hi'⟩, hbridge σ hσ i hi' hae⟩

  have hrainbow := extremumFree_rainbow he_pm hdL_pm hdR_pm hLwalk hRwalk hef
  refine ⟨hj0, hj1, ?_⟩
  intro i
  have hi := i.isLt
  have hr := hrainbow i.val (by omega)
  rw [hdLv i.val hi, hdRv i.val hi] at hr
  have hiv : (⟨i.val, hi⟩ : Fin m) = i := Fin.ext rfl
  rw [hiv] at hr

  show h (i, jL) + h (i, jR) = 2 * h (i, j)
  omega



open MiuraHeightEnvelope Finset

variable {m n : ℕ}

private theorem frozenColumn_dL_const_adjacent (h : Cell m n → ℤ) (hh : IsHeight h)
    (j : Fin n) (hfrz : frozenColumn h j) (i : ℕ) (hi1 : i + 1 < m) :
    h (⟨i + 1, hi1⟩, ⟨j.val - 1, by
      obtain ⟨hj0, _, _⟩ := hfrz; omega⟩)
      - h (⟨i + 1, hi1⟩, j)
    = h (⟨i, by omega⟩, ⟨j.val - 1, by
      obtain ⟨hj0, _, _⟩ := hfrz; omega⟩)
      - h (⟨i, by omega⟩, j) := by
  obtain ⟨hj0, hj1, hsym⟩ := hfrz
  set jL : Fin n := ⟨j.val - 1, by omega⟩ with hjLdef
  set jR : Fin n := ⟨j.val + 1, hj1⟩ with hjRdef
  set v : ℕ → ℤ := fun k => h (⟨min k (m-1), by omega⟩, j) with hvdef
  set Lc : ℕ → ℤ := fun k => h (⟨min k (m-1), by omega⟩, jL) with hLdef
  set Rc : ℕ → ℤ := fun k => h (⟨min k (m-1), by omega⟩, jR) with hRdef
  have hvk : ∀ k (hk : k < m), v k = h (⟨k, hk⟩, j) := by
    intro k hk; have hmin : min k (m-1) = k := by omega
    simp only [hvdef, hmin]
  have hLk : ∀ k (hk : k < m), Lc k = h (⟨k, hk⟩, jL) := by
    intro k hk; have hmin : min k (m-1) = k := by omega
    simp only [hLdef, hmin]
  have hRk : ∀ k (hk : k < m), Rc k = h (⟨k, hk⟩, jR) := by
    intro k hk; have hmin : min k (m-1) = k := by omega
    simp only [hRdef, hmin]
  set e : ℕ → ℤ := fun k => v (k+1) - v k with hedef
  set dL : ℕ → ℤ := fun k => Lc k - v k with hdLdef
  set dR : ℕ → ℤ := fun k => Rc k - v k with hdRdef
  have hev : ∀ k (hk1 : k + 1 < m), e k = h (⟨k+1, hk1⟩, j) - h (⟨k, by omega⟩, j) := by
    intro k hk1; simp only [hedef]; rw [hvk (k+1) hk1, hvk k (by omega)]
  have hdLv : ∀ k (hk : k < m), dL k = h (⟨k, hk⟩, jL) - h (⟨k, hk⟩, j) := by
    intro k hk; simp only [hdLdef]; rw [hLk k hk, hvk k hk]
  have hdRv : ∀ k (hk : k < m), dR k = h (⟨k, hk⟩, jR) - h (⟨k, hk⟩, j) := by
    intro k hk; simp only [hdRdef]; rw [hRk k hk, hvk k hk]
  have he_pm : ∀ i, i < m - 1 → e i = 1 ∨ e i = -1 := by
    intro i hi
    rw [hev i (by omega)]
    have hadj : adj ((⟨i+1, by omega⟩, j) : Cell m n) (⟨i, by omega⟩, j) := by
      unfold adj gdist; simp only [Fin.val_mk]; omega
    have hvv := hh _ _ hadj
    rcases abs_cases (h (⟨i+1, by omega⟩, j) - h (⟨i, by omega⟩, j))
        with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  have hLwalk : ∀ i, i < m - 1 →
      e i + (dL (i+1) - dL i) = 1 ∨ e i + (dL (i+1) - dL i) = -1 := by
    intro i hi
    have hstep : e i + (dL (i+1) - dL i)
        = h (⟨i+1, by omega⟩, jL) - h (⟨i, by omega⟩, jL) := by
      rw [hev i (by omega), hdLv (i+1) (by omega), hdLv i (by omega)]; ring
    rw [hstep]
    have hadj : adj ((⟨i+1, by omega⟩, jL) : Cell m n) (⟨i, by omega⟩, jL) := by
      unfold adj gdist; simp only [hjLdef, Fin.val_mk]; omega
    have hvv := hh _ _ hadj
    rcases abs_cases (h (⟨i+1, by omega⟩, jL) - h (⟨i, by omega⟩, jL))
        with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  have hRwalk : ∀ i, i < m - 1 →
      e i + (dR (i+1) - dR i) = 1 ∨ e i + (dR (i+1) - dR i) = -1 := by
    intro i hi
    have hstep : e i + (dR (i+1) - dR i)
        = h (⟨i+1, by omega⟩, jR) - h (⟨i, by omega⟩, jR) := by
      rw [hev i (by omega), hdRv (i+1) (by omega), hdRv i (by omega)]; ring
    rw [hstep]
    have hadj : adj ((⟨i+1, by omega⟩, jR) : Cell m n) (⟨i, by omega⟩, jR) := by
      unfold adj gdist; simp only [hjRdef, Fin.val_mk]; omega
    have hvv := hh _ _ hadj
    rcases abs_cases (h (⟨i+1, by omega⟩, jR) - h (⟨i, by omega⟩, jR))
        with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  have hrainbow : ∀ i, i ≤ m - 1 → dL i + dR i = 0 := by
    intro i hi
    have hi' : i < m := by omega
    rw [hdLv i hi', hdRv i hi']
    have hs := hsym ⟨i, hi'⟩
    simp only [hjLdef, hjRdef] at hs ⊢
    omega
  have hconst := rainbow_dL_const he_pm hLwalk hRwalk hrainbow i (by omega)
  rw [hdLv (i+1) hi1, hdLv i (by omega)] at hconst
  simp only [hjLdef] at hconst ⊢
  linarith

private theorem frozenColumn_dL_eq_row0 (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (i : Fin m) :
    h (i, ⟨j.val - 1, by obtain ⟨hj0, _, _⟩ := hfrz; omega⟩) - h (i, j)
    = h (⟨0, hm⟩, ⟨j.val - 1, by obtain ⟨hj0, _, _⟩ := hfrz; omega⟩)
        - h (⟨0, hm⟩, j) := by
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk1 : k < m := by omega
    have hstep := frozenColumn_dL_const_adjacent h hh j hfrz k hk
    have := ih hk1
    linarith

private theorem frozenColumn_slope_exists (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) :
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧
      ∀ i : Fin m, h (i, j) - h (i, ⟨j.val - 1, by
        obtain ⟨hj0, _, _⟩ := hfrz; omega⟩) = k := by
  obtain ⟨hj0, hj1, _⟩ := hfrz
  set jL : Fin n := ⟨j.val - 1, by omega⟩ with hjLdef
  set k : ℤ := h (⟨0, hm⟩, j) - h (⟨0, hm⟩, jL) with hkdef
  have hk_pm : k = 1 ∨ k = -1 := by
    have hadj : adj ((⟨0, hm⟩, j) : Cell m n) (⟨0, hm⟩, jL) := by
      unfold adj gdist; simp only [hjLdef, Fin.val_mk]; omega
    have hvv := hh _ _ hadj
    rcases abs_cases (h (⟨0, hm⟩, j) - h (⟨0, hm⟩, jL)) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      first | (left; omega) | (right; omega)
  refine ⟨k, hk_pm, ?_⟩
  intro i
  have := frozenColumn_dL_eq_row0 h hh hm j ⟨hj0, hj1, ‹_›⟩ i
  simp only [hjLdef] at this ⊢
  linarith



open MiuraHeightEnvelope Finset

def isMaxRow (M : ℕ) (a b : ℕ → ℤ) (i : ℕ) : Prop :=
  (0 < i → a (i-1) = a i - 1) ∧ (i < M → a (i+1) = a i - 1) ∧ b i = a i - 1

def isMinRow (M : ℕ) (a b : ℕ → ℤ) (i : ℕ) : Prop :=
  (0 < i → a (i-1) = a i + 1) ∧ (i < M → a (i+1) = a i + 1) ∧ b i = a i + 1

private theorem boundary_walk_abstract (M : ℕ) (a b : ℕ → ℤ)
    (hA : ∀ i, i < M → a (i+1) - a i = 1 ∨ a (i+1) - a i = -1)
    (hη : ∀ i, i ≤ M → b i - a i = 1 ∨ b i - a i = -1)
    (hB : ∀ i, i < M → b (i+1) - b i = 1 ∨ b (i+1) - b i = -1) :
    ∃ i, i ≤ M ∧ (isMaxRow M a b i ∨ isMinRow M a b i) := by
  by_contra hcon
  have hne : ∀ i, i ≤ M → ¬ isMaxRow M a b i ∧ ¬ isMinRow M a b i :=
    fun i hi => ⟨fun hm => hcon ⟨i, hi, Or.inl hm⟩, fun hm => hcon ⟨i, hi, Or.inr hm⟩⟩
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · subst hM0
    rcases hη 0 (le_refl 0) with hh | hh
    · exact (hne 0 (le_refl 0)).2 ⟨fun h => absurd h (by omega), fun h => absurd h (by omega), by omega⟩
    · exact (hne 0 (le_refl 0)).1 ⟨fun h => absurd h (by omega), fun h => absurd h (by omega), by omega⟩
  · set η0 : ℤ := b 0 - a 0 with hη0def
    have hη0v : η0 = 1 ∨ η0 = -1 := hη 0 (by omega)
    have hε0 : a (0+1) - a 0 = -η0 := by
      have h0 := hne 0 (by omega)
      rcases hA 0 hMpos with he | he <;> rcases hη0v with h1 | h1
      · exact absurd ⟨fun h => absurd h (by omega), fun _ => by omega, by omega⟩ h0.2
      · omega
      · omega
      · exact absurd ⟨fun h => absurd h (by omega), fun _ => by omega, by omega⟩ h0.1
    have key : ∀ i, i ≤ M → (b i - a i = η0) ∧ (i < M → a (i+1) - a i = -η0) := by
      intro i
      induction i with
      | zero => intro _; exact ⟨by omega, fun _ => hε0⟩
      | succ i IH =>
        intro hle
        have hiM : i < M := by omega
        obtain ⟨hηi, hεi_imp⟩ := IH (by omega)
        have hεi : a (i+1) - a i = -η0 := hεi_imp hiM
        have hη_i1 : b (i+1) - a (i+1) = η0 := by
          have hBv := hB i hiM
          have hηnext := hη (i+1) hle
          have hid : (b (i+1) - b i) = (b (i+1) - a (i+1)) - (b i - a i) + (a (i+1) - a i) := by ring
          rcases hη0v with h1 | h1 <;> rcases hBv with hb | hb <;>
            rcases hηnext with hn | hn <;> omega
        refine ⟨hη_i1, ?_⟩
        intro hi1M
        have h1 := hne (i+1) (by omega)
        have hidxL : i + 1 - 1 = i := rfl
        by_contra hcontra
        have hεnextv := hA (i+1) hi1M
        have hεnext : a (i+1+1) - a (i+1) = η0 := by
          rcases hεnextv with h | h <;> rcases hη0v with hz | hz <;> omega
        rcases hη0v with hz | hz
        · exact h1.2 ⟨fun _ => by rw [hidxL]; omega, fun _ => by omega, by omega⟩
        · exact h1.1 ⟨fun _ => by rw [hidxL]; omega, fun _ => by omega, by omega⟩
    have hηM : b M - a M = η0 := (key M (le_refl M)).1
    have hεMm : a M - a (M-1) = -η0 := by
      have h := (key (M-1) (by omega)).2 (by omega)
      have hMm : M - 1 + 1 = M := by omega
      rw [hMm] at h; exact h
    have hneM := hne M (le_refl M)
    rcases hη0v with hz | hz
    · exact hneM.2 ⟨fun _ => by omega, fun h => absurd h (by omega), by omega⟩
    · exact hneM.1 ⟨fun _ => by omega, fun h => absurd h (by omega), by omega⟩

variable {m n : ℕ}

private theorem adj_col0_cases (i : Fin m) (h0 : (0 : ℕ) < n) (u : Cell m n)
    (hu : adj ((i, ⟨0, h0⟩) : Cell m n) u) :
    (∃ (hp : i.val + 1 < m), u = (⟨i.val + 1, hp⟩, ⟨0, h0⟩))
    ∨ (∃ (hp : 0 < i.val), u = (⟨i.val - 1, by omega⟩, ⟨0, h0⟩))
    ∨ (∃ (hq : 1 < n), u = (i, ⟨1, hq⟩)) := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := u
  unfold adj gdist at hu
  have hu' : ((i.val : ℤ) - p).natAbs + ((0 : ℤ) - q).natAbs = 1 := by exact_mod_cast hu
  by_cases hqeq : q = 0
  · subst hqeq
    have hn1 : ((i.val : ℤ) - p).natAbs = 1 := by simpa using hu'
    rcases (Int.natAbs_eq_iff).mp hn1 with hpi | hpi
    · right; left; exact ⟨by omega, by ext <;> simp <;> omega⟩
    · left; exact ⟨by omega, by ext <;> simp <;> omega⟩
  · right; right
    have h0q : ((0 : ℤ) - q).natAbs = q := by simp
    have hq1 : q = 1 := by omega
    have hz : ((i.val : ℤ) - p).natAbs = 0 := by omega
    have hpi : p = i.val := by have := Int.natAbs_eq_zero.mp hz; omega
    subst hq1
    exact ⟨hq, by ext <;> simp <;> omega⟩

private theorem adj_colLast_cases (i : Fin m) (hn : 1 < n) (u : Cell m n)
    (hu : adj ((i, ⟨n-1, by omega⟩) : Cell m n) u) :
    (∃ (hp : i.val + 1 < m), u = (⟨i.val + 1, hp⟩, ⟨n-1, by omega⟩))
    ∨ (∃ (hp : 0 < i.val), u = (⟨i.val - 1, by omega⟩, ⟨n-1, by omega⟩))
    ∨ (u = (i, ⟨n-2, by omega⟩)) := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := u
  unfold adj gdist at hu
  have hu' : ((i.val : ℤ) - p).natAbs + (((n-1 : ℕ) : ℤ) - q).natAbs = 1 := by exact_mod_cast hu
  by_cases hqeq : q = n - 1
  · subst hqeq
    have hn1 : ((i.val : ℤ) - p).natAbs = 1 := by simpa using hu'
    rcases (Int.natAbs_eq_iff).mp hn1 with hpi | hpi
    · right; left; exact ⟨by omega, by ext <;> simp <;> omega⟩
    · left; exact ⟨by omega, by ext <;> simp <;> omega⟩
  · right; right
    have hzq : (((n-1 : ℕ) : ℤ) - q).natAbs = 1 → q = n - 2 ∨ q = n := by
      intro h
      rcases (Int.natAbs_eq_iff).mp h with hh | hh
      · left; omega
      · right; omega
    have hz : ((i.val : ℤ) - p).natAbs = 0 ∧ (((n-1 : ℕ) : ℤ) - q).natAbs = 1 := by
      constructor
      · by_contra hc
        have : ((i.val : ℤ) - p).natAbs ≥ 1 := by omega
        have hqn : (((n-1 : ℕ) : ℤ) - q).natAbs = 0 := by omega
        have := Int.natAbs_eq_zero.mp hqn
        omega
      · omega
    have hpi : p = i.val := by have := Int.natAbs_eq_zero.mp hz.1; omega
    have hqv : q = n - 2 := by
      rcases hzq hz.2 with h | h
      · exact h
      · omega
    exact Prod.ext (Fin.ext hpi) (Fin.ext hqv)

private theorem firstColumn_active (h : Cell m n → ℤ) (hh : IsHeight h)
    (hm : 0 < m) (hn : 1 < n) :
    activeColumn h (⟨0, by omega⟩ : Fin n) := by
  set a : ℕ → ℤ := fun k => h (⟨min k (m-1), by omega⟩, ⟨0, by omega⟩) with hadef
  set b : ℕ → ℤ := fun k => h (⟨min k (m-1), by omega⟩, ⟨1, hn⟩) with hbdef
  have hak : ∀ k (hk : k < m), a k = h (⟨k, hk⟩, ⟨0, by omega⟩) := by
    intro k hk; have hmin : min k (m-1) = k := by omega
    simp only [hadef, hmin]
  have hbk : ∀ k (hk : k < m), b k = h (⟨k, hk⟩, ⟨1, hn⟩) := by
    intro k hk; have hmin : min k (m-1) = k := by omega
    simp only [hbdef, hmin]
  have hA : ∀ i, i < m - 1 → a (i+1) - a i = 1 ∨ a (i+1) - a i = -1 := by
    intro i hi
    rw [hak i (by omega), hak (i+1) (by omega)]
    have hadj : adj ((⟨i, by omega⟩, ⟨0, by omega⟩) : Cell m n) (⟨i+1, by omega⟩, ⟨0, by omega⟩) := by
      unfold adj gdist; simp only [Fin.val_mk]; omega
    have hv := hh _ _ hadj
    rcases abs_cases (h (⟨i, by omega⟩, ⟨0, by omega⟩) - h (⟨i+1, by omega⟩, ⟨0, by omega⟩)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  have hη : ∀ i, i ≤ m - 1 → b i - a i = 1 ∨ b i - a i = -1 := by
    intro i hi
    rw [hak i (by omega), hbk i (by omega)]
    have hadj : adj ((⟨i, by omega⟩, ⟨0, by omega⟩) : Cell m n) (⟨i, by omega⟩, ⟨1, hn⟩) := by
      unfold adj gdist; simp only [Fin.val_mk]; omega
    have hv := hh _ _ hadj
    rcases abs_cases (h (⟨i, by omega⟩, ⟨0, by omega⟩) - h (⟨i, by omega⟩, ⟨1, hn⟩)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  have hB : ∀ i, i < m - 1 → b (i+1) - b i = 1 ∨ b (i+1) - b i = -1 := by
    intro i hi
    rw [hbk i (by omega), hbk (i+1) (by omega)]
    have hadj : adj ((⟨i, by omega⟩, ⟨1, hn⟩) : Cell m n) (⟨i+1, by omega⟩, ⟨1, hn⟩) := by
      unfold adj gdist; simp only [Fin.val_mk]; omega
    have hv := hh _ _ hadj
    rcases abs_cases (h (⟨i, by omega⟩, ⟨1, hn⟩) - h (⟨i+1, by omega⟩, ⟨1, hn⟩)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  obtain ⟨i, hiM, hext⟩ := boundary_walk_abstract (m-1) a b hA hη hB
  have him : i < m := by omega
  refine ⟨⟨i, him⟩, ?_⟩
  have hival : (⟨i, him⟩ : Fin m).val = i := rfl
  rcases hext with hmax | hmin
  · left
    intro u hu
    rcases adj_col0_cases ⟨i, him⟩ (by omega) u hu with ⟨hp, rfl⟩ | ⟨hp, rfl⟩ | ⟨hq, rfl⟩
    · have hc := hmax.2.1 (by omega); rw [hak (i+1) (by omega), hak i him] at hc; simpa using hc
    · have hc := hmax.1 (by omega); rw [hak (i-1) (by omega), hak i him] at hc; simpa using hc
    · have hc := hmax.2.2; rw [hbk i him, hak i him] at hc; simpa using hc
  · right
    intro u hu
    rcases adj_col0_cases ⟨i, him⟩ (by omega) u hu with ⟨hp, rfl⟩ | ⟨hp, rfl⟩ | ⟨hq, rfl⟩
    · have hc := hmin.2.1 (by omega); rw [hak (i+1) (by omega), hak i him] at hc; simpa using hc
    · have hc := hmin.1 (by omega); rw [hak (i-1) (by omega), hak i him] at hc; simpa using hc
    · have hc := hmin.2.2; rw [hbk i him, hak i him] at hc; simpa using hc

private theorem lastColumn_active (h : Cell m n → ℤ) (hh : IsHeight h)
    (hm : 0 < m) (hn : 1 < n) :
    activeColumn h (⟨n-1, by omega⟩ : Fin n) := by
  set a : ℕ → ℤ := fun k => h (⟨min k (m-1), by omega⟩, ⟨n-1, by omega⟩) with hadef
  set b : ℕ → ℤ := fun k => h (⟨min k (m-1), by omega⟩, ⟨n-2, by omega⟩) with hbdef
  have hak : ∀ k (hk : k < m), a k = h (⟨k, hk⟩, ⟨n-1, by omega⟩) := by
    intro k hk; have hmin : min k (m-1) = k := by omega
    simp only [hadef, hmin]
  have hbk : ∀ k (hk : k < m), b k = h (⟨k, hk⟩, ⟨n-2, by omega⟩) := by
    intro k hk; have hmin : min k (m-1) = k := by omega
    simp only [hbdef, hmin]
  have hA : ∀ i, i < m - 1 → a (i+1) - a i = 1 ∨ a (i+1) - a i = -1 := by
    intro i hi
    rw [hak i (by omega), hak (i+1) (by omega)]
    have hadj : adj ((⟨i, by omega⟩, ⟨n-1, by omega⟩) : Cell m n) (⟨i+1, by omega⟩, ⟨n-1, by omega⟩) := by
      unfold adj gdist; simp only [Fin.val_mk]; omega
    have hv := hh _ _ hadj
    rcases abs_cases (h (⟨i, by omega⟩, ⟨n-1, by omega⟩) - h (⟨i+1, by omega⟩, ⟨n-1, by omega⟩)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  have hη : ∀ i, i ≤ m - 1 → b i - a i = 1 ∨ b i - a i = -1 := by
    intro i hi
    rw [hak i (by omega), hbk i (by omega)]
    have hadj : adj ((⟨i, by omega⟩, ⟨n-1, by omega⟩) : Cell m n) (⟨i, by omega⟩, ⟨n-2, by omega⟩) := by
      unfold adj gdist; simp only [Fin.val_mk]; omega
    have hv := hh _ _ hadj
    rcases abs_cases (h (⟨i, by omega⟩, ⟨n-1, by omega⟩) - h (⟨i, by omega⟩, ⟨n-2, by omega⟩)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  have hB : ∀ i, i < m - 1 → b (i+1) - b i = 1 ∨ b (i+1) - b i = -1 := by
    intro i hi
    rw [hbk i (by omega), hbk (i+1) (by omega)]
    have hadj : adj ((⟨i, by omega⟩, ⟨n-2, by omega⟩) : Cell m n) (⟨i+1, by omega⟩, ⟨n-2, by omega⟩) := by
      unfold adj gdist; simp only [Fin.val_mk]; omega
    have hv := hh _ _ hadj
    rcases abs_cases (h (⟨i, by omega⟩, ⟨n-2, by omega⟩) - h (⟨i+1, by omega⟩, ⟨n-2, by omega⟩)) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  obtain ⟨i, hiM, hext⟩ := boundary_walk_abstract (m-1) a b hA hη hB
  have him : i < m := by omega
  refine ⟨⟨i, him⟩, ?_⟩
  have hival : (⟨i, him⟩ : Fin m).val = i := rfl
  rcases hext with hmax | hmin
  · left
    intro u hu
    rcases adj_colLast_cases ⟨i, him⟩ hn u hu with ⟨hp, rfl⟩ | ⟨hp, rfl⟩ | rfl
    · have hc := hmax.2.1 (by omega); rw [hak (i+1) (by omega), hak i him] at hc; simpa using hc
    · have hc := hmax.1 (by omega); rw [hak (i-1) (by omega), hak i him] at hc; simpa using hc
    · have hc := hmax.2.2; rw [hbk i him, hak i him] at hc; simpa using hc
  · right
    intro u hu
    rcases adj_colLast_cases ⟨i, him⟩ hn u hu with ⟨hp, rfl⟩ | ⟨hp, rfl⟩ | rfl
    · have hc := hmin.2.1 (by omega); rw [hak (i+1) (by omega), hak i him] at hc; simpa using hc
    · have hc := hmin.1 (by omega); rw [hak (i-1) (by omega), hak i him] at hc; simpa using hc
    · have hc := hmin.2.2; rw [hbk i him, hak i him] at hc; simpa using hc

private theorem boundary_columns_active (h : Cell m n → ℤ) (hh : IsHeight h)
    (hm : 0 < m) (hn : 1 < n) :
    activeColumn h (⟨0, by omega⟩ : Fin n)
      ∧ activeColumn h (⟨n-1, by omega⟩ : Fin n) :=
  ⟨firstColumn_active h hh hm hn, lastColumn_active h hh hm hn⟩


private theorem transpose_extremum {m n : ℕ} {h : Cell m n → ℤ} {v : Cell n m}
    (hv : IsStrictLocalExtremum (transposeHeight h) v) :
    IsStrictLocalExtremum h (v.2, v.1) := by
  rcases hv with hmax | hmin
  · left
    intro u hu
    apply hmax (u.2, u.1)
    simp only [adj, gdist] at hu ⊢
    omega
  · right
    intro u hu
    apply hmin (u.2, u.1)
    simp only [adj, gdist] at hu ⊢
    omega

/-- Every physical boundary row contains an actual ambient extremum. -/
theorem boundary_rows_occupied {m n : ℕ} {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) :
    RowOccupied h ⟨0, by omega⟩ ∧ RowOccupied h ⟨m - 1, by omega⟩ := by
  obtain ⟨ht, hb⟩ := boundary_columns_active (transposeHeight h) (transpose_isHeight hh) hn (by omega)
  constructor
  · obtain ⟨j, hj⟩ := ht
    exact ⟨j, (transpose_extremum hj).symm⟩
  · obtain ⟨j, hj⟩ := hb
    exact ⟨j, (transpose_extremum hj).symm⟩

/-- An actual unoccupied internal row has one common unit downward slope
on both incident full-width cuts. -/
theorem inactive_row_uniform_cuts {m n : ℕ} {h : Cell m n → ℤ} (hh : IsHeight h)
    (hn : 0 < n) (i : Fin m) (hi : ¬ RowOccupied h i)
    (ht : 0 < i.val) (hb : i.val + 1 < m) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (∀ j : Fin n, h (i, j) = h (⟨i.val - 1, by omega⟩, j) + s) ∧
      (∀ j : Fin n, h (⟨i.val + 1, hb⟩, j) = h (i, j) + s) := by
  have hnot : ¬ activeColumn (transposeHeight h) i := by
    intro hc
    obtain ⟨j, hj⟩ := hc
    exact hi ⟨j, (transpose_extremum hj).symm⟩
  have hfr := inactive_imp_frozenColumn (transposeHeight h) (transpose_isHeight hh) i ht hb hn hnot
  obtain ⟨s, hs, hleft⟩ := frozenColumn_slope_exists (transposeHeight h) (transpose_isHeight hh) hn i hfr
  obtain ⟨ht', hb', hsym⟩ := hfr
  refine ⟨s, hs, ?_, ?_⟩
  · intro j
    have := hleft j
    dsimp [transposeHeight] at this
    omega
  · intro j
    have he := hsym j
    have hl := hleft j
    dsimp [transposeHeight] at he hl
    omega

end D5.S3.Combinatorics.Geometry.MiuraSlabFrozen
