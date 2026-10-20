/- GID: D5/S3/Combinatorics/InversionSeq/ClassCAffine
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/ClassCAffine
   mirror-E: none(waiver:all-depth-labelled-path-affine-invariant)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Fin]
   utility: none
   digest: Integer affine continuation counts retain every site position. -/

import D5.S3.Combinatorics.InversionSeq.ClassCPaths
import D5.S3.Combinatorics.InversionSeq.ClassCInsertion
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.ClassCAffine

open ClassCSites ClassCPaths
open scoped BigOperators

/-- The lower count is the cardinality of the delivered actual path carrier. -/
noncomputable def a (r s k : ℕ) (hs : 1 ≤ s) : ℕ := phi r (lowerState k s hs)

/-- A position sum; equal suffix statistics are deliberately counted repeatedly. -/
def profile (f : ℕ → ℤ) : List Site → ℤ
  | [] => 0
  | _ :: p => f (p.count .U) + profile f p

private theorem profile_positions (f : ℕ → ℤ) (p : List Site) :
    profile f p = ∑ i : Fin p.length, f ((p.drop (i.val + 1)).count .U) := by
  induction p with
  | nil => simp [profile]
  | cons x p ih =>
    simp [profile, Fin.sum_univ_succ, List.drop_succ_cons, ih]

private theorem profile_add (f g : ℕ → ℤ) (p : List Site) :
    profile (fun k => f k + g k) p = profile f p + profile g p := by
  induction p with
  | nil => simp [profile]
  | cons x p ih => simp only [profile, ih]; ring

private theorem profile_sum {ι : Type} [Fintype ι] (f : ι → ℕ → ℤ) (p : List Site) :
    profile (fun k => ∑ i, f i k) p = ∑ i, profile (f i) p := by
  induction p with
  | nil => simp [profile]
  | cons x p ih => simp only [profile, ih, Finset.sum_add_distrib]

private theorem profile_append (f : ℕ → ℤ) (p v : List Site) :
    profile f (p ++ v) = profile (fun k => f (k + v.count .U)) p + profile f v := by
  induction p with
  | nil => simp [profile]
  | cons x p ih => simp only [List.cons_append, profile, List.count_append, ih]; ring

private theorem profile_replicate (f : ℕ → ℤ) (k : ℕ) :
    profile f (List.replicate k .U) = ∑ i : Fin k, f i.val := by
  induction k with
  | zero => simp [profile]
  | succ k ih => simp [List.replicate_succ, profile, ih, Fin.sum_univ_castSucc,
      add_comm]

private theorem profile_new (f : ℕ → ℤ) (p : List Site) (t : ℕ) :
    profile f (p ++ List.replicate t .U ++ [.S]) =
      profile (fun k => f (k + t)) p + (∑ i : Fin t, f i.val) + f 0 := by
  rw [List.append_assoc, profile_append, profile_append]
  simp [profile, profile_replicate, add_assoc]

private theorem phi_zero (q : State) : phi 0 q = 1 := by
  simp [phi, Path]

private theorem phi_step (r : ℕ) (q : State) :
    phi (r + 1) q = (∑ i : Fin q.p.length, phi r (child q (.inl i))) +
      ∑ j : Fin q.s, phi r (child q (.inr j)) := by
  classical
  unfold phi
  change Nat.card ((c : StateChoice q) × Path r (child q c)) = _
  rw [Nat.card_sigma, Fintype.sum_sum_type]

private theorem old_count (r : ℕ) (q : State) :
    (∑ i : Fin q.p.length, (phi r (child q (.inl i)) : ℤ)) =
      profile (fun k => (a r (q.s + 1) k (by omega) : ℤ)) q.p +
        (if q.h then (b r (q.s + 1) (by omega) : ℤ) -
          (a r (q.s + 1) 0 (by omega) : ℤ) else 0) := by
  classical
  rw [profile_positions]
  by_cases hh : q.h = true
  · obtain ⟨p, hp⟩ := q.coherent hh
    have hn : 0 < q.p.length := by simp [hp]
    let last : Fin q.p.length := ⟨q.p.length - 1, by omega⟩
    have he (i : Fin q.p.length) :
        (q.h = true ∧ i.val + 1 = q.p.length) ↔ i = last := by
      simp only [hh, true_and]
      constructor
      · intro hi; apply Fin.ext; dsimp [last]; omega
      · rintro rfl; dsimp [last]; omega
    have hz : (q.p.drop (last.val + 1)).count .U = 0 := by
      have hl : last.val + 1 = q.p.length := by dsimp [last]; omega
      simp [hl]
    have hpoint (i : Fin q.p.length) :
        (phi r (child q (.inl i)) : ℤ) =
          (a r (q.s + 1) ((q.p.drop (i.val + 1)).count .U) (by omega) : ℤ) +
            if i = last then (b r (q.s + 1) (by omega) : ℤ) -
              (a r (q.s + 1) 0 (by omega) : ℤ) else 0 := by
      by_cases hi : i = last
      · subst i; simp only [child, he, if_true, hz, a, b]; ring
      · simp [child, he, hi, a]
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    simp [hh]
  · simp only [child, hh, false_and, if_false, a, Bool.not_eq_true] at *
    simp_all

/-- Existence of affine coefficients is proved before their identification. -/
private theorem affine_coefficients (r : ℕ) :
    ∃ α β : (s : ℕ) → 1 ≤ s → ℤ,
      ∃ γ : (s : ℕ) → 1 ≤ s → ℕ → ℤ,
        ∀ q : State, (phi r q : ℤ) = α q.s q.hs +
          (if q.h then β q.s q.hs else 0) + profile (γ q.s q.hs) q.p := by
  induction r with
  | zero =>
    refine ⟨fun _ _ => 1, fun _ _ => 0, fun _ _ _ => 0, ?_⟩
    intro q
    have hz (p : List Site) : profile (fun _ => 0) p = 0 := by
      induction p <;> simp_all [profile]
    simp [phi_zero, hz]
  | succ r ih =>
    obtain ⟨α, β, γ, ih⟩ := ih
    let α' : (s : ℕ) → 1 ≤ s → ℤ := fun s hs =>
      ∑ t : Fin s, (α (s - t.val) (by have := t.is_lt; omega) +
        β (s - t.val) (by have := t.is_lt; omega) +
        (∑ i : Fin t.val, γ (s - t.val) (by have := t.is_lt; omega) i.val) +
        γ (s - t.val) (by have := t.is_lt; omega) 0)
    let β' : (s : ℕ) → 1 ≤ s → ℤ := fun s _ =>
      (b r (s + 1) (by omega) : ℤ) - (a r (s + 1) 0 (by omega) : ℤ)
    let γ' : (s : ℕ) → 1 ≤ s → ℕ → ℤ := fun s _ k =>
      (a r (s + 1) k (by omega) : ℤ) +
        ∑ t : Fin s, γ (s - t.val) (by have := t.is_lt; omega) (k + t.val)
    refine ⟨α', β', γ', ?_⟩
    intro q
    rw [phi_step, Nat.cast_add, Nat.cast_sum, Nat.cast_sum, old_count]
    have hnew (t : Fin q.s) : (phi r (child q (.inr t)) : ℤ) =
        α (q.s - t.val) (by have := t.is_lt; omega) +
        β (q.s - t.val) (by have := t.is_lt; omega) +
        (∑ i : Fin t.val, γ (q.s - t.val) (by have := t.is_lt; omega) i.val) +
        γ (q.s - t.val) (by have := t.is_lt; omega) 0 +
        profile (fun k => γ (q.s - t.val) (by have := t.is_lt; omega)
          (k + t.val)) q.p := by
      rw [ih]
      simp only [child, if_true, profile_new]
      ring
    simp_rw [hnew]
    simp only [α', β', γ', profile_add, profile_sum, Finset.sum_add_distrib]
    split <;> ring

private theorem profile_telescope (f : ℕ → ℤ) (k : ℕ) :
    profile (fun i => f (i + 1) - f i) (List.replicate k .U) = f k - f 0 := by
  induction k with
  | zero => simp [profile]
  | succ k ih => simp only [List.replicate_succ, profile, List.count_replicate_self, ih]; ring

/-- The universal signed affine identity, with the actual lower and repeat counts. -/
theorem continuation_affine (r : ℕ) (q : State) :
    (phi r q : ℤ) = (a r q.s 0 q.hs : ℤ) +
      (if q.h then (b r q.s q.hs : ℤ) - (a r q.s 1 q.hs : ℤ) else 0) +
      ∑ i : Fin q.p.length,
        ((a r q.s (((q.p.drop (i.val + 1)).count .U) + 1) q.hs : ℤ) -
          (a r q.s ((q.p.drop (i.val + 1)).count .U) q.hs : ℤ)) := by
  obtain ⟨α, β, γ, hc⟩ := affine_coefficients r
  have ha0 (s : ℕ) (hs : 1 ≤ s) : α s hs = (a r s 0 hs : ℤ) := by
    simpa [a, lowerState, profile] using (hc (lowerState 0 s hs)).symm
  have hak (s k : ℕ) (hs : 1 ≤ s) :
      (a r s k hs : ℤ) = α s hs + ∑ i : Fin k, γ s hs i.val := by
    simpa [a, lowerState, profile_replicate] using hc (lowerState k s hs)
  have hg (s k : ℕ) (hs : 1 ≤ s) :
      γ s hs k = (a r s (k + 1) hs : ℤ) - (a r s k hs : ℤ) := by
    rw [hak, hak, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    ring
  have hb (s : ℕ) (hs : 1 ≤ s) :
      β s hs = (b r s hs : ℤ) - (a r s 1 hs : ℤ) := by
    have h1 := hc (repeatState s hs)
    have h2 := hc (lowerState 1 s hs)
    simp [repeatState, lowerState, List.replicate_succ, profile] at h1 h2
    change (b r s hs : ℤ) = _ at h1
    change (a r s 1 hs : ℤ) = _ at h2
    linarith
  rw [hc, ha0, profile_positions]
  simp_rw [hg, hb]

private def seenState (p : List Site) (s : ℕ) (hs : 1 ≤ s) : State :=
  ⟨p ++ [.S], s, hs, true, fun _ => ⟨p, rfl⟩⟩

private theorem continuation_profile (r : ℕ) (q : State) :
    (phi r q : ℤ) = (a r q.s 0 q.hs : ℤ) +
      (if q.h then (b r q.s q.hs : ℤ) - (a r q.s 1 q.hs : ℤ) else 0) +
      profile (fun i => (a r q.s (i + 1) q.hs : ℤ) - (a r q.s i q.hs : ℤ)) q.p := by
  rw [continuation_affine, profile_positions]

private theorem lower_seen_count (r s m : ℕ) (hs : 1 ≤ s) :
    (phi r (seenState (List.replicate m .U) s hs) : ℤ) =
      (a r s m hs : ℤ) + (b r s hs : ℤ) - (a r s 0 hs : ℤ) := by
  have h := continuation_profile r (seenState (List.replicate m .U) s hs)
  change (phi r (seenState (List.replicate m .U) s hs) : ℤ) =
    (a r s 0 hs : ℤ) + ((b r s hs : ℤ) - (a r s 1 hs : ℤ)) +
      profile (fun i => (a r s (i + 1) hs : ℤ) - (a r s i hs : ℤ))
        (List.replicate m .U ++ [.S]) at h
  simp [profile_append, profile] at h
  rw [profile_telescope (fun i => (a r s i hs : ℤ)) m] at h
  linarith

private theorem repeat_seen_count (r s t : ℕ) (hs : 1 ≤ s) :
    (phi r (seenState ([.S] ++ List.replicate t .U) s hs) : ℤ) =
      (a r s (t + 1) hs : ℤ) + (b r s hs : ℤ) - (a r s 0 hs : ℤ) := by
  have h := continuation_profile r (seenState ([.S] ++ List.replicate t .U) s hs)
  change (phi r (seenState ([.S] ++ List.replicate t .U) s hs) : ℤ) =
    (a r s 0 hs : ℤ) + ((b r s hs : ℤ) - (a r s 1 hs : ℤ)) +
      profile (fun i => (a r s (i + 1) hs : ℤ) - (a r s i hs : ℤ))
        (([.S] ++ List.replicate t .U) ++ [.S]) at h
  simp [profile_append, profile] at h
  rw [profile_telescope (fun i => (a r s i hs : ℤ)) t] at h
  simp only [List.singleton_append]
  linarith

private theorem lower_step_integer (r s k : ℕ) (hs : 1 ≤ s) :
    (a (r + 1) s k hs : ℤ) =
      (∑ i : Fin k, (a r (s + 1) i.val (by omega) : ℤ)) +
      ∑ t : Fin s,
        ((a r (s - t.val) (k + t.val) (by have := t.is_lt; omega) : ℤ) +
          (b r (s - t.val) (by have := t.is_lt; omega) : ℤ) -
          (a r (s - t.val) 0 (by have := t.is_lt; omega) : ℤ)) := by
  change (phi (r + 1) (lowerState k s hs) : ℤ) = _
  rw [phi_step, Nat.cast_add, Nat.cast_sum, Nat.cast_sum, old_count]
  change (profile (fun i => (a r (s + 1) i (by omega) : ℤ))
      (List.replicate k .U) + 0) +
      (∑ t : Fin s, (phi r (child (lowerState k s hs) (.inr t)) : ℤ)) = _
  rw [profile_replicate, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  have he : child (lowerState k s hs) (.inr t) =
      seenState (List.replicate (k + t.val) .U) (s - t.val)
        (by have := t.is_lt; omega) := by
    apply State.ext <;> simp only [child, lowerState, seenState, List.replicate_add]
  rw [he]
  exact lower_seen_count r _ _ _

private theorem repeat_step_integer (r s : ℕ) (hs : 1 ≤ s) :
    (b (r + 1) s hs : ℤ) = (b r (s + 1) (by omega) : ℤ) +
      ∑ t : Fin s,
        ((a r (s - t.val) (t.val + 1) (by have := t.is_lt; omega) : ℤ) +
          (b r (s - t.val) (by have := t.is_lt; omega) : ℤ) -
          (a r (s - t.val) 0 (by have := t.is_lt; omega) : ℤ)) := by
  change (phi (r + 1) (repeatState s hs) : ℤ) = _
  rw [phi_step, Nat.cast_add, Nat.cast_sum, Nat.cast_sum, old_count]
  change ((a r (s + 1) 0 (by omega) : ℤ) + 0 +
      ((b r (s + 1) (by omega) : ℤ) - (a r (s + 1) 0 (by omega) : ℤ))) +
      (∑ t : Fin s, (phi r (child (repeatState s hs) (.inr t)) : ℤ)) = _
  have hold : (a r (s + 1) 0 (by omega) : ℤ) + 0 +
      ((b r (s + 1) (by omega) : ℤ) -
        (a r (s + 1) 0 (by omega) : ℤ)) =
      (b r (s + 1) (by omega) : ℤ) := by ring
  rw [hold]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  exact repeat_seen_count r (s - t.val) t.val (by have := t.is_lt; omega)

private theorem cast_bracket (r s k : ℕ) (hs : 1 ≤ s) :
    ((a r s k hs + b r s hs - a r s 0 hs : ℕ) : ℤ) =
      (a r s k hs : ℤ) + (b r s hs : ℤ) - (a r s 0 hs : ℤ) := by
  have hle := (ClassCInsertion.empty_difference r s hs).1
  change a r s 0 hs ≤ b r s hs at hle
  rw [Nat.cast_sub (by omega), Nat.cast_add]

private def originalIndex (s : ℕ) : Fin s ≃ ↥(Finset.Icc 1 s) where
  toFun t := ⟨t.val + 1, Finset.mem_Icc.mpr ⟨by omega, by have := t.is_lt; omega⟩⟩
  invFun j := ⟨j.val - 1, by have := Finset.mem_Icc.mp j.property; omega⟩
  left_inv := by intro t; apply Fin.ext; simp
  right_inv := by intro j; apply Subtype.ext; have := Finset.mem_Icc.mp j.property; dsimp; omega

private theorem original_sum {s : ℕ} (f : (j : ℕ) → 1 ≤ j → j ≤ s → ℕ) :
    (∑ t : Fin s, f (t.val + 1) (by omega) (by have := t.is_lt; omega)) =
      ∑ j : ↥(Finset.Icc 1 s), f j.val (Finset.mem_Icc.mp j.property).1
        (Finset.mem_Icc.mp j.property).2 := by
  exact Fintype.sum_equiv (originalIndex s) _ _ (fun _ => rfl)

/-- Original j=1,...,s recurrence, on actual lower-state path cardinalities. -/
theorem a_recurrence (r s k : ℕ) (hs : 1 ≤ s) :
    a (r + 1) s k hs = (∑ i : Fin k, a r (s + 1) i.val (by omega)) +
      ∑ j : ↥(Finset.Icc 1 s),
        (a r (s - j.val + 1) (k + j.val - 1)
          (by have := Finset.mem_Icc.mp j.property; omega) +
        b r (s - j.val + 1) (by have := Finset.mem_Icc.mp j.property; omega) -
        a r (s - j.val + 1) 0 (by have := Finset.mem_Icc.mp j.property; omega)) := by
  have hz : a (r + 1) s k hs = (∑ i : Fin k, a r (s + 1) i.val (by omega)) +
      ∑ t : Fin s, (a r (s - t.val) (k + t.val) (by have := t.is_lt; omega) +
        b r (s - t.val) (by have := t.is_lt; omega) -
        a r (s - t.val) 0 (by have := t.is_lt; omega)) := by
    apply Int.ofNat_inj.mp
    simp_rw [Nat.cast_add, Nat.cast_sum, cast_bracket]
    exact lower_step_integer r s k hs
  rw [hz]
  congr 1
  have hsl (t : Fin s) : s - (t.val + 1) + 1 = s - t.val := by
    have := t.is_lt; omega
  have hki (t : Fin s) : k + (t.val + 1) - 1 = k + t.val := by omega
  simpa only [hsl, hki] using original_sum (s := s) (fun j hj hjs =>
    a r (s - j + 1) (k + j - 1) (by omega) +
      b r (s - j + 1) (by omega) - a r (s - j + 1) 0 (by omega))

/-- Original j=1,...,s recurrence for the repeat count, including s=1. -/
theorem b_recurrence (r s : ℕ) (hs : 1 ≤ s) :
    b (r + 1) s hs = b r (s + 1) (by omega) +
      ∑ j : ↥(Finset.Icc 1 s),
        (a r (s - j.val + 1) j.val
          (by have := Finset.mem_Icc.mp j.property; omega) +
        b r (s - j.val + 1) (by have := Finset.mem_Icc.mp j.property; omega) -
        a r (s - j.val + 1) 0 (by have := Finset.mem_Icc.mp j.property; omega)) := by
  have hz : b (r + 1) s hs = b r (s + 1) (by omega) +
      ∑ t : Fin s, (a r (s - t.val) (t.val + 1) (by have := t.is_lt; omega) +
        b r (s - t.val) (by have := t.is_lt; omega) -
        a r (s - t.val) 0 (by have := t.is_lt; omega)) := by
    apply Int.ofNat_inj.mp
    simp_rw [Nat.cast_add, Nat.cast_sum, cast_bracket]
    exact repeat_step_integer r s hs
  rw [hz]
  congr 1
  have hsl (t : Fin s) : s - (t.val + 1) + 1 = s - t.val := by
    have := t.is_lt; omega
  simpa only [hsl] using original_sum (s := s) (fun j hj hjs =>
    a r (s - j + 1) j (by omega) + b r (s - j + 1) (by omega) -
      a r (s - j + 1) 0 (by omega))

end D5.S3.Combinatorics.InversionSeq.ClassCAffine
