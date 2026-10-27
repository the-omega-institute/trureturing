/- GID: D5/S3/Combinatorics/Sequenceability/CharacteristicSevenRelativePath
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/CharacteristicSevenRelativePath
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Marked-return connectivity and the complete characteristic-seven relative path. -/

import D5.S3.Combinatorics.Sequenceability.CharacteristicSevenDetour

/-! The four actual marked returns connect the entire six-column carrier.
Deleting the closing endpoint edge gives the exact relative path, including
its full vector inventory and all bounded prefix and interval clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Sequenceability.CharacteristicSevenDetour

open Equiv
open scoped BigOperators
open D5.S1.Words.Sequenceability.RowOrbitLift
open D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
open D5.S3.Combinatorics.PerfectMatchings.FiniteReturnTowers

section FullPath

variable {K : Type*} [Field K] [Finite K] [CharP K 7]

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def markedPoint (r : Kˣ) (u : K) : Fin 4 → carrier (K := K) :=
  ![headOne r u, headTwo r u, target, source]

def markedSet (r : Kˣ) (u : K) : Set (carrier (K := K)) :=
  Set.range (markedPoint r u)

private theorem markedPoint_injective (r : Kˣ) (u : K) :
    Function.Injective (markedPoint r u) := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals
    first
    | rfl
    | (have hc := congrArg (fun z : carrier (K := K) =>
          match z with
          | Sum.inl (a, _) => a.val
          | Sum.inr i => i.val + 6) h
       norm_num [markedPoint, headOne, headTwo, source, target] at hc
       try omega)

def markedEquiv (r : Kˣ) (u : K) : Fin 4 ≃ {x // x ∈ markedSet r u} := by
  classical
  apply Equiv.ofBijective (fun i =>
    ⟨markedPoint r u i, ⟨i, rfl⟩⟩)
  constructor
  · intro i j h
    exact markedPoint_injective r u (Subtype.ext_iff.mp h)
  · intro x
    rcases x.2 with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    exact Subtype.ext hi

def markedCycle : Perm (Fin 4) :=
  swap 0 1 * swap 1 2 * swap 2 3

private theorem markedCycle_apply :
    markedCycle 0 = 1 ∧ markedCycle 1 = 2 ∧ markedCycle 2 = 3 ∧
      markedCycle 3 = 0 := by
  norm_num [markedCycle, Perm.mul_apply, swap_apply_def]

private theorem markedCycle_sameCycle (i j : Fin 4) :
    markedCycle.SameCycle i j := by
  have h01 : markedCycle.SameCycle 0 1 := by
    refine ⟨1, ?_⟩
    simpa [zpow_one] using markedCycle_apply.1
  have h12 : markedCycle.SameCycle 1 2 := by
    refine ⟨1, ?_⟩
    simpa [zpow_one] using markedCycle_apply.2.1
  have h23 : markedCycle.SameCycle 2 3 := by
    refine ⟨1, ?_⟩
    simpa [zpow_one] using markedCycle_apply.2.2.1
  have h30 : markedCycle.SameCycle 3 0 := by
    refine ⟨1, ?_⟩
    simpa [zpow_one] using markedCycle_apply.2.2.2
  fin_cases i <;> fin_cases j
  all_goals first
    | exact Perm.SameCycle.refl _ _
    | exact h01
    | exact h12
    | exact h23
    | exact h30
    | exact h01.symm
    | exact h12.symm
    | exact h23.symm
    | exact h30.symm
    | exact h01.trans h12
    | exact h01.trans (h12.trans h23)
    | exact h01.trans (h12.trans (h23.trans h30))
    | exact h12.trans h23
    | exact h12.trans (h23.trans h30)
    | exact h23.trans h30
    | exact h30.trans h01
    | exact h30.trans (h01.trans h12)

private theorem q_same_cycle_head (r : Kˣ)
    (hrgen : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) (u : K)
    (v : Fin 6 × K) :
    (liftWithEndpoints r (-alpha r u))⁻¹.SameCycle
      (Sum.inl v : carrier (K := K))
      (headOne r u) ↔ initialRow v = -alpha r u := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (carrier (K := K)) := by
    change Fintype ((Fin 6 × K) ⊕ Fin 2)
    infer_instance
  let p := liftWithEndpoints r (-alpha r u)
  change p⁻¹.SameCycle (Sum.inl v : carrier (K := K)) (headOne r u) ↔ _
  constructor
  · intro h
    have h' : p.SameCycle (Sum.inl v : carrier (K := K)) (headOne r u) :=
      (Equiv.Perm.sameCycle_inv).mp h
    obtain ⟨n, hn⟩ := h'.exists_nat_pow_eq
    have hp : ∀ n : ℕ,
        (liftWithEndpoints r (-alpha r u) ^ n)
            (Sum.inl v : carrier (K := K)) =
          Sum.inl ((lift r (-alpha r u) ^ n) v) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ']
        change (liftWithEndpoints r (-alpha r u))
            ((liftWithEndpoints r (-alpha r u) ^ n)
              (Sum.inl v : carrier (K := K))) = _
        rw [ih]
        change Sum.inl
            (lift r (-alpha r u) ((lift r (-alpha r u) ^ n) v)) = _
        rw [pow_succ', Perm.mul_apply]
    rw [hp n] at hn
    change Sum.inl ((lift r (-alpha r u) ^ n) v) =
      Sum.inl (1, alpha r u) at hn
    have hn' := Sum.inl.inj hn
    have hcycle : (lift r (-alpha r u)).SameCycle v (1, alpha r u) :=
      ⟨(n : ℤ), hn'⟩
    have hiff := (lift_same_cycle r hrgen (-alpha r u) v (1, alpha r u)).mp hcycle
    exact hiff.mpr (by simp [initialRow])
  · intro h
    have hhead : initialRow (1, alpha r u) = -alpha r u := by
      simp [initialRow]
    have hbase := (lift_same_cycle r hrgen (-alpha r u) v (1, alpha r u)).mpr
      ⟨(fun _ => hhead), (fun _ => h)⟩
    obtain ⟨n, hn⟩ := hbase.exists_nat_pow_eq
    have hp : ∀ n : ℕ,
        (liftWithEndpoints r (-alpha r u) ^ n)
            (Sum.inl v : carrier (K := K)) =
          Sum.inl ((lift r (-alpha r u) ^ n) v) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ']
        change (liftWithEndpoints r (-alpha r u))
            ((liftWithEndpoints r (-alpha r u) ^ n)
              (Sum.inl v : carrier (K := K))) = _
        rw [ih]
        change Sum.inl
            (lift r (-alpha r u) ((lift r (-alpha r u) ^ n) v)) = _
        rw [pow_succ', Perm.mul_apply]
    refine (Equiv.Perm.sameCycle_inv).mpr ?_
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, hp n, hn]
    rfl

def markedRepair (r : Kˣ) (u : K) :
    Perm {x // x ∈ markedSet r u} :=
  (markedEquiv r u).permCongr markedCycle⁻¹

private theorem marked_repair_extension (r : Kˣ) (u : K) :
    (markedRepair r u).ofSubtype =
      Equiv.swap (headOne r u) (headTwo r u) *
        (Equiv.swap (headOne r u) target *
          Equiv.swap (headOne r u) source) := by
  classical
  ext x
  have hAB : headOne r u ≠ headTwo r u := by
    intro h
    have h' := congrArg (fun z : carrier (K := K) =>
      match z with | Sum.inl (a, _) => a | Sum.inr _ => 0) h
    norm_num [headOne, headTwo] at h'
  have hAS : headOne r u ≠ source := by
    change Sum.inl _ ≠ Sum.inr _
    exact Sum.inl_ne_inr
  have hAT : headOne r u ≠ target := by
    change Sum.inl _ ≠ Sum.inr _
    exact Sum.inl_ne_inr
  have hBS : headTwo r u ≠ source := by
    change Sum.inl _ ≠ Sum.inr _
    exact Sum.inl_ne_inr
  have hBT : headTwo r u ≠ target := by
    change Sum.inl _ ≠ Sum.inr _
    exact Sum.inl_ne_inr
  have hST : source (K := K) ≠ target (K := K) := by
    change (Sum.inr (0 : Fin 2) : carrier (K := K)) ≠ Sum.inr 1
    intro h
    have h' := congrArg (fun z : carrier (K := K) =>
      match z with | Sum.inl _ => (0 : Fin 2) | Sum.inr i => i) h
    norm_num at h'
  by_cases hx : x ∈ markedSet r u
  · obtain ⟨i, rfl⟩ := hx
    have hi : markedPoint r u i ∈ markedSet r u := ⟨i, rfl⟩
    rw [Equiv.Perm.ofSubtype_apply_of_mem (markedRepair r u) hi]
    have heq : (markedEquiv r u).symm
        ⟨markedPoint r u i, hi⟩ = i := by
      calc
        (markedEquiv r u).symm ⟨markedPoint r u i, hi⟩ =
            (markedEquiv r u).symm ((markedEquiv r u) i) := by
              congr 1
        _ = i := (markedEquiv r u).symm_apply_apply i
    simp only [markedRepair, Equiv.permCongr_apply]
    rw [heq]
    fin_cases i
    · change source =
        (Equiv.swap (headOne r u) (headTwo r u))
          ((Equiv.swap (headOne r u) target)
            ((Equiv.swap (headOne r u) source) (headOne r u)))
      rw [Equiv.swap_apply_left]
      rw [Equiv.swap_apply_of_ne_of_ne hAS.symm hST]
      rw [Equiv.swap_apply_of_ne_of_ne hAS.symm hBS.symm]
    · change headOne r u =
        (Equiv.swap (headOne r u) (headTwo r u))
          ((Equiv.swap (headOne r u) target)
            ((Equiv.swap (headOne r u) source) (headTwo r u)))
      rw [Equiv.swap_apply_of_ne_of_ne hAB.symm hBS]
      rw [Equiv.swap_apply_of_ne_of_ne hAB.symm hBT]
      rw [Equiv.swap_apply_right]
    · change headTwo r u =
        (Equiv.swap (headOne r u) (headTwo r u))
          ((Equiv.swap (headOne r u) target)
            ((Equiv.swap (headOne r u) source) target))
      rw [Equiv.swap_apply_of_ne_of_ne hAT.symm hST.symm]
      rw [Equiv.swap_apply_right]
      rw [Equiv.swap_apply_left]
    · change target =
        (Equiv.swap (headOne r u) (headTwo r u))
          ((Equiv.swap (headOne r u) target)
            ((Equiv.swap (headOne r u) source) source))
      rw [Equiv.swap_apply_right]
      rw [Equiv.swap_apply_left]
      rw [Equiv.swap_apply_of_ne_of_ne hAT.symm hBT.symm]
  · have h₁ : x ≠ headOne r u := by
      intro h
      apply hx
      exact ⟨0, h.symm⟩
    have h₂ : x ≠ headTwo r u := by
      intro h
      apply hx
      exact ⟨1, h.symm⟩
    have hs : x ≠ source := by
      intro h
      apply hx
      exact ⟨3, h.symm⟩
    have ht : x ≠ target := by
      intro h
      apply hx
      exact ⟨2, h.symm⟩
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem (p := fun z => z ∈ markedSet r u)
      (markedRepair r u) hx]
    simp only [Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne h₁ hs,
      Equiv.swap_apply_of_ne_of_ne h₁ ht,
      Equiv.swap_apply_of_ne_of_ne h₁ h₂]

private theorem splice_inverse_reattach (r : Kˣ) (u : K) :
    (splice r u)⁻¹ =
      (liftWithEndpoints r (-alpha r u))⁻¹ * (markedRepair r u).ofSubtype := by
  rw [marked_repair_extension]
  simp only [splice, mul_inv_rev, Equiv.swap_inv]
  group

private theorem q_same_cycle_head_two (r : Kˣ)
    (hrgen : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) (u : K) (hu : u ≠ 0)
    (v : Fin 6 × K) :
    (liftWithEndpoints r (-alpha r u))⁻¹.SameCycle
      (Sum.inl v : carrier (K := K))
      (headTwo r u) ↔ initialRow v ≠ -alpha r u := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (carrier (K := K)) := by
    change Fintype ((Fin 6 × K) ⊕ Fin 2)
    infer_instance
  let p := liftWithEndpoints r (-alpha r u)
  change p⁻¹.SameCycle (Sum.inl v : carrier (K := K)) (headTwo r u) ↔ _
  constructor
  · intro h
    have h' : p.SameCycle (Sum.inl v : carrier (K := K)) (headTwo r u) :=
      (Equiv.Perm.sameCycle_inv).mp h
    obtain ⟨n, hn⟩ := h'.exists_nat_pow_eq
    have hp : ∀ n : ℕ,
        (liftWithEndpoints r (-alpha r u) ^ n)
            (Sum.inl v : carrier (K := K)) =
          Sum.inl ((lift r (-alpha r u) ^ n) v) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ']
        change (liftWithEndpoints r (-alpha r u))
            ((liftWithEndpoints r (-alpha r u) ^ n)
              (Sum.inl v : carrier (K := K))) = _
        rw [ih]
        change Sum.inl
            (lift r (-alpha r u) ((lift r (-alpha r u) ^ n) v)) = _
        rw [pow_succ', Perm.mul_apply]
    rw [hp n] at hn
    have hcycle : (lift r (-alpha r u)).SameCycle v (0, beta r u) :=
      ⟨(n : ℤ), Sum.inl.inj hn⟩
    have hiff := (lift_same_cycle r hrgen (-alpha r u) v (0, beta r u)).mp hcycle
    have hb : initialRow (0, beta r u) ≠ -alpha r u := by
      simpa [initialRow] using (show beta r u ≠ -alpha r u from by
        intro he
        have hu0 : u = 0 := by
          dsimp [beta] at he
          linear_combination he
        exact hu hu0)
    exact fun hv => hb (hiff.mp hv)
  · intro h
    have hhead : ¬ initialRow (0, beta r u) = -alpha r u := by
      simpa [initialRow] using (show beta r u ≠ -alpha r u from by
        intro he
        have hu0 : u = 0 := by
          dsimp [beta] at he
          linear_combination he
        exact hu hu0)
    have hbase := (lift_same_cycle r hrgen (-alpha r u) v (0, beta r u)).mpr
      ⟨(fun hv => (h hv).elim), (fun hw => (hhead hw).elim)⟩
    obtain ⟨n, hn⟩ := hbase.exists_nat_pow_eq
    have hp : ∀ n : ℕ,
        (liftWithEndpoints r (-alpha r u) ^ n)
            (Sum.inl v : carrier (K := K)) =
          Sum.inl ((lift r (-alpha r u) ^ n) v) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ']
        change (liftWithEndpoints r (-alpha r u))
            ((liftWithEndpoints r (-alpha r u) ^ n)
              (Sum.inl v : carrier (K := K))) = _
        rw [ih]
        change Sum.inl
            (lift r (-alpha r u) ((lift r (-alpha r u) ^ n) v)) = _
        rw [pow_succ', Perm.mul_apply]
    refine (Equiv.Perm.sameCycle_inv).mpr ?_
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, hp n, hn]
    rfl

private theorem marked_cycle_injective (r : Kˣ) (u : K) (hu : u ≠ 0)
    (hrgen : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) (i j : Fin 4)
    (h : (liftWithEndpoints r (-alpha r u))⁻¹.SameCycle
      (markedPoint r u i) (markedPoint r u j)) : i = j := by
  letI : Finite (carrier (K := K)) := by
    change Finite ((Fin 6 × K) ⊕ Fin 2)
    infer_instance
  let p : Perm (carrier (K := K)) := (liftWithEndpoints r (-alpha r u))⁻¹
  have h12 : ¬ (liftWithEndpoints r (-alpha r u))⁻¹.SameCycle
      (headOne r u) (headTwo r u) := by
    intro hh
    have hb := (q_same_cycle_head_two r hrgen u hu (1, alpha r u)).mp hh
    exact hb (by simp [initialRow])
  have h21 : ¬ (liftWithEndpoints r (-alpha r u))⁻¹.SameCycle
      (headTwo r u) (headOne r u) := by
    intro hh
    exact h12 (Equiv.Perm.SameCycle.symm hh)
  have hsource : ∀ y : carrier (K := K),
      (liftWithEndpoints r (-alpha r u))⁻¹.SameCycle source y → y = source := by
    intro y hy
    obtain ⟨n, hn⟩ := hy.exists_nat_pow_eq
    have hs : (p ^ n) source = source := by
      exact Function.IsFixedPt.perm_pow (show Function.IsFixedPt p source by
        rfl) n
    have hs' : ((liftWithEndpoints r (-alpha r u))⁻¹ ^ n) source = source := by
      simpa [p] using hs
    rw [hs'] at hn
    exact hn.symm
  have htarget : ∀ y : carrier (K := K),
      (liftWithEndpoints r (-alpha r u))⁻¹.SameCycle target y → y = target := by
    intro y hy
    obtain ⟨n, hn⟩ := hy.exists_nat_pow_eq
    have hs : (p ^ n) target = target := by
      exact Function.IsFixedPt.perm_pow (show Function.IsFixedPt p target by
        rfl) n
    have hs' : ((liftWithEndpoints r (-alpha r u))⁻¹ ^ n) target = target := by
      simpa [p] using hs
    rw [hs'] at hn
    exact hn.symm
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact (h12 (by simpa [markedPoint] using h)).elim
    | exact (h21 (by simpa [markedPoint] using h)).elim
    | (have he := htarget _ (by simpa [markedPoint] using h)
       simp [headOne, headTwo, source, target, Fin.ext_iff] at he)
    | (have he := htarget _ (by simpa [markedPoint] using h.symm)
       simp [headOne, headTwo, source, target, Fin.ext_iff] at he)
    | (have he := hsource _ (by simpa [markedPoint] using h)
       simp [headOne, headTwo, source, target, Fin.ext_iff] at he)
    | (have he := hsource _ (by simpa [markedPoint] using h.symm)
       simp [headOne, headTwo, source, target, Fin.ext_iff] at he)

private theorem marked_return_data (r : Kˣ) (u : K) (hu : u ≠ 0)
    (hrgen : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) :
    ∀ z : {x // x ∈ markedSet r u}, ∃ n : ℕ,
      FirstVisit (liftWithEndpoints r (-alpha r u))⁻¹
        (markedSet r u) (z : carrier (K := K)) n ∧
      (((liftWithEndpoints r (-alpha r u))⁻¹ ^ n) (z : carrier (K := K))) = z := by
  intro z
  letI : Finite (carrier (K := K)) := by
    change Finite ((Fin 6 × K) ⊕ Fin 2)
    infer_instance
  let p : Perm (carrier (K := K)) := (liftWithEndpoints r (-alpha r u))⁻¹
  let n := orbitPeriod p (z : carrier (K := K))
  have hn : 0 < n ∧ (p ^ n) (z : carrier (K := K)) = z :=
    (orbit_period_spec p (z : carrier (K := K))).1
  refine ⟨n, ?_, hn.2⟩
  refine ⟨hn.1, ?_, ?_⟩
  · rw [hn.2]
    exact z.property
  · intro k hk hkn hmem
    obtain ⟨j, hj⟩ := hmem
    obtain ⟨i, hi⟩ := z.property
    have hpow : (p ^ k) (markedPoint r u i) = markedPoint r u j := by
      calc
        (p ^ k) (markedPoint r u i) = (p ^ k) (z : carrier (K := K)) :=
          congrArg (p ^ k) hi
        _ = markedPoint r u j := by simpa [p] using hj.symm
    have hij := marked_cycle_injective r u hu hrgen i j
      (show p.SameCycle (markedPoint r u i) (markedPoint r u j) from
        ⟨(k : ℤ), by simpa [zpow_natCast] using hpow⟩)
    have hret : (p ^ k) (z : carrier (K := K)) = z := by
      calc
        (p ^ k) (z : carrier (K := K)) = (p ^ k) (markedPoint r u i) :=
          congrArg (p ^ k) hi.symm
        _ = markedPoint r u j := hpow
        _ = markedPoint r u i := by rw [hij]
        _ = z := hi
    have hle := (orbit_period_spec p (z : carrier (K := K))).2 ⟨hk, hret⟩
    exact (Nat.not_lt_of_ge hle) hkn

private theorem splice_is_cycle (r : Kˣ) (u : K) (hu : u ≠ 0)
    (hrgen : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) :
    ∀ x y : carrier (K := K), (splice r u).SameCycle x y := by
  letI : Finite (carrier (K := K)) := by
    change Finite ((Fin 6 × K) ⊕ Fin 2)
    infer_instance
  let p : Perm (carrier (K := K)) := liftWithEndpoints r (-alpha r u)
  let S : Set (carrier (K := K)) := markedSet r u
  let J : Perm S := markedRepair r u
  have hmeet : ∀ x : carrier (K := K), ∃ z : S, p⁻¹.SameCycle x z := by
    intro x
    rcases x with v | i
    · by_cases hv : initialRow v = -alpha r u
      · exact ⟨⟨headOne r u, ⟨0, rfl⟩⟩,
          (q_same_cycle_head r hrgen u v).2 hv⟩
      · exact ⟨⟨headTwo r u, ⟨1, rfl⟩⟩,
          (q_same_cycle_head_two r hrgen u hu v).2 hv⟩
    · fin_cases i
      · exact ⟨⟨source, ⟨3, rfl⟩⟩, Perm.SameCycle.refl _ _⟩
      · exact ⟨⟨target, ⟨2, rfl⟩⟩, Perm.SameCycle.refl _ _⟩
  have hreturn : ∀ z : S, ∃ n : ℕ,
      FirstVisit p⁻¹ S (z : carrier (K := K)) n ∧
        ((p⁻¹ ^ n) (z : carrier (K := K))) = z := by
    intro z
    simpa only [p, S] using marked_return_data r u hu hrgen z
  have hJcycle : ∀ x y : S, J.SameCycle x y := by
    intro x y
    obtain ⟨i, hi⟩ := x.property
    obtain ⟨j, hj⟩ := y.property
    have hxi : x = markedEquiv r u i := by
      apply Subtype.ext
      exact hi.symm
    have hyj : y = markedEquiv r u j := by
      apply Subtype.ext
      exact hj.symm
    rw [hxi, hyj]
    have hsc : (markedCycle⁻¹).SameCycle i j :=
      (Equiv.Perm.sameCycle_inv).mpr (markedCycle_sameCycle i j)
    exact (D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch.same_cycle_perm_congr
      (markedEquiv r u) markedCycle⁻¹ i j).mpr hsc
  let f : Perm (carrier (K := K)) := p⁻¹ * J.ofSubtype
  have hmarked : ∀ x y : S, f.SameCycle x y := by
    intro x y
    apply (same_cycle_of_first_visit f S J ?_ x y).mpr (hJcycle x y)
    intro z
    obtain ⟨n, hn, hend⟩ := hreturn (J z)
    obtain ⟨hfirst, hjump⟩ := first_visit_reattach p⁻¹ S J z n hn
    exact ⟨n, hfirst, hjump.trans hend⟩
  -- Every old inverse edge is connected by the repaired orbit. At marked
  -- tails, the already proved four-point return supplies the missing link.
  have hstep : ∀ x : carrier (K := K), f.SameCycle x (p⁻¹ x) := by
    intro x
    by_cases hx : x ∈ S
    · let z : S := ⟨x, hx⟩
      have he : f (J⁻¹ z : S) = p⁻¹ x := by
        simp [f, Perm.mul_apply, Perm.ofSubtype_apply_coe, z]
      exact (hmarked z (J⁻¹ z)).trans
        (he ▸ (Perm.SameCycle.refl f (J⁻¹ z : S)).apply_right)
    · have he : f x = p⁻¹ x := by
        simp [f, Perm.mul_apply, Perm.ofSubtype_apply_of_not_mem J hx]
      exact he ▸ (Perm.SameCycle.refl f x).apply_right
  have hfull : ∀ x y : carrier (K := K), f.SameCycle x y := by
    have hto : ∀ x : carrier (K := K), ∃ z : S, f.SameCycle x z := by
      intro x
      obtain ⟨z, hz⟩ := hmeet x
      obtain ⟨n, hn⟩ := hz.exists_nat_pow_eq
      refine ⟨z, hn ▸ ?_⟩
      clear hn
      induction n with
      | zero => exact Perm.SameCycle.refl f x
      | succ n ih =>
        rw [pow_succ', Perm.mul_apply]
        exact ih.trans (hstep ((p⁻¹ ^ n) x))
    intro x y
    obtain ⟨zx, hx⟩ := hto x
    obtain ⟨zy, hy⟩ := hto y
    exact hx.trans ((hmarked zx zy).trans hy.symm)
  intro x y
  have hinv : (splice r u)⁻¹ = p⁻¹ * J.ofSubtype := by
    simpa [p, J] using splice_inverse_reattach r u
  have hxy : (splice r u)⁻¹.SameCycle x y := by
    rw [hinv]
    exact hfull x y
  exact (Equiv.Perm.sameCycle_inv).mp hxy

private theorem endpoint_vertices_injective (u : K) (hu : u ≠ 0) :
    Function.Injective (vertexWithEndpoints u) := by
  obtain ⟨_, _, _, _, hvertices, _⟩ := exists_characteristic_seven_lift K 0
  intro x y h
  rcases x with x | i <;> rcases y with y | j
  · exact congrArg Sum.inl (hvertices.2.1 trivial trivial h)
  · have hn := hvertices.1 (show x ∈ Set.univ from trivial)
    fin_cases j <;> apply False.elim <;> apply hn <;>
      simpa [vertexWithEndpoints] using congrArg Prod.fst h
  · have hn := hvertices.1 (show y ∈ Set.univ from trivial)
    fin_cases i <;> apply False.elim <;> apply hn <;>
      simpa [vertexWithEndpoints] using congrArg Prod.fst h.symm
  · fin_cases i <;> fin_cases j
    · rfl
    · apply False.elim
      apply hu
      simpa [vertexWithEndpoints] using (congrArg Prod.snd h).symm
    · apply False.elim
      apply hu
      simpa [vertexWithEndpoints] using congrArg Prod.snd h
    · rfl

/-- The actual overlapping two-head surgery gives a complete relative path.
The bounded functions also specify vertex and label lists, including all
prefixes, the full interval, and both endpoint values. -/
theorem exists_characteristic_seven_relative_path (K : Type*)
    [Field K] [Finite K] [CharP K 7] (u : K) (hu : u ≠ 0) :
    let N := 6 * Nat.card K + 1
    ∃ v w : ℕ → ZMod 7 × K,
      v 0 = (0, 0) ∧ v N = (0, u) ∧
      Function.Injective (fun i : Fin (N + 1) => v i.val) ∧
      Set.range (fun i : Fin (N - 1) => v (i.val + 1)) = {z | z.1 ≠ 0} ∧
      (∀ n < N, w n = v (n + 1) - v n) ∧
      Function.Injective (fun i : Fin N => w i.val) ∧
      Set.range (fun i : Fin N => w i.val) = {z | z.1 ≠ 0 ∨ z = (0, u)} ∧
      (List.ofFn (fun i : Fin (N + 1) => v i.val)).length = 6 * Nat.card K + 2 ∧
      (List.ofFn (fun i : Fin N => w i.val)).length = 6 * Nat.card K + 1 ∧
      (List.ofFn (fun i : Fin (N + 1) => v i.val)).Nodup ∧
      (List.ofFn (fun i : Fin N => w i.val)).Nodup ∧
      (∀ n ≤ N, (∑ i ∈ Finset.range n, w i) = v n) ∧
      Function.Injective (fun n : Fin (N + 1) => ∑ i ∈ Finset.range n.val, w i) ∧
      (∀ a b : ℕ, a < b → b ≤ N → (∑ i ∈ Finset.Ico a b, w i) ≠ 0) ∧
      (∑ i ∈ Finset.range N, w i) = (0, u) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (carrier (K := K)) := by
    change Fintype ((Fin 6 × K) ⊕ Fin 2)
    infer_instance
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hrgen : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z := by
    intro z
    exact (Submonoid.mem_powers_iff z r).mp (mem_powers_iff_mem_zpowers.mpr (hr z))
  have hrn := generator_add_one_ne_zero r hrgen
  let N := 6 * Nat.card K + 1
  let q := splice r u
  have hc : Fintype.card (carrier (K := K)) = N + 1 := by
    simp [carrier, N, Nat.card_eq_fintype_card, Nat.add_assoc]
  have hcycle : q.IsCycleOn (Finset.univ : Finset (carrier (K := K))) := by
    refine ⟨?_, ?_⟩
    · simpa using q.bijective.bijOn_univ
    · intro x _ y _
      exact splice_is_cycle r u hu hrgen x y
  let e : ℕ → carrier (K := K) := fun n => (q ^ n) source
  have einj : Function.Injective (fun i : Fin (N + 1) => e i.val) := by
    intro i j hij
    apply Fin.ext
    exact hcycle.injOn_pow_apply (Finset.mem_univ source)
      (by simpa [hc] using i.isLt) (by simpa [hc] using j.isLt) hij
  have esurj : ∀ x : carrier (K := K), ∃ i : Fin (N + 1), e i.val = x := by
    intro x
    obtain ⟨n, hn, he⟩ := hcycle.exists_pow_eq (Finset.mem_univ source) (Finset.mem_univ x)
    exact ⟨⟨n, by simpa [hc] using hn⟩, he⟩
  have eN : e N = target := by
    apply q.injective
    have hclose := (six_column_splice_seams r u hu hrn).2.2.2.1
    change q (e N) = q target
    rw [hclose]
    change (q * q ^ N) source = source
    rw [← pow_succ']
    simpa [hc] using hcycle.pow_card_apply (Finset.mem_univ source)
  have enotT : ∀ n < N, e n ≠ target := by
    intro n hn he
    have hi : (⟨n, by omega⟩ : Fin (N + 1)) = ⟨N, by omega⟩ :=
      einj (he.trans eN.symm)
    have hv : n = N := congrArg (fun i : Fin (N + 1) => i.val) hi
    omega
  let v : ℕ → ZMod 7 × K := fun n => vertexWithEndpoints u (e n)
  let w : ℕ → ZMod 7 × K := fun n => v (n + 1) - v n
  have hv0 : v 0 = (0, 0) := by simp [v, e, vertexWithEndpoints, source]
  have hvN : v N = (0, u) := by simp [v, eN, vertexWithEndpoints, target]
  have vinj : Function.Injective (fun i : Fin (N + 1) => v i.val) := by
    intro i j h
    exact einj (endpoint_vertices_injective u hu h)
  have einterior : ∀ n, 0 < n → n < N → ∃ x : Fin 6 × K, e n = Sum.inl x := by
    intro n hn hnN
    rcases he : e n with x | i
    · exact ⟨x, rfl⟩
    · fin_cases i
      · have hi : (⟨n, by omega⟩ : Fin (N + 1)) = ⟨0, by dsimp [N]; omega⟩ := einj he
        have hv : n = 0 := congrArg (fun i : Fin (N + 1) => i.val) hi
        omega
      · exact (enotT n hnN he).elim
  have hvertices := (exists_characteristic_seven_lift K 0).choose_spec.2.2.2.1
  have interior : Set.range (fun i : Fin (N - 1) => v (i.val + 1)) = {z | z.1 ≠ 0} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨x, hx⟩ := einterior (i.val + 1) (by omega) (by have := i.isLt; dsimp [N] at *; omega)
      change (vertexWithEndpoints u (e (i.val + 1))).1 ≠ 0
      rw [hx]
      exact hvertices.1 trivial
    · intro hz
      obtain ⟨x, _, hx⟩ := hvertices.2.2 hz
      obtain ⟨i, hi⟩ := esurj (Sum.inl x)
      have hi0 : 0 < i.val := by
        by_contra h
        have hi0 : i.val = 0 := by omega
        have hbad : source (K := K) = Sum.inl x := by simpa [e, hi0] using hi
        exact Sum.inr_ne_inl hbad
      have hiN : i.val < N := by
        have hne : i.val ≠ N := by
          intro he
          have hbad : target (K := K) = Sum.inl x := by simpa [he, eN] using hi
          exact Sum.inr_ne_inl hbad
        have := i.isLt
        omega
      refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
      change vertexWithEndpoints u (e (i.val - 1 + 1)) = z
      rw [Nat.sub_add_cancel (by omega), hi]
      exact hx
  have hw (n : ℕ) : w n = vertexWithEndpoints u (q (e n)) - vertexWithEndpoints u (e n) := by
    dsimp [w, v, e]
    rw [pow_succ', Perm.mul_apply]
  have labelbij := splice_labels_bijective r u hu hrn
  have winj : Function.Injective (fun i : Fin N => w i.val) := by
    intro i j hij
    have heij : e i.val = e j.val := labelbij.2.1 (enotT _ i.isLt)
      (enotT _ j.isLt) (by simpa only [hw] using hij)
    have hi : (⟨i.val, by omega⟩ : Fin (N + 1)) = ⟨j.val, by omega⟩ := einj heij
    exact Fin.ext (congrArg (fun i : Fin (N + 1) => i.val) hi)
  have labels : Set.range (fun i : Fin N => w i.val) = {z | z.1 ≠ 0 ∨ z = (0, u)} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      change w i.val ∈ _
      rw [hw]
      exact labelbij.1 (enotT _ i.isLt)
    · intro hz
      obtain ⟨x, hx, he⟩ := labelbij.2.2 hz
      obtain ⟨i, hi⟩ := esurj x
      have hiN : i.val < N := by
        have hne : i.val ≠ N := by
          intro heq
          exact hx (hi.symm.trans (by rw [heq, eN]))
        have := i.isLt
        omega
      refine ⟨⟨i.val, hiN⟩, ?_⟩
      change w i.val = z
      rw [hw, hi]
      exact he
  have hsum (n : ℕ) : (∑ i ∈ Finset.range n, w i) = v n := by
    change (∑ i ∈ Finset.range n, (v (i + 1) - v i)) = v n
    rw [Finset.sum_range_sub, show v 0 = 0 from hv0, sub_zero]
  refine ⟨v, w, hv0, hvN, vinj, interior, (fun _ _ => rfl), winj, labels,
    ?_, ?_, ?_, ?_, (fun n _ => hsum n), ?_, ?_, ?_⟩
  · simp [N, Nat.add_assoc]
  · simp [N]
  · exact List.nodup_ofFn.mpr vinj
  · exact List.nodup_ofFn.mpr winj
  · simpa only [hsum] using vinj
  · intro a b hab hb hzero
    have hi : (∑ i ∈ Finset.Ico a b, w i) = v b - v a := by
      rw [Finset.sum_Ico_eq_sub _ hab.le, hsum, hsum]
    have heq : v b = v a := sub_eq_zero.mp (hi.symm.trans hzero)
    have hij : (⟨b, by omega⟩ : Fin (N + 1)) = ⟨a, by omega⟩ := vinj heq
    have heab : b = a := congrArg (fun i : Fin (N + 1) => i.val) hij
    omega
  · rw [hsum, hvN]

end

end FullPath

end D5.S1.Words.Sequenceability.CharacteristicSevenDetour
