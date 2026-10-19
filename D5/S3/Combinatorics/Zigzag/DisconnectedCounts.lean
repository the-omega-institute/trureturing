/- GID: D5/S3/Combinatorics/Zigzag/DisconnectedCounts
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/DisconnectedCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Card, mathlib/module/Mathlib.Data.Fintype.Sigma]
   utility: none
   digest: Literal disconnected-choice cardinalities and their parity boundary cases. -/

import D5.S3.Combinatorics.Zigzag.DisconnectedMarking
import D5.S3.Combinatorics.Zigzag.DisconnectedReflection
import D5.S3.Combinatorics.Zigzag.DisconnectedRealization
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

private theorem even_coded_one_missing (b : Bool) (w : Fin (1-1) → Bool) :
    ¬ Active (evenCodedChoice 1 (by omega) b w).1 (if b then -1 else 1) := by
  have hw : w = (fun i => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  subst w
  cases b <;> unfold Active <;> decide

private theorem odd_coded_one_missing (b : Bool) (w : Fin (1-1) → Bool) :
    ¬ Active (oddCodedChoice 1 (by omega) b w).1 (if b then -1 else 1) := by
  have hw : w = (fun i => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  subst w
  cases b <;> unfold Active <;> decide

private theorem even_one_positive_connected
    (p : {p : EvenPath .positive 0 // evenPathCharge p = 0}) :
    ActiveConnected (evenPathChoices 1 (by omega) p.1) := by
  classical
  by_contra hd
  have hc : Balanced (evenPathChoices 1 (by omega) p.1) :=
    (evenZeroPathChoices 1 (by omega) (Sum.inl p)).2
  obtain ⟨hap, ham, color, hp, hm, he⟩ :=
    (actual_disconnected_iff_coloring 2 (by omega) _ hc).mp hd
  obtain ⟨b, w, hcode⟩ := even_native_separation_code 1 (by omega) p.1 color hp hm he
  have hmissing := even_coded_one_missing b w
  change ¬ Active (evenPathChoices 1 (by omega) (evenCodedPath 1 (by omega) b w).1)
    (if b then -1 else 1) at hmissing
  rw [← hcode] at hmissing
  cases b
  · exact hmissing hap
  · exact hmissing ham

private theorem odd_one_positive_connected
    (p : {p : OddPath .positive 2 // oddPathCharge p = 0}) :
    ActiveConnected (oddPathChoices 1 (by omega) p.1) := by
  classical
  by_contra hd
  have hc : Balanced (oddPathChoices 1 (by omega) p.1) :=
    (oddZeroPathChoices 1 (by omega) (Sum.inl p)).2
  obtain ⟨hap, ham, color, hp, hm, he⟩ :=
    (actual_disconnected_iff_coloring 3 (by omega) _ hc).mp hd
  obtain ⟨b, w, hcode⟩ := odd_native_separation_code 1 (by omega) p.1 color hp hm he
  have hmissing := odd_coded_one_missing b w
  change ¬ Active (oddPathChoices 1 (by omega) (oddCodedPath 1 (by omega) b w).1)
    (if b then -1 else 1) at hmissing
  rw [← hcode] at hmissing
  cases b
  · exact hmissing hap
  · exact hmissing ham

private theorem even_one_connected (c : Choices 2) (hc : Balanced c) :
    ActiveConnected c := by
  obtain ⟨p, hp⟩ := (evenBalancedChoicesEquiv 1 (by omega)).symm.surjective ⟨c, hc⟩
  have hpc := congrArg Subtype.val hp
  cases p with
  | inl p =>
      change evenPathChoices 1 (by omega) p.1 = c at hpc
      rw [← hpc]
      exact even_one_positive_connected p
  | inr p =>
      change evenPathChoices 1 (by omega) p.1 = c at hpc
      rw [← hpc]
      let q := (evenZeroChargeReflection 0).symm p
      have hq : evenPathReflection 0 q.1 = p.1 :=
        congrArg Subtype.val ((evenZeroChargeReflection 0).apply_symm_apply p)
      rw [← hq]
      exact (even_reflection_connected 1 (by omega) q.1).mpr
        (even_one_positive_connected q)

private theorem odd_one_connected (c : Choices 3) (hc : Balanced c) :
    ActiveConnected c := by
  obtain ⟨p, hp⟩ := (oddBalancedChoicesEquiv 1 (by omega)).symm.surjective ⟨c, hc⟩
  have hpc := congrArg Subtype.val hp
  cases p with
  | inl p =>
      change oddPathChoices 1 (by omega) p.1 = c at hpc
      rw [← hpc]
      exact odd_one_positive_connected p
  | inr p =>
      change oddPathChoices 1 (by omega) p.1 = c at hpc
      rw [← hpc]
      let q := (oddZeroChargeReflection 2).symm p
      have hq : oddPathReflection 2 q.1 = p.1 :=
        congrArg Subtype.val ((oddZeroChargeReflection 2).apply_symm_apply p)
      rw [← hq]
      exact (odd_reflection_connected 1 (by omega) q.1).mpr
        (odd_one_positive_connected q)

/-- The even r=1 case counts actual labelled balanced choices with active connectivity. -/
theorem disconnectedCount_two : disconnectedCount 2 = 0 := by
  classical
  unfold disconnectedCount
  apply Finset.card_eq_zero.mpr
  apply Finset.ext
  intro c
  constructor
  · intro hc
    have hh : Balanced c ∧ ¬ ActiveConnected c := (Finset.mem_filter.mp hc).2
    exact False.elim (hh.2 (even_one_connected c hh.1))
  · intro hc
    exact False.elim (by simpa using hc)

/-- The odd r=1 case uses the singleton-cap native parity equivalence. -/
theorem disconnectedCount_three : disconnectedCount 3 = 0 := by
  classical
  unfold disconnectedCount
  apply Finset.card_eq_zero.mpr
  apply Finset.ext
  intro c
  constructor
  · intro hc
    have hh : Balanced c ∧ ¬ ActiveConnected c := (Finset.mem_filter.mp hc).2
    exact False.elim (hh.2 (odd_one_connected c hh.1))
  · intro hc
    exact False.elim (by simpa using hc)

/-- Absolute successor words omit exactly the constant initial-state word. -/
abbrev DisconnectedCode (l : Nat) :=
  (b : Bool) × {w : Fin l → Bool // w ≠ (fun _ => b)}

private theorem even_code_path_injective (r : Nat) (hr : 1 ≤ r)
    (x y : DisconnectedCode (r-1))
    (h : evenCodedPath r hr x.1 x.2.1 = evenCodedPath r hr y.1 y.2.1) : x = y := by
  obtain ⟨b, w, hw⟩ := x
  obtain ⟨b', w', hw'⟩ := y
  have hc : evenCodedChoice r hr b w = evenCodedChoice r hr b' w' := by
    unfold evenCodedChoice
    rw [h]
  have hi := @evenCodedChoice_injective r hr (b,w) (b',w') hc
  have hb := congrArg Prod.fst hi
  have he := congrArg Prod.snd hi
  cases hb
  cases he
  rfl

private theorem odd_code_path_injective (r : Nat) (hr : 1 ≤ r)
    (x y : DisconnectedCode (r-1))
    (h : oddCodedPath r hr x.1 x.2.1 = oddCodedPath r hr y.1 y.2.1) : x = y := by
  obtain ⟨b, w, hw⟩ := x
  obtain ⟨b', w', hw'⟩ := y
  have hc : oddCodedChoice r hr b w = oddCodedChoice r hr b' w' := by
    unfold oddCodedChoice
    rw [h]
  have hi := @oddCodedChoice_injective r hr (b,w) (b',w') hc
  have hb := congrArg Prod.fst hi
  have he := congrArg Prod.snd hi
  cases hb
  cases he
  rfl

private noncomputable def even_sector_path (r : Nat) (hr : 1 ≤ r) :
    DisconnectedCode (r-1) ⊕ DisconnectedCode (r-1) → EvenZeroPaths r
  | .inl x => .inl (evenCodedPath r hr x.1 x.2.1)
  | .inr x => .inr (evenZeroChargeReflection _ (evenCodedPath r hr x.1 x.2.1))

private noncomputable def odd_sector_path (r : Nat) (hr : 1 ≤ r) :
    DisconnectedCode (r-1) ⊕ DisconnectedCode (r-1) → OddZeroPaths r
  | .inl x => .inl (oddCodedPath r hr x.1 x.2.1)
  | .inr x => .inr (oddZeroChargeReflection _ (oddCodedPath r hr x.1 x.2.1))

private theorem even_sector_path_injective (r : Nat) (hr : 1 ≤ r) :
    Function.Injective (even_sector_path r hr) := by
  intro x y h
  cases x with
  | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (even_code_path_injective r hr x y (Sum.inl.inj h))
      | inr y => cases h
  | inr x =>
      cases y with
      | inl y => cases h
      | inr y => exact congrArg Sum.inr (even_code_path_injective r hr x y
          ((evenZeroChargeReflection _).injective (Sum.inr.inj h)))

private theorem odd_sector_path_injective (r : Nat) (hr : 1 ≤ r) :
    Function.Injective (odd_sector_path r hr) := by
  intro x y h
  cases x with
  | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (odd_code_path_injective r hr x y (Sum.inl.inj h))
      | inr y => cases h
  | inr x =>
      cases y with
      | inl y => cases h
      | inr y => exact congrArg Sum.inr (odd_code_path_injective r hr x y
          ((oddZeroChargeReflection _).injective (Sum.inr.inj h)))

private theorem even_sector_disconnected (r : Nat) (hr : 1 ≤ r)
    (x : DisconnectedCode (r-1) ⊕ DisconnectedCode (r-1)) :
    ¬ ActiveConnected (evenZeroPathChoices r hr (even_sector_path r hr x)).1 := by
  cases x with
  | inl x => exact (even_code_disconnected r hr x.1 x.2.1).mpr x.2.2
  | inr x =>
      change ¬ ActiveConnected (evenPathChoices r hr
        (evenPathReflection _ (evenCodedPath r hr x.1 x.2.1).1))
      exact fun h => (even_code_disconnected r hr x.1 x.2.1).mpr x.2.2
        ((even_reflection_connected r hr _).mp h)

private theorem odd_sector_disconnected (r : Nat) (hr : 1 ≤ r)
    (x : DisconnectedCode (r-1) ⊕ DisconnectedCode (r-1)) :
    ¬ ActiveConnected (oddZeroPathChoices r hr (odd_sector_path r hr x)).1 := by
  cases x with
  | inl x => exact (odd_code_disconnected r hr x.1 x.2.1).mpr x.2.2
  | inr x =>
      change ¬ ActiveConnected (oddPathChoices r hr
        (oddPathReflection _ (oddCodedPath r hr x.1 x.2.1).1))
      exact fun h => (odd_code_disconnected r hr x.1 x.2.1).mpr x.2.2
        ((odd_reflection_connected r hr _).mp h)

private noncomputable def even_disconnected_map (r : Nat) (hr : 1 ≤ r)
    (x : DisconnectedCode (r-1) ⊕ DisconnectedCode (r-1)) :
    {c : Choices (2*r) // Balanced c ∧ ¬ ActiveConnected c} :=
  ⟨(evenZeroPathChoices r hr (even_sector_path r hr x)).1,
    (evenZeroPathChoices r hr (even_sector_path r hr x)).2,
    even_sector_disconnected r hr x⟩

private noncomputable def odd_disconnected_map (r : Nat) (hr : 1 ≤ r)
    (x : DisconnectedCode (r-1) ⊕ DisconnectedCode (r-1)) :
    {c : Choices (2*r+1) // Balanced c ∧ ¬ ActiveConnected c} :=
  ⟨(oddZeroPathChoices r hr (odd_sector_path r hr x)).1,
    (oddZeroPathChoices r hr (odd_sector_path r hr x)).2,
    odd_sector_disconnected r hr x⟩

private theorem even_disconnected_map_injective (r : Nat) (hr : 1 ≤ r) :
    Function.Injective (even_disconnected_map r hr) := by
  intro x y h
  apply even_sector_path_injective r hr
  apply (evenBalancedChoicesEquiv r hr).symm.injective
  have hc : (even_disconnected_map r hr x).1 = (even_disconnected_map r hr y).1 :=
    congrArg Subtype.val h
  exact Subtype.ext hc

private theorem odd_disconnected_map_injective (r : Nat) (hr : 1 ≤ r) :
    Function.Injective (odd_disconnected_map r hr) := by
  intro x y h
  apply odd_sector_path_injective r hr
  apply (oddBalancedChoicesEquiv r hr).symm.injective
  have hc : (odd_disconnected_map r hr x).1 = (odd_disconnected_map r hr y).1 :=
    congrArg Subtype.val h
  exact Subtype.ext hc

private theorem even_disconnected_map_surjective (r : Nat) (hr : 1 ≤ r) :
    Function.Surjective (even_disconnected_map r hr) := by
  intro d
  obtain ⟨p, hp⟩ := (evenBalancedChoicesEquiv r hr).symm.surjective ⟨d.1,d.2.1⟩
  have hpc := congrArg Subtype.val hp
  cases p with
  | inl p =>
      change evenPathChoices r hr p.1 = d.1 at hpc
      have hd : ¬ ActiveConnected (evenPathChoices r hr p.1) := by
        rw [hpc]; exact d.2.2
      have hb := (evenZeroPathChoices r hr (Sum.inl p)).2
      obtain ⟨_, _, color, hc, hm, he⟩ :=
        (actual_disconnected_iff_coloring (2*r) (by omega) _ hb).mp hd
      obtain ⟨b,w,hcode⟩ := even_native_separation_code r hr p.1 color hc hm he
      have hps : p = evenCodedPath r hr b w := Subtype.ext hcode
      subst p
      have hw := (even_code_disconnected r hr b w).mp hd
      exact ⟨Sum.inl ⟨b,⟨w,hw⟩⟩, Subtype.ext hpc⟩
  | inr p =>
      change evenPathChoices r hr p.1 = d.1 at hpc
      let q := (evenZeroChargeReflection (3*r-3)).symm p
      have hq : evenPathReflection _ q.1 = p.1 :=
        congrArg Subtype.val ((evenZeroChargeReflection _).apply_symm_apply p)
      have hd : ¬ ActiveConnected (evenPathChoices r hr q.1) := by
        intro h
        apply d.2.2
        rw [← hpc, ← hq]
        exact (even_reflection_connected r hr q.1).mpr h
      have hb := (evenZeroPathChoices r hr (Sum.inl q)).2
      obtain ⟨_, _, color, hc, hm, he⟩ :=
        (actual_disconnected_iff_coloring (2*r) (by omega) _ hb).mp hd
      obtain ⟨b,w,hcode⟩ := even_native_separation_code r hr q.1 color hc hm he
      have hqs : q = evenCodedPath r hr b w := Subtype.ext hcode
      have hw : w ≠ (fun _ => b) := by
        apply (even_code_disconnected r hr b w).mp
        change ¬ ActiveConnected (evenPathChoices r hr (evenCodedPath r hr b w).1)
        rw [← hqs]; exact hd
      refine ⟨Sum.inr ⟨b,⟨w,hw⟩⟩, Subtype.ext ?_⟩
      change evenPathChoices r hr (evenPathReflection _ (evenCodedPath r hr b w).1) = d.1
      rw [← hqs, hq, hpc]

private theorem odd_disconnected_map_surjective (r : Nat) (hr : 1 ≤ r) :
    Function.Surjective (odd_disconnected_map r hr) := by
  intro d
  obtain ⟨p, hp⟩ := (oddBalancedChoicesEquiv r hr).symm.surjective ⟨d.1,d.2.1⟩
  have hpc := congrArg Subtype.val hp
  cases p with
  | inl p =>
      change oddPathChoices r hr p.1 = d.1 at hpc
      have hd : ¬ ActiveConnected (oddPathChoices r hr p.1) := by
        rw [hpc]; exact d.2.2
      have hb := (oddZeroPathChoices r hr (Sum.inl p)).2
      obtain ⟨_, _, color, hc, hm, he⟩ :=
        (actual_disconnected_iff_coloring (2*r+1) (by omega) _ hb).mp hd
      obtain ⟨b,w,hcode⟩ := odd_native_separation_code r hr p.1 color hc hm he
      have hps : p = oddCodedPath r hr b w := Subtype.ext hcode
      subst p
      have hw := (odd_code_disconnected r hr b w).mp hd
      exact ⟨Sum.inl ⟨b,⟨w,hw⟩⟩, Subtype.ext hpc⟩
  | inr p =>
      change oddPathChoices r hr p.1 = d.1 at hpc
      let q := (oddZeroChargeReflection (3*r-1)).symm p
      have hq : oddPathReflection _ q.1 = p.1 :=
        congrArg Subtype.val ((oddZeroChargeReflection _).apply_symm_apply p)
      have hd : ¬ ActiveConnected (oddPathChoices r hr q.1) := by
        intro h
        apply d.2.2
        rw [← hpc, ← hq]
        exact (odd_reflection_connected r hr q.1).mpr h
      have hb := (oddZeroPathChoices r hr (Sum.inl q)).2
      obtain ⟨_, _, color, hc, hm, he⟩ :=
        (actual_disconnected_iff_coloring (2*r+1) (by omega) _ hb).mp hd
      obtain ⟨b,w,hcode⟩ := odd_native_separation_code r hr q.1 color hc hm he
      have hqs : q = oddCodedPath r hr b w := Subtype.ext hcode
      have hw : w ≠ (fun _ => b) := by
        apply (odd_code_disconnected r hr b w).mp
        change ¬ ActiveConnected (oddPathChoices r hr (oddCodedPath r hr b w).1)
        rw [← hqs]; exact hd
      refine ⟨Sum.inr ⟨b,⟨w,hw⟩⟩, Subtype.ext ?_⟩
      change oddPathChoices r hr (oddPathReflection _ (oddCodedPath r hr b w).1) = d.1
      rw [← hqs, hq, hpc]

/-- The native disconnected subtype retains both labelled even sectors. -/
noncomputable def evenDisconnectedChoicesEquiv (r : Nat) (hr : 1 ≤ r) :
    {c : Choices (2*r) // Balanced c ∧ ¬ ActiveConnected c} ≃
      (DisconnectedCode (r-1) ⊕ DisconnectedCode (r-1)) :=
  (Equiv.ofBijective (even_disconnected_map r hr)
    ⟨even_disconnected_map_injective r hr, even_disconnected_map_surjective r hr⟩).symm

/-- The native disconnected subtype retains both labelled odd sectors and its cap. -/
noncomputable def oddDisconnectedChoicesEquiv (r : Nat) (hr : 1 ≤ r) :
    {c : Choices (2*r+1) // Balanced c ∧ ¬ ActiveConnected c} ≃
      (DisconnectedCode (r-1) ⊕ DisconnectedCode (r-1)) :=
  (Equiv.ofBijective (odd_disconnected_map r hr)
    ⟨odd_disconnected_map_injective r hr, odd_disconnected_map_surjective r hr⟩).symm

private theorem disconnected_code_card (l : Nat) :
    Fintype.card (DisconnectedCode l) = 2*(2^l-1) := by
  classical
  have fiber (b : Bool) : Fintype.card {w : Fin l → Bool // w ≠ (fun _ => b)} = 2^l-1 := by
    simpa using Fintype.card_subtype_compl (fun w : Fin l → Bool => w = (fun _ => b))
  rw [Fintype.card_sigma]
  simp only [fiber]
  simp

attribute [local instance] Classical.propDecidable

private theorem disconnected_count_card (t : Nat) :
    disconnectedCount t = Fintype.card {c : Choices t // Balanced c ∧ ¬ ActiveConnected c} := by
  classical
  simp [disconnectedCount, Fintype.card_subtype]

/-- All labelled native even choices, including r=1 and the antipodal collision. -/
theorem disconnectedCount_even (r : Nat) (hr : 1 ≤ r) :
    disconnectedCount (2*r) = 4*(2^(r-1)-1) := by
  classical
  rw [disconnected_count_card, Fintype.card_congr (evenDisconnectedChoicesEquiv r hr),
    Fintype.card_sum, disconnected_code_card]
  omega

/-- All labelled native odd choices, including r=1 and the singleton collision. -/
theorem disconnectedCount_odd (r : Nat) (hr : 1 ≤ r) :
    disconnectedCount (2*r+1) = 4*(2^(r-1)-1) := by
  classical
  rw [disconnected_count_card, Fintype.card_congr (oddDisconnectedChoicesEquiv r hr),
    Fintype.card_sum, disconnected_code_card]
  omega

end D5.S3.Combinatorics.Zigzag
