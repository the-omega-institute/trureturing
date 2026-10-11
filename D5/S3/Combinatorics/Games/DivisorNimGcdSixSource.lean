/- GID: D5/S3/Combinatorics/Games/DivisorNimGcdSixSource
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/DivisorNimGcdSixSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Games/DivisorNimGcdSixSource.gcd_six_parent_tail; premises=D5/S3/Combinatorics/Games/DivisorNimGcdSixSource.gcd_six_source_reduction
   digest: Actual gcd-six parent tails inherit the specified follower period through a uniformly stabilizing finite transformation family. -/

import D5.S3.Combinatorics.Games.DivisorNimBound
import Mathlib.Algebra.GCDMonoid.Multiset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Games.DivisorNimGrundy

open D5.S0.Certificates.Games.CrimGrundyRefutation (mex mex_spec)

/-- Values of actual nonempty fixed followers; the varying heap is untouched. -/
noncomputable def fixedValues (A : Position) (n : ℕ) : Finset ℕ := by
  classical
  exact A.toFinset.biUnion fun h => (((Finset.Icc 1 h).filter fun d =>
      legal A h d ∧ d ∣ n ∧ successor A h d ≠ 0).image fun d =>
        grundy (n ::ₘ successor A h d))

/-- An eventual period of the actual Grundy sequence with one varying heap. -/
def HasTailPeriod (A : Position) (T : ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n → grundy ((n + T) ::ₘ A) = grundy (n ::ₘ A)

/-- The specified period, rather than an unspecified multiple of it. -/
def sixTargetPeriod (H : ℕ) : ℕ := 2 * (Finset.Icc 1 H).lcm id

/-- The zero phase records the parity of fixed heaps of dyadic depth one. -/
noncomputable def sixZeroPhase (A : Position) : ℕ := if Even (countAt A 1) then 0 else 2

set_option maxHeartbeats 1500000 in
-- Option reconstruction and state identities share the same local source proofs.
/-- This reduction uses the native game, including singleton fixed boards and
repeated heaps. The tail threshold is allowed to exceed twice the fixed sum. -/
theorem gcd_six_source_reduction {A : Position} (hp : Positive A)
    (hg : A.gcd = 6) :
    (∀ n, 0 < n → (grundy (n ::ₘ A) = 0 ↔ n % 4 = sixZeroPhase A)) ∧
    (∀ n, 2 * A.sum < n →
      grundy (n ::ₘ A) = mex (fixedValues A n ∪
        {grundy ((n - 1) ::ₘ A), grundy ((n - 2) ::ₘ A),
         grundy ((n - 3) ::ₘ A), grundy ((n - 6) ::ₘ A)})) ∧
    (∀ n, 2 * A.sum + 6 < n → n % 2 = 1 →
      fixedValues A n = {0} ∧
      1 ≤ grundy (n ::ₘ A) ∧ grundy (n ::ₘ A) ≤ 4) ∧
    (∀ t, 2 * A.sum + 10 < t → t % 4 = sixZeroPhase A →
      let u := grundy ((t - 3) ::ₘ A)
      let v := grundy ((t - 1) ::ₘ A)
      let w := grundy ((t + 1) ::ₘ A)
      let b := grundy ((t + 2) ::ₘ A)
      let y := grundy ((t + 3) ::ₘ A)
      (1 ≤ u ∧ u ≤ 4) ∧ (1 ≤ v ∧ v ≤ 4) ∧ (1 ≤ w ∧ w ≤ 4) ∧
      u ≠ v ∧ v ≠ w ∧
      b = mex (fixedValues A (t + 2) ∪ {0, v, w}) ∧
      y = mex {0, b, w, u} ∧
      grundy ((t + 5) ::ₘ A) = mex {0, y, b, v}) ∧
    (∀ H, (∀ h ∈ A, h ≤ H) →
      (∀ Q ∈ moves A, Q ≠ 0 → HasTailPeriod Q (sixTargetPeriod H)) →
      ∃ N, 4 ∣ sixTargetPeriod H ∧ ∀ n, N ≤ n →
        fixedValues A (n + sixTargetPeriod H) = fixedValues A n) := by
  classical
  have hA : A ≠ 0 := by intro h; simp [h] at hg
  have hdiv : ∀ h ∈ A, 6 ∣ h := by
    intro h hh
    rw [← hg]
    exact Multiset.gcd_dvd hh
  have heven : ∀ h ∈ A, 2 ∣ h := fun h hh => (by decide : 2 ∣ 6).trans (hdiv h hh)
  have hdepth : HasDepth A 1 := by
    constructor
    · intro h hh
      exact (padicValNat_dvd_iff_le (p := 2) (by have := hp h hh; omega)).mp
        (by simpa using heven h hh)
    · have hex : ∃ h ∈ A, ¬ 4 ∣ h := by
        by_contra hn
        have : 4 ∣ A.gcd := Multiset.dvd_gcd.mpr (by simpa using hn)
        rw [hg] at this
        norm_num at this
      rcases hex with ⟨h, hh, hn⟩
      exact ⟨h, hh, valuation_eq_of_dvd_not (by have := hp h hh; omega)
        (by simpa using heven h hh) (by simpa using hn)⟩
  have hsum : 6 ≤ A.sum := by
    rcases Multiset.exists_mem_of_ne_zero hA with ⟨h, hh⟩
    have hle : h ≤ A.sum := by
      have hs := Multiset.sum_map_erase (f := id) hh
      simp only [Multiset.map_id', id_eq] at hs
      omega
    exact (Nat.le_of_dvd (hp h hh) (hdiv h hh)).trans hle
  have hle_sum : ∀ h ∈ A, h ≤ A.sum := by
    intro h hh
    have hs := Multiset.sum_map_erase (f := id) hh
    simp only [Multiset.map_id', id_eq] at hs
    omega
  have hpositive : ∀ n, 0 < n → Positive (n ::ₘ A) := by
    intro n hn x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact hn
    · exact hp x hx
  have hv0 : ∀ n, n % 2 = 1 → valuation n = 0 := by
    intro n hn
    exact padicValNat.eq_zero_of_not_dvd (by
      intro hd
      have := Nat.mod_eq_zero_of_dvd hd
      omega)
  have hzero : ∀ n, 0 < n → (grundy (n ::ₘ A) = 0 ↔ n % 4 = sixZeroPhase A) := by
    intro n hn
    by_cases ho : n % 2 = 1
    · have hd : HasDepth (n ::ₘ A) 0 := ⟨fun _ _ => Nat.zero_le _, n, by simp, hv0 n ho⟩
      have hc : countAt (n ::ₘ A) 0 = 1 := by
        have hcA : countAt A 0 = 0 := Multiset.countP_eq_zero.mpr (by
          intro h hh hv
          have := hdepth.1 h hh
          omega)
        change (n ::ₘ A).countP (fun h => valuation h = 0) = 1
        rw [Multiset.countP_cons, if_pos (hv0 n ho)]
        change countAt A 0 + 1 = 1
        omega
      rw [zero_iff_even_count (hpositive n hn) hd, hc]
      have hz : sixZeroPhase A = 0 ∨ sixZeroPhase A = 2 := by
        unfold sixZeroPhase
        split_ifs <;> simp
      rcases hz with hz | hz <;> rw [hz] <;> norm_num <;> omega
    · have hd2 : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
      have hv : 1 ≤ valuation n :=
        (padicValNat_dvd_iff_le (p := 2) (by omega)).mp (by simpa using hd2)
      have hd : HasDepth (n ::ₘ A) 1 := by
        refine ⟨?_, ?_⟩
        · intro h hh
          rcases Multiset.mem_cons.mp hh with rfl | hh
          · exact hv
          · exact hdepth.1 h hh
        · rcases hdepth.2 with ⟨h, hh, hvh⟩
          exact ⟨h, by simp [hh], hvh⟩
      have hv1 : valuation n = 1 ↔ n % 4 = 2 := by
        constructor
        · intro he
          have hnot : ¬ 4 ∣ n := by
            have ht := pow_succ_padicValNat_not_dvd (p := 2) (by omega : n ≠ 0)
            change ¬ 2 ^ (valuation n + 1) ∣ n at ht
            norm_num only [he] at ht
            exact ht
          have hm4 : n % 4 ≠ 0 := fun hm => hnot (Nat.dvd_of_mod_eq_zero hm)
          omega
        · intro hm
          exact valuation_eq_of_dvd_not (by omega) (by simpa using hd2)
            (by simpa using (show ¬ 4 ∣ n from fun hd => by
              have := Nat.mod_eq_zero_of_dvd hd; omega))
      have hc : countAt (n ::ₘ A) 1 = countAt A 1 + if n % 4 = 2 then 1 else 0 := by
        simp only [countAt, Multiset.countP_cons]
        simp only [hv1]
      rw [zero_iff_even_count (hpositive n hn) hd, hc]
      unfold sixZeroPhase
      by_cases hm : n % 4 = 2
      · rw [if_pos hm]
        by_cases hc : Even (countAt A 1)
        · rw [if_pos hc]
          have hcmod := Nat.even_iff.mp hc
          simp only [Nat.even_iff]
          omega
        · rw [if_neg hc]
          have hcmod : countAt A 1 % 2 ≠ 0 := fun h => hc (Nat.even_iff.mpr h)
          simp only [Nat.even_iff]
          omega
      · rw [if_neg hm]
        by_cases hc : Even (countAt A 1)
        · rw [if_pos hc]
          have hcmod := Nat.even_iff.mp hc
          simp only [Nat.even_iff]
          omega
        · rw [if_neg hc]
          have hcmod : countAt A 1 % 2 ≠ 0 := fun h => hc (Nat.even_iff.mpr h)
          simp only [Nat.even_iff]
          omega
  have hsingle : ∀ n, 0 < n → grundy ({n} : Position) = n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have hvals : (moves ({n} : Position)).image grundy = Finset.range n := by
        ext v
        constructor
        · intro hv
          rcases Finset.mem_image.mp hv with ⟨Q, hQ, rfl⟩
          rcases moves_spec hQ with ⟨h, hh, d, hd, rfl⟩
          have he : h = n := by simpa using hh
          subst h
          have herase : ({n} : Position).erase n = 0 := by simp
          by_cases he : n - d = 0
          · simp only [successor, he, if_true, Multiset.erase_singleton,
              Multiset.add_zero, grundy_empty, Finset.mem_range]
            exact hn
          · have hs : successor ({n} : Position) n d = {n - d} := by
              simp [successor, he]
            rw [hs, ih (n - d) (by have := hd.1; omega) (by omega)]
            exact Finset.mem_range.mpr (by have := hd.1; omega)
        · intro hv
          have hvn := Finset.mem_range.mp hv
          have hd : legal ({n} : Position) n (n - v) := by
            exact ⟨by omega, by omega, by simp [dividesAll]⟩
          have hQ := successor_is_move (P := ({n} : Position)) (by simp) hd
          refine Finset.mem_image.mpr ⟨_, hQ, ?_⟩
          by_cases hv0 : v = 0
          · subst v
            simp [successor, grundy_empty]
          · have hs : successor ({n} : Position) n (n - v) = {v} := by
              simp [successor, Nat.sub_sub_self (by omega : v ≤ n), hv0]
            rw [hs, ih v hvn (by omega)]
      rw [grundy_eq, hvals]
      apply le_antisymm
      · by_contra h
        have := (mex_spec (Finset.range n)).2 n (by omega)
        simp at this
      · by_contra h
        exact (mex_spec (Finset.range n)).1 (Finset.mem_range.mpr (by omega))
  have hrec : ∀ n, 2 * A.sum < n →
      grundy (n ::ₘ A) = mex (fixedValues A n ∪
        {grundy ((n - 1) ::ₘ A), grundy ((n - 2) ::ₘ A),
         grundy ((n - 3) ::ₘ A), grundy ((n - 6) ::ₘ A)}) := by
    intro n hn
    let F := fixedValues A n
    let L : Finset ℕ := {grundy ((n - 1) ::ₘ A), grundy ((n - 2) ::ₘ A),
      grundy ((n - 3) ::ₘ A), grundy ((n - 6) ::ₘ A)}
    have hnn : n ∉ A := by intro hh; have := hle_sum n hh; omega
    have hvar : ∀ d, 0 < d → d ∣ 6 →
        successor (n ::ₘ A) n d = (n - d) ::ₘ A := by
      intro d hd hd6
      have hdle := Nat.le_of_dvd (by decide : 0 < 6) hd6
      simp only [successor, Multiset.erase_cons_head, if_neg (show n - d ≠ 0 by omega)]
      rw [Multiset.add_comm, Multiset.singleton_add]
    have hfixed : ∀ h ∈ A, ∀ d,
        successor (n ::ₘ A) h d = n ::ₘ successor A h d := by
      intro h hh d
      rw [successor, Multiset.erase_cons_tail_of_mem hh]
      simp only [successor, Multiset.cons_add]
    have hoptions : (moves (n ::ₘ A)).image grundy ⊆ F ∪ L ∪ {n} := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨Q, hQ, rfl⟩
      rcases moves_spec hQ with ⟨h, hh, d, hd, rfl⟩
      rcases Multiset.mem_cons.mp hh with rfl | hh
      · have hd6 : d ∣ 6 := by
          rw [← hg]
          exact Multiset.dvd_gcd.mpr (by simpa [dividesAll] using hd.2.2)
        rw [hvar d hd.1 hd6]
        have he : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 := by
          have := Nat.le_of_dvd (by decide : 0 < 6) hd6
          interval_cases d <;> norm_num at *
        rcases he with rfl | rfl | rfl | rfl <;> simp [L]
      · have hdn : d ∣ n := hd.2.2 n (by
          rw [Multiset.erase_cons_tail_of_mem hh]; simp)
        have hdA : legal A h d := by
          refine ⟨hd.1, hd.2.1, ?_⟩
          intro x hx
          exact hd.2.2 x (by rw [Multiset.erase_cons_tail_of_mem hh]; simp [hx])
        rw [hfixed h hh d]
        by_cases he : successor A h d = 0
        · simp only [he, Multiset.cons_zero]
          rw [hsingle n (by omega)]
          simp
        · apply Finset.mem_union_left
          apply Finset.mem_union_left
          simp only [F, fixedValues, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
          exact ⟨h, Multiset.mem_toFinset.mpr hh, d,
            ⟨Finset.mem_Icc.mpr ⟨hd.1, hd.2.1⟩, hdA, hdn, he⟩, rfl⟩
    have hreal : F ∪ L ⊆ (moves (n ::ₘ A)).image grundy := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · simp only [F, fixedValues, Finset.mem_biUnion, Finset.mem_image,
          Finset.mem_filter] at hv
        rcases hv with ⟨h, hh, d, ⟨_, hd, hdn, _⟩, rfl⟩
        have hhA := Multiset.mem_toFinset.mp hh
        have hd' : legal (n ::ₘ A) h d := by
          refine ⟨hd.1, hd.2.1, ?_⟩
          rw [Multiset.erase_cons_tail_of_mem hhA]
          intro x hx
          rcases Multiset.mem_cons.mp hx with rfl | hx
          · exact hdn
          · exact hd.2.2 x hx
        rw [← hfixed h hhA d]
        exact Finset.mem_image.mpr ⟨_, successor_is_move (by simp [hhA]) hd', rfl⟩
      · have hmove : ∀ d, d ∈ ({1, 2, 3, 6} : Finset ℕ) →
            grundy ((n - d) ::ₘ A) ∈ (moves (n ::ₘ A)).image grundy := by
          intro d hd
          have hcase : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 := by simpa using hd
          have hdp : 0 < d := by rcases hcase with rfl | rfl | rfl | rfl <;> decide
          have hd6 : d ∣ 6 := by rcases hcase with rfl | rfl | rfl | rfl <;> decide
          have hd' : legal (n ::ₘ A) n d := by
            refine ⟨hdp, ?_, ?_⟩
            · have := Nat.le_of_dvd (by decide : 0 < 6) hd6; omega
            · simpa [dividesAll] using (fun h hh => hd6.trans (hdiv h hh))
          rw [← hvar d hdp hd6]
          exact Finset.mem_image.mpr ⟨_, successor_is_move (by simp) hd', rfl⟩
        simp only [L, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl <;> apply hmove <;> simp
    have hb : grundy (n ::ₘ A) ≤ 2 * A.sum := by
      have hne : A.toFinset.Nonempty := by
        rcases Multiset.exists_mem_of_ne_zero hA with ⟨h, hh⟩
        exact ⟨h, Multiset.mem_toFinset.mpr hh⟩
      let m := A.toFinset.min' hne
      have hm : m ∈ A := Multiset.mem_toFinset.mp (Finset.min'_mem _ hne)
      have hmin : ∀ h ∈ n ::ₘ A, m ≤ h := by
        intro h hh
        rcases Multiset.mem_cons.mp hh with rfl | hh
        · have := hle_sum m hm; omega
        · exact Finset.min'_le _ _ (Multiset.mem_toFinset.mpr hh)
      exact (result (n ::ₘ A) (hpositive n (by omega)) (by simp) m
        (by simp [hm]) hmin).trans (Nat.mul_le_mul_left 2 (hle_sum m hm))
    have hnot : grundy (n ::ₘ A) ∉ F ∪ L := by
      intro hv
      exact grundy_not_follower (n ::ₘ A) (hreal hv)
    have hall : ∀ v < grundy (n ::ₘ A), v ∈ F ∪ L := by
      intro v hv
      have he := hoptions (follower_mem_of_lt (n ::ₘ A) hv)
      rcases Finset.mem_union.mp he with he | he
      · exact he
      · have : v = n := by simpa using he
        omega
    change grundy (n ::ₘ A) = mex (F ∪ L)
    apply le_antisymm
    · by_contra h
      exact (mex_spec (F ∪ L)).1 (hall _ (by omega))
    · by_contra h
      exact hnot ((mex_spec (F ∪ L)).2 _ (by omega))
  have hodd : ∀ n, 2 * A.sum + 6 < n → n % 2 = 1 →
      fixedValues A n = {0} ∧
      1 ≤ grundy (n ::ₘ A) ∧ grundy (n ::ₘ A) ≤ 4 := by
    intro n hn ho
    have hn0 : 0 < n := by omega
    have hF : fixedValues A n = {0} := by
      ext v
      constructor
      · intro hv
        simp only [fixedValues, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at hv
        rcases hv with ⟨h, hh, d, ⟨_, hd, hdn, hne⟩, rfl⟩
        have hhA := Multiset.mem_toFinset.mp hh
        have hdo : d % 2 = 1 := by
          by_contra h
          have hd2 : 2 ∣ d := Nat.dvd_of_mod_eq_zero (by omega)
          have := Nat.mod_eq_zero_of_dvd (hd2.trans hdn)
          omega
        have hh2 := Nat.mod_eq_zero_of_dvd (heven h hhA)
        have hrem : 0 < h - d := by
          have := hd.2.1
          omega
        have hro : (h - d) % 2 = 1 := by have := hd.2.1; omega
        have hvrem := hv0 (h - d) hro
        have hsucc : successor A h d = (h - d) ::ₘ A.erase h := by
          simp only [successor, if_neg (show h - d ≠ 0 by omega)]
          rw [Multiset.add_comm, Multiset.singleton_add]
        have hcA : countAt (A.erase h) 0 = 0 := Multiset.countP_eq_zero.mpr (by
          intro x hx hv
          have := hdepth.1 x (Multiset.mem_of_mem_erase hx)
          omega)
        have hc : countAt (n ::ₘ successor A h d) 0 = 2 := by
          rw [hsucc]
          change (n ::ₘ (h - d) ::ₘ A.erase h).countP (fun h => valuation h = 0) = 2
          rw [Multiset.countP_cons, Multiset.countP_cons, if_pos (hv0 n ho), if_pos hvrem]
          change countAt (A.erase h) 0 + 1 + 1 = 2
          omega
        have hd0 : HasDepth (n ::ₘ successor A h d) 0 :=
          ⟨fun _ _ => Nat.zero_le _, n, by simp, hv0 n ho⟩
        have hp' : Positive (n ::ₘ successor A h d) := by
          intro x hx
          rcases Multiset.mem_cons.mp hx with rfl | hx
          · exact hn0
          · exact successor_positive hp hhA hd x hx
        have hz : grundy (n ::ₘ successor A h d) = 0 :=
          (zero_iff_even_count hp' hd0).mpr (by rw [hc]; decide)
        simpa using hz
      · intro hv
        have hv0' : v = 0 := by simpa using hv
        subst v
        rcases Multiset.exists_mem_of_ne_zero hA with ⟨h, hh⟩
        have hhp := hp h hh
        have hh2 := Nat.mod_eq_zero_of_dvd (heven h hh)
        have hgt : 1 < h := by omega
        have hd : legal A h 1 := ⟨by omega, by omega, fun _ _ => one_dvd _⟩
        have hne : successor A h 1 ≠ 0 := by
          have hm : h - 1 ∈ successor A h 1 := successor_mem_remainder (by omega)
          intro he; simp [he] at hm
        have hz : grundy (n ::ₘ successor A h 1) = 0 := by
          have hro : (h - 1) % 2 = 1 := by omega
          have hsucc : successor A h 1 = (h - 1) ::ₘ A.erase h := by
            simp only [successor, if_neg (show h - 1 ≠ 0 by omega)]
            rw [Multiset.add_comm, Multiset.singleton_add]
          have hcA : countAt (A.erase h) 0 = 0 := Multiset.countP_eq_zero.mpr (by
            intro x hx hv
            have := hdepth.1 x (Multiset.mem_of_mem_erase hx)
            omega)
          have hc : countAt (n ::ₘ successor A h 1) 0 = 2 := by
            rw [hsucc]
            change (n ::ₘ (h - 1) ::ₘ A.erase h).countP (fun h => valuation h = 0) = 2
            rw [Multiset.countP_cons, Multiset.countP_cons,
              if_pos (hv0 n ho), if_pos (hv0 (h - 1) hro)]
            change countAt (A.erase h) 0 + 1 + 1 = 2
            omega
          apply (zero_iff_even_count ?_ ?_).mpr
          · rw [hc]; decide
          · intro x hx
            rcases Multiset.mem_cons.mp hx with rfl | hx
            · exact hn0
            · exact successor_positive hp hh hd x hx
          · exact ⟨fun _ _ => Nat.zero_le _, n, by simp, hv0 n ho⟩
        simp only [fixedValues, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
        exact ⟨h, Multiset.mem_toFinset.mpr hh, 1,
          ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hd, one_dvd _, hne⟩, hz⟩
    have hnonzero : grundy (n ::ₘ A) ≠ 0 := by
      intro hz
      have := (hzero n hn0).mp hz
      unfold sixZeroPhase at this
      split_ifs at this <;> omega
    refine ⟨hF, by omega, ?_⟩
    rw [hrec n (by omega), hF]
    have hzpair : grundy ((n - 1) ::ₘ A) = 0 ∨ grundy ((n - 3) ::ₘ A) = 0 := by
      have h1 := hzero (n - 1) (by omega)
      have h3 := hzero (n - 3) (by omega)
      unfold sixZeroPhase at h1 h3
      split_ifs at h1 h3 <;> omega
    rcases hzpair with hz | hz
    · rw [hz]
      have hc : ({0} ∪ ({0, grundy ((n - 2) ::ₘ A),
          grundy ((n - 3) ::ₘ A), grundy ((n - 6) ::ₘ A)} : Finset ℕ)).card ≤ 4 := by
        simp only [Finset.singleton_union, Finset.insert_idem]
        exact (Finset.card_insert_le _ _).trans (by
          have := Finset.card_insert_le (grundy ((n - 2) ::ₘ A))
            ({grundy ((n - 3) ::ₘ A), grundy ((n - 6) ::ₘ A)} : Finset ℕ)
          have := Finset.card_insert_le (grundy ((n - 3) ::ₘ A))
            ({grundy ((n - 6) ::ₘ A)} : Finset ℕ)
          simp only [Finset.card_singleton] at *
          omega)
      exact (mex_le_card _).trans hc
    · rw [hz]
      have he : ({0} ∪ ({grundy ((n - 1) ::ₘ A), grundy ((n - 2) ::ₘ A),
          0, grundy ((n - 6) ::ₘ A)} : Finset ℕ)) =
          {0, grundy ((n - 1) ::ₘ A), grundy ((n - 2) ::ₘ A),
            grundy ((n - 6) ::ₘ A)} := by ext v; simp; tauto
      rw [he]
      exact (mex_le_card _).trans (by
        have := Finset.card_insert_le 0
          ({grundy ((n - 1) ::ₘ A), grundy ((n - 2) ::ₘ A),
            grundy ((n - 6) ::ₘ A)} : Finset ℕ)
        have := Finset.card_insert_le (grundy ((n - 1) ::ₘ A))
          ({grundy ((n - 2) ::ₘ A), grundy ((n - 6) ::ₘ A)} : Finset ℕ)
        have := Finset.card_insert_le (grundy ((n - 2) ::ₘ A))
          ({grundy ((n - 6) ::ₘ A)} : Finset ℕ)
        simp only [Finset.card_singleton] at *
        omega)
  have hblock : ∀ t, 2 * A.sum + 10 < t → t % 4 = sixZeroPhase A →
      let u := grundy ((t - 3) ::ₘ A)
      let v := grundy ((t - 1) ::ₘ A)
      let w := grundy ((t + 1) ::ₘ A)
      let b := grundy ((t + 2) ::ₘ A)
      let y := grundy ((t + 3) ::ₘ A)
      (1 ≤ u ∧ u ≤ 4) ∧ (1 ≤ v ∧ v ≤ 4) ∧ (1 ≤ w ∧ w ≤ 4) ∧
      u ≠ v ∧ v ≠ w ∧
      b = mex (fixedValues A (t + 2) ∪ {0, v, w}) ∧
      y = mex {0, b, w, u} ∧
      grundy ((t + 5) ::ₘ A) = mex {0, y, b, v} := by
    intro t ht htz
    dsimp only
    have hzphase : sixZeroPhase A = 0 ∨ sixZeroPhase A = 2 := by
      unfold sixZeroPhase
      split_ifs <;> simp
    have ht2 : t % 2 = 0 := by rcases hzphase with h | h <;> rw [h] at htz <;> omega
    have hu := (hodd (t - 3) (by omega) (by omega)).2
    have hv := (hodd (t - 1) (by omega) (by omega)).2
    have hw := (hodd (t + 1) (by omega) (by omega)).2
    have hneq : ∀ k, 2 < k → grundy ((k - 2) ::ₘ A) ≠ grundy (k ::ₘ A) := by
      intro k hk he
      have hd : legal (k ::ₘ A) k 2 := by
        refine ⟨by decide, by omega, ?_⟩
        simpa only [Multiset.erase_cons_head, dividesAll] using heven
      have hq := successor_is_move (P := k ::ₘ A) (by simp) hd
      have hs : successor (k ::ₘ A) k 2 = (k - 2) ::ₘ A := by
        simp only [successor, Multiset.erase_cons_head,
          if_neg (show k - 2 ≠ 0 by omega)]
        rw [Multiset.add_comm, Multiset.singleton_add]
      apply grundy_not_follower (k ::ₘ A)
      exact Finset.mem_image.mpr ⟨_, hq, by rw [hs]; exact he⟩
    have huv : grundy ((t - 3) ::ₘ A) ≠ grundy ((t - 1) ::ₘ A) := by
      have he : t - 1 - 2 = t - 3 := by omega
      simpa only [he] using hneq (t - 1) (by omega)
    have hvw : grundy ((t - 1) ::ₘ A) ≠ grundy ((t + 1) ::ₘ A) := by
      have he : t + 1 - 2 = t - 1 := by omega
      simpa only [he] using hneq (t + 1) (by omega)
    have hz0 : grundy (t ::ₘ A) = 0 := (hzero t (by omega)).mpr htz
    have hzm4 : grundy ((t - 4) ::ₘ A) = 0 := (hzero (t - 4) (by omega)).mpr (by omega)
    have hzp4 : grundy ((t + 4) ::ₘ A) = 0 := (hzero (t + 4) (by omega)).mpr (by omega)
    have hb := hrec (t + 2) (by omega)
    have he2 : t + 2 - 1 = t + 1 ∧ t + 2 - 2 = t ∧
        t + 2 - 3 = t - 1 ∧ t + 2 - 6 = t - 4 := by omega
    simp only [he2.1, he2.2.1, he2.2.2.1, he2.2.2.2, hz0, hzm4] at hb
    have hb' : grundy ((t + 2) ::ₘ A) =
        mex (fixedValues A (t + 2) ∪ {0, grundy ((t - 1) ::ₘ A),
          grundy ((t + 1) ::ₘ A)}) := by
      rw [hb]
      congr 1
      ext v
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hy := hrec (t + 3) (by omega)
    have hF3 := (hodd (t + 3) (by omega) (by omega)).1
    have he3 : t + 3 - 1 = t + 2 ∧ t + 3 - 2 = t + 1 ∧
        t + 3 - 3 = t ∧ t + 3 - 6 = t - 3 := by omega
    simp only [he3.1, he3.2.1, he3.2.2.1, he3.2.2.2, hz0, hF3] at hy
    have hy' : grundy ((t + 3) ::ₘ A) =
        mex {0, grundy ((t + 2) ::ₘ A), grundy ((t + 1) ::ₘ A),
          grundy ((t - 3) ::ₘ A)} := by
      rw [hy]
      congr 1
      ext v
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hx := hrec (t + 5) (by omega)
    have hF5 := (hodd (t + 5) (by omega) (by omega)).1
    have he5 : t + 5 - 1 = t + 4 ∧ t + 5 - 2 = t + 3 ∧
        t + 5 - 3 = t + 2 ∧ t + 5 - 6 = t - 1 := by omega
    simp only [he5.1, he5.2.1, he5.2.2.1, he5.2.2.2, hzp4, hF5] at hx
    have hx' : grundy ((t + 5) ::ₘ A) =
        mex {0, grundy ((t + 3) ::ₘ A), grundy ((t + 2) ::ₘ A),
          grundy ((t - 1) ::ₘ A)} := by
      rw [hx]
      congr 1
      ext v
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact ⟨hu, hv, hw, huv, hvw, hb', hy', hx'⟩
  refine ⟨hzero, hrec, hodd, hblock, ?_⟩
  intro H hH htail
  have hH6 : 6 ≤ H := by
    rcases Multiset.exists_mem_of_ne_zero hA with ⟨h, hh⟩
    exact (Nat.le_of_dvd (hp h hh) (hdiv h hh)).trans (hH h hh)
  have hdT : ∀ d, 0 < d → d ≤ H → d ∣ sixTargetPeriod H := by
    intro d hd hdH
    have he : d ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨hd, hdH⟩
    exact (Finset.dvd_lcm (f := id) he).trans (dvd_mul_left _ 2)
  have h4 : 4 ∣ sixTargetPeriod H := by
    have hd : 2 ∣ (Finset.Icc 1 H).lcm id :=
      Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    exact Nat.mul_dvd_mul_left 2 hd
  let M := (moves A).filter (fun Q => Q ≠ 0)
  have htailM : ∀ Q ∈ M, ∃ N, ∀ n, N ≤ n →
      grundy ((n + sixTargetPeriod H) ::ₘ Q) = grundy (n ::ₘ Q) := by
    intro Q hQ
    exact htail Q (Finset.mem_filter.mp hQ).1 (Finset.mem_filter.mp hQ).2
  let start : {Q // Q ∈ M} → ℕ := fun Q => Classical.choose (htailM Q.1 Q.2)
  let N := M.attach.sup start
  have hperiod : ∀ Q ∈ M, ∀ n, N ≤ n →
      grundy ((n + sixTargetPeriod H) ::ₘ Q) = grundy (n ::ₘ Q) := by
    intro Q hQ n hn
    apply Classical.choose_spec (htailM Q hQ) n
    exact (Finset.le_sup (f := start) (Finset.mem_attach M ⟨Q, hQ⟩)).trans hn
  refine ⟨N, h4, ?_⟩
  intro n hn
  ext v
  simp only [fixedValues, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨h, hh, d, ⟨hdI, hdA, hdn, hne⟩, hv⟩
    have hhA := Multiset.mem_toFinset.mp hh
    have hdT' := hdT d hdA.1 (hdA.2.1.trans (hH h hhA))
    have hdn' : d ∣ n := by
      simpa only [Nat.add_sub_cancel] using Nat.dvd_sub hdn hdT'
    have hQM : successor A h d ∈ M := Finset.mem_filter.mpr ⟨successor_is_move hhA hdA, hne⟩
    refine ⟨h, hh, d, ⟨hdI, hdA, hdn', hne⟩, ?_⟩
    exact (hperiod _ hQM n hn).symm.trans hv
  · rintro ⟨h, hh, d, ⟨hdI, hdA, hdn, hne⟩, hv⟩
    have hhA := Multiset.mem_toFinset.mp hh
    have hdT' := hdT d hdA.1 (hdA.2.1.trans (hH h hhA))
    have hdn' : d ∣ n + sixTargetPeriod H := dvd_add hdn hdT'
    have hQM : successor A h d ∈ M := Finset.mem_filter.mpr ⟨successor_is_move hhA hdA, hne⟩
    refine ⟨h, hh, d, ⟨hdI, hdA, hdn', hne⟩, ?_⟩
    exact (hperiod _ hQM n hn).trans hv

/-- The complete odd triple alphabet, in lexicographic order. -/
def sixStates : Fin 36 → ℕ × ℕ × ℕ := ![
  (1, 2, 1), (1, 2, 3), (1, 2, 4), (1, 3, 1), (1, 3, 2), (1, 3, 4),
  (1, 4, 1), (1, 4, 2), (1, 4, 3), (2, 1, 2), (2, 1, 3), (2, 1, 4),
  (2, 3, 1), (2, 3, 2), (2, 3, 4), (2, 4, 1), (2, 4, 2), (2, 4, 3),
  (3, 1, 2), (3, 1, 3), (3, 1, 4), (3, 2, 1), (3, 2, 3), (3, 2, 4),
  (3, 4, 1), (3, 4, 2), (3, 4, 3), (4, 1, 2), (4, 1, 3), (4, 1, 4),
  (4, 2, 1), (4, 2, 3), (4, 2, 4), (4, 3, 1), (4, 3, 2), (4, 3, 4)]
/-- All subsets of the four observable positive values. -/
def sixMasks : Fin 16 → Finset ℕ := ![
  ∅, {1}, {2}, {1, 2}, {3}, {1, 3}, {2, 3}, {1, 2, 3},
  {4}, {1, 4}, {2, 4}, {1, 2, 4}, {3, 4}, {1, 3, 4}, {2, 3, 4}, {1, 2, 3, 4}]
def sixGeneratorMasks : Fin 7 → Fin 16 := ![0, 1, 2, 3, 5, 6, 7]
def sixMaskGenerator : Fin 16 → Fin 7 := ![0, 1, 2, 3, 0, 4, 5, 6, 0, 1, 2, 3, 0, 4, 5, 6]
/-- The finite transformation family, including the identity at row zero. -/
def sixRows : Fin 48 → Fin 36 → Fin 36 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
    18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35],
  ![0, 22, 31, 3, 13, 32, 3, 13, 22, 9, 19, 28, 3, 13, 34, 3, 13, 25,
    9, 19, 28, 0, 22, 31, 6, 16, 22, 9, 19, 28, 0, 22, 31, 3, 13, 32],
  ![0, 21, 30, 3, 12, 33, 3, 15, 24, 9, 19, 28, 3, 9, 29, 3, 9, 19,
    9, 19, 28, 0, 19, 29, 6, 9, 19, 9, 19, 28, 0, 19, 29, 3, 9, 29],
  ![0, 22, 31, 0, 13, 32, 0, 13, 22, 9, 18, 27, 3, 13, 34, 6, 13, 25,
    9, 18, 27, 0, 22, 31, 0, 16, 22, 9, 18, 27, 0, 22, 31, 0, 13, 32],
  ![0, 21, 30, 0, 12, 30, 0, 15, 21, 9, 18, 27, 3, 9, 27, 6, 9, 18,
    9, 18, 27, 0, 19, 29, 0, 9, 18, 9, 18, 27, 0, 19, 29, 0, 9, 27],
  ![0, 21, 30, 3, 12, 33, 3, 12, 24, 9, 19, 28, 3, 9, 29, 3, 9, 19,
    9, 19, 28, 0, 19, 28, 6, 9, 19, 9, 19, 28, 0, 19, 28, 3, 9, 29],
  ![0, 22, 31, 0, 13, 32, 0, 13, 22, 9, 18, 27, 3, 13, 34, 3, 13, 25,
    9, 18, 27, 0, 22, 31, 0, 16, 22, 9, 18, 27, 0, 22, 31, 0, 13, 32],
  ![0, 21, 30, 0, 12, 30, 0, 12, 21, 9, 18, 27, 3, 9, 27, 3, 9, 18,
    9, 18, 27, 0, 19, 28, 0, 9, 18, 9, 18, 27, 0, 19, 28, 0, 9, 27],
  ![0, 22, 22, 3, 13, 31, 3, 13, 22, 9, 19, 19, 3, 13, 13, 3, 13, 16,
    9, 19, 19, 0, 22, 22, 3, 13, 22, 9, 19, 19, 0, 22, 22, 3, 13, 31],
  ![0, 19, 19, 3, 9, 29, 3, 9, 19, 9, 19, 19, 3, 9, 9, 3, 9, 9,
    9, 19, 19, 0, 19, 19, 3, 9, 19, 9, 19, 19, 0, 19, 19, 3, 9, 29],
  ![0, 22, 22, 0, 13, 31, 0, 13, 22, 9, 18, 18, 0, 13, 13, 0, 13, 16,
    9, 18, 18, 0, 22, 22, 0, 13, 22, 9, 18, 18, 0, 22, 22, 0, 13, 31],
  ![0, 19, 19, 0, 9, 29, 0, 9, 19, 9, 18, 18, 0, 9, 9, 0, 9, 9,
    9, 18, 18, 0, 19, 19, 0, 9, 19, 9, 18, 18, 0, 19, 19, 0, 9, 29],
  ![0, 19, 19, 3, 9, 28, 3, 9, 19, 9, 19, 19, 3, 9, 9, 3, 9, 9,
    9, 19, 19, 0, 19, 19, 3, 9, 19, 9, 19, 19, 0, 19, 19, 3, 9, 28],
  ![0, 19, 19, 0, 9, 28, 0, 9, 19, 9, 18, 18, 0, 9, 9, 0, 9, 9,
    9, 18, 18, 0, 19, 19, 0, 9, 19, 9, 18, 18, 0, 19, 19, 0, 9, 28],
  ![0, 0, 0, 3, 3, 3, 3, 3, 6, 9, 19, 19, 3, 9, 28, 3, 9, 19,
    9, 19, 19, 0, 19, 28, 3, 9, 19, 9, 19, 19, 0, 19, 28, 3, 9, 28],
  ![0, 0, 0, 0, 3, 0, 0, 6, 0, 9, 18, 18, 0, 9, 27, 0, 9, 18,
    9, 18, 18, 0, 18, 27, 0, 9, 18, 9, 18, 18, 0, 18, 27, 0, 9, 27],
  ![0, 0, 0, 0, 3, 0, 0, 3, 0, 9, 18, 18, 0, 9, 27, 0, 9, 18,
    9, 18, 18, 0, 18, 27, 0, 9, 18, 9, 18, 18, 0, 18, 27, 0, 9, 27],
  ![0, 22, 22, 0, 13, 31, 0, 13, 22, 9, 9, 9, 3, 13, 13, 3, 13, 16,
    9, 9, 9, 0, 22, 22, 0, 13, 22, 9, 9, 9, 0, 22, 22, 0, 13, 31],
  ![0, 19, 19, 0, 9, 29, 0, 9, 19, 9, 9, 9, 3, 9, 9, 3, 9, 9,
    9, 9, 9, 0, 19, 19, 0, 9, 19, 9, 9, 9, 0, 19, 19, 0, 9, 29],
  ![0, 22, 22, 0, 13, 31, 0, 13, 22, 9, 9, 9, 0, 13, 13, 0, 13, 16,
    9, 9, 9, 0, 22, 22, 0, 13, 22, 9, 9, 9, 0, 22, 22, 0, 13, 31],
  ![0, 19, 19, 0, 9, 29, 0, 9, 19, 9, 9, 9, 0, 9, 9, 0, 9, 9,
    9, 9, 9, 0, 19, 19, 0, 9, 19, 9, 9, 9, 0, 19, 19, 0, 9, 29],
  ![0, 19, 19, 0, 9, 28, 0, 9, 19, 9, 9, 9, 3, 9, 9, 3, 9, 9,
    9, 9, 9, 0, 19, 19, 0, 9, 19, 9, 9, 9, 0, 19, 19, 0, 9, 28],
  ![0, 19, 19, 0, 9, 28, 0, 9, 19, 9, 9, 9, 0, 9, 9, 0, 9, 9,
    9, 9, 9, 0, 19, 19, 0, 9, 19, 9, 9, 9, 0, 19, 19, 0, 9, 28],
  ![0, 0, 0, 0, 3, 0, 0, 3, 0, 9, 9, 9, 3, 9, 9, 3, 9, 9,
    9, 9, 9, 0, 19, 28, 0, 9, 9, 9, 9, 9, 0, 19, 28, 0, 9, 9],
  ![0, 0, 0, 0, 3, 0, 0, 6, 0, 9, 9, 9, 0, 9, 9, 0, 9, 9,
    9, 9, 9, 0, 18, 27, 0, 9, 9, 9, 9, 9, 0, 18, 27, 0, 9, 9],
  ![0, 0, 0, 0, 3, 0, 0, 3, 0, 9, 9, 9, 0, 9, 9, 0, 9, 9,
    9, 9, 9, 0, 18, 27, 0, 9, 9, 9, 9, 9, 0, 18, 27, 0, 9, 9],
  ![0, 0, 0, 3, 3, 3, 3, 3, 6, 9, 19, 19, 3, 9, 28, 3, 9, 19,
    9, 19, 19, 0, 19, 19, 3, 9, 19, 9, 19, 19, 0, 19, 19, 3, 9, 28],
  ![0, 0, 0, 0, 3, 0, 0, 3, 0, 9, 18, 18, 0, 9, 27, 0, 9, 18,
    9, 18, 18, 0, 18, 18, 0, 9, 18, 9, 18, 18, 0, 18, 18, 0, 9, 27],
  ![0, 0, 0, 0, 3, 0, 0, 3, 0, 9, 9, 9, 3, 9, 9, 3, 9, 9,
    9, 9, 9, 0, 19, 19, 0, 9, 9, 9, 9, 9, 0, 19, 19, 0, 9, 9],
  ![0, 0, 0, 0, 3, 0, 0, 3, 0, 9, 9, 9, 0, 9, 9, 0, 9, 9,
    9, 9, 9, 0, 18, 18, 0, 9, 9, 9, 9, 9, 0, 18, 18, 0, 9, 9],
  ![0, 22, 22, 3, 13, 22, 3, 13, 22, 9, 19, 19, 3, 13, 13, 3, 13, 13,
    9, 19, 19, 0, 22, 22, 3, 13, 22, 9, 19, 19, 0, 22, 22, 3, 13, 22],
  ![0, 19, 19, 3, 9, 19, 3, 9, 19, 9, 19, 19, 3, 9, 9, 3, 9, 9,
    9, 19, 19, 0, 19, 19, 3, 9, 19, 9, 19, 19, 0, 19, 19, 3, 9, 19],
  ![0, 22, 22, 0, 13, 22, 0, 13, 22, 9, 18, 18, 0, 13, 13, 0, 13, 13,
    9, 18, 18, 0, 22, 22, 0, 13, 22, 9, 18, 18, 0, 22, 22, 0, 13, 22],
  ![0, 19, 19, 0, 9, 19, 0, 9, 19, 9, 18, 18, 0, 9, 9, 0, 9, 9,
    9, 18, 18, 0, 19, 19, 0, 9, 19, 9, 18, 18, 0, 19, 19, 0, 9, 19],
  ![0, 18, 18, 0, 9, 27, 0, 9, 18, 9, 18, 18, 0, 9, 9, 0, 9, 9,
    9, 18, 18, 0, 18, 18, 0, 9, 18, 9, 18, 18, 0, 18, 18, 0, 9, 27],
  ![0, 22, 22, 0, 13, 22, 0, 13, 22, 9, 9, 9, 0, 13, 13, 0, 13, 13,
    9, 9, 9, 0, 22, 22, 0, 13, 22, 9, 9, 9, 0, 22, 22, 0, 13, 22],
  ![0, 19, 19, 0, 9, 19, 0, 9, 19, 9, 9, 9, 0, 9, 9, 0, 9, 9,
    9, 9, 9, 0, 19, 19, 0, 9, 19, 9, 9, 9, 0, 19, 19, 0, 9, 19],
  ![0, 18, 18, 0, 9, 27, 0, 9, 18, 9, 9, 9, 0, 9, 9, 0, 9, 9,
    9, 9, 9, 0, 18, 18, 0, 9, 18, 9, 9, 9, 0, 18, 18, 0, 9, 27],
  ![0, 18, 18, 0, 9, 18, 0, 9, 18, 9, 18, 18, 0, 9, 9, 0, 9, 9,
    9, 18, 18, 0, 18, 18, 0, 9, 18, 9, 18, 18, 0, 18, 18, 0, 9, 18],
  ![0, 18, 18, 0, 9, 18, 0, 9, 18, 9, 9, 9, 0, 9, 9, 0, 9, 9,
    9, 9, 9, 0, 18, 18, 0, 9, 18, 9, 9, 9, 0, 18, 18, 0, 9, 18],
  ![0, 0, 0, 3, 3, 3, 3, 3, 3, 9, 19, 19, 3, 9, 19, 3, 9, 19,
    9, 19, 19, 0, 19, 19, 3, 9, 19, 9, 19, 19, 0, 19, 19, 3, 9, 19],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 18, 18, 0, 9, 18, 0, 9, 18,
    9, 18, 18, 0, 18, 18, 0, 9, 18, 9, 18, 18, 0, 18, 18, 0, 9, 18],
  ![0, 0, 0, 0, 3, 0, 0, 3, 0, 9, 9, 9, 0, 9, 9, 0, 9, 9,
    9, 9, 9, 0, 9, 9, 0, 9, 9, 9, 9, 9, 0, 9, 9, 0, 9, 9],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 0, 9, 9, 0, 9, 9,
    9, 9, 9, 0, 9, 9, 0, 9, 9, 9, 9, 9, 0, 9, 9, 0, 9, 9],
  ![0, 22, 22, 0, 13, 22, 0, 13, 22, 9, 9, 9, 3, 13, 13, 3, 13, 13,
    9, 9, 9, 0, 22, 22, 0, 13, 22, 9, 9, 9, 0, 22, 22, 0, 13, 22],
  ![0, 19, 19, 0, 9, 19, 0, 9, 19, 9, 9, 9, 3, 9, 9, 3, 9, 9,
    9, 9, 9, 0, 19, 19, 0, 9, 19, 9, 9, 9, 0, 19, 19, 0, 9, 19],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 0, 9, 9, 0, 9, 9,
    9, 9, 9, 0, 18, 18, 0, 9, 9, 9, 9, 9, 0, 18, 18, 0, 9, 9],
  ![0, 9, 9, 0, 9, 9, 0, 9, 9, 9, 9, 9, 0, 9, 9, 0, 9, 9,
    9, 9, 9, 0, 9, 9, 0, 9, 9, 9, 9, 9, 0, 9, 9, 0, 9, 9]]
/-- Append one generator on the left of the existing transformation. -/
def sixExtensions : Fin 48 → Fin 7 → Fin 48 := ![
  ![1, 2, 3, 4, 5, 6, 7], ![8, 9, 10, 11, 12, 10, 13], ![14, 14, 15, 15, 14, 16, 16],
  ![17, 18, 19, 20, 21, 19, 22], ![23, 23, 24, 24, 23, 25, 25], ![26, 26, 27, 27, 26, 27, 27],
  ![17, 18, 19, 20, 21, 19, 22], ![28, 28, 29, 29, 28, 29, 29], ![30, 31, 32, 33, 31, 32, 33],
  ![12, 12, 34, 34, 12, 34, 34], ![35, 36, 35, 36, 36, 35, 36], ![22, 22, 37, 37, 22, 37, 37],
  ![31, 31, 38, 38, 31, 38, 38], ![36, 36, 39, 39, 36, 39, 39], ![40, 40, 41, 41, 40, 41, 41],
  ![42, 42, 43, 43, 42, 43, 43], ![42, 42, 43, 43, 42, 43, 43], ![44, 45, 35, 36, 45, 35, 36],
  ![21, 21, 37, 37, 21, 37, 37], ![35, 36, 35, 36, 36, 35, 36], ![22, 22, 37, 37, 22, 37, 37],
  ![45, 45, 39, 39, 45, 39, 39], ![36, 36, 39, 39, 36, 39, 39], ![28, 28, 46, 46, 28, 46, 46],
  ![42, 42, 43, 43, 42, 43, 43], ![42, 42, 43, 43, 42, 43, 43], ![40, 40, 41, 41, 40, 41, 41],
  ![42, 42, 43, 43, 42, 43, 43], ![28, 28, 46, 46, 28, 46, 46], ![42, 42, 43, 43, 42, 43, 43],
  ![30, 31, 32, 33, 31, 32, 33], ![31, 31, 38, 38, 31, 38, 38], ![35, 36, 35, 36, 36, 35, 36],
  ![36, 36, 39, 39, 36, 39, 39], ![47, 47, 47, 47, 47, 47, 47], ![35, 36, 35, 36, 36, 35, 36],
  ![36, 36, 39, 39, 36, 39, 39], ![47, 47, 47, 47, 47, 47, 47], ![47, 47, 47, 47, 47, 47, 47],
  ![47, 47, 47, 47, 47, 47, 47], ![40, 40, 41, 41, 40, 41, 41], ![43, 43, 43, 43, 43, 43, 43],
  ![42, 42, 43, 43, 42, 43, 43], ![43, 43, 43, 43, 43, 43, 43], ![44, 45, 35, 36, 45, 35, 36],
  ![45, 45, 39, 39, 45, 39, 39], ![43, 43, 43, 43, 43, 43, 43], ![47, 47, 47, 47, 47, 47, 47]]
def sixLowMex (E : Finset ℕ) : ℕ :=
  if 0 ∉ E then 0 else if 1 ∉ E then 1 else if 2 ∉ E then 2
  else if 3 ∉ E then 3 else if 4 ∉ E then 4 else 5

def sixFiniteStep (m : Fin 16) (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let b := sixLowMex (sixMasks m ∪ {0, s.2.1, s.2.2})
  let y := sixLowMex {0, b, s.2.2, s.1}
  (s.2.2, y, sixLowMex {0, y, b, s.2.1})

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
-- The finite closure and actual parent reconstruction share one local proof.
/-- Every positive fixed multiset of gcd six inherits the specified tail period
from all of its actual nonempty direct fixed followers. -/
theorem gcd_six_parent_tail {A : Position} (hp : Positive A)
    (hg : A.gcd = 6) (H : ℕ) (hH : ∀ h ∈ A, h ≤ H)
    (htail : ∀ Q ∈ moves A, Q ≠ 0 → HasTailPeriod Q (sixTargetPeriod H)) :
    HasTailPeriod A (sixTargetPeriod H) := by
  classical
  rcases gcd_six_source_reduction hp hg with ⟨hz, hrec, hodd, hblock, hforcing⟩
  rcases hforcing H hH htail with ⟨N, h4, hF⟩
  have hstates : ∀ (u v w : Fin 4), u ≠ v → v ≠ w →
      ∃ s : Fin 36, sixStates s = (u.val + 1, v.val + 1, w.val + 1) := by decide +kernel
  have hinj : Function.Injective sixStates := by decide +kernel
  have hgenBase : ∀ (j : Fin 7) (s : Fin 36),
      sixStates (sixRows (sixExtensions 0 j) s) =
        sixFiniteStep (sixGeneratorMasks j) (sixStates s) := by decide +kernel
  have hmaskGen : ∀ (m : Fin 16) (s : Fin 36),
      sixFiniteStep m (sixStates s) =
        sixFiniteStep (sixGeneratorMasks (sixMaskGenerator m)) (sixStates s) := by decide +kernel
  have hgen : ∀ (m : Fin 16) (s : Fin 36),
      sixStates (sixRows (sixExtensions 0 (sixMaskGenerator m)) s) =
        sixFiniteStep m (sixStates s) := by
    intro m s
    rw [hgenBase, ← hmaskGen]
  have hid : ∀ s, sixRows 0 s = s := by decide +kernel
  have hclose : ∀ (r : Fin 48) (j : Fin 7) (s : Fin 36),
      sixRows (sixExtensions r j) s =
        sixRows (sixExtensions 0 j) (sixRows r s) := by decide +kernel
  have hpower : ∀ (r : Fin 48) (s : Fin 36),
      sixRows r (sixRows r (sixRows r (sixRows r s))) =
        sixRows r (sixRows r (sixRows r s)) := by decide +kernel
  have hlow : ∀ E : Finset ℕ, sixLowMex E = min (mex E) 5 := by
    intro E
    clear! A H N hstates hinj hgenBase hmaskGen hgen hid hclose hpower
    have hs := mex_spec E
    have hl : sixLowMex E ≤ 5 := by unfold sixLowMex; split_ifs <;> omega
    have hn : sixLowMex E < 5 → sixLowMex E ∉ E := by
      unfold sixLowMex
      split_ifs <;> simp_all
    have hb : ∀ k < sixLowMex E, k ∈ E := by
      intro k hk
      have hk5 : k < 5 := by omega
      interval_cases k <;> unfold sixLowMex at hk <;>
        split_ifs at hk <;> simp_all
    by_cases hc : sixLowMex E < 5
    · have he : mex E = sixLowMex E := by
        apply le_antisymm
        · by_contra h; exact hn hc (hs.2 _ (by omega))
        · by_contra h; exact hs.1 (hb _ (by omega))
      rw [he, min_eq_left (by omega)]
    · have hm : 5 ≤ mex E := by
        by_contra h
        exact hs.1 (hb _ (by omega))
      rw [min_eq_right hm]
      omega
  let mask (E : Finset ℕ) : Fin 16 := Fin.ofNat 16
    ((if 1 ∈ E then 1 else 0) + (if 2 ∈ E then 2 else 0) +
      (if 3 ∈ E then 4 else 0) + (if 4 ∈ E then 8 else 0))
  have hmask : ∀ (E : Finset ℕ) (k : ℕ), 1 ≤ k → k ≤ 4 →
      (k ∈ sixMasks (mask E) ↔ k ∈ E) := by
    intro E k hk1 hk4
    by_cases h1 : 1 ∈ E <;> by_cases h2 : 2 ∈ E <;>
      by_cases h3 : 3 ∈ E <;> by_cases h4' : 4 ∈ E <;>
      interval_cases k <;> norm_num [mask, sixMasks, h1, h2, h3, h4'] <;> decide
  have hagree : ∀ (E F : Finset ℕ),
      (∀ k ≤ 4, k ∈ E ↔ k ∈ F) → sixLowMex E = sixLowMex F := by
    intro E F h
    simp only [sixLowMex, h 0 (by omega), h 1 (by omega), h 2 (by omega),
      h 3 (by omega), h 4 (by omega)]
  have hproject : ∀ (E : Finset ℕ) (u v w b y x : ℕ),
      b = mex (E ∪ {0, v, w}) → y = mex {0, b, w, u} →
      x = mex {0, y, b, v} → y ≤ 4 → x ≤ 4 →
      (w, y, x) = sixFiniteStep (mask E) (u, v, w) := by
    intro E u v w b y x hb hy hx hyle hxle
    let c := sixLowMex (sixMasks (mask E) ∪ {0, v, w})
    have hc : c = min b 5 := by
      rw [hb, ← hlow]
      apply hagree
      intro k hk
      by_cases hk0 : k = 0
      · simp [hk0]
      · have hm := hmask E k (by omega) hk
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
    have hcbit : ∀ k ≤ 4, k = c ↔ k = b := by
      intro k hk
      rw [hc]
      omega
    have hyc : y = sixLowMex {0, c, w, u} := by
      have he : min (mex {0, b, w, u}) 5 = y := by rw [← hy]; exact min_eq_left (by omega)
      rw [← he, ← hlow]
      apply hagree
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rw [hcbit k hk]
    have hxc : x = sixLowMex {0, y, c, v} := by
      have he : min (mex {0, y, b, v}) 5 = x := by rw [← hx]; exact min_eq_left (by omega)
      rw [← he, ← hlow]
      apply hagree
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rw [hcbit k hk]
    simp only [sixFiniteStep]
    change (w, y, x) = (w, sixLowMex {0, c, w, u},
      sixLowMex {0, sixLowMex {0, c, w, u}, c, v})
    rw [← hyc, ← hxc]
  have hphase : sixZeroPhase A = 0 ∨ sixZeroPhase A = 2 := by
    unfold sixZeroPhase
    split_ifs <;> simp
  have hphase4 : sixZeroPhase A < 4 := by rcases hphase with h | h <;> omega
  let z := 4 * (N + 2 * A.sum + 20) + sixZeroPhase A
  let anchor (k : ℕ) := z + 4 * k
  let f (n : ℕ) := grundy (n ::ₘ A)
  have ha : ∀ k, 2 * A.sum + 10 < anchor k ∧ N ≤ anchor k ∧
      anchor k % 4 = sixZeroPhase A := by
    intro k
    dsimp [anchor, z]
    omega
  have hb : ∀ k,
      (1 ≤ f (anchor k - 3) ∧ f (anchor k - 3) ≤ 4) ∧
      (1 ≤ f (anchor k - 1) ∧ f (anchor k - 1) ≤ 4) ∧
      (1 ≤ f (anchor k + 1) ∧ f (anchor k + 1) ≤ 4) ∧
      f (anchor k - 3) ≠ f (anchor k - 1) ∧
      f (anchor k - 1) ≠ f (anchor k + 1) ∧
      f (anchor k + 2) = mex (fixedValues A (anchor k + 2) ∪
        {0, f (anchor k - 1), f (anchor k + 1)}) ∧
      f (anchor k + 3) = mex {0, f (anchor k + 2), f (anchor k + 1), f (anchor k - 3)} ∧
      f (anchor k + 5) = mex {0, f (anchor k + 3), f (anchor k + 2), f (anchor k - 1)} := by
    intro k
    exact hblock (anchor k) (ha k).1 (ha k).2.2
  have hex : ∀ k, ∃ s : Fin 36,
      sixStates s = (f (anchor k - 3), f (anchor k - 1), f (anchor k + 1)) := by
    intro k
    rcases hb k with ⟨hu, hv, hw, huv, hvw, _⟩
    let u : Fin 4 := ⟨f (anchor k - 3) - 1, by omega⟩
    let v : Fin 4 := ⟨f (anchor k - 1) - 1, by omega⟩
    let w : Fin 4 := ⟨f (anchor k + 1) - 1, by omega⟩
    rcases hstates u v w (by intro h; have := congrArg Fin.val h; dsimp [u,v] at this; omega)
      (by intro h; have := congrArg Fin.val h; dsimp [v,w] at this; omega) with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    dsimp [u,v,w] at hs
    simpa only [Nat.sub_add_cancel hu.1, Nat.sub_add_cancel hv.1, Nat.sub_add_cancel hw.1] using hs
  choose S hS using hex
  let M (k : ℕ) := mask (fixedValues A (anchor k + 2))
  have hstep : ∀ k, S (k + 1) =
      sixRows (sixExtensions 0 (sixMaskGenerator (M k))) (S k) := by
    intro k
    apply hinj
    rw [hgen, hS, hS]
    have he1 : anchor (k + 1) - 3 = anchor k + 1 := by dsimp [anchor]; omega
    have he2 : anchor (k + 1) - 1 = anchor k + 3 := by dsimp [anchor]; omega
    have he3 : anchor (k + 1) + 1 = anchor k + 5 := by dsimp [anchor]; omega
    rw [he1, he2, he3]
    rcases hb k with ⟨_, _, _, _, _, hbk, hyk, hxk⟩
    have hodd3 := (hodd (anchor k + 3) (by have := (ha k).1; omega)
      (by have := (ha k).2.2; rcases hphase with h | h <;> omega)).2.2
    have hodd5 := (hodd (anchor k + 5) (by have := (ha k).1; omega)
      (by have := (ha k).2.2; rcases hphase with h | h <;> omega)).2.2
    exact hproject _ _ _ _ _ _ _ hbk hyk hxk hodd3 hodd5
  let q := sixTargetPeriod H / 4
  have hT : sixTargetPeriod H = 4 * q := (Nat.mul_div_cancel' h4).symm
  have hM : ∀ k, M (k + q) = M k := by
    intro k
    dsimp [M]
    congr 1
    have he : anchor (k + q) + 2 = anchor k + 2 + sixTargetPeriod H := by
      dsimp [anchor]
      omega
    rw [he]
    exact hF _ (by have := (ha k).2.1; omega)
  let run (p : ℕ → Fin 16) (j : ℕ) : Fin 36 → Fin 36 := Nat.rec (fun s => s)
      (fun i R s => sixRows (sixExtensions 0 (sixMaskGenerator (p i))) (R s)) j
  have hword : ∀ (p : ℕ → Fin 16) j, ∃ r : Fin 48,
      ∀ s, run p j s = sixRows r s := by
    intro p j
    induction j with
    | zero => exact ⟨0, fun s => (hid s).symm⟩
    | succ j ih =>
      rcases ih with ⟨r, hr⟩
      refine ⟨sixExtensions r (sixMaskGenerator (p j)), ?_⟩
      intro s
      change sixRows (sixExtensions 0 (sixMaskGenerator (p j))) (run p j s) = _
      rw [hr]
      exact (hclose r (sixMaskGenerator (p j)) s).symm
  have hwalk : ∀ k j, S (k + j) = run (fun i => M (k + i)) j (S k) := by
    intro k j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Nat.add_succ, hstep]
      rw [ih]
  have hMmul : ∀ k j, M (k + j * q) = M k := by
    intro k j
    induction j with
    | zero => simp
    | succ j ih =>
      have he : k + (j + 1) * q = (k + j * q) + q := by ring
      rw [he, hM, ih]
  have hstabilize : ∀ k, S (k + 4 * q) = S (k + 3 * q) := by
    intro k
    rcases hword (fun i => M (k + i)) q with ⟨r, hr⟩
    have hseg : ∀ j, S (k + (j + 1) * q) = sixRows r (S (k + j * q)) := by
      intro j
      have he : k + (j + 1) * q = (k + j * q) + q := by ring
      rw [he, hwalk]
      have hm : (fun i => M ((k + j * q) + i)) = (fun i => M (k + i)) := by
        funext i
        have he : (k + j * q) + i = (k + i) + j * q := by omega
        rw [he, hMmul]
      rw [hm, hr]
    have h0 := hseg 0
    have h1 := hseg 1
    have h2 := hseg 2
    have h3 := hseg 3
    norm_num only [Nat.zero_mul, Nat.add_zero, Nat.one_mul] at h0 h1 h2 h3
    rw [h3, h2, h1, h0, hpower]
  have hSperiod : ∀ k, 3 * q ≤ k → S (k + q) = S k := by
    intro k hk
    have he1 : (k - 3 * q) + 4 * q = k + q := by omega
    have he2 : (k - 3 * q) + 3 * q = k := by omega
    simpa only [he1, he2] using hstabilize (k - 3 * q)
  have hap : ∀ k, anchor (k + q) = anchor k + sixTargetPeriod H := by
    intro k
    dsimp [anchor]
    omega
  have hreconstruct : ∀ k, 3 * q ≤ k → ∀ r, r < 4 →
      f (anchor (k + q) + r) = f (anchor k + r) := by
    intro k hk
    have ht := congrArg sixStates (hSperiod k hk)
    rw [hS, hS] at ht
    have hu : f (anchor (k + q) - 3) = f (anchor k - 3) :=
      congrArg (fun s : ℕ × ℕ × ℕ => s.1) ht
    have hv : f (anchor (k + q) - 1) = f (anchor k - 1) :=
      congrArg (fun s : ℕ × ℕ × ℕ => s.2.1) ht
    have hw : f (anchor (k + q) + 1) = f (anchor k + 1) :=
      congrArg (fun s : ℕ × ℕ × ℕ => s.2.2) ht
    have hcoef : fixedValues A (anchor (k + q) + 2) =
        fixedValues A (anchor k + 2) := by
      rw [hap]
      have he : anchor k + sixTargetPeriod H + 2 = anchor k + 2 + sixTargetPeriod H := by omega
      rw [he]
      exact hF _ (by have := (ha k).2.1; omega)
    have hb0 := (hb k).2.2.2.2.2.1
    have hb1 := (hb (k + q)).2.2.2.2.2.1
    have heven : f (anchor (k + q) + 2) = f (anchor k + 2) := by
      rw [hb1, hb0, hcoef, hv, hw]
    have hy0 := (hb k).2.2.2.2.2.2.1
    have hy1 := (hb (k + q)).2.2.2.2.2.2.1
    have hy : f (anchor (k + q) + 3) = f (anchor k + 3) := by
      rw [hy1, hy0, heven, hw, hu]
    intro r hr
    interval_cases r
    · simp only [Nat.add_zero]
      have hz0 : f (anchor k) = 0 := (hz _ (by have := (ha k).1; omega)).mpr (ha k).2.2
      have hz1 : f (anchor (k + q)) = 0 :=
        (hz _ (by have := (ha (k + q)).1; omega)).mpr (ha (k + q)).2.2
      rw [hz0, hz1]
    · exact hw
    · exact heven
    · exact hy
  refine ⟨anchor (3 * q), ?_⟩
  intro n hn
  let k := (n - z) / 4
  let r := (n - z) % 4
  have hr : r < 4 := Nat.mod_lt _ (by decide)
  have hnz : z ≤ n := by dsimp [anchor] at hn; omega
  have hnkr : n = anchor k + r := by
    have he := Nat.mod_add_div (n - z) 4
    dsimp [anchor, k, r]
    omega
  have hk : 3 * q ≤ k := by
    dsimp [anchor] at hn
    dsimp [anchor] at hnkr
    omega
  change f (n + sixTargetPeriod H) = f n
  rw [hnkr]
  have he : anchor k + r + sixTargetPeriod H = anchor (k + q) + r := by
    rw [hap]
    omega
  rw [he]
  exact hreconstruct k hk r hr
end D5.S3.Combinatorics.Games.DivisorNimGrundy
